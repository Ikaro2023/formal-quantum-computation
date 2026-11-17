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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.StageLoop
public import QuantumComputation.Maths.Trigonometry
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section Sec_LockOddSetStage
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
/-!
 ## Section 1: Multi-Target Stationary-chord Stationary Eigenvector & Pure-Angle Schedule
 Bounds
-/
theorem cos_sub_sq_sub_cos_add_sq (x y : ℝ) :
    Real.cos (x - y) ^ 2 - Real.cos (x + y) ^ 2 = Real.sin (2 * x) * Real.sin (2 * y) := by
  rw [Real.cos_sub, Real.cos_add, Real.sin_two_mul, Real.sin_two_mul]; ring
theorem arcsin_le_add_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 2) : Real.arcsin x ≤ x + x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have h3 : x * (1 + x) ^ 3 ≤ 2 := by
    nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 3 / 2) 3]
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩
    ⟨by nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩]
  nlinarith [Real.sin_gt_sub_cube (by positivity : 0 < x + x ^ 2),
    mul_le_mul_of_nonneg_left h3 (sq_nonneg x)]
theorem sqrt_dim_mul_cos_halfAngleSet (q c : ℕ) :
    √(2 ^ q : ℝ) * Real.cos (halfAngleSet q c) = √((2 ^ q : ℝ) - (c : ℝ)) := by
  rw [halfAngleSet, Real.cos_arcsin, Real.sq_sqrt (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1; have hd : (2 ^ q : ℝ) ≠ 0 := (by positivity); field_simp
/-- Amplitude of every unmarked basis state in `groverSetState M0 K` (`M0.card = c < 2 ^
  q`). -/
noncomputable def nonTargetSetAmp (q c K : ℕ) : ℝ :=
  Real.cos ((2 * (K : ℝ) + 1) * halfAngleSet q c) / √((2 ^ q : ℝ) - (c : ℝ))
/-- Ratio `cos((2K + 3)θ) / cos((2K + 1)θ)` of unmarked amplitudes across one Grover step. -/
noncomputable def nonTargetAngleRatio (θ : ℝ) (K : ℕ) : ℝ :=
  Real.cos ((2 * (K : ℝ) + 3) * θ) / Real.cos ((2 * (K : ℝ) + 1) * θ)
/-- Target attenuation ratio `s` making `lockSetKraus0 M0 s` preserve the Grover ray. -/
noncomputable def targetAngleRatio (θ : ℝ) (K : ℕ) : ℝ :=
  nonTargetAngleRatio θ K * Real.sin ((2 * (K : ℝ) + 1) * θ) / Real.sin ((2 * (K : ℝ) + 3) * θ)
theorem nonTargetSetAmp_succ {q c : ℕ} (K : ℕ) (hcos : Real.cos ((2 * (K : ℝ) + 1) * halfAngleSet q
    c) ≠ 0) : nonTargetSetAmp q c (K + 1) = nonTargetAngleRatio (halfAngleSet q c) K *
    nonTargetSetAmp q c K := by
  have h3 : 2 * ((K + 1 : ℕ) : ℝ) + 1 = 2 * (K : ℝ) + 3 := (by push_cast; ring)
  rw [nonTargetSetAmp, nonTargetSetAmp, nonTargetAngleRatio, h3, div_mul_div_cancel₀ hcos]
theorem groverSetState_apply_not_mem {q : ℕ} (M0 : Finset (Fin (2 ^ q)))
    (hc1 : 1 ≤ M0.card) (hcN : M0.card < 2 ^ q) (K : ℕ) {u : Fin (2 ^ q)} (hu : u ∉ M0) :
    groverSetState M0 K u = ((nonTargetSetAmp q M0.card K : ℝ) : ℂ) := by
  have heq (v : Fin (2 ^ q)) (hv : v ∉ M0) : groverSetState M0 K v = groverSetState M0 K u := by
    induction K with
    | zero => rfl
    | succ K ih =>
        simp only [groverSetState, Grover.diffuserMatrix_mulVec, setOracleMatrix_mulVec,
          ite_eq_right hu, ite_eq_right hv, ih]
  obtain ⟨htarget, hsum⟩ := groverSetState_target_sum M0 hc1 hcN.le K; set c := M0.card
  set θ := halfAngleSet q c; have hsumM0 : ∑ x ∈ M0, groverSetState M0 K x =
      ((√(c : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * θ) : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl htarget, Finset.sum_const, nsmul_eq_mul]; norm_cast
    have hcc : (c : ℝ) * (1 / √(c : ℝ)) = √(c : ℝ) := (by rw [mul_one_div, Real.div_sqrt])
    change (c : ℝ) * (1 / √(c : ℝ) * _) = _; rw [← mul_assoc, hcc]
  have hsumCompl : ∑ x ∈ M0ᶜ, groverSetState M0 K x =
      (((2 ^ q : ℝ) - (c : ℝ) : ℝ) : ℂ) * groverSetState M0 K u := by
    have hcongr : ∑ x ∈ M0ᶜ, groverSetState M0 K x = ∑ _x ∈ M0ᶜ, groverSetState M0 K u :=
      Finset.sum_congr rfl fun v hv ↦ heq v (Finset.mem_compl.1 hv)
    rw [hcongr, Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub hcN.le]
    push_cast; rfl
  have hpart : ∑ x ∈ M0, groverSetState M0 K x + ∑ x ∈ M0ᶜ, groverSetState M0 K x = ∑ i : Fin (2 ^
    q), groverSetState M0 K i := Finset.sum_add_sum_compl M0 (groverSetState M0 K)
  rw [hsumM0, hsumCompl, hsum] at hpart
  have hnum : √(2 ^ q : ℝ) * Real.cos (2 * (K : ℝ) * θ) - √(c : ℝ) * Real.sin ((2 * (K : ℝ) + 1) *
    θ) = √((2 ^ q : ℝ) - (c : ℝ)) * Real.cos ((2 * (K : ℝ) + 1) * θ) := by
    rw [← sqrt_dim_mul_cos_halfAngleSet q c,
      show 2 * (K : ℝ) * θ = (2 * (K : ℝ) + 1) * θ - θ by ring, Real.cos_sub]
    linear_combination Real.sin ((2 * (K : ℝ) + 1) * θ) * sqrt_dim_mul_sin_halfAngleSet hcN.le
  have hsub_pos : (0 : ℝ) < (2 ^ q : ℝ) - (c : ℝ) := by
    have hlt : (c : ℝ) < (2 ^ q : ℝ) := (by exact_mod_cast hcN); linarith
  have hx : groverSetState M0 K u * (((2 ^ q : ℝ) - (c : ℝ) : ℝ) : ℂ) =
      ((√((2 ^ q : ℝ) - (c : ℝ)) * Real.cos ((2 * (K : ℝ) + 1) * θ) : ℝ) : ℂ) := by
    rw [← hnum]; push_cast at hpart ⊢; linear_combination hpart
  have hne : (((2 ^ q : ℝ) - (c : ℝ) : ℝ) : ℂ) ≠ 0 := (by exact_mod_cast hsub_pos.ne')
  rw [nonTargetSetAmp, ← mul_div_cancel_right₀ (groverSetState M0 K u) hne, hx,
    ← Complex.ofReal_div, mul_div_right_comm, Real.sqrt_div_self', one_div_mul_eq_div]
/-- Effective diagonal matrix on `Fin (2 ^ q)` of outcome `0` of the weak parity
  measurement. -/
def lockSetKraus0 {q : ℕ} (M0 : Finset (Fin (2 ^ q))) (s : ℝ) :
    Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ := Matrix.diagonal fun u ↦ if u ∈ M0 then (-s : ℂ) else 1
theorem lockSetKraus0_mulVec_groverSetState {q : ℕ} (M0 : Finset (Fin (2 ^ q))) (hc1 : 1 ≤
    M0.card) (hcN : M0.card < 2 ^ q) (K : ℕ) (hsin : Real.sin ((2 * (K : ℝ) + 3) * halfAngleSet q
    M0.card) ≠ 0) (hcos : Real.cos ((2 * (K : ℝ) + 1) * halfAngleSet q M0.card) ≠ 0) :
    lockSetKraus0 M0 (targetAngleRatio (halfAngleSet q M0.card) K) *ᵥ groverSetState M0 (K + 1) =
    (nonTargetAngleRatio (halfAngleSet q M0.card) K : ℂ) • (setOracleMatrix M0 *ᵥ groverSetState M0
    K) := by
  set θ := halfAngleSet q M0.card; ext u
  rw [lockSetKraus0, Matrix.mulVec_diagonal, Pi.smul_apply, setOracleMatrix_mulVec, smul_eq_mul]
  by_cases hu : u ∈ M0
  · rw [ite_eq_left hu, ite_eq_left hu, (groverSetState_target_sum M0 hc1 hcN.le (K + 1)).1 u hu,
      (groverSetState_target_sum M0 hc1 hcN.le K).1 u hu, show 2 * ((K + 1 : ℕ) : ℝ) + 1 = 2 * (K :
      ℝ) + 3 by push_cast; ring]
    have hmul : -targetAngleRatio θ K * (1 / √(M0.card : ℝ) * Real.sin ((2 * (K : ℝ) + 3) * θ)) =
      nonTargetAngleRatio θ K * -(1 / √(M0.card : ℝ) * Real.sin ((2 * (K : ℝ) + 1) * θ)) := by
      rw [targetAngleRatio]
      have hdiv : nonTargetAngleRatio θ K * Real.sin ((2 * (K : ℝ) + 1) * θ) / Real.sin ((2 * (K :
        ℝ) + 3) * θ) * Real.sin ((2 * (K : ℝ) + 3) * θ) = nonTargetAngleRatio θ K * Real.sin ((2 *
        (K : ℝ) + 1) * θ) := div_mul_cancel₀ _ hsin
      linear_combination -(1 / √(M0.card : ℝ)) * hdiv
    exact_mod_cast hmul
  · rw [ite_eq_right hu, ite_eq_right hu, groverSetState_apply_not_mem M0 hc1 hcN (K + 1) hu,
      groverSetState_apply_not_mem M0 hc1 hcN K hu, one_mul]
    exact_mod_cast nonTargetSetAmp_succ K hcos
/-- Initial Grover iteration schedule `⌊(π / 8) / x⌋₊` for sin-half-angle `x`. -/
noncomputable def lockAngleSched (x : ℝ) : ℕ := ⌊π / 8 * (1 / x)⌋₊
theorem cos_sq_sub_cos_sq_angle (θ : ℝ) (K : ℕ) :
    Real.cos ((2 * (K : ℝ) + 1) * θ) ^ 2 - Real.cos ((2 * (K : ℝ) + 3) * θ) ^ 2 =
      2 * Real.sin θ * Real.cos θ * Real.sin ((4 * (K : ℝ) + 4) * θ) := by
  rw [← Real.sin_two_mul, mul_comm (Real.sin _)]
  convert cos_sub_sq_sub_cos_add_sq ((2 * (K : ℝ) + 2) * θ) θ using 3 <;> ring_nf
/-- Pure-angle generalization of `Analysis.Schedule_hyps_le`: for any `0 < x ≤ 1 / 16`
  with `θ = arcsin x` and `K = ⌊(π / 8) / x⌋₊`, `targetAngleRatio θ K ∈ (0, 1)`, `q = α ^ 2
  < 1`,
  and `(K: ℝ) + 3 + q / (1 - q) ≤ (π / 8 + 1 / 4) * (1 / x) + 4`. -/
theorem lockAngle_hyps_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 16) :
    let θ := Real.arcsin x; let K := lockAngleSched x; let q := nonTargetAngleRatio θ K ^ 2
    (0 < targetAngleRatio θ K ∧ targetAngleRatio θ K < 1 ∧ Real.sin ((2 * (K : ℝ) + 3) * θ) ≠ 0 ∧
      Real.cos ((2 * (K : ℝ) + 1) * θ) ≠ 0 ∧ q < 1) ∧ (K : ℝ) + 3 + q / (1 - q) ≤ (π / 8 + 1 / 4) *
      (1 / x) + 4 := by
  intro θ K q; set s := 1 / x with hs_def; have hs_pos : 0 < s := (by positivity)
  have hs : 16 ≤ s := (by rw [hs_def]; exact (le_div_iff₀ hx0).2 (by linarith))
  have hsx : s * x = 1 := one_div_mul_cancel hx0.ne'
  have hsx2 : s * x ^ 2 = x := (by rw [sq, ← mul_assoc, hsx, one_mul])
  have hk1 : (K : ℝ) ≤ π / 8 * s := Nat.floor_le (by positivity)
  have hk2 : π / 8 * s < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsinθ_eq : Real.sin θ = x := Real.sin_arcsin (by linarith) (by linarith)
  have hθ_nn : 0 ≤ θ := Real.arcsin_nonneg.2 hx0.le
  have hθl : x ≤ θ := hsinθ_eq ▸ Real.sin_le hθ_nn
  have hθu : θ ≤ x + x ^ 2 := arcsin_le_add_sq hx0.le (by linarith); set k := (K : ℝ) with hk_def
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hxx : x ^ 2 ≤ x / 16 := by
    rw [sq, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hx1 hx0.le
  have hθ0 : 0 < θ := hx0.trans_le hθl; have hθ2 : θ ≤ 2 * x := (by linarith)
  have hπ := Real.pi_gt_three; have hπ' := Real.pi_lt_d2
  have hπsx : π * (s * x) = π := (by rw [hsx, mul_one])
  have hπsx2 : π * (s * x ^ 2) = π * x := (by rw [hsx2])
  have hφ1 : π / 2 ≤ (4 * k + 4) * θ := by
    linarith [mul_le_mul_of_nonneg_left hθl (by positivity : (0 : ℝ) ≤ π / 8 * s),
      mul_le_mul_of_nonneg_right hk2.le hθ0.le]
  have hφ2 : (4 * k + 4) * θ ≤ π / 2 + 6 * x := by
    linarith [mul_le_mul_of_nonneg_left hθu (by linarith : (0 : ℝ) ≤ 4 * k + 4),
      mul_le_mul_of_nonneg_right hk1 (by positivity : (0 : ℝ) ≤ x + x ^ 2),
      mul_le_mul_of_nonneg_right hπ'.le hx0.le]
  have hsinθ_pos : 0 < Real.sin θ := (by linarith)
  have hcosθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : 0 < Real.sin ((2 * k + 1) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos (by linarith) hθ0) (by linarith)
  have hc1 : 0 < Real.cos ((2 * k + 1) * θ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 ≤ Real.cos ((2 * k + 2) * θ) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc3_pos : 0 < Real.cos ((2 * k + 3) * θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs4 : 0 < Real.sin ((4 * k + 4) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs3_pos : 0 < Real.sin ((2 * k + 3) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos (by linarith) hθ0) (by linarith)
  have hs3_ge : Real.sin ((2 * k + 1) * θ) ≤ Real.sin ((2 * k + 3) * θ) := by
    have hdiff := Real.sin_sub_sin ((2 * k + 3) * θ) ((2 * k + 1) * θ)
    rw [show ((2 * k + 3) * θ - (2 * k + 1) * θ) / 2 = θ by ring,
      show ((2 * k + 3) * θ + (2 * k + 1) * θ) / 2 = (2 * k + 2) * θ by ring] at hdiff
    have hprod : 0 ≤ 2 * Real.sin θ * Real.cos ((2 * k + 2) * θ) := (by positivity); linarith
  have hatt0 : 0 ≤ nonTargetAngleRatio θ K := div_nonneg hc3_pos.le hc1.le
  have hatt_pos : 0 < nonTargetAngleRatio θ K := div_pos hc3_pos hc1
  have hatt1 : nonTargetAngleRatio θ K < 1 := (div_lt_one hc1).2 <|
    lt_of_pow_lt_pow_left₀ 2 hc1.le <| by
      linarith [cos_sq_sub_cos_sq_angle θ K, mul_pos (mul_pos hsinθ_pos hcosθ) hs4]
  have htar_pos : 0 < targetAngleRatio θ K := div_pos (mul_pos hatt_pos hs1) hs3_pos
  have htar_lt1 : targetAngleRatio θ K < 1 :=
    (div_lt_one hs3_pos).2 ((mul_lt_of_lt_one_left hs1 hatt1).trans_le hs3_ge)
  have hq_lt1 : q < 1 := pow_lt_one₀ hatt0 hatt1 two_ne_zero
  refine ⟨⟨htar_pos, htar_lt1, hs3_pos.ne', hc1.ne', hq_lt1⟩, ?_⟩
  have hC : Real.cos ((2 * k + 3) * θ) ^ 2 ≤ 1 / 2 := by
    linarith [Real.cos_sq ((2 * k + 3) * θ), Real.cos_nonpos_of_pi_div_two_le_of_le
      (x := 2 * ((2 * k + 3) * θ)) (by linarith) (by linarith)]
  have hcθ : 1 - 2 * x ^ 2 ≤ Real.cos θ := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ), pow_le_pow_left₀ hθ0.le hθ2 2]
  have hsφ : 1 - 18 * x ^ 2 ≤ Real.sin ((4 * k + 4) * θ) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (4 * k + 4) * θ - π / 2)
    rw [Real.cos_sub_pi_div_two] at h
    linarith [pow_le_pow_left₀ (by linarith : 0 ≤ (4 * k + 4) * θ - π / 2)
      (by linarith : (4 * k + 4) * θ - π / 2 ≤ 6 * x) 2]
  have hP : 2 * (1 - 20 * x ^ 2) ≤ 2 * Real.cos θ * Real.sin ((4 * k + 4) * θ) := by
    linarith [mul_le_mul hcθ hsφ (by linarith) hcosθ.le, pow_nonneg hx0.le 4]
  have hPpos : 0 < 2 * Real.cos θ * Real.sin ((4 * k + 4) * θ) := (by positivity)
  have hc1_sq_ne : Real.cos ((2 * k + 1) * θ) ^ 2 ≠ 0 := pow_ne_zero 2 hc1.ne'
  have hq_div : q / (1 - q) = Real.cos ((2 * k + 3) * θ) ^ 2 / (2 * Real.cos θ * Real.sin ((4 * k +
    4) * θ)) * s := by
    have hxs : x = 1 / s := (by rw [hs_def, one_div_one_div])
    rw [show q = nonTargetAngleRatio θ K ^ 2 from rfl, nonTargetAngleRatio,
      div_pow, one_sub_div hc1_sq_ne, div_div_div_cancel_right₀ hc1_sq_ne,
      cos_sq_sub_cos_sq_angle, ← hk_def, hsinθ_eq, hxs]
    field_simp [hs_pos.ne', hcosθ.ne', hs4.ne']
  have hfrac : Real.cos ((2 * k + 3) * θ) ^ 2 /
      (2 * Real.cos θ * Real.sin ((4 * k + 4) * θ)) * s ≤ s / 4 + 1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hPpos]
    linarith [mul_le_mul_of_nonneg_right hC hs_pos.le,
      mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ s / 4 + 1)]
  rw [hq_div]; linarith
/-! ## Section 2: `localAddrReg`, `oddSet`, `oddFrac`, and `n ≥ 100` Stage Cost Ratio Bounds -/
/-- The `m * n`-qubit address subregister inside `((n + 1) * m)` wires, selecting the `n`
  index
  wires `localIdxReg n` of each slot `localSlotReg n m i`. -/
def localAddrReg (n m : ℕ) : QRegister (m * n) ((n + 1) * m) :=
  ⟨{ toFun := fun u ↦
        let p := finProdFinEquiv.symm u
        localSlotReg n m p.1 (localIdxReg n p.2)
     inj' := by
        intro u₁ u₂ heq
        let p₁ := finProdFinEquiv.symm u₁
        let p₂ := finProdFinEquiv.symm u₂
        change localSlotReg n m p₁.1 (localIdxReg n p₁.2) =
          localSlotReg n m p₂.1 (localIdxReg n p₂.2) at heq
        by_cases hj : p₁.1 = p₂.1
        · have heq' : localSlotReg n m p₁.1 (localIdxReg n p₁.2) =
              localSlotReg n m p₁.1 (localIdxReg n p₂.2) := hj ▸ heq
          have hr : p₁.2 = p₂.2 :=
            (localIdxReg n).wires.injective ((localSlotReg n m p₁.1).wires.injective heq')
          exact finProdFinEquiv.symm.injective (Prod.ext hj hr)
        · exact (QRegister.disjoint_iff.1 (localSlotReg_disjoint hj) _ _ heq).elim }⟩
@[simp]
theorem localAddrReg_finProdFinEquiv (n m : ℕ) (i : Fin m) (r : Fin n) :
    localAddrReg n m (finProdFinEquiv (i, r)) = localSlotReg n m i (localIdxReg n r) := by
  change (let p := finProdFinEquiv.symm (finProdFinEquiv (i, r))
    localSlotReg n m p.1 (localIdxReg n p.2)) = _
  rw [Equiv.symm_apply_apply]
/-- Marker wire `i` inside `((n + 1) * m)` as a `1`-qubit local `QRegister`. -/
def localFlagReg (n m : ℕ) (i : Fin m) : QRegister 1 ((n + 1) * m) :=
  (localSlotReg n m i).compose (localMarkerReg n)
theorem markerReg_eq_compose_localFlagReg (n m k : ℕ) (i : Fin m) :
    markerReg n m k i = (oracleReg n m k).compose (localFlagReg n m i) := by ext w; rfl
/-- Bijection between `m * n`-bit basis indices and `m`-tuples of `n`-bit addresses. -/
def addrEquiv (n m : ℕ) : Fin (2 ^ (m * n)) ≃ (Fin m → Fin (2 ^ n)) :=
  (basisBits (m * n)).trans <|
    ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl (ZMod 2))).symm).trans <|
      (Equiv.curry (Fin m) (Fin n) (ZMod 2)).trans <|
        Equiv.piCongrRight (fun _ ↦ (basisBits n).symm)
/-- Slot `i`'s `n`-bit address extracted from a `((n + 1) * m)`-wire basis index `z`. -/
def localSlotAddr (n m : ℕ) (z : Fin (2 ^ ((n + 1) * m))) (i : Fin m) : Fin (2 ^ n) :=
  (localIdxReg n).extractIndex ((localSlotReg n m i).extractIndex z)
/-- Slot `i`'s `1`-bit marker flag extracted from a `((n + 1) * m)`-wire basis index `z`. -/
def localSlotFlag (n m : ℕ) (z : Fin (2 ^ ((n + 1) * m))) (i : Fin m) : Fin (2 ^ 1) :=
  (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex z)
theorem addrEquiv_extractIndex_localAddrReg (n m : ℕ) (z : Fin (2 ^ ((n + 1) * m))) (i : Fin m) :
    addrEquiv n m ((localAddrReg n m).extractIndex z) i = localSlotAddr n m z i := by
  apply (basisBits n).injective; funext r; have hL (u : Fin (2 ^ (m * n))) :
      basisBits n (addrEquiv n m u i) r = basisBits (m * n) u (finProdFinEquiv (i, r)) := by
    simp [addrEquiv]
  rw [hL, QRegister.basisBits_extractIndex, localAddrReg_finProdFinEquiv, localSlotAddr,
    QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
/-- Marker wire `i` viewed in `(localAddrReg n m).Environment`. -/
def localFlagEnvWire (n m : ℕ) (i : Fin m) : (localAddrReg n m).Environment :=
  ⟨localSlotReg n m i (localMarkerReg n 0), by
    rintro ⟨u, hu⟩
    obtain ⟨⟨j, r⟩, rfl⟩ := finProdFinEquiv.surjective u
    rw [localAddrReg_finProdFinEquiv] at hu
    by_cases hij : j = i
    · subst hij
      have hsub := (localSlotReg n m j).wires.injective hu
      exact QRegister.disjoint_iff.1 (localMarkerReg_disjoint_localIdxReg n) _ _ hsub.symm
    · exact QRegister.disjoint_iff.1 (localSlotReg_disjoint hij) _ _ hu⟩
theorem basisBits_localSlotFlag (n m : ℕ) (z : Fin (2 ^ ((n + 1) * m))) (i : Fin m) :
    basisBits 1 (localSlotFlag n m z i) 0 =
      ((localAddrReg n m).basisSplitEquiv z).2 (localFlagEnvWire n m i) := by
  rw [QRegister.basisSplitEquiv_apply_snd, localFlagEnvWire, localSlotFlag,
    QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
theorem localSlotFlag_of_env_zero {n m : ℕ} (z : Fin (2 ^ ((n + 1) * m))) (hE : ((localAddrReg n
    m).basisSplitEquiv z).2 = 0) (i : Fin m) : localSlotFlag n m z i = 0 := by
  rw [(show ∀ b : Fin (2 ^ 1), b = 0 ↔ basisBits 1 b 0 = 0 by
          intro b; rw [basisBits_eq_div_mod]; fin_cases b
          · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
          · exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩),
    basisBits_localSlotFlag, hE, Pi.zero_apply]
theorem localSlotFlag_of_env_one {n m : ℕ} (z : Fin (2 ^ ((n + 1) * m))) (hE : ((localAddrReg n
    m).basisSplitEquiv z).2 = 1) (i : Fin m) : localSlotFlag n m z i = 1 := by
  rw [(show ∀ b : Fin (2 ^ 1), b = 1 ↔ basisBits 1 b 0 = 1 by
      intro b; rw [basisBits_eq_div_mod]; fin_cases b
      · exact ⟨fun h ↦ (nomatch h), fun h ↦ (nomatch h)⟩
      · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩),
    basisBits_localSlotFlag, hE, Pi.one_apply]
/-- Odd-parity `m`-tuple address set: tuples `(x_0,..., x_{m-1})` hitting `A` an odd number
  of
  times. -/
def oddSet (n m : ℕ) (A : Finset (Fin (2 ^ n))) : Finset (Fin (2 ^ (m * n))) :=
  Finset.univ.filter fun u ↦ (∏ i : Fin m, if addrEquiv n m u i ∈ A then (-1 : ℤ) else 1) = -1
theorem prod_ite_neg_one_or_one {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] : (∏ i ∈
    s, if P i then (-1 : ℤ) else 1) = -1 ∨ (∏ i ∈ s, if P i then (-1 : ℤ) else 1) = 1 := by
  induction s using Finset.cons_induction with
  | empty => exact .inr rfl
  | cons a s _ ih =>
      rw [Finset.prod_cons]; rcases ih with h | h <;> by_cases hP : P a <;> simp [h, hP]
/-- Exact fraction `|oddSet n m A| / 2^(m*n) = (1 - (1 - 2r / 2^n)^m) / 2` for `r = A.card`. -/
noncomputable def oddFrac (n m r : ℕ) : ℝ := (1 - (1 - 2 * (r : ℝ) / (2 ^ n : ℝ)) ^ m) / 2
theorem oddSet_card_div {n m : ℕ} (A : Finset (Fin (2 ^ n))) :
    ((oddSet n m A).card : ℝ) / (2 ^ (m * n) : ℝ) = oddFrac n m A.card := by
  let M0 := oddSet n m A; let g (x : Fin (2 ^ n)) : ℝ := if x ∈ A then -1 else 1
  have htm (u : Fin (2 ^ (m * n))) :
      (if u ∈ M0 then (2 : ℝ) else 0) = 1 - ∏ i : Fin m, g (addrEquiv n m u i) := by
    simp_rw [show ∀ x, g x = ((if x ∈ A then (-1 : ℤ) else 1 : ℤ) : ℝ) from fun _ ↦ by
      dsimp only [g]; split_ifs <;> norm_num, ← Int.cast_prod]
    simp only [M0, oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases prod_ite_neg_one_or_one Finset.univ
      (fun i : Fin m ↦ addrEquiv n m u i ∈ A) with h | h <;> rw [h] <;> norm_num
  have hce : 2 * (M0.card : ℝ) = (2 ^ (m * n) : ℝ) - ((2 ^ n : ℝ) - 2 * (A.card : ℝ)) ^ m := by
    rw [show 2 * (M0.card : ℝ) = ∑ u : Fin (2 ^ (m * n)), if u ∈ M0 then (2 : ℝ) else 0 by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]]
    simp_rw [htm]
    rw [Finset.sum_sub_distrib, (addrEquiv n m).sum_comp (fun f : Fin m → Fin (2 ^ n) ↦
      ∏ i, g (f i)), ← Fintype.sum_pow g m,
      show ∑ x : Fin (2 ^ n), g x = (2 ^ n : ℝ) - 2 * (A.card : ℝ) by
        simp_rw [show ∀ x, g x = 1 - if x ∈ A then (2 : ℝ) else 0 from fun _ ↦ by
          dsimp only [g]; split_ifs <;> norm_num]
        rw [Finset.sum_sub_distrib]
        simp [Finset.sum_ite_mem, Finset.univ_inter, mul_comm]]
    simp
  unfold oddFrac; rw [div_eq_iff (by positivity)]
  have hpow : ((2 ^ n : ℝ) - 2 * (A.card : ℝ)) ^ m =
      (1 - 2 * (A.card : ℝ) / (2 ^ n : ℝ)) ^ m * (2 ^ (m * n) : ℝ) := by
    rw [show (2 ^ (m * n) : ℝ) = (2 ^ n : ℝ) ^ m by rw [mul_comm, pow_mul], ← mul_pow]; congr 1
    have hd : (2 ^ n : ℝ) ≠ 0 := (by positivity); field_simp
  linarith
/-- Grover half-angle on `oddSet n m A` (`A.card = r`). -/
noncomputable def halfAngleOdd (n m r : ℕ) : ℝ := Real.arcsin √(oddFrac n m r)
theorem halfAngleSet_oddSet_eq {n m : ℕ} (A : Finset (Fin (2 ^ n))) :
    halfAngleSet (m * n) (oddSet n m A).card = halfAngleOdd n m A.card := by
  rw [halfAngleSet, oddSet_card_div, halfAngleOdd]
/-- Initial Grover iteration count `⌊(π / 8) / √(oddFrac n m r)⌋₊` for stage `r`. -/
noncomputable def lockOddSched (n m r : ℕ) : ℕ := lockAngleSched √(oddFrac n m r)
/-- Clamped attenuation ratio `s ∈ [0, 1]` used in `lockStageCircuit`. -/
noncomputable def clampedOddRatio (n m r : ℕ) : ℝ :=
  max 0 (min 1 (targetAngleRatio (halfAngleOdd n m r) (lockOddSched n m r)))
theorem clampedOddRatio_mem_Icc (n m r : ℕ) :
    0 ≤ clampedOddRatio n m r ∧ clampedOddRatio n m r ≤ 1 :=
  ⟨le_max_left 0 _, max_le zero_le_one (min_le_left 1 _)⟩
/-- Claimed asymptotic relative cost `4091549431 / 5000000000 = 0.8183098862`
  (`verified_cost = 818,310`). -/
def relCostLock : ℚ≥0 := 4091549431 / 5000000000
theorem one_sub_mul_le_pow {y : ℝ} (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * y ≤ (1 - y) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 - y); nlinarith [sq_nonneg y]
theorem pow_le_one_sub_mul_add_sq {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (m : ℕ) :
    (1 - y) ^ m ≤ 1 - (m : ℝ) * y + (m : ℝ) ^ 2 * y ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 - y)
      have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hstep : (1 - (m : ℝ) * y + (m : ℝ) ^ 2 * y ^ 2) * (1 - y) ≤
          1 - ((m : ℝ) + 1) * y + ((m : ℝ) + 1) ^ 2 * y ^ 2 := by
        have hdiff : 1 - ((m : ℝ) + 1) * y + ((m : ℝ) + 1) ^ 2 * y ^ 2 -
            (1 - (m : ℝ) * y + (m : ℝ) ^ 2 * y ^ 2) * (1 - y) =
            ((m : ℝ) + 1) * y ^ 2 + (m : ℝ) ^ 2 * y ^ 3 := by ring
        have hnn : 0 ≤ ((m : ℝ) + 1) * y ^ 2 + (m : ℝ) ^ 2 * y ^ 3 := (by positivity); linarith
      exact hmul.trans hstep
/-- Complete numerical and schedule guarantees for stage `r` when `100 ≤ n` and
  `1 ≤ m, r ≤ 1024`. -/
theorem oddFrac_bounds_of_ge_100 {n m r : ℕ} (hn : 100 ≤ n)
    (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hr1 : 1 ≤ r) (hr1024 : r ≤ 1024) :
    let θ := halfAngleOdd n m r; let K := lockOddSched n m r; let q := nonTargetAngleRatio θ K ^ 2
    (∀ A : Finset (Fin (2 ^ n)), A.card = r → 1 ≤ (oddSet n m A).card ∧ (oddSet n m A).card < 2 ^
      (m * n)) ∧ clampedOddRatio n m r = targetAngleRatio θ K ∧ Real.sin ((2 * (K : ℝ) + 3) * θ) ≠ 0
      ∧ Real.cos ((2 * (K : ℝ) + 1) * θ) ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ (K : ℝ) + 3 + q / (1 - q) ≤
      ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
  intro θ K q
  have h2n_ge : (2 ^ 100 : ℝ) ≤ (2 ^ n : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by positivity) hn
  have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) := (by positivity)
  have hmr_le : (m : ℝ) * (r : ℝ) ≤ 2 ^ 20 := by
    have hnat : m * r ≤ 1024 * 1024 := Nat.mul_le_mul hm1024 hr1024
    calc (m : ℝ) * (r : ℝ) = ((m * r : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((1024 * 1024 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 2 ^ 20 := by norm_num
  set p : ℝ := (m : ℝ) * (r : ℝ) / (2 ^ n : ℝ) with hp_def; have hp_pos : 0 < p := (by positivity)
  have hp_le80 : p ≤ 1 / 2 ^ 80 := by
    rw [hp_def, div_le_iff₀ (by positivity)]
    calc (m : ℝ) * (r : ℝ) ≤ 2 ^ 20 := hmr_le
      _ = (1 / 2 ^ 80) * 2 ^ 100 := by norm_num
      _ ≤ (1 / 2 ^ 80) * (2 ^ n : ℝ) := by gcongr
  set y : ℝ := 2 * (r : ℝ) / (2 ^ n : ℝ); have hy0 : 0 ≤ y := (by positivity)
  have hy1 : y ≤ 1 := by
    have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024); rw [div_le_one (by positivity)]
    linarith
  have hmy : (m : ℝ) * y = 2 * p := (by dsimp [y, p]; ring)
  have hodd_le : oddFrac n m r ≤ p := by
    have h1 := one_sub_mul_le_pow hy0 hy1 m; unfold oddFrac; linarith
  have hodd_ge : p * (1 - 1 / 2 ^ 39) ^ 2 ≤ oddFrac n m r := by
    have h2 := pow_le_one_sub_mul_add_sq hy0 hy1 m
    have hmy2 : (m : ℝ) ^ 2 * y ^ 2 = 4 * p ^ 2 := by
      calc (m : ℝ) ^ 2 * y ^ 2 = ((m : ℝ) * y) ^ 2 := by ring
        _ = (2 * p) ^ 2 := by rw [hmy]
        _ = 4 * p ^ 2 := by ring
    have hodd_ge1 : p * (1 - 2 * p) ≤ oddFrac n m r := (by unfold oddFrac; linarith)
    have h1m2p : (1 - (1 / 2 ^ 39 : ℝ)) ^ 2 ≤ 1 - 2 * p := by
      have hp79 : 2 * p ≤ 1 / 2 ^ 79 := (by linarith)
      have hnum : (1 - (1 / 2 ^ 39 : ℝ)) ^ 2 ≤ 1 - 1 / 2 ^ 79 := (by norm_num); linarith
    exact mul_le_mul_of_nonneg_left h1m2p hp_pos.le |>.trans hodd_ge1
  have hodd_pos : 0 < oddFrac n m r := by
    have hc_pos : (0 : ℝ) < (1 - 1 / 2 ^ 39) ^ 2 := (by norm_num)
    exact lt_of_lt_of_le (mul_pos hp_pos hc_pos) hodd_ge
  set x := √(oddFrac n m r); have hx0 : 0 < x := Real.sqrt_pos.2 hodd_pos
  have hx40 : x ≤ 1 / 2 ^ 40 := by
    calc x ≤ √(1 / 2 ^ 80 : ℝ) := Real.sqrt_le_sqrt (hodd_le.trans hp_le80)
      _ = √((1 / 2 ^ 40 : ℝ) ^ 2) := by congr 1; norm_num
      _ = 1 / 2 ^ 40 := Real.sqrt_sq (by norm_num)
  have hx16 : x ≤ 1 / 16 := hx40.trans (by norm_num)
  obtain ⟨⟨htar_pos, htar_lt1, hsin3, hcos1, hq_lt1⟩, hQ_bound⟩ := lockAngle_hyps_le hx0 hx16
  have hθx : Real.arcsin x = θ := rfl; have hKx : lockAngleSched x = K := rfl
  rw [hθx, hKx] at htar_pos htar_lt1 hsin3 hcos1 hq_lt1 hQ_bound
  have hcard_bounds : ∀ A : Finset (Fin (2 ^ n)), A.card = r →
      1 ≤ (oddSet n m A).card ∧ (oddSet n m A).card < 2 ^ (m * n) := by
    intro A hA; have hdiv := oddSet_card_div (m := m) A; rw [hA] at hdiv
    have hd_pos : (0 : ℝ) < 2 ^ (m * n) := (by positivity)
    have hc_pos : (0 : ℝ) < (oddSet n m A).card := by rw [div_eq_iff hd_pos.ne'] at hdiv; nlinarith
    have hc_lt : ((oddSet n m A).card : ℝ) < 2 ^ (m * n) := by
      rw [div_eq_iff hd_pos.ne'] at hdiv
      have hodd_lt1 : oddFrac n m r < 1 := (hodd_le.trans hp_le80).trans_lt (by norm_num); nlinarith
    exact ⟨by exact_mod_cast (Nat.one_le_iff_ne_zero.2 (by
      have : 0 < (oddSet n m A).card := (by exact_mod_cast hc_pos)
      omega)), by exact_mod_cast hc_lt⟩
  have hclamp : clampedOddRatio n m r = targetAngleRatio θ K := by
    unfold clampedOddRatio; change max 0 (min 1 (targetAngleRatio θ K)) = targetAngleRatio θ K
    rw [min_eq_right htar_lt1.le, max_eq_right htar_pos.le]
  set Smr : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) with hSmr_def
  have hSmr_pos : 0 < Smr := Real.sqrt_pos.2 (by positivity)
  have hSmr_inv : √p = 1 / Smr := by
    rw [hp_def, hSmr_def, Real.sqrt_div (by positivity), Real.sqrt_div (by positivity), one_div_div]
  have hx_ge : (1 - 1 / 2 ^ 39) / Smr ≤ x := by
    have h1 : √(p * (1 - 1 / 2 ^ 39) ^ 2) ≤ x := Real.sqrt_le_sqrt hodd_ge
    rw [Real.sqrt_mul hp_pos.le, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 39), hSmr_inv]
      at h1; simpa [div_eq_mul_inv, mul_comm] using h1
  have hinv_x : 1 / x ≤ Smr / (1 - 1 / 2 ^ 39) := by
    have hc39_pos : (0 : ℝ) < (1 - 1 / 2 ^ 39) / Smr := div_pos (by norm_num) hSmr_pos
    have h := one_div_le_one_div_of_le hc39_pos hx_ge; rwa [one_div_div] at h
  have hSmr_ge40 : (2 ^ 40 : ℝ) ≤ Smr := by
    have hdiv80 : (2 ^ 80 : ℝ) ≤ (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) := by
      rw [le_div_iff₀ hmr_pos]; rw [hp_def, div_le_iff₀ (by positivity)] at hp_le80; linarith
    calc (2 ^ 40 : ℝ) = √((2 ^ 40 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ = √(2 ^ 80 : ℝ) := by congr 1; norm_num
      _ ≤ Smr := Real.sqrt_le_sqrt hdiv80
  have h4_le : (4 : ℝ) ≤ (4 / 2 ^ 40) * Smr := (by linarith); have hpi_lt := Real.pi_lt_d20
  have hpi_gt := Real.pi_gt_d20; have hcoeff : (π / 8 + 1 / 4) / (1 - 1 / 2 ^ 39) + 4 / 2 ^ 40 ≤
      ((relCostLock : ℚ≥0) : ℝ) * (π / 4) := by
    have hnum_pi : (314159265358979323847 / 100000000000000000000 / 8 + 1 / 4 : ℝ) / (1 - 1 / 2 ^
      39) + 4 / 2 ^ 40 ≤ ((relCostLock : ℚ≥0) : ℝ) * (314159265358979323846 /
      100000000000000000000 / 4) := by
      norm_num [relCostLock]
    have hL : (π / 8 + 1 / 4) / (1 - 1 / 2 ^ 39) + 4 / 2 ^ 40 ≤ (314159265358979323847 /
      100000000000000000000 / 8 + 1 / 4 : ℝ) / (1 - 1 / 2 ^ 39) + 4 / 2 ^ 40 := by
      have h1 : π / 8 + 1 / 4 ≤
          314159265358979323847 / 100000000000000000000 / 8 + 1 / 4 := by linarith
      linarith [div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 39)]
    have hR : ((relCostLock : ℚ≥0) : ℝ) * (314159265358979323846 / 100000000000000000000 / 4) ≤
      ((relCostLock : ℚ≥0) : ℝ) * (π / 4) := by
      have hrc : (0 : ℝ) ≤ ((relCostLock : ℚ≥0) : ℝ) := (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) hrc
    exact (hL.trans hnum_pi).trans hR
  have hSmr_split : Smr = (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
    rw [hSmr_def, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_div (by positivity)]
    ring
  have hcost_final : (K : ℝ) + 3 + q / (1 - q) ≤
      ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
    have hstep1 : (π / 8 + 1 / 4) * (1 / x) + 4 ≤
        ((π / 8 + 1 / 4) / (1 - 1 / 2 ^ 39) + 4 / 2 ^ 40) * Smr := by
      calc (π / 8 + 1 / 4) * (1 / x) + 4 ≤ (π / 8 + 1 / 4) * (Smr / (1 - 1 / 2 ^ 39)) + (4 / 2 ^
            40) * Smr := add_le_add (mul_le_mul_of_nonneg_left hinv_x (by positivity)) h4_le
        _ = ((π / 8 + 1 / 4) / (1 - 1 / 2 ^ 39) + 4 / 2 ^ 40) * Smr := by ring
    calc (K : ℝ) + 3 + q / (1 - q) ≤ (π / 8 + 1 / 4) * (1 / x) + 4 := hQ_bound
      _ ≤ ((π / 8 + 1 / 4) / (1 - 1 / 2 ^ 39) + 4 / 2 ^ 40) * Smr := hstep1
      _ ≤ (((relCostLock : ℚ≥0) : ℝ) * (π / 4)) * Smr :=
          mul_le_mul_of_nonneg_right hcoeff hSmr_pos.le
      _ = ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
          rw [hSmr_split]; ring
  exact ⟨hcard_bounds, hclamp, hsin3, hcos1, sq_nonneg _, hq_lt1, hcost_final⟩
/-!
 ## Section 3: Odd-Parity Phase Kickback & Parametric `chordUnitary` on `(n + 1) * m` Wires
-/
theorem splitBasisEquiv_fst_eq_localIdxReg {n : ℕ} (u : Fin (2 ^ (n + 1))) :
    (splitBasisEquiv n 1 u).1 = (localIdxReg n).extractIndex u := by
  obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  rw [Equiv.apply_symm_apply, extractIndex_localIdxReg_splitSymm]
theorem splitBasisEquiv_snd_eq_localMarkerReg {n : ℕ} (u : Fin (2 ^ (n + 1))) :
    (splitBasisEquiv n 1 u).2 = (localMarkerReg n).extractIndex u := by
  obtain ⟨⟨x, b⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  rw [Equiv.apply_symm_apply, extractIndex_localMarkerReg_splitSymm]
theorem permutationUnitary_apply {d : ℕ} (e : Equiv.Perm (Fin d)) (i j : Fin d) :
    (permutationUnitary e).1 i j = if i = e j then 1 else 0 := by
  simpa [Matrix.mulVec_single_one, Pi.single_apply] using
    congrFun (permutationUnitary_mulVec_single e j (1 : ℂ)) i
/-- Single-slot diagonal phase `-1` on `(x ∈ A, b = 0)` and `+1` everywhere else. -/
def slotDiag (n : ℕ) (A : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (n + 1))) : ℂ :=
  if (localIdxReg n).extractIndex u ∈ A ∧ (localMarkerReg n).extractIndex u = 0 then (-1 : ℂ) else 1
/-- Sign table `+1` on `(0, 0)` and `-1` otherwise, conjugating `X` on `b` into
  `-Z = -|0⟩⟨0| + |1⟩⟨1|`. -/
def flagSign (a b : Fin (2 ^ 1)) : ℤ := if a = 0 ∧ b = 0 then 1 else -1
/-- Single-slot real Hermitian involutive matrix conjugating `setMarkingOracle A` into
  `slotDiag n A`. -/
noncomputable def flagWMat (n : ℕ) : Operator (2 ^ (n + 1)) :=
  fun u v ↦
    if (splitBasisEquiv n 1 u).1 = (splitBasisEquiv n 1 v).1 then
      (((1 / √(2 : ℝ)) *
        (flagSign (splitBasisEquiv n 1 u).2 (splitBasisEquiv n 1 v).2 : ℝ) : ℝ) : ℂ)
    else
      0
theorem isRealMatrix_flagWMat (n : ℕ) : IsRealMatrix (flagWMat n) := by
  intro u v; unfold flagWMat; split_ifs <;> simp
theorem flagWMat_conj_setMarkingOracle (n : ℕ) (A : Finset (Fin (2 ^ n))) :
    flagWMat n * (setMarkingOracle A).1 * flagWMat n = Matrix.diagonal (slotDiag n A) := by
  ext u v; rw [Matrix.mul_apply, ← (splitBasisEquiv n 1).symm.sum_comp, Fintype.sum_prod_type]
  have hm1 (w : Fin (2 ^ (n + 1))) :
      (flagWMat n * (setMarkingOracle A).1) u w = flagWMat n u (slotMarkPerm A w) := by
    rw [setMarkingOracle, Matrix.mul_apply,
      Fintype.sum_eq_single (slotMarkPerm A w) (fun y hy ↦ by
        rw [permutationUnitary_apply, ite_eq_right hy, mul_zero]),
      permutationUnitary_apply, ite_eq_left rfl, mul_one]
  simp_rw [hm1]
  have hmark (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) : splitBasisEquiv n 1 (slotMarkPerm A
    ((splitBasisEquiv n 1).symm (x, b))) = (x, b + if x ∈ A then 1 else 0) := by
    simp [slotMarkPerm, tableAddPerm, addRightShear]
  dsimp only [flagWMat]; simp_rw [hmark, Equiv.apply_symm_apply]
  set xu := (splitBasisEquiv n 1 u).1; set bu := (splitBasisEquiv n 1 u).2
  set xv := (splitBasisEquiv n 1 v).1; set bv := (splitBasisEquiv n 1 v).2
  set δ : Fin (2 ^ 1) := if xu ∈ A then 1 else 0
  rw [Fintype.sum_eq_single xu (fun x hx ↦ Finset.sum_eq_zero fun b _ ↦ by
    rw [ite_eq_right (Ne.symm hx), zero_mul])]
  by_cases h1 : xu = xv
  · have hsm : (∑ b : Fin (2 ^ 1), (if xu = xu then (((1 / √(2 : ℝ)) * (flagSign bu (b + δ) : ℝ) :
      ℝ) : ℂ) else 0) * (if xu = xv then (((1 / √(2 : ℝ)) * (flagSign b bv : ℝ) : ℝ) : ℂ) else 0)) =
      (((1 / 2 : ℝ) * ((∑ b : Fin (2 ^ 1), flagSign bu (b + δ) * flagSign b bv : ℤ) : ℝ) : ℝ) :
      ℂ) := by
      have hsq2 : (1 / √(2 : ℝ)) * (1 / √(2 : ℝ)) = 1 / 2 := by
        have h := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2); field_simp; linarith
      simp only [h1, ↓reduceIte, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Int.cast_sum,
        Int.cast_mul, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun b _ ↦ ?_
      linear_combination (flagSign bu (b + δ) : ℝ) * (flagSign b bv : ℝ) * hsq2
    have hfs : ∀ d b₁ b₂ : Fin (2 ^ 1), (∑ b : Fin (2 ^ 1), flagSign b₁ (b + d) * flagSign b b₂) =
      if b₁ = b₂ then (if d = 1 ∧ b₁ = 0 then -2 else 2) else 0 := by
      intro d b₁ b₂
      rw [show (∑ b : Fin (2 ^ 1), flagSign b₁ (b + d) * flagSign b b₂) =
          flagSign b₁ (0 + d) * flagSign 0 b₂ + flagSign b₁ (1 + d) * flagSign 1 b₂
          from Fin.sum_univ_two fun b : Fin 2 ↦ flagSign b₁ (b + d) * flagSign b b₂]
      fin_cases d <;> fin_cases b₁ <;> fin_cases b₂ <;> rfl
    rw [hsm, hfs]; by_cases hb : bu = bv
    · have huv : u = v := (splitBasisEquiv n 1).injective (Prod.ext h1 hb); subst huv
      rw [ite_eq_left rfl, Matrix.diagonal_apply_eq, slotDiag,
        ← splitBasisEquiv_fst_eq_localIdxReg, ← splitBasisEquiv_snd_eq_localMarkerReg]
      have hPδ : (xu ∈ A ∧ bu = 0) ↔ (δ = 1 ∧ bu = 0) := (by by_cases hA : xu ∈ A <;> simp [δ, hA])
      change (((1 / 2 : ℝ) * ((if δ = 1 ∧ bu = 0 then (-2 : ℤ) else 2 : ℤ) : ℝ) : ℝ) : ℂ) =
        if xu ∈ A ∧ bu = 0 then (-1 : ℂ) else 1
      rw [if_congr hPδ rfl rfl]; by_cases hδ : δ = 1 ∧ bu = 0 <;> simp [hδ]
    · have huv : u ≠ v := fun huv ↦ hb (congrArg (fun z ↦ (splitBasisEquiv n 1 z).2) huv)
      rw [ite_eq_right hb, Matrix.diagonal_apply_ne _ huv]; simp
  · have huv : u ≠ v := fun huv ↦ h1 (congrArg (fun z ↦ (splitBasisEquiv n 1 z).1) huv)
    rw [Matrix.diagonal_apply_ne _ huv]
    exact Finset.sum_eq_zero fun b _ ↦ by rw [ite_eq_right h1, mul_zero]
noncomputable def flagWUnitary (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  ⟨flagWMat n, by
    have h0 := flagWMat_conj_setMarkingOracle n ∅
    have hO : (setMarkingOracle (∅ : Finset (Fin (2 ^ n)))).1 = 1 := by
      ext i j
      rw [setMarkingOracle, permutationUnitary_apply, Matrix.one_apply]
      have hid : slotMarkPerm (∅ : Finset (Fin (2 ^ n))) j = j :=
        (splitBasisEquiv n 1).injective (by simp [slotMarkPerm, tableAddPerm, addRightShear])
      rw [hid]
    have hcj : (flagWMat n)ᴴ = flagWMat n := by
      ext u v
      dsimp only [Matrix.conjTranspose_apply, flagWMat]
      by_cases h : (splitBasisEquiv n 1 u).1 = (splitBasisEquiv n 1 v).1
      · rw [ite_eq_left h.symm, ite_eq_left h]
        have hsym : ∀ a b : Fin (2 ^ 1), flagSign a b = flagSign b a := fun a b ↦ by
          simp only [flagSign, and_comm]
        rw [hsym]
        simp
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_zero]
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hcj]
    have hdiag : Matrix.diagonal (slotDiag n ∅) = 1 := by
      ext i j
      simp [slotDiag, Matrix.diagonal_apply, Matrix.one_apply]
    rw [hO, mul_one, hdiag] at h0
    exact h0⟩
/-- `m`-slot product of `flagWUnitary n` on `(n + 1) * m` wires. -/
noncomputable def flagConj (n m : ℕ) : Unitary (2 ^ ((n + 1) * m)) :=
  ((List.finRange m).map fun i ↦ (localSlotReg n m i).embedUnitary (flagWUnitary n)).prod
theorem isRealMatrix_flagConj (n m : ℕ) : IsRealMatrix (flagConj n m).1 := by
  refine isRealMatrix_listProd _ ?_
  intro U hU; rw [List.mem_map] at hU; obtain ⟨i, _, rfl⟩ := hU
  exact isRealMatrix_embedMatrix _ (isRealMatrix_flagWMat n)
/-- Product diagonal matrix `∏_{i < m} slotDiag n A (slot_i z)` on `(n + 1) * m` wires. -/
def sDiagM (n m : ℕ) (A : Finset (Fin (2 ^ n))) : Operator (2 ^ ((n + 1) * m)) :=
  Matrix.diagonal fun z ↦ ∏ i : Fin m, slotDiag n A ((localSlotReg n m i).extractIndex z)
theorem sDiagM_conjTranspose (n m : ℕ) (A : Finset (Fin (2 ^ n))) :
    (sDiagM n m A)ᴴ = sDiagM n m A := by
  rw [sDiagM, Matrix.diagonal_conjTranspose]; congr 1; funext z; rw [Pi.star_apply, star_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  unfold slotDiag; split_ifs <;> simp
theorem flagConj_mul_parallelMarkingOracle_mul_flagConj (n m : ℕ) (A : Finset (Fin (2 ^ n))) :
    (flagConj n m).1 * (parallelMarkingOracle m A).1 * (flagConj n m).1 = sDiagM n m A := by
  let emb (B : Operator (2 ^ (n + 1))) (l : List (Fin m)) : Operator (2 ^ ((n + 1) * m)) :=
    (l.map fun i ↦ (localSlotReg n m i).embedMatrix B).prod
  have hF : (flagConj n m).1 = emb (flagWMat n) (List.finRange m) := by
    rw [flagConj, Submonoid.coe_list_prod, List.map_map]; rfl
  have hO : (parallelMarkingOracle m A).1 = emb (setMarkingOracle A).1 (List.finRange m) := by
    rw [parallelMarkingOracle, List.ofFn_eq_map, Submonoid.coe_list_prod, List.map_map]; rfl
  have epc {i : Fin m} {l : List (Fin m)} (hi : i ∉ l) (B₁ B₂ : Operator (2 ^ (n + 1))) :
      (localSlotReg n m i).embedMatrix B₁ * emb B₂ l =
        emb B₂ l * (localSlotReg n m i).embedMatrix B₁ := by
    induction l with
    | nil => simp [emb]
    | cons j l ih =>
        simp only [List.mem_cons, not_or] at hi; dsimp only [emb] at *
        simp only [List.map_cons, List.prod_cons]
        rw [← Matrix.mul_assoc, QRegister.embedMatrix_comm_of_disjoint _ _ (localSlotReg_disjoint
          hi.1), Matrix.mul_assoc, ih hi.2, ← Matrix.mul_assoc]
  have epm {l : List (Fin m)} (hl : l.Nodup) (B₁ B₂ : Operator (2 ^ (n + 1))) :
      emb B₁ l * emb B₂ l = emb (B₁ * B₂) l := by
    induction l with
    | nil => simp [emb]
    | cons i l ih =>
        rcases List.nodup_cons.mp hl with ⟨hil, hl'⟩; dsimp only [emb] at *
        simp only [List.map_cons, List.prod_cons]
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (l.map _).prod, ← epc hil B₂ B₁,
          Matrix.mul_assoc, ← Matrix.mul_assoc ((localSlotReg n m i).embedMatrix B₁),
          ← QRegister.embedMatrix_mul, ih hl']
  have epd (l : List (Fin m)) : emb (Matrix.diagonal (slotDiag n A)) l = Matrix.diagonal fun z ↦
    (l.map fun i ↦ slotDiag n A ((localSlotReg n m i).extractIndex z)).prod := by
    induction l with
    | nil => simp [emb, Matrix.diagonal_one]
    | cons i l ih =>
        dsimp only [emb] at *
        simp only [List.map_cons, List.prod_cons]
        rw [QRegister.embedMatrix_diagonal, ih, Matrix.diagonal_mul_diagonal]
  have hnd := List.nodup_finRange m
  rw [hF, hO, epm hnd, epm hnd, flagWMat_conj_setMarkingOracle n A, epd, sDiagM]
  exact congrArg Matrix.diagonal (funext fun _ ↦ (Fin.prod_univ_def _).symm)
theorem diag_mulVec_localAddr_tensorState {n m : ℕ} (d : Fin (2 ^ ((n + 1) * m)) → ℂ) (c : Fin (2 ^
    (m * n)) → ℂ) (v : Fin (2 ^ (m * n)) → ℂ) (e : (localAddrReg n m).Environment → ZMod 2) (hd : ∀
    z, ((localAddrReg n m).basisSplitEquiv z).2 = e → d z = c ((localAddrReg n m).extractIndex z)) :
    Matrix.diagonal d *ᵥ (localAddrReg n m).tensorState v (Pi.single e 1) = (localAddrReg n
    m).tensorState (fun u ↦ c u * v u) (Pi.single e 1) := by
  funext z; rw [Matrix.mulVec_diagonal]; dsimp only [QRegister.tensorState]
  by_cases h : ((localAddrReg n m).basisSplitEquiv z).2 = e
  · rw [hd z h, h, Pi.single_eq_same, mul_one, mul_one]
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero, mul_zero]
theorem sDiagM_mulVec_env_zero {n m : ℕ} (A : Finset (Fin (2 ^ n))) (v : Fin (2 ^ (m * n)) → ℂ) :
    sDiagM n m A *ᵥ (localAddrReg n m).tensorState v (Pi.single 0 1) = (localAddrReg n
    m).tensorState (setOracleMatrix (oddSet n m A) *ᵥ v) (Pi.single 0 1) := by
  rw [sDiagM, diag_mulVec_localAddr_tensorState _ (fun u ↦ if u ∈ oddSet n m A then -1 else 1) v 0]
  · congr 1; funext u; rw [setOracleMatrix, Matrix.mulVec_diagonal]
  · intro z hE
    have hf (i : Fin m) : slotDiag n A ((localSlotReg n m i).extractIndex z) = ((if addrEquiv n m
      ((localAddrReg n m).extractIndex z) i ∈ A then (-1 : ℤ) else 1 : ℤ) : ℂ) := by
      change (if localSlotAddr n m z i ∈ A ∧ localSlotFlag n m z i = 0 then (-1 : ℂ) else 1) = _
      rw [← addrEquiv_extractIndex_localAddrReg n m z i, localSlotFlag_of_env_zero z hE i]
      split_ifs <;> simp_all
    simp_rw [hf, ← Int.cast_prod]; simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases prod_ite_neg_one_or_one Finset.univ
      (fun i : Fin m ↦ addrEquiv n m ((localAddrReg n m).extractIndex z) i ∈ A) with h | h <;>
      rw [h] <;> norm_num
theorem sDiagM_mulVec_env_one {n m : ℕ} (A : Finset (Fin (2 ^ n))) (v : Fin (2 ^ (m * n)) → ℂ) :
    sDiagM n m A *ᵥ (localAddrReg n m).tensorState v (Pi.single 1 1) = (localAddrReg n
    m).tensorState v (Pi.single 1 1) := by
  rw [sDiagM, diag_mulVec_localAddr_tensorState _ (fun _ ↦ 1) v 1]
  · simp only [one_mul]
  · intro z hE; refine Finset.prod_eq_one fun i _ ↦ ?_
    change (if localSlotAddr n m z i ∈ A ∧ localSlotFlag n m z i = 0 then (-1 : ℂ) else 1) = 1
    rw [localSlotFlag_of_env_one z hE i]
    exact ite_eq_right fun h ↦ (fun h0 : (1 : Fin (2 ^ 1)) = 0 ↦ nomatch h0) h.2
/-- Collective bit-flip permutation on all `m` marker wires `(localAddrReg n
  m).Environment`. -/
noncomputable def flipPerm (n m : ℕ) : Equiv.Perm (Fin (2 ^ ((n + 1) * m))) :=
  (localAddrReg n m).basisSplitEquiv.trans <|
    (Equiv.prodCongr (.refl _) (Equiv.addRight 1)).trans
      (localAddrReg n m).basisSplitEquiv.symm
@[simp]
theorem localEnv_one_add_one {n m : ℕ} : (1 : (localAddrReg n m).Environment → ZMod 2) + 1 = 0 :=
  funext fun _ ↦ CharTwo.add_self_eq_zero (1 : ZMod 2)
@[simp] theorem localEnv_add_two {n m : ℕ} (e : (localAddrReg n m).Environment → ZMod 2) :
    e + 1 + 1 = e := by rw [add_assoc, localEnv_one_add_one, add_zero]
@[simp] theorem basisSplitEquiv_flipPerm (n m : ℕ) (z : Fin (2 ^ ((n + 1) * m))) :
    (localAddrReg n m).basisSplitEquiv (flipPerm n m z) =
      (((localAddrReg n m).basisSplitEquiv z).1, ((localAddrReg n m).basisSplitEquiv z).2 + 1) := by
  unfold flipPerm
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply, Equiv.coe_refl,
    Equiv.coe_addRight]; rfl
theorem flipPerm_involutive (n m : ℕ) : Function.Involutive (flipPerm n m) :=
  fun z ↦ (localAddrReg n m).basisSplitEquiv.injective <| by
    rw [basisSplitEquiv_flipPerm, basisSplitEquiv_flipPerm]
    exact Prod.ext rfl (localEnv_add_two _)
noncomputable def flipMat (n m : ℕ) : Operator (2 ^ ((n + 1) * m)) :=
  (permutationUnitary (flipPerm n m)).1
def flag0ZMat (n m : ℕ) (hm : 1 ≤ m) : Operator (2 ^ ((n + 1) * m)) :=
  Matrix.diagonal fun z ↦ if localSlotFlag n m z ⟨0, hm⟩ = 0 then (1 : ℂ) else -1
theorem flipMat_mulVec_tensorState {n m : ℕ} (v : Fin (2 ^ (m * n)) → ℂ) (e : (localAddrReg n
    m).Environment → ZMod 2) : flipMat n m *ᵥ (localAddrReg n m).tensorState v (Pi.single e 1) =
    (localAddrReg n m).tensorState v (Pi.single (e + 1) 1) := by
  funext z
  change (Equiv.Perm.permMatrix ℂ (flipPerm n m)⁻¹ *ᵥ
    (localAddrReg n m).tensorState v (Pi.single e 1)) z = _
  rw [Matrix.permMatrix_mulVec, Function.comp_apply,
    show (flipPerm n m)⁻¹ z = flipPerm n m z by
      simpa [Equiv.symm_apply_eq] using (flipPerm_involutive n m z).symm]
  dsimp only [QRegister.tensorState]
  rw [← QRegister.basisSplitEquiv_apply_fst, basisSplitEquiv_flipPerm,
    QRegister.basisSplitEquiv_apply_fst]
  dsimp only; by_cases h : ((localAddrReg n m).basisSplitEquiv z).2 = e + 1
  · rw [show ((localAddrReg n m).basisSplitEquiv z).2 + 1 = e by rw [h, localEnv_add_two], h,
      Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (show ((localAddrReg n m).basisSplitEquiv z).2 + 1 ≠ e from
      fun h' ↦ h (by rw [← h', localEnv_add_two])), Pi.single_eq_of_ne h, mul_zero]
/-- Cosine weight `√((1 + clamp s) / 2)` for the parametric weak-measurement reflection. -/
noncomputable def chordCos (s : ℝ) : ℝ := √((1 + max 0 (min 1 s)) / 2)
/-- Sine weight `√((1 - clamp s) / 2)` for the parametric weak-measurement reflection. -/
noncomputable def chordSin (s : ℝ) : ℝ := √((1 - max 0 (min 1 s)) / 2)
theorem chordCos_sq_add_chordSin_sq (s : ℝ) : chordCos s ^ 2 + chordSin s ^ 2 = 1 := by
  set s' := max 0 (min 1 s); have hs0 : 0 ≤ s' := le_max_left 0 _
  have hs1 : s' ≤ 1 := max_le zero_le_one (min_le_left 1 _)
  rw [chordCos, chordSin, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]; ring
theorem chordSin_sq_sub_chordCos_sq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    chordSin s ^ 2 - chordCos s ^ 2 = -s := by
  have hclamp : max 0 (min 1 s) = s := (by rw [min_eq_right hs1, max_eq_right hs0])
  rw [chordCos, chordSin, hclamp, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]; ring
/-- Parametric weak-measurement unitary matrix
  `chordCos s • Z_{flag_0} + chordSin s • X_{flags}`. -/
noncomputable def chordMat (n m : ℕ) (hm : 1 ≤ m) (s : ℝ) : Operator (2 ^ ((n + 1) * m)) :=
  (chordCos s : ℂ) • flag0ZMat n m hm + (chordSin s : ℂ) • flipMat n m
theorem isRealMatrix_chordMat (n m : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    IsRealMatrix (chordMat n m hm s) := by
  intro a b
  rw [chordMat, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  have hZ : (flag0ZMat n m hm a b).im = 0 := by
    rw [flag0ZMat]; by_cases hab : a = b
    · subst hab; rw [Matrix.diagonal_apply_eq]; split_ifs <;> simp
    · rw [Matrix.diagonal_apply_ne _ hab]; simp
  have hX : (flipMat n m a b).im = 0 := isRealMatrix_permutationUnitary (flipPerm n m) a b
  simp [Complex.add_im, Complex.mul_im, hZ, hX]
noncomputable def chordUnitary (n m : ℕ) (hm : 1 ≤ m) (s : ℝ) : Unitary (2 ^ ((n + 1) * m)) :=
  ⟨chordMat n m hm s, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    unfold chordMat
    set Z := flag0ZMat n m hm
    set X := flipMat n m
    set u := chordCos s
    set v := chordSin s
    have hZc : Zᴴ = Z := by
      dsimp only [Z, flag0ZMat]
      rw [Matrix.diagonal_conjTranspose]
      refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
      by_cases h : localSlotFlag n m z ⟨0, hm⟩ = 0 <;> simp [h]
    have hZX : Z * X + X * Z = 0 := by
      ext i j
      simp only [Z, X, flag0ZMat, flipMat, Matrix.add_apply, Matrix.diagonal_mul,
        Matrix.mul_diagonal, Matrix.zero_apply, permutationUnitary_apply]
      by_cases hij : i = flipPerm n m j
      · subst hij
        have h0 : ∀ b : Fin (2 ^ 1), b = 0 ↔ basisBits 1 b 0 = 0 := fun b ↦
          ⟨fun hb ↦ by rw [hb, basisBits_zero, Pi.zero_apply], fun hb ↦
            (basisBits 1).injective (funext fun i ↦ by
              rw [Subsingleton.elim i 0, hb, basisBits_zero, Pi.zero_apply])⟩
        have hf : localSlotFlag n m (flipPerm n m j) ⟨0, hm⟩ = 0 ↔
            localSlotFlag n m j ⟨0, hm⟩ ≠ 0 := by
          rw [h0, Ne, h0, basisBits_localSlotFlag, basisBits_localSlotFlag,
            basisSplitEquiv_flipPerm]
          have hz2 : ∀ b : ZMod 2, b + 1 = 0 ↔ b ≠ 0 := fun b ↦ by
            by_cases hb : b = 0
            · subst hb; simp
            · refine ⟨fun _ ↦ hb, fun _ ↦ ?_⟩
              have hv1 : b.val = 1 := by
                have hlt : b.val < 2 := b.val_lt
                have hne0 : b.val ≠ 0 := fun hz ↦
                  hb (by rw [← ZMod.natCast_zmod_val b, hz]; simp)
                omega
              have hb1 : b = 1 := by rw [← ZMod.natCast_zmod_val b, hv1, Nat.cast_one]
              rw [hb1]; exact CharTwo.add_self_eq_zero (1 : ZMod 2)
          exact hz2 _
        by_cases h : localSlotFlag n m j ⟨0, hm⟩ = 0 <;> simp [hf, h]
      · simp [hij]
    have hXc : Xᴴ = X := by
      ext i j
      simp only [X, flipMat, Matrix.conjTranspose_apply, permutationUnitary_apply]
      by_cases h : i = flipPerm n m j
      · rw [ite_eq_left (by rw [h, flipPerm_involutive n m j]), ite_eq_left h, star_one]
      · rw [ite_eq_right fun h' ↦ h (by rw [h', flipPerm_involutive n m i]),
          ite_eq_right h, star_zero]
    have hZ2 : Z * Z = 1 := by
      dsimp only [Z, flag0ZMat]
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      exact congrArg Matrix.diagonal (funext fun _ ↦ by split_ifs <;> ring)
    have hX2 : X * X = 1 := by
      nth_rw 1 [← hXc]
      rw [← Matrix.star_eq_conjTranspose]
      exact (permutationUnitary (flipPerm n m)).2.1
    have hcj : ((u : ℂ) • Z + (v : ℂ) • X)ᴴ = (u : ℂ) • Z + (v : ℂ) • X := by
      simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hZc, hXc]
    have hsq : ((u : ℂ) • Z + (v : ℂ) • X) * ((u : ℂ) • Z + (v : ℂ) • X) =
        ((u : ℂ) * u + (v : ℂ) * v) • 1 + ((u : ℂ) * v) • (Z * X + X * Z) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        hZ2, hX2, add_smul, smul_add, mul_comm (v : ℂ) (u : ℂ)]
      abel
    have huv : (u : ℂ) * u + (v : ℂ) * v = 1 := by
      have hreal := chordCos_sq_add_chordSin_sq s
      exact_mod_cast (by linear_combination hreal : u * u + v * v = 1)
    rw [hcj, hsq, hZX, smul_zero, add_zero, huv, one_smul]⟩
/-- Hit-branch (`o = 1`) local address state supported exclusively on `M0 = oddSet n m A`. -/
noncomputable def pinHitVec {q : ℕ} (M0 : Finset (Fin (2 ^ q))) (s : ℝ)
    (w : Fin (2 ^ q) → ℂ) (u : Fin (2 ^ q)) : ℂ :=
  if u ∈ M0 then ((-2 * chordCos s * chordSin s : ℝ) : ℂ) * w u else 0
theorem parityMat_mulVec_zero {n m : ℕ} (hm : 1 ≤ m) (A : Finset (Fin (2 ^ n))) {s : ℝ} (hs0 : 0 ≤
    s) (hs1 : s ≤ 1) (w : Fin (2 ^ (m * n)) → ℂ) : (chordMat n m hm s * sDiagM n m A * chordMat n m
    hm s) *ᵥ (localAddrReg n m).tensorState w (Pi.single 0 1) = (localAddrReg n m).tensorState
    (lockSetKraus0 (oddSet n m A) s *ᵥ w) (Pi.single 0 1) + (localAddrReg n m).tensorState
    (pinHitVec (oddSet n m A) s w) (Pi.single 1 1) := by
  let reg := localAddrReg n m
  have hch (v : Fin (2 ^ (m * n)) → ℂ) (e : reg.Environment → ZMod 2) (b : Fin (2 ^ 1)) (hs : ∀ z,
    (reg.basisSplitEquiv z).2 = e → localSlotFlag n m z ⟨0, hm⟩ = b) : chordMat n m hm s *ᵥ
    reg.tensorState v (Pi.single e 1) = reg.tensorState (((chordCos s : ℂ) * if b = 0 then 1 else
    -1) • v) (Pi.single e 1) + reg.tensorState ((chordSin s : ℂ) • v) (Pi.single (e + 1) 1) := by
    let sgn : ℂ := if b = 0 then 1 else -1
    rw [chordMat, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, flag0ZMat,
      diag_mulVec_localAddr_tensorState _ (fun _ ↦ sgn) v e (fun z hz ↦ by
        dsimp only [sgn]; rw [hs z hz]),
      show (fun u ↦ sgn * v u) = sgn • v from rfl,
      flipMat_mulVec_tensorState v e,
      ← reg.tensorState_smul_left, ← reg.tensorState_smul_left, smul_smul]
  have hs_e0 := fun z hE ↦ localSlotFlag_of_env_zero (n := n) z hE ⟨0, hm⟩
  have hs_e1 := fun z hE ↦ localSlotFlag_of_env_one (n := n) z hE ⟨0, hm⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hch w 0 0 hs_e0, ite_eq_left rfl, mul_one,
    zero_add, Matrix.mulVec_add, sDiagM_mulVec_env_zero A _, sDiagM_mulVec_env_one A _,
    Matrix.mulVec_add, hch _ 0 0 hs_e0, ite_eq_left rfl, zero_add, hch _ 1 1 hs_e1, ite_eq_right
    (fun h0 : (1 : Fin (2 ^ 1)) = 0 ↦ nomatch h0), localEnv_one_add_one]
  have hdiff := chordSin_sq_sub_chordCos_sq hs0 hs1; have hsum := chordCos_sq_add_chordSin_sq s
  funext z
  simp only [reg, Pi.add_apply, QRegister.tensorState, Pi.smul_apply, Matrix.mulVec_smul,
    smul_eq_mul, setOracleMatrix_mulVec, lockSetKraus0, Matrix.mulVec_diagonal, pinHitVec]
  by_cases hu : (localAddrReg n m).extractIndex z ∈ oddSet n m A
  · simp only [hu, ↓reduceIte]
    have h1 : (-(chordCos s : ℂ) ^ 2 + (chordSin s : ℂ) ^ 2) = (-s : ℂ) := by
      have h := congrArg Complex.ofReal hdiff; push_cast at h ⊢; linear_combination h
    have h2 : ((-2 * chordCos s * chordSin s : ℝ) : ℂ) =
        -((chordCos s : ℂ) * (chordSin s : ℂ)) - (chordSin s : ℂ) * (chordCos s : ℂ) := by
      push_cast; ring
    rw [h2]; by_cases hE : ((localAddrReg n m).basisSplitEquiv z).2 = 0
    · simp only [hE, Pi.single_eq_same, mul_one]
      linear_combination w ((localAddrReg n m).extractIndex z) * h1
    · simp only [Pi.single_eq_of_ne hE, mul_zero]; ring
  · simp only [hu, ↓reduceIte]
    have h1 : ((chordCos s : ℂ) ^ 2 + (chordSin s : ℂ) ^ 2) = 1 := by
      have h := congrArg Complex.ofReal hsum; push_cast at h ⊢; linear_combination h
    by_cases hE : ((localAddrReg n m).basisSplitEquiv z).2 = 0
    · simp only [hE, Pi.single_eq_same, mul_one]
      linear_combination w ((localAddrReg n m).extractIndex z) * h1
    · simp only [Pi.single_eq_of_ne hE, mul_zero]; ring
theorem localFlagReg0_split {n m : ℕ} (hm : 1 ≤ m) (v₀ v₁ : Fin (2 ^ (m * n)) → ℂ) :
    let r := localAddrReg n m
    let ψ := r.tensorState v₀ (Pi.single 0 1) + r.tensorState v₁ (Pi.single 1 1)
    (localFlagReg n m ⟨0, hm⟩).basisOutcomeProjector 0 *ᵥ ψ = r.tensorState v₀ (Pi.single 0 1) ∧
      (localFlagReg n m ⟨0, hm⟩).basisOutcomeProjector 1 *ᵥ ψ =
        r.tensorState v₁ (Pi.single 1 1) := by
  intro r ψ; have hfl (z : Fin (2 ^ ((n + 1) * m))) :
      (localFlagReg n m ⟨0, hm⟩).extractIndex z = localSlotFlag n m z ⟨0, hm⟩ := by
    rw [localFlagReg, QRegister.extractIndex_compose]; rfl
  have h0 : (localFlagReg n m ⟨0, hm⟩).basisOutcomeProjector 0 *ᵥ ψ =
      r.tensorState v₀ (Pi.single 0 1) := by
    dsimp only [r, ψ]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec_add,
      diag_mulVec_localAddr_tensorState _ (fun _ ↦ 1) v₀ 0 (fun z hz ↦ by
        rw [hfl z, localSlotFlag_of_env_zero z hz ⟨0, hm⟩, ite_eq_left rfl]),
      diag_mulVec_localAddr_tensorState _ (fun _ ↦ 0) v₁ 1 (fun z hz ↦ by
        rw [hfl z, localSlotFlag_of_env_one z hz ⟨0, hm⟩,
          ite_eq_right (fun h0 : (1 : Fin (2 ^ 1)) = 0 ↦ nomatch h0)])]
    simp only [one_mul, zero_mul, Pi.zero_def.symm, (localAddrReg n m).tensorState_zero_left,
      add_zero]
  refine ⟨h0, add_left_cancel (a := r.tensorState v₀ (Pi.single 0 1)) ?_⟩
  nth_rw 1 [← h0]; have hsum : (localFlagReg n m ⟨0, hm⟩).basisOutcomeProjector 0 +
      (localFlagReg n m ⟨0, hm⟩).basisOutcomeProjector 1 = 1 := by
    simpa [Fin.sum_univ_two] using (localFlagReg n m ⟨0, hm⟩).sum_basisOutcomeProjector
  rw [← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
theorem sum_normSq_tensorState_single {W Q : ℕ} (r : QRegister W Q) (v : Fin (2 ^ W) → ℂ) (e :
    r.Environment → ZMod 2) : ∑ z : Fin (2 ^ Q), Complex.normSq (r.tensorState v (Pi.single e 1) z)
    = ∑ u : Fin (2 ^ W), Complex.normSq (v u) := by
  rw [← r.basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Fintype.sum_eq_single e]
  · simp [QRegister.tensorState, ← QRegister.basisSplitEquiv_apply_fst]
  · intro e' he'; simp [QRegister.tensorState, Pi.single_eq_of_ne he']
theorem sum_normSq_setOracleMatrix_mulVec {q : ℕ} (M0 : Finset (Fin (2 ^ q))) (v : Fin (2 ^ q) → ℂ)
    : ∑ u : Fin (2 ^ q), Complex.normSq ((setOracleMatrix M0 *ᵥ v) u) = ∑ u : Fin (2 ^ q),
    Complex.normSq (v u) := by
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [setOracleMatrix_mulVec]; split_ifs <;> simp
/-- Local `(n + 1) * m`-wire vector after loop exit (`o = 1`), `flipPerm`, and one unmarked
  verification call `parallelMarkingOracle m A`. -/
noncomputable def exitLocalVec (n m : ℕ) (A : Finset (Fin (2 ^ n))) (s : ℝ) (K : ℕ) :
    Fin (2 ^ ((n + 1) * m)) → ℂ :=
  let M0 := oddSet n m A
  (parallelMarkingOracle m A).1 *ᵥ
    (localAddrReg n m).tensorState (pinHitVec M0 s (groverSetState M0 (K + 1))) (Pi.single 0 1)
theorem sum_normSq_exitLocalVec {n m : ℕ} (hm : 1 ≤ m) (A : Finset (Fin (2 ^ n)))
    (hc1 : 1 ≤ (oddSet n m A).card) (hcN : (oddSet n m A).card < 2 ^ (m * n)) (K : ℕ)
    (hsin : Real.sin ((2 * (K : ℝ) + 3) * halfAngleSet (m * n) (oddSet n m A).card) ≠ 0)
    (hcos : Real.cos ((2 * (K : ℝ) + 1) * halfAngleSet (m * n) (oddSet n m A).card) ≠ 0)
    (hs0 : 0 ≤ targetAngleRatio (halfAngleSet (m * n) (oddSet n m A).card) K)
    (hs1 : targetAngleRatio (halfAngleSet (m * n) (oddSet n m A).card) K ≤ 1) :
    let θ := halfAngleSet (m * n) (oddSet n m A).card; let s := targetAngleRatio θ K
    ∑ o : Fin (2 ^ ((n + 1) * m)), Complex.normSq (exitLocalVec n m A s K o) =
      1 - nonTargetAngleRatio θ K ^ 2 := by
  intro θ s; let M0 := oddSet n m A; let α := nonTargetAngleRatio θ K
  let vK := setOracleMatrix M0 *ᵥ groverSetState M0 K
  let hA := pinHitVec M0 s (groverSetState M0 (K + 1))
  let φ0 := (localAddrReg n m).tensorState vK (Pi.single 0 1)
  let Uloc : Unitary (2 ^ ((n + 1) * m)) := chordUnitary n m hm s * flagConj n m *
    parallelMarkingOracle m A * flagConj n m * chordUnitary n m hm s * (localAddrReg n
    m).embedUnitary (Grover.diffuserUnitary (n := m * n))
  have hUloc_mat : Uloc.1 = (chordMat n m hm s * sDiagM n m A * chordMat n m hm s) * ((localAddrReg
    n m).embedMatrix (Grover.diffuserMatrix (n := m * n))) := by
    have hpar : (flagConj n m * parallelMarkingOracle m A * flagConj n m).1 = sDiagM n m A := by
      simp only [Submonoid.coe_mul, flagConj_mul_parallelMarkingOracle_mul_flagConj]
    simp only [Uloc, Submonoid.coe_mul, chordUnitary, QRegister.embedUnitary_val,
      Grover.diffuserUnitary_coe]
    calc chordMat n m hm s * (flagConj n m).1 * (parallelMarkingOracle m A).1 * (flagConj n m).1 *
          chordMat n m hm s * (localAddrReg n m).embedMatrix (Grover.diffuserMatrix (n := m * n)) =
          (chordMat n m hm s * ((flagConj n m).1 * (parallelMarkingOracle m A).1 * (flagConj n
          m).1) * chordMat n m hm s) * (localAddrReg n m).embedMatrix (Grover.diffuserMatrix (n :=
          m * n)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Submonoid.coe_mul, ← Submonoid.coe_mul, hpar]
  have hUloc_vec : Uloc.1 *ᵥ φ0 = (localAddrReg n m).tensorState ((α : ℂ) • vK) (Pi.single 0 1) +
    (localAddrReg n m).tensorState hA (Pi.single 1 1) := by
    rw [hUloc_mat, ← Matrix.mulVec_mulVec, (localAddrReg n m).embedMatrix_mulVec_tensorState, show
      Grover.diffuserMatrix *ᵥ vK = groverSetState M0 (K + 1) from rfl, parityMat_mulVec_zero hm A
      hs0 hs1, lockSetKraus0_mulVec_groverSetState M0 hc1 hcN K hsin hcos]
  have hnorm_φ0 : ∑ z : Fin (2 ^ ((n + 1) * m)), Complex.normSq (φ0 z) = 1 := by
    rw [sum_normSq_tensorState_single, sum_normSq_setOracleMatrix_mulVec,
      sum_normSq_groverSetState_univ]
  have hnorm_U : ∑ z : Fin (2 ^ ((n + 1) * m)), Complex.normSq ((Uloc.1 *ᵥ φ0) z) = 1 := by
    rw [sum_normSq_unitary_mulVec Uloc φ0, hnorm_φ0]
  have henv_ne : (0 : (localAddrReg n m).Environment → ZMod 2) ≠ 1 := by
    intro heq; have h01 := congrFun heq (localFlagEnvWire n m ⟨0, hm⟩); exact zero_ne_one h01
  have hpt (z : Fin (2 ^ ((n + 1) * m))) : Complex.normSq (((localAddrReg n m).tensorState ((α : ℂ)
    • vK) (Pi.single 0 1) + (localAddrReg n m).tensorState hA (Pi.single 1 1)) z) = Complex.normSq
    ((localAddrReg n m).tensorState ((α : ℂ) • vK) (Pi.single 0 1) z) + Complex.normSq
    ((localAddrReg n m).tensorState hA (Pi.single 1 1) z) := by
    simp only [Pi.add_apply, QRegister.tensorState]
    by_cases h0 : ((localAddrReg n m).basisSplitEquiv z).2 = 0
    · simp [h0, Pi.single_eq_of_ne henv_ne]
    · simp [Pi.single_eq_of_ne h0]
  rw [hUloc_vec] at hnorm_U; simp_rw [hpt] at hnorm_U
  rw [Finset.sum_add_distrib, sum_normSq_tensorState_single,
    sum_normSq_tensorState_single] at hnorm_U
  have hα_sum : ∑ u : Fin (2 ^ (m * n)), Complex.normSq (((α : ℂ) • vK) u) = α ^ 2 := by
    have hterm : ∀ u : Fin (2 ^ (m * n)),
        Complex.normSq (((α : ℂ) • vK) u) = α ^ 2 * Complex.normSq (vK u) := by
      intro u; simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.normSq_ofReal, sq]
    simp_rw [hterm]
    rw [← Finset.mul_sum, sum_normSq_setOracleMatrix_mulVec,
      sum_normSq_groverSetState_univ, mul_one]
  rw [hα_sum] at hnorm_U
  rw [exitLocalVec, sum_normSq_unitary_mulVec (parallelMarkingOracle m A),
    sum_normSq_tensorState_single]; linarith
/-- Iterated slot-wise marking permutation over `localSlotReg` wires. -/
noncomputable def localAppMark (n m : ℕ) (A : Finset (Fin (2 ^ n))) :
    List (Fin m) → Fin (2 ^ ((n + 1) * m)) → Fin (2 ^ ((n + 1) * m))
  | [], z => z
  | i :: rest, z =>
      let acc := localAppMark n m A rest z
      (localSlotReg n m i).replaceIndex acc
        (slotMarkPerm A ((localSlotReg n m i).extractIndex acc))
theorem parallelMarkingOracle_mulVec_single_local (n m : ℕ) (A : Finset (Fin (2 ^ n))) (z : Fin (2 ^
    ((n + 1) * m))) : (parallelMarkingOracle m A).1 *ᵥ Pi.single z (1 : ℂ) = Pi.single (localAppMark
    n m A (List.finRange m) z) 1 := by
  have hL (l : List (Fin m)) : ((l.map fun i ↦ (localSlotReg n m i).embedMatrix (setMarkingOracle
    A).1).prod) *ᵥ Pi.single z (1 : ℂ) = Pi.single (localAppMark n m A l z) 1 := by
    induction l with
    | nil => exact Matrix.one_mulVec _
    | cons i rest ih =>
        rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, (localSlotReg n m
          i).embedMatrix_mulVec_single_factors, setMarkingOracle, permutationUnitary_mulVec_single,
          (localSlotReg n m i).tensorState_single_replaceIndex]; rfl
  have hO : (parallelMarkingOracle m A).1 = ((List.finRange m).map fun i ↦ (localSlotReg n m
    i).embedMatrix (setMarkingOracle A).1).prod := by
    rw [parallelMarkingOracle, List.ofFn_eq_map, Submonoid.coe_list_prod, List.map_map]; rfl
  rw [hO, hL]
theorem extractIndex_localSlotReg_localAppMark (n m : ℕ) (A : Finset (Fin (2 ^ n))) (l : List (Fin
    m)) (hl : l.Nodup) (z : Fin (2 ^ ((n + 1) * m))) (j : Fin m) : (localSlotReg n m j).extractIndex
    (localAppMark n m A l z) = if j ∈ l then slotMarkPerm A ((localSlotReg n m j).extractIndex z)
    else (localSlotReg n m j).extractIndex z := by
  induction l with
  | nil => simp [localAppMark]
  | cons i rest ih =>
      rcases List.nodup_cons.mp hl with ⟨hi, hrest⟩; rw [localAppMark]; by_cases hji : j = i
      · subst hji
        rw [QRegister.extractIndex_replaceIndex, ih hrest, ite_eq_right hi,
          ite_eq_left List.mem_cons_self]
      · rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint _ (localSlotReg_disjoint
          hji), ih hrest]; simp [List.mem_cons, hji]
theorem localAppMark_involutive (n m : ℕ) (A : Finset (Fin (2 ^ n))) :
    Function.Involutive (localAppMark n m A (List.finRange m)) := by
  intro z; set z₁ := localAppMark n m A (List.finRange m) z
  set z₂ := localAppMark n m A (List.finRange m) z₁; have hslots (j : Fin m) :
      (localSlotReg n m j).extractIndex z₂ = (localSlotReg n m j).extractIndex z := by
    rw [extractIndex_localSlotReg_localAppMark n m A _ (List.nodup_finRange m) z₁ j, ite_eq_left
      (List.mem_finRange j), extractIndex_localSlotReg_localAppMark n m A _ (List.nodup_finRange m)
      z j, ite_eq_left (List.mem_finRange j)]; exact slotMarkPerm_involutive A _
  apply (basisBits ((n + 1) * m)).injective; funext w
  let j : Fin m := ⟨w.val / (n + 1), Nat.div_lt_of_lt_mul (by linarith [w.isLt])⟩
  let r : Fin (n + 1) := ⟨w.val % (n + 1), Nat.mod_lt _ (by omega)⟩
  have hw : w = localSlotReg n m j r := by
    ext; simp only [localSlotReg, QRegister.block_apply_val, j, r]
    linarith [Nat.div_add_mod w.val (n + 1)]
  rw [hw, ← (localSlotReg n m j).basisBits_extractIndex,
    ← (localSlotReg n m j).basisBits_extractIndex, hslots j]
theorem extractMarkedIdx_mem_of_exitLocalVec_ne_zero {n m : ℕ} {A : Finset (Fin (2 ^ n))} {s : ℝ} {K
    : ℕ} {o : Fin (2 ^ ((n + 1) * m))} (hne : exitLocalVec n m A s K o ≠ 0) : (⟨extractMarkedIdx n m
    (o.val : ℤ), extractMarkedIdx_lt n m (o.val : ℤ)⟩ : Fin (2 ^ n)) ∈ A := by
  let φ := (localAddrReg n m).tensorState
    (pinHitVec (oddSet n m A) s (groverSetState (oddSet n m A) (K + 1))) (Pi.single 0 1)
  set z := localAppMark n m A (List.finRange m) o
  have happ : exitLocalVec n m A s K o = φ z := by
    have hdecomp : φ = ∑ x : Fin (2 ^ ((n + 1) * m)), φ x • Pi.single x (1 : ℂ) := by
      funext u; rw [Finset.sum_apply]; simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single u]
      · simp
      · intro x _ hxu; simp [Ne.symm hxu]
      · intro hu; exact (hu (Finset.mem_univ u)).elim
    calc exitLocalVec n m A s K o = ((parallelMarkingOracle m A).1 *ᵥ (∑ x : Fin (2 ^ ((n + 1) *
          m)), φ x • Pi.single x (1 : ℂ))) o := by
          rw [← hdecomp]; rfl
      _ = φ z := by
          rw [Matrix.mulVec_sum]
          simp only [Matrix.mulVec_smul, parallelMarkingOracle_mulVec_single_local,
            Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
          rw [Finset.sum_eq_single z]
          · have hz_eq : o = localAppMark n m A (List.finRange m) z :=
              (localAppMark_involutive n m A o).symm
            simp [hz_eq]
          · intro x _ hxz
            have hne_o : o ≠ localAppMark n m A (List.finRange m) x := fun heq ↦
              hxz (by dsimp only [z]; rw [heq, localAppMark_involutive])
            simp [hne_o]
          · intro hz; exact (hz (Finset.mem_univ z)).elim
  rw [happ] at hne
  have hz_env : ((localAddrReg n m).basisSplitEquiv z).2 = 0 := by
    by_contra hne0
    apply hne; simp [φ, QRegister.tensorState, Pi.single_eq_of_ne hne0]
  have hz_mem : (localAddrReg n m).extractIndex z ∈ oddSet n m A := by
    by_contra hnot
    apply hne; simp [φ, QRegister.tensorState, pinHitVec, hnot]
  have hslots (i : Fin m) : (localSlotReg n m i).extractIndex z = slotMarkPerm A ((localSlotReg n m
    i).extractIndex o) := by
    rw [extractIndex_localSlotReg_localAppMark n m A _ (List.nodup_finRange m) o i]
    simp [List.mem_finRange]
  have haddr_eq (i : Fin m) : localSlotAddr n m z i = localSlotAddr n m o i := by
    simp only [localSlotAddr, hslots i, extractIndex_localIdxReg_slotMarkPerm]
  have hextr_eq : (localAddrReg n m).extractIndex z = (localAddrReg n m).extractIndex o := by
    apply (addrEquiv n m).injective; funext i
    rw [addrEquiv_extractIndex_localAddrReg, addrEquiv_extractIndex_localAddrReg, haddr_eq i]
  rw [hextr_eq] at hz_mem; have hflag_iff (i : Fin m) :
      localSlotFlag n m o i = (if localSlotAddr n m o i ∈ A then 1 else 0) := by
    have hz0 : localSlotFlag n m z i = 0 := localSlotFlag_of_env_zero z hz_env i
    rw [localSlotFlag, hslots i, extractIndex_localMarkerReg_slotMarkPerm] at hz0
    change localSlotFlag n m o i + (if localSlotAddr n m o i ∈ A then 1 else 0) = 0 at hz0
    generalize localSlotFlag n m o i = b at hz0 ⊢
    by_cases hxA : localSlotAddr n m o i ∈ A <;> simp only [hxA, ↓reduceIte] at hz0 ⊢ <;>
      fin_cases b <;> cases hz0 <;> rfl
  have hex_mark : ∃ i : Fin m, localSlotFlag n m o i = 1 := by
    simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz_mem
    by_contra! hall
    have hallA : ∀ i : Fin m, localSlotAddr n m o i ∉ A := by
      intro i hiA; have hf := hflag_iff i; rw [ite_eq_left hiA] at hf; exact hall i hf
    have hprod1 : (∏ i : Fin m,
        if addrEquiv n m ((localAddrReg n m).extractIndex o) i ∈ A then (-1 : ℤ) else 1) = 1 := by
      refine Finset.prod_eq_one fun i _ ↦ ?_
      rw [addrEquiv_extractIndex_localAddrReg]; exact ite_eq_right (hallA i)
    rw [hprod1] at hz_mem; exact nomatch hz_mem
  have hmark : hasMarkedSlotNat n m o.val = true := by
    by_contra hfalse
    simp only [Bool.not_eq_true] at hfalse; obtain ⟨i, hi1⟩ := hex_mark
    have hi0 := (hasMarkedSlotNat_eq_false_iff o).1 hfalse i
    change localSlotFlag n m o i = 0 at hi0; rw [hi0] at hi1; exact zero_ne_one hi1
  unfold hasMarkedSlotNat at hmark; rw [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hmark
  cases hlist : markedSlotsList n m o.val with
  | nil => exact (hmark hlist).elim
  | cons i₀ rest =>
      have hmem : i₀ ∈ markedSlotsList n m o.val := (by rw [hlist]; exact List.mem_cons_self)
      rw [markedSlotsList, List.mem_filter, List.mem_range] at hmem
      let iFin : Fin m := ⟨i₀, hmem.1⟩
      have hb1 : localSlotFlag n m o iFin = 1 := (slotMarkedNat_eq_true_iff o iFin).1 hmem.2
      have hex : extractMarkedIdx n m (o.val : ℤ) = slotIdxNat n o.val i₀ := by
        simp [extractMarkedIdx, Int.toNat_natCast, hlist]
      have hidx : (⟨extractMarkedIdx n m (o.val : ℤ),
            extractMarkedIdx_lt n m (o.val : ℤ)⟩ : Fin (2 ^ n)) = localSlotAddr n m o iFin := by
        ext; dsimp only [localSlotAddr]; rw [hex, slotIdxNat]
        change slotValNat n o.val iFin.val / 2 % 2 ^ n = _
        rw [slotValNat_eq_extractIndex, extractIndex_localIdxReg_eq]
      rw [hidx]; have hf := hflag_iff iFin; rw [hb1] at hf
      by_cases hxA : localSlotAddr n m o iFin ∈ A
      · exact hxA
      · rw [ite_eq_right hxA] at hf; exact (one_ne_zero hf).elim
/-! ## Section 4: Global `liftOracleVec`, `lockStageCircuit`, Correctness & Cost Bounds -/
/-- Lift a local `((n + 1) * m)`-wire state `v` into `findAllQubits n m k` with the
  environment
  bits (memory + zero wire) fixed to those of global basis state `a`. -/
noncomputable def liftOracleVec (n m k : ℕ) (a : Fin (2 ^ findAllQubits n m k))
    (v : Fin (2 ^ ((n + 1) * m)) → ℂ) : Fin (2 ^ findAllQubits n m k) → ℂ :=
  (oracleReg n m k).tensorState v (Pi.single ((oracleReg n m k).basisSplitEquiv a).2 1)
theorem liftOracleVec_single_zero {n m k j : ℕ} {S : Finset (Fin (2 ^ n))}
    {a : Fin (2 ^ findAllQubits n m k)} (ha : ValidStageBasis n m k S j a) :
    liftOracleVec n m k a (Pi.single 0 1) = Pi.single a 1 := by
  rw [liftOracleVec, ← ha.1, (oracleReg n m k).tensorState_single_factors]
theorem embedOracle_mulVec_liftOracleVec (n m k : ℕ) (a : Fin (2 ^ findAllQubits n m k)) (M :
    Operator (2 ^ ((n + 1) * m))) (v : Fin (2 ^ ((n + 1) * m)) → ℂ) : (oracleReg n m k).embedMatrix
    M *ᵥ liftOracleVec n m k a v = liftOracleVec n m k a (M *ᵥ v) :=
  (oracleReg n m k).embedMatrix_mulVec_tensorState M v _
theorem liftOracleVec_smul (n m k : ℕ) (a : Fin (2 ^ findAllQubits n m k)) (c : ℂ) (v : Fin (2 ^
    ((n + 1) * m)) → ℂ) : liftOracleVec n m k a (c • v) = c • liftOracleVec n m k a v :=
  (oracleReg n m k).tensorState_smul_left c v _
theorem liftOracleVec_add (n m k : ℕ) (a : Fin (2 ^ findAllQubits n m k))
    (v₁ v₂ : Fin (2 ^ ((n + 1) * m)) → ℂ) :
    liftOracleVec n m k a (v₁ + v₂) = liftOracleVec n m k a v₁ + liftOracleVec n m k a v₂ := by
  funext z; simp only [liftOracleVec, QRegister.tensorState, Pi.add_apply]; ring
theorem effectiveOracle_mulVec_liftOracleVec {n m k j : ℕ} {S : Finset (Fin (2 ^ n))} {a : Fin (2 ^
    findAllQubits n m k)} (ha : ValidStageBasis n m k S j a) (v : Fin (2 ^ ((n + 1) * m)) → ℂ) :
    ((unmarkUnitary n m k (activeMemSlots k j)).1 * ((oracleReg n m k).embedUnitary
    (parallelMarkingOracle m S)).1) *ᵥ liftOracleVec n m k a v = liftOracleVec n m k a
    ((parallelMarkingOracle m (S \ memFoundSet n m k (activeMemSlots k j) a)).1 *ᵥ v) := by
  let memTuple : Fin k → Fin (2 ^ n) := fun l ↦ (memSlotReg n m k l).extractIndex a
  have himg : (activeMemSlots k j).image memTuple = memFoundSet n m k (activeMemSlots k j) a := rfl
  have hsub : (activeMemSlots k j).image memTuple ⊆ S := validStageBasis_memFoundSet_subset ha
  have hproj : memTupleProj n m k (activeMemSlots k j) memTuple *ᵥ liftOracleVec n m k a v =
      liftOracleVec n m k a v := by
    funext z; rw [memTupleProj, Matrix.mulVec_diagonal]
    by_cases hE : ((oracleReg n m k).basisSplitEquiv z).2 = ((oracleReg n m k).basisSplitEquiv a).2
    · have hag : (oracleReg n m k).AgreeOutside z a := by
        intro q hq; have h1 := congrFun hE ⟨q, hq⟩
        simpa [QRegister.basisSplitEquiv_apply_snd] using h1
      have hmem : ∀ l ∈ activeMemSlots k j, (memSlotReg n m k l).extractIndex z = memTuple l := by
        intro l _
        have hdisj : (memSlotReg n m k l).DisjointWires (oracleReg n m k) :=
          QRegister.disjoint_comm.1
            ((oracleReg_disjoint_memAllReg n m k).compose_right (localMemSlotReg n k l))
        apply (basisBits n).injective; funext w; dsimp only [memTuple]
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        exact hag _ (Set.disjoint_left.1 hdisj ⟨w, rfl⟩)
      rw [ite_eq_left hmem, one_mul]
    · simp [liftOracleVec, QRegister.tensorState, Pi.single_eq_of_ne hE]
  rw [← hproj, Matrix.mulVec_mulVec, unmarkUnitary_mul_parallelOracle_mul_proj _ _ hsub, ←
    Matrix.mulVec_mulVec, hproj, himg, QRegister.embedUnitary_val, embedOracle_mulVec_liftOracleVec]
theorem marker0Proj_mulVec_liftOracleVec {n m k : ℕ} (hm : 1 ≤ m) (a : Fin (2 ^ findAllQubits n m
    k)) (o : Fin (2 ^ 1)) (v : Fin (2 ^ ((n + 1) * m)) → ℂ) : (markerReg n m k ⟨0,
    hm⟩).basisOutcomeProjector o *ᵥ liftOracleVec n m k a v = liftOracleVec n m k a ((localFlagReg n
    m ⟨0, hm⟩).basisOutcomeProjector o *ᵥ v) := by
  have heq : (markerReg n m k ⟨0, hm⟩).basisOutcomeProjector o =
      (oracleReg n m k).embedMatrix ((localFlagReg n m ⟨0, hm⟩).basisOutcomeProjector o) := by
    rw [markerReg_eq_compose_localFlagReg, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal, QRegister.embedMatrix_diagonal]
    congr 1; funext z; rw [QRegister.extractIndex_compose]
  rw [heq, embedOracle_mulVec_liftOracleVec]
theorem resetKraus_mulVec_liftOracleVec {n m k j : ℕ} {S : Finset (Fin (2 ^ n))}
    {a : Fin (2 ^ findAllQubits n m k)} (ha : ValidStageBasis n m k S j a)
    (o : Fin (2 ^ ((n + 1) * m))) (v : Fin (2 ^ ((n + 1) * m)) → ℂ) :
    (oracleReg n m k).resetKraus o *ᵥ liftOracleVec n m k a v = v o • Pi.single a 1 := by
  rw [liftOracleVec, (oracleReg n m k).resetKraus_mulVec_tensorState]
  have hsingle : (Pi.single (0 : Fin (2 ^ ((n + 1) * m))) (v o)) =
      v o • Pi.single ((oracleReg n m k).extractIndex a) (1 : ℂ) := by
    rw [ha.1]; funext u; by_cases hu : u = 0 <;> simp [hu]
  rw [hsingle, (oracleReg n m k).tensorState_smul_left,
    (oracleReg n m k).tensorState_single_factors]
/-- Global zero-cost unitary step helpers wrapped in `phaseI` at circuit call sites. -/
noncomputable def globAddrHadamard (n m k : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
  (oracleReg n m k).embedUnitary ((localAddrReg n m).embedUnitary (hadamardUnitary (q := m * n)))
noncomputable def globAddrDiffuser (n m k : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
  (oracleReg n m k).embedUnitary
    ((localAddrReg n m).embedUnitary (Grover.diffuserUnitary (n := m * n)))
noncomputable def globFlagConj (n m k : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
  (oracleReg n m k).embedUnitary (flagConj n m)
noncomputable def globChord (n m k : ℕ) (hm : 1 ≤ m) (s : ℝ) : Unitary (2 ^ findAllQubits n m k) :=
  (oracleReg n m k).embedUnitary (chordUnitary n m hm s)
noncomputable def globFlip (n m k : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
  (oracleReg n m k).embedUnitary (permutationUnitary (flipPerm n m))
theorem isRealMatrix_globAddrHadamard (n m k : ℕ) : IsRealMatrix (globAddrHadamard n m k).1 :=
  isRealMatrix_embedMatrix _ (isRealMatrix_embedMatrix _ (isRealMatrix_hadamardMatrix (m * n)))
theorem isRealMatrix_globAddrDiffuser (n m k : ℕ) : IsRealMatrix (globAddrDiffuser n m k).1 :=
  isRealMatrix_embedMatrix _ (isRealMatrix_embedMatrix _ (isRealMatrix_diffuserMatrix (m * n)))
theorem isRealMatrix_globFlagConj (n m k : ℕ) : IsRealMatrix (globFlagConj n m k).1 :=
  isRealMatrix_embedMatrix _ (isRealMatrix_flagConj n m)
theorem isRealMatrix_globChord (n m k : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    IsRealMatrix (globChord n m k hm s).1 :=
  isRealMatrix_embedMatrix _ (isRealMatrix_chordMat n m hm s)
theorem isRealMatrix_globFlip (n m k : ℕ) : IsRealMatrix (globFlip n m k).1 :=
  isRealMatrix_embedMatrix _ (isRealMatrix_permutationUnitary _)
/-- One odd-parity phase kickback step (`1` oracle query) with coherent unmarking over
  `activeMem`. -/
noncomputable def oddPhaseStep {Var : Type} (n m k : ℕ) (activeMem : Finset (Fin k)) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  let Uf := globFlagConj n m k
  .seq (.step (phaseI Uf))
    (.seq (effectiveOracleCircuit n m k activeMem) (.step (phaseI Uf)))
/-- One odd-parity Grover iteration (`oddPhaseStep` followed by `globAddrDiffuser`, `1`
  query). -/
noncomputable def oddGroverIterCircuit {Var : Type} (n m k : ℕ) (activeMem : Finset (Fin k)) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  let Ud := globAddrDiffuser n m k
  .seq (oddPhaseStep n m k activeMem) (.step (phaseI Ud))
/-- Unitary preparation `cPrep` (`K + 1` queries) before the weak-measurement `.qWhile`
  loop. -/
noncomputable def lockPrepCircuit {Var : Type} (n m k : ℕ) (activeMem : Finset (Fin k)) (K : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
    m) :=
  let Uh := globAddrHadamard n m k
  .seq (.step (phaseI Uh))
    (.seq (OracleDynamicCircuit.sequence (List.replicate K (oddGroverIterCircuit n m k activeMem)))
      (oddPhaseStep n m k activeMem))
/-- Unitary part of `cBody` (`1` query) before measuring `markerReg n m k ⟨0, hm⟩`. -/
noncomputable def lockBodyUnitaryCircuit {Var : Type} (n m k : ℕ) (hm : 1 ≤ m) (activeMem : Finset
    (Fin k)) (s : ℝ) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n
    m k) ((n + 1) * m) :=
  let Ud := globAddrDiffuser n m k
  let Uc := globChord n m k hm s
  .seq (.step (phaseI Ud))
    (.seq (.step (phaseI Uc))
      (.seq (oddPhaseStep n m k activeMem) (.step (phaseI Uc))))
/-- Loop body `cBody` (`1` query): apply `lockBodyUnitaryCircuit` and measure `markerReg 0`. -/
noncomputable def lockBodyCircuit {Var : Type} (res : Var) (n m k : ℕ) (hm : 1 ≤ m) (activeMem :
    Finset (Fin k)) (s : ℝ) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
    (findAllQubits n m k) ((n + 1) * m) :=
  .seq (lockBodyUnitaryCircuit n m k hm activeMem s)
    (.measure res (markerReg n m k ⟨0, hm⟩))
/-- Loop continuation guard: weak-measurement flag wire returned `0`. -/
def lockGuard {Var : Type} (res : Var) (σ : Store Var) : Prop := σ res = 0
instance instDecidablePredLockGuard {Var : Type} (res : Var) :
    DecidablePred (lockGuard res) := by
  intro σ
  unfold lockGuard
  infer_instance
/-- Loop exit circuit `cExit` (`1` query): flip all `m` flags `1 ↦ 0`, run one unmarked
  verification call, reset `oracleReg` into `res`, and write the first marked index to
  `memSlotReg j`. -/
noncomputable def lockExitCircuit {Var : Type} (res : Var) (n m k : ℕ) (j : Fin k) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  let Uflip := globFlip n m k
  .seq (.step (phaseI Uflip))
    (.seq (effectiveOracleCircuit n m k (activeMemSlots k j.val))
      (.seq (resetRegCircuit res (oracleReg n m k))
        (xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j))))
/-- Full Stationary-chord odd-parity weak-measurement stage circuit for stage `j: Fin k`. -/
noncomputable def lockStageCircuit {Var : Type} (res : Var) (n m k : ℕ) (j : Fin k) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  if hm : 1 ≤ m then
    let r := k - j.val
    let activeMem := activeMemSlots k j.val
    let K := lockOddSched n m r
    let s := clampedOddRatio n m r
    .seq (.measure res (oracleReg n m k))
      (.seq (lockPrepCircuit n m k activeMem K)
        (.seq (.qWhile (lockGuard res) (lockBodyCircuit res n m k hm activeMem s))
          (lockExitCircuit res n m k j)))
  else
    .skip
/-!
 ### CostBounds of `oddPhaseStep`, `lockPrepCircuit`, `lockBodyCircuit`,
  `lockExitCircuit`
-/
theorem costBound_phaseI_step {Var : Type} [DecidableEq Var] {n m k : ℕ} (S : Finset (Fin (2 ^ n)))
    (U : Unitary (2 ^ findAllQubits n m k)) (hU : IsRealMatrix U.1) : CostBound (Var := Var)
    (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) (.qAssign (phaseI U)) 0 := by
  have hc := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero
    (isRealMatrix_parallelMarkingOracle (m := m) S) hU
  simpa [hc] using CostBound.qAssign (Var := Var)
    (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) (phaseI U)
theorem costBound_oddPhaseStep {Var : Type} [DecidableEq Var] (n m k : ℕ) (activeMem : Finset (Fin
    k)) (S : Finset (Fin (2 ^ n))) : CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m
    S)) ((oddPhaseStep (Var := Var) n m k activeMem).compile QProg.qAssign (parallelMarkingOracle m
    S)) 1 := by
  have hf := costBound_phaseI_step (Var := Var) S (globFlagConj n m k)
    (isRealMatrix_globFlagConj n m k)
  have he := costBound_effectiveOracleCircuit (Var := Var) n m k activeMem S
  simp only [oddPhaseStep, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step]
  simpa using CostBound.seq hf (CostBound.seq he hf)
theorem costBound_oddGroverIterLoop {Var : Type} [DecidableEq Var] (n m k : ℕ) (activeMem : Finset
    (Fin k)) (S : Finset (Fin (2 ^ n))) (K : ℕ) : CostBound (CostModel.ofEmbeddedOracle
    (parallelMarkingOracle m S)) ((OracleDynamicCircuit.sequence (List.replicate K
    (oddGroverIterCircuit (Var := Var) n m k activeMem))).compile QProg.qAssign
    (parallelMarkingOracle m S)) (K : ℝ≥0) := by
  induction K with
  | zero =>
      simpa using CostBound.skip_zero (Var := Var)
        (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
  | succ K ih =>
      rw [List.replicate_succ, OracleDynamicCircuit.sequence_cons, OracleDynamicCircuit.compile_seq]
      have hd := costBound_phaseI_step (Var := Var) S (globAddrDiffuser n m k)
        (isRealMatrix_globAddrDiffuser n m k)
      have hp := costBound_oddPhaseStep (Var := Var) n m k activeMem S
      have hiter : CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
          ((oddGroverIterCircuit (Var := Var) n m k activeMem).compile
            QProg.qAssign (parallelMarkingOracle m S)) 1 := by
        simp only [oddGroverIterCircuit, OracleDynamicCircuit.compile_seq,
          OracleDynamicCircuit.compile_step]; simpa using CostBound.seq hp hd
      have hseq := CostBound.seq hiter ih; simpa [Nat.cast_add, Nat.cast_one, add_comm] using hseq
theorem costBound_lockPrepCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ) (activeMem : Finset
    (Fin k)) (S : Finset (Fin (2 ^ n))) (K : ℕ) : CostBound (CostModel.ofEmbeddedOracle
    (parallelMarkingOracle m S)) ((lockPrepCircuit (Var := Var) n m k activeMem K).compile
    QProg.qAssign (parallelMarkingOracle m S)) ((K : ℝ≥0) + 1) := by
  have hh := costBound_phaseI_step (Var := Var) S (globAddrHadamard n m k)
    (isRealMatrix_globAddrHadamard n m k)
  have hl := costBound_oddGroverIterLoop (Var := Var) n m k activeMem S K
  have hp := costBound_oddPhaseStep (Var := Var) n m k activeMem S
  simp only [lockPrepCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step]
  simpa using CostBound.seq hh (CostBound.seq hl hp)
theorem costBound_lockBodyCircuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) (hm : 1 ≤
    m) (activeMem : Finset (Fin k)) (s : ℝ) (S : Finset (Fin (2 ^ n))) : CostBound
    (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) ((lockBodyCircuit res n m k hm
    activeMem s).compile QProg.qAssign (parallelMarkingOracle m S)) 1 := by
  have hd := costBound_phaseI_step (Var := Var) S (globAddrDiffuser n m k)
    (isRealMatrix_globAddrDiffuser n m k)
  have hc := costBound_phaseI_step (Var := Var) S (globChord n m k hm s)
    (isRealMatrix_globChord n m k hm s)
  have hp := costBound_oddPhaseStep (Var := Var) n m k activeMem S
  have hm0 : CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
      (QProg.measureRegister res (markerReg n m k ⟨0, hm⟩)) 0 := by
    intro Δ; simp [QProg.measureRegister]
  simp only [lockBodyCircuit, lockBodyUnitaryCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_measure]
  simpa using CostBound.seq (CostBound.seq hd (CostBound.seq hc (CostBound.seq hp hc))) hm0
theorem costBound_lockExitCircuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) (j : Fin
    k) (S : Finset (Fin (2 ^ n))) : CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m
    S)) ((lockExitCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle m S)) 1 := by
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
  have hfl := costBound_phaseI_step (Var := Var) S (globFlip n m k) (isRealMatrix_globFlip n m k)
  have he := costBound_effectiveOracleCircuit (Var := Var) n m k (activeMemSlots k j.val) S
  have hr := costBound_resetRegCircuit horacle res (oracleReg n m k)
  have hx := costBound_xorRegCircuit horacle res (extractMarkedIdx n m) (memSlotReg n m k j)
  simp only [lockExitCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step]
  simpa using CostBound.seq hfl (CostBound.seq he (CostBound.seq hr hx))
/-! ### Unitary `wp` reductions and stationary vector action -/
noncomputable def oddPhaseUnitary (n m k : ℕ) (activeMem : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) : Unitary (2 ^ findAllQubits n m k) :=
  globFlagConj n m k *
    (unmarkUnitary n m k activeMem * (oracleReg n m k).embedUnitary (parallelMarkingOracle m S)) *
    globFlagConj n m k
noncomputable def lockPrepUnitary (n m k : ℕ) (activeMem : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) (K : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
  oddPhaseUnitary n m k activeMem S *
    (globAddrDiffuser n m k * oddPhaseUnitary n m k activeMem S) ^ K *
    globAddrHadamard n m k
noncomputable def lockBodyUnitary (n m k : ℕ) (hm : 1 ≤ m) (activeMem : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) (s : ℝ) : Unitary (2 ^ findAllQubits n m k) :=
  globChord n m k hm s * oddPhaseUnitary n m k activeMem S * globChord n m k hm s *
    globAddrDiffuser n m k
theorem wp_oddPhaseStep {Var : Type} [DecidableEq Var] (n m k : ℕ) (activeMem : Finset (Fin k)) (S :
    Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
      ((oddPhaseStep (Var
    := Var) n m k activeMem).compile QProg.qAssign (parallelMarkingOracle m S)) Θ = Θ.qAssign
    (oddPhaseUnitary n m k activeMem S) := by
  simp only [oddPhaseStep, effectiveOracleCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle, wp_qSeq, wp_qAssign,
    qAssign_phaseI]; simp only [CQAssertion.qAssign_qAssign, oddPhaseUnitary, mul_assoc]
theorem wp_oddGroverIterCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ) (activeMem : Finset (Fin
    k)) (S : Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
    ((oddGroverIterCircuit (Var := Var) n m k activeMem).compile QProg.qAssign
    (parallelMarkingOracle m S)) Θ = Θ.qAssign (globAddrDiffuser n m k * oddPhaseUnitary n m k
    activeMem S) := by
  simp only [oddGroverIterCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, wp_qSeq, wp_oddPhaseStep, wp_qAssign, qAssign_phaseI]
  simp only [CQAssertion.qAssign_qAssign]
theorem wp_lockPrepCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ) (activeMem : Finset (Fin k))
    (S : Finset (Fin (2 ^ n))) (K : ℕ) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
    ((lockPrepCircuit (Var := Var) n m k activeMem K).compile QProg.qAssign (parallelMarkingOracle
    m S)) Θ = Θ.qAssign (lockPrepUnitary n m k activeMem S K) := by
  have hloop := wp_replicate_qAssign (oddGroverIterCircuit (Var := Var) n m k activeMem)
    (parallelMarkingOracle m S) (globAddrDiffuser n m k * oddPhaseUnitary n m k activeMem S)
    (wp_oddGroverIterCircuit n m k activeMem S) K
  simp only [lockPrepCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
    wp_qSeq, hloop, wp_oddPhaseStep, wp_qAssign, qAssign_phaseI]
  simp only [CQAssertion.qAssign_qAssign, lockPrepUnitary, mul_assoc]
theorem wp_lockBodyUnitaryCircuit {Var : Type} [DecidableEq Var] (n m k : ℕ) (hm : 1 ≤ m)
    (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) (s : ℝ) (Θ : CQAssertion (Store Var) (2
      ^
    findAllQubits n m k)) : wp ((lockBodyUnitaryCircuit (Var := Var) n m k hm activeMem s).compile
    QProg.qAssign (parallelMarkingOracle m S)) Θ = Θ.qAssign (lockBodyUnitary n m k hm activeMem S
    s) := by
  simp only [lockBodyUnitaryCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, wp_qSeq, wp_oddPhaseStep, wp_qAssign, qAssign_phaseI]
  simp only [CQAssertion.qAssign_qAssign, lockBodyUnitary, mul_assoc]
theorem oddPhaseUnitary_mulVec_liftOracleVec {n m k j : ℕ} {S : Finset (Fin (2 ^ n))} {a : Fin (2 ^
    findAllQubits n m k)} (ha : ValidStageBasis n m k S j a) (v : Fin (2 ^ ((n + 1) * m)) → ℂ) :
    (oddPhaseUnitary n m k (activeMemSlots k j) S).1 *ᵥ liftOracleVec n m k a v = liftOracleVec n m
    k a (sDiagM n m (S \ memFoundSet n m k (activeMemSlots k j) a) *ᵥ v) := by
  have hstep : (oddPhaseUnitary n m k (activeMemSlots k j) S).1 *ᵥ liftOracleVec n m k a v =
    (globFlagConj n m k).1 *ᵥ (((unmarkUnitary n m k (activeMemSlots k j)).1 * ((oracleReg n m
    k).embedUnitary (parallelMarkingOracle m S)).1) *ᵥ ((globFlagConj n m k).1 *ᵥ liftOracleVec n m
    k a v)) := by
    simp only [oddPhaseUnitary, Submonoid.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hstep, globFlagConj, QRegister.embedUnitary_val, embedOracle_mulVec_liftOracleVec,
    effectiveOracle_mulVec_liftOracleVec ha, embedOracle_mulVec_liftOracleVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, flagConj_mul_parallelMarkingOracle_mul_flagConj]
theorem lockPrepUnitary_mulVec_single {n m k j : ℕ} {S : Finset (Fin (2 ^ n))} {a : Fin (2 ^
    findAllQubits n m k)} (ha : ValidStageBasis n m k S j a) (K : ℕ) :
    let A_a := S \ memFoundSet n m k (activeMemSlots k j) a; let mA0 := oddSet n m A_a
    (lockPrepUnitary n m k (activeMemSlots k j) S K).1 *ᵥ Pi.single a 1 = liftOracleVec n m k a
      ((localAddrReg n m).tensorState (setOracleMatrix mA0 *ᵥ groverSetState mA0 K) (Pi.single 0
      1)) := by
  intro A_a mA0
  have hH : (globAddrHadamard n m k).1 *ᵥ Pi.single a 1 = liftOracleVec n m k a ((localAddrReg n
    m).tensorState (groverSetState mA0 0) (Pi.single 0 1)) := by
    rw [← liftOracleVec_single_zero ha, globAddrHadamard, QRegister.embedUnitary_val,
      embedOracle_mulVec_liftOracleVec]
    congr 1; change (localAddrReg n m).embedMatrix (hadamardMatrix (m * n)) *ᵥ Pi.single 0 1 = _
    rw [(localAddrReg n m).embedMatrix_mulVec_single_factors,
      extractIndex_zero (localAddrReg n m),
      show ((localAddrReg n m).basisSplitEquiv 0).2 = 0 from
        funext fun _ ↦ by simp [QRegister.basisSplitEquiv_apply_snd, basisBits_eq_div_mod]]
    congr 1; funext u
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply_zero, groverSetState]; simp
  have hiter (t : ℕ) : (((globAddrDiffuser n m k * oddPhaseUnitary n m k (activeMemSlots k j) S) ^
    t).1 *ᵥ liftOracleVec n m k a ((localAddrReg n m).tensorState (groverSetState mA0 0) (Pi.single
    0 1))) = liftOracleVec n m k a ((localAddrReg n m).tensorState (groverSetState mA0 t)
    (Pi.single 0 1)) := by
    induction t with
    | zero => simp
    | succ t ih =>
        rw [pow_succ', Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih, Submonoid.coe_mul, ←
          Matrix.mulVec_mulVec, oddPhaseUnitary_mulVec_liftOracleVec ha, sDiagM_mulVec_env_zero,
          globAddrDiffuser, QRegister.embedUnitary_val, embedOracle_mulVec_liftOracleVec,
          QRegister.embedUnitary_val, (localAddrReg n m).embedMatrix_mulVec_tensorState,
          Grover.diffuserUnitary_coe]; rfl
  rw [lockPrepUnitary, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hH, ←
    Matrix.mulVec_mulVec, hiter K, oddPhaseUnitary_mulVec_liftOracleVec ha, sDiagM_mulVec_env_zero]
theorem lockBodyUnitary_outcomes {n m k j : ℕ} (hm : 1 ≤ m) {S : Finset (Fin (2 ^ n))} {a : Fin (2
    ^ findAllQubits n m k)} (ha : ValidStageBasis n m k S j a) (hc1 : 1 ≤ (oddSet n m (S \
    memFoundSet n m k (activeMemSlots k j) a)).card) (hcN : (oddSet n m (S \ memFoundSet n m k
    (activeMemSlots k j) a)).card < 2 ^ (m * n)) (K : ℕ) (hsin : Real.sin ((2 * (K : ℝ) + 3) *
    halfAngleOdd n m (S \ memFoundSet n m k (activeMemSlots k j) a).card) ≠ 0) (hcos : Real.cos
    ((2 * (K : ℝ) + 1) * halfAngleOdd n m (S \ memFoundSet n m k (activeMemSlots k j) a).card) ≠ 0)
    (s : ℝ) (hs_eq : s = targetAngleRatio (halfAngleOdd n m (S \ memFoundSet n m k (activeMemSlots k
    j) a).card) K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let A_a := S \ memFoundSet n m k (activeMemSlots k j) a; let mA0 := oddSet n m A_a
    let θ := halfAngleOdd n m A_a.card
    let ψ_a := (lockPrepUnitary n m k (activeMemSlots k j) S K).1 *ᵥ Pi.single a 1
    let Ub := (lockBodyUnitary n m k hm (activeMemSlots k j) S s).1
    (markerReg n m k ⟨0, hm⟩).basisOutcomeProjector 0 *ᵥ (Ub *ᵥ ψ_a) = (nonTargetAngleRatio θ K : ℂ)
      • ψ_a ∧ (markerReg n m k ⟨0, hm⟩).basisOutcomeProjector 1 *ᵥ (Ub *ᵥ ψ_a) = liftOracleVec n m k
      a ((localAddrReg n m).tensorState (pinHitVec mA0 s (groverSetState mA0 (K + 1))) (Pi.single
      1 1)) := by
  intro A_a mA0 θ ψ_a Ub
  have hθ_eq : halfAngleSet (m * n) mA0.card = θ := halfAngleSet_oddSet_eq A_a
  have hsin' : Real.sin ((2 * (K : ℝ) + 3) * halfAngleSet (m * n) mA0.card) ≠ 0 :=
    hθ_eq.symm ▸ hsin
  have hcos' : Real.cos ((2 * (K : ℝ) + 1) * halfAngleSet (m * n) mA0.card) ≠ 0 :=
    hθ_eq.symm ▸ hcos
  have hs_eq' : s = targetAngleRatio (halfAngleSet (m * n) mA0.card) K := hθ_eq.symm ▸ hs_eq
  have hψ : ψ_a = liftOracleVec n m k a ((localAddrReg n m).tensorState (setOracleMatrix mA0 *ᵥ
    groverSetState mA0 K) (Pi.single 0 1)) := lockPrepUnitary_mulVec_single ha K
  have hUb_ψ : Ub *ᵥ ψ_a = liftOracleVec n m k a ((localAddrReg n m).tensorState (lockSetKraus0
    mA0 s *ᵥ groverSetState mA0 (K + 1)) (Pi.single 0 1) + (localAddrReg n m).tensorState
    (pinHitVec mA0 s (groverSetState mA0 (K + 1))) (Pi.single 1 1)) := by
    have hstep : Ub *ᵥ ψ_a = (globChord n m k hm s).1 *ᵥ ((oddPhaseUnitary n m k (activeMemSlots k
      j) S).1 *ᵥ ((globChord n m k hm s).1 *ᵥ ((globAddrDiffuser n m k).1 *ᵥ ψ_a))) := by
      simp only [Ub, lockBodyUnitary, Submonoid.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hstep, hψ, globAddrDiffuser, QRegister.embedUnitary_val, embedOracle_mulVec_liftOracleVec,
      QRegister.embedUnitary_val, (localAddrReg n m).embedMatrix_mulVec_tensorState,
      Grover.diffuserUnitary_coe, show Grover.diffuserMatrix *ᵥ (setOracleMatrix mA0 *ᵥ
      groverSetState mA0 K) = groverSetState mA0 (K + 1) from rfl, globChord,
      QRegister.embedUnitary_val, embedOracle_mulVec_liftOracleVec,
      oddPhaseUnitary_mulVec_liftOracleVec ha, embedOracle_mulVec_liftOracleVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show (chordUnitary n m hm s).1 = chordMat n m hm s
      from rfl, parityMat_mulVec_zero hm A_a hs0 hs1]
  obtain ⟨hp0, hp1⟩ := localFlagReg0_split hm (lockSetKraus0 mA0 s *ᵥ groverSetState mA0 (K +
    1)) (pinHitVec mA0 s (groverSetState mA0 (K + 1)))
  constructor
  · rw [hUb_ψ, marker0Proj_mulVec_liftOracleVec, hp0, hs_eq',
      lockSetKraus0_mulVec_groverSetState mA0 hc1 hcN K hsin' hcos', hθ_eq,
      (localAddrReg n m).tensorState_smul_left, liftOracleVec_smul, ← hψ]
  · rw [hUb_ψ, marker0Proj_mulVec_liftOracleVec, hp1]
/-!
 ### Bilinear inner product evaluation of `wp lockBodyCircuit`, `wp lockExitCircuit`,
`whileActiveWP`, and `whileRecWP`
-/
theorem wp_lockBodyCircuit_dotProduct {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hm :
    1 ≤ m) (activeMem : Finset (Fin k)) (S : Finset (Fin (2 ^ n))) (s : ℝ) (Φ : CQAssertion (Store
      Var) (2 ^
    findAllQubits n m k)) (τ : Store Var) (ψ₁ ψ₂ : Fin (2 ^ findAllQubits n m k) → ℂ) :
    let P0 := (markerReg n m k ⟨0, hm⟩).basisOutcomeProjector 0
    let P1 := (markerReg n m k ⟨0, hm⟩).basisOutcomeProjector 1
    let Ub := (lockBodyUnitary n m k hm activeMem S s).1
    star ψ₁ ⬝ᵥ ((wp ((lockBodyCircuit res n m k hm activeMem s).compile
        QProg.qAssign (parallelMarkingOracle m S)) Φ τ).1.mat *ᵥ ψ₂) =
      star (P0 *ᵥ (Ub *ᵥ ψ₁)) ⬝ᵥ ((Φ (Store.subst τ res 0)).1.mat *ᵥ (P0 *ᵥ (Ub *ᵥ ψ₂))) +
        star (P1 *ᵥ (Ub *ᵥ ψ₁)) ⬝ᵥ ((Φ (Store.subst τ res 1)).1.mat *ᵥ (P1 *ᵥ (Ub *ᵥ ψ₂))) := by
  intro P0 P1 Ub
  have hm_mat : (wp (QProg.measureRegister res (markerReg n m k ⟨0, hm⟩)) Φ τ).1.mat = P0 * (Φ
    (Store.subst τ res 0)).1.mat * P0 + P1 * (Φ (Store.subst τ res 1)).1.mat * P1 := by
    rw [wp_measureRegister_coe_ax, HermitianMat.mat_finset_sum]
    have hterm : ∀ i : Fin (2 ^ 1), (HermitianMat.conj ((markerReg n m k ⟨0,
      hm⟩).basisOutcomeProjector i)ᴴ (Φ (Store.subst τ res ↑i.val)).1).mat = (markerReg n m k ⟨0,
      hm⟩).basisOutcomeProjector i * (Φ (Store.subst τ res ↑i.val)).1.mat * (markerReg n m k ⟨0,
      hm⟩).basisOutcomeProjector i := by
      intro i
      simp only [HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose]
    have hsum2 (f : Fin (2 ^ 1) → Matrix (Fin (2 ^ findAllQubits n m k)) (Fin (2 ^ findAllQubits n m
      k)) ℂ) : ∑ x, f x = f 0 + f 1 := Fin.sum_univ_two f
    simp_rw [hterm]; rw [hsum2]
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one, P0, P1]
  simp only [lockBodyCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_measure, wp_qSeq, wp_lockBodyUnitaryCircuit]
  rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe, hm_mat]
  have hmul (A M : Matrix (Fin (2 ^ findAllQubits n m k)) (Fin (2 ^ findAllQubits n m k)) ℂ) :
      star ψ₁ ⬝ᵥ ((Aᴴ * M * A) *ᵥ ψ₂) = star (A *ᵥ ψ₁) ⬝ᵥ (M *ᵥ (A *ᵥ ψ₂)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec, vecMul_conjTranspose, star_star]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add]
  have hassoc (P M : Matrix (Fin (2 ^ findAllQubits n m k)) (Fin (2 ^ findAllQubits n m k)) ℂ) (hP :
    Pᴴ = P) : Ubᴴ * (P * M * P) * Ub = (P * Ub)ᴴ * M * (P * Ub) := by
    simp [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
  rw [hassoc P0 _ ((markerReg n m k ⟨0, hm⟩).basisOutcomeProjector_conjTranspose 0), hassoc P1 _
    ((markerReg n m k ⟨0, hm⟩).basisOutcomeProjector_conjTranspose 1), hmul, hmul, ←
    Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
theorem wp_lockExitCircuit_dotProduct {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hm :
    1 ≤ m) (j : Fin k) {S : Finset (Fin (2 ^ n))} (hScard : S.card = k) (τ : Store Var) {a b : Fin
    (2 ^ findAllQubits n m k)} (ha : ValidStageBasis n m k S j.val a) (hb : ValidStageBasis n m k S
    j.val b) (hc1 : ∀ A : Finset (Fin (2 ^ n)), A.card = k - j.val → 1 ≤ (oddSet n m A).card ∧
    (oddSet n m A).card < 2 ^ (m * n)) (K : ℕ) (hsin : Real.sin ((2 * (K : ℝ) + 3) * halfAngleOdd n
    m (k - j.val)) ≠ 0) (hcos : Real.cos ((2 * (K : ℝ) + 1) * halfAngleOdd n m (k - j.val)) ≠ 0) (s
    : ℝ) (hs_eq : s = targetAngleRatio (halfAngleOdd n m (k - j.val)) K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    :
    let A_a := S \ memFoundSet n m k (activeMemSlots k j.val) a
    let A_b := S \ memFoundSet n m k (activeMemSlots k j.val) b; let mA0 := oddSet n m A_a
    let mB0 := oddSet n m A_b
    let w1_a := liftOracleVec n m k a
      ((localAddrReg n m).tensorState (pinHitVec mA0 s (groverSetState mA0 (K + 1)))
        (Pi.single 1 1))
    let w1_b := liftOracleVec n m k b
      ((localAddrReg n m).tensorState (pinHitVec mB0 s (groverSetState mB0 (K + 1)))
        (Pi.single 1 1))
    star w1_a ⬝ᵥ ((wp ((lockExitCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle
      m S)) (diagAssertion (ValidStageBasis n m k S (j.val + 1))) τ).1.mat *ᵥ w1_b) = if a = b then
      ((1 - nonTargetAngleRatio (halfAngleOdd n m (k - j.val)) K ^ 2 : ℝ) : ℂ) else 0 := by
  intro A_a A_b mA0 mB0 w1_a w1_b
  let Uex : Unitary (2 ^ findAllQubits n m k) := unmarkUnitary n m k (activeMemSlots k j.val) *
    (oracleReg n m k).embedUnitary (parallelMarkingOracle m S) * globFlip n m k
  have hwp_ex (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
    ((OracleDynamicCircuit.seq (.step
    (phaseI (globFlip n m k))) (effectiveOracleCircuit (Var := Var) n m k (activeMemSlots k
    j.val))).compile QProg.qAssign (parallelMarkingOracle m S)) Θ = Θ.qAssign Uex := by
    simp only [effectiveOracleCircuit, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle, wp_qSeq, wp_qAssign,
      qAssign_phaseI]; simp only [CQAssertion.qAssign_qAssign, Uex, mul_assoc]
  have hUex_vec {z : Fin (2 ^ findAllQubits n m k)} (hz : ValidStageBasis n m k S j.val z) :
      let A_z := S \ memFoundSet n m k (activeMemSlots k j.val) z; let mZ0 := oddSet n m A_z
      Uex.1 *ᵥ liftOracleVec n m k z
          ((localAddrReg n m).tensorState (pinHitVec mZ0 s (groverSetState mZ0 (K + 1)))
            (Pi.single 1 1)) =
        liftOracleVec n m k z (exitLocalVec n m A_z s K) := by
    intro A_z mZ0
    have hstep : Uex.1 *ᵥ liftOracleVec n m k z ((localAddrReg n m).tensorState (pinHitVec mZ0 s
      (groverSetState mZ0 (K + 1))) (Pi.single 1 1)) = ((unmarkUnitary n m k (activeMemSlots k
      j.val)).1 * ((oracleReg n m k).embedUnitary (parallelMarkingOracle m S)).1) *ᵥ ((globFlip n m
      k).1 *ᵥ liftOracleVec n m k z ((localAddrReg n m).tensorState (pinHitVec mZ0 s
      (groverSetState mZ0 (K + 1))) (Pi.single 1 1))) := by
      simp only [Uex, Submonoid.coe_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hflip : (globFlip n m k).1 *ᵥ liftOracleVec n m k z ((localAddrReg n m).tensorState
      (pinHitVec mZ0 s (groverSetState mZ0 (K + 1))) (Pi.single 1 1)) = liftOracleVec n m k z
      ((localAddrReg n m).tensorState (pinHitVec mZ0 s (groverSetState mZ0 (K + 1))) (Pi.single 0
      1)) := by
      rw [globFlip, QRegister.embedUnitary_val, embedOracle_mulVec_liftOracleVec,
        show (permutationUnitary (flipPerm n m)).1 = flipMat n m from rfl,
        flipMat_mulVec_tensorState, localEnv_one_add_one]
    rw [hstep, hflip, effectiveOracle_mulVec_liftOracleVec hz]; rfl
  let cTail : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k)
    ((n + 1) * m) := OracleDynamicCircuit.seq (resetRegCircuit (Var := Var) res (oracleReg n m k))
    (xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j))
  have hcExit_eq : wp ((lockExitCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle
    m S)) (diagAssertion (ValidStageBasis n m k S (j.val + 1))) τ = (wp (cTail.compile QProg.qAssign
    (parallelMarkingOracle m S)) (diagAssertion (ValidStageBasis n m k S (j.val + 1)))).qAssign Uex
    τ := by
    simp only [lockExitCircuit, cTail, OracleDynamicCircuit.compile_seq, wp_qSeq]
    exact congrFun (hwp_ex _) τ
  rw [hcExit_eq, ← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe]
  have hmul_Uex (M : Matrix (Fin (2 ^ findAllQubits n m k)) (Fin (2 ^ findAllQubits n m k)) ℂ) :
      star w1_a ⬝ᵥ ((Uex.1ᴴ * M * Uex.1) *ᵥ w1_b) =
        star (Uex.1 *ᵥ w1_a) ⬝ᵥ (M *ᵥ (Uex.1 *ᵥ w1_b)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec, vecMul_conjTranspose, star_star]
  rw [hmul_Uex, hUex_vec ha, hUex_vec hb]
  simp only [cTail, OracleDynamicCircuit.compile_seq, wp_qSeq]
  rw [wp_resetRegCircuit, Matrix.sum_mulVec, dotProduct_sum]
  have hterm (o : Fin (2 ^ ((n + 1) * m))) : star (liftOracleVec n m k a (exitLocalVec n m A_a s K))
    ⬝ᵥ ((((oracleReg n m k).resetKraus o)ᴴ * (wp ((xorRegCircuit res (extractMarkedIdx n m)
    (memSlotReg n m k j)).compile QProg.qAssign (parallelMarkingOracle m S)) (diagAssertion
    (ValidStageBasis n m k S (j.val + 1))) (Store.subst τ res ↑o.val)).1.mat * (oracleReg n m
    k).resetKraus o) *ᵥ liftOracleVec n m k b (exitLocalVec n m A_b s K)) = if a = b then
    (Complex.normSq (exitLocalVec n m A_a s K o) : ℂ) else 0 := by
    set Mx := (wp ((xorRegCircuit res (extractMarkedIdx n m) (memSlotReg n m k j)).compile
      QProg.qAssign (parallelMarkingOracle m S)) (diagAssertion (ValidStageBasis n m k S (j.val +
      1))) (Store.subst τ res ↑o.val)).1.mat
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      vecMul_conjTranspose, star_star, resetKraus_mulVec_liftOracleVec ha o,
      resetKraus_mulVec_liftOracleVec hb o, Matrix.mulVec_smul, star_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, Matrix.mulVec_single_one]
    have hdot : star (Pi.single a (1 : ℂ)) ⬝ᵥ Mx.col b = Mx a b := by
      simp [dotProduct, Pi.single_apply]
    rw [hdot]; dsimp only [Mx]; rw [wp_xorRegCircuit]
    set σ' := Store.subst τ res (o.val : Expr Var)
    have hσ' : σ' res = (o.val : ℤ) := (by simp [σ'])
    let xStar : Fin (2 ^ n) :=
      ⟨extractMarkedIdx n m (o.val : ℤ), extractMarkedIdx_lt n m (o.val : ℤ)⟩
    have hperm : regMaskVec (memSlotReg n m k j) (extractMarkedIdx n m (σ' res)) =
        regMaskVec (memSlotReg n m k j) xStar.val := by rw [hσ']
    rw [hperm]
    let U := permutationUnitary (xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val))
    have hmat : ((diagAssertion (ValidStageBasis n m k S (j.val + 1))).qAssign U σ').1.mat a b =
      (diagProj (ValidStageBasis n m k S (j.val + 1))) (xorBitsPerm (regMaskVec (memSlotReg n m k j)
      xStar.val) a) (xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val) b) := by
      rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
        conjTranspose_mul_mul_apply_single, permutationUnitary_mulVec_single,
        permutationUnitary_mulVec_single]
      simp [diagAssertion, diagObs_mat, Matrix.col_apply, dotProduct, Pi.single_apply]
    rw [hmat]; by_cases hab : a = b
    · subst hab; by_cases hzero : exitLocalVec n m A_a s K o = 0
      · dsimp only [A_a, A_b] at hzero ⊢; simp [hzero]
      · have hxmem : xStar ∈ A_a := extractMarkedIdx_mem_of_exitLocalVec_ne_zero hzero
        have hrep := xorBitsPerm_regMaskVec_of_clean (memSlotReg n m k j) xStar a
          (ha.2.2.2 j le_rfl)
        rw [hrep]; have hv := validStageBasis_write_succ j ha hxmem
        have hdiag : diagProj (ValidStageBasis n m k S (j.val + 1)) ((memSlotReg n m k
          j).replaceIndex a xStar) ((memSlotReg n m k j).replaceIndex a xStar) = 1 := by
          simp [diagProj, hv]
        rw [hdiag]; dsimp only [A_a, A_b]
        simp only [smul_eq_mul, mul_one, ↓reduceIte, RCLike.star_def, Complex.mul_conj]
    · have hne : xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val) a ≠ xorBitsPerm (regMaskVec
        (memSlotReg n m k j) xStar.val) b := fun h ↦ hab ((xorBitsPerm _).injective h)
      have hdiag0 : diagProj (ValidStageBasis n m k S (j.val + 1)) (xorBitsPerm (regMaskVec
        (memSlotReg n m k j) xStar.val) a) (xorBitsPerm (regMaskVec (memSlotReg n m k j) xStar.val)
        b) = 0 := Matrix.diagonal_apply_ne _ hne
      rw [hdiag0]; simp [hab]
  rw [Finset.sum_congr rfl (fun o _ ↦ hterm o)]; by_cases hab : a = b
  · subst hab; simp only [↓reduceIte, ← Complex.ofReal_sum]
    have hcardA : A_a.card = k - j.val := validStageBasis_card_sdiff hScard (le_of_lt j.isLt) ha
    obtain ⟨hm0_1, hm0_N⟩ := hc1 A_a hcardA
    have hθ_eq : halfAngleSet (m * n) (oddSet n m A_a).card = halfAngleOdd n m (k - j.val) := by
      rw [halfAngleSet_oddSet_eq, hcardA]
    have hs_eq' : s = targetAngleRatio (halfAngleSet (m * n) (oddSet n m A_a).card) K := by
      rw [hθ_eq, hs_eq]
    rw [hs_eq', sum_normSq_exitLocalVec hm A_a hm0_1 hm0_N K
      (hθ_eq.symm ▸ hsin) (hθ_eq.symm ▸ hcos) (hs_eq' ▸ hs0) (hs_eq' ▸ hs1), hθ_eq]
  · simp [hab]
/-! ### Single-stage Stationary-chord transition theorem (`n ≥ 100`) -/
theorem lockStage_transition {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hn : 100 ≤ n)
    (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024) {S : Finset (Fin (2 ^ n))} (hScard :
    S.card = k) (j : Fin k) {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : SupportedOn
    (ValidStageBasis n m k S j.val) Δ) :
    let prog := (lockStageCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle m S)
    let r := k - j.val
    SupportedOn (ValidStageBasis n m k S (j.val + 1)) ((interp prog).toStateFun Δ) ∧ ((interp
      prog).toStateFun Δ).trace = Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle
      (parallelMarkingOracle m S)) prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((relCostLock :
      ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  intro prog r; have hr1 : 1 ≤ r := (by dsimp [r]; omega)
  have hr1024 : r ≤ 1024 := (by dsimp [r]; omega)
  obtain ⟨hcard_odd, hclamp, hsin3, hcos1, hq_nn, hq_lt, hcost_ratio⟩ :=
    oddFrac_bounds_of_ge_100 hn hm1 hm1024 hr1 hr1024
  obtain ⟨hs0, hs1⟩ := clampedOddRatio_mem_Icc n m r; set θ := halfAngleOdd n m r
  generalize hK_def : lockOddSched n m r = K; generalize hs_def : clampedOddRatio n m r = s
  rw [hK_def] at hclamp hsin3 hcos1 hq_nn hq_lt hcost_ratio; rw [hs_def] at hclamp hs0 hs1
  set α := nonTargetAngleRatio θ K; set q := α ^ 2; have h1mq_pos : 0 < 1 - q := (by linarith)
  set cInit : QProg Var (2 ^ findAllQubits n m k) := QProg.measureRegister res (oracleReg n m k)
  set cPrep : QProg Var (2 ^ findAllQubits n m k) := (lockPrepCircuit n m k (activeMemSlots k
    j.val) K).compile QProg.qAssign (parallelMarkingOracle m S)
  set cBody : QProg Var (2 ^ findAllQubits n m k) := (lockBodyCircuit res n m k hm1
    (activeMemSlots k j.val) s).compile QProg.qAssign (parallelMarkingOracle m S)
  set cLoop : QProg Var (2 ^ findAllQubits n m k) := .qWhile (lockGuard res) cBody
  set cExit : QProg Var (2 ^ findAllQubits n m k) :=
    (lockExitCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle m S)
  have hprog_eq : prog = (cInit ;; (cPrep ;; (cLoop ;; cExit))) := by
    simp [prog, lockStageCircuit, hm1, cInit, cPrep, cLoop, cBody, cExit, r, hK_def, hs_def]
  let Uprep := lockPrepUnitary n m k (activeMemSlots k j.val) S K
  have hdot_Uprep {a b : Fin (2 ^ findAllQubits n m k)} : star (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ
    (Uprep.1 *ᵥ Pi.single b 1) = if a = b then (1 : ℂ) else 0 := by
    have h := conjTranspose_mul_mul_apply_single Uprep.1 1 a b
    have hU1 : Uprep.1ᴴ * 1 * Uprep.1 = 1 := by
      rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]; exact Uprep.2.1
    rw [hU1, Matrix.one_mulVec] at h; simpa [Matrix.one_apply] using h.symm
  -- Key induction 1: `whileActiveWP` on `(Uprep *ᵥ e_a, Uprep *ᵥ e_b)`
  have hact_dot (t : ℕ) (τ : Store Var) {a b : Fin (2 ^ findAllQubits n m k)} (ha : ValidStageBasis
    n m k S j.val a) (hb : ValidStageBasis n m k S j.val b) : star (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ
    ((whileActiveWP (wp cBody) (lockGuard res) t τ).1.mat *ᵥ (Uprep.1 *ᵥ Pi.single b 1)) = if
    lockGuard res τ then if a = b then ((q ^ t : ℝ) : ℂ) else 0 else 0 := by
    induction t generalizing τ with
    | zero =>
        by_cases hg : lockGuard res τ
        · have htop : (whileActiveWP (wp cBody) (lockGuard res) 0 τ).1.mat = 1 := by
            simp [whileActiveWP, hg]
          rw [htop, Matrix.one_mulVec, ite_eq_left hg]; exact hdot_Uprep
        · have hbot0 : (whileActiveWP (wp cBody) (lockGuard res) 0 τ).1.mat = 0 := by
            simp [whileActiveWP, hg]
          rw [hbot0]; simp [hg]
    | succ t ih =>
        rw [whileActiveWP]; by_cases hg : lockGuard res τ
        · simp only [hg, ↓reduceIte]; rw [wp_lockBodyCircuit_dotProduct]
          have hcard_a : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card = r :=
            validStageBasis_card_sdiff hScard (le_of_lt j.isLt) ha
          have hcard_b : (S \ memFoundSet n m k (activeMemSlots k j.val) b).card = r :=
            validStageBasis_card_sdiff hScard (le_of_lt j.isLt) hb
          obtain ⟨hp0_a, _⟩ := lockBodyUnitary_outcomes hm1 ha (hcard_odd _ hcard_a).1 (hcard_odd
            _ hcard_a).2 K (hcard_a.symm ▸ hsin3) (hcard_a.symm ▸ hcos1) s (hcard_a.symm ▸ hclamp)
            hs0 hs1
          obtain ⟨hp0_b, _⟩ := lockBodyUnitary_outcomes hm1 hb (hcard_odd _ hcard_b).1 (hcard_odd
            _ hcard_b).2 K (hcard_b.symm ▸ hsin3) (hcard_b.symm ▸ hcos1) s (hcard_b.symm ▸ hclamp)
            hs0 hs1
          have hg1 : ¬ lockGuard res (Store.subst τ res 1) := (by simp [lockGuard])
          have hterm1 : (whileActiveWP (wp cBody) (lockGuard res) t
              (Store.subst τ res 1)).1.mat = 0 := by
            cases t with
            | zero => simp [whileActiveWP, hg1]
            | succ t' => simp [whileActiveWP, hg1]
          rw [hterm1, Matrix.zero_mulVec, dotProduct_zero, add_zero, hp0_a, hp0_b, hcard_a, hcard_b,
            Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
            Complex.star_def, Complex.conj_ofReal, ih (Store.subst τ res 0)]
          have hg0 : lockGuard res (Store.subst τ res 0) := (by simp [lockGuard])
          simp only [hg0, ↓reduceIte]; by_cases hab : a = b
          · subst hab; simp only [↓reduceIte]; dsimp [q, α, θ]; push_cast [pow_succ']; ring
          · simp [hab]
        · simp [hg]
  -- Key induction 2: `whileRecWP` on `(Uprep *ᵥ e_a, Uprep *ᵥ e_b)`
  let Ψ := wp cExit (diagAssertion (ValidStageBasis n m k S (j.val + 1)))
  have hrec_dot (t : ℕ) (τ : Store Var) (hg : lockGuard res τ) {a b : Fin (2 ^ findAllQubits n m
    k)} (ha : ValidStageBasis n m k S j.val a) (hb : ValidStageBasis n m k S j.val b) : star
    (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ ((whileRecWP (wp cBody) (lockGuard res) (t + 1) Ψ τ).1.mat *ᵥ
    (Uprep.1 *ᵥ Pi.single b 1)) = if a = b then ((1 - q ^ t : ℝ) : ℂ) else 0 := by
    induction t generalizing τ with
    | zero =>
        have hbot : wp cBody ⊥ = ⊥ := by
          simp only [cBody, lockBodyCircuit, OracleDynamicCircuit.compile_seq,
            OracleDynamicCircuit.compile_measure, wp_qSeq, wp_lockBodyUnitaryCircuit]
          have hm_bot : wp (QProg.measureRegister (Var := Var) res (markerReg n m k ⟨0, hm1⟩)) ⊥ =
              ⊥ := by
            funext ν; ext1; ext x y
            rw [QProg.measureRegister, wp_qMeasure, CQAssertion.qMeasure_coe,
              HermitianMat.mat_finset_sum]; simp
          rw [hm_bot, CQAssertion.qAssign_bot]
        simp [whileRecWP, hg, hbot]
    | succ t ih =>
        rw [whileRecWP]; simp only [hg, ↓reduceIte]; rw [wp_lockBodyCircuit_dotProduct]
        have hcard_a : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card = r :=
          validStageBasis_card_sdiff hScard (le_of_lt j.isLt) ha
        have hcard_b : (S \ memFoundSet n m k (activeMemSlots k j.val) b).card = r :=
          validStageBasis_card_sdiff hScard (le_of_lt j.isLt) hb
        obtain ⟨hp0_a, hp1_a⟩ := lockBodyUnitary_outcomes hm1 ha (hcard_odd _ hcard_a).1
          (hcard_odd _ hcard_a).2 K (hcard_a.symm ▸ hsin3) (hcard_a.symm ▸ hcos1) s (hcard_a.symm ▸
          hclamp) hs0 hs1
        obtain ⟨hp0_b, hp1_b⟩ := lockBodyUnitary_outcomes hm1 hb (hcard_odd _ hcard_b).1
          (hcard_odd _ hcard_b).2 K (hcard_b.symm ▸ hsin3) (hcard_b.symm ▸ hcos1) s (hcard_b.symm ▸
          hclamp) hs0 hs1
        have hg0 : lockGuard res (Store.subst τ res 0) := (by simp [lockGuard])
        have hg1 : ¬ lockGuard res (Store.subst τ res 1) := (by simp [lockGuard])
        rw [whileRecWP_succ_apply_of_not _ hg1, hp0_a, hp0_b, hp1_a, hp1_b, hcard_a, hcard_b,
          Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, ih (Store.subst τ res 0) hg0,
          wp_lockExitCircuit_dotProduct res hm1 j hScard (Store.subst τ res 1) ha hb hcard_odd K
          hsin3 hcos1 s hclamp hs0 hs1]
        by_cases hab : a = b
        · subst hab; simp only [↓reduceIte]; dsimp [q, α, θ]; push_cast [pow_succ']; ring
        · simp [hab]
  -- Helper sandwiching `wp cInit (wp cPrep Φ)` with `diagProj (ValidStageBasis... j)`
  have hsandwich (Φ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (val : ℝ) (hdot : ∀ τ,
    lockGuard
    res τ → ∀ {a b}, ValidStageBasis n m k S j.val a → ValidStageBasis n m k S j.val b → star
    (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ ((Φ τ).1.mat *ᵥ (Uprep.1 *ᵥ Pi.single b 1)) = if a = b then (val :
    ℂ) else 0) (σ : Store Var) : diagProj (ValidStageBasis n m k S j.val) * (wp cInit (wp cPrep Φ)
    σ).1.mat * diagProj (ValidStageBasis n m k S j.val) = (val : ℂ) • diagProj (ValidStageBasis n m
    k S j.val) := by
    rw [diagProj_wp_measureInit, wp_lockPrepCircuit]; ext a b
    rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]
    by_cases hv : ValidStageBasis n m k S j.val a ∧ ValidStageBasis n m k S j.val b
    · obtain ⟨ha, hb⟩ := hv; simp only [ha, hb, and_self, ↓reduceIte]
      rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
        conjTranspose_mul_mul_apply_single,
        hdot (Store.subst σ res 0) (by simp [lockGuard]) ha hb]
      by_cases hab : a = b
      · subst hab; simp [diagProj, ha]
      · simp [hab, diagProj]
    · rw [diagProj, Matrix.diagonal_apply]; by_cases hab : a = b
      · subst hab; have hna : ¬ ValidStageBasis n m k S j.val a := fun ha ↦ hv ⟨ha, ha⟩; simp [hna]
      · simp [hv, hab]
  set Δinit := (interp cInit).toStateFun Δ; set Δprep := (interp cPrep).toStateFun Δinit
  set Δout := (interp prog).toStateFun Δ
  -- Part 1 & 2: Correctness and trace preservation
  have hexp_ge (t : ℕ) : (1 - q ^ t) * Δ.trace ≤
      𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] := by
    have hle_wp : whileRecWP (wp cBody) (lockGuard res) (t + 1) Ψ ≤ wp cLoop Ψ :=
      whileRecWP_le_wp_qWhile _ _ (t + 1) _
    have hexp1 : 𝔼[Δprep, whileRecWP (wp cBody) (lockGuard res) (t + 1) Ψ] ≤
        𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] := by
      have hout_eq : 𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] =
          𝔼[Δprep, wp cLoop Ψ] := by
        rw [← wp_expectation_eq prog Δ, hprog_eq, wp_qSeq, wp_expectation_eq cInit Δ,
          wp_qSeq, wp_expectation_eq cPrep Δinit, wp_qSeq]
      rw [hout_eq]; exact expect_mono le_rfl hle_wp
    rw [← wp_expectation_eq cPrep Δinit, ← wp_expectation_eq cInit Δ, expect_of_supportedOn hΔ
      (hsandwich _ (1 - q ^ t) fun τ hg _ _ ha hb ↦ hrec_dot t τ hg ha hb)] at hexp1; exact hexp1
  have htend : Filter.Tendsto (fun t : ℕ ↦ (1 - q ^ t) * (Δ.trace : ℝ))
      Filter.atTop (nhds (Δ.trace : ℝ)) := by
    have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp0).mul
      (tendsto_const_nhds (x := (Δ.trace : ℝ)))
  have htrace_le1 :
      𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] ≤ (Δout.trace : ℝ) := by
    rw [← expect_top Δout]; exact expect_mono le_rfl le_top
  have htrace_le2 : Δout.trace ≤ Δ.trace := (interp prog).trace_toStateFun_le Δ
  have hge_lim : (Δ.trace : ℝ) ≤ 𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] :=
    le_of_tendsto' htend hexp_ge
  have htrace_eq : Δout.trace = Δ.trace :=
    le_antisymm htrace_le2 (NNReal.coe_le_coe.mp (hge_lim.trans htrace_le1))
  have hexp_eq : 𝔼[Δout, diagAssertion (ValidStageBasis n m k S (j.val + 1))] = (Δout.trace : ℝ) :=
    le_antisymm htrace_le1 (htrace_eq ▸ hge_lim)
  have hsupp_out : SupportedOn (ValidStageBasis n m k S (j.val + 1)) Δout :=
    supportedOn_of_expect_diagAssertion_eq_trace hexp_eq
  -- Part 3: Expected cost bound
  have hact_mass (t : ℕ) :
      ((activeIter (lockGuard res) cBody t Δprep).trace : ℝ≥0∞) =
        (Δ.trace : ℝ≥0∞) * (ENNReal.ofReal q) ^ t := by
    have hexp := expect_whileActiveWP (lockGuard res) cBody t Δprep
    rw [← wp_expectation_eq cPrep Δinit, ← wp_expectation_eq cInit Δ,
      expect_of_supportedOn hΔ (hsandwich _ (q ^ t) fun τ hg _ _ ha hb ↦ by
        simpa [hg] using hact_dot t τ ha hb)] at hexp
    nth_rw 1 [← ENNReal.ofReal_coe_nnreal]
    rw [← hexp, mul_comm (q ^ t), ENNReal.ofReal_mul Δ.trace.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow hq_nn]
  have hexp_iter : expectedIterations (lockGuard res) cBody Δprep =
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - q)⁻¹) := by
    rw [expectedIterations]; simp_rw [hact_mass]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _
      hq_nn, ENNReal.ofReal_inv_of_pos h1mq_pos]
  let model : CostModel (2 ^ findAllQubits n m k) :=
    CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
  have hcost : expectedCost model prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((relCostLock :
    ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
    rw [hprog_eq, expectedCost_qSeq, expectedCost_qSeq, expectedCost_qSeq]
    have hc_init : expectedCost model cInit Δ = 0 := (by simp [cInit, QProg.measureRegister, model])
    have hmass_init_le : (Δinit.trace : ℝ≥0∞) ≤ (Δ.trace : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr ((interp cInit).trace_toStateFun_le Δ)
    have hc_prep :
        expectedCost model cPrep Δinit ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 1) := by
      have hcb := costBound_lockPrepCircuit (Var := Var) n m k (activeMemSlots k j.val) S K Δinit
      have hk_coe : (((K : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) + 1) := by
        rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
      rw [hk_coe] at hcb; exact hcb.trans (mul_le_mul_of_nonneg_right hmass_init_le zero_le)
    have hc_loop :
        expectedCost model cLoop Δprep ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - q)⁻¹) := by
      have hbody := costBound_lockBodyCircuit (Var := Var) res n m k hm1
        (activeMemSlots k j.val) s S
      calc expectedCost model cLoop Δprep ≤ expectedIterations (lockGuard res) cBody Δprep * (1 :
            ℝ≥0∞) := expectedCost_qWhile_le hbody _ Δprep
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - q)⁻¹) := by rw [mul_one, hexp_iter]
    set Δloop := (interp cLoop).toStateFun Δprep
    have hmass_loop_le : (Δloop.trace : ℝ≥0∞) ≤ (Δ.trace : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr <|
        ((interp cLoop).trace_toStateFun_le Δprep).trans <|
          ((interp cPrep).trace_toStateFun_le Δinit).trans ((interp cInit).trace_toStateFun_le Δ)
    have hc_exit : expectedCost model cExit Δloop ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
      have hcb := costBound_lockExitCircuit (Var := Var) res n m k j S Δloop
      simpa using hcb.trans (mul_le_mul_of_nonneg_right hmass_loop_le zero_le)
    rw [hc_init, zero_add]
    have hsum_cost : expectedCost model cPrep Δinit + (expectedCost model cLoop Δprep + expectedCost
      model cExit Δloop) ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 3 + q / (1 - q)) := by
      calc expectedCost model cPrep Δinit + (expectedCost model cLoop Δprep + expectedCost model
            cExit Δloop) ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 1) + ((Δ.trace : ℝ≥0∞) *
            ENNReal.ofReal ((1 - q)⁻¹) + (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1) := add_le_add hc_prep
            (add_le_add hc_loop hc_exit)
        _ = (Δ.trace : ℝ≥0∞) * (ENNReal.ofReal ((K : ℝ) + 1) +
              ENNReal.ofReal ((1 - q)⁻¹) + ENNReal.ofReal 1) := by ring
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 1 + (1 - q)⁻¹ + 1) := by
            congr 1
            rw [← ENNReal.ofReal_add (by positivity) (inv_nonneg.2 h1mq_pos.le),
              ← ENNReal.ofReal_add (by positivity) zero_le_one]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 3 + q / (1 - q)) := by
            congr 2
            have hinv_eq : (1 - q)⁻¹ = 1 + q / (1 - q) := (by field_simp [h1mq_pos.ne']; ring)
            linarith
    exact hsum_cost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hcost_ratio) zero_le)
  exact ⟨hsupp_out, htrace_eq, hcost⟩
/-- Sequence of the last `rem` Stationary-chord stages `k - rem.. k - 1`. -/
noncomputable def lockStagesRemCircuit {Var : Type} (res : Var) (n m k : ℕ) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | 0 => .skip
  | rem + 1 =>
      if h : k - (rem + 1) < k then
        .seq (lockStageCircuit res n m k ⟨k - (rem + 1), h⟩)
          (lockStagesRemCircuit res n m k rem)
      else
        .skip
theorem lockStagesRem_transition {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hn : 100
    ≤ n) (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024) {S : Finset (Fin (2 ^ n))} (hScard :
    S.card = k) : ∀ rem ≤ k, ∀ Δ : CQState (Store Var) (2 ^ findAllQubits n m k), SupportedOn
    (ValidStageBasis n m k S (k - rem)) Δ →
      let prog := (lockStagesRemCircuit res n m k rem).compile
        QProg.qAssign (parallelMarkingOracle m S)
      SupportedOn (ValidStageBasis n m k S k) ((interp prog).toStateFun Δ) ∧ ((interp
        prog).toStateFun Δ).trace = Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle
        (parallelMarkingOracle m S)) prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (∑ r ∈ Finset.Icc
        1 rem, ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  intro rem
  induction rem with
  | zero =>
      intro _ Δ hΔ; have hempty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, ENNReal.ofReal_zero, mul_zero]; refine ⟨hΔ, rfl, ?_⟩
      simp [lockStagesRemCircuit]
  | succ rem ih =>
      intro hrem Δ hΔ; have hklt : k - (rem + 1) < k := (by omega)
      simp only [lockStagesRemCircuit, hklt, ↓reduceDIte, OracleDynamicCircuit.compile_seq,
        interp_qSeq, QMonad.Q.toStateFun_bind, expectedCost_qSeq]
      let j : Fin k := ⟨k - (rem + 1), hklt⟩
      have hj_rem : k - j.val = rem + 1 := (by dsimp only [j]; omega)
      have hsucc_eq : j.val + 1 = k - rem := (by dsimp only [j]; omega)
      obtain ⟨hsupp1, htr1, hcost1⟩ := lockStage_transition res hn hm1 hm1024 hk1024 hScard j hΔ
      rw [hsucc_eq] at hsupp1; rw [hj_rem] at hcost1
      set Δ₁ := (interp ((lockStageCircuit res n m k j).compile
        QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ
      obtain ⟨hsupp2, htr2, hcost2⟩ := ih (by omega) Δ₁ hsupp1; refine ⟨hsupp2, htr2.trans htr1, ?_⟩
      have hmass1 : (Δ₁.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr1
      let termFn (r : ℕ) : ℝ :=
        ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)
      have hc1_nn : 0 ≤ termFn (rem + 1) := (by dsimp [termFn]; positivity)
      have hsum_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 rem, termFn r :=
        Finset.sum_nonneg fun r _ ↦ by dsimp [termFn]; positivity
      calc _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (termFn (rem + 1)) +
              (Δ₁.trace : ℝ≥0∞) * ENNReal.ofReal (∑ r ∈ Finset.Icc 1 rem, termFn r) :=
            add_le_add hcost1 hcost2
        _ = (Δ.trace : ℝ≥0∞) * (ENNReal.ofReal (∑ r ∈ Finset.Icc 1 rem, termFn r) +
              ENNReal.ofReal (termFn (rem + 1))) := by
            rw [hmass1, mul_add, add_comm]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (∑ r ∈ Finset.Icc 1 (rem + 1), termFn r) := by
            rw [← ENNReal.ofReal_add hsum_nn hc1_nn,
              Finset.sum_Icc_succ_top (by omega : 1 ≤ rem + 1)]
/-! ### Zero-iteration non-certified cell fallback (`findAllLockCircuit`) -/
/-- Zero-iteration uniform-sampling fallback `OracleDynamicCircuit` for non-certified
  `(n, m, k)` cells (`noncomputable abbrev` preserving kernel reducibility-hint height). -/
noncomputable abbrev findAllLockCircuit {Var : Type} (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) := findAllCircuit res (fun _ _ _ ↦ 0) n m k
theorem p_succ_set_zero_pos {n r : ℕ} (hr1 : 1 ≤ r) (hrN : r ≤ 2 ^ n) : 0 < p_succ_set 0 n r := by
  simp only [p_succ_set, Nat.cast_zero, mul_zero, zero_add, one_mul, halfAngleSet]
  have h0 : 0 ≤ (r : ℝ) / 2 ^ n := (by positivity)
  have h1 : (r : ℝ) / 2 ^ n ≤ 1 := (by rw [div_le_one (by positivity)]; exact_mod_cast hrN)
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((r : ℝ) / 2 ^ n)]) (Real.sqrt_le_one.2 h1),
    Real.sq_sqrt h0]; positivity
theorem findAllLock_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hmk : isGridCell m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))}
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) ⦄
    (QProg.qSet ;; (findAllLockCircuit res n m k).compile QProg.qAssign
      (parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄ := by
  rw [isGridCell, Bool.and_eq_true] at hmk; have hm1 : 1 ≤ m := pos_of_isGridElem hmk.1
  have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2
  exact findAllProgram_correctness res (fun _ _ _ ↦ 0) hm1 hScard hkN fun _ hr1 hrk ↦
    p_succ_set_zero_pos hr1 (hrk.trans hkN)
end QuantumComputation.Specs.GroverFindAll
end
end Sec_LockOddSetStage
section Sec_BoundaryLock
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
/-! ## 1. Certified Rational Bound via Mathlib's `Real.pi_gt_d20` -/
/-- Certified asymptotic relative cost via Mathlib's `Real.pi_gt_d20` (within `1.86 × 10⁻²¹` of
  `1 / 2 + 1 / π`) across all 121 grid cells. -/
def relCostBoundary : ℚ≥0 :=
  514159265358979323847 / 628318530717958647692
namespace BoundaryLockHelpers
/-! ## 2. Stage & Multi-Stage Expected-Cost Bounds (`n ≥ 200`) -/
private theorem le_1024_of_isGridElem {x : ℕ} (hx : isGridElem x = true) : x ≤ 1024 := by
  obtain ⟨i, hi, rfl⟩ := (isGridElem_iff x).1 hx; rw [Finset.mem_range] at hi
  exact Nat.pow_le_pow_right (by omega) (by omega : i ≤ 10)
/-- Numerical and schedule bounds for stage `r` when `200 ≤ n` and `1 ≤ m, r ≤ 1024`,
  certifying relative cost `relCostBoundary`. -/
theorem oddFrac_bounds_of_ge_200 {n m r : ℕ} (hn : 200 ≤ n)
    (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hr1 : 1 ≤ r) (hr1024 : r ≤ 1024) :
    let θ := halfAngleOdd n m r; let K := lockOddSched n m r; let q := nonTargetAngleRatio θ K ^ 2
    (∀ A : Finset (Fin (2 ^ n)), A.card = r → 1 ≤ (oddSet n m A).card ∧ (oddSet n m A).card < 2 ^
      (m * n)) ∧ clampedOddRatio n m r = targetAngleRatio θ K ∧ Real.sin ((2 * (K : ℝ) + 3) * θ) ≠ 0
      ∧ Real.cos ((2 * (K : ℝ) + 1) * θ) ≠ 0 ∧ 0 ≤ q ∧ q < 1 ∧ (K : ℝ) + 3 + q / (1 - q) ≤
      ((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
  intro θ K q
  obtain ⟨hcard_bounds, hclamp, hsin3, hcos1, hq_nn, hq_lt1, _⟩ :=
    oddFrac_bounds_of_ge_100 (by omega : 100 ≤ n) hm1 hm1024 hr1 hr1024
  have hmr_pos : (0 : ℝ) < (m : ℝ) * (r : ℝ) := (by positivity)
  have hmr_le : (m : ℝ) * (r : ℝ) ≤ (2 : ℝ) ^ 20 := by
    have hmR : (m : ℝ) ≤ 1024 := (by exact_mod_cast hm1024)
    have hrR : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
    exact (mul_le_mul hmR hrR (by positivity) (by positivity)).trans (by norm_num)
  have hdiv_ge : ((2 : ℝ) ^ 90) ^ 2 ≤ (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) := by
    rw [le_div_iff₀ hmr_pos]
    calc ((2 : ℝ) ^ 90) ^ 2 * ((m : ℝ) * (r : ℝ)) ≤ ((2 : ℝ) ^ 90) ^ 2 * (2 : ℝ) ^ 20 :=
          mul_le_mul_of_nonneg_left hmr_le (by positivity)
      _ = (2 : ℝ) ^ 200 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  set Smr : ℝ := √((2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ))) with hSmr_def
  have hSmr_ge90 : (2 : ℝ) ^ 90 ≤ Smr := by
    calc (2 : ℝ) ^ 90 = √(((2 : ℝ) ^ 90) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Smr := Real.sqrt_le_sqrt hdiv_ge
  have hSmr_ge16 : (16 : ℝ) ≤ Smr :=
    le_trans (by norm_num : (16 : ℝ) ≤ (2 : ℝ) ^ 90) hSmr_ge90
  have hSmr_pos : 0 < Smr := lt_of_lt_of_le (by positivity) hSmr_ge16
  have hSmr_sq : Smr ^ 2 = (2 ^ n : ℝ) / ((m : ℝ) * (r : ℝ)) := Real.sq_sqrt (by positivity)
  set p : ℝ := (m : ℝ) * (r : ℝ) / (2 ^ n : ℝ) with hp_def
  have hp_eq_inv_sq : p = 1 / Smr ^ 2 := (by rw [hSmr_sq, one_div_div])
  have h2n_ge2048 : (2048 : ℝ) ≤ (2 ^ n : ℝ) := by
    have h11 : (2 : ℝ) ^ 11 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    exact (by norm_num : (2048 : ℝ) = (2 : ℝ) ^ 11).le.trans h11
  set y : ℝ := 2 * (r : ℝ) / (2 ^ n : ℝ); have hy0 : 0 ≤ y := (by positivity)
  have hy1 : y ≤ 1 := by
    have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024); rw [div_le_one (by positivity)]
    exact (mul_le_mul_of_nonneg_left hr_le (by norm_num)).trans
      ((by norm_num : (2 : ℝ) * 1024 = 2048).le.trans h2n_ge2048)
  have hmy : (m : ℝ) * y = 2 * p := (by dsimp only [y, p]; ring)
  have hodd_le : oddFrac n m r ≤ p := by
    have h1 := one_sub_mul_le_pow hy0 hy1 m; unfold oddFrac; linarith only [h1, hmy]
  have hodd_ge1 : p * (1 - 2 * p) ≤ oddFrac n m r := by
    have h2 := pow_le_one_sub_mul_add_sq hy0 hy1 m
    have hmy2 : (m : ℝ) ^ 2 * y ^ 2 = 4 * p ^ 2 := by
      calc (m : ℝ) ^ 2 * y ^ 2 = ((m : ℝ) * y) ^ 2 := by ring
        _ = (2 * p) ^ 2 := by rw [hmy]
        _ = 4 * p ^ 2 := by ring
    unfold oddFrac; linarith only [h2, hmy, hmy2]
  have hpoly : 1 ≤ (Smr + 2) ^ 2 * (p * (1 - 2 * p)) := by
    rw [hp_eq_inv_sq]; have hne : Smr ≠ 0 := hSmr_pos.ne'
    have hdiff : (Smr + 2) ^ 2 * ((1 / Smr ^ 2) * (1 - 2 * (1 / Smr ^ 2))) - 1 =
        ((Smr - 2) * (4 * Smr ^ 2 + 10 * Smr + 12) + 16) / Smr ^ 4 := by
      field_simp [hne]; ring
    have h2_le_Smr : (2 : ℝ) ≤ Smr := le_trans (by norm_num : (2 : ℝ) ≤ 16) hSmr_ge16
    have hsub_nn : 0 ≤ Smr - 2 := sub_nonneg.mpr h2_le_Smr
    have hquad_nn : 0 ≤ 4 * Smr ^ 2 + 10 * Smr + 12 := (by positivity)
    have hnum_nn : 0 ≤ (Smr - 2) * (4 * Smr ^ 2 + 10 * Smr + 12) + 16 :=
      add_nonneg (mul_nonneg hsub_nn hquad_nn) (by norm_num)
    have hrhs_nn : 0 ≤ ((Smr - 2) * (4 * Smr ^ 2 + 10 * Smr + 12) + 16) / Smr ^ 4 :=
      div_nonneg hnum_nn (by positivity)
    linarith only [hdiff, hrhs_nn]
  have hp1m2p_pos : 0 < p * (1 - 2 * p) :=
    pos_of_mul_pos_right (lt_of_lt_of_le zero_lt_one hpoly) (by positivity)
  have hodd_pos : 0 < oddFrac n m r := lt_of_lt_of_le hp1m2p_pos hodd_ge1; set x := √(oddFrac n m r)
  have hx0 : 0 < x := Real.sqrt_pos.2 hodd_pos
  have hx16 : x ≤ 1 / 16 := by
    have hp16 : p ≤ (1 / 16 : ℝ) ^ 2 := by
      rw [hp_eq_inv_sq, _root_.one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hSmr_ge16 2)
    calc x ≤ √((1 / 16 : ℝ) ^ 2) := Real.sqrt_le_sqrt (hodd_le.trans hp16)
      _ = 1 / 16 := Real.sqrt_sq (by norm_num)
  have hQ_bound : (K : ℝ) + 3 + q / (1 - q) ≤ (π / 8 + 1 / 4) * (1 / x) + 4 :=
    (lockAngle_hyps_le hx0 hx16).2
  have hinv_x : 1 / x ≤ Smr + 2 := by
    have hs := Real.sqrt_le_sqrt (hpoly.trans (mul_le_mul_of_nonneg_left hodd_ge1 (by positivity)))
    rw [Real.sqrt_one, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hs
    exact (div_le_iff₀ hx0).mpr hs
  have hstep1 : (π / 8 + 1 / 4) * (1 / x) + 4 ≤ (π / 8 + 1 / 4) * Smr + 6 := by
    have hmul := mul_le_mul_of_nonneg_left hinv_x (by positivity : (0 : ℝ) ≤ π / 8 + 1 / 4)
    have hpi := Real.pi_lt_d2; linarith only [hmul, hpi]
  have hgap6 : 6 ≤ (((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) - (π / 8 + 1 / 4)) * Smr := by
    have hπ20 : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
    have hrelR : ((relCostBoundary : ℚ≥0) : ℝ) =
        514159265358979323847 / 628318530717958647692 := by
      dsimp only [relCostBoundary]; norm_num
    have hcoeff : (1 / 10 ^ 21 : ℝ) ≤
        ((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) - (π / 8 + 1 / 4) := by
      rw [hrelR]; linarith
    have h2_90 : (6 * 10 ^ 21 : ℝ) ≤ (2 : ℝ) ^ 90 := by norm_num
    nlinarith [hcoeff, hSmr_ge90, h2_90]
  have hSmr_split : Smr = (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
    rw [hSmr_def, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_div (by positivity)]
    ring
  have hcost_final : (K : ℝ) + 3 + q / (1 - q) ≤ ((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) *
    (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
    have hcost_smr : (K : ℝ) + 3 + q / (1 - q) ≤
        (((relCostBoundary : ℚ≥0) : ℝ) * (π / 4)) * Smr := by
      linarith only [hQ_bound, hstep1, hgap6]
    calc (K : ℝ) + 3 + q / (1 - q)
        ≤ (((relCostBoundary : ℚ≥0) : ℝ) * (π / 4)) * Smr := hcost_smr
      _ = ((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) *
            (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := by
          rw [hSmr_split]; ring
  exact ⟨hcard_bounds, hclamp, hsin3, hcos1, hq_nn, hq_lt1, hcost_final⟩
theorem lockStage_transition_boundary {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hn
    : 200 ≤ n) (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) (j : Fin k) {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ :
      SupportedOn
    (ValidStageBasis n m k S j.val) Δ) :
    let prog := (lockStageCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle m S)
    let r := k - j.val
    SupportedOn (ValidStageBasis n m k S (j.val + 1)) ((interp prog).toStateFun Δ) ∧ ((interp
      prog).toStateFun Δ).trace = Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle
      (parallelMarkingOracle m S)) prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal
      (((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  intro prog r
  obtain ⟨hsupp_out, htrace_eq, _⟩ :=
    lockStage_transition res (by omega : 100 ≤ n) hm1 hm1024 hk1024 hScard j hΔ
  have hr1 : 1 ≤ r := (by dsimp only [r]; omega)
  have hr1024 : r ≤ 1024 := (by dsimp only [r]; omega)
  obtain ⟨hcard_odd, hclamp, hsin3, hcos1, hq_nn, hq_lt, hcost_ratio⟩ :=
    oddFrac_bounds_of_ge_200 hn hm1 hm1024 hr1 hr1024
  obtain ⟨hs0, hs1⟩ := clampedOddRatio_mem_Icc n m r; set θ := halfAngleOdd n m r
  generalize hK_def : lockOddSched n m r = K; generalize hs_def : clampedOddRatio n m r = s
  rw [hK_def] at hclamp hsin3 hcos1 hq_nn hq_lt hcost_ratio; rw [hs_def] at hclamp hs0 hs1
  set α := nonTargetAngleRatio θ K; set q := α ^ 2; have h1mq_pos : 0 < 1 - q := (by linarith)
  set cInit : QProg Var (2 ^ findAllQubits n m k) := QProg.measureRegister res (oracleReg n m k)
  set cPrep : QProg Var (2 ^ findAllQubits n m k) := (lockPrepCircuit n m k (activeMemSlots k
    j.val) K).compile QProg.qAssign (parallelMarkingOracle m S)
  set cBody : QProg Var (2 ^ findAllQubits n m k) := (lockBodyCircuit res n m k hm1
    (activeMemSlots k j.val) s).compile QProg.qAssign (parallelMarkingOracle m S)
  set cLoop : QProg Var (2 ^ findAllQubits n m k) := .qWhile (lockGuard res) cBody
  set cExit : QProg Var (2 ^ findAllQubits n m k) :=
    (lockExitCircuit res n m k j).compile QProg.qAssign (parallelMarkingOracle m S)
  have hprog_eq : prog = (cInit ;; (cPrep ;; (cLoop ;; cExit))) := by
    simp [prog, lockStageCircuit, hm1, cInit, cPrep, cLoop, cBody, cExit, r, hK_def, hs_def]
  let Uprep := lockPrepUnitary n m k (activeMemSlots k j.val) S K
  have hdot_Uprep {a b : Fin (2 ^ findAllQubits n m k)} : star (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ
    (Uprep.1 *ᵥ Pi.single b 1) = if a = b then (1 : ℂ) else 0 := by
    have h := conjTranspose_mul_mul_apply_single Uprep.1 1 a b
    have hU1 : Uprep.1ᴴ * 1 * Uprep.1 = 1 := by
      rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]; exact Uprep.2.1
    rw [hU1, Matrix.one_mulVec] at h; simpa [Matrix.one_apply] using h.symm
  have hact_dot (t : ℕ) (τ : Store Var) {a b : Fin (2 ^ findAllQubits n m k)} (ha : ValidStageBasis
    n m k S j.val a) (hb : ValidStageBasis n m k S j.val b) : star (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ
    ((whileActiveWP (wp cBody) (lockGuard res) t τ).1.mat *ᵥ (Uprep.1 *ᵥ Pi.single b 1)) = if
    lockGuard res τ then if a = b then ((q ^ t : ℝ) : ℂ) else 0 else 0 := by
    induction t generalizing τ with
    | zero =>
        by_cases hg : lockGuard res τ
        · have htop : (whileActiveWP (wp cBody) (lockGuard res) 0 τ).1.mat = 1 := by
            simp [whileActiveWP, hg]
          rw [htop, Matrix.one_mulVec, ite_eq_left hg]; exact hdot_Uprep
        · have hbot0 : (whileActiveWP (wp cBody) (lockGuard res) 0 τ).1.mat = 0 := by
            simp [whileActiveWP, hg]
          rw [hbot0]; simp [hg]
    | succ t ih =>
        rw [whileActiveWP]; by_cases hg : lockGuard res τ
        · simp only [hg, ↓reduceIte]; rw [wp_lockBodyCircuit_dotProduct]
          have hcard_a : (S \ memFoundSet n m k (activeMemSlots k j.val) a).card = r :=
            validStageBasis_card_sdiff hScard (le_of_lt j.isLt) ha
          have hcard_b : (S \ memFoundSet n m k (activeMemSlots k j.val) b).card = r :=
            validStageBasis_card_sdiff hScard (le_of_lt j.isLt) hb
          obtain ⟨hp0_a, _⟩ := lockBodyUnitary_outcomes hm1 ha (hcard_odd _ hcard_a).1 (hcard_odd
            _ hcard_a).2 K (hcard_a.symm ▸ hsin3) (hcard_a.symm ▸ hcos1) s (hcard_a.symm ▸ hclamp)
            hs0 hs1
          obtain ⟨hp0_b, _⟩ := lockBodyUnitary_outcomes hm1 hb (hcard_odd _ hcard_b).1 (hcard_odd
            _ hcard_b).2 K (hcard_b.symm ▸ hsin3) (hcard_b.symm ▸ hcos1) s (hcard_b.symm ▸ hclamp)
            hs0 hs1
          have hg1 : ¬ lockGuard res (Store.subst τ res 1) := (by simp [lockGuard])
          have hterm1 : (whileActiveWP (wp cBody) (lockGuard res) t
              (Store.subst τ res 1)).1.mat = 0 := by
            cases t with
            | zero => simp [whileActiveWP, hg1]
            | succ t' => simp [whileActiveWP, hg1]
          rw [hterm1, Matrix.zero_mulVec, dotProduct_zero, add_zero, hp0_a, hp0_b, hcard_a, hcard_b,
            Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
            Complex.star_def, Complex.conj_ofReal, ih (Store.subst τ res 0)]
          have hg0 : lockGuard res (Store.subst τ res 0) := (by simp [lockGuard])
          simp only [hg0, ↓reduceIte]; by_cases hab : a = b
          · subst hab; simp only [↓reduceIte]; dsimp only [q, α, θ]; push_cast [pow_succ']; ring
          · simp [hab]
        · simp [hg]
  have hsandwich (Φ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (val : ℝ) (hdot : ∀ τ,
    lockGuard
    res τ → ∀ {a b}, ValidStageBasis n m k S j.val a → ValidStageBasis n m k S j.val b → star
    (Uprep.1 *ᵥ Pi.single a 1) ⬝ᵥ ((Φ τ).1.mat *ᵥ (Uprep.1 *ᵥ Pi.single b 1)) = if a = b then (val :
    ℂ) else 0) (σ : Store Var) : diagProj (ValidStageBasis n m k S j.val) * (wp cInit (wp cPrep Φ)
    σ).1.mat * diagProj (ValidStageBasis n m k S j.val) = (val : ℂ) • diagProj (ValidStageBasis n m
    k S j.val) := by
    rw [diagProj_wp_measureInit, wp_lockPrepCircuit]; ext a b
    rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]
    by_cases hv : ValidStageBasis n m k S j.val a ∧ ValidStageBasis n m k S j.val b
    · obtain ⟨ha, hb⟩ := hv; simp only [ha, hb, and_self, ↓reduceIte]
      rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
        conjTranspose_mul_mul_apply_single,
        hdot (Store.subst σ res 0) (by simp [lockGuard]) ha hb]
      by_cases hab : a = b
      · subst hab; simp [diagProj, ha]
      · simp [hab, diagProj]
    · rw [diagProj, Matrix.diagonal_apply]; by_cases hab : a = b
      · subst hab; have hna : ¬ ValidStageBasis n m k S j.val a := fun ha ↦ hv ⟨ha, ha⟩; simp [hna]
      · simp [hv, hab]
  set Δinit := (interp cInit).toStateFun Δ; set Δprep := (interp cPrep).toStateFun Δinit
  have hact_mass (t : ℕ) :
      ((activeIter (lockGuard res) cBody t Δprep).trace : ℝ≥0∞) =
        (Δ.trace : ℝ≥0∞) * (ENNReal.ofReal q) ^ t := by
    have hexp := expect_whileActiveWP (lockGuard res) cBody t Δprep
    rw [← wp_expectation_eq cPrep Δinit, ← wp_expectation_eq cInit Δ,
      expect_of_supportedOn hΔ (hsandwich _ (q ^ t) fun τ hg _ _ ha hb ↦ by
        simpa [hg] using hact_dot t τ ha hb)] at hexp
    nth_rw 1 [← ENNReal.ofReal_coe_nnreal]
    rw [← hexp, mul_comm (q ^ t), ENNReal.ofReal_mul Δ.trace.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow hq_nn]
  have hexp_iter : expectedIterations (lockGuard res) cBody Δprep =
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - q)⁻¹) := by
    rw [expectedIterations]; simp_rw [hact_mass]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _
      hq_nn, ENNReal.ofReal_inv_of_pos h1mq_pos]
  let model : CostModel (2 ^ findAllQubits n m k) :=
    CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
  have hcost : expectedCost model prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal
      (((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
    rw [hprog_eq, expectedCost_qSeq, expectedCost_qSeq, expectedCost_qSeq]
    have hc_init : expectedCost model cInit Δ = 0 := (by simp [cInit, QProg.measureRegister, model])
    have hmass_init_le : (Δinit.trace : ℝ≥0∞) ≤ (Δ.trace : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr ((interp cInit).trace_toStateFun_le Δ)
    have hc_prep :
        expectedCost model cPrep Δinit ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 1) := by
      have hcb := costBound_lockPrepCircuit (Var := Var) n m k (activeMemSlots k j.val) S K Δinit
      have hk_coe : (((K : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((K : ℝ) + 1) := by
        rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
      rw [hk_coe] at hcb; exact hcb.trans (mul_le_mul_of_nonneg_right hmass_init_le zero_le)
    have hc_loop :
        expectedCost model cLoop Δprep ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - q)⁻¹) := by
      have hbody := costBound_lockBodyCircuit (Var := Var) res n m k hm1
        (activeMemSlots k j.val) s S
      calc expectedCost model cLoop Δprep ≤ expectedIterations (lockGuard res) cBody Δprep * (1 :
            ℝ≥0∞) := expectedCost_qWhile_le hbody _ Δprep
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - q)⁻¹) := by rw [mul_one, hexp_iter]
    set Δloop := (interp cLoop).toStateFun Δprep
    have hmass_loop_le : (Δloop.trace : ℝ≥0∞) ≤ (Δ.trace : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr <|
        ((interp cLoop).trace_toStateFun_le Δprep).trans <|
          ((interp cPrep).trace_toStateFun_le Δinit).trans ((interp cInit).trace_toStateFun_le Δ)
    have hc_exit : expectedCost model cExit Δloop ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
      have hcb := costBound_lockExitCircuit (Var := Var) res n m k j S Δloop
      simpa using hcb.trans (mul_le_mul_of_nonneg_right hmass_loop_le zero_le)
    rw [hc_init, zero_add]
    have hsum_cost : expectedCost model cPrep Δinit + (expectedCost model cLoop Δprep + expectedCost
      model cExit Δloop) ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 3 + q / (1 - q)) := by
      calc expectedCost model cPrep Δinit + (expectedCost model cLoop Δprep + expectedCost model
            cExit Δloop) ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 1) + ((Δ.trace : ℝ≥0∞) *
            ENNReal.ofReal ((1 - q)⁻¹) + (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1) := add_le_add hc_prep
            (add_le_add hc_loop hc_exit)
        _ = (Δ.trace : ℝ≥0∞) * (ENNReal.ofReal ((K : ℝ) + 1) +
              ENNReal.ofReal ((1 - q)⁻¹) + ENNReal.ofReal 1) := by ring
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 1 + (1 - q)⁻¹ + 1) := by
            congr 1
            rw [← ENNReal.ofReal_add (by positivity) (inv_nonneg.2 h1mq_pos.le),
              ← ENNReal.ofReal_add (by positivity) zero_le_one]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) + 3 + q / (1 - q)) := by
            congr 2
            have hinv_eq : (1 - q)⁻¹ = 1 + q / (1 - q) := (by field_simp [h1mq_pos.ne']; ring)
            linarith
    exact hsum_cost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hcost_ratio) zero_le)
  exact ⟨hsupp_out, htrace_eq, hcost⟩
theorem lockStagesRem_transition_boundary {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    (hn : 200 ≤ n) (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024) {S : Finset (Fin (2 ^ n))}
    (hScard : S.card = k) : ∀ rem ≤ k, ∀ Δ : CQState (Store Var) (2 ^ findAllQubits n m k),
      SupportedOn
    (ValidStageBasis n m k S (k - rem)) Δ →
      let prog := (lockStagesRemCircuit res n m k rem).compile
        QProg.qAssign (parallelMarkingOracle m S)
      SupportedOn (ValidStageBasis n m k S k) ((interp prog).toStateFun Δ) ∧ ((interp
        prog).toStateFun Δ).trace = Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle
        (parallelMarkingOracle m S)) prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (∑ r ∈ Finset.Icc
        1 rem, ((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) *
        √((2 ^ n : ℝ) / m)) := by
  intro rem
  induction rem with
  | zero =>
      intro _ Δ hΔ; have hempty : Finset.Icc 1 0 = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, ENNReal.ofReal_zero, mul_zero]; refine ⟨hΔ, rfl, ?_⟩
      simp [lockStagesRemCircuit]
  | succ rem ih =>
      intro hrem Δ hΔ; have hklt : k - (rem + 1) < k := (by omega)
      simp only [lockStagesRemCircuit, hklt, ↓reduceDIte, OracleDynamicCircuit.compile_seq,
        interp_qSeq, QMonad.Q.toStateFun_bind, expectedCost_qSeq]
      let j : Fin k := ⟨k - (rem + 1), hklt⟩
      have hj_rem : k - j.val = rem + 1 := (by simp only [j]; omega)
      have hsucc_eq : j.val + 1 = k - rem := (by simp only [j]; omega)
      obtain ⟨hsupp1, htr1, hcost1⟩ :=
        lockStage_transition_boundary res hn hm1 hm1024 hk1024 hScard j hΔ
      rw [hsucc_eq] at hsupp1; rw [hj_rem] at hcost1
      set Δ₁ := (interp ((lockStageCircuit res n m k j).compile
        QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ
      obtain ⟨hsupp2, htr2, hcost2⟩ := ih (by omega) Δ₁ hsupp1; refine ⟨hsupp2, htr2.trans htr1, ?_⟩
      have hmass1 : (Δ₁.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr1
      let termFn (r : ℕ) : ℝ :=
        ((relCostBoundary : ℚ≥0) : ℝ) * (π / 4) * (1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)
      have hc1_nn : 0 ≤ termFn (rem + 1) := (by dsimp only [termFn]; positivity)
      have hsum_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 rem, termFn r :=
        Finset.sum_nonneg fun r _ ↦ by dsimp only [termFn]; positivity
      calc _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (termFn (rem + 1)) +
              (Δ₁.trace : ℝ≥0∞) * ENNReal.ofReal (∑ r ∈ Finset.Icc 1 rem, termFn r) :=
            add_le_add hcost1 hcost2
        _ = (Δ.trace : ℝ≥0∞) * (ENNReal.ofReal (∑ r ∈ Finset.Icc 1 rem, termFn r) +
              ENNReal.ofReal (termFn (rem + 1))) := by
            rw [hmass1, mul_add, add_comm]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (∑ r ∈ Finset.Icc 1 (rem + 1), termFn r) := by
            rw [← ENNReal.ofReal_add hsum_nn hc1_nn,
              Finset.sum_Icc_succ_top (by omega : 1 ≤ rem + 1)]
end BoundaryLockHelpers
/-! ## 4. Top-Level `BaselineRouter` Exports -/
/-- Top-level `GroverFindAll` circuit for `boundaryProfile`: uses
  `findAllLockCircuit`
  for `n < 100` and `lockStagesRemCircuit` for `100 ≤ n`. -/
noncomputable abbrev findAllBoundaryCircuit {Var : Type} (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  if n < 100 then
    findAllLockCircuit res n m k
  else
    .seq (lockStagesRemCircuit res n m k k) (.measure res (memAllReg n m k))
/-- Full-grid cost profile certifying the stationary weak-measurement locking
  bound
  `relCostBoundary` at `n ≥ 200` across all 121 cells (`validCell:= fun _ _ ↦
  true`). -/
def boundaryProfile : FindAllCostProfile where
  validCell _ _ := true
  relCost _ _ := relCostBoundary
  n0 _ _ := 200
theorem boundaryProfile_validCell (m k : ℕ) :
    boundaryProfile.validCell m k = true := rfl
theorem findAllBoundary_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hmk : isGridCell m k = true) (hkN : k ≤ 2 ^ n)
    {S : Finset (Fin (2 ^ n))}
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) ⦄
    (QProg.qSet ;; (findAllBoundaryCircuit res n m k).compile QProg.qAssign
      (parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄ := by
  unfold findAllBoundaryCircuit; by_cases hn100 : n < 100
  · rw [ite_eq_left hn100]; exact findAllLock_correctness res hmk hkN hS
  · rw [ite_eq_right hn100]; have hn : 100 ≤ n := (by omega)
    rw [isGridCell, Bool.and_eq_true] at hmk; have hm1 : 1 ≤ m := pos_of_isGridElem hmk.1
    have hm1024 : m ≤ 1024 := BoundaryLockHelpers.le_1024_of_isGridElem hmk.1
    have hk1024 : k ≤ 1024 := BoundaryLockHelpers.le_1024_of_isGridElem hmk.2
    have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2; intro Δ
    rw [expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet]
    simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
      interp_qSeq, QMonad.Q.toStateFun_bind]
    have h0 : SupportedOn (ValidStageBasis n m k S (k - k)) Δ.qSet := by
      rw [Nat.sub_self]; exact supportedOn_qSet (validStageBasis_zero n m k S) Δ
    obtain ⟨hsupp_k, htr_k, _⟩ :=
      lockStagesRem_transition res hn hm1 hm1024 hk1024 hScard k le_rfl Δ.qSet h0
    set Δ_k := (interp ((lockStagesRemCircuit res n m k k).compile
      QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ.qSet
    rw [← wp_expectation_eq (QProg.measureRegister res (memAllReg n m k)) Δ_k, expect_of_supportedOn
      hsupp_k (diagProj_wp_finalReadout res hScard), one_mul, htr_k, CQState.trace_qSet]
theorem findAllBoundary_costBound_uniform {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hmk : isGridCell m k = true) :
    ∀ n ≥ 200, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
            (QProg.qSet ;; (findAllBoundaryCircuit (Var := Var) res n m k).compile
              QProg.qAssign (parallelMarkingOracle m S))
            (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostBoundary : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  rw [isGridCell, Bool.and_eq_true] at hmk; have hm1 : 1 ≤ m := pos_of_isGridElem hmk.1
  have hm1024 : m ≤ 1024 := BoundaryLockHelpers.le_1024_of_isGridElem hmk.1
  have hk1024 : k ≤ 1024 := BoundaryLockHelpers.le_1024_of_isGridElem hmk.2; intro n hn hkN
  have hn_not_lt : ¬ n < 100 := (by omega)
  set boundReal : ℝ := ((relCostBoundary : ℚ≥0) : ℝ) *
    ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m))
  have hsum_nn : 0 ≤ ∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ) :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  have hbound_nn : 0 ≤ boundReal := (by positivity); let B : ℝ≥0 := Real.toNNReal boundReal
  have hB_coe : (B : ℝ) = boundReal := Real.coe_toNNReal boundReal hbound_nn
  refine ⟨fun _ ↦ B, ?_, ?_⟩
  · intro S hS; have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2; intro Δ
    let model : CostModel (2 ^ findAllQubits n m k) :=
      CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
    rw [findAllBoundaryCircuit, ite_eq_right hn_not_lt,
      expectedCost_qSeq, interp_qSet, QMonad.Q.toStateFun_qSet]
    have hqset : expectedCost model QProg.qSet Δ = 0 := (by simp [model]); rw [hqset, zero_add]
    simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
      expectedCost_qSeq]
    have hmeas : expectedCost model (QProg.measureRegister res (memAllReg n m k))
        ((interp ((lockStagesRemCircuit res n m k k).compile
          QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ.qSet) = 0 := by
      simp [QProg.measureRegister, model]
    rw [hmeas, add_zero]
    have h0 : SupportedOn (ValidStageBasis n m k S (k - k)) Δ.qSet := by
      rw [Nat.sub_self]; exact supportedOn_qSet (validStageBasis_zero n m k S) Δ
    obtain ⟨_, _, hcost⟩ := BoundaryLockHelpers.lockStagesRem_transition_boundary res hn hm1 hm1024
      hk1024 hScard k le_rfl Δ.qSet h0
    have hmass : (Δ.qSet.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) :=
      congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
    rw [hmass] at hcost; refine hcost.trans ?_
    gcongr
    rw [← ENNReal.ofReal_coe_nnreal, hB_coe]; apply ENNReal.ofReal_le_ofReal; dsimp only [boundReal]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]; apply le_of_eq
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    ring
  · set T := (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k
    have hcard_pos : 0 < T.card := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; exact Nat.choose_pos hkN
    have hcard_ne : (T.card : ℝ) ≠ 0 := (by positivity)
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_ne, hB_coe]
/-- Composable `ValidFindAllFamily` instance for `boundaryProfile`. -/
theorem validFamily_boundary {Var : Type} [DecidableEq Var] (res : Var) :
    ValidFindAllFamily res boundaryProfile (findAllBoundaryCircuit res) where
  correctness _hn hmk _hvalid hkN hS := findAllBoundary_correctness res hmk hkN hS
  costBound_uniform hmk _hvalid := findAllBoundary_costBound_uniform res hmk
end QuantumComputation.Specs.GroverFindAll
end
end Sec_BoundaryLock
