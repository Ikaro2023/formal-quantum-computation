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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.GrayCodeKinNucUlpCerts
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.RieszUnitCoveringQsp
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateWalkSeamElecOpt
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.TopHadStage1Tab1Shard1
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.TopHadStage1Tab2Shard1
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.TopHadStage1Tab2Shard2
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.TopHadStage1Tab2Shard3

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances

set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 8192

open _root_.QuantumComputation.Specs.PhotochemistrySolution.Pyth32Su2 (su2Diag su2Diag_neg)
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge
open scoped Matrix Matrix.Norms.L2Operator BigOperators Polynomial
open Operator QProg DynamicCircuit Matrix Circuit Qubit Real ComplexConjugate Polynomial
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore
open PhotochemistrySolution.GQSP PhotochemistrySolution.OvBidir
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationTop
/-- Special unitary `2 × 2` matrices (`Q ∈ unitaryGroup (Fin 2) ℂ` and `Q.det = 1`). -/
def IsSu2 (Q : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Q ∈ unitaryGroup (Fin 2) ℂ ∧ Q.det = 1
def adj2 (Q : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Q 1 1, -Q 0 1; -Q 1 0, Q 0 0]

theorem adj2_mul_self (Q : Matrix (Fin 2) (Fin 2) ℂ) : adj2 Q * Q = Q.det • (1 : Matrix (Fin 2)
    (Fin 2) ℂ) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [adj2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem su2_entries_of_isSu2 {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSu2 Q) : Q 1 1 = conj (Q 0 0) ∧
    Q 0 1 = -conj (Q 1 0) ∧ (Q 0 0).re ^ 2 + (Q 0 0).im ^ 2 + (Q 1 0).re ^ 2 + (Q 1 0).im ^ 2 =
    1 := by
  have hQQh : Q * Qᴴ = 1 := by simpa [star_eq_conjTranspose] using Unitary.mul_star_self_of_mem hQ.1
  have hQhQ : Qᴴ * Q = 1 := by simpa [star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hQ.1
  have hadj : adj2 Q = Qᴴ := by
    rw [← Matrix.mul_one (adj2 Q), ← hQQh, ← Matrix.mul_assoc, adj2_mul_self, hQ.2, one_smul,
      Matrix.one_mul]
  have h10 : -Q 1 0 = conj (Q 0 1) :=
    by simpa [adj2, Matrix.conjTranspose_apply] using congr_fun (congr_fun hadj 1) 0
  refine ⟨by simpa [adj2, Matrix.conjTranspose_apply] using congr_fun (congr_fun hadj 0) 0,
    by simpa [map_neg, Complex.conj_conj] using (congrArg (starRingEnd ℂ) h10).symm, ?_⟩
  have hcol0 := congrArg Complex.re (congr_fun (congr_fun hQhQ 0) 0)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq, Complex.star_def, Complex.add_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.one_re] at hcol0
  nlinarith

/-- Exact `SU(2)` identity `‖Q - 1‖ ^ 2 ≤ 2 * (1 - (Q 0 0).re)`. -/
theorem su2_opNorm_sub_one_sq_le {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSu2 Q) : ‖Q - 1‖ ^ 2 ≤ 2 *
    (1 - (Q 0 0).re) := by
  obtain ⟨h11, h01, hsq⟩ := su2_entries_of_isSu2 hQ
  set s : ℝ := 2 * (1 - (Q 0 0).re)
  have hs_nn : 0 ≤ s := show 0 ≤ 2 * (1 - (Q 0 0).re) by nlinarith [sq_nonneg ((Q 0 0).re - 1)]
  have hsum : Qᴴ + Q = ((2 * (Q 0 0).re : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply,
        Fin.zero_eta, Fin.mk_one, ↓reduceIte, zero_ne_one, one_ne_zero, smul_eq_mul, mul_one,
        mul_zero, h01, h11] <;> (apply Complex.ext <;> (simp; try ring))
  have hprod : (Q - 1)ᴴ * (Q - 1) = (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [show (Q - 1)ᴴ * (Q - 1) = Qᴴ * Q + 1 - (Qᴴ + Q) by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
        noncomm_ring,
      show Qᴴ * Q = 1 by simpa [star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hQ.1,
      hsum]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [s] <;> ring
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self (Q - 1), hprod, norm_smul,
    Complex.norm_of_nonneg hs_nn]
  exact (mul_le_mul_of_nonneg_left (GQSP.norm_le_one_of_mem_unitaryGroup (one_mem _))
      hs_nn).trans_eq (mul_one _)

/--
First-column Euclidean bound `(M 0 0).re^2 + (M 0 0).im^2 + (M 1 0).re^2 + (M 1 0).im^2 ≤ ‖M‖^2`
for ANY `2 × 2` complex matrix `M`.
-/
theorem col0_four_sq_le_opNorm_sq (M : Matrix (Fin 2) (Fin 2) ℂ) : (M 0 0).re ^ 2 + (M 0 0).im ^ 2 +
    (M 1 0).re ^ 2 + (M 1 0).im ^ 2 ≤ ‖M‖ ^ 2 := by
  let e0 : Fin 2 → ℂ := ![1, 0]
  have he0_sq : pgL2Norm e0 ^ 2 = 1 := by rw [pgL2Norm_sq, Fin.sum_univ_two]; simp [e0]
  have he0 : pgL2Norm e0 = 1 := by have hnn : 0 ≤ pgL2Norm e0 := norm_nonneg _; nlinarith
  have hle := qubTop_pgL2Norm_mulVec_le_opNorm M e0; rw [he0, mul_one] at hle;
  have hsq : pgL2Norm (M *ᵥ e0) ^ 2 ≤ ‖M‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg M)).mpr hle
  have hmv0 : (M *ᵥ e0) 0 = M 0 0 := by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e0]
  have hmv1 : (M *ᵥ e0) 1 = M 1 0 := by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e0]
  have hc_sq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z ↦ by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [pgL2Norm_sq, Fin.sum_univ_two, hmv0, hmv1, hc_sq, hc_sq] at hsq; linarith
abbrev IsSU2 : Matrix (Fin 2) (Fin 2) ℂ → Prop := IsSu2

/-- Chordal semi-distance `1 - Re(Q₀₀)` from `1` on `SU(2)`. -/
def chordalY (Q : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := 1 - (Q 0 0).re
theorem isSU2_one : IsSU2 1 := ⟨one_mem _, Matrix.det_one⟩
theorem chordalY_one : chordalY 1 = 0 := by simp [chordalY]
theorem isSU2_mul {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsSU2 P) (hQ : IsSU2 Q) : IsSU2 (P * Q) :=
  ⟨mul_mem hP.1 hQ.1, by rw [Matrix.det_mul, hP.2, hQ.2, one_mul]⟩

theorem isSU2_entries {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSU2 Q) :
    Q 1 1 = conj (Q 0 0) ∧ Q 0 1 = -conj (Q 1 0) ∧
      (Q 0 0).re ^ 2 + (Q 0 0).im ^ 2 + (Q 1 0).re ^ 2 + (Q 1 0).im ^ 2 = 1 :=
  su2_entries_of_isSu2 hQ

theorem trace_re_of_isSU2 {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSU2 Q) : (Q.trace).re = 2 *
    (Q 0 0).re := by
  obtain ⟨h11, _, _⟩ :=
      isSU2_entries hQ; simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, h11, Complex.add_re,
      Complex.conj_re]; ring
theorem isSU2_conj_unitary {U Q : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ unitaryGroup (Fin 2) ℂ)
    (hQ : IsSU2 Q) : IsSU2 (U * Q * Uᴴ) ∧ chordalY (U * Q * Uᴴ) = chordalY Q := by
  have hUU1 : U * Uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hU
  have hU1U : Uᴴ * U = 1 := by rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hU
  have hUs : Uᴴ ∈ unitaryGroup (Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact hU1U
  have hSU2 : IsSU2 (U * Q * Uᴴ) := by
    refine ⟨mul_mem (mul_mem hU hQ.1) hUs, ?_⟩;
    rw [Matrix.det_mul, Matrix.det_mul, hQ.2, mul_one, ← Matrix.det_mul, hUU1, Matrix.det_one]
  refine ⟨hSU2, ?_⟩
  have htr : (U * Q * Uᴴ).trace = Q.trace := by
    rw [Matrix.trace_mul_comm (U * Q) Uᴴ, ← Matrix.mul_assoc, hU1U, Matrix.one_mul]
  have hre :=
      congrArg Complex.re htr; rw [trace_re_of_isSU2 hSU2,
      trace_re_of_isSU2 hQ] at hre; unfold chordalY; linarith
theorem chordalY_bounds {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSU2 Q) :
    0 ≤ chordalY Q ∧ |1 - chordalY Q| ≤ 1 ∧
      (-(Q 0 0).im) ^ 2 ≤ 2 * chordalY Q ∧ |-(Q 0 0).im| ≤ 1 := by
  obtain ⟨_, _, hsum⟩ := isSU2_entries hQ
  have hre_abs : |(Q 0 0).re| ≤ 1 :=
      abs_le.mpr ⟨by nlinarith [sq_nonneg ((Q 0 0).re + 1)],
      by nlinarith [sq_nonneg ((Q 0 0).re - 1)]⟩
  have him_abs : |-(Q 0 0).im| ≤ 1 :=
      abs_le.mpr ⟨by nlinarith [sq_nonneg ((Q 0 0).im - 1)],
      by nlinarith [sq_nonneg ((Q 0 0).im + 1)]⟩
  unfold chordalY
  refine ⟨by linarith [abs_le.mp hre_abs], by simpa only [sub_sub_cancel] using hre_abs, ?_,
      him_abs⟩
  nlinarith [sq_nonneg (Q 1 0).re, sq_nonneg (Q 1 0).im, sq_nonneg (1 - (Q 0 0).re)]
theorem norm_sub_one_le_sqrt_two_chordalY {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSU2 Q) :
    ‖Q - 1‖ ≤ √(2 * chordalY Q) :=
  (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    ((su2_opNorm_sub_one_sq_le hQ).trans_eq (Real.sq_sqrt
      (mul_nonneg zero_le_two (chordalY_bounds hQ).1)).symm)

/-! ### 2A.2 Trig Bounds, Hoeffding's 2-Point MGF Lemma, and Power-1 Riccati Step -/

theorem hoeffding_two_point {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) : (1 - p) * Real.exp (-p * t) + p * Real.exp ((1 - p) * t) ≤ Real.exp (t ^ 2 / 8) := by
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · simpa using Real.one_le_exp (show (0 : ℝ) ≤ t ^ 2 / 8 by positivity)
  · let D : ℝ → ℝ := fun s ↦ (1 - p) + p * Real.exp s
    have hD_pos (s : ℝ) : 0 < D s :=
      add_pos_of_nonneg_of_pos (by linarith) (mul_pos hp_pos (Real.exp_pos s))
    let ψ : ℝ → ℝ := fun s ↦ p + s / 4 - p * Real.exp s / D s
    have hD_deriv (s : ℝ) : HasDerivAt D (p * Real.exp s) s :=
      ((Real.hasDerivAt_exp s).const_mul p).const_add (1 - p)
    have hψ_deriv (s : ℝ) : HasDerivAt ψ (1 / 4 - (p * Real.exp s * (1 - p)) / (D s) ^ 2) s :=
      ((((hasDerivAt_id' s).div_const (4 : ℝ)).const_add p).sub
        (((Real.hasDerivAt_exp s).const_mul p).div (hD_deriv s) (hD_pos s).ne')).congr_deriv
        (by dsimp only [D]; ring)
    have hψ_mono : Monotone ψ :=
      monotone_of_deriv_nonneg (fun s ↦ (hψ_deriv s).differentiableAt) fun s ↦ by
        set q : ℝ := p * Real.exp s / D s
        rw [(hψ_deriv s).deriv, show (p * Real.exp s * (1 - p)) / (D s) ^ 2 = q * (1 - q) by
          dsimp only [q]
          rw [show 1 - p = D s - p * Real.exp s from eq_sub_of_add_eq rfl]
          field_simp [(hD_pos s).ne']]
        nlinarith [sq_nonneg (q - 1 / 2)]
    have hψ0 : ψ 0 = 0 := by simp only [ψ, D, Real.exp_zero, mul_one, sub_add_cancel]; ring
    let φ : ℝ → ℝ := fun s ↦ p * s + s ^ 2 / 8 - Real.log (D s)
    have hφ_deriv (s : ℝ) : HasDerivAt φ (ψ s) s :=
      ((((hasDerivAt_id' s).const_mul p).add ((hasDerivAt_pow 2 s).div_const (8 : ℝ))).sub
        ((hD_deriv s).log (hD_pos s).ne')).congr_deriv (by dsimp only [ψ]; ring)
    have hφ0 : φ 0 = 0 := by
      simp only [φ, D, Real.exp_zero, mul_one, sub_add_cancel, Real.log_one]; ring
    have hnn (B B' : ℝ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (h0 : B 0 = 0) (hd : ∀ s, HasDerivAt B (B' s) s)
        (hb : ∀ s ∈ Set.Ico 0 τ, 0 ≤ B' s) : 0 ≤ B τ := by
      simpa using image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun _ : ℝ ↦ (0 : ℝ))
        continuousOn_const (fun s _ ↦ (hasDerivAt_const s (0 : ℝ)).hasDerivWithinAt)
        (by simp [h0]) hd (fun s hs ↦ by simpa using hb s hs) (Set.right_mem_Icc.mpr hτ)
    have hφ_nonneg : 0 ≤ φ t := by
      rcases le_or_gt 0 t with ht | ht
      · exact hnn φ ψ t ht hφ0 hφ_deriv fun s hs ↦ hψ0 ▸ hψ_mono hs.1
      · simpa using hnn (fun s ↦ φ (-s)) (fun s ↦ -ψ (-s)) (-t) (by linarith) (by simp [hφ0])
          (fun s ↦ (HasDerivAt.comp s (hφ_deriv (-s)) (hasDerivAt_id' s).neg).congr_deriv (by ring))
          (fun s hs ↦ by linarith [hψ0, hψ_mono (show -s ≤ 0 by linarith [hs.1])])
    have hmul := mul_le_mul_of_nonneg_left ((Real.exp_log (hD_pos t)).symm.trans_le
      (Real.exp_le_exp.mpr (sub_nonneg.mp hφ_nonneg))) (Real.exp_pos (-p * t)).le
    rwa [show Real.exp (-p * t) * D t = (1 - p) * Real.exp (-p * t) + p * Real.exp ((1 - p) * t) by
      dsimp only [D]
      rw [mul_add, mul_comm (Real.exp (-p * t)) (1 - p), ← mul_assoc,
        mul_comm (Real.exp (-p * t)) p, mul_assoc, ← Real.exp_add,
        show -p * t + t = (1 - p) * t by ring],
      ← Real.exp_add, show -p * t + (p * t + t ^ 2 / 8) = t ^ 2 / 8 by ring] at hmul
theorem exp_mul_le_ratio {u_prev c : ℝ} (hu : 0 < u_prev) (hc : 0 ≤ c) :
    Real.exp ((1 / (u_prev + c)) * c) ≤ (u_prev + c) / u_prev := by
  have huc : 0 < u_prev + c := by linarith
  set s : ℝ := (1 / (u_prev + c)) * c
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((Real.add_one_le_exp (-s)).trans_eq (Real.exp_neg s)) (div_nonneg huc.le hu.le))
    (Real.exp_pos s).le
  rwa [show (u_prev + c) / u_prev * (-s + 1) * Real.exp s = Real.exp s by
      dsimp only [s]; field_simp [hu.ne', huc.ne']; ring,
    show (u_prev + c) / u_prev * (Real.exp s)⁻¹ * Real.exp s = (u_prev + c) / u_prev by
      field_simp [(Real.exp_pos s).ne']] at hmul


def mgfPot (M : ℕ) (u : ℝ) (E D : Fin M → Matrix (Fin 2) (Fin 2) ℂ) (γ : ℝ) : ℝ :=
    ∑ j : Fin M, Real.exp ((1 / u) * chordalY ((Complex.exp (((γ : ℝ) : ℂ) * Complex.I) • D j) *
    (E j)ᴴ))
abbrev idE : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    AlgHom.id ℂ (Matrix (Fin 2) (Fin 2) ℂ)
def scalarWalk (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Complex.exp ((θ : ℂ) * Complex.I) • 1
theorem scalarWalk_mem_unitary (θ : ℝ) : scalarWalk θ ∈ _root_.unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
    exp_smul_mem_unitaryGroup θ (one_mem _)
theorem scalarWalk_mem_commutant (θ : ℝ) : scalarWalk θ ∈ qubitCommutant idE := by
  rw [Subalgebra.mem_centralizer_iff]; rintro _ ⟨M, rfl⟩; simp [scalarWalk, idE]
theorem scalarWalk_conj_mem_commutant (θ : ℝ) : (scalarWalk θ)ᴴ ∈ qubitCommutant idE :=
  conjTranspose_mem_qubitCommutant idE (fun _ ↦ rfl) (scalarWalk_mem_commutant θ)


theorem sigOp_scalarWalk_true_eq (θ : ℝ) :
    sigOp idE (scalarWalk θ) true =
      !![1, 0; 0, Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)] := by
  have hconj : (scalarWalk θ)ᴴ = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) • 1 := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [scalarWalk, ← Complex.exp_conj]
  ext i j : 1; fin_cases i <;> fin_cases j <;>
    simp [sigOp, blockOp, mixedSignal, idE, hconj, Fin.sum_univ_two]

theorem sigOp_scalarWalk_step_eq (θ : ℝ) : sigOp idE (scalarWalk θ) false *
    sigOp idE (scalarWalk θ) true = su2Diag (-θ) := by
  have hfalse : sigOp idE (scalarWalk θ) false = !![Complex.exp ((θ : ℂ) * Complex.I), 0; 0, 1]
      := by
    ext i j : 1; fin_cases i <;> fin_cases j <;>
      simp [sigOp, blockOp, mixedSignal, idE, scalarWalk, Fin.sum_univ_two]
  rw [hfalse, sigOp_scalarWalk_true_eq, su2Diag_neg]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
def cayleyNum (k : ℕ) : ℂ := 1 + Complex.I * ((k + 1 : ℕ) : ℂ)
def cayleyDen (k : ℕ) : ℂ := 1 - Complex.I * ((k + 1 : ℕ) : ℂ)
theorem cayleyNum_ne_zero (k : ℕ) : cayleyNum k ≠ 0 := by
  intro h; have hre := congrArg Complex.re h; simp [cayleyNum] at hre
theorem cayleyDen_ne_zero (k : ℕ) : cayleyDen k ≠ 0 := by
  intro h; have hre := congrArg Complex.re h; simp [cayleyDen] at hre
def cayleyPt (k : ℕ) : ℂ := cayleyNum k / cayleyDen k
theorem cayleyPt_injective : Function.Injective cayleyPt := by
  intro k₁ k₂ h; dsimp only [cayleyPt] at h;
  rw [div_eq_div_iff (cayleyDen_ne_zero k₁) (cayleyDen_ne_zero k₂)] at h;
  have him :=
      congrArg Complex.im h; simp only [cayleyNum, cayleyDen, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.natCast_im] at him; push_cast at him
  have heq : (k₁ : ℝ) = (k₂ : ℝ) := by linarith
  exact_mod_cast heq

theorem star_cayleyPt_mul_self (k : ℕ) : star (cayleyPt k) * cayleyPt k = 1 := by
  have hsn : star (cayleyNum k) = cayleyDen k := by
    apply Complex.ext <;> simp [cayleyNum, cayleyDen]
  have hsd : star (cayleyDen k) = cayleyNum k := by
    apply Complex.ext <;> simp [cayleyNum, cayleyDen]
  dsimp only [cayleyPt]; rw [div_eq_mul_inv, star_mul, star_inv₀, hsn, hsd, ← div_eq_mul_inv]
  field_simp [cayleyNum_ne_zero k, cayleyDen_ne_zero k]

theorem norm_cayleyPt (k : ℕ) : ‖cayleyPt k‖ = 1 := by
  have h :=
      congrArg norm (star_cayleyPt_mul_self k); rw [norm_mul, norm_star,
      norm_one] at h; nlinarith [norm_nonneg (cayleyPt k)]
theorem exists_cayley_regular {Env : Type*} [Fintype Env] [DecidableEq Env]
    (W₀ : Matrix Env Env ℂ) : ∃ w : ℂ, star w * w = 1 ∧ ‖w‖ = 1 ∧
    IsUnit ((w • (1 : Matrix Env Env ℂ) - W₀).det) := by
  let S : Finset ℂ := (Finset.range (Fintype.card Env + 1)).image cayleyPt
  have hcard_S : S.card = Fintype.card Env + 1 := by
    rw [Finset.card_image_of_injective _ cayleyPt_injective, Finset.card_range]
  let R : Finset ℂ := W₀.charpoly.roots.toFinset
  have hcard_R : R.card ≤ Fintype.card Env := (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans_eq (Matrix.charpoly_natDegree_eq_dim W₀))
  obtain ⟨w, hwS, hwR⟩ : ∃ w ∈ S, w ∉ R := by
    by_contra! hall; exact absurd (Finset.card_le_card fun w hw ↦ hall w hw) (by omega)
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hwS
  refine ⟨cayleyPt k, star_cayleyPt_mul_self k, norm_cayleyPt k, isUnit_iff_ne_zero.mpr fun h0 ↦
      hwR ?_⟩
  refine Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots (Matrix.charpoly_monic W₀).ne_zero).mpr ?_)
  change W₀.charpoly.eval (cayleyPt k) = 0
  rw [Matrix.eval_charpoly, show Matrix.scalar Env (cayleyPt k) = cayleyPt k • 1 from
    Matrix.ext fun i j ↦ by by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij], h0]
theorem smul_diagonal_eq {Env : Type*} [DecidableEq Env] (c : ℂ)
    (f : Env → ℂ) : c • Matrix.diagonal f = Matrix.diagonal (fun a ↦ c * f a) := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

/--
Every finite-dimensional unitary matrix over `ℂ` admits an orthonormal eigenbasis with
unit-modulus eigenvalues `exp(i θ_a)`.
-/
theorem unitary_spectral_decomp {Env : Type*} [Fintype Env] [DecidableEq Env]
    {W₀ : Matrix Env Env ℂ} (hW₀ : W₀ ∈ _root_.unitary (Matrix Env Env ℂ)) :
    ∃ (U_env : _root_.unitary (Matrix Env Env ℂ)) (θ_fn : Env → ℝ), W₀ = U_env.1 *
    Matrix.diagonal (fun a ↦ Complex.exp ((θ_fn a : ℂ) * Complex.I)) * (U_env.1)ᴴ := by
  obtain ⟨w, hw_star, hw_norm, hUnitDet⟩ := exists_cayley_regular W₀
  have hW₀_mul : W₀ᴴ * W₀ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hW₀
  let A : Matrix Env Env ℂ := w • 1 - W₀
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hUnitDet
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hUnitDet
  let Binv : Matrix Env Env ℂ := (A⁻¹)ᴴ
  have hAhB : Aᴴ * Binv = 1 := by
    dsimp only [Binv]; rw [← Matrix.conjTranspose_mul, hAinvA, Matrix.conjTranspose_one]
  have hBAh : Binv * Aᴴ = 1 := by
    dsimp only [Binv]; rw [← Matrix.conjTranspose_mul, hAAinv, Matrix.conjTranspose_one]
  let H : Matrix Env Env ℂ := Complex.I • ((w • 1 + W₀) * A⁻¹)
  have hHA : H * A = Complex.I • (w • 1 + W₀) := by
    dsimp only [H]; rw [smul_mul_assoc, Matrix.mul_assoc, hAinvA, Matrix.mul_one]
  have hH_herm : Matrix.IsHermitian H := by
    change Hᴴ = H
    have hHh_eq : Hᴴ = (-Complex.I) • (Binv * (star w • 1 + W₀ᴴ)) := by
      dsimp only [H, Binv];
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Complex.star_def]
    have hmid : Aᴴ * Hᴴ * A = Aᴴ * H * A := by
      have hlhs : Aᴴ * Hᴴ * A = (-Complex.I) • ((star w • 1 + W₀ᴴ) * (w • 1 - W₀)) := by
        rw [hHh_eq, mul_smul_comm, smul_mul_assoc, ← Matrix.mul_assoc Aᴴ Binv, hAhB,
          Matrix.one_mul]
      have hrhs : Aᴴ * H * A = Complex.I • ((star w • 1 - W₀ᴴ) * (w • 1 + W₀)) := by
        rw [Matrix.mul_assoc Aᴴ H A, hHA, mul_smul_comm]
        dsimp only [A]
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
      have hexp1 :
          (star w • (1 : Matrix Env Env ℂ) + W₀ᴴ) * (w • 1 - W₀) = w • W₀ᴴ - star w • W₀ := by
        rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, Matrix.one_mul, smul_smul, hw_star,
          one_smul, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, hW₀_mul]
        abel
      have hexp2 :
          (star w • (1 : Matrix Env Env ℂ) - W₀ᴴ) * (w • 1 + W₀) = star w • W₀ - w • W₀ᴴ := by
        rw [sub_mul, mul_add, mul_add, smul_mul_assoc, Matrix.one_mul, smul_smul, hw_star,
          one_smul, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, hW₀_mul]
        abel
      rw [hlhs, hrhs, hexp1, hexp2, neg_smul, ← smul_neg, neg_sub]
    have hL : ∀ X : Matrix Env Env ℂ, Binv * (Aᴴ * X * A) * A⁻¹ = X := fun X => by
      rw [← Matrix.mul_assoc Binv (Aᴴ * X) A, ← Matrix.mul_assoc Binv Aᴴ X,
        hBAh, Matrix.one_mul, Matrix.mul_assoc X A A⁻¹, hAAinv, Matrix.mul_one]
    rw [← hL Hᴴ, hmid, hL H]
  let U_env := hH_herm.eigenvectorUnitary
  let ev : Env → ℝ := hH_herm.eigenvalues
  have hU_mul_star : U_env.1 * (U_env.1)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact U_env.2.2
  have hU_star_mul : (U_env.1)ᴴ * U_env.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact U_env.2.1
  have hsc_diag : ∀ c : ℂ, c • (1 : Matrix Env Env ℂ) = U_env.1 * Matrix.diagonal (fun _ : Env ↦
      c) * (U_env.1)ᴴ := fun c ↦ by
    rw [show U_env.1 * Matrix.diagonal (fun _ : Env ↦ c) * (U_env.1)ᴴ = U_env.1 * (c • 1) *
      (U_env.1)ᴴ by
      rw [← Matrix.diagonal_one, smul_diagonal_eq]; simp only [mul_one],
      mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hU_mul_star]
  have hdiag : H = U_env.1 * Matrix.diagonal (fun a ↦ (ev a : ℂ)) * (U_env.1)ᴴ := by
    simpa [Matrix.star_eq_conjTranspose, Unitary.coe_star, Function.comp_def,
        Matrix.mul_assoc] using hH_herm.spectral_theorem
  have hev_ne : ∀ a : Env, (ev a : ℂ) + Complex.I ≠ 0 := fun a h ↦ by
    simpa using congrArg Complex.im h
  let R_inv : Matrix Env Env ℂ :=
      U_env.1 * Matrix.diagonal (fun a ↦ ((ev a : ℂ) + Complex.I)⁻¹) * (U_env.1)ᴴ
  have hHi_eq : H + Complex.I • 1 = U_env.1 * Matrix.diagonal (fun a ↦ (ev a : ℂ) + Complex.I) *
      (U_env.1)ᴴ := by
    rw [hdiag, hsc_diag Complex.I, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  have hR_left : R_inv * (H + Complex.I • 1) = 1 := by
    dsimp only [R_inv]; rw [hHi_eq]
    calc U_env.1 * Matrix.diagonal (fun a ↦ ((ev a : ℂ) + Complex.I)⁻¹) * (U_env.1)ᴴ *
        (U_env.1 * Matrix.diagonal (fun a ↦ (ev a : ℂ) + Complex.I) * (U_env.1)ᴴ)
        = U_env.1 * (Matrix.diagonal (fun a ↦ ((ev a : ℂ) + Complex.I)⁻¹) *
            (((U_env.1)ᴴ * U_env.1) * Matrix.diagonal (fun a ↦ (ev a : ℂ) + Complex.I))) *
            (U_env.1)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hU_star_mul, Matrix.one_mul, Matrix.diagonal_mul_diagonal, show (fun a : Env ↦
            ((ev a : ℂ) + Complex.I)⁻¹ * ((ev a : ℂ) + Complex.I)) = (fun _ ↦ 1) from funext fun a ↦
            inv_mul_cancel₀ (hev_ne a),
          Matrix.diagonal_one, Matrix.mul_one, hU_mul_star]
  have hHi_A : (H + Complex.I • 1) * A = (2 * Complex.I * w) • 1 := by
    rw [add_mul, hHA, smul_mul_assoc, Matrix.one_mul]; ext i j; dsimp only [A];
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hA_diag : A = U_env.1 * Matrix.diagonal (fun a ↦ (2 * Complex.I * w) *
      ((ev a : ℂ) + Complex.I)⁻¹) * (U_env.1)ᴴ := by
    rw [← Matrix.one_mul A, ← hR_left, Matrix.mul_assoc, hHi_A, mul_smul_comm, Matrix.mul_one]
    dsimp only [R_inv]
    rw [← smul_mul_assoc, ← mul_smul_comm, smul_diagonal_eq]
  let d : Env → ℂ := fun a ↦ w * (((ev a : ℂ) - Complex.I) / ((ev a : ℂ) + Complex.I))
  have hd_norm : ∀ a : Env, ‖d a‖ = 1 := fun a ↦ by
    have hconj_ev : (ev a : ℂ) - Complex.I = star ((ev a : ℂ) + Complex.I) := by
      apply Complex.ext <;> simp
    dsimp only [d]
    rw [norm_mul, norm_div, hw_norm, one_mul, hconj_ev, norm_star,
        div_self (norm_pos_iff.mpr (hev_ne a)).ne']
  let θ_fn : Env → ℝ := fun a ↦ Complex.arg (d a)
  refine ⟨U_env, θ_fn, ?_⟩
  rw [show W₀ = w • 1 - A by dsimp only [A]; abel, hsc_diag w, hA_diag, ← Matrix.sub_mul,
    ← Matrix.mul_sub, Matrix.diagonal_sub]
  refine congrArg (fun f ↦ U_env.1 * Matrix.diagonal f * (U_env.1)ᴴ) (funext fun a ↦ ?_)
  rw [← (by simpa [hd_norm a] using (Complex.norm_mul_exp_arg_mul_I (d a)).symm : d a =
    Complex.exp ((θ_fn a : ℂ) * Complex.I))]
  dsimp only [d]
  field_simp [hev_ne a]
  ring
/-! ### 2B.2 Single-Qubit Split Kronecker Decomposition & Fiberwise Evaluation -/

abbrev WireEnv {N : ℕ} (q : Wire N) : Type := (QRegister.singleton q).Environment → ZMod 2
def wireSplitEquiv {N : ℕ} (q : Wire N) : Fin (2 ^ N) ≃ Fin 2 × WireEnv q :=
    (QRegister.singleton q).basisSplitEquiv
def splitKronecker {N : ℕ} (q : Wire N) (M : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (WireEnv q)
    (WireEnv q) ℂ) : Operator (2 ^ N) :=
  Matrix.of fun g₁ g₂ ↦
    let p₁ := wireSplitEquiv q g₁
    let p₂ := wireSplitEquiv q g₂
    M p₁.1 p₂.1 * B p₁.2 p₂.2

theorem splitKronecker_apply {N : ℕ} (q : Wire N)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (WireEnv q) (WireEnv q) ℂ)
    (g₁ g₂ : Fin (2 ^ N)) :
    splitKronecker q M B g₁ g₂ =
      M (wireSplitEquiv q g₁).1 (wireSplitEquiv q g₂).1 *
      B (wireSplitEquiv q g₁).2 (wireSplitEquiv q g₂).2 := rfl

theorem splitKronecker_one {N : ℕ} (q : Wire N) : splitKronecker q 1 1 = 1 := by
  ext g₁ g₂
  rw [splitKronecker_apply]
  rcases eq_or_ne g₁ g₂ with rfl | h
  · simp
  · by_cases h1 : (wireSplitEquiv q g₁).1 = (wireSplitEquiv q g₂).1
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne fun h2 ↦
          h ((wireSplitEquiv q).injective (Prod.ext h1 h2))]
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne h1]

theorem splitKronecker_conjTranspose {N : ℕ} (q : Wire N) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (WireEnv q) (WireEnv q) ℂ) : (splitKronecker q M B)ᴴ = splitKronecker q Mᴴ Bᴴ := by
  ext g₁ g₂; simp [splitKronecker_apply, Matrix.conjTranspose_apply]
theorem splitKronecker_mul {N : ℕ} (q : Wire N) (M₁ M₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (B₁ B₂ : Matrix (WireEnv q) (WireEnv q) ℂ) : splitKronecker q M₁ B₁ * splitKronecker q M₂ B₂ =
    splitKronecker q (M₁ * M₂) (B₁ * B₂) := by
  ext g₁ g₂;
  rw [Matrix.mul_apply, splitKronecker_apply, ← (wireSplitEquiv q).symm.sum_comp,
      Fintype.sum_prod_type]; simp only [splitKronecker_apply, Equiv.apply_symm_apply,
      Matrix.mul_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  ring

theorem eQWire_eq_splitKronecker {N : ℕ} (q : Wire N) (M : Matrix (Fin 2) (Fin 2) ℂ) : eQWire q M =
    splitKronecker q M 1 := by
  ext g₁ g₂; change (QRegister.singleton q).embedMatrix M g₁ g₂ = _;
  rw [QRegister.embedMatrix_apply, splitKronecker_apply, Matrix.one_apply]; rfl
def envBlock {N : ℕ} (q : Wire N) (W : Operator (2 ^ N)) : Matrix (WireEnv q) (WireEnv q) ℂ :=
    Matrix.of fun e₁ e₂ ↦ W ((wireSplitEquiv q).symm (0, e₁)) ((wireSplitEquiv q).symm (0, e₂))
theorem commutant_eq_splitKronecker {N : ℕ} (q : Wire N) {W : Operator (2 ^ N)}
    (hWc : W ∈ qubitCommutant (eQWire q)) : W = splitKronecker q 1 (envBlock q W) := by
  have hcomm : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, splitKronecker q M 1 * W = W *
      splitKronecker q M 1 := by
    intro M; rw [← eQWire_eq_splitKronecker]; exact comm_of_mem_qubitCommutant (eQWire q) hWc M
  have hleft : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (e₁ e₂ : WireEnv q),
      (splitKronecker q M 1 * W) ((wireSplitEquiv q).symm (i, e₁))
      ((wireSplitEquiv q).symm (j, e₂)) = ∑ k : Fin 2, M i k * W ((wireSplitEquiv q).symm (k, e₁))
      ((wireSplitEquiv q).symm (j, e₂)) := by
    intro M i j e₁ e₂
    rw [Matrix.mul_apply, ← (wireSplitEquiv q).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm, Finset.sum_eq_single e₁]
    · refine Finset.sum_congr rfl fun _ _ ↦ ?_
      rw [splitKronecker_apply, (wireSplitEquiv q).apply_symm_apply,
        (wireSplitEquiv q).apply_symm_apply, Matrix.one_apply_eq, mul_one]
    · exact fun _ _ hne ↦ Finset.sum_eq_zero fun _ _ ↦ by simp [splitKronecker_apply, Ne.symm hne]
    · exact fun h ↦ absurd (Finset.mem_univ e₁) h
  have hright : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (e₁ e₂ : WireEnv q),
      (W * splitKronecker q M 1) ((wireSplitEquiv q).symm (i, e₁))
      ((wireSplitEquiv q).symm (j, e₂)) = ∑ k : Fin 2, W ((wireSplitEquiv q).symm (i, e₁))
      ((wireSplitEquiv q).symm (k, e₂)) * M k j := by
    intro M i j e₁ e₂
    rw [Matrix.mul_apply, ← (wireSplitEquiv q).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm, Finset.sum_eq_single e₂]
    · refine Finset.sum_congr rfl fun _ _ ↦ ?_
      rw [splitKronecker_apply, (wireSplitEquiv q).apply_symm_apply,
        (wireSplitEquiv q).apply_symm_apply, Matrix.one_apply_eq, mul_one]
    · exact fun _ _ hne ↦ Finset.sum_eq_zero fun _ _ ↦ by simp [splitKronecker_apply, hne]
    · exact fun h ↦ absurd (Finset.mem_univ e₂) h
  have h01 : ∀ e₁ e₂ : WireEnv q, W ((wireSplitEquiv q).symm (0, e₁))
      ((wireSplitEquiv q).symm (1, e₂)) = 0 := by
    intro e₁ e₂;
    have hc := congrFun (congrFun (hcomm (Matrix.single 0 0 1)) ((wireSplitEquiv q).symm (0, e₁)))
        ((wireSplitEquiv q).symm (1, e₂)); rw [hleft, hright, Fin.sum_univ_two,
        Fin.sum_univ_two] at hc; simpa [Matrix.single] using hc
  have h10 : ∀ e₁ e₂ : WireEnv q, W ((wireSplitEquiv q).symm (1, e₁))
      ((wireSplitEquiv q).symm (0, e₂)) = 0 := by
    intro e₁ e₂;
    have hc := congrFun (congrFun (hcomm (Matrix.single 0 0 1)) ((wireSplitEquiv q).symm (1, e₁)))
        ((wireSplitEquiv q).symm (0, e₂)); rw [hleft, hright, Fin.sum_univ_two,
        Fin.sum_univ_two] at hc; simpa [Matrix.single] using hc.symm
  have h11 : ∀ e₁ e₂ : WireEnv q, W ((wireSplitEquiv q).symm (1, e₁))
      ((wireSplitEquiv q).symm (1, e₂)) = W ((wireSplitEquiv q).symm (0, e₁))
      ((wireSplitEquiv q).symm (0, e₂)) := by
    intro e₁ e₂;
    have hc := congrFun (congrFun (hcomm (Matrix.single 0 1 1)) ((wireSplitEquiv q).symm (0, e₁)))
        ((wireSplitEquiv q).symm (1, e₂)); rw [hleft, hright, Fin.sum_univ_two,
        Fin.sum_univ_two] at hc; simpa [Matrix.single] using hc
  ext g₁ g₂;
  obtain ⟨⟨i, e₁⟩, rfl⟩ := (wireSplitEquiv q).symm.surjective g₁; obtain ⟨⟨j, e₂⟩, rfl⟩ :=
      (wireSplitEquiv q).symm.surjective g₂; rw [splitKronecker_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  fin_cases i <;> fin_cases j <;> simp [envBlock, h01, h10, h11]

theorem envBlock_mem_unitary {N : ℕ} (q : Wire N) {W : Operator (2 ^ N)}
    (hW : W ∈ _root_.unitary (Operator (2 ^ N))) (hWc : W ∈ qubitCommutant (eQWire q)) :
    envBlock q W ∈ _root_.unitary (Matrix (WireEnv q) (WireEnv q) ℂ) := by
  have hW_eq := commutant_eq_splitKronecker q hWc
  have h1 : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hW
  have h2 : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hW
  rw [hW_eq, splitKronecker_conjTranspose, Matrix.conjTranspose_one, splitKronecker_mul,
      Matrix.one_mul] at h1 h2; rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]; constructor
  · ext e₁ e₂;
    have h :=
        congrFun (congrFun h1 ((wireSplitEquiv q).symm (0, e₁)))
        ((wireSplitEquiv q).symm (0, e₂)); rw [splitKronecker_apply, ← splitKronecker_one q,
        splitKronecker_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h; simpa using h
  · ext e₁ e₂;
    have h :=
        congrFun (congrFun h2 ((wireSplitEquiv q).symm (0, e₁)))
        ((wireSplitEquiv q).symm (0, e₂)); rw [splitKronecker_apply, ← splitKronecker_one q,
        splitKronecker_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h; simpa using h
/--
Fiberwise `2 × 2` operator on wire `q` indexed by environment basis assignments `a : WireEnv q` .
-/
def envFiberOp {N : ℕ} (q : Wire N) (F : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) : Operator (2 ^ N) :=
  Matrix.of fun g₁ g₂ ↦
    let p₁ := wireSplitEquiv q g₁
    let p₂ := wireSplitEquiv q g₂
    if p₁.2 = p₂.2 then F p₁.2 p₁.1 p₂.1 else 0

theorem envFiberOp_apply {N : ℕ} (q : Wire N) (F : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ)
    (g₁ g₂ : Fin (2 ^ N)) :
    envFiberOp q F g₁ g₂ =
      if (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2 then
        F (wireSplitEquiv q g₁).2 (wireSplitEquiv q g₁).1 (wireSplitEquiv q g₂).1
      else 0 := rfl

theorem envFiberOp_const {N : ℕ} (q : Wire N) (M : Matrix (Fin 2) (Fin 2) ℂ) : envFiberOp q (fun _ ↦
    M) = eQWire q M := by
  ext g₁ g₂; rw [eQWire_eq_splitKronecker, splitKronecker_apply, envFiberOp_apply, Matrix.one_apply]
  by_cases he : (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2 <;> simp [he]
theorem envFiberOp_one {N : ℕ} (q : Wire N) : envFiberOp q (fun _ ↦ 1) = 1 := by
  rw [envFiberOp_const, map_one]
theorem envFiberOp_add {N : ℕ} (q : Wire N) (F₁ F₂ : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) :
    envFiberOp q F₁ + envFiberOp q F₂ = envFiberOp q (fun a ↦ F₁ a + F₂ a) := by
  ext g₁ g₂
  by_cases he : (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2 <;> simp [envFiberOp_apply, he]
theorem envFiberOp_sub {N : ℕ} (q : Wire N) (F₁ F₂ : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) :
    envFiberOp q F₁ - envFiberOp q F₂ = envFiberOp q (fun a ↦ F₁ a - F₂ a) := by
  ext g₁ g₂
  by_cases he : (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2 <;> simp [envFiberOp_apply, he]
theorem envFiberOp_smul {N : ℕ} (q : Wire N) (c : ℂ) (F : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) :
    c • envFiberOp q F = envFiberOp q (fun a ↦ c • F a) := by
  ext g₁ g₂
  by_cases he : (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2 <;> simp [envFiberOp_apply, he]
theorem envFiberOp_conjTranspose {N : ℕ} (q : Wire N) (F : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) :
    (envFiberOp q F)ᴴ = envFiberOp q (fun a ↦ (F a)ᴴ) := by
  ext g₁ g₂
  by_cases h : (wireSplitEquiv q g₂).2 = (wireSplitEquiv q g₁).2
  · simp [envFiberOp_apply, h]
  · simp [envFiberOp_apply, h, Ne.symm h]
theorem envFiberOp_mul {N : ℕ} (q : Wire N) (F₁ F₂ : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) :
    envFiberOp q F₁ * envFiberOp q F₂ = envFiberOp q (fun a ↦ F₁ a * F₂ a) := by
  ext g₁ g₂;
  rw [Matrix.mul_apply, envFiberOp_apply, ← (wireSplitEquiv q).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
  by_cases he : (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2
  · simp only [he, ↓reduceIte]
    rw [Finset.sum_eq_single (wireSplitEquiv q g₂).2]
    · simp only [envFiberOp_apply, Equiv.apply_symm_apply, he, ↓reduceIte, Matrix.mul_apply]
    · exact fun _ _ hne ↦ Finset.sum_eq_zero fun _ _ ↦ by simp [envFiberOp_apply, hne]
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  · simp only [he, ↓reduceIte]
    refine Finset.sum_eq_zero fun e _ ↦ Finset.sum_eq_zero fun _ _ ↦ ?_
    rcases eq_or_ne (wireSplitEquiv q g₁).2 e with rfl | h1
    · simp [envFiberOp_apply, he]
    · simp [envFiberOp_apply, h1]

theorem splitKronecker_diagonal_eq_envFiberOp {N : ℕ} (q : Wire N) (θ_fn : WireEnv q → ℝ) :
    splitKronecker q 1 (Matrix.diagonal (fun a ↦ Complex.exp ((θ_fn a : ℂ) * Complex.I))) =
    envFiberOp q (fun a ↦ scalarWalk (θ_fn a)) := by
  ext g₁ g₂
  by_cases he : (wireSplitEquiv q g₁).2 = (wireSplitEquiv q g₂).2 <;>
    simp [splitKronecker_apply, envFiberOp_apply, he, scalarWalk, mul_comm]

theorem sigOp_envFiberOp_scalarWalk {N : ℕ} (q : Wire N) (θ_fn : WireEnv q → ℝ)
    (s : Bool) : sigOp (eQWire q) (envFiberOp q (fun a ↦ scalarWalk (θ_fn a))) s =
    envFiberOp q (fun a ↦ sigOp idE (scalarWalk (θ_fn a)) s) := by
  cases s
  · simp only [sigOp, mixedSignal, Bool.false_eq_true, ↓reduceIte, blockOp_diag, idE, AlgHom.coe_id,
        id_eq]; rw [← envFiberOp_const q (Matrix.single 0 0 1),
        ← envFiberOp_const q (Matrix.single 1 1 1), ← envFiberOp_one q, envFiberOp_mul,
        envFiberOp_mul, envFiberOp_add]
  · simp only [sigOp, mixedSignal, ↓reduceIte, blockOp_diag, idE, AlgHom.coe_id, id_eq];
    rw [← envFiberOp_const q (Matrix.single 0 0 1), ← envFiberOp_const q (Matrix.single 1 1 1),
        ← envFiberOp_one q, envFiberOp_conjTranspose, envFiberOp_mul, envFiberOp_mul,
        envFiberOp_add]
theorem gqspOp_envFiberOp_scalarWalk {N : ℕ} (q : Wire N) (θ_fn : WireEnv q → ℝ) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ × Bool),
      gqspOp (eQWire q) (envFiberOp q (fun a ↦ scalarWalk (θ_fn a))) Rs =
        envFiberOp q (fun a ↦ gqspOp idE (scalarWalk (θ_fn a)) Rs)
  | [] => by simp only [gqspOp, envFiberOp_one]
  | (R, s) :: Rs => by
      simp only [gqspOp, idE, AlgHom.coe_id, id_eq];
      rw [gqspOp_envFiberOp_scalarWalk q θ_fn Rs, sigOp_envFiberOp_scalarWalk,
          ← envFiberOp_const q R, envFiberOp_mul, envFiberOp_mul]
theorem opNorm_envFiberOp_le {N : ℕ} (q : Wire N) (F : WireEnv q → Matrix (Fin 2) (Fin 2) ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hF : ∀ a : WireEnv q, ‖F a‖ ≤ c) : ‖envFiberOp q F‖ ≤ c := by
  refine qubTop_opNorm_le_of_mulVec_pgL2Norm_top hc fun ψ ↦ ?_
  have hsum (f : Fin (2 ^ N) → ℂ) :
      ∑ j : Fin (2 ^ N), f j = ∑ e : WireEnv q, ∑ y : Fin 2, f ((wireSplitEquiv q).symm (y, e))
          := by
    rw [← Equiv.sum_comp (wireSplitEquiv q).symm, Fintype.sum_prod_type, Finset.sum_comm]
  have hsumR (f : Fin (2 ^ N) → ℝ) :
      ∑ j : Fin (2 ^ N), f j = ∑ e : WireEnv q, ∑ y : Fin 2, f ((wireSplitEquiv q).symm (y, e))
          := by
    rw [← Equiv.sum_comp (wireSplitEquiv q).symm, Fintype.sum_prod_type, Finset.sum_comm]
  have hpoint (x : Fin 2) (env : WireEnv q) :
      (envFiberOp q F *ᵥ ψ) ((wireSplitEquiv q).symm (x, env)) =
        (F env *ᵥ fun y ↦ ψ ((wireSplitEquiv q).symm (y, env))) x := by
    rw [Matrix.mulVec, dotProduct, hsum, Finset.sum_eq_single env]
    · simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun y _ ↦ by simp [envFiberOp_apply]
    · exact fun env' _ hne ↦ Finset.sum_eq_zero fun y _ ↦ by simp [envFiberOp_apply, Ne.symm hne]
    · exact fun hmem ↦ absurd (Finset.mem_univ env) hmem
  refine (sq_le_sq₀ (pgL2Norm_nonneg _) (mul_nonneg hc (pgL2Norm_nonneg ψ))).mp ?_
  rw [pgL2Norm_sq, hsumR, mul_pow, pgL2Norm_sq, hsumR, Finset.mul_sum]
  simp_rw [hpoint]
  refine Finset.sum_le_sum fun env _ ↦ ?_
  rw [← pgL2Norm_sq, show (∑ y : Fin 2, ‖ψ ((wireSplitEquiv q).symm (y, env))‖ ^ 2) =
    pgL2Norm (fun y ↦ ψ ((wireSplitEquiv q).symm (y, env))) ^ 2 from (pgL2Norm_sq _).symm,
        ← mul_pow]
  exact (sq_le_sq₀ (pgL2Norm_nonneg _) (mul_nonneg hc (pgL2Norm_nonneg _))).mpr
    ((qubTop_pgL2Norm_mulVec_le_opNorm (F env) _).trans
      (mul_le_mul_of_nonneg_right (hF env) (pgL2Norm_nonneg _)))
/-! ### 2B.3 Unitary Environment Basis Conjugation & Main `2 ^ N`-Qubit Sub-Gaussian QSP Theorem -/

theorem conj_unitary_mul {N : ℕ} {U : Operator (2 ^ N)} (hUU : Uᴴ * U = 1)
    (A B : Operator (2 ^ N)) : (U * A * Uᴴ) * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc (U * A * Uᴴ) * (U * B * Uᴴ)
      = U * (A * ((Uᴴ * U) * B)) * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uᴴ := by rw [hUU, Matrix.one_mul]

theorem splitKronecker_one_unitary_mul {N : ℕ} (q : Wire N)
    (U_env : _root_.unitary (Matrix (WireEnv q) (WireEnv q) ℂ)) :
    (splitKronecker q 1 U_env.1)ᴴ * splitKronecker q 1 U_env.1 = 1 ∧
    splitKronecker q 1 U_env.1 * (splitKronecker q 1 U_env.1)ᴴ = 1 := by
  have h2 : (U_env.1)ᴴ * U_env.1 = 1 := by
    simpa only [← Matrix.star_eq_conjTranspose] using U_env.2.1
  have h1 : U_env.1 * (U_env.1)ᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U_env.2.2
  exact
      ⟨by rw [splitKronecker_conjTranspose, Matrix.conjTranspose_one, splitKronecker_mul,
            Matrix.one_mul, h2, splitKronecker_one],
         by rw [splitKronecker_conjTranspose, Matrix.conjTranspose_one, splitKronecker_mul,
              Matrix.one_mul, h1, splitKronecker_one]⟩
theorem conj_eQWire_splitKronecker {N : ℕ} (q : Wire N)
    {U_env : _root_.unitary (Matrix (WireEnv q) (WireEnv q) ℂ)} (M : Matrix (Fin 2) (Fin 2) ℂ) :
    let U_tot : Operator (2 ^ N) := splitKronecker q 1 U_env.1
    U_tot * eQWire q M * U_totᴴ = eQWire q M := by
  intro U_tot
  have h1 : U_env.1 * (U_env.1)ᴴ = 1 := by
    simpa only [← Matrix.star_eq_conjTranspose] using U_env.2.2
  rw [eQWire_eq_splitKronecker, splitKronecker_conjTranspose, Matrix.conjTranspose_one,
      splitKronecker_mul, splitKronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
      h1]
theorem conj_sigOp_splitKronecker {N : ℕ} (q : Wire N)
    {U_env : _root_.unitary (Matrix (WireEnv q) (WireEnv q) ℂ)} (W_d : Operator (2 ^ N))
        (s : Bool) :
    let U_tot : Operator (2 ^ N) := splitKronecker q 1 U_env.1
    U_tot * sigOp (eQWire q) W_d s * U_totᴴ = sigOp (eQWire q) (U_tot * W_d * U_totᴴ) s := by
  intro U_tot
  have hU_star := (splitKronecker_one_unitary_mul q U_env).1
  cases s
  · simp only [sigOp, mixedSignal, Bool.false_eq_true, ↓reduceIte, blockOp_diag, Matrix.mul_one];
    rw [Matrix.mul_add, Matrix.add_mul, ← conj_eQWire_splitKronecker q (U_env := U_env)
        (Matrix.single 0 0 1), conj_unitary_mul hU_star (eQWire q (Matrix.single 0 0 1)) W_d,
        conj_eQWire_splitKronecker q (U_env := U_env) (Matrix.single 0 0 1),
        conj_eQWire_splitKronecker q (U_env := U_env) (Matrix.single 1 1 1)]
  · simp only [sigOp, mixedSignal, ↓reduceIte, blockOp_diag, Matrix.mul_one]
    have hconj : (U_tot * W_d * U_totᴴ)ᴴ = U_tot * W_dᴴ * U_totᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hconj, Matrix.mul_add, Matrix.add_mul, conj_eQWire_splitKronecker q (U_env := U_env)
        (Matrix.single 0 0 1), ← conj_eQWire_splitKronecker q (U_env := U_env)
        (Matrix.single 1 1 1), conj_unitary_mul hU_star (eQWire q (Matrix.single 1 1 1)) W_dᴴ,
        conj_eQWire_splitKronecker q (U_env := U_env) (Matrix.single 1 1 1)]
theorem conj_gqspOp_splitKronecker {N : ℕ} (q : Wire N)
    {U_env : _root_.unitary (Matrix (WireEnv q) (WireEnv q) ℂ)} (W_d : Operator (2 ^ N)) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ × Bool),
      let U_tot : Operator (2 ^ N) := splitKronecker q 1 U_env.1
      U_tot * gqspOp (eQWire q) W_d Rs * U_totᴴ = gqspOp (eQWire q) (U_tot * W_d * U_totᴴ) Rs
  | [] => by
        intro U_tot
        simpa only [gqspOp, Matrix.mul_one] using (splitKronecker_one_unitary_mul q U_env).2
  | (R, s) :: Rs => by
      intro U_tot
      have hU_star := (splitKronecker_one_unitary_mul q U_env).1
      simp only [gqspOp];
      rw [← conj_gqspOp_splitKronecker q W_d Rs, ← conj_sigOp_splitKronecker q W_d s]
      conv_rhs => rw [← conj_eQWire_splitKronecker q (U_env := U_env) R]
      rw [conj_unitary_mul hU_star, conj_unitary_mul hU_star]
/-- Simplicial `SU(2)` step specification parameterized by `(cap, ep_nm, mean_num)`. -/
structure SimpStepSpecCapEp (cap ep_nm mean_num : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) where
  p : Fin 3 → ℝ
  circ : Fin 3 → Circuit 1
  γ : Fin 3 → ℝ
  g : Fin 3 → ℝ
  hp_nn : ∀ i, 0 ≤ p i
  hp_sum : ∑ i : Fin 3, p i = 1
  hcirc_1q : ∀ i, (CircExt.isOneQubitCircuit (circ i)) = true
  hcirc_T : ∀ i, (circ i).count PrimitiveGate.T ≤ cap
  hcirc_toff : ∀ i, (circ i).count PrimitiveGate.TOFF = 0
  hE_su2 : ∀ i,
    IsSu2 (U * (((Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1))ᴴ)
  hV_err : ∀ i,
    ‖U - (Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1‖ ≤
      ((ep_nm + 1 : ℕ) : ℝ) / 10 ^ 9
  hV_pair : ∀ i j,
    ‖(Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1 -
      (Complex.exp ((γ j : ℂ) * Complex.I) • phaseTurn (g j)) * (circ j).eval.1‖ ≤
      (ep_nm : ℝ) / 10 ^ 9
  hV_mean :
    ‖U - ∑ i : Fin 3, (p i : ℂ) •
      ((Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1)‖ ≤
      (mean_num : ℝ) / 10 ^ 18

/-- Simplicial `SU(2)` step specification at `(540 nm, 470 nm, 36868e-18)`. -/
structure SimpStepSpecCap (cap : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) where
  p : Fin 3 → ℝ
  circ : Fin 3 → Circuit 1
  γ : Fin 3 → ℝ
  g : Fin 3 → ℝ
  hp_nn : ∀ i, 0 ≤ p i
  hp_sum : ∑ i : Fin 3, p i = 1
  hcirc_1q : ∀ i, (CircExt.isOneQubitCircuit (circ i)) = true
  hcirc_T : ∀ i, (circ i).count PrimitiveGate.T ≤ cap
  hcirc_toff : ∀ i, (circ i).count PrimitiveGate.TOFF = 0
  hE_su2 : ∀ i,
    IsSu2 (U * (((Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1))ᴴ)
  hV_err : ∀ i,
    ‖U - (Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1‖ ≤ 540 / 10 ^ 9
  hV_pair : ∀ i j,
    ‖(Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1 -
      (Complex.exp ((γ j : ℂ) * Complex.I) • phaseTurn (g j)) * (circ j).eval.1‖ ≤ 470 / 10 ^ 9
  hV_mean :
    ‖U - ∑ i : Fin 3, (p i : ℂ) •
      ((Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1)‖ ≤ 36868 / 10 ^ 18
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge.Synth
set_option exponentiation.threshold 256
open scoped TopHad.Synth Matrix Matrix.Norms.L2Operator BigOperators Circuit.Notation
open TopHad.Synth Real Matrix ComplexConjugate Operator QProg DynamicCircuit Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.GQSP
/-! ### 1. `Nat` Boolean Helpers, `BTree` Lookup, and Grid Coverage Soundness -/

theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by simp [Nat.beq_eq]
theorem nat_ble_true_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b := by simp [Nat.ble_eq]
theorem nat_ble_false_iff (a b : Nat) : Nat.ble a b = false ↔ b < a := by
  rw [← Bool.not_eq_true, Nat.ble_eq]; omega
theorem _root_.QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth.BTree.all2_of_get?_right
    {α β : Type} {p : α → β → Bool} {t1 : BTree α} {t2 : BTree β} {idx : Nat} {b : β}
    (hall : BTree.all2 p t1 t2 = true) (hget : BTree.get? t2 idx = some b) : ∃ a : α,
    BTree.get? t1 idx = some a ∧ p a b = true := by
  induction t1 generalizing t2 idx with
  | empty => cases t2 <;> simp [BTree.all2, BTree.get?] at hall hget
  | node a la ra ihla ihra =>
    cases t2 with
    | empty => simp [BTree.all2] at hall
    | node b0 lb rb =>
      unfold BTree.all2 at hall
      cases hp : p a b0 <;> simp only [hp, Bool.false_eq_true] at hall
      cases hl : BTree.all2 p la lb <;> simp only [hl, Bool.false_eq_true] at hall
      cases idx with
      | zero =>
          simp only [BTree.get?, Option.some.injEq, exists_eq_left'] at hget ⊢
          exact hget ▸ hp
      | succ n =>
        unfold BTree.get? at hget ⊢
        cases hmod : Nat.beq (Nat.mod n 2) 0 <;> simp only [hmod] at hget ⊢
        · exact ihra hall hget
        · exact ihla hl hget

theorem forest256GetOpt_all2_right {α β : Type} {p : α → β → Bool} {f1 : BTree (BTree α)}
    {f2 : BTree (BTree β)} {idx : Nat} {b : β} (hall : BTree.all2 (BTree.all2 p) f1 f2 = true)
    (hget : forest256GetOpt f2 idx = some b) : ∃ a : α, forest256GetOpt f1 idx = some a ∧ p a b =
    true := by
  unfold forest256GetOpt at hget ⊢
  cases h2 : BTree.get? f2 (Nat.div idx 256) with
  | none => simp [h2] at hget
  | some sub2 =>
    simp only [h2] at hget
    obtain ⟨sub1, h1, hsub⟩ := BTree.all2_of_get?_right hall h2
    simp only [h1]
    exact BTree.all2_of_get?_right hsub hget
def _root_.QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth.SInt.toInt (x : SInt) : ℤ :=
    if x.isNeg then -(x.mag : ℤ) else (x.mag : ℤ)
@[local simp] theorem sNeg_toInt (x : SInt) : (sNeg x).toInt = -x.toInt := by
  rcases x with ⟨isNeg, mag⟩
  cases isNeg <;> simp [sNeg, SInt.toInt]
@[local simp] theorem sAdd_toInt (x y : SInt) : (sAdd x y).toInt = x.toInt + y.toInt := by
  rcases x with ⟨nx, mx⟩
  rcases y with ⟨ny, my⟩
  unfold sAdd
  cases nx <;> cases ny <;> dsimp
  · simp [SInt.toInt]
  · cases h : Nat.ble my mx <;> simp only [SInt.toInt, Bool.false_eq_true, ↓reduceIte] <;>
      simp only [Bool.eq_false_iff, Ne, nat_ble_true_iff] at h <;> omega
  · cases h : Nat.ble my mx <;> simp only [SInt.toInt, Bool.false_eq_true, ↓reduceIte] <;>
      simp only [Bool.eq_false_iff, Ne, nat_ble_true_iff] at h <;> omega
  · simp [SInt.toInt]; ring
@[local simp] theorem sSub_toInt (x y : SInt) : (sSub x y).toInt = x.toInt - y.toInt := by
  unfold sSub; rw [sAdd_toInt, sNeg_toInt]; ring
@[local simp] theorem sMul_toInt (x y : SInt) : (sMul x y).toInt = x.toInt * y.toInt := by
  rcases x with ⟨nx, mx⟩
  rcases y with ⟨ny, my⟩
  cases nx <;> cases ny <;> simp [sMul, SInt.toInt, Nat.mul_eq]
theorem sNonneg_iff (x : SInt) : sNonneg x = true ↔ 0 ≤ x.toInt := by
  rcases x with ⟨isNeg, m⟩
  cases isNeg <;>
    simp only [sNonneg, nat_beq_true_iff, SInt.toInt, Bool.false_eq_true, ↓reduceIte, true_iff] <;>
    omega
theorem sNonneg_false_iff (x : SInt) : sNonneg x = false ↔ x.toInt < 0 := by
  rw [← Bool.not_eq_true, sNonneg_iff]; omega
theorem sLe_iff (x y : SInt) : sLe x y = true ↔ x.toInt ≤ y.toInt := by
  change sNonneg (sSub y x) = true ↔ _
  rw [sNonneg_iff, sSub_toInt]; omega
theorem sPos_iff (x : SInt) : sPos x = true ↔ 0 < x.toInt := by
  rcases x with ⟨isNeg, m⟩
  cases isNeg
  · cases hm : Nat.beq m 0 <;> simp only [sPos, SInt.toInt, hm, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, true_iff, false_iff]
    · have := mt (nat_beq_true_iff m 0).mpr (by simp [hm])
      omega
    · have := (nat_beq_true_iff m 0).mp hm
      omega
  · simp only [sPos, SInt.toInt, Bool.false_eq_true, ↓reduceIte, false_iff]
    omega
@[local simp] theorem sAbs_toInt (x : SInt) : (sAbs x).toInt = |x.toInt| := by
  rcases x with ⟨isNeg, m⟩
  cases isNeg <;> simp [sAbs, SInt.toInt, abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
@[local simp] theorem sintMax_toInt (x y : SInt) : (sintMax x y).toInt = max x.toInt y.toInt := by
  unfold sintMax
  cases h : sLe x y
  · have hn : ¬ x.toInt ≤ y.toInt := by simp [← sLe_iff, h]
    exact (max_eq_left (show y.toInt ≤ x.toInt by omega)).symm
  · exact (max_eq_right ((sLe_iff x y).mp h)).symm
@[local simp] theorem sMin_toInt (x y : SInt) : (sMin x y).toInt = min x.toInt y.toInt := by
  unfold sMin
  cases h : sLe x y
  · have hn : ¬ x.toInt ≤ y.toInt := by simp [← sLe_iff, h]
    exact (min_eq_right (show y.toInt ≤ x.toInt by omega)).symm
  · exact (min_eq_left ((sLe_iff x y).mp h)).symm
@[local simp] theorem unbiasS_toInt (x : Nat) : (unbiasS x).toInt = (x : ℤ) - (bias : ℤ) := by
  unfold unbiasS
  cases h : Nat.ble bias x <;> simp only [SInt.toInt, Bool.false_eq_true, ↓reduceIte,
      Nat.sub_eq] <;> simp only [Bool.eq_false_iff, Ne, nat_ble_true_iff] at h <;> omega
def _root_.QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth.FastZ8.toCyc (z : FastZ8) :
    CyclotomicEight := ⟨z.a.toInt, z.b.toInt, z.c.toInt, z.d.toInt⟩
@[local simp] theorem fzNeg_toCyc (x : FastZ8) : (fzNeg x).toCyc = -x.toCyc := by
  change FastZ8.toCyc (fzNeg x) = CyclotomicEight.neg x.toCyc;
  simp [fzNeg, FastZ8.toCyc, CyclotomicEight.neg]
@[local simp] theorem fzMul_toCyc (x y : FastZ8) : (fzMul x y).toCyc = x.toCyc * y.toCyc := by
  change FastZ8.toCyc (fzMul x y) = CyclotomicEight.mul x.toCyc y.toCyc;
  simp [fzMul, FastZ8.toCyc, CyclotomicEight.mul]
theorem fzConj_toComplex (x : FastZ8) : (fzConj x).toCyc.toComplex = conj x.toCyc.toComplex := by
  apply Complex.ext <;>
    simp only [fzConj, FastZ8.toCyc, CyclotomicEight.toComplex_re, CyclotomicEight.toComplex_im,
      Complex.conj_re, Complex.conj_im, sNeg_toInt] <;> push_cast <;> ring
theorem omegaComplex_pow_eight : CyclotomicEight.omegaComplex ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, CyclotomicEight.omegaComplex_pow_four]; norm_num
theorem omegaComplex_pow_mod_eight (m : Nat) : CyclotomicEight.omegaComplex ^ (m % 8) =
    CyclotomicEight.omegaComplex ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 8]
  rw [pow_add, pow_mul, omegaComplex_pow_eight, one_pow, mul_one]

def omBasis : Nat → CyclotomicEight
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | 3 => ⟨0, 0, 0, 1⟩
  | 4 => ⟨-1, 0, 0, 0⟩
  | 5 => ⟨0, -1, 0, 0⟩
  | 6 => ⟨0, 0, -1, 0⟩
  | _ => ⟨0, 0, 0, -1⟩

theorem omBasis_toComplex {m : Nat} (hm : m < 8) : (omBasis m).toComplex =
    CyclotomicEight.omegaComplex ^ m := by
  have h4 : CyclotomicEight.omegaComplex ^ 4 = -1 := CyclotomicEight.omegaComplex_pow_four
  interval_cases m <;>
      simp only [CyclotomicEight.toComplex, omBasis, Int.cast_one, Int.cast_zero, zero_mul,
        add_zero, pow_zero, one_mul, zero_add, pow_one, Int.reduceNeg, Int.cast_neg, neg_mul]
  · exact h4.symm
  · linear_combination -CyclotomicEight.omegaComplex * h4
  · linear_combination -(CyclotomicEight.omegaComplex ^ 2) * h4
  · linear_combination -(CyclotomicEight.omegaComplex ^ 3) * h4

theorem fzMulOmega_toCyc (m : Nat) (x : FastZ8) : (fzMulOmega m x).toCyc = omBasis (m % 8) *
    x.toCyc := by
  unfold fzMulOmega; have hmod : Nat.mod m 8 = m % 8 := rfl; rw [hmod]; dsimp only
  set m8 := m % 8
  have hm8 : m8 < 8 := Nat.mod_lt m (by omega)
  interval_cases m8 <;>
    (change _ = CyclotomicEight.mul _ x.toCyc;
     simp [omBasis, FastZ8.toCyc, CyclotomicEight.mul])

theorem fzMulOmega_toComplex (m : Nat) (x : FastZ8) : (fzMulOmega m x).toCyc.toComplex =
    (CyclotomicEight.omegaComplex ^ m) * x.toCyc.toComplex := by
  rw [fzMulOmega_toCyc, CyclotomicEight.toComplex_mul,
    omBasis_toComplex (Nat.mod_lt m (by omega)), omegaComplex_pow_mod_eight]

theorem abs_d18_sqrt_two_sub_le :
    |(10 ^ 18 : ℝ) * Real.sqrt 2 - 1414213562373095048| ≤ 1 := by
  have hpos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1414213562373095047 : ℝ) ^ 2 ≤ ((10 ^ 18 : ℝ) * Real.sqrt 2) ^ 2 := by nlinarith
  have h2 : ((10 ^ 18 : ℝ) * Real.sqrt 2) ^ 2 ≤ (1414213562373095049 : ℝ) ^ 2 := by nlinarith
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
theorem d18_sqrt2_bounds (a d : ℤ) :
    ((2000000000000000000 * a + d * 1414213562373095048 - |d| : ℤ) : ℝ) ≤ (2 * 10 ^ 18 : ℝ) *
        ((a : ℝ) + (d : ℝ) * (Real.sqrt 2 / 2)) ∧
    (2 * 10 ^ 18 : ℝ) * ((a : ℝ) + (d : ℝ) * (Real.sqrt 2 / 2)) ≤ ((2000000000000000000 * a + d *
        1414213562373095048 + |d| : ℤ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
      abs_le.mp (show |(d : ℝ) * ((10 ^ 18 : ℝ) * √2 - 1414213562373095048)| ≤ |(d : ℝ)| by
    rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left abs_d18_sqrt_two_sub_le (abs_nonneg
        (d : ℝ)))
  push_cast; exact ⟨by linarith, by linarith⟩
theorem fzReLo_le (z : FastZ8) : ((fzReLo z).toInt : ℝ) ≤ (2 * 10 ^ 18 : ℝ) *
    z.toCyc.toComplex.re := by
  simpa [fzReLo, FastZ8.toCyc, CyclotomicEight.toComplex_re, show twoD18S.toInt =
      2000000000000000000 from rfl,
    show s2MidS.toInt = 1414213562373095048 from rfl] using (d18_sqrt2_bounds z.a.toInt (z.b.toInt -
        z.d.toInt)).1
theorem le_fzReHi (z : FastZ8) : (2 * 10 ^ 18 : ℝ) * z.toCyc.toComplex.re ≤ ((fzReHi z).toInt : ℝ)
    := by
  simpa [fzReHi, FastZ8.toCyc, CyclotomicEight.toComplex_re, show twoD18S.toInt =
      2000000000000000000 from rfl,
    show s2MidS.toInt = 1414213562373095048 from rfl] using (d18_sqrt2_bounds z.a.toInt (z.b.toInt -
        z.d.toInt)).2
theorem fzImLo_le (z : FastZ8) : ((fzImLo z).toInt : ℝ) ≤ (2 * 10 ^ 18 : ℝ) *
    z.toCyc.toComplex.im := by
  simpa [fzImLo, FastZ8.toCyc, CyclotomicEight.toComplex_im, show twoD18S.toInt =
      2000000000000000000 from rfl,
    show s2MidS.toInt = 1414213562373095048 from rfl] using (d18_sqrt2_bounds z.c.toInt (z.b.toInt +
        z.d.toInt)).1
theorem le_fzImHi (z : FastZ8) : (2 * 10 ^ 18 : ℝ) * z.toCyc.toComplex.im ≤ ((fzImHi z).toInt : ℝ)
    := by
  simpa [fzImHi, FastZ8.toCyc, CyclotomicEight.toComplex_im, show twoD18S.toInt =
      2000000000000000000 from rfl,
    show s2MidS.toInt = 1414213562373095048 from rfl] using (d18_sqrt2_bounds z.c.toInt (z.b.toInt +
        z.d.toInt)).2
/-! ### 3. 1-Qubit Gate Primitives, Syllable Limb Decoder, and `FastCol` Soundness -/

def _root_.QuantumComputation.Specs.PhotochemistrySolution.TopHad.Synth.Box2DS.Mem (bx : Box2DS)
    (z : ℂ) : Prop :=
    (bx.x0.toInt : ℝ) / (2 ^ 52 : ℝ) ≤ z.re ∧ z.re ≤ (bx.x1.toInt : ℝ) / (2 ^ 52 : ℝ) ∧
    (bx.y0.toInt : ℝ) / (2 ^ 52 : ℝ) ≤ z.im ∧ z.im ≤ (bx.y1.toInt : ℝ) / (2 ^ 52 : ℝ)
def matEta (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := -conj (M 1 0 / M 0 0)
def gate1 (g : PrimitiveGate 1) : Circuit 1 := Circuit.gate g (QRegister.whole 1)
@[local simp] theorem gate1_isOneQubit (g : PrimitiveGate 1) :
    (CircExt.isOneQubitCircuit (gate1 g)) = true := rfl

theorem gate1_eval (g : PrimitiveGate 1) : (gate1 g).eval.1 = g.eval.1 := by
  simp [gate1, Circuit.eval_gate, QRegister.whole_embedUnitary]
theorem gate1_x_eval : (gate1 .x).eval.1 = !![(0 : ℂ), 1; 1, 0] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [gate1_eval, PrimitiveGate.eval, Qubit.X]
theorem gate1_y_eval : (gate1 .y).eval.1 = !![(0 : ℂ), -Complex.I; Complex.I, 0] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [gate1_eval, PrimitiveGate.eval, Qubit.Y]
theorem gate1_z_eval : (gate1 .z).eval.1 = !![(1 : ℂ), 0; 0, -1] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [gate1_eval, PrimitiveGate.eval, Qubit.Z]
theorem gate1_s_eval : (gate1 .s).eval.1 = !![(1 : ℂ), 0; 0, Complex.I] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [gate1_eval, PrimitiveGate.eval, Qubit.S]
theorem gate1_t_eval :
    (gate1 .t).eval.1 = !![(1 : ℂ), 0; 0, CyclotomicEight.omegaComplex] := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [gate1_eval, PrimitiveGate.eval, Qubit.T, CyclotomicEight.omegaComplex]

theorem gate1_h_eval :
    (gate1 .h).eval.1 =
      !![(1 / Real.sqrt 2 : ℂ), (1 / Real.sqrt 2 : ℂ);
         (1 / Real.sqrt 2 : ℂ), -(1 / Real.sqrt 2 : ℂ)] := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [gate1_eval, PrimitiveGate.eval, Qubit.H]

theorem gate1_x_det : ((gate1 .x).eval.1).det = -1 := by
  rw [gate1_x_eval, Matrix.det_fin_two];
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
theorem gate1_h_det : ((gate1 .h).eval.1).det = -1 := by
  rw [gate1_h_eval, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [show (Real.sqrt 2 : ℂ) ≠ 0 by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)]
  rw [show (Real.sqrt 2 : ℂ) ^ 2 = 2 by exact_mod_cast Real.sq_sqrt (by norm_num)]; ring
def phaseGate1 (m : Nat) : Circuit 1 :=
  match m % 8 with
  | 0 => .identity
  | 1 => gate1 .t
  | 2 => gate1 .s
  | 3 => gate1 .s ;;ᶜ gate1 .t
  | 4 => gate1 .z
  | 5 => gate1 .z ;;ᶜ gate1 .t
  | 6 => gate1 .z ;;ᶜ gate1 .s
  | _ => gate1 .z ;;ᶜ (gate1 .s ;;ᶜ gate1 .t)

theorem phaseGate1_props {m : Nat} (hm : m < 8) :
    (CircExt.isOneQubitCircuit (phaseGate1 m)) = true ∧
    (phaseGate1 m).count PrimitiveGate.T = m % 2 ∧
    (phaseGate1 m).count PrimitiveGate.TOFF = 0 ∧
    (phaseGate1 m).eval.1 = !![(1 : ℂ), 0; 0, CyclotomicEight.omegaComplex ^ m] := by
  have hm8 : m % 8 = m := Nat.mod_eq_of_lt hm;
  have hsq : CyclotomicEight.omegaComplex ^ 2 = Complex.I := CyclotomicEight.omegaComplex_sq;
  have h4 : CyclotomicEight.omegaComplex ^ 4 = -1 := CyclotomicEight.omegaComplex_pow_four
  interval_cases m <;>
    refine ⟨rfl, rfl, rfl, ?_⟩ <;>
      (unfold phaseGate1; simp only [hm8];
       ext i j : 1; fin_cases i <;> fin_cases j <;>
         simp only [Nat.reducePow, eval_identity, Fin.zero_eta, Fin.isValue, OneMemClass.coe_one,
             one_apply_eq, pow_zero, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
             Fin.mk_one, Nat.reduceAdd, ne_eq, zero_ne_one, not_false_eq_true, one_apply_ne,
             cons_val_one, one_ne_zero, gate1_t_eval, pow_one, gate1_s_eval, eval_seq,
             Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_one, mul_zero, add_zero,
             zero_mul, zero_add, gate1_z_eval, mul_neg, neg_zero, cons_mul, Nat.succ_eq_add_one,
             vecMul_cons, head_cons, one_smul, tail_cons, zero_smul, empty_vecMul, smul_cons,
             smul_eq_mul, smul_empty, empty_mul, Equiv.symm_apply_apply])
  · exact hsq.symm
  · linear_combination -CyclotomicEight.omegaComplex * hsq
  · exact h4.symm
  · linear_combination -CyclotomicEight.omegaComplex * h4
  · linear_combination -Complex.I * h4 - (CyclotomicEight.omegaComplex ^ 4) * hsq
  · linear_combination -CyclotomicEight.omegaComplex * Complex.I * h4 -
      (CyclotomicEight.omegaComplex ^ 5) * hsq

theorem phaseGate1_det {m : Nat} (hm : m < 8) : ((phaseGate1 m).eval.1).det =
    CyclotomicEight.omegaComplex ^ m := by
  rw [(phaseGate1_props hm).2.2.2, Matrix.det_fin_two];
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
def sylCircuit (c : Nat) : Circuit 1 :=
  if c = 0 then .identity
  else if c ≤ 8 then phaseGate1 (c - 1) ;;ᶜ gate1 .h
  else if c ≤ 15 then phaseGate1 (c - 8)
  else if c = 16 then gate1 .x
  else .identity


def mid1Circuit (p : Nat × Circuit 1) : Nat × Circuit 1 :=
  match Nat.ble p.1 1 with
  | true => p
  | false => (Nat.div p.1 4, p.2 ;;ᶜ sylCircuit (Nat.add (Nat.mul 2 (Nat.mod p.1 4)) 2))

def mid4Circuit (p : Nat × Circuit 1) : Nat × Circuit 1 :=
  match Nat.ble p.1 1 with
  | true => p
  | false => mid1Circuit (mid1Circuit (mid1Circuit (mid1Circuit p)))

def mid12Circuit (p : Nat × Circuit 1) : Nat × Circuit 1 :=
    mid4Circuit (mid4Circuit (mid4Circuit p))
def decodeWord2Bit (w : Nat) : Circuit 1 :=
  match Nat.beq w 0 with
  | true => .identity
  | false =>
      let cFirst := Nat.mod w 16
      let cLast := Nat.mod (Nat.div w 16) 16
      let m0 := Nat.div w 256
      let c0 := (.identity : Circuit 1) ;;ᶜ sylCircuit cFirst
      let q1 := mid12Circuit (m0, c0)
      let q2 := mid12Circuit q1
      let q3 := mid12Circuit q2
      let q4 := mid12Circuit q3
      q4.2 ;;ᶜ sylCircuit cLast
theorem bias_relations : bias = 70368744177664 ∧ biasLo = 70364449210368 ∧ biasHi = 70373039144960 ∧
    bias2 = 2 * bias :=
  ⟨rfl, rfl, rfl, rfl⟩

attribute [local irreducible] bias biasLo biasHi bias2

def BoundedBias (R x : Nat) : Prop := bias ≤ x + R ∧ x ≤ bias + R
def BoundedCol (R : Nat) (s : FastCol) : Prop :=
    BoundedBias R s.ua ∧ BoundedBias R s.ub ∧ BoundedBias R s.uc ∧ BoundedBias R s.ud ∧
    BoundedBias R s.va ∧ BoundedBias R s.vb ∧ BoundedBias R s.vc ∧ BoundedBias R s.vd
def colU (s : FastCol) : FastZ8 := ⟨unbiasS s.ua, unbiasS s.ub, unbiasS s.uc, unbiasS s.ud⟩
def colV (s : FastCol) : FastZ8 := ⟨unbiasS s.va, unbiasS s.vb, unbiasS s.vc, unbiasS s.vd⟩
def ColTracks (s : FastCol) (c : Circuit 1) (k : Nat) : Prop :=
    (CircExt.isOneQubitCircuit c) = true ∧ c.count PrimitiveGate.T = s.tCount ∧
        c.count PrimitiveGate.TOFF =
    0 ∧ s.detM < 8 ∧ c.eval.1.det = CyclotomicEight.omegaComplex ^ s.detM ∧ c.eval.1 0 0 =
    ((1 / Real.sqrt 2 : ℂ) ^ k) * (colU s).toCyc.toComplex ∧ c.eval.1 1 0 =
    ((1 / Real.sqrt 2 : ℂ) ^ k) * (colV s).toCyc.toComplex
theorem boundedBias_mono {R1 R2 x : Nat} (hR : R1 ≤ R2) (hb : BoundedBias R1 x) :
    BoundedBias R2 x :=
  ⟨by have := hb.1; omega, by have := hb.2; omega⟩

theorem boundedCol_mono {R1 R2 : Nat} {s : FastCol} (hR : R1 ≤ R2) (hb : BoundedCol R1 s) :
    BoundedCol R2 s :=
    ⟨boundedBias_mono hR hb.1, boundedBias_mono hR hb.2.1, boundedBias_mono hR hb.2.2.1,
    boundedBias_mono hR hb.2.2.2.1, boundedBias_mono hR hb.2.2.2.2.1,
    boundedBias_mono hR hb.2.2.2.2.2.1, boundedBias_mono hR hb.2.2.2.2.2.2.1,
    boundedBias_mono hR hb.2.2.2.2.2.2.2⟩
theorem inRangeCol_imp_bounded (s : FastCol) (h : inRangeCol s = true) :
    BoundedCol 4294967296 s := by
  rcases s with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
  obtain ⟨hb, hblo, hbhi, _⟩ := bias_relations
  have h1 (x : Nat) (hx : inRange1 x = true) : BoundedBias 4294967296 x := by
    unfold inRange1 at hx
    cases hlo : Nat.ble biasLo x <;> rw [hlo] at hx
    · cases hx
    · simp only [Nat.ble_eq] at hlo hx
      unfold BoundedBias
      omega
  simp only [inRangeCol, Bool.and_eq_true, and_assoc] at h
  rcases h with ⟨hua, hub, huc, hud, hva, hvb, hvc, hvd⟩
  exact ⟨h1 ua hua, h1 ub hub, h1 uc huc, h1 ud hud, h1 va hva, h1 vb hvb, h1 vc hvc, h1 vd hvd⟩
theorem bias2_sub_props {R x : Nat} (hR : R ≤ bias) (hx : BoundedBias R x) :
    BoundedBias R (Nat.sub bias2 x) ∧ (unbiasS (Nat.sub bias2 x)).toInt = -(unbiasS x).toInt := by
  have := hx.1; have := hx.2; have := bias_relations.2.2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [unbiasS_toInt, Nat.sub_eq] <;> omega
theorem had_coord_props {R u w : Nat} (hR : 2 * R ≤ bias) (hu : BoundedBias R u)
    (hw : BoundedBias R w) : BoundedBias (2 * R) (Nat.sub (Nat.add u w) bias) ∧ BoundedBias (2 * R)
    (Nat.sub (Nat.add u bias) w) ∧ (unbiasS (Nat.sub (Nat.add u w) bias)).toInt =
    (unbiasS u).toInt + (unbiasS w).toInt ∧ (unbiasS (Nat.sub (Nat.add u bias) w)).toInt =
    (unbiasS u).toInt - (unbiasS w).toInt := by
  have := hu.1; have := hu.2; have := hw.1; have := hw.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [unbiasS_toInt, Nat.add_eq, Nat.sub_eq] <;>
      omega

theorem hadStep_col_sound {R tc dm : Nat} {ok : Bool} {ua ub uc ud wa wb wc wd : Nat}
    (hR : 2 * R ≤ bias) (hu : BoundedBias R ua ∧ BoundedBias R ub ∧ BoundedBias R uc ∧
    BoundedBias R ud) (hw : BoundedBias R wa ∧ BoundedBias R wb ∧ BoundedBias R wc ∧
    BoundedBias R wd) : BoundedCol (2 * R) (hadStep tc dm ok ua ub uc ud wa wb wc wd) ∧
    (colU (hadStep tc dm ok ua ub uc ud wa wb wc wd)).toCyc.toComplex =
    (⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩ : FastZ8).toCyc.toComplex +
    (⟨unbiasS wa, unbiasS wb, unbiasS wc, unbiasS wd⟩ : FastZ8).toCyc.toComplex ∧
    (colV (hadStep tc dm ok ua ub uc ud wa wb wc wd)).toCyc.toComplex =
    (⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩ : FastZ8).toCyc.toComplex -
    (⟨unbiasS wa, unbiasS wb, unbiasS wc, unbiasS wd⟩ : FastZ8).toCyc.toComplex := by
  have ha := had_coord_props hR hu.1 hw.1; have hb := had_coord_props hR hu.2.1 hw.2.1;
  have hc := had_coord_props hR hu.2.2.1 hw.2.2.1;
  have hd :=
      had_coord_props hR hu.2.2.2 hw.2.2.2; refine ⟨⟨ha.1, hb.1, hc.1, hd.1, ha.2.1, hb.2.1, hc.2.1,
      hd.2.1⟩, ?_, ?_⟩
  · rw [← CyclotomicEight.toComplex_add]; congr 1; change FastZ8.toCyc _ = CyclotomicEight.add _ _;
    dsimp only [hadStep, colU, FastZ8.toCyc, CyclotomicEight.add];
    rw [ha.2.2.1, hb.2.2.1, hc.2.2.1, hd.2.2.1]
  · rw [← CyclotomicEight.toComplex_sub]; congr 1; change FastZ8.toCyc _ = CyclotomicEight.sub _ _;
    dsimp only [hadStep, colV, FastZ8.toCyc, CyclotomicEight.sub];
    rw [ha.2.2.2, hb.2.2.2, hc.2.2.2, hd.2.2.2]
def phaseColCoords (s : FastCol) (m : Nat) : Nat × Nat × Nat × Nat :=
  match m with
  | 0 => (s.va, s.vb, s.vc, s.vd)
  | 1 => (Nat.sub bias2 s.vd, s.va, s.vb, s.vc)
  | 2 => (Nat.sub bias2 s.vc, Nat.sub bias2 s.vd, s.va, s.vb)
  | 3 => (Nat.sub bias2 s.vb, Nat.sub bias2 s.vc, Nat.sub bias2 s.vd, s.va)
  | 4 => (Nat.sub bias2 s.va, Nat.sub bias2 s.vb, Nat.sub bias2 s.vc, Nat.sub bias2 s.vd)
  | 5 => (s.vd, Nat.sub bias2 s.va, Nat.sub bias2 s.vb, Nat.sub bias2 s.vc)
  | 6 => (s.vc, s.vd, Nat.sub bias2 s.va, Nat.sub bias2 s.vb)
  | _ => (s.vb, s.vc, s.vd, Nat.sub bias2 s.va)

theorem phase_col_vec {s : FastCol} {R m : Nat} (hR : R ≤ bias) (hb : BoundedCol R s)
    (hm : m < 8) : ∃ (wa wb wc wd : Nat), (BoundedBias R wa ∧ BoundedBias R wb ∧ BoundedBias R wc ∧
    BoundedBias R wd) ∧ (⟨unbiasS wa, unbiasS wb, unbiasS wc,
    unbiasS wd⟩ : FastZ8).toCyc.toComplex = (CyclotomicEight.omegaComplex ^ m) *
    (colV s).toCyc.toComplex ∧ (wa, wb, wc, wd) = phaseColCoords s m := by
  obtain ⟨_, _, _, _, hva, hvb, hvc, hvd⟩ := hb
  obtain ⟨nva1, nva2⟩ := bias2_sub_props hR hva
  obtain ⟨nvb1, nvb2⟩ := bias2_sub_props hR hvb
  obtain ⟨nvc1, nvc2⟩ := bias2_sub_props hR hvc
  obtain ⟨nvd1, nvd2⟩ := bias2_sub_props hR hvd
  refine ⟨(phaseColCoords s m).1, (phaseColCoords s m).2.1, (phaseColCoords s m).2.2.1,
      (phaseColCoords s m).2.2.2, ?_, ?_, rfl⟩
  · interval_cases m <;> dsimp only [phaseColCoords] <;> exact ⟨by assumption, by assumption,
        by assumption, by assumption⟩
  · rw [← fzMulOmega_toComplex m (colV s)]
    congr 1
    interval_cases m <;> dsimp only [phaseColCoords, fzMulOmega, colV,
        FastZ8.toCyc] <;> simp only [sNeg_toInt, nva2, nvb2, nvc2, nvd2]
theorem hadStep_congr_td {tc1 tc2 dm1 dm2 : Nat} (htc : tc1 = tc2) (hdm : dm1 = dm2) (ok : Bool)
    (ua ub uc ud wa wb wc wd : Nat) : hadStep tc1 dm1 ok ua ub uc ud wa wb wc wd =
    hadStep tc2 dm2 ok ua ub uc ud wa wb wc wd := by subst htc; subst hdm; rfl
theorem fastCol_congr_td {tc1 tc2 dm1 dm2 : Nat} (htc : tc1 = tc2) (hdm : dm1 = dm2) (ok : Bool)
    (ua ub uc ud va vb vc vd : Nat) : FastCol.mk tc1 dm1 ok ua ub uc ud va vb vc vd =
    FastCol.mk tc2 dm2 ok ua ub uc ud va vb vc vd := by subst htc; subst hdm; rfl
theorem stepSyl_sound {R c k : Nat} {s : FastCol} {circ : Circuit 1}
    (hc : c ≤ 16) (hR : 2 * R ≤ bias) (hb : BoundedCol R s) (htr : ColTracks s circ k) :
    BoundedCol (2 * R) (stepSyl c s) ∧
    ∃ k' : Nat, ColTracks (stepSyl c s) (circ ;;ᶜ sylCircuit c) k' := by
  obtain ⟨hc1, hcT, hcToff, hdm, hdet, h00, h10⟩ := htr
  have hR1 : R ≤ bias := by omega
  have huB : BoundedBias R s.ua ∧ BoundedBias R s.ub ∧ BoundedBias R s.uc ∧ BoundedBias R s.ud :=
      ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1⟩
  by_cases hc0 : c = 0
  · subst hc0
    rw [show stepSyl 0 s = s by cases s; rfl, show sylCircuit 0 = .identity from rfl]
    refine ⟨boundedCol_mono (by omega) hb, k, by simp [CircExt.isOneQubitCircuit, hc1], hcT, hcToff,
        hdm,
      by simp [Circuit.eval_seq, hdet], by simp [Circuit.eval_seq, h00],
          by simp [Circuit.eval_seq, h10]⟩
  · by_cases hc8 : c ≤ 8
    · set m := c - 1 with hm_def
      have hm : m < 8 := by omega
      obtain ⟨hp1, hpT, hpToff, hpEval⟩ :=
          phaseGate1_props hm; obtain ⟨wa, wb, wc, wd, hwB, hwC, hwEq⟩ := phase_col_vec hR1 hb hm
      have hsy : sylCircuit c = phaseGate1 m ;;ᶜ gate1 .h := by
        unfold sylCircuit; simp [hc0, hc8, m]
      have hhad :=
          hadStep_col_sound hR huB hwB (tc := s.tCount + m % 2) (dm := (s.detM + m + 4) % 8)
          (ok := s.ok)
      have hstep_eq : stepSyl c s = hadStep (s.tCount + m % 2)
          ((s.detM + m + 4) % 8) s.ok s.ua s.ub s.uc s.ud wa wb wc wd := by
        have hc1_ge : 1 ≤ c := by omega
        have hmod_def : ∀ x : Nat, Nat.mod x 8 = x % 8 := fun _ => rfl
        rcases s with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
        dsimp only at hdm
        interval_cases c <;> (
          rw [hm_def] at hwEq
          dsimp [phaseColCoords] at hwEq
          rcases hwEq with ⟨rfl, rfl, rfl, rfl⟩
          dsimp only [stepSyl, Nat.ble, Nat.beq]
          apply hadStep_congr_td <;> rw [hm_def] <;> (try simp only [Nat.add_eq,
            hmod_def]) <;> omega)
      rw [hstep_eq, hsy]
      refine ⟨hhad.1, k + 1, by simp [CircExt.isOneQubitCircuit, hc1, hp1],
        by change circ.count _ + ((phaseGate1 m).count _ + 0) = s.tCount + m % 2; omega,
        by change circ.count _ + ((phaseGate1 m).count _ + 0) = 0; omega,
        Nat.mod_lt _ (by omega), ?_, ?_, ?_⟩
      · dsimp only [hadStep];
        simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.det_mul, gate1_h_det,
            phaseGate1_det hm,
            hdet]; have hneg1 : (-1 : ℂ) = CyclotomicEight.omegaComplex ^ 4 :=
                     CyclotomicEight.omegaComplex_pow_four.symm; rw [hneg1,
                     omegaComplex_pow_mod_eight, ← pow_add, ← pow_add]
        exact congrArg _ (by omega)
      · rw [hhad.2.1, hwC]; dsimp only [colU] at h00 ⊢;
        simp [Circuit.eval_seq, gate1_h_eval, hpEval, Matrix.mul_apply, Fin.sum_univ_two, h00, h10];
        ring
      · rw [hhad.2.2, hwC]; dsimp only [colU] at h00 ⊢;
        simp [Circuit.eval_seq, gate1_h_eval, hpEval, Matrix.mul_apply, Fin.sum_univ_two, h00, h10];
        ring
    · by_cases hc15 : c ≤ 15
      · set m := c - 8 with hm_def
        have hm1 : 1 ≤ m := by omega
        have hm : m < 8 := by omega
        obtain ⟨hp1, hpT, hpToff, hpEval⟩ :=
            phaseGate1_props hm; obtain ⟨wa, wb, wc, wd, hwB, hwC, hwEq⟩ := phase_col_vec hR1 hb hm
        have hsy : sylCircuit c = phaseGate1 m := by unfold sylCircuit; simp [hc0, hc8, hc15, m]
        have hstep_eq : stepSyl c s = ⟨s.tCount + m % 2, (s.detM + m) % 8, s.ok, s.ua, s.ub, s.uc,
            s.ud, wa, wb, wc, wd⟩ := by
          have hc9_ge : 9 ≤ c := by omega
          have hmod_def : ∀ x : Nat, Nat.mod x 8 = x % 8 := fun _ => rfl
          rcases s with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
          interval_cases c <;> (
            rw [hm_def] at hwEq
            dsimp [phaseColCoords] at hwEq
            rcases hwEq with ⟨rfl, rfl, rfl, rfl⟩
            dsimp only [stepSyl, Nat.ble, Nat.beq]
            apply fastCol_congr_td <;> rw [hm_def] <;>
              ((try simp only [Nat.add_eq, hmod_def]); try omega))
        rw [hstep_eq, hsy]
        refine ⟨boundedCol_mono (by omega) ⟨huB.1, huB.2.1, huB.2.2.1, huB.2.2.2, hwB.1, hwB.2.1,
            hwB.2.2.1, hwB.2.2.2⟩, k,
          by simp [CircExt.isOneQubitCircuit, hc1, hp1],
          by change circ.count _ + (phaseGate1 m).count _ = s.tCount + m % 2; omega,
          by change circ.count _ + (phaseGate1 m).count _ = 0; omega,
          Nat.mod_lt _ (by omega), ?_, ?_, ?_⟩
        · simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.det_mul, phaseGate1_det hm, hdet,
            omegaComplex_pow_mod_eight, ← pow_add]
          exact congrArg _ (by omega)
        · simp [colU, Circuit.eval_seq, hpEval, Matrix.mul_apply, Fin.sum_univ_two, h00]
        · dsimp only [colV]; rw [hwC]; change ((phaseGate1 m).eval.1 * circ.eval.1) 1 0 = _;
          simp [hpEval, Matrix.mul_apply, Fin.sum_univ_two, h10]; ring
      · have hc16 : c = 16 := by omega
        subst hc16
        have hstep_eq : stepSyl 16 s = ⟨s.tCount, (s.detM + 4) % 8, s.ok, s.va, s.vb, s.vc, s.vd,
            s.ua, s.ub, s.uc, s.ud⟩ := by rcases s; rfl
        rw [hstep_eq, show sylCircuit 16 = gate1 .x from rfl]
        refine ⟨boundedCol_mono (by omega) ⟨hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1,
            hb.2.2.2.2.2.2.2, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1⟩, k,
          by simp [CircExt.isOneQubitCircuit, hc1], hcT, hcToff, Nat.mod_lt _ (by omega), ?_, ?_,
              ?_⟩
        · simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.det_mul, gate1_x_det, hdet,
            CyclotomicEight.omegaComplex_pow_four.symm, omegaComplex_pow_mod_eight, ← pow_add]
          exact congrArg _ (by omega)
        · simp [colU, colV, Circuit.eval_seq, gate1_x_eval, Matrix.mul_apply, Fin.sum_univ_two,
            h10]
        · simp [colU, colV, Circuit.eval_seq, gate1_x_eval, Matrix.mul_apply, Fin.sum_univ_two,
            h00]

theorem fastColInit_tracks : ColTracks fastColInit .identity 0 := by
  refine ⟨rfl, rfl, rfl, by decide, by simp [fastColInit], ?_, ?_⟩
  · have h : (colU fastColInit).toCyc = 1 := by
      change FastZ8.toCyc (colU fastColInit) = CyclotomicEight.one;
      dsimp only [colU, fastColInit, FastZ8.toCyc, CyclotomicEight.one];
      simp only [unbiasS_toInt, Nat.add_eq]
      congr 1 <;> omega
    simp [h]
  · have h : (colV fastColInit).toCyc = 0 := by
      change FastZ8.toCyc (colV fastColInit) = CyclotomicEight.zero;
      dsimp only [colV, fastColInit, FastZ8.toCyc, CyclotomicEight.zero]; simp only [unbiasS_toInt]
      congr 1 <;> omega
    simp [h]
/-! ### 4. `checkWordLimbsBox_sound`, `conjCircuit`, `applyD8Circuit`, and `cosetCircuit` -/

theorem box_scale_lower_bound {q denLo denHi numLo : SInt} {D N : ℝ}
    (hdPos : 0 < (denLo.toInt : ℝ)) (hdLo : (denLo.toInt : ℝ) ≤ D) (hdHi : D ≤ (denHi.toInt : ℝ))
        (hnLo : (numLo.toInt : ℝ) ≤ N)
    (hle : sLe (match sNonneg q with | true => sMul q denHi | false => sMul q denLo)
        (sMul numLo boxScaleS) = true) :
    (q.toInt : ℝ) / (2 ^ 52 : ℝ) ≤ N / D := by
  have hleR :
      (((match sNonneg q with | true => sMul q denHi | false => sMul q denLo).toInt : ℤ) : ℝ) ≤
      (((sMul numLo boxScaleS).toInt : ℤ) : ℝ) := by exact_mod_cast (sLe_iff _ _).mp hle
  rw [sMul_toInt, Int.cast_mul, show (boxScaleS.toInt : ℝ) =
      2 ^ 52 by norm_num [boxScaleS, SInt.toInt]] at hleR
  rw [div_le_div_iff₀ (by positivity) (hdPos.trans_le hdLo)]
  cases hnn : sNonneg q <;> simp only [hnn, sMul_toInt, Int.cast_mul] at hleR
  · nlinarith [show (q.toInt : ℝ) < 0 by exact_mod_cast (sNonneg_false_iff q).mp hnn]
  · nlinarith [show (0 : ℝ) ≤ q.toInt by exact_mod_cast (sNonneg_iff q).mp hnn]
theorem box_scale_upper_bound {q denLo denHi numHi : SInt} {D N : ℝ}
    (hdPos : 0 < (denLo.toInt : ℝ)) (hdLo : (denLo.toInt : ℝ) ≤ D) (hdHi : D ≤ (denHi.toInt : ℝ))
        (hnHi : N ≤ (numHi.toInt : ℝ))
    (hle : sLe (sMul numHi boxScaleS)
        (match sNonneg q with | true => sMul q denLo | false => sMul q denHi) = true) :
    N / D ≤ (q.toInt : ℝ) / (2 ^ 52 : ℝ) := by
  have hleR : (((sMul numHi boxScaleS).toInt : ℤ) : ℝ) ≤
      (((match sNonneg q with | true => sMul q denLo | false => sMul q denHi).toInt : ℤ) : ℝ) := by
    exact_mod_cast (sLe_iff _ _).mp hle
  rw [sMul_toInt, Int.cast_mul, show (boxScaleS.toInt : ℝ) =
      2 ^ 52 by norm_num [boxScaleS, SInt.toInt]] at hleR
  rw [div_le_div_iff₀ (hdPos.trans_le hdLo) (by positivity)]
  cases hnn : sNonneg q <;> simp only [hnn, sMul_toInt, Int.cast_mul] at hleR
  · nlinarith [show (q.toInt : ℝ) < 0 by exact_mod_cast (sNonneg_false_iff q).mp hnn]
  · nlinarith [show (0 : ℝ) ≤ q.toInt by exact_mod_cast (sNonneg_iff q).mp hnn]
theorem stepMid1_fst (m : Nat) (s : FastCol) (c : Circuit 1) : (stepMid1 (m, s)).1 =
    (mid1Circuit (m, c)).1 := by
  unfold stepMid1 mid1Circuit
  cases Nat.ble m 1 <;> rfl
theorem stepMid1_fst_pair {p : Nat × FastCol} {q : Nat × Circuit 1}
    (hf : p.1 = q.1) : (stepMid1 p).1 = (mid1Circuit q).1 := by
  rw [← Prod.eta p, ← Prod.eta q, hf]
  exact stepMid1_fst q.1 p.2 q.2
theorem stepMid4_fst (m : Nat) (s : FastCol) (c : Circuit 1) : (stepMid4 (m, s)).1 =
    (mid4Circuit (m, c)).1 := by
  unfold stepMid4 mid4Circuit; dsimp only
  cases Nat.ble m 1 with
  | true => rfl
  | false => exact stepMid1_fst_pair (stepMid1_fst_pair (stepMid1_fst_pair (stepMid1_fst m s c)))
theorem stepMid4_fst_pair {p : Nat × FastCol} {q : Nat × Circuit 1}
    (hf : p.1 = q.1) : (stepMid4 p).1 = (mid4Circuit q).1 := by
  rw [← Prod.eta p, ← Prod.eta q, hf]
  exact stepMid4_fst q.1 p.2 q.2
theorem stepMid12Raw_fst (m : Nat) (s : FastCol) (c : Circuit 1) : (stepMid12Raw (m, s)).1 =
    (mid12Circuit (m, c)).1 :=
  stepMid4_fst_pair (stepMid4_fst_pair (stepMid4_fst m s c))
theorem stepMid1_sound {R m k : Nat} {s : FastCol} {c : Circuit 1} (hR : 2 * R ≤ bias)
    (hb : BoundedCol R s) (htr : ColTracks s c k) : BoundedCol (2 * R) (stepMid1 (m, s)).2 ∧ ∃ k' :
    Nat, ColTracks (stepMid1 (m, s)).2 (mid1Circuit (m, c)).2 k' := by
  unfold stepMid1 mid1Circuit; dsimp only
  cases Nat.ble m 1 with
  | true => exact ⟨boundedCol_mono (by omega) hb, k, htr⟩
  | false => exact stepSyl_sound (show 2 * (m % 4) + 2 ≤ 16 by omega) hR hb htr
theorem stepMid1_pair {R k : Nat} {p : Nat × FastCol} {q : Nat × Circuit 1} (hR : 2 * R ≤ bias)
    (hf : p.1 = q.1) (hb : BoundedCol R p.2) (htr : ColTracks p.2 q.2 k) :
    (stepMid1 p).1 = (mid1Circuit q).1 ∧ BoundedCol (2 * R) (stepMid1 p).2 ∧ ∃ k',
        ColTracks (stepMid1 p).2 (mid1Circuit q).2 k' := by
  rw [← Prod.eta p, ← Prod.eta q, hf]
  exact ⟨stepMid1_fst q.1 p.2 q.2, stepMid1_sound hR hb htr⟩
theorem stepMid4_sound {R m k : Nat} {s : FastCol} {c : Circuit 1} (hR : 16 * R ≤ bias)
    (hb : BoundedCol R s) (htr : ColTracks s c k) : BoundedCol (16 * R) (stepMid4 (m, s)).2 ∧ ∃ k' :
    Nat, ColTracks (stepMid4 (m, s)).2 (mid4Circuit (m, c)).2 k' := by
  unfold stepMid4 mid4Circuit; dsimp only
  cases Nat.ble m 1 with
  | true => exact ⟨boundedCol_mono (by omega) hb, k, htr⟩
  | false =>
    obtain ⟨hf1, hb1, _, htr1⟩ := stepMid1_pair (p := (m, s)) (q := (m, c)) (by omega) rfl hb htr
    obtain ⟨hf2, hb2, _, htr2⟩ := stepMid1_pair (by omega) hf1 hb1 htr1
    obtain ⟨hf3, hb3, _, htr3⟩ := stepMid1_pair (by omega) hf2 hb2 htr2
    obtain ⟨_, hb4, k4, htr4⟩ := stepMid1_pair (by omega) hf3 hb3 htr3
    exact ⟨boundedCol_mono (by omega) hb4, k4, htr4⟩
theorem stepMid4_pair {R k : Nat} {p : Nat × FastCol} {q : Nat × Circuit 1} (hR : 16 * R ≤ bias)
    (hf : p.1 = q.1) (hb : BoundedCol R p.2) (htr : ColTracks p.2 q.2 k) :
    (stepMid4 p).1 = (mid4Circuit q).1 ∧ BoundedCol (16 * R) (stepMid4 p).2 ∧ ∃ k',
        ColTracks (stepMid4 p).2 (mid4Circuit q).2 k' := by
  rw [← Prod.eta p, ← Prod.eta q, hf]
  exact ⟨stepMid4_fst q.1 p.2 q.2, stepMid4_sound hR hb htr⟩
theorem stepMid12Raw_sound {m k : Nat} {s : FastCol} {c : Circuit 1} (hin : inRangeCol s = true)
    (htr : ColTracks s c k) : ∃ k' : Nat, ColTracks (stepMid12Raw (m, s)).2 (mid12Circuit (m,
    c)).2 k' := by
  unfold stepMid12Raw mid12Circuit
  have := bias_relations.1
  obtain ⟨hf1, hb1, _, htr1⟩ := stepMid4_pair (p := (m, s)) (q := (m, c)) (by omega) rfl
    (inRangeCol_imp_bounded s hin) htr
  obtain ⟨hf2, hb2, _, htr2⟩ := stepMid4_pair (by omega) hf1 hb1 htr1
  exact (stepMid4_pair (by omega) hf2 hb2 htr2).2.2
theorem stepMid12Raw_pair_sound {p : Nat × FastCol} {q : Nat × Circuit 1} {k : Nat}
    (hfst : p.1 = q.1) (hin : inRangeCol p.2 = true) (htr : ColTracks p.2 q.2 k) :
    (stepMid12Raw p).1 = (mid12Circuit q).1 ∧ ∃ k' : Nat,
    ColTracks (stepMid12Raw p).2 (mid12Circuit q).2 k' := by
  rw [← Prod.eta p, ← Prod.eta q, hfst]
  exact ⟨stepMid12Raw_fst q.1 p.2 q.2, stepMid12Raw_sound hin htr⟩
theorem decodeWord2Bit_sound {w : Nat} (hok : (evalWord2Bit w).ok = true) : ∃ k : Nat,
    ColTracks (evalWord2Bit w) (decodeWord2Bit w) k := by
  unfold evalWord2Bit decodeWord2Bit at *
  cases hbw : Nat.beq w 0 with
  | true => exact ⟨0, fastColInit_tracks⟩
  | false =>
    simp only [hbw] at hok ⊢
    set s0 := stepSyl (Nat.mod w 16) fastColInit
    set c0 := (.identity : Circuit 1) ;;ᶜ sylCircuit (Nat.mod w 16)
    set p1 := stepMid12Raw (Nat.div w 256, s0)
    set q1 := mid12Circuit (Nat.div w 256, c0)
    set p2 := stepMid12Raw p1
    set p3 := stepMid12Raw p2
    set p4 := stepMid12Raw p3
    set sf := stepSyl (Nat.mod (Nat.div w 16) 16) p4.2
    simp only [Bool.and_eq_true, and_assoc] at hok;
    obtain ⟨hin0, hin1, hin2, hin3, hin4, hp4_end, hsf_ok⟩ := hok;
    have hbias : bias = 70368744177664 := bias_relations.1
    have hb_init : BoundedCol 4294967296 fastColInit := by
      dsimp only [BoundedCol, BoundedBias, fastColInit]; simp only [Nat.add_eq]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
             ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    obtain ⟨_, k0, htr0⟩ :=
        stepSyl_sound (show w % 16 ≤ 16 by omega) (by omega) hb_init fastColInit_tracks
    obtain ⟨k1, htr1⟩ := stepMid12Raw_sound hin0 htr0
    obtain ⟨hf2, k2, htr2⟩ :=
        stepMid12Raw_pair_sound (stepMid12Raw_fst (Nat.div w 256) s0 c0) hin1 htr1
    obtain ⟨hf3, k3, htr3⟩ := stepMid12Raw_pair_sound hf2 hin2 htr2
    obtain ⟨_, k4, htr4⟩ := stepMid12Raw_pair_sound hf3 hin3 htr3
    obtain ⟨_, kf, htrf⟩ :=
        stepSyl_sound (show (w / 16) % 16 ≤ 16 by omega) (by omega)
        (inRangeCol_imp_bounded p4.2 hin4) htr4
    rw [show { sf with ok := (inRangeCol s0 && inRangeCol p1.2 && inRangeCol p2.2 &&
        inRangeCol p3.2 && inRangeCol p4.2 && Nat.beq p4.1 1 && sf.ok) } = sf by
      cases sf
      simp [hin0, hin1, hin2, hin3, hin4, hp4_end]]
    exact ⟨kf, htrf⟩
theorem checkWord2BitBox_sound {tCap w : Nat} {bx : Box2DS}
    (hchk : checkWord2BitBox tCap w bx = true) :
    let c := decodeWord2Bit w
    (CircExt.isOneQubitCircuit c) = true ∧ c.count PrimitiveGate.T ≤ tCap ∧
        c.count PrimitiveGate.TOFF = 0 ∧
        c.eval.1 0 0 ≠ 0 ∧ bx.Mem (matEta c.eval.1) := by
  set st := evalWord2Bit w with hst_def
  unfold checkWord2BitBox at hchk
  rcases hst : st with ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩
  rw [← hst_def, hst] at hchk
  simp only [Bool.and_eq_true, and_assoc] at hchk
  obtain ⟨hok, _, _, htc_le, hden_pos, _, _, hx0, hx1, hy0, hy1⟩ := hchk
  obtain ⟨k, hc1, hcT, hcToff, _, _, h00, h10⟩ :=
      decodeWord2Bit_sound (w := w) (by rwa [← hst_def, hst])
  rw [← hst_def, hst] at hcT h00 h10
  set c := decodeWord2Bit w
  set u : FastZ8 := ⟨unbiasS ua, unbiasS ub, unbiasS uc, unbiasS ud⟩
  set v : FastZ8 := ⟨unbiasS va, unbiasS vb, unbiasS vc, unbiasS vd⟩
  set wden := fzMul u (fzConj u)
  set wnum := fzNeg (fzMul (fzConj v) u)
  have hwden_c : wden.toCyc.toComplex = ((‖u.toCyc.toComplex‖ ^ 2 : ℝ) : ℂ) := by
    simp only [wden, fzMul_toCyc, CyclotomicEight.toComplex_mul, fzConj_toComplex,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hwden_re : wden.toCyc.toComplex.re = ‖u.toCyc.toComplex‖ ^ 2 := by
    rw [hwden_c, Complex.ofReal_re]
  have hdenLo_pos : 0 < ((fzReLo wden).toInt : ℝ) := by
    exact_mod_cast (sPos_iff (fzReLo wden)).mp hden_pos
  have hdenLo_le := fzReLo_le wden
  have hdenHi_ge := le_fzReHi wden
  have hu_pos : 0 < ‖u.toCyc.toComplex‖ ^ 2 := by nlinarith [hwden_re, hdenLo_pos, hdenLo_le]
  have hu_ne : u.toCyc.toComplex ≠ 0 := fun h0 => by norm_num [h0] at hu_pos
  have hs_ne : ((1 / Real.sqrt 2 : ℂ) ^ k) ≠ 0 :=
    pow_ne_zero k (by exact_mod_cast (show (0 : ℝ) < 1 / Real.sqrt 2 by positivity).ne')
  have heta : matEta c.eval.1 = wnum.toCyc.toComplex / ((wden.toCyc.toComplex.re : ℝ) : ℂ) := by
    unfold matEta
    rw [h00, h10, show colU ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ = u from rfl,
      show colV ⟨tc, dm, ok, ua, ub, uc, ud, va, vb, vc, vd⟩ = v from rfl,
          mul_div_mul_left _ _ hs_ne, map_div₀,
      show wnum.toCyc.toComplex = -(conj v.toCyc.toComplex *
          u.toCyc.toComplex) by simp [wnum, fzNeg_toCyc, fzMul_toCyc, fzConj_toComplex],
      hwden_re, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    have hconj_ne : conj u.toCyc.toComplex ≠ 0 := star_ne_zero.mpr hu_ne
    field_simp [hu_ne, hconj_ne]
  have heta_re : (matEta c.eval.1).re = ((2 * 10 ^ 18 : ℝ) * wnum.toCyc.toComplex.re) /
      ((2 * 10 ^ 18 : ℝ) * wden.toCyc.toComplex.re) := by
    rw [heta, Complex.div_ofReal_re]
    field_simp
  have heta_im : (matEta c.eval.1).im = ((2 * 10 ^ 18 : ℝ) * wnum.toCyc.toComplex.im) /
      ((2 * 10 ^ 18 : ℝ) * wden.toCyc.toComplex.re) := by
    rw [heta, Complex.div_ofReal_im]
    field_simp
  refine ⟨hc1, hcT.trans_le ((nat_ble_true_iff tc tCap).mp htc_le), hcToff,
      ne_of_eq_of_ne h00 (mul_ne_zero hs_ne hu_ne), ?_, ?_, ?_, ?_⟩
  · exact (box_scale_lower_bound hdenLo_pos hdenLo_le hdenHi_ge (fzReLo_le wnum) hx0).trans_eq
        heta_re.symm
  · exact (le_of_eq heta_re).trans (box_scale_upper_bound hdenLo_pos hdenLo_le hdenHi_ge (le_fzReHi
        wnum) hx1)
  · exact (box_scale_lower_bound hdenLo_pos hdenLo_le hdenHi_ge (fzImLo_le wnum) hy0).trans_eq
        heta_im.symm
  · exact (le_of_eq heta_im).trans (box_scale_upper_bound hdenLo_pos hdenLo_le hdenHi_ge (le_fzImHi
        wnum) hy1)
def conjGate1 (g : PrimitiveGate 1) : Circuit 1 :=
  match g with
  | .x => gate1 .x
  | .y => gate1 .z ;;ᶜ (gate1 .y ;;ᶜ gate1 .z)
  | .z => gate1 .z
  | .h => gate1 .h
  | .s => gate1 .z ;;ᶜ gate1 .s
  | .t => gate1 .z ;;ᶜ (gate1 .s ;;ᶜ gate1 .t)

def conjCircuit : Circuit 1 → Circuit 1
  | .identity => .identity
  | .gate (k := 1) g _ => conjGate1 g
  | .gate (k := _) g r => .gate g r
  | .seq c1 c2 => .seq (conjCircuit c1) (conjCircuit c2)

theorem conjGate1_props (g : PrimitiveGate 1) (r : QRegister 1 1) :
    (CircExt.isOneQubitCircuit (conjGate1 g)) = true ∧ (conjGate1 g).count PrimitiveGate.T =
    (Circuit.gate g r).count PrimitiveGate.T ∧ (conjGate1 g).count PrimitiveGate.TOFF =
    (Circuit.gate g r).count PrimitiveGate.TOFF ∧ (conjGate1 g).eval.1 =
    (g.eval.1).map (starRingEnd ℂ) := by
  cases g <;>
    refine ⟨rfl, rfl, rfl, ?_⟩ <;>
      (ext i j : 1; fin_cases i <;> fin_cases j <;>
      (simp only [Nat.reducePow, conjGate1, Fin.zero_eta, Fin.isValue, gate1_x_eval, of_apply,
          cons_val', cons_val_zero, cons_val_fin_one, PrimitiveGate.eval, Qubit.X, map_apply,
          map_zero, Fin.mk_one, cons_val_one, map_one, eval_seq, Submonoid.coe_mul, gate1_z_eval,
          gate1_y_eval, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
          one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, neg_smul, neg_cons, neg_zero,
          neg_empty, zero_add, empty_mul, Equiv.symm_apply_apply, Matrix.mul_apply,
          Fin.sum_univ_two, mul_one, mul_zero, Qubit.Y, mul_neg, neg_neg, map_neg, Complex.conj_I,
          Qubit.Z, gate1_h_eval, one_div, Qubit.H, sqrt_inv, smul_of, smul_cons, Complex.real_smul,
          Complex.ofReal_inv, smul_empty, smul_neg, map_inv₀, Complex.conj_ofReal, gate1_s_eval,
          Qubit.S, gate1_t_eval, CyclotomicEight.omegaComplex, smul_eq_mul, Qubit.T, map_div₀,
          map_add];
       try (ring_nf; simp [Complex.I_sq])))

theorem conjCircuit_sound (c : Circuit 1) (hc : (CircExt.isOneQubitCircuit c) = true) :
    (CircExt.isOneQubitCircuit (conjCircuit c)) = true ∧ (conjCircuit c).count PrimitiveGate.T =
    c.count PrimitiveGate.T ∧ (conjCircuit c).count PrimitiveGate.TOFF =
    c.count PrimitiveGate.TOFF ∧ (conjCircuit c).eval.1 = (c.eval.1).map (starRingEnd ℂ) := by
  induction c with
  | identity =>
    exact ⟨rfl, rfl, rfl, Matrix.ext fun i j ↦
        by fin_cases i <;> fin_cases j <;> simp [conjCircuit]⟩
  | @gate k g r =>
    rcases k with _ | _ | _
    · cases hc
    · have hr : r = QRegister.whole 1 := by
        ext i; simp [Fin.eq_zero i]
      obtain ⟨h1, h2, h3, h4⟩ := conjGate1_props g r
      exact ⟨h1, h2, h3,
          by simpa [conjCircuit, Circuit.eval_gate, hr, QRegister.whole_embedUnitary] using h4⟩
    · cases hc
  | seq c1 c2 ih1 ih2 =>
    simp only [CircExt.isOneQubitCircuit, Bool.and_eq_true] at hc
    obtain ⟨h1a, h1b, h1c, h1d⟩ := ih1 hc.1
    obtain ⟨h2a, h2b, h2c, h2d⟩ := ih2 hc.2
    refine ⟨by simp [conjCircuit, CircExt.isOneQubitCircuit, h1a, h2a],
      by simpa [conjCircuit, Circuit.count] using congrArg₂ (· + ·) h1b h2b,
      by simpa [conjCircuit, Circuit.count] using congrArg₂ (· + ·) h1c h2c, ?_⟩
    simp only [conjCircuit, Circuit.eval_seq, Submonoid.coe_mul, h1d, h2d]
    exact Matrix.ext fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def rotGate1 (r : Nat) : Circuit 1 :=
  match r % 4 with
  | 0 => .identity
  | 1 => gate1 .s
  | 2 => gate1 .z
  | _ => gate1 .z ;;ᶜ gate1 .s

theorem rotGate1_eq_phaseGate1 (r : Nat) : rotGate1 r = phaseGate1 (2 * (r % 4)) := by
  unfold rotGate1 phaseGate1
  have : r % 4 < 4 := Nat.mod_lt r (by decide)
  interval_cases (r % 4) <;> rfl
theorem rotGate1_props (r : Nat) :
    (CircExt.isOneQubitCircuit (rotGate1 r)) = true ∧ (rotGate1 r).count PrimitiveGate.T = 0 ∧
        (rotGate1 r).count PrimitiveGate.TOFF = 0 ∧
    (rotGate1 r).eval.1 = (Matrix.of ![![(1 : ℂ), 0], ![0, Complex.I ^ (r % 4)]]) ∧
        (rotGate1 r).eval.1 = phaseTurn (((r % 4 : Nat) : ℝ) / 4) := by
  obtain ⟨h1, hT, hToff, hEv⟩ := phaseGate1_props (show 2 * (r % 4) < 8 by omega)
  rw [rotGate1_eq_phaseGate1 r]
  have hI : CyclotomicEight.omegaComplex ^ (2 * (r % 4)) = Complex.I ^ (r % 4) := by
    rw [pow_mul, CyclotomicEight.omegaComplex_sq]
  have hp : Complex.I ^ (r % 4) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((r % 4 : Nat) : ℝ) / 4)) := by
    rw [congrArg (· ^ (r % 4)) (show Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) *
        Complex.I) by
      simp [Complex.exp_mul_I]), ← Complex.exp_nat_mul]
    exact congrArg Complex.exp (by push_cast; ring)
  refine ⟨h1, hT.trans (by omega), hToff, by rwa [hI] at hEv, ?_⟩
  rw [hEv, hI, hp, phaseTurn_eq]
  push_cast; rfl
def applyD8Circuit (sym : Nat) (c : Circuit 1) : Circuit 1 :=
  let c1 := if sym % 2 = 1 then conjCircuit c else c
  c1 ;;ᶜ rotGate1 (sym / 2)

theorem applyD8Circuit_sound (sym : Nat) (c : Circuit 1) (bx : Box2DS)
    (hc : (CircExt.isOneQubitCircuit c) =
        true) (h00 : c.eval.1 0 0 ≠ 0) (hmem : bx.Mem (matEta c.eval.1)) :
    (CircExt.isOneQubitCircuit (applyD8Circuit sym c)) = true ∧
        (applyD8Circuit sym c).count PrimitiveGate.T =
    c.count PrimitiveGate.T ∧ (applyD8Circuit sym c).count PrimitiveGate.TOFF =
    c.count PrimitiveGate.TOFF ∧ (applyD8Circuit sym c).eval.1 0 0 ≠ 0 ∧
    (applyD8Box bx sym).Mem (matEta (applyD8Circuit sym c).eval.1) := by
  unfold applyD8Circuit
  set c1 := if sym % 2 = 1 then conjCircuit c else c
  obtain ⟨hr1, hrT, hrToff, hrMat, _⟩ := rotGate1_props (sym / 2)
  set y0 : SInt := match Nat.beq (Nat.mod sym 2) 1 with
    | true => sNeg bx.y1
    | false => bx.y0 with hy0_def
  set y1 : SInt := match Nat.beq (Nat.mod sym 2) 1 with
    | true => sNeg bx.y0
    | false => bx.y1 with hy1_def
  have hc1_all : (CircExt.isOneQubitCircuit c1) = true ∧ c1.count PrimitiveGate.T =
      c.count PrimitiveGate.T ∧
      c1.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF ∧ c1.eval.1 0 0 ≠ 0 ∧
      (Box2DS.mk bx.x0 bx.x1 y0 y1).Mem (matEta c1.eval.1) := by
    rcases Nat.mod_two_eq_zero_or_one sym with hpar | hpar
    · rw [show c1 = c by simp [c1, hpar],
        show y0 = bx.y0 by rw [hy0_def, show Nat.mod sym 2 = sym % 2 from rfl, hpar],
        show y1 = bx.y1 by rw [hy1_def, show Nat.mod sym 2 = sym % 2 from rfl, hpar]]
      exact ⟨hc, rfl, rfl, h00, hmem⟩
    · simp only [c1, hy0_def, hy1_def, show Nat.mod sym 2 = sym % 2 from rfl, hpar, ↓reduceIte,
          Nat.beq]
      obtain ⟨hj1, hjT, hjToff, hjEv⟩ := conjCircuit_sound c hc
      have hjEta : matEta (conjCircuit c).eval.1 = conj (matEta c.eval.1) := by
        simp [matEta, hjEv]
      rcases hmem with ⟨hx0, hx1, hy0, hy1⟩
      refine ⟨hj1, hjT, hjToff, by simp [hjEv, h00], ?_⟩
      simp only [Box2DS.Mem, hjEta, Complex.conj_re, Complex.conj_im, sNeg_toInt, Int.cast_neg]
      exact ⟨hx0, hx1, by linarith, by linarith⟩
  obtain ⟨hc1_1q, hc1_T, hc1_Toff, hc1_00, hx0, hx1, hy0, hy1⟩ := hc1_all
  refine ⟨by simp [CircExt.isOneQubitCircuit, hc1_1q, hr1],
    by simpa [Circuit.count, hrT] using hc1_T,
    by simpa [Circuit.count, hrToff] using hc1_Toff,
    by simp [Circuit.eval_seq, hrMat, Matrix.mul_apply, Fin.sum_univ_two, hc1_00], ?_⟩
  have hrot_eta : matEta (c1 ;;ᶜ rotGate1 (sym / 2)).eval.1 =
      conj (Complex.I ^ ((sym / 2) % 4)) * matEta c1.eval.1 := by
    simp only [matEta, Circuit.eval_seq, Submonoid.coe_mul, hrMat, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul,
        zero_mul, add_zero, zero_add]
    rw [mul_div_assoc, map_mul]
    ring
  rw [hrot_eta, show applyD8Box bx sym =
      let r := (sym / 2) % 4
      match Nat.ble r 1 with
      | true =>
        match Nat.beq r 0 with
          | true => ⟨bx.x0, bx.x1, y0, y1⟩
          | false => ⟨y0, y1, sNeg bx.x1, sNeg bx.x0⟩
      | false =>
        match Nat.beq r 2 with
          | true => ⟨sNeg bx.x1, sNeg bx.x0, sNeg y1, sNeg y0⟩
          | false => ⟨sNeg y1, sNeg y0, bx.x0, bx.x1⟩ from rfl]
  set r := (sym / 2) % 4
  have hr_lt : r < 4 := Nat.mod_lt (sym / 2) (by omega)
  have hI3 : conj (Complex.I ^ 3) = Complex.I := by
    simp [show (3 : Nat) = 2 + 1 from rfl]
  interval_cases r <;>
    (simp only [pow_zero, pow_one, Complex.I_sq, hI3, map_one, map_neg, Complex.conj_I, Box2DS.Mem,
        sNeg_toInt, Int.cast_neg, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im]
     exact ⟨by linarith, by linarith, by linarith, by linarith⟩)

def cosetCircuit (idx : Nat) : Circuit 1 :=
  match idx with
  | 0 => .identity
  | 1 => gate1 .x
  | 2 => gate1 .h
  | 3 => gate1 .h ;;ᶜ gate1 .s
  | 4 => gate1 .h ;;ᶜ gate1 .z
  | _ => gate1 .h ;;ᶜ (gate1 .z ;;ᶜ gate1 .s)

theorem cosetCircuit_props (idx : Nat) : (CircExt.isOneQubitCircuit (cosetCircuit idx)) = true ∧
    (cosetCircuit idx).count PrimitiveGate.T = 0 ∧ (cosetCircuit idx).count PrimitiveGate.TOFF =
    0 := by
  match idx with
  | 0 | 1 | 2 | 3 | 4 | _ + 5 => exact ⟨rfl, rfl, rfl⟩

theorem cosetCircuit_eval (idx : Nat) :
    (cosetCircuit idx).eval.1 =
      match idx with
      | 0 => 1
      | 1 => !![(0 : ℂ), 1; 1, 0]
      | 2 => hadamard2
      | 3 => !![(1 : ℂ), 0; 0, Complex.I] * hadamard2
      | 4 => !![(1 : ℂ), 0; 0, -1] * hadamard2
      | _ => !![(1 : ℂ), 0; 0, -Complex.I] * hadamard2 := by
  have hh : (gate1 .h).eval.1 = hadamard2 := by
    rw [gate1_h_eval]; unfold hadamard2 invSqrtTwo
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [one_div]
  match idx with
  | 0 => rfl
  | 1 => exact gate1_x_eval
  | 2 => exact hh
  | 3 => simp [cosetCircuit, Circuit.eval_seq, gate1_s_eval, hh]
  | 4 => simp [cosetCircuit, Circuit.eval_seq, gate1_z_eval, hh]
  | n + 5 =>
    simp only [cosetCircuit, Circuit.eval_seq, Submonoid.coe_mul, gate1_z_eval, gate1_s_eval, hh];
        congr 1
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

set_option exponentiation.threshold 8192


attribute [local simp]
  sNeg_toInt sAdd_toInt sSub_toInt sMul_toInt sAbs_toInt sintMax_toInt sMin_toInt
  unbiasS_toInt fzNeg_toCyc fzMul_toCyc gate1_isOneQubit

/-! ### 1. Zero-Extra-`T` 1-Qubit Circuit Inversion (`invertCircuit1`) -/

def invertGate1 (g : PrimitiveGate 1) : Circuit 1 :=
  match g with
  | .x => gate1 .x
  | .y => gate1 .y
  | .z => gate1 .z
  | .h => gate1 .h
  | .s => gate1 .z ;;ᶜ gate1 .s
  | .t => gate1 .z ;;ᶜ (gate1 .s ;;ᶜ gate1 .t)

def invertCircuit1 : Circuit 1 → Circuit 1
  | .identity => .identity
  | .gate (k := 1) g _ => invertGate1 g
  | .gate (k := _) g r => .gate g r
  | .seq c1 c2 => .seq (invertCircuit1 c2) (invertCircuit1 c1)

theorem invertGate1_props (g : PrimitiveGate 1) (r : QRegister 1 1) :
    (CircExt.isOneQubitCircuit (invertGate1 g)) = true ∧ (invertGate1 g).count PrimitiveGate.T =
    (Circuit.gate g r).count PrimitiveGate.T ∧ (invertGate1 g).count PrimitiveGate.TOFF =
    (Circuit.gate g r).count PrimitiveGate.TOFF ∧ (invertGate1 g).eval.1 = (g.eval.1)ᴴ := by
  cases g <;>
    refine ⟨rfl, rfl, rfl, ?_⟩ <;>
      (ext i j : 1; fin_cases i <;> fin_cases j <;>
      (simp only [Nat.reducePow, invertGate1, Fin.zero_eta, Fin.isValue, gate1_x_eval, of_apply,
          cons_val', cons_val_zero, cons_val_fin_one, PrimitiveGate.eval, Qubit.X,
          conjTranspose_apply, star_zero, Fin.mk_one, cons_val_one, star_one, gate1_y_eval, Qubit.Y,
          RCLike.star_def, Complex.conj_I, star_neg, neg_neg, gate1_z_eval, Qubit.Z, gate1_h_eval,
          one_div, Qubit.H, sqrt_inv, smul_of, smul_cons, Complex.real_smul, Complex.ofReal_inv,
          mul_one, smul_empty, smul_neg, star_inv₀, Complex.conj_ofReal, eval_seq,
          Submonoid.coe_mul, gate1_s_eval, Matrix.mul_apply, Fin.sum_univ_two, mul_zero, add_zero,
          Qubit.S, mul_neg, neg_zero, zero_add, gate1_t_eval, CyclotomicEight.omegaComplex,
          cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, one_smul, tail_cons,
          zero_smul, empty_vecMul, smul_eq_mul, empty_mul, Equiv.symm_apply_apply, Qubit.T,
          star_div₀, star_add];
       try (ring_nf; simp [Complex.I_sq])))

theorem invertCircuit1_sound (c : Circuit 1) (hc : (CircExt.isOneQubitCircuit c) = true) :
    (CircExt.isOneQubitCircuit (invertCircuit1 c)) = true ∧
        (invertCircuit1 c).count PrimitiveGate.T =
    c.count PrimitiveGate.T ∧ (invertCircuit1 c).count PrimitiveGate.TOFF =
    c.count PrimitiveGate.TOFF ∧ (invertCircuit1 c).eval.1 = (c.eval.1)ᴴ := by
  induction c with
  | identity =>
    exact ⟨rfl, rfl, rfl, Matrix.ext fun i j ↦
        by fin_cases i <;> fin_cases j <;> simp [invertCircuit1]⟩
  | @gate k g r =>
    rcases k with _ | _ | _
    · cases hc
    · have hr : r = QRegister.whole 1 := by
        ext i; simp [Fin.eq_zero i]
      obtain ⟨h1, h2, h3, h4⟩ := invertGate1_props g r
      exact ⟨h1, h2, h3,
          by simpa [invertCircuit1, Circuit.eval_gate, hr, QRegister.whole_embedUnitary] using h4⟩
    · cases hc
  | seq c1 c2 ih1 ih2 =>
    simp only [CircExt.isOneQubitCircuit, Bool.and_eq_true] at hc
    obtain ⟨h1a, h1b, h1c, h1d⟩ := ih1 hc.1
    obtain ⟨h2a, h2b, h2c, h2d⟩ := ih2 hc.2
    exact ⟨by simp [invertCircuit1, CircExt.isOneQubitCircuit, h1a, h2a],
      by simpa [invertCircuit1, Circuit.count, Nat.add_comm] using congrArg₂ (· + ·) h2b h1b,
      by simpa [invertCircuit1, Circuit.count, Nat.add_comm] using congrArg₂ (· + ·) h2c h1c,
      by simp only [invertCircuit1, Circuit.eval_seq, Submonoid.coe_mul, h1d, h2d,
           Matrix.conjTranspose_mul]⟩


attribute [local irreducible]
  invertGate1 invertCircuit1
  gate1 phaseGate1 sylCircuit mid1Circuit mid4Circuit mid12Circuit decodeWord2Bit
  conjGate1
/-! ### 2. `2×2` Matrix Operator Norm Helpers -/

theorem opNorm_quat2_le (a : ℝ) (b : ℂ) :
    ‖(!![(a : ℂ), b; -conj b, (a : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ |a| + ‖b‖ := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![(a : ℂ), b; -conj b, (a : ℂ)]
  set s : ℝ := a ^ 2 + ‖b‖ ^ 2
  have hs_nn : 0 ≤ s := by positivity
  have hMHM : Mᴴ * M = (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp only [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Complex.star_def, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, ↓reduceIte,
          zero_ne_one, one_ne_zero, Complex.conj_ofReal, map_neg, Complex.conj_conj, mul_one,
          mul_zero]
    · rw [neg_mul_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [s, Complex.ofReal_add, Complex.ofReal_pow]; ring
    · ring
    · ring
    · rw [mul_comm (conj b) b, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [s, Complex.ofReal_add, Complex.ofReal_pow]; ring
  refine (sq_le_sq₀ (norm_nonneg M) (by positivity)).mp ?_
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self M, hMHM, norm_smul,
      Complex.norm_of_nonneg hs_nn]
  refine (mul_le_mul_of_nonneg_left (norm_le_one_of_mem_unitaryGroup (one_mem _)) hs_nn).trans ?_
  dsimp only [s]
  nlinarith [sq_abs a, mul_nonneg (abs_nonneg a) (norm_nonneg b)]

theorem su2_opNorm_sub_one_sq_eq {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsSu2 P) : ‖P - 1‖ ^ 2 = 2 *
    (1 - (P 0 0).re) := by
  apply le_antisymm (su2_opNorm_sub_one_sq_le hP); obtain ⟨_, _, hcol⟩ := su2_entries_of_isSu2 hP;
  have hc0 := col0_four_sq_le_opNorm_sq (P - 1)
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (one_ne_zero : (1 : Fin 2) ≠ 0), Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero] at hc0
  linarith [show ((P 0 0).re - 1) ^ 2 = (P 0 0).re ^ 2 - 2 * (P 0 0).re + 1 by ring, hcol]

def su2EtaMat (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt (1 + ‖z‖ ^ 2) : ℝ) : ℂ) • !![(1 : ℂ), z; -conj z, 1]

theorem su2EtaMat_isSu2 (z : ℂ) : IsSu2 (su2EtaMat z) := by
  set s : ℝ := 1 / Real.sqrt (1 + ‖z‖ ^ 2)
  have hsu_s : su2EtaMat z = (s : ℂ) • !![(1 : ℂ), z; -conj z, 1] := rfl
  have h1_pos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hs_sq : (s : ℂ) ^ 2 * (1 + (‖z‖ : ℂ) ^ 2) = 1 := by
    norm_cast; dsimp [s];
    rw [div_pow, one_pow, Real.sq_sqrt h1_pos.le, div_mul_cancel₀ _ h1_pos.ne']
  have hzc : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hcz : conj z * z = (‖z‖ : ℂ) ^ 2 := by rw [mul_comm, hzc]
  refine ⟨?_, ?_⟩
  · rw [mem_unitaryGroup_iff, hsu_s]; ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
          star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.star_def, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Matrix.one_apply_eq,
          Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, map_mul,
          Complex.conj_ofReal, map_one, map_neg, Complex.conj_conj]
    · linear_combination (s : ℂ) ^ 2 * hzc + hs_sq
    · ring
    · ring
    · linear_combination (s : ℂ) ^ 2 * hcz + hs_sq
  · rw [hsu_s, Matrix.det_smul, Fintype.card_fin, Matrix.det_fin_two];
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one];
    linear_combination (s : ℂ) ^ 2 * hzc + hs_sq
theorem su2EtaMat_mem (z : ℂ) : su2EtaMat z ∈ unitaryGroup (Fin 2) ℂ := (su2EtaMat_isSu2 z).1
theorem isSu2_conjTranspose_mul {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X)
    (hY : IsSu2 Y) : IsSu2 (Xᴴ * Y) := by
  refine ⟨Submonoid.mul_mem _ (by simpa only [← star_eq_conjTranspose] using Unitary.star_mem hX.1)
      hY.1, ?_⟩
  rw [Matrix.det_mul, Matrix.det_conjTranspose, hX.2, hY.2, star_one, one_mul]
theorem unitary_eq_su2EtaMat_mul_diag {W : Matrix (Fin 2) (Fin 2) ℂ}
    (hW : W ∈ unitaryGroup (Fin 2) ℂ) (h00 : W 0 0 ≠ 0) :
    ∃ d0 d1 : ℂ, ‖d0‖ = 1 ∧ ‖d1‖ = 1 ∧
      W = su2EtaMat (matEta W) * !![d0, 0; 0, d1] ∧
      d0 * d1 = W.det := by
  set w := matEta W
  set S := su2EtaMat w
  set sw : ℝ := 1 / Real.sqrt (1 + ‖w‖ ^ 2)
  have hS_eq : S = (sw : ℂ) • !![(1 : ℂ), w; -conj w, 1] := rfl
  have hS_su2 := su2EtaMat_isSu2 w
  set D := Sᴴ * W
  have hD_mem : D ∈ unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (by simpa only [← star_eq_conjTranspose] using Unitary.star_mem hS_su2.1) hW
  have hD10 : D 1 0 = 0 := by
    dsimp only [D]; rw [hS_eq];
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
        Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_mul, Complex.conj_ofReal, map_one]
    rw [show conj w = -(W 1 0 / W 0 0) by simp [w, matEta]]
    field_simp [h00]
    ring
  have hDhD : Dᴴ * D = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hD_mem
  have hd0_norm : ‖D 0 0‖ = 1 := by
    have h00_eq :=
        congrFun (congrFun hDhD 0) 0; simp only [Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.star_def, Matrix.one_apply_eq, hD10, map_zero, zero_mul,
        add_zero] at h00_eq; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h00_eq
    exact (sq_eq_sq₀ (norm_nonneg (D 0 0)) zero_le_one).mp
        (by linear_combination (by exact_mod_cast h00_eq : ‖D 0 0‖ ^ 2 = 1))
  have hd0_ne : conj (D 0 0) ≠ 0 := star_ne_zero.mpr fun h0 => by simp [h0] at hd0_norm
  have hD01 : D 0 1 = 0 := (mul_eq_zero.mp (by simpa [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, hD10] using congrFun (congrFun hDhD 0) 1)).resolve_left hd0_ne
  have hd1_norm : ‖D 1 1‖ = 1 := by
    have h11_eq :=
        congrFun (congrFun hDhD 1) 1;
            simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
            Complex.star_def, Matrix.one_apply_eq, hD01, map_zero, mul_zero, zero_add] at h11_eq;
            rw [mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq] at h11_eq
    exact (sq_eq_sq₀ (norm_nonneg (D 1 1)) zero_le_one).mp
        (by linear_combination (by exact_mod_cast h11_eq : ‖D 1 1‖ ^ 2 = 1))
  have hD_mat : D = !![D 0 0, 0; 0, D 1 1] := by
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [hD01, hD10]
  have hSSh : S * Sᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hS_su2.1
  have hW_eq : W = S * !![D 0 0, 0; 0, D 1 1] := by
    rw [← hD_mat]; dsimp [D]; rw [← Matrix.mul_assoc, hSSh, Matrix.one_mul]
  refine ⟨D 0 0, D 1 1, hd0_norm, hd1_norm, hW_eq, ?_⟩;
  rw [hW_eq, Matrix.det_mul, hS_su2.2, one_mul, Matrix.det_fin_two]; simp
theorem diag_unit_eq_exp_smul_phaseTurn {d0 d1 : ℂ} (hd0 : ‖d0‖ = 1) (hd1 : ‖d1‖ = 1) :
    ∃ γ g : ℝ,
      (!![d0, 0; 0, d1] : Matrix (Fin 2) (Fin 2) ℂ) =
        Complex.exp ((γ : ℂ) * Complex.I) • phaseTurn g := by
  let γ : ℝ := d0.arg
  let θ : ℝ := (d1 * conj d0).arg
  let g : ℝ := θ / (2 * Real.pi)
  have hd0_exp : Complex.exp ((γ : ℂ) * Complex.I) = d0 :=
    by simpa [hd0, γ] using Complex.norm_mul_exp_arg_mul_I d0
  have hd10_exp : Complex.exp ((θ : ℂ) * Complex.I) = d1 * conj d0 :=
    by simpa [hd0, hd1, θ] using Complex.norm_mul_exp_arg_mul_I (d1 * conj d0)
  refine ⟨γ, g, ?_⟩; rw [phaseTurn_eq]; ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, mul_one, mul_zero]
  · exact hd0_exp.symm
  · have hg_c : ((2 * Real.pi : ℝ) : ℂ) * (g : ℂ) = (θ : ℂ) := by
      exact_mod_cast mul_div_cancel₀ θ (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    have h2pi_g : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (g : ℂ) = (θ : ℂ) * Complex.I := by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hg_c
      linear_combination Complex.I * hg_c
    rw [h2pi_g, hd0_exp, hd10_exp]
    have hd0_c : d0 * conj d0 = 1 :=
      by simpa [Complex.normSq_eq_norm_sq, hd0] using Complex.mul_conj d0
    linear_combination -d1 * hd0_c

theorem mobius_conjTranspose_mul_eta {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ unitaryGroup (Fin 2) ℂ) (hB : B ∈ unitaryGroup (Fin 2) ℂ) (hA00 : A 0 0 ≠ 0)
    (hB00 : B 0 0 ≠ 0) (hdot : 0 < 1 + (matEta A).re * (matEta B).re + (matEta A).im *
    (matEta B).im) : (Aᴴ * B) 0 0 ≠ 0 ∧ ‖matEta (Aᴴ * B)‖ ^ 2 ≤
    (((matEta B).re - (matEta A).re) ^ 2 + ((matEta B).im - (matEta A).im) ^ 2) /
    (1 + (matEta A).re * (matEta B).re + (matEta A).im * (matEta B).im) ^ 2 := by
  set a := matEta A with ha_def
  set b := matEta B with hb_def
  obtain ⟨dA0, dA1, hdA0, hdA1, hA_eq, _⟩ := unitary_eq_su2EtaMat_mul_diag hA hA00
  obtain ⟨dB0, dB1, hdB0, hdB1, hB_eq, _⟩ := unitary_eq_su2EtaMat_mul_diag hB hB00
  set sa : ℝ := 1 / Real.sqrt (1 + ‖a‖ ^ 2)
  set sb : ℝ := 1 / Real.sqrt (1 + ‖b‖ ^ 2)
  have hprod : (Aᴴ * B) 0 0 = ((sa * sb : ℝ) : ℂ) * conj dA0 * dB0 * (1 + a * conj b) ∧
      (Aᴴ * B) 1 0 = ((sa * sb : ℝ) : ℂ) * conj dA1 * dB0 * (conj a - conj b) := by
    rw [hA_eq, hB_eq, ← ha_def, ← hb_def,
      show su2EtaMat a = (sa : ℂ) • Matrix.of ![![(1 : ℂ), a], ![-conj a, 1]] from rfl,
      show su2EtaMat b = (sb : ℂ) • Matrix.of ![![(1 : ℂ), b], ![-conj b, 1]] from rfl]
    constructor <;>
        simp only [Matrix.conjTranspose_mul, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.star_def, Matrix.smul_apply, smul_eq_mul,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_mul, map_mul,
        Complex.conj_ofReal, map_one, map_zero, map_neg, Complex.conj_conj] <;> ring
  obtain ⟨hprod00, hprod10⟩ := hprod
  have h1ab_re : (1 + a * conj b).re = 1 + a.re * b.re + a.im * b.im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have h1ab_ne : 1 + a * conj b ≠ 0 := by intro hz; rw [hz, Complex.zero_re] at h1ab_re; linarith
  have hsab_ne : ((sa * sb : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (div_pos one_pos (Real.sqrt_pos.mpr (by positivity)))
      (div_pos one_pos (Real.sqrt_pos.mpr (by positivity)))).ne'
  have hdA0_raw_ne : dA0 ≠ 0 := fun h0 => by simp [h0] at hdA0
  have hdA0_ne : conj dA0 ≠ 0 := star_ne_zero.mpr hdA0_raw_ne
  have hdB0_ne : dB0 ≠ 0 := fun h0 => by simp [h0] at hdB0
  refine ⟨ne_of_eq_of_ne hprod00 (mul_ne_zero (mul_ne_zero (mul_ne_zero hsab_ne hdA0_ne) hdB0_ne)
      h1ab_ne), ?_⟩
  have heta : matEta (Aᴴ * B) = -(dA1 / dA0) * ((a - b) / (1 + conj a * b)) := by
    unfold matEta
    rw [hprod10, hprod00]
    field_simp [hsab_ne, hdA0_ne, hdB0_ne, h1ab_ne]
    simp only [map_div₀, map_mul, map_sub, map_add, map_one, Complex.conj_conj]
    have h1cab_ne : 1 + conj a * b ≠ 0 := by simpa using star_ne_zero.mpr h1ab_ne
    field_simp [hdA0_raw_ne, h1cab_ne]
  rw [heta, norm_mul, norm_neg, norm_div, hdA1, hdA0, div_one, one_mul, norm_div, norm_sub_rev,
      div_pow,
    show ‖b - a‖ ^ 2 = (b.re - a.re) ^ 2 +
        (b.im -
        a.im) ^ 2
        by simpa [Complex.normSq_apply, sq] using (Complex.normSq_eq_norm_sq (b - a)).symm]
  refine div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hdot) ?_
  have h1cab_re : (1 + conj a * b).re = 1 + a.re * b.re + a.im * b.im := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h1cab_re]
  nlinarith [sq_nonneg (1 + conj a * b).im]

def d8Map (sym : Nat) (z : ℂ) : ℂ :=
    conj (Complex.I ^ ((sym / 2) % 4)) * (if sym % 2 = 1 then conj z else z)
theorem applyD8Circuit_eta (sym : Nat) (c : Circuit 1) (hc : (CircExt.isOneQubitCircuit c) = true)
    (_h00 : c.eval.1 0 0 ≠ 0) : matEta (applyD8Circuit sym c).eval.1 = d8Map sym (matEta c.eval.1)
    := by
  set c1 : Circuit 1 := if sym % 2 = 1 then conjCircuit c else c
  obtain ⟨_, _, _, hrMat, _⟩ := rotGate1_props (sym / 2)
  have hc1_eta : matEta c1.eval.1 = if sym % 2 =
      1 then conj (matEta c.eval.1) else matEta c.eval.1 := by
    rcases Nat.mod_two_eq_zero_or_one sym with h0 | h1
    · simp [c1, h0]
    · simp only [c1, h1, ↓reduceIte]; obtain ⟨_, _, _, hjEv⟩ := conjCircuit_sound c hc
      unfold matEta; rw [hjEv]; simp
  have hstep : matEta (applyD8Circuit sym c).eval.1 = conj (Complex.I ^ ((sym / 2) % 4)) *
      matEta c1.eval.1 := by
    have hev : (applyD8Circuit sym c).eval.1 = (rotGate1 (sym / 2)).eval.1 * c1.eval.1 := by
      simp [applyD8Circuit, c1, Circuit.eval_seq]
    rw [hev, hrMat]; unfold matEta;
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, one_mul, zero_mul, add_zero, zero_add];
        rw [mul_div_assoc, map_mul]; ring
  rw [hstep, hc1_eta]; rfl
theorem applyD8Circuit_basic (sym : Nat) (c : Circuit 1) (hc : (CircExt.isOneQubitCircuit c) = true)
    (h00 : c.eval.1 0 0 ≠ 0) : (CircExt.isOneQubitCircuit (applyD8Circuit sym c)) = true ∧
    (applyD8Circuit sym c).count PrimitiveGate.T = c.count PrimitiveGate.T ∧
    (applyD8Circuit sym c).count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF ∧
    (applyD8Circuit sym c).eval.1 0 0 ≠ 0 ∧ matEta (applyD8Circuit sym c).eval.1 =
    d8Map sym (matEta c.eval.1) := by
  have heta := applyD8Circuit_eta sym c hc h00; obtain ⟨hr1, hrT, hrToff, hrMat, _⟩ :=
      rotGate1_props (sym / 2); unfold applyD8Circuit
  rcases Nat.mod_two_eq_zero_or_one sym with hp | hp
  · simp only [hp]
    refine ⟨by simp [CircExt.isOneQubitCircuit, hc, hr1],
      by change c.count PrimitiveGate.T + (rotGate1 (sym / 2)).count PrimitiveGate.T =
           c.count PrimitiveGate.T; omega,
      by change c.count PrimitiveGate.TOFF + (rotGate1 (sym / 2)).count PrimitiveGate.TOFF =
           c.count PrimitiveGate.TOFF; omega,
      by simp [Circuit.eval_seq, hrMat, Matrix.mul_apply, Fin.sum_univ_two, h00],
      by simpa [applyD8Circuit, hp] using heta⟩
  · simp only [hp, ↓reduceIte]; obtain ⟨hj1, hjT, hjToff, hjEv⟩ := conjCircuit_sound c hc
    refine ⟨by simp [CircExt.isOneQubitCircuit, hj1, hr1],
      by change (conjCircuit c).count PrimitiveGate.T + (rotGate1 (sym / 2)).count PrimitiveGate.T =
           c.count PrimitiveGate.T; omega,
      by change (conjCircuit c).count PrimitiveGate.TOFF +
           (rotGate1 (sym / 2)).count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF; omega,
      by simp [Circuit.eval_seq, hrMat, hjEv, Matrix.mul_apply, Fin.sum_univ_two, h00],
      by simpa [applyD8Circuit, hp] using heta⟩

attribute [local irreducible] applyD8Circuit rotGate1 conjCircuit cosetCircuit

theorem d8Map_add (sym : Nat) (a b : ℂ) : d8Map sym (a + b) = d8Map sym a + d8Map sym b := by
  unfold d8Map
  split_ifs <;> simp [mul_add]

theorem d8Map_smul_real (sym : Nat) (r : ℝ) (a : ℂ) : d8Map sym ((r : ℂ) • a) =
    (r : ℂ) • d8Map sym a := by
  unfold d8Map
  split_ifs <;> simp [smul_eq_mul, Complex.conj_ofReal, mul_left_comm]

theorem d8Map_invariants (sym : Nat) (a b : ℂ) : ‖d8Map sym a‖ = ‖a‖ ∧ ‖d8Map sym a - d8Map sym b‖ =
    ‖a - b‖ ∧ (d8Map sym a).re * (d8Map sym b).re + (d8Map sym a).im * (d8Map sym b).im = a.re *
    b.re + a.im * b.im ∧ ‖(su2EtaMat (d8Map sym a))ᴴ * su2EtaMat (d8Map sym b) - 1‖ =
    ‖(su2EtaMat a)ᴴ * su2EtaMat b - 1‖ := by
  set r := (sym / 2) % 4
  set ζ : ℂ := conj (Complex.I ^ r)
  have hζ_norm : ‖ζ‖ = 1 := by simp [ζ]
  have hζc : ζ * conj ζ = 1 := by
    simpa [Complex.normSq_eq_norm_sq, hζ_norm] using Complex.mul_conj ζ
  have h1 (z : ℂ) : ‖d8Map sym z‖ = ‖z‖ := by
    rw [show d8Map sym z = ζ * (if sym % 2 = 1 then conj z else z) from rfl, norm_mul, hζ_norm,
        one_mul]
    split_ifs <;> simp
  have h2 : ‖d8Map sym a - d8Map sym b‖ = ‖a - b‖ := by
    rw [show d8Map sym a - d8Map sym b = ζ * ((if sym % 2 = 1 then conj a else a) -
      (if sym % 2 = 1 then conj b else b)) by simp only [d8Map, ζ, r, mul_sub], norm_mul, hζ_norm,
          one_mul]
    split_ifs <;> simp [← map_sub]
  have h3 : (d8Map sym a).re * (d8Map sym b).re + (d8Map sym a).im * (d8Map sym b).im = a.re *
      b.re + a.im * b.im := by
    have hre_prod (u v : ℂ) : u.re * v.re + u.im * v.im = (u * conj v).re := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [hre_prod, hre_prod, show d8Map sym a = ζ * (if sym % 2 = 1 then conj a else a) from rfl,
      show d8Map sym b = ζ * (if sym % 2 = 1 then conj b else b) from rfl, map_mul,
      show (ζ * (if sym % 2 = 1 then conj a else a)) *
          (conj ζ * conj (if sym % 2 = 1 then conj b else b)) =
        (ζ * conj ζ) * ((if sym % 2 = 1 then conj a else a) * conj (if sym % 2 =
            1 then conj b else b)) by ring,
      hζc, one_mul]
    split_ifs <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  refine ⟨h1 a, h2, h3, (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_⟩
  have hP1 :=
      isSu2_conjTranspose_mul (su2EtaMat_isSu2 (d8Map sym a)) (su2EtaMat_isSu2 (d8Map sym b))
  have hP2 := isSu2_conjTranspose_mul (su2EtaMat_isSu2 a) (su2EtaMat_isSu2 b)
  have hre00 : ((su2EtaMat (d8Map sym a))ᴴ * su2EtaMat (d8Map sym b)) 0 0 =
      if sym % 2 = 1 then conj (((su2EtaMat a)ᴴ * su2EtaMat b) 0 0) else ((su2EtaMat a)ᴴ *
          su2EtaMat b) 0 0 := by
    have hsu_eq (z : ℂ) : su2EtaMat z =
        ((1 / Real.sqrt (1 + ‖z‖ ^ 2) : ℝ) : ℂ) • Matrix.of ![![(1 : ℂ), z], ![-conj z, 1]] := rfl
    have h00_uv (s₁ s₂ : ℝ) (u v : ℂ) :
        (((s₁ : ℂ) • Matrix.of ![![(1 : ℂ), u], ![-conj u, 1]])ᴴ *
          ((s₂ : ℂ) • Matrix.of ![![(1 : ℂ), v], ![-conj v, 1]])) 0 0 =
          (s₁ : ℂ) * (s₂ : ℂ) * (1 + u * conj v) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
          Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, map_mul, Complex.conj_ofReal, map_one, map_neg, Complex.conj_conj]
      ring
    rw [hsu_eq (d8Map sym a), hsu_eq (d8Map sym b), h1 a, h1 b, hsu_eq a, hsu_eq b, h00_uv, h00_uv]
    set sa : ℝ := 1 / Real.sqrt (1 + ‖a‖ ^ 2)
    set sb : ℝ := 1 / Real.sqrt (1 + ‖b‖ ^ 2)
    rcases Nat.mod_two_eq_zero_or_one sym with hp0 | hp1
    · rw [show d8Map sym a = ζ * a by simp [d8Map, hp0, ζ, r], show d8Map sym b = ζ *
          b by simp [d8Map, hp0, ζ, r],
        ite_eq_right (by omega), map_mul]
      linear_combination (sa : ℂ) * (sb : ℂ) * (a * conj b) * hζc
    · rw [show d8Map sym a = ζ * conj a by simp [d8Map, hp1, ζ, r],
        show d8Map sym b = ζ * conj b by simp [d8Map, hp1, ζ, r], ite_eq_left hp1]
      simp only [map_mul, map_add, map_one, Complex.conj_ofReal, Complex.conj_conj]
      linear_combination (sa : ℂ) * (sb : ℂ) * (conj a * b) * hζc
  rw [su2_opNorm_sub_one_sq_eq hP1, su2_opNorm_sub_one_sq_eq hP2, hre00]
  split_ifs <;> simp

theorem exists_foldD8 (z : ℂ) :
    ∃ (sym : Nat) (zw : ℂ),
      sym < 8 ∧ 0 ≤ zw.im ∧ zw.im ≤ zw.re ∧ zw.re ≤ max |z.re| |z.im| ∧ d8Map sym zw = z := by
  have hm_re := le_max_left |z.re| |z.im|
  have hm_im := le_max_right |z.re| |z.im|
  have hle_re := le_abs_self z.re
  have hneg_re := neg_le_abs z.re
  have hle_im := le_abs_self z.im
  have hneg_im := neg_le_abs z.im
  have hquad : ∃ (r : Nat) (z1 : ℂ), r < 4 ∧ 0 ≤ z1.re ∧ 0 ≤ z1.im ∧
      z1.re ≤ max |z.re| |z.im| ∧ z1.im ≤ max |z.re| |z.im| ∧ conj (Complex.I ^ r) * z1 = z := by
    by_cases hx : 0 ≤ z.re <;> by_cases hy : 0 ≤ z.im
    · exact ⟨0, z, by omega, hx, hy, by linarith, by linarith, by simp⟩
    · refine ⟨1, Complex.I * z, by omega, ?_, ?_, ?_, ?_, by simp [← mul_assoc]⟩ <;>
          simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          zero_sub, zero_add] <;> linarith
    · have hc3 : conj (Complex.I ^ 3) * ((-Complex.I) * z) = z := by
        rw [show (3 : Nat) = 2 + 1 from rfl, pow_add, pow_one, Complex.I_sq]
        simp [← mul_assoc]
      refine ⟨3, (-Complex.I) * z, by omega, ?_, ?_, ?_, ?_, hc3⟩ <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
            Complex.I_im, zero_mul, neg_zero, neg_one_mul, sub_neg_eq_add, zero_add] <;>
        linarith
    · refine ⟨2, -z, by omega, ?_, ?_, ?_, ?_, by simp⟩ <;> simp only [Complex.neg_re,
          Complex.neg_im] <;> linarith
  obtain ⟨r, z1, hr, hx1, hy1, hbx1, hby1, hz1⟩ := hquad
  by_cases hle : z1.im ≤ z1.re
  · exact ⟨2 * r, z1, by omega, hy1, hle, hbx1, by
      simp only [d8Map, show (2 * r) % 2 = 0 by omega,
        show ((2 * r) / 2) % 4 = r by omega, zero_ne_one, ↓reduceIte, hz1]⟩
  · let zw : ℂ := ⟨z1.im, z1.re⟩
    let r' : Nat := (r + 3) % 4
    refine ⟨2 * r' + 1, zw, by omega, hx1, show zw.im ≤ zw.re by dsimp [zw]; linarith, hby1, ?_⟩
    simp only [d8Map, show (2 * r' + 1) % 2 = 1 by omega, show ((2 * r' + 1) / 2) % 4 = r' by omega,
      ↓reduceIte, show conj zw = (-Complex.I) * z1 by apply Complex.ext <;> simp [zw]]
    exact (show conj (Complex.I ^ r') * ((-Complex.I) * z1) = conj (Complex.I ^ r) * z1 by
      dsimp [r']; interval_cases r <;> (apply Complex.ext <;> simp [pow_succ, pow_zero])).trans hz1

theorem interval_abs_diff_le {x0 x1 w0 w1 z w : ℝ} (hz0 : x0 ≤ z) (hz1 : z ≤ x1) (hw0 : w0 ≤ w)
    (hw1 : w ≤ w1) : |z - w| ≤ max |x0 - w1| |x1 - w0| :=
  abs_le.mpr ⟨by linarith [neg_le_abs (x0 - w1), le_max_left |x0 - w1| |x1 - w0|],
    by linarith [le_abs_self (x1 - w0), le_max_right |x0 - w1| |x1 - w0|]⟩

theorem interval_prod_ge_min4 {x0 x1 w0 w1 z w : ℝ} (hz0 : x0 ≤ z) (hz1 : z ≤ x1) (hw0 : w0 ≤ w)
    (hw1 : w ≤ w1) : min (x0 * w0) (min (x0 * w1) (min (x1 * w0) (x1 * w1))) ≤ z * w := by
  have hl0 : min (x0 * w0) (x1 * w0) ≤ z * w0 :=
      if hw : 0 ≤
      w0 then (min_le_left _ _).trans (by nlinarith) else (min_le_right _ _).trans (by nlinarith)
  have hl1 : min (x0 * w1) (x1 * w1) ≤ z * w1 :=
      if hw : 0 ≤
      w1 then (min_le_left _ _).trans (by nlinarith) else (min_le_right _ _).trans (by nlinarith)
  have hmz : min (z * w0) (z * w1) ≤ z * w :=
      if hz : 0 ≤
      z then (min_le_left _ _).trans (by nlinarith) else (min_le_right _ _).trans (by nlinarith)
  set m := min (x0 * w0) (min (x0 * w1) (min (x1 * w0) (x1 * w1)))
  exact (le_min ((le_min (min_le_left _ _)
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans hl0)
    ((le_min ((min_le_right _ _).trans (min_le_left _ _))
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).trans hl1)).trans
        hmz
theorem interval_prod_le_max4 {x0 x1 w0 w1 z w : ℝ} (hz0 : x0 ≤ z) (hz1 : z ≤ x1) (hw0 : w0 ≤ w)
    (hw1 : w ≤ w1) : z * w ≤ max (x0 * w0) (max (x0 * w1) (max (x1 * w0) (x1 * w1))) := by
  have hu0 : z * w0 ≤ max (x0 * w0) (x1 * w0) :=
      if hw : 0 ≤
      w0 then (by nlinarith : z * w0 ≤ x1 * w0).trans (le_max_right _ _) else
      (by nlinarith : z * w0 ≤ x0 * w0).trans (le_max_left _ _)
  have hu1 : z * w1 ≤ max (x0 * w1) (x1 * w1) :=
      if hw : 0 ≤
      w1 then (by nlinarith : z * w1 ≤ x1 * w1).trans (le_max_right _ _) else
      (by nlinarith : z * w1 ≤ x0 * w1).trans (le_max_left _ _)
  have hMz : z * w ≤ max (z * w0) (z * w1) :=
      if hz : 0 ≤
      z then (by nlinarith : z * w ≤ z * w1).trans (le_max_right _ _) else
      (by nlinarith : z * w ≤ z * w0).trans (le_max_left _ _)
  set M := max (x0 * w0) (max (x0 * w1) (max (x1 * w0) (x1 * w1)))
  exact hMz.trans (max_le (hu0.trans (max_le (le_max_left _ _)
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))))
    (hu1.trans (max_le ((le_max_left _ _).trans (le_max_right _ _))
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)))))

theorem interval_abs_le_max_abs {x0 x1 z : ℝ} (hz0 : x0 ≤ z) (hz1 : z ≤ x1) :
    |z| ≤ max |x0| |x1| :=
  abs_le.mpr ⟨by linarith [neg_abs_le x0, le_max_left |x0| |x1|],
    by linarith [le_abs_self x1, le_max_right |x0| |x1|]⟩

set_option maxHeartbeats 1600000 in
-- Nonlinear interval/Lagrange SU(2) norm arithmetic needs raised heartbeats.
theorem checkLagrangeBox_sound {a b : Box2DS} {capNum capDen : Nat} {za zb : ℂ}
    (hchk : checkLagrangeBox a b capNum capDen = true) (hden : 0 < capDen) (ha : a.Mem za)
    (hb : b.Mem zb) : ‖zb - za‖ ≤ (capNum : ℝ) / (capDen : ℝ) ∧ ‖(su2EtaMat za)ᴴ * su2EtaMat zb -
    1‖ ≤ (capNum : ℝ) / (capDen : ℝ) := by
  simp only [checkLagrangeBox, Bool.and_eq_true] at hchk
  obtain ⟨hdot_pos, hle_s⟩ := hchk
  set BS : ℝ := 2 ^ 52
  have hBS_pos : 0 < BS := by positivity
  have hbs_int : (boxScaleS.toInt : ℝ) = BS := by norm_num [boxScaleS, SInt.toInt, BS]
  rcases ha with ⟨hax0, hax1, hay0, hay1⟩
  rcases hb with ⟨hbx0, hbx1, hby0, hby1⟩
  have lo {s : SInt} {r : ℝ} (h : (s.toInt : ℝ) / BS ≤ r) : (s.toInt : ℝ) ≤ BS * r :=
    (div_le_iff₀' hBS_pos).mp h
  have hi {s : SInt} {r : ℝ} (h : r ≤ (s.toInt : ℝ) / BS) : BS * r ≤ (s.toInt : ℝ) :=
    (le_div_iff₀' hBS_pos).mp h
  set dxMax := sintMax (sAbs (sSub a.x0 b.x1)) (sAbs (sSub a.x1 b.x0))
  set dyMax := sintMax (sAbs (sSub a.y0 b.y1)) (sAbs (sSub a.y1 b.y0))
  set axAbs := sintMax (sAbs a.x0) (sAbs a.x1)
  set ayAbs := sintMax (sAbs a.y0) (sAbs a.y1)
  set bxAbs := sintMax (sAbs b.x0) (sAbs b.x1)
  set byAbs := sintMax (sAbs b.y0) (sAbs b.y1)
  set imUb := sAdd (sMul ayAbs bxAbs) (sMul axAbs byAbs)
  set bsSq := sMul boxScaleS boxScaleS
  set dotLo := sSub (sSub bsSq (sMul axAbs bxAbs)) (sMul ayAbs byAbs)
  set distSq := sAdd (sMul dxMax dxMax) (sMul dyMax dyMax)
  set num := sAdd (sMul distSq bsSq) (sMul imUb imUb)
  have hdx : |BS * (za.re - zb.re)| ≤ (dxMax.toInt : ℝ) := by
    simpa [mul_sub, dxMax] using interval_abs_diff_le (lo hax0) (hi hax1) (lo hbx0) (hi hbx1)
  have hdy : |BS * (za.im - zb.im)| ≤ (dyMax.toInt : ℝ) := by
    simpa [mul_sub, dyMax] using interval_abs_diff_le (lo hay0) (hi hay1) (lo hby0) (hi hby1)
  have hax_abs : |BS * za.re| ≤ (axAbs.toInt : ℝ) :=
      (interval_abs_le_max_abs (lo hax0) (hi hax1)).trans (by simp [axAbs])
  have hay_abs : |BS * za.im| ≤ (ayAbs.toInt : ℝ) :=
      (interval_abs_le_max_abs (lo hay0) (hi hay1)).trans (by simp [ayAbs])
  have hbx_abs : |BS * zb.re| ≤ (bxAbs.toInt : ℝ) :=
      (interval_abs_le_max_abs (lo hbx0) (hi hbx1)).trans (by simp [bxAbs])
  have hby_abs : |BS * zb.im| ≤ (byAbs.toInt : ℝ) :=
      (interval_abs_le_max_abs (lo hby0) (hi hby1)).trans (by simp [byAbs])
  have him_le : |BS ^ 2 * (za.im * zb.re - za.re * zb.im)| ≤ (imUb.toInt : ℝ) := by
    rw [show BS ^ 2 * (za.im * zb.re - za.re * zb.im) = (BS * za.im) *
        (BS * zb.re) + -((BS * za.re) * (BS * zb.im)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul]
    simpa [imUb] using add_le_add (mul_le_mul hay_abs hbx_abs (abs_nonneg _)
        ((abs_nonneg _).trans hay_abs))
      (mul_le_mul hax_abs hby_abs (abs_nonneg _) ((abs_nonneg _).trans hax_abs))
  have hdot_le : (dotLo.toInt : ℝ) ≤ BS ^ 2 * (1 + za.re * zb.re + za.im * zb.im) ∧
      (dotLo.toInt : ℝ) ≤ BS ^ 2 := by
    have hd_eq : (dotLo.toInt : ℝ) = BS ^ 2 - (axAbs.toInt : ℝ) * bxAbs.toInt -
        (ayAbs.toInt : ℝ) * byAbs.toInt := by simp [dotLo, bsSq, hbs_int, sq]
    have hp1 : |(BS * za.re) * (BS * zb.re)| ≤ (axAbs.toInt : ℝ) * bxAbs.toInt := by
      rw [abs_mul];
      exact mul_le_mul hax_abs hbx_abs (abs_nonneg _) (le_trans (abs_nonneg _) hax_abs)
    have hp2 : |(BS * za.im) * (BS * zb.im)| ≤ (ayAbs.toInt : ℝ) * byAbs.toInt := by
      rw [abs_mul];
      exact mul_le_mul hay_abs hby_abs (abs_nonneg _) (le_trans (abs_nonneg _) hay_abs)
    have hn1 := neg_abs_le ((BS * za.re) * (BS * zb.re));
    have hn2 := neg_abs_le ((BS * za.im) * (BS * zb.im));
    have hnn1 : 0 ≤ (axAbs.toInt : ℝ) * bxAbs.toInt := le_trans (abs_nonneg _) hp1;
    have hnn2 : 0 ≤ (ayAbs.toInt : ℝ) * byAbs.toInt := le_trans (abs_nonneg _) hp2; rw [hd_eq]
    exact ⟨by nlinarith, by linarith⟩
  have hdot_int_pos : 0 < (dotLo.toInt : ℝ) := by exact_mod_cast (sPos_iff dotLo).mp hdot_pos
  have h1dot_pos : 0 < 1 + za.re * zb.re + za.im * zb.im :=
    pos_of_mul_pos_right (lt_of_lt_of_le hdot_int_pos hdot_le.1) (by positivity)
  have hle_r : ((distSq.toInt : ℝ) * BS ^ 2 + (imUb.toInt : ℝ) ^ 2) * (capDen : ℝ) ^ 2 ≤
      (capNum : ℝ) ^ 2 * (dotLo.toInt : ℝ) ^ 2 := by
    have hz :=
        (sLe_iff _ _).mp hle_s; dsimp only [num] at hz; simp only [sMul_toInt, sAdd_toInt] at hz
    have hzr : ((((distSq.toInt * bsSq.toInt + imUb.toInt * imUb.toInt) *
        (⟨false, Nat.mul capDen capDen⟩ : SInt).toInt) : ℤ) : ℝ) ≤
        ((((⟨false, Nat.mul capNum capNum⟩ : SInt).toInt * (dotLo.toInt * dotLo.toInt)) : ℤ) : ℝ)
        := by exact_mod_cast hz
    have hs1 : ((⟨false, Nat.mul capDen capDen⟩ : SInt).toInt : ℝ) = (capDen : ℝ) ^ 2 := by
      simp [SInt.toInt, Nat.mul_eq, sq]
    have hs2 : ((⟨false, Nat.mul capNum capNum⟩ : SInt).toInt : ℝ) = (capNum : ℝ) ^ 2 := by
      simp [SInt.toInt, Nat.mul_eq, sq]
    have hbs2 : (bsSq.toInt : ℝ) = BS ^ 2 := by simp [bsSq, sMul_toInt, hbs_int, sq]
    push_cast at hzr; rw [hs1, hs2, hbs2, ← sq (imUb.toInt : ℝ), ← sq (dotLo.toInt : ℝ)] at hzr;
    exact hzr
  have hdist_le : BS ^ 2 * ‖zb - za‖ ^ 2 ≤ (distSq.toInt : ℝ) := by
    have hnorm : ‖zb - za‖ ^ 2 = (za.re - zb.re) ^ 2 + (za.im - zb.im) ^ 2 := by
      rw [norm_sub_rev, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have h1 : (BS * (za.re - zb.re)) ^ 2 ≤ (dxMax.toInt : ℝ) ^ 2 := by
      rw [← sq_abs (BS * (za.re - zb.re))];
      exact (sq_le_sq₀ (abs_nonneg _) (le_trans (abs_nonneg _) hdx)).mpr hdx
    have h2 : (BS * (za.im - zb.im)) ^ 2 ≤ (dyMax.toInt : ℝ) ^ 2 := by
      rw [← sq_abs (BS * (za.im - zb.im))];
      exact (sq_le_sq₀ (abs_nonneg _) (le_trans (abs_nonneg _) hdy)).mpr hdy
    have hd_eq : (distSq.toInt : ℝ) = (dxMax.toInt : ℝ) ^ 2 + (dyMax.toInt : ℝ) ^ 2 := by
      simp [distSq, sq]
    rw [hnorm, hd_eq]; nlinarith
  have him_sq_le : BS ^ 4 * (za.im * zb.re - za.re * zb.im) ^ 2 ≤ (imUb.toInt : ℝ) ^ 2 := by
    have h1 : (BS ^ 2 * (za.im * zb.re - za.re * zb.im)) ^ 2 ≤ (imUb.toInt : ℝ) ^ 2 := by
      rw [← sq_abs (BS ^ 2 * (za.im * zb.re - za.re * zb.im))];
      exact (sq_le_sq₀ (abs_nonneg _) (le_trans (abs_nonneg _) him_le)).mpr him_le
    nlinarith
  have hden_r_pos : 0 < (capDen : ℝ) := by exact_mod_cast hden
  -- 1. Direct Euclidean chord bound: ‖zb - za‖ ≤ capNum / capDen
  have heucl_sq : ‖zb - za‖ ^ 2 ≤ ((capNum : ℝ) / (capDen : ℝ)) ^ 2 := by
    have hdot_bs : (dotLo.toInt : ℝ) ^ 2 ≤ BS ^ 4 := by
      have := mul_self_le_mul_self hdot_int_pos.le hdot_le.2; nlinarith
    have h1 : BS ^ 4 * (‖zb - za‖ ^ 2 * (capDen : ℝ) ^ 2) ≤ BS ^ 4 * (capNum : ℝ) ^ 2 := by
      nlinarith [hle_r, hdist_le, sq_nonneg (imUb.toInt : ℝ), hdot_bs]
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hden_r_pos)]
    exact le_of_mul_le_mul_left h1 (by positivity)
  -- 2. SU(2) Lagrange operator norm bound: ‖(su2EtaMat za)ᴴ * su2EtaMat zb - 1‖ ≤ capNum / capDen
  set Q := (su2EtaMat za)ᴴ * su2EtaMat zb
  have hQ_su2 : IsSu2 Q := isSu2_conjTranspose_mul (su2EtaMat_isSu2 za) (su2EtaMat_isSu2 zb)
  obtain ⟨_, _, hQ_col⟩ := su2_entries_of_isSu2 hQ_su2
  set sa : ℝ := 1 / Real.sqrt (1 + ‖za‖ ^ 2)
  set sb : ℝ := 1 / Real.sqrt (1 + ‖zb‖ ^ 2)
  set sAB : ℝ := sa * sb
  have hsAB_pos : 0 < sAB := by dsimp [sAB, sa, sb]; positivity
  have hsuA_eq : su2EtaMat za = (sa : ℂ) • !![(1 : ℂ), za; -conj za, 1] := rfl
  have hsuB_eq : su2EtaMat zb = (sb : ℂ) • !![(1 : ℂ), zb; -conj zb, 1] := rfl
  have hQ00 : Q 0 0 = (sAB : ℂ) * (1 + za * conj zb) := by
    change ((su2EtaMat za)ᴴ * su2EtaMat zb) 0 0 = _; rw [hsuA_eq, hsuB_eq]; dsimp only [sAB];
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
        Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.ofReal_mul, map_mul, Complex.conj_ofReal, map_one, map_neg, Complex.conj_conj]; ring
  have hQ10 : Q 1 0 = (sAB : ℂ) * (conj za - conj zb) := by
    change ((su2EtaMat za)ᴴ * su2EtaMat zb) 1 0 = _; rw [hsuA_eq, hsuB_eq]; dsimp only [sAB];
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
        Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Complex.ofReal_mul, map_mul, Complex.conj_ofReal, map_one]; ring
  set u := (Q 0 0).re
  set v := (Q 0 0).im
  have hu_eq : u = sAB * (1 + za.re * zb.re + za.im * zb.im) := by
    change (Q 0 0).re = _; rw [hQ00];
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]; ring
  have hv_eq : v = sAB * (za.im * zb.re - za.re * zb.im) := by
    change (Q 0 0).im = _; rw [hQ00];
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]; ring
  have hw_sq : ‖Q 1 0‖ ^ 2 = sAB ^ 2 * ‖zb - za‖ ^ 2 := by
    rw [hQ10, norm_mul, Complex.norm_of_nonneg hsAB_pos.le, mul_pow, ← map_sub, Complex.norm_conj,
        norm_sub_rev]
  have hu_pos : 0 < u := by rw [hu_eq]; exact mul_pos hsAB_pos h1dot_pos
  have hunit : u ^ 2 + v ^ 2 + ‖Q 1 0‖ ^ 2 = 1 := by
    have h10_sq : ‖Q 1 0‖ ^ 2 = (Q 1 0).re ^ 2 + (Q 1 0).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    dsimp only [u, v]; linarith [hQ_col, h10_sq]
  have hu_le1 : u ≤ 1 := by nlinarith [sq_nonneg v, sq_nonneg ‖Q 1 0‖]
  have hQ_sq : ‖Q - 1‖ ^ 2 ≤ ((capNum : ℝ) / (capDen : ℝ)) ^ 2 := by
    have hsu_le := su2_opNorm_sub_one_sq_le hQ_su2
    -- 2 * (1 - u) * u^2 = (1 - u) * 2 * u^2 <= (1 - u) * (1 + u) = 1 - u^2 = v^2 + ‖Q 1 0‖^2
    have hlag : 2 * (1 - u) * u ^ 2 ≤ v ^ 2 + ‖Q 1 0‖ ^ 2 := by
      linarith [mul_nonneg (show 0 ≤ 1 - u by linarith) (show 0 ≤ (1 + u) - 2 * u ^ 2 by nlinarith)]
    have hlag_cancel : 2 * (1 - u) * (1 + za.re * zb.re + za.im * zb.im) ^ 2 ≤ ‖zb - za‖ ^ 2 +
        (za.im * zb.re - za.re * zb.im) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ (sq_pos_of_pos hsAB_pos)
      calc sAB ^ 2 * (2 * (1 - u) * (1 + za.re * zb.re + za.im * zb.im) ^ 2)
          = 2 * (1 - u) * u ^ 2 := by
            rw [hu_eq]
            ring
        _ ≤ v ^ 2 + ‖Q 1 0‖ ^ 2 := hlag
        _ = sAB ^ 2 * (‖zb - za‖ ^ 2 + (za.im * zb.re - za.re * zb.im) ^ 2) := by
            rw [hv_eq, hw_sq]
            ring
    have hdot_sq_le : (dotLo.toInt : ℝ) ^ 2 ≤ BS ^ 4 * (1 + za.re * zb.re + za.im * zb.im) ^ 2 := by
      have := mul_self_le_mul_self hdot_int_pos.le hdot_le.1; nlinarith
    have hscaled : BS ^ 4 * ((‖zb - za‖ ^ 2 + (za.im * zb.re - za.re * zb.im) ^ 2) *
        (capDen : ℝ) ^ 2) ≤ BS ^ 4 * ((capNum : ℝ) ^ 2 * (1 + za.re * zb.re + za.im * zb.im) ^ 2)
        := by nlinarith [hle_r, hdist_le, him_sq_le, hdot_sq_le]
    have hscaled' := le_of_mul_le_mul_left hscaled (show 0 < BS ^ 4 by positivity)
    have hcomb : (‖Q - 1‖ ^ 2 * (capDen : ℝ) ^ 2) * (1 + za.re * zb.re + za.im * zb.im) ^ 2 ≤
        (capNum : ℝ) ^ 2 * (1 + za.re * zb.re + za.im * zb.im) ^ 2 := by
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsu_le (by positivity))
          (by positivity)).trans ?_
      rw [show (2 * (1 - u) * (capDen : ℝ) ^ 2) * (1 + za.re * zb.re + za.im * zb.im) ^ 2 =
          (2 * (1 - u) * (1 + za.re * zb.re + za.im * zb.im) ^ 2) * (capDen : ℝ) ^ 2 by ring]
      exact (mul_le_mul_of_nonneg_right hlag_cancel (by positivity)).trans hscaled'
    have hcomb' :=
        le_of_mul_le_mul_right hcomb (sq_pos_of_pos h1dot_pos); rw [div_pow,
        le_div_iff₀ (sq_pos_of_pos hden_r_pos)]; exact hcomb'
  exact ⟨(sq_le_sq₀ (norm_nonneg _) (by positivity)).mp heucl_sq, (sq_le_sq₀ (norm_nonneg _)
      (by positivity)).mp hQ_sq⟩

/-! ### 4. Stage 0 Coset Reduction, 4-Stage Simplicial Cancellation, & `exists_simplicial_step` -/

theorem unitary_bloch_sphere {V0 : Matrix (Fin 2) (Fin 2) ℂ} (hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ) :
    ‖V0 0 0‖ ^ 2 + ‖V0 1 0‖ ^ 2 = 1 ∧
    (2 * (conj (V0 0 0) * V0 1 0).re) ^ 2 + (2 * (conj (V0 0 0) * V0 1 0).im) ^ 2 + (‖V0 0 0‖ ^ 2 -
        ‖V0 1 0‖ ^ 2) ^ 2 = 1 := by
  have h00 :=
      congrFun (congrFun (star_eq_conjTranspose V0 ▸ Unitary.star_mul_self_of_mem hV0 : V0ᴴ * V0 =
      1) 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def,
      Matrix.one_apply_eq] at h00
  rw [mul_comm (conj (V0 0 0)), mul_comm (conj (V0 1 0)), Complex.mul_conj, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h00
  have hcol : ‖V0 0 0‖ ^ 2 + ‖V0 1 0‖ ^ 2 = 1 := by exact_mod_cast h00
  have hp := Complex.normSq_apply (conj (V0 0 0) * V0 1 0)
  rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj, mul_pow] at hp
  exact ⟨hcol, by nlinarith [hcol, hp]⟩

theorem matEta_bloch_identities {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hpos : 0 < ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2) :
    M 0 0 ≠ 0 ∧ 0 < ‖M 0 0‖ ^ 2 ∧
    |(conj (M 0 0) * M 1 0).re| = ‖M 0 0‖ ^ 2 * |(matEta M).re| ∧
    |(conj (M 0 0) * M 1 0).im| = ‖M 0 0‖ ^ 2 * |(matEta M).im| ∧
    ‖M 1 0‖ ^ 2 = ‖M 0 0‖ ^ 2 * ‖matEta M‖ ^ 2 := by
  have hu_pos : 0 < ‖M 0 0‖ ^ 2 := by nlinarith [sq_nonneg ‖M 1 0‖]
  have hu_ne : M 0 0 ≠ 0 := fun hz => by simp [hz] at hu_pos
  set z := matEta M
  have hv_eq : M 1 0 = -conj z * M 0 0 := by
    rw [show conj z = -(M 1 0 / M 0 0) by simp [z, matEta]]
    field_simp [hu_ne]
  have hprod : conj (M 0 0) * M 1 0 = -((‖M 0 0‖ ^ 2 : ℝ) : ℂ) * conj z := by
    rw [hv_eq, show conj (M 0 0) * (-conj z * M 0 0) = -(M 0 0 * conj (M 0 0)) * conj z by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨hu_ne, hu_pos, ?_, ?_, by
    rw [hv_eq, norm_mul, norm_neg, Complex.norm_conj, mul_pow]
    ring⟩
  · rw [hprod, show (-((‖M 0 0‖ ^ 2 : ℝ) : ℂ) * conj z).re = -(‖M 0 0‖ ^ 2 *
        z.re) by rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, Complex.conj_re], abs_neg,
        abs_mul, abs_of_pos hu_pos]
  · rw [hprod, show (-((‖M 0 0‖ ^ 2 : ℝ) : ℂ) * conj z).im = ‖M 0 0‖ ^ 2 *
        z.im by rw [neg_mul, Complex.neg_im, Complex.im_ofReal_mul, Complex.conj_im, mul_neg,
                  neg_neg], abs_mul, abs_of_pos hu_pos]

theorem had_pair_bloch (u w : ℂ) :
    let c2 : ℝ := 1 / Real.sqrt 2
    ‖(c2 : ℂ) * (u + w)‖ ^ 2 - ‖(c2 : ℂ) * (u - w)‖ ^ 2 = 2 * (conj u * w).re ∧
    2 * |(conj ((c2 : ℂ) * (u + w)) * ((c2 : ℂ) * (u - w))).re| = |‖u‖ ^ 2 - ‖w‖ ^ 2| ∧
    2 * |(conj ((c2 : ℂ) * (u + w)) * ((c2 : ℂ) * (u - w))).im| = |2 * (conj u * w).im| := by
  intro c2
  have hc2_sq : c2 ^ 2 = 1 / 2 := by rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hns (x : ℂ) : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hz : ‖(c2 : ℂ) * (u + w)‖ ^ 2 - ‖(c2 : ℂ) * (u - w)‖ ^ 2 = 2 * (conj u * w).re := by
    rw [hns, hns]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, zero_mul,
        sub_zero, add_zero]
    linear_combination 4 * (u.re * w.re + u.im * w.im) * hc2_sq
  have hx : 2 * (conj ((c2 : ℂ) * (u + w)) * ((c2 : ℂ) * (u - w))).re = ‖u‖ ^ 2 - ‖w‖ ^ 2 := by
    rw [hns u, hns w]
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.conj_re, Complex.conj_im,
        zero_mul, sub_zero, add_zero]
    linear_combination 2 * (u.re ^ 2 + u.im ^ 2 - w.re ^ 2 - w.im ^ 2) * hc2_sq
  have hy : 2 * (conj ((c2 : ℂ) * (u + w)) * ((c2 : ℂ) * (u - w))).im = -(2 * (conj u * w).im) := by
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.conj_re, Complex.conj_im,
        zero_mul, sub_zero, add_zero]
    linear_combination 4 * (u.im * w.re - u.re * w.im) * hc2_sq
  exact ⟨hz, by rw [← hx, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)],
      by rw [← abs_neg (2 * (conj u * w).im), ← hy, abs_mul,
           abs_of_pos (by norm_num : (0 : ℝ) < 2)]⟩

theorem coset_bloch_coords (V0 : Matrix (Fin 2) (Fin 2) ℂ) :
    let u := V0 0 0
    let v := V0 1 0
    let s1 : ℝ := 2 * (conj u * v).re
    let s2 : ℝ := 2 * (conj u * v).im
    let s3 : ℝ := ‖u‖ ^ 2 - ‖v‖ ^ 2
    let rem (idx : Nat) : Matrix (Fin 2) (Fin 2) ℂ := (cosetCircuit idx).eval.1ᴴ * V0
    (‖rem 0 0 0‖ ^ 2 - ‖rem 0 1 0‖ ^ 2 = s3 ∧ 2 * |(conj (rem 0 0 0) * rem 0 1 0).re| = |s1| ∧ 2 *
        |(conj (rem 0 0 0) * rem 0 1 0).im| = |s2|) ∧
    (‖rem 1 0 0‖ ^ 2 - ‖rem 1 1 0‖ ^ 2 = -s3 ∧ 2 * |(conj (rem 1 0 0) * rem 1 1 0).re| = |s1| ∧ 2 *
        |(conj (rem 1 0 0) * rem 1 1 0).im| = |s2|) ∧
    (‖rem 2 0 0‖ ^ 2 - ‖rem 2 1 0‖ ^ 2 = s1 ∧ 2 * |(conj (rem 2 0 0) * rem 2 1 0).re| = |s3| ∧ 2 *
        |(conj (rem 2 0 0) * rem 2 1 0).im| = |s2|) ∧
    (‖rem 3 0 0‖ ^ 2 - ‖rem 3 1 0‖ ^ 2 = s2 ∧ 2 * |(conj (rem 3 0 0) * rem 3 1 0).re| = |s3| ∧ 2 *
        |(conj (rem 3 0 0) * rem 3 1 0).im| = |s1|) ∧
    (‖rem 4 0 0‖ ^ 2 - ‖rem 4 1 0‖ ^ 2 = -s1 ∧ 2 * |(conj (rem 4 0 0) * rem 4 1 0).re| = |s3| ∧ 2 *
        |(conj (rem 4 0 0) * rem 4 1 0).im| = |s2|) ∧
    (‖rem 5 0 0‖ ^ 2 - ‖rem 5 1 0‖ ^ 2 = -s2 ∧ 2 * |(conj (rem 5 0 0) * rem 5 1 0).re| = |s3| ∧ 2 *
        |(conj (rem 5 0 0) * rem 5 1 0).im| = |s1|) := by
  intro u v s1 s2 s3 rem
  set c2 : ℝ := 1 / Real.sqrt 2
  have hhad : hadamard2 = Matrix.of ![![(c2 : ℂ), (c2 : ℂ)], ![(c2 : ℂ), -(c2 : ℂ)]] :=
    Matrix.ext fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [hadamard2, invSqrtTwo, c2, one_div]
  have hrem0 : rem 0 0 0 = u ∧ rem 0 1 0 = v := by simp [rem, cosetCircuit_eval 0, u, v]
  have hrem1 : rem 1 0 0 = v ∧ rem 1 1 0 = u := by
    constructor <;> simp [rem, cosetCircuit_eval 1, u, v, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply]
  have hrem2 : rem 2 0 0 = (c2 : ℂ) * (u + v) ∧ rem 2 1 0 = (c2 : ℂ) * (u - v) := by
    constructor <;>
        simp [rem, cosetCircuit_eval 2, hhad, u, v, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.conj_ofReal] <;> ring
  have hrem3 : rem 3 0 0 = (c2 : ℂ) * (u + -(Complex.I * v)) ∧ rem 3 1 0 = (c2 : ℂ) *
      (u - -(Complex.I * v)) := by
    constructor <;>
        simp [rem, cosetCircuit_eval 3, hhad, u, v, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.conj_ofReal] <;> ring
  have hrem4 : rem 4 0 0 = (c2 : ℂ) * (u + -v) ∧ rem 4 1 0 = (c2 : ℂ) * (u - -v) := by
    constructor <;>
        simp [rem, cosetCircuit_eval 4, hhad, u, v, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.conj_ofReal] <;> ring
  have hrem5 : rem 5 0 0 = (c2 : ℂ) * (u + Complex.I * v) ∧ rem 5 1 0 = (c2 : ℂ) * (u - Complex.I *
      v) := by
    constructor <;>
        simp [rem, cosetCircuit_eval 5, hhad, u, v, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Complex.conj_ofReal] <;> ring
  let B (i : Nat) (z x y : ℝ) : Prop := ‖rem i 0 0‖ ^ 2 - ‖rem i 1 0‖ ^ 2 = z ∧
    2 * |(conj (rem i 0 0) * rem i 1 0).re| = |x| ∧ 2 * |(conj (rem i 0 0) * rem i 1 0).im| = |y|
  have hhad_br {idx : Nat} {w : ℂ} {z y : ℝ}
      (hr : rem idx 0 0 = (c2 : ℂ) * (u + w) ∧ rem idx 1 0 = (c2 : ℂ) * (u - w))
      (hre : 2 * (conj u * w).re = z) (hnw : ‖w‖ = ‖v‖) (him : |2 * (conj u * w).im| = |y|) :
          B idx z s3 y := by
    obtain ⟨hz, hx, hy⟩ := had_pair_bloch u w
    dsimp only [B]
    rw [hr.1, hr.2]
    exact ⟨hz.trans hre, hx.trans (congrArg (fun t => |‖u‖ ^ 2 - t ^ 2|) hnw), hy.trans him⟩
  have h5_re : 2 * (conj u * (Complex.I * v)).re = -s2 := by
    simp only [s2, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
        Complex.I_im]
    ring
  have h5_im : 2 * (conj u * (Complex.I * v)).im = s1 := by
    simp only [s1, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
        Complex.I_im]
    ring
  -- Bloch coordinate permutations for idx = 0..5
  refine ⟨?_, ?_, hhad_br hrem2 rfl rfl rfl,
    hhad_br hrem3 (by rw [mul_neg, Complex.neg_re, mul_neg, h5_re, neg_neg]) (by simp)
      (by rw [mul_neg, Complex.neg_im, mul_neg, abs_neg, h5_im]),
    hhad_br hrem4 (by rw [mul_neg, Complex.neg_re, mul_neg]) (norm_neg v)
      (by rw [mul_neg, Complex.neg_im, mul_neg, abs_neg]),
    hhad_br hrem5 h5_re (by simp) (congrArg abs h5_im)⟩
  · rw [hrem0.1, hrem0.2]
    exact ⟨rfl, abs_mul (2 : ℝ) _ ▸ by norm_num [s1], abs_mul (2 : ℝ) _ ▸ by norm_num [s2]⟩
  · rw [hrem1.1, hrem1.2]
    exact ⟨(neg_sub (‖u‖ ^ 2) (‖v‖ ^ 2)).symm,
      by rw [← show 2 * (conj v * u).re = s1 by simp [s1, Complex.mul_re, Complex.conj_re,
                                                  Complex.conj_im]; ring,
           abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)],
      by rw [← abs_neg s2, ← show 2 * (conj v * u).im = -s2 by
           simp [s2, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring,
           abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]⟩

theorem exists_coset_wedge (V0 : Matrix (Fin 2) (Fin 2) ℂ) (hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ) :
    ∃ idx : Nat, idx < 6 ∧
      let rem0 := (cosetCircuit idx).eval.1ᴴ * V0
      rem0 0 0 ≠ 0 ∧
      2 * max |(matEta rem0).re| |(matEta rem0).im| ≤ 1 - ‖matEta rem0‖ ^ 2 := by
  obtain ⟨_, hs_sphere⟩ := unitary_bloch_sphere hV0
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩ := coset_bloch_coords V0
  set u := V0 0 0
  set v := V0 1 0
  set s1 : ℝ := 2 * (conj u * v).re
  set s2 : ℝ := 2 * (conj u * v).im
  set s3 : ℝ := ‖u‖ ^ 2 - ‖v‖ ^ 2
  let rem (idx : Nat) : Matrix (Fin 2) (Fin 2) ℂ := (cosetCircuit idx).eval.1ᴴ * V0
  have hwedge : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, 2 * |(conj (M 0 0) * M 1 0).re| ≤ ‖M 0 0‖ ^ 2 -
      ‖M 1 0‖ ^ 2 →
      2 * |(conj (M 0 0) * M 1 0).im| ≤ ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 → 0 < ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 →
      M 0 0 ≠ 0 ∧ 2 * max |(matEta M).re| |(matEta M).im| ≤ 1 - ‖matEta M‖ ^ 2 := by
    intro M hbX hbY hpos
    obtain ⟨hu_ne, hu_pos, hre_p, him_p, hv_norm⟩ := matEta_bloch_identities hpos
    rw [hre_p, hv_norm] at hbX
    rw [him_p, hv_norm] at hbY
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact ⟨hu_ne, max_le (le_of_mul_le_mul_left (by linarith) hu_pos)
        (le_of_mul_le_mul_left (by linarith) hu_pos)⟩
  -- Pick the coset maximizing |blochZ| >= max |blochX| |blochY|, with |blochZ| > 0 from
  -- s1^2+s2^2+s3^2=1
  have hpos_of_dom : ∀ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 → |a| ≤ |c| → |b| ≤ |c| → 0 < |c| := by
    intro a b c hsp hac hbc
    have h1 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hac
    have h2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hbc
    exact lt_of_le_of_ne (abs_nonneg c) fun hz => by
      linarith [hsp, sq_abs a, sq_abs b, sq_abs c, sq_eq_zero_iff.mpr hz.symm]
  let B (i : Nat) (z x y : ℝ) : Prop := ‖rem i 0 0‖ ^ 2 - ‖rem i 1 0‖ ^ 2 = z ∧
    2 * |(conj (rem i 0 0) * rem i 1 0).re| = |x| ∧ 2 * |(conj (rem i 0 0) * rem i 1 0).im| = |y|
  let Goal : Prop := ∃ idx < 6,
    rem idx 0 0 ≠ 0 ∧ 2 * max |(matEta (rem idx)).re| |(matEta (rem idx)).im| ≤ 1 -
        ‖matEta (rem idx)‖ ^ 2
  have haxis {ip ineg : Nat} {a b s : ℝ} (hip : ip < 6) (hin : ineg < 6)
      (hsp : a ^ 2 + b ^ 2 + s ^ 2 = 1) (ha : |a| ≤ |s|) (hb : |b| ≤ |s|)
      (hbp : B ip s a b) (hbn : B ineg (-s) a b) : Goal := by
    have hs_pos := hpos_of_dom a b s hsp ha hb
    by_cases hnn : 0 ≤ s
    · rw [abs_of_nonneg hnn] at ha hb hs_pos
      exact ⟨ip, hip, hwedge (rem ip) (by rwa [hbp.2.1, hbp.1]) (by rwa [hbp.2.2, hbp.1])
        (by rwa [hbp.1])⟩
    · rw [abs_of_neg (lt_of_not_ge hnn)] at ha hb hs_pos
      exact ⟨ineg, hin, hwedge (rem ineg) (by rwa [hbn.2.1, hbn.1]) (by rwa [hbn.2.2, hbn.1])
        (by rwa [hbn.1])⟩
  by_cases h3_dom : |s1| ≤ |s3| ∧ |s2| ≤ |s3|
  · exact haxis (by omega) (by omega) (by linarith) h3_dom.1 h3_dom.2 hb0 hb1
  · by_cases h1_dom : |s2| ≤ |s1| ∧ |s3| ≤ |s1|
    · exact haxis (by omega) (by omega) (by linarith) h1_dom.2 h1_dom.1 hb2 hb4
    · have h2_dom : |s1| ≤ |s2| ∧ |s3| ≤ |s2| := by
        rcases le_total |s1| |s2| with h12 | h21 <;> rcases le_total |s3| |s2| with h32 | h23
        · exact ⟨h12, h32⟩
        · exact (h3_dom ⟨h12.trans h23, h23⟩).elim
        · exact (h1_dom ⟨h21, h32.trans h21⟩).elim
        · exact (le_total |s1| |s3|).elim (fun h13 => (h3_dom ⟨h13, h23⟩).elim)
              (fun h31 => (h1_dom ⟨h21, h31⟩).elim)
      exact haxis (by omega) (by omega) (by linarith) h2_dom.2 h2_dom.1 hb3 hb5

/-! ### 5. Affine 4-Corner Barycentric Enclosure & Rational Simplicial Mean Bound -/

def cross2 (p a b : ℂ) : ℝ := (a.re - p.re) * (b.im - p.im) - (a.im - p.im) * (b.re - p.re)
theorem crossLoCorner_sound {px py : SInt} {va vb : Box2DS} {ua ub : ℂ}
    (hpos : sPos (crossLoCorner px py va vb) = true) (ha : va.Mem ua) (hb : vb.Mem ub) : 0 <
    cross2 ⟨(px.toInt : ℝ) / (2 ^ 52 : ℝ), (py.toInt : ℝ) / (2 ^ 52 : ℝ)⟩ ua ub := by
  set BS : ℝ := 2 ^ 52
  have hBS_pos : 0 < BS := by dsimp [BS]; positivity
  rcases ha with ⟨hax0, hax1, hay0, hay1⟩
  rcases hb with ⟨hbx0, hbx1, hby0, hby1⟩
  have sLo (p : SInt) {s : SInt} {r : ℝ} (h : (s.toInt : ℝ) / BS ≤ r) : ((sSub s p).toInt : ℝ) ≤
      BS * r - p.toInt := by
    simpa [sSub_toInt] using sub_le_sub_right ((div_le_iff₀' hBS_pos).mp h) (p.toInt : ℝ)
  have sHi (p : SInt) {s : SInt} {r : ℝ} (h : r ≤ (s.toInt : ℝ) / BS) : BS * r - p.toInt ≤
      ((sSub s p).toInt : ℝ) := by
    simpa [sSub_toInt] using sub_le_sub_right ((le_div_iff₀' hBS_pos).mp h) (p.toInt : ℝ)
  have hp1 := interval_prod_ge_min4 (sLo px hax0) (sHi px hax1) (sLo py hby0) (sHi py hby1)
  have hp2 := interval_prod_le_max4 (sLo py hay0) (sHi py hay1) (sLo px hbx0) (sHi px hbx1)
  have hpos_int : (0 : ℝ) < ((crossLoCorner px py va vb).toInt : ℝ) := by
    exact_mod_cast (sPos_iff _).mp hpos
  have hlo_eq : ((crossLoCorner px py va vb).toInt : ℝ) = min (((sSub va.x0 px).toInt : ℝ) *
      (sSub vb.y0 py).toInt) (min (((sSub va.x0 px).toInt : ℝ) * (sSub vb.y1 py).toInt)
      (min (((sSub va.x1 px).toInt : ℝ) * (sSub vb.y0 py).toInt)
      (((sSub va.x1 px).toInt : ℝ) * (sSub vb.y1 py).toInt))) - max (((sSub va.y0 py).toInt : ℝ) *
      (sSub vb.x0 px).toInt) (max (((sSub va.y0 py).toInt : ℝ) * (sSub vb.x1 px).toInt)
      (max (((sSub va.y1 py).toInt : ℝ) * (sSub vb.x0 px).toInt)
      (((sSub va.y1 py).toInt : ℝ) * (sSub vb.x1 px).toInt)))
      := by simp [crossLoCorner, sMin4, sMax4]
  have hscale : BS ^ 2 * cross2 ⟨(px.toInt : ℝ) / BS, (py.toInt : ℝ) / BS⟩ ua ub =
      (BS * ua.re - px.toInt) * (BS * ub.im - py.toInt) - (BS * ua.im - py.toInt) *
      (BS * ub.re - px.toInt) := by
    dsimp [cross2]
    field_simp [hBS_pos.ne']
  have hprod_pos : 0 < BS ^ 2 * cross2 ⟨(px.toInt : ℝ) / BS, (py.toInt : ℝ) / BS⟩ ua ub := by
    rw [hscale]; linarith [hpos_int, hlo_eq, hp1, hp2]
  exact pos_of_mul_pos_right hprod_pos (by positivity)

theorem cross2_rect_pos {rx0 rx1 ry0 ry1 : ℝ} {z ua ub : ℂ} (hx_lt : rx0 < rx1) (hy_lt : ry0 < ry1)
    (hzx0 : rx0 ≤ z.re) (hzx1 : z.re ≤ rx1) (hzy0 : ry0 ≤ z.im) (hzy1 : z.im ≤ ry1)
    (hc00 : 0 < cross2 ⟨rx0, ry0⟩ ua ub) (hc01 : 0 < cross2 ⟨rx0, ry1⟩ ua ub)
    (hc10 : 0 < cross2 ⟨rx1, ry0⟩ ua ub) (hc11 : 0 < cross2 ⟨rx1, ry1⟩ ua ub) : 0 <
    cross2 z ua ub := by
  set tx : ℝ := (z.re - rx0) / (rx1 - rx0)
  set ty : ℝ := (z.im - ry0) / (ry1 - ry0)
  have htx0 : 0 ≤ tx := div_nonneg (by linarith) (by linarith)
  have htx1 : tx ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hty0 : 0 ≤ ty := div_nonneg (by linarith) (by linarith)
  have hty1 : ty ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hz_re : z.re = (1 - tx) * rx0 + tx * rx1 := by
    dsimp [tx]; field_simp [(sub_pos.mpr hx_lt).ne']; ring
  have hz_im : z.im = (1 - ty) * ry0 + ty * ry1 := by
    dsimp [ty]; field_simp [(sub_pos.mpr hy_lt).ne']; ring
  have haff : cross2 z ua ub = (1 - tx) * (1 - ty) * cross2 ⟨rx0, ry0⟩ ua ub + (1 - tx) * ty *
      cross2 ⟨rx0, ry1⟩ ua ub + tx * (1 - ty) * cross2 ⟨rx1, ry0⟩ ua ub + tx * ty *
      cross2 ⟨rx1, ry1⟩ ua ub := by unfold cross2; rw [hz_re, hz_im]; dsimp only; ring
  set m :=
      min (min (cross2 ⟨rx0, ry0⟩ ua ub) (cross2 ⟨rx0, ry1⟩ ua ub)) (min (cross2 ⟨rx1, ry0⟩ ua ub)
      (cross2 ⟨rx1, ry1⟩ ua ub))
  have hm_pos : 0 < m := lt_min (lt_min hc00 hc01) (lt_min hc10 hc11);
  have hm00 : m ≤ cross2 ⟨rx0, ry0⟩ ua ub := (min_le_left _ _).trans (min_le_left _ _);
  have hm01 : m ≤ cross2 ⟨rx0, ry1⟩ ua ub := (min_le_left _ _).trans (min_le_right _ _);
  have hm10 : m ≤ cross2 ⟨rx1, ry0⟩ ua ub := (min_le_right _ _).trans (min_le_left _ _);
  have hm11 : m ≤ cross2 ⟨rx1, ry1⟩ ua ub := (min_le_right _ _).trans (min_le_right _ _)
  have hw00 : 0 ≤ (1 - tx) * (1 - ty) := mul_nonneg (by linarith) (by linarith)
  have hw01 : 0 ≤ (1 - tx) * ty := mul_nonneg (by linarith) hty0
  have hw10 : 0 ≤ tx * (1 - ty) := mul_nonneg htx0 (by linarith)
  have hw11 : 0 ≤ tx * ty := mul_nonneg htx0 hty0
  have hw_sum : (1 - tx) * (1 - ty) + (1 - tx) * ty + tx * (1 - ty) + tx * ty = 1 := by ring
  rw [haff]; have t1 := mul_le_mul_of_nonneg_left hm00 hw00;
  have t2 := mul_le_mul_of_nonneg_left hm01 hw01; have t3 := mul_le_mul_of_nonneg_left hm10 hw10;
  have t4 := mul_le_mul_of_nonneg_left hm11 hw11
  nlinarith

theorem checkCornerEncl_barycentric_sound {x0 x1 y0 y1 : SInt} {v0 v1 v2 : Box2DS}
    {zw uw0 uw1 uw2 : ℂ} (hx_lt : (x0.toInt : ℝ) < (x1.toInt : ℝ))
    (hy_lt : (y0.toInt : ℝ) < (y1.toInt : ℝ)) (hmem_z : (Box2DS.mk x0 x1 y0 y1).Mem zw)
    (hm0 : v0.Mem uw0) (hm1 : v1.Mem uw1) (hm2 : v2.Mem uw2)
    (he00 : checkCornerEncl x0 y0 v0 v1 v2 = true) (he01 : checkCornerEncl x0 y1 v0 v1 v2 = true)
    (he10 : checkCornerEncl x1 y0 v0 v1 v2 = true) (he11 : checkCornerEncl x1 y1 v0 v1 v2 = true) :
    ∃ p : Fin 3 → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i : Fin 3, p i = 1 ∧ (p 0 : ℂ) * uw0 + (p 1 : ℂ) * uw1 +
    (p 2 : ℂ) * uw2 = zw := by
  unfold checkCornerEncl at he00 he01 he10 he11;
  simp only [Bool.and_eq_true, and_assoc] at he00 he01 he10 he11
  have hrx_lt : (x0.toInt : ℝ) / (2 ^ 52 : ℝ) < (x1.toInt : ℝ) / (2 ^ 52 : ℝ) :=
    div_lt_div_of_pos_right hx_lt (by positivity)
  have hry_lt : (y0.toInt : ℝ) / (2 ^ 52 : ℝ) < (y1.toInt : ℝ) / (2 ^ 52 : ℝ) :=
    div_lt_div_of_pos_right hy_lt (by positivity)
  rcases hmem_z with ⟨hzx0, hzx1, hzy0, hzy1⟩
  have hw0_pos : 0 < cross2 zw uw1 uw2 :=
      cross2_rect_pos hrx_lt hry_lt hzx0 hzx1 hzy0 hzy1 (crossLoCorner_sound he00.1 hm1 hm2)
      (crossLoCorner_sound he01.1 hm1 hm2) (crossLoCorner_sound he10.1 hm1 hm2)
      (crossLoCorner_sound he11.1 hm1 hm2); have hw1_pos : 0 < cross2 zw uw2 uw0 :=
                                              cross2_rect_pos hrx_lt hry_lt hzx0 hzx1 hzy0 hzy1
                                              (crossLoCorner_sound he00.2.1 hm2 hm0)
                                              (crossLoCorner_sound he01.2.1 hm2 hm0)
                                              (crossLoCorner_sound he10.2.1 hm2 hm0)
                                              (crossLoCorner_sound he11.2.1 hm2 hm0);
                                              have hw2_pos : 0 < cross2 zw uw0 uw1 :=
                                              cross2_rect_pos hrx_lt hry_lt hzx0 hzx1 hzy0 hzy1
                                              (crossLoCorner_sound he00.2.2 hm0 hm1)
                                              (crossLoCorner_sound he01.2.2 hm0 hm1)
                                              (crossLoCorner_sound he10.2.2 hm0 hm1)
                                              (crossLoCorner_sound he11.2.2 hm0 hm1)
  set w0 := cross2 zw uw1 uw2
  set w1 := cross2 zw uw2 uw0
  set w2 := cross2 zw uw0 uw1
  set W := w0 + w1 + w2
  have hW_pos : 0 < W := by dsimp [W]; linarith
  let p : Fin 3 → ℝ := ![w0 / W, w1 / W, w2 / W]; have hp0 : p 0 = w0 / W := rfl;
  have hp1 : p 1 = w1 / W := rfl; have hp2 : p 2 = w2 / W := rfl; refine ⟨p, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change 0 ≤ w0 / W; exact div_nonneg hw0_pos.le hW_pos.le
    · change 0 ≤ w1 / W; exact div_nonneg hw1_pos.le hW_pos.le
    · change 0 ≤ w2 / W; exact div_nonneg hw2_pos.le hW_pos.le
  · rw [Fin.sum_univ_three, hp0, hp1, hp2, ← add_div, ← add_div, div_eq_one_iff_eq hW_pos.ne']
  · rw [hp0, hp1, hp2]; apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]; rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          ← add_div, div_eq_iff hW_pos.ne']; dsimp [W, w0, w1, w2, cross2]; ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]; rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          ← add_div, div_eq_iff hW_pos.ne']; dsimp [W, w0, w1, w2, cross2]; ring
theorem inv_sqrt_one_add_bounds {x : ℝ} (hx0 : -(1 / 4) ≤ x) (hx1 : x ≤ 1 / 4) : 1 - x / 2 ≤ 1 /
    Real.sqrt (1 + x) ∧ 1 / Real.sqrt (1 + x) ≤ 1 - x / 2 + x ^ 2 / 2 := by
  have h1x_pos : 0 < 1 + x := by linarith
  have hs_pos : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr h1x_pos;
  have hs_sq : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt h1x_pos.le; constructor
  · rw [le_div_iff₀ hs_pos]
    refine (sq_le_sq₀ (mul_nonneg (by linarith) hs_pos.le) zero_le_one).mp ?_
    rw [mul_pow, hs_sq]
    linarith [div_nonneg (mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 3 - x))
        (by norm_num : (0 : ℝ) ≤ 4),
      show (1 - x / 2) ^ 2 * (1 + x) = 1 - x ^ 2 * (3 - x) / 4 by ring]
  · rw [div_le_iff₀ hs_pos]
    refine (sq_le_sq₀ zero_le_one (mul_nonneg (by nlinarith [sq_nonneg x]) hs_pos.le)).mp ?_
    rw [mul_pow, hs_sq]
    have hcubic : 0 ≤ 1 + 3 * x - x ^ 2 + x ^ 3 := by
      nlinarith [sq_nonneg x, mul_le_mul_of_nonneg_right hx0 (sq_nonneg x)]
    linarith [mul_nonneg (show 0 ≤ x ^ 2 / 4 by positivity) hcubic,
      show (1 - x / 2 + x ^ 2 / 2) ^ 2 * (1 + x) = 1 + (x ^ 2 / 4) * (1 + 3 * x - x ^ 2 +
          x ^ 3) by ring]

theorem fin3_convex_norm_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    {p : Fin 3 → ℝ} {f : Fin 3 → E} {B : ℝ}
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin 3, p i = 1) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖∑ i : Fin 3, (p i : ℂ) • f i‖ ≤ B := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ =>
      ?_).trans_eq (by rw [← Finset.sum_mul, hp_sum, one_mul]))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp_nn i)]
  exact mul_le_mul_of_nonneg_left (hf i) (hp_nn i)

theorem su2EtaMat_jung_mean_le_ep {z : ℂ} {u : Fin 3 → ℂ} {p : Fin 3 → ℝ}
    (ep_nm mean_num : ℕ) (hep_hi : ep_nm ≤ 1000)
    (hmean_ok :
      ((ep_nm : ℝ) / 10 ^ 9) ^ 2 / 6 +
        ((3 / 2) * (116 / 10 ^ 6) + ((ep_nm : ℝ) / 10 ^ 9) / 2) *
          ((ep_nm : ℝ) / 10 ^ 9) ^ 2 ≤
        (mean_num : ℝ) / 10 ^ 18)
    (hz : ‖z‖ ≤ 116 / 10 ^ 6) (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin 3, p i = 1)
    (hbary : ∑ i : Fin 3, (p i : ℂ) • u i = z)
    (hpair : ∀ i j, ‖u i - u j‖ ≤ (ep_nm : ℝ) / 10 ^ 9) :
    ‖su2EtaMat z - ∑ i : Fin 3, (p i : ℂ) • su2EtaMat (u i)‖ ≤ (mean_num : ℝ) / 10 ^ 18 := by
  set R : ℝ := 116 / 10 ^ 6
  set h : ℝ := (ep_nm : ℝ) / 10 ^ 9
  set tMax : ℝ := 2 * R * h + h ^ 2
  have hR_nn : 0 ≤ R := by norm_num [R]
  have hh_nn : 0 ≤ h := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hh_hi : h ≤ 1 / 10 ^ 6 :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hep_hi) (by positivity)).trans_eq (by norm_num)
  have htMax_nn : 0 ≤ tMax :=
    add_nonneg (mul_nonneg (mul_nonneg zero_le_two hR_nn) hh_nn) (sq_nonneg h)
  have hlt_h : tMax ≤ h := (by nlinarith [hh_nn, hh_hi] : 2 * (116 / 10 ^ 6 : ℝ) * h + h ^ 2 ≤ h)
  let d : Fin 3 → ℂ := fun i => u i - z
  have hu_eq : ∀ i, u i = z + d i := fun i => (add_sub_cancel z (u i)).symm
  have hp_sum_c : ∑ i : Fin 3, (p i : ℂ) = 1 := by exact_mod_cast hp_sum
  have hd_norm (i : Fin 3) : ‖d i‖ ≤ h := by
    rw [show d i = ∑ j : Fin 3, (p j : ℂ) • (u i - u j) by
      simp only [d, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hbary, hp_sum_c, one_smul]]
    exact fin3_convex_norm_le hp_nn hp_sum (hpair i)
  have hd_sum : ∑ i : Fin 3, (p i : ℂ) * d i = 0 := by
    have h1 : ∑ i : Fin 3, (p i : ℂ) * (u i - z) = (∑ i : Fin 3, (p i : ℂ) • u i) -
        (∑ i : Fin 3, (p i : ℂ)) * z := by simp [Fin.sum_univ_three, smul_eq_mul]; ring
    dsimp [d]; rw [h1, hbary, hp_sum_c, one_mul, sub_self]
  have hd_re_sum : ∑ i : Fin 3, p i * (d i).re = 0 := by
    simpa [Fin.sum_univ_three] using congrArg Complex.re hd_sum
  have hd_im_sum : ∑ i : Fin 3, p i * (d i).im = 0 := by
    simpa [Fin.sum_univ_three] using congrArg Complex.im hd_sum
  set D0 : ℝ := 1 + ‖z‖ ^ 2
  have hD0_ge1 : 1 ≤ D0 := by dsimp [D0]; nlinarith [sq_nonneg ‖z‖]
  have hD0_pos : 0 < D0 := by linarith
  set s0 : ℝ := 1 / √D0
  have hs0_pos : 0 < s0 := div_pos one_pos (Real.sqrt_pos.mpr hD0_pos)
  have hs0_le1 : s0 ≤ 1 :=
      (div_le_one (Real.sqrt_pos.mpr hD0_pos)).mpr (Real.le_sqrt_of_sq_le (by linarith))
  let lin : Fin 3 → ℝ := fun i => 2 * (z.re * (d i).re + z.im * (d i).im) / D0
  let q : Fin 3 → ℝ := fun i => ‖d i‖ ^ 2 / D0
  let t : Fin 3 → ℝ := fun i => lin i + q i
  have hlin_sum : ∑ i : Fin 3, p i * lin i = 0 := by
    have h1 : ∑ i : Fin 3, p i * lin i = (2 / D0) * (z.re * (∑ i : Fin 3, p i * (d i).re) + z.im *
        (∑ i : Fin 3, p i * (d i).im)) := by
      simp [lin, Fin.sum_univ_three]
      ring
    rw [h1, hd_re_sum, hd_im_sum]; ring
  have hlin_abs : ∀ i, |lin i| ≤ 2 * R * h := fun i => by
    have hcs : |z.re * (d i).re + z.im * (d i).im| ≤ ‖z‖ * ‖d i‖ := by
      rw [show z.re * (d i).re + z.im * (d i).im =
          (conj z * d i).re by simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]]
      exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
    dsimp [lin]
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hD0_pos]
    exact (div_le_self (by positivity) hD0_ge1).trans
        (by linarith [mul_le_mul hz (hd_norm i) (norm_nonneg _) hR_nn])
  have hq_bounds : ∀ i, 0 ≤ q i ∧ q i ≤ ‖d i‖ ^ 2 ∧ ‖d i‖ ^ 2 ≤ h ^ 2 := fun i =>
    ⟨div_nonneg (sq_nonneg _) hD0_pos.le, div_le_self (sq_nonneg _) hD0_ge1,
      (sq_le_sq₀ (norm_nonneg _) hh_nn).mpr (hd_norm i)⟩
  have ht_abs : ∀ i, |t i| ≤ tMax ∧ |t i| ≤ h ∧ -(1 / 4) ≤ t i ∧ t i ≤ 1 / 4 := fun i => by
    have hq_le : |q i| ≤ h ^ 2 := (abs_of_nonneg (hq_bounds i).1).trans_le
      ((hq_bounds i).2.1.trans (hq_bounds i).2.2)
    have hbd : |t i| ≤ tMax := (abs_add_le _ _).trans (add_le_add (hlin_abs i) hq_le)
    have habs_q : |t i| ≤ 1 / 4 := (hbd.trans hlt_h).trans (hh_hi.trans (by norm_num))
    exact ⟨hbd, hbd.trans hlt_h, (abs_le.mp habs_q).1, (abs_le.mp habs_q).2⟩
  let s : Fin 3 → ℝ := fun i => 1 / √(1 + ‖u i‖ ^ 2)
  have hs_factor : ∀ i, s i = s0 * (1 / √(1 + t i)) := fun i => by
    have hnd : ‖u i‖ ^ 2 - ‖z‖ ^ 2 = 2 * (z.re * (d i).re + z.im * (d i).im) + ‖d i‖ ^ 2 := by
      rw [hu_eq i, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
          ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      ring
    have h1u : 1 + ‖u i‖ ^ 2 = D0 * (1 + t i) := by
      dsimp [D0, t, lin, q] at *
      field_simp [hD0_pos.ne']
      linarith
    dsimp [s, s0]; rw [h1u, Real.sqrt_mul hD0_pos.le, div_mul_div_comm, one_mul]
  let δ : Fin 3 → ℝ := fun i => (1 / √(1 + t i)) - (1 - lin i / 2)
  have hs_lin (i : Fin 3) : s i = s0 * (1 - lin i / 2 + δ i) := by
    rw [hs_factor i]
    dsimp only [δ]
    ring
  have hδ_bounds : ∀ i, -(‖d i‖ ^ 2 / 2) ≤ δ i ∧ δ i ≤ tMax ^ 2 / 2 ∧ |δ i| ≤ h ^ 2 / 2 := fun i =>
      by
    obtain ⟨hlo, hhi⟩ := inv_sqrt_one_add_bounds (ht_abs i).2.2.1 (ht_abs i).2.2.2
    have hti_sq : (t i) ^ 2 ≤ tMax ^ 2 :=
      sq_abs (t i) ▸ (sq_le_sq₀ (abs_nonneg _) htMax_nn).mpr (ht_abs i).1
    obtain ⟨hqi0, hqi_d, hd_h⟩ := hq_bounds i
    have hth2 : tMax ^ 2 ≤ h ^ 2 := (sq_le_sq₀ htMax_nn hh_nn).mpr hlt_h
    dsimp only [δ, t] at hlo hhi ⊢
    exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  -- Lagrange barycentric variance identity: ∑ p_i ‖d_i‖^2 = ∑_{i<j} p_i p_j ‖u_i - u_j‖^2 ≤ h^2 / 3
  have hd_sq_sum : ∑ i : Fin 3, p i * ‖d i‖ ^ 2 ≤ h ^ 2 / 3 := by
    have hnc : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have hp3 : p 0 + p 1 + p 2 = 1 := by simpa [Fin.sum_univ_three, add_assoc] using hp_sum
    have hdr : p 0 * (d 0).re + p 1 * (d 1).re + p 2 * (d 2).re = 0 := by
      simpa [Fin.sum_univ_three, add_assoc] using hd_re_sum
    have hdi : p 0 * (d 0).im + p 1 * (d 1).im + p 2 * (d 2).im = 0 := by
      simpa [Fin.sum_univ_three, add_assoc] using hd_im_sum
    have hlag : ∑ i : Fin 3, p i * ‖d i‖ ^ 2 = p 0 * p 1 * ‖d 0 - d 1‖ ^ 2 + p 0 * p 2 * ‖d 0 -
        d 2‖ ^ 2 + p 1 * p 2 * ‖d 1 - d 2‖ ^ 2 := by
      rw [Fin.sum_univ_three]
      simp only [hnc, Complex.sub_re, Complex.sub_im]
      linear_combination -(p 0 * ((d 0).re ^ 2 + (d 0).im ^ 2) + p 1 * ((d 1).re ^ 2 +
          (d 1).im ^ 2) + p 2 * ((d 2).re ^ 2 + (d 2).im ^ 2)) * hp3 + (p 0 * (d 0).re + p 1 *
          (d 1).re + p 2 * (d 2).re) * hdr + (p 0 * (d 0).im +
          p 1 * (d 1).im + p 2 * (d 2).im) * hdi
    have hch : ∀ i j, ‖d i - d j‖ ^ 2 ≤ h ^ 2 := fun i j =>
      sub_sub_sub_cancel_right (u i) (u j) z ▸ (sq_le_sq₀ (norm_nonneg _) hh_nn).mpr (hpair i j)
    have hsym_p : p 0 * p 1 + p 0 * p 2 + p 1 * p 2 ≤ 1 / 3 := by
      nlinarith [hp3, sq_nonneg (p 0 - p 1), sq_nonneg (p 0 - p 2), sq_nonneg (p 1 - p 2)]
    rw [hlag]
    nlinarith [mul_nonneg (hp_nn 0) (hp_nn 1), mul_nonneg (hp_nn 0) (hp_nn 2),
      mul_nonneg (hp_nn 1) (hp_nn 2), hch 0 1, hch 0 2, hch 1 2, sq_nonneg h]
  set a : ℝ := s0 - ∑ i : Fin 3, p i * s i
  set b : ℂ := (s0 : ℂ) * z - ∑ i : Fin 3, (p i : ℂ) * ((s i : ℂ) * u i)
  have hmat_eq : su2EtaMat z - ∑ i : Fin 3, (p i : ℂ) • su2EtaMat (u i) =
      (Matrix.of ![![(a : ℂ), b], ![-conj b, (a : ℂ)]]) := by
    unfold su2EtaMat
    ext r c : 1
    fin_cases r <;> fin_cases c <;>
        simp [a, b, s0, D0, s, Fin.sum_univ_three, smul_eq_mul, Complex.conj_ofReal]; ring
  have ha_abs : |a| ≤ h ^ 2 / 6 := by
    have ha_eq : a = -s0 * ∑ i : Fin 3, p i * δ i := by
      have hexp : ∑ i : Fin 3, p i * (s0 * (1 - lin i / 2 + δ i)) = s0 * (∑ i : Fin 3, p i) -
          (s0 / 2) * (∑ i : Fin 3, p i * lin i) + s0 * (∑ i : Fin 3, p i * δ i) := by
        simp [Fin.sum_univ_three]; ring
      dsimp [a]
      simp only [hs_lin]
      rw [hexp, hp_sum, hlin_sum]
      ring
    have ht3 : tMax ≤ h / 3 := (by nlinarith [hh_nn, hh_hi] : 2 * (116 / 10 ^ 6 : ℝ) * h + h ^ 2 ≤
      h / 3)
    have htMax_h6 : tMax ^ 2 / 2 ≤ h ^ 2 / 6 := by
      nlinarith [(sq_le_sq₀ htMax_nn (by positivity)).mpr ht3]
    have hsum_hi : ∑ i : Fin 3, p i * δ i ≤ h ^ 2 / 6 :=
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hδ_bounds i).2.1 (hp_nn i)).trans
        (by rwa [← Finset.sum_mul, hp_sum, one_mul])
    have hsum_lo : -(h ^ 2 / 6) ≤ ∑ i : Fin 3, p i * δ i := by
      have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          mul_le_mul_of_nonneg_left (hδ_bounds i).1 (hp_nn i)
      have hrw : ∑ i : Fin 3, p i * (-(‖d i‖ ^ 2 / 2)) = -(1 / 2 : ℝ) * ∑ i : Fin 3, p i *
          ‖d i‖ ^ 2 := by
        simp [Fin.sum_univ_three]
        ring
      linarith [hd_sq_sum]
    rw [ha_eq, abs_mul, abs_neg, abs_of_pos hs0_pos]
    exact (mul_le_mul hs0_le1 (abs_le.mpr ⟨hsum_lo, hsum_hi⟩)
        (abs_nonneg _) zero_le_one).trans (by linarith)
  have hb_norm : ‖b‖ ≤ ((3 / 2) * R + h / 2) * h ^ 2 := by
    have hlin_c : ∑ i : Fin 3, (p i : ℂ) * (lin i : ℂ) = 0 := by exact_mod_cast hlin_sum
    have hb_eq : b = (s0 : ℂ) * ∑ i : Fin 3, (p i : ℂ) • (-((δ i : ℂ) * z) +
        (((lin i / 2 - δ i : ℝ) : ℂ) * d i)) := by
      have hexp : ∑ i : Fin 3, (p i : ℂ) * (((s0 * (1 - lin i / 2 + δ i) : ℝ) : ℂ) * (z + d i)) =
          (s0 : ℂ) * (∑ i : Fin 3, (p i : ℂ)) * z - ((s0 : ℂ) / 2) * (∑ i : Fin 3, (p i : ℂ) *
              (lin i : ℂ)) * z +
          (s0 : ℂ) * (∑ i : Fin 3, (p i : ℂ) * d i) -
          (s0 : ℂ) * ∑ i : Fin 3, (p i : ℂ) • (-((δ i : ℂ) * z) + (((lin i / 2 - δ i : ℝ) : ℂ) *
              d i)) := by
        simp [Fin.sum_univ_three, smul_eq_mul]
        ring
      dsimp only [b]
      simp only [hs_lin, hu_eq]
      rw [hexp, hp_sum_c, hlin_c, hd_sum]
      ring
    have hterm : ∀ i, ‖-((δ i : ℂ) * z) + (((lin i / 2 - δ i : ℝ) : ℂ) * d i)‖ ≤ ((3 / 2) * R + h /
        2) * h ^ 2 := fun i => by
      have ht1 : ‖-((δ i : ℂ) * z)‖ ≤ (h ^ 2 / 2) * R := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hδ_bounds i).2.2 hz (norm_nonneg _) (by positivity)
      have hcoef : |lin i / 2 - δ i| ≤ R * h + h ^ 2 / 2 := by
        have hl2 : |lin i / 2| ≤ R * h := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm (R * h) 2, ← mul_assoc]
          exact hlin_abs i
        linarith [abs_sub (lin i / 2) (δ i), (hδ_bounds i).2.2]
      have ht2 : ‖(((lin i / 2 - δ i : ℝ) : ℂ) * d i)‖ ≤ (R * h + h ^ 2 / 2) * h := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hcoef (hd_norm i) (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (by linarith)
    rw [hb_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0_pos.le]
    exact (mul_le_mul hs0_le1 (fin3_convex_norm_le hp_nn hp_sum hterm)
        (norm_nonneg _) zero_le_one).trans (by linarith)
  rw [hmat_eq]
  exact (opNorm_quat2_le a b).trans ((add_le_add ha_abs hb_norm).trans hmean_ok)

/-! ### 6. Adaptive Quadtree Soundness & 3-Stage Jung-Tile Cascade (`87 T`) -/

def SquareMem (x0 y0 w : Nat) (zw : ℂ) : Prop :=
    (x0 : ℝ) / (2 ^ 52 : ℝ) ≤ zw.re ∧ zw.re ≤ ((x0 + w : Nat) : ℝ) / (2 ^ 52 : ℝ) ∧ (y0 : ℝ) /
    (2 ^ 52 : ℝ) ≤ zw.im ∧ zw.im ≤ ((y0 + w : Nat) : ℝ) / (2 ^ 52 : ℝ)
theorem nat_blt_false_of_ge {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hlt : Nat.blt a b
  · rfl
  · exact absurd ((nat_ble_true_iff (Nat.succ a) b).mp hlt) (by omega)
theorem isOutsideDom_false_of_dom0 {x0 y0 w rInNumSq rInScaleSq : Nat} {zw : ℂ}
    (him0 : 0 ≤ zw.im) (hle : zw.im ≤ zw.re) (hdisc : (zw.re + 1) ^ 2 + zw.im ^ 2 ≤ 2)
    (hsq : SquareMem x0 y0 w zw) : isOutsideDom 0 x0 y0 w rInNumSq rInScaleSq = false := by
  rcases hsq with ⟨hx0, hx1, hy0, _⟩
  set BS : ℝ := 2 ^ 52
  have hBS_pos : 0 < BS := by positivity
  have hy_le_xw : y0 ≤ x0 + w := by
    exact_mod_cast (div_le_div_iff_of_pos_right hBS_pos).mp (hy0.trans (hle.trans hx1))
  have hx0_r := (div_le_iff₀' hBS_pos).mp hx0
  have hy0_r := (div_le_iff₀' hBS_pos).mp hy0
  have hBS_val : BS = 4503599627370496 := by norm_num [BS]
  have hdom_nat : (x0 + 4503599627370496) * (x0 + 4503599627370496) + y0 * y0 ≤
      2 * (4503599627370496 * 4503599627370496) := by
    exact_mod_cast (show (((x0 + 4503599627370496) * (x0 + 4503599627370496) + y0 * y0 : Nat) : ℝ) ≤
        ((2 * (4503599627370496 * 4503599627370496) : Nat) : ℝ) by
      push_cast
      nlinarith [hdisc,
        (sq_le_sq₀ (by positivity) (by linarith)).mpr
          (show (x0 : ℝ) + 4503599627370496 ≤ 4503599627370496 * (zw.re + 1) by linarith),
        (sq_le_sq₀ (by positivity) (by linarith)).mpr
          (show (y0 : ℝ) ≤ 4503599627370496 * zw.im by linarith)])
  dsimp only [isOutsideDom]
  rw [show Nat.blt (Nat.add x0 w) y0 = false from nat_blt_false_of_ge hy_le_xw, Bool.false_or]
  exact nat_blt_false_of_ge hdom_nat

theorem isOutsideDom_false_of_rad {stageKind x0 y0 w rInNumSq rInScaleSq : Nat} {zw : ℂ}
    (hkind : stageKind ≠ 0) (hrScale : 0 < rInScaleSq) (him0 : 0 ≤ zw.im) (hle : zw.im ≤ zw.re)
    (hrad : zw.re ^ 2 + zw.im ^ 2 ≤ (rInNumSq : ℝ) / (rInScaleSq : ℝ))
    (hsq : SquareMem x0 y0 w zw) : isOutsideDom stageKind x0 y0 w rInNumSq rInScaleSq = false := by
  rcases hsq with ⟨hx0, hx1, hy0, _⟩
  set BS : ℝ := 2 ^ 52
  have hBS_pos : 0 < BS := by positivity
  have hy_le_xw : y0 ≤ x0 + w := by
    exact_mod_cast (div_le_div_iff_of_pos_right hBS_pos).mp (hy0.trans (hle.trans hx1))
  have hx0_r := (div_le_iff₀' hBS_pos).mp hx0
  have hy0_r := (div_le_iff₀' hBS_pos).mp hy0
  have hBS_val : BS = 4503599627370496 := by norm_num [BS]
  have hrad_mul := (le_div_iff₀ (Nat.cast_pos.mpr hrScale)).mp hrad
  have hdom_nat :
      (x0 * x0 + y0 * y0) * rInScaleSq ≤ rInNumSq * (4503599627370496 * 4503599627370496) := by
    exact_mod_cast (show (((x0 * x0 + y0 * y0) * rInScaleSq : Nat) : ℝ) ≤
        ((rInNumSq * (4503599627370496 * 4503599627370496) : Nat) : ℝ) by
      push_cast
      have hsq1 := (sq_le_sq₀ (by positivity) (by linarith)).mpr
        (show (x0 : ℝ) ≤ 4503599627370496 * zw.re by linarith)
      have hsq2 := (sq_le_sq₀ (by positivity) (by linarith)).mpr
        (show (y0 : ℝ) ≤ 4503599627370496 * zw.im by linarith)
      nlinarith [hrad_mul, mul_le_mul_of_nonneg_right
        (show (x0 : ℝ) * x0 + (y0 : ℝ) * y0 ≤
          (4503599627370496 * 4503599627370496 : ℝ) * (zw.re ^ 2 + zw.im ^ 2) by nlinarith)
        (Nat.cast_nonneg rInScaleSq)])
  unfold isOutsideDom
  rw [Bool.eq_false_iff.mpr (mt Nat.beq_eq.mp hkind)]
  dsimp only
  rw [show Nat.blt (Nat.add x0 w) y0 = false from nat_blt_false_of_ge hy_le_xw, Bool.false_or]
  exact nat_blt_false_of_ge hdom_nat

theorem squareMem_branch_split {x0 y0 w : Nat} {zw : ℂ}
    (heven : Nat.beq (Nat.mod w 2) 0 = true) (hsq : SquareMem x0 y0 w zw) :
    let hw := Nat.div w 2
    SquareMem x0 y0 hw zw ∨ SquareMem x0 (Nat.add y0 hw) hw zw ∨
    SquareMem (Nat.add x0 hw) y0 hw zw ∨ SquareMem (Nat.add x0 hw) (Nat.add y0 hw) hw zw := by
  intro hw
  have hmod0 : w % 2 = 0 := Nat.beq_eq.mp heven
  have hw2 : hw + hw = w := by
    change w / 2 + w / 2 = w
    omega
  rcases hsq with ⟨hx0, hx1, hy0, hy1⟩
  have hre_u : zw.re ≤ ((Nat.add x0 hw + hw : Nat) : ℝ) / (2 ^ 52 : ℝ) := by
    simpa [Nat.add_eq, show x0 + hw + hw = x0 + w by omega] using hx1
  have him_u : zw.im ≤ ((Nat.add y0 hw + hw : Nat) : ℝ) / (2 ^ 52 : ℝ) := by
    simpa [Nat.add_eq, show y0 + hw + hw = y0 + w by omega] using hy1
  rcases le_total zw.re (((x0 + hw : Nat) : ℝ) / (2 ^ 52 : ℝ)) with hre_lo | hre_hi <;>
    rcases le_total zw.im (((y0 + hw : Nat) : ℝ) / (2 ^ 52 : ℝ)) with him_lo | him_hi
  · exact Or.inl ⟨hx0, hre_lo, hy0, him_lo⟩
  · exact Or.inr (Or.inl ⟨hx0, hre_lo, by simpa [Nat.add_eq] using him_hi, him_u⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simpa [Nat.add_eq] using hre_hi, hre_u, hy0, him_lo⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa [Nat.add_eq] using hre_hi, hre_u,
      by simpa [Nat.add_eq] using him_hi, him_u⟩))

theorem checkDetQTree_sound {stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq : Nat}
    {boxes : BTree (BTree Nat)} {zw : ℂ}
    (hout_false : ∀ x0' y0' w', SquareMem x0' y0' w' zw →
      isOutsideDom stageKind x0' y0' w' rInNumSq rInScaleSq = false) :
    ∀ (t : QTree Nat) (x0 y0 w : Nat),
      checkDetQTree stageKind biasB modB rInNumSq rInScaleSq rOutNumSq rOutScaleSq boxes t x0 y0 w =
          true →
      SquareMem x0 y0 w zw →
      ∃ x0' y0' w' u,
        checkDetLeaf biasB modB x0' y0' w' rOutNumSq rOutScaleSq boxes u = true ∧
        SquareMem x0' y0' w' zw
  | .out, x0, y0, w, hchk, hsq => by
      simp [checkDetQTree, hout_false x0 y0 w hsq] at hchk
  | .leaf u, x0, y0, w, hchk, hsq => ⟨x0, y0, w, u, hchk, hsq⟩
  | .branch c00 c01 c10 c11, x0, y0, w, hchk, hsq => by
      simp only [checkDetQTree, Bool.and_eq_true, and_assoc] at hchk
      obtain ⟨heven, _, hc00, hc01, hc10, hc11⟩ := hchk
      rcases squareMem_branch_split heven hsq with h00 | h01 | h10 | h11
      exacts [checkDetQTree_sound hout_false c00 x0 y0 _ hc00 h00,
        checkDetQTree_sound hout_false c01 x0 _ _ hc01 h01,
        checkDetQTree_sound hout_false c10 _ y0 _ hc10 h10,
        checkDetQTree_sound hout_false c11 _ _ _ hc11 h11]

theorem stage1SquareCov_find_leaf {zw : ℂ}
    (hout_false : ∀ x0' y0' w', SquareMem x0' y0' w' zw →
      isOutsideDom 1 x0' y0' w' 1020100 100000000 = false)
    {x0 y0 w : Nat} (hcov : Stage1SquareCov x0 y0 w) (hsq : SquareMem x0 y0 w zw) :
    ∃ x0' y0' w', Stage1CellWitness x0' y0' w' ∧ SquareMem x0' y0' w' zw := by
  induction hcov with
  | out hout => simp [hout_false _ _ _ hsq] at hout
  | leaf hwit => exact ⟨_, _, _, hwit, hsq⟩
  | branch hmod _ _ _ _ _ ih00 ih01 ih10 ih11 =>
      rcases squareMem_branch_split (Nat.beq_eq.mpr hmod) hsq with h00 | h01 | h10 | h11
      exacts [ih00 h00, ih01 h01, ih10 h10, ih11 h11]

theorem stage2SquareCov_find_leaf {epPair rVert : Nat} {zw : ℂ}
    (hout_false : ∀ x0' y0' w', SquareMem x0' y0' w' zw →
      isOutsideDom 2 x0' y0' w' 13456 1000000000000 = false)
    {x0 y0 w : Nat} (hcov : Stage2SquareCov epPair rVert x0 y0 w) (hsq : SquareMem x0 y0 w zw) :
    ∃ x0' y0' w', Stage2CellWitness epPair rVert x0' y0' w' ∧ SquareMem x0' y0' w' zw := by
  induction hcov with
  | out hout => simp [hout_false _ _ _ hsq] at hout
  | leaf hwit => exact ⟨_, _, _, hwit, hsq⟩
  | branch hmod _ _ _ _ _ ih00 ih01 ih10 ih11 =>
      rcases squareMem_branch_split (Nat.beq_eq.mpr hmod) hsq with h00 | h01 | h10 | h11
      exacts [ih00 h00, ih01 h01, ih10 h10, ih11 h11]

theorem top1DSegCov_find_leaf {x : ℝ} {x0 w : Nat}
    (hcov : Top1DSegCov x0 w)
    (hlo : (x0 : ℝ) / (2 ^ 52 : ℝ) ≤ x)
    (hhi : x ≤ ((x0 + w : Nat) : ℝ) / (2 ^ 52 : ℝ)) :
    ∃ x0' w', Top1DCellWitness x0' w' ∧
      (x0' : ℝ) / (2 ^ 52 : ℝ) ≤ x ∧
      x ≤ ((x0' + w' : Nat) : ℝ) / (2 ^ 52 : ℝ) := by
  induction hcov with
  | leaf hwit => exact ⟨_, _, hwit, hlo, hhi⟩
  | @branch xb wb hmod _ _ _ ihl ihr =>
      have hmod' : wb % 2 = 0 := hmod
      have hxhw : xb + Nat.div wb 2 + Nat.div wb 2 = xb + wb := by
        change xb + wb / 2 + wb / 2 = xb + wb
        omega
      rcases le_total x (((xb + Nat.div wb 2 : Nat) : ℝ) / (2 ^ 52 : ℝ)) with hmid | hmid
      · exact ihl hlo hmid
      · exact ihr (by simpa [Nat.add_eq] using hmid) (by simpa [Nat.add_eq, hxhw] using hhi)
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge.Synth

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge.Synth
open PhotochemistrySolution.TopHad.Synth
set_option maxHeartbeats 1600000 in
-- Deep quadtree grid coverage proof term requires raised heartbeat limit.
theorem root_stage1_cov : Stage1SquareCov 0 0 457396837154816 := by
  have p0 {k x y : Nat} (u0 : (D1 k (x * 2) (y * 2) ∧ D1 k (x * 2) (y * 2 + 1)) ∧ D1 k (x * 2 + 1)
      (y * 2) ∧ D1 k (x * 2 + 1)
    (y * 2 + 1)) : D1 (k + 1) x y := d1_b u0.1.1 u0.1.2 u0.2.1 u0.2.2
  have p1 {k x y : Nat} {a0 a1 a2 : Prop} (u0 : (a0 ∧ D1 k (x * 2) (y * 2)) ∧ D1 k (x * 2)
      (y * 2 + 1) ∧ D1 k (x * 2 + 1) (y * 2))
    (u1 : (D1 k (x * 2 + 1) (y * 2 + 1) ∧ a1) ∧ a2) : D1 (k + 1) x y :=
        d1_b u0.1.2 u0.2.1 u0.2.2 u1.1.1
  have p2 {k x y : Nat} {a0 a1 : Prop} (u0 : a0 ∧ D1 k (x * 2) (y * 2) ∧ D1 k (x * 2) (y * 2 + 1))
      (u1 : (D1 k (x * 2 + 1) (y * 2) ∧
    D1 k (x * 2 + 1) (y * 2 + 1)) ∧ a1) : D1 (k + 1) x y := d1_b u0.2.1 u0.2.2 u1.1.1 u1.1.2
  exact d1_root (d1_b (d1_b (d1_b (d1_b (d1_b c1_0.1.1.1 c1_0.1.1.2 c1_0.1.2 c1_0.2.1.1) c1_0.2.1.2
      (d1_b c1_0.2.2 c1_1.1.1 c1_1.1.2
    c1_1.2.1) (d1_b c1_1.2.2.1 c1_1.2.2.2 c1_2.1.1 c1_2.1.2.1)) c1_2.1.2.2 (d1_b (p2 c1_2 c1_3)
        (p2 c1_3 c1_4) (p2 c1_4 c1_5) (p2
    c1_5 c1_6)) (d1_b (d1_b c1_6.2.1.1 c1_6.2.1.2 c1_6.2.2 c1_7.1.1.1) c1_7.1.1.2 (p1 c1_7 c1_8)
        (d1_b c1_8.1.2.1 c1_8.1.2.2
    c1_8.2.1 c1_8.2.2.1))) c1_8.2.2.2 (d1_b (d1_b (p0 c1_9) (p0 c1_10) (p0 c1_11) (p0 c1_12))
        (d1_b (p0 c1_13) (p0 c1_14) (p0 c1_15)
    (p0 c1_16)) (d1_b (p0 c1_17) (p0 c1_18) (p0 c1_19) (p0 c1_20)) (d1_b (p0 c1_21) (p0 c1_22)
        (p0 c1_23) (p0 c1_24))) (d1_b (d1_b
    (d1_b c1_25.1.1.1 c1_25.1.1.2 c1_25.1.2 c1_25.2.1.1) c1_25.2.1.2 (d1_b c1_25.2.2 c1_26.1.1
        c1_26.1.2 c1_26.2.1) (d1_b
    c1_26.2.2.1 c1_26.2.2.2 c1_27.1.1 c1_27.1.2.1)) c1_27.1.2.2 (d1_b (p2 c1_27 c1_28)
        (p2 c1_28 c1_29) (p2 c1_29 c1_30) (p2 c1_30
    c1_31)) (d1_b (d1_b c1_31.2.1.1 c1_31.2.1.2 c1_31.2.2 c1_32.1.1.1) c1_32.1.1.2 (p1 c1_32 c1_33)
        (d1_b c1_33.1.2.1 c1_33.1.2.2
    c1_33.2.1 c1_33.2.2.1)))) c1_33.2.2.2 (d1_b (d1_b (d1_b (p0 c1_34) (p0 c1_35) (p0 c1_36)
        (p0 c1_37)) (d1_b (p0 c1_38) (p0 c1_39)
    (p0 c1_40) (p0 c1_41)) (d1_b (p0 c1_42) (p0 c1_43) (p0 c1_44) (p0 c1_45)) (d1_b (p0 c1_46)
        (p0 c1_47) (p0 c1_48) (p0 c1_49)))
    (d1_b (d1_b (p0 c1_50) (p0 c1_51) (p0 c1_52) (p0 c1_53)) (d1_b (p0 c1_54) (p0 c1_55) (p0 c1_56)
        (p0 c1_57)) (d1_b (p0 c1_58) (p0
    c1_59) (p0 c1_60) (p0 c1_61)) (d1_b (p0 c1_62) (p0 c1_63) (p0 c1_64) (p0 c1_65)))
        (d1_b (d1_b (p0 c1_66) (p0 c1_67) (p0 c1_68)
    (p0 c1_69)) (d1_b (p0 c1_70) (p0 c1_71) (p0 c1_72) (p0 c1_73)) (d1_b (p0 c1_74) (p0 c1_75)
        (p0 c1_76) (p0 c1_77)) (d1_b (p0
    c1_78) (p0 c1_79) (d1_b c1_80.1.1 c1_80.1.2 c1_80.2.1.1 c1_80.2.1.2)
        (d1_b c1_80.2.2 c1_81.1.1.1 c1_81.1.1.2.1 c1_81.1.1.2.2)))
    (d1_b (d1_b (p1 c1_81 c1_82) (p1 c1_82 c1_83) (p1 c1_83 c1_84) (p1 c1_84 c1_85))
        (d1_b (p1 c1_85 c1_86) (p1 c1_86 c1_87) (p1
    c1_87 c1_88) (p1 c1_88 c1_89)) (d1_b (p1 c1_89 c1_90) (p1 c1_90 c1_91) c1_91.1.2.1 c1_91.1.2.2)
        (d1_b (d1_b c1_91.2.1
    c1_91.2.2.1 c1_91.2.2.2.1 c1_91.2.2.2.2) c1_92.1.1.1 d1_o d1_o)))
        (d1_b (d1_b (d1_b (d1_b c1_92.1.1.2.1 c1_92.1.1.2.2 c1_92.1.2
    c1_92.2.1.1) c1_92.2.1.2 (d1_b c1_92.2.2 c1_93.1.1 c1_93.1.2 c1_93.2.1)
        (d1_b c1_93.2.2.1 c1_93.2.2.2 c1_94.1.1 c1_94.1.2.1))
    c1_94.1.2.2 (d1_b (p2 c1_94 c1_95) (p2 c1_95 c1_96) (p2 c1_96 c1_97) (p2 c1_97 c1_98))
        (d1_b (d1_b c1_98.2.1.1 c1_98.2.1.2
    c1_98.2.2 c1_99.1.1.1) c1_99.1.1.2 (d1_b c1_99.1.2 c1_99.2.1 c1_99.2.2 c1_100.1.1.1)
        c1_100.1.1.2.1)) c1_100.1.1.2.2 (d1_b (d1_b
    (p1 c1_100 c1_101) (d1_b c1_101.1.2 c1_101.2.1 c1_101.2.2.1 c1_101.2.2.2)
        (d1_b c1_102.1.1 c1_102.1.2.1 c1_102.1.2.2.1 d1_o)
    c1_102.1.2.2.2) c1_102.2 d1_o d1_o) d1_o))

theorem root_stage2_cov_460 : Stage2SquareCov 460 540 0 0 687194767360 := by
  have p0 {k x y : Nat} {a0 a1 : Prop} (u0 : a0 ∧ (D2 k (x * 2) (y * 2) ∧ D2 k (x * 2)
      (y * 2 + 1) ∧ D2 k (x * 2 + 1) (y * 2)) ∧ D2
    k (x * 2 + 1) (y * 2 + 1) ∧ a1) : D2 (k + 1) x y := d2_b u0.2.1.1 u0.2.1.2.1 u0.2.1.2.2 u0.2.2.1
  have p1 {k x y : Nat} {a0 a1 a2 : Prop} (u0 : ((a0 ∧ a1 ∧ D2 k (x * 2) (y * 2)) ∧ D2 k (x * 2)
      (y * 2 + 1) ∧ D2 k (x * 2 + 1)
    (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1)) ∧ a2) : D2 (k + 1) x y :=
        d2_b u0.1.1.2.2 u0.1.2.1 u0.1.2.2.1 u0.1.2.2.2
  have p2 {k x y : Nat} {a0 a1 a2 a3 a4 a5 : Prop} (u0 : a0 ∧ a1 ∧ a2 ∧ D2 k (x * 2)
      (y * 2) ∧ D2 k (x * 2) (y * 2 + 1)) (u1 : ((D2
    k (x * 2 + 1) (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1) ∧ a3) ∧ a4) ∧ a5) : D2 (k + 1) x y :=
        d2_b u0.2.2.2.1 u0.2.2.2.2 u1.1.1.1
    u1.1.1.2.1
  have p3 {k x y : Nat} {a0 a1 a2 a3 : Prop} (u0 : (a0 ∧ a1 ∧ a2 ∧ D2 k (x * 2) (y * 2)) ∧
      (D2 k (x * 2) (y * 2 + 1) ∧ D2 k
    (x * 2 + 1) (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1)) ∧ a3) : D2 (k + 1) x y :=
        d2_b u0.1.2.2.2 u0.2.1.1 u0.2.1.2.1 u0.2.1.2.2
  have p4 {k x y : Nat} {a0 a1 a2 a3 a4 : Prop} (u0 : a0 ∧ a1 ∧ D2 k (x * 2) (y * 2) ∧ D2 k (x * 2)
      (y * 2 + 1) ∧ D2 k (x * 2 + 1)
    (y * 2)) (u1 : ((D2 k (x * 2 + 1) (y * 2 + 1) ∧ a2) ∧ a3) ∧ a4) : D2 (k + 1) x y :=
        d2_b u0.2.2.1 u0.2.2.2.1 u0.2.2.2.2 u1.1.1.1
  have p5 {k x y : Nat} {a0 a1 a2 : Prop} (u0 : ((a0 ∧ D2 k (x * 2) (y * 2) ∧ D2 k (x * 2)
      (y * 2 + 1)) ∧ D2 k (x * 2 + 1) (y * 2) ∧
    D2 k (x * 2 + 1) (y * 2 + 1) ∧ a1) ∧ a2) : D2 (k + 1) x y :=
        d2_b u0.1.1.2.1 u0.1.1.2.2 u0.1.2.1 u0.1.2.2.1
  have p6 {k x y : Nat} {a0 a1 a2 : Prop} (u0 : (a0 ∧ D2 k (x * 2) (y * 2) ∧ D2 k (x * 2)
      (y * 2 + 1) ∧ D2 k (x * 2 + 1) (y * 2)) ∧
    (D2 k (x * 2 + 1) (y * 2 + 1) ∧ a1) ∧ a2) : D2 (k + 1) x y :=
        d2_b u0.1.2.1 u0.1.2.2.1 u0.1.2.2.2 u0.2.1.1
  have p7 {k x y : Nat} {a0 a1 a2 : Prop} (u0 : a0 ∧ (a1 ∧ a2 ∧ D2 k (x * 2) (y * 2)) ∧ D2 k (x * 2)
      (y * 2 + 1) ∧ D2 k (x * 2 + 1)
    (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1)) : D2 (k + 1) x y :=
        d2_b u0.2.1.2.2 u0.2.2.1 u0.2.2.2.1 u0.2.2.2.2
  have p8 {k x y : Nat} {a0 a1 a2 a3 a4 a5 : Prop} (u0 : a0 ∧ a1 ∧ a2 ∧ a3 ∧ D2 k (x * 2) (y * 2))
      (u1 : ((D2 k (x * 2) (y * 2 + 1) ∧
    D2 k (x * 2 + 1) (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1)) ∧ a4) ∧ a5) : D2 (k + 1) x y :=
        d2_b u0.2.2.2.2 u1.1.1.1 u1.1.1.2.1
    u1.1.1.2.2
  have p9 {k x y : Nat} {a0 a1 a2 a3 : Prop} (u0 : (a0 ∧ a1 ∧ D2 k (x * 2) (y * 2) ∧ D2 k (x * 2)
      (y * 2 + 1)) ∧ (D2 k (x * 2 + 1)
    (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1) ∧ a2) ∧ a3) : D2 (k + 1) x y :=
        d2_b u0.1.2.2.1 u0.1.2.2.2 u0.2.1.1 u0.2.1.2.1
  have p10 {k x y : Nat} {a0 a1 : Prop}
      (u0 : ((D2 k (x * 2) (y * 2) ∧ D2 k (x * 2) (y * 2 + 1) ∧ D2 k (x * 2 + 1) (y * 2)) ∧ D2 k
    (x * 2 + 1) (y * 2 + 1) ∧ a0) ∧ a1) : D2 (k + 1) x y :=
        d2_b u0.1.1.1 u0.1.1.2.1 u0.1.1.2.2 u0.1.2.1
  have p11 {k x y : Nat} {a0 a1 a2 : Prop} (u0 : a0 ∧ (a1 ∧ D2 k (x * 2) (y * 2) ∧ D2 k (x * 2)
      (y * 2 + 1)) ∧ D2 k (x * 2 + 1)
    (y * 2) ∧ D2 k (x * 2 + 1) (y * 2 + 1) ∧ a2) : D2 (k + 1) x y :=
        d2_b u0.2.1.2.1 u0.2.1.2.2 u0.2.2.1 u0.2.2.2.1
  have q0 {k x y : Nat} {a0 a1 a2 a3 a4 a5 : Prop} (u0 : a0 ∧ a1 ∧ a2 ∧ D2 k (x * 2 * 2)
      (y * 2 * 2) ∧ D2 k (x * 2 * 2)
    (y * 2 * 2 + 1)) (u1 : ((D2 k (x * 2 * 2 + 1) (y * 2 * 2) ∧ D2 k (x * 2 * 2 + 1)
        (y * 2 * 2 + 1) ∧ D2 k (x * 2 * 2) ((y * 2 + 1)
    * 2)) ∧ D2 k (x * 2 * 2) ((y * 2 + 1) * 2 + 1) ∧ D2 k (x * 2 * 2 + 1)
        ((y * 2 + 1) * 2) ∧ D2 k (x * 2 * 2 + 1) ((y * 2 + 1) * 2
    + 1)) ∧ (D2 k ((x * 2 + 1) * 2) (y * 2 * 2) ∧ D2 k ((x * 2 + 1) * 2)
        (y * 2 * 2 + 1) ∧ D2 k ((x * 2 + 1) * 2 + 1) (y * 2 * 2)) ∧
    D2 k ((x * 2 + 1) * 2 + 1) (y * 2 * 2 + 1) ∧ D2 k ((x * 2 + 1) * 2)
        ((y * 2 + 1) * 2) ∧ D2 k ((x * 2 + 1) * 2) ((y * 2 + 1) * 2
    + 1)) (u2 : ((D2 k ((x * 2 + 1) * 2 + 1) ((y * 2 + 1) * 2) ∧ D2 k ((x * 2 + 1) * 2 + 1)
        ((y * 2 + 1) * 2 + 1) ∧ a3) ∧ a4) ∧ a5)
    : D2 (k + 1 + 1) x y := d2_b (p2 u0 u1) (p1 u1) (p0 u1) (p2 u1 u2)
  have q1 {k x y : Nat} {a0 a1 : Prop} (u0 : a0 ∧ (D2 k (x * 2 * 2) (y * 2 * 2) ∧ D2 k (x * 2 * 2)
      (y * 2 * 2 + 1) ∧ D2 k
    (x * 2 * 2 + 1) (y * 2 * 2)) ∧ D2 k (x * 2 * 2 + 1) (y * 2 * 2 + 1) ∧ D2 k (x * 2 * 2)
        ((y * 2 + 1) * 2) ∧ D2 k (x * 2 * 2)
    ((y * 2 + 1) * 2 + 1)) (u1 : ((D2 k (x * 2 * 2 + 1) ((y * 2 + 1) * 2) ∧ D2 k (x * 2 * 2 + 1)
        ((y * 2 + 1) * 2 + 1) ∧ D2 k
    ((x * 2 + 1) * 2) (y * 2 * 2)) ∧ D2 k ((x * 2 + 1) * 2) (y * 2 * 2 + 1) ∧ D2 k ((x * 2 + 1) *
        2 + 1) (y * 2 * 2) ∧ D2 k
    ((x * 2 + 1) * 2 + 1) (y * 2 * 2 + 1)) ∧ (D2 k ((x * 2 + 1) * 2)
        ((y * 2 + 1) * 2) ∧ D2 k ((x * 2 + 1) * 2) ((y * 2 + 1) * 2 +
    1) ∧ D2 k ((x * 2 + 1) * 2 + 1) ((y * 2 + 1) * 2)) ∧ D2 k ((x * 2 + 1) * 2 + 1)
        ((y * 2 + 1) * 2 + 1) ∧ a1)
    : D2 (k + 1 + 1) x y := d2_b (p0 u0) (p2 u0 u1) (p1 u1) (p0 u1)
  have q2 {k x y : Nat} {a0 a1 a2 : Prop}
      (u0 : ((a0 ∧ a1 ∧ D2 k (x * 2 * 2) (y * 2 * 2)) ∧ D2 k (x * 2 * 2) (y * 2 * 2 + 1) ∧ D2 k
    (x * 2 * 2 + 1) (y * 2 * 2) ∧ D2 k (x * 2 * 2 + 1) (y * 2 * 2 + 1)) ∧ (D2 k (x * 2 * 2)
        ((y * 2 + 1) * 2) ∧ D2 k (x * 2 * 2)
    ((y * 2 + 1) * 2 + 1) ∧ D2 k (x * 2 * 2 + 1) ((y * 2 + 1) * 2)) ∧ D2 k (x * 2 * 2 + 1)
        ((y * 2 + 1) * 2 + 1) ∧ D2 k ((x * 2 + 1)
    * 2) (y * 2 * 2) ∧ D2 k ((x * 2 + 1) * 2) (y * 2 * 2 + 1))
        (u1 : ((D2 k ((x * 2 + 1) * 2 + 1) (y * 2 * 2) ∧ D2 k ((x * 2 + 1) *
    2 + 1) (y * 2 * 2 + 1) ∧ D2 k ((x * 2 + 1) * 2) ((y * 2 + 1) * 2)) ∧ D2 k ((x * 2 + 1) * 2)
        ((y * 2 + 1) * 2 + 1) ∧ D2 k
    ((x * 2 + 1) * 2 + 1) ((y * 2 + 1) * 2) ∧ D2 k ((x * 2 + 1) * 2 + 1) ((y * 2 + 1) * 2 + 1)) ∧
        a2) : D2 (k + 1 + 1) x y := d2_b
    (p1 u0) (p0 u0) (p2 u0 u1) (p1 u1)
  have q3 {k x y : Nat} {a0 a1 a2 a3 a4 : Prop} (u0 : a0 ∧ a1 ∧ D2 k (x * 2 * 2)
      (y * 2 * 2) ∧ D2 k (x * 2 * 2) (y * 2 * 2 + 1) ∧ D2
    k (x * 2 * 2 + 1) (y * 2 * 2)) (u1 : ((D2 k (x * 2 * 2 + 1) (y * 2 * 2 + 1) ∧ D2 k (x * 2 * 2)
        ((y * 2 + 1) * 2) ∧ D2 k
    (x * 2 * 2) ((y * 2 + 1) * 2 + 1)) ∧ D2 k (x * 2 * 2 + 1) ((y * 2 + 1) * 2) ∧ D2 k (x * 2 * 2 +
        1) ((y * 2 + 1) * 2 + 1) ∧ D2 k
    ((x * 2 + 1) * 2) (y * 2 * 2)) ∧ (D2 k ((x * 2 + 1) * 2) (y * 2 * 2 + 1) ∧ D2 k ((x * 2 + 1) *
        2 + 1) (y * 2 * 2) ∧ D2 k
    ((x * 2 + 1) * 2 + 1) (y * 2 * 2 + 1)) ∧ D2 k ((x * 2 + 1) * 2)
        ((y * 2 + 1) * 2) ∧ D2 k ((x * 2 + 1) * 2) ((y * 2 + 1) * 2 + 1) ∧
    D2 k ((x * 2 + 1) * 2 + 1) ((y * 2 + 1) * 2))
        (u2 : ((D2 k ((x * 2 + 1) * 2 + 1) ((y * 2 + 1) * 2 + 1) ∧ a2) ∧ a3) ∧ a4)
    : D2 (k + 1 + 1) x y := d2_b (p4 u0 u1) (p5 u1) (p3 u1) (p4 u1 u2)
  exact d2_root (d2_b (d2_b (d2_b (d2_b (d2_b (d2_b c2_0.1.1.1 c2_0.1.1.2 (p6 c2_0) c2_0.2.1.2.1)
      c2_0.2.1.2.2 (q3 c2_0 c2_1 c2_2)
    (d2_b c2_2.1.1.2.1 c2_2.1.1.2.2 (p6 c2_2) c2_2.2.1.2.1)) c2_2.2.1.2.2 (d2_b (q3 c2_2 c2_3 c2_4)
        (d2_b (p5 c2_4) (p3 c2_4) (p4
    c2_4 c2_5) (p5 c2_5)) (d2_b (p3 c2_5) (p4 c2_5 c2_6) (p5 c2_6) (p3 c2_6)) (q3 c2_6 c2_7 c2_8))
        (d2_b (d2_b c2_8.1.1.2.1
    c2_8.1.1.2.2 (p6 c2_8) c2_8.2.1.2.1) c2_8.2.1.2.2 (q3 c2_8 c2_9 c2_10)
        (d2_b c2_10.1.1.2.1 c2_10.1.1.2.2 (p6 c2_10)
    c2_10.2.1.2.1))) c2_10.2.1.2.2 (d2_b (d2_b (q3 c2_10 c2_11 c2_12) (d2_b (p5 c2_12) (p3 c2_12)
        (p4 c2_12 c2_13) (p5 c2_13)) (d2_b
    (p3 c2_13) (p4 c2_13 c2_14) (p5 c2_14) (p3 c2_14)) (q3 c2_14 c2_15 c2_16))
        (d2_b (d2_b (p5 c2_16) (p3 c2_16) (p4 c2_16 c2_17)
    (p5 c2_17)) (d2_b (p3 c2_17) (p4 c2_17 c2_18) (p5 c2_18) (p3 c2_18)) (q3 c2_18 c2_19 c2_20)
        (d2_b (p5 c2_20) (p3 c2_20)
    c2_20.2.2 (p10 c2_21))) (d2_b (d2_b (p9 c2_21) (p7 c2_21) c2_22.1.1 (p6 c2_22))
        (d2_b (p11 c2_22) (p8 c2_22 c2_23) (p6 c2_23)
    (p11 c2_23)) (d2_b (p8 c2_23 c2_24) (p6 c2_24) (p11 c2_24) (p8 c2_24 c2_25)) (d2_b (p6 c2_25)
        (p11 c2_25) (p8 c2_25 c2_26) (p6
    c2_26))) (d2_b (d2_b (p11 c2_26) (p8 c2_26 c2_27) (p6 c2_27) (p11 c2_27)) (d2_b (p8 c2_27 c2_28)
        (p6 c2_28) (p11 c2_28) (p8
    c2_28 c2_29)) (d2_b (p6 c2_29) (p11 c2_29) (p8 c2_29 c2_30) (p6 c2_30)) (d2_b (p11 c2_30)
        (p8 c2_30 c2_31) (p6 c2_31) (d2_b
    c2_31.2.1.2.1 c2_31.2.1.2.2 c2_31.2.2.1 c2_31.2.2.2))))
        (d2_b (d2_b (d2_b c2_32.1.1.1 c2_32.1.1.2.1 (p1 c2_32) c2_32.2.1.1)
    c2_32.2.1.2.1 (d2_b (p7 c2_32)
        (d2_b c2_33.1.1.1 c2_33.1.1.2.1 c2_33.1.1.2.2 c2_33.1.2) c2_33.2.1 (p4 c2_33 c2_34)) (d2_b
    c2_34.1.1.2.1 c2_34.1.1.2.2 (p6 c2_34) c2_34.2.1.2.1)) c2_34.2.1.2.2 (d2_b (q3 c2_34 c2_35
        c2_36) (d2_b (p5 c2_36) (p3 c2_36)
    (p4 c2_36 c2_37) (p5 c2_37)) (d2_b (p3 c2_37) (p4 c2_37 c2_38) (p5 c2_38) (p3 c2_38))
        (q3 c2_38 c2_39 c2_40)) (d2_b (d2_b
    c2_40.1.1.2.1 c2_40.1.1.2.2 (p6 c2_40) c2_40.2.1.2.1) c2_40.2.1.2.2 (q3 c2_40 c2_41 c2_42)
        (d2_b c2_42.1.1.2.1 c2_42.1.1.2.2 (p6
    c2_42) c2_42.2.1.2.1)))) c2_42.2.1.2.2 (d2_b (d2_b (d2_b (q3 c2_42 c2_43 c2_44) (d2_b (p5 c2_44)
        (p3 c2_44) (p4 c2_44 c2_45) (p5
    c2_45)) (d2_b (p3 c2_45)
        (d2_b c2_45.2.2.1 c2_45.2.2.2.1 c2_45.2.2.2.2 c2_46.1.1) c2_46.1.2 (p0 c2_46))
        (q0 c2_46 c2_47 c2_48))
    (d2_b (q2 c2_48 c2_49) (q1 c2_49 c2_50) (q0 c2_50 c2_51 c2_52) (q2 c2_52 c2_53))
        (d2_b (q1 c2_53 c2_54) (q0 c2_54 c2_55 c2_56)
    (q2 c2_56 c2_57) (q1 c2_57 c2_58)) (d2_b (q0 c2_58 c2_59 c2_60) (q2 c2_60 c2_61)
        (q1 c2_61 c2_62) (q0 c2_62 c2_63 c2_64))) (d2_b
    (d2_b (q2 c2_64 c2_65) (q1 c2_65 c2_66) (q0 c2_66 c2_67 c2_68) (q2 c2_68 c2_69))
        (d2_b (q1 c2_69 c2_70) (q0 c2_70 c2_71 c2_72)
    (q2 c2_72 c2_73) (q1 c2_73 c2_74)) (d2_b (q0 c2_74 c2_75 c2_76) (q2 c2_76 c2_77)
        (q1 c2_77 c2_78) (q0 c2_78 c2_79 c2_80)) (d2_b
    (q2 c2_80 c2_81) (q1 c2_81 c2_82) (q0 c2_82 c2_83 c2_84) (q2 c2_84 c2_85)))
        (d2_b (d2_b (q1 c2_85 c2_86) (q0 c2_86 c2_87 c2_88)
    (q2 c2_88 c2_89) (q1 c2_89 c2_90)) (d2_b (q0 c2_90 c2_91 c2_92) (q2 c2_92 c2_93)
        (q1 c2_93 c2_94) (q0 c2_94 c2_95 c2_96)) (d2_b
    (q2 c2_96 c2_97) (q1 c2_97 c2_98) (q0 c2_98 c2_99 c2_100) (q2 c2_100 c2_101))
        (d2_b (q1 c2_101 c2_102) (q0 c2_102 c2_103 c2_104)
    (q2 c2_104 c2_105) (q1 c2_105 c2_106))) (d2_b (d2_b (q0 c2_106 c2_107 c2_108) (q2 c2_108 c2_109)
        (q1 c2_109 c2_110) (q0 c2_110
    c2_111 c2_112)) (d2_b (q2 c2_112 c2_113) (q1 c2_113 c2_114) (q0 c2_114 c2_115 c2_116)
        (q2 c2_116 c2_117)) (d2_b (q1 c2_117
    c2_118) (q0 c2_118 c2_119 c2_120) (q2 c2_120 c2_121) (q1 c2_121 c2_122))
        (d2_b (q0 c2_122 c2_123 c2_124) (q2 c2_124 c2_125) (q1
    c2_125 c2_126) (d2_b (p2 c2_126 c2_127) (p1 c2_127) (p0 c2_127)
        (d2_b c2_127.2.2.2.1 c2_127.2.2.2.2 c2_128.1.1.1
    c2_128.1.1.2)))))
        (d2_b (d2_b (d2_b (d2_b c2_128.1.2.1 c2_128.1.2.2.1 (p3 c2_128) c2_128.2.2.1) c2_128.2.2.2.1
        (d2_b (p8 c2_128
    c2_129) (p6 c2_129) (p11 c2_129) (p8 c2_129 c2_130))
        (d2_b c2_130.1.2.1 c2_130.1.2.2.1 (p3 c2_130) c2_130.2.2.1)) c2_130.2.2.2.1
    (d2_b (d2_b (p8 c2_130 c2_131) (p6 c2_131) (p11 c2_131) (p8 c2_131 c2_132)) (d2_b (p6 c2_132)
        (p11 c2_132) (p8 c2_132 c2_133)
    (p6 c2_133)) (d2_b (p11 c2_133) (p8 c2_133 c2_134) (p6 c2_134) (p11 c2_134))
        (d2_b (p8 c2_134 c2_135) (p6 c2_135) (p11 c2_135)
    (p8 c2_135 c2_136)))
        (d2_b (d2_b c2_136.1.2.1 c2_136.1.2.2.1 (p3 c2_136) c2_136.2.2.1) c2_136.2.2.2.1
        (d2_b (p8 c2_136 c2_137)
    (p6 c2_137) (p11 c2_137) (p8 c2_137 c2_138))
        (d2_b c2_138.1.2.1 c2_138.1.2.2.1 (p3 c2_138) c2_138.2.2.1))) c2_138.2.2.2.1 (d2_b
    (d2_b (d2_b (p8 c2_138 c2_139) (p6 c2_139) (p11 c2_139) (p8 c2_139 c2_140)) (d2_b (p6 c2_140)
        (p11 c2_140) (p8 c2_140 c2_141)
    (p6 c2_141)) (d2_b (p11 c2_141) (p8 c2_141 c2_142) (p6 c2_142) (p11 c2_142))
        (d2_b (p8 c2_142 c2_143) (p6 c2_143) (p11 c2_143)
    (p8 c2_143 c2_144))) (d2_b (d2_b (p6 c2_144) (p11 c2_144) (p8 c2_144 c2_145) (p6 c2_145))
        (d2_b (p11 c2_145) (p8 c2_145 c2_146)
    (p6 c2_146) (p11 c2_146)) (d2_b (p8 c2_146 c2_147) (p6 c2_147) (p11 c2_147) (p8 c2_147 c2_148))
        (d2_b (p6 c2_148) (p11 c2_148)
    (p8 c2_148 c2_149) (p6 c2_149))) (d2_b (d2_b (p11 c2_149) (p8 c2_149 c2_150) (p6 c2_150)
        (p11 c2_150)) (d2_b (p8 c2_150 c2_151)
    (p6 c2_151) (p11 c2_151) (p8 c2_151 c2_152)) (d2_b (p6 c2_152) (p11 c2_152) (p8 c2_152 c2_153)
        (p6 c2_153)) (d2_b (p11 c2_153)
    (p8 c2_153 c2_154) (p6 c2_154) (p11 c2_154))) (d2_b (d2_b (p8 c2_154 c2_155) (p6 c2_155)
        (p11 c2_155) (p8 c2_155 c2_156)) (d2_b
    (p6 c2_156) (p11 c2_156) (p8 c2_156 c2_157) (p6 c2_157)) (d2_b (p11 c2_157) (p8 c2_157 c2_158)
        (p6 c2_158) (p11 c2_158)) (d2_b
    (p8 c2_158 c2_159) (p6 c2_159) (p11 c2_159) (p8 c2_159 c2_160))))
        (d2_b (d2_b (d2_b c2_160.1.2.1 c2_160.1.2.2.1 (p3 c2_160)
    c2_160.2.2.1) c2_160.2.2.2.1 (d2_b (p8 c2_160 c2_161) (p6 c2_161) (p11 c2_161)
        (p8 c2_161 c2_162)) (d2_b c2_162.1.2.1
    c2_162.1.2.2.1 (p3 c2_162) c2_162.2.2.1)) c2_162.2.2.2.1 (d2_b (d2_b (p8 c2_162 c2_163)
        (p6 c2_163) (p11 c2_163) (p8 c2_163
    c2_164)) (d2_b (p6 c2_164) (p11 c2_164) (p8 c2_164 c2_165) (p6 c2_165)) (d2_b (p11 c2_165)
        (p8 c2_165 c2_166) (p6 c2_166) (p11
    c2_166)) (d2_b (p8 c2_166 c2_167) (p6 c2_167) (p11 c2_167) (p8 c2_167 c2_168)))
        (d2_b (d2_b c2_168.1.2.1 c2_168.1.2.2.1 (p3
    c2_168) c2_168.2.2.1) c2_168.2.2.2.1 (d2_b (p8 c2_168 c2_169) (p6 c2_169) (p11 c2_169)
        (p8 c2_169 c2_170)) (d2_b c2_170.1.2.1
    c2_170.1.2.2.1 (p3 c2_170) c2_170.2.2.1))))) c2_170.2.2.2.1
        (d2_b (d2_b (d2_b (d2_b (d2_b (p8 c2_170 c2_171) (p6 c2_171) (p11
    c2_171) (p8 c2_171 c2_172)) (d2_b c2_172.1.2 (p0 c2_172) (p2 c2_172 c2_173) (p1 c2_173))
        (d2_b c2_173.2.1 (p4 c2_173 c2_174) (p5
    c2_174) (p3 c2_174)) (q3 c2_174 c2_175 c2_176)) (d2_b (d2_b (p5 c2_176) (p3 c2_176)
        (p4 c2_176 c2_177) (p5 c2_177)) (d2_b (p3
    c2_177) (p4 c2_177 c2_178) (p5 c2_178) (p3 c2_178)) (q3 c2_178 c2_179 c2_180) (d2_b (p5 c2_180)
        (p3 c2_180) (p4 c2_180 c2_181)
    (p5 c2_181))) (d2_b (d2_b (p3 c2_181) (p4 c2_181 c2_182) (p5 c2_182) (p3 c2_182))
        (q3 c2_182 c2_183 c2_184) (d2_b (p5 c2_184)
    (p3 c2_184) (p4 c2_184 c2_185) (p5 c2_185)) (d2_b (p3 c2_185) (p4 c2_185 c2_186) (p5 c2_186)
        (p3 c2_186))) (d2_b (q3 c2_186
    c2_187 c2_188) (d2_b (p5 c2_188) (p3 c2_188) (p4 c2_188 c2_189) (p5 c2_189)) (d2_b (p3 c2_189)
        (p4 c2_189 c2_190) (p5 c2_190)
    (p3 c2_190)) (q3 c2_190 c2_191 c2_192)))
        (d2_b (d2_b (d2_b (p5 c2_192) (p3 c2_192) (p4 c2_192 c2_193) (p5 c2_193)) (d2_b (p3
    c2_193) (p4 c2_193 c2_194)
        (d2_b c2_194.1.1.2.1 c2_194.1.1.2.2 c2_194.1.2.1 c2_194.1.2.2) c2_194.2.1)
        (q3 c2_194 c2_195 c2_196)
    (d2_b (p5 c2_196) (p3 c2_196) (p4 c2_196 c2_197) (p5 c2_197)))
        (d2_b (d2_b (p3 c2_197) (p4 c2_197 c2_198) (p5 c2_198) (p3
    c2_198)) (q3 c2_198 c2_199 c2_200) (d2_b (p5 c2_200) (p3 c2_200) (p4 c2_200 c2_201) (p5 c2_201))
        (d2_b (p3 c2_201) (p4 c2_201
    c2_202) (p5 c2_202) (p3 c2_202))) (d2_b (q3 c2_202 c2_203 c2_204) (d2_b (p5 c2_204) (p3 c2_204)
        (p4 c2_204 c2_205) (p5 c2_205))
    (d2_b (p3 c2_205) (p4 c2_205 c2_206) (p5 c2_206) (p3 c2_206)) (q3 c2_206 c2_207 c2_208))
        (d2_b (d2_b (p5 c2_208) (p3 c2_208) (p4
    c2_208 c2_209) (p5 c2_209)) (d2_b (p3 c2_209) (p4 c2_209 c2_210) (p5 c2_210) (p3 c2_210))
        (q3 c2_210 c2_211 c2_212) (d2_b (p5
    c2_212) (p3 c2_212) (p4 c2_212 c2_213) (p5 c2_213))))
        (d2_b (d2_b (d2_b (p3 c2_213) (p4 c2_213 c2_214) (p5 c2_214) (p3 c2_214))
    (d2_b (p4 c2_214 c2_215) (p5 c2_215) (p3 c2_215)
        (d2_b c2_215.2.2.1 c2_215.2.2.2.1 c2_215.2.2.2.2 c2_216.1.1)) (d2_b c2_216.1.2
    (d2_b c2_216.2.1.1 c2_216.2.1.2.1 c2_216.2.1.2.2 c2_216.2.2) c2_217.1.1 (p6 c2_217))
        (d2_b (p11 c2_217) (p8 c2_217 c2_218) (p6
    c2_218) (p11 c2_218))) (d2_b (d2_b (p8 c2_218 c2_219) (p6 c2_219) (p11 c2_219)
        (p8 c2_219 c2_220)) (d2_b (p6 c2_220) (p11
    c2_220) (p8 c2_220 c2_221) (p6 c2_221)) (d2_b (p11 c2_221) (p8 c2_221 c2_222) (p6 c2_222)
        (p11 c2_222)) (d2_b (p8 c2_222 c2_223)
    (p6 c2_223) (p11 c2_223) (p8 c2_223 c2_224))) (d2_b (d2_b (p6 c2_224) (p11 c2_224)
        (p8 c2_224 c2_225) (p6 c2_225)) (d2_b (p11
    c2_225) (p8 c2_225 c2_226) (p6 c2_226)
        (d2_b c2_226.2.1.2.1 c2_226.2.1.2.2 c2_226.2.2.1 c2_226.2.2.2)) (d2_b c2_227.1.1 (d2_b
    c2_227.1.2.1 c2_227.1.2.2.1 c2_227.1.2.2.2 c2_227.2.1) c2_227.2.2 (p10 c2_228))
        (d2_b (p9 c2_228) (p7 c2_228) (p10 c2_229) (p9
    c2_229))) (d2_b (d2_b (p7 c2_229) (p10 c2_230) (p9 c2_230) (p7 c2_230)) (d2_b (p10 c2_231)
        (p9 c2_231) (p7 c2_231) (p10 c2_232))
    (d2_b (p9 c2_232) (p7 c2_232) (p10 c2_233) (p9 c2_233)) (d2_b (p7 c2_233) (p10 c2_234)
        (p9 c2_234) (p7 c2_234)))) (d2_b (d2_b
    (d2_b (p10 c2_235) (p9 c2_235) (p7 c2_235) (p10 c2_236)) (d2_b (p9 c2_236) (p7 c2_236)
        (p10 c2_237) (p9 c2_237)) (d2_b (p7
    c2_237) (p10 c2_238) (p9 c2_238) (p7 c2_238)) (d2_b (p10 c2_239) (p9 c2_239) (p7 c2_239)
        (p10 c2_240))) (d2_b (d2_b (p9 c2_240)
    (p7 c2_240) (p10 c2_241) (p9 c2_241)) (d2_b (p7 c2_241) (p10 c2_242) (p9 c2_242) (p7 c2_242))
        (d2_b (p10 c2_243) (p9 c2_243) (p7
    c2_243) (p10 c2_244)) (d2_b (p9 c2_244) (p7 c2_244) (p10 c2_245) (p9 c2_245)))
        (d2_b (d2_b (p7 c2_245) (p10 c2_246) (p9 c2_246)
    (p7 c2_246)) (d2_b (p10 c2_247) (p9 c2_247) (p7 c2_247) (p10 c2_248)) (d2_b (p9 c2_248)
        (p7 c2_248) c2_249.1.1 c2_249.1.2) (d2_b
    (p0 c2_249)
        (d2_b c2_249.2.2.2.1 c2_249.2.2.2.2 c2_250.1.1.1 c2_250.1.1.2) c2_250.1.2.1 c2_250.1.2.2))
        (d2_b (q1 c2_250 c2_251)
    (q0 c2_251 c2_252 c2_253) (d2_b (p1 c2_253) c2_253.2.1.1 c2_253.2.1.2 d2_o) c2_253.2.2)))
        (d2_b (d2_b (d2_b (d2_b (p10 c2_254)
    (p9 c2_254) (p7 c2_254) (p10 c2_255)) (d2_b (p9 c2_255) (p7 c2_255) (p10 c2_256) (p9 c2_256))
        (d2_b (p7 c2_256) (p10 c2_257) (p9
    c2_257) (p7 c2_257)) (d2_b (p10 c2_258) (p9 c2_258) (p7 c2_258) (p10 c2_259)))
        (d2_b (d2_b (p9 c2_259) (p7 c2_259) (p10 c2_260)
    (p9 c2_260)) (d2_b (p7 c2_260) (p10 c2_261) (p9 c2_261) (p7 c2_261)) (d2_b (p10 c2_262)
        (p9 c2_262) (p7 c2_262) (p10 c2_263))
    (d2_b (p9 c2_263) (p7 c2_263) (p10 c2_264) (p9 c2_264))) (d2_b (d2_b (p7 c2_264) (p10 c2_265)
        (p9 c2_265) (p7 c2_265)) (d2_b
    (p10 c2_266) (p9 c2_266) (p7 c2_266) (p10 c2_267)) (d2_b (p9 c2_267) (p7 c2_267) (p10 c2_268)
        (p9 c2_268)) (d2_b (p7 c2_268)
    (p10 c2_269) (p9 c2_269) (p7 c2_269))) (d2_b (d2_b (p10 c2_270) (p9 c2_270) (p7 c2_270)
        (p10 c2_271)) (d2_b (p9 c2_271) (p7
    c2_271) (p10 c2_272) (p9 c2_272)) (d2_b (p7 c2_272) (p10 c2_273) (p9 c2_273) (p7 c2_273))
        (d2_b (p10 c2_274) (p9 c2_274) (p7
    c2_274) (p10 c2_275)))) (d2_b (d2_b (d2_b (p9 c2_275) (p7 c2_275) (p10 c2_276) (p9 c2_276))
        (d2_b (p7 c2_276) (p10 c2_277) (p9
    c2_277) (p7 c2_277)) (d2_b (p10 c2_278) (p9 c2_278) (p7 c2_278) (p10 c2_279)) (d2_b (p9 c2_279)
        (p7 c2_279) (p10 c2_280) (p9
    c2_280))) (d2_b (d2_b (p7 c2_280) (p10 c2_281) (p9 c2_281) (p7 c2_281)) (d2_b (p10 c2_282)
        (p9 c2_282) (p7 c2_282) (p10 c2_283))
    (d2_b (p9 c2_283) (p7 c2_283) (p10 c2_284) (p9 c2_284)) (d2_b (p7 c2_284) (p10 c2_285)
        (p9 c2_285) (p7 c2_285))) (d2_b (d2_b
    (p10 c2_286) (p9 c2_286) (p7 c2_286) (p10 c2_287)) (d2_b (p9 c2_287) (p7 c2_287) (p10 c2_288)
        (p9 c2_288)) (d2_b (p7 c2_288)
    (p10 c2_289) (p9 c2_289) (p7 c2_289)) (d2_b (p10 c2_290) (p9 c2_290) (p7 c2_290) (p10 c2_291)))
        (d2_b (d2_b (p9 c2_291) (p7
    c2_291) (p10 c2_292) (p9 c2_292)) (d2_b (p7 c2_292) c2_293.1.1 c2_293.1.2 c2_293.2.1.1)
        (d2_b (d2_b c2_293.2.1.2.1
    c2_293.2.1.2.2 c2_293.2.2.1 c2_293.2.2.2) c2_294.1.1 c2_294.1.2.1 c2_294.1.2.2.1)
        c2_294.1.2.2.2)) (d2_b (d2_b (q1 c2_294
    c2_295) (q0 c2_295 c2_296 c2_297) (q2 c2_297 c2_298) (q1 c2_298 c2_299))
        (d2_b (q0 c2_299 c2_300 c2_301) (q2 c2_301 c2_302)
    (d2_b (p0 c2_302) (p2 c2_302 c2_303) (p1 c2_303) c2_303.2.1)
        (d2_b (p4 c2_303 c2_304) c2_304.1.1.2 c2_304.1.2.1 d2_o)) (d2_b
    (d2_b (p9 c2_304) (p7 c2_304) c2_305.1.1 c2_305.1.2.1)
        (d2_b (d2_b c2_305.1.2.2 c2_305.2.1.1 c2_305.2.1.2.1 c2_305.2.1.2.2)
    c2_305.2.2.1 c2_305.2.2.2 d2_o) d2_o d2_o) c2_306.1.1.1)
        (d2_b (d2_b (d2_b (p5 c2_306) (p3 c2_306) (p4 c2_306 c2_307)
    c2_307.1.1.2)
        (d2_b c2_307.1.2 c2_307.2.1.1 c2_307.2.1.2.1 d2_o) c2_307.2.1.2.2 d2_o) d2_o d2_o d2_o))
        (d2_b (d2_b (d2_b (d2_b
    c2_307.2.2 c2_308.1.1 d2_o d2_o) (d2_b c2_308.1.2 c2_308.2.1 d2_o d2_o) d2_o d2_o)
        (d2_b c2_308.2.2 c2_309.1.1 d2_o d2_o) d2_o
    d2_o) d2_o d2_o d2_o) d2_o)
        (d2_b (d2_b (d2_b (d2_b (d2_b c2_309.1.2.1 c2_309.1.2.2.1 (p3 c2_309) c2_309.2.2.1)
        c2_309.2.2.2.1
    (d2_b (p8 c2_309 c2_310) (p6 c2_310)
        (p11 c2_310) c2_310.2.2.2.2) c2_311.1) c2_311.2.1 c2_311.2.2 d2_o) d2_o d2_o d2_o) d2_o
    d2_o d2_o))
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge.Synth

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge.Synth
open scoped TopHad.Synth Matrix Matrix.Norms.L2Operator BigOperators Circuit.Notation
open TopHad.Synth Real Matrix ComplexConjugate Operator QProg DynamicCircuit Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.GQSP
attribute [local simp]
  sNeg_toInt sAdd_toInt sSub_toInt sMul_toInt sAbs_toInt sintMax_toInt sMin_toInt
  unbiasS_toInt fzNeg_toCyc fzMul_toCyc gate1_isOneQubit


theorem checkDetCore_geom_sound {rNumSq rScaleSq : Nat} {dxMax dyMax dotMin : SInt} {wc zw : ℂ}
    (hrScale : 0 < rScaleSq)
    (hdx : |(2 ^ 52 : ℝ) * (zw.re - wc.re)| ≤ (dxMax.toInt : ℝ))
    (hdy : |(2 ^ 52 : ℝ) * (zw.im - wc.im)| ≤ (dyMax.toInt : ℝ))
    (hdot_min : (dotMin.toInt : ℝ) ≤ (2 ^ 52 : ℝ) ^ 2 * (1 + wc.re * zw.re + wc.im * zw.im))
    (hdot_pos : sPos dotMin = true)
    (hle_s : sLe (sMul (sMul (sAdd (sMul dxMax dxMax) (sMul dyMax dyMax)) ⟨false, rScaleSq⟩)
        (sMul boxScaleS boxScaleS))
      (sMul ⟨false, rNumSq⟩ (sMul dotMin dotMin)) = true) :
    0 < 1 + wc.re * zw.re + wc.im * zw.im ∧
    ((zw.re - wc.re) ^ 2 + (zw.im - wc.im) ^ 2) / (1 + wc.re * zw.re + wc.im * zw.im) ^ 2 ≤
        (rNumSq : ℝ) / (rScaleSq : ℝ) := by
  set BS : ℝ := 2 ^ 52
  have hBS2 : 0 < BS ^ 2 := by positivity
  have hbs_int : (boxScaleS.toInt : ℝ) = BS := by norm_num [boxScaleS, SInt.toInt, BS]
  have hdot_int_pos : 0 < (dotMin.toInt : ℝ) := by exact_mod_cast (sPos_iff dotMin).mp hdot_pos
  have h1dot_pos : 0 < 1 + wc.re * zw.re + wc.im * zw.im :=
    pos_of_mul_pos_right (lt_of_lt_of_le hdot_int_pos hdot_min) hBS2.le
  refine ⟨h1dot_pos, (div_le_div_iff₀ (sq_pos_of_pos h1dot_pos) (Nat.cast_pos.mpr hrScale)).mpr ?_⟩
  have hle_r : (((dxMax.toInt : ℝ) ^ 2 + (dyMax.toInt : ℝ) ^ 2) * (rScaleSq : ℝ)) * BS ^ 2 ≤
      (rNumSq : ℝ) * (dotMin.toInt : ℝ) ^ 2 := by
    have hz : (((sMul (sMul (sAdd (sMul dxMax dxMax) (sMul dyMax dyMax)) ⟨false, rScaleSq⟩)
        (sMul boxScaleS boxScaleS)).toInt : ℤ) : ℝ) ≤
        (((sMul ⟨false, rNumSq⟩ (sMul dotMin dotMin)).toInt : ℤ) : ℝ) := by
      exact_mod_cast (sLe_iff _ _).mp hle_s
    simp only [sMul_toInt, sAdd_toInt, Int.cast_mul, Int.cast_add] at hz
    simpa only [hbs_int, show (⟨false, rScaleSq⟩ : SInt).toInt = (rScaleSq : ℤ) from rfl,
      show (⟨false, rNumSq⟩ : SInt).toInt = (rNumSq : ℤ) from rfl, Int.cast_natCast, sq] using hz
  have h1 := sq_abs (BS * (zw.re - wc.re)) ▸ (sq_le_sq₀ (abs_nonneg _)
    ((abs_nonneg _).trans hdx)).mpr hdx
  have h2 := sq_abs (BS * (zw.im - wc.im)) ▸ (sq_le_sq₀ (abs_nonneg _)
    ((abs_nonneg _).trans hdy)).mpr hdy
  have hdist_le : BS ^ 2 * ((zw.re - wc.re) ^ 2 + (zw.im - wc.im) ^ 2) ≤
      (dxMax.toInt : ℝ) ^ 2 + (dyMax.toInt : ℝ) ^ 2 := by nlinarith
  have hdot_sq : (dotMin.toInt : ℝ) ^ 2 ≤ BS ^ 4 * (1 + wc.re * zw.re + wc.im * zw.im) ^ 2 := by
    nlinarith [(sq_le_sq₀ hdot_int_pos.le (by nlinarith)).mpr hdot_min]
  refine le_of_mul_le_mul_left (a := BS ^ 4) ?_ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdist_le
      (Nat.cast_nonneg rScaleSq)) hBS2.le,
    hle_r, hdot_sq, (rNumSq.cast_nonneg : (0 : ℝ) ≤ rNumSq)]

theorem checkDetBox1D_geom_sound {x0 w rNumSq rScaleSq : Nat} {rawBox : Box2DS} {sym : Nat}
    {wc zw : ℂ} (hchk : checkDetBox1D x0 w rNumSq rScaleSq rawBox sym = true)
    (hrScale : 0 < rScaleSq) (hmem_wb : (applyD8Box rawBox sym).Mem wc)
    (hzw_re0 : (x0 : ℝ) / (2 ^ 52 : ℝ) ≤ zw.re) (hzw_re1 : zw.re ≤ ((x0 + w : Nat) : ℝ) /
    (2 ^ 52 : ℝ)) (hzw_im : zw.im = 0) : 0 < 1 + wc.re * zw.re + wc.im * zw.im ∧
    ((zw.re - wc.re) ^ 2 + (zw.im - wc.im) ^ 2) / (1 + wc.re * zw.re + wc.im * zw.im) ^ 2 ≤
    (rNumSq : ℝ) / (rScaleSq : ℝ) := by
  simp only [checkDetBox1D, Bool.and_eq_true] at hchk
  obtain ⟨_, hdot_pos, hle_s⟩ := hchk
  set BS : ℝ := 2 ^ 52
  have hBS_pos : 0 < BS := by positivity
  have hbs_int : (boxScaleS.toInt : ℝ) = BS := by norm_num [boxScaleS, SInt.toInt, BS]
  set x0s : SInt := ⟨false, x0⟩
  set x1s : SInt := ⟨false, Nat.add x0 w⟩
  rcases hmem_wb with ⟨hwx0, hwx1, hwy0, hwy1⟩
  have hzx0 : (x0s.toInt : ℝ) ≤ BS * zw.re := by
    simpa [x0s, SInt.toInt] using (div_le_iff₀' hBS_pos).mp hzw_re0
  have hzx1 : BS * zw.re ≤ (x1s.toInt : ℝ) := by
    simpa [x1s, SInt.toInt, Nat.add_eq] using (le_div_iff₀' hBS_pos).mp hzw_re1
  have hwx0' := (div_le_iff₀' hBS_pos).mp hwx0
  have hwx1' := (le_div_iff₀' hBS_pos).mp hwx1
  refine checkDetCore_geom_sound hrScale ?_ ?_ ?_ hdot_pos hle_s
  · simpa [mul_sub] using interval_abs_diff_le hzx0 hzx1 hwx0' hwx1'
  · rw [hzw_im, zero_sub, mul_neg, abs_neg]
    refine (interval_abs_le_max_abs ((div_le_iff₀' hBS_pos).mp hwy0)
      ((le_div_iff₀' hBS_pos).mp hwy1)).trans ?_
    rw [max_comm]
    simp
  · have hpx := interval_prod_ge_min4 hzx0 hzx1 hwx0' hwx1'
    simp [sMin4, hbs_int, hzw_im, ← sq]
    nlinarith

/-!
### Part 3. Word Peeling (`bodyFuseOut`, `bodyFuseIn` ) & 5-Gate Seam Collapse (`seam5_collapse`)
-/

def bodyFuseOut (w : Nat) : Circuit 1 :=
  let cFirst := Nat.mod w 16
  let m0 := Nat.div w 256
  let c0 := (.identity : Circuit 1) ;;ᶜ sylCircuit cFirst
  let q1 := mid12Circuit (m0, c0)
  let q2 := mid12Circuit q1
  let q3 := mid12Circuit q2
  let q4 := mid12Circuit q3
  q4.2

theorem gate1_h_eval_hadamard2 : (gate1 .h).eval.1 = hadamard2 := by
  rw [gate1_h_eval]; unfold hadamard2 invSqrtTwo
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [one_div]

theorem decodeWord2Bit_fuseOut_peel {w : Nat} (hfo : isFuseOutWord w = true)
    (hc1 : (CircExt.isOneQubitCircuit (decodeWord2Bit w)) = true)
    (hcToff : (decodeWord2Bit w).count PrimitiveGate.TOFF = 0) : ∃ p1 : Nat, p1 < 8 ∧ p1 % 2 = 1 ∧
    (CircExt.isOneQubitCircuit (bodyFuseOut w)) = true ∧ (decodeWord2Bit w).count PrimitiveGate.T =
    (bodyFuseOut w).count PrimitiveGate.T + 1 ∧ (bodyFuseOut w).count PrimitiveGate.TOFF = 0 ∧
    (decodeWord2Bit w).eval.1 = hadamard2 * ((phaseGate1 p1).eval.1 * (bodyFuseOut w).eval.1) := by
  unfold isFuseOutWord at hfo; dsimp only at hfo;
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfo; obtain ⟨hw0, hcl_or⟩ := hfo
  set cl := Nat.mod (Nat.div w 16) 16
  have hcl_cases : cl = 2 ∨ cl = 4 ∨ cl = 6 ∨ cl = 8 := by
    simp only [Bool.or_eq_true, Nat.beq_eq] at hcl_or
    rcases hcl_or with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hdec : decodeWord2Bit w = bodyFuseOut w ;;ᶜ sylCircuit cl := by
    unfold decodeWord2Bit bodyFuseOut; simp [hw0, cl]
  set p1 := cl - 1
  have hp1_lt : p1 < 8 ∧ p1 % 2 = 1 ∧ sylCircuit cl = phaseGate1 p1 ;;ᶜ gate1 .h := by
    rcases hcl_cases with h | h | h | h <;>
      (dsimp [p1]; rw [h]; exact ⟨by decide, by decide, rfl⟩)
  obtain ⟨hlt, hodd, hsyl⟩ :=
      hp1_lt; rw [hdec, hsyl] at hc1 hcToff; simp only [CircExt.isOneQubitCircuit,
      Bool.and_eq_true] at hc1; obtain ⟨_, hp_T, _, _⟩ :=
      phaseGate1_props hlt; refine ⟨p1, hlt, hodd, hc1.1, ?_, ?_, ?_⟩
  · rw [hdec, hsyl];
    change (bodyFuseOut w).count PrimitiveGate.T + ((phaseGate1 p1).count PrimitiveGate.T +
        (gate1 .h).count PrimitiveGate.T) = (bodyFuseOut w).count PrimitiveGate.T +
        1; have hhT : (gate1 .h).count PrimitiveGate.T = 0 := rfl; rw [hp_T, hodd, hhT]
  · change (bodyFuseOut w).count PrimitiveGate.TOFF +
        ((phaseGate1 p1).count PrimitiveGate.TOFF + (gate1 .h).count PrimitiveGate.TOFF) =
            0 at hcToff
    omega
  · rw [hdec, hsyl];
    simp only [Circuit.eval_seq, Submonoid.coe_mul, gate1_h_eval_hadamard2, Matrix.mul_assoc]
def PrefixRel (pref : Circuit 1) (pL pR : Nat × Circuit 1) : Prop :=
    pL.1 = pR.1 ∧ (CircExt.isOneQubitCircuit pL.2) =
        ((CircExt.isOneQubitCircuit pref) && (CircExt.isOneQubitCircuit pR.2)) ∧
    pL.2.count PrimitiveGate.T = pref.count PrimitiveGate.T + pR.2.count PrimitiveGate.T ∧
    pL.2.count PrimitiveGate.TOFF = pref.count PrimitiveGate.TOFF + pR.2.count PrimitiveGate.TOFF ∧
    pL.2.eval.1 = pR.2.eval.1 * pref.eval.1
theorem mid1Circuit_prefixRel {pref : Circuit 1} {pL pR : Nat × Circuit 1}
    (h : PrefixRel pref pL pR) : PrefixRel pref (mid1Circuit pL) (mid1Circuit pR) := by
  rcases pL with ⟨mL, cL⟩
  rcases pR with ⟨mR, cR⟩
  obtain ⟨hm, h1q, hT, hToff, hev⟩ :=
      h; dsimp only at hm h1q hT hToff hev; subst hm; unfold mid1Circuit; dsimp only
  cases Nat.ble mL 1
  · dsimp only; refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · simp only [CircExt.isOneQubitCircuit, h1q, Bool.and_assoc]
    · change cL.count PrimitiveGate.T + _ = pref.count PrimitiveGate.T + (cR.count PrimitiveGate.T +
          _); omega
    · change cL.count PrimitiveGate.TOFF + _ = pref.count PrimitiveGate.TOFF +
          (cR.count PrimitiveGate.TOFF + _); omega
    · simp only [Circuit.eval_seq, Submonoid.coe_mul, hev, Matrix.mul_assoc]
  · exact ⟨rfl, h1q, hT, hToff, hev⟩

theorem mid4Circuit_prefixRel {pref : Circuit 1} {pL pR : Nat × Circuit 1}
    (h : PrefixRel pref pL pR) : PrefixRel pref (mid4Circuit pL) (mid4Circuit pR) := by
  rcases pL with ⟨mL, cL⟩
  rcases pR with ⟨mR, cR⟩
  have hm : mL = mR := h.1; subst hm; unfold mid4Circuit; dsimp only
  cases Nat.ble mL 1
  · exact mid1Circuit_prefixRel (mid1Circuit_prefixRel (mid1Circuit_prefixRel (mid1Circuit_prefixRel
        h)))
  · exact h

theorem mid12Circuit_prefixRel {pref : Circuit 1} {pL pR : Nat × Circuit 1}
    (h : PrefixRel pref pL pR) : PrefixRel pref (mid12Circuit pL) (mid12Circuit pR) :=
    mid4Circuit_prefixRel (mid4Circuit_prefixRel (mid4Circuit_prefixRel h))
def restAfterFirstMid1 (m1 cLast : Nat) (init : Circuit 1) : Circuit 1 :=
  let r1 := mid1Circuit (mid1Circuit (mid1Circuit (m1, init)))
  let q1 := mid4Circuit (mid4Circuit r1)
  let q2 := mid12Circuit q1
  let q3 := mid12Circuit q2
  let q4 := mid12Circuit q3
  q4.2 ;;ᶜ sylCircuit cLast

def bodyFuseIn (w : Nat) : Circuit 1 :=
    restAfterFirstMid1 (Nat.div (Nat.div w 256) 4) (Nat.mod (Nat.div w 16) 16) (gate1 .h)
theorem decodeWord2Bit_fuseIn_peel {w : Nat} (hfi : isFuseInWord w = true)
    (hc1 : (CircExt.isOneQubitCircuit (decodeWord2Bit w)) = true)
    (hcToff : (decodeWord2Bit w).count PrimitiveGate.TOFF = 0) : ∃ p0 : Nat, p0 < 8 ∧ p0 % 2 = 1 ∧
    (CircExt.isOneQubitCircuit (bodyFuseIn w)) = true ∧ (decodeWord2Bit w).count PrimitiveGate.T =
        1 +
    (bodyFuseIn w).count PrimitiveGate.T ∧ (bodyFuseIn w).count PrimitiveGate.TOFF = 0 ∧
    (decodeWord2Bit w).eval.1 = (bodyFuseIn w).eval.1 * ((phaseGate1 p0).eval.1 * hadamard2) := by
  unfold isFuseInWord at hfi;
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq, and_assoc] at hfi;
  obtain ⟨hw0, hcF1, hm0_ble⟩ := hfi;
  have hm0_ge4 : 4 ≤ Nat.div w 256 := (nat_ble_true_iff 4 (Nat.div w 256)).mp hm0_ble
  set m0 := Nat.div w 256
  set cLast := Nat.mod (Nat.div w 16) 16
  set c0 : Circuit 1 := (.identity : Circuit 1) ;;ᶜ sylCircuit 1
  have hm0_ble1 : Nat.ble m0 1 = false := (nat_ble_false_iff m0 1).mpr (by omega)
  set rem := Nat.mod m0 4
  set p0 := Nat.add (Nat.mul 2 rem) 1
  have hp0_lt : p0 < 8 := by change 2 * (m0 % 4) + 1 < 8; omega
  have hp0_odd : p0 % 2 = 1 := by change (2 * (m0 % 4) + 1) % 2 = 1; omega
  have hsyl_mid : sylCircuit (Nat.add (Nat.mul 2 rem) 2) = phaseGate1 p0 ;;ᶜ gate1 .h := by
    dsimp only [p0]
    have hrem_lt : rem < 4 := Nat.mod_lt m0 (by decide)
    interval_cases rem <;> rfl
  have hmid1_first : mid1Circuit (m0, c0) = (Nat.div m0 4, c0 ;;ᶜ (phaseGate1 p0 ;;ᶜ gate1 .h))
      := by
      unfold mid1Circuit; dsimp only; rw [hm0_ble1, hsyl_mid]
  have hmid4_first : mid4Circuit (m0, c0) = mid1Circuit (mid1Circuit (mid1Circuit (Nat.div m0 4,
      c0 ;;ᶜ (phaseGate1 p0 ;;ᶜ gate1 .h)))) := by
      unfold mid4Circuit; dsimp only; rw [hm0_ble1]; dsimp only; rw [hmid1_first]
  have hq1_eq : mid12Circuit (m0, c0) =
      mid4Circuit (mid4Circuit (mid1Circuit (mid1Circuit (mid1Circuit (Nat.div m0 4,
      c0 ;;ᶜ (phaseGate1 p0 ;;ᶜ gate1 .h)))))) := by
    unfold mid12Circuit
    rw [hmid4_first]
  have hdec_eq : decodeWord2Bit w =
      restAfterFirstMid1 (Nat.div m0 4) cLast (c0 ;;ᶜ (phaseGate1 p0 ;;ᶜ gate1 .h)) := by
    unfold decodeWord2Bit restAfterFirstMid1; simp only [hw0, hcF1]; rw [hq1_eq]
  set pref : Circuit 1 := c0 ;;ᶜ phaseGate1 p0
  obtain ⟨hp0_1q, hp0_T, hp0_Toff, _⟩ := phaseGate1_props hp0_lt
  have hpref_1q : (CircExt.isOneQubitCircuit pref) = true := by
    have hc0_1q : (CircExt.isOneQubitCircuit c0) = true :=
        rfl; simp [pref, CircExt.isOneQubitCircuit, hc0_1q, hp0_1q]
  have hpref_T : pref.count PrimitiveGate.T = 1 := by
    have hc0_T : c0.count PrimitiveGate.T = 0 :=
        rfl; change c0.count PrimitiveGate.T + (phaseGate1 p0).count PrimitiveGate.T =
        1; rw [hc0_T, hp0_T, hp0_odd]
  have hpref_Toff : pref.count PrimitiveGate.TOFF = 0 := by
    have hc0_Toff : c0.count PrimitiveGate.TOFF = 0 :=
        rfl; change c0.count PrimitiveGate.TOFF + (phaseGate1 p0).count PrimitiveGate.TOFF =
        0; rw [hc0_Toff, hp0_Toff]
  have hpref_ev : pref.eval.1 = (phaseGate1 p0).eval.1 * hadamard2 := by
    have hc0_ev : c0.eval.1 = hadamard2 := by
      dsimp [c0, sylCircuit, phaseGate1]; simp [gate1_h_eval_hadamard2]
    dsimp [pref]; simp only [hc0_ev]
  have hinit_rel : PrefixRel pref (Nat.div m0 4, c0 ;;ᶜ (phaseGate1 p0 ;;ᶜ gate1 .h))
      (Nat.div m0 4, gate1 .h) := by
    refine ⟨rfl, by simp only [pref, CircExt.isOneQubitCircuit, Bool.and_assoc], ?_, ?_,
      by simp only [pref, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]⟩
    · change c0.count PrimitiveGate.T + ((phaseGate1 p0).count PrimitiveGate.T +
          (gate1 .h).count PrimitiveGate.T) =
        (c0.count PrimitiveGate.T + (phaseGate1 p0).count PrimitiveGate.T) +
            (gate1 .h).count PrimitiveGate.T
      omega
    · change c0.count PrimitiveGate.TOFF + ((phaseGate1 p0).count PrimitiveGate.TOFF +
          (gate1 .h).count PrimitiveGate.TOFF) =
        (c0.count PrimitiveGate.TOFF + (phaseGate1 p0).count PrimitiveGate.TOFF) +
            (gate1 .h).count PrimitiveGate.TOFF
      omega
  obtain ⟨_, hq4_1q, hq4_T, hq4_Toff, hq4_ev⟩ :=
    mid12Circuit_prefixRel (mid12Circuit_prefixRel (mid12Circuit_prefixRel
      (mid4Circuit_prefixRel (mid4Circuit_prefixRel
        (mid1Circuit_prefixRel (mid1Circuit_prefixRel (mid1Circuit_prefixRel hinit_rel)))))))
  have hbody_def : bodyFuseIn w =
      ((mid12Circuit (mid12Circuit (mid12Circuit (mid4Circuit (mid4Circuit
        (mid1Circuit (mid1Circuit (mid1Circuit (Nat.div m0 4,
            gate1 .h))))))))).2 ;;ᶜ sylCircuit cLast) := rfl
  rw [hdec_eq] at hc1 hcToff ⊢; unfold restAfterFirstMid1 at hc1 hcToff ⊢; rw [hbody_def];
  dsimp only at hq4_1q hq4_T hq4_Toff hq4_ev hc1 hcToff ⊢;
  simp only [CircExt.isOneQubitCircuit, hq4_1q, hpref_1q, Bool.true_and, Bool.and_eq_true] at hc1
  refine ⟨p0, hp0_lt, hp0_odd, by simp [CircExt.isOneQubitCircuit, hc1.1, hc1.2], ?_, ?_, ?_⟩
  · change _ + (sylCircuit cLast).count PrimitiveGate.T = 1 +
        (_ + (sylCircuit cLast).count PrimitiveGate.T)
    rw [hq4_T, hpref_T]; omega
  · change _ + (sylCircuit cLast).count PrimitiveGate.TOFF = 0 at hcToff;
    rw [hq4_Toff, hpref_Toff] at hcToff; change _ + (sylCircuit cLast).count PrimitiveGate.TOFF = 0;
    omega
  · simp only [Circuit.eval_seq, Submonoid.coe_mul, hq4_ev, hpref_ev, Matrix.mul_assoc]

/-! ### Part 3B. `D8` Matrix Peeling & `seam5_collapse` -/

theorem hadamard2_map_conj : hadamard2.map (starRingEnd ℂ) = hadamard2 := by
  unfold hadamard2 invSqrtTwo
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]

theorem hadamard2_mul_self_eq_one : hadamard2 * hadamard2 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold hadamard2 invSqrtTwo
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hne] <;>
      first | ring
theorem hadamard2_mul_z_mul_hadamard2 : hadamard2 * (Matrix.of ![![(1 : ℂ), 0], ![0, -1]]) *
    hadamard2 = (Matrix.of ![![(0 : ℂ), 1], ![1, 0]]) := by
  unfold hadamard2 invSqrtTwo
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hne] <;>
      first | ring

theorem phaseGate1_map_conj {p : Nat} (hp : p < 8) : ((phaseGate1 p).eval.1).map (starRingEnd ℂ) =
    (phaseGate1 ((8 - p) % 8)).eval.1 := by
  have hp' : (8 - p) % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [(phaseGate1_props hp).2.2.2, (phaseGate1_props hp').2.2.2]
  have hconj : conj CyclotomicEight.omegaComplex = CyclotomicEight.omegaComplex ^ 7 := by
    have h7 : CyclotomicEight.omegaComplex ^ 7 =
        CyclotomicEight.omegaComplex ^ 4 * CyclotomicEight.omegaComplex ^ 2 *
          CyclotomicEight.omegaComplex := by ring
    rw [h7, CyclotomicEight.omegaComplex_pow_four, CyclotomicEight.omegaComplex_sq];
    unfold CyclotomicEight.omegaComplex;
    simp only [map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal]; ring_nf;
    rw [Complex.I_sq]; ring
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one, map_one, map_zero]
  rw [map_pow, hconj, ← pow_mul, ← omegaComplex_pow_mod_eight (7 * p)]; congr 1; omega
theorem complex_I_pow_mod_four (n : Nat) : Complex.I ^ (n % 4) = Complex.I ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 4]
  rw [pow_add, pow_mul, show Complex.I ^ 4 = 1 by
    rw [show (4 : Nat) = 2 + 2 from rfl, pow_add, Complex.I_sq]
    ring, one_pow, one_mul]

theorem rotGate1_map_conj (r : Nat) : ((rotGate1 r).eval.1).map (starRingEnd ℂ) =
    (rotGate1 ((4 - r % 4) % 4)).eval.1 := by
  rw [(rotGate1_props r).2.2.2.1, (rotGate1_props ((4 - r % 4) % 4)).2.2.2.1]
  have hconjI : conj Complex.I = Complex.I ^ 3 := by
    rw [Complex.conj_I, show (3 : Nat) = 2 + 1 from rfl, pow_add, pow_one, Complex.I_sq]
    ring
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.zero_eta, Fin.mk_one, map_one, map_zero]
  rw [map_pow, hconjI, ← pow_mul, ← complex_I_pow_mod_four (3 * (r % 4))]; congr 1; omega
theorem rotGate1_mul (a b : Nat) : (rotGate1 a).eval.1 * (rotGate1 b).eval.1 =
    (rotGate1 (a % 4 + b % 4)).eval.1 := by
  rw [(rotGate1_props a).2.2.2.1, (rotGate1_props b).2.2.2.1,
      (rotGate1_props (a % 4 + b % 4)).2.2.2.1]; ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, mul_zero, zero_mul, add_zero, zero_add,
        one_mul]
  rw [← pow_add, ← complex_I_pow_mod_four (a % 4 + b % 4)]

theorem map_conj_mul_2x2 (A B : Matrix (Fin 2) (Fin 2) ℂ) : (A * B).map (starRingEnd ℂ) =
    A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem map_conj_involutive_2x2 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp

theorem applyD8Circuit_1q_and_eval (sym : Nat) (c : Circuit 1) (hc : (CircExt.isOneQubitCircuit c) =
    true) :
    (CircExt.isOneQubitCircuit (applyD8Circuit sym c)) = true ∧ (applyD8Circuit sym c).eval.1 =
    (rotGate1 (sym / 2)).eval.1 * (if sym % 2 = 1 then (c.eval.1).map (starRingEnd ℂ) else c.eval.1)
    := by
  unfold applyD8Circuit;
  obtain ⟨hr1, _, _, _, _⟩ := rotGate1_props (sym / 2); obtain ⟨hj1, _, _, hjEv⟩ :=
      conjCircuit_sound c hc
  rcases Nat.mod_two_eq_zero_or_one sym with hp0 | hp1
  · simp [hp0, CircExt.isOneQubitCircuit, hc, hr1, Circuit.eval_seq]
  · simp [hp1, CircExt.isOneQubitCircuit, hj1, hr1, Circuit.eval_seq, hjEv]

def seamCircuit (rTot p1Eff p0Eff : Nat) : Circuit 1 :=
  if rTot % 4 = 0 then
    phaseGate1 ((p1Eff + p0Eff) % 8)
  else
    phaseGate1 ((p1Eff + 8 - p0Eff) % 8) ;;ᶜ gate1 .x

theorem seam5_collapse {rTot p1Eff p0Eff : Nat}
    (hr_even : rTot % 2 = 0)
    (hp1_lt : p1Eff < 8) (hp1_odd : p1Eff % 2 = 1)
    (hp0_lt : p0Eff < 8) (hp0_odd : p0Eff % 2 = 1) :
    let sc := seamCircuit rTot p1Eff p0Eff
    (CircExt.isOneQubitCircuit sc) = true ∧ sc.count PrimitiveGate.T = 0 ∧
        sc.count PrimitiveGate.TOFF = 0 ∧
    ∃ ζ : ℂ, ζ ≠ 0 ∧ sc.eval.1 = ζ • (((phaseGate1 p0Eff).eval.1 * hadamard2) *
        ((rotGate1 rTot).eval.1 * (hadamard2 * (phaseGate1 p1Eff).eval.1))) := by
  intro sc
  let ω := CyclotomicEight.omegaComplex
  let D (p : Nat) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![(1 : ℂ), 0], ![0, ω ^ p]]
  have homega_ne : ω ≠ 0 := fun h0 => by
    have h4 := CyclotomicEight.omegaComplex_pow_four
    norm_num [ω, h0] at h4
  rcases (by omega : rTot % 4 = 0 ∨ rTot % 4 = 2) with hr0 | hr2
  · have hsc : sc = phaseGate1 ((p1Eff + p0Eff) % 8) := by simp [sc, seamCircuit, hr0]
    obtain ⟨h1q, hT, hToff, hEv⟩ := phaseGate1_props (Nat.mod_lt (p1Eff + p0Eff) (by decide))
    refine ⟨by rwa [hsc], by rw [hsc, hT, show ((p1Eff + p0Eff) % 8) % 2 = 0 by omega],
        by rwa [hsc], 1, one_ne_zero, ?_⟩
    rw [hsc, one_smul, show (rotGate1 rTot).eval.1 = 1 by
        rw [(rotGate1_props rTot).2.2.2.1, hr0]
        ext i j : 1
        fin_cases i <;> fin_cases j <;> simp,
      Matrix.one_mul, hEv, (phaseGate1_props hp0_lt).2.2.2, (phaseGate1_props hp1_lt).2.2.2,
      show (D p0Eff * hadamard2) * (hadamard2 * D p1Eff) =
        D p0Eff * (hadamard2 * hadamard2) * D p1Eff by simp [Matrix.mul_assoc],
      hadamard2_mul_self_eq_one, Matrix.mul_one, omegaComplex_pow_mod_eight (p1Eff + p0Eff)]
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [D, ω, Matrix.mul_apply, Fin.sum_univ_two, ← pow_add, add_comm]
  · have hsc : sc = phaseGate1 ((p1Eff + 8 - p0Eff) % 8) ;;ᶜ gate1 .x := by
      simp [sc, seamCircuit, hr2]
    obtain ⟨h1q, hT, hToff, hEv⟩ := phaseGate1_props (Nat.mod_lt (p1Eff + 8 - p0Eff) (by decide))
    refine ⟨by simp [hsc, CircExt.isOneQubitCircuit, h1q],
      by rw [hsc]; change _ + 0 = 0; rw [hT]; omega,
      by rw [hsc]; change _ + 0 = 0; exact hToff,
      (ω ^ p0Eff)⁻¹, inv_ne_zero (pow_ne_zero _ homega_ne), ?_⟩
    rw [hsc, show (rotGate1 rTot).eval.1 = Matrix.of ![![(1 : ℂ), 0], ![0, -1]] by
        rw [(rotGate1_props rTot).2.2.2.1, hr2]
        ext i j : 1
        fin_cases i <;> fin_cases j <;> simp,
      (phaseGate1_props hp0_lt).2.2.2, (phaseGate1_props hp1_lt).2.2.2,
      show (D p0Eff * hadamard2) * (Matrix.of ![![(1 : ℂ), 0], ![0, -1]] * (hadamard2 * D p1Eff)) =
        D p0Eff * (hadamard2 * Matrix.of ![![(1 : ℂ), 0], ![0, -1]] * hadamard2) * D p1Eff by
        simp [Matrix.mul_assoc],
      hadamard2_mul_z_mul_hadamard2]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, gate1_x_eval, hEv]
    have h8 : ω ^ 8 = 1 := by
      rw [show (8 : Nat) = 4 + 4 from rfl, pow_add, CyclotomicEight.omegaComplex_pow_four]
      ring
    have hpow : (ω ^ p0Eff)⁻¹ * ω ^ p1Eff = ω ^ ((p1Eff + 8 - p0Eff) % 8) := by
      rw [omegaComplex_pow_mod_eight (p1Eff + 8 - p0Eff)]
      refine mul_left_cancel₀ (pow_ne_zero p0Eff homega_ne) ?_
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero p0Eff homega_ne), one_mul, ← pow_add,
        show p0Eff + (p1Eff + 8 - p0Eff) = p1Eff + 8 by omega, pow_add, h8, mul_one]
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
        simp only [Nat.reducePow, Fin.zero_eta, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, Fin.sum_univ_two, mul_one, cons_val_one, mul_zero,
        add_zero, Nat.succ_eq_add_one, Nat.reduceAdd, cons_mul, vecMul_cons, head_cons, one_smul,
        tail_cons, zero_smul, empty_vecMul, smul_cons, smul_eq_mul, smul_empty, zero_add, empty_mul,
        Equiv.symm_apply_apply, Matrix.smul_apply, ω, D, Fin.mk_one, one_mul, zero_mul]
    · exact hpow.symm
    · exact (inv_mul_cancel₀ (pow_ne_zero p0Eff homega_ne)).symm

theorem applyD8_twice_fuseOut {s1 sym1 w1 p1 : Nat}
    (hp1_lt : p1 < 8) (hp1_odd : p1 % 2 =
        1) (hw1_1q : (CircExt.isOneQubitCircuit (decodeWord2Bit w1)) = true)
    (hb1_1q : (CircExt.isOneQubitCircuit (bodyFuseOut w1)) = true)
    (hw1_ev : (decodeWord2Bit w1).eval.1 = hadamard2 * ((phaseGate1 p1).eval.1 *
        (bodyFuseOut w1).eval.1)) :
    let flip1 := (s1 % 2 + sym1 % 2) % 2
    let g1Body := if flip1 = 1 then conjCircuit (bodyFuseOut w1) else bodyFuseOut w1
    let p1Eff := if flip1 = 1 then (8 - p1) % 8 else p1
    let r1In := if sym1 % 2 = 1 then (4 - (s1 / 2) % 4) % 4 else (s1 / 2) % 4
    let rTot := (sym1 / 2) % 4 + r1In % 4
    p1Eff < 8 ∧ p1Eff % 2 = 1 ∧ rTot % 2 = (s1 / 2 + sym1 / 2) % 2 ∧
    (CircExt.isOneQubitCircuit g1Body) = true ∧ g1Body.count PrimitiveGate.T =
        (bodyFuseOut w1).count PrimitiveGate.T ∧
    g1Body.count PrimitiveGate.TOFF = (bodyFuseOut w1).count PrimitiveGate.TOFF ∧
    (applyD8Circuit sym1 (applyD8Circuit s1 (decodeWord2Bit w1))).eval.1 = ((rotGate1 rTot).eval.1 *
        (hadamard2 * (phaseGate1 p1Eff).eval.1)) * g1Body.eval.1 := by
  intro flip1 g1Body p1Eff r1In rTot
  have hp1Eff_lt : p1Eff < 8 := by dsimp [p1Eff]; split_ifs <;> omega
  have hp1Eff_odd : p1Eff % 2 = 1 := by dsimp [p1Eff]; split_ifs <;> omega
  have hrTot_par : rTot % 2 = (s1 / 2 + sym1 / 2) % 2 := by dsimp [rTot, r1In]; split_ifs <;> omega
  obtain ⟨hcj_1q, hcj_T, hcj_Toff, hcj_ev⟩ := conjCircuit_sound (bodyFuseOut w1) hb1_1q
  have hg1_props : (CircExt.isOneQubitCircuit g1Body) = true ∧ g1Body.count PrimitiveGate.T =
      (bodyFuseOut w1).count PrimitiveGate.T ∧ g1Body.count PrimitiveGate.TOFF =
      (bodyFuseOut w1).count PrimitiveGate.TOFF := by
    dsimp [g1Body]; split_ifs
    · exact ⟨hcj_1q, hcj_T, hcj_Toff⟩
    · exact ⟨hb1_1q, rfl, rfl⟩
  refine ⟨hp1Eff_lt, hp1Eff_odd, hrTot_par, hg1_props.1, hg1_props.2.1, hg1_props.2.2, ?_⟩
  obtain ⟨hd8_s1_1q, hd8_s1_ev⟩ := applyD8Circuit_1q_and_eval s1 (decodeWord2Bit w1) hw1_1q
  obtain ⟨_, hd8_sym1_ev⟩ := applyD8Circuit_1q_and_eval sym1 _ hd8_s1_1q
  rw [hd8_sym1_ev, hd8_s1_ev, hw1_ev]
  have hp1_inv : (8 - (8 - p1) % 8) % 8 = p1 := by omega
  have hp1c_lt : (8 - p1) % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases Nat.mod_two_eq_zero_or_one s1 with hs1 | hs1 <;>
    rcases Nat.mod_two_eq_zero_or_one sym1 with hsym1 | hsym1 <;>
    (dsimp [flip1, g1Body, p1Eff, r1In, rTot]
     simp only [hs1, hsym1, show (0 + 0) % 2 = 0 from rfl, show (0 + 1) % 2 = 1 from rfl,
         zero_ne_one, ↓reduceIte, hcj_ev, map_conj_mul_2x2, map_conj_involutive_2x2,
         hadamard2_map_conj, phaseGate1_map_conj hp1_lt, phaseGate1_map_conj hp1c_lt, hp1_inv]
     try rw [rotGate1_map_conj (s1 / 2)]
     try rw [← Matrix.mul_assoc ((rotGate1 (sym1 / 2)).eval.1)]
     rw [rotGate1_mul]
     simp [Matrix.mul_assoc])

theorem applyD8Circuit_counts (sym : Nat) (c : Circuit 1) (hc : (CircExt.isOneQubitCircuit c) =
    true) :
    (CircExt.isOneQubitCircuit (applyD8Circuit sym c)) = true ∧
        (applyD8Circuit sym c).count PrimitiveGate.T =
    c.count PrimitiveGate.T ∧ (applyD8Circuit sym c).count PrimitiveGate.TOFF =
    c.count PrimitiveGate.TOFF := by
  unfold applyD8Circuit
  obtain ⟨hr1, hrT, hrToff, _, _⟩ := rotGate1_props (sym / 2)
  obtain ⟨hj1, hjT, hjToff, _⟩ := conjCircuit_sound c hc
  split_ifs <;> refine ⟨by simp [CircExt.isOneQubitCircuit, hj1, hc, hr1], ?_, ?_⟩ <;> (
      change _ + (rotGate1 (sym / 2)).count _ = _
      simp [hjT, hjToff, hrT, hrToff])

theorem applyD8_twice_fuseIn {s0 sym0 w0 p0 : Nat}
    (hp0_lt : p0 < 8) (hp0_odd : p0 % 2 =
        1) (hw0_1q : (CircExt.isOneQubitCircuit (decodeWord2Bit w0)) = true)
    (hb0_1q : (CircExt.isOneQubitCircuit (bodyFuseIn w0)) = true)
    (hw0_ev : (decodeWord2Bit w0).eval.1 = (bodyFuseIn w0).eval.1 * ((phaseGate1 p0).eval.1 *
        hadamard2)) :
    let flip0 := (s0 % 2 + sym0 % 2) % 2
    let p0Eff := if flip0 = 1 then (8 - p0) % 8 else p0
    let g0Tail := applyD8Circuit sym0 (applyD8Circuit s0 (bodyFuseIn w0))
    p0Eff < 8 ∧ p0Eff % 2 = 1 ∧ (CircExt.isOneQubitCircuit g0Tail) = true ∧
    g0Tail.count PrimitiveGate.T = (bodyFuseIn w0).count PrimitiveGate.T ∧
    g0Tail.count PrimitiveGate.TOFF = (bodyFuseIn w0).count PrimitiveGate.TOFF ∧
    (applyD8Circuit sym0 (applyD8Circuit s0 (decodeWord2Bit w0))).eval.1 = g0Tail.eval.1 *
        ((phaseGate1 p0Eff).eval.1 * hadamard2) := by
  intro flip0 p0Eff g0Tail
  obtain ⟨hd8_b0_s0_1q, hd8_b0_s0_ev⟩ := applyD8Circuit_1q_and_eval s0 (bodyFuseIn w0) hb0_1q
  obtain ⟨hd8_b0_sym0_1q, hd8_b0_sym0_ev⟩ := applyD8Circuit_1q_and_eval sym0 _ hd8_b0_s0_1q
  obtain ⟨_, hT1, hToff1⟩ := applyD8Circuit_counts s0 (bodyFuseIn w0) hb0_1q
  obtain ⟨_, hT2, hToff2⟩ := applyD8Circuit_counts sym0 _ hd8_b0_s0_1q
  obtain ⟨hd8_w0_s0_1q, hd8_w0_s0_ev⟩ := applyD8Circuit_1q_and_eval s0 (decodeWord2Bit w0) hw0_1q
  obtain ⟨_, hd8_w0_sym0_ev⟩ := applyD8Circuit_1q_and_eval sym0 _ hd8_w0_s0_1q
  refine ⟨by dsimp [p0Eff]; split_ifs <;> omega, by dsimp [p0Eff]; split_ifs <;> omega,
    hd8_b0_sym0_1q, hT2.trans hT1, hToff2.trans hToff1, ?_⟩
  rw [show g0Tail = applyD8Circuit sym0 (applyD8Circuit s0 (bodyFuseIn w0)) from rfl,
    hd8_w0_sym0_ev, hd8_w0_s0_ev, hd8_b0_sym0_ev, hd8_b0_s0_ev, hw0_ev]
  have hp0_inv : (8 - (8 - p0) % 8) % 8 = p0 := by omega
  have hp0c_lt : (8 - p0) % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases Nat.mod_two_eq_zero_or_one s0 with hs0 | hs0 <;>
    rcases Nat.mod_two_eq_zero_or_one sym0 with hsym0 | hsym0 <;> (
      dsimp [flip0, p0Eff]
      simp only [hs0, hsym0, show (0 + 0) % 2 = 0 from rfl, show (0 + 1) % 2 = 1 from rfl,
          zero_ne_one, ↓reduceIte, map_conj_mul_2x2, map_conj_involutive_2x2, hadamard2_map_conj,
          phaseGate1_map_conj hp0_lt, phaseGate1_map_conj hp0c_lt, hp0_inv, Matrix.mul_assoc])

theorem fused_stage01_pair_sound {capFi capNoFi wd0 s0 sym0 wd1 s1 sym1 : Nat}
    (hw0_1q : (CircExt.isOneQubitCircuit (decodeWord2Bit wd0)) = true)
    (hw0_Toff : (decodeWord2Bit wd0).count PrimitiveGate.TOFF = 0)
    (hw0_cap : (isFuseInWord wd0 = true ∧ (decodeWord2Bit wd0).count PrimitiveGate.T ≤ capFi) ∨
        (decodeWord2Bit wd0).count PrimitiveGate.T ≤ capNoFi)
    (hw1_1q : (CircExt.isOneQubitCircuit (decodeWord2Bit wd1)) = true)
    (hw1_Toff : (decodeWord2Bit wd1).count PrimitiveGate.TOFF = 0)
    (hw1_cap : (isFuseOutWord wd1 = true ∧ (s1 / 2 + sym1 / 2) % 2 = 0 ∧
        (decodeWord2Bit wd1).count PrimitiveGate.T ≤ 28) ∨
        (decodeWord2Bit wd1).count PrimitiveGate.T ≤ 26) :
    let cStage0 := applyD8Circuit sym0 (applyD8Circuit s0 (decodeWord2Bit wd0))
    let cStage1 := applyD8Circuit sym1 (applyD8Circuit s1 (decodeWord2Bit wd1))
    ∃ cFused : Circuit 1, (CircExt.isOneQubitCircuit cFused) = true ∧ cFused.count PrimitiveGate.T ≤
        max (26 + capFi) (28 + capNoFi) ∧ cFused.count PrimitiveGate.TOFF = 0 ∧ ∃ ζ : ℂ,
      ζ ≠ 0 ∧ cFused.eval.1 = ζ • (cStage1 ;;ᶜ cStage0).eval.1 := by
  intro cStage0 cStage1
  obtain ⟨hs0_1q, hs0_T, hs0_Toff⟩ := applyD8Circuit_counts s0 (decodeWord2Bit wd0) hw0_1q
  obtain ⟨hc0_1q, hc0_T, hc0_Toff⟩ := applyD8Circuit_counts sym0 _ hs0_1q
  obtain ⟨hs1_1q, hs1_T, hs1_Toff⟩ := applyD8Circuit_counts s1 (decodeWord2Bit wd1) hw1_1q
  obtain ⟨hc1_1q, hc1_T, hc1_Toff⟩ := applyD8Circuit_counts sym1 _ hs1_1q
  have h1 := le_max_left (26 + capFi) (28 + capNoFi)
  have h2 := le_max_right (26 + capFi) (28 + capNoFi)
  let Goal : Prop := ∃ cFused : Circuit 1, (CircExt.isOneQubitCircuit cFused) = true ∧
    cFused.count PrimitiveGate.T ≤ max (26 + capFi) (28 + capNoFi) ∧
    cFused.count PrimitiveGate.TOFF = 0 ∧ ∃ ζ ≠ (0 : ℂ), cFused.eval.1 =
        ζ • (cStage1 ;;ᶜ cStage0).eval.1
  have hnofuse (ht : (decodeWord2Bit wd1).count PrimitiveGate.T +
      (decodeWord2Bit wd0).count PrimitiveGate.T ≤ max (26 + capFi) (28 + capNoFi)) : Goal :=
    ⟨cStage1 ;;ᶜ cStage0, by simp [cStage1, cStage0, CircExt.isOneQubitCircuit, hc1_1q, hc0_1q],
      by change cStage1.count _ + cStage0.count _ ≤ _; rwa [hc1_T, hs1_T, hc0_T, hs0_T],
      by simp [cStage1, cStage0, Circuit.count, hc1_Toff, hs1_Toff, hc0_Toff, hs0_Toff, hw1_Toff,
        hw0_Toff], 1, one_ne_zero, by simp⟩
  rcases hw1_cap with ⟨hfo1, hpar1, ht1_28⟩ | ht1_26
  · rcases hw0_cap with ⟨hfi0, ht0_fi⟩ | ht0_nofi
    · -- FUSED H-Z^r-H SEAM CASE: (tc1 - 1) + 0 + (tc0 - 1) <= 27 + (capFi - 1) <= 26 + capFi!
      obtain ⟨p1, hp1_lt, hp1_odd, hb1_1q, ht1_peel, hb1_Toff, hw1_ev⟩ :=
          decodeWord2Bit_fuseOut_peel hfo1 hw1_1q hw1_Toff
      obtain ⟨p0, hp0_lt, hp0_odd, hb0_1q, ht0_peel, hb0_Toff, hw0_ev⟩ :=
          decodeWord2Bit_fuseIn_peel hfi0 hw0_1q hw0_Toff
      obtain ⟨hp1Eff_lt, hp1Eff_odd, hrTot_par, hg1_1q, hg1_T, hg1_Toff, hc1_ev⟩ :=
          applyD8_twice_fuseOut (s1 := s1) (sym1 := sym1) hp1_lt hp1_odd hw1_1q hb1_1q hw1_ev
      obtain ⟨hp0Eff_lt, hp0Eff_odd, hg0_1q, hg0_T, hg0_Toff, hc0_ev⟩ :=
          applyD8_twice_fuseIn (s0 := s0) (sym0 := sym0) hp0_lt hp0_odd hw0_1q hb0_1q hw0_ev
      obtain ⟨hsc_1q, hsc_T, hsc_Toff, ζ, hζ_ne, hsc_ev⟩ :=
          seam5_collapse (hrTot_par.trans hpar1) hp1Eff_lt hp1Eff_odd hp0Eff_lt hp0Eff_odd
      set g1Body :=
          if (s1 % 2 + sym1 % 2) % 2 = 1 then conjCircuit (bodyFuseOut wd1) else bodyFuseOut wd1
      set sc :=
          seamCircuit ((sym1 / 2) % 4 + (if sym1 % 2 = 1 then (4 - (s1 / 2) % 4) % 4 else (s1 /
          2) % 4) % 4) (if (s1 % 2 + sym1 % 2) % 2 = 1 then (8 - p1) % 8 else p1)
          (if (s0 % 2 + sym0 % 2) % 2 =
          1 then (8 - p0) % 8 else p0)
      set g0Tail := applyD8Circuit sym0 (applyD8Circuit s0 (bodyFuseIn wd0))
      refine ⟨g1Body ;;ᶜ sc ;;ᶜ g0Tail, by simp [CircExt.isOneQubitCircuit, hg1_1q, hsc_1q, hg0_1q],
          ?_, ?_, ζ, hζ_ne, ?_⟩
      · change g1Body.count _ + (sc.count _ + g0Tail.count _) ≤ _
        rw [hg1_T, hsc_T, hg0_T]
        omega
      · change g1Body.count _ + (sc.count _ + g0Tail.count _) = 0
        rw [hg1_Toff, hsc_Toff, hg0_Toff]
        omega
      · simp only [Circuit.eval_seq, Submonoid.coe_mul]; dsimp only [cStage1, cStage0];
        rw [hsc_ev, hc0_ev, hc1_ev]; simp only [smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc]
    · -- Non-fused hi + capNoFi: 28 + capNoFi
      exact hnofuse (by omega)
  · -- Non-fused lo (<= 26): either 26 + capFi or 26 + capNoFi <= 28 + capNoFi
    rcases hw0_cap with ⟨_, ht0⟩ | ht0 <;> exact hnofuse (by omega)

attribute [local irreducible]
  invertGate1 invertCircuit1
  gate1 phaseGate1 sylCircuit mid1Circuit mid4Circuit mid12Circuit decodeWord2Bit
  conjGate1 applyD8Circuit rotGate1 conjCircuit cosetCircuit
  bodyFuseOut bodyFuseIn seamCircuit

/-! ### Part 4. Dual Stage-1 Lookup, Equator Reduction, & Shared Stage-2 Simplicial Finish -/

theorem matEta_smul_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℂ) : ((ζ • M) 0 0 ≠ 0 ↔
    M 0 0 ≠ 0) ∧ matEta (ζ • M) = matEta M := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.smul_apply, smul_eq_mul, hζ]
  · unfold matEta; simp only [Matrix.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hζ]
theorem checkWord0CapPacked_sound {capFi capNoFi w pb : Nat}
    (hchk : checkWord0CapPacked capFi capNoFi w pb = true) :
    let c := decodeWord2Bit w
    (CircExt.isOneQubitCircuit c) = true ∧
    c.count PrimitiveGate.TOFF = 0 ∧
    c.eval.1 0 0 ≠ 0 ∧
    (unpackBox 2251799813685248 4503599627370496 pb).Mem (matEta c.eval.1) ∧
    ((isFuseInWord w = true ∧ c.count PrimitiveGate.T ≤ capFi) ∨
     c.count PrimitiveGate.T ≤ capNoFi) := by
  unfold checkWord0CapPacked at hchk; simp only [Bool.or_eq_true, Bool.and_eq_true] at hchk
  rcases hchk with ⟨hfi, hbox⟩ | hbox
  · unfold checkWord2BitPacked at hbox;
    obtain ⟨h1q, hT, hToff, h00, hmem⟩ :=
        checkWord2BitBox_sound hbox; exact ⟨h1q, hToff, h00, hmem, Or.inl ⟨hfi, hT⟩⟩
  · unfold checkWord2BitPacked at hbox;
    obtain ⟨h1q, hT, hToff, h00, hmem⟩ :=
        checkWord2BitBox_sound hbox; exact ⟨h1q, hToff, h00, hmem, Or.inr hT⟩
theorem checkDetBox_geom_sound {x0 y0 w rNumSq rScaleSq : Nat} {rawBox : Box2DS} {sym : Nat}
    {wc zw : ℂ} (hchk : checkDetBox x0 y0 w rNumSq rScaleSq rawBox sym = true)
    (hrScale : 0 < rScaleSq) (hmem_wb : (applyD8Box rawBox sym).Mem wc)
    (hsq : SquareMem x0 y0 w zw) : 0 < 1 + wc.re * zw.re + wc.im * zw.im ∧ ((zw.re - wc.re) ^ 2 +
    (zw.im - wc.im) ^ 2) / (1 + wc.re * zw.re + wc.im * zw.im) ^ 2 ≤ (rNumSq : ℝ) / (rScaleSq : ℝ)
    := by
  rcases hsq with ⟨hzw_re0, hzw_re1, hzw_im0, hzw_im1⟩
  unfold checkDetBox at hchk; simp only [Bool.and_eq_true] at hchk;
  obtain ⟨_, hdot_pos, hle_s⟩ := hchk
  set wb := applyD8Box rawBox sym
  set BS : ℝ := 2 ^ 52
  have hBS_pos : 0 < BS := by dsimp [BS]; positivity
  have hbs_int : (boxScaleS.toInt : ℝ) = BS := by dsimp [boxScaleS, SInt.toInt, BS]; norm_num
  set x0s : SInt := ⟨false, x0⟩
  set x1s : SInt := ⟨false, Nat.add x0 w⟩
  set y0s : SInt := ⟨false, y0⟩
  set y1s : SInt := ⟨false, Nat.add y0 w⟩
  rcases hmem_wb with ⟨hwx0, hwx1, hwy0, hwy1⟩
  have hzx0 : (x0s.toInt : ℝ) ≤ BS * zw.re := by
    simpa [x0s, SInt.toInt] using (div_le_iff₀' hBS_pos).mp hzw_re0
  have hzx1 : BS * zw.re ≤ (x1s.toInt : ℝ) := by
    simpa [x1s, SInt.toInt, Nat.add_eq] using (le_div_iff₀' hBS_pos).mp hzw_re1
  have hzy0 : (y0s.toInt : ℝ) ≤ BS * zw.im := by
    simpa [y0s, SInt.toInt] using (div_le_iff₀' hBS_pos).mp hzw_im0
  have hzy1 : BS * zw.im ≤ (y1s.toInt : ℝ) := by
    simpa [y1s, SInt.toInt, Nat.add_eq] using (le_div_iff₀' hBS_pos).mp hzw_im1
  have hwx0' := (div_le_iff₀' hBS_pos).mp hwx0
  have hwx1' := (le_div_iff₀' hBS_pos).mp hwx1
  have hwy0' := (div_le_iff₀' hBS_pos).mp hwy0
  have hwy1' := (le_div_iff₀' hBS_pos).mp hwy1
  refine checkDetCore_geom_sound hrScale ?_ ?_ ?_ hdot_pos hle_s
  · rw [show BS * (zw.re - wc.re) = BS * zw.re - BS * wc.re by ring]
    exact (interval_abs_diff_le hzx0 hzx1 hwx0' hwx1').trans (by simp)
  · rw [show BS * (zw.im - wc.im) = BS * zw.im - BS * wc.im by ring]
    exact (interval_abs_diff_le hzy0 hzy1 hwy0' hwy1').trans (by simp)
  · have hpx := interval_prod_ge_min4 hzx0 hzx1 hwx0' hwx1'
    have hpy := interval_prod_ge_min4 hzy0 hzy1 hwy0' hwy1'
    simp [sMin4, hbs_int, ← sq]
    nlinarith

theorem d8_mobius_step_sound
    {V0 : Matrix (Fin 2) (Fin 2) ℂ} {cPrev wCirc : Circuit 1} {sym : Nat} {zw : ℂ} {rOut : ℝ}
    (hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ)
    (hrem00 : (cPrev.eval.1ᴴ * V0) 0 0 ≠ 0)
    (hw1 : (CircExt.isOneQubitCircuit wCirc) = true)
    (hw00 : wCirc.eval.1 0 0 ≠ 0)
    (hd8 : d8Map sym zw = matEta (cPrev.eval.1ᴴ * V0))
    (hdot_w : 0 < 1 + (matEta wCirc.eval.1).re * zw.re + (matEta wCirc.eval.1).im * zw.im)
    (hrat_w : ((zw.re - (matEta wCirc.eval.1).re) ^ 2 + (zw.im - (matEta wCirc.eval.1).im) ^ 2) /
      (1 + (matEta wCirc.eval.1).re * zw.re + (matEta wCirc.eval.1).im * zw.im) ^ 2 ≤ rOut) :
    let cNext := applyD8Circuit sym wCirc ;;ᶜ cPrev
    (cNext.eval.1ᴴ * V0) 0 0 ≠ 0 ∧
    ‖matEta (cNext.eval.1ᴴ * V0)‖ ^ 2 ≤ rOut := by
  intro cNext;
  let cStage : Circuit 1 := applyD8Circuit sym wCirc; obtain ⟨_, _, _, hs00, hs_eta⟩ :=
      applyD8Circuit_basic sym wCirc hw1 hw00; obtain ⟨_, hdist_inv, hdot_inv, _⟩ :=
      d8Map_invariants sym (matEta wCirc.eval.1) zw
  set remPrev := cPrev.eval.1ᴴ * V0
  have hremPrev_mem : remPrev ∈ unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (by rw [← star_eq_conjTranspose]; exact Unitary.star_mem cPrev.eval.2) hV0
  have hdot_z : 0 < 1 + (matEta cStage.eval.1).re * (matEta remPrev).re +
      (matEta cStage.eval.1).im * (matEta remPrev).im := by
    rw [hs_eta, ← hd8, add_assoc, hdot_inv, ← add_assoc]; exact hdot_w
  obtain ⟨hnext00, hnext_eta⟩ :=
      mobius_conjTranspose_mul_eta cStage.eval.2 hremPrev_mem hs00 hrem00 hdot_z
  have hcNext_rem : cNext.eval.1ᴴ * V0 = cStage.eval.1ᴴ * remPrev := by
    dsimp [cNext, cStage, remPrev];
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  refine ⟨by rwa [hcNext_rem], ?_⟩
  rw [hcNext_rem]; refine hnext_eta.trans ?_
  have hnum_eq : ((matEta remPrev).re - (matEta cStage.eval.1).re) ^ 2 + ((matEta remPrev).im -
      (matEta cStage.eval.1).im) ^ 2 = (zw.re - (matEta wCirc.eval.1).re) ^ 2 +
      (zw.im - (matEta wCirc.eval.1).im) ^ 2 := by
    have hn : ∀ a b : ℂ, (b.re - a.re) ^ 2 + (b.im - a.im) ^ 2 = ‖a - b‖ ^ 2 := by
      intro a b; rw [norm_sub_rev, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp; ring
    rw [hn, hn, hs_eta, ← hd8, hdist_inv]
  rw [hnum_eq, hs_eta, ← hd8, add_assoc, hdot_inv, ← add_assoc]; exact hrat_w

theorem squareMem_zero_of_wedge {w : Nat} {zw : ℂ}
    (him0 : 0 ≤ zw.im) (hle : zw.im ≤ zw.re) (hhi : zw.re ≤ ((0 + w : Nat) : ℝ) / (2 ^ 52 : ℝ)) :
    SquareMem 0 0 w zw :=
  ⟨by simpa using him0.trans hle, hhi, by simpa using him0, hle.trans hhi⟩

theorem fused_stage01_step_sound {capFi capNoFi idx wd0 s0 sym0 : Nat}
    {V0 : Matrix (Fin 2) (Fin 2) ℂ}
    (hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ)
    (hcov1 : Stage1SquareCov 0 0 457396837154816)
    (hw0_1q : (CircExt.isOneQubitCircuit (decodeWord2Bit wd0)) = true)
    (hw0_Toff : (decodeWord2Bit wd0).count PrimitiveGate.TOFF = 0)
    (hw0_cap : (isFuseInWord wd0 = true ∧ (decodeWord2Bit wd0).count PrimitiveGate.T ≤ capFi) ∨
        (decodeWord2Bit wd0).count PrimitiveGate.T ≤ capNoFi)
    (hrem1_ne : (((applyD8Circuit sym0 (applyD8Circuit s0 (decodeWord2Bit wd0)) ;;ᶜ cosetCircuit
        idx).eval.1)ᴴ * V0) 0 0 ≠ 0)
    (hrem1_rad : ‖matEta (((applyD8Circuit sym0 (applyD8Circuit s0 (decodeWord2Bit wd0)) ;;ᶜ
        cosetCircuit idx).eval.1)ᴴ * V0)‖ ^ 2 ≤ (1020100 : ℝ) / (100000000 : ℝ)) :
    ∃ cPref : Circuit 1, (CircExt.isOneQubitCircuit cPref) = true ∧ cPref.count PrimitiveGate.T ≤
        max (26 + capFi) (28 + capNoFi) ∧ cPref.count PrimitiveGate.TOFF = 0 ∧ (cPref.eval.1ᴴ *
        V0) 0 0 ≠ 0 ∧
      ‖matEta (cPref.eval.1ᴴ * V0)‖ ^ 2 ≤ (13456 : ℝ) / (1000000000000 : ℝ) := by
  set c0 := cosetCircuit idx
  set cStage0 := applyD8Circuit sym0 (applyD8Circuit s0 (decodeWord2Bit wd0))
  set c1 := cStage0 ;;ᶜ c0
  set rem1 := c1.eval.1ᴴ * V0
  obtain ⟨hc0_1q, hc0_T, hc0_Toff⟩ := cosetCircuit_props idx
  obtain ⟨sym1, zw1, _, hzw1_im0, hzw1_le, _, hd8_1⟩ := exists_foldD8 (matEta rem1)
  have hzw1_rad : zw1.re ^ 2 + zw1.im ^ 2 ≤ ((1020100 : Nat) : ℝ) / ((100000000 : Nat) : ℝ) := by
    have hn1 : ‖zw1‖ = ‖matEta rem1‖ := by simpa [hd8_1] using (d8Map_invariants sym1 zw1 0).1.symm
    rw [sq zw1.re, sq zw1.im, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hn1]
    simpa using hrem1_rad
  have hroot1 : SquareMem 0 0 457396837154816 zw1 := by
    have hre_hi : zw1.re ≤ 13 / 128 :=
        (sq_le_sq₀ (hzw1_im0.trans hzw1_le)
        (by norm_num)).mp
        (by nlinarith [show zw1.re ^ 2 + zw1.im ^ 2 ≤ 1020100 / 100000000 by simpa using hzw1_rad,
              sq_nonneg zw1.im])
    exact squareMem_zero_of_wedge hzw1_im0 hzw1_le (hre_hi.trans_eq (by norm_num))
  obtain ⟨x0', y0', w', hwit1, hsq1⟩ :=
      stage1SquareCov_find_leaf (fun x0' y0' w' hsq => isOutsideDom_false_of_rad (by decide)
      (by norm_num) hzw1_im0 hzw1_le hzw1_rad hsq) hcov1 hroot1
  obtain ⟨wd1, rawBox, s1, hcap_box, hdet1⟩ := hwit1 ((sym1 / 2) % 2) (Nat.mod_lt _ (by decide))
  have hent : (CircExt.isOneQubitCircuit (decodeWord2Bit wd1)) = true ∧
      (decodeWord2Bit wd1).count PrimitiveGate.TOFF = 0 ∧
      ((isFuseOutWord wd1 = true ∧ (s1 / 2 + sym1 / 2) % 2 = 0 ∧
          (decodeWord2Bit wd1).count PrimitiveGate.T ≤ 28) ∨
          (decodeWord2Bit wd1).count PrimitiveGate.T ≤ 26) ∧
      rawBox.Mem (matEta (decodeWord2Bit wd1).eval.1) ∧ (decodeWord2Bit wd1).eval.1 0 0 ≠ 0 := by
    rcases hcap_box with ⟨hfo, hpar, hwb28⟩ | hwb26
    · obtain ⟨h1q, hT, hToff, h00, hmem⟩ := checkWord2BitBox_sound hwb28
      exact ⟨h1q, hToff, Or.inl ⟨hfo, by omega, hT⟩, hmem, h00⟩
    · obtain ⟨h1q, hT, hToff, h00, hmem⟩ := checkWord2BitBox_sound hwb26
      exact ⟨h1q, hToff, Or.inr hT, hmem, h00⟩
  obtain ⟨hd1_1q, hd1_Toff, hd1_cap_pair, hmem_raw, hd1_00⟩ := hent
  obtain ⟨hw1_1q, _, _, hw1_00, hmem_wb⟩ :=
      applyD8Circuit_sound s1 (decodeWord2Bit wd1) rawBox hd1_1q hd1_00 hmem_raw
  obtain ⟨hdot1, hrat1⟩ := checkDetBox_geom_sound hdet1 (by norm_num) hmem_wb hsq1
  obtain ⟨hRef_ne, hRef_rad⟩ := d8_mobius_step_sound hV0 hrem1_ne hw1_1q hw1_00 hd8_1 hdot1 hrat1
  obtain ⟨cFused, hf_1q, hf_T, hf_Toff, ζ, hζ_ne, hf_ev⟩ :=
      fused_stage01_pair_sound (sym0 := sym0) (s0 := s0) (sym1 := sym1)
      (s1 := s1) hw0_1q hw0_Toff hw0_cap hd1_1q hd1_Toff hd1_cap_pair
  set cPref := cFused ;;ᶜ c0
  set cRef := applyD8Circuit sym1 (applyD8Circuit s1 (decodeWord2Bit wd1)) ;;ᶜ c1
  have hcPref_rem : cPref.eval.1ᴴ * V0 = conj ζ • (cRef.eval.1ᴴ * V0) := by
    rw [show cPref.eval.1 = ζ • cRef.eval.1 by
      simp [cPref, cRef, c1, cStage0, Circuit.eval_seq, hf_ev, Matrix.mul_assoc],
      Matrix.conjTranspose_smul, Complex.star_def, smul_mul_assoc]
  obtain ⟨h00_iff, heta_eq⟩ :=
      matEta_smul_ne_zero ((map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _)).mpr hζ_ne)
      (cRef.eval.1ᴴ * V0)
  refine ⟨cPref, by simp [cPref, c0, CircExt.isOneQubitCircuit, hf_1q, hc0_1q], ?_, ?_,
    hcPref_rem ▸ h00_iff.mpr hRef_ne, by rwa [hcPref_rem, heta_eq]⟩
  · change cFused.count _ + (cosetCircuit idx).count _ ≤ _
    rw [hc0_T]
    omega
  · change cFused.count _ + (cosetCircuit idx).count _ = 0
    rw [hc0_Toff, hf_Toff]

set_option maxHeartbeats 1600000 in
-- Coset Bloch-sphere equator case analysis requires raised heartbeat limit.
theorem exists_coset_equator (g_final : ℝ) :
    let V0 := (hadamard2 * phaseTurn g_final)ᴴ
    ∃ idx : Nat, idx < 6 ∧
      let rem0 := (cosetCircuit idx).eval.1ᴴ * V0
      rem0 0 0 ≠ 0 ∧ (matEta rem0).re = 0 ∧ |(matEta rem0).im| ≤ 1 / 2 := by
  intro V0
  have hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ := by
    dsimp [V0]; rw [← star_eq_conjTranspose];
    exact Unitary.star_mem (Submonoid.mul_mem _ hadamard2_mem (phaseTurn_mem g_final))
  obtain ⟨hcol, hs_full⟩ := unitary_bloch_sphere hV0
  obtain ⟨_, _, hb2, hb3, hb4, hb5⟩ := coset_bloch_coords V0
  set u := V0 0 0
  set v := V0 1 0
  set s1 : ℝ := 2 * (conj u * v).re
  set s2 : ℝ := 2 * (conj u * v).im
  set s3 : ℝ := ‖u‖ ^ 2 - ‖v‖ ^ 2
  have hu_sq : ‖u‖ ^ 2 = 1 / 2 := by
    rw [show u = ((1 / Real.sqrt 2 : ℝ) : ℂ) by
        dsimp [u, V0]
        unfold hadamard2 invSqrtTwo
        rw [phaseTurn_eq]
        simp [Matrix.mul_apply, Fin.sum_univ_two, one_div],
      Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hs3_zero : s3 = 0 := by linarith [hcol, hu_sq]
  have hs_sphere : s1 ^ 2 + s2 ^ 2 = 1 := by nlinarith [hs_full, hs3_zero]
  let rem (idx : Nat) : Matrix (Fin 2) (Fin 2) ℂ := (cosetCircuit idx).eval.1ᴴ * V0
  have heq (M : Matrix (Fin 2) (Fin 2) ℂ) (hre0 : 2 * |(conj (M 0 0) * M 1 0).re| = 0)
      (hbY : 2 * |(conj (M 0 0) * M 1 0).im| ≤ ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2)
      (hpos : 0 < ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2) :
      M 0 0 ≠ 0 ∧ (matEta M).re = 0 ∧ |(matEta M).im| ≤ 1 / 2 := by
    obtain ⟨hu_ne, hu_pos, hre_p, him_p, hv_norm⟩ := matEta_bloch_identities hpos
    rw [hre_p] at hre0
    rw [him_p, hv_norm] at hbY
    have hz_re := (mul_eq_zero.mp (show (2 * ‖M 0 0‖ ^ 2) * |(matEta M).re| = 0 by linarith)
      ).resolve_left (by positivity)
    have hz_im := le_of_mul_le_mul_left (show ‖M 0 0‖ ^ 2 * (2 * |(matEta M).im|) ≤
      ‖M 0 0‖ ^ 2 * 1 by nlinarith [sq_nonneg ‖matEta M‖, hu_pos]) hu_pos
    exact ⟨hu_ne, abs_eq_zero.mp hz_re, by linarith⟩
  have hs3_abs0 : |s3| = 0 := by simp [hs3_zero]
  let B (i : Nat) (z y : ℝ) : Prop := ‖rem i 0 0‖ ^ 2 - ‖rem i 1 0‖ ^ 2 = z ∧
    2 * |(conj (rem i 0 0) * rem i 1 0).re| = |s3| ∧ 2 * |(conj (rem i 0 0) * rem i 1 0).im| = |y|
  have haxis_eq {ip ineg : Nat} {a s : ℝ} (hip : ip < 6) (hin : ineg < 6)
      (hsp : a ^ 2 + s ^ 2 = 1) (ha : |a| ≤ |s|) (hbp : B ip s a) (hbn : B ineg (-s) a) :
      ∃ idx < 6, rem idx 0 0 ≠ 0 ∧ (matEta (rem idx)).re = 0 ∧ |(matEta (rem idx)).im| ≤ 1 / 2 := by
    have hs_pos : 0 < |s| := lt_of_le_of_ne (abs_nonneg s) fun hz => by
      linarith [hsp, sq_abs a, sq_abs s, (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr ha,
        sq_eq_zero_iff.mpr hz.symm]
    by_cases hnn : 0 ≤ s
    · rw [abs_of_nonneg hnn] at ha hs_pos
      exact ⟨ip, hip, heq _ (hbp.2.1.trans hs3_abs0) (by rwa [hbp.2.2, hbp.1]) (by rwa [hbp.1])⟩
    · rw [abs_of_neg (lt_of_not_ge hnn)] at ha hs_pos
      exact ⟨ineg, hin, heq _ (hbn.2.1.trans hs3_abs0) (by rwa [hbn.2.2, hbn.1]) (by rwa [hbn.1])⟩
  rcases le_total |s2| |s1| with h1_dom | h2_dom
  · exact haxis_eq (by omega) (by omega) (by linarith) h1_dom hb2 hb4
  · exact haxis_eq (by omega) (by omega) hs_sphere h2_dom hb3 hb5

theorem exists_foldD8_imag {z : ℂ} (hre : z.re = 0) :
    ∃ sym : Nat, sym < 8 ∧ d8Map sym ((|z.im| : ℝ) : ℂ) = z := by
  by_cases him : 0 ≤ z.im
  · exact ⟨6, by decide, by
      rw [abs_of_nonneg him]
      unfold d8Map
      apply Complex.ext <;> simp [pow_succ, pow_zero, hre]⟩
  · exact ⟨2, by decide, by
      rw [abs_of_neg (lt_of_not_ge him)]
      unfold d8Map
      apply Complex.ext <;> simp [pow_succ, pow_zero, hre]⟩

theorem simplicial_finish_of_prefix_ep {tPref ep_nm rVert mean_num : Nat}
    {U : Matrix (Fin 2) (Fin 2) ℂ} {cPref : Circuit 1}
    (hU : U ∈ unitaryGroup (Fin 2) ℂ) (hep_hi : ep_nm ≤ 1000) (hmean_le : mean_num ≤ 10 ^ 9)
    (hmean_ok : ((ep_nm : ℝ) / 10 ^ 9) ^ 2 / 6 + ((3 / 2) * (116 / 10 ^ 6) +
        ((ep_nm : ℝ) / 10 ^ 9) / 2) * ((ep_nm : ℝ) / 10 ^ 9) ^ 2 ≤ (mean_num : ℝ) / 10 ^ 18)
    (hcov2 : Stage2SquareCov ep_nm rVert 0 0 687194767360)
    (hcPref_1q : (CircExt.isOneQubitCircuit cPref) =
        true) (hcPref_T : cPref.count PrimitiveGate.T ≤ tPref)
    (hcPref_Toff : cPref.count PrimitiveGate.TOFF = 0)
    (hrem3_ne : (cPref.eval.1ᴴ * Uᴴ) 0 0 ≠ 0)
    (hrem3_rad : ‖matEta (cPref.eval.1ᴴ * Uᴴ)‖ ^ 2 ≤ (13456 : ℝ) / (1000000000000 : ℝ)) :
    Nonempty (SimpStepSpecCapEp (45 + tPref) ep_nm mean_num U) := by
  set V0 : Matrix (Fin 2) (Fin 2) ℂ := Uᴴ
  have hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ := by
    dsimp [V0]; rw [← star_eq_conjTranspose]; exact Unitary.star_mem hU
  set rem3 := cPref.eval.1ᴴ * V0
  set z3 := matEta rem3
  have hz3_ub : ‖z3‖ ≤ 116 / 10 ^ 6 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (hrem3_rad.trans (by norm_num))
  obtain ⟨sym3, zw3, _, hzw3_im0, hzw3_le, _, hd8_3⟩ := exists_foldD8 z3
  have hzw3_rad : zw3.re ^ 2 + zw3.im ^ 2 ≤ ((13456 : Nat) : ℝ) / ((1000000000000 : Nat) : ℝ) := by
    have hn3 : ‖zw3‖ = ‖z3‖ := by simpa [hd8_3] using (d8Map_invariants sym3 zw3 0).1.symm
    rw [sq zw3.re, sq zw3.im, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hn3]
    simpa using hrem3_rad
  have hroot3 : SquareMem 0 0 687194767360 zw3 := by
    have hre_hi : zw3.re ≤ 5 / 32768 :=
        (sq_le_sq₀ (hzw3_im0.trans hzw3_le)
        (by norm_num)).mp
        (by nlinarith [show zw3.re ^ 2 + zw3.im ^ 2 ≤ 13456 / 1000000000000 by simpa using hzw3_rad,
              sq_nonneg zw3.im])
    exact squareMem_zero_of_wedge hzw3_im0 hzw3_le (hre_hi.trans_eq (by norm_num))
  obtain ⟨x0', y0', w', hwit2, ⟨hx3_0, hx3_1, hy3_0, hy3_1⟩⟩ :=
    stage2SquareCov_find_leaf (fun x0' y0' w' hsq => isOutsideDom_false_of_rad (by decide)
        (by norm_num) hzw3_im0 hzw3_le hzw3_rad hsq) hcov2 hroot3
  obtain ⟨hw_pos, wd0, wd1, wd2, raw0, raw1, raw2, s0, s1, s2, hwc0, hwc1, hwc2, hlag01, hlag02,
      hlag12, he00, he01, he10, he11⟩ := hwit2
  set x0s : SInt := ⟨false, x0'⟩
  set x1s : SInt := ⟨false, Nat.add x0' w'⟩
  set y0s : SInt := ⟨false, y0'⟩
  set y1s : SInt := ⟨false, Nat.add y0' w'⟩
  have hw_step {w : Nat} {r : Box2DS} (s : Nat) (hc : checkWord2BitBox 45 w r = true) :
      ((CircExt.isOneQubitCircuit (applyD8Circuit s (decodeWord2Bit w))) = true ∧
        (applyD8Circuit s (decodeWord2Bit w)).count PrimitiveGate.T ≤ 45 ∧
        (applyD8Circuit s (decodeWord2Bit w)).count PrimitiveGate.TOFF = 0 ∧
        (applyD8Circuit s (decodeWord2Bit w)).eval.1 0 0 ≠ 0) ∧
      (applyD8Box r s).Mem (matEta (applyD8Circuit s (decodeWord2Bit w)).eval.1) := by
    obtain ⟨h1, hT, hToff, h00, hm⟩ := checkWord2BitBox_sound hc
    obtain ⟨w1, wT, wToff, w00, wm⟩ := applyD8Circuit_sound s (decodeWord2Bit w) r h1 h00 hm
    exact ⟨⟨w1, wT.trans_le hT, wToff.trans hToff, w00⟩, wm⟩
  obtain ⟨hpw0, hmem_v0⟩ := hw_step s0 hwc0
  obtain ⟨hpw1, hmem_v1⟩ := hw_step s1 hwc1
  obtain ⟨hpw2, hmem_v2⟩ := hw_step s2 hwc2
  have hmem_zw3 : (Box2DS.mk x0s x1s y0s y1s).Mem zw3 := by
    simpa only [Box2DS.Mem, x0s, x1s, y0s, y1s, SInt.toInt, Bool.false_eq_true, ↓reduceIte,
      Nat.add_eq, Int.cast_natCast] using And.intro hx3_0 (And.intro hx3_1 (And.intro hy3_0 hy3_1))
  have hx01_lt : (x0s.toInt : ℝ) < (x1s.toInt : ℝ) := by
    simpa only [x0s, x1s, SInt.toInt, Bool.false_eq_true, ↓reduceIte, Nat.add_eq, Int.cast_natCast,
      Nat.cast_lt] using (show x0' < x0' + w' by omega)
  have hy01_lt : (y0s.toInt : ℝ) < (y1s.toInt : ℝ) := by
    simpa only [y0s, y1s, SInt.toInt, Bool.false_eq_true, ↓reduceIte, Nat.add_eq, Int.cast_natCast,
      Nat.cast_lt] using (show y0' < y0' + w' by omega)
  obtain ⟨p, hp_nn, hp_sum, hbary_w⟩ :=
    checkCornerEncl_barycentric_sound hx01_lt hy01_lt hmem_zw3 hmem_v0 hmem_v1 hmem_v2 he00 he01
        he10 he11
  obtain ⟨hch01, hsu_01⟩ := checkLagrangeBox_sound hlag01 (by norm_num) hmem_v0 hmem_v1
  obtain ⟨hch02, hsu_02⟩ := checkLagrangeBox_sound hlag02 (by norm_num) hmem_v0 hmem_v2
  obtain ⟨hch12, hsu_12⟩ := checkLagrangeBox_sound hlag12 (by norm_num) hmem_v1 hmem_v2
  rw [show (ep_nm : ℝ) / ((1000000000 : Nat) : ℝ) = (ep_nm : ℝ) /
      10 ^ 9 by norm_num] at hch01 hch02 hch12 hsu_01 hsu_02 hsu_12
  let cWedge : Fin 3 → Circuit 1 := fun
    | ⟨0, _⟩ => applyD8Circuit s0 (decodeWord2Bit wd0)
    | ⟨1, _⟩ => applyD8Circuit s1 (decodeWord2Bit wd1)
    | ⟨_ + 2, _⟩ => applyD8Circuit s2 (decodeWord2Bit wd2)
  let cStage3 : Fin 3 → Circuit 1 := fun i => applyD8Circuit sym3 (cWedge i)
  have hcW_props (i : Fin 3) : (CircExt.isOneQubitCircuit (cWedge i)) = true ∧
      (cWedge i).count PrimitiveGate.T ≤ 45 ∧
      (cWedge i).count PrimitiveGate.TOFF = 0 ∧ (cWedge i).eval.1 0 0 ≠ 0 := by
    fin_cases i <;> first | exact hpw0 | exact hpw1 | exact hpw2
  have hcS3_props (i : Fin 3) : (CircExt.isOneQubitCircuit (cStage3 i)) = true ∧
      (cStage3 i).count PrimitiveGate.T ≤ 45 ∧
      (cStage3 i).count PrimitiveGate.TOFF = 0 ∧ (cStage3 i).eval.1 0 0 ≠ 0 ∧
      matEta (cStage3 i).eval.1 = d8Map sym3 (matEta (cWedge i).eval.1) := by
    obtain ⟨h1, hT, hToff, h00⟩ := hcW_props i
    obtain ⟨hs1, hsT_eq, hsToff_eq, hs00, hs_eta⟩ := applyD8Circuit_basic sym3 (cWedge i) h1 h00
    exact ⟨hs1, hsT_eq.trans_le hT, hsToff_eq.trans hToff, hs00, hs_eta⟩
  let u3 : Fin 3 → ℂ := fun i => matEta (cStage3 i).eval.1
  have hu3_eq (i : Fin 3) : u3 i = d8Map sym3 (matEta (cWedge i).eval.1) := (hcS3_props i).2.2.2.2
  have hbary_3 : ∑ i : Fin 3, (p i : ℂ) • u3 i = z3 := by
    rw [Fin.sum_univ_three, hu3_eq 0, hu3_eq 1, hu3_eq 2, ← d8Map_smul_real, ← d8Map_smul_real,
      ← d8Map_smul_real, ← d8Map_add, ← d8Map_add, show (p 0 : ℂ) • matEta (cWedge 0).eval.1 +
        (p 1 : ℂ) • matEta (cWedge 1).eval.1 + (p 2 : ℂ) • matEta (cWedge 2).eval.1 = zw3 by
          simpa [cWedge, smul_eq_mul, add_assoc] using hbary_w, hd8_3]
  have hu3_pair_chord (i j : Fin 3) : ‖u3 i - u3 j‖ ≤ (ep_nm : ℝ) / 10 ^ 9 := by
    have h0 (x : ℂ) : ‖x - x‖ ≤ (ep_nm : ℝ) / 10 ^ 9 := by rw [sub_self, norm_zero]; positivity
    rw [hu3_eq i, hu3_eq j, (d8Map_invariants sym3 (matEta (cWedge i).eval.1)
        (matEta (cWedge j).eval.1)).2.1]
    fin_cases i <;> fin_cases j <;> dsimp only [cWedge] <;> with_reducible_and_instances first
      | exact h0 _ | exact hch01 | exact hch02 | exact hch12
      | exact (norm_sub_rev _ _).trans_le hch01 | exact (norm_sub_rev _ _).trans_le hch02
      | exact (norm_sub_rev _ _).trans_le hch12
  have hsu2_symm (a b : ℂ) : ‖(su2EtaMat b)ᴴ * su2EtaMat a - 1‖ = ‖(su2EtaMat a)ᴴ * su2EtaMat b -
      1‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      rw [su2_opNorm_sub_one_sq_eq (isSu2_conjTranspose_mul (su2EtaMat_isSu2 b)
          (su2EtaMat_isSu2 a)),
        su2_opNorm_sub_one_sq_eq (isSu2_conjTranspose_mul (su2EtaMat_isSu2 a) (su2EtaMat_isSu2 b)),
        show ((su2EtaMat b)ᴴ * su2EtaMat a) 0 0 = conj (((su2EtaMat a)ᴴ * su2EtaMat b) 0 0) by
          rw [show (su2EtaMat b)ᴴ * su2EtaMat a = ((su2EtaMat a)ᴴ * su2EtaMat b)ᴴ by
            simp [Matrix.conjTranspose_mul], Matrix.conjTranspose_apply, Complex.star_def],
        Complex.conj_re])
  have hu3_su2_pair (i j : Fin 3) : ‖(su2EtaMat (u3 i))ᴴ * su2EtaMat (u3 j) - 1‖ ≤ (ep_nm : ℝ) /
      10 ^ 9 := by
    have hself (x : ℂ) : ‖(su2EtaMat x)ᴴ * su2EtaMat x - 1‖ ≤ (ep_nm : ℝ) / 10 ^ 9 := by
      rw [show (su2EtaMat x)ᴴ * su2EtaMat x = 1 by
        simpa [star_eq_conjTranspose] using Unitary.star_mul_self_of_mem (su2EtaMat_mem x),
            sub_self, norm_zero]
      positivity
    rw [hu3_eq i, hu3_eq j, (d8Map_invariants sym3 (matEta (cWedge i).eval.1)
        (matEta (cWedge j).eval.1)).2.2.2]
    fin_cases i <;> fin_cases j <;> dsimp only [cWedge] <;> with_reducible_and_instances first
      | exact hself _ | exact hsu_01 | exact hsu_02 | exact hsu_12
      | exact (hsu2_symm _ _).trans_le hsu_01 | exact (hsu2_symm _ _).trans_le hsu_02
      | exact (hsu2_symm _ _).trans_le hsu_12
  have diag2_mem {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : Matrix.of ![![x, 0],
      ![0, y]] ∈ unitaryGroup (Fin 2) ℂ :=
    mem_unitaryGroup_iff.mpr <| Matrix.ext fun r s ↦ by fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_conj_eq_one_of_norm_eq_one, hx, hy]
  have hrem3_mem : rem3 ∈ unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (star_eq_conjTranspose cPref.eval.1 ▸ Unitary.star_mem cPref.eval.2) hV0
  obtain ⟨dr0, dr1, hdr0, hdr1, hrem3_eq, _⟩ := unitary_eq_su2EtaMat_mul_diag hrem3_mem hrem3_ne
  set Drem : Matrix (Fin 2) (Fin 2) ℂ := !![dr0, 0; 0, dr1]
  have hDrem_mem : Drem ∈ unitaryGroup (Fin 2) ℂ := diag2_mem hdr0 hdr1
  have hU_fact : U = Dremᴴ * (su2EtaMat z3)ᴴ * cPref.eval.1ᴴ := by
    have hcP_unit : cPref.eval.1 * cPref.eval.1ᴴ = 1 := by
      simpa [star_eq_conjTranspose] using Unitary.mul_star_self_of_mem cPref.eval.2
    rw [show U = V0ᴴ from (Matrix.conjTranspose_conjTranspose U).symm,
      show V0 = cPref.eval.1 * rem3 by
        rw [show rem3 = cPref.eval.1ᴴ * V0 from rfl, ← Matrix.mul_assoc, hcP_unit, Matrix.one_mul],
            hrem3_eq]
    simp [Drem, z3, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  choose di0 di1 hdi0 hdi1 hS3_eq using fun i =>
    let ⟨d0, d1, hd0, hd1, heq, _⟩ :=
        unitary_eq_su2EtaMat_mul_diag (cStage3 i).eval.2 (hcS3_props i).2.2.2.1
    (⟨d0, d1, hd0, hd1, heq⟩ : ∃ d0 d1 : ℂ, ‖d0‖ = 1 ∧ ‖d1‖ = 1 ∧
      (cStage3 i).eval.1 = su2EtaMat (u3 i) * Matrix.of ![![d0, 0], ![0, d1]])
  have hPi_ex (i : Fin 3) : ∃ γi gi : ℝ,
      Complex.exp ((γi : ℂ) * Complex.I) • phaseTurn gi = Dremᴴ * Matrix.of ![![di0 i, 0],
          ![0, di1 i]] := by
    have hpd : Dremᴴ * Matrix.of ![![di0 i, 0], ![0, di1 i]] = Matrix.of ![![conj dr0 * di0 i, 0],
        ![0, conj dr1 * di1 i]] :=
      Matrix.ext fun r s ↦ by
        fin_cases r <;> fin_cases s <;>
          simp [Drem, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    obtain ⟨γi, gi, heq⟩ := diag_unit_eq_exp_smul_phaseTurn
      (by rw [norm_mul, Complex.norm_conj, hdr0, hdi0 i, one_mul] : ‖conj dr0 * di0 i‖ = 1)
      (by rw [norm_mul, Complex.norm_conj, hdr1, hdi1 i, one_mul] : ‖conj dr1 * di1 i‖ = 1)
    exact ⟨γi, gi, (hpd.trans heq).symm⟩
  choose γ g hPg_eq using hPi_ex
  let circ : Fin 3 → Circuit 1 := fun i => invertCircuit1 (cStage3 i ;;ᶜ cPref)
  have hcirc_all (i : Fin 3) : (CircExt.isOneQubitCircuit (circ i)) = true ∧
      (circ i).count PrimitiveGate.T ≤
      45 + tPref ∧
      (circ i).count PrimitiveGate.TOFF = 0 ∧
      (Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1 =
        Dremᴴ * (su2EtaMat (u3 i))ᴴ * cPref.eval.1ᴴ := by
    obtain ⟨hs1, hsT, hsToff, _, _⟩ := hcS3_props i
    obtain ⟨hi1, hInvT, hiToff, hiEv⟩ := invertCircuit1_sound (cStage3 i ;;ᶜ cPref)
      (by simp [CircExt.isOneQubitCircuit, hs1, hcPref_1q])
    have hDi_unit : Matrix.of ![![di0 i, 0], ![0, di1 i]] *
        (Matrix.of ![![di0 i, 0], ![0, di1 i]])ᴴ = 1 := by
      simpa [star_eq_conjTranspose] using Unitary.mul_star_self_of_mem (diag2_mem (hdi0 i) (hdi1 i))
    refine ⟨hi1, hInvT.trans_le (Nat.add_le_add hsT hcPref_T),
      hiToff.trans (congrArg₂ (· + ·) hsToff hcPref_Toff), ?_⟩
    dsimp [circ]
    rw [hPg_eq i, hiEv]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, hS3_eq i, Matrix.conjTranspose_mul]
    rw [show (Dremᴴ * Matrix.of ![![di0 i, 0], ![0, di1 i]]) *
        ((Matrix.of ![![di0 i, 0], ![0, di1 i]])ᴴ * (su2EtaMat (u3 i))ᴴ * cPref.eval.1ᴴ) =
        Dremᴴ * (Matrix.of ![![di0 i, 0], ![0, di1 i]] * (Matrix.of ![![di0 i, 0], ![0, di1 i]])ᴴ) *
          (su2EtaMat (u3 i))ᴴ * cPref.eval.1ᴴ by simp [Matrix.mul_assoc], hDi_unit, Matrix.mul_one]
  have hDremh_mem : Dremᴴ ∈ unitaryGroup (Fin 2) ℂ := by
    simpa [star_eq_conjTranspose] using Unitary.star_mem hDrem_mem
  have hcPrefh_mem : cPref.eval.1ᴴ ∈ unitaryGroup (Fin 2) ℂ := by
    simpa [star_eq_conjTranspose] using Unitary.star_mem cPref.eval.2
  have hsand_norm (X : Matrix (Fin 2) (Fin 2) ℂ) : ‖Dremᴴ * X * cPref.eval.1ᴴ‖ ≤ ‖X‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul (norm_mul_le _ _)
      (norm_le_one_of_mem_unitaryGroup hcPrefh_mem) (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (by
        linarith [
          mul_le_mul_of_nonneg_right (norm_le_one_of_mem_unitaryGroup hDremh_mem) (norm_nonneg X)]))
  let V : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := fun i =>
      (Complex.exp ((γ i : ℂ) * Complex.I) • phaseTurn (g i)) * (circ i).eval.1
  have hV_pair : ∀ i j, ‖V i - V j‖ ≤ (ep_nm : ℝ) / 10 ^ 9 := fun i j => by
    dsimp [V]
    rw [(hcirc_all i).2.2.2, (hcirc_all j).2.2.2]
    have hu_id : su2EtaMat (u3 j) * (su2EtaMat (u3 j))ᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem (su2EtaMat_mem (u3 j))
    have hmid : (su2EtaMat (u3 i))ᴴ - (su2EtaMat (u3 j))ᴴ = ((su2EtaMat (u3 i))ᴴ *
        su2EtaMat (u3 j) - 1) * (su2EtaMat (u3 j))ᴴ := by
      rw [sub_mul, Matrix.mul_assoc, hu_id, Matrix.mul_one, Matrix.one_mul]
    rw [← sub_mul, ← Matrix.mul_sub, hmid]
    have hsu_h : ‖(su2EtaMat (u3 j))ᴴ‖ ≤ 1 :=
        norm_le_one_of_mem_unitaryGroup (star_eq_conjTranspose (su2EtaMat (u3 j)) ▸ Unitary.star_mem
        (su2EtaMat_mem (u3 j)))
    exact (hsand_norm _).trans ((norm_mul_le _ _).trans ((mul_le_mul (hu3_su2_pair i j) hsu_h
        (norm_nonneg _) (by positivity)).trans_eq (mul_one _)))
  have hV_mean : ‖U - ∑ i : Fin 3, (p i : ℂ) • V i‖ ≤ (mean_num : ℝ) / 10 ^ 18 := by
    have hsu_conj : ∀ w : ℂ, (su2EtaMat w)ᴴ = su2EtaMat (-w) := fun w => by
      unfold su2EtaMat
      rw [norm_neg]
      ext r s : 1
      fin_cases r <;> fin_cases s <;> simp [Matrix.conjTranspose_apply, Complex.conj_ofReal]
    have hsum_eq : U - ∑ i : Fin 3, (p i : ℂ) • V i = Dremᴴ * (su2EtaMat (-z3) - ∑ i : Fin 3,
        (p i : ℂ) • su2EtaMat (-u3 i)) * cPref.eval.1ᴴ := by
      rw [hU_fact]
      simp only [V, fun i => (hcirc_all i).2.2.2, hsu_conj, show ∀ (c : ℂ) (M : Matrix (Fin 2)
          (Fin 2) ℂ), c • (Dremᴴ * M * cPref.eval.1ᴴ) = Dremᴴ * (c • M) * cPref.eval.1ᴴ by
          intro c M
          rw [← smul_mul_assoc, ← mul_smul_comm], ← Finset.sum_mul, ← Finset.mul_sum, ← sub_mul,
              ← Matrix.mul_sub]
    rw [hsum_eq]
    refine (hsand_norm _).trans (su2EtaMat_jung_mean_le_ep ep_nm mean_num hep_hi hmean_ok
        (by simpa using hz3_ub) hp_nn hp_sum ?_ ?_)
    · rw [show ∑ i : Fin 3, (p i : ℂ) • (-u3 i) = -(∑ i : Fin 3,
          (p i : ℂ) • u3 i) by simp [Fin.sum_univ_three], hbary_3]
    · intro i j
      exact (by rw [show -u3 i - (-u3 j) = -(u3 i - u3 j) by ring, norm_neg] : ‖-u3 i - (-u3 j)‖ =
                  ‖u3 i - u3 j‖).trans_le (hu3_pair_chord i j)
  have hV_err : ∀ i, ‖U - V i‖ ≤ ((ep_nm + 1 : ℕ) : ℝ) / 10 ^ 9 := fun i => by
    have hp_sum_c : ∑ j : Fin 3, (p j : ℂ) = 1 := by exact_mod_cast hp_sum
    have hUV_eq : U - V i = (U - ∑ j : Fin 3, (p j : ℂ) • V j) + ∑ j : Fin 3, (p j : ℂ) • (V j -
        V i) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp_sum_c, one_smul]
      abel
    have hmean_r : (mean_num : ℝ) / 10 ^ 18 ≤ 1 / 10 ^ 9 :=
      (div_le_div_of_nonneg_right (by exact_mod_cast hmean_le : (mean_num : ℝ) ≤ 10 ^ 9)
          (by positivity)).trans_eq (by norm_num)
    rw [hUV_eq]
    exact (norm_add_le _ _).trans ((add_le_add hV_mean (fin3_convex_norm_le hp_nn hp_sum (fun j =>
        hV_pair j i))).trans (by
        push_cast
        linarith))
  refine ⟨⟨p, circ, γ, g, hp_nn, hp_sum, fun i => (hcirc_all i).1, fun i => (hcirc_all i).2.1,
      fun i => (hcirc_all i).2.2.1, ?_, hV_err, hV_pair, hV_mean⟩⟩
  intro i
  rw [(hcirc_all i).2.2.2, hU_fact]
  have hcP_id : cPref.eval.1ᴴ * cPref.eval.1 = 1 := by
    simpa only [← star_eq_conjTranspose] using Unitary.star_mul_self_of_mem cPref.eval.2
  have hprod_eq : (Dremᴴ * (su2EtaMat z3)ᴴ * cPref.eval.1ᴴ) * (Dremᴴ * (su2EtaMat (u3 i))ᴴ *
      cPref.eval.1ᴴ)ᴴ = Dremᴴ * ((su2EtaMat z3)ᴴ * su2EtaMat (u3 i)) * Drem := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Dremᴴ * (su2EtaMat z3)ᴴ * cPref.eval.1ᴴ * (cPref.eval.1 * (su2EtaMat (u3 i) * Drem)) =
        Dremᴴ * (su2EtaMat z3)ᴴ * (cPref.eval.1ᴴ * cPref.eval.1) * su2EtaMat (u3 i) *
        Drem by simp [Matrix.mul_assoc], hcP_id]
    simp [Matrix.mul_assoc]
  rw [hprod_eq]
  have hmid := isSu2_conjTranspose_mul (su2EtaMat_isSu2 z3) (su2EtaMat_isSu2 (u3 i))
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _ hDremh_mem hmid.1) hDrem_mem, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, hmid.2, mul_one, ← Matrix.det_mul,
    show Dremᴴ * Drem = 1 by
      simpa [star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hDrem_mem,
    Matrix.det_one]

theorem exists_simp76_step_of_cov {ep_nm rVert mean_num : Nat}
    (hep_hi : ep_nm ≤ 1000) (hmean_le : mean_num ≤ 10 ^ 9)
    (hmean_ok : ((ep_nm : ℝ) / 10 ^ 9) ^ 2 / 6 + ((3 / 2) * (116 / 10 ^ 6) +
        ((ep_nm : ℝ) / 10 ^ 9) / 2) * ((ep_nm : ℝ) / 10 ^ 9) ^ 2 ≤ (mean_num : ℝ) / 10 ^ 18)
    (hcov1 : Stage1SquareCov 0 0 457396837154816)
        (hcov2 : Stage2SquareCov ep_nm rVert 0 0 687194767360)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    Nonempty (SimpStepSpecCapEp 76 ep_nm mean_num U) := by
  set V0 : Matrix (Fin 2) (Fin 2) ℂ := Uᴴ
  have hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ := by
    dsimp [V0]; rw [← star_eq_conjTranspose]; exact Unitary.star_mem hU
  obtain ⟨idx, _, hrem0_ne, hrem0_bloch⟩ := exists_coset_wedge V0 hV0
  set rem0 := (cosetCircuit idx).eval.1ᴴ * V0
  obtain ⟨sym0, zw0, _, hzw0_im0, hzw0_le, hzw0_max, hd8_0⟩ := exists_foldD8 (matEta rem0)
  have hzw0_disc : (zw0.re + 1) ^ 2 + zw0.im ^ 2 ≤ 2 := by
    have hn0 : ‖zw0‖ = ‖matEta rem0‖ := by simpa [hd8_0] using (d8Map_invariants sym0 zw0 0).1.symm
    have := Complex.normSq_eq_norm_sq zw0
    rw [Complex.normSq_apply, hn0] at this
    linarith
  have hroot0 : SquareMem 0 0 2251799813685248 zw0 := by
    have h1 : zw0.re + 1 ≤ 3 / 2 :=
        (sq_le_sq₀ (by linarith [hzw0_im0.trans hzw0_le])
        (by norm_num)).mp (by nlinarith [hzw0_disc, sq_nonneg zw0.im])
    exact squareMem_zero_of_wedge hzw0_im0 hzw0_le ((show zw0.re ≤ 1 /
        2 by linarith).trans_eq (by norm_num))
  obtain ⟨x0', y0', w', u0, hleaf0, hsq0⟩ :=
      checkDetQTree_sound (fun x0' y0' w' hsq =>
      isOutsideDom_false_of_dom0 hzw0_im0 hzw0_le hzw0_disc hsq) stageQTree0Stg1Had 0 0
      2251799813685248 stageQTree0Stg1Had_ok hroot0
  unfold checkDetLeaf at hleaf0
  set wid0 := Nat.div u0 8
  set s0 := Nat.mod u0 8
  cases hpb0 : forest256GetOpt stageBoxes0Stg1Had wid0 with
  | none => simp [hpb0] at hleaf0
  | some pb0 =>
    simp only [hpb0] at hleaf0
    obtain ⟨wd0, _, hw0_chk⟩ := forest256GetOpt_all2_right stageWords0Stg1Had_ok hpb0
    obtain ⟨hw0_1q, hw0_Toff, hw0_00, hmem_raw0, hw0_cap⟩ := checkWord0CapPacked_sound hw0_chk
    obtain ⟨hwc0_1q, _, _, hwc0_00, hmem_wb0⟩ :=
        applyD8Circuit_sound s0 (decodeWord2Bit wd0) _ hw0_1q hw0_00 hmem_raw0
    obtain ⟨hdot0, hrat0⟩ := checkDetBox_geom_sound hleaf0 (by norm_num) hmem_wb0 hsq0
    obtain ⟨hrem1_ne, hrem1_rad⟩ :=
        d8_mobius_step_sound hV0 hrem0_ne hwc0_1q hwc0_00 hd8_0 hdot0 hrat0
    obtain ⟨cPref, hcP_1q, hcP_T, hcP_Toff, hrem3_ne, hrem3_rad⟩ :=
        fused_stage01_step_sound (capFi := 5)
        (capNoFi := 3) hV0 hcov1 hw0_1q hw0_Toff hw0_cap hrem1_ne hrem1_rad
    rw [show max (26 + 5) (28 + 3) = 31 by decide] at hcP_T
    exact simplicial_finish_of_prefix_ep hU hep_hi hmean_le hmean_ok hcov2 hcP_1q hcP_T hcP_Toff
        hrem3_ne hrem3_rad

theorem exists_top73_step_of_cov {ep_nm rVert mean_num : Nat}
    (hep_hi : ep_nm ≤ 1000) (hmean_le : mean_num ≤ 10 ^ 9)
    (hmean_ok :
      ((ep_nm : ℝ) / 10 ^ 9) ^ 2 / 6 +
        ((3 / 2) * (116 / 10 ^ 6) + ((ep_nm : ℝ) / 10 ^ 9) / 2) *
          ((ep_nm : ℝ) / 10 ^ 9) ^ 2 ≤
        (mean_num : ℝ) / 10 ^ 18)
    (hcovTop : Top1DSegCov 0 2251799813685248)
    (hcov2 : Stage2SquareCov ep_nm rVert 0 0 687194767360)
    (g_final : ℝ) :
    Nonempty (SimpStepSpecCapEp 73 ep_nm mean_num (hadamard2 * phaseTurn g_final)) := by
  set U : Matrix (Fin 2) (Fin 2) ℂ := hadamard2 * phaseTurn g_final
  have hU : U ∈ unitaryGroup (Fin 2) ℂ := Submonoid.mul_mem _ hadamard2_mem (phaseTurn_mem g_final)
  set V0 : Matrix (Fin 2) (Fin 2) ℂ := Uᴴ
  have hV0 : V0 ∈ unitaryGroup (Fin 2) ℂ := by
    dsimp [V0]; rw [← star_eq_conjTranspose]; exact Unitary.star_mem hU
  obtain ⟨idx, _, hrem0_ne, hrem0_re, hrem0_im⟩ := exists_coset_equator g_final
  obtain ⟨hc0_1q, hc0_T, hc0_Toff⟩ := cosetCircuit_props idx
  set c0 := cosetCircuit idx
  set rem0 : Matrix (Fin 2) (Fin 2) ℂ := c0.eval.1ᴴ * V0
  obtain ⟨sym0, _, hd8_0⟩ := exists_foldD8_imag (z := matEta rem0) hrem0_re
  set zw0 : ℂ := ((|(matEta rem0).im| : ℝ) : ℂ)
  have hzw0_lo : ((0 : Nat) : ℝ) / (2 ^ 52 : ℝ) ≤ zw0.re :=
    by simp [zw0]
  have hzw0_hi : zw0.re ≤ ((0 + 2251799813685248 : Nat) : ℝ) / (2 ^ 52 : ℝ) :=
    (show zw0.re ≤ 1 / 2 from hrem0_im).trans_eq (by norm_num)
  obtain ⟨x0', w', ⟨wd0, rawBox, s0, hwb28, hdet1d⟩, hx_lo, hx_hi⟩ :=
      top1DSegCov_find_leaf hcovTop hzw0_lo hzw0_hi
  obtain ⟨hd0_1q, hd0_T, hd0_Toff, hd0_00, hmem_raw0⟩ := checkWord2BitBox_sound hwb28
  obtain ⟨hwc0_1q, _, _, hwc0_00, hmem_wb0⟩ :=
      applyD8Circuit_sound s0 (decodeWord2Bit wd0) rawBox hd0_1q hd0_00 hmem_raw0
  obtain ⟨hs0_1q, hs0_T, hs0_Toff⟩ := applyD8Circuit_counts s0 (decodeWord2Bit wd0) hd0_1q
  obtain ⟨hcS0_1q, hcS0_T, hcS0_Toff⟩ := applyD8Circuit_counts sym0 _ hs0_1q
  obtain ⟨hdot0, hrat0⟩ :=
      checkDetBox1D_geom_sound hdet1d (by norm_num) hmem_wb0 hx_lo hx_hi (rfl : zw0.im = 0)
  obtain ⟨hrem3_ne, hrem3_rad⟩ :=
      d8_mobius_step_sound hV0 hrem0_ne hwc0_1q hwc0_00 hd8_0 hdot0 hrat0
  set cStage0 := applyD8Circuit sym0 (applyD8Circuit s0 (decodeWord2Bit wd0))
  set cPref := cStage0 ;;ᶜ c0
  exact simplicial_finish_of_prefix_ep (tPref := 28) hU hep_hi hmean_le hmean_ok hcov2
    (by simp [cPref, cStage0, c0, CircExt.isOneQubitCircuit, hcS0_1q, hc0_1q])
    (by change cStage0.count _ + c0.count _ ≤ 28; rw [hcS0_T, hs0_T, hc0_T]; omega)
    (by change cStage0.count _ + c0.count _ = 0; rw [hcS0_Toff, hs0_Toff, hc0_Toff, hd0_Toff])
    hrem3_ne hrem3_rad
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge.Synth

section
open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.GQSP
  QuantumComputation.Specs.PhotochemistrySolution.OvBidir
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationCore
open QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationProgram
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationTop
  QuantumComputation.Specs.PhotochemistrySolution.SelectSymDyn
open QuantumComputation.Specs.PhotochemistrySolution.SelectSymDynInstance
  QuantumComputation.Specs.PhotochemistrySolution.BucketRouterCircuit
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
open QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge
open scoped ComplexOrder Circuit.Notation Fin.CommRing
open WithLp Polynomial ComplexConjugate PhotochemistrySolution.SelectEulerRot32
open PhotochemistrySolution.SelectCsa64GqspWalk PhotochemistrySolution.SelectLcu70Rot32
def concretePhaseStateLo5_4 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .S 0, .H 0, .Z 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .X 0, .S 0, .H 0 ]
def concretePhaseCyclotomicStateLo5_4 : CyclotomicState :=
  { u := ⟨-537600, -756736, 207872, -181248⟩,
    v := ⟨-867328, -492544, 457728, -238592⟩,
    k := 41 }

def concretePhaseStateLo5_5 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .H 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .S 0, .H 0 ]
def concretePhaseCyclotomicStateLo5_5 : CyclotomicState :=
  { u := ⟨-467968, 96256, -136192, 172032⟩,
    v := ⟨-506880, 92160, 29696, 83968⟩,
    k := 39 }

def concretePhaseStateLo5_6 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .H 0,
    .S 0, .H 0, .Z 0, .Z 0, .Z 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .Z 0, .H 0, .Z 0, .S 0 ]
def concretePhaseCyclotomicStateLo5_6 : CyclotomicState :=
  { u := ⟨-370688, 77824, -79872, 260096⟩,
    v := ⟨36864, -192512, -38912, 540672⟩,
    k := 39 }

def concretePhaseStateLo5_7 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .H 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .H 0, .S 0 ]
def concretePhaseCyclotomicStateLo5_7 : CyclotomicState :=
  { u := ⟨-242688, 7168, -242688, 402432⟩,
    v := ⟨-123904, -408576, 254976, 150528⟩,
    k := 39 }

def concretePhaseStateLo5_8 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .S 0,
    .H 0, .X 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .H 0 ]
def concretePhaseCyclotomicStateLo5_8 : CyclotomicState :=
  { u := ⟨-245760, -101376, -325632, -82944⟩,
    v := ⟨-414720, 77824, -414720, -126976⟩,
    k := 39 }

def concretePhaseStateSu2 (j : ℕ) : Circuit 1 :=
    if j = 4 then concretePhaseStateLo5_4 else if j = 5 then concretePhaseStateLo5_5 else if j =
    6 then concretePhaseStateLo5_6 else if j = 7 then concretePhaseStateLo5_7 else if j =
    8 then concretePhaseStateLo5_8 else concretePhaseState j
def concretePhaseErrSu2 (j : ℕ) : ℝ :=
  match j with
  | 1 => 0
  | 2 => 0
  | 3 => 1 / 10 ^ 17
  | 4 => 862 / 10 ^ 9
  | 5 => 389 / 10 ^ 9
  | 6 => 834 / 10 ^ 9
  | 7 => 724 / 10 ^ 9
  | 8 => 1889 / 10 ^ 9
  | _ => concretePhaseErr j

theorem concretePhaseErrSu2_nonneg (j : ℕ) : 0 ≤ concretePhaseErrSu2 j := by
  unfold concretePhaseErrSu2
  split <;> first | positivity | exact concretePhaseErr_nonneg _

theorem concretePhaseStateLo5_4_approx : ∃ α : ℝ,
    ‖WithLp.toLp 2 (concretePhaseStateLo5_4.eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 4)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErrSu2 4 :=
  circuit_approx_plusPhase concretePhaseStateLo5_4 rfl concretePhaseCyclotomicStateLo5_4 rfl 20 4
      rfl
    (-2369493389245399 / 2630506610754601) (-1142394900000000 / 2630506610754601) cosMid4 (2 /
        10 ^ 16) sinMid4 (1 / 10 ^ 9)
    (concretePhaseErrSu2 4) (by norm_num [concretePhaseErrSu2])
        (by norm_num) cos_two_pi_div_two_pow_4_approx sin_two_pi_div_two_pow_4_approx
    (by unfold concretePhaseCyclotomicStateLo5_4 concretePhaseErrSu2 cosMid4 sinMid4 sqrtTwoMid
          sqrtTwoRad; norm_num)
theorem concretePhaseStateLo5_5_approx : ∃ α : ℝ,
    ‖WithLp.toLp 2 (concretePhaseStateLo5_5.eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 5)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErrSu2 5 :=
  circuit_approx_plusPhase concretePhaseStateLo5_5 rfl concretePhaseCyclotomicStateLo5_5 rfl 19 5
      rfl
    (-2493453878185479 / 2506546121814521) (255853900000000 / 2506546121814521) cosMid5 (2 /
        10 ^ 16) sinMid5 (1 / 10 ^ 9)
    (concretePhaseErrSu2 5) (by norm_num [concretePhaseErrSu2])
        (by norm_num) cos_two_pi_div_two_pow_5_approx sin_two_pi_div_two_pow_5_approx
    (by unfold concretePhaseCyclotomicStateLo5_5 concretePhaseErrSu2 cosMid5 sinMid5 sqrtTwoMid
          sqrtTwoRad; norm_num)
theorem concretePhaseStateLo5_6_approx : ∃ α : ℝ,
    ‖WithLp.toLp 2 (concretePhaseStateLo5_6.eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 6)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErrSu2 6 :=
  circuit_approx_plusPhase concretePhaseStateLo5_6 rfl concretePhaseCyclotomicStateLo5_6 rfl 19 6
      rfl
    (-97586131282431 / 102413868717569) (31073260000000 / 102413868717569) cosMid6 (2 /
        10 ^ 16) sinMid6 (1 / 10 ^ 9)
    (concretePhaseErrSu2 6) (by norm_num [concretePhaseErrSu2])
        (by norm_num) cos_two_pi_div_two_pow_6_approx sin_two_pi_div_two_pow_6_approx
    (by unfold concretePhaseCyclotomicStateLo5_6 concretePhaseErrSu2 cosMid6 sinMid6 sqrtTwoMid
          sqrtTwoRad; norm_num)
theorem concretePhaseStateLo5_7_approx : ∃ α : ℝ,
    ‖WithLp.toLp 2 (concretePhaseStateLo5_7.eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 7)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErrSu2 7 :=
  circuit_approx_plusPhase concretePhaseStateLo5_7 rfl concretePhaseCyclotomicStateLo5_7 rfl 19 7
      rfl
    (-623742334197151 / 626257665802849) (56072850000000 / 626257665802849) cosMid7 (2 /
        10 ^ 16) sinMid7 (1 / 10 ^ 9)
    (concretePhaseErrSu2 7) (by norm_num [concretePhaseErrSu2])
        (by norm_num) cos_two_pi_div_two_pow_7_approx sin_two_pi_div_two_pow_7_approx
    (by unfold concretePhaseCyclotomicStateLo5_7 concretePhaseErrSu2 cosMid7 sinMid7 sqrtTwoMid
          sqrtTwoRad; norm_num)
theorem concretePhaseStateLo5_8_approx : ∃ α : ℝ,
    ‖WithLp.toLp 2 (concretePhaseStateLo5_8.eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 8)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErrSu2 8 :=
  circuit_approx_plusPhase concretePhaseStateLo5_8 rfl concretePhaseCyclotomicStateLo5_8 rfl 19 8
      rfl
    (-76152842613281 / 154277842613281) (-134173012500000 / 154277842613281) cosMid8 (2 /
        10 ^ 16) sinMid8 (1 / 10 ^ 9)
    (concretePhaseErrSu2 8) (by norm_num [concretePhaseErrSu2])
        (by norm_num) cos_two_pi_div_two_pow_8_approx sin_two_pi_div_two_pow_8_approx
    (by unfold concretePhaseCyclotomicStateLo5_8 concretePhaseErrSu2 cosMid8 sinMid8 sqrtTwoMid
          sqrtTwoRad; norm_num)
theorem concretePhaseStateSu2_approx_le_8 {j : ℕ} (hj1 : 1 ≤ j) (hj8 : j ≤ 8) : ∃ α : ℝ,
    ‖WithLp.toLp 2 ((concretePhaseStateSu2 j).eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErrSu2 j := by
  interval_cases j
  exacts [
    by simpa [concretePhaseStateSu2, concretePhaseErrSu2, concretePhaseErr] using
      concretePhaseState_approx_tight_1,
    by simpa [concretePhaseStateSu2, concretePhaseErrSu2, concretePhaseErr] using
      concretePhaseState_approx_tight_2,
    by simpa [concretePhaseStateSu2, concretePhaseErrSu2, concretePhaseErr] using
      concretePhaseState_approx_tight_3,
    concretePhaseStateLo5_4_approx, concretePhaseStateLo5_5_approx,
    concretePhaseStateLo5_6_approx, concretePhaseStateLo5_7_approx, concretePhaseStateLo5_8_approx]

theorem concretePhaseStateSu2_count_toff (j : ℕ) :
    (concretePhaseStateSu2 j).count PrimitiveGate.TOFF = 0 := by
  unfold concretePhaseStateSu2
  split_ifs <;> first | rfl | exact concretePhaseState_count_toff j
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge
open scoped Polynomial
open Real ComplexConjugate Polynomial PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectEulerRot32
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RieszQspCovering hiding mgfPot


theorem exists_simp76_step_ep460 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    Nonempty (SimpStepSpecCapEp 76 460 35304 U) :=
  Synth.exists_simp76_step_of_cov (ep_nm := 460) (rVert := 540) (mean_num := 35304)
    (by decide) (by decide) (by norm_num) Synth.root_stage1_cov Synth.root_stage2_cov_460 U hU

theorem exists_top73_step_ep460 (g_final : ℝ) :
    Nonempty (SimpStepSpecCapEp 73 460 35304 (hadamard2 * phaseTurn g_final)) :=
  Synth.exists_top73_step_of_cov (ep_nm := 460) (rVert := 540) (mean_num := 35304)
    (by decide) (by decide) (by norm_num)
    PhotochemistrySolution.TopHad.Synth.top1D73_cov
    Synth.root_stage2_cov_460 g_final

theorem abs_re_entry00_le_opNorm (M : Matrix (Fin 2) (Fin 2) ℂ) :
    |(M 0 0).re| ≤ ‖M‖ := by
  refine (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp ?_
  nlinarith [col0_four_sq_le_opNorm_sq M, sq_abs (M 0 0).re, sq_nonneg (M 0 0).im,
    sq_nonneg (M 1 0).re, sq_nonneg (M 1 0).im]

theorem two_mul_chordalY_le_norm_sub_one_sq {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSU2 Q) :
    2 * chordalY Q ≤ ‖Q - 1‖ ^ 2 := by
  have hcol := col0_four_sq_le_opNorm_sq (Q - 1)
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (one_ne_zero : (1 : Fin 2) ≠ 0), sub_zero, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im] at hcol
  unfold chordalY
  nlinarith [(isSU2_entries hQ).2.2]
theorem isSU2_of_isSu2_conjTranspose {Q : Matrix (Fin 2) (Fin 2) ℂ} (hQ : IsSu2 Q) : IsSU2 Qᴴ := by
  refine ⟨by rw [← star_eq_conjTranspose]; exact Unitary.star_mem hQ.1, ?_⟩
  have hd :=
      congrArg (starRingEnd ℂ) hQ.2; rw [Matrix.det_fin_two] at hd ⊢;
      simp only [Matrix.conjTranspose_apply, Complex.star_def, map_sub, map_mul,
      map_one] at hd ⊢; linear_combination hd
theorem exp_mul_le_secant {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    Real.exp (q * s) ≤ (1 - q) + q * Real.exp s := by
  have hcomb : 1 ≤ (1 - q) * Real.exp (-q * s) + q * Real.exp ((1 - q) * s) := by
    nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-q * s)) (sub_nonneg.mpr hq1),
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp ((1 - q) * s)) hq0]
  have hmul := mul_le_mul_of_nonneg_right hcomb (Real.exp_pos (q * s)).le
  rwa [one_mul, add_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add,
    show -q * s + q * s = 0 by ring, show (1 - q) * s + q * s = s by ring,
    Real.exp_zero, mul_one] at hmul

theorem hoeffding_fin3_mgf {p X : Fin 3 → ℝ} {R μ : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hpsum : ∑ i : Fin 3, p i = 1)
    (hR : 0 ≤ R) (hpair : ∀ i k, |X i - X k| ≤ R) (_hμ : 0 ≤ μ) :
    ∑ i : Fin 3, p i * Real.exp (μ * X i) ≤ Real.exp (μ * (∑ i : Fin 3, p i * X i) + (μ * R) ^ 2 /
        8) := by
  have hp3 : p 0 + p 1 + p 2 = 1 := by simpa [Fin.sum_univ_three, add_assoc] using hpsum
  rcases eq_or_lt_of_le hR with rfl | hR_pos
  · have hX : ∀ i, X i = X 0 := fun i => by linarith [abs_le.mp (hpair i 0)]
    simp only [hX, ← Finset.sum_mul, hpsum, one_mul, mul_zero, zero_pow two_ne_zero, zero_div,
                                              add_zero]
    exact le_rfl
  · set a : ℝ := min (X 0) (min (X 1) (X 2))
    have ha_le (i : Fin 3) : a ≤ X i := by
      fin_cases i
      exacts [min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
        (min_le_right _ _).trans (min_le_right _ _)]
    obtain ⟨k₀, hak₀⟩ : ∃ k₀ : Fin 3, a = X k₀ :=
      (min_choice (X 0) (min (X 1) (X 2))).elim (fun h0 => ⟨0, h0⟩)
        (fun h12 => (min_choice (X 1) (X 2)).elim (fun h1 => ⟨1, h12.trans h1⟩)
            (fun h2 => ⟨2, h12.trans h2⟩))
    let q : Fin 3 → ℝ := fun i => (X i - a) / R
    have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (by linarith [ha_le i]) hR_pos.le
    have hq1 (i : Fin 3) : q i ≤ 1 :=
      (div_le_one hR_pos).mpr (hak₀ ▸ (le_abs_self _).trans (hpair i k₀))
    have hX_q (i : Fin 3) : X i = a + q i * R := by
      dsimp only [q]
      field_simp [hR_pos.ne']
      ring
    set qb : ℝ := ∑ i : Fin 3, p i * q i
    have hqb0 : 0 ≤ qb := Finset.sum_nonneg fun i _ => mul_nonneg (hp0 i) (hq0 i)
    have hqb1 : qb ≤ 1 :=
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq1 i)
        (hp0 i)).trans_eq (by simp [hpsum])
    have hmean : ∑ i : Fin 3, p i * X i = a + qb * R := by
      rw [Fin.sum_univ_three, hX_q 0, hX_q 1, hX_q 2]
      dsimp only [qb]
      rw [Fin.sum_univ_three]
      linear_combination a * hp3
    have hsec : ∑ i : Fin 3, p i * Real.exp (μ * X i) ≤ Real.exp (μ * a) * ((1 - qb) + qb *
        Real.exp (μ * R)) := by
      refine (Finset.sum_le_sum (g := fun i => p i * (Real.exp (μ * a) * ((1 - q i) +
        q i * Real.exp (μ * R))))
        fun i _ => mul_le_mul_of_nonneg_left ?_ (hp0 i)).trans_eq ?_
      · rw [show μ * X i = μ * a + q i * (μ * R) by linear_combination μ * hX_q i, Real.exp_add]
        exact mul_le_mul_of_nonneg_left (exp_mul_le_secant (hq0 i) (hq1 i) (μ * R))
          (Real.exp_pos _).le
      · dsimp [qb]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        linear_combination Real.exp (μ * a) * hp3
    have hm :=
        mul_le_mul_of_nonneg_left (hoeffding_two_point hqb0 hqb1 (μ * R))
        (Real.exp_pos (μ * (a + qb * R))).le
    have hlhs : Real.exp (μ * (a + qb * R)) * ((1 - qb) * Real.exp (-qb * (μ * R)) + qb *
        Real.exp ((1 - qb) * (μ * R))) = Real.exp (μ * a) * ((1 - qb) + qb * Real.exp (μ * R)) := by
      rw [mul_add, mul_left_comm _ (1 - qb), ← Real.exp_add, mul_left_comm _ qb, ← Real.exp_add,
          show μ * (a + qb * R) + -qb * (μ * R) = μ * a by ring, show μ * (a + qb * R) + (1 - qb) *
          (μ * R) = μ * a + μ * R by ring,
          Real.exp_add]
      ring
    have hrhs : Real.exp (μ * (a + qb * R)) * Real.exp ((μ * R) ^ 2 / 8) =
        Real.exp (μ * (∑ i : Fin 3, p i * X i) + (μ * R) ^ 2 / 8) := by rw [← Real.exp_add, hmean]
    rw [hlhs, hrhs] at hm
    exact hsec.trans hm
def ChainSU2R (E D : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (γ : ℝ) : Prop :=
    ∀ θ : ℝ, E θ ∈ unitaryGroup (Fin 2) ℂ ∧ D θ ∈ unitaryGroup (Fin 2) ℂ ∧
    IsSU2 ((Complex.exp (((γ : ℝ) : ℂ) * Complex.I) • D θ) * (E θ)ᴴ)
theorem chain_left_mul_unitaryR {M : ℕ} {θ_fn : Fin M → ℝ} {E D V : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {γ u : ℝ} (hC : ChainSU2R E D γ) (hV : ∀ θ, V θ ∈ unitaryGroup (Fin 2) ℂ) : ChainSU2R (fun θ ↦
    V θ * E θ) (fun θ ↦ V θ * D θ) γ ∧ mgfPot M u (fun j ↦ V (θ_fn j) * E (θ_fn j))
    (fun j ↦ V (θ_fn j) * D (θ_fn j)) γ = mgfPot M u (fun j ↦ E (θ_fn j))
    (fun j ↦ D (θ_fn j)) γ := by
  have hprod : ∀ θ : ℝ, (Complex.exp (((γ : ℝ) : ℂ) * Complex.I) • (V θ * D θ)) * (V θ * E θ)ᴴ =
      V θ * ((Complex.exp (((γ : ℝ) : ℂ) * Complex.I) • D θ) * (E θ)ᴴ) * (V θ)ᴴ := by
    intro θ; rw [Matrix.conjTranspose_mul, ← mul_smul_comm]; simp only [Matrix.mul_assoc]
  refine ⟨fun θ ↦ ?_, ?_⟩
  · obtain ⟨hEθ, hDθ, hQθ⟩ :=
        hC θ; refine ⟨mul_mem (hV θ) hEθ, mul_mem (hV θ) hDθ,
        ?_⟩; rw [hprod θ]; exact (isSU2_conj_unitary (hV θ) hQθ).1
  · unfold mgfPot
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hprod (θ_fn j), (isSU2_conj_unitary (hV (θ_fn j)) (hC (θ_fn j)).2.2).2]


def simpFusedChainOfCircuits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ) (W : Matrix ι ι ℂ)
    (c₀ : Circuit 1) : {m : ℕ} → (Fin m → Circuit 1) → Matrix ι ι ℂ
  | 0, _ => e c₀.eval.1 * sigOp e W true
  | m + 1, stepC =>
      e (stepC (Fin.last m)).eval.1 *
        (sigOp e W false * sigOp e W true) *
        simpFusedChainOfCircuits e W c₀ (fun i ↦ stepC (Fin.castSucc i))

def snocCircuits {m : ℕ} (stepC : Fin m → Circuit 1) (top : Circuit 1) (idx : Fin (m + 1)) :
    Circuit 1 := if h : idx.val < m then stepC ⟨idx.val, h⟩ else top
theorem snocCircuits_last {m : ℕ} (stepC : Fin m → Circuit 1)
    (top : Circuit 1) : snocCircuits stepC top (Fin.last m) = top := by simp [snocCircuits]
theorem snocCircuits_castSucc {m : ℕ} (stepC : Fin m → Circuit 1) (top : Circuit 1)
    (i : Fin m) : snocCircuits stepC top (Fin.castSucc i) = stepC i := by
  simp [snocCircuits, i.isLt]
theorem simpFusedChainOfCircuits_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ) (he_star : ∀ M, (e M)ᴴ = e Mᴴ)
    {W : Matrix ι ι ℂ} (hW : W ∈ _root_.unitary (Matrix ι ι ℂ)) (hWc : W ∈ qubitCommutant e)
    (c₀ : Circuit 1) :
    ∀ {m : ℕ} (stepC : Fin m → Circuit 1),
      simpFusedChainOfCircuits e W c₀ stepC ∈ _root_.unitary (Matrix ι ι ℂ)
  | 0, _ =>
      mul_mem (e_mem_unitary e he_star c₀.eval.2)
        (sigOp_mem_unitary e he_star hW hWc true)
  | _ + 1, stepC =>
      mul_mem (mul_mem (e_mem_unitary e he_star (stepC _).eval.2)
        (mul_mem (sigOp_mem_unitary e he_star hW hWc false)
          (sigOp_mem_unitary e he_star hW hWc true)))
        (simpFusedChainOfCircuits_mem_unitary e he_star hW hWc c₀
          (fun i ↦ stepC (Fin.castSucc i)))

theorem simpFusedChainOfCircuits_envFiberOp_scalarWalk {N : ℕ} (q : Wire N)
    (θ_fn : WireEnv q → ℝ) (c₀ : Circuit 1) :
    ∀ {m : ℕ} (stepC : Fin m → Circuit 1),
      simpFusedChainOfCircuits (eQWire q) (envFiberOp q (fun a ↦ scalarWalk (θ_fn a))) c₀ stepC =
        envFiberOp q (fun a ↦ simpFusedChainOfCircuits idE (scalarWalk (θ_fn a)) c₀ stepC)
  | 0, _ => by
      simp only [simpFusedChainOfCircuits, idE, AlgHom.coe_id, id_eq];
      rw [sigOp_envFiberOp_scalarWalk, ← envFiberOp_const q c₀.eval.1, envFiberOp_mul]
  | _ + 1, stepC => by
      simp only [simpFusedChainOfCircuits, idE, AlgHom.coe_id, id_eq]
      rw [simpFusedChainOfCircuits_envFiberOp_scalarWalk q θ_fn c₀ (fun i ↦ stepC (Fin.castSucc i)),
          sigOp_envFiberOp_scalarWalk, sigOp_envFiberOp_scalarWalk,
          ← envFiberOp_const q (stepC _).eval.1, envFiberOp_mul, envFiberOp_mul, envFiberOp_mul]

theorem conj_simpFusedChainOfCircuits_splitKronecker {N : ℕ} (q : Wire N)
    {U_env : _root_.unitary (Matrix (WireEnv q) (WireEnv q) ℂ)}
    (W_d : Operator (2 ^ N)) (c₀ : Circuit 1) :
    ∀ {m : ℕ} (stepC : Fin m → Circuit 1),
      let U_tot : Operator (2 ^ N) := splitKronecker q 1 U_env.1
      U_tot * simpFusedChainOfCircuits (eQWire q) W_d c₀ stepC * U_totᴴ =
        simpFusedChainOfCircuits (eQWire q) (U_tot * W_d * U_totᴴ) c₀ stepC
  | 0, _ => by
      intro U_tot
      have hU_star := (splitKronecker_one_unitary_mul q U_env).1
      simp only [simpFusedChainOfCircuits]; rw [← conj_sigOp_splitKronecker q W_d true]
      conv_rhs => rw [← conj_eQWire_splitKronecker q (U_env := U_env) c₀.eval.1]
      rw [conj_unitary_mul hU_star]
  | _ + 1, stepC => by
      intro U_tot
      have hU_star := (splitKronecker_one_unitary_mul q U_env).1
      simp only [simpFusedChainOfCircuits]
      rw [← conj_simpFusedChainOfCircuits_splitKronecker q W_d c₀ (fun i ↦ stepC (Fin.castSucc i)),
          ← conj_sigOp_splitKronecker q W_d false, ← conj_sigOp_splitKronecker q W_d true]
      conv_rhs => rw [← conj_eQWire_splitKronecker q (U_env := U_env) (stepC _).eval.1]
      rw [conj_unitary_mul hU_star, conj_unitary_mul hU_star, conj_unitary_mul hU_star]

theorem simpFusedChainOfCircuits_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ) {W P : Matrix ι ι ℂ}
    (he : ∀ M, Commute (e M) P)
    (hsF : Commute (sigOp e W false) P) (hsT : Commute (sigOp e W true) P)
    (c₀ : Circuit 1) :
    ∀ {m : ℕ} (stepC : Fin m → Circuit 1),
      Commute (simpFusedChainOfCircuits e W c₀ stepC) P
  | 0, _ => (he _).mul_left hsT
  | _ + 1, stepC =>
      ((he _).mul_left (hsF.mul_left hsT)).mul_left
        (simpFusedChainOfCircuits_commute e he hsF hsT c₀ (fun i ↦ stepC (Fin.castSucc i)))

theorem foldFin_step_mul_proj_circuits {N : ℕ}
    (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Operator (2 ^ N))
    (rotU : Circuit 1 → Unitary (2 ^ N)) (V : Unitary (2 ^ N)) (W P : Operator (2 ^ N))
    (he : ∀ M, Commute (e M) P)
    (hsF : Commute (sigOp e W false) P)
    (hsT : Commute (sigOp e W true) P)
    (hstep : ∀ c : Circuit 1, (rotU c * V).1 * P =
      (e c.eval.1 * (sigOp e W false * sigOp e W true)) * P)
    (c₀ : Circuit 1) :
    ∀ {m : ℕ} (stepC : Fin m → Circuit 1),
      (foldFinUnitary (m := m) fun s ↦ rotU (stepC s) * V).1 *
        ((e c₀.eval.1 * sigOp e W true) * P) =
      simpFusedChainOfCircuits e W c₀ stepC * P
  | 0, _ => by simp only [foldFinUnitary, OneMemClass.coe_one, one_mul, simpFusedChainOfCircuits]
  | m + 1, stepC => by
      have ih :=
          foldFin_step_mul_proj_circuits e rotU V W P he hsF hsT hstep c₀ (fun i ↦
          stepC (Fin.castSucc i))
      have hcomm :=
          (simpFusedChainOfCircuits_commute e he hsF hsT c₀ (fun i ↦ stepC (Fin.castSucc i))).eq
      change ((rotU (stepC (Fin.last m)) * V) *
          foldFinUnitary (m := m) (fun i ↦ rotU (stepC (Fin.castSucc i)) * V)).1 *
          ((e c₀.eval.1 * sigOp e W true) * P) = _
      rw [Submonoid.coe_mul, mul_assoc, ih, hcomm, ← mul_assoc, hstep, mul_assoc, ← hcomm];
      simp only [simpFusedChainOfCircuits, mul_assoc]
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge

namespace QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge
open Real ComplexConjugate PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.UnembedIdleAncillas PhotochemistrySolution.UnembedO3Bridge
open PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.FusedUnembedLGen PhotochemistrySolution.Stage5StackCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCerts (alphaTier1WalkFull
    sMax_tier1Walk_full hs_tier1Walk_full_le_sMax)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RieszQspCovering
    (commute_walk_data_locCat8SharedGen pureRotLocalUnitary pureRotLocalUnitary_val)
noncomputable def bidirBodyPureTopHadLocalUnitary
    {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n d tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D)
    (rot0 rotTop : Circuit 1) (steps : Fin d → Circuit 1) :
    Unitary (2 ^ (systemQubits_frozen + ancW)) :=
  pureRotLocalUnitary hAnc rotTop *
    walkLocalUnitaryShared34 D false *
    (foldFinUnitary (m := d) fun s ↦
      pureRotLocalUnitary hAnc (steps s) * bidirStepLocalUnitaryShared34 D U) *
    pureRotLocalUnitary hAnc rot0 *
    walkLocalUnitaryShared34 D true *
    (Circuit.H (locQGen hAnc)).eval

theorem bidirBodyPureTopHad_mul_cat8Shared_simp
    {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n d tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D)
    (rot0 rotTop : Circuit 1) (steps : Fin d → Circuit 1) :
    (bidirBodyPureTopHadLocalUnitary (d := d) D U rot0 rotTop steps).1 *
        cat8SharedProjGen hAnc =
    (eQGen hAnc rotTop.eval.1 * sigOp (eQGen hAnc) (walkOpShared D) false *
      simpFusedChainOfCircuits (eQGen hAnc) (walkOpShared D) rot0 steps *
      eQGen hAnc hadamard2) * cat8SharedProjGen hAnc := by
  have hc : (∀ M, Commute (eQGen hAnc M) (cat8SharedProjGen hAnc)) ∧ Commute (lcuProjGen D.lcuSub)
      (cat8SharedProjGen hAnc) ∧ Commute D.S.1 (cat8SharedProjGen hAnc) :=
      commute_walk_data_locCat8SharedGen D (Matrix.vecMulVec (phaseGradientState 8)
      (star (phaseGradientState 8)))
  have hsB (b : Bool) : Commute (sigOp (eQGen hAnc) (walkOpShared D) b) (cat8SharedProjGen hAnc)
      := by have h := commute_gqspOp_walkGen D hc [(1, b)]; simpa [gqspOp] using h
  have hstep (c : Circuit 1) : (pureRotLocalUnitary hAnc c *
      bidirStepLocalUnitaryShared34 D U).1 * cat8SharedProjGen hAnc = (eQGen hAnc c.eval.1 *
      (sigOp (eQGen hAnc) (walkOpShared D) false * sigOp (eQGen hAnc) (walkOpShared D) true)) *
      cat8SharedProjGen hAnc := by
    rw [Submonoid.coe_mul, pureRotLocalUnitary_val, mul_assoc,
        bidirStepLocalUnitaryShared34_mul_cat8Shared D U, ← mul_assoc]
  have hr₀ : (pureRotLocalUnitary hAnc rot0).1 * ((walkLocalUnitaryShared34 D true).1 *
      cat8SharedProjGen hAnc) = (eQGen hAnc rot0.eval.1 * sigOp (eQGen hAnc)
      (walkOpShared D) true) *
      cat8SharedProjGen hAnc := by
    rw [pureRotLocalUnitary_val, walkLocalUnitaryShared34_mul_cat8Shared D true, ← mul_assoc]
  let F := (foldFinUnitary (m := d) fun s ↦
    pureRotLocalUnitary hAnc (steps s) * bidirStepLocalUnitaryShared34 D U).1
  have hF : F * ((eQGen hAnc rot0.eval.1 * sigOp (eQGen hAnc) (walkOpShared D) true) *
      cat8SharedProjGen hAnc) = simpFusedChainOfCircuits (eQGen hAnc)
      (walkOpShared D) rot0 steps * cat8SharedProjGen hAnc :=
      foldFin_step_mul_proj_circuits (eQGen hAnc) (pureRotLocalUnitary hAnc)
      (bidirStepLocalUnitaryShared34 D U) (walkOpShared D)
      (cat8SharedProjGen hAnc) hc.1 (hsB false)
      (hsB true) hstep rot0 steps; have hdc : simpFusedChainOfCircuits (eQGen hAnc)
                                     (walkOpShared D) rot0 steps * cat8SharedProjGen hAnc =
                                     cat8SharedProjGen hAnc * simpFusedChainOfCircuits (eQGen hAnc)
                                     (walkOpShared D) rot0 steps :=
                                     (simpFusedChainOfCircuits_commute (eQGen hAnc) hc.1 (hsB false)
                                     (hsB true) rot0 steps).eq
  let P := cat8SharedProjGen hAnc
  let C := simpFusedChainOfCircuits (eQGen hAnc) (walkOpShared D) rot0 steps
  calc (bidirBodyPureTopHadLocalUnitary (d := d) D U rot0 rotTop steps).1 * P
      = eQGen hAnc rotTop.eval.1 * (walkLocalUnitaryShared34 D false).1 *
          (F * ((pureRotLocalUnitary hAnc rot0).1 * ((walkLocalUnitaryShared34 D true).1 *
              P))) *
          eQGen hAnc hadamard2 := by
        unfold bidirBodyPureTopHadLocalUnitary
        simp only [F, P, Submonoid.coe_mul, circuit_H_locQGen_eval, pureRotLocalUnitary_val]
        rw [mul_assoc _ (eQGen hAnc hadamard2) P, (hc.1 hadamard2).eq]
        simp only [mul_assoc]
    _ = eQGen hAnc rotTop.eval.1 * (((walkLocalUnitaryShared34 D false).1 * P) * C) *
        eQGen hAnc hadamard2 := by
        rw [show P = cat8SharedProjGen hAnc from rfl, hr₀, hF, hdc]
        simp only [C, mul_assoc]
    _ = (eQGen hAnc rotTop.eval.1 * sigOp (eQGen hAnc) (walkOpShared D) false * C *
        eQGen hAnc hadamard2) * P := by
        rw [show P = cat8SharedProjGen hAnc from rfl,
            walkLocalUnitaryShared34_mul_cat8Shared D false,
          mul_assoc (sigOp _ _ false) _ C, ← hdc]
        simp only [C, mul_assoc]
        rw [(hc.1 hadamard2).eq]

theorem hs_tier1Walk_of_alpha_le {α : ℝ} (hα_le : α ≤ alphaTier1WalkFull) : α *
    evolutionTime_frozen ≤ sMax_tier1Walk_full := by
  have ht : 0 ≤ evolutionTime_frozen := by unfold evolutionTime_frozen; norm_num
  exact (mul_le_mul_of_nonneg_right hα_le ht).trans hs_tier1Walk_full_le_sMax
end QuantumComputation.Specs.PhotochemistrySolution.TopHadBridge
end
end

end
