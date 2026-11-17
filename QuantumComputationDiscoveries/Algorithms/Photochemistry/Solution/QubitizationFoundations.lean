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
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import QuantumComputation.Algorithms.QFT.States
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CyclotomicPhaseCheck

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section
open Matrix
namespace QuantumComputation.Specs.PhotochemistrySolution.GQSP
open scoped Matrix.Norms.L2Operator
open Polynomial ComplexConjugate
noncomputable def conjRev (d : ℕ) (f : ℂ[X]) : ℂ[X] := reflect d (f.map (starRingEnd ℂ))
theorem coeff_conjRev (d : ℕ) (f : ℂ[X]) (k : ℕ) : (conjRev d f).coeff k =
    conj (f.coeff (revAt d k)) := by rw [conjRev, coeff_reflect, coeff_map]
theorem coeff_conjRev_zero (d : ℕ) (f : ℂ[X]) : (conjRev d f).coeff 0 = conj (f.coeff d) := by
  rw [coeff_conjRev, revAt_le (Nat.zero_le d), Nat.sub_zero]
theorem conjRev_add (d : ℕ) (f g : ℂ[X]) : conjRev d (f + g) = conjRev d f + conjRev d g := by
  simp only [conjRev, Polynomial.map_add, reflect_add]
theorem conjRev_sub (d : ℕ) (f g : ℂ[X]) : conjRev d (f - g) = conjRev d f - conjRev d g := by
  simp only [conjRev, Polynomial.map_sub, reflect_sub]
theorem conjRev_C_mul (d : ℕ) (a : ℂ) (f : ℂ[X]) : conjRev d (C a * f) = C (conj a) *
    conjRev d f := by simp only [conjRev, Polynomial.map_mul, map_C, reflect_C_mul]
theorem conjRev_conjRev (d : ℕ) (f : ℂ[X]) : conjRev d (conjRev d f) = f :=
  Polynomial.ext fun k ↦ by rw [coeff_conjRev, coeff_conjRev, revAt_invol, Complex.conj_conj]
theorem natDegree_conjRev_le {d : ℕ} {f : ℂ[X]} (hf : f.natDegree ≤ d) : (conjRev d f).natDegree ≤
    d :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hN ↦ by
    rw [coeff_conjRev, revAt_eq_self_of_lt hN, coeff_eq_zero_of_natDegree_lt (hf.trans_lt hN),
        map_zero]
theorem natDegree_le_of_le_succ {f : ℂ[X]} {n : ℕ} (hf : f.natDegree ≤ n + 1)
    (htop : f.coeff (n + 1) = 0) : f.natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun N hN ↦
    (Nat.lt_or_ge (n + 1) N).elim (fun h ↦ coeff_eq_zero_of_natDegree_lt (hf.trans_lt h)) fun hle ↦
        (congrArg f.coeff (by omega : N = n + 1)).trans htop
theorem conjRev_mul {a b : ℕ} {f g : ℂ[X]} (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) :
    conjRev (a + b) (f * g) = conjRev a f * conjRev b g := by
  simpa only [conjRev, Polynomial.map_mul] using reflect_mul _ _ (natDegree_map_le.trans hf)
      (natDegree_map_le.trans hg)
theorem conjRev_X_mul {d : ℕ} {g : ℂ[X]} (hg : g.natDegree ≤ d) : conjRev (d + 1)
    (X * g) = conjRev d g := by
  rw [add_comm, conjRev_mul natDegree_X_le hg]; simp [conjRev]
theorem conjRev_succ {d : ℕ} {g : ℂ[X]} (hg : g.natDegree ≤ d) : conjRev (d + 1) g = X *
    conjRev d g := by
  have h := conjRev_mul (a := 1) (f := 1) (by simp) hg
  rw [one_mul, add_comm] at h
  simpa [conjRev, reflect_one] using h
theorem eq_zero_of_mul_conj_add_eq_zero {x y : ℂ} (h : x * conj x + y * conj y = 0) : x = 0 ∧ y =
    0 := by
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have hxy : 0 ≤ Complex.normSq x ∧ 0 ≤ Complex.normSq y :=
      ⟨Complex.normSq_nonneg x, Complex.normSq_nonneg y⟩
  exact ⟨Complex.normSq_eq_zero.mp (by linarith), Complex.normSq_eq_zero.mp (by linarith)⟩
theorem exists_real_scale {x y : ℂ} (h : x * conj x + y * conj y ≠ 0) : ∃ t : ℝ, (x * conj x + y *
    conj y) * ((t : ℂ) * t) = 1 := by
  simp only [Complex.mul_conj, ← Complex.ofReal_add, ne_eq, Complex.ofReal_eq_zero] at h ⊢
  have hpos : 0 < Complex.normSq x + Complex.normSq y :=
    lt_of_le_of_ne (add_nonneg (Complex.normSq_nonneg x) (Complex.normSq_nonneg y)) (Ne.symm h)
  exact ⟨(√(Complex.normSq x + Complex.normSq y))⁻¹, mod_cast by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, mul_inv_cancel₀ hpos.ne']⟩
theorem exists_unit_pair {a b c e : ℂ} (h : a * conj c + b * conj e = 0) :
    ∃ u v : ℂ, u * conj u + v * conj v = 1 ∧ u * a + v * b = 0 ∧ -conj v * c + conj u * e = 0 := by
  have h' : conj a * c + conj b * e = 0 := by
    simpa [map_add, map_mul, Complex.conj_conj] using congrArg conj h
  by_cases hab : a * conj a + b * conj b = 0
  · obtain ⟨rfl, rfl⟩ := eq_zero_of_mul_conj_add_eq_zero hab
    by_cases hce : c * conj c + e * conj e = 0
    · obtain ⟨rfl, rfl⟩ := eq_zero_of_mul_conj_add_eq_zero hce
      exact ⟨1, 0, by simp, by simp, by simp⟩
    · obtain ⟨t, ht⟩ := exists_real_scale hce
      exact ⟨conj c * t, conj e * t,
          by simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]; linear_combination ht,
        by simp, by simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]; ring⟩
  · obtain ⟨t, ht⟩ := exists_real_scale hab
    exact ⟨b * t, -a * t,
        by simp only [map_mul, map_neg, Complex.conj_ofReal]; linear_combination ht,
      by ring,
          by simp only [map_mul, map_neg, Complex.conj_ofReal]; linear_combination (t : ℂ) * h'⟩
noncomputable def unitaryOfColumn (p q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![p, -conj q; q, conj p]
theorem unitaryOfColumn_mem {p q : ℂ} (h : p * conj p + q * conj q = 1) :
    unitaryOfColumn p q ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; ext i j
  fin_cases i <;> fin_cases j <;> rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
      dsimp [unitaryOfColumn, Matrix.one_apply] <;>
      simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply] <;>
      first | ring1 | linear_combination h
noncomputable def signal : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  !![X, 0; 0, 1]
noncomputable def gqspTail : List (Matrix (Fin 2) (Fin 2) ℂ) → Matrix (Fin 2) (Fin 2) ℂ[X]
  | [] => 1
  | R :: Rs => R.map C * signal * gqspTail Rs
theorem mul_conj_eq_one_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u * conj u = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
theorem eval_conjRev {d : ℕ} {f : ℂ[X]} (hf : f.natDegree ≤ d) {w : ℂ} (hw : w ≠ 0) :
    (conjRev d f).eval w = w ^ d * conj (f.eval (conj w)⁻¹) := by
  let _ : Invertible w⁻¹ := invertibleOfNonzero (inv_ne_zero hw)
  have h :=
      eval₂_reflect_mul_pow (RingHom.id ℂ) w⁻¹ d (f.map (starRingEnd ℂ)) (natDegree_map_le.trans hf)
  rw [invOf_eq_inv, inv_inv, eval₂_map, RingHom.id_comp] at h
  have key : (conjRev d f).eval w * w⁻¹ ^ d = conj (f.eval (conj w)⁻¹) := by
    rw [← show f.eval₂ (starRingEnd ℂ) w⁻¹ =
        conj (f.eval (conj w)⁻¹) by rw [← eval₂_hom, map_inv₀, Complex.conj_conj], ← h]
    rfl
  rw [← key, inv_pow, mul_comm _ ((w ^ d)⁻¹), ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hw),
      one_mul]
theorem eval_conjRev_of_norm_eq_one {d : ℕ} {f : ℂ[X]} (hf : f.natDegree ≤ d) {z : ℂ}
    (hz : ‖z‖ = 1) :
    (conjRev d f).eval z = z ^ d * conj (f.eval z) := by
  rw [eval_conjRev hf (by rintro rfl; norm_num at hz),
      inv_eq_of_mul_eq_one_right (by rw [mul_comm, mul_conj_eq_one_of_norm_eq_one hz])]
theorem conjRev_X_sub_C (α : ℂ) : conjRev 1 (X - C α) = 1 - C (conj α) * X := by
  simp [conjRev, reflect_C]
theorem exists_mul_conjRev_eq (d : ℕ) {r : ℂ[X]} (hr : r.natDegree ≤ 2 * d)
    (hsym : conjRev (2 * d) r = r)
    (hpos : ∀ z : ℂ, ‖z‖ = 1 → ∃ s : ℝ, 0 < s ∧ r.eval z = z ^ d * s) : ∃ Q : ℂ[X], Q.natDegree ≤
        d ∧ Q * conjRev d Q = r := by
  induction d generalizing r with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c, r = C c := ⟨_, eq_C_of_natDegree_le_zero (by simpa using hr)⟩
    obtain ⟨s, hs, hcs⟩ := hpos 1 (by simp)
    rw [eval_C, pow_zero, one_mul] at hcs
    exact ⟨C (Real.sqrt s : ℂ), by simp, by
      rw [hcs, conjRev, map_C, reflect_C, pow_zero, mul_one, Complex.conj_ofReal, ← C_mul,
          ← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]⟩
  | succ d ih =>
    have hz0 : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 0 := by rintro z hz rfl; norm_num at hz
    have hr0 : r ≠ 0 := by
      rintro rfl; obtain ⟨s, hs, h0⟩ := hpos 1 (by simp); exact hs.ne' (by simpa using h0.symm)
    have hdeg : 0 < r.degree := natDegree_pos_iff_degree_pos.mp <| by
      by_contra hcon
      have hc := congrArg (fun f ↦ f.coeff 0) hsym
      rw [coeff_conjRev_zero, coeff_eq_zero_of_natDegree_lt (by omega), map_zero] at hc
      exact hr0 (by rw [eq_C_of_natDegree_le_zero (by omega : r.natDegree ≤ 0), ← hc, C_0])
    obtain ⟨α, hα⟩ := Complex.exists_root hdeg
    have hnorm : ‖α‖ ≠ 1 := fun h1 ↦ by
      obtain ⟨s, hs, hαs⟩ := hpos α h1
      exact mul_ne_zero (pow_ne_zero _ (hz0 α h1)) (by exact_mod_cast hs.ne')
          (hαs.symm.trans hα.eq_zero)
    by_cases hα0 : α = 0
    · subst hα0
      obtain ⟨r₁, hr₁⟩ : X ∣ r := by simpa using dvd_iff_isRoot.mpr hα
      have hrle := natDegree_le_of_le_succ (n := 2 * d + 1) hr (show r.coeff (2 * (d + 1)) = 0 by
        have hc := congrArg (fun f ↦ f.coeff (2 * (d + 1))) hsym
        simp only [coeff_conjRev, revAt_le le_rfl, Nat.sub_self] at hc
        rw [← hc, coeff_zero_eq_eval_zero, hα.eq_zero, map_zero])
      have hr₁deg : r₁.natDegree ≤ 2 * d := by
        have h := natDegree_X_mul (fun h : r₁ = 0 ↦ hr0 (by rw [hr₁, h, mul_zero]))
        rw [← hr₁] at h
        omega
      have hsym₁ : conjRev (2 * d) r₁ = r₁ := by
        rw [show 2 * (d + 1) = 2 * d + 1 + 1 by ring, hr₁, conjRev_X_mul (by omega),
            conjRev_succ hr₁deg] at hsym
        exact mul_left_cancel₀ X_ne_zero hsym
      have hpos₁ : ∀ z : ℂ, ‖z‖ = 1 → ∃ s : ℝ, 0 < s ∧ r₁.eval z = z ^ d * s := fun z hz ↦ by
        obtain ⟨s, hs, hzs⟩ := hpos z hz
        rw [hr₁, eval_mul, eval_X, pow_succ'] at hzs
        exact ⟨s, hs, mul_left_cancel₀ (hz0 z hz) (by rw [hzs, mul_assoc])⟩
      obtain ⟨Q₁, hQ₁deg, hQ₁⟩ := ih hr₁deg hsym₁ hpos₁
      exact ⟨X * Q₁, natDegree_mul_le.trans (by have := natDegree_X_le (R := ℂ); omega),
          by rw [conjRev_X_mul hQ₁deg, mul_assoc, hQ₁, hr₁]⟩
    · have hca : conj α ≠ 0 := (_root_.map_ne_zero _).mpr hα0
      have hαβ : α ≠ (conj α)⁻¹ := fun h ↦ hnorm (by
        have h2 : Complex.normSq α = 1 := by
          exact_mod_cast (Complex.mul_conj α).symm.trans ((congrArg (· * conj α) h).trans
              (inv_mul_cancel₀ hca))
        rw [Complex.normSq_eq_norm_sq] at h2; nlinarith [norm_nonneg α])
      obtain ⟨ra, hra⟩ : X - C α ∣ r := dvd_iff_isRoot.mpr hα
      have hβa : ra.IsRoot (conj α)⁻¹ := by
        have h1 : r.eval (conj α)⁻¹ = 0 := by
          rw [← hsym, eval_conjRev hr (inv_ne_zero hca), map_inv₀, Complex.conj_conj, inv_inv,
              hα.eq_zero, map_zero, mul_zero]
        rw [hra, eval_mul, eval_sub, eval_X, eval_C] at h1
        exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hαβ.symm)
      obtain ⟨rb, hrb⟩ : X - C (conj α)⁻¹ ∣ ra := dvd_iff_isRoot.mpr hβa
      have hra0 : ra ≠ 0 := fun h ↦ hr0 (by rw [hra, h, mul_zero])
      have hrbdeg : rb.natDegree ≤ 2 * d := by
        have h1 := natDegree_mul (X_sub_C_ne_zero α) hra0
        have h2 :=
            natDegree_mul (X_sub_C_ne_zero (conj α)⁻¹)
            (fun h : rb = 0 ↦ hra0 (by rw [hrb, h, mul_zero]))
        rw [← hra, natDegree_X_sub_C] at h1
        rw [← hrb, natDegree_X_sub_C] at h2
        omega
      have hinv : C (conj α) * C (conj α)⁻¹ = (1 : ℂ[X]) := by
        rw [← C_mul, mul_inv_cancel₀ hca, C_1]
      have hr'deg : (C (-(conj α)⁻¹) * rb).natDegree ≤ 2 * d :=
          (natDegree_C_mul_le _ _).trans hrbdeg
      have hr' : r = (X - C α) * conjRev 1 (X - C α) * (C (-(conj α)⁻¹) * rb) := by
        rw [conjRev_X_sub_C, hra, hrb, C_neg]; linear_combination (-(X - C α) * rb * X) * hinv
      generalize C (-(conj α)⁻¹) * rb = r' at hr' hr'deg
      have hsym' : conjRev (2 * d) r' = r' := by
        rw [hr', show 2 * (d + 1) = 2 + 2 * d by ring, conjRev_mul (natDegree_mul_le.trans
          (add_le_add (natDegree_X_sub_C_le α)
              (natDegree_conjRev_le (natDegree_X_sub_C_le α)))) hr'deg,
          show conjRev 2 ((X - C α) * conjRev 1 (X - C α)) = (X - C α) * conjRev 1 (X - C α) by
            rw [show (2 : ℕ) = 1 + 1 from rfl, conjRev_mul (natDegree_X_sub_C_le α)
              (natDegree_conjRev_le (natDegree_X_sub_C_le α)), conjRev_conjRev, mul_comm]] at hsym
        exact mul_left_cancel₀ (fun h0 ↦ hr0 (by rw [hr', h0, zero_mul])) hsym
      have hpos' : ∀ z : ℂ, ‖z‖ = 1 → ∃ s : ℝ, 0 < s ∧ r'.eval z = z ^ d * s := fun z hz ↦ by
        obtain ⟨s, hs, hzs⟩ := hpos z hz
        have hn : 0 < Complex.normSq (z - α) := Complex.normSq_pos.mpr fun h0 ↦
            hnorm (by rw [← sub_eq_zero.mp h0, hz])
        have hfz : ((X - C α) * conjRev 1 (X - C α)).eval z = z * (Complex.normSq (z - α) : ℂ) := by
          rw [conjRev_X_sub_C, ← Complex.mul_conj]
          simp only [eval_mul, eval_sub, eval_X, eval_C, eval_one, map_sub]
          linear_combination (-(z - α)) * mul_conj_eq_one_of_norm_eq_one hz
        refine ⟨s / Complex.normSq (z - α), div_pos hs hn, ?_⟩
        have hn0 : (Complex.normSq (z - α) : ℂ) ≠ 0 := mod_cast hn.ne'
        apply mul_left_cancel₀ (mul_ne_zero (hz0 z hz) hn0)
        conv_lhs => rw [← hfz, ← eval_mul, ← hr', hzs]
        rw [Complex.ofReal_div]
        field_simp
        ring
      obtain ⟨Q', hQ'deg, hQ'⟩ := ih hr'deg hsym' hpos'
      exact ⟨(X - C α) * Q', natDegree_mul_le.trans (by rw [natDegree_X_sub_C]; omega),
        by rw [add_comm d 1, conjRev_mul (natDegree_X_sub_C_le α) hQ'deg, hr', ← hQ']; ring⟩
noncomputable abbrev phaseTurn (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := diagPhaseMatrix ![0, x]
theorem phaseTurn_eq (x : ℝ) :
    phaseTurn x = !![1, 0; 0, Complex.exp (2 * Real.pi * Complex.I * x)] := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [phaseTurn, diagPhaseMatrix]
theorem phaseTurn_mem (x : ℝ) : phaseTurn x ∈ unitaryGroup (Fin 2) ℂ :=
    diagPhaseMatrix_mem_unitaryGroup _
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  rw [invSqrtTwo, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two]; norm_num
theorem conj_invSqrtTwo : conj invSqrtTwo = invSqrtTwo := by
  rw [invSqrtTwo, map_inv₀, Complex.conj_ofReal]
noncomputable def hadamard2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![invSqrtTwo, invSqrtTwo; invSqrtTwo, -invSqrtTwo]
theorem hadamard2_mem : hadamard2 ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [hadamard2, Matrix.mul_apply, Fin.sum_univ_two,
      conj_invSqrtTwo] <;>
    linear_combination (2 : ℂ) * invSqrtTwo_mul_self
theorem norm_le_one_of_mem_unitaryGroup {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    (hA : A ∈ unitaryGroup m ℂ) : ‖A‖ ≤ 1 :=
  (isEmpty_or_nonempty m).elim (fun _ ↦ by rw [Subsingleton.elim A 0, norm_zero]; exact zero_le_one)
    fun _ ↦ (CStarRing.norm_of_mem_unitary hA).le
theorem exp_smul_mem_unitaryGroup (γ : ℝ) {W : Matrix (Fin 2) (Fin 2) ℂ}
    (hW : W ∈ unitaryGroup (Fin 2) ℂ) :
    Complex.exp (γ * Complex.I) • W ∈ unitaryGroup (Fin 2) ℂ := by
  have h := mul_conj_eq_one_of_norm_eq_one (Complex.norm_exp_ofReal_mul_I γ)
  exact Unitary.smul_mem_of_mem (Unitary.mem_iff.mpr ⟨(mul_comm _ _).trans h, h⟩) hW
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem scalarBlock_mem_unitary {R : Matrix (Fin 2) (Fin 2) ℂ} (hR : R ∈ unitaryGroup (Fin 2) ℂ) :
    R.map (algebraMap ℂ (Matrix n n ℂ)) ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) := by
  have hstar : star (R.map (algebraMap ℂ (Matrix n n ℂ))) =
      (star R).map (algebraMap ℂ (Matrix n n ℂ)) := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_map _ (fun c ↦
        algebraMap_star_comm c)]
  rw [Unitary.mem_iff, hstar, ← Matrix.map_mul, ← Matrix.map_mul,
    Unitary.star_mul_self_of_mem hR, Unitary.mul_star_self_of_mem hR, Matrix.map_one _ (map_zero _)
        (map_one _)]
  exact ⟨rfl, rfl⟩
theorem diagSignal_mem_unitary {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    (!![U, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) ∈
      unitary (Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Unitary.star_mul_self_of_mem hU,
        Unitary.mul_star_self_of_mem hU]
theorem diagonal_const_mem_unitary {V : Matrix n n ℂ} (hV : V ∈ unitary (Matrix n n ℂ)) :
    diagonal (fun _ : Fin 2 ↦ V) ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;> ext i j : 1 <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Unitary.star_mul_self_of_mem hV,
        Unitary.mul_star_self_of_mem hV]
theorem mapMatrix_aeval_gqspTail_cons (U : Matrix n n ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ)
    (Rs : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    (aeval U).toRingHom.mapMatrix (gqspTail (R :: Rs)) =
      R.map (algebraMap ℂ (Matrix n n ℂ)) * !![U, 0; 0, 1] *
        (aeval U).toRingHom.mapMatrix (gqspTail Rs) := by
  rw [gqspTail, map_mul, map_mul]; congr 2
  · ext i j : 1; simp
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [signal]
theorem mapMatrix_gqsp_mem_unitary {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    {R₀ : Matrix (Fin 2) (Fin 2) ℂ} (hR₀ : R₀ ∈ unitaryGroup (Fin 2) ℂ) :
    ∀ {Rs : List (Matrix (Fin 2) (Fin 2) ℂ)}, (∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ) →
      (aeval U).toRingHom.mapMatrix (gqspTail Rs * R₀.map C) ∈
        unitary (Matrix (Fin 2) (Fin 2) (Matrix n n ℂ))
  | [], _ => by
    rw [show (aeval U).toRingHom.mapMatrix (gqspTail [] * R₀.map C) =
        R₀.map (algebraMap ℂ (Matrix n n ℂ)) by rw [gqspTail, one_mul]; ext i j : 1; simp]
    exact scalarBlock_mem_unitary hR₀
  | R :: Rs, hRs => by
    rw [map_mul, mapMatrix_aeval_gqspTail_cons, Matrix.mul_assoc, ← map_mul]
    exact mul_mem (mul_mem (scalarBlock_mem_unitary (hRs R List.mem_cons_self))
        (diagSignal_mem_unitary hU))
      (mapMatrix_gqsp_mem_unitary hU hR₀ fun R' hR' ↦ hRs R' (List.mem_cons_of_mem _ hR'))
theorem compRingEquiv_mem_unitary {M : Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)}
    (hM : M ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix n n ℂ))) :
    compRingEquiv (Fin 2) n ℂ M ∈ unitaryGroup (Fin 2 × n) ℂ := by
  have hstar : compRingEquiv (Fin 2) n ℂ (star M) = star (compRingEquiv (Fin 2) n ℂ M) := by
    ext ⟨i, k⟩ ⟨j, l⟩; simp [compRingEquiv_apply, comp_apply, star_eq_conjTranspose]
  rw [Unitary.mem_iff, ← hstar, ← map_mul, ← map_mul, Unitary.star_mul_self_of_mem hM,
      Unitary.mul_star_self_of_mem hM, map_one]
  exact ⟨rfl, rfl⟩
noncomputable def mixedSignal (U : Matrix n n ℂ) (b : Bool) : Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)
    :=
  if b then !![1, 0; 0, Uᴴ] else !![U, 0; 0, 1]
noncomputable def gqspMixedTail (U : Matrix n n ℂ) :
    List (Matrix (Fin 2) (Fin 2) ℂ × Bool) → Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)
  | [] => 1
  | (R, b) :: Rs => R.map (algebraMap ℂ (Matrix n n ℂ)) * mixedSignal U b * gqspMixedTail U Rs
theorem mixedSignal_true {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    mixedSignal U true = diagonal (fun _ ↦ Uᴴ) * !![U, 0; 0, 1] := by
  have h : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [mixedSignal, diagonal_mul, h]
theorem gqspMixedTail_eq {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ × Bool),
      gqspMixedTail U Rs = diagonal (fun _ ↦ Uᴴ ^ Rs.countP (·.2)) *
        (aeval U).toRingHom.mapMatrix (gqspTail (Rs.map Prod.fst))
  | [] => by simp [gqspMixedTail, gqspTail]
  | (R, b) :: Rs => by
    have hcomm : Commute U Uᴴ :=
        (Unitary.mul_star_self_of_mem hU).trans (Unitary.star_mul_self_of_mem hU).symm
    have h1 (W : Matrix n n ℂ) (Y : Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) :
        R.map (algebraMap ℂ (Matrix n n ℂ)) * (diagonal (fun _ ↦ W) * Y) = diagonal (fun _ ↦ W) *
            (R.map (algebraMap ℂ (Matrix n n ℂ)) * Y) := by
      rw [← Matrix.mul_assoc, show R.map (algebraMap ℂ (Matrix n n ℂ)) * diagonal (fun _ : Fin 2 ↦
          W) = diagonal (fun _ : Fin 2 ↦ W) * R.map (algebraMap ℂ (Matrix n n ℂ))
        by ext i j : 1; rw [mul_diagonal, diagonal_mul,
             Matrix.map_apply]; exact Algebra.commutes _ _, Matrix.mul_assoc]
    have h2 (k : ℕ) (Y : Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) :
        !![U, 0; 0, 1] * (diagonal (fun _ ↦ Uᴴ ^ k) * Y) = diagonal (fun _ ↦ Uᴴ ^ k) *
            (!![U, 0; 0, 1] * Y) := by
      rw [← Matrix.mul_assoc, show !![U, 0; 0, 1] * diagonal (fun _ : Fin 2 ↦ Uᴴ ^ k) =
          diagonal (fun _ ↦ Uᴴ ^ k) * !![U, 0; 0, 1]
        by ext i j : 1; fin_cases i <;> fin_cases j <;> simp [mul_diagonal, diagonal_mul,
             (hcomm.pow_right k).eq], Matrix.mul_assoc]
    rw [gqspMixedTail, gqspMixedTail_eq hU Rs, List.map_cons, mapMatrix_aeval_gqspTail_cons,
        List.countP_cons]
    cases b
    · simp only [mixedSignal, Bool.false_eq_true, ↓reduceIte, add_zero, Matrix.mul_assoc];
      rw [h2, h1]
    · simp only [mixedSignal_true hU, ↓reduceIte, Matrix.mul_assoc]
      rw [h2, h1, h1, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
          ← pow_succ']
theorem gqsp_laurent_realisation_zip {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    {R₀ : Matrix (Fin 2) (Fin 2) ℂ} {Rs : List (Matrix (Fin 2) (Fin 2) ℂ)} {bs : List Bool}
        {P Q : ℂ[X]}
    (hR₀ : R₀ ∈ unitaryGroup (Fin 2) ℂ) (hRs : ∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ)
    (hlen : Rs.length = bs.length) (h : (gqspTail Rs * R₀.map C) *ᵥ ![1, 0] = ![P, Q]) :
    compRingEquiv (Fin 2) n ℂ (gqspMixedTail U (Rs.zip bs) *
        R₀.map (algebraMap ℂ (Matrix n n ℂ))) ∈ unitaryGroup (Fin 2 × n) ℂ ∧
    (gqspMixedTail U (Rs.zip bs) * R₀.map (algebraMap ℂ (Matrix n n ℂ))) 0 0 = Uᴴ ^ bs.count true *
        aeval U P ∧
    (gqspMixedTail U (Rs.zip bs) * R₀.map (algebraMap ℂ (Matrix n n ℂ))) 1 0 = Uᴴ ^ bs.count true *
        aeval U Q := by
  have h0 : (gqspTail Rs * R₀.map C) 0 0 = P := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
  have h1 : (gqspTail Rs * R₀.map C) 1 0 = Q := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1
  have hfac : gqspMixedTail U (Rs.zip bs) * R₀.map (algebraMap ℂ (Matrix n n ℂ)) =
      diagonal (fun _ ↦ Uᴴ ^ bs.count true) * (aeval U).toRingHom.mapMatrix (gqspTail Rs * R₀.map C)
          := by
    rw [gqspMixedTail_eq hU, show (Rs.zip bs).countP (·.2) = bs.count true by
      conv_rhs => rw [← List.map_snd_zip hlen.ge]
      rw [List.count_eq_countP, List.countP_map]; exact List.countP_congr fun _ _ ↦ by simp,
      List.map_fst_zip hlen.le, map_mul,
      show (aeval U).toRingHom.mapMatrix (R₀.map C) =
          R₀.map (algebraMap ℂ (Matrix n n ℂ)) by ext i j : 1; simp, Matrix.mul_assoc]
  rw [hfac]
  exact ⟨compRingEquiv_mem_unitary (mul_mem (diagonal_const_mem_unitary (pow_mem (Unitary.star_mem
      hU) _))
      (mapMatrix_gqsp_mem_unitary hU hR₀ hRs)), by rw [diagonal_mul]; simp [h0],
          by rw [diagonal_mul]; simp [h1]⟩
theorem mixedSignal_mem_unitary {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) (b : Bool) :
    mixedSignal U b ∈ unitary (Matrix (Fin 2) (Fin 2) (Matrix n n ℂ)) := by
  cases b
  · exact diagSignal_mem_unitary hU
  · rw [mixedSignal_true hU];
    exact mul_mem (diagonal_const_mem_unitary (Unitary.star_mem hU)) (diagSignal_mem_unitary hU)
end QuantumComputation.Specs.PhotochemistrySolution.GQSP

namespace QuantumComputation.Specs.PhotochemistrySolution.OvBidir
open Polynomial ComplexConjugate PhotochemistrySolution.GQSP
noncomputable def twist (f : ℂ[X]) : ℂ[X] := f.comp (-X)
theorem coeff_twist (f : ℂ[X]) (n : ℕ) : (twist f).coeff n = f.coeff n * (-1) ^ n := by
  rw [twist, show (-X : ℂ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff]
theorem twist_mul (f g : ℂ[X]) : twist (f * g) = twist f * twist g := by simp [twist, mul_comp]
theorem twist_add (f g : ℂ[X]) : twist (f + g) = twist f + twist g := by simp [twist, add_comp]
theorem twist_sub (f g : ℂ[X]) : twist (f - g) = twist f - twist g := by simp [twist, sub_comp]
theorem twist_neg (f : ℂ[X]) : twist (-f) = -twist f := by simp [twist, neg_comp]
theorem twist_C (a : ℂ) : twist (C a) = C a := by simp [twist]
theorem twist_X : twist (X : ℂ[X]) = -X := by simp [twist]
theorem twist_one : twist (1 : ℂ[X]) = 1 := by simp [twist]
theorem twist_twist (f : ℂ[X]) : twist (twist f) = f := by simp only [twist, comp_neg_X_comp_neg_X]
theorem conjRev_X_pow {N k : ℕ} (hk : k ≤ N) : conjRev N ((X : ℂ[X]) ^ k) = X ^ (N - k) := by
  simp [conjRev, reflect_monomial, revAt_le hk]
theorem conjRev_zero_C (a : ℂ) : conjRev 0 (C a) = C (conj a) := by simp [conjRev]
theorem expand_conjRev {N : ℕ} {f : ℂ[X]} (hf : f.natDegree ≤ N) : expand ℂ 2 (conjRev N f) =
    conjRev (2 * N) (expand ℂ 2 f) := by
  ext k; rw [coeff_expand two_pos, coeff_conjRev, coeff_conjRev]
  by_cases hk : k ≤ 2 * N
  · rw [revAt_le hk, coeff_expand two_pos]
    by_cases h2 : 2 ∣ k
    · rw [ite_eq_left h2, ite_eq_left (by omega : 2 ∣ 2 * N - k), revAt_le (by omega : k / 2 ≤ N)];
      congr 2; omega
    · rw [ite_eq_right h2, ite_eq_right (by omega : ¬ 2 ∣ 2 * N - k), map_zero]
  · rw [revAt_eq_self_of_lt (not_le.mp hk), coeff_expand two_pos]
    by_cases h2 : 2 ∣ k
    · rw [ite_eq_left h2, ite_eq_left h2, revAt_eq_self_of_lt (by omega : N < k / 2),
          coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < k / 2), map_zero]
    · rw [ite_eq_right h2, ite_eq_right h2, map_zero]
theorem expand_contract_of_odd_eq_zero {g : ℂ[X]} (hodd : ∀ n, ¬ 2 ∣ n → g.coeff n = 0) :
    expand ℂ 2 (contract 2 g) = g := by
  ext n; rw [coeff_expand two_pos]
  by_cases h : 2 ∣ n
  · rw [ite_eq_left h, coeff_contract two_ne_zero, Nat.div_mul_cancel h]
  · rw [ite_eq_right h, hodd n h]
theorem natDegree_contract_two_le {g : ℂ[X]} {m : ℕ} (hg : g.natDegree ≤ 2 * m) :
    (contract 2 g).natDegree ≤ m :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ _ ↦ by
    rw [coeff_contract two_ne_zero]; exact coeff_eq_zero_of_natDegree_lt (by omega)
theorem coeff_eq_zero_of_twist_eq {g : ℂ[X]} (h : twist g = g) (n : ℕ) (hn : ¬ 2 ∣ n) : g.coeff n =
    0 := by
  have e := congrArg (fun f ↦ f.coeff n) h
  rw [coeff_twist, Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))] at e; linear_combination -e / 2
theorem eq_X_mul_divX_of_twist_eq_neg {g : ℂ[X]} (h : twist g = -g) : g = X * g.divX ∧
    twist g.divX = g.divX := by
  have h0 : g.coeff 0 = 0 := by
    have e := congrArg (fun f ↦ f.coeff 0) h
    simp only [coeff_twist, pow_zero, mul_one, coeff_neg] at e; linear_combination e / 2
  have hX : g = X * g.divX := by
    have := X_mul_divX_add g; rw [h0, C_0, add_zero] at this; exact this.symm
  refine ⟨hX, mul_left_cancel₀ (X_ne_zero : (X : ℂ[X]) ≠ 0) ?_⟩
  have e := h; rw [hX, twist_mul, twist_X] at e; linear_combination -e
theorem exists_twisted_lift (m : ℕ) {Q : ℂ[X]} (hQ : Q.natDegree ≤ m) :
    ∃ H : ℂ[X], H.natDegree ≤ 2 * m ∧ H * conjRev (2 * m) H = expand ℂ 2 (Q * conjRev m Q) ∧
        twist H = C ((-1) ^ m) * conjRev (2 * m) H := by
  induction m generalizing Q with
  | zero =>
    obtain ⟨q, rfl⟩ : ∃ q, Q = C q := ⟨_, eq_C_of_natDegree_le_zero hQ⟩
    exact ⟨C (‖q‖ : ℂ), by simp,
      by rw [mul_zero, conjRev_zero_C, conjRev_zero_C, Complex.conj_ofReal, ← C_mul, ← C_mul,
           expand_C, Complex.mul_conj', sq],
      by rw [mul_zero, twist_C, pow_zero, C_1, one_mul, conjRev_zero_C, Complex.conj_ofReal]⟩
  | succ m ih =>
    by_cases htop : Q.coeff (m + 1) = 0
    · have hQm := natDegree_le_of_le_succ hQ htop
      obtain ⟨H₁, hH₁, hHH₁, htw₁⟩ := ih hQm
      have hcX : conjRev (2 * (m + 1)) (X * H₁) = X * conjRev (2 * m) H₁ := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, conjRev_X_mul (by omega), conjRev_succ hH₁]
      refine ⟨X * H₁, natDegree_mul_le.trans (by rw [natDegree_X]; omega), ?_, ?_⟩
      · rw [hcX, conjRev_succ hQm]; simp only [map_mul, expand_X] at hHH₁ ⊢;
        linear_combination X ^ 2 * hHH₁
      · rw [hcX, twist_mul, twist_X, htw₁, pow_succ, C_mul, C_neg, C_1]; ring
    · have hQ0 : Q ≠ 0 := fun h ↦ htop (by rw [h, coeff_zero])
      have hdeg : Q.natDegree = m + 1 := le_antisymm hQ (le_natDegree_of_ne_zero htop)
      obtain ⟨r, hr⟩ :=
          IsAlgClosed.exists_root Q
          (by rw [degree_eq_natDegree hQ0, hdeg]; exact_mod_cast Nat.succ_ne_zero m)
      obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁, Q₁ = Q /ₘ (X - C r) := ⟨_, rfl⟩
      have hQfac : Q = (X - C r) * Q₁ := by rw [hQ₁, mul_divByMonic_eq_iff_isRoot.mpr hr]
      have hQ₁deg : Q₁.natDegree ≤ m := by
        rw [hQ₁, natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]; omega
      obtain ⟨H₁, hH₁, hHH₁, htw₁⟩ := ih hQ₁deg
      obtain ⟨a, rfl⟩ := IsAlgClosed.isSquare r
      have hl1 : (X - C a).natDegree ≤ 1 := natDegree_X_sub_C_le a
      have hl2 : (C (conj a) * X + 1).natDegree ≤ 1 := by compute_degree
      have hφ : ((X - C a) * (C (conj a) * X + 1)).natDegree ≤ 2 :=
          natDegree_mul_le.trans (by omega)
      have hcφ : conjRev (2 * (m + 1)) ((X - C a) * (C (conj a) * X + 1) * H₁) =
          (1 - C (conj a) * X) * (C a + X) * conjRev (2 * m) H₁ := by
        rw [show 2 * (m + 1) = 2 + 2 * m by ring, conjRev_mul hφ hH₁, conjRev_mul hl1 hl2,
            conjRev_X_sub_C,
          show conjRev 1 (C (conj a) * X + 1) = C a + X by
            rw [conjRev_add, conjRev_C_mul, show (X : ℂ[X]) = X ^ 1 from (pow_one X).symm,
                conjRev_X_pow le_rfl,
              show (1 : ℂ[X]) = X ^ 0 from (pow_zero X).symm, conjRev_X_pow (Nat.zero_le 1),
                  pow_zero, pow_one,
              Complex.conj_conj, mul_one]]
      refine ⟨(X - C a) * (C (conj a) * X + 1) * H₁, natDegree_mul_le.trans (by omega), ?_, ?_⟩
      · rw [hcφ, hQfac, show m + 1 = 1 + m by ring, conjRev_mul (natDegree_X_sub_C_le _) hQ₁deg,
            conjRev_X_sub_C]
        simp only [map_mul, map_sub, map_one, expand_X, expand_C] at hHH₁ ⊢
        linear_combination (X ^ 2 - C a * C a) * (1 - C (conj a) * C (conj a) * X ^ 2) * hHH₁
      · rw [hcφ, twist_mul, twist_mul, htw₁, twist_sub, twist_add, twist_X, twist_C, twist_mul,
            twist_C, twist_X, twist_one, pow_succ, C_mul, C_neg, C_1]; ring
theorem exists_bidir_pair {d : ℕ} (hd : Odd d) {P₀ : ℂ[X]} (hP₀ : P₀.natDegree ≤ 2 * d)
    (htw : twist P₀ = -conjRev (2 * d) P₀) (hlt : ∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ < 1) :
    ∃ P Q : ℂ[X], P.natDegree ≤ d ∧ Q.natDegree ≤ d ∧ P * conjRev d P + Q * conjRev d Q = X ^ d ∧
      X ^ 2 * expand ℂ 2 P + conjRev (2 * d) (expand ℂ 2 P) + X * (expand ℂ 2 Q - conjRev (2 * d)
          (expand ℂ 2 Q)) = 2 * (X * P₀) := by
  obtain ⟨Ps, hPs⟩ : ∃ Ps, Ps = conjRev (2 * d) P₀ := ⟨_, rfl⟩
  rw [← hPs] at htw
  have hPsdeg : Ps.natDegree ≤ 2 * d := hPs ▸ natDegree_conjRev_le hP₀
  have htw' : twist Ps = -P₀ := by
    simpa only [twist_neg, neg_neg, twist_twist] using congrArg (fun f ↦ -twist f) htw.symm
  have hcPs : conjRev (2 * d) Ps = P₀ := by rw [hPs, conjRev_conjRev]
  obtain ⟨r, hr⟩ : ∃ r, r = X ^ (2 * d) - P₀ * Ps := ⟨_, rfl⟩
  have hrdeg : r.natDegree ≤ 2 * (2 * d) := hr ▸ (natDegree_sub_le _ _).trans
    (max_le ((natDegree_X_pow_le _).trans (by omega)) (natDegree_mul_le.trans (by omega)))
  have htwr : twist r = r := by
    rw [hr, twist_sub, twist_mul, show twist ((X : ℂ[X]) ^ (2 * d)) =
        X ^ (2 * d) by simp [twist, pow_mul], htw, htw']; ring
  have hsymr : conjRev (2 * (2 * d)) r = r := by
    rw [hr, conjRev_sub, show 2 * (2 * d) = 2 * d + 2 * d by ring, conjRev_mul hP₀ hPsdeg, hcPs,
      conjRev_X_pow (by omega), show 2 * d + 2 * d - 2 * d = 2 * d by omega, hPs]; ring
  let R := contract 2 r
  have hRr : expand ℂ 2 R = r := expand_contract_of_odd_eq_zero (coeff_eq_zero_of_twist_eq htwr)
  have hRdeg : R.natDegree ≤ 2 * d := natDegree_contract_two_le (by omega)
  have hRsym : conjRev (2 * d) R = R :=
      expand_injective two_pos
      (by rw [expand_conjRev hRdeg, hRr, mul_comm 2 (2 * d), mul_comm (2 * d) 2]; exact hsymr)
  have hRpos : ∀ w : ℂ, ‖w‖ = 1 → ∃ s : ℝ, 0 < s ∧ R.eval w = w ^ d * s := fun w hw ↦ by
    obtain ⟨z, rfl⟩ := IsAlgClosed.isSquare w
    have hz : ‖z‖ = 1 := (mul_self_eq_one_iff.mp ((norm_mul z z).symm.trans hw)).elim id fun h ↦ by
      linarith [norm_nonneg z]
    refine ⟨1 - ‖P₀.eval z‖ ^ 2, by nlinarith [hlt z hz, norm_nonneg (P₀.eval z)], ?_⟩
    rw [← sq, show R.eval (z ^ 2) = r.eval z by rw [← hRr, expand_eval], hr, hPs, eval_sub,
        eval_pow,
      eval_X, eval_mul, eval_conjRev_of_norm_eq_one hP₀ hz, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_pow, ← Complex.mul_conj', pow_mul]
    ring
  obtain ⟨Q₀, hQ₀deg, hQ₀⟩ := exists_mul_conjRev_eq d hRdeg hRsym hRpos
  obtain ⟨H, hHdeg, hHH, htwH⟩ := exists_twisted_lift d hQ₀deg
  rw [hQ₀, hRr, Odd.neg_one_pow hd, C_neg, C_1, neg_one_mul] at *
  obtain ⟨Hs, hHs⟩ : ∃ Hs, Hs = conjRev (2 * d) H := ⟨_, rfl⟩
  rw [← hHs] at hHH htwH
  have hHsdeg : Hs.natDegree ≤ 2 * d := hHs ▸ natDegree_conjRev_le hHdeg
  have htwH' : twist Hs = -H := by
    simpa only [twist_neg, neg_neg, twist_twist] using congrArg (fun f ↦ -twist f) htwH.symm
  have hcHs : conjRev (2 * d) Hs = H := by rw [hHs, conjRev_conjRev]
  have hsum : P₀ * Ps + H * Hs = X ^ (2 * d) := by linear_combination hHH + hr
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = P₀ + Ps + C Complex.I * (H + Hs) := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = P₀ - Ps - C Complex.I * (H - Hs) := ⟨_, rfl⟩
  have htwA : twist A2 = -A2 := by
    rw [hA2, twist_add, twist_add, twist_mul, twist_add, twist_C, htw, htw', htwH, htwH']; ring
  have htwB : twist B2 = B2 := by
    rw [hB2, twist_sub, twist_sub, twist_mul, twist_sub, twist_C, htw, htw', htwH, htwH']; ring
  have hcA : conjRev (2 * d) A2 = P₀ + Ps - C Complex.I * (H + Hs) := by
    rw [hA2, conjRev_add, conjRev_add, conjRev_C_mul, conjRev_add, ← hPs, hcPs, ← hHs, hcHs,
        Complex.conj_I, C_neg]; ring
  have hcB : conjRev (2 * d) B2 = Ps - P₀ - C Complex.I * (H - Hs) := by
    rw [hB2, conjRev_sub, conjRev_sub, conjRev_C_mul, conjRev_sub, ← hPs, hcPs, ← hHs, hcHs,
        Complex.conj_I, C_neg]; ring
  have hI : C Complex.I * C Complex.I = (-1 : ℂ[X]) := by rw [← C_mul, Complex.I_mul_I, C_neg, C_1]
  have hAB : A2 * conjRev (2 * d) A2 + B2 * conjRev (2 * d) B2 = 4 * X ^ (2 * d) := by
    rw [hcA, hcB, hA2, hB2]; linear_combination 4 * hsum - 4 * H * Hs * hI
  have hA2deg : A2.natDegree ≤ 2 * d := hA2 ▸ natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le hP₀ hPsdeg)
        ((natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le hHdeg hHsdeg))
  have hB2deg : B2.natDegree ≤ 2 * d := hB2 ▸ (natDegree_sub_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le hP₀ hPsdeg))
        ((natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le hHdeg hHsdeg))))
  obtain ⟨hAX, htwA'⟩ := eq_X_mul_divX_of_twist_eq_neg htwA
  have hA'deg : A2.divX.natDegree ≤ 2 * d - 1 := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have hd1 : 1 ≤ d := hd.pos
  have hcA' : conjRev (2 * d) A2.divX = X * conjRev (2 * d) A2 := by
    conv_rhs => rw [hAX]
    rw [show 2 * d = (2 * d - 1) + 1 by omega, conjRev_X_mul hA'deg, conjRev_succ hA'deg]
  let Pc := contract 2 A2.divX
  let Qc := contract 2 B2
  have hePc : expand ℂ 2 Pc = A2.divX :=
      expand_contract_of_odd_eq_zero (coeff_eq_zero_of_twist_eq htwA')
  have heQc : expand ℂ 2 Qc = B2 := expand_contract_of_odd_eq_zero (coeff_eq_zero_of_twist_eq htwB)
  have hPcdeg : Pc.natDegree ≤ d := natDegree_contract_two_le (by omega)
  have hQcdeg : Qc.natDegree ≤ d := natDegree_contract_two_le hB2deg
  have hPQc : Pc * conjRev d Pc + Qc * conjRev d Qc = 4 * X ^ d := expand_injective two_pos (by
    simp only [map_add, map_mul, map_pow, expand_X]
    rw [expand_conjRev hPcdeg, expand_conjRev hQcdeg, hePc, heQc, hcA', map_ofNat]
    linear_combination hAB - conjRev (2 * d) A2 * hAX)
  have hh : C ((1 / 2 : ℝ) : ℂ) * 2 = (1 : ℂ[X]) := by
    rw [← map_ofNat C 2, ← C_mul, ← C_1]; congr 1; push_cast; norm_num
  refine ⟨C ((1 / 2 : ℝ) : ℂ) * Pc, C ((1 / 2 : ℝ) : ℂ) * Qc,
    (natDegree_C_mul_le _ _).trans hPcdeg, (natDegree_C_mul_le _ _).trans hQcdeg, ?_, ?_⟩
  · rw [conjRev_C_mul, conjRev_C_mul, Complex.conj_ofReal]
    linear_combination C ((1 / 2 : ℝ) : ℂ) ^ 2 * hPQc + X ^ d * (C ((1 / 2 : ℝ) : ℂ) * 2 + 1) * hh
  · rw [map_mul, map_mul, expand_C, conjRev_C_mul, conjRev_C_mul, Complex.conj_ofReal, hePc, heQc,
        hcA', hcA, hcB]
    linear_combination C ((1 / 2 : ℝ) : ℂ) * X * (hAX.symm + hA2 + hB2) + X * (2 * P₀) * hh
theorem exists_layer_su2 {d : ℕ} {P Q : ℂ[X]} (hP : P.natDegree ≤ d + 1) (hQ : Q.natDegree ≤ d + 1)
    (h : P * conjRev (d + 1) P + Q * conjRev (d + 1) Q = X ^ (d + 1)) :
    ∃ (p q : ℂ) (P' Q' : ℂ[X]), p * conj p + q * conj q = 1 ∧ P'.natDegree ≤ d ∧ Q'.natDegree ≤ d ∧
      P' * conjRev d P' + Q' * conjRev d Q' = X ^ d ∧ P = C p * (X * P') - C (conj q) * Q' ∧ Q =
          C q * (X * P') + C (conj p) * Q' := by
  have h0 : P.coeff 0 * conj (P.coeff (d + 1)) + Q.coeff 0 * conj (Q.coeff (d + 1)) = 0 := by
    have := congrArg (fun f ↦ f.coeff 0) h
    simp only [coeff_add, mul_coeff_zero, coeff_conjRev_zero] at this
    rwa [coeff_zero_eq_eval_zero (X ^ (d + 1)), eval_pow, eval_X,
        zero_pow (Nat.succ_ne_zero d)] at this
  obtain ⟨u, v, huv, hlow, hhigh⟩ := exists_unit_pair h0
  have hu' : C u * C (conj u) + C v * C (conj v) = (1 : ℂ[X]) := by
    rw [← C_mul, ← C_mul, ← C_add, huv, C_1]
  obtain ⟨F, hF⟩ : ∃ F : ℂ[X], F = C u * P + C v * Q := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : ℂ[X], Q' = C (conj u) * Q - C (conj v) * P := ⟨_, rfl⟩
  have hQ'deg : Q'.natDegree ≤ d := natDegree_le_of_le_succ
    (hQ' ▸ (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hQ)
        ((natDegree_C_mul_le _ _).trans hP)))
    (by rw [hQ', coeff_sub, coeff_C_mul, coeff_C_mul]; linear_combination hhigh)
  have hFX : F = X * F.divX := by
    have := X_mul_divX_add F
    rw [show F.coeff 0 = 0 by rw [hF, coeff_add, coeff_C_mul, coeff_C_mul, hlow], C_0,
        add_zero] at this; exact this.symm
  have hP'deg : F.divX.natDegree ≤ d := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    have hFdeg : F.natDegree ≤ d + 1 :=
        hF ▸ natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hP)
        ((natDegree_C_mul_le _ _).trans hQ); omega
  refine ⟨conj u, conj v, F.divX, Q',
      by rw [Complex.conj_conj, Complex.conj_conj]; linear_combination huv, hP'deg, hQ'deg, ?_,
    by rw [Complex.conj_conj, ← hFX, hF, hQ']; linear_combination -P * hu',
    by rw [Complex.conj_conj, ← hFX, hF, hQ']; linear_combination -Q * hu'⟩
  have hsum : F * conjRev (d + 1) F + Q' * conjRev (d + 1) Q' = X ^ (d + 1) := by
    rw [hF, hQ']; simp only [conjRev_add, conjRev_sub, conjRev_C_mul, Complex.conj_conj]
    linear_combination (P * conjRev (d + 1) P + Q * conjRev (d + 1) Q) * hu' + h
  rw [show conjRev (d + 1) F = conjRev (d + 1) (X * F.divX) from congrArg _ hFX,
      conjRev_X_mul hP'deg, conjRev_succ hQ'deg] at hsum
  exact mul_left_cancel₀ (X_ne_zero : (X : ℂ[X]) ≠ 0)
      (by linear_combination hsum - conjRev d F.divX * hFX)
theorem gqsp_decomposition_su2 {d : ℕ} {P Q : ℂ[X]} (hP : P.natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) (h : P * conjRev d P + Q * conjRev d Q = X ^ d) :
    ∃ (R₀ : Matrix (Fin 2) (Fin 2) ℂ) (Rs : List (Matrix (Fin 2) (Fin 2) ℂ)),
      R₀ ∈ unitaryGroup (Fin 2) ℂ ∧ (∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ) ∧ Rs.length = d ∧
        gqspTail Rs * R₀.map C = !![P, -conjRev d Q; Q, conjRev d P] := by
  induction d generalizing P Q with
  | zero =>
    obtain ⟨p, rfl⟩ : ∃ p, P = C p := ⟨_, eq_C_of_natDegree_le_zero hP⟩
    obtain ⟨q, rfl⟩ : ∃ q, Q = C q := ⟨_, eq_C_of_natDegree_le_zero hQ⟩
    have hpq : p * conj p + q * conj q = 1 := C_inj.mp (by
      simp only [conjRev, map_C, reflect_C, pow_zero, mul_one] at h; rwa [← C_mul, ← C_mul, ← C_add,
          ← C_1] at h)
    refine ⟨unitaryOfColumn p q, [], unitaryOfColumn_mem hpq, by simp, rfl, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [gqspTail, unitaryOfColumn, conjRev_zero_C]
  | succ d ih =>
    obtain ⟨p, q, P', Q', hpq, hP', hQ', h', hPe, hQe⟩ := exists_layer_su2 hP hQ h
    obtain ⟨R₀, Rs, hR₀, hRs, hlen, hmat⟩ := ih hP' hQ' h'
    refine ⟨R₀, unitaryOfColumn p q :: Rs, hR₀,
      fun R hR ↦
          (List.mem_cons.mp hR).elim (fun e ↦ e.symm ▸ unitaryOfColumn_mem hpq)
          (hRs R), by simp [hlen], ?_⟩
    rw [gqspTail, Matrix.mul_assoc, Matrix.mul_assoc, hmat, hPe, hQe]
    simp only [conjRev_sub, conjRev_add, conjRev_C_mul, conjRev_X_mul hP', conjRev_succ hQ',
        Complex.conj_conj]
    ext i j : 1;
    fin_cases i <;> fin_cases j <;> simp [unitaryOfColumn, signal, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring
end QuantumComputation.Specs.PhotochemistrySolution.OvBidir
end

noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
section
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder BigOperators Circuit.Notation
open Operator Matrix Qubit WithLp
theorem exists_exp_mul_I_eq_of_sq_add_sq_eq_one (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ∃ α : ℝ,
    Complex.exp (α * Complex.I) = (c : ℂ) + (s : ℂ) * Complex.I := by
  let z : ℂ := (c : ℂ) + (s : ℂ) * Complex.I
  have hns : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply, show z.re = c by simp [z], show z.im = s by simp [z]]
    linear_combination h
  exact ⟨Complex.arg z, by simpa only [Complex.norm_def, hns, Real.sqrt_one,
    Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I z⟩
theorem l2Norm_one_qubit_le {v : StateVector 1} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : 2 * ((v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2) ≤ 2 * δ ^ 2) :
    ‖WithLp.toLp 2 v‖ ≤
    δ := by rw [PiLp.norm_eq_of_L2, ← Real.sqrt_sq hδ]; apply Real.sqrt_le_sqrt; change ∑ i : Fin 2,
              ‖v i‖ ^ 2 ≤ δ ^ 2; rw [Fin.sum_univ_two, Complex.sq_norm, Complex.sq_norm,
              Complex.normSq_apply, Complex.normSq_apply]; linarith
noncomputable abbrev sinMid6 : ℝ := 98017140330 / 10 ^ 12

noncomputable abbrev cosMid7 : ℝ := 9987954562051724 / 10 ^ 16

def concretePhaseState4 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .Z 0, .Z 0, .Z 0, .S 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .Z 0, .S 0, .H 0 ]
def concretePhaseState7 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .X 0, .Z 0, .H 0, .Z 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .X 0, .Z 0, .S 0 ]
def concretePhaseState10 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .H 0, .S 0,
    .H 0, .Z 0, .S 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0 ]
def concretePhaseState12 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .H 0, .H 0, .X 0, .S 0, .Z 0, .H 0, .Z 0, .S 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .H 0, .Z 0, .H 0, .Z 0, .S 0 ]
def concretePhaseState14 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .X 0, .S 0, .Z 0, .H 0,
    .Z 0, .S 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .Z 0, .Z 0, .S 0 ]
def concretePhaseState15 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .S 0, .H 0, .Z 0, .S 0, .X 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .Z 0, .H 0, .Z 0,
    .S 0 ]
def concretePhaseState17 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .H 0, .X 0, .S 0, .H 0, .Z 0, .S 0, .X 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .Z 0, .S 0 ]
open scoped Fin.CommRing
def stateToFactor (ψ : Fin (2 ^ 1) → ℂ) : ZMod 2 → ℂ := fun b ↦ ψ ⟨b.val, b.val_lt⟩
theorem stateToFactor_sub (ψ φ : Fin (2 ^ 1) → ℂ) :
    stateToFactor (ψ - φ) = stateToFactor ψ - stateToFactor φ := rfl

theorem stateToFactor_smul (c : ℂ) (ψ : Fin (2 ^ 1) → ℂ) :
    stateToFactor (c • ψ) = c • stateToFactor ψ := rfl

def pgColZeroMatrix {d : ℕ} (u : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ := fun i j ↦
    if j.val = 0 then u i else 0
theorem pgColZeroMatrix_mulVec_basisState_zero {d : ℕ} [NeZero d]
    (u : Fin d → ℂ) : pgColZeroMatrix u *ᵥ basisState (0 : Fin d) = u :=
  funext fun i ↦ by
    simp [pgColZeroMatrix, Matrix.mulVec, dotProduct, basisState]
@[simp] theorem pgColZeroMatrix_smul {d : ℕ} (c : ℂ) (u : Fin d → ℂ) :
    pgColZeroMatrix (c • u) = c • pgColZeroMatrix u := by
  ext i j; simp [pgColZeroMatrix]
theorem pgEmbedMatrix_colZeroMatrix_mulVec_tensorState {n m : ℕ} (r : QRegister m n)
    (u : Fin (2 ^ m) → ℂ) (env : (r.Environment → ZMod 2) → ℂ) :
    (r.embedMatrix (pgColZeroMatrix u)).mulVec (r.tensorState (basisState 0) env) =
    r.tensorState u env := by
  rw [r.embedMatrix_mulVec_tensorState, pgColZeroMatrix_mulVec_basisState_zero]
end
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec

noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.BucketRouterCircuit
open scoped Circuit.Notation
open QProg
variable {Var : Type} {n N R B : ℕ}
def foldFinDyn : {m : ℕ} → (Fin m → DynamicCircuit Var n) → DynamicCircuit Var n
  | 0, _ => .identity
  | m + 1, body =>
      .seq (foldFinDyn (m := m) (fun i ↦ body (Fin.castSucc i))) (body (Fin.last m))
@[simp] theorem count_foldFinDyn_zero :
    ∀ {m arity : ℕ} {g : PrimitiveGate arity} (body : Fin m → DynamicCircuit Var n),
      (∀ i, (body i).count g = 0) →
      (foldFinDyn body).count g = 0
  | 0, _, _, _, _ => by simp [foldFinDyn, DynamicCircuit.identity]
  | m + 1, _, _, body, h => by
      simp [foldFinDyn, DynamicCircuit.count, count_foldFinDyn_zero (fun i ↦ body (Fin.castSucc i))
          (fun i ↦ h (Fin.castSucc i)), h (Fin.last m)]
end QuantumComputation.Specs.PhotochemistrySolution.BucketRouterCircuit
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PrimitiveGate
/-- Monomorphic pair selector (`0` classical decidability). -/
def muxPair : Bool → ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
  | true, va, _ => va
  | false, _, vb => vb
/-- Combine upper and lower `224`-bit limbs into a `<= 448`-bit `Nat` mask. -/
def h224 (hi lo : ℕ) : ℕ := (hi <<< 224) ||| lo
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end

noncomputable section

open scoped Matrix BigOperators
noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator Matrix QProg HermitianMat PhotochemistrySolution.BucketRouterCircuit
variable {n : ℕ}
noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
    basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm β) = β :=
  (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j :=
  (basisBitsEquiv q).symm_apply_apply j
theorem single_eq_ket (g : Fin (2 ^ n)) : (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g)
    := by simp [ket, basisState]
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j;
  have :=
      congrFun (h (basisBits n j)) i; simpa [← single_eq_ket, Matrix.mulVec_single_one] using this
noncomputable def writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    BitAssignment n :=
    basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegExt.basisBits_replaceIdx_apply]
theorem writeReg_apply_of_not_mem {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegExt.basisBits_replaceIdx_of_not_mem _ _ _ _ hw]
theorem writeReg_eq_update {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) : writeReg β r γ = Function.update β (r i₀)
    (γ i₀) := by
  funext w
  rcases Classical.em (w ∈ Set.range r.wires) with ⟨i, rfl⟩ | hw
  · exact if hi : i =
        i₀ then hi ▸ by simp else by simp [Function.update_of_ne (r.wires.injective.ne hi), hγ i hi]
  · simp [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne fun h ↦ hw ⟨i₀, h.symm⟩]
noncomputable abbrev localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
    (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {k : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k))
    (Fin (2 ^ k)) ℂ) (β : BitAssignment n) : (r.embedMatrix A).mulVec (ket β) = ∑ l : Fin (2 ^ k),
    A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors,
    show r.extractIndex ((basisBitsEquiv n).symm β) = localIdx r β by simp [QRegister.extractIndex],
    show A.mulVec (Pi.single (localIdx r β) 1) = ∑ l : Fin (2 ^ k),
        A l (localIdx r β) • Pi.single l 1
      from funext fun _ ↦
          by simp [Matrix.mulVec, dotProduct, Pi.single_apply], QRegister.tensorState_sum_left]
  exact Finset.sum_congr rfl fun l _ ↦ by
    simp [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex, writeReg, ket,
        basisState]
theorem embedMatrix_permMatrix_mulVec_ket {k : ℕ} (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) : (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
    ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))
    (fun l _ hl ↦ by simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      show σ l ≠ localIdx r β from fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])]) (by simp)]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
theorem singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
    A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
    A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (.singleton q) (basisBits 1 l) = Function.update β q b :=
    (writeReg_eq_update _ _ _ 0 fun i hi ↦ absurd (Subsingleton.elim i 0) hi).trans (hb ▸ rfl)
  rw [embedMatrix_mulVec_ket, show localIdx (.singleton q) β = if β q = 0 then 0 else 1 from
    (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b =
          0 then 0 else 1) (β q)]
  exact (Fin.sum_univ_two _).trans (by rw [hw 0 0 (by decide), hw 1 1 (by decide)])
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
noncomputable def sqrtHalf : ℂ := (Real.sqrt (1 / 2) : ℝ)
theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  dsimp [sqrtHalf]; rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; rfl
theorem star_sqrtHalf : star sqrtHalf = sqrtHalf := by dsimp [sqrtHalf]; exact Complex.conj_ofReal _
theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> first | exact .inl rfl | exact .inr rfl
theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl
theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
      simp [bitSign, one_add_one_zmod2]
theorem bitSign_mul_self (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  rcases bit_cases a with rfl | rfl <;> simp [bitSign]
theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]; rfl
theorem ket_X (q : Wire n) (β : BitAssignment n) : (Circuit.X q).eval.1.mulVec (ket β) =
    ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  refine (singleton_embedMatrix_mulVec_ket q !![0, 1; 1, 0] β).trans ?_
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]
theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
      embedMatrix_permMatrix_mulVec_ket, localIdx,
    (by decide : ∀ γ : BitAssignment 2,
          basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBitsEquiv 2).symm γ)) =
      Function.update γ 1 (γ 1 + γ 0)), writeReg_eq_update _ _ _ 1 fun i hi ↦
          by fin_cases i <;> simp_all]; simp
theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
    ket (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
      embedMatrix_permMatrix_mulVec_ket, localIdx,
    (by decide : ∀ γ : BitAssignment 3,
          basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBitsEquiv 3).symm γ)) =
      Function.update γ 2 (γ 2 + γ 0 * γ 1)), writeReg_eq_update _ _ _ 2 fun i hi ↦
          by fin_cases i <;> simp_all]; simp
theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) = if β q =
    0 then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single];
    simp [QRegister.extractIndex,
        (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = 0 ↔ b = 0)]
theorem ket_projector_one (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) = if β q =
    1 then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single];
    simp [QRegister.extractIndex,
        (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = 1 ↔ b = 1)]
theorem sqrtHalf_sq : sqrtHalf ^ 2 = 1 / 2 := by rw [sq, sqrtHalf_mul_sqrtHalf]
theorem ket_H (q : Wire n) (β : BitAssignment n) : (Circuit.H q).eval.1.mulVec (ket β) =
    sqrtHalf • (ket (Function.update β q 0) + bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  refine (singleton_embedMatrix_mulVec_ket q ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1,
      -1]) β).trans ?_
  rcases bit_cases (β q) with hb | hb <;> simp [hb, sqrtHalf, smul_add, Complex.real_smul]
def xorWirePerm (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) : Equiv.Perm (BitAssignment n) where
  toFun β := Function.update β q (β q + f β)
  invFun β := Function.update β q (β q + f β)
  left_inv β := by
    dsimp; rw [Function.update_idem, Function.update_self, hf]
    have hadd : β q + f β + f β = β q := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hadd, Function.update_eq_self]
  right_inv β := by
    dsimp; rw [Function.update_idem, Function.update_self, hf]
    have hadd : β q + f β + f β = β q := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hadd, Function.update_eq_self]
noncomputable def permUnitary (e : Equiv.Perm (BitAssignment n)) : Unitary (2 ^ n) :=
  let idxPerm : Equiv.Perm (Fin (2 ^ n)) :=
      ((basisBitsEquiv n).trans (e.trans (basisBitsEquiv n).symm)).symm
  ⟨Equiv.Perm.permMatrix ℂ idxPerm, by
    rw [Matrix.mem_unitaryGroup_iff']; ext i j;
    rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (idxPerm.symm i)]
    · by_cases hij : i = j
      · subst hij; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hij]
    · intro k _ hk
      have hki : idxPerm k ≠ i := fun h ↦ hk (by rw [← h, Equiv.symm_apply_apply])
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hki]
    · simp⟩
theorem permUnitary_mulVec_ket (e : Equiv.Perm (BitAssignment n)) (β : BitAssignment n) :
    (permUnitary e).1.mulVec (ket β) = ket (e β) := by
  let idxPerm := ((basisBitsEquiv n).trans (e.trans (basisBitsEquiv n).symm)).symm
  refine (funext fun i ↦ ?_ : (Equiv.Perm.permMatrix ℂ idxPerm).mulVec (ket β) =
    basisState (idxPerm.symm ((basisBitsEquiv n).symm β))).trans (by simp [idxPerm, ket])
  simp only [ket, basisState, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mulVec,
      dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single ((basisBitsEquiv n).symm β) (fun _ _ hk ↦ by simp [hk]) (by simp)]
  exact if hi : idxPerm i = (basisBitsEquiv n).symm β then by simp [idxPerm.eq_symm_apply.mpr hi]
    else by simp [hi, show i ≠ idxPerm.symm ((basisBitsEquiv n).symm β) from fun h ↦
                                                            hi (idxPerm.eq_symm_apply.mp h)]
noncomputable def xorWireUnitary (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) : Unitary (2 ^ n) :=
    permUnitary (xorWirePerm q f hf)
@[simp] theorem xorWireUnitary_mulVec_ket (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) (β : BitAssignment n) :
    (xorWireUnitary q f hf).1.mulVec (ket β) =
      ket (Function.update β q (β q + f β)) :=
  permUnitary_mulVec_ket (xorWirePerm q f hf) β
@[simp] theorem qAssign_obs_map_val {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    (qAssign_obs_map U A).1 = A.1.conj U.1ᴴ := rfl
theorem gidney_kraus0_mul_xorUnitary
    (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) :
    let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
    (P₀ * (Circuit.H q).eval.1) * ((xorWireUnitary q f hf).1 * P₀) = sqrtHalf • P₀ := by
  intro P₀; refine matrix_ext_ket fun β ↦ ?_
  simp only [P₀, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
  exact if hq : β q = 0 then by
    rw [ite_eq_left hq, xorWireUnitary_mulVec_ket, ket_H]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_zero, Function.update_self,
        Function.update_idem,
      ↓reduceIte, one_ne_zero, smul_zero, add_zero, show Function.update β q 0 =
          β from hq ▸ Function.update_eq_self q β, hq]
  else by simp [ite_eq_right hq]
theorem gidney_kraus1_mul_xorUnitary
    (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β)
    (Z : Unitary (2 ^ n))
    (hZ : ∀ β, Z.1.mulVec (ket β) = bitSign (f β) • ket β) :
    let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
    (Z.1 * (Circuit.X q).eval.1 * P₁ * (Circuit.H q).eval.1) * ((xorWireUnitary q f hf).1 * P₀) =
      sqrtHalf • P₀ := by
  intro P₀ P₁; refine matrix_ext_ket fun β ↦ ?_
  simp only [P₀, P₁, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      ket_projector_zero]
  exact if hq : β q = 0 then by
    rw [ite_eq_left hq, xorWireUnitary_mulVec_ket, hq, zero_add, ket_H]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_one, Function.update_self,
        Function.update_idem,
      hq, zero_ne_one, ite_false, ite_true, zero_add, ket_X, one_add_one_zmod2,
      show Function.update β q 0 = β from hq ▸ Function.update_eq_self q β, hZ, smul_smul,
          mul_assoc, bitSign_mul_self, mul_one]
  else by simp [ite_eq_right hq]
theorem cz_Combine (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) :
    sqrtHalf • (sqrtHalf • (ψ₀ + bitSign c₁ • ψ₁) + bitSign c₂ • (sqrtHalf • (ψ₀ +
    bitSign (1 + c₁) • ψ₁))) = bitSign (c₁ * c₂) • (if c₂ = 0 then ψ₀ else ψ₁) := by
  ext i
  rcases bit_cases c₁ with rfl | rfl
  · rcases bit_cases c₂ with rfl | rfl <;> dsimp [bitSign] <;>
      first
      | linear_combination (2 * ψ₀ i) * sqrtHalf_mul_sqrtHalf
      | linear_combination (2 * ψ₁ i) * sqrtHalf_mul_sqrtHalf
  · rcases bit_cases c₂ with rfl | rfl <;> rw [one_add_one_zmod2] <;> dsimp [bitSign] <;>
      first
      | linear_combination (2 * ψ₀ i) * sqrtHalf_mul_sqrtHalf
      | linear_combination (-2 * ψ₁ i) * sqrtHalf_mul_sqrtHalf
theorem ket_CZ_circuit (w₁ w₂ : Wire n) (h₁₂ : w₁ ≠ w₂) (β : BitAssignment n) :
    (Circuit.H w₂ ;;ᶜ Circuit.CNOT w₁ w₂ h₁₂ ;;ᶜ Circuit.H w₂).eval.1.mulVec (ket β) =
      bitSign (β w₁ * β w₂) • ket β := by
  simp only [eval_seq_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT,
    Function.update_self, Function.update_of_ne h₁₂, Function.update_idem, zero_add]
  rw [cz_Combine (β w₁) (β w₂)]
  rcases bit_cases (β w₂) with h₂ | h₂ <;> simp [h₂, h₂ ▸ Function.update_eq_self w₂ β]
end QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
end

noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
noncomputable abbrev pgOpNorm {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

theorem two_pi_div_two_pow_nonneg (j : ℕ) : 0 ≤ 2 * Real.pi / (2 : ℝ) ^ j := by positivity
theorem sin_two_pi_div_two_pow_one_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 1) - 0| ≤ 0 := by
  rw [show 2 * Real.pi / (2 : ℝ) ^ 1 = Real.pi by ring, Real.sin_pi, sub_self, abs_zero]

def concretePhaseState9 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .H 0, .X 0, .S 0, .Z 0, .H 0, .Z 0, .S 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .X 0, .Z 0, .S 0, .H 0 ]
def concretePhaseState11 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .X 0, .S 0, .X 0, .H 0,
    .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .H 0, .Z 0, .S 0, .H 0 ]
def concretePhaseState13 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .H 0, .S 0, .H 0, .Z 0,
    .S 0, .X 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .Z 0 ]
def concretePhaseState16 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .S 0, .H 0, .Z 0,
    .X 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .Z 0, .S 0, .H 0 ]
def concretePhaseState18 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .X 0, .Z 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .Z 0, .Z 0, .S 0, .H 0 ]
open scoped Fin.CommRing
noncomputable def gradZeroEnv {n b : ℕ} (rGrad : QRegister b n) (v : Fin (2 ^ n) → ℂ) :
    (rGrad.Environment → ZMod 2) → ℂ := fun e ↦ v (rGrad.basisSplitEquiv.symm (0, e))
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec

open Real Complex BigOperators
/-! ## Section 1: Species Mapping (`Photochemistry.atomicNumber` -> `0=H, 1=C, 2=N, 3=O`) -/

/--
Canonical species code on `Fin 47` matching `gNNQ` / `enSpecs` (`0=H, 1=C, 2=N, 3=O`).
Note: `Photochemistry.atomicNumber` places `C` at `0..22`, `H` at `23..42`, `N` at `43..45`,
and `O` at `46`.
-/
def nucSpecies (n : Fin 47) : Fin 4 :=
  if n.val < 23 then 1
  else if n.val < 43 then 0
  else if n.val < 46 then 2
  else 3
/-- Atomic number directly from canonical species code `0=H, 1=C, 2=N, 3=O`. -/
def speciesZ : Fin 4 → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 7
  | 3 => 8
theorem speciesZ_nucSpecies_all :
    ∀ n : Fin 47, speciesZ (nucSpecies n) =
      atomicNumber_frozen ⟨n.val, Nat.lt_trans n.isLt (by decide)⟩ := by
  decide +kernel
theorem speciesZ_nucSpecies_eq (n : Fin 47) :
    speciesZ (nucSpecies n) = atomicNumber_frozen ⟨n.val, Nat.lt_trans n.isLt (by decide)⟩ :=
  speciesZ_nucSpecies_all n
/-! ## Section 2: True Open-Box Signed Coordinate Difference & Short-Range `Fin 8` Bucket -/

/-- Exact `Fin 8` short-range bucket map on squared grid distance `d2` with cutoff `d2 < 48`. -/
def fin8Bin (d2 : ℕ) : Fin 8 :=
  if 48 ≤ d2 then 0
  else if d2 == 0 then 1
  else if d2 == 1 then 2
  else if d2 ≤ 3 then 3
  else if d2 ≤ 7 then 4
  else if d2 ≤ 15 then 5
  else if d2 ≤ 31 then 6
  else 7
/--
True open-box 1D grid distance `|twosComplement u - twosComplement v| ∈ [0, 255]` matching
`Photochemistry.position` (fixing the wrap bug of periodic `torusDist1D`).
-/
def openBoxDist1D (u v : Fin 256) : ℕ :=
  (twosComplement_frozen u - twosComplement_frozen v).natAbs
/--
Biased unsigned coordinate `u.val ^^^ 128 ∈ [0, 255]` satisfying
`(biasCoord u : ℤ) - (biasCoord v : ℤ) = twosComplement u - twosComplement v`.
-/
def biasCoord (u : Fin 256) : ℕ := u.val ^^^ 128
theorem biasCoord_eq_all : ∀ u : Fin 256, (biasCoord u : ℤ) - 128 = twosComplement_frozen u ∧
    biasCoord u < 256 := by decide +kernel
theorem biasCoord_sub_eq_twosComplement (u v : Fin 256) : (biasCoord u : ℤ) - (biasCoord v : ℤ) =
    twosComplement_frozen u - twosComplement_frozen v := by
  linarith [(biasCoord_eq_all u).1, (biasCoord_eq_all v).1]
def signedAbsD9 (d9 : ℕ) : ℕ := if d9 < 256 then d9 else 512 - d9
theorem openBoxDist1D_eq_signedAbsD9 (u v : Fin 256) : openBoxDist1D u v =
    signedAbsD9 ((512 + biasCoord u - biasCoord v) % 512) := by
  have ⟨hsub, ha, hb⟩ : _ ∧ _ ∧ _ :=
      ⟨biasCoord_sub_eq_twosComplement u v, (biasCoord_eq_all u).2, (biasCoord_eq_all v).2⟩
  unfold openBoxDist1D signedAbsD9; split_ifs <;> omega
/-! ## Section 3: Frozen 41-Bit Coin & 40-Bit `rOut40Layout` Interface -/

/--
Exact zero-remainder LCU coin sector (`c : Fin (2 ^ 41)` on `rOuter41Layout`, preserving
`mLayout = 80` and `rZ : Fin 41`):
- `.idle`: all 40 output bits `0`
- `.ee n1 e1 e2`: `e1 < e2`, `1` nucleus + `2` electrons (`wHasN1=1, wRawHasN2=0, wHasE1=1,
wRawHasE2=1`)
- `.nn n1 n2 e1`: `n1 < n2`, `2` nuclei + `1` electron (`wHasN1=1, wRawHasN2=1, wHasE1=1,
wRawHasE2=0`)
- `.en n1 e1`: `1` nucleus + `1` electron (`wHasN1=1, wRawHasN2=0, wHasE1=1, wRawHasE2=0`, 0
screening)
- `.kin i ax`: `1` particle + `ax : Fin 3` (`j=34,38..39`, identical to `KineticFast`).
-/
inductive ZeroNEremSector where
  | idle : ZeroNEremSector
  | ee : Fin 47 → Fin 187 → Fin 187 → ZeroNEremSector
  | nn : Fin 47 → Fin 47 → Fin 187 → ZeroNEremSector
  | en : Fin 47 → Fin 187 → ZeroNEremSector
  | kin : Particle_frozen → Fin 3 → ZeroNEremSector
  deriving DecidableEq
/--
Pack 40-bit `rOut40Layout` word (`j = 0..39`):
- `0`: `hasN1`, `1`: `rawHasN2`, `2..7`: `n1` (`6`b), `8..13`: `n2` (`6`b),
- `14`: `hasE1`, `15`: `rawHasE2`, `16..23`: `e1` (`8`b), `24..31`: `e2` (`8`b),
- `32`: `isScreen` (`1` on `.ee, .nn`, `0` otherwise),
- `33`: `isPot` (`1` on `.ee, .nn, .en`, `0` otherwise),
- `34`: `isKin` (`1` on `.kin` ONLY — 100% identical to `KineticFast`),
- `35`: `isNN` (`1` on `.nn`, `0` otherwise),
- `36..37`: `sp1` (`(nucSpecies n1).val` pre-decoded in Stage 1 at 0 Stage-4 Toffoli cost),
- `38..39`: `aux2` (`ax.val` on `.kin` matching `KineticFast`; `(nucSpecies n2).val` on `.nn`).
-/
def packOut40ZeroNErem (hasN1 hasN2 : Bool) (n1 n2 : ℕ) (hasE1 hasE2 : Bool) (e1 e2 : ℕ)
    (isScreen isPot isKin isNN : Bool) (sp1 aux2 : ℕ) : ℕ :=
  (if hasN1 then 1 else 0) |||
  ((if hasN2 then 1 else 0) <<< 1) |||
  ((n1 &&& 63) <<< 2) |||
  ((n2 &&& 63) <<< 8) |||
  ((if hasE1 then 1 else 0) <<< 14) |||
  ((if hasE2 then 1 else 0) <<< 15) |||
  ((e1 &&& 255) <<< 16) |||
  ((e2 &&& 255) <<< 24) |||
  ((if isScreen then 1 else 0) <<< 32) |||
  ((if isPot then 1 else 0) <<< 33) |||
  ((if isKin then 1 else 0) <<< 34) |||
  ((if isNN then 1 else 0) <<< 35) |||
  ((sp1 &&& 3) <<< 36) |||
  ((aux2 &&& 3) <<< 38)
/-- Exact 40-bit `rOut40Layout` target mask for every `ZeroNEremSector` outcome. -/
def zeroNEremOutMask : ZeroNEremSector → ℕ
  | .idle => 0
  | .ee n1 e1 e2 =>
      packOut40ZeroNErem true false n1.val 0 true true e1.val e2.val
        true true false false (nucSpecies n1).val 0
  | .nn n1 n2 e1 =>
      packOut40ZeroNErem true true n1.val n2.val true false e1.val 0
        true true false true (nucSpecies n1).val (nucSpecies n2).val
  | .en n1 e1 =>
      packOut40ZeroNErem true false n1.val 0 true false e1.val 0
        false true false false (nucSpecies n1).val 0
  | .kin i ax =>
      if i.val < 47 then
        packOut40ZeroNErem true false i.val 0 false false 0 0
          false false true false 0 ax.val
      else
        packOut40ZeroNErem false false 0 0 true false (i.val - 47) 0
          false false true false 0 ax.val
/-! ## Section 4: Exact 41-Bit Block Weights (`2^55 / (1381915000000 * gridSpacing)`) -/
end QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec

open PhotochemistrySolution.ZeroNEremSpec
/-- Total-arithmetic constructor for `Fin 47` with zero embedded tactic terms. -/
def mkFin47 (k : ℕ) : Fin 47 := ⟨k % 47, Nat.mod_lt k (Nat.succ_pos 46)⟩
/-- Total-arithmetic constructor for `Fin 187` with zero embedded tactic terms. -/
def mkFin187 (k : ℕ) : Fin 187 := ⟨k % 187, Nat.mod_lt k (Nat.succ_pos 186)⟩
/-- Total-arithmetic constructor for `Particle` (`Fin 234`) with zero embedded tactic terms. -/
def mkFin234 (k : ℕ) : Particle_frozen := ⟨k % 234, Nat.mod_lt k (Nat.succ_pos 233)⟩
/-- Total-arithmetic constructor for `Fin 3` with zero embedded tactic terms. -/
def mkFin3 (k : ℕ) : Fin 3 := ⟨k % 3, Nat.mod_lt k (Nat.succ_pos 2)⟩
/-- Product-splitting identity for filtering `Fin (A * B)` when `0 < B`. -/
theorem card_fin_mul_split {A B : ℕ} (_hB : 0 < B) (P : ℕ → Prop)
    [DecidablePred P] : ((Finset.univ : Finset (Fin (A * B))).filter (fun c ↦ P c.val)).card = ∑ a :
    Fin A, ((Finset.univ : Finset (Fin B)).filter (fun b ↦ P (a.val * B + b.val))).card := by
  simp only [Finset.card_filter, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    congrArg (if P · then 1 else 0) (by dsimp [finProdFinEquiv]; ring)
/-- Exact prefix cardinality `#{x : Fin N | x.val < M} = M` whenever `M ≤ N`. -/
theorem card_fin_lt_of_le {M N : ℕ} (hle : M ≤ N) : ((Finset.univ : Finset (Fin N)).filter (fun x ↦
    x.val < M)).card = M :=
  (Finset.card_bij (fun (x : Fin N) hx ↦ (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin M))
      (fun _ _ ↦ Finset.mem_univ _)
    (fun _ _ _ _ h ↦ Fin.ext (congrArg (Fin.val : Fin M → ℕ) h))
    (fun (y : Fin M) _ ↦ ⟨⟨y.val, y.isLt.trans_le hle⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        y.isLt⟩, rfl⟩)).trans
    (Finset.card_fin M)
end QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
end

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix
namespace QuantumComputation.Specs.PhotochemistrySolution
open Operator WithLp NormedSpace
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem jacobi_ja_norm_unitary_mul (U : 𝐔[I]) (M : Matrix I I ℂ) : ‖(U : Matrix I I ℂ) * M‖ =
    ‖M‖ := by
  have h : ‖(U : Matrix I I ℂ) * M‖ * ‖(U : Matrix I I ℂ) * M‖ = ‖M‖ * ‖M‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self ((U : Matrix I I ℂ) * M),
      Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix I I ℂ)ᴴ,
      show (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 from U.2.1,
      Matrix.one_mul, Matrix.l2_opNorm_conjTranspose_mul_self]
  nlinarith [norm_nonneg ((U : Matrix I I ℂ) * M), norm_nonneg M]
theorem jacobi_ja_norm_mul_unitary (M : Matrix I I ℂ) (U : 𝐔[I]) : ‖M * (U : Matrix I I ℂ)‖ =
    ‖M‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose (M * (U : Matrix I I ℂ)), Matrix.conjTranspose_mul,
    show (U : Matrix I I ℂ)ᴴ = ((star U : 𝐔[I]) : Matrix I I ℂ) from rfl,
    jacobi_ja_norm_unitary_mul (star U) Mᴴ, Matrix.l2_opNorm_conjTranspose]
theorem jacobi_ja_exp_neg_mul_I_mem_unitary {H : Matrix I I ℂ} (hH : Hᴴ = H)
    (s : ℝ) : NormedSpace.exp ((-Complex.I * (s : ℂ)) • H) ∈ 𝐔[I] := by
  let +nondep : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℂ (Matrix I I ℂ)
  have hskew : (-Complex.I * (s : ℂ)) • H ∈ skewAdjoint (Matrix I I ℂ) := by
    rw [skewAdjoint.mem_iff, star_smul, Matrix.star_eq_conjTranspose, hH, star_mul',
        Complex.star_def, Complex.conj_ofReal, map_neg,
        Complex.conj_I]; ext i j; simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]; ring
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskew
theorem jacobi_ja_norm_mul_exp_neg_I {H : Matrix I I ℂ} (hH : Hᴴ = H) (M : Matrix I I ℂ)
    (s : ℝ) : ‖M * NormedSpace.exp ((-Complex.I * (s : ℂ)) • H)‖ = ‖M‖ :=
    jacobi_ja_norm_mul_unitary M ⟨NormedSpace.exp ((-Complex.I * (s : ℂ)) • H),
    jacobi_ja_exp_neg_mul_I_mem_unitary hH s⟩
theorem jacobi_ja_hasDerivAt_exp_neg_I (H : Matrix I I ℂ)
    (s : ℝ) : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp ((-Complex.I * (u : ℂ)) • H))
    ((-Complex.I) • (H * NormedSpace.exp ((-Complex.I * (s : ℂ)) • H))) s := by
  simpa only [smul_mul_assoc, show ∀ u : ℝ, (u : ℝ) • ((-Complex.I) • H) =
      (-Complex.I * (u : ℂ)) • H from
    fun u ↦ Matrix.ext fun _ _ ↦
        by simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]; ring] using
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := Matrix I I ℂ) ((-Complex.I) • H) s
theorem jacobi_ja_norm_le_of_hasDerivAt {f f' : ℝ → Matrix I I ℂ} {B B' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hB : ∀ s, HasDerivAt B (B' s) s)
    (hf0 : f 0 = 0) (hB0 : B 0 = 0) (hbound : ∀ s, 0 ≤ s → ‖f' s‖ ≤ B' s) {τ : ℝ}
        (hτ : 0 ≤ τ) : ‖f τ‖ ≤ B τ :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary (fun x _ ↦
      (hf x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (hf x).hasDerivWithinAt) (by simp [hf0, hB0]) hB (fun x hx ↦ hbound x hx.1)
        (Set.right_mem_Icc.mpr hτ)
noncomputable def expNegITaylor (H : Matrix I I ℂ) (D : ℕ) (s : ℝ) : Matrix I I ℂ :=
    ∑ j ∈ Finset.range (D + 1), (((-Complex.I * (s : ℂ)) ^ j) / (j.factorial : ℂ)) • (H ^ j)
@[simp] theorem expNegITaylor_zero (H : Matrix I I ℂ) (D : ℕ) :
    expNegITaylor H D 0 = 1 := by
  simp [expNegITaylor, Finset.sum_range_succ']
theorem hasDerivAt_expNegITaylor_succ (H : Matrix I I ℂ) (D : ℕ)
    (s : ℝ) : HasDerivAt (expNegITaylor H (D + 1))
    ((-Complex.I) • (H * expNegITaylor H D s)) s := by
  rw [show expNegITaylor H (D + 1) = fun u : ℝ ↦ (1 : Matrix I I ℂ) + (∑ j ∈ Finset.range (D + 1),
      fun v : ℝ ↦
          (((-Complex.I * (v : ℂ)) ^ (j + 1)) / ((j + 1).factorial : ℂ)) • (H ^ (j + 1))) u from
    funext fun u ↦
        by unfold expNegITaylor; rw [Finset.sum_range_succ', Finset.sum_apply];
             simp [add_comm]]
  refine ((HasDerivAt.sum fun j _ ↦ ?_).const_add (1 : Matrix I I ℂ)).congr_deriv
    (by unfold expNegITaylor; rw [Matrix.mul_sum, Finset.smul_sum])
  refine ((show HasDerivAt (fun u : ℝ ↦ ((-Complex.I * (u : ℂ)) ^ (j + 1)) /
      ((j + 1).factorial : ℂ))
      ((-Complex.I) * (((-Complex.I * (s : ℂ)) ^ j) / (j.factorial : ℂ))) s from
    ((((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-Complex.I)).congr_deriv (by simp) :
      HasDerivAt (fun u : ℝ ↦ -Complex.I * (u : ℂ)) (-Complex.I) s).pow (j + 1) |>.div_const
        ((j + 1).factorial : ℂ)).congr_deriv (by
          simp only [add_tsub_cancel_right, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
              Nat.cast_one, Complex.ofRealCLM_apply]
          field_simp [show (j : ℂ) + 1 ≠ 0 from mod_cast Nat.succ_ne_zero j])).smul_const (H ^ (j +
              1))).congr_deriv
    (by rw [pow_succ', Matrix.mul_smul, smul_smul])
theorem opNorm_expNegITaylor_sub_exp_le {H : Matrix I I ℂ} (hH : Hᴴ = H) (D : ℕ) {s : ℝ}
    (hs : 0 ≤ s) : ‖expNegITaylor H D s - NormedSpace.exp ((-Complex.I * (s : ℂ)) • H)‖ ≤
    (s * ‖H‖) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  have hB (k : ℕ) (u : ℝ) : HasDerivAt (fun v : ℝ ↦ (v * ‖H‖) ^ (k + 1) / ((k + 1).factorial : ℝ))
      (‖H‖ * ((u * ‖H‖) ^ k / (k.factorial : ℝ))) u := by
    refine (((((hasDerivAt_id u).mul_const ‖H‖).congr_deriv (one_mul _)).pow (k + 1)).div_const
      ((k + 1).factorial : ℝ)).congr_deriv ?_
    rw [id_eq, Nat.factorial_succ]; push_cast; field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
  induction D generalizing s with
  | zero =>
    have h0 (u : ℝ) : HasDerivAt (expNegITaylor H 0) 0 u :=
      (show expNegITaylor H 0 = fun _ ↦ (1 : Matrix I I ℂ) from
        funext fun _ ↦ by simp [expNegITaylor]) ▸ hasDerivAt_const u 1
    refine jacobi_ja_norm_le_of_hasDerivAt
      (fun u ↦ (h0 u).sub (jacobi_ja_hasDerivAt_exp_neg_I H u))
      (hB 0) (by simp) (by simp) (fun u _ ↦ ?_) hs
    rw [zero_sub, norm_neg, norm_smul, norm_neg, Complex.norm_I, one_mul,
      jacobi_ja_norm_mul_exp_neg_I hH]
    simp
  | succ D ih =>
    refine jacobi_ja_norm_le_of_hasDerivAt
      (fun u ↦ (hasDerivAt_expNegITaylor_succ H D u).sub (jacobi_ja_hasDerivAt_exp_neg_I H u))
      (hB (D + 1)) (by simp) (by simp) (fun u hu ↦ ?_) hs
    rw [← smul_sub, ← Matrix.mul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact (norm_mul_le H _).trans (mul_le_mul_of_nonneg_left (ih hu) (norm_nonneg H))
def chebyshevT : ℕ → Matrix I I ℂ → Matrix I I ℂ
  | 0, _ => 1
  | 1, H => H
  | k + 2, H => (2 : ℂ) • (H * chebyshevT (k + 1) H) - chebyshevT k H
@[simp] theorem chebyshevT_zero (H : Matrix I I ℂ) : chebyshevT 0 H = 1 := rfl
@[simp] theorem chebyshevT_one (H : Matrix I I ℂ) : chebyshevT 1 H = H := rfl
theorem chebyshevT_add_two (H : Matrix I I ℂ) (k : ℕ) :
    chebyshevT (k + 2) H = (2 : ℂ) • (H * chebyshevT (k + 1) H) - chebyshevT k H := rfl
theorem mul_chebyshevT_zero (H : Matrix I I ℂ) : H * chebyshevT 0 H = chebyshevT 1 H := by
  simp [chebyshevT]
theorem mul_chebyshevT_succ (H : Matrix I I ℂ) (k : ℕ) : H * chebyshevT (k + 1) H =
    (1 / 2 : ℂ) • (chebyshevT (k + 2) H + chebyshevT k H) := by
  simp only [chebyshevT, sub_add_cancel]; rw [smul_smul]; norm_num
noncomputable def chebStep (c : ℕ → ℂ) : ℕ → ℂ
  | 0 => (c 1) / 2
  | 1 => c 0 + (c 2) / 2
  | k + 2 => (c (k + 1)) / 2 + (c (k + 3)) / 2
theorem sum_mul_chebyshevT_sub (H : Matrix I I ℂ) (c : ℕ → ℂ) :
    ∀ m : ℕ,
      (∑ k ∈ Finset.range (m + 2), H * (c k • chebyshevT k H)) -
        (∑ k ∈ Finset.range (m + 2), chebStep c k • chebyshevT k H) =
      ((c (m + 1)) / 2) • chebyshevT (m + 2) H -
        ((c (m + 2)) / 2) • chebyshevT (m + 1) H
  | 0 => by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Matrix.mul_smul, mul_chebyshevT_zero, mul_chebyshevT_succ, smul_add, smul_smul,
      mul_one_div, chebStep, add_smul]
    abel
  | m + 1 => by
    rw [Finset.sum_range_succ _ (m + 2), Finset.sum_range_succ _ (m + 2),
      sub_eq_iff_eq_add.mp (sum_mul_chebyshevT_sub H c m), show H *
          (c (m + 2) • chebyshevT (m + 2) H) =
        (c (m + 2) / 2) • chebyshevT (m + 3) H + (c (m + 2) / 2) • chebyshevT (m + 1) H by
          rw [Matrix.mul_smul, mul_chebyshevT_succ H (m + 1), smul_smul, mul_one_div, smul_add],
      show chebStep c (m + 2) • chebyshevT (m + 2) H =
        (c (m + 1) / 2) • chebyshevT (m + 2) H + (c (m + 3) / 2) • chebyshevT (m +
            2) H from add_smul _ _ _]
    abel
noncomputable def chebPowCoeff : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, k => chebStep (chebPowCoeff j) k
theorem chebPowCoeff_eq_zero_of_lt {j k : ℕ} (h : j < k) : chebPowCoeff j k = 0 := by
  induction j generalizing k with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rfl
  | succ j ih =>
    rcases k with _ | _ | m <;> first | omega |
      simp [chebPowCoeff, chebStep, ih (by omega : j < m + 1), ih (by omega : j < m + 3)]
theorem pow_eq_sum_chebyshevT (H : Matrix I I ℂ) :
    ∀ (j D : ℕ), j ≤ D →
      H ^ j = ∑ k ∈ Finset.range (D + 1), chebPowCoeff j k • chebyshevT k H
  | 0, D, _ => by
    rw [pow_zero, Finset.sum_eq_single 0]
    · simp [chebPowCoeff, chebyshevT]
    · intro k _ hk; obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk; simp [chebPowCoeff]
    · exact fun h ↦ (h (Finset.mem_range.mpr (Nat.zero_lt_succ D))).elim
  | j + 1, D, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
    rw [pow_succ', pow_eq_sum_chebyshevT H j (m + 1) (by omega), Matrix.mul_sum]
    exact sub_eq_zero.mp (by
      simpa only [chebPowCoeff, chebPowCoeff_eq_zero_of_lt (by omega : j < m + 1),
        chebPowCoeff_eq_zero_of_lt (by omega : j < m + 2), zero_div, zero_smul, sub_zero] using
        sum_mul_chebyshevT_sub H (chebPowCoeff j) m)
noncomputable def jacobiAngerTruncCoeff (D : ℕ) (s : ℝ) (k : ℕ) : ℂ :=
    ∑ j ∈ Finset.range (D + 1), (((-Complex.I * (s : ℂ)) ^ j) / (j.factorial : ℂ)) *
    chebPowCoeff j k
noncomputable def chebyshevPolyApprox (H : Matrix I I ℂ) (D : ℕ) (s : ℝ) : Matrix I I ℂ :=
    ∑ k ∈ Finset.range (D + 1), jacobiAngerTruncCoeff D s k • chebyshevT k H
theorem chebyshevPolyApprox_eq_expNegITaylor (H : Matrix I I ℂ) (D : ℕ) (s : ℝ) :
    chebyshevPolyApprox H D s = expNegITaylor H D s := by
  unfold chebyshevPolyApprox jacobiAngerTruncCoeff expNegITaylor
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [pow_eq_sum_chebyshevT H j D (Finset.mem_range_succ_iff.mp hj), Finset.smul_sum]
  simp_rw [smul_smul]
theorem opNorm_chebyshevPolyApprox_sub_exp_le {H : Matrix I I ℂ} (hH : Hᴴ = H) (D : ℕ) {s : ℝ}
    (hs : 0 ≤ s) : ‖chebyshevPolyApprox H D s - NormedSpace.exp ((-Complex.I * (s : ℂ)) • H)‖ ≤
    (s * ‖H‖) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  rw [chebyshevPolyApprox_eq_expNegITaylor]; exact opNorm_expNegITaylor_sub_exp_le hH D hs
theorem opNorm_chebyshevPolyApprox_sub_exp_le_of_norm_le_one {H : Matrix I I ℂ} (hH : Hᴴ = H)
    (hnorm : ‖H‖ ≤ 1) (D : ℕ) {s : ℝ} (hs : 0 ≤ s) : ‖chebyshevPolyApprox H D s -
    NormedSpace.exp ((-Complex.I * (s : ℂ)) • H)‖ ≤ s ^ (D + 1) / ((D + 1).factorial : ℝ) := by
  have hpow : (s * ‖H‖) ^ (D + 1) ≤ s ^ (D + 1) :=
    pow_le_pow_left₀ (mul_nonneg hs (norm_nonneg H))
        ((mul_le_mul_of_nonneg_left hnorm hs).trans_eq (mul_one s)) (D + 1)
  exact (opNorm_chebyshevPolyApprox_sub_exp_le hH D hs).trans (div_le_div_of_nonneg_right hpow
      (Nat.cast_nonneg _))
end QuantumComputation.Specs.PhotochemistrySolution

namespace QuantumComputation.Specs.PhotochemistrySolution.GQSP
open Polynomial ComplexConjugate
noncomputable def laurentPoly (K : ℕ) (c : ℕ → ℂ) : ℂ[X] :=
    C (c 0) * X ^ K + ∑ k ∈ Finset.Icc 1 K, C (c k) * (X ^ (K + k) + X ^ (K - k))
theorem natDegree_laurentPoly_le (K : ℕ) (c : ℕ → ℂ) : (laurentPoly K c).natDegree ≤ 2 * K := by
  unfold laurentPoly
  refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le K).trans
      (by omega))) ?_
  refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ (natDegree_C_mul_le _ _).trans ?_
  rw [Finset.mem_Icc] at hk
  exact natDegree_add_le_of_degree_le ((natDegree_X_pow_le _).trans (by omega))
      ((natDegree_X_pow_le _).trans (by omega))
theorem eval_laurentPoly_of_norm_eq_one (K : ℕ) (c : ℕ → ℂ) {z : ℂ}
    (hz : ‖z‖ = 1) : (laurentPoly K c).eval z = z ^ K * (c 0 + ∑ k ∈ Finset.Icc 1 K, c k *
    (z ^ k + conj z ^ k)) := by
  have hz_mul : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, one_pow, Complex.ofReal_one]
  unfold laurentPoly
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum, mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) (mul_comm _ _) (Finset.sum_congr rfl fun k hk ↦ ?_)
  rw [pow_add, show z ^ (K - k) = z ^ K * conj z ^ k by
    rw [show z ^ K = z ^ (K - k) *
        z ^ k by rw [← pow_add, Nat.sub_add_cancel (Finset.mem_Icc.mp hk).2],
      mul_assoc, ← mul_pow, hz_mul, one_pow, mul_one]]
  ring
theorem norm_eval_laurentPoly_of_norm_eq_one (K : ℕ) (c : ℕ → ℂ) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖(laurentPoly K c).eval z‖ = ‖c 0 + ∑ k ∈ Finset.Icc 1 K, c k *
    (z ^ k + conj z ^ k)‖ := by
  rw [eval_laurentPoly_of_norm_eq_one K c hz, norm_mul, norm_pow, hz, one_pow, one_mul]
theorem gqspBr_unitary_star_pow_mul_pow_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) (m : ℕ) :
    (Uᴴ) ^ m * U ^ m = 1 := by
  rw [← ((commute_iff_eq Uᴴ U).mpr (by
    rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hU,
      Unitary.mul_star_self_of_mem hU])).mul_pow,
    ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hU, one_pow]
theorem mul_star_pow_aeval_laurentPoly {n : Type*} [Fintype n] [DecidableEq n] (K : ℕ) (c : ℕ → ℂ)
    {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) : (Uᴴ) ^ K * aeval U (laurentPoly K c) =
    c 0 • (1 : Matrix n n ℂ) + ∑ k ∈ Finset.Icc 1 K, c k • (U ^ k + (Uᴴ) ^ k) := by
  have hcancel :=
      gqspBr_unitary_star_pow_mul_pow_eq_one hU; unfold laurentPoly; simp only [map_add, map_mul,
      aeval_C, map_pow, aeval_X, map_sum, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]; rw [Matrix.mul_add, Matrix.mul_smul, hcancel K, Matrix.mul_sum]; congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp only [Finset.mem_Icc] at hk; rw [Matrix.mul_smul]; congr 1; rw [Matrix.mul_add]
  exact congrArg₂ (· + ·) (by rw [pow_add, ← Matrix.mul_assoc, hcancel K, Matrix.one_mul])
    (by rw [show (Uᴴ) ^ K = (Uᴴ) ^ k * (Uᴴ) ^ (K - k) by rw [← pow_add, Nat.add_sub_cancel' hk.2],
      Matrix.mul_assoc, hcancel (K - k), Matrix.mul_one])
theorem chebyshevT_half_add_star_eq {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    ∀ k : ℕ, chebyshevT k ((1 / 2 : ℂ) • (U + Uᴴ)) = (1 / 2 : ℂ) • (U ^ k + (Uᴴ) ^ k) ∧
      chebyshevT (k + 1) ((1 / 2 : ℂ) • (U + Uᴴ)) =
        (1 / 2 : ℂ) • (U ^ (k + 1) + (Uᴴ) ^ (k + 1))
  | 0 => ⟨Matrix.ext fun _ _ ↦ by simp [chebyshevT]; ring, by simp [chebyshevT]⟩
  | k + 1 => by
    obtain ⟨ih0, ih1⟩ := chebyshevT_half_add_star_eq hU k
    refine ⟨ih1, ?_⟩
    rw [chebyshevT, ih1, ih0, smul_mul_smul_comm, smul_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, ← pow_succ' U (k + 1), ← pow_succ' Uᴴ (k + 1),
      show U * (Uᴴ) ^ (k + 1) = (Uᴴ) ^ k by
        rw [pow_succ', ← Matrix.mul_assoc, ← star_eq_conjTranspose, Unitary.mul_star_self_of_mem hU,
            Matrix.one_mul],
      show Uᴴ * U ^ (k + 1) = U ^ k by
        rw [pow_succ', ← Matrix.mul_assoc, ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hU,
            Matrix.one_mul]]
    exact Matrix.ext fun _ _ ↦ by
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
noncomputable def jacobiAngerLaurentCoeff (D : ℕ) (s : ℝ) : ℕ → ℂ
  | 0 => jacobiAngerTruncCoeff D s 0
  | k + 1 => (1 / 2 : ℂ) * jacobiAngerTruncCoeff D s (k + 1)
noncomputable def jacobiAngerLaurentPoly (D : ℕ) (s : ℝ) : ℂ[X] :=
    laurentPoly D (jacobiAngerLaurentCoeff D s)
theorem mul_star_pow_aeval_jacobiAngerLaurentPoly {n : Type*} [Fintype n] [DecidableEq n] (D : ℕ)
    (s : ℝ) {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) : (Uᴴ) ^ D *
    aeval U (jacobiAngerLaurentPoly D s) = chebyshevPolyApprox ((1 / 2 : ℂ) • (U + Uᴴ)) D s := by
  unfold jacobiAngerLaurentPoly; rw [mul_star_pow_aeval_laurentPoly D _ hU];
  unfold chebyshevPolyApprox
  rw [show Finset.range (D + 1) = insert 0 (Finset.Icc 1 D) by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp)]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun k hk ↦ ?_)
  simp only [Finset.mem_Icc] at hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [(chebyshevT_half_add_star_eq hU (m + 1)).1, smul_smul]; congr 1;
  simp only [jacobiAngerLaurentCoeff]; ring
theorem norm_eval_jacobiAngerLaurentPoly_le (D : ℕ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : ‖z‖ = 1) : ‖(jacobiAngerLaurentPoly D s).eval z‖ ≤ 1 + s ^ (D + 1) /
    ((D + 1).factorial : ℝ) := by
  let U : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal fun _ ↦ z
  have hz_mul : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, one_pow, Complex.ofReal_one]
  have hU : U ∈ unitary (Matrix (Fin 1) (Fin 1) ℂ) := Unitary.mem_iff.mpr (by
    simp [U, star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      mul_comm z (conj z) ▸ hz_mul, hz_mul])
  let H : Matrix (Fin 1) (Fin 1) ℂ := (1 / 2 : ℂ) • (U + Uᴴ)
  have hH_eq : H = Matrix.diagonal (fun _ : Fin 1 ↦ (z.re : ℂ)) := Matrix.ext fun i j ↦ by
    fin_cases i; fin_cases j; simp only [H, U, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, smul_eq_mul, Complex.star_def,
          Complex.add_conj]
    push_cast; ring
  have hH_herm : Hᴴ = H := by simp [hH_eq, Matrix.diagonal_conjTranspose]
  have hH_norm : ‖H‖ ≤ 1 := by
    rw [hH_eq, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ by
      simpa [Complex.norm_real] using (Complex.abs_re_le_norm z).trans_eq hz
  have htri :=
      (sub_add_cancel (chebyshevPolyApprox H D s) (NormedSpace.exp ((-Complex.I * (s : ℂ)) • H))) ▸
    norm_add_le (chebyshevPolyApprox H D s - NormedSpace.exp ((-Complex.I * (s : ℂ)) • H))
        (NormedSpace.exp ((-Complex.I * (s : ℂ)) • H))
  rw [show ‖NormedSpace.exp ((-Complex.I * (s : ℂ)) • H)‖ = 1 by
    rw [← Matrix.one_mul (NormedSpace.exp _), jacobi_ja_norm_mul_exp_neg_I hH_herm,
        norm_one]] at htri
  have hentry : ‖chebyshevPolyApprox H D s 0 0‖ ≤ ‖chebyshevPolyApprox H D s‖ := by
    conv_rhs =>
        rw [show chebyshevPolyApprox H D s = Matrix.diagonal (fun _ : Fin 1 ↦
        chebyshevPolyApprox H D s 0 0) from
      Matrix.ext fun i j ↦ by fin_cases i; fin_cases j; rfl, Matrix.l2_opNorm_diagonal]
    exact norm_le_pi_norm (fun _ : Fin 1 ↦ chebyshevPolyApprox H D s 0 0) 0
  have hp (Q : ℂ[X]) : aeval U Q 0 0 = Q.eval z :=
      Polynomial.induction_on' Q (fun _ _ ihp ihq ↦ by simp [ihp, ihq])
    fun _ _ ↦ by simp [U, Algebra.algebraMap_eq_smul_one, Matrix.diagonal_pow]
  rw [← show ‖((Uᴴ) ^ D * aeval U (jacobiAngerLaurentPoly D s)) 0 0‖ =
      ‖(jacobiAngerLaurentPoly D s).eval z‖ by
    simp [Matrix.mul_apply, U, Matrix.diagonal_conjTranspose, Matrix.diagonal_pow, 
        hp, hz],
    mul_star_pow_aeval_jacobiAngerLaurentPoly D s hU]
  linarith [hentry, htri, opNorm_chebyshevPolyApprox_sub_exp_le_of_norm_le_one hH_herm hH_norm D hs]
noncomputable def scaledPoly (ε δ : ℝ) (P₀ : ℂ[X]) : ℂ[X] := C ((1 / (1 + ε + δ) : ℝ) : ℂ) * P₀
theorem natDegree_scaledPoly_le (ε δ : ℝ) (P₀ : ℂ[X]) : (scaledPoly ε δ P₀).natDegree ≤
    P₀.natDegree := natDegree_C_mul_le _ _
theorem norm_eval_scaledPoly_lt_one {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) {P₀ : ℂ[X]}
    (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1 + ε) :
    ∀ z : ℂ, ‖z‖ = 1 → ‖(scaledPoly ε δ P₀).eval z‖ < 1 := fun z hz ↦ by
  have hden : 0 < 1 + ε + δ := by linarith
  unfold scaledPoly
  rw [eval_mul, eval_C, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg zero_le_one hden.le)]
  refine (mul_le_mul_of_nonneg_left (hbound z hz) (div_nonneg zero_le_one hden.le)).trans_lt ?_
  rw [show 1 / (1 + ε + δ) * (1 + ε) = (1 + ε) / (1 + ε + δ) by ring]
  exact (div_lt_one hden).mpr (by linarith)
theorem norm_scaled_approx_sub_target_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {S V_target : X} {ε δ ε_poly : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hV : ‖V_target‖ ≤ 1) (hS : ‖S - V_target‖ ≤ ε_poly) :
    ‖((1 / (1 + ε + δ) : ℝ) : ℂ) • S - V_target‖ ≤ ε_poly + ε + δ := by
  have hden : 0 < 1 + ε + δ := by linarith
  have hc1 : 1 / (1 + ε + δ) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have h1mc : 1 - 1 / (1 + ε + δ) ≤ ε + δ := by
    rw [one_sub_div hden.ne', show 1 + ε + δ - 1 = ε + δ by ring]
    exact div_le_self (by linarith) (by linarith)
  rw [show ((1 / (1 + ε + δ) : ℝ) : ℂ) • S - V_target =
      ((1 / (1 + ε + δ) : ℝ) : ℂ) • (S - V_target) - ((1 - 1 / (1 + ε + δ) : ℝ) : ℂ) • V_target by
    push_cast
    rw [smul_sub, sub_smul, one_smul]
    abel]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg zero_le_one hden.le), Real.norm_of_nonneg (sub_nonneg.mpr hc1)]
  linarith [mul_le_mul_of_nonneg_right hc1 (norm_nonneg (S - V_target)),
    mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr hc1)]
end QuantumComputation.Specs.PhotochemistrySolution.GQSP
end

noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
section
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
noncomputable abbrev sqrtTwoMid : ℝ := 1414213562373095048 / 10 ^ 18

noncomputable abbrev sqrtTwoRad : ℝ := 1 / 10 ^ 18

theorem abs_sqrt_two_sub_le : |Real.sqrt 2 - sqrtTwoMid| ≤ sqrtTwoRad := by
  unfold sqrtTwoMid sqrtTwoRad
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_comm]
  exact ⟨Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩, Real.le_sqrt_of_sq_le (by norm_num)⟩

theorem basisBits_one_zero : basisBits 1 0 0 = 0 := by decide

theorem two_pi_div_two_pow_le_pi {j : ℕ} (hj : 1 ≤ j) : 2 * Real.pi / (2 : ℝ) ^ j ≤ Real.pi := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj, Real.pi_pos]

theorem cos_two_pi_div_two_pow_one_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 1) - (-1)| ≤ 0 := by
  rw [show 2 * Real.pi / (2 : ℝ) ^ 1 = Real.pi by ring, Real.cos_pi, sub_self, abs_zero]

theorem cos_two_pi_div_two_pow_three_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 3) - sqrtTwoMid / 2| ≤ sqrtTwoRad / 2 := by
  rw [show 2 * Real.pi / (2 : ℝ) ^ 3 = Real.pi / 4 by ring, Real.cos_pi_div_four, ← sub_div,
      abs_div]
  simpa using div_le_div_of_nonneg_right abs_sqrt_two_sub_le zero_le_two

theorem sin_two_pi_div_two_pow_three_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 3) - sqrtTwoMid / 2| ≤ sqrtTwoRad / 2 := by
  rw [show 2 * Real.pi / (2 : ℝ) ^ 3 = Real.pi / 4 by ring, Real.sin_pi_div_four, ← sub_div,
      abs_div]
  simpa using div_le_div_of_nonneg_right abs_sqrt_two_sub_le zero_le_two

noncomputable abbrev sinMid5 : ℝ := 195090322016 / 10 ^ 12

def concretePhaseState2 : Circuit 1 := Circuit.sequence [ .H 0, .S 0, .Z 0 ]
def concretePhaseState5 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .H 0, .S 0, .X 0, .X 0, .H 0, .Z 0, .S 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .Z 0 ]
def concretePhaseState6 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0,
    .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .H 0,
    .S 0, .H 0, .Z 0, .Z 0, .Z 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .Z 0, .H 0, .Z 0, .S 0 ]
theorem sum_basisBits_mul_two_pow (q : ℕ) (j : Fin (2 ^ q)) : ∑ i : Fin q, (basisBits q j i).val *
    2 ^ i.val = j.val := by
  refine Eq.trans (rfl : _ = ∑ i, (finFunctionFinEquiv.symm j i).val * 2 ^ i.val) ?_
  simpa only [finFunctionFinEquiv_apply] using congrArg Fin.val
      (finFunctionFinEquiv.apply_symm_apply j)
theorem sum_basisBits_div_two_pow (m : ℕ) (y : Fin (2 ^ m)) : ∑ r : Fin m,
    ((basisBits m y r).val : ℝ) / (2 ^ (m - r.val) : ℝ) = (y.val : ℝ) / (2 ^ m : ℝ) := by
  simp_rw [show ∀ r : Fin m, ((basisBits m y r).val : ℝ) / (2 ^ (m - r.val) : ℝ) =
      (((basisBits m y r).val * 2 ^ r.val : ℕ) : ℝ) / (2 ^ m : ℝ) from fun r ↦ by
    rw [show (2 : ℝ) ^ m = (2 : ℝ) ^ (m - r.val) * (2 : ℝ) ^ r.val by
      rw [← pow_add, Nat.sub_add_cancel r.isLt.le], Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      mul_div_mul_right _ _ (by positivity)], ← Finset.sum_div, ← Nat.cast_sum,
          sum_basisBits_mul_two_pow]
open scoped Fin.CommRing
theorem sum_fin_two_pow_one {α : Type*} [AddCommMonoid α] (f : Fin (2 ^ 1) → α) :
    (∑ i : Fin (2 ^ 1), f i) = f 0 + f 1 := by
  change (∑ i : Fin 2, f i) = f 0 + f 1; exact Fin.sum_univ_two f
theorem sum_zmod_two_local {α : Type*} [AddCommMonoid α] (f : ZMod 2 → α) : (∑ b : ZMod 2, f b) =
    f 0 + f 1 := Fin.sum_univ_two f
theorem sequence_drop_ofFn_step_local {n m : ℕ} (c : Fin m → Circuit n) {r : ℕ} (hr : r < m) :
    Circuit.sequence ((List.ofFn c).drop r) =
      c ⟨r, hr⟩ ;;ᶜ Circuit.sequence ((List.ofFn c).drop (r + 1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hr), List.getElem_ofFn, Circuit.sequence_cons]
end
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec

section
namespace QuantumComputation.Specs.PhotochemistrySolution
open scoped Matrix.Norms.L2Operator
open Operator Matrix WithLp NormedSpace
section NormsAndTelescoping
variable {I : Type*} [Fintype I] [DecidableEq I]
@[simp] theorem norm_unitary [Nonempty I] (U : 𝐔[I]) : ‖U.1‖ = 1 := by
  nlinarith [norm_nonneg U.1, show ‖U.1‖ * ‖U.1‖ = 1 by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose, U.2.1, norm_one]]
theorem norm_unitary_le_one (U : 𝐔[I]) : ‖U.1‖ ≤ 1 := by
  exact (isEmpty_or_nonempty I).elim (fun _ ↦ by simp [Subsingleton.elim U.1 0])
    fun _ ↦ (norm_unitary U).le
@[simp] theorem norm_unitary_mul (U : 𝐔[I]) (A : Matrix I I ℂ) : ‖U.1 * A‖ = ‖A‖ := by
  nlinarith [norm_nonneg (U.1 * A), norm_nonneg A, show ‖U.1 * A‖ * ‖U.1 * A‖ = ‖A‖ * ‖A‖ by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.conjTranspose_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc Aᴴ U.1ᴴ U.1, ← Matrix.star_eq_conjTranspose U.1, U.2.1, Matrix.mul_one,
      Matrix.l2_opNorm_conjTranspose_mul_self]]
@[simp] theorem norm_mul_unitary (A : Matrix I I ℂ) (U : 𝐔[I]) : ‖A * U.1‖ = ‖A‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose (A * U.1), Matrix.conjTranspose_mul,
      ← Matrix.star_eq_conjTranspose]
  exact (norm_unitary_mul (star U) Aᴴ).trans (Matrix.l2_opNorm_conjTranspose A)
end NormsAndTelescoping
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem exp_mul_I_mem_unitary {H : Matrix I I ℂ} (hH : Hᴴ = H)
    (c : ℝ) : NormedSpace.exp ((Complex.I * (c : ℂ)) • H) ∈ 𝐔[I] := by
  let +nondep : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℂ (Matrix I I ℂ)
  have hskew : (Complex.I * (c : ℂ)) • H ∈ skewAdjoint (Matrix I I ℂ) := by
    rw [skewAdjoint.mem_iff, star_smul, Matrix.star_eq_conjTranspose, hH, star_mul',
        Complex.star_def, Complex.conj_ofReal,
        Complex.conj_I]; ext i j; simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]; ring
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskew
noncomputable def expUnitaryOfHermitian {H : Matrix I I ℂ} (hH : Hᴴ = H) (c : ℝ) : 𝐔[I] :=
    ⟨NormedSpace.exp ((Complex.I * (c : ℂ)) • H), exp_mul_I_mem_unitary hH c⟩
theorem exp_neg_mul_I_mem_unitary {H : Matrix I I ℂ} (hH : Hᴴ = H)
    (c : ℝ) : NormedSpace.exp ((-Complex.I * (c : ℂ)) • H) ∈ 𝐔[I] := by
  simpa [neg_mul, mul_neg] using exp_mul_I_mem_unitary hH (-c)
noncomputable def expNegUnitaryOfHermitian {H : Matrix I I ℂ} (hH : Hᴴ = H) (c : ℝ) : 𝐔[I] :=
    ⟨NormedSpace.exp ((-Complex.I * (c : ℂ)) • H), exp_neg_mul_I_mem_unitary hH c⟩
theorem norm_exp_mul_I_mul {H : Matrix I I ℂ} (hH : Hᴴ = H) (c : ℝ) (M : Matrix I I ℂ) :
    ‖NormedSpace.exp ((Complex.I * (c : ℂ)) • H) * M‖ = ‖M‖ :=
    norm_unitary_mul (expUnitaryOfHermitian hH c) M
theorem norm_exp_neg_mul_I_mul {H : Matrix I I ℂ} (hH : Hᴴ = H) (c : ℝ) (M : Matrix I I ℂ) :
    ‖NormedSpace.exp ((-Complex.I * (c : ℂ)) • H) * M‖ = ‖M‖ :=
    norm_unitary_mul (expNegUnitaryOfHermitian hH c) M
theorem norm_mul_exp_neg_mul_I {H : Matrix I I ℂ} (hH : Hᴴ = H) (c : ℝ) (M : Matrix I I ℂ) : ‖M *
    NormedSpace.exp ((-Complex.I * (c : ℂ)) • H)‖ = ‖M‖ :=
    norm_mul_unitary M (expNegUnitaryOfHermitian hH c)
theorem exp_neg_mul_I_mul_exp_mul_I (H : Matrix I I ℂ)
    (c : ℝ) : NormedSpace.exp ((-Complex.I * (c : ℂ)) • H) *
    NormedSpace.exp ((Complex.I * (c : ℂ)) • H) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl H).smul_left _).smul_right _), ← add_smul,
    show -Complex.I * (c : ℂ) + Complex.I * (c : ℂ) = 0 by ring, zero_smul, NormedSpace.exp_zero]
theorem hasDerivAt_exp_smul_right (z : ℂ) (M : Matrix I I ℂ)
    (s : ℝ) : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp ((z * (u : ℂ)) • M))
    (NormedSpace.exp ((z * (s : ℂ)) • M) * (z • M)) s := by
  simpa only [show ∀ u : ℝ, (u : ℝ) • (z • M) = (z * (u : ℂ)) • M from fun _ ↦
    Matrix.ext fun _ _ ↦
        by simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]; ring] using
    hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := Matrix I I ℂ) (z • M) s
theorem hasDerivAt_exp_smul_left (z : ℂ) (M : Matrix I I ℂ)
    (s : ℝ) : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp ((z * (u : ℂ)) • M))
    ((z • M) * NormedSpace.exp ((z * (s : ℂ)) • M)) s := by
  simpa only [show ∀ u : ℝ, (u : ℝ) • (z • M) = (z * (u : ℂ)) • M from fun _ ↦
    Matrix.ext fun _ _ ↦
        by simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]; ring] using
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := Matrix I I ℂ) (z • M) s
theorem norm_le_of_hasDerivAt_norm_le {f f' : ℝ → Matrix I I ℂ} {B B' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hB : ∀ s, HasDerivAt B (B' s) s) (hf0 : f 0 = 0)
    (hB0 : B 0 = 0) (hbound : ∀ s, 0 ≤ s → ‖f' s‖ ≤ B' s) {τ : ℝ} (hτ : 0 ≤ τ) : ‖f τ‖ ≤ B τ := by
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary (fun x _ ↦
      (hf x).continuousAt.continuousWithinAt) (fun x _ ↦
      (hf x).hasDerivWithinAt) (by rw [hf0, hB0, norm_zero]) hB (fun x hx ↦ hbound x hx.1)
          (Set.right_mem_Icc.mpr hτ)
end QuantumComputation.Specs.PhotochemistrySolution
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchyA
/-- Symbolic `4 ^ (D + 1)` domination avoiding huge exponent reduction (`4 ^ 60 ≥ 10 ^ 20`). -/
theorem exp_div_four_pow_le {D E : ℕ} {x : ℝ} (hx : x ≤ E) (hEN : E + 60 ≤ D + 1) : Real.exp x /
    (4 : ℝ) ^ (D + 1) ≤ (1 : ℝ) / (10 ^ 20 : ℝ) := by
  have hexp : Real.exp x ≤ (4 : ℝ) ^ E := (Real.exp_le_exp.mpr hx).trans <|
    (mul_one (E : ℝ) ▸ Real.exp_nat_mul 1 E).trans_le (pow_le_pow_left₀ (Real.exp_pos 1).le
        (by linarith [Real.exp_one_lt_d9]) E)
  have hpow : (4 : ℝ) ^ E * (10 ^ 20 : ℝ) ≤ (4 : ℝ) ^ (D + 1) :=
    (mul_le_mul_of_nonneg_left (by norm_num) (by positivity)).trans
      ((pow_add (4 : ℝ) E 60).symm.trans_le (pow_le_pow_right₀ (by norm_num) hEN))
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hpow
lemma sin_le_self_nonneg_cauchyA {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x := by
  have hd (t : ℝ) : HasDerivAt (fun u ↦ u - Real.sin u) (1 - Real.cos t) t :=
    (hasDerivAt_id t).sub (Real.hasDerivAt_sin t)
  linarith [Real.sin_zero, monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) (fun t _ ↦ (hd t).hasDerivWithinAt)
    (fun t _ ↦ sub_nonneg.mpr (Real.cos_le_one t)) (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx]
lemma cos_ge_quad_nonneg_cauchyA {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 ≤ Real.cos x := by
  have hd (t : ℝ) : HasDerivAt (fun u ↦ Real.cos u + u ^ 2 / 2) (-Real.sin t + t) t :=
    (Real.hasDerivAt_cos t).add (((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring))
  linarith [Real.cos_zero, monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) (fun t _ ↦ (hd t).hasDerivWithinAt)
    (fun t ht ↦ by linarith [sin_le_self_nonneg_cauchyA (interior_subset ht)])
    (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx]
lemma sin_ge_cubic_nonneg_cauchyA {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hd (t : ℝ) : HasDerivAt (fun u ↦ Real.sin u - (u - u ^ 3 / 6))
      (Real.cos t - (1 - t ^ 2 / 2)) t :=
    (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).sub (((hasDerivAt_pow 3 t).div_const
        6).congr_deriv (by ring)))
  linarith [Real.sin_zero, monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) (fun t _ ↦ (hd t).hasDerivWithinAt)
    (fun t ht ↦ by linarith [cos_ge_quad_nonneg_cauchyA (interior_subset ht)])
    (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx]
lemma cos_le_quartic_cauchyA (u : ℝ) : Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
  have hnn (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    have hd (t : ℝ) : HasDerivAt (fun v ↦ (v ^ 4 / 24 - v ^ 2 / 2) - Real.cos v)
        ((t ^ 3 / 6 - t) + Real.sin t) t :=
      ((((hasDerivAt_pow 4 t).div_const 24).sub ((hasDerivAt_pow 2 t).div_const 2)).sub
          (Real.hasDerivAt_cos t)).congr_deriv (by ring)
    linarith [Real.cos_zero, monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) (fun t _ ↦ (hd t).hasDerivWithinAt)
      (fun t ht ↦ by linarith [sin_ge_cubic_nonneg_cauchyA (interior_subset ht)])
      (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx]
  simpa [Real.cos_abs, Even.pow_abs (by decide : Even 4)] using hnn |u| (abs_nonneg u)
lemma sin_le_zero_of_mem_Icc_pi {φ : ℝ} (h1 : Real.pi ≤ φ) (h2 : φ ≤ 2 * Real.pi) : Real.sin φ ≤
    0 := by
  have hsin2 {v : ℝ} (hv0 : 0 ≤ v) (hv2 : v ≤ 2) : 0 ≤ Real.sin v := by
    nlinarith [sin_ge_cubic_nonneg_cauchyA hv0, mul_nonneg hv0 (show 0 ≤ 6 - v ^ 2 by nlinarith)]
  rw [show φ = (φ - Real.pi) + Real.pi by ring, Real.sin_add, Real.cos_pi, Real.sin_pi]
  linarith [if hhalf : φ - Real.pi ≤ Real.pi / 2 then hsin2 (by linarith)
      (by linarith [Real.pi_lt_d4])
    else Real.sin_pi_sub (φ - Real.pi) ▸ hsin2 (by linarith) (by linarith [Real.pi_lt_d4])]
lemma sin_upper_shell_le {j A : ℕ} (hj : j < 40000001) (hAle : A ≤ 20000000)
    (hA : j ≤ 20000000 - A ∨ 20000000 + A ≤ j) :
    let u0 : ℝ := (31415926 : ℝ) * (max (0 : ℝ) (4 * (A : ℝ) - 1)) / (20000000 * 80000001)
    Real.sin (2 * Real.pi * (j : ℝ) / 80000001) ≤ 1 - (u0 ^ 2 / 2 - u0 ^ 4 / 24) := by
  intro u0
  let φ : ℝ := 2 * Real.pi * (j : ℝ) / 80000001
  let u : ℝ := |Real.pi / 2 - φ|
  have hφpi : φ ≤ Real.pi := (div_le_iff₀ (by norm_num)).mpr
    (by nlinarith [Real.pi_pos, (show (j : ℝ) ≤ 40000000 by exact_mod_cast Nat.lt_succ_iff.mp hj)])
  have hu0_nn : 0 ≤ u0 := by positivity
  have hu2 : u ≤ 2 := abs_le.mpr ⟨by linarith [Real.pi_lt_d4],
    by linarith [Real.pi_lt_d4, show 0 ≤ φ by positivity]⟩
  have hgapR : max (0 : ℝ) (4 * (A : ℝ) - 1) ≤ |(80000001 : ℝ) - 4 * (j : ℝ)| :=
      max_le (abs_nonneg _)
    (by exact_mod_cast (by rcases abs_cases ((80000001 : ℤ) - 4 * (j : ℤ)) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      rw [h] <;> omega : 4 * (A : ℤ) - 1 ≤ |(80000001 : ℤ) - 4 * (j : ℤ)|))
  have hu_ge : u0 ≤ u := by
    dsimp only [u, u0]
    rw [show Real.pi / 2 - φ = Real.pi * ((80000001 : ℝ) - 4 * (j : ℝ)) / (2 * 80000001) by
      dsimp only [φ]
      field_simp; ring, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      show |(2 * 80000001 : ℝ)| = 2 * 80000001 by norm_num]
    linarith [mul_le_mul (show (31415926 / 10000000 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_d20])
      hgapR (by positivity) Real.pi_pos.le]
  linarith [show Real.sin φ = Real.cos u by
      rw [Real.cos_abs, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring,
    cos_le_quartic_cauchyA u,
    mul_nonneg (by nlinarith : 0 ≤ (u - u0) * (u + u0)) (by nlinarith : 0 ≤ 12 - u ^ 2 - u0 ^ 2),
    show (u ^ 2 / 2 - u ^ 4 / 24) - (u0 ^ 2 / 2 - u0 ^ 4 / 24) =
      (u - u0) * (u + u0) * (12 - u ^ 2 - u0 ^ 2) / 24 by ring]
lemma card_filter_ge_nat (M K : ℕ) (_hK : K ≤ M) : ((Finset.range M).filter (fun j : ℕ ↦ K ≤
    j)).card ≤ M - K := by
  refine (Finset.card_le_card fun j hj ↦ Finset.mem_Ico.mpr ?_).trans (Nat.card_Ico K M).le
  exact ⟨(Finset.mem_filter.mp hj).2, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩
lemma sum_ite_le_mul_card {M : ℕ} (p : ℕ → Prop) [DecidablePred p] {B : ℝ} (hB : 0 ≤ B) {C : ℕ}
    (hcard : ((Finset.range M).filter p).card ≤ C) : (∑ j ∈ Finset.range M, if p j then B else 0) ≤
    (C : ℝ) * B := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchyA

namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchyB
open PhotochemistrySolution.TightWalkCauchyA
/-- Stationary-phase shell cosine drop at integer offset `A` from `j = 20,000,000`. -/
def shellDrop : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
    let u0 : ℝ := (31415926 : ℝ) * (4 * ((k + 1 : ℕ) : ℝ) - 1) / (20000000 * 80000001)
    u0 ^ 2 / 2 - u0 ^ 4 / 24
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchyB
end

section
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
open scoped Circuit.Notation ComplexOrder
section
open Operator Matrix Qubit WithLp
theorem pgL2Norm_nonneg {I : Type*} [Fintype I] (v : I → ℂ) : 0 ≤ pgL2Norm v := norm_nonneg _
open scoped Fin.CommRing
noncomputable def phaseGradTargetQubitState (j : ℕ) : Fin (2 ^ 1) → ℂ := fun i ↦
    QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j) (basisBits 1 i 0)
theorem basisBits_one_val_eq (b : ZMod 2) : basisBits 1 ⟨b.val, b.val_lt⟩ 0 = b := by
  rcases zmodTwo_eq_zero_or_one b with rfl | rfl <;> decide

theorem stateToFactor_phaseGradTargetQubitState (j : ℕ) :
    stateToFactor (phaseGradTargetQubitState j) = QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j) := by
  funext b; unfold stateToFactor phaseGradTargetQubitState; rw [basisBits_one_val_eq]
theorem singleton_onRegister_evolve_prodState_local {m : ℕ} (c : Circuit 1) (r : Fin m)
    (v : Fin m → (ZMod 2 → ℂ)) (hvr : v r = basisState 0) :
    ((c.onRegister (QRegister.singleton r)).eval.1).mulVec (QFT.prodState m v) =
    QFT.prodState m (Function.update v r (stateToFactor (c.eval.1 *ᵥ basisState 0))) := by
  rw [Circuit.eval_onRegister, QRegister.embedUnitary_val]; funext j;
  rw [(QRegister.singleton r).embedMatrix_mulVec_apply, sum_fin_two_pow_one]
  have hsplit : (QRegister.singleton r).basisSplitEquiv.symm
      (0, ((QRegister.singleton r).basisSplitEquiv j).2) =
      (QRegister.singleton r).replaceIndex j 0 := rfl
  have hsplit1 : (QRegister.singleton r).basisSplitEquiv.symm
      (1, ((QRegister.singleton r).basisSplitEquiv j).2) =
      (QRegister.singleton r).replaceIndex j 1 := rfl
  rw [hsplit, hsplit1]
  have hprod1 : QFT.prodState m v ((QRegister.singleton r).replaceIndex j 1) = 0 := by
    unfold QFT.prodState; apply Finset.prod_eq_zero (Finset.mem_univ r)
    have hbit1 : basisBits m ((QRegister.singleton r).replaceIndex j 1) r = 1 := by
      change basisBits m ((QRegister.singleton r).replaceIndex j 1) (QRegister.singleton r 0) = 1;
      rw [(QRegExt.basisBits_replaceIdx_apply (QRegister.singleton r))]; decide
    rw [hbit1, hvr, basisState, Pi.single_apply]; simp
  rw [hprod1, mul_zero, add_zero]
  have hprod0 : QFT.prodState m v ((QRegister.singleton r).replaceIndex j 0) =
      ∏ k ∈ Finset.univ.erase r, v k (basisBits m j k) := by
    unfold QFT.prodState; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    have hbit0 : basisBits m ((QRegister.singleton r).replaceIndex j 0) r = 0 := by
      change basisBits m ((QRegister.singleton r).replaceIndex j 0) (QRegister.singleton r 0) = 0;
      rw [(QRegExt.basisBits_replaceIdx_apply (QRegister.singleton r))]; decide
    rw [hbit0, hvr, basisState, Pi.single_apply, ite_eq_left rfl, one_mul]
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    have hkr : k ∉ Set.range (QRegister.singleton r).wires := by
      intro ⟨idx, hidx⟩
      fin_cases idx
      exact (Finset.mem_erase.mp hk).1 hidx.symm
    rw [(QRegExt.basisBits_replaceIdx_of_not_mem (QRegister.singleton r)) j 0 k hkr]
  rw [hprod0]; unfold QFT.prodState;
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), Function.update_self]; congr 1
  · have hentry : c.eval.1 ((QRegister.singleton r).extractIndex j) 0 =
        stateToFactor (c.eval.1 *ᵥ basisState 0) (basisBits m j r) := by
      unfold stateToFactor
      have hext : (QRegister.singleton r).extractIndex j = ⟨(basisBits m j r).val,
          (basisBits m j r).val_lt⟩ := by
        apply (basisBitsEquiv 1).injective; funext idx
        fin_cases idx
        change basisBits 1 ((QRegister.singleton r).extractIndex j) 0 = _;
        rw [(QRegExt.basisBits_extractIdx (QRegister.singleton r)) j 0];
        change basisBits m j r = basisBits 1 ⟨(basisBits m j r).val, (basisBits m j r).val_lt⟩ 0;
        rw [basisBits_one_val_eq]
      rw [hext]; unfold Matrix.mulVec dotProduct basisState; rw [sum_fin_two_pow_one]; simp
    exact hentry
  · refine Finset.prod_congr rfl fun k hk ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
end

section
open Operator Matrix Qubit WithLp
theorem pgL2Norm_sq {I : Type*} [Fintype I] (v : I → ℂ) : pgL2Norm v ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq (toLp 2 v)
theorem pgL2Norm_mulVec_le {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (v : I → ℂ) : pgL2Norm (A *ᵥ v) ≤ pgOpNorm A * pgL2Norm v :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (toLp 2 v)

theorem sin_half_abs_sub_le {θ C₀ εC s₀ εs : ℝ}
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi) (hs_lo : 0 ≤ s₀ - εs) (hεs : 0 ≤ εs)
    (hC : |Real.cos θ - C₀| ≤ εC)
    (h_lo : 2 * (s₀ - εs) ^ 2 ≤ 1 - (C₀ + εC))
    (h_hi : 1 - (C₀ - εC) ≤ 2 * (s₀ + εs) ^ 2) :
    |Real.sin (θ / 2) - s₀| ≤ εs := by
  have hsin_nonneg : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  have htwo : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (θ / 2);
    have h2 := Real.sin_sq (θ / 2); ring_nf at h1 h2 ⊢; linarith
  rw [abs_le] at hC ⊢
  have h_hi_pos : 0 ≤ s₀ + εs := by linarith
  constructor <;> nlinarith

theorem sin_two_pi_div_two_pow_succ_approx {j : ℕ} (hj : 1 ≤ j) {C₀ εC s₀ εs : ℝ}
    (hs_lo : 0 ≤ s₀ - εs) (hεs : 0 ≤ εs)
    (hC : |Real.cos (2 * Real.pi / (2 : ℝ) ^ j) - C₀| ≤ εC)
    (h_lo : 2 * (s₀ - εs) ^ 2 ≤ 1 - (C₀ + εC))
    (h_hi : 1 - (C₀ - εC) ≤ 2 * (s₀ + εs) ^ 2) :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ (j + 1)) - s₀| ≤ εs := by
  have hdiv : 2 * Real.pi / (2 : ℝ) ^ (j + 1) = (2 * Real.pi / (2 : ℝ) ^ j) / 2 := by
    rw [pow_succ]; ring
  rw [hdiv];
  exact sin_half_abs_sub_le (two_pi_div_two_pow_nonneg j)
      (two_pi_div_two_pow_le_pi hj) hs_lo hεs hC h_lo h_hi
end

section
open Operator Matrix Qubit WithLp
theorem pgOpNorm_nonneg {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) : 0 ≤
    pgOpNorm A := norm_nonneg _
theorem cos_half_abs_sub_le {θ C₀ εC c₀ εc : ℝ}
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi) (hc_lo : 0 ≤ c₀ - εc) (hεc : 0 ≤ εc)
    (hC : |Real.cos θ - C₀| ≤ εC)
    (h_lo : 2 * (c₀ - εc) ^ 2 - 1 ≤ C₀ - εC)
    (h_hi : C₀ + εC ≤ 2 * (c₀ + εc) ^ 2 - 1) :
    |Real.cos (θ / 2) - c₀| ≤ εc := by
  have hcos_nonneg : 0 ≤ Real.cos (θ / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  have htwo : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2); ring_nf at h ⊢; exact h
  rw [abs_le] at hC ⊢
  have h_hi_pos : 0 ≤ c₀ + εc := by linarith
  constructor <;> nlinarith

theorem cos_two_pi_div_two_pow_succ_approx {j : ℕ} (hj : 1 ≤ j) {C₀ εC c₀ εc : ℝ}
    (hc_lo : 0 ≤ c₀ - εc) (hεc : 0 ≤ εc)
    (hC : |Real.cos (2 * Real.pi / (2 : ℝ) ^ j) - C₀| ≤ εC)
    (h_lo : 2 * (c₀ - εc) ^ 2 - 1 ≤ C₀ - εC)
    (h_hi : C₀ + εC ≤ 2 * (c₀ + εc) ^ 2 - 1) :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ (j + 1)) - c₀| ≤ εc := by
  have hdiv : 2 * Real.pi / (2 : ℝ) ^ (j + 1) = (2 * Real.pi / (2 : ℝ) ^ j) / 2 := by
    rw [pow_succ]; ring
  rw [hdiv];
  exact cos_half_abs_sub_le (two_pi_div_two_pow_nonneg j)
      (two_pi_div_two_pow_le_pi hj) hc_lo hεc hC h_lo h_hi
end
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end

noncomputable section
open Matrix
namespace QuantumComputation.Specs.PhotochemistrySolution.GQSP
open Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev qubitCommutant (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ) :
    Subalgebra ℂ (Matrix ι ι ℂ) := Subalgebra.centralizer ℂ (Set.range e)
noncomputable def blockOp (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ) (M : Matrix (Fin 2)
    (Fin 2) (Matrix ι ι ℂ)) : Matrix ι ι ℂ := ∑ i, ∑ j, e (single i j 1) * M i j
variable (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ)
theorem comm_of_mem_qubitCommutant {X : Matrix ι ι ℂ} (hX : X ∈ qubitCommutant e)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : e M * X = X * e M :=
  (Subalgebra.mem_centralizer_iff ℂ).mp hX _ ⟨M, rfl⟩
theorem e_single_mul_single (i j k l : Fin 2) : e (single i j 1) * e (single k l 1) = if j =
    k then e (single i l 1) else 0 := by
  rw [← map_mul]
  exact if h : j = k then h ▸ by simp else by simp [h, single_mul_single_of_ne _ _ _ _ h]
theorem blockOp_mul {M N : Matrix (Fin 2) (Fin 2) (Matrix ι ι ℂ)}
    (hM : ∀ i j, M i j ∈ qubitCommutant e) : blockOp e (M * N) = blockOp e M * blockOp e N := by
  have key : ∀ i j k l, e (single i j 1) * M i j * (e (single k l 1) * N k l) =
      (if j = k then e (single i l 1) else 0) * (M i j * N k l) := by
    intro i j k l;
    rw [← e_single_mul_single, Matrix.mul_assoc, ← Matrix.mul_assoc (M i j),
        ← comm_of_mem_qubitCommutant e (hM i j), Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [blockOp, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_add, Matrix.add_mul, key];
  simp only [Fin.isValue, ite_true, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero, ite_false,
      Matrix.zero_mul, add_zero, zero_add]
  abel
theorem blockOp_one : blockOp e 1 =
    1 := by have h : (1 : Matrix (Fin 2) (Fin 2) ℂ) = ∑ i, ∑ j, single i j ((1 : Matrix (Fin 2)
              (Fin 2) ℂ) i j) :=
              matrix_eq_sum_single _; simp only [blockOp, Fin.sum_univ_two, Matrix.one_apply,
              Fin.isValue] at h ⊢; simp only [Fin.isValue, ite_true, Fin.zero_eq_one_iff,
              OfNat.ofNat_ne_one, one_ne_zero, ite_false, Matrix.mul_one, Matrix.mul_zero, add_zero,
              zero_add, single_zero] at h ⊢; rw [← map_add, ← h, map_one]
theorem blockOp_map_algebraMap (R : Matrix (Fin 2) (Fin 2) ℂ) :
    blockOp e (R.map (algebraMap ℂ (Matrix ι ι ℂ))) = e R := by
  conv_rhs => rw [matrix_eq_sum_single R]
  simp [blockOp, Algebra.algebraMap_eq_smul_one, ← map_smul]
theorem blockOp_diag (X Y : Matrix ι ι ℂ) :
    blockOp e !![X, 0; 0, Y] = e (single 0 0 1) * X + e (single 1 1 1) * Y := by
  simp [blockOp, Fin.sum_univ_two]
theorem corner_blockOp {M : Matrix (Fin 2) (Fin 2) (Matrix ι ι ℂ)}
    (hM : ∀ i j, M i j ∈ qubitCommutant e) : e (single 0 0 1) * blockOp e M * e (single 0 0 1) =
    e (single 0 0 1) * M 0 0 := by
  have key : ∀ i j, e (single 0 0 1) * (e (single i j 1) * M i j) * e (single 0 0 1) =
      e (single 0 0 1) * e (single i j 1) * e (single 0 0 1) * M i j := by
    intro i j; rw [Matrix.mul_assoc, Matrix.mul_assoc, ← comm_of_mem_qubitCommutant e (hM i j)];
    simp only [Matrix.mul_assoc]
  simp only [blockOp, Fin.sum_univ_two, Matrix.mul_add, Matrix.add_mul, key];
  simp [e_single_mul_single]
theorem mul_entries_mem {M N : Matrix (Fin 2) (Fin 2) (Matrix ι ι ℂ)}
    (hM : ∀ i j, M i j ∈ qubitCommutant e) (hN : ∀ i j, N i j ∈ qubitCommutant e) :
    ∀ i j, (M * N) i j ∈ qubitCommutant e := fun i j ↦ by
  rw [Matrix.mul_apply]; exact Subalgebra.sum_mem _ fun k _ ↦ Subalgebra.mul_mem _ (hM i k) (hN k j)
theorem map_algebraMap_entries_mem (R : Matrix (Fin 2) (Fin 2) ℂ) : ∀ i j,
    R.map (algebraMap ℂ (Matrix ι ι ℂ)) i j ∈ qubitCommutant e := fun _ _ ↦
    Subalgebra.algebraMap_mem _ _
theorem mixedSignal_entries_mem {U : Matrix ι ι ℂ} (hU : U ∈ qubitCommutant e)
    (hU' : Uᴴ ∈ qubitCommutant e) (b : Bool) :
    ∀ i j, mixedSignal U b i j ∈ qubitCommutant e := fun i j ↦ by
  cases b <;> fin_cases i <;> fin_cases j <;> simp [mixedSignal, hU, hU']
theorem gqspMixedTail_entries_mem {U : Matrix ι ι ℂ} (hU : U ∈ qubitCommutant e)
    (hU' : Uᴴ ∈ qubitCommutant e) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ × Bool),
      ∀ i j, gqspMixedTail U Rs i j ∈ qubitCommutant e
  | [] => fun i j ↦ by
    rw [gqspMixedTail, Matrix.one_apply]
    exact if h : i = j then by simp [h] else by simp [h]
  | (R, b) :: Rs => mul_entries_mem e (mul_entries_mem e (map_algebraMap_entries_mem e R)
      (mixedSignal_entries_mem e hU hU' b)) (gqspMixedTail_entries_mem hU hU' Rs)
noncomputable def sigOp (U : Matrix ι ι ℂ) (b : Bool) : Matrix ι ι ℂ := blockOp e (mixedSignal U b)
noncomputable def gqspOp (U : Matrix ι ι ℂ) :
    List (Matrix (Fin 2) (Fin 2) ℂ × Bool) → Matrix ι ι ℂ
  | [] => 1
  | (R, b) :: Rs => e R * sigOp e U b * gqspOp U Rs
theorem blockOp_gqspMixedTail {U : Matrix ι ι ℂ} (hU : U ∈ qubitCommutant e)
    (hU' : Uᴴ ∈ qubitCommutant e) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ × Bool),
      blockOp e (gqspMixedTail U Rs) = gqspOp e U Rs
  | [] => blockOp_one e
  | (R, b) :: Rs => by
    rw [gqspMixedTail, blockOp_mul e (mul_entries_mem e (map_algebraMap_entries_mem e R)
        (mixedSignal_entries_mem e hU hU' b)), blockOp_mul e (map_algebraMap_entries_mem e R),
        blockOp_map_algebraMap, blockOp_gqspMixedTail hU hU' Rs]; rfl
theorem corner_gqspOp_zip {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (hUc : U ∈ qubitCommutant e) (hUc' : Uᴴ ∈ qubitCommutant e) {R₀ : Matrix (Fin 2) (Fin 2) ℂ}
    {Rs : List (Matrix (Fin 2) (Fin 2) ℂ)} {bs : List Bool} {P Q : ℂ[X]}
    (hR₀ : R₀ ∈ unitaryGroup (Fin 2) ℂ) (hRs : ∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ)
    (hlen : Rs.length = bs.length) (h : (gqspTail Rs * R₀.map C) *ᵥ ![1, 0] = ![P, Q]) :
    e (single 0 0 1) * (gqspOp e U (Rs.zip bs) * e R₀) * e (single 0 0 1) = e (single 0 0 1) *
    (Uᴴ ^ bs.count true * aeval U P) := by
  rw [← blockOp_map_algebraMap e R₀, ← blockOp_gqspMixedTail e hUc hUc',
    ← blockOp_mul e (gqspMixedTail_entries_mem e hUc hUc' _), corner_blockOp e
      (mul_entries_mem e (gqspMixedTail_entries_mem e hUc hUc' _)
          (map_algebraMap_entries_mem e R₀)),
    (gqsp_laurent_realisation_zip hU hR₀ hRs hlen h).2.1]
section Unitary
variable (he_star : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, (e M)ᴴ = e Mᴴ)
include he_star
theorem conjTranspose_mem_qubitCommutant {X : Matrix ι ι ℂ} (hX : X ∈ qubitCommutant e) :
    Xᴴ ∈ qubitCommutant e := by
  rw [Subalgebra.mem_centralizer_iff]; rintro _ ⟨M, rfl⟩;
  have h := congrArg Matrix.conjTranspose (comm_of_mem_qubitCommutant e hX Mᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, he_star,
      Matrix.conjTranspose_conjTranspose] at h; exact h.symm
theorem e_mem_unitary {R : Matrix (Fin 2) (Fin 2) ℂ} (hR : R ∈ unitaryGroup (Fin 2) ℂ) :
    e R ∈ unitary (Matrix ι ι ℂ) :=
  Unitary.mem_iff.mpr (by rw [star_eq_conjTranspose, he_star, ← map_mul, ← map_mul,
    show Rᴴ * R = 1 from Unitary.star_mul_self_of_mem hR, show R * Rᴴ =
        1 from Unitary.mul_star_self_of_mem hR, map_one]; exact ⟨rfl, rfl⟩)
theorem blockOp_conjTranspose {M : Matrix (Fin 2) (Fin 2) (Matrix ι ι ℂ)}
    (hM : ∀ i j, M i j ∈ qubitCommutant e) : (blockOp e M)ᴴ = blockOp e (star M) := by
  have key (i j : Fin 2) : (e (single i j 1) * M i j)ᴴ = e (single j i 1) * star (M i j) := by
    rw [Matrix.conjTranspose_mul, he_star, conjTranspose_single, star_one, ← star_eq_conjTranspose]
    exact (comm_of_mem_qubitCommutant e (conjTranspose_mem_qubitCommutant e he_star (hM i j))
        _).symm
  simp only [blockOp, Fin.sum_univ_two, Matrix.conjTranspose_add, key, Matrix.star_apply]; abel
theorem blockOp_mem_unitary {M : Matrix (Fin 2) (Fin 2) (Matrix ι ι ℂ)}
    (hM : ∀ i j, M i j ∈ qubitCommutant e) (hMu : M ∈ unitary (Matrix (Fin 2) (Fin 2)
    (Matrix ι ι ℂ))) : blockOp e M ∈ unitary (Matrix ι ι ℂ) :=
  Unitary.mem_iff.mpr (by
    rw [star_eq_conjTranspose, blockOp_conjTranspose e he_star hM,
      ← blockOp_mul e (show ∀ i j, (star M) i j ∈ qubitCommutant e from fun i j ↦
          conjTranspose_mem_qubitCommutant e he_star (hM j i)),
      ← blockOp_mul e hM, Unitary.star_mul_self_of_mem hMu, Unitary.mul_star_self_of_mem hMu,
          blockOp_one]; exact ⟨rfl, rfl⟩)
theorem sigOp_mem_unitary {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (hUc : U ∈ qubitCommutant e) (b : Bool) : sigOp e U b ∈ unitary (Matrix ι ι ℂ) :=
    blockOp_mem_unitary e he_star (mixedSignal_entries_mem e hUc (conjTranspose_mem_qubitCommutant e
    he_star hUc) b) (mixedSignal_mem_unitary hU b)
theorem gqspOp_mem_unitary {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (hUc : U ∈ qubitCommutant e) :
    ∀ {Rs : List (Matrix (Fin 2) (Fin 2) ℂ × Bool)}, (∀ R ∈ Rs, R.1 ∈ unitaryGroup (Fin 2) ℂ) →
      gqspOp e U Rs ∈ unitary (Matrix ι ι ℂ)
  | [], _ => one_mem _
  | (_R, b) :: _Rs, h => mul_mem
      (mul_mem (e_mem_unitary e he_star (h _ List.mem_cons_self))
          (sigOp_mem_unitary e he_star hU hUc b))
      (gqspOp_mem_unitary hU hUc fun R' hR' ↦ h R' (List.mem_cons_of_mem _ hR'))
end Unitary
theorem norm_exp_neg_mul_I_sub_le {I : Type*} [Fintype I] [DecidableEq I] {A B : Matrix I I ℂ}
    (hA : Aᴴ = A) (hB : Bᴴ = B) {s : ℝ}
    (hs : 0 ≤ s) : ‖NormedSpace.exp ((-Complex.I * (s : ℂ)) • A) - NormedSpace.exp ((-Complex.I *
    (s : ℂ)) • B)‖ ≤ s * ‖A - B‖ := by
  rw [show NormedSpace.exp ((-Complex.I * (s : ℂ)) • A) - NormedSpace.exp ((-Complex.I *
      (s : ℂ)) • B) =
      NormedSpace.exp ((-Complex.I * (s : ℂ)) • B) *
        (NormedSpace.exp ((Complex.I * (s : ℂ)) • B) * NormedSpace.exp ((-Complex.I *
            (s : ℂ)) • A) - 1) by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, exp_neg_mul_I_mul_exp_mul_I,
        Matrix.one_mul],
    norm_exp_neg_mul_I_mul hB]
  exact norm_le_of_hasDerivAt_norm_le (f' := fun u ↦ NormedSpace.exp ((Complex.I * (u : ℂ)) • B) *
      (Complex.I • (B - A)) * NormedSpace.exp ((-Complex.I * (u : ℂ)) • A))
    (fun u ↦
        (((hasDerivAt_exp_smul_right Complex.I B u).mul (hasDerivAt_exp_smul_left (-Complex.I) A
        u)).sub_const 1).congr_deriv
      (by simp only [Matrix.mul_assoc, smul_sub, Matrix.mul_sub, Matrix.sub_mul, neg_smul,
            Matrix.neg_mul, Matrix.mul_neg]; abel))
    (fun u ↦ ((hasDerivAt_id u).mul_const ‖A - B‖).congr_deriv (by ring))
        (by simp [NormedSpace.exp_zero]) (by simp)
    (fun u _ ↦
        by rw [norm_mul_exp_neg_mul_I hA, norm_exp_mul_I_mul hB, norm_smul, Complex.norm_I, one_mul,
             ← norm_neg, neg_sub]) hs
end QuantumComputation.Specs.PhotochemistrySolution.GQSP

namespace QuantumComputation.Specs.PhotochemistrySolution.OvBidir
open Polynomial ComplexConjugate PhotochemistrySolution.GQSP
def bidirLayers (R₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    List (Matrix (Fin 2) (Fin 2) ℂ) → List (Matrix (Fin 2) (Fin 2) ℂ × Bool)
  | [] => [(R₀, true)]
  | R :: Rs => (R, false) :: (1, true) :: bidirLayers R₀ Rs
theorem count_true_bidirLayers (R₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ),
      ((bidirLayers R₀ Rs).map Prod.snd).count true = Rs.length + 1
  | [] => rfl
  | _ :: Rs => by simp [bidirLayers, count_true_bidirLayers R₀ Rs]
theorem mem_bidirLayers_unitary {R₀ : Matrix (Fin 2) (Fin 2) ℂ}
    (hR₀ : R₀ ∈ unitaryGroup (Fin 2) ℂ) :
    ∀ {Rs : List (Matrix (Fin 2) (Fin 2) ℂ)}, (∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ) →
      ∀ t ∈ bidirLayers R₀ Rs, t.1 ∈ unitaryGroup (Fin 2) ℂ
  | [], _, _, ht => (List.mem_singleton.mp ht) ▸ hR₀
  | R :: _Rs, hRs, t, ht =>
        (List.mem_cons.mp ht).elim (fun e ↦ e ▸ hRs R List.mem_cons_self) fun ht ↦
      (List.mem_cons.mp ht).elim (fun e ↦ e ▸ one_mem _)
        (mem_bidirLayers_unitary hR₀ (fun R' hR' ↦ hRs R' (List.mem_cons_of_mem _ hR')) t)
theorem mem_cons_bidirLayers_unitary {R₀ : Matrix (Fin 2) (Fin 2) ℂ}
    {Rs : List (Matrix (Fin 2) (Fin 2) ℂ)} (hR₀ : R₀ ∈ unitaryGroup (Fin 2) ℂ)
    (hRs : ∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ) : ∀ t ∈ (hadamard2, false) :: bidirLayers R₀ Rs,
    t.1 ∈ unitaryGroup (Fin 2) ℂ := fun t ht ↦
  (List.mem_cons.mp ht).elim (fun h ↦ by subst h; exact hadamard2_mem)
      (mem_bidirLayers_unitary hR₀ hRs t)
theorem gqspTail_cons (R : Matrix (Fin 2) (Fin 2) ℂ) (Rs : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    gqspTail (R :: Rs) = R.map C * signal * gqspTail Rs := rfl
theorem map_expand_mul (A B : Matrix (Fin 2) (Fin 2) ℂ[X]) : (A * B).map (expand ℂ 2) =
    A.map (expand ℂ 2) * B.map (expand ℂ 2) :=
  Matrix.map_mul (f := (expand ℂ 2).toRingHom)
theorem map_C_map_expand (R : Matrix (Fin 2) (Fin 2) ℂ) : (R.map C).map (expand ℂ 2) = R.map C := by
  ext i j; simp
theorem signal_map_expand : (signal : Matrix (Fin 2) (Fin 2) ℂ[X]).map (expand ℂ 2) = signal *
    signal := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [signal, Matrix.mul_apply, Fin.sum_univ_two, sq]
theorem bidirTail_eq (R₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ Rs : List (Matrix (Fin 2) (Fin 2) ℂ),
      gqspTail ((bidirLayers R₀ Rs).map Prod.fst) =
        ((gqspTail Rs * R₀.map C).map (expand ℂ 2)) * signal
  | [] => by
      simp only [bidirLayers, List.map_cons, List.map_nil, gqspTail, Matrix.mul_one, Matrix.one_mul,
          map_C_map_expand]
  | R :: Rs => by
    simp only [bidirLayers, List.map_cons, gqspTail_cons, bidirTail_eq R₀ Rs,
        Matrix.map_one C C_0 C_1,
      Matrix.one_mul, Matrix.mul_assoc, map_expand_mul, map_C_map_expand, signal_map_expand]
theorem exists_bidir_cert {d : ℕ} (hd : Odd d) {P₀ : ℂ[X]} (hP₀ : P₀.natDegree ≤ 2 * d)
    (htw : twist P₀ = -conjRev (2 * d) P₀) (hlt : ∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ < 1) :
    ∃ (R₀ : Matrix (Fin 2) (Fin 2) ℂ) (Rs : List (Matrix (Fin 2) (Fin 2) ℂ))
    (Q : ℂ[X]), R₀ ∈ unitaryGroup (Fin 2) ℂ ∧ (∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ) ∧ Rs.length =
    d ∧ (gqspTail (hadamard2 :: (bidirLayers R₀ Rs).map Prod.fst) *
    hadamard2.map Polynomial.C) *ᵥ ![1, 0] = ![X * P₀, Q] := by
  obtain ⟨P, Q, hP, hQ, hPQ, hpair⟩ := exists_bidir_pair hd hP₀ htw hlt
  obtain ⟨R₀, Rs, hR₀, hRs, hlen, hmat⟩ := gqsp_decomposition_su2 hP hQ hPQ
  refine ⟨R₀, Rs, ((gqspTail (hadamard2 :: (bidirLayers R₀ Rs).map Prod.fst) *
      hadamard2.map C) *ᵥ ![1, 0]) 1,
    hR₀, hRs, hlen, funext fun i ↦ ?_⟩
  fin_cases i
  · simp [gqspTail_cons, bidirTail_eq, show (gqspTail Rs * R₀.map C).map (expand ℂ 2) =
        !![expand ℂ 2 P, -conjRev (2 * d) (expand ℂ 2 Q); expand ℂ 2 Q, conjRev (2 * d)
            (expand ℂ 2 P)] by
      rw [hmat, ← expand_conjRev hQ, ← expand_conjRev hP]; ext r c; fin_cases r <;>
          fin_cases c <;> simp,
      hadamard2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, signal]
    linear_combination C invSqrtTwo * C invSqrtTwo * hpair + X * P₀ *
      (by rw [← C_mul, invSqrtTwo_mul_self, ← map_ofNat C 2, ← C_mul]; norm_num : C invSqrtTwo *
            C invSqrtTwo * (2 : ℂ[X]) = 1)
  · rfl
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (e : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ)
theorem gqspOp_bidirLayers_nil (W : Matrix ι ι ℂ) (R₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    gqspOp e W (bidirLayers R₀ []) = e R₀ * sigOp e W true := by simp [bidirLayers, gqspOp]
theorem gqspOp_bidirLayers_cons (W : Matrix ι ι ℂ) (R₀ R : Matrix (Fin 2) (Fin 2) ℂ)
    (Rs : List (Matrix (Fin 2) (Fin 2) ℂ)) : gqspOp e W (bidirLayers R₀ (R :: Rs)) = e R *
    (sigOp e W false * sigOp e W true) * gqspOp e W (bidirLayers R₀ Rs) := by
  simp only [bidirLayers, gqspOp, map_one, Matrix.one_mul, Matrix.mul_assoc]
theorem corner_bidir {W : Matrix ι ι ℂ} (hW : W ∈ unitary (Matrix ι ι ℂ))
    (hWc : W ∈ qubitCommutant e) (hWc' : Wᴴ ∈ qubitCommutant e) {R₀ : Matrix (Fin 2) (Fin 2) ℂ}
    {Rs : List (Matrix (Fin 2) (Fin 2) ℂ)} {P₀ Q : ℂ[X]} (hR₀ : R₀ ∈ unitaryGroup (Fin 2) ℂ)
    (hRs : ∀ R ∈ Rs, R ∈ unitaryGroup (Fin 2) ℂ)
    (hcert : (gqspTail (hadamard2 :: (bidirLayers R₀ Rs).map Prod.fst) *
    hadamard2.map Polynomial.C) *ᵥ ![1, 0] = ![X * P₀, Q]) : e (single 0 0 1) *
    (gqspOp e W ((hadamard2, false) :: bidirLayers R₀ Rs) * e hadamard2) * e (single 0 0 1) =
    e (single 0 0 1) * (Wᴴ ^ Rs.length * aeval W P₀) := by
  set L := (hadamard2, false) :: bidirLayers R₀ Rs
  have hc := corner_gqspOp_zip e hW hWc hWc' hadamard2_mem (bs := L.map Prod.snd)
    (fun _ hR ↦ let ⟨t, ht, hr⟩ := List.mem_map.mp hR
      hr ▸ mem_cons_bidirLayers_unitary hR₀ hRs t ht) (by simp [L]) hcert
  rw [show (L.map Prod.fst).zip (L.map Prod.snd) =
      L by rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]] at hc
  rw [hc, show (L.map Prod.snd).count true = Rs.length + 1 by simp [L, count_true_bidirLayers],
    pow_succ, map_mul, aeval_X, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, show Wᴴ * W =
        1 from Unitary.star_mul_self_of_mem hW, Matrix.one_mul]
theorem commute_sigOp {W A : Matrix ι ι ℂ} (he : ∀ M, Commute (e M) A) (hW : Commute W A)
    (hW' : Commute Wᴴ A) (b : Bool) : Commute (sigOp e W b) A := by
  cases b <;> simp only [sigOp, mixedSignal, Bool.false_eq_true, ↓reduceIte, blockOp_diag, mul_one]
  exacts [((he _).mul_left hW).add_left (he _), (he _).add_left ((he _).mul_left hW')]
theorem commute_gqspOp {W A : Matrix ι ι ℂ} (he : ∀ M, Commute (e M) A) (hW : Commute W A)
    (hW' : Commute Wᴴ A) :
    ∀ L : List (Matrix (Fin 2) (Fin 2) ℂ × Bool), Commute (gqspOp e W L) A
  | [] => Commute.one_left A
  | (R, b) :: L =>
        ((he R).mul_left (commute_sigOp e he hW hW' b)).mul_left (commute_gqspOp he hW hW' L)
end QuantumComputation.Specs.PhotochemistrySolution.OvBidir
end

noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
section
open scoped ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
noncomputable abbrev cosMid4 : ℝ := 9238795325112868 / 10 ^ 16

theorem cos_two_pow_step {j : ℕ} (hj : 1 ≤ j) {C₀ εC c₀ : ℝ}
    (hC : |Real.cos (2 * Real.pi / (2 : ℝ) ^ j) - C₀| ≤ εC)
    (h : 0 ≤ c₀ - 2 / 10 ^ 16 ∧ 2 * (c₀ - 2 / 10 ^ 16) ^ 2 - 1 ≤ C₀ - εC ∧ C₀ + εC ≤ 2 *
        (c₀ + 2 / 10 ^ 16) ^ 2 - 1) :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ (j + 1)) - c₀| ≤ 2 / 10 ^ 16 :=
  cos_two_pi_div_two_pow_succ_approx hj h.1 (by norm_num) hC h.2.1 h.2.2

theorem sin_two_pow_step {j : ℕ} (hj : 1 ≤ j) {C₀ εC s₀ : ℝ}
    (hC : |Real.cos (2 * Real.pi / (2 : ℝ) ^ j) - C₀| ≤ εC)
    (h : 0 ≤ s₀ - 1 / 10 ^ 9 ∧ 2 * (s₀ - 1 / 10 ^ 9) ^ 2 ≤ 1 - (C₀ + εC) ∧ 1 - (C₀ - εC) ≤ 2 *
        (s₀ + 1 / 10 ^ 9) ^ 2) :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ (j + 1)) - s₀| ≤ 1 / 10 ^ 9 :=
  sin_two_pi_div_two_pow_succ_approx hj h.1 (by norm_num) hC h.2.1 h.2.2

theorem cos_two_pi_div_two_pow_4_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 4) - cosMid4| ≤ 2 / 10 ^ 16 :=
  cos_two_pow_step (by decide) cos_two_pi_div_two_pow_three_approx
    (by norm_num [cosMid4, sqrtTwoMid, sqrtTwoRad])
theorem cos_two_pi_div_two_pow_5_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 5) - cosMid5| ≤ 2 / 10 ^ 16 :=
  cos_two_pow_step (by decide) cos_two_pi_div_two_pow_4_approx (by norm_num [cosMid5, cosMid4])
theorem sin_two_pi_div_two_pow_5_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 5) - sinMid5| ≤ 1 / 10 ^ 9 :=
  sin_two_pow_step (by decide) cos_two_pi_div_two_pow_4_approx (by norm_num [sinMid5, cosMid4])
theorem cos_two_pi_div_two_pow_6_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 6) - cosMid6| ≤ 2 / 10 ^ 16 :=
  cos_two_pow_step (by decide) cos_two_pi_div_two_pow_5_approx (by norm_num [cosMid6, cosMid5])
theorem sin_two_pi_div_two_pow_6_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 6) - sinMid6| ≤ 1 / 10 ^ 9 :=
  sin_two_pow_step (by decide) cos_two_pi_div_two_pow_5_approx (by norm_num [sinMid6, cosMid5])
noncomputable abbrev sinMid7 : ℝ := 49067674327 / 10 ^ 12
theorem cos_two_pi_div_two_pow_7_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 7) - cosMid7| ≤ 2 / 10 ^ 16 :=
  cos_two_pow_step (by decide) cos_two_pi_div_two_pow_6_approx (by norm_num [cosMid7, cosMid6])
theorem sin_two_pi_div_two_pow_7_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 7) - sinMid7| ≤ 1 / 10 ^ 9 :=
  sin_two_pow_step (by decide) cos_two_pi_div_two_pow_6_approx (by norm_num [sinMid7, cosMid6])
noncomputable abbrev cosMid8 : ℝ := 9996988186962042 / 10 ^ 16
noncomputable abbrev sinMid8 : ℝ := 24541228523 / 10 ^ 12
theorem cos_two_pi_div_two_pow_8_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 8) - cosMid8| ≤ 2 / 10 ^ 16 :=
  cos_two_pow_step (by decide) cos_two_pi_div_two_pow_7_approx (by norm_num [cosMid8, cosMid7])
theorem sin_two_pi_div_two_pow_8_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 8) - sinMid8| ≤ 1 / 10 ^ 9 :=
  sin_two_pow_step (by decide) cos_two_pi_div_two_pow_7_approx (by norm_num [sinMid8, cosMid7])

noncomputable def phaseGradientState (m : ℕ) : StateVector m :=
    QFT.prodState m (fun r ↦ QFT.plusPhase (-(1 : ℝ) / (2 ^ (m - r.val) : ℝ)))
protected theorem sqrt_two_pow (m : ℕ) : (Real.sqrt 2) ^ m = Real.sqrt ((2 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ _ ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]

theorem phaseGradientState_apply (m : ℕ) (y : Fin (2 ^ m)) : phaseGradientState m y =
    (1 / Real.sqrt (2 ^ m : ℝ) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I *
    ((y.val : ℝ) / (2 ^ m : ℝ))) := by
  unfold phaseGradientState QFT.prodState QFT.plusPhase
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mod_cast (by rw [_root_.one_div_pow, PgBase.sqrt_two_pow] :
      (1 / Real.sqrt 2 : ℝ) ^ m = 1 / Real.sqrt ((2 : ℝ) ^ m))
  · rw [← Complex.exp_sum]
    congr 1
    have hsum :=
        congrArg (fun t : ℝ ↦ -2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
        (sum_basisBits_div_two_pow m y)
    rw [Complex.ofReal_sum, Finset.mul_sum] at hsum
    exact (Finset.sum_congr rfl fun _ _ ↦
        by push_cast; ring).trans (hsum.trans (by push_cast; ring))
end
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec

namespace QuantumComputation.Specs.PhotochemistrySolution
theorem norm_projector_le_one {I : Type*} [Fintype I] [DecidableEq I] {P : Matrix I I ℂ}
    (hH : Pᴴ = P) (hI : P * P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ * ‖P‖ = ‖P‖ := by rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hH, hI]
  nlinarith [norm_nonneg P]
end QuantumComputation.Specs.PhotochemistrySolution

noncomputable section
set_option exponentiation.threshold 8192
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat WithLp QuantumComputation.Specs
namespace QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.DynamicCircuit
variable {Var : Type}
def onRegister {k n : ℕ} (placement : QRegister k n) :
    DynamicCircuit Var k → DynamicCircuit Var n
  | .circuit c => .circuit (c.onRegister placement)
  | .measure v r => .measure v (placement.compose r)
  | @DynamicCircuit.qIf _ _ cond inst t f =>
        @DynamicCircuit.qIf _ _ cond inst (onRegister placement t) (onRegister placement f)
  | .seq p₁ p₂ => .seq (onRegister placement p₁) (onRegister placement p₂)
@[simp] theorem count_onRegister {k n a : ℕ} (g : PrimitiveGate a) (placement : QRegister k n)
    (p : DynamicCircuit Var k) :
    (onRegister placement p).count g = p.count g := by
  induction p <;> simp_all [onRegister, DynamicCircuit.count, Circuit.count_onRegister]
end QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
@[simp] theorem restrictAssertionToZeroAncilla_coe_loc {Var : Type} {n k : ℕ}
    (N : CQAssertion (Store Var) (2 ^ n)) (rAnc : QRegister k n) (σ : Store Var) :
    (CQAssertion.restrictToZeroAncilla N rAnc σ).1 = (N σ).1.conj (rAnc.basisOutcomeProjector 0) :=
        rfl
@[simp] theorem restrictAssertionToBasisOutcomes_coe {Var : Type} {n k : ℕ}
    (N : CQAssertion (Store Var) (2 ^ n)) (r : QRegister k n) (outcomes : Finset (Fin (2 ^ k)))
        (σ : Store Var) :
    (CQAssertion.restrictToBasisOutcomes N r outcomes σ).1 =
        (N σ).1.conj (r.basisOutcomesProjector outcomes) := rfl
@[simp] theorem restrictAssertionToBasisOutcomes_univ {Var : Type} {n k : ℕ}
    (N : CQAssertion (Store Var) (2 ^ n)) (r : QRegister k n) :
    CQAssertion.restrictToBasisOutcomes N r Finset.univ = N := by
  exact funext fun σ ↦ Subtype.ext <| HermitianMat.ext <| by simp [QRegister.basisOutcomesProjector]
theorem extractIndex_eq_zero_iff_basisBits_eq_zero {n k : ℕ} (r : QRegister k n)
    (global : Fin (2 ^ n)) : r.extractIndex global = 0 ↔ ∀ j : Fin k, basisBits n global (r j) =
    0 := by
  rw [← (basisBitsEquiv k).apply_eq_iff_eq, funext_iff]; refine forall_congr' fun j ↦ ?_
  rw [← (QRegExt.basisBits_extractIdx r)]; simp [basisBits, finFunctionFinEquiv]
@[simp] protected theorem wp_qAssign_comp_loc {Var : Type} [Fintype Var] {d : ℕ}
    (U₁ U₂ : Unitary d) (Θ : CQAssertion (Store Var) d) :
    wpQAssignCompat U₁ (wpQAssignCompat U₂ Θ) = wpQAssignCompat (U₂ * U₁) Θ := by
  funext σ; exact conjUnitary_star_comp U₁ U₂ (Θ σ)
@[simp high] theorem wp_circuit_compile_loc {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)]
    (c : Circuit n) (Θ : CQAssertion (Store Var) (2 ^ n)) :
    wp c.compile Θ = wpQAssignCompat c.eval Θ := by
  induction c generalizing Θ <;>
    simp_all [funext_iff, Circuit.compile, wpQAssignCompat, qAssign_obs_map]
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end
end
noncomputable section
open QuantumComputation.Specs
namespace QuantumComputation.Specs.PhotochemistrySolution.KineticStep
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Circuit.Notation Real
open Operator Matrix QProg HermitianMat WithLp DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
theorem sqrt_two_pow (m : ℕ) : (√2) ^ m = √((2 : ℝ) ^ m) := by
  induction m <;> simp_all [pow_succ, Real.sqrt_mul (pow_nonneg zero_le_two _)]
noncomputable def plusPhase (θ : ℝ) : ZMod 2 → ℂ :=
  fun b ↦ (1 / √2 : ℂ) * Complex.exp (2 * π * Complex.I * (θ * (b.val : ℝ) : ℂ))
theorem hadamardPhase_eq_plusPhase (a b : ZMod 2) :
    (1 / √2 : ℂ) * hadamardPhase (a * b) = plusPhase ((b.val : ℝ) / 2) a := by
  rcases (by decide +revert : (a = 0 ∨ b = 0) ∨ a = 1 ∧ b = 1) with (rfl | rfl) | ⟨rfl, rfl⟩
  · simp [plusPhase, hadamardPhase]
  · simp [plusPhase, hadamardPhase]
  · rw [hadamardPhase, plusPhase, mul_one, ite_eq_left rfl, ← Complex.exp_pi_mul_I,
      show (1 : ZMod 2).val = 1 from rfl]
    exact congrArg ((1 / √2 : ℂ) * Complex.exp ·) (by push_cast; ring)
@[simp] theorem bitRevEquiv_involutive (n : ℕ) (j : Fin (2 ^ n)) :
    bitRevEquiv n (bitRevEquiv n j) = j := by
  exact (basisBitsEquiv n).injective <| funext fun i ↦ by simp [basisBits_bitRevEquiv_coe]
@[simp] theorem bitRevEquiv_symm (n : ℕ) : (bitRevEquiv n).symm = bitRevEquiv n := by
  exact Equiv.ext fun j ↦ (Equiv.symm_apply_eq _).mpr (bitRevEquiv_involutive n j).symm
theorem swapAllUnitary_mulVec_basisState (n : ℕ) (j : Fin (2 ^ n)) :
    (QFT.swapAllUnitary n).1.mulVec (basisState j) = basisState (bitRevEquiv n j) := by
  simpa [QFT.swapAllUnitary, basisState] using Operator.permutationUnitary_mulVec_single _ j (1 : ℂ)
end QuantumComputation.Specs.PhotochemistrySolution.KineticStep

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
open PhotochemistrySolution.ZeroNEremSpec
/-- Stack-safe tail-recursive finite sum `∑_{i=0}^{M-1} f i`. -/
def foldSum (M : ℕ) (f : ℕ → ℕ) : ℕ := (List.range M).foldl (fun acc i ↦ acc + f i) 0
theorem foldSum_succ (M : ℕ) (f : ℕ → ℕ) : foldSum (M + 1) f = foldSum M f + f M := by
  simp [foldSum, List.range_succ]
theorem sum_fin_eq_foldSum (M : ℕ) (f : ℕ → ℕ) : (∑ x : Fin M, f x.val) = foldSum M f := by
  induction M <;> simp_all [Fin.sum_univ_castSucc, foldSum_succ, show foldSum 0 f = 0 from rfl]
/-- Exact complement prefix cardinality `#{x : Fin N | ¬ x.val < M} = N - M` when `M ≤ N`. -/
theorem card_fin_ge_of_le {M N : ℕ} (hle : M ≤ N) : ((Finset.univ : Finset (Fin N)).filter (fun x ↦
    ¬ x.val < M)).card = N - M := by
  simpa [card_fin_lt_of_le hle] using Nat.eq_sub_of_add_eq'
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x : Fin N ↦ x.val < M))
/-- Generic block-prefix counting theorem handling both hit and fallback outcomes. -/
theorem card_prefix_hit_or_miss {N : ℕ} (tag fallback s : ZeroNEremSector) (thr : ℕ)
    (hThr : thr ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x ↦ (if x.val < thr then tag else fallback) =
        s)).card =
      (if tag = s then thr else 0) + (if fallback = s then N - thr else 0) := by
  rw [← Finset.card_filter_add_card_filter_not (fun x : Fin N ↦ x.val < thr)]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.filter_comm, Finset.filter_congr (q := fun _ ↦ tag = s)
      fun _ hx ↦ by simp [(Finset.mem_filter.mp hx).2], Finset.filter_const]
    split_ifs <;> first | exact card_fin_lt_of_le hThr | rfl
  · rw [Finset.filter_comm, Finset.filter_congr (q := fun _ ↦ fallback = s)
      fun _ hx ↦ by simp [(Finset.mem_filter.mp hx).2], Finset.filter_const]
    split_ifs <;> first | exact card_fin_ge_of_le hThr | rfl
/-- Sum-splitting identity over `Fin (M + N)`. -/
theorem sum_fin_add {M N : ℕ} (g : ℕ → ℕ) : (∑ x : Fin (M + N), g x.val) = (∑ i : Fin M, g i.val) +
    (∑ j : Fin N, g (M + j.val)) := by
  simpa using Fin.sum_univ_add (f := fun x : Fin (M + N) ↦ g x.val)
/-- Product-splitting identity for summing `g : ℕ → ℕ` over `Fin (A * B)`. -/
theorem sum_fin_mul {A B : ℕ} (_hB : 0 < B) (g : ℕ → ℕ) : (∑ x : Fin (A * B), g x.val) = ∑ a :
    Fin A, ∑ b : Fin B, g (a.val * B + b.val) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [finProdFinEquiv, mul_comm, add_comm]
end QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
end

noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
def concretePhaseState1 : Circuit 1 := Circuit.sequence [ .H 0, .Z 0 ]
def concretePhaseState8 : Circuit 1 :=
    Circuit.sequence [ .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0,
    .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0,
    .H 0, .S 0, .Z 0, .Z 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0,
    .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0,
    .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .S 0, .H 0, .T 0, .H 0, .T 0, .H 0, .H 0,
    .Z 0, .S 0, .X 0, .H 0 ]
def concretePhaseState (j : ℕ) : Circuit 1 :=
  match j with
  | 1 => concretePhaseState1
  | 2 => concretePhaseState2
  | 3 => concretePhaseState3
  | 4 => concretePhaseState4
  | 5 => concretePhaseState5
  | 6 => concretePhaseState6
  | 7 => concretePhaseState7
  | 8 => concretePhaseState8
  | 9 => concretePhaseState9
  | 10 => concretePhaseState10
  | 11 => concretePhaseState11
  | 12 => concretePhaseState12
  | 13 => concretePhaseState13
  | 14 => concretePhaseState14
  | 15 => concretePhaseState15
  | 16 => concretePhaseState16
  | 17 => concretePhaseState17
  | 18 => concretePhaseState18
  | _ => Circuit.H 0

@[simp] theorem concretePhaseState_count_toff (j : ℕ) :
    (concretePhaseState j).count PrimitiveGate.TOFF = 0 := by
  unfold concretePhaseState; split <;> rfl
theorem concretePhaseState_count_t_of_gt_18 {j : ℕ}
    (hj : 18 < j) : (concretePhaseState j).count PrimitiveGate.T = 0 := by
  unfold concretePhaseState; split <;> first | omega | decide
theorem sum_concretePhaseState_count_t_Icc_18 : (∑ j ∈ Finset.Icc 1 18,
    (concretePhaseState j).count PrimitiveGate.T) = 487 := by decide
open scoped Fin.CommRing
def preparePhaseGradient {n b : ℕ} (rGrad : QRegister b n) : Circuit n :=
    Circuit.sequence (List.ofFn (fun r : Fin b ↦
    (concretePhaseState (b - r.val)).onRegister (QRegister.singleton (rGrad r))))
@[simp] theorem preparePhaseGradient_count_toff {n b : ℕ} (rGrad : QRegister b n) :
    (preparePhaseGradient rGrad).count PrimitiveGate.TOFF = 0 := by
  simp [preparePhaseGradient, Circuit.count_sequence, List.sum_ofFn]
theorem preparePhaseGradient_count_t_eq {n b : ℕ} (rGrad : QRegister b n) :
    (preparePhaseGradient rGrad).count PrimitiveGate.T = ∑ r : Fin b,
    (concretePhaseState (b - r.val)).count PrimitiveGate.T := by
  simp [preparePhaseGradient, Circuit.count_sequence, List.sum_ofFn]
theorem preparePhaseGradient_count_t_of_ge_18 {n b : ℕ} (hb : 18 ≤ b) (rGrad : QRegister b n) :
    (preparePhaseGradient rGrad).count PrimitiveGate.T = 487 := by
  let emb : Fin b ↪ ℕ := ⟨fun r ↦ b - r.val, fun _ _ (h : b - _ = b - _) ↦ Fin.ext (by omega)⟩
  refine (preparePhaseGradient_count_t_eq rGrad).trans (((Finset.sum_map Finset.univ emb
    fun j ↦
        (concretePhaseState j).count .T).symm.trans ?_).trans sum_concretePhaseState_count_t_Icc_18)
  rw [← Finset.sum_filter_of_ne fun j hj hne ↦ by
    rcases Finset.mem_map.mp hj with ⟨r, _, rfl⟩
    exact Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt r.isLt, not_lt.mp fun h ↦
        hne (concretePhaseState_count_t_of_gt_18 h)⟩]
  refine congrArg (Finset.sum · _) (Finset.ext fun j ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Icc]
  exact ⟨And.right, fun ⟨h1, h2⟩ ↦ ⟨⟨⟨b - j, by omega⟩, Nat.sub_sub_self (by omega)⟩, h1, h2⟩⟩
@[simp] theorem preparePhaseGradient_count_t_48 {n : ℕ} (rGrad : QRegister 48 n) :
    (preparePhaseGradient rGrad).count PrimitiveGate.T = 487 :=
        preparePhaseGradient_count_t_of_ge_18 (by decide) rGrad
@[simp] theorem preparePhaseGradient_count_t_56 {n : ℕ} (rGrad : QRegister 56 n) :
    (preparePhaseGradient rGrad).count PrimitiveGate.T = 487 :=
        preparePhaseGradient_count_t_of_ge_18 (by decide) rGrad
@[simp] theorem preparePhaseGradient_count_t_62 {n : ℕ} (rGrad : QRegister 62 n) :
    (preparePhaseGradient rGrad).count PrimitiveGate.T = 487 :=
        preparePhaseGradient_count_t_of_ge_18 (by decide) rGrad
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.QubitizationCore
open scoped Matrix.Norms.L2Operator
open Operator Matrix WithLp NormedSpace
def chebyshevOpNat {I : Type*} [Fintype I] [DecidableEq I] : ℕ → Matrix I I ℂ → Matrix I I ℂ
  | 0, _ => 1
  | 1, X => X
  | n + 2, X => (2 : ℂ) • (X * chebyshevOpNat (n + 1) X) - chebyshevOpNat n X
def reflectionMatrix {I : Type*} [Fintype I] [DecidableEq I] (proj0 : Matrix I I ℂ) :
    Matrix I I ℂ := (2 : ℂ) • proj0 - 1
theorem reflectionMatrix_mul_self {I : Type*} [Fintype I] [DecidableEq I] {proj0 : Matrix I I ℂ}
    (h_idem : proj0 * proj0 = proj0) : reflectionMatrix proj0 * reflectionMatrix proj0 = 1 := by
  unfold reflectionMatrix;
  simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
      Matrix.mul_one, h_idem]; ext i j; simp; ring
theorem proj_walk_add_symm {I : Type*} [Fintype I] [DecidableEq I] {proj0 U : Matrix I I ℂ}
    (h_idem : proj0 * proj0 = proj0) : proj0 * (reflectionMatrix proj0 * U + U *
    reflectionMatrix proj0) = (2 : ℂ) • (proj0 * U * proj0) := by
  simp only [reflectionMatrix, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, h_idem]
  ext; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
theorem qubiti_walk_pow_proj_eq_chebyshev_pair {I : Type*} [Fintype I] [DecidableEq I]
    {proj0 U X : Matrix I I ℂ} (h_idem : proj0 * proj0 = proj0) (hU : U * U = 1)
    (hblock : proj0 * U * proj0 = X * proj0) (n : ℕ) : proj0 * (reflectionMatrix proj0 * U) ^ n *
    proj0 = chebyshevOpNat n X * proj0 ∧ proj0 * (reflectionMatrix proj0 * U) ^ (n + 1) * proj0 =
    chebyshevOpNat (n + 1) X * proj0 := by
  set R := reflectionMatrix proj0
  induction n with
  | zero =>
    refine ⟨by simp [chebyshevOpNat, h_idem], ?_⟩
    rw [pow_one, ← Matrix.mul_assoc, show proj0 * R = proj0 by
      simp only [R, reflectionMatrix, Matrix.mul_sub, mul_smul_comm, h_idem, Matrix.mul_one]
      ext; simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring, hblock,
          chebyshevOpNat]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [show (R * U) ^ (n + 2) = (R * U + U * R) * (R * U) ^ (n + 1) - (R * U) ^ n by
        rw [pow_succ' (R * U) (n + 1), Matrix.add_mul, pow_succ' (R * U) n, ← Matrix.mul_assoc (U *
            R),
          show U * R * (R * U) =
              1 by rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, reflectionMatrix_mul_self h_idem,
                     Matrix.one_mul, hU],
          Matrix.one_mul]; abel,
      Matrix.mul_sub, Matrix.sub_mul, ih.1, ← Matrix.mul_assoc proj0 (R * U + U * R),
          proj_walk_add_symm h_idem, hblock]
    simp only [chebyshevOpNat, Matrix.sub_mul, smul_mul_assoc, Matrix.mul_assoc,
      show proj0 * ((R * U) ^ (n + 1) * proj0) = _ from (Matrix.mul_assoc _ _ _).symm.trans ih.2]
theorem walk_pow_proj_eq_chebyshev {I : Type*} [Fintype I] [DecidableEq I]
    {proj0 U X : Matrix I I ℂ} (h_idem : proj0 * proj0 = proj0) (hU : U * U = 1)
    (hblock : proj0 * U * proj0 = X * proj0) (n : ℕ) : proj0 * (reflectionMatrix proj0 * U) ^ n *
    proj0 = chebyshevOpNat n X * proj0 :=
    (qubiti_walk_pow_proj_eq_chebyshev_pair h_idem hU hblock n).1
theorem opNorm_cleanAncilla_le_sqrt_two_mul_block_error {k m : ℕ}
    (W : 𝐔[Fin (2 ^ (k + m))]) (U_sys : 𝐔[Fin (2 ^ k)])
    {ε_poly : ℝ} (_hε : 0 ≤ ε_poly)
    (hblock : ‖(QRegister.block k m le_rfl).basisOutcomeProjector 0 *
        (W.1 - (QRegister.block 0 k (by omega)).embedMatrix U_sys.1) *
        (QRegister.block k m le_rfl).basisOutcomeProjector 0‖ ≤ ε_poly) :
    ‖(W.1 - (QRegister.block 0 k (by omega)).embedMatrix U_sys.1) *
        (QRegister.block k m le_rfl).basisOutcomeProjector 0‖ ≤ Real.sqrt (2 * ε_poly) := by
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let proj0 := anc.basisOutcomeProjector 0
  let U_mat := sys.embedMatrix U_sys.1
  have hcomm : U_mat * proj0 = proj0 * U_mat :=
    sys.embedMatrix_comm_of_disjoint anc (QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl
        (by omega)) U_sys.1 (compProj 0)
  have hP_herm : proj0ᴴ = proj0 := anc.basisOutcomeProjector_conjTranspose 0
  have hU_adj : U_matᴴ * U_mat = 1 := by
    rw [← sys.embedMatrix_conjTranspose, ← sys.embedMatrix_mul, show U_sys.1ᴴ * U_sys.1 =
        1 from U_sys.2.1, sys.embedMatrix_one]
  let D := proj0 * (U_mat - W.1) * proj0
  have hnorm_U : ‖U_mat‖ ≤ 1 := by
    have : ‖U_mat‖ * ‖U_mat‖ = 1 := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hU_adj, NormOneClass.norm_one]
    nlinarith [norm_nonneg U_mat]
  have hD_le : ‖D‖ ≤ ε_poly := by
    simpa only [show D = -(proj0 * (W.1 - U_mat) *
        proj0) by simp [D, Matrix.mul_sub, Matrix.sub_mul], norm_neg] using hblock
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, show ((W.1 - U_mat) * proj0)ᴴ *
      ((W.1 - U_mat) * proj0) =
      U_matᴴ * D + Dᴴ * U_mat by
    have hcomm_adj : proj0 * U_matᴴ = U_matᴴ * proj0 := by
      simpa only [Matrix.conjTranspose_mul, hP_herm] using congrArg Matrix.conjTranspose hcomm
    refine (by simp only [Matrix.conjTranspose_mul, hP_herm, Matrix.mul_assoc] :
      _ = proj0 * ((W.1 - U_mat)ᴴ * (W.1 - U_mat)) * proj0).trans ?_
    rw [show (W.1 - U_mat)ᴴ * (W.1 - U_mat) = U_matᴴ * (U_mat - W.1) + (U_mat - W.1)ᴴ * U_mat by
      simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, show W.1ᴴ * W.1 =
          1 from W.2.1, hU_adj]; abel]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc proj0 U_matᴴ, hcomm_adj, hcomm, D, Matrix.conjTranspose_mul,
        hP_herm, Matrix.mul_assoc]]
  refine (norm_add_le _ _).trans ((add_le_add (Matrix.l2_opNorm_mul _ _)
      (Matrix.l2_opNorm_mul _ _)).trans ?_)
  rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
  linarith [mul_le_mul hnorm_U hD_le (norm_nonneg D) zero_le_one,
      mul_le_mul hD_le hnorm_U (norm_nonneg U_mat) _hε]
theorem exp_sub_smul_one_eq_smul_exp {d : ℕ} [NeZero d] (H : Operator d)
    (c t : ℝ) : NormedSpace.exp ((-Complex.I * t) • (H - (c : ℂ) • (1 : Operator d))) =
    Complex.exp (((c * t : ℝ) : ℂ) * Complex.I) • NormedSpace.exp ((-Complex.I * t) • H) := by
  let z : ℂ := ((c * t : ℝ) : ℂ) * Complex.I
  let +nondep : NormedAlgebra ℚ (Operator d) := .restrictScalars ℚ ℂ (Operator d)
  rw [show (-Complex.I * t) • (H - (c : ℂ) • (1 : Operator d)) = z • (1 : Operator d) +
      (-Complex.I * t) • H by
      ext; simp only [z, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul];
          push_cast; ring,
    NormedSpace.exp_add_of_commute (((Commute.one_left H).smul_right _).smul_left _),
    show NormedSpace.exp (z • (1 : Operator d)) = Complex.exp z • (1 : Operator d) by
      rw [show z • (1 : Operator d) = Matrix.diagonal fun _ ↦
          z by ext i j; by_cases h : i = j <;> simp [h], Matrix.exp_diagonal]
      ext i j; by_cases h : i = j <;> simp [h, Complex.exp_eq_exp_ℂ],
    smul_mul_assoc, Matrix.one_mul]
end QuantumComputation.Specs.PhotochemistrySolution.QubitizationCore
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.GQSP
open Polynomial Matrix PhotochemistrySolution.QubitizationCore
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem chebyshevOpNat_commute_pair {A B : Matrix I I ℂ} (h : Commute A B) :
    ∀ k : ℕ, Commute (chebyshevOpNat k A) B ∧ Commute (chebyshevOpNat (k + 1) A) B
  | 0 => ⟨Commute.one_left B, h⟩
  | k + 1 => match chebyshevOpNat_commute_pair h k with
      | ⟨h0, h1⟩ => ⟨h1, ((h.mul_left h1).smul_left 2).sub_left h0⟩
theorem chebyshevOpNat_commute {A B : Matrix I I ℂ} (h : Commute A B)
    (k : ℕ) : Commute (chebyshevOpNat k A) B := (chebyshevOpNat_commute_pair h k).1
theorem chebyshevOpNat_conjTranspose_pair {A : Matrix I I ℂ} (hA : Aᴴ = A) :
    ∀ k : ℕ, (chebyshevOpNat k A)ᴴ = chebyshevOpNat k A ∧
      (chebyshevOpNat (k + 1) A)ᴴ = chebyshevOpNat (k + 1) A
  | 0 => ⟨by simp [chebyshevOpNat], hA⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := chebyshevOpNat_conjTranspose_pair hA k
    exact ⟨h1,
        by simp [chebyshevOpNat, conjTranspose_mul, h0, h1, hA,
             (chebyshevOpNat_commute (Commute.refl A) (k + 1)).eq]⟩
theorem chebyshevOpNat_conjTranspose {A : Matrix I I ℂ} (hA : Aᴴ = A)
    (k : ℕ) : (chebyshevOpNat k A)ᴴ = chebyshevOpNat k A :=
    (chebyshevOpNat_conjTranspose_pair hA k).1
theorem reflectionMatrix_conjTranspose {proj0 : Matrix I I ℂ} (hPh : proj0ᴴ = proj0) :
    (reflectionMatrix proj0)ᴴ = reflectionMatrix proj0 := by simp [reflectionMatrix, hPh]
theorem walk_mem_unitary {proj0 S : Matrix I I ℂ} (hPh : proj0ᴴ = proj0)
    (hP : proj0 * proj0 = proj0) (hS : S * S = 1) (hSh : Sᴴ = S) : reflectionMatrix proj0 *
    S ∈ unitary (Matrix I I ℂ) :=
  mul_mem (Unitary.mem_iff.mpr
      (by simp [star_eq_conjTranspose, reflectionMatrix_conjTranspose hPh,
            reflectionMatrix_mul_self hP]))
    (Unitary.mem_iff.mpr (by simp [star_eq_conjTranspose, hSh, hS]))
end QuantumComputation.Specs.PhotochemistrySolution.GQSP
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.GQSP
open scoped Matrix.Norms.L2Operator
open Polynomial Matrix ComplexConjugate PhotochemistrySolution.QubitizationCore
def kapteynTruncD : ℕ := 40000000
def chebScalarC : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, x => x
  | k + 2, x => 2 * x * chebScalarC (k + 1) x - chebScalarC k x
theorem select_chebyshevT_fin1_pair (x : ℂ) :
    ∀ k : ℕ, chebyshevT k (!![x] : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = chebScalarC k x ∧
      chebyshevT (k + 1) (!![x] : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = chebScalarC (k + 1) x
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
      obtain ⟨ih0, ih1⟩ := select_chebyshevT_fin1_pair x k
      refine ⟨ih1, ?_⟩
      rw [chebyshevT, chebScalarC, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
          Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, smul_eq_mul, ih0, ih1]
      simp only [Matrix.of_apply, Matrix.cons_val_zero]
      ring
theorem select_chebScalarC_joukowsky_pair {w : ℂ} (hw : w ≠ 0) :
    ∀ k : ℕ,
      chebScalarC k ((w + w⁻¹) / 2) = (w ^ k + (w⁻¹) ^ k) / 2 ∧
      chebScalarC (k + 1) ((w + w⁻¹) / 2) = (w ^ (k + 1) + (w⁻¹) ^ (k + 1)) / 2
  | 0 => ⟨by norm_num [chebScalarC], by simp [chebScalarC]⟩
  | k + 1 =>
      let ⟨ih0, ih1⟩ := select_chebScalarC_joukowsky_pair hw k
      ⟨ih1,
          by simp only [chebScalarC, ih1, ih0, pow_succ']; linear_combination ((w⁻¹) ^ k +
               w ^ k) / 2 * mul_inv_cancel₀ hw⟩
noncomputable def expTaylorC (N : ℕ) (z : ℂ) : ℂ :=
    ∑ j ∈ Finset.range (N + 1), z ^ j / (j.factorial : ℂ)
theorem laurent_sum_joukowsky_eq_expTaylorC (D : ℕ) (s : ℝ) {w : ℂ}
    (hw : w ≠ 0) : jacobiAngerLaurentCoeff D s 0 + ∑ k ∈ Finset.Icc 1 D,
    jacobiAngerLaurentCoeff D s k * (w ^ k + (w⁻¹) ^ k) = expTaylorC D (-Complex.I * (s : ℂ) *
    ((w + w⁻¹) / 2)) := by
  let x : ℂ := (w + w⁻¹) / 2
  have hpow (j : ℕ) : ((!![x] : Matrix (Fin 1) (Fin 1) ℂ) ^ j) 0 0 = x ^ j := by
    induction j with | zero => rfl | succ j ih => simp [pow_succ, Matrix.mul_apply, ih]
  refine (Eq.symm ?_).trans ((congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ ↦ M 0 0)
    (chebyshevPolyApprox_eq_expNegITaylor (!![x] : Matrix (Fin 1) (Fin 1) ℂ) D s)).trans ?_)
  · unfold chebyshevPolyApprox
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [show Finset.range (D + 1) = insert 0 (Finset.Icc 1 D) from Finset.ext fun k ↦
        by simp; omega,
      Finset.sum_insert (by simp), show jacobiAngerTruncCoeff D s 0 *
          chebyshevT 0 (!![x] : Matrix (Fin 1) (Fin 1) ℂ) 0 0 =
        jacobiAngerLaurentCoeff D s 0 by simp [jacobiAngerLaurentCoeff, chebyshevT]]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun k hk ↦ ?_)
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := (Finset.mem_Icc.mp hk).1; omega⟩
    rw [(select_chebyshevT_fin1_pair x (m + 1)).1,
      (select_chebScalarC_joukowsky_pair hw (m + 1)).1]
    simp only [jacobiAngerLaurentCoeff]; ring
  · unfold expNegITaylor expTaylorC
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hpow j, div_mul_eq_mul_div, ← mul_pow]
theorem select_geom_sum_unit_root {M : ℕ} {η : ℂ} (h1 : η ≠ 1)
    (hM : η ^ M = 1) : ∑ m ∈ Finset.range M, η ^ m = 0 :=
  (mul_eq_zero.mp
      (by rw [mul_geom_sum, hM, sub_self] : (η - 1) * ∑ m ∈ Finset.range M, η ^ m = 0)).resolve_left
      (sub_ne_zero.mpr h1)
theorem select_root_of_unity_pow_ne_one {M p : ℕ} (hp1 : 1 ≤ p)
    (hpM : p < M) : Complex.exp (2 * Real.pi * Complex.I / (M : ℂ)) ^ p ≠ 1 := by
  rw [← Complex.exp_nat_mul]
  intro h1
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  have hdiv : (p : ℂ) * (2 * Real.pi * Complex.I) / (M : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I)
      := by
    simpa [mul_div_assoc] using hk
  rw [div_eq_iff (by exact_mod_cast (by omega : M ≠ 0))] at hdiv
  have heqZ : (p : ℤ) = k * (M : ℤ) := by
    exact_mod_cast (mul_right_cancel₀
      (by simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * Real.pi * Complex.I : ℂ) ≠ 0)
      (by linear_combination hdiv) : (p : ℂ) = k * (M : ℂ))
  rcases le_or_gt k 0 with hk0 | hk1
  · have := mul_nonpos_of_nonpos_of_nonneg hk0 (by omega : (0 : ℤ) ≤ M)
    omega
  · have := mul_le_mul_of_nonneg_right hk1 (by omega : (0 : ℤ) ≤ M)
    omega
theorem select_inv_pow_swap {z : ℂ} (m n : ℕ) : ((z ^ m)⁻¹) ^ n = ((z⁻¹) ^ n) ^ m := by
  rw [← inv_pow, ← pow_mul, mul_comm m n, pow_mul, inv_pow]
theorem jacobiAngerLaurentCoeff_eq_discrete_cauchy (D : ℕ) (s : ℝ) {r : ℝ} (hr : 0 < r)
    {n : ℕ} (hn : n ∈ Finset.Icc 1 D) :
    let M : ℕ := 2 * D + 1; let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))
    let w : ℕ → ℂ := fun m ↦ (r : ℂ) * ζ ^ m
    jacobiAngerLaurentCoeff D s n =
      (1 / (M : ℂ)) * ∑ m ∈ Finset.range M,
        expTaylorC D (-Complex.I * (s : ℂ) * ((w m + (w m)⁻¹) / 2)) * ((w m)⁻¹) ^ n := by
  intro M ζ w
  simp only [Finset.mem_Icc] at hn
  have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
  have hw_ne : ∀ m, w m ≠ 0 := fun m ↦
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (pow_ne_zero m hζ_ne)
  have hM_ne : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hζM : ζ ^ M = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, show (M : ℂ) * (2 * Real.pi * Complex.I / (M : ℂ)) = 2 * Real.pi *
        Complex.I by field_simp [hM_ne], Complex.exp_two_pi_mul_I]
  have hw_prod (a b m : ℕ) : (w m) ^ a * ((w m)⁻¹) ^ b = ((r : ℂ) ^ a * ((r : ℂ)⁻¹) ^ b) *
      (ζ ^ a * (ζ⁻¹) ^ b) ^ m := by
    dsimp only [w]
    rw [mul_pow, mul_inv, mul_pow, ← pow_mul, mul_comm m a, pow_mul, select_inv_pow_swap, mul_pow]
    ring
  have hsum_ne (a b : ℕ) (hne : a ≠ b) (hab : a + b < M) : ∑ m ∈ Finset.range M, (w m) ^ a *
      ((w m)⁻¹) ^ b = 0 := by
    have hne1 : ζ ^ a * (ζ⁻¹) ^ b ≠ 1 := fun h1 ↦ by
      have heq : ζ ^ a = ζ ^ b := by
        rw [← mul_one (ζ ^ a), ← inv_mul_cancel₀ (pow_ne_zero b hζ_ne), ← inv_pow, ← mul_assoc, h1,
            one_mul]
      have step {u v : ℕ} (huv : u < v) (hv : v - u < M) (h : ζ ^ u = ζ ^ v) : False := by
        rw [← Nat.add_sub_cancel' huv.le, pow_add] at h
        exact select_root_of_unity_pow_ne_one (by omega) hv (mul_left_cancel₀ (pow_ne_zero u hζ_ne)
            (by linear_combination h.symm))
      exact (lt_or_gt_of_ne hne).elim (fun h ↦ step h (by omega) heq)
          (fun h ↦ step h (by omega) heq.symm)
    have hM1 : (ζ ^ a * (ζ⁻¹) ^ b) ^ M = 1 := by
      rw [mul_pow, ← pow_mul, mul_comm a M, pow_mul, hζM, one_pow, one_mul, ← pow_mul, mul_comm b M,
          pow_mul, inv_pow, hζM, inv_one, one_pow]
    simp_rw [hw_prod a b, ← Finset.mul_sum, select_geom_sum_unit_root hne1 hM1, mul_zero]
  have hterm : ∀ m ∈ Finset.range M, expTaylorC D (-Complex.I * (s : ℂ) * ((w m + (w m)⁻¹) / 2)) *
      ((w m)⁻¹) ^ n =
      jacobiAngerLaurentCoeff D s 0 * ((w m)⁻¹) ^ n + ∑ k ∈ Finset.Icc 1 D,
          jacobiAngerLaurentCoeff D s k * ((w m) ^ k * ((w m)⁻¹) ^ n + ((w m)⁻¹) ^ k *
          ((w m)⁻¹) ^ n) := fun m _ ↦ by
    rw [← laurent_sum_joukowsky_eq_expTaylorC D s (hw_ne m), add_mul, Finset.sum_mul]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
  have h0n := hsum_ne 0 n (by omega) (by omega)
  simp only [pow_zero, one_mul] at h0n
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, h0n, mul_zero, zero_add,
      Finset.sum_comm]
  have hinner : ∀ k ∈ Finset.Icc 1 D, (∑ m ∈ Finset.range M, jacobiAngerLaurentCoeff D s k *
      ((w m) ^ k * ((w m)⁻¹) ^ n + ((w m)⁻¹) ^ k * ((w m)⁻¹) ^ n)) = if k = n then (M : ℂ) *
      jacobiAngerLaurentCoeff D s n else 0 := fun k hk ↦ by
    simp only [Finset.mem_Icc] at hk
    have h0kn := hsum_ne 0 (k + n) (by omega) (by omega)
    simp only [pow_zero, one_mul, pow_add] at h0kn
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, h0kn, mul_zero, add_zero]
    obtain rfl | hkn := eq_or_ne k n
    · have h1 : ∀ m, (w m) ^ k * ((w m)⁻¹) ^ k = 1 := fun m ↦ by
        rw [← mul_pow, mul_inv_cancel₀ (hw_ne m), one_pow]
      simp_rw [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ite_true]
      ring
    · simp only [hkn, ↓reduceIte, hsum_ne k n hkn (by omega), mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.Icc 1 D) n]
  simp only [Finset.mem_Icc, hn.1, hn.2, and_self, ite_true]
  field_simp [hM_ne]
theorem select_expTaylorC_zero (N : ℕ) : expTaylorC N 0 = 1 := by
  simp [expTaylorC, Finset.sum_range_succ']
theorem select_hasDerivAt_expTaylorC_succ (N : ℕ) (z : ℂ)
    (t : ℝ) : HasDerivAt (fun u : ℝ ↦ expTaylorC (N + 1) ((u : ℂ) * z))
    (z * expTaylorC N ((t : ℂ) * z)) t := by
  rw [show (fun u : ℝ ↦ expTaylorC (N + 1) ((u : ℂ) * z)) = fun u : ℝ ↦ (1 : ℂ) +
      (∑ j ∈ Finset.range (N + 1), fun v : ℝ ↦ (((v : ℂ) * z) ^ (j + 1)) /
          ((j + 1).factorial : ℂ)) u from
    funext fun u ↦
        by unfold expTaylorC; rw [Finset.sum_range_succ', Finset.sum_apply]; simp [add_comm]]
  refine ((HasDerivAt.sum fun j _ ↦ (?_ : HasDerivAt (fun v : ℝ ↦ (((v : ℂ) * z) ^ (j + 1)) /
      ((j + 1).factorial : ℂ))
    (z * ((((t : ℂ) * z) ^ j) /
        (j.factorial : ℂ))) t)).const_add (1 : ℂ)).congr_deriv (by rw [expTaylorC, Finset.mul_sum])
  refine (((show HasDerivAt (fun u : ℝ ↦ (u : ℂ) * z) z t from
    ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).congr_deriv (one_mul z)).pow (j +
        1)).div_const
      ((j + 1).factorial : ℂ)).congr_deriv ?_
  simp only [add_tsub_cancel_right, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [show (j : ℂ) + 1 ≠ 0 from mod_cast Nat.succ_ne_zero j]
theorem norm_expTaylorC_sub_exp_le (N : ℕ) (z : ℂ) : ‖expTaylorC N z - Complex.exp z‖ ≤
    (‖z‖ ^ (N + 1) / ((N + 1).factorial : ℝ)) * Real.exp ‖z‖ := by
  suffices h : ∀ (M : ℕ) (t : ℝ), 0 ≤ t → ‖expTaylorC M ((t : ℂ) * z) - Complex.exp ((t : ℂ) * z)‖ ≤
      ((t * ‖z‖) ^ (M + 1) / ((M + 1).factorial : ℝ)) *
      Real.exp (t * ‖z‖) by simpa using h N 1 zero_le_one
  have hexpD : ∀ u : ℝ, HasDerivAt (fun v : ℝ ↦ Complex.exp ((v : ℂ) * z))
      (Complex.exp ((u : ℂ) * z) * z) u := fun u ↦
      (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const z).congr_deriv (one_mul z)).cexp
  have hode : ∀ (M : ℕ) (f' : ℝ → ℂ), (∀ u, HasDerivAt (fun v : ℝ ↦ expTaylorC M ((v : ℂ) * z) -
      Complex.exp ((v : ℂ) * z)) (f' u) u) →
      (∀ u, 0 ≤ u → ‖f' u‖ ≤ ‖z‖ * (((u * ‖z‖) ^ M / (M.factorial : ℝ)) * Real.exp (u * ‖z‖))) →
      ∀ (t : ℝ), 0 ≤ t → ‖expTaylorC M ((t : ℂ) * z) - Complex.exp ((t : ℂ) * z)‖ ≤
          ((t * ‖z‖) ^ (M + 1) / ((M + 1).factorial : ℝ)) * Real.exp (t * ‖z‖) :=
          fun M f' hf hle t ht ↦ by
    have hBD : ∀ u : ℝ, HasDerivAt (fun v : ℝ ↦ ((v * ‖z‖) ^ (M + 1) / ((M + 1).factorial : ℝ)) *
        Real.exp (v * ‖z‖))
        (‖z‖ * (((u * ‖z‖) ^ M / (M.factorial : ℝ)) * Real.exp (u * ‖z‖)) + ((u * ‖z‖) ^ (M + 1) /
            ((M + 1).factorial : ℝ)) * ‖z‖ * Real.exp (u * ‖z‖)) u := fun u ↦ by
      have hg1 : HasDerivAt (fun v : ℝ ↦ (v * ‖z‖) ^ (M + 1) / ((M + 1).factorial : ℝ))
          (‖z‖ * ((u * ‖z‖) ^ M / (M.factorial : ℝ))) u := by
        refine ((((hasDerivAt_id' u).mul_const ‖z‖).congr_deriv (one_mul _)).pow (M +
            1) |>.div_const _).congr_deriv ?_
        have hne : (M : ℝ) + 1 ≠ 0 := by positivity
        simp only [add_tsub_cancel_right, Nat.factorial_succ M, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one]
        field_simp [hne]
      exact (hg1.mul ((((hasDerivAt_id' u).mul_const ‖z‖).congr_deriv (one_mul _)).exp)).congr_deriv
          (by ring)
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun u _ ↦ (hf u).continuousAt.continuousWithinAt : ContinuousOn _ (Set.Icc 0 t))
      (fun u _ ↦ (hf u).hasDerivWithinAt)
      (by simp [select_expTaylorC_zero]) hBD (fun u hu ↦ ?_) (Set.right_mem_Icc.mpr ht)
    linarith [hle u hu.1,
        mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg (mul_nonneg hu.1 (norm_nonneg z)) (M + 1))
        (Nat.cast_nonneg (α := ℝ) (M + 1).factorial)) (norm_nonneg z)) (Real.exp_pos (u * ‖z‖)).le]
  intro M
  induction M with
  | zero =>
      refine hode 0 (fun u ↦ -z * Complex.exp ((u : ℂ) * z)) (fun u ↦ ?_) (fun u hu ↦ ?_)
      · exact (HasDerivAt.sub (by simpa [expTaylorC] using hasDerivAt_const u (1 : ℂ))
            (hexpD u)).congr_deriv (by ring)
      · rw [norm_mul, norm_neg, Complex.norm_exp]
        simpa using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (by simpa using mul_le_mul_of_nonneg_left (Complex.re_le_norm z) hu)) (norm_nonneg z)
  | succ M ih =>
      exact hode (M + 1) (fun u ↦ z * (expTaylorC M ((u : ℂ) * z) - Complex.exp ((u : ℂ) * z)))
        (fun u ↦ ((select_hasDerivAt_expTaylorC_succ M z u).sub (hexpD u)).congr_deriv (by ring))
        (fun u hu ↦ (norm_mul z _).le.trans (mul_le_mul_of_nonneg_left (ih u hu) (norm_nonneg z)))
noncomputable def truncLaurentPoly (K D : ℕ) (s : ℝ) : ℂ[X] :=
    laurentPoly K (jacobiAngerLaurentCoeff D s)
noncomputable def truncChebApprox {I : Type*} [Fintype I] [DecidableEq I] (K D : ℕ)
    (H : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
    ∑ k ∈ Finset.range (K + 1), jacobiAngerTruncCoeff D s k • chebyshevT k H
theorem poly_mul_star_pow_aeval_truncLaurentPoly {n : Type*} [Fintype n] [DecidableEq n] (K D : ℕ)
    (s : ℝ) {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) : (Uᴴ) ^ K *
    aeval U (truncLaurentPoly K D s) = truncChebApprox K D ((1 / 2 : ℂ) • (U + Uᴴ)) s := by
  unfold truncLaurentPoly truncChebApprox
  rw [mul_star_pow_aeval_laurentPoly K _ hU, show Finset.range (K + 1) =
      insert 0 (Finset.Icc 1 K) from
      Finset.ext fun k ↦ by simp; omega, Finset.sum_insert (by simp)]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun k hk ↦ ?_)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 :=
      ⟨k - 1, (Nat.succ_pred_eq_of_pos (Finset.mem_Icc.mp hk).1).symm⟩
  rw [(chebyshevT_half_add_star_eq hU (m + 1)).1, smul_smul]
  congr 1
  simp only [jacobiAngerLaurentCoeff]
  ring
end QuantumComputation.Specs.PhotochemistrySolution.GQSP
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy

open PhotochemistrySolution.GQSP PhotochemistrySolution.TightWalkCauchyA
  PhotochemistrySolution.TightWalkCauchyB
theorem kapteyn_scalar_rem_gen_le {E : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hBE : 5 * s ≤ E)
    (hEN : E + 60 ≤ kapteynTruncD + 1) : s ^ (kapteynTruncD + 1) /
    ((kapteynTruncD + 1).factorial : ℝ) ≤ 1 / 10 ^ 12 := by
  let N := kapteynTruncD + 1
  have h2 : (s ^ N / (N.factorial : ℝ)) * Real.exp s ≤ Real.exp (5 * s) / (4 : ℝ) ^ N := by
    rw [le_div_iff₀ (by positivity), show ((s ^ N / (N.factorial : ℝ)) * Real.exp s) * (4 : ℝ) ^ N =
        ((4 * s) ^ N / (N.factorial : ℝ)) * Real.exp s by
      rw [mul_pow]
      ring, show (5 : ℝ) * s = 4 * s + s by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right
      (Real.pow_div_factorial_le_exp (4 * s) (by positivity) N) (Real.exp_pos s).le
  exact (le_mul_of_one_le_right (div_nonneg (pow_nonneg hs0 _) (Nat.cast_nonneg _))
      (Real.one_le_exp hs0)).trans
    (h2.trans ((exp_div_four_pow_le hBE hEN).trans (by norm_num)))
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation
@[ext high] theorem qreg_ext {n k : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  congrArg QRegister.mk (Function.Embedding.ext h)
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end
noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
theorem cos_two_pi_div_two_pow_two_approx :
    |Real.cos (2 * Real.pi / (2 : ℝ) ^ 2) - 0| ≤ 0 := by
  rw [show 2 * Real.pi / (2 : ℝ) ^ 2 = Real.pi / 2 by ring, Real.cos_pi_div_two, sub_self, abs_zero]

noncomputable abbrev sinMid4 : ℝ := 382683432365 / 10 ^ 12

theorem sin_two_pi_div_two_pow_4_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 4) - sinMid4| ≤ 1 / 10 ^ 9 :=
  sin_two_pi_div_two_pow_succ_approx (by decide) (by norm_num [sinMid4]) (by norm_num)
    cos_two_pi_div_two_pow_three_approx (by norm_num [sinMid4, sqrtTwoMid, sqrtTwoRad])
    (by norm_num [sinMid4, sqrtTwoMid, sqrtTwoRad])
open scoped Fin.CommRing
theorem onRegister_sequence_local {n k : ℕ} (placement : QRegister k n) (cs : List (Circuit k)) :
    (Circuit.sequence cs).onRegister placement =
    Circuit.sequence (cs.map (Circuit.onRegister placement)) := by
  induction cs <;> simp [Circuit.sequence, *]

theorem compose_singleton_local {n k : ℕ} (r : QRegister k n) (ℓ : Fin k) :
    r.compose (QRegister.singleton ℓ) = QRegister.singleton (r ℓ) :=
  qreg_ext fun i ↦ by fin_cases i; rfl

theorem preparePhaseGradient_onRegister {n b : ℕ} (rGrad : QRegister b n) :
    preparePhaseGradient rGrad = (preparePhaseGradient (QRegister.whole b)).onRegister rGrad := by
  unfold preparePhaseGradient; rw [onRegister_sequence_local, List.map_ofFn]; congr 1; congr 1;
  funext r; dsimp only [Function.comp_apply];
  rw [Circuit.onRegister_compose, QRegister.whole_apply, compose_singleton_local]
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.QRegExt
open _root_.QRegister
open Operator Matrix
variable {n k m w : ℕ}
@[simp] theorem basisOutcomesProjector_univ (r : QRegister k n) :
    r.basisOutcomesProjector Finset.univ = (1 : Operator (2 ^ n)) := by
  ext i j; simp [QRegister.basisOutcomesProjector, Matrix.one_apply]
theorem regist_basisBits_zero_apply {k : ℕ} (i : Fin k) : basisBits k 0 i = (0 : ZMod 2) :=
  Fin.ext (by simp [basisBits, finFunctionFinEquiv])
theorem extractIndex_compose_eq_zero {m w : ℕ} (r : QRegister m n) (sub : QRegister w m)
    {g : Fin (2 ^ n)} (hg : r.extractIndex g = 0) : (r.compose sub).extractIndex g = 0 := by
  apply (basisBitsEquiv w).injective; ext i;
  change basisBits w ((r.compose sub).extractIndex g) i = basisBits w 0 i;
  rw [(basisBits_extractIdx (r.compose sub)), QRegister.compose_apply,
      ← (basisBits_extractIdx r) g (sub i), hg, regist_basisBits_zero_apply,
      regist_basisBits_zero_apply]
theorem basisOutcomeProjector_zero_mul_compose (rAnc : QRegister m n) (sub : QRegister w m) :
    rAnc.basisOutcomeProjector 0 * (rAnc.compose sub).basisOutcomeProjector 0 =
        rAnc.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  if h0 : rAnc.extractIndex i = 0 then simp [extractIndex_compose_eq_zero rAnc sub h0,
      h0] else simp [h0]
theorem basisOutcomeProjector_compose_mul_zero (rAnc : QRegister m n) (sub : QRegister w m) :
    (rAnc.compose sub).basisOutcomeProjector 0 * rAnc.basisOutcomeProjector 0 =
        rAnc.basisOutcomeProjector 0 := by
  simpa only [Matrix.conjTranspose_mul, rAnc.basisOutcomeProjector_conjTranspose,
    (rAnc.compose sub).basisOutcomeProjector_conjTranspose] using
      congrArg Matrix.conjTranspose ((basisOutcomeProjector_zero_mul_compose rAnc) sub)
end QuantumComputation.Specs.PhotochemistrySolution.QRegExt
open QuantumComputation.Specs.PhotochemistrySolution.QRegExt
open scoped ComplexOrder MatrixOrder QHLExpectation
open QuantumComputation.Specs Operator QProg Matrix HermitianMat
namespace QuantumComputation.Specs.PhotochemistrySolution
variable {Var : Type}
def CleanWorkStep [Fintype Var] [DecidableEq Var] {n w : ℕ} [NeZero (2 ^ n)] (rWork : QRegister w n)
    (U : Unitary (2 ^ n)) (p : DynamicCircuit Var n) : Prop :=
  let P₀ := rWork.basisOutcomeProjector 0
  (U.1 * P₀ = P₀ * U.1) ∧
    ∀ M : Observable (Fin (2 ^ n)),
      ∃ N : Observable (Fin (2 ^ n)),
        wp p.compile (fun _ ↦ M) = (fun _ ↦ N) ∧
          P₀ * (U.1ᴴ * M.1.1 * U.1) * P₀ = P₀ * N.1.1 * P₀
theorem CleanWorkStep.identity [Fintype Var] [DecidableEq Var] {n w : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister w n) :
    CleanWorkStep (Var := Var) rWork 1 .identity := by
  exact ⟨by simp, fun M ↦
      ⟨M, rfl,
      by simp only [Submonoid.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]⟩⟩
theorem qAssign_obs_map_mat_eq {d : ℕ} (U : Unitary d) (M : Observable (Fin d)) :
    (qAssign_obs_map U M).1.1 = U.1ᴴ * M.1.1 * U.1 := by
  simp [qAssign_obs_map, Observable.conjUnitary, Matrix.star_eq_conjTranspose]
theorem wp_circuit_constObservable [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (c : Circuit n) (M : Observable (Fin (2 ^ n))) :
    wp (DynamicCircuit.circuit c : DynamicCircuit Var n).compile (fun _ ↦ M) = fun _ ↦
    qAssign_obs_map c.eval M := by
  change wp (c.compile : QProg Var (2 ^ n)) (fun _ ↦ M) = fun _ ↦ qAssign_obs_map c.eval M
  induction c generalizing M with
  | identity => funext _; simp [qAssign_obs_map]
  | gate _ _ => rfl
  | seq c₁ c₂ ih₁ ih₂ =>
      change wp c₁.compile (wp c₂.compile (fun _ ↦ M)) = _
      rw [ih₂ M, ih₁ (qAssign_obs_map c₂.eval M)];
      exact funext fun _ ↦ qAssign_obs_map_comp c₁.eval c₂.eval M
theorem CleanWorkStep.seq [Fintype Var] [DecidableEq Var] {n w : ℕ} [NeZero (2 ^ n)]
    {rWork : QRegister w n} {U₁ U₂ : Unitary (2 ^ n)} {p₁ p₂ : DynamicCircuit Var n}
    (h₁ : CleanWorkStep rWork U₁ p₁) (h₂ : CleanWorkStep rWork U₂ p₂) : CleanWorkStep rWork (U₂ *
    U₁) (.seq p₁ p₂) := by
  have hU₁_adj : rWork.basisOutcomeProjector 0 * U₁.1ᴴ = U₁.1ᴴ * rWork.basisOutcomeProjector 0 := by
    simpa only [Matrix.conjTranspose_mul,
        rWork.basisOutcomeProjector_conjTranspose 0] using congrArg Matrix.conjTranspose h₁.1
  have hconj (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      rWork.basisOutcomeProjector 0 * (U₁.1ᴴ * A * U₁.1) * rWork.basisOutcomeProjector 0 =
        U₁.1ᴴ * (rWork.basisOutcomeProjector 0 * A * rWork.basisOutcomeProjector 0) * U₁.1 := by
    simp only [← Matrix.mul_assoc]
    rw [hU₁_adj, Matrix.mul_assoc (U₁.1ᴴ * rWork.basisOutcomeProjector 0 * A), h₁.1,
        ← Matrix.mul_assoc]
  refine
      ⟨by rw [Submonoid.coe_mul, Matrix.mul_assoc, h₁.1, ← Matrix.mul_assoc, h₂.1,
            Matrix.mul_assoc], fun M ↦ ?_⟩
  rcases h₂.2 M with ⟨N₂, hwp₂, hmat₂⟩
  rcases h₁.2 N₂ with ⟨N₁, hwp₁, hmat₁⟩
  refine ⟨N₁, ?_, ?_⟩
  · change wp p₁.compile (wp p₂.compile (fun _ ↦ M)) = (fun _ ↦ N₁)
    rw [hwp₂, hwp₁]
  · rw [show (U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1 = U₁.1ᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * U₁.1 by
      simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc], hconj, hmat₂,
          ← hconj, hmat₁]
theorem realizes_from_cleanWorkStep [Fintype Var] [DecidableEq Var] {k m w n : ℕ} [NeZero (2 ^ n)]
    (_v : Var) (rSys : QRegister k n) (rAnc : QRegister m n) (hdisj : rSys.DisjointWires rAnc)
    (sub : QRegister w m) (W : Unitary (2 ^ (k + m))) (pBody : DynamicCircuit Var n)
    (hclean : CleanWorkStep (rAnc.compose sub) ((rSys.concat rAnc hdisj).embedUnitary W) pBody) :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W pBody.compile
    := by
  intro M σ
  rcases hclean.2 M with ⟨N_body, hwp_body, hmat_body⟩
  have habsorb (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      rAnc.basisOutcomeProjector 0 * ((rAnc.compose sub).basisOutcomeProjector 0 * A *
        (rAnc.compose sub).basisOutcomeProjector 0) * rAnc.basisOutcomeProjector 0 =
        rAnc.basisOutcomeProjector 0 * A * rAnc.basisOutcomeProjector 0 := by
    rw [← Matrix.mul_assoc (rAnc.basisOutcomeProjector 0) (_ * A),
      ← Matrix.mul_assoc (rAnc.basisOutcomeProjector 0) _ A,
          (QRegExt.basisOutcomeProjector_zero_mul_compose rAnc) sub,
      Matrix.mul_assoc (rAnc.basisOutcomeProjector 0 * A),
          (QRegExt.basisOutcomeProjector_compose_mul_zero rAnc) sub]
  change (CQAssertion.restrictToZeroAncilla _ rAnc σ).1 ≤
      (CQAssertion.restrictToZeroAncilla _ rAnc σ).1
  rw [hwp_body, restrictAssertionToBasisOutcomes_univ (fun _ ↦ N_body),
      CQAssertion.restrictToZeroAncilla_coe (fun _ ↦ N_body)]
  refine le_of_eq ?_
  ext1
  change rAnc.basisOutcomeProjector 0 * (rSys.basisOutcomesProjector Finset.univ *
    (qAssign_obs_map ((rSys.concat rAnc hdisj).embedUnitary W) M).1.1 *
      (rSys.basisOutcomesProjector Finset.univ)ᴴ) * (rAnc.basisOutcomeProjector 0)ᴴ =
    rAnc.basisOutcomeProjector 0 * N_body.1.1 * (rAnc.basisOutcomeProjector 0)ᴴ
  rw [(QRegExt.basisOutcomesProjector_univ rSys), rAnc.basisOutcomeProjector_conjTranspose 0,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, qAssign_obs_map_mat_eq, ← habsorb _,
        hmat_body, habsorb]
end QuantumComputation.Specs.PhotochemistrySolution
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.OvBidir
open Polynomial Matrix ComplexConjugate PhotochemistrySolution.GQSP
theorem twist_C_mul_X_pow (a : ℂ) (m : ℕ) : twist (C a * X ^ m) = C ((-1) ^ m * a) * X ^ m := by
  ext n; rw [coeff_twist, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  split_ifs <;> simp_all [mul_comm]
theorem conjRev_C_mul_X_pow {N m : ℕ} (hm : m ≤ N) (a : ℂ) : conjRev N (C a * X ^ m) = C (conj a) *
    X ^ (N - m) := by rw [conjRev_C_mul, conjRev_X_pow hm]
theorem twist_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) : twist (∑ i ∈ s, f i) = ∑ i ∈ s,
    twist (f i) := by
  classical
  induction s using Finset.induction_on <;> simp [twist, *]
theorem conjRev_sum (N : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) : conjRev N (∑ i ∈ s, f i) =
    ∑ i ∈ s, conjRev N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conjRev]
  | insert _ _ ha ih => simp [ha, conjRev_add, ih]
theorem twist_laurentPoly {K : ℕ} (hK : Odd K) {c : ℕ → ℂ} (hc : ∀ k, conj (c k) = (-1) ^ k * c k) :
    twist (laurentPoly K c) = -conjRev (2 * K) (laurentPoly K c) := by
  have hKs : (-1 : ℂ) ^ K = -1 := hK.neg_one_pow; unfold laurentPoly
  rw [twist_add, conjRev_add, twist_sum, conjRev_sum, twist_C_mul_X_pow,
    conjRev_C_mul_X_pow (by omega), hc, hKs, show 2 * K - K = K by omega, neg_add,
    ← Finset.sum_neg_distrib]
  congr 1
  · simp only [pow_zero, one_mul, map_neg, neg_mul]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_Icc] at hk
    rw [mul_add, twist_add, conjRev_add, twist_C_mul_X_pow, twist_C_mul_X_pow,
      conjRev_C_mul_X_pow (by omega), conjRev_C_mul_X_pow (by omega), hc,
      show 2 * K - (K + k) = K - k by omega, show 2 * K - (K - k) = K + k by omega,
      pow_add, hKs]
    have hsub : (-1 : ℂ) ^ (K - k) = -(-1) ^ k := by
      have h2 : (-1 : ℂ) ^ (K - k) * (-1) ^ k = -1 := by
        rw [← pow_add, Nat.sub_add_cancel hk.2, hKs]
      have h3 : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination (-1 : ℂ) ^ k * h2 - (-1 : ℂ) ^ (K - k) * h3
    rw [hsub]; simp only [map_neg, map_mul, neg_mul, one_mul]; ring
theorem chebPowCoeff_conj_and_parity :
    ∀ j k : ℕ, conj (chebPowCoeff j k) = chebPowCoeff j k ∧
      (Odd (j + k) → chebPowCoeff j k = 0)
  | 0, 0 => by simp [chebPowCoeff]
  | 0, k + 1 => by simp [chebPowCoeff]
  | j + 1, 0 => by
    obtain ⟨h1, h2⟩ := chebPowCoeff_conj_and_parity j 1
    exact ⟨by simp [chebPowCoeff, chebStep, map_div₀, map_ofNat, h1],
      fun ho ↦ by simp [chebPowCoeff, chebStep, h2 (by simpa [Nat.add_comm] using ho)]⟩
  | j + 1, 1 =>
    let ⟨h0, h0'⟩ := chebPowCoeff_conj_and_parity j 0
    let ⟨h2, h2'⟩ := chebPowCoeff_conj_and_parity j 2
    ⟨by simp [chebPowCoeff, chebStep, map_div₀, map_ofNat, h0, h2],
      fun ⟨t, ht⟩ ↦ by simp [chebPowCoeff, chebStep, h0' ⟨t - 1, by omega⟩, h2' ⟨t, by omega⟩]⟩
  | j + 1, k + 2 =>
    let ⟨ha, ha'⟩ := chebPowCoeff_conj_and_parity j (k + 1)
    let ⟨hb, hb'⟩ := chebPowCoeff_conj_and_parity j (k + 3)
    ⟨by simp [chebPowCoeff, chebStep, map_div₀, map_ofNat, ha, hb],
      fun ⟨t, ht⟩ ↦ by simp [chebPowCoeff, chebStep, ha' ⟨t - 1, by omega⟩, hb' ⟨t, by omega⟩]⟩
theorem conj_jacobiAngerTruncCoeff (D : ℕ) (s : ℝ) (k : ℕ) : conj (jacobiAngerTruncCoeff D s k) =
    (-1) ^ k * jacobiAngerTruncCoeff D s k := by
  unfold jacobiAngerTruncCoeff; rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  obtain ⟨hre, hpar⟩ := chebPowCoeff_conj_and_parity j k
  rcases Nat.even_or_odd (j + k) with he | ho
  · have h1 : (-1 : ℂ) ^ j * (-1 : ℂ) ^ k = 1 := by rw [← pow_add, he.neg_one_pow]
    have h2 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hjk : (-1 : ℂ) ^ j = (-1 : ℂ) ^ k := by
      linear_combination (-1 : ℂ) ^ k * h1 - (-1 : ℂ) ^ j * h2
    have hI : conj ((-Complex.I * (s : ℂ)) ^ j) = (-1) ^ j * (-Complex.I * (s : ℂ)) ^ j := by
      rw [map_pow, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, ← mul_pow]; congr 1; ring
    rw [map_mul, map_div₀, hI, map_natCast, hre, ← hjk]; ring
  · rw [hpar ho, mul_zero, map_zero, mul_zero]
theorem conj_jacobiAngerLaurentCoeff (D : ℕ) (s : ℝ)
    (k : ℕ) : conj (jacobiAngerLaurentCoeff D s k) = (-1) ^ k * jacobiAngerLaurentCoeff D s k := by
  rcases k with _ | k
  · simpa [jacobiAngerLaurentCoeff] using conj_jacobiAngerTruncCoeff D s 0
  · simp only [jacobiAngerLaurentCoeff, map_mul, map_div₀, map_one, map_ofNat,
        conj_jacobiAngerTruncCoeff]; ring
end QuantumComputation.Specs.PhotochemistrySolution.OvBidir

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PrimitiveGate
/-- Strict WHNF `Bool` binder (`0` DAG zeta-expansion blowup in `rfl`). -/
def letB {α : Type} : Bool → (Bool → α) → α
  | true, fn => fn true
  | false, fn => fn false
@[simp] theorem letB_eq {α : Type} : ∀ (b : Bool) (fn : Bool → α), letB b fn = fn b
  | true, _ => rfl
  | false, _ => rfl
/-- Coin wire mask `1 <<< (1 + j)`. -/
def coinW (j : ℕ) : ℕ := 1 <<< (1 + j)
/-- Output wire `q` of a prior block mask list. -/
def outW (gouts : List ℕ) (q : ℕ) : ℕ := gouts.getD q 0
/-- Pack a list of `Bool`s LSB-first using pure `cond` (`0` `Decidable` synthesis). -/
def packBools : List Bool → ℕ
  | [] => 0
  | b :: bs => cond b 1 0 + 2 * packBools bs
open PhotochemistrySolution.ZeroNEremSpec
/-- Monomorphic `Bool` equality (`0` `Decidable` synthesis). -/
def b2BEq (a b : Bool) : Bool := cond a b (Bool.not b)
theorem b2_bEq_iff (a b : Bool) : b2BEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [b2BEq]
/-- Extract `[vv.testBit sh, ..., vv.testBit (sh + kv - 1)]`. -/
def b2PackSlice (vv sh : ℕ) : ℕ → List Bool
  | 0 => []
  | kv + 1 => vv.testBit sh :: b2PackSlice vv (sh + 1) kv
theorem b2_packBools_append :
    ∀ xs ys : List Bool, packBools (xs ++ ys) = packBools xs + 2 ^ xs.length * packBools ys
  | [], _ => by simp [packBools]
  | _ :: xs, ys => by
      dsimp only [List.cons_append, packBools, List.length_cons]; rw [b2_packBools_append xs ys];
      ring
theorem b2_mod_two_mul (qv mv : ℕ) (hm : 0 < mv) : qv % 2 + 2 * ((qv / 2) % mv) = qv % (2 * mv)
    := by
  have := Nat.mod_lt (qv / 2) hm
  conv_rhs => rw [show qv = (qv % 2 + 2 * ((qv / 2) % mv)) + (2 * mv) * ((qv / 2) / mv) by
    nlinarith [Nat.div_add_mod qv 2, Nat.div_add_mod (qv / 2) mv]]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show qv % 2 + 2 * ((qv / 2) % mv) < 2 *
      mv by omega)]
theorem b2_packBools_slice (vv : ℕ) :
    ∀ (kv sh : ℕ), packBools (b2PackSlice vv sh kv) = (vv / 2 ^ sh) % 2 ^ kv
  | 0, sh => by simp [b2PackSlice, packBools, pow_zero, Nat.mod_one]
  | kv + 1, sh => by
      dsimp only [b2PackSlice, packBools]
      rw [b2_packBools_slice vv kv (sh + 1)]
      have hBit : cond (vv.testBit sh) 1 0 = (vv / 2 ^ sh) % 2 := by
        rw [show vv.testBit sh =
            (vv / 2 ^ sh).testBit 0 by rw [Nat.testBit_div_two_pow, Nat.zero_add], Nat.testBit_zero]
        rcases (show (vv / 2 ^ sh) % 2 = 0 ∨ (vv / 2 ^ sh) % 2 = 1 by omega) with h | h <;>
            rw [h] <;> rfl
      rw [hBit, show vv / 2 ^ (sh + 1) = (vv / 2 ^ sh) /
          2 by rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul],
        show 2 ^ (kv + 1) = 2 * 2 ^ kv by ring]
      exact b2_mod_two_mul (vv / 2 ^ sh) (2 ^ kv) (Nat.two_pow_pos kv)
theorem b2_testBit_mod_pow (av kv iv : ℕ) (hi : iv < kv) : (av % 2 ^ kv).testBit iv =
    av.testBit iv := by rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end

noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 8192
section
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
theorem pgOpNorm_conjTranspose_mul_self {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    pgOpNorm (Aᴴ * A) = pgOpNorm A * pgOpNorm A := Matrix.l2_opNorm_conjTranspose_mul_self A
theorem pgOpNorm_unitary_le_one {I : Type*} [Fintype I] [DecidableEq I] (U : 𝐔[I]) : pgOpNorm U.1 ≤
    1 := by
  rcases isEmpty_or_nonempty I with hI | hI
  · simp [Subsingleton.elim U.1 0, pgOpNorm]
  · nlinarith [pgOpNorm_nonneg U.1, show pgOpNorm U.1 * pgOpNorm U.1 = 1 by
      rw [← pgOpNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose, U.2.1]
      exact (norm_one : ‖(1 : Matrix I I ℂ)‖ = 1)]

@[simp] theorem pgL2Norm_unitary_mulVec {I : Type*} [Fintype I] [DecidableEq I]
    (U : 𝐔[I]) (v : I → ℂ) :
    pgL2Norm (U.1 *ᵥ v) = pgL2Norm v := by
  have hle (V : 𝐔[I]) (w : I → ℂ) : pgL2Norm (V.1 *ᵥ w) ≤ pgL2Norm w :=
    (pgL2Norm_mulVec_le V.1 w).trans (mul_le_of_le_one_left (pgL2Norm_nonneg w)
        (pgOpNorm_unitary_le_one V))
  exact le_antisymm (hle U v) (by
    simpa [Matrix.mulVec_mulVec, ← Submonoid.coe_mul] using hle U⁻¹ (U.1 *ᵥ v))

theorem pgL2Norm_tensorState {n k : ℕ} (r : QRegister k n) (u : Fin (2 ^ k) → ℂ)
    (w : (r.Environment → ZMod 2) → ℂ) : pgL2Norm (r.tensorState u w) = pgL2Norm u *
    pgL2Norm w := by
  have hnonneg_lhs : 0 ≤ pgL2Norm (r.tensorState u w) := pgL2Norm_nonneg _;
  have hnonneg_rhs : 0 ≤ pgL2Norm u * pgL2Norm w :=
      mul_nonneg (pgL2Norm_nonneg u) (pgL2Norm_nonneg w); rw [← sq_eq_sq₀ hnonneg_lhs hnonneg_rhs,
      mul_pow, pgL2Norm_sq, pgL2Norm_sq, pgL2Norm_sq, Finset.sum_mul_sum]
  rw [← r.basisSplitEquiv.symm.sum_comp (fun global ↦ ‖r.tensorState u w global‖ ^ 2),
      Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun loc _ ↦ Finset.sum_congr rfl fun env _ ↦ ?_
  have hloc : r.extractIndex (r.basisSplitEquiv.symm (loc, env)) = loc := by
    rw [← r.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  simp [QRegister.tensorState, hloc, mul_pow]

theorem pgL2Norm_tensorState_sub_left {n k : ℕ} (r : QRegister k n) (u₁ u₂ : Fin (2 ^ k) → ℂ)
    (w : (r.Environment → ZMod 2) → ℂ) : pgL2Norm (r.tensorState u₁ w - r.tensorState u₂ w) =
    pgL2Norm (u₁ - u₂) * pgL2Norm w := by rw [← r.tensorState_sub_left, pgL2Norm_tensorState]
theorem pgProdState_smul (n : ℕ) (c : Fin n → ℂ) (v : Fin n → (ZMod 2 → ℂ)) :
    QFT.prodState n (fun k ↦ c k • v k) = (∏ k : Fin n, c k) • QFT.prodState n v := by
  funext j; simp [QFT.prodState, Finset.prod_mul_distrib]
theorem pgL2Norm_prodState (n : ℕ) (v : Fin n → (ZMod 2 → ℂ)) : pgL2Norm (QFT.prodState n v) = ∏ k :
    Fin n, pgL2Norm (v k) := by
  rw [← sq_eq_sq₀ (pgL2Norm_nonneg _) (Finset.prod_nonneg fun k _ ↦ pgL2Norm_nonneg (v k)),
    ← Finset.prod_pow, pgL2Norm_sq]
  simp_rw [pgL2Norm_sq]
  rw [Fintype.prod_sum, ← (basisBitsEquiv n).symm.sum_comp (fun j ↦ ‖QFT.prodState n v j‖ ^ 2)]
  exact Finset.sum_congr rfl fun b _ ↦ by
    simp [QFT.prodState, (basisBitsEquiv n).apply_symm_apply b, norm_prod, Finset.prod_pow]
@[simp] theorem pgL2Norm_plusPhase (θ : ℝ) : pgL2Norm (QFT.plusPhase θ) = 1 := by
  have hnorm (b : ZMod 2) : ‖QFT.plusPhase θ b‖ ^ 2 = 1 / 2 := by
    unfold QFT.plusPhase
    rw [norm_mul, show (2 * Real.pi * Complex.I * (θ * (b.val : ℝ) : ℂ)) =
      ((2 * Real.pi * (θ * b.val) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [pgL2Norm_nonneg (QFT.plusPhase θ),
    show pgL2Norm (QFT.plusPhase θ) ^ 2 = 1 by simp [pgL2Norm_sq, hnorm, Finset.sum_const]]

theorem sq_linear_le_self {r r₀ εr c c₀ εc s s₀ εs : ℝ} (A B C D : ℝ)
    (hr : |r - r₀| ≤ εr) (hc : |c - c₀| ≤ εc) (hs : |s - s₀| ≤ εs) :
    (A + B * r + C * c + D * s) ^ 2 ≤
      (|A + B * r₀ + C * c₀ + D * s₀| + |B| * εr + |C| * εc + |D| * εs) ^ 2 := by
  let m0 := A + B * r₀ + C * c₀ + D * s₀
  have h1 := abs_add_le (m0 + B * (r - r₀) + C * (c - c₀)) (D * (s - s₀))
  have h2 := abs_add_le (m0 + B * (r - r₀)) (C * (c - c₀))
  have h3 := abs_add_le m0 (B * (r - r₀))
  rw [abs_mul] at h1 h2 h3
  rw [← sq_abs (A + B * r + C * c + D * s)]
  nlinarith [abs_nonneg (A + B * r + C * c + D * s), show |A + B * r + C * c + D * s| ≤
      |m0| + |B| * εr + |C| * εc + |D| * εs by
    rw [show A + B * r + C * c + D * s = m0 + B * (r - r₀) + C * (c - c₀) + D *
        (s - s₀) by dsimp [m0]; ring]
    linarith [mul_le_mul_of_nonneg_left hr (abs_nonneg B),
      mul_le_mul_of_nonneg_left hc (abs_nonneg C), mul_le_mul_of_nonneg_left hs (abs_nonneg D)]]
theorem basisBits_one_one : basisBits 1 1 0 = 1 := by decide

theorem plusPhase_neg_inv_two_pow_zero (j : ℕ) : QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j)
    (basisBits 1 0 0) = (1 / Real.sqrt 2 : ℂ) := by rw [basisBits_one_zero]; simp [QFT.plusPhase]
theorem plusPhase_neg_inv_two_pow_one (j : ℕ) : QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j)
    (basisBits 1 1 0) = (1 / Real.sqrt 2 : ℂ) * ((Real.cos (2 * Real.pi / (2 : ℝ) ^ j) : ℂ) -
    (Real.sin (2 * Real.pi / (2 : ℝ) ^ j) : ℂ) * Complex.I) := by
  rw [basisBits_one_one]; unfold QFT.plusPhase; congr 1
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((-(1 : ℝ) / (2 : ℝ) ^ j : ℝ) *
      (((1 : ZMod 2).val : ℝ) : ℂ)) = ((-(2 * Real.pi / (2 : ℝ) ^ j) : ℝ) : ℂ) *
      Complex.I := by rw [ZMod.val_one]; push_cast; ring
  rw [harg, Complex.exp_mul_I]; push_cast; rw [Complex.cos_neg, Complex.sin_neg]; ring
theorem cyclotomicState_approx_plusPhase (s : CyclotomicState) (m j : ℕ)
    (hk : s.k = 2 * m + 1) (cα sα c₀ εc s₀ εs δ : ℝ)
    (hδ : 0 ≤ δ) (hα : cα ^ 2 + sα ^ 2 = 1)
    (hc : |Real.cos (2 * Real.pi / (2 : ℝ) ^ j) - c₀| ≤ εc)
    (hs : |Real.sin (2 * Real.pi / (2 : ℝ) ^ j) - s₀| ≤ εs)
    (h_num :
      (|((s.u.a : ℝ) / (2 : ℝ) ^ m - cα) +
          ((s.u.b - s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid| +
        |((s.u.b - s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad) ^ 2 +
      (|((s.u.c : ℝ) / (2 : ℝ) ^ m - sα) +
          ((s.u.b + s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid| +
        |((s.u.b + s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad) ^ 2 +
      (|(s.v.a : ℝ) / (2 : ℝ) ^ m +
          ((s.v.b - s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid +
          (-cα) * c₀ + (-sα) * s₀| +
        |((s.v.b - s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad +
        |(-cα)| * εc + |(-sα)| * εs) ^ 2 +
      (|(s.v.c : ℝ) / (2 : ℝ) ^ m +
          ((s.v.b + s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid +
          (-sα) * c₀ + cα * s₀| +
        |((s.v.b + s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad +
        |(-sα)| * εc + |cα| * εs) ^ 2 ≤
      2 * δ ^ 2) :
    ∃ α : ℝ, ‖WithLp.toLp 2 (s.toStateVector -
      Complex.exp (α * Complex.I) •
        (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j) (basisBits 1 i 0)))‖ ≤ δ := by
  obtain ⟨α, hα_exp⟩ := exists_exp_mul_I_eq_of_sq_add_sq_eq_one cα sα hα
  refine ⟨α, hα_exp ▸ l2Norm_one_qubit_le hδ ?_⟩
  let r2 : ℂ := (1 / Real.sqrt 2 : ℂ)
  let cI : ℂ := (cα : ℂ) + (sα : ℂ) * Complex.I
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv_re : r2.re = Real.sqrt 2 / 2 := by
    rw [show r2 = (Real.sqrt 2 : ℂ)⁻¹ from one_div _, Complex.inv_re, Complex.ofReal_re,
        Complex.normSq_ofReal, ← sq, h2]
  have hinv_im : r2.im = 0 := by simp [r2]
  have hpow : r2 ^ s.k = r2 * ((1 / (2 : ℝ) ^ m : ℝ) : ℂ) := by
    rw [hk, pow_succ', pow_mul, show r2 ^ 2 =
        (1 / 2 : ℝ) by dsimp only [r2]; rw [div_pow, _root_.one_pow]; norm_cast; rw [h2]]
    simp [one_div]
  have hpow_re : (r2 ^ s.k).re = Real.sqrt 2 / 2 * (1 / (2 : ℝ) ^ m) := by
    rw [hpow, Complex.mul_re, hinv_re, hinv_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hpow_im : (r2 ^ s.k).im = 0 := by
    rw [hpow, Complex.mul_im, hinv_re, hinv_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  let v : StateVector 1 := s.toStateVector - cI • fun i : Fin (2 ^ 1) ↦
      QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j) (basisBits 1 i 0)
  have hre (w : CyclotomicEight) (C S : ℝ) :
      Real.sqrt 2 * (r2 ^ s.k * w.toComplex - cI * (r2 * ((C : ℂ) - (S : ℂ) * Complex.I))).re =
      (w.a : ℝ) / (2 : ℝ) ^ m + ((w.b - w.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * Real.sqrt 2 + (-cα) *
          C + (-sα) * S := by
    simp only [cI, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, hpow_re, hpow_im, hinv_re,
          hinv_im, CyclotomicEight.toComplex_re, CyclotomicEight.toComplex_im, pow_succ]
    linear_combination ((w.a : ℝ) / ((2 : ℝ) ^ m * 2) + ((w.b - w.d : ℤ) : ℝ) / ((2 : ℝ) ^ m * 4) *
        Real.sqrt 2 - cα * C / 2 - sα * S / 2) * h2
  have him (w : CyclotomicEight) (C S : ℝ) :
      Real.sqrt 2 * (r2 ^ s.k * w.toComplex - cI * (r2 * ((C : ℂ) - (S : ℂ) * Complex.I))).im =
      (w.c : ℝ) / (2 : ℝ) ^ m + ((w.b + w.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * Real.sqrt 2 + (-sα) *
          C + cα * S := by
    simp only [cI, Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, hpow_re, hpow_im, hinv_re,
          hinv_im, CyclotomicEight.toComplex_re, CyclotomicEight.toComplex_im, pow_succ]
    linear_combination ((w.c : ℝ) / ((2 : ℝ) ^ m * 2) + ((w.b + w.d : ℤ) : ℝ) / ((2 : ℝ) ^ m * 4) *
        Real.sqrt 2 - sα * C / 2 + cα * S / 2) * h2
  have hv0 : v 0 = r2 ^ s.k * s.u.toComplex - cI * (r2 * (((1 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) *
      Complex.I)) := by
    simp only [v, r2, cI, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CyclotomicState.toStateVector,
        Fin.val_zero, ↓reduceIte, plusPhase_neg_inv_two_pow_zero, Complex.ofReal_one,
        Complex.ofReal_zero, zero_mul, sub_zero, mul_one]
  have hv1 : v 1 = r2 ^ s.k * s.v.toComplex - cI *
      (r2 * ((Real.cos (2 * Real.pi / (2 : ℝ) ^ j) : ℂ) -
      (Real.sin (2 * Real.pi / (2 : ℝ) ^ j) : ℂ) * Complex.I)) := by
    simp only [v, r2, cI, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CyclotomicState.toStateVector,
        Fin.val_one, one_ne_zero, ↓reduceIte, plusPhase_neg_inv_two_pow_one]
  have hv0_re : Real.sqrt 2 * (v 0).re = ((s.u.a : ℝ) / (2 : ℝ) ^ m - cα) +
      ((s.u.b - s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * Real.sqrt 2 := by rw [hv0, hre]; ring
  have hv0_im : Real.sqrt 2 * (v 0).im = ((s.u.c : ℝ) / (2 : ℝ) ^ m - sα) +
      ((s.u.b + s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * Real.sqrt 2 := by rw [hv0, him]; ring
  change 2 * ((v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2) ≤ 2 * δ ^ 2
  rw [show 2 * ((v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2) =
      (Real.sqrt 2 * (v 0).re) ^ 2 + (Real.sqrt 2 * (v 0).im) ^ 2 + (Real.sqrt 2 * (v 1).re) ^ 2 +
          (Real.sqrt 2 * (v 1).im) ^ 2 by
    linear_combination -((v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2) * h2, hv0_re,
        hv0_im, hv1, hre, him]
  have hb0 :=
      sq_linear_le_self ((s.u.a : ℝ) / (2 : ℝ) ^ m - cα)
      (((s.u.b - s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)) 0 0 abs_sqrt_two_sub_le hc hs
  have hb1 :=
      sq_linear_le_self ((s.u.c : ℝ) / (2 : ℝ) ^ m - sα)
      (((s.u.b + s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)) 0 0 abs_sqrt_two_sub_le hc hs
  simp only [zero_mul, add_zero, abs_zero] at hb0 hb1
  linarith [sq_linear_le_self ((s.v.a : ℝ) / (2 : ℝ) ^ m)
      (((s.v.b - s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)) (-cα) (-sα) abs_sqrt_two_sub_le hc hs,
    sq_linear_le_self ((s.v.c : ℝ) / (2 : ℝ) ^ m) (((s.v.b + s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1))
        (-sα) cα abs_sqrt_two_sub_le hc hs]
end
end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec

noncomputable section
set_option exponentiation.threshold 8192
section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator Matrix QProg HermitianMat
namespace QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.DynamicCircuit
variable {Var : Type} {n : ℕ}
@[simp] theorem compile_circuit_loc (c : Circuit n) : (circuit (Var := Var) c).compile =
    c.compile := rfl
end QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.Circuit
variable {n : ℕ}
def andCompute_loc (control₁ control₂ ancilla : Wire n) (_h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) : Circuit n :=
  Circuit.H ancilla ;;ᶜ
  Circuit.T ancilla ;;ᶜ
  Circuit.CNOT control₂ ancilla h₂a ;;ᶜ
  (Circuit.T ancilla).inverse ;;ᶜ
  Circuit.CNOT control₁ ancilla h₁a ;;ᶜ
  Circuit.T ancilla ;;ᶜ
  Circuit.CNOT control₂ ancilla h₂a ;;ᶜ
  (Circuit.T ancilla).inverse ;;ᶜ
  Circuit.CNOT control₁ ancilla h₁a ;;ᶜ
  Circuit.H ancilla ;;ᶜ
  Circuit.S ancilla
def andUncomputeFixup_loc (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂) :
    Circuit n :=
  Circuit.X ancilla ;;ᶜ
  Circuit.H control₂ ;;ᶜ
  Circuit.CNOT control₁ control₂ h₁₂ ;;ᶜ
  Circuit.H control₂
@[simp] theorem support_andCompute_loc (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).support = {control₁, control₂, ancilla}
        := by
  ext q;
  simp only [andCompute_loc, support_seq, support_inverse, support_single, support_cnot,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
@[simp] theorem support_andUncomputeFixup (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    (andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).support = {control₁, control₂, ancilla}
        := by
  ext q;
  simp only [andUncomputeFixup_loc, support_seq, support_single, support_cnot, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]; tauto
@[simp] theorem count_andCompute_t_loc (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).count .T = 4 := by
  simp [andCompute_loc, Circuit.H, Circuit.T, Circuit.S, Circuit.CNOT, Circuit.inverse,
      Circuit.inverseGate, Circuit.sequence]
@[simp] theorem count_andCompute_toff_loc (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).count .TOFF = 0 := by
  simp [andCompute_loc, Circuit.H, Circuit.T, Circuit.S, Circuit.CNOT, Circuit.inverse,
      Circuit.inverseGate, Circuit.sequence]
@[simp] theorem count_andUncomputeFixup_t (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    (andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).count .T = 0 := by
  simp [andUncomputeFixup_loc, Circuit.X, Circuit.H, Circuit.CNOT]
@[simp] theorem count_andUncomputeFixup_toff (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    (andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).count .TOFF = 0 := by
  simp [andUncomputeFixup_loc, Circuit.X, Circuit.H, Circuit.CNOT]
end QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.DynamicCircuit
variable {Var : Type} {n : ℕ}
def andUncompute_loc (v : Var) (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂)
    (_h₁a : control₁ ≠ ancilla) (_h₂a : control₂ ≠ ancilla) : DynamicCircuit Var n :=
    .seq (.circuit (Circuit.H ancilla)) (.seq (.measure v (QRegister.singleton ancilla))
    (.qIf (fun σ ↦ σ v = 1)
    (.circuit (CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂)) .identity))
@[simp] theorem count_andUncompute_t_loc (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).count .T = 0 := by
  simp [andUncompute_loc, DynamicCircuit.identity, Circuit.H]
@[simp] theorem count_andUncompute_toff_loc (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).count .TOFF = 0 := by
  simp [andUncompute_loc, DynamicCircuit.identity, Circuit.H]
variable [Fintype Var] [DecidableEq Var]
noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
    basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm β) = β :=
  (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j :=
  (basisBitsEquiv q).symm_apply_apply j
theorem single_eq_ket (g : Fin (2 ^ n)) : (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g)
    := by simp [ket, basisState]
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j;
  have :=
      congrFun (h (basisBits n j)) i; simpa [← single_eq_ket, Matrix.mulVec_single_one] using this
noncomputable def writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    BitAssignment n :=
    basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegExt.basisBits_replaceIdx_apply]
theorem writeReg_apply_of_not_mem {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegExt.basisBits_replaceIdx_of_not_mem _ _ _ _ hw]
theorem writeReg_eq_update {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) : writeReg β r γ = Function.update β (r i₀)
        (γ i₀) :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.writeReg_eq_update β r γ i₀ hγ
noncomputable abbrev localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
    (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {k : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k))
    (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) = ∑ l : Fin (2 ^ k),
        A l (localIdx r β) • ket (writeReg β r (basisBits k l)) :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.embedMatrix_mulVec_ket r A β
theorem embedMatrix_permMatrix_mulVec_ket {k : ℕ} (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) : (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
    ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · exact fun l _ hl ↦ by simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      show σ l ≠ localIdx r β from fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])]
  · simp
theorem gad_singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
    A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
    A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hloc : localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 :=
    (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b =
          0 then 0 else 1) (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b :=
    (writeReg_eq_update _ _ _ 0 fun i hi ↦ absurd (Subsingleton.elim i 0) hi).trans (hb ▸ rfl)
  erw [embedMatrix_mulVec_ket, hloc, Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
abbrev gad_bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
abbrev gad_bitPhaseI (b : ZMod 2) : ℂ := if b = 0 then 1 else Complex.I
noncomputable def gad_omega8 : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
noncomputable abbrev gad_bitPhaseT (b : ZMod 2) : ℂ := if b = 0 then 1 else gad_omega8
noncomputable abbrev gad_bitPhaseTInv (b : ZMod 2) : ℂ :=
    gad_bitSign b * gad_bitPhaseI b * gad_bitPhaseT b
noncomputable def gad_sqrtHalf : ℂ := (Real.sqrt (1 / 2) : ℝ)
theorem gad_sqrtHalf_mul_sqrtHalf : gad_sqrtHalf * gad_sqrtHalf = 1 / 2 := by
  rw [gad_sqrtHalf, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
theorem gad_sqrtHalf_sq : gad_sqrtHalf ^ 2 = 1 / 2 := by
  linear_combination gad_sqrtHalf_mul_sqrtHalf
theorem gad_star_sqrtHalf : star gad_sqrtHalf = gad_sqrtHalf := by
  dsimp [gad_sqrtHalf]; exact Complex.conj_ofReal _
theorem gad_omega8_mul_omega8 : gad_omega8 * gad_omega8 = Complex.I := by
  dsimp [gad_omega8]
  rw [div_mul_div_comm, show (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) =
      2 from mod_cast Real.mul_self_sqrt (by norm_num)]
  linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
theorem gad_omega8_sq : gad_omega8 ^ 2 = Complex.I := by linear_combination gad_omega8_mul_omega8
theorem gad_omega8_pow_four : gad_omega8 ^ 4 = -1 := by
  linear_combination (gad_omega8 ^ 2 + Complex.I) * gad_omega8_mul_omega8 + Complex.I_mul_I
theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b
theorem gad_one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl
theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]; rfl
theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.ket_X q β
theorem gad_ket_diag2 (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h00 : A 0 0 = 1) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
        (if β q = 0 then 1 else A 1 1) • ket β := by
  rw [gad_singleton_embedMatrix_mulVec_ket]
  exact (bit_cases (β q)).elim
    (fun hb ↦
        by simp [hb, h00, h10,
             (congrArg (Function.update β q) hb.symm).trans (Function.update_eq_self q β)])
    (fun hb ↦
        by simp [hb, h01,
             (congrArg (Function.update β q) hb.symm).trans (Function.update_eq_self q β)])
theorem gad_ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = gad_bitSign (β q) • ket β := by
  erw [Circuit.eval_single, PrimitiveGate.eval]; exact gad_ket_diag2 q _ rfl rfl rfl β
theorem gad_ket_S (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) = gad_bitPhaseI (β q) • ket β := by
  erw [Circuit.eval_single, PrimitiveGate.eval]; exact gad_ket_diag2 q _ rfl rfl rfl β
theorem gad_ket_T (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket β) = gad_bitPhaseT (β q) • ket β := by
  erw [Circuit.eval_single, PrimitiveGate.eval]; exact gad_ket_diag2 q _ rfl rfl rfl β
theorem gad_ket_T_inv (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).inverse.eval.1.mulVec (ket β) = gad_bitPhaseTInv (β q) • ket β := by
  change (Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity))).eval.1.mulVec (ket β) = _
  simp only [eval_seq_mulVec, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
      gad_ket_T, gad_ket_S, gad_ket_Z, Matrix.mulVec_smul, smul_smul,
      gad_bitPhaseTInv]; congr 1; ring
theorem gad_ket_H (q : Wire n) (β : BitAssignment n) : (Circuit.H q).eval.1.mulVec (ket β) =
    gad_sqrtHalf • (ket (Function.update β q 0) + gad_bitSign (β q) • ket (Function.update β q 1))
    := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  erw [gad_singleton_embedMatrix_mulVec_ket q ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1]) β]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, gad_sqrtHalf, smul_add, Complex.real_smul]
theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.ket_CNOT c t h β
theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      ket (Function.update β t (β t + β c₁ * β c₂)) :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t β
theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) = if β q =
        0 then ket β else 0 :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.ket_projector_zero q β
theorem ket_projector_one (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) = if β q =
        1 then ket β else 0 :=
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld.ket_projector_one q β
noncomputable def gad_phase4T (c₁ c₂ a : ZMod 2) : ℂ :=
    gad_bitPhaseT (a + c₂ + c₁) * gad_bitPhaseTInv (a + c₂) * gad_bitPhaseT a *
    gad_bitPhaseTInv (a + c₁)
theorem gad_phase4T_eq (c₁ c₂ a : ZMod 2) : gad_phase4T c₁ c₂ a = if c₁ * c₂ = 0 then 1 else if a =
    0 then -Complex.I else Complex.I := by
  rcases bit_cases c₁ with rfl | rfl <;> rcases bit_cases c₂ with rfl | rfl <;>
      rcases bit_cases a with rfl | rfl <;>
    simp only [gad_phase4T, gad_bitPhaseT, gad_bitPhaseTInv, gad_bitSign,
      gad_bitPhaseI, gad_one_add_one_zmod2, add_zero, zero_add, mul_zero, mul_one, one_ne_zero,
          ↓reduceIte] <;>
    (ring_nf; simp only [gad_omega8_sq, gad_omega8_pow_four, Complex.I_sq,
        Complex.I_mul_I]; try ring1)
theorem gad_tempAnd_Combine (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) :
    gad_sqrtHalf • (gad_phase4T c₁ c₂ 0 • (gad_sqrtHalf • (ψ₀ + gad_bitPhaseI 1 • ψ₁)) +
    gad_phase4T c₁ c₂ 1 • (gad_sqrtHalf • (ψ₀ + gad_bitSign 1 • gad_bitPhaseI 1 • ψ₁))) = if c₁ *
    c₂ = 0 then ψ₀ else ψ₁ := by
  rw [gad_phase4T_eq c₁ c₂ 0, gad_phase4T_eq c₁ c₂ 1]
  rcases bit_cases (c₁ * c₂) with h | h <;>
    simp only [h, gad_bitPhaseI, gad_bitSign, one_ne_zero, ↓reduceIte, smul_add, smul_smul] <;>
    match_scalars <;> first | ring1 | (ring_nf; simp only [gad_sqrtHalf_sq, Complex.I_sq]; ring1)
theorem gad_cz_Combine (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) :
    gad_sqrtHalf • (gad_sqrtHalf • (ψ₀ + gad_bitSign c₁ • ψ₁) +
    gad_bitSign c₂ • (gad_sqrtHalf • (ψ₀ + gad_bitSign (1 + c₁) • ψ₁))) = gad_bitSign (c₁ *
    c₂) • (if c₂ = 0 then ψ₀ else ψ₁) := by
  rcases bit_cases c₁ with rfl | rfl <;> rcases bit_cases c₂ with rfl | rfl <;>
    simp only [gad_bitSign, gad_one_add_one_zmod2, add_zero, mul_zero, mul_one,
      one_ne_zero, ↓reduceIte, smul_add, smul_smul] <;>
    match_scalars <;> first | ring1 | (ring_nf; simp only [gad_sqrtHalf_sq]; ring1)
theorem gad_jonesPhaseStep_mulVec_ket
    (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (rest : Circuit n) (β : BitAssignment n) :
    (Circuit.T anc ;;ᶜ
      Circuit.CNOT c₂ anc h₂a ;;ᶜ
      (Circuit.T anc).inverse ;;ᶜ
      Circuit.CNOT c₁ anc h₁a ;;ᶜ
      Circuit.T anc ;;ᶜ
      Circuit.CNOT c₂ anc h₂a ;;ᶜ
      (Circuit.T anc).inverse ;;ᶜ
      Circuit.CNOT c₁ anc h₁a ;;ᶜ
      rest).eval.1.mulVec (ket β) =
      gad_phase4T (β c₁) (β c₂) (β anc) • rest.eval.1.mulVec (ket β) := by
  have hadd1 (x y : ZMod 2) : x + y + y = x := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hadd2 (x y z : ZMod 2) : x + y + z + y = x + z := by
    rw [show x + y + z + y = x + z + (y + y) by ring, CharTwo.add_self_eq_zero, add_zero]
  simp only [eval_seq_mulVec, gad_ket_T, gad_ket_T_inv, ket_CNOT, Matrix.mulVec_smul,
      Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      Function.update_idem, hadd2, hadd1, Function.update_eq_self,
      smul_smul]; congr 1; rw [gad_phase4T]; ring
theorem andCompute_mulVec_ket_of_zero (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (β : BitAssignment n) (hanc : β ancilla = 0) :
    (CircExt.andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1.mulVec (ket β) =
    ket (Function.update β ancilla (β control₁ * β control₂)) := by
  have hanc_sign : gad_bitSign (β ancilla) = 1 := by simp [hanc, gad_bitSign]
  rw [CircExt.andCompute_loc, eval_seq_mulVec, gad_ket_H, hanc_sign, one_smul];
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, gad_jonesPhaseStep_mulVec_ket,
      Function.update_self, Function.update_of_ne h₁a,
      Function.update_of_ne h₂a]; simp only [eval_seq_mulVec, gad_ket_H, Function.update_self,
      Function.update_idem, Matrix.mulVec_smul, Matrix.mulVec_add,
      gad_ket_S]; have h0 : gad_bitPhaseI 0 = 1 := rfl; have hs0 : gad_bitSign 0 = 1 :=
                                                          rfl; rw [h0, hs0, one_smul, one_smul,
                                                          gad_tempAnd_Combine]
  rcases bit_cases (β control₁ * β control₂) with h | h <;> simp [h]
theorem gad_andUncomputeFixup_mulVec_ket (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (β : BitAssignment n) :
    (CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).eval.1.mulVec (ket β) =
    gad_bitSign (β control₁ * β control₂) • ket (Function.update β ancilla (β ancilla + 1)) := by
  rw [CircExt.andUncomputeFixup_loc]; let γ := Function.update β ancilla (β ancilla + 1);
  have hX : (Circuit.X ancilla).eval.1.mulVec (ket β) = ket γ :=
      ket_X ancilla β; simp only [eval_seq_mulVec, hX, gad_ket_H, Matrix.mulVec_smul,
      Matrix.mulVec_add, ket_CNOT, Function.update_self, Function.update_of_ne h₁₂,
      Function.update_idem,
      zero_add]; have hγ₁ : γ control₁ = β control₁ :=
                   Function.update_of_ne h₁a _ _; have hγ₂ : γ control₂ = β control₂ :=
                                                    Function.update_of_ne h₂a _ _; rw [hγ₁, hγ₂,
                                                    gad_cz_Combine (β control₁) (β control₂)]
  rw [show (if β control₂ =
      0 then ket (Function.update γ control₂ 0) else ket (Function.update γ control₂ 1)) = ket γ by
    rcases bit_cases (β control₂) with h₂ | h₂ <;>
      simp [h₂, (congrArg (Function.update γ control₂)
          (hγ₂.trans h₂).symm).trans (Function.update_eq_self control₂ γ)]]
@[simp] theorem qAssign_obs_map_val {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    (qAssign_obs_map U A).1 = A.1.conj U.1ᴴ := rfl
omit [DecidableEq Var] in
@[simp] theorem wp_qAssign_comp_loc (U₁ U₂ : Unitary (2 ^ n)) (Θ : CQAssertion (Store Var)
    (2 ^ n)) :
    wpQAssignCompat U₁ (wpQAssignCompat U₂ Θ) = wpQAssignCompat (U₂ * U₁) Θ := by
  funext σ; exact qAssign_obs_map_comp U₁ U₂ (Θ σ)
theorem gad_andCompute_eval_mul_projector_zero
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    (CircExt.andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ =
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ := by
  intro P₀; apply matrix_ext_ket; intro β;
  simp only [P₀, ← Matrix.mulVec_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · rw [ite_eq_left hanc,
        andCompute_mulVec_ket_of_zero control₁ control₂ ancilla h₁₂ h₁a h₂a β hanc, ket_TOFF, hanc,
        zero_add]
  · simp [ite_eq_right hanc]
omit [DecidableEq Var] in
@[simp] theorem restrictAssertionToZeroAncilla_wp_qAssign_andCompute_loc
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (CircExt.andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) := by
  refine funext fun σ ↦ Subtype.ext ?_
  simp only [restrictAssertionToZeroAncilla_coe_loc, wpQAssignCompat, qAssign_obs_map_val,
      conj_conj,
    show (QRegister.singleton ancilla).basisOutcomeProjector 0 *
        (CircExt.andCompute_loc control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1ᴴ =
        (QRegister.singleton ancilla).basisOutcomeProjector 0 *
            (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1ᴴ by
      simpa only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
        congrArg conjTranspose (gad_andCompute_eval_mul_projector_zero control₁ control₂ ancilla h₁₂
            h₁a h₂a)]
omit [Fintype Var] in
theorem gad_wp_andUncompute_apply_assertion [Finite Var] [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0;
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1;
    let L₀ := P₀ * (Circuit.H ancilla).eval.1;
    let L₁ :=
        (CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
        (Circuit.H ancilla).eval.1
    (wp (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).compile Θ σ).1 =
      (Θ (Function.update σ v 0)).1.conj L₀ᴴ + (Θ (Function.update σ v 1)).1.conj L₁ᴴ := by
  let _ : Fintype Var := Fintype.ofFinite Var
  intro P₀ P₁ L₀ L₁; let F := CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂;
  let U := Circuit.H ancilla
  have hmeas_apply : (wp (.qSeq (QProg.measureRegister v (QRegister.singleton ancilla))
      (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip)) Θ σ).1 =
      (Θ (Function.update σ v 0)).1.conj P₀ᴴ +
      ((Θ (Function.update σ v 1)).1.conj F.eval.1ᴴ).conj P₁ᴴ := by
    have hsubst0 : σ.subst v 0 = Function.update σ v 0 := by
      funext y; simp [Store.subst, Function.update]
    have hsubst1 : σ.subst v 1 = Function.update σ v 1 := by
      funext y; simp [Store.subst, Function.update]
    simp only [wp, QProg.measureRegister, wp_qMeasure_apply, qMeasure_obs_map_coe,
        CQAssertion.subst_apply]; change ∑ o : Fin 2, _ =
        _; rw [Fin.sum_univ_two]; simp [qMeasure_outcome_herm_eq_conj, hsubst0, hsubst1,
        wpQAssignCompat, CompleteMeasurement.toMeasurement_coe,
        QRegister.computationalBasisMeasurement_apply, P₀, P₁, F]
  change (wp U.compile (wp (.qSeq (QProg.measureRegister v (QRegister.singleton ancilla))
      (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip)) Θ) σ).1 = _
  rw [wp_circuit_compile_loc]; simp only [wpQAssignCompat, qAssign_obs_map_val];
  rw [hmeas_apply, map_add, conj_conj, conj_conj, conj_conj]; dsimp only [L₀, L₁, U, F];
  simp only [Matrix.mul_assoc, conjTranspose_mul]
omit [Fintype Var] in
@[simp] theorem wp_andUncompute_update_self_loc [Finite Var] [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) (val : ℤ) :
    wp (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).compile
      Θ (Function.update σ v val) =
    wp (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).compile Θ σ := by
  apply Subtype.ext;
  rw [gad_wp_andUncompute_apply_assertion, gad_wp_andUncompute_apply_assertion,
      Function.update_idem, Function.update_idem]
theorem gad_andUncomputeFixup_clean_ancilla
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0;
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    P₀ * ((CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).eval.1 * P₁) =
      (CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).eval.1 * P₁ := by
  intro P₀ P₁; apply matrix_ext_ket; intro β;
  simp only [P₀, P₁, ← Matrix.mulVec_mulVec, ket_projector_one]
  by_cases hanc : β ancilla = 1
  · rw [ite_eq_left hanc, gad_andUncomputeFixup_mulVec_ket control₁ control₂ ancilla h₁₂ h₁a h₂a,
        Matrix.mulVec_smul, ket_projector_zero, Function.update_self, hanc, gad_one_add_one_zmod2,
        ite_eq_left rfl]
  · simp [ite_eq_right hanc]
omit [Fintype Var] in
@[simp] theorem wp_andUncompute_clean_post_loc [Finite Var] [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) :
    wp (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).compile
      (CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton ancilla)) =
    wp (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).compile Θ := by
  refine funext fun σ ↦ Subtype.ext ?_
  have htr (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
      (h : (QRegister.singleton ancilla).basisOutcomeProjector 0 * X = X) :
      Xᴴ * (QRegister.singleton ancilla).basisOutcomeProjector 0 = Xᴴ := by
    simpa only [conjTranspose_mul,
        QRegister.basisOutcomeProjector_conjTranspose] using congrArg conjTranspose h
  simp only [gad_wp_andUncompute_apply_assertion, restrictAssertionToZeroAncilla_coe_loc, conj_conj]
  rw [htr (_ * (Circuit.H ancilla).eval.1)
      (by rw [← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]),
    htr ((CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).eval.1 *
      (QRegister.singleton ancilla).basisOutcomeProjector 1 * (Circuit.H ancilla).eval.1) (by
        rw [← Matrix.mul_assoc _ _ (Circuit.H ancilla).eval.1,
          gad_andUncomputeFixup_clean_ancilla control₁ control₂ ancilla h₁₂ h₁a h₂a])]
theorem gad_andUncompute_kraus_zero_mul_toffoli
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    P₀ * (Circuit.H ancilla).eval.1 *
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ =
      gad_sqrtHalf • P₀ := by
  intro P₀; apply matrix_ext_ket; intro β;
  simp only [P₀, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · have hupd : Function.update β ancilla 0 = β :=
        (congrArg (Function.update β ancilla) hanc.symm).trans (Function.update_eq_self ancilla β)
    rw [ite_eq_left hanc, ket_TOFF, gad_ket_H];
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_zero, Function.update_self,
        Function.update_idem, ↓reduceIte, one_ne_zero, smul_zero, add_zero, hupd, hanc]
  · simp [ite_eq_right hanc]
theorem gad_andUncompute_kraus_one_mul_toffoli
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0;
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    (CircExt.andUncomputeFixup_loc control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
      (Circuit.H ancilla).eval.1 *
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ =
      gad_sqrtHalf • P₀ := by
  intro P₀ P₁; apply matrix_ext_ket; intro β;
  simp only [P₀, P₁, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · have hupd : Function.update β ancilla 0 = β :=
        (congrArg (Function.update β ancilla) hanc.symm).trans (Function.update_eq_self ancilla β)
    have hsign_sq : gad_bitSign (β control₁ * β control₂) * gad_bitSign (β control₁ * β control₂) =
        1 := by
      rcases bit_cases (β control₁ * β control₂) with h | h <;> simp [h, gad_bitSign]
    rw [ite_eq_left hanc, ket_TOFF, hanc, zero_add, gad_ket_H];
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_one, Function.update_self,
        Function.update_idem, zero_ne_one, ↓reduceIte, zero_add,
        gad_andUncomputeFixup_mulVec_ket control₁ control₂ ancilla h₁₂ h₁a h₂a,
        Function.update_of_ne h₁a, Function.update_of_ne h₂a, gad_one_add_one_zmod2, hupd,
        hanc]; rw [smul_smul, smul_smul, mul_assoc, hsign_sq, mul_one]
  · simp [ite_eq_right hanc]
theorem restrictZeroAnc_wp_qAssign_toffoli_andUncomp_upd_eq [NeZero (2 ^ n)] (v : Var)
    (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla)
    (h₂a : control₂ ≠ ancilla) (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat (Circuit.TOFF control₁ control₂ ancilla h₁₂
    h₁a h₂a).eval (wp (andUncompute_loc v control₁ control₂ ancilla h₁₂ h₁a h₂a).compile Θ))
    (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton ancilla) := by
  refine funext fun σ ↦ Subtype.ext ?_
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
  have htr (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
      (h : X * T_anc * (QRegister.singleton ancilla).basisOutcomeProjector 0 =
        gad_sqrtHalf • (QRegister.singleton ancilla).basisOutcomeProjector 0) :
      P₀ * T_ancᴴ * Xᴴ = (gad_sqrtHalf • P₀)ᴴ := by
    have hc := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
        ← Matrix.mul_assoc] at hc
  simp only [restrictAssertionToZeroAncilla_coe_loc, wpQAssignCompat, qAssign_obs_map_val]
  rw [gad_wp_andUncompute_apply_assertion, hΘ σ 0, hΘ σ 1, map_add, map_add, conj_conj, conj_conj,
      conj_conj, conj_conj]
  change (Θ σ).1.conj (P₀ * T_ancᴴ * _) + (Θ σ).1.conj (P₀ * T_ancᴴ * _) = (Θ σ).1.conj P₀
  rw [htr _ (gad_andUncompute_kraus_zero_mul_toffoli control₁ control₂ ancilla h₁₂ h₁a h₂a),
    htr _ (gad_andUncompute_kraus_one_mul_toffoli control₁ control₂ ancilla h₁₂ h₁a h₂a)]
  ext1
  simp only [P₀, HermitianMat.mat_add, conj_apply_mat, conjTranspose_smul, gad_star_sqrtHalf,
    QRegister.basisOutcomeProjector_conjTranspose, Matrix.smul_mul, Matrix.mul_smul]
  match_scalars; linear_combination 2 * gad_sqrtHalf_mul_sqrtHalf
end QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
end
end

noncomputable section
open QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
attribute [local irreducible] foldSum
/-- Point mass isolation inside `foldSum M`. -/
theorem foldSum_eq_single {M : ℕ} (k : ℕ) (hk : k < M) (g : ℕ → ℕ)
    (h0 : ∀ i : ℕ, i < M → i ≠ k → g i = 0) : foldSum M g = g k := by
  rw [← sum_fin_eq_foldSum M g]
  exact Finset.sum_eq_single ⟨k, hk⟩ (fun b _ hne ↦ h0 b.val b.isLt fun hv ↦ hne (Fin.ext hv))
    fun h ↦ absurd (Finset.mem_univ _) h
end QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
theorem foldSum_ext {M : ℕ} {f g : ℕ → ℕ} (h : ∀ i < M, f i = g i) : foldSum M f = foldSum M g := by
  rw [← sum_fin_eq_foldSum M f, ← sum_fin_eq_foldSum M g]
  exact Finset.sum_congr rfl fun x _ ↦ h x.val x.isLt
theorem foldSum_add (A B : ℕ) (f : ℕ → ℕ) : foldSum (A + B) f = foldSum A f + foldSum B (fun i ↦
    f (A + i)) := by
  induction B with
  | zero => simp [foldSum]
  | succ b ih =>
    rw [Nat.add_succ, foldSum_succ, foldSum_succ, ih]; omega
/--
Structural-fuel binary tree sum matching `foldSum len (fun i ↦ f (base + i))` in `O(fuel)`
kernel reduction depth.
-/
def bSum : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ
  | _, 0, _, _ => 0
  | _, 1, base, f => f base
  | 0, len, base, f => foldSum len (fun i ↦ f (base + i))
  | fuel + 1, len, base, f =>
    let h := len / 2
    bSum fuel h base f + bSum fuel (len - h) (base + h) f
theorem foldSum_shift_eq_bSum (fuel len base : ℕ) (f : ℕ → ℕ) : foldSum len (fun i ↦ f (base + i)) =
    bSum fuel len base f := by
  induction fuel generalizing len base with
  | zero => exact match len with | 0 | 1 => by simp [foldSum, bSum] | _ + 2 => rfl
  | succ fuel ih =>
    match len with
    | 0 | 1 => simp [foldSum, bSum]
    | m' + 2 =>
      simp only [bSum];
      conv_lhs => rw [show m' + 2 = (m' + 2) / 2 + (m' + 2 - (m' + 2) / 2) by omega]
      rw [foldSum_add, ih ((m' + 2) / 2) base, ← ih (m' + 2 - (m' + 2) / 2) (base + (m' + 2) / 2)]
      exact congrArg (_ + ·) (foldSum_ext fun i _ ↦ congrArg f (by omega))
theorem foldSum_eq_bSum (fuel M : ℕ) (f : ℕ → ℕ) : foldSum M f = bSum fuel M 0 f := by
  simpa only [Nat.zero_add] using foldSum_shift_eq_bSum fuel M 0 f

/-- Sector 3: `.nn n1 n2 e1`. -/
theorem foldSum_add_distrib (M : ℕ) (f g : ℕ → ℕ) : foldSum M (fun i ↦ f i + g i) = foldSum M f +
    foldSum M g := by
  rw [← sum_fin_eq_foldSum M, ← sum_fin_eq_foldSum M, ← sum_fin_eq_foldSum M];
  exact Finset.sum_add_distrib
end QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.QubitizationProgram
open scoped Circuit.Notation
open Operator QProg DynamicCircuit PhotochemistrySolution.BucketRouterCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.XMeasUnld
variable {Var : Type} {n : ℕ}
def qubitizationAncillas : ℕ := 639
end QuantumComputation.Specs.PhotochemistrySolution.QubitizationProgram
end

noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution
open scoped Matrix.Norms.L2Operator
open Operator
theorem hamilt_diagonal_sum2 {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} (f : ι → κ → Fin d → ℂ) :
    Matrix.diagonal (fun x : Fin d ↦ ∑ i : ι, ∑ j : κ, f i j x) = ∑ i : ι, ∑ j : κ,
    Matrix.diagonal (fun x : Fin d ↦ f i j x) := by
  ext x y
  by_cases hxy : x = y <;> simp [Matrix.sum_apply, hxy]
theorem opNorm_diagonal_le {d : ℕ} {f : Fin d → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : Fin d, ‖f x‖ ≤ B) : ‖Matrix.diagonal f‖ ≤ B := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hB).mpr hf
theorem opNorm_diagonal_ofReal_le {d : ℕ} {f : Fin d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : Fin d, |f x| ≤ B) :
    ‖Matrix.diagonal (fun x ↦ (f x : ℂ))‖ ≤ B :=
  opNorm_diagonal_le hB fun x ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf x
theorem hamilt_opNorm_unitary_mul_self_eq_one {d : ℕ} [NeZero d] (U : Unitary d) : ‖U.1‖ = 1 := by
  have hsq : ‖U.1‖ * ‖U.1‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose, U.2.1, norm_one]
  nlinarith [norm_nonneg U.1]
theorem hamilt_opNorm_unitary_le_one {d : ℕ} (U : Unitary d) : ‖U.1‖ ≤ 1 := by
  rcases eq_zero_or_neZero d with rfl | _
  · simpa only [Subsingleton.elim U.1 0, norm_zero] using zero_le_one
  · rw [hamilt_opNorm_unitary_mul_self_eq_one U]
theorem opNorm_conj_unitary_le {d : ℕ} (U : Unitary d) (A : Operator d) : ‖U.1ᴴ * A * U.1‖ ≤
    ‖A‖ := by
  have hU : ‖U.1‖ ≤ 1 := hamilt_opNorm_unitary_le_one U
  have hU' : ‖U.1ᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul_of_nonneg_left hU (norm_nonneg _)).trans
    (by simpa only [mul_one,
          one_mul] using (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hU'
          (norm_nonneg A))))
noncomputable abbrev kineticHamiltonian : Operator (2 ^ systemQubits_frozen) :=
    SpecDefs.kineticEnergy_frozen
noncomputable abbrev potentialHamiltonian : Operator (2 ^ systemQubits_frozen) :=
    SpecDefs.potentialEnergy_frozen
theorem hamiltonian_eq_kinetic_add_potential : SpecDefs.hamiltonian_frozen =
    kineticHamiltonian + potentialHamiltonian :=
  rfl
noncomputable def kineticLocalRaw : Operator (2 ^ gridBits_frozen) :=
  let F := QFT.qftMatrix gridBits_frozen
  Fᴴ * Matrix.diagonal (fun k ↦ (twosComplement_frozen k ^ 2 : ℂ)) * F
noncomputable def kineticCoeff (i : Particle_frozen) : ℝ :=
    2 * Real.pi ^ 2 / (boxWidth_frozen ^ 2 * mass_frozen i)
noncomputable def kineticTerm (i : Particle_frozen) (w : Fin 3) : Operator (2 ^ systemQubits_frozen)
    := (kineticCoeff i : ℂ) • (coordinateRegister_frozen i w).embedMatrix kineticLocalRaw
theorem kineticEnergy_eq_sum : SpecDefs.kineticEnergy_frozen = ∑ i : Particle_frozen, ∑ w :
    Fin 3, kineticTerm i w :=
  rfl
noncomputable def potentialPairDiag (i j : Particle_frozen) (x : Fin (2 ^ systemQubits_frozen)) :
    ℝ :=
    if i = j then 0 else charge_frozen i * charge_frozen j / (2 * gridSpacing_frozen *
    √((max (∑ w, (position_frozen x i w - position_frozen x j w) ^ 2)
    (saturationSq_frozen i j) : ℤ) : ℝ))
noncomputable def potentialPairTerm (i j : Particle_frozen) : Operator (2 ^ systemQubits_frozen) :=
    Matrix.diagonal fun x ↦ (potentialPairDiag i j x : ℂ)
theorem hamilt_diagonal_congr {d : ℕ} {f g : Fin d → ℂ} (h : ∀ x : Fin d, f x = g x) :
    Matrix.diagonal f = Matrix.diagonal g :=
  congrArg Matrix.diagonal (funext h)
theorem hamilt_ite_ofReal_zero {P : Prop} [Decidable P] (r : ℝ) : (if P then (0 : ℂ) else (r : ℂ)) =
    ((if P then 0 else r : ℝ) : ℂ) := by split_ifs <;> simp
theorem hamilt_potentialEnergy_eq_diagonal_sum : SpecDefs.potentialEnergy_frozen =
    Matrix.diagonal (fun x : Fin (2 ^ systemQubits_frozen) ↦ ∑ i : Particle_frozen,
    ∑ j : Particle_frozen, (potentialPairDiag i j x : ℂ)) :=
  hamilt_diagonal_congr fun _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      hamilt_ite_ofReal_zero _
theorem potentialEnergy_eq_sum : SpecDefs.potentialEnergy_frozen = ∑ i : Particle_frozen,
    ∑ j : Particle_frozen, potentialPairTerm i j := by
  rw [hamilt_potentialEnergy_eq_diagonal_sum, hamilt_diagonal_sum2]
  rfl
theorem qftMatrix_conjTranspose_mul_self (n : ℕ) : (QFT.qftMatrix n)ᴴ * QFT.qftMatrix n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hNpos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hsqrt_ne : (Real.sqrt (2 ^ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr hNpos
  have hNne : ((2 ^ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hmul : (1 / (Real.sqrt (2 ^ n : ℝ) : ℂ)) * (1 / (Real.sqrt (2 ^ n : ℝ) : ℂ)) =
      (1 / (2 ^ n : ℝ) : ℂ) := by
    field_simp [hsqrt_ne]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hNpos.le]
  have hterm : ∀ k : Fin (2 ^ n), ((QFT.qftMatrix n)ᴴ i k) * QFT.qftMatrix n k j =
      (1 / (2 ^ n : ℝ) : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (((j.val : ℝ) - (i.val : ℝ)) /
      (2 ^ n : ℝ)))) ^ k.val := fun k ↦ by
    simp only [Matrix.conjTranspose_apply, QFT.qftMatrix, star_mul', star_div₀, star_one,
        Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I * ((i.val * k.val : ℝ) /
        (2 ^ n : ℝ))) = -(2 * ↑Real.pi * Complex.I * ((i.val * k.val : ℝ) / (2 ^ n : ℝ))) := by
      simp only [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hc, ← Complex.exp_nat_mul, mul_mul_mul_comm, hmul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  obtain rfl | hij := eq_or_ne i j
  · simp only [↓reduceIte, sub_self, zero_div, mul_zero, Complex.exp_zero, one_pow,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hNnat_ne : (Nat.cast (2 ^ n) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 ^ n ≠ 0)
    field_simp [hNne, hNnat_ne]
    norm_cast
  · simp only [hij, ↓reduceIte]
    let ω : ℂ :=
        Complex.exp (2 * ↑Real.pi * Complex.I * (((j.val : ℝ) - (i.val : ℝ)) / (2 ^ n : ℝ)))
    have hω_pow : ω ^ (2 ^ n) = 1 := by
      dsimp only [ω]
      rw [← Complex.exp_nat_mul]
      have hexp : Nat.cast (2 ^ n) * (2 * ↑Real.pi * Complex.I * (((j.val : ℝ) - (i.val : ℝ)) /
          (2 ^ n : ℝ))) = ((((j.val : ℤ) - (i.val : ℤ)) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        rw [show (Nat.cast (2 ^ n) : ℂ) = ((2 ^ n : ℝ) : ℂ) by norm_cast]
        field_simp [hNne]
        push_cast
        ring
      rw [hexp, Complex.exp_int_mul_two_pi_mul_I]
    have hω_ne : ω ≠ 1 := fun h1 ↦ by
      rcases Complex.exp_eq_one_iff.mp h1 with ⟨m, hm⟩
      have hdiv : (((j.val : ℝ) - (i.val : ℝ)) / (2 ^ n : ℝ) : ℂ) = m :=
        mul_left_cancel₀
            (by simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0)
            (by linear_combination hm)
      have hreal : (j.val : ℝ) - (i.val : ℝ) = (m : ℝ) * (2 ^ n : ℝ) := Complex.ofReal_injective (by
        push_cast at *
        field_simp [hNne] at hdiv
        linear_combination hdiv)
      have hi_lt : (i.val : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast i.isLt
      have hj_lt : (j.val : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast j.isLt
      rcases lt_trichotomy m 0 with hm_neg | rfl | hm_pos
      · nlinarith [show (m : ℝ) ≤ -1 by exact_mod_cast Int.le_sub_one_of_lt hm_neg]
      · push_cast at hreal
        exact hij (Fin.ext ((Nat.cast_injective (R := ℝ) (by linarith : (j.val : ℝ) = i.val)).symm))
      · nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm_pos]
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hω_ne, hω_pow, sub_self, zero_div, mul_zero]
theorem qftMatrix_mul_conjTranspose_self (n : ℕ) : QFT.qftMatrix n * (QFT.qftMatrix n)ᴴ = 1 :=
    mul_eq_one_comm.mp (qftMatrix_conjTranspose_mul_self n)
@[simp] theorem kineticLocalRaw_conjTranspose : kineticLocalRawᴴ = kineticLocalRaw := by
  unfold kineticLocalRaw
  have hdiag : (Matrix.diagonal fun k : Fin (2 ^ gridBits_frozen) ↦
      (twosComplement_frozen k ^ 2 : ℂ))ᴴ = Matrix.diagonal fun k : Fin (2 ^ gridBits_frozen) ↦
      (twosComplement_frozen k ^ 2 : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    exact congrArg Matrix.diagonal (funext fun _ ↦ by simp)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hdiag,
      Matrix.mul_assoc]
@[simp] theorem kineticTerm_conjTranspose (i : Particle_frozen) (w : Fin 3) :
    (kineticTerm i w)ᴴ = kineticTerm i w := by
  unfold kineticTerm
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      ← QRegister.embedMatrix_conjTranspose, kineticLocalRaw_conjTranspose]
@[simp] theorem kineticHamiltonian_conjTranspose : kineticHamiltonianᴴ = kineticHamiltonian := by
  change SpecDefs.kineticEnergy_frozenᴴ = SpecDefs.kineticEnergy_frozen
  rw [kineticEnergy_eq_sum]
  simp [Matrix.conjTranspose_sum]
@[simp] theorem potentialPairTerm_conjTranspose (i j : Particle_frozen) :
    (potentialPairTerm i j)ᴴ = potentialPairTerm i j := by
  unfold potentialPairTerm
  rw [Matrix.diagonal_conjTranspose]
  exact congrArg Matrix.diagonal (funext fun _ ↦ by simp)
@[simp] theorem potentialHamiltonian_conjTranspose : potentialHamiltonianᴴ =
    potentialHamiltonian := by
  change SpecDefs.potentialEnergy_frozenᴴ = SpecDefs.potentialEnergy_frozen
  rw [potentialEnergy_eq_sum]
  simp [Matrix.conjTranspose_sum]
@[simp] theorem hamiltonian_conjTranspose : SpecDefs.hamiltonian_frozenᴴ =
    SpecDefs.hamiltonian_frozen := by
  rw [hamiltonian_eq_kinetic_add_potential, Matrix.conjTranspose_add,
      kineticHamiltonian_conjTranspose, potentialHamiltonian_conjTranspose]
end QuantumComputation.Specs.PhotochemistrySolution
end
end

noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution
open scoped Matrix.Norms.L2Operator Circuit.Notation Polynomial
open Operator QProg Matrix Polynomial DynamicCircuit PhotochemistrySolution.QubitizationCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.GQSP PhotochemistrySolution.QubitizationProgram
noncomputable def embedMatrixStarAlgHom {k n : ℕ} (r : QRegister k n) :
    Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ →⋆ₐ[ℂ] Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ where
  toFun := r.embedMatrix
  map_zero' := r.embedMatrix_zero
  map_one' := r.embedMatrix_one
  map_mul' := r.embedMatrix_mul
  map_add' := r.embedMatrix_add
  commutes' := fun c ↦ by simp [Algebra.algebraMap_eq_smul_one]
  map_star' := fun M ↦ by simp [Matrix.star_eq_conjTranspose]
theorem opNorm_embedMatrix_le {k n : ℕ} (r : QRegister k n) (A : Operator (2 ^ k)) :
    ‖r.embedMatrix A‖ ≤ ‖A‖ := NonUnitalStarAlgHom.norm_apply_le (embedMatrixStarAlgHom r) A
theorem embedMatrix_sub {k n : ℕ} (r : QRegister k n) (A B : Operator (2 ^ k)) : r.embedMatrix (A -
    B) = r.embedMatrix A - r.embedMatrix B := map_sub (embedMatrixStarAlgHom r) A B
noncomputable def qftGridUnitary : Unitary (2 ^ gridBits_frozen) :=
  ⟨QFT.qftMatrix gridBits_frozen, by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    exact ⟨qftMatrix_conjTranspose_mul_self gridBits_frozen,
      qftMatrix_mul_conjTranspose_self gridBits_frozen⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PotentialDecomp

open scoped Matrix.Norms.L2Operator
open Operator Matrix
/-- Real diagonal operator on `Fin d`, matching `Matrix.diagonal (fun x ↦ (f x : ℂ))`. -/
noncomputable def diagReal {d : ℕ} (f : Fin d → ℝ) : Operator d :=
    Matrix.diagonal (fun x ↦ (f x : ℂ))
theorem diagReal_conjTranspose {d : ℕ} (f : Fin d → ℝ) : (diagReal f)ᴴ = diagReal f := by
  unfold diagReal
  rw [Matrix.diagonal_conjTranspose]
  exact congrArg Matrix.diagonal (funext fun _ ↦ by simp)
theorem diagReal_const {d : ℕ} (c : ℝ) : diagReal (fun _ : Fin d ↦ c) = (c : ℂ) • (1 : Operator d)
    := by
  ext x y
  by_cases hxy : x = y <;> simp [diagReal, hxy]
theorem diagReal_sub {d : ℕ} (f g : Fin d → ℝ) : diagReal (fun x ↦ f x - g x) = diagReal f -
    diagReal g := by
  ext x y
  by_cases hxy : x = y <;> simp [diagReal, Complex.ofReal_sub, hxy]
/-- Spectral norm bound on a real diagonal matrix from pointwise bounds `|f x| ≤ B`. -/
theorem opNorm_diagReal_le {d : ℕ} (f : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : Fin d, |f x| ≤ B) :
    ‖diagReal f‖ ≤ B :=
  PhotochemistrySolution.opNorm_diagonal_ofReal_le hB hf
/-- Squared Euclidean grid distance between particles `i` and `j` in basis state `x`. -/
def gridDistSq (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) : ℤ :=
    ∑ w : Fin 3, (position_frozen x i w - position_frozen x j w) ^ 2
@[simp] theorem gridDistSq_self (x : Fin (2 ^ systemQubits_frozen)) (i : Particle_frozen) :
    gridDistSq x i i = 0 := by simp [gridDistSq]
theorem gridDistSq_comm (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) :
    gridDistSq x i j = gridDistSq x j i :=
  Finset.sum_congr rfl fun _ _ ↦ by ring
noncomputable def pairPot (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) : ℝ :=
    if i = j then 0 else charge_frozen i * charge_frozen j / (2 * gridSpacing_frozen *
    √((max (gridDistSq x i j) (saturationSq_frozen i j) : ℤ) : ℝ))
@[simp] theorem pairPot_self (x : Fin (2 ^ systemQubits_frozen)) (i : Particle_frozen) :
    pairPot x i i = 0 := by simp [pairPot]
/-- `Photochemistry.potentialEnergy` as `diagReal` of the exact `234 × 234` pair sum. -/
theorem potentialEnergy_eq_diagReal : potentialEnergy_frozen = diagReal (fun x ↦
    ∑ i : Particle_frozen, ∑ j : Particle_frozen, pairPot x i j) := by
  ext x y
  obtain rfl | hxy := eq_or_ne x y
  · simp only [potentialEnergy_frozen, diagReal, Matrix.diagonal_apply_eq, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hij : i = j <;> simp [pairPot, gridDistSq, hij]
  · simp [potentialEnergy_frozen, diagReal, hxy]
end QuantumComputation.Specs.PhotochemistrySolution.PotentialDecomp
end

noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
variable {Var : Type}
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
@[simp] theorem bitSign_zero : bitSign 0 = 1 := rfl
@[simp] theorem bitSign_one : bitSign 1 = -1 := rfl
theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitSign, CharTwo.add_self_eq_zero]
@[simp] theorem bitSign_mul_self (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  rcases bit_cases a with rfl | rfl <;> simp [bitSign, one_ne_zero]
noncomputable def sqrtHalf : ℂ := (Real.sqrt (1 / 2) : ℝ)
theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  rw [sqrtHalf, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num
@[simp] theorem star_sqrtHalf : star sqrtHalf = sqrtHalf :=
  Complex.conj_ofReal _
theorem singleton_embedMatrix_mulVec_ket {n : ℕ} (q : Wire n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix M).mulVec (ket β) =
      M 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
      M 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hw (l : Fin 2) : writeReg β (.singleton q) (basisBits 1 l) =
      Function.update β q (basisBits 1 l 0) :=
    writeReg_eq_update _ _ _ 0 fun i hi ↦ absurd (Subsingleton.elim i 0) hi
  rw [embedMatrix_mulVec_ket, show localIdx (.singleton q) β = if β q = 0 then 0 else 1 from
    (by decide : ∀ b, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1) (β q)]
  exact (Fin.sum_univ_two _).trans (by
    rw [hw, hw, show basisBits 1 0 0 = 0 by decide, show basisBits 1 1 0 = 1 by decide])
theorem ket_H_apply {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) = sqrtHalf • (ket (Function.update β q 0) +
    bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec (ket β) = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, sqrtHalf, bitSign, smul_add, Complex.real_smul]
def bitToggleFun {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2) (β : BitAssignment n) :
    BitAssignment n := Function.update β q (β q + f β)
theorem bitToggleFun_involutive {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) (β : BitAssignment n) :
    bitToggleFun q f (bitToggleFun q f β) = β := by
  dsimp only [bitToggleFun];
  rw [hf, Function.update_self, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Function.update_eq_self]
noncomputable def bitToggleMatrix {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := fun i j ↦
    if i = (basisBitsEquiv n).symm (bitToggleFun q f (basisBits n j)) then 1 else 0
theorem bitToggleMatrix_mulVec_ket {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (β : BitAssignment n) : (bitToggleMatrix q f).mulVec (ket β) = ket (Function.update β q (β q +
    f β))
    := by
  funext i;
  simp [bitToggleMatrix, ket, basisState, Matrix.mulVec, dotProduct, Pi.single_apply, bitToggleFun]
theorem bitToggleMatrix_mul_self {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) : bitToggleMatrix q f * bitToggleMatrix q f =
    1 := by
  apply matrix_ext_ket; intro β;
  simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec, bitToggleMatrix_mulVec_ket, hf,
      Function.update_self, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Function.update_eq_self]
theorem bitToggleMatrix_conjTranspose {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) : (bitToggleMatrix q f)ᴴ =
    bitToggleMatrix q f := by
  have hflip {i j} (h : i = (basisBitsEquiv n).symm (bitToggleFun q f (basisBits n j))) :
      j = (basisBitsEquiv n).symm (bitToggleFun q f (basisBits n i)) := by
    simp [h, bitToggleFun_involutive q f hf]
  ext i j
  simp [bitToggleMatrix, propext ⟨@hflip j i, @hflip i j⟩]
noncomputable def bitToggleUnitary {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) : Unitary (2 ^ n) :=
  ⟨bitToggleMatrix q f, by
    rw [Matrix.mem_unitaryGroup_iff'];
    rw [Matrix.star_eq_conjTranspose, bitToggleMatrix_conjTranspose q f hf]
    exact bitToggleMatrix_mul_self q f hf⟩
theorem bitToggleUnitary_mulVec_ket {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) (β : BitAssignment n) :
    (bitToggleUnitary q f hf).1.mulVec (ket β) = ket (Function.update β q (β q + f β)) :=
    bitToggleMatrix_mulVec_ket q f β
@[simp] theorem bitToggleUnitary_mul_self {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) :
    bitToggleUnitary q f hf * bitToggleUnitary q f hf = 1 :=
  Subtype.ext (bitToggleMatrix_mul_self q f hf)
@[simp] theorem bitToggleUnitary_conjTranspose {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β b, f (Function.update β q b) = f β) :
    (bitToggleUnitary q f hf).1ᴴ = (bitToggleUnitary q f hf).1 :=
  bitToggleMatrix_conjTranspose q f hf
noncomputable def toffoliUnitary {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) : Unitary (2 ^ n) :=
  bitToggleUnitary t (fun β ↦ β c₁ * β c₂)
    (fun β b ↦ by simp [Function.update_of_ne h₁t, Function.update_of_ne h₂t])
theorem wp_seq_compile [DecidableEq Var] {n : ℕ} (d₁ d₂ : DynamicCircuit Var n)
    (Q : CQAssertion (Store Var) (2 ^ n)) :
    wp (DynamicCircuit.seq d₁ d₂).compile Q = wp d₁.compile (wp d₂.compile Q) := rfl
def xBasisUnloadDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (phaseFixup : DynamicCircuit Var n) : DynamicCircuit Var n :=
    DynamicCircuit.seq (.circuit (Circuit.H q))
    (DynamicCircuit.seq (.measure v (QRegister.singleton q)) (.qIf (fun σ ↦ σ v = 1)
    (DynamicCircuit.seq (.circuit (Circuit.X q)) phaseFixup) .identity))
theorem wp_measure_qIf_const [DecidableEq Var] {n : ℕ} (v : Var) (q : Wire n)
    (dThen : DynamicCircuit Var n) (M B : Observable (Fin (2 ^ n)))
    (hThen : wp dThen.compile (fun _ ↦ M) = fun _ ↦ B) :
    wp (DynamicCircuit.seq (.measure v (QRegister.singleton q))
    (.qIf (fun σ ↦ σ v = 1) dThen .identity)).compile (fun _ ↦ M) = fun _ ↦
    qMeasure_obs_map ((QRegister.singleton q).computationalBasisMeasurement : Measurement (2 ^ n)
    (2 ^ 1)) (fun o ↦ if o.val = 0 then M else B)
    := by funext τ; apply Subtype.ext; simp only [DynamicCircuit.compile, wp_qSeq,
            QProg.measureRegister, wp_qMeasure_apply, qMeasure_obs_map_coe,
            CQAssertion.subst_apply]; change ∑ o : Fin 2, _ = ∑ o : Fin 2, _; rw [Fin.sum_univ_two,
            Fin.sum_univ_two]; have h0 : (τ.subst v 0) v = 0 :=
                                 Function.update_self v 0 τ;
                                 have h1 : (τ.subst v 1) v = 1 :=
                                 Function.update_self v 1 τ; simp [qMeasure_outcome_herm_eq_conj,
                                 CompleteMeasurement.toMeasurement_coe, hThen, wp]
theorem wp_xBasisUnloadDyn_uncomputes [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (q : Wire n)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β)
    (phaseFixup : DynamicCircuit Var n) (Z_f : Circuit n)
    (hwp_fix : ∀ A : Observable (Fin (2 ^ n)),
      wp phaseFixup.compile (fun _ ↦ A) = wp (DynamicCircuit.circuit Z_f).compile (fun _ ↦ A))
    (hket_fix : ∀ β : BitAssignment n, Z_f.eval.1.mulVec (ket β) = bitSign (f β) • ket β)
    (M : Observable (Fin (2 ^ n))) :
    let P₀ := (QRegister.singleton q).basisOutcomeProjector 0; let U_f := bitToggleUnitary q f hf
    ∃ N : Observable (Fin (2 ^ n)),
      wp (xBasisUnloadDyn v q phaseFixup).compile (fun _ ↦ M) = (fun _ ↦ N) ∧
        P₀ * U_f.1 * N.1.1 * U_f.1 * P₀ = P₀ * M.1.1 * P₀ := by
  intro P₀ U_f
  let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
  let F : Circuit n := Circuit.X q ;;ᶜ Z_f
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hbranch : wp (DynamicCircuit.seq (.circuit (Circuit.X q)) phaseFixup).compile (fun _ ↦ M) =
      fun _ ↦ qAssign_obs_map F.eval M := by
    rw [wp_seq_compile, hwp_fix M, wp_circuit_constObservable, wp_circuit_constObservable]
    exact funext fun _ ↦ qAssign_obs_map_comp (Circuit.X q).eval Z_f.eval M
  let N_meas : Observable (Fin (2 ^ n)) :=
    qMeasure_obs_map ((QRegister.singleton q).computationalBasisMeasurement : Measurement (2 ^ n)
        (2 ^ 1))
      (fun o ↦ if o.val = 0 then M else qAssign_obs_map F.eval M)
  refine ⟨qAssign_obs_map (Circuit.H q).eval N_meas, by
    rw [xBasisUnloadDyn, wp_seq_compile, wp_measure_qIf_const v q _ M _ hbranch,
      wp_circuit_constObservable], ?_⟩
  let L₀ := P₀ * (Circuit.H q).eval.1
  let L₁ := F.eval.1 * P₁ * (Circuit.H q).eval.1
  have hNm : N_meas.1 = M.1.conj P₀ᴴ + (qAssign_obs_map F.eval M).1.conj P₁ᴴ := by
    simp only [N_meas, qMeasure_obs_map_coe]
    exact (Fin.sum_univ_two _).trans (by
      simp [qMeasure_outcome_herm_eq_conj, 
        CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply, P₀,
            P₁])
  have hN_mat : (qAssign_obs_map (Circuit.H q).eval N_meas).1.1 =
      L₀ᴴ * M.1.1 * L₀ + L₁ᴴ * M.1.1 * L₁ := by
    rw [qAssign_obs_map_mat_eq, show N_meas.1.1 =
        P₀ᴴ * M.1.1 * P₀ + P₁ᴴ * (qAssign_obs_map F.eval M).1.1 * P₁ by
      rw [show N_meas.1.1 = (M.1.conj P₀ᴴ).mat + ((qAssign_obs_map F.eval M).1.conj P₁ᴴ).mat from
        congrArg HermitianMat.mat hNm]
      simp only [conj_apply_mat, Matrix.mul_assoc, conjTranspose_conjTranspose]
      rfl, qAssign_obs_map_mat_eq]
    simp only [L₀, L₁, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, conjTranspose_mul]
  have hK₀ : L₀ * U_f.1 * P₀ = sqrtHalf • P₀ := matrix_ext_ket fun β ↦ by
    simp only [L₀, P₀, U_f, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
    by_cases hq0 : β q = 0
    · rw [ite_eq_left hq0, bitToggleUnitary_mulVec_ket, ket_H_apply]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_zero, Function.update_self,
        Function.update_idem, ↓reduceIte, one_ne_zero, smul_zero, add_zero, hq0,
        hq0 ▸ Function.update_eq_self q β]
    · simp [ite_eq_right hq0]
  have hK₁ : L₁ * U_f.1 * P₀ = sqrtHalf • P₀ := matrix_ext_ket fun β ↦ by
    simp only [L₁, F, P₀, P₁, U_f, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
    by_cases hq0 : β q = 0
    · rw [ite_eq_left hq0, bitToggleUnitary_mulVec_ket, hq0, zero_add, ket_H_apply]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_one, Function.update_self,
        Function.update_idem, zero_ne_one, ↓reduceIte, zero_add, eval_seq_mulVec, ket_X,
        hket_fix, CharTwo.add_self_eq_zero, hq0 ▸ Function.update_eq_self q β, hq0,
        smul_smul, mul_assoc, bitSign_mul_self, mul_one]
    · simp [ite_eq_right hq0]
  have hAdj {L} (hL : L * U_f.1 * P₀ = sqrtHalf • P₀) : P₀ * U_f.1 * Lᴴ = (sqrtHalf • P₀)ᴴ := by
    simpa only [conjTranspose_mul, hP₀_herm, U_f, bitToggleUnitary_conjTranspose,
      ← Matrix.mul_assoc] using congrArg conjTranspose hL
  rw [hN_mat, show P₀ * U_f.1 * (L₀ᴴ * M.1.1 * L₀ + L₁ᴴ * M.1.1 * L₁) * U_f.1 * P₀ =
      (P₀ * U_f.1 * L₀ᴴ) * M.1.1 * (L₀ * U_f.1 * P₀) +
      (P₀ * U_f.1 * L₁ᴴ) * M.1.1 * (L₁ * U_f.1 * P₀) by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc], hAdj hK₀, hK₀, hAdj hK₁, hK₁]
  simp only [conjTranspose_smul, star_sqrtHalf, hP₀_herm, Matrix.smul_mul, Matrix.mul_smul]
  match_scalars
  linear_combination 2 * sqrtHalf_mul_sqrtHalf
def foldFinUnitary {d : ℕ} : {m : ℕ} → (Fin m → Unitary d) → Unitary d
  | 0, _ => 1
  | m + 1, U => U (Fin.last m) * foldFinUnitary (m := m) (fun i ↦ U (Fin.castSucc i))
theorem CleanWorkStep.of_foldFinDyn [Fintype Var] [DecidableEq Var] {n w m : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister w n)
    (U : Fin m → Unitary (2 ^ n)) (body : Fin m → DynamicCircuit Var n)
    (hstep : ∀ i : Fin m, CleanWorkStep (Var := Var) rWork (U i) (body i)) :
    CleanWorkStep (Var := Var) rWork (foldFinUnitary U) (foldFinDyn body) := by
  induction m with
  | zero => exact CleanWorkStep.identity rWork
  | succ m ih =>
      exact CleanWorkStep.seq (ih (fun i ↦ U (Fin.castSucc i)) (fun i ↦ body (Fin.castSucc i))
          (fun i ↦ hstep (Fin.castSucc i))) (hstep (Fin.last m))
def czCircuit {n : ℕ} (c₁ c₂ : Wire n) (h₁₂ : c₁ ≠ c₂) : Circuit n :=
  Circuit.H c₂ ;;ᶜ Circuit.CNOT c₁ c₂ h₁₂ ;;ᶜ Circuit.H c₂
theorem czCircuit_mulVec_ket {n : ℕ} (c₁ c₂ : Wire n) (h₁₂ : c₁ ≠ c₂) (β : BitAssignment n) :
    (QubitizationWalkSem.czCircuit c₁ c₂ h₁₂).eval.1.mulVec (ket β) = bitSign (β c₁ *
    β c₂) • ket β := by
  simp only [PhotochemistrySolution.QubitizationWalkSem.czCircuit, eval_seq_mulVec, ket_H_apply,
    Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT, Function.update_self,
    Function.update_of_ne h₁₂, Function.update_idem, zero_add]
  rcases bit_cases (β c₁) with h₁ | h₁ <;> rcases bit_cases (β c₂) with h₂ | h₂ <;> (
    simp only [h₁, h₂, h₂ ▸ Function.update_eq_self c₂ β, bitSign, CharTwo.add_self_eq_zero,
      add_zero, mul_zero, mul_one, one_ne_zero, ↓reduceIte, smul_add, smul_smul]
    match_scalars <;> norm_num [sqrtHalf_mul_sqrtHalf])
end QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectSymDyn
open scoped Circuit.Notation
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
variable {Var : Type} {n : ℕ}
theorem CleanWorkStep.of_pureCircuit_comm [Fintype Var] [DecidableEq Var] {n w : ℕ}
    [NeZero (2 ^ n)]
    (rWork : QRegister w n) (c : Circuit n)
    (hcomm : c.eval.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 * c.eval.1) :
    CleanWorkStep (Var := Var) rWork c.eval (.circuit c) :=
  ⟨hcomm, fun M ↦
    ⟨qAssign_obs_map c.eval M, wp_circuit_constObservable c M, by
      rw [qAssign_obs_map_mat_eq]⟩⟩
theorem ket_X_apply (w : Wire n) (β : BitAssignment n) : (Circuit.X w).eval.1.mulVec (ket β) =
    ket (Function.update β w (β w + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton w).embedMatrix !![(0 : ℂ), 1; 1, 0]).mulVec (ket β) = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β w) with hb | hb
  all_goals simp [hb, show (1 : ZMod 2) + 1 = 0 from rfl]
theorem eval_H_mul_self (w : Wire n) : (Circuit.H w).eval * (Circuit.H w).eval = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_H_apply w β, Matrix.mulVec_smul, Matrix.mulVec_add, ket_H_apply w]
  rcases bit_cases (β w) with hw | hw <;> ext i <;>
    simp [hw, hw ▸ Function.update_eq_self w β, bitSign_zero, bitSign_one, Function.update_idem] <;>
    linear_combination 2 * (ket β i) * sqrtHalf_mul_sqrtHalf
theorem eval_X_mul_self (w : Wire n) : (Circuit.X w).eval * (Circuit.X w).eval = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      ket_X_apply, Function.update_self, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero,
      add_zero, Function.update_eq_self]
theorem eval_CNOT_mul_self (c t : Wire n) (hct : c ≠ t) : (Circuit.CNOT c t hct).eval *
    (Circuit.CNOT c t hct).eval = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      ket_CNOT, Function.update_self, Function.update_of_ne hct, Function.update_idem, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
inductive SymDyn (Var : Type) (n : ℕ) (wAnc : Wire n) where
  | hadamard (w : Wire n) (hw : w ≠ wAnc)
  | pauliX (w : Wire n) (hw : w ≠ wAnc)
  | cnot (c t : Wire n) (hct : c ≠ t) (ht : t ≠ wAnc)
  | toffoli (v : Var) (c₁ c₂ t : Wire n)
      (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
      (h₁a : c₁ ≠ wAnc) (h₂a : c₂ ≠ wAnc) (hta : t ≠ wAnc)
  | circuit (c : Circuit n)
      (hcomm : c.eval.1 * (QRegister.singleton wAnc).basisOutcomeProjector 0 =
        (QRegister.singleton wAnc).basisOutcomeProjector 0 * c.eval.1)
  | seq (p q : SymDyn Var n wAnc)
  | fold (m : ℕ) (f : Fin m → SymDyn Var n wAnc)
namespace SymDyn
open BucketRouterCircuit
variable {wAnc : Wire n}
noncomputable def unitary : SymDyn Var n wAnc → Unitary (2 ^ n)
  | .hadamard w _ => (Circuit.H w).eval
  | .pauliX w _ => (Circuit.X w).eval
  | .cnot c t hct _ => (Circuit.CNOT c t hct).eval
  | .toffoli _ c₁ c₂ t _ h₁t h₂t _ _ _ => toffoliUnitary c₁ c₂ t h₁t h₂t
  | .circuit c _ => c.eval
  | .seq p q => q.unitary * p.unitary
  | .fold m f => foldFinUnitary (m := m) (fun i ↦ (f i).unitary)
end SymDyn
end QuantumComputation.Specs.PhotochemistrySolution.SelectSymDyn
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.QubitizationTop
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.GQSP PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationWalkSem WithLp Polynomial
noncomputable def eQWire {N : ℕ} (q : Wire N) : Matrix (Fin 2)
    (Fin 2) ℂ →ₐ[ℂ] Operator (2 ^ N) where
  toFun := (QRegister.singleton q).embedMatrix
  map_one' := (QRegister.singleton q).embedMatrix_one
  map_mul' := (QRegister.singleton q).embedMatrix_mul
  map_zero' := (QRegister.singleton q).embedMatrix_zero
  map_add' := (QRegister.singleton q).embedMatrix_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        (QRegister.singleton q).embedMatrix_smul, (QRegister.singleton q).embedMatrix_one]
theorem qubTop_opNorm_le_of_mulVec_pgL2Norm_top {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ ψ : I → ℂ, pgL2Norm (A *ᵥ ψ) ≤ c * pgL2Norm ψ) :
    ‖A‖ ≤ c :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) A).opNorm_le_bound hc fun ψ ↦ h ψ.ofLp
theorem qubTop_pgL2Norm_mulVec_le_opNorm {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (ψ : I → ℂ) : pgL2Norm (A *ᵥ ψ) ≤ ‖A‖ * pgL2Norm ψ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 ψ)
theorem opNorm_embedMatrix_le {N b : ℕ} (r : QRegister b N) (M : Operator (2 ^ b)) :
    ‖r.embedMatrix M‖ ≤ ‖M‖ := by
  refine qubTop_opNorm_le_of_mulVec_pgL2Norm_top (norm_nonneg M) fun ψ ↦ ?_
  have hsum {α : Type} [AddCommMonoid α] (f : Fin (2 ^ N) → α) :
      ∑ j, f j = ∑ e, ∑ y, f (r.basisSplitEquiv.symm (y, e)) := by
    rw [← Equiv.sum_comp r.basisSplitEquiv.symm, Fintype.sum_prod_type, Finset.sum_comm]
  have hf (y e) : r.extractIndex (r.basisSplitEquiv.symm (y, e)) = y :=
    congrArg Prod.fst (r.basisSplitEquiv.apply_symm_apply (y, e))
  have hs (y e) := congrArg Prod.snd (r.basisSplitEquiv.apply_symm_apply (y, e))
  have hpt (x e) : (r.embedMatrix M *ᵥ ψ) (r.basisSplitEquiv.symm (x, e)) =
      (M *ᵥ fun y ↦ ψ (r.basisSplitEquiv.symm (y, e))) x := by
    rw [Matrix.mulVec, dotProduct, hsum, Finset.sum_eq_single e
      (fun e' _ hne ↦ Finset.sum_eq_zero fun y _ ↦ by
        rw [r.embedMatrix_apply, ite_eq_right fun h ↦
          hne ((hs y e').symm.trans (h.symm.trans (hs x e))), mul_zero, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    exact Finset.sum_congr rfl fun y _ ↦ by
      simp [hf x e, hf y e]
  have hsq : pgL2Norm (r.embedMatrix M *ᵥ ψ) ^ 2 ≤ (‖M‖ * pgL2Norm ψ) ^ 2 := by
    rw [pgL2Norm_sq, hsum, mul_pow, pgL2Norm_sq, hsum, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ ↦ ?_
    simp_rw [hpt, ← pgL2Norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (pgL2Norm_nonneg _)
      (qubTop_pgL2Norm_mulVec_le_opNorm M _) 2
  nlinarith [pgL2Norm_nonneg (r.embedMatrix M *ᵥ ψ), mul_nonneg (norm_nonneg M) (pgL2Norm_nonneg ψ)]
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
theorem eQ_pauliX_conj_diag_poly {N : ℕ} (q : Wire N) (X Y : Operator (2 ^ N))
    (hX : X ∈ GQSP.qubitCommutant (eQWire q)) (hY : Y ∈ GQSP.qubitCommutant (eQWire q)) :
    eQWire q pauliX2 * (eQWire q (Matrix.single 0 0 1) * X + eQWire q (Matrix.single 1 1 1) * Y) *
    eQWire q pauliX2 = eQWire q (Matrix.single 1 1 1) * X + eQWire q (Matrix.single 0 0 1) * Y := by
  let e := eQWire q
  have hx {a b : Fin 2} (hab : a ≠ b) :
      pauliX2 * Matrix.single a a (1 : ℂ) * pauliX2 = Matrix.single b b 1 := by
    fin_cases a <;> fin_cases b <;> first | contradiction |
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pauliX2, Matrix.mul_apply, Matrix.single, Matrix.vecHead, Matrix.vecTail]
  rw [show e pauliX2 * (e (.single 0 0 1) * X + e (.single 1 1 1) * Y) * e pauliX2 =
        (e pauliX2 * e (.single 0 0 1)) * (X * e pauliX2) +
        (e pauliX2 * e (.single 1 1 1)) * (Y * e pauliX2) by simp [mul_add, add_mul, mul_assoc],
    ← PhotochemistrySolution.GQSP.comm_of_mem_qubitCommutant e hX pauliX2,
    ← GQSP.comm_of_mem_qubitCommutant e hY pauliX2, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← map_mul, hx (b := 1) (by decide), ← map_mul, ← map_mul, hx (b := 0) (by decide)]
variable {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
  {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister qubitizationAncillas n}
  {hdisj : rSys.DisjointWires rAnc} {tSel : ℕ}
theorem diag_prod_rule_poly {N : ℕ} (q : Wire N) (X₁ Y₁ X₂ Y₂ : Operator (2 ^ N))
    (hX₁ : X₁ ∈ GQSP.qubitCommutant (eQWire q)) (hY₁ : Y₁ ∈ GQSP.qubitCommutant (eQWire q)) :
    (eQWire q (Matrix.single 0 0 1) * X₁ + eQWire q (Matrix.single 1 1 1) * Y₁) *
    (eQWire q (Matrix.single 0 0 1) * X₂ + eQWire q (Matrix.single 1 1 1) * Y₂) =
    eQWire q (Matrix.single 0 0 1) * (X₁ * X₂) + eQWire q (Matrix.single 1 1 1) * (Y₁ * Y₂) := by
  set e := eQWire q
  have ht (i j : Fin 2) {U V : Operator (2 ^ N)} (hU : U ∈ GQSP.qubitCommutant e) :
      (e (.single i i 1) * U) * (e (.single j j 1) * V) =
        (e (.single i i 1) * e (.single j j 1)) * (U * V) := by
    simpa only [mul_assoc] using congrArg (fun M ↦ e (.single i i 1) * (M * V))
      (PhotochemistrySolution.GQSP.comm_of_mem_qubitCommutant e hU (.single j j 1)).symm
  simp [add_mul, mul_add, ht _ _ hX₁, ht _ _ hY₁, GQSP.e_single_mul_single]
noncomputable def catIsom {N b : ℕ} (r : QRegister b N) : Operator (2 ^ N) :=
    r.embedMatrix (Matrix.vecMulVec (phaseGradientState b) (Pi.single 0 1))
theorem phaseGradientState_inner_self (b : ℕ) : dotProduct (star (phaseGradientState b))
    (phaseGradientState b) = 1 := by
  rw [dotProduct, show (∑ i, star (phaseGradientState b) i * phaseGradientState b i) =
      ((pgL2Norm (PgBase.phaseGradientState b) ^ 2 : ℝ) : ℂ) by
    simp [pgL2Norm_sq, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]]
  simp [PgBase.phaseGradientState, pgL2Norm_prodState, pgL2Norm_plusPhase]
theorem catProj_mul_catIsom {N b : ℕ} (r : QRegister b N) :
    r.embedMatrix (Matrix.vecMulVec (phaseGradientState b) (star (phaseGradientState b))) *
    catIsom r = catIsom r := by
  unfold catIsom;
  rw [← r.embedMatrix_mul, Matrix.vecMulVec_mul_vecMulVec, phaseGradientState_inner_self b,
      one_smul]
theorem norm_basisOutcomeProjector_zero_le_one {N b : ℕ} (r : QRegister b N) :
    ‖r.basisOutcomeProjector 0‖ ≤ 1 := by
  refine (opNorm_embedMatrix_le r (compProj 0)).trans
    (qubTop_opNorm_le_of_mulVec_pgL2Norm_top zero_le_one fun ψ ↦ ?_)
  have hle : pgL2Norm ((compProj 0 : Operator (2 ^ b)) *ᵥ ψ) ^ 2 ≤ pgL2Norm ψ ^ 2 := by
    rw [pgL2Norm_sq, pgL2Norm_sq]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : i = 0
    · subst hi
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single 0
        (fun j _ hj ↦ by simp [compProj, Ne.symm hj]) (fun h ↦ absurd (Finset.mem_univ _) h)]
      simp [compProj]
    · simp [Matrix.mulVec, dotProduct, compProj, Ne.symm hi]
  nlinarith [pgL2Norm_nonneg ((compProj 0 : Operator (2 ^ b)) *ᵥ ψ), pgL2Norm_nonneg ψ]
theorem norm_unitary_le_one {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (U : 𝐔[I]) : ‖U.1‖ ≤ 1 := by
  have h1 : U.1ᴴ * U.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.1
  have hsq : ‖U.1‖ * ‖U.1‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, h1, NormOneClass.norm_one]
  nlinarith [norm_nonneg U.1]
end QuantumComputation.Specs.PhotochemistrySolution.QubitizationTop
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectSymDynInstance
open scoped Circuit.Notation
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
variable {Var : Type} {n : ℕ}
theorem ket_Z_apply (w : Wire n) (β : BitAssignment n) : (Circuit.Z w).eval.1.mulVec (ket β) =
    bitSign (β w) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval,
    singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β w) with hb | hb <;>
    simp [Qubit.Z, hb, hb ▸ Function.update_eq_self w β, bitSign]
inductive ClassicalSym (Var : Type) (n : ℕ) (wAnc : Wire n) where
  | id
  | pauliX (w : Wire n) (hw : w ≠ wAnc)
  | cnot (c t : Wire n) (hct : c ≠ t) (ht : t ≠ wAnc)
  | toffoli (v : Var) (c₁ c₂ t : Wire n)
      (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
      (h₁a : c₁ ≠ wAnc) (h₂a : c₂ ≠ wAnc) (hta : t ≠ wAnc)
  | seq (p q : ClassicalSym Var n wAnc)
  | fold (m : ℕ) (f : Fin m → ClassicalSym Var n wAnc)
theorem CleanWorkStep.congr_on_proj [Fintype Var] [DecidableEq Var] {w : ℕ}
    [NeZero (2 ^ n)]
    (rWork : QRegister w n) (U₀ U₁ : Unitary (2 ^ n)) (prog : DynamicCircuit Var n)
    (hcomm₁ : U₁.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 * U₁.1)
    (heq : U₁.1 * rWork.basisOutcomeProjector 0 = U₀.1 * rWork.basisOutcomeProjector 0)
    (hstep : CleanWorkStep (Var := Var) rWork U₀ prog) :
    CleanWorkStep (Var := Var) rWork U₁ prog := by
  refine ⟨hcomm₁, fun M ↦ (hstep.2 M).imp fun N ⟨hwp, hmat⟩ ↦ ⟨hwp, ?_⟩⟩
  have hadj : rWork.basisOutcomeProjector 0 * U₁.1ᴴ = rWork.basisOutcomeProjector 0 * U₀.1ᴴ := by
    simpa [conjTranspose_mul, rWork.basisOutcomeProjector_conjTranspose 0] using
      congrArg conjTranspose heq
  simpa only [Matrix.mul_assoc] using (congrArg₂ (· * M.1.1 * ·) hadj heq).trans
    (by simpa only [Matrix.mul_assoc] using hmat)
theorem block_apply_val {a k m : ℕ} (h : a + k ≤ m) (i : Fin k) :
    (QRegister.block a k h i).val = a + i.val := rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectSymDynInstance
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.QubitizationKapteyn
open scoped Matrix.Norms.L2Operator Polynomial
open Operator QProg DynamicCircuit PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.GQSP PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationWalkSem WithLp Polynomial Matrix
  PhotochemistrySolution.QubitizationTop
theorem qubiti_embedMatrix_sub_poly {N k : ℕ} (r : QRegister k N) (X Y : Operator (2 ^ k)) :
    r.embedMatrix (X - Y) = r.embedMatrix X - r.embedMatrix Y := by
  have h : -Y = (-1 : ℂ) • Y :=
      (neg_one_smul ℂ Y).symm; rw [sub_eq_add_neg, h, r.embedMatrix_add, r.embedMatrix_smul,
      neg_one_smul, ← sub_eq_add_neg]
theorem embedMatrix_truncChebApprox {N k : ℕ} (r : QRegister k N) (K D : ℕ) (A : Operator (2 ^ k))
    (s : ℝ) : r.embedMatrix (GQSP.truncChebApprox K D A s) =
    GQSP.truncChebApprox K D (r.embedMatrix A) s := by
  have hT : ∀ m : ℕ, r.embedMatrix (chebyshevT m A) = chebyshevT m (r.embedMatrix A) := by
    intro m
    suffices r.embedMatrix (chebyshevT m A) = chebyshevT m (r.embedMatrix A) ∧
        r.embedMatrix (chebyshevT (m + 1) A) = chebyshevT (m + 1) (r.embedMatrix A) from this.1
    induction m with
    | zero => exact ⟨r.embedMatrix_one, rfl⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩;
      rw [chebyshevT, chebyshevT, qubiti_embedMatrix_sub_poly r, r.embedMatrix_smul,
          r.embedMatrix_mul, ih.2, ih.1]
  unfold PhotochemistrySolution.GQSP.truncChebApprox
  induction (K + 1) with
  | zero => simp [r.embedMatrix_zero]
  | succ m ihm =>
    rw [Finset.sum_range_succ, r.embedMatrix_add, ihm, r.embedMatrix_smul, hT m,
        Finset.sum_range_succ]
end QuantumComputation.Specs.PhotochemistrySolution.QubitizationKapteyn
end
end

section
open scoped Matrix.Norms.L2Operator
section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectApprox
open Operator QProg Matrix DynamicCircuit PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationTop
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
noncomputable def diagReal {d : ℕ} (f : Fin d → ℝ) : Operator d :=
    Matrix.diagonal (fun x ↦ (f x : ℂ))
theorem diagReal_conjTranspose {d : ℕ} (f : Fin d → ℝ) : (diagReal f)ᴴ = diagReal f := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; simp [diagReal]
  · simp [diagReal, hxy, Ne.symm hxy]
theorem opNorm_diagReal_le {d : ℕ} (f : Fin d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : Fin d, |f x| ≤ B) :
    ‖diagReal f‖ ≤ B :=
  opNorm_diagonal_ofReal_le hB hf
end QuantumComputation.Specs.PhotochemistrySolution.SelectApprox
end

noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.OvBidir
open Operator QProg DynamicCircuit PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.QubitizationWalkSem
variable {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
  {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister qubitizationAncillas n}
  {hdisj : rSys.DisjointWires rAnc} {tSel : ℕ}
theorem embedUnitary_foldFinUnitary {n k : ℕ} (r : QRegister k n) {m : ℕ}
    (f : Fin m → Unitary (2 ^ k)) : r.embedUnitary
    (foldFinUnitary f) = foldFinUnitary (fun s ↦ r.embedUnitary (f s)) := by
  induction m with
  | zero => exact r.embedUnitary_one
  | succ m ih =>
    change r.embedUnitary (f (Fin.last m) * foldFinUnitary fun i ↦ f i.castSucc) =
        r.embedUnitary (f (Fin.last m)) * foldFinUnitary fun i ↦ r.embedUnitary (f i.castSucc)
    rw [r.embedUnitary_mul, ih]
end QuantumComputation.Specs.PhotochemistrySolution.OvBidir
end
end

noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.OvBidir
open scoped Polynomial
open Operator QProg DynamicCircuit PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.QubitizationWalkSem WithLp
  Polynomial Matrix ComplexConjugate
noncomputable def cat8SharedProjOf {N : ℕ} (r : QRegister 34 N) : Operator (2 ^ N) :=
    (r.slice 26 8 le_rfl).embedMatrix (Matrix.vecMulVec (phaseGradientState 8)
    (star (phaseGradientState 8)))
abbrev locSysGen (ancW : ℕ) : QRegister systemQubits_frozen (systemQubits_frozen + ancW) :=
    .block 0 systemQubits_frozen ((Nat.zero_add _).trans_le (Nat.le_add_right _ _))
abbrev locAncGen (ancW : ℕ) : QRegister ancW (systemQubits_frozen + ancW) :=
    .block systemQubits_frozen ancW le_rfl
abbrev locQGen {ancW : ℕ} (hAnc : 100 ≤ ancW) : Wire (systemQubits_frozen + ancW) :=
  locAncGen ancW ⟨ancW - 1, by omega⟩
noncomputable abbrev eQGen {ancW : ℕ} (hAnc : 100 ≤ ancW) : Matrix (Fin 2)
    (Fin 2) ℂ →ₐ[ℂ] Operator (2 ^ (systemQubits_frozen + ancW)) := eQWire (locQGen hAnc)
noncomputable abbrev projOneQGen {ancW : ℕ} (hAnc : 100 ≤ ancW) :
    Operator (2 ^ (systemQubits_frozen + ancW)) :=
    (QRegister.singleton (locQGen hAnc)).basisOutcomeProjector 1
noncomputable abbrev lcuProjGen {ancW l : ℕ} (lcuSub : QRegister l ancW) :
    Operator (2 ^ (systemQubits_frozen + ancW)) :=
    ((locAncGen ancW).compose lcuSub).basisOutcomeProjector 0
theorem _locGrad34Gen_le {ancW : ℕ} (hAnc : 100 ≤ ancW) : 0 + 34 ≤ ancW := by omega
abbrev locGrad34Gen {ancW : ℕ} (hAnc : 100 ≤ ancW) : QRegister 34 (systemQubits_frozen + ancW) :=
    (locAncGen ancW).slice 0 34 (_locGrad34Gen_le hAnc)
abbrev locCat8SharedGen {ancW : ℕ} (hAnc : 100 ≤ ancW) : QRegister 8 (systemQubits_frozen + ancW) :=
    (locGrad34Gen hAnc).slice 26 8 le_rfl
noncomputable abbrev cat8SharedProjGen {ancW : ℕ} (hAnc : 100 ≤ ancW) :
    Operator (2 ^ (systemQubits_frozen + ancW)) := cat8SharedProjOf (locGrad34Gen hAnc)
def qspQubitGen {ancW n : ℕ} (hAnc : 100 ≤ ancW) (rAnc : QRegister ancW n) : Wire n :=
  rAnc ⟨ancW - 1, by omega⟩
def OffIndexAndScratchGen {ancW k l s : ℕ} (lcuSub : QRegister l ancW) (scrSub : QRegister s ancW)
    (r : QRegister k (systemQubits_frozen + ancW)) : Prop :=
    ∀ i, ∃ j : Fin ancW, r i = locAncGen ancW j ∧ j ∉ Set.range lcuSub.wires ∧
    j ∉ Set.range scrSub.wires
structure SelectConjugationDataShared34 {Var : Type} [Fintype Var] [DecidableEq Var]
    {ancW n : ℕ} (hAnc : 100 ≤ ancW)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister ancW n)
    (hdisj : rSys.DisjointWires rAnc) (tSel : ℕ) where
  scrL : ℕ
  scrSub : QRegister scrL ancW
  lcuL : ℕ
  lcuSub : QRegister lcuL ancW
  lcu_scr_ne : ∀ i j, lcuSub i ≠ scrSub j
  lcu_idx : ∀ i, 34 ≤ (lcuSub i).val ∧ ((lcuSub i).val < 64 ∨ 99 ≤ (lcuSub i).val) ∧
    (lcuSub i).val ≠ ancW - 1
  scr_idx : ∀ j, 34 ≤ (scrSub j).val ∧ (scrSub j).val ≠ ancW - 1
  scr_rot34 : ∀ t : Fin ancW, 64 ≤ t.val ∧ t.val < 99 → t ∈ Set.range scrSub.wires
  α : ℝ
  c : ℝ
  α_pos : 0 < α
  α_time_le : α * evolutionTime_frozen ≤ 4231872
  aImpl : Operator (2 ^ systemQubits_frozen)
  aImpl_herm : aImplᴴ = aImpl
  aImpl_norm : ‖aImpl‖ ≤ 1
  εBlock : ℝ
  εBlock_nonneg : 0 ≤ εBlock
  εBlock_le : 4231872 * εBlock ≤ 100
  aImpl_approx : ‖aImpl - ((α : ℂ)⁻¹) • (hamiltonian_frozen - (c : ℂ) • 1)‖ ≤ εBlock
  S : Unitary (2 ^ (systemQubits_frozen + ancW))
  S_herm : S.1ᴴ = S.1
  S_comm : ∀ {k : ℕ} (r : QRegister k (systemQubits_frozen + ancW))
    (M : Operator (2 ^ k)), OffIndexAndScratchGen lcuSub scrSub r → Commute S.1 (r.embedMatrix M)
  S_scr : Commute S.1 (((locAncGen ancW).compose scrSub).basisOutcomeProjector 0)
  hblock : lcuProjGen lcuSub * S.1 * lcuProjGen lcuSub *
      ((locAncGen ancW).compose scrSub).basisOutcomeProjector 0 =
    (locSysGen ancW).embedMatrix aImpl * lcuProjGen lcuSub *
      ((locAncGen ancW).compose scrSub).basisOutcomeProjector 0
  cselCirc : DynamicCircuit Var n
  cselU : Unitary (2 ^ (systemQubits_frozen + ancW))
  cselU_cat : cselU.1 * cat8SharedProjGen hAnc =
    (1 - projOneQGen hAnc * (1 - S.1)) * cat8SharedProjGen hAnc
  csel_clean : CleanWorkStep (rAnc.compose scrSub)
    ((rSys.concat rAnc hdisj).embedUnitary cselU) cselCirc
  reflCirc : DynamicCircuit Var n
  reflU : Unitary (2 ^ (systemQubits_frozen + ancW))
  reflU_eq : reflU.1 = 1 - (2 : ℂ) • (projOneQGen hAnc * (1 - lcuProjGen lcuSub))
  refl_clean : CleanWorkStep (rAnc.compose scrSub)
    ((rSys.concat rAnc hdisj).embedUnitary reflU) reflCirc
  csel_toff : cselCirc.count .TOFF = 0
  refl_toff : reflCirc.count .TOFF = 0
  t_le : cselCirc.count .T + reflCirc.count .T ≤ tSel
structure UselDataShared34 {Var : Type} [Fintype Var] [DecidableEq Var]
    {ancW n : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc} {tSel : ℕ}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) where
  uselCirc : DynamicCircuit Var n
  uselU : Unitary (2 ^ (systemQubits_frozen + ancW))
  uselU_cat : uselU.1 * cat8SharedProjGen hAnc = D.S.1 * cat8SharedProjGen hAnc
  usel_clean : CleanWorkStep (rAnc.compose D.scrSub)
    ((rSys.concat rAnc hdisj).embedUnitary uselU) uselCirc
  usel_toff : uselCirc.count .TOFF = 0
variable {Var : Type} [Fintype Var] [DecidableEq Var]
  {ancW n : ℕ} {hAnc : 100 ≤ ancW}
  {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
  {hdisj : rSys.DisjointWires rAnc} {tSel : ℕ}
noncomputable abbrev projScrGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    Operator (2 ^ (systemQubits_frozen + ancW)) :=
  ((locAncGen ancW).compose D.scrSub).basisOutcomeProjector 0
noncomputable def walkOpShared
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    Operator (2 ^ (systemQubits_frozen + ancW)) :=
  reflectionMatrix (lcuProjGen D.lcuSub) * D.S.1
noncomputable def scaleTimeShared
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) : ℝ :=
  D.α * evolutionTime_frozen
theorem scaleTimeShared_nonneg (D : SelectConjugationDataShared34 (Var :=
    Var) hAnc rSys rAnc hdisj tSel) :
    0 ≤ scaleTimeShared D := by
  unfold scaleTimeShared evolutionTime_frozen
  exact mul_nonneg D.α_pos.le (by norm_num)
theorem offIndexAndScratchGen_locQ
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    OffIndexAndScratchGen D.lcuSub D.scrSub (QRegister.singleton (locQGen hAnc)) := by
  intro i; fin_cases i
  exact ⟨⟨ancW - 1, by omega⟩, rfl,
    fun ⟨a, ha⟩ ↦ (D.lcu_idx a).2.2 (congrArg Fin.val ha),
    fun ⟨a, ha⟩ ↦ (D.scr_idx a).2 (congrArg Fin.val ha)⟩
omit [Fintype Var] [DecidableEq Var] in
theorem disj_locQGen_locCat8SharedGen :
    (QRegister.singleton (locQGen hAnc)).DisjointWires (locCat8SharedGen hAnc) := by
  rw [QRegister.disjoint_iff]; intro i j hij; fin_cases i
  have hv := congrArg Fin.val ((locAncGen ancW).wires.injective hij)
  dsimp [locQGen, locCat8SharedGen, locGrad34Gen, QRegister.slice] at hv; omega
theorem disj_locQGen_lcu
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    (QRegister.singleton (locQGen hAnc)).DisjointWires ((locAncGen ancW).compose D.lcuSub) := by
  rw [QRegister.disjoint_iff]; intro i j hij; fin_cases i
  exact (D.lcu_idx j).2.2 (congrArg Fin.val ((locAncGen ancW).wires.injective hij)).symm
theorem disj_lcu_locCat8SharedGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    ((locAncGen ancW).compose D.lcuSub).DisjointWires (locCat8SharedGen hAnc) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val ((locAncGen ancW).wires.injective hij); have hlcu := (D.lcu_idx i).1
  dsimp [locCat8SharedGen, locGrad34Gen, QRegister.slice] at hv; omega
theorem disj_lcu_scrGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    ((locAncGen ancW).compose D.lcuSub).DisjointWires ((locAncGen ancW).compose D.scrSub) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  exact D.lcu_scr_ne i j ((locAncGen ancW).wires.injective hij)
omit [Fintype Var] [DecidableEq Var] in
theorem disj_locSysGen_locAncGen : (locSysGen ancW).DisjointWires (locAncGen ancW) :=
  QRegister.block_disjoint_of_le 0 systemQubits_frozen systemQubits_frozen ancW (by omega) le_rfl
      (by omega)
theorem disj_locSysGen_lcu (D : SelectConjugationDataShared34 (Var :=
    Var) hAnc rSys rAnc hdisj tSel) :
    (locSysGen ancW).DisjointWires ((locAncGen ancW).compose D.lcuSub) :=
  QRegister.disjoint_iff.mpr fun i j hij ↦
      QRegister.disjoint_iff.mp disj_locSysGen_locAncGen i (D.lcuSub j) hij
theorem disj_locSysGen_scr (D : SelectConjugationDataShared34 (Var :=
    Var) hAnc rSys rAnc hdisj tSel) :
    (locSysGen ancW).DisjointWires ((locAncGen ancW).compose D.scrSub) :=
  QRegister.disjoint_iff.mpr fun i j hij ↦
      QRegister.disjoint_iff.mp disj_locSysGen_locAncGen i (D.scrSub j) hij
noncomputable def walkLocalUnitaryShared34
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) (b : Bool) :
    Unitary (2 ^ (systemQubits_frozen + ancW)) :=
  if b then D.cselU * D.reflU
  else (Circuit.X (locQGen hAnc)).eval * D.reflU * D.cselU * (Circuit.X (locQGen hAnc)).eval
noncomputable def bidirStepLocalUnitaryShared34
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D) : Unitary (2 ^ (systemQubits_frozen + ancW)) :=
  (Circuit.X (locQGen hAnc)).eval * D.reflU * (Circuit.X (locQGen hAnc)).eval * U.uselU * D.reflU
omit [Fintype Var] [DecidableEq Var] in
theorem compose_singleton_locQGen :
    (rSys.concat rAnc hdisj).compose (QRegister.singleton (locQGen hAnc)) =
      QRegister.singleton (qspQubitGen hAnc rAnc) :=
  qreg_ext fun i ↦ by
    fin_cases i
    exact QRegister.concat_apply_right rSys rAnc hdisj ⟨ancW - 1, by omega⟩
omit [Fintype Var] [DecidableEq Var] in
theorem embedUnitary_X_locQGen :
    (rSys.concat rAnc hdisj).embedUnitary (Circuit.X (locQGen hAnc)).eval =
    (Circuit.X (qspQubitGen hAnc rAnc)).eval := by
  rw [Circuit.eval_single, Circuit.eval_single, ← QRegister.embedUnitary_compose,
      compose_singleton_locQGen]
omit [Fintype Var] [DecidableEq Var] in
theorem embedUnitary_H_locQGen :
    (rSys.concat rAnc hdisj).embedUnitary (Circuit.H (locQGen hAnc)).eval =
    (Circuit.H (qspQubitGen hAnc rAnc)).eval := by
  rw [Circuit.eval_single, Circuit.eval_single, ← QRegister.embedUnitary_compose,
      compose_singleton_locQGen]
theorem disj_qspQubit_scr
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    (QRegister.singleton (qspQubitGen hAnc rAnc)).DisjointWires (rAnc.compose D.scrSub) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  fin_cases i
  exact (D.scr_idx j).2 (congrArg Fin.val (rAnc.wires.injective hij)).symm
theorem cleanWorkStep_X_qspGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    CleanWorkStep (Var := Var) (rAnc.compose D.scrSub)
      ((rSys.concat rAnc hdisj).embedUnitary (Circuit.X (locQGen hAnc)).eval)
      (.circuit (Circuit.X (qspQubitGen hAnc rAnc))) := by
  rw [embedUnitary_X_locQGen]; apply CleanWorkStep.of_pureCircuit_comm;
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  exact (QRegister.singleton (qspQubitGen hAnc rAnc)).embedMatrix_comm_of_disjoint _
      (disj_qspQubit_scr D) _ _
theorem cleanWorkStep_H_qspGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    CleanWorkStep (Var := Var) (rAnc.compose D.scrSub)
      ((rSys.concat rAnc hdisj).embedUnitary (Circuit.H (locQGen hAnc)).eval)
      (.circuit (Circuit.H (qspQubitGen hAnc rAnc))) := by
  rw [embedUnitary_H_locQGen]; apply CleanWorkStep.of_pureCircuit_comm;
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  exact (QRegister.singleton (qspQubitGen hAnc rAnc)).embedMatrix_comm_of_disjoint _
      (disj_qspQubit_scr D) _ _
omit [Fintype Var] [DecidableEq Var] in
theorem eQGen_star (M : Matrix (Fin 2) (Fin 2) ℂ) : (eQGen hAnc M)ᴴ = eQGen hAnc Mᴴ :=
    ((QRegister.singleton (locQGen hAnc)).embedMatrix_conjTranspose M).symm
omit [Fintype Var] [DecidableEq Var] in
theorem circuit_X_locQGen_eval : (Circuit.X (locQGen hAnc)).eval.1 = eQGen hAnc pauliX2 := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]; rfl
omit [Fintype Var] [DecidableEq Var] in
theorem circuit_H_locQGen_eval : (Circuit.H (locQGen hAnc)).eval.1 = eQGen hAnc GQSP.hadamard2 := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval];
  change (QRegister.singleton (locQGen hAnc)).embedMatrix Qubit.H.1 =
      (QRegister.singleton (locQGen hAnc)).embedMatrix GQSP.hadamard2
  congr 1; ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Qubit.H, GQSP.hadamard2, GQSP.invSqrtTwo, Real.sqrt_inv]
omit [Fintype Var] [DecidableEq Var] in
theorem eQGen_single_11 : eQGen hAnc (Matrix.single 1 1 1) = projOneQGen hAnc := by
  have hs : Matrix.single (1 : Fin 2) 1 (1 : ℂ) = compProj 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hs]; rfl
omit [Fintype Var] [DecidableEq Var] in
theorem eQGen_single_00_eq_sub : eQGen hAnc (Matrix.single 0 0 1) = 1 - projOneQGen hAnc := by
  rw [← eQGen_single_11 (hAnc := hAnc), eq_sub_iff_add_eq, ← map_add]
  have h1 : (Matrix.single 0 0 (1 : ℂ) + Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  rw [h1, map_one]
theorem mem_qubitCommutant_lcuProjGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    lcuProjGen D.lcuSub ∈ PhotochemistrySolution.GQSP.qubitCommutant (eQGen hAnc) := by
  rw [Subalgebra.mem_centralizer_iff]; rintro _ ⟨M, rfl⟩;
  exact ((QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint ((locAncGen ancW).compose
      D.lcuSub) (disj_locQGen_lcu D) M (compProj 0))
theorem mem_qubitCommutant_reflWalkGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    reflectionMatrix (lcuProjGen D.lcuSub) ∈ GQSP.qubitCommutant (eQGen hAnc) :=
  Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (mem_qubitCommutant_lcuProjGen D) (2 : ℂ))
      (Subalgebra.one_mem _)
theorem mem_qubitCommutant_SGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    D.S.1 ∈ PhotochemistrySolution.GQSP.qubitCommutant (eQGen hAnc) := by
  rw [Subalgebra.mem_centralizer_iff]; rintro _ ⟨M, rfl⟩;
  exact (D.S_comm (QRegister.singleton (locQGen hAnc)) M (offIndexAndScratchGen_locQ D)).eq.symm
theorem mem_qubitCommutant_walkGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    walkOpShared D ∈ PhotochemistrySolution.GQSP.qubitCommutant (eQGen hAnc) :=
  Subalgebra.mul_mem _ (mem_qubitCommutant_reflWalkGen D) (mem_qubitCommutant_SGen D)
theorem S_mul_self_eq_oneGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    D.S.1 * D.S.1 = 1 := by
  calc D.S.1 * D.S.1 = D.S.1ᴴ * D.S.1 := by rw [D.S_herm]
    _ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact D.S.2.1
theorem walkOpShared_mem_unitary
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    walkOpShared D ∈ unitary (Operator (2 ^ (systemQubits_frozen + ancW))) :=
  GQSP.walk_mem_unitary (((locAncGen ancW).compose D.lcuSub).basisOutcomeProjector_conjTranspose 0)
    (((locAncGen ancW).compose D.lcuSub).basisOutcomeProjector_mul_self 0)
        (S_mul_self_eq_oneGen D) D.S_herm
theorem walkOpShared_conjTranspose
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    (walkOpShared D)ᴴ = D.S.1 * reflectionMatrix (lcuProjGen D.lcuSub) := by
  unfold walkOpShared;
  rw [Matrix.conjTranspose_mul, D.S_herm,
      GQSP.reflectionMatrix_conjTranspose (((locAncGen ancW).compose
      D.lcuSub).basisOutcomeProjector_conjTranspose 0)]
theorem refl_block_id_shared {N : ℕ} (Pq Pl : Operator (2 ^ N)) :
    (1 : Operator (2 ^ N)) - (2 : ℂ) • (Pq * (1 - Pl)) = (1 - Pq) + Pq * reflectionMatrix Pl := by
  unfold reflectionMatrix; rw [mul_sub, mul_sub, mul_one, mul_smul_comm, smul_sub]
  ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]; ring
theorem csel_block_id_shared {N : ℕ} (Pq S : Operator (2 ^ N)) :
    (1 : Operator (2 ^ N)) - Pq * (1 - S) = (1 - Pq) + Pq * S := by rw [mul_sub, mul_one]; abel
theorem refl_comm_id_shared {N : ℕ} (Pq Pl C : Operator (2 ^ N))
    (hQ : Pq * C = C * Pq) (hL : Pl * C = C * Pl) : ((1 : Operator (2 ^ N)) - (2 : ℂ) • (Pq *
    (1 - Pl))) * C = C * (1 - (2 : ℂ) • (Pq * (1 - Pl))) := by
  simp only [mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  rw [mul_assoc Pq Pl C, hL, ← mul_assoc Pq C Pl, hQ, mul_assoc C Pq Pl]
theorem reflU_eq_block_diagGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    D.reflU.1 =
      eQGen hAnc (Matrix.single 0 0 1) +
        eQGen hAnc (Matrix.single 1 1 1) * reflectionMatrix (lcuProjGen D.lcuSub) := by
  rw [D.reflU_eq, refl_block_id_shared, ← eQGen_single_00_eq_sub,
      ← eQGen_single_11]
theorem csel_rhs_eq_block_diagGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    1 - projOneQGen hAnc * (1 - D.S.1) =
      eQGen hAnc (Matrix.single 0 0 1) + eQGen hAnc (Matrix.single 1 1 1) * D.S.1 := by
  rw [csel_block_id_shared, ← eQGen_single_00_eq_sub, ← eQGen_single_11]
theorem comm_reflU_cat8SharedProjGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) :
    D.reflU.1 * cat8SharedProjGen hAnc = cat8SharedProjGen hAnc * D.reflU.1 := by
  rw [D.reflU_eq];
  exact refl_comm_id_shared _ _ _ ((QRegister.singleton
      (locQGen hAnc)).embedMatrix_comm_of_disjoint (locCat8SharedGen hAnc)
      disj_locQGen_locCat8SharedGen _ _)
      (((locAncGen ancW).compose D.lcuSub).embedMatrix_comm_of_disjoint (locCat8SharedGen hAnc)
      (disj_lcu_locCat8SharedGen D) _ _)
omit [Fintype Var] [DecidableEq Var] in
theorem comm_X_cat8SharedProjGen : eQGen hAnc pauliX2 * cat8SharedProjGen hAnc =
    cat8SharedProjGen hAnc * eQGen hAnc pauliX2 :=
    (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint (locCat8SharedGen hAnc)
    disj_locQGen_locCat8SharedGen pauliX2 _
theorem sigOp_false_eq_poly_shared {N : ℕ} (q : Wire N)
    (W : Operator (2 ^ N)) : GQSP.sigOp (eQWire q) W false = eQWire q (Matrix.single 0 0 1) * W +
    eQWire q (Matrix.single 1 1 1) := by
  unfold GQSP.sigOp GQSP.mixedSignal;
  rw [ite_eq_right Bool.false_ne_true, GQSP.blockOp_diag (eQWire q), mul_one]
theorem sigOp_true_eq_poly_shared {N : ℕ} (q : Wire N)
    (W : Operator (2 ^ N)) : GQSP.sigOp (eQWire q) W true = eQWire q (Matrix.single 0 0 1) +
    eQWire q (Matrix.single 1 1 1) * Wᴴ := by
  unfold GQSP.sigOp GQSP.mixedSignal; rw [ite_eq_left rfl, GQSP.blockOp_diag (eQWire q), mul_one]
theorem walk_mul_cat8_poly_shared {N : ℕ} (q : Wire N)
    (reflU cselU S : Unitary (2 ^ N)) (Plcu cat8 : Operator (2 ^ N)) (b : Bool)
    (hRc : reflectionMatrix Plcu ∈ GQSP.qubitCommutant (eQWire q))
    (hSc : S.1 ∈ GQSP.qubitCommutant (eQWire q))
    (hWc : reflectionMatrix Plcu * S.1 ∈ GQSP.qubitCommutant (eQWire q))
    (hX : (Circuit.X q).eval.1 = eQWire q pauliX2) (hcX : eQWire q pauliX2 * cat8 = cat8 *
    eQWire q pauliX2) (hcR : reflU.1 * cat8 = cat8 * reflU.1)
    (hcsel : cselU.1 * cat8 = (1 - eQWire q (Matrix.single 1 1 1) * (1 - S.1)) * cat8)
    (hrefl : reflU.1 = eQWire q (Matrix.single 0 0 1) + eQWire q (Matrix.single 1 1 1) *
    reflectionMatrix Plcu) (hcsel_d : 1 - eQWire q (Matrix.single 1 1 1) * (1 - S.1) =
    eQWire q (Matrix.single 0 0 1) + eQWire q (Matrix.single 1 1 1) * S.1)
    (hW_adj : (reflectionMatrix Plcu * S.1)ᴴ = S.1 * reflectionMatrix Plcu) :
    ((if b then cselU * reflU else (Circuit.X q).eval * reflU * cselU *
    (Circuit.X q).eval) : Unitary (2 ^ N)).1 * cat8 = GQSP.sigOp (eQWire q)
    (reflectionMatrix Plcu * S.1) b * cat8 := by
  have h1c : (1 : Operator (2 ^ N)) ∈ PhotochemistrySolution.GQSP.qubitCommutant (eQWire q) :=
    Subalgebra.one_mem _
  have hrefl1 : reflU.1 = eQWire q (.single 0 0 1) * 1 +
      eQWire q (.single 1 1 1) * reflectionMatrix Plcu := by simpa only [mul_one] using hrefl
  have hcsel1 : 1 - eQWire q (.single 1 1 1) * (1 - S.1) =
      eQWire q (.single 0 0 1) * 1 + eQWire q (.single 1 1 1) * S.1 := by
    simpa only [mul_one] using hcsel_d
  cases b
  · rw [ite_eq_right Bool.false_ne_true, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
      hX, mul_assoc (eQWire q pauliX2 * reflU.1 * cselU.1), hcX, ← mul_assoc,
      mul_assoc (eQWire q pauliX2 * reflU.1), hcsel, ← mul_assoc,
      mul_assoc (eQWire q pauliX2 * _ * _) cat8, ← hcX, ← mul_assoc]
    exact congrArg (· * cat8) (by
      rw [mul_assoc (eQWire q pauliX2) reflU.1, hrefl1, hcsel1,
        diag_prod_rule_poly q 1 _ 1 S.1 h1c hRc, mul_one,
        eQ_pauliX_conj_diag_poly q 1 _ h1c hWc, mul_one,
        sigOp_false_eq_poly_shared q _, add_comm])
  · rw [ite_eq_left rfl, Submonoid.coe_mul, mul_assoc, hcR, ← mul_assoc, hcsel, mul_assoc, ← hcR,
      ← mul_assoc]
    exact congrArg (· * cat8) (by
      rw [hcsel1, hrefl1, diag_prod_rule_poly q 1 S.1 1 _ h1c hSc, mul_one, mul_one, ← hW_adj,
        sigOp_true_eq_poly_shared q _])
theorem bidir_cat8_poly_shared {N : ℕ} (q : Wire N)
    (reflU uselU : Unitary (2 ^ N)) (R S cat8 : Operator (2 ^ N))
    (hRc : R ∈ GQSP.qubitCommutant (eQWire q)) (hSc : S ∈ GQSP.qubitCommutant (eQWire q))
    (hX : (Circuit.X q).eval.1 = eQWire q pauliX2) (hcR : reflU.1 * cat8 = cat8 * reflU.1)
    (husel : uselU.1 * cat8 = S * cat8) (hrefl : reflU.1 = eQWire q (Matrix.single 0 0 1) +
    eQWire q (Matrix.single 1 1 1) * R) (hW_adj : (R * S)ᴴ = S * R) : ((Circuit.X q).eval * reflU *
    (Circuit.X q).eval * uselU * reflU).1 * cat8 = GQSP.sigOp (eQWire q)
    (R * S) false * GQSP.sigOp (eQWire q) (R * S) true * cat8 := by
  have h1c : (1 : Operator (2 ^ N)) ∈ GQSP.qubitCommutant (eQWire q) :=
      Subalgebra.one_mem (GQSP.qubitCommutant (eQWire q))
  have hrefl1 : reflU.1 = eQWire q (Matrix.single 0 0 1) * 1 +
      eQWire q (Matrix.single 1 1 1) * R := by rw [mul_one]; exact hrefl
  have hXRX : eQWire q pauliX2 * reflU.1 * eQWire q pauliX2 = eQWire q (Matrix.single 0 0 1) * R +
      eQWire q (Matrix.single 1 1 1) * 1 := by
    rw [hrefl1, eQ_pauliX_conj_diag_poly q 1 R h1c hRc, add_comm]
  have hSd : S = eQWire q (Matrix.single 0 0 1) * S + eQWire q (Matrix.single 1 1 1) * S := by
    rw [← add_mul, ← map_add]
    have h1 : (Matrix.single 0 0 (1 : ℂ) + Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
    rw [h1, map_one, one_mul]
  have hsig : GQSP.sigOp (eQWire q) (R * S) false * GQSP.sigOp (eQWire q)
      (R * S) true = eQWire q (Matrix.single 0 0 1) * (R * S) + eQWire q (Matrix.single 1 1 1) *
      (S * R) := by
    unfold GQSP.sigOp GQSP.mixedSignal;
    rw [ite_eq_right Bool.false_ne_true, ite_eq_left rfl, GQSP.blockOp_diag, GQSP.blockOp_diag,
        diag_prod_rule_poly q (R * S) 1 1 ((R * S)ᴴ) (Subalgebra.mul_mem _ hRc hSc) h1c, mul_one,
        one_mul, hW_adj]
  have hop : eQWire q pauliX2 * reflU.1 * eQWire q pauliX2 * S * reflU.1 = GQSP.sigOp (eQWire q)
      (R * S) false * GQSP.sigOp (eQWire q) (R * S) true := by
    rw [hXRX, hsig]
    conv_lhs => rw [hSd, hrefl1]
    rw [diag_prod_rule_poly q R 1 S S hRc h1c, diag_prod_rule_poly q (R * S)
        (1 * S) 1 R (Subalgebra.mul_mem _ hRc hSc) (Subalgebra.mul_mem _ h1c hSc), mul_one, one_mul]
  have e1 : uselU.1 * reflU.1 * cat8 = S * reflU.1 * cat8 := by
    rw [mul_assoc, hcR, ← mul_assoc, husel, mul_assoc, ← hcR, ← mul_assoc]
  calc ((Circuit.X q).eval * reflU * (Circuit.X q).eval * uselU * reflU).1 * cat8
      = eQWire q pauliX2 * reflU.1 * eQWire q pauliX2 * (uselU.1 * reflU.1 * cat8) := by
        simp only [Submonoid.coe_mul, hX, mul_assoc]
    _ = eQWire q pauliX2 * reflU.1 * eQWire q pauliX2 * (S * reflU.1 * cat8) := by rw [e1]
    _ = _ := by rw [← hop]; simp only [mul_assoc]
theorem walkLocalUnitaryShared34_mul_cat8Shared
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) (b : Bool) :
    (walkLocalUnitaryShared34 D b).1 * cat8SharedProjGen hAnc =
      GQSP.sigOp (eQGen hAnc) (walkOpShared D) b * cat8SharedProjGen hAnc :=
  @walk_mul_cat8_poly_shared (systemQubits_frozen + ancW)
      (locQGen hAnc) D.reflU D.cselU D.S
    (lcuProjGen D.lcuSub) (cat8SharedProjGen hAnc) b (mem_qubitCommutant_reflWalkGen D)
        (mem_qubitCommutant_SGen D)
    (mem_qubitCommutant_walkGen D) circuit_X_locQGen_eval comm_X_cat8SharedProjGen
        (comm_reflU_cat8SharedProjGen D)
    (eQGen_single_11.symm ▸ D.cselU_cat) (reflU_eq_block_diagGen D)
    (eQGen_single_11.symm ▸ csel_rhs_eq_block_diagGen D) (walkOpShared_conjTranspose D)
theorem bidirStepLocalUnitaryShared34_mul_cat8Shared
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (U : UselDataShared34 D) :
    (bidirStepLocalUnitaryShared34 D U).1 * cat8SharedProjGen hAnc =
      (PhotochemistrySolution.GQSP.sigOp (eQGen hAnc) (walkOpShared D) false *
        GQSP.sigOp (eQGen hAnc) (walkOpShared D) true) * cat8SharedProjGen hAnc :=
  @bidir_cat8_poly_shared (systemQubits_frozen + ancW)
      (locQGen hAnc) D.reflU U.uselU
    (reflectionMatrix (lcuProjGen D.lcuSub)) D.S.1 (cat8SharedProjGen hAnc)
    (mem_qubitCommutant_reflWalkGen D) (mem_qubitCommutant_SGen D) circuit_X_locQGen_eval
    (comm_reflU_cat8SharedProjGen D) U.uselU_cat (reflU_eq_block_diagGen D)
        (walkOpShared_conjTranspose D)
theorem commute_gqspOp_refl_mul_shared {N : ℕ} (e : Matrix (Fin 2)
    (Fin 2) ℂ →ₐ[ℂ] Operator (2 ^ N)) {Pl S A : Operator (2 ^ N)}
    (hW' : (reflectionMatrix Pl * S)ᴴ = S * reflectionMatrix Pl) (he : ∀ M, Commute (e M) A)
    (hl : Commute Pl A) (hS : Commute S A) (L : List (Matrix (Fin 2) (Fin 2) ℂ × Bool)) :
    Commute (GQSP.gqspOp e (reflectionMatrix Pl * S) L) A := by
  have hR : Commute (reflectionMatrix Pl) A := by
    unfold reflectionMatrix;
    rw [commute_iff_eq, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hl.eq, one_mul, mul_one]
  refine commute_gqspOp e he (hR.mul_left hS) ?_ L; rw [hW']; exact hS.mul_left hR
theorem commute_walk_data_embedMatrixGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    {b : ℕ} (r : QRegister b (systemQubits_frozen + ancW))
    (hl : ((locAncGen ancW).compose D.lcuSub).DisjointWires r)
    (hq : (QRegister.singleton (locQGen hAnc)).DisjointWires r)
    (hoff : OffIndexAndScratchGen D.lcuSub D.scrSub r) (M : Operator (2 ^ b)) :
    (∀ N, Commute (eQGen hAnc N) (r.embedMatrix M)) ∧
      Commute (lcuProjGen D.lcuSub) (r.embedMatrix M) ∧
      Commute D.S.1 (r.embedMatrix M) :=
  ⟨fun N ↦ (QRegister.singleton (locQGen hAnc)).embedMatrix_comm_of_disjoint r hq N M,
    ((locAncGen ancW).compose D.lcuSub).embedMatrix_comm_of_disjoint r hl (compProj 0) M,
        D.S_comm r M hoff⟩
theorem commute_gqspOp_walkGen
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    {A : Operator (2 ^ (systemQubits_frozen + ancW))}
    (h : (∀ M, Commute (eQGen hAnc M) A) ∧ Commute (lcuProjGen D.lcuSub) A ∧ Commute D.S.1 A)
    (L : List (Matrix (Fin 2) (Fin 2) ℂ × Bool)) :
    Commute (PhotochemistrySolution.GQSP.gqspOp (eQGen hAnc) (walkOpShared D) L) A :=
  commute_gqspOp_refl_mul_shared (eQGen hAnc)
      (walkOpShared_conjTranspose D) h.1 h.2.1 h.2.2 L
end QuantumComputation.Specs.PhotochemistrySolution.OvBidir
end
end

set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
open Operator QProg DynamicCircuit PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop
def ancWOfScr (scrW : ℕ) : ℕ := 34 + scrW + 70 + 1
abbrev totDimCompactGen (scrW : ℕ) : ℕ := systemQubits_frozen + ancWOfScr scrW
abbrev locSysCompactGen (scrW : ℕ) : QRegister systemQubits_frozen (totDimCompactGen scrW) :=
  .block 0 systemQubits_frozen (by unfold totDimCompactGen; omega)
abbrev locAncCompactGen (scrW : ℕ) : QRegister (ancWOfScr scrW) (totDimCompactGen scrW) :=
    .block systemQubits_frozen (ancWOfScr scrW) le_rfl
abbrev locGrad34CompactGen (scrW : ℕ) : QRegister 34 (totDimCompactGen scrW) :=
  (locAncCompactGen scrW).slice 0 34 (by unfold ancWOfScr; omega)
abbrev locCat8SharedCompactGen (scrW : ℕ) : QRegister 8 (totDimCompactGen scrW) :=
    (locGrad34CompactGen scrW).slice 26 8 le_rfl
abbrev locQCompactGen (scrW : ℕ) : Wire (totDimCompactGen scrW) :=
  locAncCompactGen scrW ⟨34 + scrW + 70, by unfold ancWOfScr; omega⟩
def locSysPoly (sysW scrW : ℕ) : QRegister sysW (sysW + ancWOfScr scrW) :=
    .block 0 sysW ((Nat.zero_add _).trans_le (Nat.le_add_right _ _))
def locAncPoly (sysW scrW : ℕ) : QRegister (ancWOfScr scrW) (sysW + ancWOfScr scrW) :=
    .block sysW (ancWOfScr scrW) le_rfl
def locGrad34Poly (sysW scrW : ℕ) : QRegister 34 (sysW + ancWOfScr scrW) :=
  (locAncPoly sysW scrW).slice 0 34 (by unfold ancWOfScr; omega)
def locCat8SharedPoly (sysW scrW : ℕ) : QRegister 8 (sysW + ancWOfScr scrW) :=
    (locGrad34Poly sysW scrW).slice 26 8 le_rfl
def locQPoly (sysW scrW : ℕ) : Wire (sysW + ancWOfScr scrW) :=
  locAncPoly sysW scrW ⟨34 + scrW + 70, by unfold ancWOfScr; omega⟩
noncomputable def projOneQPoly (sysW scrW : ℕ) : Operator (2 ^ (sysW + ancWOfScr scrW)) :=
    (QRegister.singleton (locQPoly sysW scrW)).basisOutcomeProjector 1
noncomputable def lcuProjPoly (sysW scrW : ℕ) {l : ℕ} (lcuSub : QRegister l (ancWOfScr scrW)) :
    Operator (2 ^ (sysW + ancWOfScr scrW)) :=
    ((locAncPoly sysW scrW).compose lcuSub).basisOutcomeProjector 0
noncomputable def cat8SharedProjPoly (sysW scrW : ℕ) : Operator (2 ^ (sysW + ancWOfScr scrW)) :=
    (locCat8SharedPoly sysW scrW).embedMatrix (Matrix.vecMulVec (PgBase.phaseGradientState 8)
    (star (PgBase.phaseGradientState 8)))
def OffIndexAndScratchPoly (sysW scrW : ℕ) {k l s : ℕ} (lcuSub : QRegister l (ancWOfScr scrW))
    (scrSub : QRegister s (ancWOfScr scrW)) (r : QRegister k (sysW + ancWOfScr scrW)) : Prop :=
    ∀ i, ∃ j : Fin (ancWOfScr scrW), r i = locAncPoly sysW scrW j ∧ j ∉ Set.range lcuSub.wires ∧
    j ∉ Set.range scrSub.wires
noncomputable abbrev projOneQCompactGen (scrW : ℕ) := projOneQPoly systemQubits_frozen scrW
noncomputable abbrev lcuProjCompactGen (scrW : ℕ) {l : ℕ} (lcuSub : QRegister l (ancWOfScr scrW)) :=
    lcuProjPoly systemQubits_frozen scrW lcuSub
noncomputable abbrev cat8SharedProjCompactGen (scrW : ℕ) :=
    cat8SharedProjPoly systemQubits_frozen scrW
structure BlockApproxSpecGen {sysW : ℕ} (H : Operator (2 ^ sysW))
    (α c εBlock : ℝ) (aImpl : Operator (2 ^ sysW)) : Prop where
  α_pos : 0 < α
  α_time_le : α * evolutionTime_frozen ≤ 4231872
  aImpl_herm : aImplᴴ = aImpl
  aImpl_norm : ‖aImpl‖ ≤ 1
  εBlock_nonneg : 0 ≤ εBlock
  εBlock_le : 4231872 * εBlock ≤ 100
  aImpl_approx : ‖aImpl - ((α : ℂ)⁻¹) • (H - (c : ℂ) • 1)‖ ≤ εBlock
structure SelectLocalSpecGen {sysW scrW scrL lcuL : ℕ}
    (scrSub : QRegister scrL (ancWOfScr scrW))
    (lcuSub : QRegister lcuL (ancWOfScr scrW))
    (aImpl : Operator (2 ^ sysW))
    (S cselU reflU : Unitary (2 ^ (sysW + ancWOfScr scrW))) : Prop where
  S_herm : S.1ᴴ = S.1
  S_comm : ∀ {k : ℕ} (r : QRegister k (sysW + ancWOfScr scrW))
    (M : Operator (2 ^ k)), OffIndexAndScratchPoly sysW scrW lcuSub scrSub r →
      Commute S.1 (r.embedMatrix M)
  S_scr : Commute S.1 (((locAncPoly sysW scrW).compose scrSub).basisOutcomeProjector 0)
  hblock :
    lcuProjPoly sysW scrW lcuSub * S.1 * lcuProjPoly sysW scrW lcuSub *
        ((locAncPoly sysW scrW).compose scrSub).basisOutcomeProjector 0 =
      (locSysPoly sysW scrW).embedMatrix aImpl * lcuProjPoly sysW scrW lcuSub *
        ((locAncPoly sysW scrW).compose scrSub).basisOutcomeProjector 0
  cselU_cat :
    cselU.1 * cat8SharedProjPoly sysW scrW =
      (1 - projOneQPoly sysW scrW * (1 - S.1)) * cat8SharedProjPoly sysW scrW
  reflU_eq :
    reflU.1 = 1 - (2 : ℂ) • (projOneQPoly sysW scrW * (1 - lcuProjPoly sysW scrW lcuSub))
structure LocalUnitary (d : ℕ) where
  u : Unitary (2 ^ d)
end QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
end
end

noncomputable section
open Operator QProg Matrix QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectApprox
namespace QuantumComputation.Specs.PhotochemistrySolution.ClusterPotSlice
attribute [local irreducible] SpecDefs.systemQubits_frozen
instance (priority := 100000) instNeZeroHPowNatOfNat_gridClusterPotSlice {k : ℕ} :
    NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
theorem nucP_lt (a : Fin 47) : a.val < 234 := Nat.lt_trans a.isLt (by decide)
theorem elecP_lt (e : Fin 187) : 47 + e.val < 234 := by omega
def nucP (a : Fin 47) : Particle_frozen := ⟨a.val, nucP_lt a⟩
def elecP (e : Fin 187) : Particle_frozen := ⟨47 + e.val, elecP_lt e⟩
theorem sum_particle_split {α : Type*} [AddCommMonoid α] (f : Particle_frozen → α) : (∑ i, f i) =
    (∑ a, f (nucP a)) + (∑ e, f (elecP e)) := by
  let g (i : ℕ) := f ⟨i % 234, Nat.mod_lt i (by decide)⟩
  have hS {n} (p : Fin n → Particle_frozen) (k : ℕ → ℕ)
      (hk : ∀ x (h : x < n), (p ⟨x, h⟩).val = k x) :
      (∑ x, f (p x)) = ∑ x ∈ Finset.range n, g (k x) :=
    (Finset.sum_fin_eq_sum_range _).trans (Finset.sum_congr rfl fun x hx ↦ by
      have hlt := Finset.mem_range.mp hx
      simpa [hlt, g] using congrArg f
        (Fin.ext ((hk x hlt).trans (Nat.mod_eq_of_lt (hk x hlt ▸ (p ⟨x, hlt⟩).isLt)).symm)))
  rw [hS (fun x ↦ x) (fun x ↦ x) fun _ _ ↦ rfl, hS nucP (fun x ↦ x) fun _ _ ↦ rfl,
    hS elecP (47 + ·) fun _ _ ↦ rfl, ← Finset.sum_range_add g 47 187]
def wIdleA : ℕ := 37969163
def wKinParticle (i : Particle_frozen) : ℕ :=
    if i.val < 23 then 7262 else if i.val < 43 then 86491 else if i.val <
    46 then 6223 else if i.val < 47 then 5448 else 158810294
def wIdleOpt : ℕ := 616742114
def wKinParticleOpt (i : Particle_frozen) : ℕ :=
    if i.val < 23 then 29311 else if i.val < 43 then 349091 else if i.val <
    46 then 25118 else if i.val < 47 then 21990 else 640983863
theorem grid_small_sums :
    (454893117492 + 5726389410 + 89098337823 + wIdleA = 2 ^ 39) ∧
    ((∑ i, ∑ _w : Fin 3, wKinParticle i) = 89098337823) ∧
    (1815923594694 + 22867711650 + 359615207094 + wIdleOpt = 2 ^ 41) ∧
    ((∑ i, ∑ _w : Fin 3, wKinParticleOpt i) = 359615207094) ∧
    ((∑ a, charge_frozen (nucP a)) = 187) ∧
    ((∑ a, charge_frozen (nucP a) ^ 2) = 1059) ∧
    (∀ a : Fin 47, 0 ≤ charge_frozen (nucP a)) := by decide +kernel
theorem fin187_offdiag :
    ∀ e : Fin 187,
      (∑ e' : Fin 187, if e = e' then (0 : ℕ) else 1) = 186 ∧
      (∑ e' : Fin 187, if e' = e then (0 : ℕ) else 1) = 186 := by decide +kernel
theorem grid_pair_blocks :
    ((∑ a : Fin 47, ∑ b : Fin 47,
        if nucP a = nucP b then (0 : ℤ) else |charge_frozen (nucP a) * charge_frozen (nucP b)|) =
            33910) ∧
    ((∑ a : Fin 47, ∑ e : Fin 187,
        if nucP a = elecP e then (0 : ℤ) else |charge_frozen (nucP a) * charge_frozen (elecP e)|) =
            34969) ∧
    ((∑ e : Fin 187, ∑ a : Fin 47,
        if elecP e = nucP a then (0 : ℤ) else |charge_frozen (elecP e) * charge_frozen (nucP a)|) =
            34969) ∧
    ((∑ e1 : Fin 187, ∑ e2 : Fin 187,
        if elecP e1 = elecP e2 then (0 : ℤ)
        else |charge_frozen (elecP e1) * charge_frozen (elecP e2)|) = 34782) := by decide +kernel
theorem pair_charge_sum_eq :
    (∑ i : Particle_frozen, ∑ j : Particle_frozen, if i = j then (0 : ℤ) else |charge_frozen i *
        charge_frozen j|) =
      138630 := by
  obtain ⟨s1, s2, s3, s4⟩ := grid_pair_blocks
  rw [sum_particle_split]; simp_rw [sum_particle_split, Finset.sum_add_distrib]
  rw [s1, s2, s3, s4]; norm_num
theorem grid_static_sums :
    (454893117492 + 5726389410 + 89098337823 + wIdleA = 2 ^ 39) ∧
    ((∑ i, ∑ _w : Fin 3, wKinParticle i) = 89098337823) ∧
    (1815923594694 + 22867711650 + 359615207094 + wIdleOpt = 2 ^ 41) ∧
    ((∑ i, ∑ _w : Fin 3, wKinParticleOpt i) = 359615207094) ∧
    ((∑ a, charge_frozen (nucP a)) = 187) ∧
    ((∑ a, charge_frozen (nucP a) ^ 2) = 1059) ∧
    ((∑ e1 : Fin 187, ∑ e2 : Fin 187, if e1 = e2 then (0 : ℕ) else 1) = 34782) ∧
    (∀ e : Fin 187, (∑ e', if e = e' then (0 : ℕ) else 1) = 186 ∧
      (∑ e', if e' = e then (0 : ℕ) else 1) = 186) ∧
    ((∑ i, ∑ j, if i = j then (0 : ℤ) else |charge_frozen i * charge_frozen j|) = 138630) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := grid_small_sums
  have h7 : (∑ e1 : Fin 187, ∑ e2 : Fin 187, if e1 = e2 then (0 : ℕ) else 1) = 34782 := by
    simp_rw [(fin187_offdiag _).1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fin187_offdiag, pair_charge_sum_eq⟩
theorem grid_real_sums :
    ((∑ a, (charge_frozen (nucP a) : ℝ)) = 187) ∧ ((∑ a, (charge_frozen (nucP a) : ℝ) ^ 2) = 1059) ∧
    ((∑ e1 : Fin 187, ∑ e2 : Fin 187, if e1 = e2 then (0 : ℝ) else 1) = 34782) ∧
    (∀ e : Fin 187, (∑ e', if e = e' then (0 : ℝ) else 1) = 186 ∧
      (∑ e', if e' = e then (0 : ℝ) else 1) = 186) ∧
    ((∑ i : Particle_frozen, ∑ j : Particle_frozen,
      if i = j then (0 : ℝ) else |(charge_frozen i : ℝ) * (charge_frozen j : ℝ)|) = 138630) := by
  let s := grid_static_sums.2.2.2.2
  have f1 := congrArg (Int.cast (R := ℝ)) s.1
  have f2 := congrArg (Int.cast (R := ℝ)) s.2.1
  have f3 := congrArg (Nat.cast (R := ℝ)) s.2.2.1
  have f5 := congrArg (Int.cast (R := ℝ)) s.2.2.2.2
  have f4 : ∀ e, _ ∧ _ := fun e ↦
    ⟨congrArg (Nat.cast (R := ℝ)) (s.2.2.2.1 e).1,
     congrArg (Nat.cast (R := ℝ)) (s.2.2.2.1 e).2⟩
  simp only [Int.cast_sum, Int.cast_pow, apply_ite (Int.cast (R := ℝ)), Int.cast_zero, Int.cast_abs,
      Int.cast_mul, Int.cast_ofNat, Nat.cast_sum, apply_ite (Nat.cast (R := ℝ)), Nat.cast_zero,
      Nat.cast_one, Nat.cast_ofNat] at f1 f2 f3 f4 f5; exact ⟨f1, f2, f3, f4, f5⟩
theorem gridSpacing_eq_rat : gridSpacing_frozen = (44 / 0.529177210544) / 255 := by
  unfold gridSpacing_frozen boxWidth_frozen gridBits_frozen; norm_num
theorem gridSpacing_pos : 0 < gridSpacing_frozen := by rw [gridSpacing_eq_rat]; norm_num
end QuantumComputation.Specs.PhotochemistrySolution.ClusterPotSlice

namespace QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice
open scoped Matrix.Norms.L2Operator
open DynamicCircuit PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
attribute [local irreducible] systemQubits_frozen
attribute [local semireducible] atomicMass_frozen atomicNumber_frozen wKinParticle wKinParticleOpt
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
--   maxRecDepth=512
abbrev OpSys := Operator (2 ^ systemQubits_frozen)
abbrev OpGrid := Operator (2 ^ gridBits_frozen)
abbrev qU : OpGrid := qftGridUnitary.1
/-- Kinetic operator slice for particle `i` along axis `w`. -/
def kinNormOp (i : Particle_frozen) (w : Fin 3) : OpSys :=
  (coordinateRegister_frozen i w).embedMatrix
    (qftGridUnitary.1ᴴ *
      diagReal (fun k ↦ ((twosComplement_frozen k : ℝ) ^ 2 - 8192) / 8192) *
      qftGridUnitary.1)
/-- Scaled kinetic LCU operator sum. -/
def tImplOf (cBits : ℕ) (wKin : Particle_frozen → ℕ) (α : ℝ) : OpSys :=
  ∑ i : Particle_frozen, ∑ w : Fin 3, (((wKin i : ℝ) / (2 ^ cBits : ℝ)) * α : ℂ) • kinNormOp i w
/-- Constant identity shift from kinetic terms. -/
def shiftKin : ℝ :=
    ∑ i : Particle_frozen, ∑ _w : Fin 3, 8192 * (2 * Real.pi ^ 2 / (boxWidth_frozen ^ 2 *
    mass_frozen i))
theorem opNorm_conj_qft_diagReal_le (f : Fin (2 ^ gridBits_frozen) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ k, |f k| ≤ B) : ‖qUᴴ * diagReal f * qU‖ ≤ B :=
  (opNorm_conj_unitary_le qftGridUnitary _).trans (opNorm_diagReal_le f hB hf)
theorem tc_sq_le (k : Fin (2 ^ gridBits_frozen)) :
    |(twosComplement_frozen k : ℝ) ^ 2 - 8192| ≤ 8192 := by
  have hlo := Int.le_bmod (x := (k.val : ℤ)) (by decide : 0 < 256)
  have hhi := Int.bmod_le (x := (k.val : ℤ)) (by decide : 0 < 256)
  have h1 : (-128 : ℝ) ≤ (twosComplement_frozen k : ℝ) := by
    exact_mod_cast (show (-128 : ℤ) ≤ (k.val : ℤ).bmod 256 by omega)
  have h2 : (twosComplement_frozen k : ℝ) ≤ 127 := by
    exact_mod_cast (show (k.val : ℤ).bmod 256 ≤ 127 by omega)
  have ha : |(twosComplement_frozen k : ℝ)| ≤ |(128 : ℝ)| := by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 128)]
    exact abs_le.mpr ⟨h1, by linarith⟩
  exact abs_le.mpr
    ⟨by linarith [sq_nonneg (twosComplement_frozen k : ℝ)], by linarith [sq_le_sq.mpr ha]⟩
theorem opNorm_kinNormOp_le (i : Particle_frozen) (w : Fin 3) : ‖kinNormOp i w‖ ≤ 1 := by
  refine (opNorm_embedMatrix_le _ _).trans (opNorm_conj_qft_diagReal_le _ (by norm_num) fun k ↦ ?_)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8192), div_le_one (by norm_num)]
  exact tc_sq_le k
theorem tImplOf_herm (cB : ℕ) (wK : Particle_frozen → ℕ) (α : ℝ) : (tImplOf cB wK α)ᴴ =
    tImplOf cB wK α := by
  unfold tImplOf kinNormOp
  rw [Matrix.conjTranspose_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.conjTranspose_sum]; refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hc : (((wK i : ℝ) / (2 ^ cB : ℝ)) * α : ℂ) = (((wK i : ℝ) / (2 ^ cB : ℝ) * α : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Matrix.conjTranspose_smul, ← (coordinateRegister_frozen i w).embedMatrix_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      diagReal_conjTranspose, Matrix.mul_assoc, Complex.star_def, Complex.conj_ofReal]
theorem diagReal_smul_kin (c : ℝ) (f : Fin (2 ^ gridBits_frozen) → ℝ) : (c : ℂ) • diagReal f =
    diagReal (fun k ↦ c * f k) := by ext a b; by_cases h : a = b <;> simp [diagReal, h]
theorem dR_sub_kin (f g : Fin (2 ^ gridBits_frozen) → ℝ) : diagReal f - diagReal g =
    diagReal (fun k ↦ f k - g k) := by
  unfold diagReal; rw [Matrix.diagonal_sub]; congr 1; ext k; simp
theorem smul_qft_diagReal_kin (c : ℝ) (f : Fin (2 ^ gridBits_frozen) → ℝ) :
    ((c : ℂ) • (qUᴴ * diagReal f * qU)) = qUᴴ * diagReal (fun k ↦ c * f k) * qU := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, diagReal_smul_kin]
theorem qft_diagReal_sub_kin (f g : Fin (2 ^ gridBits_frozen) → ℝ) : qUᴴ * diagReal f * qU - qUᴴ *
    diagReal g * qU = qUᴴ * diagReal (fun k ↦ f k - g k) * qU := by
  rw [← dR_sub_kin, ← Matrix.sub_mul, ← Matrix.mul_sub]
theorem norm_nat_div_two_pow (n k : ℕ) : ‖(((n : ℝ) / (2 ^ k : ℝ)) : ℂ)‖ = (n : ℝ) / (2 ^ k : ℝ)
    := by
  rw [norm_div, Complex.norm_of_nonneg (Nat.cast_nonneg n),
      Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ k : ℝ))]
theorem kin_scalar_sub_eq_kin (a b t : ℝ) : a * t - 8192 * a * 1 - b * ((t - 8192) / 8192) =
    (a - b / 8192) * (t - 8192) := by ring
theorem kin_term_sub_eq_kin (i : Particle_frozen) (w : Fin 3)
    (a b : ℝ) : ((a : ℂ) • (coordinateRegister_frozen i w).embedMatrix (qUᴴ *
    Matrix.diagonal (fun k ↦ (twosComplement_frozen k ^ 2 : ℂ)) * qU)) -
    ((8192 * a : ℝ) : ℂ) • (1 : OpSys) -
    ((b : ℂ) • (coordinateRegister_frozen i w).embedMatrix (qUᴴ * diagReal (fun k ↦
    ((twosComplement_frozen k : ℝ) ^ 2 - 8192) / 8192) * qU)) =
    (coordinateRegister_frozen i w).embedMatrix (qUᴴ * diagReal (fun k ↦ (a - b / 8192) *
    ((twosComplement_frozen k : ℝ) ^ 2 - 8192)) * qU) := by
  let cR := coordinateRegister_frozen i w
  have hd1 : diagReal (fun _ : Fin (2 ^ gridBits_frozen) ↦ (1 : ℝ)) = 1 := by
    unfold diagReal; simp [Matrix.diagonal_one]
  have fqft : qUᴴ * (1 : OpGrid) * qU = 1 := by
    rw [Matrix.mul_one]; exact qftMatrix_conjTranspose_mul_self gridBits_frozen
  have h1 : (1 : OpSys) = cR.embedMatrix (qUᴴ * diagReal (fun _ ↦ 1) * qU) := by
    rw [hd1, fqft, cR.embedMatrix_one]
  have hdk : Matrix.diagonal (fun k : Fin (2 ^ gridBits_frozen) ↦
      (twosComplement_frozen k ^ 2 : ℂ)) = diagReal (fun k ↦ (twosComplement_frozen k : ℝ) ^ 2)
      := by unfold diagReal; congr 1; ext k; simp
  rw [h1, hdk, ← cR.embedMatrix_smul, ← cR.embedMatrix_smul, ← cR.embedMatrix_smul,
      ← embedMatrix_sub,
      ← embedMatrix_sub]; refine congrArg cR.embedMatrix ?_; rw [smul_qft_diagReal_kin,
      smul_qft_diagReal_kin, smul_qft_diagReal_kin, qft_diagReal_sub_kin, qft_diagReal_sub_kin]
  refine congrArg (fun M ↦ qUᴴ * M * qU) (congrArg Matrix.diagonal (funext fun k ↦ ?_))
  exact congrArg Complex.ofReal (kin_scalar_sub_eq_kin a b ((twosComplement_frozen k : ℝ) ^ 2))
theorem kin_sum_sub_eq_kin (cB : ℕ) (wK : Particle_frozen → ℕ) (α : ℝ) : kineticEnergy_frozen -
    (shiftKin : ℂ) • (1 : OpSys) - tImplOf cB wK α = ∑ i, ∑ w,
    (coordinateRegister_frozen i w).embedMatrix (qUᴴ * diagReal (fun k ↦ (2 * Real.pi ^ 2 /
    (boxWidth_frozen ^ 2 * mass_frozen i) - (((wK i : ℝ) / (2 ^ cB : ℝ)) * α) / 8192) *
    ((twosComplement_frozen k : ℝ) ^ 2 - 8192)) * qU) := by
  unfold kineticEnergy_frozen shiftKin tImplOf kinNormOp
  change (∑ i, ∑ w,
      ((2 * Real.pi ^ 2 / (boxWidth_frozen ^ 2 *
      mass_frozen i) : ℝ) : ℂ) • (coordinateRegister_frozen i w).embedMatrix (qUᴴ *
      Matrix.diagonal (fun k ↦ (twosComplement_frozen k ^ 2 : ℂ)) * qU)) -
      ((∑ i, ∑ _w : Fin 3, 8192 * (2 * Real.pi ^ 2 / (boxWidth_frozen ^ 2 *
      mass_frozen i)) : ℝ) : ℂ) • 1 - (∑ i, ∑ w, (((wK i : ℝ) / (2 ^ cB : ℝ)) *
      α : ℂ) • (coordinateRegister_frozen i w).embedMatrix (qUᴴ * diagReal (fun k ↦
      ((twosComplement_frozen k : ℝ) ^ 2 - 8192) / 8192) * qU)) = _
  rw [Complex.ofReal_sum, Finset.sum_smul];
  simp_rw [Complex.ofReal_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
  have hc3 : (((wK i : ℝ) / (2 ^ cB : ℝ)) * α : ℂ) =
      (((wK i : ℝ) / (2 ^ cB : ℝ) * α : ℝ) : ℂ) := by push_cast; rfl
  rw [hc3];
  exact kin_term_sub_eq_kin i w (2 * Real.pi ^ 2 / (boxWidth_frozen ^ 2 * mass_frozen i))
      (((wK i : ℝ) / (2 ^ cB : ℝ)) * α)
abbrev meR_kin : ℝ := 5.485799090441e-4
theorem pi_sq_bounds_kin : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 ∧ Real.pi ^ 2 <
    (3.14159265358979323847 : ℝ) ^ 2 :=
  ⟨by nlinarith [Real.pi_gt_d20], by nlinarith [Real.pi_lt_d20, Real.pi_pos]⟩
theorem m_spec_kin (i : Particle_frozen) : (i.val < 23 ∧ mass_frozen i = atomicMass_frozen 6 /
    meR_kin - 6) ∨ (¬(i.val < 23) ∧ i.val < 43 ∧ mass_frozen i = atomicMass_frozen 1 / meR_kin -
    1) ∨ (¬(i.val < 23) ∧ ¬(i.val < 43) ∧ i.val < 46 ∧ mass_frozen i = atomicMass_frozen 7 /
    meR_kin - 7) ∨ (¬(i.val < 23) ∧ ¬(i.val < 43) ∧ ¬(i.val < 46) ∧ i.val < 47 ∧ mass_frozen i =
    atomicMass_frozen 8 / meR_kin - 8) ∨ (¬(i.val < 23) ∧ ¬(i.val < 43) ∧ ¬(i.val < 46) ∧
    ¬(i.val < 47) ∧ mass_frozen i = 1) := by
  by_cases h1 : i.val < 23 <;> by_cases h2 : i.val < 43 <;> by_cases h3 : i.val < 46 <;>
    by_cases h4 : i.val < 47 <;> first | omega |
    simp [mass_frozen, atomicNumber_frozen, meR_kin, Fin.lt_def, h1, h2, h3, h4]
theorem ht_zIdle_le_kin (cB kS : ℕ) (wK : Particle_frozen → ℕ) (α : ℝ) (hα0 : 0 < α)
    (hkS : (∑ i, ∑ _w : Fin 3, wK i) = kS) : ‖((α : ℂ)⁻¹) • tImplOf cB wK α‖ ≤ (kS : ℝ) /
    (2 ^ cB : ℝ) := by
  have hα := ne_of_gt hα0
  have heq : ((α : ℂ)⁻¹) • tImplOf cB wK α = ∑ i, ∑ w,
      (((wK i : ℝ) / (2 ^ cB : ℝ)) : ℂ) • kinNormOp i w := by
    unfold tImplOf; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [smul_smul]; refine congrArg (· • kinNormOp i w) ?_; push_cast; field_simp [hα]
  have hks : (∑ i, ∑ _w : Fin 3, (wK i : ℝ) / (2 ^ cB : ℝ)) = (kS : ℝ) / (2 ^ cB : ℝ) := by
    simp_rw [← Finset.sum_div]
    have h := congrArg (Nat.cast (R := ℝ)) hkS; simp only [Nat.cast_sum] at h; rw [h]
  rw [heq, ← hks]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ ↦ ?_))
  refine (norm_smul_le _ _).trans ?_; rw [norm_nat_div_two_pow]
  exact mul_le_of_le_one_right (div_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _))
      (opNorm_kinNormOp_le i w)
end QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TelescopeSlice

open Operator QProg DynamicCircuit Matrix Real PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.KinNormSlice
  PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotentialDecomp (gridDistSq
    gridDistSq_comm)
open scoped Matrix.Norms.L2Operator
/-! ## Section 1: Open-Box Squared Distance & `Fin 8` Short-Range Bucket Bridge -/

/-- Exact 3D open-box squared grid distance `∑ w, openBoxDist1D (u_w) (v_w) ^ 2 ∈ [0, 195075]`. -/
def pairOpenDistSq (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) : ℕ :=
  ∑ w : Fin 3, openBoxDist1D ((coordinateRegister_frozen i w).extractIndex x)
    ((coordinateRegister_frozen j w).extractIndex x) ^ 2
/-- Short-range `Fin 8` bucket index `(fin8Bin (pairOpenDistSq x i j)).val ∈ [0, 7]`. -/
def pairShortBin (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) : ℕ :=
    (fin8Bin (pairOpenDistSq x i j)).val
theorem openBoxDist1D_sq_cast (u v : Fin 256) : ((openBoxDist1D u v ^ 2 : ℕ) : ℤ) =
    (twosComplement_frozen u - twosComplement_frozen v) ^ 2 := by
  unfold openBoxDist1D; rw [Nat.cast_pow, Int.natAbs_sq]
theorem pairOpenDistSq_cast_eq_gridDistSq (x : Fin (2 ^ systemQubits_frozen))
    (i j : Particle_frozen) : (pairOpenDistSq x i j : ℤ) = gridDistSq x i j := by
  unfold pairOpenDistSq gridDistSq position_frozen; rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun w _ ↦
      openBoxDist1D_sq_cast ((coordinateRegister_frozen i w).extractIndex x)
      ((coordinateRegister_frozen j w).extractIndex x)
theorem pairOpenDistSq_comm (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) :
    pairOpenDistSq x i j = pairOpenDistSq x j i :=
  Int.ofNat_inj.mp
      (by rw [pairOpenDistSq_cast_eq_gridDistSq, pairOpenDistSq_cast_eq_gridDistSq,
            gridDistSq_comm])
/-! ## Section 2: Zero-Coin-Error Rational Denominators Across All 17 Active Sectors -/
theorem speciesZ_cast_ne_zero (s : Fin 4) : (speciesZ s : ℝ) ≠ 0 := by
  fin_cases s <;> norm_num [speciesZ]
theorem not_both_species3_all : ∀ n1 n2 : Fin 47, n1 ≠ n2 → ¬(nucSpecies n1 = 3 ∧ nucSpecies n2 = 3)
    := by decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.TelescopeSlice

end

noncomputable section
open QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix Real PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.KinNormSlice
  PhotochemistrySolution.TelescopeSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
/-- Unscaled (`α`-free) potential diagonal sum over `.ee`, `.nn`, and `.en` coin items. -/
def vDiagGenZeroNErem (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (x : Fin (2 ^ systemQubits_frozen)) : ℝ :=
  (∑ n1 : Fin 47, ∑ e1 : Fin 187, ∑ e2 : Fin 187,
    if e1 < e2 then ((wEE (nucSpecies n1) : ℝ) / (2 ^ 41 : ℝ)) * vEE x n1 e1 e2 else 0) +
  (∑ n1 : Fin 47, ∑ n2 : Fin 47, ∑ e1 : Fin 187,
    if n1 < n2 then
      ((wNN (nucSpecies n1) (nucSpecies n2) : ℝ) / (2 ^ 41 : ℝ)) * vNN x n1 n2 e1
    else 0) -
  (∑ n1 : Fin 47, ∑ e1 : Fin 187,
    ((wEN (nucSpecies n1) : ℝ) / (2 ^ 41 : ℝ)) * vEN x n1 e1)
/--
Normalized block-encoded system operator for arbitrary 41-bit coin weights `(wEE, wNN, wEN,
wKin, wIdle)`.
-/
def aImplGenZeroNEremOf (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ)
    (wKin : Particle_frozen → ℕ) (wIdle : ℕ) (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 →
    Fin 187 → Fin 187 → ℝ) (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ) : OpSys :=
  (((wIdle : ℝ) / (2 ^ 41 : ℝ)) : ℂ) • (1 : OpSys) +
  (∑ i : Particle_frozen, ∑ w : Fin 3, (((wKin i : ℝ) / (2 ^ 41 : ℝ)) : ℂ) • kinNormOp i w) +
  diagReal (vDiagGenZeroNErem wEE wNN wEN vEE vNN vEN)
/-- Exact `S = 2 ^ 35` `.ee` threshold denominator for arbitrary `(wEE, α)`. -/
def denomGenEE (wEE : Fin 4 → ℕ) (α : ℝ) (s : Fin 4) : ℝ :=
  ((wEE s : ℝ) * α * 187 * gridSpacing_frozen) / (64 * (speciesZ s : ℝ))
/-- Exact `S = 2 ^ 35` `.nn` threshold denominator for arbitrary `(wNN, α)`. -/
def denomGenNN (wNN : Fin 4 → Fin 4 → ℕ) (α : ℝ) (s1 s2 : Fin 4) : ℝ :=
  ((wNN s1 s2 : ℝ) * α * 187 * gridSpacing_frozen) / (64 * ((speciesZ s1 * speciesZ s2 : ℕ) : ℝ))
/-- Exact `S = 2 ^ 35` `.en` threshold denominator for arbitrary `(wEN, α)`. -/
def denomGenEN (wEN : Fin 4 → ℕ) (α : ℝ) (s : Fin 4) : ℝ :=
  ((wEN s : ℝ) * α * gridSpacing_frozen) / (64 * (speciesZ s : ℝ))
/-- Scaled potential diagonal sum `α * vDiagGenZeroNErem` for arbitrary `(wEE, wNN, wEN, α)`. -/
def vImplGenDiag (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ) (α : ℝ)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (x : Fin (2 ^ systemQubits_frozen)) : ℝ :=
  α * vDiagGenZeroNErem wEE wNN wEN vEE vNN vEN x
/-- Scaled potential operator `diagReal (vImplGenDiag ...)` on `OpSys`. -/
def vImplGenOf (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ) (α : ℝ)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ) : OpSys :=
  diagReal (vImplGenDiag wEE wNN wEN α vEE vNN vEN)
/-- Total block-encoding spectral error cap `α⁻¹ * (εKin + εPot)` for arbitrary `(α, εKin)`. -/
def epsBlockGenOf (α εKin εEE εNN εEN : ℝ) : ℝ :=
    α⁻¹ * (εKin + (17391 * εEE + 16955 * εNN + 34969 * εEN) / ((2 ^ 35 : ℝ) * gridSpacing_frozen))
end QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect

namespace QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix Real PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.KinNormSlice PhotochemistrySolution.TelescopeSlice
  PhotochemistrySolution.GenWeightsSelect
/--
Hamiltonian block-encoding scale (`M0 = 3713, n_alpha = 1,369,243,200,000`,
`s = alphaFermatCoin * evolutionTime = 3,336,127.99727 <= 3,336,128`).
-/
def alphaFermatCoin : ℝ := (2 ^ 55 : ℝ) / (1369243200000 * gridSpacing_frozen)
theorem alphaFermatCoin_pos : 0 < alphaFermatCoin := by
  unfold alphaFermatCoin; have := gridSpacing_pos; positivity
/-- Proton-pair `.ee` subweight (`167,085` per unordered electron pair per proton). -/
abbrev qEEFermatCoin : ℕ := 167085
/-- Per-item 41-bit coin weights on `.ee` (`0=H, 1=C, 2=N, 3=O`). -/
def wEESpeciesFermatCoin : Fin 4 → ℕ
  | 0 => 334170
  | 1 => 2005020
  | 2 => 2339190
  | 3 => 2673360
/-- Per-item 41-bit coin weights on `.nn` (`s1, s2 : Fin 4`, symmetric). -/
def wNNSpeciesFermatCoin (s1 s2 : Fin 4) : ℕ :=
  let a := min s1.val s2.val; let b := max s1.val s2.val
  match a, b with
  | 0, 0 => 167085  | 0, 1 => 1002510
  | 0, 2 => 1169595 | 0, 3 => 1336680
  | 1, 1 => 6015060 | 1, 2 => 7017570
  | 1, 3 => 8020080 | 2, 2 => 8187165
  | 2, 3 => 9356760 | _, _ => 0
def sumTreeW (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, lo => f lo
  | k + 1, lo => sumTreeW f k lo + sumTreeW f k (lo + 2 ^ k)
theorem sumTreeW_eq_Ico (f : ℕ → ℕ) :
    ∀ k lo, sumTreeW f k lo = ∑ x ∈ Finset.Ico lo (lo + 2 ^ k), f x
  | 0, lo => by simp [sumTreeW]
  | k + 1, lo => by
    rw [sumTreeW, sumTreeW_eq_Ico f k lo, sumTreeW_eq_Ico f k (lo + 2 ^ k),
      show lo + 2 ^ k + 2 ^ k = lo + 2 ^ (k + 1) by rw [pow_succ]; omega]
    exact Finset.sum_Ico_consecutive f (Nat.le_add_right _ _)
      (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)) lo)
theorem sum_fin_eq_sumTreeW (N k : ℕ) (hk : N ≤ 2 ^ k) (g : Fin N → ℕ) : (∑ i : Fin N, g i) =
    sumTreeW (fun x ↦ if h : x < N then g ⟨x, h⟩ else 0) k 0 := by
  rw [Finset.sum_fin_eq_sum_range, sumTreeW_eq_Ico, zero_add, ← Finset.range_eq_Ico]
  exact Finset.sum_subset (Finset.range_mono hk) fun x _ hx ↦
    dite_eq_right fun hlt ↦ hx (Finset.mem_range.mpr hlt)
/-- Uniform exact `.ee` denominator (`gain = 1`). -/
def denomEEFermatCoin : ℝ := (4580550048152027136 : ℝ) / 178286875
/-- Uniform exact `.nn` denominator on all active nuclear pairs `n1 < n2` (`gain = 2`). -/
def denomNNFermatCoinVal : ℝ := (2290275024076013568 : ℝ) / 178286875
/--
Species-indexed `.nn` denominator (`0` on vacuous `(O, O)` , `denomNNFermatCoinVal` otherwise).
-/
def denomNNFermatCoin (s1 s2 : Fin 4) : ℝ :=
  if s1.val = 3 ∧ s2.val = 3 then 0 else denomNNFermatCoinVal
/-- Exact `.en` denominator (`gain = 9` on `H, N, O`; `gain = 10` on `C`). -/
def denomENFermatCoin : Fin 4 → ℝ
  | 1 => (2290275024076013568 : ℝ) / 891434375
  | _ => (1526850016050675712 : ℝ) / 534860625
theorem nucSpecies_pair_not_both_three {n1 n2 : Fin 47} (hlt : n1 < n2) : ¬ (nucSpecies n1 = 3 ∧
    nucSpecies n2 = 3) :=
  not_both_species3_all n1 n2 (ne_of_lt hlt)
theorem denomGenEE_fermatCoin_eq (s : Fin 4) : denomGenEE wEESpeciesFermatCoin alphaFermatCoin s =
    denomEEFermatCoin := by
  have hg : gridSpacing_frozen ≠ 0 :=
      ne_of_gt gridSpacing_pos; unfold denomGenEE alphaFermatCoin denomEEFermatCoin
  fin_cases s <;> simp only [wEESpeciesFermatCoin, speciesZ] <;> field_simp [hg] <;> norm_num
theorem denomGenNN_fermatCoin_eq (s1 s2 : Fin 4) :
    denomGenNN wNNSpeciesFermatCoin alphaFermatCoin s1 s2 = denomNNFermatCoin s1 s2 := by
  have hg : gridSpacing_frozen ≠ 0 :=
      ne_of_gt gridSpacing_pos; unfold denomGenNN alphaFermatCoin denomNNFermatCoin
      denomNNFermatCoinVal
  fin_cases s1 <;> fin_cases s2 <;> simp only [wNNSpeciesFermatCoin, speciesZ] <;>
      field_simp [hg] <;> norm_num
theorem denomGenNN_fermatCoin_of_lt {n1 n2 : Fin 47}
    (hlt : n1 < n2) : denomGenNN wNNSpeciesFermatCoin alphaFermatCoin (nucSpecies n1)
    (nucSpecies n2) = denomNNFermatCoinVal := by
  rw [denomGenNN_fermatCoin_eq, denomNNFermatCoin, ite_eq_right fun h ↦
    nucSpecies_pair_not_both_three hlt ⟨Fin.ext h.1, Fin.ext h.2⟩]
end QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PhotochemistrySolution.ScreenFermatCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec (mkFin3 mkFin47
    mkFin187 mkFin234)
/-- Aligned `16`-AND nuclear decoder (`row_valid = [63, 62, 62]`) on `z = 64 * h1 + x1`.
-/
def decodeUltraNuc192 (z : ℕ) : Bool × Fin 47 :=
  let h := z / 64; let x := z % 64
  cond (Nat.blt x 46) (true, mkFin47 (x / 2))
    (cond (Nat.blt x 48)
      (cond ((h == 0) && (x == 46)) (true, mkFin47 23) (false, mkFin47 0))
      (let k := (x - 48) / 2
       let odd := x % 2
       cond (h == 0)
         (true, mkFin47 (cond (odd == 0) (24 + k) (32 + k)))
         (cond (h == 1)
           (true, mkFin47 (cond (Nat.blt k 7) (44 + odd) (40 + odd)))
           (cond (odd == 1) (true, mkFin47 46)
             (cond (Nat.blt k 7) (true, mkFin47 43) (true, mkFin47 42))))))
/-- Aligned `17`-AND nuclear decoder (`valid ↔ z < 187`, `row_valid = [64, 64, 59]`).
-/
def decodePinnedNuc192 (z : ℕ) : Bool × Fin 47 :=
  cond (Nat.ble 187 z) (false, mkFin47 0)
    (let h := z / 64
     let x := z % 64
     cond (Nat.blt x 46) (true, mkFin47 (x / 2))
       (cond (Nat.blt x 48) (true, mkFin47 43)
         (cond (h == 0)
           (let k := (x - 48) / 2
            (true, mkFin47 (cond (x % 2 == 0) (24 + k) (32 + k))))
           (cond (h == 1)
             (cond (Nat.blt x 55) (true, mkFin47 44)
               (cond (x == 55) (true, mkFin47 23)
                 (cond (Nat.blt x 63) (true, mkFin47 45) (true, mkFin47 43))))
             (cond ((x == 49) || (x == 51) || (x == 53))
               (true, mkFin47 (40 + (x - 49) / 2))
               (true, mkFin47 46))))))
/-- Per-`(sp, h2)` `.en` threshold (`2082993` on C; `2314437 / 2314436` on HNO). -/
def tENFermat (sp : Fin 4) (h2 : ℕ) : ℕ :=
  cond (sp.val == 1) 2082993 (cond (h2 == 2) 2314436 2314437)
/-- `4`-atom residual hydrogen lookup `{40, 41, 42, 23}` for `kinNucBlkFermat`. -/
def h4NucIdx (r2 : ℕ) : ℕ :=
  cond (r2 == 0) 40 (cond (r2 == 1) 41 (cond (r2 == 2) 42 23))
/-- `1024`-slice (`hi10 = w25 / 32768`) prefix table for `x16 = 65535` `.kinNuc`. -/
def kinNucBlkFermat (hi10 : ℕ) : ZeroNEremSector × ℕ :=
  cond (Nat.ble 768 hi10) (.idle, 0)
    (let ax := mkFin3 (hi10 / 256)
     let s8 := hi10 % 256; let hi4 := s8 / 16; let k4 := s8 % 16;
     let naH16 := cond (Nat.blt k4 8) (32 + k4) (24 + (k4 - 8))
     cond (Nat.blt hi4 10) (.kin (mkFin234 naH16) ax, 32768)
       (cond (hi4 == 10) (.kin (mkFin234 naH16) ax, 19440)
         (let q6 := s8 / 4
          let naH4 := h4NucIdx (s8 % 4)
          cond (Nat.blt q6 54) (.kin (mkFin234 naH4) ax, 32768)
            (cond (q6 == 54) (.kin (mkFin234 naH4) ax, 19440)
              (cond (q6 == 55) (.idle, 0)
                (let idx5 := s8 % 32
                 cond (Nat.blt idx5 23) (.kin (mkFin234 idx5) ax, 29145)
                   (cond (Nat.ble 27 idx5 && Nat.ble idx5 29)
                     (.kin (mkFin234 (16 + idx5)) ax, 24976)
                     (cond (idx5 == 30) (.kin (mkFin234 46) ax, 21866)
                       (.idle, 0)))))))))
/-- Pure `Bool` equality on `ZeroNEremSector` (`0` `Decidable` synthesis). -/
def eqSec : ZeroNEremSector → ZeroNEremSector → Bool
  | .idle, .idle => true
  | .ee a1 b1 c1, .ee a2 b2 c2 => (a1 == a2) && (b1 == b2) && (c1 == c2)
  | .nn a1 b1 c1, .nn a2 b2 c2 => (a1 == a2) && (b1 == b2) && (c1 == c2)
  | .en a1 b1, .en a2 b2 => (a1 == a2) && (b1 == b2)
  | .kin i1 w1, .kin i2 w2 => (i1 == i2) && (w1 == w2)
  | _, _ => false
theorem eqSec_iff (a b : ZeroNEremSector) : eqSec a b = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [eqSec, Bool.and_eq_true, beq_iff_eq, and_assoc]
/-- Unshifted `x16 = 65535` `.kinNuc` sub-box on `w25 < 2 ^ 25`. -/
def decodeFermatKinNuc25 (w25 : ℕ) : ZeroNEremSector :=
  let p := kinNucBlkFermat (w25 / 32768)
  cond (Nat.blt (w25 % 32768) p.2) p.1 .idle
/-- `.ee` cell entry `(u1, z1, z2) ↦ (tag, thr)` on `192 × 192`. -/
def eeCellFermat (u1 z1 z2 : ℕ) : ZeroNEremSector × ℕ :=
  let d1 := decodeUltraNuc192 z1
  cond (d1.1 && Nat.blt z2 187 && ((z2 == u1) == false))
    (.ee d1.2 (mkFin187 (min u1 z2)) (mkFin187 (max u1 z2)), qEEFermatCoin)
    (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64)), 0)
/-- `.nn` cell entry `(u1, z1, z2) ↦ (tag, thr)` on `192 × 192`. -/
def nnCellFermat (u1 z1 z2 : ℕ) : ZeroNEremSector × ℕ :=
  let d1 := decodeUltraNuc192 z1; let d2 := decodePinnedNuc192 z2
  cond (d1.1 && d2.1 && ((d1.2 == d2.2) == false))
    (let cLt := Nat.blt d2.2.val d1.2.val
     (.nn (cond cLt d2.2 d1.2) (cond cLt d1.2 d2.2) (mkFin187 u1),
      cond cLt 83543 83542))
    (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64)), 0)
/-- `.en` cell entry `(u1, h2, z1) ↦ (tag, thr)` on `3 × 192`. -/
def enCellFermat (u1 h2 z1 : ℕ) : ZeroNEremSector × ℕ :=
  let d1 := decodeUltraNuc192 z1
  cond d1.1
    (.en d1.2 (mkFin187 u1), tENFermat (nucSpecies d1.2) h2)
    (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64)), 0)
/-- Main-box cell decoder on `u1 ∈ 0..186, h1, h2 ∈ 0..2, uBig ∈ 0..1306587999`.
-/
def decodeFermatCell (u1 h1 h2 uBig : ℕ) : ZeroNEremSector :=
  let z1 := h1 * 64 + uBig % 64; let z2 := h2 * 64 + (uBig / 64) % 64;
  let fbKin := ZeroNEremSector.kin (mkFin234 (47 + u1)) (mkFin3 h1)
  cond (Nat.blt uBig 704643072)
    (let p := eeCellFermat u1 z1 z2
     cond (Nat.blt (uBig / 4096) p.2) p.1 fbKin)
    (cond (Nat.blt uBig 1073741824)
      (let p := nnCellFermat u1 z1 z2
       cond (Nat.blt ((uBig - 704643072) / 4096) p.2) p.1 fbKin)
      (cond (Nat.blt uBig 1275068416)
        (let p := enCellFermat u1 h2 z1
         cond (Nat.blt ((uBig - 1073741824) / 64) p.2) p.1 fbKin)
        (let uSp := uBig - 1275068416
         cond ((h1 == 1) && (h2 == 0) && Nat.blt uSp 19848333)
           (.kin (mkFin234 (47 + u1)) 0)
           (cond ((h1 == 2) && (h2 == 0) && Nat.blt uSp 20880606)
             (.kin (mkFin234 (47 + u1)) 0)
             (cond ((h1 == 2) && (h2 == 2) && Nat.blt uSp 137290) .idle fbKin)))))
/-- Canonical `2 ^ 41` `51 x 33` Fermat coin decoder. -/
def decodeFermatCanon (c : Fin (2 ^ 41)) : ZeroNEremSector :=
  let x16 := c.val / 33554432; let w25 := c.val % 33554432
  cond (Nat.blt x16 65535)
    (let y20 := w25 / 32
     let c5 := w25 % 32
     cond (Nat.blt y20 1048575)
       (let s51 := x16 % 51
        let q1285 := x16 / 51; let s33 := y20 % 33; let q31775 := y20 / 33;
        let u1 := (s51 / 3) * 11 + (s33 / 3); let h1 := s51 % 3; let h2 := s33 % 3;
        let uBig := (q1285 * 31775 + q31775) * 32 + c5
        decodeFermatCell u1 h1 h2 uBig)
       .idle)
    (decodeFermatKinNuc25 w25)
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PhotochemistrySolution.Stage1ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
theorem card_fin_add_filter {M N : ℕ} (P : ℕ → Prop)
    [DecidablePred P] : ((Finset.univ : Finset (Fin (M + N))).filter (fun x ↦ P x.val)).card =
    ((Finset.univ : Finset (Fin M)).filter (fun x ↦ P x.val)).card +
    ((Finset.univ : Finset (Fin N)).filter (fun x ↦ P (M + x.val))).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact sum_fin_add (fun n ↦ if P n then 1 else 0)
theorem card_prefix_cond {N : ℕ} (tag fb s : ZeroNEremSector) (thr : ℕ) (hThr : thr ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x ↦ cond (Nat.blt x.val thr) tag fb = s)).card =
      cond (eqSec tag s) thr 0 + cond (eqSec fb s) (N - thr) 0 := by
  rw [show ((Finset.univ : Finset (Fin N)).filter fun x ↦ cond (Nat.blt x.val thr) tag fb = s) =
        Finset.univ.filter fun x : Fin N ↦ (if x.val < thr then tag else fb) = s from
      Finset.ext fun x ↦ by cases h : Nat.blt x.val thr <;> simp [← Nat.blt_eq, h],
    card_prefix_hit_or_miss tag fb s thr hThr]
  simp only [← eqSec_iff]
  cases eqSec tag s <;> cases eqSec fb s <;> simp
theorem sum_fin_div_mod {A B : ℕ} (hB : 0 < B) (g : ℕ → ℕ → ℕ) :
    (∑ n : Fin (A * B), g (n.val / B) (n.val % B)) = ∑ a : Fin A, ∑ b : Fin B, g a.val b.val := by
  refine (sum_fin_mul hB fun m ↦ g (m / B) (m % B)).trans
    (Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_)
  rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt b.isLt, Nat.add_zero, Nat.mul_comm,
    Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt b.isLt]
theorem sum_fermat_box_reassoc (K : ℕ → ℕ → ℕ → ℕ → ℕ) :
    (∑ x : Fin 65535, ∑ y : Fin 1048575, K ((x.val % 51 / 3) * 11 + (y.val % 33 / 3))
        (x.val % 51 % 3) (y.val % 33 % 3) ((x.val /
        51) * 31775 + y.val / 33)) =
      ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ q : Fin 40830875,
          K u1.val h1.val h2.val q.val := by
  have hy (x : Fin 65535) : (∑ y : Fin 1048575, K ((x.val % 51 / 3) * 11 + (y.val % 33 / 3))
      (x.val % 51 % 3) (y.val % 33 % 3)
      ((x.val / 51) * 31775 + y.val / 33)) =
      ∑ s33 : Fin 33, ∑ qy : Fin 31775, K ((x.val % 51 / 3) * 11 + s33.val / 3) (x.val % 51 % 3)
          (s33.val % 3) ((x.val / 51) * 31775
          + qy.val) := by
    rw [show (1048575 : ℕ) = 31775 * 33 from rfl, sum_fin_div_mod (A := 31775) (B := 33)
        (Nat.succ_pos _) (fun qy s33 ↦ K ((x.val %
        51 / 3) * 11 + s33 / 3) (x.val % 51 % 3) (s33 % 3) ((x.val / 51) * 31775 + qy)),
            Finset.sum_comm]
  rw [Finset.sum_congr rfl fun x _ ↦ hy x, show (65535 : ℕ) = 1285 * 51 from rfl,
    sum_fin_div_mod (A := 1285) (B := 51) (Nat.succ_pos _)
        (fun qx s51 ↦ ∑ s33 : Fin 33, ∑ qy : Fin 31775, K ((s51 / 3) * 11 +
        s33.val / 3) (s51 % 3) (s33.val % 3) (qx * 31775 + qy.val)), Finset.sum_comm]
  have hs51 (s51 : Fin 51) : (∑ qx : Fin 1285, ∑ s33 : Fin 33, ∑ qy : Fin 31775, K ((s51.val / 3) *
      11 + s33.val / 3) (s51.val % 3)
      (s33.val % 3) (qx.val * 31775 + qy.val)) =
      ∑ s33 : Fin 33, ∑ q : Fin 40830875, K ((s51.val / 3) * 11 + s33.val / 3) (s51.val % 3)
          (s33.val % 3) q.val := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s33 _ ↦
        (sum_fin_mul (A := 1285) (B := 31775) (Nat.succ_pos _) (fun q ↦ K ((s51.val / 3) * 11 +
        s33.val / 3) (s51.val % 3) (s33.val % 3) q)).symm
  rw [Finset.sum_congr rfl fun s51 _ ↦ hs51 s51]
  let Q : ℕ → ℕ → ℕ → ℕ := fun u1 h1 h2 ↦ ∑ q : Fin 40830875, K u1 h1 h2 q.val
  change (∑ s51 : Fin 51, ∑ s33 : Fin 33, Q ((s51.val / 3) * 11 + s33.val / 3) (s51.val % 3)
      (s33.val % 3)) = ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, Q u1.val h1.val h2.val
  have inner33 (r17 h1 : ℕ) : (∑ s33 : Fin 33, Q (r17 * 11 + s33.val / 3) h1 (s33.val % 3)) =
      ∑ r11 : Fin 11, ∑ h2 : Fin 3, Q (r17 *
      11 + r11.val) h1 h2.val :=
    sum_fin_div_mod (A := 11) (B := 3) (Nat.succ_pos _) (fun r11 h2 ↦ Q (r17 * 11 + r11) h1 h2)
  rw [show (51 : ℕ) = 17 * 3 from rfl, sum_fin_div_mod (A := 17) (B := 3) (Nat.succ_pos _)
      (fun r17 h1 ↦ ∑ s33 : Fin 33, Q (r17 * 11
      + s33.val / 3) h1 (s33.val % 3))]
  have outer17 (r17 : Fin 17) : (∑ h1 : Fin 3, ∑ s33 : Fin 33, Q (r17.val * 11 + s33.val /
      3) h1.val (s33.val %
      3)) = ∑ r11 : Fin 11, ∑ h1 : Fin 3, ∑ h2 : Fin 3, Q (r17.val * 11 +
          r11.val) h1.val h2.val := by
    rw [Finset.sum_congr rfl fun (h1 : Fin 3) _ ↦ inner33 r17.val h1.val, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun r17 _ ↦ outer17 r17, ← sum_fin_mul (A := 17) (B := 11)
      (Nat.succ_pos _) (fun u1 ↦ ∑ h1 : Fin 3, ∑ h2 : Fin 3, Q u1 h1.val h2.val)]

attribute [local irreducible] decodeFermatCell decodeFermatKinNuc25
theorem decodeFermatCanon_s02_top {c : Fin (2 ^ 41)} {w : ℕ} (hm : c.val = 65535 * 33554432 + w)
    (hd : (65535 * 33554432 + w) / 33554432 = 65535) (hr : (65535 * 33554432 + w) % 33554432 = w) :
    decodeFermatCanon c = decodeFermatKinNuc25 w := by
  change cond (Nat.blt (c.val / 33554432) 65535) _ _ = _;
  rw [hm, hd, show Nat.blt 65535 65535 = false by decide, Bool.cond_false, hr]
theorem decodeFermatCanon_s02_idle {c : Fin (2 ^ 41)} {x w : ℕ} (hx : x < 65535)
    (hd1 : c.val / 33554432 = x) (hr1 : c.val % 33554432 = w) (hd2 : w / 32 = 1048575) :
    decodeFermatCanon c = .idle := by
  change cond (Nat.blt (c.val / 33554432) 65535) _ _ = _;
  rw [hd1, Nat.blt_eq.mpr hx, Bool.cond_true];
  change cond (Nat.blt (c.val % 33554432 / 32) 1048575) _ _ = _;
  rw [hr1, hd2, show Nat.blt 1048575 1048575 = false by decide, Bool.cond_false]
theorem decodeFermatCanon_s02_grid_raw {c : Fin (2 ^ 41)} (hbx : Nat.blt (c.val / 33554432) 65535 =
    true) (hby : Nat.blt (c.val % 33554432 / 32) 1048575 = true) : decodeFermatCanon c =
    decodeFermatCell (((c.val / 33554432) % 51 / 3) * 11 + ((c.val % 33554432 / 32) % 33 / 3))
    ((c.val / 33554432) % 51 % 3) ((c.val % 33554432 / 32) % 33 % 3)
    (((c.val / 33554432 / 51) * 31775 + (c.val % 33554432 / 32 / 33)) * 32 + c.val % 33554432 % 32)
    := by
  change cond (Nat.blt (c.val / 33554432) 65535) _ _ = _; rw [hbx, Bool.cond_true];
  change cond (Nat.blt (c.val % 33554432 / 32) 1048575) _ _ = _; rw [hby, Bool.cond_true]
theorem decodeFermatCanon_s02_grid {c : Fin (2 ^ 41)} {x y c5 : ℕ} (hx : x < 65535)
    (hy : y < 1048575) (hd1 : c.val / 33554432 = x) (hr1 : c.val % 33554432 = y * 32 + c5)
    (hd2 : (y * 32 + c5) / 32 = y) (hr2 : (y * 32 + c5) % 32 = c5) : decodeFermatCanon c =
    decodeFermatCell ((x % 51 / 3) * 11 + (y % 33 / 3)) (x % 51 % 3) (y % 33 % 3)
    (((x / 51) * 31775 + y / 33) * 32 + c5) := by
  rw [decodeFermatCanon_s02_grid_raw (by rw [hd1]; exact Nat.blt_eq.mpr hx)
        (by rw [hr1, hd2]; exact Nat.blt_eq.mpr hy),
      hd1, hr1, hd2, hr2]
theorem card_decodeFermatCanon_split (s : ZeroNEremSector) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeFermatCanon c = s)).card =
    (∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3,
    ((Finset.univ : Finset (Fin 1306588000)).filter (fun u ↦
    decodeFermatCell u1.val h1.val h2.val u.val = s)).card) + cond (eqSec .idle s) 2097120 0 +
    ((Finset.univ : Finset (Fin 33554432)).filter (fun w ↦ decodeFermatKinNuc25 w.val =
    s)).card := by
  have hpos41 : 0 < 2 ^ 41 := Nat.two_pow_pos 41
  have hmod (n : ℕ) (hn : n < 65536 * 33554432) : n % 2 ^ 41 = n :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_eq hn (by rfl))
  let F (xv : ℕ) := ((Finset.univ : Finset (Fin 33554432)).filter fun w ↦
    decodeFermatCanon ⟨(xv * 33554432 + w.val) % 2 ^ 41, Nat.mod_lt _ hpos41⟩ = s).card
  have hlhs : ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeFermatCanon c = s)).card = ∑ x : Fin 65536, F x.val := by
    rw [show ((Finset.univ : Finset (Fin (2 ^ 41))).filter fun c ↦ decodeFermatCanon c = s) =
        Finset.univ.filter fun c : Fin (2 ^ 41) ↦
          decodeFermatCanon ⟨c.val % 2 ^ 41, Nat.mod_lt _ hpos41⟩ = s from
      Finset.ext fun c ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show (⟨c.val % 2 ^ 41, _⟩ : Fin (2 ^ 41)) = c from Fin.ext (Nat.mod_eq_of_lt c.isLt)]]
    exact @card_fin_mul_split 65536 33554432 (Nat.succ_pos _)
      (fun n ↦ decodeFermatCanon ⟨n % 2 ^ 41, Nat.mod_lt _ hpos41⟩ = s) fun _ ↦ inferInstance
  rw [hlhs, show (65536 : ℕ) = 65535 + 1 from rfl, sum_fin_add (M := 65535) (N := 1) F,
    Fin.sum_univ_one, show F (65535 + (0 : Fin 1).val) =
      (Finset.univ.filter fun w : Fin 33554432 ↦ decodeFermatKinNuc25 w.val = s).card from
    congrArg Finset.card (Finset.ext fun w ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero, Nat.add_zero]
      rw [decodeFermatCanon_s02_top (hmod _ (by omega)) (by omega) (by omega)])]
  refine congrArg₂ HAdd.hAdd ?_ rfl
  let K (u1 h1 h2 q : ℕ) := ((Finset.univ : Finset (Fin 32)).filter fun c5 ↦
    decodeFermatCell u1 h1 h2 (q * 32 + c5.val) = s).card
  have hx (x : Fin 65535) : F x.val = (∑ y : Fin 1048575,
      K ((x.val % 51 / 3) * 11 + (y.val % 33 / 3)) (x.val % 51 % 3) (y.val % 33 % 3)
        ((x.val / 51) * 31775 + y.val / 33)) + cond (eqSec .idle s) 32 0 := by
    change ((Finset.univ : Finset (Fin (1048576 * 32))).filter (fun w ↦
      decodeFermatCanon ⟨(x.val * 33554432 + w.val) % 2 ^ 41, Nat.mod_lt _ hpos41⟩ = s)).card = _
    rw [@card_fin_mul_split 1048576 32 (Nat.succ_pos _) (fun n ↦ decodeFermatCanon
          ⟨(x.val * 33554432 + n) % 2 ^ 41, Nat.mod_lt _ hpos41⟩ = s) fun _ ↦ inferInstance,
      show (1048576 : ℕ) = 1048575 + 1 from rfl,
      sum_fin_add (M := 1048575) (N := 1) fun av ↦ ((Finset.univ : Finset (Fin 32)).filter
        fun b ↦ decodeFermatCanon ⟨(x.val * 33554432 + (av * 32 + b.val)) % 2 ^ 41,
          Nat.mod_lt _ hpos41⟩ = s).card,
      Fin.sum_univ_one]
    refine congrArg₂ HAdd.hAdd (Finset.sum_congr rfl fun y _ ↦
      congrArg Finset.card (Finset.ext fun c5 ↦ ?_)) ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hm := hmod (x.val * 33554432 + (y.val * 32 + c5.val)) (by omega)
      rw [decodeFermatCanon_s02_grid (c5 := c5.val) x.isLt y.isLt
        ((congrArg (· / 33554432) hm).trans (by omega))
        ((congrArg (· % 33554432) hm).trans (by omega)) (by omega) (by omega)]
    · simp only [Fin.val_zero, Nat.add_zero]
      rw [show ((Finset.univ : Finset (Fin 32)).filter fun c5 ↦ decodeFermatCanon
              ⟨(x.val * 33554432 + (1048575 * 32 + c5.val)) % 2 ^ 41, _⟩ = s) =
            Finset.univ.filter fun c5 : Fin 32 ↦ cond (Nat.blt c5.val 32) .idle .idle = s from
          Finset.ext fun c5 ↦ by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hm := hmod (x.val * 33554432 + (1048575 * 32 + c5.val)) (by omega)
            rw [decodeFermatCanon_s02_idle (w := 1048575 * 32 + c5.val) x.isLt
              ((congrArg (· / 33554432) hm).trans (by omega))
              ((congrArg (· % 33554432) hm).trans (by omega)) (by omega),
              Nat.blt_eq.mpr c5.isLt, Bool.cond_true],
        card_prefix_cond .idle .idle s 32 le_rfl]
      cases eqSec .idle s <;> rfl
  rw [Finset.sum_congr rfl fun x _ ↦ hx x, Finset.sum_add_distrib, sum_fermat_box_reassoc]
  refine congrArg₂ HAdd.hAdd (Finset.sum_congr rfl fun u1 _ ↦ Finset.sum_congr rfl fun h1 _ ↦
    Finset.sum_congr rfl fun h2 _ ↦ (@card_fin_mul_split 40830875 32 (Nat.succ_pos _)
      (fun n ↦ decodeFermatCell u1.val h1.val h2.val n = s) fun _ ↦ inferInstance).symm) ?_
  simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]
  cases eqSec .idle s <;> rfl
theorem cond_le {b : Bool} {x y M : ℕ} (hx : x ≤ M) (hy : y ≤ M) : cond b x y ≤ M := by
  cases b <;> assumption
theorem cond_snd_le {α : Type*} {b : Bool} {p q : α × ℕ} {M : ℕ} (hp : p.2 ≤ M)
    (hq : q.2 ≤ M) : (cond b p q).2 ≤ M := by
  cases b <;> assumption
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PhotochemistrySolution.Stage1ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
theorem card_fin_div_lt_of_mod {M B : ℕ} (hB : 0 < B) (tag : ℕ → ZeroNEremSector)
    (fb s : ZeroNEremSector) (thr : ℕ → ℕ) (hLe : ∀ r < B, thr r ≤ M) :
    ((Finset.univ : Finset (Fin (M * B))).filter (fun u ↦ cond (Nat.blt (u.val / B)
    (thr (u.val % B))) (tag (u.val % B)) fb = s)).card = ∑ r : Fin B, (cond (eqSec (tag r.val) s)
    (thr r.val) 0 + cond (eqSec fb s) (M - thr r.val) 0) := by
  rw [card_fin_mul_split (A := M) (B := B) hB
        (fun n ↦ cond (Nat.blt (n / B) (thr (n % B))) (tag (n % B)) fb = s),
      Finset.sum_congr rfl fun q _ ↦ (Finset.card_eq_sum_ones _).trans
        ((Finset.sum_filter _ _).trans (Finset.sum_congr rfl fun r _ ↦ by
          rw [show (q.val * B + r.val) / B = q.val by
                rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt r.isLt, Nat.add_zero],
              Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt])),
      Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ ↦ by
    rw [← card_prefix_cond (tag r.val) fb s (thr r.val) (hLe r.val r.isLt),
      Finset.card_eq_sum_ones, Finset.sum_filter]
theorem sum_h1_h2_fin4096 (G : ℕ → ℕ → ℕ) :
    (∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ r : Fin 4096,
      G (h1.val * 64 + r.val % 64) (h2.val * 64 + r.val / 64)) =
    foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦ G z1 z2 := by
  have hm1 (h1 : Fin 3) :
      (∑ h2 : Fin 3, ∑ r : Fin 4096, G (h1.val * 64 + r.val % 64) (h2.val * 64 + r.val / 64)) =
      ∑ x1 : Fin 64, foldSum 192 fun z2 ↦ G (h1.val * 64 + x1.val) z2 := by
    rw [Finset.sum_congr rfl fun (h2 : Fin 3) _ ↦ (sum_fin_div_mod (A := 64) (B := 64)
          (Nat.succ_pos 63) fun x2 x1 ↦ G (h1.val * 64 + x1) (h2.val * 64 + x2) :
          (∑ r : Fin 4096, _) = _),
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun x1 _ ↦ by
      rw [← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos 63), sum_fin_eq_foldSum]
  rw [Finset.sum_congr rfl fun h1 _ ↦ hm1 h1,
    ← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos 63) fun z1 ↦ foldSum 192 fun z2 ↦ G z1 z2]
  exact sum_fin_eq_foldSum (3 * 64) fun z1 ↦ foldSum 192 fun z2 ↦ G z1 z2
theorem sum_h1_fin64 (G : ℕ → ℕ) : (∑ h1 : Fin 3, ∑ r : Fin 64, G (h1.val * 64 + r.val)) =
    foldSum 192 G := by
  rw [← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _) G]; exact sum_fin_eq_foldSum (3 * 64) G
/--
Top-slab (`1275068416 ≤ uBig < 1306588000`) contribution summed over `h1, h2 ∈
Fin 3`.
-/
def fermatTopSpill (u1 : ℕ) (s : ZeroNEremSector) : ℕ :=
  cond (eqSec (.kin (mkFin234 (47 + u1)) 0) s) 135287691 0 +
  cond (eqSec (.kin (mkFin234 (47 + u1)) 1) s) 74710419 0 +
  cond (eqSec (.kin (mkFin234 (47 + u1)) 2) s) 73540856 0 +
  cond (eqSec .idle s) 137290 0
/--
Total main-box count at fixed `u1 ∈ 0..186` summed across all `9` `(h1, h2)`
cells.
-/
def fermatPerU1 (u1 : ℕ) (s : ZeroNEremSector) : ℕ :=
    (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦ cond (eqSec (eeCellFermat u1 z1 z2).1 s)
    (eeCellFermat u1 z1 z2).2 0 + cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s)
    (172032 - (eeCellFermat u1 z1 z2).2) 0) + (foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦
    cond (eqSec (nnCellFermat u1 z1 z2).1 s) (nnCellFermat u1 z1 z2).2 0 +
    cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s)
    (90112 - (nnCellFermat u1 z1 z2).2) 0) + (foldSum 3 fun h2 ↦ foldSum 192 fun z1 ↦
    cond (eqSec (enCellFermat u1 h2 z1).1 s) (enCellFermat u1 h2 z1).2 0 +
    cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s)
    (3145728 - (enCellFermat u1 h2 z1).2) 0) + fermatTopSpill u1 s
theorem kinNucBlkFermat_snd_le (b : ℕ) : (kinNucBlkFermat b).2 ≤ 32768 := by
  unfold kinNucBlkFermat
  repeat first | refine cond_snd_le ?_ ?_ | omega

open PhotochemistrySolution.GenWeightsSelect
theorem foldSum_add_split (m n : ℕ) (f : ℕ → ℕ) : foldSum (m + n) f = foldSum m f +
    foldSum n (fun r ↦ f (m + r)) := by
  induction n with
  | zero => simp [foldSum]
  | succ k ih => rw [Nat.add_succ, foldSum_succ, ih, foldSum_succ, Nat.add_assoc]
theorem foldSum_mul3 (B : ℕ) (f : ℕ → ℕ) : foldSum (3 * B) f = foldSum B (fun r ↦ f r) +
    foldSum B (fun r ↦ f (B + r)) + foldSum B (fun r ↦ f (2 * B + r)) := by
  rw [show 3 * B = (B + B) + B by omega, foldSum_add_split, foldSum_add_split,
    show B + B = 2 * B by omega]
theorem fin47_beq_val (a b : Fin 47) : (a == b) = (a.val == b.val) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.ext_iff]
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PhotochemistrySolution.Stage1ZeroNEremSpec PhotochemistrySolution.GenWeightsSelect
  PhotochemistrySolution.ScreenFermatCore
attribute [local irreducible] foldSum
def phiU1 (r11 r17 : ℕ) : ℕ :=
  cond (Nat.blt r17 16) (r11 * 16 + r17) (176 + r11)
/-- Inverse of `phiU1` on `u1 < 187`. -/
def phiU1Inv (u1 : ℕ) : ℕ × ℕ := cond (Nat.blt u1 176) (u1 / 16, u1 % 16) (u1 - 176, 16)
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse

namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PhotochemistrySolution.Stage1ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
theorem check_phiU1_bij_fwd :
    ((List.range 11).all fun r11 ↦
      (List.range 17).all fun r17 ↦
        let u := phiU1 r11 r17
        Nat.blt u 187 && (phiU1Inv u == (r11, r17))) = true := by rfl
theorem phiU1_spec {r11 r17 : ℕ} (h11 : r11 < 11) (h17 : r17 < 17) : phiU1 r11 r17 < 187 ∧
    phiU1Inv (phiU1 r11 r17) = (r11, r17) := by
  have ha := List.all_eq_true.mp check_phiU1_bij_fwd r11 (List.mem_range.mpr h11);
  have hb := List.all_eq_true.mp ha r17 (List.mem_range.mpr h17)
  rcases Bool.and_eq_true_iff.mp hb with ⟨hlt, hinv⟩
  exact ⟨Nat.blt_eq.mp hlt, beq_iff_eq.mp hinv⟩
theorem phiU1Inv_spec {u : ℕ} (hu : u < 187) :
    (phiU1Inv u).1 < 11 ∧ (phiU1Inv u).2 < 17 ∧ phiU1 (phiU1Inv u).1 (phiU1Inv u).2 = u := by
  by_cases h : u < 176 <;>
    simp [phiU1Inv, phiU1, Bool.cond_eq_ite, Nat.blt_eq, h, show u % 16 < 16 by omega] <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end
end
end

end
