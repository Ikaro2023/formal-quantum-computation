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
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WindowedCsaStageA
set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution


section NucMatADipSexticCap
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option Elab.async false
set_option maxRecDepth 512
set_option exponentiation.threshold 256

namespace NucMatADipSexticCap

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowNucMatADip (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner (fermionicProjector_idem)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open SpecsAux.DyadicSubgridToeplitz128
  (InMomGrid1D InMomGrid3D shiftedMom3D shiftedFin64ToInt uEnManyBody)
open Dyadic128OrbitTableCert
  (cellSide cellSide_pos normSqInt coulombKernel_eq_of_ne_zero)
open SingleAnchorFermionicPauliCap
  (rEl_sp rk1_sp op_sp nSub_sp nSub_isHermitian_any nSub_mul_self_mul_fermionicProjector)
open NuclearTwistAndXor654Concrete (oneElecNucDiagExact)
open TwosCompAndWire0Cancel (smToTwosSysUnitary)
open PosSlots24SemanticOracleConcrete80 (pos80Slot2Scale)
open Pos24MergedVepPrepAndStitch (mergedPosSlot2WeightGen)
open Pos24Slot2FermionicBridge (pos24Slot2E2Const bModSlot248)
open PosSlots24Q30Tight (eps4_q30_tight)
open SubvoxelNuclearTrunc34And33Physics
open SubvoxelNuclearTrunc28To35Chiral
open PosS3Bounds (tierBB2IdMod4)
open PosMod4FermionicBounds (tierBB2IdMod4_trunc_intrinsic_agrees_tight)
open Leaf2Packed18Mux2DCore (truncChiralOfW)
open GqspCleanCoinAndGuardBridge (truncChiralChiralOfW)
open Pos512FastPrepAndCoin (truncChiralPos512OfW)

/-! ## Section 1: Polymorphic Skew-Rank-2 Fermionic Pauli Exclusion (`{d D : ℕ}`) -/

/-- Skew-symmetric rank-2 Hermitian matrix `i * (|ψ⟩⟨φ| - |φ⟩⟨ψ|)` for real vectors `φ, ψ`. -/
noncomputable def skewRank2Mat {d : ℕ} (φ ψ : Fin d → ℝ) : Operator d :=
  Matrix.of fun u v ↦ ((ψ u * φ v - φ u * ψ v : ℝ) : ℂ) * Complex.I

theorem skewRank2Mat_imag {d : ℕ} (φ ψ : Fin d → ℝ) (u v : Fin d) :
    star (skewRank2Mat φ ψ u v) = -skewRank2Mat φ ψ u v := by
  unfold skewRank2Mat
  simp only [Matrix.of_apply, star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem skewRank2Mat_isHermitian {d : ℕ} (φ ψ : Fin d → ℝ) :
    (skewRank2Mat φ ψ).IsHermitian := by
  ext u v
  rw [Matrix.conjTranspose_apply, skewRank2Mat_imag]
  unfold skewRank2Mat
  simp only [Matrix.of_apply]
  push_cast; ring

private theorem skewRank2Mat_zero_left {d : ℕ} {φ ψ : Fin d → ℝ} (h : ∀ u, φ u = 0) :
    skewRank2Mat φ ψ = 0 := by
  ext u v; simp [skewRank2Mat, h]

private theorem skewRank2Mat_zero_right {d : ℕ} {φ ψ : Fin d → ℝ} (h : ∀ u, ψ u = 0) :
    skewRank2Mat φ ψ = 0 := by
  ext u v; simp [skewRank2Mat, h]

private theorem skewRank2Mat_scale {d : ℕ} {φ ψ e₁ e₂ : Fin d → ℝ} {a b : ℝ}
    (hφ : ∀ u, φ u = a * e₁ u) (hψ : ∀ u, ψ u = b * e₂ u) :
    skewRank2Mat φ ψ = ((a * b : ℝ) : ℂ) • skewRank2Mat e₁ e₂ := by
  ext u v
  simp only [skewRank2Mat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hφ, hψ]
  push_cast; ring

private noncomputable def chiPlusGen {d : ℕ} (e₁ e₂ : Fin d → ℝ) (u : Fin d) : ℂ :=
  ((e₁ u / √2 : ℝ) : ℂ) + ((e₂ u / √2 : ℝ) : ℂ) * Complex.I

private noncomputable def chiMinusGen {d : ℕ} (e₁ e₂ : Fin d → ℝ) (u : Fin d) : ℂ :=
  ((e₁ u / √2 : ℝ) : ℂ) - ((e₂ u / √2 : ℝ) : ℂ) * Complex.I

private theorem rk1Gen_chiPlus_sub_chiMinus {d : ℕ} (e₁ e₂ : Fin d → ℝ) :
    rk1Gen (chiPlusGen e₁ e₂) - rk1Gen (chiMinusGen e₁ e₂) = skewRank2Mat e₁ e₂ := by
  ext u v
  simp only [Matrix.sub_apply, rk1Gen, skewRank2Mat, Matrix.of_apply, chiPlusGen, chiMinusGen,
    map_add, map_sub, map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  have hreal : 2 * ((e₂ u / √2) * (e₁ v / √2) - (e₁ u / √2) * (e₂ v / √2)) =
      e₂ u * e₁ v - e₁ u * e₂ v := by
    have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_mul_div_comm, div_mul_div_comm, h2]; ring
  have hcast : (((2 * ((e₂ u / √2) * (e₁ v / √2) - (e₁ u / √2) * (e₂ v / √2)) : ℝ) : ℂ)) =
      ((e₂ u * e₁ v - e₁ u * e₂ v : ℝ) : ℂ) := by rw [hreal]
  rw [← hcast]
  push_cast; ring

private theorem chiPlusGen_norm {d : ℕ} {e₁ e₂ : Fin d → ℝ}
    (he₁ : (∑ u : Fin d, (e₁ u) ^ 2) = 1) (he₂ : (∑ u : Fin d, (e₂ u) ^ 2) = 1) :
    ∑ u : Fin d, star (chiPlusGen e₁ e₂ u) * chiPlusGen e₁ e₂ u = 1 := by
  have hterm : ∀ u : Fin d,
      star (chiPlusGen e₁ e₂ u) * chiPlusGen e₁ e₂ u =
        ((((e₁ u) ^ 2 + (e₂ u) ^ 2) / 2 : ℝ) : ℂ) := fun u ↦ by
    have hab : ∀ a b : ℝ,
        star ((a : ℂ) + (b : ℂ) * Complex.I) * ((a : ℂ) + (b : ℂ) * Complex.I) =
          ((a * a + b * b : ℝ) : ℂ) := fun a b ↦ by
      simp only [map_add, map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
      push_cast; linear_combination -((b : ℂ) ^ 2) * Complex.I_mul_I
    have hr : (e₁ u / √2) * (e₁ u / √2) + (e₂ u / √2) * (e₂ u / √2) =
        ((e₁ u) ^ 2 + (e₂ u) ^ 2) / 2 := by
      have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
      rw [div_mul_div_comm, div_mul_div_comm, h2]; ring
    dsimp only [chiPlusGen]
    rw [hab, hr]
  rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← Complex.ofReal_sum, ← Finset.sum_div,
    Finset.sum_add_distrib, he₁, he₂]
  norm_num

private theorem chiMinusGen_norm {d : ℕ} {e₁ e₂ : Fin d → ℝ}
    (he₁ : (∑ u : Fin d, (e₁ u) ^ 2) = 1) (he₂ : (∑ u : Fin d, (e₂ u) ^ 2) = 1) :
    ∑ u : Fin d, star (chiMinusGen e₁ e₂ u) * chiMinusGen e₁ e₂ u = 1 := by
  have hsteq : ∀ u : Fin d,
      star (chiMinusGen e₁ e₂ u) * chiMinusGen e₁ e₂ u =
        star (chiPlusGen e₁ e₂ u) * chiPlusGen e₁ e₂ u := fun u ↦ by
    dsimp only [chiMinusGen, chiPlusGen]
    simp only [map_add, map_sub, map_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Finset.sum_congr rfl fun u _ ↦ hsteq u]
  exact chiPlusGen_norm he₁ he₂

private noncomputable def unitaryMulVecGen {d : ℕ} (V : Unitary d)
    (χ : Fin d → ℂ) (u : Fin d) : ℂ :=
  ∑ a : Fin d, V.1 u a * χ a

private theorem conj_skewRank2Mat_eq {d : ℕ} (V : Unitary d) (e₁ e₂ : Fin d → ℝ) :
    V.1 * skewRank2Mat e₁ e₂ * V.1ᴴ =
      rk1Gen (unitaryMulVecGen V (chiPlusGen e₁ e₂)) -
        rk1Gen (unitaryMulVecGen V (chiMinusGen e₁ e₂)) := by
  rw [← rk1Gen_chiPlus_sub_chiMinus e₁ e₂, Matrix.mul_sub, Matrix.sub_mul,
    conj_rk1Gen, conj_rk1Gen]
  rfl

private theorem unitaryMulVecGen_norm {d : ℕ} (V : Unitary d) {χ : Fin d → ℂ}
    (hχ : ∑ a : Fin d, star (χ a) * χ a = 1) :
    ∑ u : Fin d, star (unitaryMulVecGen V χ u) * unitaryMulVecGen V χ u = 1 := by
  have hVhV : V.1ᴴ * V.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp V.2)
  have hexp : ∀ u : Fin d,
      star (unitaryMulVecGen V χ u) * unitaryMulVecGen V χ u =
        ∑ a : Fin d, ∑ b : Fin d,
          star (χ a) * (star (V.1 u a) * V.1 u b) * χ b := fun u ↦ by
    dsimp only [unitaryMulVecGen]
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [star_mul']; ring
  rw [Finset.sum_congr rfl fun u _ ↦ hexp u, Finset.sum_comm]
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans hχ
  rw [Finset.sum_comm]
  have hb : ∀ b : Fin d,
      (∑ u : Fin d, star (χ a) * (star (V.1 u a) * V.1 u b) * χ b) =
        if a = b then star (χ a) * χ b else 0 := fun b ↦ by
    have hmid : (∑ u : Fin d, star (V.1 u a) * V.1 u b) = (V.1ᴴ * V.1) a b := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    calc (∑ u : Fin d, star (χ a) * (star (V.1 u a) * V.1 u b) * χ b)
        = star (χ a) * (∑ u : Fin d, star (V.1 u a) * V.1 u b) * χ b := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = star (χ a) * ((V.1ᴴ * V.1) a b) * χ b := by rw [hmid]
      _ = if a = b then star (χ a) * χ b else 0 := by
            rw [hVhV, Matrix.one_apply]; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun b _ ↦ hb b, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ a)]

private theorem skewRank2Mat_scale_unit {d : ℕ} [NeZero d] (φ ψ : Fin d → ℝ)
    {Fφ Fψ : ℝ} (hFφ0 : 0 ≤ Fφ) (hFψ0 : 0 ≤ Fψ)
    (hφ : (∑ u : Fin d, (φ u) ^ 2) ≤ Fφ ^ 2)
    (hψ : (∑ u : Fin d, (ψ u) ^ 2) ≤ Fψ ^ 2) :
    ∃ (c : ℝ) (e₁ e₂ : Fin d → ℝ),
      0 ≤ c ∧ c ≤ Fφ * Fψ ∧
      (∑ u : Fin d, (e₁ u) ^ 2 = 1) ∧
      (∑ u : Fin d, (e₂ u) ^ 2 = 1) ∧
      skewRank2Mat φ ψ = (c : ℂ) • skewRank2Mat e₁ e₂ := by
  let Sφ := ∑ u : Fin d, (φ u) ^ 2
  let Sψ := ∑ u : Fin d, (ψ u) ^ 2
  have hSφ0 : 0 ≤ Sφ := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hSψ0 : 0 ≤ Sψ := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  by_cases hzero : Sφ = 0 ∨ Sψ = 0
  · let e₀ : Fin d → ℝ := fun u ↦ if (0 : Fin d) = u then 1 else 0
    have he₀ : (∑ u : Fin d, (e₀ u) ^ 2) = 1 := by
      have hsq : ∀ u : Fin d, (e₀ u) ^ 2 = if (0 : Fin d) = u then 1 else 0 := fun u ↦ by
        dsimp only [e₀]; split_ifs <;> norm_num
      rw [Finset.sum_congr rfl fun u _ ↦ hsq u, Finset.sum_ite_eq,
        ite_eq_left (Finset.mem_univ (0 : Fin d))]
    have hmat0 : skewRank2Mat φ ψ = 0 := by
      rcases hzero with hφ0 | hψ0
      · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ ↦ sq_nonneg (φ u))).mp hφ0
        exact skewRank2Mat_zero_left fun u ↦ sq_eq_zero_iff.mp (hall u (Finset.mem_univ u))
      · have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ ↦ sq_nonneg (ψ u))).mp hψ0
        exact skewRank2Mat_zero_right fun u ↦ sq_eq_zero_iff.mp (hall u (Finset.mem_univ u))
    refine ⟨0, e₀, e₀, le_rfl, mul_nonneg hFφ0 hFψ0, he₀, he₀, ?_⟩
    rw [hmat0, Complex.ofReal_zero, zero_smul]
  · have hne1 : Sφ ≠ 0 := fun h ↦ hzero (Or.inl h)
    have hne2 : Sψ ≠ 0 := fun h ↦ hzero (Or.inr h)
    have hSφ_pos : 0 < Sφ := lt_of_le_of_ne hSφ0 hne1.symm
    have hSψ_pos : 0 < Sψ := lt_of_le_of_ne hSψ0 hne2.symm
    let nφ := √Sφ
    let nψ := √Sψ
    have hnφ_pos : 0 < nφ := Real.sqrt_pos.mpr hSφ_pos
    have hnψ_pos : 0 < nψ := Real.sqrt_pos.mpr hSψ_pos
    have hnφ_le : nφ ≤ Fφ := by rw [← Real.sqrt_sq hFφ0]; exact Real.sqrt_le_sqrt hφ
    have hnψ_le : nψ ≤ Fψ := by rw [← Real.sqrt_sq hFψ0]; exact Real.sqrt_le_sqrt hψ
    let e₁ : Fin d → ℝ := fun u ↦ φ u / nφ
    let e₂ : Fin d → ℝ := fun u ↦ ψ u / nψ
    have he₁ : (∑ u : Fin d, (e₁ u) ^ 2) = 1 := by
      have hpt : ∀ u : Fin d, (e₁ u) ^ 2 = (φ u) ^ 2 / Sφ := fun u ↦ by
        dsimp only [e₁]; rw [div_pow, Real.sq_sqrt hSφ0]
      rw [Finset.sum_congr rfl fun u _ ↦ hpt u, ← Finset.sum_div]
      exact div_self hSφ_pos.ne'
    have he₂ : (∑ u : Fin d, (e₂ u) ^ 2) = 1 := by
      have hpt : ∀ u : Fin d, (e₂ u) ^ 2 = (ψ u) ^ 2 / Sψ := fun u ↦ by
        dsimp only [e₂]; rw [div_pow, Real.sq_sqrt hSψ0]
      rw [Finset.sum_congr rfl fun u _ ↦ hpt u, ← Finset.sum_div]
      exact div_self hSψ_pos.ne'
    refine ⟨nφ * nψ, e₁, e₂, mul_nonneg hnφ_pos.le hnψ_pos.le,
      mul_le_mul hnφ_le hnψ_le hnψ_pos.le hFφ0, he₁, he₂,
      skewRank2Mat_scale (fun u ↦ (mul_div_cancel₀ (φ u) hnφ_pos.ne').symm)
        (fun u ↦ (mul_div_cancel₀ (ψ u) hnψ_pos.ne').symm)⟩

private theorem quad_idem_bounds {D : ℕ} (P Nk : Operator D)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P)
    (hNk_herm : Nk.IsHermitian) (hNk_idem : Nk * Nk * P = Nk * P)
    (v : Fin D → ℂ) (hv : (∑ x : Fin D, ‖v x‖ ^ 2) = 1) :
    let w := P *ᵥ v
    let q := (∑ x : Fin D, star (w x) * (Nk *ᵥ w) x).re
    0 ≤ q ∧ q ≤ 1 := by
  intro w q
  obtain ⟨_hPw, hw_le⟩ := proj_vec_norm_sq_le P hP_herm hP_idem v
  have hw_le1 : (∑ x : Fin D, ‖w x‖ ^ 2) ≤ 1 := hw_le.trans (le_of_eq hv)
  let uk := Nk *ᵥ w
  have hNk_uk : Nk *ᵥ uk = uk := by
    dsimp only [uk, w]
    rw [Matrix.mulVec_mulVec (P *ᵥ v) Nk Nk, Matrix.mulVec_mulVec v (Nk * Nk) P,
      hNk_idem, ← Matrix.mulVec_mulVec v Nk P]
  have hw_uk : (∑ x : Fin D, star (w x) * uk x) = ∑ x : Fin D, star (uk x) * uk x := by
    symm
    change (∑ x : Fin D, star ((Nk *ᵥ w) x) * uk x) = _
    simp only [Matrix.mulVec, dotProduct, star_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hy : (∑ x : Fin D, star (Nk x y * w y) * uk x) = star (w y) * (∑ x : Fin D,
      Nk y x * uk x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hnk : star (Nk x y) = Nk y x := by
        have := congrFun (congrFun hNk_herm.eq y) x
        simpa only [Matrix.conjTranspose_apply] using this
      rw [star_mul', hnk]; ring
    rw [hy, show (∑ x : Fin D, Nk y x * uk x) = uk y from congrFun hNk_uk y]
  have hq_eq : q = ∑ x : Fin D, ‖uk x‖ ^ 2 := by
    dsimp only [q]
    change (∑ x : Fin D, star (w x) * uk x).re = _
    rw [hw_uk, Complex.re_sum]
    exact Finset.sum_congr rfl fun x _ ↦ star_mul_self_re_eq_norm_sq (uk x)
  have hq_nn : 0 ≤ q := by rw [hq_eq]; exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  let rk : Fin D → ℂ := fun x ↦ w x - uk x
  have hrk_nn : 0 ≤ ∑ x : Fin D, ‖rk x‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have huk_w : (∑ x : Fin D, star (uk x) * w x) = ∑ x : Fin D, star (uk x) * uk x := by
    have hst := congrArg star hw_uk
    simp only [star_sum, star_mul', star_star] at hst
    simpa only [mul_comm] using hst
  have hrk_eq : (∑ x : Fin D, star (rk x) * rk x) =
      (∑ x : Fin D, star (w x) * w x) - (∑ x : Fin D, star (uk x) * uk x) := by
    have hexp : ∀ x : Fin D, star (rk x) * rk x =
        star (w x) * w x - star (w x) * uk x - star (uk x) * w x + star (uk x) * uk x :=
      fun x ↦ by dsimp only [rk]; rw [star_sub]; ring
    rw [Finset.sum_congr rfl fun x _ ↦ hexp x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hw_uk, huk_w]; ring
  have hre := congrArg Complex.re hrk_eq
  simp only [Complex.re_sum, Complex.sub_re, star_mul_self_re_eq_norm_sq] at hre
  exact ⟨hq_nn, by linarith [hq_eq]⟩

private theorem norm_proj_sandwich_four_idem_le {D : ℕ}
    (P Npu Nmu Npd Nmd : Operator D)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P)
    (hNpu_h : Npu.IsHermitian) (hNpu_i : Npu * Npu * P = Npu * P)
    (hNmu_h : Nmu.IsHermitian) (hNmu_i : Nmu * Nmu * P = Nmu * P)
    (hNpd_h : Npd.IsHermitian) (hNpd_i : Npd * Npd * P = Npd * P)
    (hNmd_h : Nmd.IsHermitian) (hNmd_i : Nmd * Nmd * P = Nmd * P) :
    ‖P * ((Npu - Nmu) + (Npd - Nmd)) * P‖ ≤ 2 := by
  let M_tot : Operator D := (Npu - Nmu) + (Npd - Nmd)
  let H_sys : Operator D := P * M_tot * P
  have hM_herm : M_tot.IsHermitian := (hNpu_h.sub hNmu_h).add (hNpd_h.sub hNmd_h)
  have hH_herm : H_sys.IsHermitian := by
    rw [Matrix.IsHermitian]
    dsimp only [H_sys]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_herm.eq, hM_herm.eq,
      Matrix.mul_assoc]
  refine norm_hermitian_le_of_unit_quad_form H_sys hH_herm (by norm_num) fun v hv ↦ ?_
  let w := P *ᵥ v
  have hquad_rew : (∑ x : Fin D, star (v x) * (H_sys *ᵥ v) x) =
      ∑ x : Fin D, star (w x) * (M_tot *ᵥ w) x := by
    change star v ⬝ᵥ ((P * M_tot * P) *ᵥ v) = star (P *ᵥ v) ⬝ᵥ (M_tot *ᵥ (P *ᵥ v))
    rw [Matrix.mul_assoc P M_tot P, ← Matrix.mulVec_mulVec v P (M_tot * P),
      ← Matrix.mulVec_mulVec v M_tot P, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hP_herm.eq]
  have hsplit : (∑ x : Fin D, star (w x) * (M_tot *ᵥ w) x).re =
      (∑ x : Fin D, star (w x) * (Npu *ᵥ w) x).re -
      (∑ x : Fin D, star (w x) * (Nmu *ᵥ w) x).re +
      (∑ x : Fin D, star (w x) * (Npd *ᵥ w) x).re -
      (∑ x : Fin D, star (w x) * (Nmd *ᵥ w) x).re := by
    have hpt : ∀ x : Fin D, star (w x) * (M_tot *ᵥ w) x =
        (star (w x) * (Npu *ᵥ w) x - star (w x) * (Nmu *ᵥ w) x) +
        (star (w x) * (Npd *ᵥ w) x - star (w x) * (Nmd *ᵥ w) x) := fun x ↦ by
      dsimp only [M_tot]
      simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Pi.add_apply, Pi.sub_apply]
      ring
    rw [Finset.sum_congr rfl fun x _ ↦ hpt x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Complex.add_re, Complex.sub_re, Complex.sub_re]
    ring
  have hb_pu := quad_idem_bounds P Npu hP_herm hP_idem hNpu_h hNpu_i v hv
  have hb_mu := quad_idem_bounds P Nmu hP_herm hP_idem hNmu_h hNmu_i v hv
  have hb_pd := quad_idem_bounds P Npd hP_herm hP_idem hNpd_h hNpd_i v hv
  have hb_md := quad_idem_bounds P Nmd hP_herm hP_idem hNmd_h hNmd_i v hv
  rw [hquad_rew, hsplit]
  exact abs_le.mpr ⟨by linarith [hb_pu.1, hb_mu.2, hb_pd.1, hb_md.2],
    by linarith [hb_pu.2, hb_mu.1, hb_pd.2, hb_md.1]⟩

private theorem embedMatrix_sub_gen {m n : ℕ} (r : QRegister m n) (A B : Operator (2 ^ m)) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  have hneg : r.embedMatrix (-B) = -r.embedMatrix B := by
    rw [← neg_one_smul ℂ B, r.embedMatrix_smul, neg_one_smul]
  rw [sub_eq_add_neg, r.embedMatrix_add, hneg, ← sub_eq_add_neg]

private theorem sum_sub_split_compl {α : Type*} [Fintype α] [DecidableEq α]
    {G : Type*} [AddCommGroup G] (S : Finset α) (f g : α → G) :
    (∑ i : α, (f i - g i)) =
      ((∑ i ∈ S, f i) - (∑ i ∈ S, g i)) + ((∑ i ∈ Sᶜ, f i) - (∑ i ∈ Sᶜ, g i)) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_add_sum_compl S f, ← Finset.sum_add_sum_compl S g]
  abel

private theorem embedMatrix_sum_smul_gen {ι : Type*} [Fintype ι] {m n : ℕ}
    (r : ι → QRegister m n) (z : ℂ) (A : Operator (2 ^ m)) :
    (∑ i : ι, (r i).embedMatrix (z • A)) = z • ∑ i : ι, (r i).embedMatrix A := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (r i).embedMatrix_smul z A

private theorem norm_proj_sandwich_smul_le {D : ℕ} (P M : Operator D) {c B : ℝ}
    (hc0 : 0 ≤ c) (hc : c ≤ B) (hM : ‖P * M * P‖ ≤ 2) :
    ‖P * ((c : ℂ) • M) * P‖ ≤ 2 * B := by
  have hp : P * ((c : ℂ) • M) * P = (c : ℂ) • (P * M * P) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hp, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
  nlinarith [norm_nonneg (P * M * P)]

private theorem norm_proj_sandwich_embed_skewRank2_unit_le
    (e₁ e₂ : Fin (2 ^ 18) → ℝ)
    (he₁ : (∑ u : Fin (2 ^ 18), (e₁ u) ^ 2) = 1)
    (he₂ : (∑ u : Fin (2 ^ 18), (e₂ u) ^ 2) = 1)
    (V : Unitary (2 ^ 18))
    (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp *
        (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix (V.1 * skewRank2Mat e₁ e₂ * V.1ᴴ)) *
        fermionicProjector spinUp‖ ≤ 2 := by
  let ξp := unitaryMulVecGen V (chiPlusGen e₁ e₂)
  let ξm := unitaryMulVecGen V (chiMinusGen e₁ e₂)
  have hξp : ∑ u : Fin (2 ^ 18), star (ξp u) * ξp u = 1 :=
    unitaryMulVecGen_norm V (chiPlusGen_norm he₁ he₂)
  have hξm : ∑ u : Fin (2 ^ 18), star (ξm u) * ξm u = 1 :=
    unitaryMulVecGen_norm V (chiMinusGen_norm he₁ he₂)
  have hconj : V.1 * skewRank2Mat e₁ e₂ * V.1ᴴ = rk1_sp ξp - rk1_sp ξm :=
    conj_skewRank2Mat_eq V e₁ e₂
  have hM_eq :
      (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix (V.1 * skewRank2Mat e₁ e₂ * V.1ᴴ)) =
        (nSub_sp ξp spinUp - nSub_sp ξm spinUp) +
          (nSub_sp ξp spinUpᶜ - nSub_sp ξm spinUpᶜ) := by
    rw [hconj, Finset.sum_congr rfl fun i _ ↦
      embedMatrix_sub_gen (rEl_sp i) (rk1_sp ξp) (rk1_sp ξm)]
    exact sum_sub_split_compl spinUp (op_sp ξp) (op_sp ξm)
  have hSup : ∀ i ∈ spinUp, ∀ j ∈ spinUp, i ∈ spinUp ↔ j ∈ spinUp :=
    fun _ hi _ hj ↦ ⟨fun _ ↦ hj, fun _ ↦ hi⟩
  have hSdn : ∀ i ∈ spinUpᶜ, ∀ j ∈ spinUpᶜ, i ∈ spinUp ↔ j ∈ spinUp :=
    fun _ hi _ hj ↦ by
      simp only [Finset.mem_compl] at hi hj
      exact ⟨fun h ↦ (hi h).elim, fun h ↦ (hj h).elim⟩
  rw [hM_eq]
  exact norm_proj_sandwich_four_idem_le (fermionicProjector spinUp)
    (nSub_sp ξp spinUp) (nSub_sp ξm spinUp) (nSub_sp ξp spinUpᶜ) (nSub_sp ξm spinUpᶜ)
    (fermionicProjector_isHermitian spinUp) (fermionicProjector_idem spinUp)
    (nSub_isHermitian_any ξp spinUp) (nSub_mul_self_mul_fermionicProjector hξp spinUp spinUp hSup)
    (nSub_isHermitian_any ξm spinUp) (nSub_mul_self_mul_fermionicProjector hξm spinUp spinUp hSup)
    (nSub_isHermitian_any ξp spinUpᶜ) (nSub_mul_self_mul_fermionicProjector hξp spinUp spinUpᶜ hSdn)
    (nSub_isHermitian_any ξm spinUpᶜ) (nSub_mul_self_mul_fermionicProjector hξm spinUp spinUpᶜ hSdn)

private theorem norm_proj_sandwich_embed_skewRank2_le
    (φ ψ : Fin (2 ^ 18) → ℝ) (V : Unitary (2 ^ 18))
    {Fφ Fψ : ℝ} (hFφ0 : 0 ≤ Fφ) (hFψ0 : 0 ≤ Fψ)
    (hφ : (∑ u : Fin (2 ^ 18), (φ u) ^ 2) ≤ Fφ ^ 2)
    (hψ : (∑ u : Fin (2 ^ 18), (ψ u) ^ 2) ≤ Fψ ^ 2)
    (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp *
        (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix (V.1 * skewRank2Mat φ ψ * V.1ᴴ)) *
        fermionicProjector spinUp‖ ≤ 2 * Fφ * Fψ := by
  obtain ⟨c, e₁, e₂, hc0, hc_le, he₁, he₂, hsc⟩ :=
    skewRank2Mat_scale_unit φ ψ hFφ0 hFψ0 hφ hψ
  have hpull :
      (∑ i : Fin numElectrons, (rEl_sp i).embedMatrix (V.1 * skewRank2Mat φ ψ * V.1ᴴ)) =
        (c : ℂ) • ∑ i : Fin numElectrons,
          (rEl_sp i).embedMatrix (V.1 * skewRank2Mat e₁ e₂ * V.1ᴴ) := by
    rw [hsc, Matrix.mul_smul, Matrix.smul_mul]
    exact embedMatrix_sum_smul_gen rEl_sp (c : ℂ) (V.1 * skewRank2Mat e₁ e₂ * V.1ᴴ)
  rw [hpull, mul_assoc (2 : ℝ) Fφ Fψ]
  exact norm_proj_sandwich_smul_le (fermionicProjector spinUp) _ hc0 hc_le
    (norm_proj_sandwich_embed_skewRank2_unit_le e₁ e₂ he₁ he₂ V spinUp)

/-! ## Section 2: Sextic-Bell Dipole Subtraction & 1D Moment Frobenius Cap -/

/-- Even integer sextic-Bell 1D profile on `[-31, 31]`. -/
def fSexticBellZ (t : ℤ) : ℤ :=
  5381975497 - 4504450 * t ^ 2 + 2996 * t ^ 4 - t ^ 6

/-- Optimal dipole-subtraction scalar `c₀ = 785363 / 10^67`. -/
noncomputable def c0Dip : ℝ := (785363 : ℝ) / (10 : ℝ) ^ 67

private def tNatZ (k : ℕ) : ℤ := (k : ℤ) - 31
private def fNatZ (k : ℕ) : ℤ := fSexticBellZ (tNatZ k)
private def t63 (i : Fin 63) : ℤ := (i.val : ℤ) - 31
private def f63 (i : Fin 63) : ℤ := fSexticBellZ (t63 i)

private def sumRangeZ (g : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumRangeZ g n + g n

private theorem sum_range_eq_sumRangeZ (g : ℕ → ℤ) :
    ∀ n : ℕ, (∑ i ∈ Finset.range n, g i) = sumRangeZ g n
  | 0 => rfl
  | n + 1 => by rw [Finset.sum_range_succ, sumRangeZ, sum_range_eq_sumRangeZ g n]

private theorem sum_fin63_eq_sumRangeZ (g : ℕ → ℤ) :
    (∑ i : Fin 63, (g i.val : ℝ)) = ((sumRangeZ g 63 : ℤ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (g i : ℝ)) 63, ← Int.cast_sum, sum_range_eq_sumRangeZ]

private theorem sumRange_f1 : sumRangeZ fNatZ 63 = 273586423959 := by decide +kernel
private theorem sumRange_m0 :
    sumRangeZ (fun k ↦ (fNatZ k) ^ 2) 63 = 1228043870767229868495 := by decide +kernel
private theorem sumRange_m1 :
    sumRangeZ (fun k ↦ tNatZ k * (fNatZ k) ^ 2) 63 = 0 := by decide +kernel
private theorem sumRange_m2 :
    sumRangeZ (fun k ↦ (tNatZ k) ^ 2 * (fNatZ k) ^ 2) 63 = 283174258570147953487680 := by
      decide +kernel

private theorem sum_f63_real : (∑ i : Fin 63, (f63 i : ℝ)) = 273586423959 := by
  simpa [f63, t63, fNatZ, tNatZ, sumRange_f1] using sum_fin63_eq_sumRangeZ fNatZ

private theorem nat_three_sq_eq_zero {a b c : ℕ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h12 : a ^ 2 + b ^ 2 = 0 ∧ c ^ 2 = 0 := Nat.add_eq_zero_iff.mp h
  have h1 : a ^ 2 = 0 ∧ b ^ 2 = 0 := Nat.add_eq_zero_iff.mp h12.1
  exact ⟨sq_eq_zero_iff.mp h1.1, sq_eq_zero_iff.mp h1.2, sq_eq_zero_iff.mp h12.2⟩

private theorem sum_prod3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (a : α → ℝ) (b : β → ℝ) (c : γ → ℝ) :
    (∑ x : α × β × γ, a x.1 * b x.2.1 * c x.2.2) =
      (∑ x, a x) * (∑ y, b y) * (∑ z, c z) := by
  rw [Fintype.sum_prod_type]
  have h1 : ∀ x : α, (∑ yz : β × γ, a x * b yz.1 * c yz.2) = a x * ((∑ y, b y) * (∑ z, c z)) :=
    fun x ↦ by
      rw [Fintype.sum_prod_type]
      have h2 : ∀ y : β, (∑ z : γ, a x * b y * c z) = (a x * b y) * (∑ z, c z) :=
        fun y ↦ by rw [← Finset.mul_sum]
      rw [Finset.sum_congr rfl fun y _ ↦ h2 y, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
  rw [Finset.sum_congr rfl fun x _ ↦ h1 x, ← Finset.sum_mul, ← mul_assoc]

private theorem sum_grid63_3_mul (s : ℝ) (a b c : Fin 63 → ℝ) :
    (∑ g : Grid63_3, s * (a g.1 * b g.2.1 * c g.2.2)) =
      s * ((∑ i, a i) * (∑ j, b j) * (∑ k, c k)) := by
  rw [← Finset.mul_sum, sum_prod3 a b c]

private theorem sum_f63_sq_real :
    (∑ i : Fin 63, (f63 i : ℝ) ^ 2) = 1228043870767229868495 := by
  have h := sum_fin63_eq_sumRangeZ (fun k ↦ (fNatZ k) ^ 2)
  rw [sumRange_m0] at h
  simpa [f63, t63, fNatZ, tNatZ, Int.cast_pow] using h

private theorem sum_t63_f63_sq_real :
    (∑ i : Fin 63, (t63 i : ℝ) * (f63 i : ℝ) ^ 2) = 0 := by
  have h := sum_fin63_eq_sumRangeZ (fun k ↦ tNatZ k * (fNatZ k) ^ 2)
  rw [sumRange_m1] at h
  simpa [f63, t63, fNatZ, tNatZ, Int.cast_mul, Int.cast_pow] using h

private theorem sum_t63_sq_f63_sq_real :
    (∑ i : Fin 63, (t63 i : ℝ) ^ 2 * (f63 i : ℝ) ^ 2) = 283174258570147953487680 := by
  have h := sum_fin63_eq_sumRangeZ (fun k ↦ (tNatZ k) ^ 2 * (fNatZ k) ^ 2)
  rw [sumRange_m2] at h
  simpa [f63, t63, fNatZ, tNatZ, Int.cast_mul, Int.cast_pow] using h

private theorem f63_flip63 (i : Fin 63) : f63 (flip63 i) = f63 i := by
  have ht : t63 (flip63 i) = -t63 i := by
    dsimp [t63, flip63]; have := i.isLt; omega
  unfold f63
  rw [ht]
  unfold fSexticBellZ; ring

private theorem inGrid18_succGrid63_3 (g : Grid63_3) :
    inGrid18 (u18ToGrid64_3.symm (succGrid63_3 g)) := by
  unfold inGrid18 InMomGrid3D pOf18 u18ToGrid64_3 succGrid63_3 shiftedMom3D
  intro w
  simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  fin_cases w
  · exact (inMomGrid1D_shiftedFin64ToInt_iff g.1.succ).mpr (Fin.succ_ne_zero g.1)
  · exact (inMomGrid1D_shiftedFin64ToInt_iff g.2.1.succ).mpr (Fin.succ_ne_zero g.2.1)
  · exact (inMomGrid1D_shiftedFin64ToInt_iff g.2.2.succ).mpr (Fin.succ_ne_zero g.2.2)

private theorem pOf18_succGrid_apply (g : Grid63_3) (w : Fin 3) :
    pOf18 (u18ToGrid64_3.symm (succGrid63_3 g)) w =
      match w with | 0 => t63 g.1 | 1 => t63 g.2.1 | _ => t63 g.2.2 := by
  unfold pOf18 u18ToGrid64_3 succGrid63_3 shiftedMom3D shiftedFin64ToInt t63
  simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  fin_cases w <;> (dsimp [fin3EquivProd3]; simp only [Fin.val_succ]; push_cast; ring)

open Classical in
/-- Separable 3D sextic-Bell vector `φ(u) = f(p₀) f(p₁) f(p₂)` supported on `inGrid18`. -/
noncomputable def nucPhi (u : Fin (2 ^ 18)) : ℝ :=
  if inGrid18 u then
    (fSexticBellZ (pOf18 u 0) * fSexticBellZ (pOf18 u 1) * fSexticBellZ (pOf18 u 2) : ℝ)
  else 0

/-- Dipole-modulated companion vector `ψ(u) = (2 / cellSide) * c0Dip * (p(u) · δ) * φ(u)`. -/
noncomputable def nucPsi (W : ℕ) (c : Configuration) (l : Fin 216) (u : Fin (2 ^ 18)) : ℝ :=
  (2 / cellSide) * c0Dip * (∑ w : Fin 3, (pOf18 u w : ℝ) * nucDelta W c l w) * nucPhi u

/-- Dipole-subtracted chiral remainder matrix `nucMatA - skewRank2Mat nucPhi nucPsi`. -/
noncomputable def nucMatARem (W : ℕ) (c : Configuration) (l : Fin 216) : Operator (2 ^ 18) :=
  nucMatA W c l - skewRank2Mat nucPhi (nucPsi W c l)

private theorem nucPhi_succGrid63_3 (g : Grid63_3) :
    nucPhi (u18ToGrid64_3.symm (succGrid63_3 g)) =
      (f63 g.1 : ℝ) * (f63 g.2.1 : ℝ) * (f63 g.2.2 : ℝ) := by
  have hig := inGrid18_succGrid63_3 g
  unfold nucPhi
  rw [ite_eq_left hig, pOf18_succGrid_apply g 0, pOf18_succGrid_apply g 1, pOf18_succGrid_apply g 2]
  dsimp [f63]; push_cast; rfl

open Classical in
private theorem sum_nucPhi_sq_eq :
    (∑ u : Fin (2 ^ 18), (nucPhi u) ^ 2) = (1228043870767229868495 : ℝ) ^ 3 := by
  have hrew : ∀ u : Fin (2 ^ 18),
      (nucPhi u) ^ 2 = if inGrid18 u then (nucPhi u) ^ 2 else 0 := fun u ↦ by
    by_cases h : inGrid18 u
    · simp [h]
    · unfold nucPhi; simp [h]
  rw [Finset.sum_congr rfl fun u _ ↦ hrew u, sum_u18_inGrid18]
  have hg : ∀ g : Grid63_3,
      (nucPhi (u18ToGrid64_3.symm (succGrid63_3 g))) ^ 2 =
        (f63 g.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2 * (f63 g.2.2 : ℝ) ^ 2 := fun g ↦ by
    rw [nucPhi_succGrid63_3]; ring
  rw [Finset.sum_congr rfl fun g _ ↦ hg g,
    sum_prod3 (fun i ↦ (f63 i : ℝ) ^ 2) (fun j ↦ (f63 j : ℝ) ^ 2) (fun k ↦ (f63 k : ℝ) ^ 2),
    sum_f63_sq_real]; ring

open Classical in
private theorem sum_nucPsi_sq_le (W : ℕ) (c : Configuration) (l : Fin 216) :
    (∑ u : Fin (2 ^ 18), (nucPsi W c l u) ^ 2) ≤
      ((2 / lLoRat) * c0Dip * ((1 / 2 : ℝ) / (2 ^ W : ℝ)) *
        √(3 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2)) ^ 2 := by
  set δ := nucDelta W c l
  set dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
  have hrew : ∀ u : Fin (2 ^ 18),
      (nucPsi W c l u) ^ 2 = if inGrid18 u then (nucPsi W c l u) ^ 2 else 0 := fun u ↦ by
    by_cases h : inGrid18 u
    · simp [h]
    · unfold nucPsi nucPhi; simp [h]
  rw [Finset.sum_congr rfl fun u _ ↦ hrew u, sum_u18_inGrid18]
  have hg : ∀ g : Grid63_3,
      (nucPsi W c l (u18ToGrid64_3.symm (succGrid63_3 g))) ^ 2 =
        ((2 / cellSide) * c0Dip) ^ 2 *
          (((t63 g.1 : ℝ) * δ 0 + (t63 g.2.1 : ℝ) * δ 1 + (t63 g.2.2 : ℝ) * δ 2) ^ 2 *
            ((f63 g.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2 * (f63 g.2.2 : ℝ) ^ 2)) := fun g ↦ by
    unfold nucPsi
    rw [nucPhi_succGrid63_3, Fin.sum_univ_three, pOf18_succGrid_apply g 0,
      pOf18_succGrid_apply g 1, pOf18_succGrid_apply g 2]
    simp only [Fin.isValue]
    change _ = ((2 / cellSide) * c0Dip) ^ 2 *
      (((t63 g.1 : ℝ) * nucDelta W c l 0 + (t63 g.2.1 : ℝ) * nucDelta W c l 1 +
          (t63 g.2.2 : ℝ) * nucDelta W c l 2) ^ 2 *
        ((f63 g.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2 * (f63 g.2.2 : ℝ) ^ 2))
    ring
  simp_rw [hg, ← Finset.mul_sum]
  have hgrid :
      (∑ g : Grid63_3,
        ((t63 g.1 : ℝ) * δ 0 + (t63 g.2.1 : ℝ) * δ 1 + (t63 g.2.2 : ℝ) * δ 2) ^ 2 *
          ((f63 g.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2 * (f63 g.2.2 : ℝ) ^ 2)) =
        (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) *
          ((283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2) := by
    have hexp : ∀ g : Grid63_3,
        ((t63 g.1 : ℝ) * δ 0 + (t63 g.2.1 : ℝ) * δ 1 + (t63 g.2.2 : ℝ) * δ 2) ^ 2 *
          ((f63 g.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2 * (f63 g.2.2 : ℝ) ^ 2) =
          δ 0 ^ 2 * (((t63 g.1 : ℝ) ^ 2 * (f63 g.1 : ℝ) ^ 2) * (f63 g.2.1 : ℝ) ^ 2 *
            (f63 g.2.2 : ℝ) ^ 2) +
          δ 1 ^ 2 * ((f63 g.1 : ℝ) ^ 2 * ((t63 g.2.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2) *
            (f63 g.2.2 : ℝ) ^ 2) +
          δ 2 ^ 2 * ((f63 g.1 : ℝ) ^ 2 * (f63 g.2.1 : ℝ) ^ 2 * ((t63 g.2.2 : ℝ) ^ 2 *
            (f63 g.2.2 : ℝ) ^ 2)) +
          (2 * δ 0 * δ 1) * (((t63 g.1 : ℝ) * (f63 g.1 : ℝ) ^ 2) * ((t63 g.2.1 : ℝ) *
            (f63 g.2.1 : ℝ) ^ 2) * (f63 g.2.2 : ℝ) ^ 2) +
          (2 * δ 0 * δ 2) * (((t63 g.1 : ℝ) * (f63 g.1 : ℝ) ^ 2) * (f63 g.2.1 : ℝ) ^ 2 *
            ((t63 g.2.2 : ℝ) * (f63 g.2.2 : ℝ) ^ 2)) +
          (2 * δ 1 * δ 2) * ((f63 g.1 : ℝ) ^ 2 * ((t63 g.2.1 : ℝ) * (f63 g.2.1 : ℝ) ^ 2) *
            ((t63 g.2.2 : ℝ) * (f63 g.2.2 : ℝ) ^ 2)) :=
      fun g ↦ by ring
    rw [Finset.sum_congr rfl fun g _ ↦ hexp g,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_grid63_3_mul (δ 0 ^ 2) (fun i ↦ (t63 i : ℝ) ^ 2 * (f63 i : ℝ) ^ 2) (fun j ↦
        (f63 j : ℝ) ^ 2) (fun k ↦ (f63 k : ℝ) ^ 2),
      sum_grid63_3_mul (δ 1 ^ 2) (fun i ↦ (f63 i : ℝ) ^ 2) (fun j ↦
        (t63 j : ℝ) ^ 2 * (f63 j : ℝ) ^ 2) (fun k ↦ (f63 k : ℝ) ^ 2),
      sum_grid63_3_mul (δ 2 ^ 2) (fun i ↦ (f63 i : ℝ) ^ 2) (fun j ↦ (f63 j : ℝ) ^ 2) (fun k ↦
        (t63 k : ℝ) ^ 2 * (f63 k : ℝ) ^ 2),
      sum_grid63_3_mul (2 * δ 0 * δ 1) (fun i ↦ (t63 i : ℝ) * (f63 i : ℝ) ^ 2) (fun j ↦
        (t63 j : ℝ) * (f63 j : ℝ) ^ 2) (fun k ↦ (f63 k : ℝ) ^ 2),
      sum_grid63_3_mul (2 * δ 0 * δ 2) (fun i ↦ (t63 i : ℝ) * (f63 i : ℝ) ^ 2) (fun j ↦
        (f63 j : ℝ) ^ 2) (fun k ↦ (t63 k : ℝ) * (f63 k : ℝ) ^ 2),
      sum_grid63_3_mul (2 * δ 1 * δ 2) (fun i ↦ (f63 i : ℝ) ^ 2) (fun j ↦
        (t63 j : ℝ) * (f63 j : ℝ) ^ 2) (fun k ↦ (t63 k : ℝ) * (f63 k : ℝ) ^ 2),
      sum_t63_sq_f63_sq_real, sum_t63_f63_sq_real, sum_f63_sq_real]
    ring
  rw [hgrid]
  have hδ_sq : ∀ w : Fin 3, δ w ^ 2 ≤ dmax ^ 2 := fun w ↦ by
    have habs : |δ w| ≤ dmax := abs_nucDelta_le W c l w
    have hd0 : 0 ≤ dmax := by dsimp [dmax]; positivity
    nlinarith [abs_le.mp habs]
  have hsum_δ : δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2 ≤ 3 * dmax ^ 2 := by
    linarith [hδ_sq 0, hδ_sq 1, hδ_sq 2]
  have hsc_le : ((2 / cellSide) * c0Dip) ^ 2 ≤ ((2 / lLoRat) * c0Dip) ^ 2 := by
    have h1 : 2 / cellSide ≤ 2 / lLoRat :=
      div_le_div_of_nonneg_left zero_le_two lLoRat_pos lLoRat_le_cellSide
    have hc0 : 0 ≤ c0Dip := by unfold c0Dip; positivity
    exact pow_le_pow_left₀ (mul_nonneg (div_nonneg zero_le_two cellSide_pos.le) hc0)
      (mul_le_mul_of_nonneg_right h1 hc0) 2
  have hM_nn : (0 : ℝ) ≤ (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2 := by
    norm_num
  have hinner : (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) *
        ((283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2) ≤
      (3 * dmax ^ 2) * ((283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hsum_δ hM_nn
  have hprod :=
    mul_le_mul hsc_le hinner (mul_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (sq_nonneg _)) hM_nn) (sq_nonneg _)
  have hrt :
      ((2 / lLoRat) * c0Dip * dmax *
        √(3 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2)) ^ 2 =
      ((2 / lLoRat) * c0Dip) ^ 2 *
        ((3 * dmax ^ 2) *
          ((283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2)) := by
    rw [mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤
        3 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2)]
    ring
  rw [hrt]; exact hprod

private def bell3P (x : PairGrid63_3) : ℝ :=
  ((f63 x.1.1 : ℝ) * (f63 x.1.2.1 : ℝ) * (f63 x.1.2.2 : ℝ)) *
    ((f63 x.2.1 : ℝ) * (f63 x.2.2.1 : ℝ) * (f63 x.2.2.2 : ℝ))

private noncomputable def remKerSqP (x : PairGrid63_3) : ℝ :=
  if r2P x = 0 then 0 else (1 / (r2P x : ℝ) - c0Dip * bell3P x) ^ 2

private def bellOffDiagP (x : PairGrid63_3) : ℝ :=
  if r2P x = 0 then 0 else bell3P x

private theorem bell3P_flipAxis0P (x : PairGrid63_3) : bell3P (flipAxis0P x) = bell3P x := by
  simp only [bell3P, flipAxis0P, Equiv.coe_fn_mk, f63_flip63]

private theorem bell3P_flipAxis1P (x : PairGrid63_3) : bell3P (flipAxis1P x) = bell3P x := by
  simp only [bell3P, flipAxis1P, Equiv.coe_fn_mk, f63_flip63]

private theorem bell3P_rotAxesP (x : PairGrid63_3) : bell3P (rotAxesP x) = bell3P x := by
  unfold bell3P rotAxesP; dsimp; ring

private theorem r2P_flipAxis0P (x : PairGrid63_3) : r2P (flipAxis0P x) = r2P x := by
  simp only [r2P, d0P, d1P, d2P, flipAxis0P, Equiv.coe_fn_mk, flip63_sub_int, Int.natAbs_neg]

private theorem r2P_flipAxis1P (x : PairGrid63_3) : r2P (flipAxis1P x) = r2P x := by
  simp only [r2P, d0P, d1P, d2P, flipAxis1P, Equiv.coe_fn_mk, flip63_sub_int, Int.natAbs_neg]

private theorem r2P_rotAxesP (x : PairGrid63_3) : r2P (rotAxesP x) = r2P x := by
  simp only [r2P, d0P, d1P, d2P, rotAxesP, Equiv.coe_fn_mk]
  ring

private theorem remKerSqP_flipAxis0P (x : PairGrid63_3) : remKerSqP (flipAxis0P x) = remKerSqP x :=
  by
  unfold remKerSqP; rw [r2P_flipAxis0P, bell3P_flipAxis0P]

private theorem remKerSqP_flipAxis1P (x : PairGrid63_3) : remKerSqP (flipAxis1P x) = remKerSqP x :=
  by
  unfold remKerSqP; rw [r2P_flipAxis1P, bell3P_flipAxis1P]

private theorem remKerSqP_rotAxesP (x : PairGrid63_3) : remKerSqP (rotAxesP x) = remKerSqP x := by
  unfold remKerSqP; rw [r2P_rotAxesP, bell3P_rotAxesP]

private theorem cubic_sym_remKerSqP (δ : Fin 3 → ℝ) :
    (∑ x : PairGrid63_3,
      ((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) ^ 2 * remKerSqP x) =
      ((δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3) * (∑ x : PairGrid63_3, (r2P x : ℝ) * remKerSqP x) := by
  have hexp : ∀ x : PairGrid63_3,
      ((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) ^ 2 * remKerSqP x =
        δ 0 ^ 2 * ((d0P x : ℝ) ^ 2 * remKerSqP x) +
        δ 1 ^ 2 * ((d1P x : ℝ) ^ 2 * remKerSqP x) +
        δ 2 ^ 2 * ((d2P x : ℝ) ^ 2 * remKerSqP x) +
        (2 * δ 0 * δ 1) * ((d0P x : ℝ) * (d1P x : ℝ) * remKerSqP x) +
        (2 * δ 0 * δ 2) * ((d0P x : ℝ) * (d2P x : ℝ) * remKerSqP x) +
        (2 * δ 1 * δ 2) * ((d1P x : ℝ) * (d2P x : ℝ) * remKerSqP x) := fun _ ↦ by ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd0_fl : ∀ x : PairGrid63_3, (d0P (flipAxis0P x) : ℝ) = -(d0P x : ℝ) := fun x ↦ by
    simp only [d0P, flipAxis0P, Equiv.coe_fn_mk]
    exact_mod_cast flip63_sub_int x.1.1 x.2.1
  have hc01 : (∑ x : PairGrid63_3, (d0P x : ℝ) * (d1P x : ℝ) * remKerSqP x) = 0 :=
    sum_eq_zero_of_involutive_neg flipAxis0P _ fun x ↦ by
      rw [hd0_fl x, show d1P (flipAxis0P x) = d1P x from rfl, remKerSqP_flipAxis0P]
      ring
  have hc02 : (∑ x : PairGrid63_3, (d0P x : ℝ) * (d2P x : ℝ) * remKerSqP x) = 0 :=
    sum_eq_zero_of_involutive_neg flipAxis0P _ fun x ↦ by
      rw [hd0_fl x, show d2P (flipAxis0P x) = d2P x from rfl, remKerSqP_flipAxis0P]
      ring
  have hc12 : (∑ x : PairGrid63_3, (d1P x : ℝ) * (d2P x : ℝ) * remKerSqP x) = 0 :=
    sum_eq_zero_of_involutive_neg flipAxis1P _ fun x ↦ by
      have hd1 : (d1P (flipAxis1P x) : ℝ) = -(d1P x : ℝ) := by
        simp only [d1P, flipAxis1P, Equiv.coe_fn_mk]
        exact_mod_cast flip63_sub_int x.1.2.1 x.2.2.1
      rw [hd1, show d2P (flipAxis1P x) = d2P x from rfl, remKerSqP_flipAxis1P]
      ring
  have hrot01 : (∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * remKerSqP x) =
      ∑ x : PairGrid63_3, (d1P x : ℝ) ^ 2 * remKerSqP x := by
    rw [← Equiv.sum_comp rotAxesP (fun x ↦ (d0P x : ℝ) ^ 2 * remKerSqP x)]
    exact Finset.sum_congr rfl fun x _ ↦ by
      rw [show d0P (rotAxesP x) = d1P x from rfl, remKerSqP_rotAxesP]
  have hrot12 : (∑ x : PairGrid63_3, (d1P x : ℝ) ^ 2 * remKerSqP x) =
      ∑ x : PairGrid63_3, (d2P x : ℝ) ^ 2 * remKerSqP x := by
    rw [← Equiv.sum_comp rotAxesP (fun x ↦ (d1P x : ℝ) ^ 2 * remKerSqP x)]
    exact Finset.sum_congr rfl fun x _ ↦ by
      rw [show d1P (rotAxesP x) = d2P x from rfl, remKerSqP_rotAxesP]
  have hsum3 : (∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * remKerSqP x) +
      (∑ x : PairGrid63_3, (d1P x : ℝ) ^ 2 * remKerSqP x) +
      (∑ x : PairGrid63_3, (d2P x : ℝ) ^ 2 * remKerSqP x) =
      ∑ x : PairGrid63_3, (r2P x : ℝ) * remKerSqP x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by
      rw [r2P_cast_eq x]
      ring
  have hS2 : (∑ x : PairGrid63_3, (d2P x : ℝ) ^ 2 * remKerSqP x) =
      (∑ x : PairGrid63_3, (r2P x : ℝ) * remKerSqP x) / 3 := by
    linarith [hrot01, hrot12, hsum3]
  rw [hc01, hc02, hc12, hrot01, hrot12, hS2]
  ring

private theorem r2P_eq_zero_iff_eq (g1 g2 : Grid63_3) : r2P (g1, g2) = 0 ↔ g1 = g2 := by
  constructor
  · intro hz
    rcases g1 with ⟨a0, a1, a2⟩; rcases g2 with ⟨b0, b1, b2⟩
    unfold r2P d0P d1P d2P at hz
    dsimp only at hz
    rcases nat_three_sq_eq_zero hz with ⟨h0, h1, h2⟩
    have e0 : a0 = b0 := Fin.ext (by have := Int.natAbs_eq_zero.mp h0; omega)
    have e1 : a1 = b1 := Fin.ext (by have := Int.natAbs_eq_zero.mp h1; omega)
    have e2 : a2 = b2 := Fin.ext (by have := Int.natAbs_eq_zero.mp h2; omega)
    subst e0 e1 e2; rfl
  · rintro rfl; simp [r2P, d0P, d1P, d2P]

private theorem sum_bellOffDiagP_eq :
    (∑ x : PairGrid63_3, bellOffDiagP x) =
      (273586423959 : ℝ) ^ 6 - (1228043870767229868495 : ℝ) ^ 3 := by
  have hfull : (∑ x : PairGrid63_3, bell3P x) = (273586423959 : ℝ) ^ 6 := by
    rw [Fintype.sum_prod_type]
    have hg2 : ∀ g1 : Grid63_3,
        (∑ g2 : Grid63_3, bell3P (g1, g2)) =
          ((f63 g1.1 : ℝ) * (f63 g1.2.1 : ℝ) * (f63 g1.2.2 : ℝ)) * (273586423959 : ℝ) ^ 3 :=
      fun g1 ↦ by
        have hpt : ∀ g2 : Grid63_3, bell3P (g1, g2) =
            ((f63 g1.1 : ℝ) * (f63 g1.2.1 : ℝ) * (f63 g1.2.2 : ℝ)) *
              ((f63 g2.1 : ℝ) * (f63 g2.2.1 : ℝ) * (f63 g2.2.2 : ℝ)) := fun _ ↦ rfl
        rw [Finset.sum_congr rfl fun g2 _ ↦ hpt g2, ← Finset.mul_sum,
          sum_prod3 (fun i ↦ (f63 i : ℝ)) (fun j ↦ (f63 j : ℝ)) (fun k ↦ (f63 k : ℝ)),
          sum_f63_real]; ring
    rw [Finset.sum_congr rfl fun g1 _ ↦ hg2 g1, ← Finset.sum_mul,
      sum_prod3 (fun i ↦ (f63 i : ℝ)) (fun j ↦ (f63 j : ℝ)) (fun k ↦ (f63 k : ℝ)),
      sum_f63_real]; ring
  have hdiag : (∑ g1 : Grid63_3, ∑ g2 : Grid63_3, if g1 = g2 then bell3P (g1, g2) else 0) =
      (1228043870767229868495 : ℝ) ^ 3 := by
    have h1 : ∀ g1 : Grid63_3,
        (∑ g2 : Grid63_3, if g1 = g2 then bell3P (g1, g2) else 0) =
          (f63 g1.1 : ℝ) ^ 2 * (f63 g1.2.1 : ℝ) ^ 2 * (f63 g1.2.2 : ℝ) ^ 2 := fun g1 ↦ by
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ g1)]
      unfold bell3P; ring
    rw [Finset.sum_congr rfl fun g1 _ ↦ h1 g1,
      sum_prod3 (fun i ↦ (f63 i : ℝ) ^ 2) (fun j ↦ (f63 j : ℝ) ^ 2) (fun k ↦ (f63 k : ℝ) ^ 2),
      sum_f63_sq_real]; ring
  have hsplit : (∑ x : PairGrid63_3, bellOffDiagP x) +
      (∑ g1 : Grid63_3, ∑ g2 : Grid63_3, if g1 = g2 then bell3P (g1, g2) else 0) =
      ∑ x : PairGrid63_3, bell3P x := by
    rw [Fintype.sum_prod_type (f := bellOffDiagP), ← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun g1 _ ↦ ?_).trans (Fintype.sum_prod_type (f := bell3P)).symm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g2 _ ↦ ?_
    unfold bellOffDiagP
    by_cases h : g1 = g2
    · rw [ite_eq_left ((r2P_eq_zero_iff_eq g1 g2).mpr h), ite_eq_left h, zero_add]
    · rw [ite_eq_right (mt (r2P_eq_zero_iff_eq g1 g2).mp h), ite_eq_right h, add_zero]
  linarith

private theorem sum_r2P_bell3P_sq_eq :
    (∑ x : PairGrid63_3, (r2P x : ℝ) * (bell3P x) ^ 2) =
      6 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 5 := by
  have hr01 : (∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * (bell3P x) ^ 2) =
      ∑ x : PairGrid63_3, (d1P x : ℝ) ^ 2 * (bell3P x) ^ 2 := by
    rw [← Equiv.sum_comp rotAxesP (fun x ↦ (d0P x : ℝ) ^ 2 * (bell3P x) ^ 2)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hd : d0P (rotAxesP x) = d1P x := rfl
    rw [hd, bell3P_rotAxesP]
  have hr12 : (∑ x : PairGrid63_3, (d1P x : ℝ) ^ 2 * (bell3P x) ^ 2) =
      ∑ x : PairGrid63_3, (d2P x : ℝ) ^ 2 * (bell3P x) ^ 2 := by
    rw [← Equiv.sum_comp rotAxesP (fun x ↦ (d1P x : ℝ) ^ 2 * (bell3P x) ^ 2)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hd : d1P (rotAxesP x) = d2P x := rfl
    rw [hd, bell3P_rotAxesP]
  have hsum3 : (∑ x : PairGrid63_3, (r2P x : ℝ) * (bell3P x) ^ 2) =
      3 * ∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * (bell3P x) ^ 2 := by
    have hpt : ∀ x : PairGrid63_3, (r2P x : ℝ) * (bell3P x) ^ 2 =
        (d0P x : ℝ) ^ 2 * (bell3P x) ^ 2 + (d1P x : ℝ) ^ 2 * (bell3P x) ^ 2 +
          (d2P x : ℝ) ^ 2 * (bell3P x) ^ 2 := fun x ↦ by rw [r2P_cast_eq x]; ring
    simp_rw [hpt, Finset.sum_add_distrib]
    linarith [hr01, hr12]
  have hpair1D_m0 : (∑ p : Fin 63 × Fin 63, (f63 p.1 : ℝ) ^ 2 * (f63 p.2 : ℝ) ^ 2) =
      (1228043870767229868495 : ℝ) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, sum_f63_sq_real, ← Finset.sum_mul, sum_f63_sq_real]; ring
  have hpair1D_d2 :
      (∑ p : Fin 63 × Fin 63,
        (((p.1.val : ℤ) - (p.2.val : ℤ) : ℤ) : ℝ) ^ 2 * (f63 p.1 : ℝ) ^ 2 * (f63 p.2 : ℝ) ^ 2) =
        2 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) := by
    rw [Fintype.sum_prod_type]
    have hsub : ∀ i j : Fin 63, (((i.val : ℤ) - (j.val : ℤ) : ℤ) : ℝ) = (t63 i : ℝ) - (t63 j : ℝ) :=
      fun i j ↦ by unfold t63; push_cast; ring
    have hexp : ∀ i j : Fin 63,
        (((i.val : ℤ) - (j.val : ℤ) : ℤ) : ℝ) ^ 2 * (f63 i : ℝ) ^ 2 * (f63 j : ℝ) ^ 2 =
          ((t63 i : ℝ) ^ 2 * (f63 i : ℝ) ^ 2) * (f63 j : ℝ) ^ 2 -
          2 * ((t63 i : ℝ) * (f63 i : ℝ) ^ 2) * ((t63 j : ℝ) * (f63 j : ℝ) ^ 2) +
          (f63 i : ℝ) ^ 2 * ((t63 j : ℝ) ^ 2 * (f63 j : ℝ) ^ 2) := fun i j ↦ by
      rw [hsub i j]; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_f63_sq_real, sum_t63_f63_sq_real, sum_t63_sq_f63_sq_real]
    simp only [mul_zero, Finset.sum_const_zero, sub_zero, ← Finset.sum_mul,
      sum_f63_sq_real, sum_t63_sq_f63_sq_real]
    ring
  have hd0_eval : (∑ x : PairGrid63_3, (d0P x : ℝ) ^ 2 * (bell3P x) ^ 2) =
      2 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 5 := by
    rw [← Equiv.sum_comp pairGridReorder.symm (fun x ↦ (d0P x : ℝ) ^ 2 * (bell3P x) ^ 2)]
    have hleaf : ∀ x : (Fin 63 × Fin 63) × (Fin 63 × Fin 63) × (Fin 63 × Fin 63),
        (d0P (pairGridReorder.symm x) : ℝ) ^ 2 * (bell3P (pairGridReorder.symm x)) ^ 2 =
        ((((x.1.1.val : ℤ) - (x.1.2.val : ℤ) : ℤ) : ℝ) ^ 2 * (f63 x.1.1 : ℝ) ^ 2 *
          (f63 x.1.2 : ℝ) ^ 2) *
          ((f63 x.2.1.1 : ℝ) ^ 2 * (f63 x.2.1.2 : ℝ) ^ 2) *
          ((f63 x.2.2.1 : ℝ) ^ 2 * (f63 x.2.2.2 : ℝ) ^ 2) := fun x ↦ by
      unfold d0P bell3P pairGridReorder; simp only [Equiv.coe_fn_symm_mk]; ring
    rw [Finset.sum_congr rfl fun x _ ↦ hleaf x,
      sum_prod3
        (fun p0 : Fin 63 × Fin 63 ↦
          (((p0.1.val : ℤ) - (p0.2.val : ℤ) : ℤ) : ℝ) ^ 2 * (f63 p0.1 : ℝ) ^ 2 * (f63 p0.2 : ℝ) ^ 2)
        (fun p1 : Fin 63 × Fin 63 ↦ (f63 p1.1 : ℝ) ^ 2 * (f63 p1.2 : ℝ) ^ 2)
        (fun p2 : Fin 63 × Fin 63 ↦ (f63 p2.1 : ℝ) ^ 2 * (f63 p2.2 : ℝ) ^ 2),
      hpair1D_d2, hpair1D_m0]; ring
  rw [hsum3, hd0_eval]; ring

/-- Compact rational upper cap `49989973949147 / 10^6` on the dipole-subtracted 3D remainder sum. -/
noncomputable def remSumCapRat : ℝ := (49989973949147 : ℝ) / 1000000

private theorem sum_r2P_remKerSqP_le :
    (∑ x : PairGrid63_3, (r2P x : ℝ) * remKerSqP x) ≤ remSumCapRat := by
  have hpt : ∀ x : PairGrid63_3,
      (r2P x : ℝ) * remKerSqP x =
        invR2P x - 2 * c0Dip * bellOffDiagP x + c0Dip ^ 2 * ((r2P x : ℝ) * (bell3P x) ^ 2) :=
    fun x ↦ by
      unfold remKerSqP invR2P bellOffDiagP
      by_cases hr : r2P x = 0
      · simp [hr]
      · simp only [hr, ↓reduceIte]
        have hrR : (r2P x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
        field_simp [hrR]; ring
  simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_bellOffDiagP_eq, sum_r2P_bell3P_sq_eq]
  have hexact_le :
      (1385394456 : ℝ) / 16 -
        2 * c0Dip * ((273586423959 : ℝ) ^ 6 - (1228043870767229868495 : ℝ) ^ 3) +
        c0Dip ^ 2 * (6 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 5) ≤
        remSumCapRat := by
    unfold c0Dip remSumCapRat; norm_num
  linarith [sum_invR2P_le, hexact_le]

private theorem nucMatARem_imag (W : ℕ) (c : Configuration) (l : Fin 216) (u v : Fin (2 ^ 18)) :
    star (nucMatARem W c l u v) = -nucMatARem W c l u v := by
  unfold nucMatARem
  simp only [Matrix.sub_apply, star_sub, nucMatA_imag, skewRank2Mat_imag]; ring

private theorem nucMatARem_isHermitian (W : ℕ) (c : Configuration) (l : Fin 216) :
    (nucMatARem W c l).IsHermitian :=
  (nucMatA_isHermitian W c l).sub (skewRank2Mat_isHermitian nucPhi (nucPsi W c l))

open Classical in
private theorem frob_nucMatARem_le (W : ℕ) (c : Configuration) (l : Fin 216) :
    (∑ u : Fin (2 ^ 18), ∑ v : Fin (2 ^ 18), ‖nucMatARem W c l u v‖ ^ 2) ≤
      ((2 / lLoRat) * ((1 / 2 : ℝ) / (2 ^ W : ℝ)) * √remSumCapRat) ^ 2 := by
  have hcell_ne : cellSide ≠ 0 := cellSide_pos.ne'
  set δ := nucDelta W c l
  have hzero_uv : ∀ u v : Fin (2 ^ 18), ¬(inGrid18 u ∧ inGrid18 v) →
      nucMatARem W c l u v = 0 := fun u v h ↦ by
    unfold nucMatARem nucMatA skewRank2Mat nucPsi nucPhi
    by_cases hu : inGrid18 u
    · simp [hu, show ¬inGrid18 v from fun hv ↦ h ⟨hu, hv⟩]
    · simp [hu]
  have hrew_uv : ∀ u v : Fin (2 ^ 18),
      ‖nucMatARem W c l u v‖ ^ 2 =
        if inGrid18 u then
          (if inGrid18 v then ‖nucMatARem W c l u v‖ ^ 2 else 0)
        else 0 := fun u v ↦ by
    by_cases hu : inGrid18 u
    · by_cases hv : inGrid18 v
      · simp [hu, hv]
      · simp [hu, hv, hzero_uv u v (fun h ↦ hv h.2)]
    · simp [hu, hzero_uv u v (fun h ↦ hu h.1)]
  rw [Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ hrew_uv u v]
  have hv_sum : ∀ u : Fin (2 ^ 18),
      (∑ v : Fin (2 ^ 18), if inGrid18 u then
        (if inGrid18 v then ‖nucMatARem W c l u v‖ ^ 2 else 0) else 0) =
      if inGrid18 u then
        ∑ g2 : Grid63_3,
          ‖nucMatARem W c l u (u18ToGrid64_3.symm (succGrid63_3 g2))‖ ^ 2
      else 0 := fun u ↦ by
    by_cases hu : inGrid18 u
    · simp only [hu, ↓reduceIte]; exact sum_u18_inGrid18 _
    · simp [hu]
  rw [Finset.sum_congr rfl fun u _ ↦ hv_sum u, sum_u18_inGrid18, ← Fintype.sum_prod_type'
    (fun g1 g2 : Grid63_3 ↦
      ‖nucMatARem W c l (u18ToGrid64_3.symm (succGrid63_3 g1))
        (u18ToGrid64_3.symm (succGrid63_3 g2))‖ ^ 2)]
  have hleaf : ∀ x : PairGrid63_3,
      ‖nucMatARem W c l (u18ToGrid64_3.symm (succGrid63_3 x.1))
          (u18ToGrid64_3.symm (succGrid63_3 x.2))‖ ^ 2 =
        (2 / cellSide) ^ 2 *
          (((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) ^ 2 * remKerSqP x) := by
    intro x
    set u := u18ToGrid64_3.symm (succGrid63_3 x.1)
    set v := u18ToGrid64_3.symm (succGrid63_3 x.2)
    have higx : inGrid18 u := inGrid18_succGrid63_3 x.1
    have higy : inGrid18 v := inGrid18_succGrid63_3 x.2
    set ν := pOf18 u - pOf18 v
    have hν_eq := pOf18_succGrid_sub x.1 x.2
    have hν0_eq : ν 0 = d0P x := congrFun hν_eq 0
    have hν1_eq : ν 1 = d1P x := congrFun hν_eq 1
    have hν2_eq : ν 2 = d2P x := congrFun hν_eq 2
    have hns : normSqInt ν = r2P x := by
      unfold normSqInt r2P
      change (ν 0).natAbs ^ 2 + (ν 1).natAbs ^ 2 + (ν 2).natAbs ^ 2 = _
      rw [hν0_eq, hν1_eq, hν2_eq]
    have hphi_prod : nucPhi u * nucPhi v = bell3P x := by
      dsimp only [u, v]
      rw [nucPhi_succGrid63_3 x.1, nucPhi_succGrid63_3 x.2]
      unfold bell3P; ring
    have hpsi_diff : nucPsi W c l u * nucPhi v - nucPhi u * nucPsi W c l v =
        (2 / cellSide) * c0Dip *
          ((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) * bell3P x := by
      have hp_sub : (∑ w : Fin 3, (pOf18 u w : ℝ) * δ w) - (∑ w : Fin 3, (pOf18 v w : ℝ) * δ w) =
          (d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2 := by
        rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hν0_eq, ← hν1_eq, ← hν2_eq]
        dsimp only [ν, Pi.sub_apply]; push_cast; ring
      calc nucPsi W c l u * nucPhi v - nucPhi u * nucPsi W c l v
          = (2 / cellSide) * c0Dip *
              ((∑ w : Fin 3, (pOf18 u w : ℝ) * δ w) - (∑ w : Fin 3, (pOf18 v w : ℝ) * δ w)) *
              (nucPhi u * nucPhi v) := by unfold nucPsi; ring
        _ = _ := by rw [hp_sub, hphi_prod]
    unfold nucMatARem nucMatA skewRank2Mat
    simp only [Matrix.sub_apply, Matrix.of_apply, higx, higy, and_self, ↓reduceIte, hpsi_diff]
    by_cases hν0 : ν = 0
    · have hr0 : r2P x = 0 := by rw [← hns, hν0]; simp [normSqInt]
      have hd0z : d0P x = 0 := by rw [← hν0_eq, hν0]; rfl
      have hd1z : d1P x = 0 := by rw [← hν1_eq, hν0]; rfl
      have hd2z : d2P x = 0 := by rw [← hν2_eq, hν0]; rfl
      change ‖((-(coulombKernel ν * nucTheta W c l ν) : ℝ) : ℂ) * Complex.I - _‖ ^ 2 = _
      rw [hν0, coulombKernel_zero, hd0z, hd1z, hd2z]
      unfold remKerSqP; simp [hr0]
    · have hr_ne : r2P x ≠ 0 := by
        intro hz
        have hns0 : normSqInt ν = 0 := by rw [hns, hz]
        unfold normSqInt at hns0
        rcases nat_three_sq_eq_zero hns0 with ⟨hz0, hz1, hz2⟩
        apply hν0; ext w; fin_cases w
        · exact Int.natAbs_eq_zero.mp hz0
        · exact Int.natAbs_eq_zero.mp hz1
        · exact Int.natAbs_eq_zero.mp hz2
      have hcoul : -(coulombKernel ν * nucTheta W c l ν) =
          (2 / cellSide) * (1 / (r2P x : ℝ)) *
            ((d0P x : ℝ) * δ 0 + (d1P x : ℝ) * δ 1 + (d2P x : ℝ) * δ 2) := by
        rw [coulombKernel_eq_of_ne_zero hν0, hns]
        unfold nucTheta
        rw [Fin.sum_univ_three]
        change -((1 : ℝ) / (π * cellSide) * (1 / (r2P x : ℝ)) *
          -(2 * π * ((ν 0 : ℝ) * δ 0 + (ν 1 : ℝ) * δ 1 + (ν 2 : ℝ) * δ 2))) = _
        rw [hν0_eq, hν1_eq, hν2_eq]
        have hrR_ne : (r2P x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr_ne
        field_simp [Real.pi_ne_zero, hcell_ne, hrR_ne]
      change ‖((-(coulombKernel ν * nucTheta W c l ν) : ℝ) : ℂ) * Complex.I - _‖ ^ 2 = _
      rw [hcoul]
      have hsub_c : ∀ a b : ℝ, ((a : ℂ) * Complex.I - (b : ℂ) * Complex.I) =
          (((a - b : ℝ) : ℂ) * Complex.I) := fun a b ↦ by push_cast; ring
      rw [hsub_c, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      unfold remKerSqP; simp only [hr_ne, ↓reduceIte]; ring
  simp_rw [hleaf, ← Finset.mul_sum]
  rw [cubic_sym_remKerSqP δ]
  set dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
  have hδ_sq : ∀ w : Fin 3, δ w ^ 2 ≤ dmax ^ 2 := fun w ↦ by
    have habs : |δ w| ≤ dmax := abs_nucDelta_le W c l w
    have hd0 : 0 ≤ dmax := by dsimp [dmax]; positivity
    nlinarith [abs_le.mp habs]
  have havg_le : (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3 ≤ dmax ^ 2 := by
    linarith [hδ_sq 0, hδ_sq 1, hδ_sq 2]
  have htwo_div_le : (2 / cellSide) ^ 2 ≤ (2 / lLoRat) ^ 2 := by
    have h1 : 2 / cellSide ≤ 2 / lLoRat :=
      div_le_div_of_nonneg_left zero_le_two lLoRat_pos lLoRat_le_cellSide
    exact pow_le_pow_left₀ (div_nonneg zero_le_two cellSide_pos.le) h1 2
  have hS_nn : 0 ≤ ∑ x : PairGrid63_3, (r2P x : ℝ) * remKerSqP x :=
    Finset.sum_nonneg fun x _ ↦ by
      unfold remKerSqP; split_ifs <;> positivity
  have havg_nn : 0 ≤ (δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3 :=
    div_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) (by norm_num)
  have hinner : ((δ 0 ^ 2 + δ 1 ^ 2 + δ 2 ^ 2) / 3) *
        (∑ x : PairGrid63_3, (r2P x : ℝ) * remKerSqP x) ≤ dmax ^ 2 * remSumCapRat :=
    mul_le_mul havg_le sum_r2P_remKerSqP_le hS_nn (sq_nonneg dmax)
  have hprod1 := mul_le_mul htwo_div_le hinner (mul_nonneg havg_nn hS_nn) (sq_nonneg _)
  have hrt_sq : ((2 / lLoRat) * dmax * √remSumCapRat) ^ 2 =
      (2 / lLoRat) ^ 2 * (dmax ^ 2 * remSumCapRat) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by unfold remSumCapRat; norm_num)]; ring
  rw [hrt_sq]; exact hprod1

/-- Compact rational upper cap `58539000278793586732 / 10^12` on `12 * c0Dip^2 * M2 * M0^5`. -/
noncomputable def dipProdCapRat : ℝ := (58539000278793586732 : ℝ) / 1000000000000


theorem norm_proj_uEnManyBody_truncWCfg_sub_le_opt {W : ℕ} (hW20 : 20 ≤ W)
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    let dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
    let FRem : ℝ := (2 / lLoRat) * dmax * √remSumCapRat
    let FDip : ℝ := (2 / lLoRat) * dmax * √dipProdCapRat
    let FB : ℝ := (2 ^ 18 : ℝ) * ((12 * (315 / 100) / lLoRat) * dmax ^ 2)
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg W c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤
      216 * (√218 * FRem) + 216 * FDip + 216 * (218 * FB) := by
  intro dmax FRem FDip FB
  have hFRem0 : 0 ≤ FRem := by
    dsimp [FRem, dmax];
    have :=
      lLoRat_pos; unfold remSumCapRat; positivity
  have hFDip0 : 0 ≤ FDip := by
    dsimp [FDip, dmax];
    have :=
      lLoRat_pos; unfold dipProdCapRat; positivity
  have hFB0 : 0 ≤ FB := by dsimp [FB, dmax]; have := lLoRat_pos; positivity
  set Fφ : ℝ := √((1228043870767229868495 : ℝ) ^ 3)
  set Fψ : ℝ := (2 / lLoRat) * c0Dip * dmax *
    √(3 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2)
  have hFφ0 : 0 ≤ Fφ := Real.sqrt_nonneg _
  have hFψ0 : 0 ≤ Fψ := by dsimp [Fψ, dmax]; have := lLoRat_pos; unfold c0Dip; positivity
  have hφ_sq : (∑ u : Fin (2 ^ 18), (nucPhi u) ^ 2) ≤ Fφ ^ 2 := by
    rw [sum_nucPhi_sq_eq]; dsimp [Fφ]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1228043870767229868495 : ℝ) ^ 3)]
  have hDip_num : 2 * Fφ * Fψ ≤ FDip := by
    have hsq : (2 * Fφ * Fψ) ^ 2 ≤ FDip ^ 2 := by
      have hLHS : (2 * Fφ * Fψ) ^ 2 =
          ((2 / lLoRat) * dmax) ^ 2 *
            (12 * c0Dip ^ 2 * (283174258570147953487680 : ℝ) *
              (1228043870767229868495 : ℝ) ^ 5) := by
        dsimp [Fφ, Fψ]
        rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1228043870767229868495 : ℝ) ^ 3),
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤
            3 * (283174258570147953487680 : ℝ) * (1228043870767229868495 : ℝ) ^ 2)]
        ring
      have hRHS : FDip ^ 2 = ((2 / lLoRat) * dmax) ^ 2 * dipProdCapRat := by
        dsimp [FDip]
        rw [mul_pow, Real.sq_sqrt (by unfold dipProdCapRat; norm_num)]
      have hcap : 12 * c0Dip ^ 2 * (283174258570147953487680 : ℝ) *
          (1228043870767229868495 : ℝ) ^ 5 ≤ dipProdCapRat := by
        unfold c0Dip dipProdCapRat; norm_num
      rw [hLHS, hRHS]
      exact mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
    exact (mul_self_le_mul_self_iff (by positivity) hFDip0).mpr (by simpa [sq] using hsq)
  set P := fermionicProjector spinUp
  set V := oneElecNucDiagExact c
  have hP1 : ‖P‖ ≤ 1 := norm_fermionicProjector_le_one spinUp
  rw [proj_uEnManyBody_truncWCfg_sub_eq W c spinUp]
  have hA_split : ∀ l : Fin 216,
      P * (∑ i : Fin numElectrons,
        (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P =
      P * (∑ i : Fin numElectrons,
        (rEl_sp i).embedMatrix ((V l).1 * nucMatARem W c l * (V l).1ᴴ)) * P +
      P * (∑ i : Fin numElectrons,
        (rEl_sp i).embedMatrix ((V l).1 * skewRank2Mat nucPhi (nucPsi W c l) * (V l).1ᴴ)) * P :=
    fun l ↦ by
      have hm : nucMatA W c l = nucMatARem W c l + skewRank2Mat nucPhi (nucPsi W c l) :=
        (sub_add_cancel (nucMatA W c l) (skewRank2Mat nucPhi (nucPsi W c l))).symm
      rw [hm, Matrix.mul_add, Matrix.add_mul,
        Finset.sum_congr rfl fun i _ ↦ (rEl_sp i).embedMatrix_add _ _,
        Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]
  have hDip_l : ∀ l : Fin 216,
      ‖P * (∑ i : Fin numElectrons,
        (rEl_sp i).embedMatrix ((V l).1 * skewRank2Mat nucPhi (nucPsi W c l) * (V l).1ᴴ)) * P‖ ≤
        FDip := fun l ↦
    (norm_proj_sandwich_embed_skewRank2_le nucPhi (nucPsi W c l) (V l)
      hFφ0 hFψ0 hφ_sq (sum_nucPsi_sq_le W c l) spinUp).trans hDip_num
  have hA_sum :
      ‖∑ l : Fin 216, P * (∑ i : Fin numElectrons,
          (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P‖ ≤
        216 * (√218 * FRem) + 216 * FDip := by
    calc ‖∑ l : Fin 216, P * (∑ i : Fin numElectrons,
            (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P‖
        ≤ ∑ l : Fin 216,
            ‖P * (∑ i : Fin numElectrons,
              (rEl_sp i).embedMatrix ((V l).1 * nucMatA W c l * (V l).1ᴴ)) * P‖ :=
          norm_op_sum_le _ _
      _ ≤ ∑ _l : Fin 216, (√218 * FRem + FDip) :=
          Finset.sum_le_sum fun l _ ↦ by
            rw [hA_split l]
            exact (norm_op_add_le _ _).trans (add_le_add
              (norm_proj_sandwich_embed_chiral_le (nucMatARem W c l)
                (nucMatARem_isHermitian W c l) (nucMatARem_imag W c l) (V l) hFRem0
                (frob_nucMatARem_le W c l) spinUp)
              (hDip_l l))
      _ = 216 * (√218 * FRem) + 216 * FDip := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hB_sum :
      ‖∑ l : Fin 216, ∑ i : Fin numElectrons,
          P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ ≤
        216 * (218 * FB) := by
    have hper : ∀ (l : Fin 216) (i : Fin numElectrons),
        ‖P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ ≤ FB := fun l i ↦
      norm_proj_mul_op_mul_proj_le P _ hP1 hFB0
        (norm_embed_hermitian_le_frob (nucMatB W c l) (nucMatB_isHermitian W c l)
          (V l) hFB0 (frob_nucMatB_le hW20 c l) i)
    calc ‖∑ l : Fin 216, ∑ i : Fin numElectrons,
            P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖
        ≤ ∑ l : Fin 216, ∑ i : Fin numElectrons,
            ‖P * (rEl_sp i).embedMatrix ((V l).1 * nucMatB W c l * (V l).1ᴴ) * P‖ :=
          (norm_op_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_op_sum_le _ _)
      _ ≤ ∑ _l : Fin 216, ∑ _i : Fin numElectrons, FB :=
          Finset.sum_le_sum fun l _ ↦ Finset.sum_le_sum fun i _ ↦ hper l i
      _ = 216 * (218 * FB) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons,
            nsmul_eq_mul]; ring
  exact ((norm_op_add_le _ _).trans (add_le_add hA_sum hB_sum)).trans_eq (by ring)

attribute [irreducible] skewRank2Mat nucPhi nucPsi nucMatARem

/-! ## Section 3: Per-Width Tightened `Slot 2` & Turnkey `Pos512` Endpoints (`W ∈ {28..36}`) -/

private theorem norm_proj_uEnManyBody_truncWCfg_sub_le_rat
    {W : ℕ} (hW20 : 20 ≤ W) {totCap : ℝ}
    (htot : ((6715552358 * 2 ^ 29 : ℝ) / 1000000000000) * ((1 / 2 : ℝ) / (2 ^ W : ℝ)) +
        216 * (218 * ((2 ^ 18 : ℝ) *
          ((12 * (315 / 100) / lLoRat) * ((1 / 2 : ℝ) / (2 ^ W : ℝ)) ^ 2))) ≤ totCap)
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg W c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ totCap := by
  refine (norm_proj_uEnManyBody_truncWCfg_sub_le_opt hW20 c spinUp).trans ?_
  set dmax : ℝ := (1 / 2 : ℝ) / (2 ^ W : ℝ)
  have hdmax0 : 0 ≤ dmax := by
    dsimp [dmax]
    positivity
  have hRemC_sq : (216 * (√218 * ((2 / lLoRat) * √remSumCapRat))) ^ 2 ≤
      ((6256970316 * 2 ^ 29 : ℝ) / 1000000000000) ^ 2 := by
    have hrew : (216 * (√218 * ((2 / lLoRat) * √remSumCapRat))) ^ 2 =
        216 ^ 2 * 218 * (2 / lLoRat) ^ 2 * remSumCapRat := by
      rw [mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 218),
        Real.sq_sqrt (by unfold remSumCapRat; norm_num)]
      ring
    rw [hrew]
    dsimp [lLoRat, remSumCapRat]
    norm_num
  have hRemC_le : 216 * (√218 * ((2 / lLoRat) * √remSumCapRat)) ≤
      (6256970316 * 2 ^ 29 : ℝ) / 1000000000000 := by
    have hnn : 0 ≤ 216 * (√218 * ((2 / lLoRat) * √remSumCapRat)) := by
      have := lLoRat_pos
      unfold remSumCapRat
      positivity
    exact (mul_self_le_mul_self_iff hnn (by norm_num)).mpr (by simpa [sq] using hRemC_sq)
  have hDipC_sq : (216 * ((2 / lLoRat) * √dipProdCapRat)) ^ 2 ≤
      ((458582042 * 2 ^ 29 : ℝ) / 1000000000000) ^ 2 := by
    have hrew : (216 * ((2 / lLoRat) * √dipProdCapRat)) ^ 2 =
        216 ^ 2 * (2 / lLoRat) ^ 2 * dipProdCapRat := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by unfold dipProdCapRat; norm_num)]
      ring
    rw [hrew]
    dsimp [lLoRat, dipProdCapRat]
    norm_num
  have hDipC_le : 216 * ((2 / lLoRat) * √dipProdCapRat) ≤
      (458582042 * 2 ^ 29 : ℝ) / 1000000000000 := by
    have hnn : 0 ≤ 216 * ((2 / lLoRat) * √dipProdCapRat) := by
      have := lLoRat_pos
      unfold dipProdCapRat
      positivity
    exact (mul_self_le_mul_self_iff hnn (by norm_num)).mpr (by simpa [sq] using hDipC_sq)
  have hlin_eq :
      216 * (√218 * ((2 / lLoRat) * dmax * √remSumCapRat)) +
        216 * ((2 / lLoRat) * dmax * √dipProdCapRat) =
      (216 * (√218 * ((2 / lLoRat) * √remSumCapRat)) +
        216 * ((2 / lLoRat) * √dipProdCapRat)) * dmax := by
    ring
  have hlin_le :
      (216 * (√218 * ((2 / lLoRat) * √remSumCapRat)) +
        216 * ((2 / lLoRat) * √dipProdCapRat)) * dmax ≤
      ((6715552358 * 2 ^ 29 : ℝ) / 1000000000000) * dmax :=
    mul_le_mul_of_nonneg_right (by linarith) hdmax0
  linarith

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 28` (`6679762` nHa). -/
noncomputable def eps2_trunc28_chiral_opt : ℝ := (6679762 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc28_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 28 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (6715673 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc28_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 28 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (6741373 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 28 c) c
    (norm_proj_uEnManyBody_trunc28_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 29` (`3352702` nHa). -/
noncomputable def eps2_trunc29_chiral_opt : ℝ := (3352702 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc29_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 29 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (3357807 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc29_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 29 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (3383507 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 29 c) c
    (norm_proj_uEnManyBody_trunc29_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 30` (`1689194` nHa). -/
noncomputable def eps2_trunc30_chiral_opt : ℝ := (1689194 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc30_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 30 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (1678896 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc30_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 30 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (1704596 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 30 c) c
    (norm_proj_uEnManyBody_trunc30_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 31` (`857445` nHa). -/
noncomputable def eps2_trunc31_chiral_opt : ℝ := (857445 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc31_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 31 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (839446 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc31_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 31 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (865146 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 31 c) c
    (norm_proj_uEnManyBody_trunc31_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 32` (`441573` nHa). -/
noncomputable def eps2_trunc32_chiral_opt : ℝ := (441573 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc32_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 32 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (419723 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc32_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 32 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (445423 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 32 c) c
    (norm_proj_uEnManyBody_trunc32_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 33` (`233637` nHa). -/
noncomputable def eps2_trunc33_chiral_opt : ℝ := (233637 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc33_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 33 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (209862 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc33_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 33 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (235562 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 33 c) c
    (norm_proj_uEnManyBody_trunc33_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 34` (`129669` nHa). -/
noncomputable def eps2_trunc34_chiral_opt : ℝ := (129669 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc34_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 34 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (104931 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc34_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 34 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (130631 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 34 c) c
    (norm_proj_uEnManyBody_trunc34_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 35` (`77685` nHa). -/
noncomputable def eps2_trunc35_chiral_opt : ℝ := (77685 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc35_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 35 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (52466 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc35_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 35 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (78166 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 35 c) c
    (norm_proj_uEnManyBody_trunc35_sub_le_opt c) (by norm_num) spinUp

/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap `eps2` at `W = 36` (`51693` nHa). -/
noncomputable def eps2_trunc36_chiral_opt : ℝ := (51693 : ℝ) / 1000000000

theorem norm_proj_uEnManyBody_trunc36_sub_le_opt
    (c : Configuration) (spinUp : Finset (Fin numElectrons)) :
    ‖fermionicProjector spinUp * (uEnManyBody (truncWCfg 36 c) - uEnManyBody c) *
      fermionicProjector spinUp‖ ≤ (26233 : ℝ) / 1000000000 :=
  norm_proj_uEnManyBody_truncWCfg_sub_le_rat (by omega)
    (by dsimp [lLoRat]; norm_num) c spinUp

theorem bModSlot248_trunc36_shifted_err_le_opt (c : Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E2only : Fin 6 → ℝ := fun q ↦ if q = 2 then pos24Slot2E2Const else 0
    ‖fermionicProjector spinUp * (bModSlot248 (truncWCfg 36 c) - sixChannelShifted c E2only 2) *
      fermionicProjector spinUp‖ ≤ (51933 : ℝ) / 1000000000 :=
  bModSlot248_trunc_shifted_err_le_of_uEn (truncWCfg 36 c) c
    (norm_proj_uEnManyBody_trunc36_sub_le_opt c) (by norm_num) spinUp


attribute [irreducible] fSexticBellZ c0Dip remSumCapRat dipProdCapRat
/-- Optimized dipole-subtracted `Slot 2` intrinsic error cap on `truncChiralPos512OfW W`. -/
noncomputable def eps2ChiralPos512OptOfW (W : ℕ) : ℝ :=
  if W = 36 then eps2_trunc36_chiral_opt
  else if W = 34 then eps2_trunc34_chiral_opt
  else if W = 35 then eps2_trunc35_chiral_opt
  else if W = 29 then eps2_trunc29_chiral_opt
  else if W = 30 then eps2_trunc30_chiral_opt
  else if W = 31 then eps2_trunc31_chiral_opt
  else if W = 32 then eps2_trunc32_chiral_opt
  else if W = 33 then eps2_trunc33_chiral_opt
  else eps2_trunc28_chiral_opt

/-- Optimized dipole-subtracted non-`S3` intrinsic error cap in nano-Hartree (`W ∈ {28..36}`). -/
def nonS3ChiralPos512OptNano (W : ℕ) : ℕ :=
  if W = 36 then 94141
  else if W = 34 then 172839
  else if W = 35 then 120374
  else if W = 29 then 3425715
  else if W = 30 then 1746804
  else if W = 31 then 907354
  else if W = 32 then 487631
  else if W = 33 then 277770
  else 6783581

theorem tierBB2IdMod4_truncChiralPos512OfW_opt_intrinsic_agr (W : ℕ)
    (cfg : Configuration) (spinUp : Finset (Fin numElectrons))
    (E_sp : Fin 6 → ℝ) (hEsp2 : E_sp 2 = pos24Slot2E2Const)
    (hEsp5 : E_sp 5 = pos24Slot2E2Const / 108) :
    AgreesOnFermionicSector spinUp
      (gridProjector *
        ((mergedPosSlot2WeightGen ((108 : ℝ) / 109) (fun _ ↦ pos80Slot2Scale) cfg : ℂ) •
          (smToTwosSysUnitary.1 *
            tierBB2IdMod4 (truncChiralPos512OfW W cfg) * smToTwosSysUnitary.1)) *
        gridProjector)
      (sixChannelShifted cfg E_sp 2 + sixChannelShifted cfg E_sp 5)
      ((109 / 108 : ℝ) * eps2ChiralPos512OptOfW W) := by
  rcases eq_or_ne W 36 with rfl | h36
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 36)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc36_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc36_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 34 with rfl | h34
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 34)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc34_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc34_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 35 with rfl | h35
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 35)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc35_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc35_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 29 with rfl | h29
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 29)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc29_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc29_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 30 with rfl | h30
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 30)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc30_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc30_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 31 with rfl | h31
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 31)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc31_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc31_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 32 with rfl | h32
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 32)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc32_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc32_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  rcases eq_or_ne W 33 with rfl | h33
  · exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 33)
      (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc33_shifted_err_le_opt
      (by unfold eps2ChiralPos512OptOfW eps2_trunc33_chiral_opt; norm_num) cfg spinUp E_sp hEsp2
        hEsp5
  have hT : truncChiralPos512OfW W = truncWCfg 28 := by
    unfold truncChiralPos512OfW truncChiralChiralOfW truncChiralOfW
    simp [h36, h34, h35, h29, h30, h31, h32, h33]
  have hE : eps2ChiralPos512OptOfW W = eps2_trunc28_chiral_opt := by
    unfold eps2ChiralPos512OptOfW; simp [h36, h34, h35, h29, h30, h31, h32, h33]
  rw [hT, hE]
  exact tierBB2IdMod4_trunc_intrinsic_agrees_tight (truncWCfg 28)
    (truncWCfg_cfgProjZ512 (by omega)) (fun _ ↦ rfl) bModSlot248_trunc28_shifted_err_le_opt
    (by unfold eps2_trunc28_chiral_opt; norm_num) cfg spinUp E_sp hEsp2 hEsp5

theorem eps2ChiralPos512Opt_nonS3_base_le (W : ℕ) :
    (6 : ℝ) / 10 ^ 7 + (109 / 108 : ℝ) * eps2ChiralPos512OptOfW W + eps4_q30_tight ≤
      ((nonS3ChiralPos512OptNano W - 29000 : ℕ) : ℝ) / 1000000000 := by
  unfold eps4_q30_tight
  by_cases h : W = 36 ∨ W = 34 ∨ W = 35 ∨ W = 29 ∨ W = 30 ∨ W = 31 ∨ W = 32 ∨ W = 33
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold nonS3ChiralPos512OptNano eps2ChiralPos512OptOfW
        eps2_trunc36_chiral_opt eps2_trunc34_chiral_opt eps2_trunc35_chiral_opt
        eps2_trunc29_chiral_opt eps2_trunc30_chiral_opt eps2_trunc31_chiral_opt
        eps2_trunc32_chiral_opt eps2_trunc33_chiral_opt
      simp only [↓reduceIte]
      norm_num
  · push Not at h
    rcases h with ⟨h36, h34, h35, h29, h30, h31, h32, h33⟩
    have hE : eps2ChiralPos512OptOfW W = eps2_trunc28_chiral_opt := by
      unfold eps2ChiralPos512OptOfW
      simp [h36, h34, h35, h29, h30, h31, h32, h33]
    have hN : nonS3ChiralPos512OptNano W = 6783581 := by
      unfold nonS3ChiralPos512OptNano
      simp [h36, h34, h35, h29, h30, h31, h32, h33]
    rw [hE, hN]
    unfold eps2_trunc28_chiral_opt
    norm_num
end NucMatADipSexticCap
end NucMatADipSexticCap
end QuantumComputation.Specs.StoppingPowerSolution
end
