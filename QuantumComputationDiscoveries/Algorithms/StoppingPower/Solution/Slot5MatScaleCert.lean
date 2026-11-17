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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosCompactHead123
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModSlot5MatrixAndScaleCert
set_option exponentiation.threshold 8192
@[expose] public section
namespace Slot5MatrixAndScaleCert
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open ModWrapCoarse8PureMomentum
open TwosCompAndWire0Cancel
open KaratsubaQft64Matrix (twosComp6Int)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
attribute [local irreducible] box3D nonzeroBox3D
def signBit3 (s3 : Fin 8) (w : Fin 3) : ℕ := (s3.val / 2 ^ w.val) % 2
theorem signBit3_le_one (s3 : Fin 8) (w : Fin 3) : signBit3 s3 w ≤ 1 := by
  unfold signBit3
  omega
theorem signBit3_mk {b0 b1 b2 : ℕ} (h0 : b0 ≤ 1) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (w : Fin 3) :
    signBit3 ⟨b0 + 2 * b1 + 4 * b2, by omega⟩ w =
      match w with | 0 => b0 | 1 => b1 | 2 => b2 := by
  fin_cases w <;> simp [signBit3] <;> omega
theorem s3_eq_sum_signBit3 (s3 : Fin 8) : s3.val = signBit3 s3 0 + 2 * signBit3 s3 1 + 4 *
    signBit3 s3 2 := by
  have := s3.isLt
  simp only [signBit3, Fin.val_zero, Fin.val_one, Fin.val_two]; omega
noncomputable def signedPermMatrix {D : ℕ} (π_inv : Equiv.Perm (Fin D)) (ε : Fin D → ℝ) :
    Operator D := Matrix.diagonal (fun x ↦ (ε x : ℂ)) * (fwdPermUnitary π_inv).1
theorem signedPermMatrix_apply {D : ℕ} (π_inv : Equiv.Perm (Fin D)) (ε : Fin D → ℝ)
    (i j : Fin D) : signedPermMatrix π_inv ε i j = if π_inv j = i then (ε i : ℂ) else 0 := by
  rw [signedPermMatrix, Matrix.diagonal_mul, fwdPermUnitary_apply]
  by_cases h : π_inv j = i <;> simp [h]
noncomputable def signedInvolutionUnitary {D : ℕ} (π_inv : Equiv.Perm (Fin D)) (ε : Fin D → ℝ)
    (hInv : ∀ x, π_inv (π_inv x) = x) (hSymm : ∀ x, ε (π_inv x) = ε x) (hSq : ∀ x,
      ε x * ε x = 1) : Unitary D :=
  ⟨signedPermMatrix π_inv ε, by
    let _ := hSymm
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]; ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (π_inv i)
      (fun k _ hk ↦ by
        have hki : π_inv k ≠ i := fun h ↦ hk ((hInv k).symm.trans (congrArg π_inv h))
        rw [signedPermMatrix_apply, ite_eq_right hki, zero_mul])
      (fun hm ↦ absurd (Finset.mem_univ _) hm)]
    rw [Matrix.conjTranspose_apply, signedPermMatrix_apply, signedPermMatrix_apply,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp only [hInv i, ite_true, Complex.star_def, Complex.conj_ofReal]
      exact_mod_cast hSq i
    · simp [hInv i, hij]⟩
private noncomputable def cosLowerPoly18 (t : ℝ) : ℝ := cosUpperPoly12 t -
    t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 - t ^ 18 / 6402373705728000
private noncomputable def cosUpperPoly20 (t : ℝ) : ℝ :=
    cosLowerPoly18 t + t ^ 20 / 0x21c3677c82b40000
private lemma deriv_le_step {f g f' g' : ℝ → ℝ} (h0 : g 0 - f 0 = 0) (hf : ∀ x,
    HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hd : ∀ z, 0 ≤ z → f' z ≤ g' z) {z : ℝ} (hz : 0 ≤ z) : f z ≤ g z :=
  sub_nonneg.mp (nonneg_of_deriv_nonneg (fun y ↦ g y - f y) hz h0
    (fun x ↦ hasDerivAt_fn_sub (hg x) (hf x)) (fun x hx _ ↦ sub_nonneg.mpr (hd x hx)))
private lemma pow_div_deriv {k : ℕ} {a b : ℝ} (hab : ((k + 1 : ℕ) : ℝ) / a = 1 /
    b) (x : ℝ) : HasDerivAt (fun y : ℝ ↦ y ^ (k + 1) / a) (x ^ k / b) x :=
  ((hasDerivAt_pow (k + 1) x).div_const a).congr_deriv (by
    rw [Nat.add_sub_cancel, mul_div_right_comm, hab, one_div, inv_mul_eq_div])
private lemma cos_step4 {S₀ P : ℝ → ℝ} (k : ℕ) (c0 c1 c2 c3 c4 : ℝ)
    (hdS : ∀ x, HasDerivAt S₀ (P x - x ^ k / c0) x) (hdP : ∀ x, HasDerivAt P (-S₀ x) x)
    (hS0 : S₀ 0 = 0) (hP0 : P 0 = 1) (hP : ∀ z, 0 ≤ z → Real.cos z ≤ P z)
    (hc1 : ((k + 1 : ℕ) : ℝ) / c1 = 1 / c0) (hc2 : ((k + 2 : ℕ) : ℝ) / c2 = 1 / c1)
    (hc3 : ((k + 3 : ℕ) : ℝ) / c3 = 1 / c2) (hc4 : ((k + 4 : ℕ) : ℝ) / c4 = 1 / c3) :
    let P₂ := fun y ↦ P y - y ^ (k + 2) / c2
    let S₃ := fun y ↦ S₀ y + y ^ (k + 1) / c1 - y ^ (k + 3) / c3
    let P₄ := fun y ↦ P₂ y + y ^ (k + 4) / c4
    (∀ z, 0 ≤ z → P₂ z ≤ Real.cos z) ∧ (∀ z, 0 ≤ z → Real.cos z ≤ P₄ z) ∧
      (∀ x, HasDerivAt S₃ (P₄ x - x ^ (k + 4) / c4) x) ∧ (∀ x, HasDerivAt P₄ (-S₃ x) x) := by
  intro P₂ S₃ P₄; let S₁ : ℝ → ℝ := fun y ↦ S₀ y + y ^ (k + 1) / c1
  have hdS₁ (x : ℝ) : HasDerivAt S₁ (P x) x :=
    (hasDerivAt_fn_add (hdS x) (pow_div_deriv hc1 x)).congr_deriv (sub_add_cancel _ _)
  have hdP₂ (x : ℝ) : HasDerivAt P₂ (-S₁ x) x :=
    (hasDerivAt_fn_sub (hdP x) (pow_div_deriv hc2 x)).congr_deriv (by dsimp only [S₁]; ring)
  have hdS₃ (x : ℝ) : HasDerivAt S₃ (P₂ x) x := hasDerivAt_fn_sub (hdS₁ x) (pow_div_deriv hc3 x)
  have hdP₄ (x : ℝ) : HasDerivAt P₄ (-S₃ x) x :=
    (hasDerivAt_fn_add (hdP₂ x) (pow_div_deriv hc4 x)).congr_deriv
      (by dsimp only [S₃, S₁]; ring)
  have hS₁ {z : ℝ} (hz : 0 ≤ z) : Real.sin z ≤ S₁ z :=
    deriv_le_step (by simp [S₁, hS0]) Real.hasDerivAt_sin hdS₁ hP hz
  have hP₂ {z : ℝ} (hz : 0 ≤ z) : P₂ z ≤ Real.cos z :=
    deriv_le_step (by simp [P₂, hP0]) hdP₂ Real.hasDerivAt_cos
      (fun _ hx ↦ neg_le_neg (hS₁ hx)) hz
  have hS₃ {z : ℝ} (hz : 0 ≤ z) : S₃ z ≤ Real.sin z :=
    deriv_le_step (by simp [S₃, hS0]) hdS₃ Real.hasDerivAt_sin (fun _ ↦ hP₂) hz
  exact ⟨fun _ ↦ hP₂, fun _ hz ↦ deriv_le_step (by simp [P₄, P₂, hP0])
    Real.hasDerivAt_cos hdP₄ (fun _ hx ↦ neg_le_neg (hS₃ hx)) hz,
    fun x ↦ (hdS₃ x).congr_deriv (by dsimp only [P₄]; ring), hdP₄⟩
private theorem cosLowerPoly18_le_cos_and_cos_le_cosUpperPoly20 {t : ℝ} (ht : 0 ≤
    t) : cosLowerPoly18 t ≤ Real.cos t ∧ Real.cos t ≤ cosUpperPoly20 t := by
  let S11 : ℝ → ℝ := fun y ↦
    y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 + y ^ 9 / 362880 - y ^ 11 / 39916800
  have hd_S11 (x : ℝ) : HasDerivAt S11 (cosUpperPoly12 x - x ^ 12 / 479001600) x :=
    (hasDerivAt_fn_sub (hasDerivAt_fn_add (hasDerivAt_fn_sub
      (hasDerivAt_fn_add (hasDerivAt_fn_sub (hasDerivAt_id' x)
        ((hasDerivAt_pow 3 x).div_const 6)) ((hasDerivAt_pow 5 x).div_const 120))
      ((hasDerivAt_pow 7 x).div_const 5040)) ((hasDerivAt_pow 9 x).div_const 362880))
      ((hasDerivAt_pow 11 x).div_const 39916800)).congr_deriv (by
        unfold cosUpperPoly12 cosLowerPoly10; push_cast; ring)
  have hd_P12 (x : ℝ) : HasDerivAt cosUpperPoly12 (-S11 x) x :=
    (hasDerivAt_fn_add (hasDerivAt_fn_sub (hasDerivAt_fn_add (hasDerivAt_fn_sub
      (hasDerivAt_fn_add (hasDerivAt_fn_sub (hasDerivAt_const x (1 : ℝ))
        ((hasDerivAt_pow 2 x).div_const 2)) ((hasDerivAt_pow 4 x).div_const 24))
      ((hasDerivAt_pow 6 x).div_const 720)) ((hasDerivAt_pow 8 x).div_const 40320))
      ((hasDerivAt_pow 10 x).div_const 3628800))
      ((hasDerivAt_pow 12 x).div_const 479001600)).congr_deriv (by dsimp only [S11]; ring)
  rcases cos_step4 12 479001600 6227020800 87178291200 1307674368000 20922789888000
      hd_S11 hd_P12 (by norm_num [S11]) (by norm_num [cosUpperPoly12, cosLowerPoly10])
      (fun _ hz ↦ (cosLowerPoly10_le_cos_and_cos_le_cosUpperPoly12 hz).2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) with ⟨_, hP16, hdS15, hdP16⟩
  rcases cos_step4 16 20922789888000 355687428096000 6402373705728000
      0x1b02b9306890000 0x21c3677c82b40000 hdS15 hdP16
      (by norm_num [S11]) (by norm_num [cosUpperPoly12, cosLowerPoly10]) hP16
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) with ⟨hP18, hP20, _, _⟩
  exact ⟨hP18 t ht, hP20 t ht⟩
private theorem pi_bounds_18digit : (0x2b992ddfa23249d6 / 10 ^ 18 : ℝ) ≤ π ∧ π ≤
    (0x2b992ddfa23249d7 / 10 ^ 18 : ℝ) := by
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  set t0 : ℝ := 0x2b992ddfa23249d6 / (4 * 10 ^ 18)
  set t1 : ℝ := 0x2b992ddfa23249d7 / (4 * 10 ^ 18)
  have hb0 := (cosLowerPoly18_le_cos_and_cos_le_cosUpperPoly20 (by positivity : (0 : ℝ) ≤ t0)).1
  have hb1 := (cosLowerPoly18_le_cos_and_cos_le_cosUpperPoly20 (by positivity : (0 : ℝ) ≤ t1)).2
  have hp0 : (0 : ℝ) < cosLowerPoly18 t0 ∧ (0 : ℝ) < 2 * cosLowerPoly18 t0 ^ 2 - 1 := by
    unfold cosLowerPoly18 cosUpperPoly12 cosLowerPoly10; norm_num [t0]
  have hp1_sq : 2 * cosUpperPoly20 t1 ^ 2 - 1 < 0 := by
    unfold cosUpperPoly20 cosLowerPoly18 cosUpperPoly12 cosLowerPoly10; norm_num [t1]
  have hc0 : 0 < Real.cos (2 * t0) := by
    rw [Real.cos_two_mul]; nlinarith [mul_self_le_mul_self hp0.1.le hb0]
  have hct1 : 0 ≤ Real.cos t1 :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
  have hc1 : Real.cos (2 * t1) < 0 := by
    rw [Real.cos_two_mul]; nlinarith [mul_self_le_mul_self hct1 hb1]
  have hm0 : 2 * t0 ∈ Set.Icc (0 : ℝ) π := ⟨by dsimp [t0]; norm_num, by dsimp [t0]; linarith⟩
  have hm1 : 2 * t1 ∈ Set.Icc (0 : ℝ) π := ⟨by dsimp [t1]; norm_num, by dsimp [t1]; linarith⟩
  have hmp : π / 2 ∈ Set.Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
  refine ⟨by_contra fun h ↦ ?_, by_contra fun h ↦ ?_⟩
  · have := Real.cos_pi_div_two ▸
      Real.strictAntiOn_cos.antitoneOn hmp hm0 (by dsimp [t0]; linarith)
    linarith
  · have := Real.cos_pi_div_two ▸
      Real.strictAntiOn_cos.antitoneOn hm1 hmp (by dsimp [t1]; linarith)
    linarith
def cRad38True : ℕ → ℕ
  | 0 => 273728345630
  | 1 => 1094913382523
  | 2 => 4379653530094
  | 3 => 17518614120377
  | 4 => 70074456481511
  | 5 => 280297825926047
  | 6 => 0x3fbb7b161ee7e
  | _ => 0
theorem boxRadConst_38_eq_cRad38True {μ : ℕ} (hμ : μ < 7) : boxRadConst 38 (1 / 42) 1 μ =
    cRad38True μ := by
  rcases pi_bounds_18digit with ⟨hpi_lo, hpi_hi⟩
  have hv_bds : (0xba4fc02c25080839 / 10 ^ 18 : ℝ) ≤ cellVolume ^ (1 / 3 : ℝ) ∧
    cellVolume ^ (1 / 3 : ℝ) ≤ (0xba4fc02c2508083a / 10 ^ 18 : ℝ) := by
    have cc (r : ℝ) (hr : 0 ≤ r) : (r ^ 3) ^ (1 / 3 : ℝ) = r := by
      rw [show r ^ 3 = r ^ (3 : ℝ) by norm_num, ← Real.rpow_mul hr]; norm_num
    have h1 := Real.rpow_le_rpow (by positivity)
      (by unfold cellVolume; norm_num : (0xba4fc02c25080839 / 10 ^ 18 : ℝ) ^ 3 ≤ cellVolume)
      (by positivity : (0 : ℝ) ≤ 1 / 3)
    have h2 := Real.rpow_le_rpow (by unfold cellVolume; positivity)
      (by unfold cellVolume; norm_num : cellVolume ≤ (0xba4fc02c2508083a / 10 ^ 18 : ℝ) ^ 3)
      (by positivity : (0 : ℝ) ≤ 1 / 3)
    rw [cc _ (by positivity)] at h1; rw [cc _ (by positivity)] at h2
    exact ⟨h1, h2⟩
  rcases hv_bds with ⟨hv_lo, hv_hi⟩
  set P_lo : ℝ := (0x2b992ddfa23249d6 / 10 ^ 18 : ℝ) * (0xba4fc02c25080839 / 10 ^ 18 : ℝ)
  set P_hi : ℝ := (0x2b992ddfa23249d7 / 10 ^ 18 : ℝ) * (0xba4fc02c2508083a / 10 ^ 18 : ℝ)
  have hprod_lo : P_lo ≤ π * cellVolume ^ (1 / 3 : ℝ) :=
    mul_le_mul hpi_lo hv_lo (by norm_num) (by linarith)
  have hprod_hi : π * cellVolume ^ (1 / 3 : ℝ) ≤ P_hi :=
    mul_le_mul hpi_hi hv_hi (by linarith) (by norm_num)
  have hden_pos : (0 : ℝ) < (1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ)) := by
    have : (0 : ℝ) < P_lo := by dsimp [P_lo]; positivity
    linarith
  have hle : cRad38True μ ≤ boxRadConst 38 (1 / 42) 1 μ := by
    unfold boxRadConst
    apply Nat.le_floor
    rw [le_div_iff₀ hden_pos]
    have hmul_hi : (cRad38True μ : ℝ) * ((1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ))) ≤
      (cRad38True μ : ℝ) * ((1 / 42 : ℝ) * P_hi) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    refine hmul_hi.trans ?_
    have hcases : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [cRad38True, P_hi]
  have hlt : boxRadConst 38 (1 / 42) 1 μ < cRad38True μ + 1 := by
    unfold boxRadConst
    refine (Nat.floor_lt (by positivity)).mpr ?_
    rw [div_lt_iff₀ hden_pos]
    have hmul_lo : ((cRad38True μ + 1 : ℕ) : ℝ) * ((1 / 42 : ℝ) * P_lo) ≤
      ((cRad38True μ + 1 : ℕ) : ℝ) * ((1 / 42 : ℝ) * (π * cellVolume ^ (1 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    refine lt_of_lt_of_le ?_ hmul_lo
    have hcases : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [cRad38True, P_lo]
  omega
theorem fine38_imp_coarseEnv8_lt {μ s_fold s_true u_fine30 u_coarse8 : ℕ} (hμ : μ < 7) (hs_pos : 0 <
    s_fold) (hs_le : s_fold ≤ s_true)
    (hfine : u_fine30 + 2 ^ 30 * u_coarse8 < boxRadConst 38 (1 / 42) 1 μ / s_true) : u_coarse8 <
      coarseEnv8Count (boxRadConst 36 (1 / 42) 1 μ) s_fold := by
  rw [boxRadConst_38_eq_cRad38True hμ] at hfine
  rw [coarseEnv8Count_eq_coarseRadCeilVal7 (by omega) hs_pos]
  have hsep : cRad38True μ < 2 ^ 30 * (coarseRadCeilVal7 μ + 1) := by
    rcases (by omega : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [cRad38True, coarseRadCeilVal7]
  set q := (coarseRadCeilVal7 μ + s_fold) / s_fold
  have hq : coarseRadCeilVal7 μ + 1 ≤ s_fold * q := by
    have := Nat.div_add_mod (coarseRadCeilVal7 μ + s_fold) s_fold
    have := Nat.mod_lt (coarseRadCeilVal7 μ + s_fold) hs_pos
    dsimp [q] at *; nlinarith
  have h1 : cRad38True μ / s_true ≤ cRad38True μ / s_fold := Nat.div_le_div_left hs_le hs_pos
  have h2 : cRad38True μ / s_fold < 2 ^ 30 * q + 1 :=
    (Nat.div_lt_iff_lt_mul hs_pos).mpr (by nlinarith)
  change u_coarse8 < q; omega
theorem dampCoinConst_36_two_div_42_eq : dampCoinConst 36 (2 / 42) 2 = 2 ^ 36 := by
  unfold dampCoinConst
  have heq : (2 : ℝ) ^ 36 * ((2 : ℝ) / 42) / ((2 : ℝ) / 42) = ((2 ^ 36 : ℕ) : ℝ) := by
    push_cast; norm_num
  rw [heq, Nat.floor_natCast]
def IsTwosGridState (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : Prop :=
  (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3, (elecAxisField x i w).val ≠ 32) ∧
    (∀ w : Fin 3, (projAxisField x w).val ≠ 128)
def twosMomentum (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    SpecsAux.SpecMirror.Particle → Fin 3 → ℤ
  | .electron i, w => twosComp6Int (elecAxisField x i w)
  | .projectile, w => twosComp8Int (projAxisField x w)
theorem isTwosGridState_smToTwosSysPerm_iff (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    IsTwosGridState (smToTwosSysPerm x) ↔ IsGridState x := by
  have hiff3 (u : Fin 64) : (smToTwosAxisPerm 3 u).val = 32 ↔ u.val = 32 :=
    smToTwosAxisPerm_eq_negZero_iff 3 u
  have hiff5 (u : Fin 256) : (smToTwosAxisPerm 5 u).val = 128 ↔ u.val = 128 :=
    smToTwosAxisPerm_eq_negZero_iff 5 u
  refine ⟨fun ⟨he, hp⟩ a w ↦ ?_, fun hx ↦ ⟨fun i w h32 ↦ ?_, fun w h128 ↦ ?_⟩⟩
  · cases a with
    | electron i =>
        rw [signMagnitude_electron_eq]; intro hbad; obtain ⟨h1, h2⟩ := Prod.mk.inj hbad
        have hv : (elecAxisField x i w).val = 32 := by
          have := (elecAxisField x i w).isLt; omega
        exact he i w (by rw [elecAxisField_smToTwosSys, (hiff3 _).mpr hv])
    | projectile =>
        rw [signMagnitude_projectile_eq]; intro hbad; obtain ⟨h1, h2⟩ := Prod.mk.inj hbad
        have hv : (projAxisField x w).val = 128 := by
          have := (projAxisField x w).isLt; omega
        exact hp w (by rw [projAxisField_smToTwosSys, (hiff5 _).mpr hv])
  · rw [elecAxisField_smToTwosSys, hiff3] at h32
    exact hx (.electron i) w (by rw [signMagnitude_electron_eq, h32])
  · rw [projAxisField_smToTwosSys, hiff5] at h128
    exact hx .projectile w (by rw [signMagnitude_projectile_eq, h128])
theorem twosMomentum_smToTwosSysPerm {x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)}
    (hx : IsGridState x) (d : SpecsAux.SpecMirror.Particle) :
    twosMomentum (smToTwosSysPerm x) d = SpecsAux.SpecMirror.momentum x d := by
  ext w
  cases d with
  | electron i =>
      dsimp [twosMomentum]
      exact twosComp6_smToTwosSys_eq_momentum hx i w
  | projectile =>
      dsimp [twosMomentum]
      exact twosComp8_smToTwosSys_eq_momentum hx w
end Slot5MatrixAndScaleCert
end
end ModSlot5MatrixAndScaleCert

section ModMomSlots35Slot3Helpers
@[expose] public section
namespace MomSlots35Slot3HelpersAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) : (f.trans g) x = g (f x) :=
  rfl
end MomSlots35Slot3HelpersAlt
namespace MomSlots35Slot3ProjNuclear
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open MomSlots35Coulomb
open ModWrapCoarse8PureMomentum
open Slot5MatrixAndScaleCert
open SpecsAux.DyadicSubgridToeplitz512AndShift
open TwosCompAndWire0Cancel
open KaratsubaQft64Matrix (twosComp6Int)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
section ShellDecoder3
attribute [local irreducible] box3D nonzeroBox3D
def shellMu3 (u22 : Fin 4194304) : ℕ := if u22.val < 65536 then 0 else if u22.val < 131072
    then 1 else if u22.val < 262144 then 2 else if u22.val < 524288 then 3 else if u22.val <
    1048576 then 4 else if u22.val < 2097152 then 5 else 6
theorem shellMu3_lt_seven (u22 : Fin 4194304) : shellMu3 u22 < 7 := by
  unfold shellMu3
  split_ifs <;> omega
theorem two_pow_15_add_shellMu3_bounds {u22 : Fin 4194304} (hu : 32768 ≤ u22.val) :
    2 ^ (15 + shellMu3 u22) ≤ u22.val ∧ u22.val < 2 ^ (16 + shellMu3 u22) := by
  have hlt := u22.isLt
  unfold shellMu3
  split_ifs <;> norm_num <;> omega
theorem shellMu3_eq_of_mem_range {u22 : Fin 4194304} {μ : ℕ} (hμ : μ < 7)
    (hlo : 2 ^ (15 + μ) ≤ u22.val) (hhi : u22.val < 2 ^ (16 + μ)) : shellMu3 u22 = μ := by
  have hcases : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 := by omega
  unfold shellMu3
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at hlo hhi <;> split_ifs <;> omega
def shellMagCoord3 (u22 : Fin 4194304) (w : Fin 3) : ℕ :=
  (u22.val / 2 ^ (w.val * (shellMu3 u22 + 1))) % 2 ^ (shellMu3 u22 + 1)
def shellFree3 (u22 : Fin 4194304) : ℕ :=
  (u22.val - 2 ^ (15 + shellMu3 u22)) / 2 ^ (3 * (shellMu3 u22 + 1))
def negSign3_22 (u22 : Fin 4194304) (s3 : Fin 8) : Fin 8 :=
  let b := fun w : Fin 3 ↦
    if shellMagCoord3 u22 w = 0 then signBit3 s3 w else 1 - signBit3 s3 w
  ⟨b 0 + 2 * b 1 + 4 * b 2, by
    have h0 : b 0 ≤ 1 := by dsimp [b]; split_ifs <;> [exact signBit3_le_one s3 0; omega]
    have h1 : b 1 ≤ 1 := by dsimp [b]; split_ifs <;> [exact signBit3_le_one s3 1; omega]
    have h2 : b 2 ≤ 1 := by dsimp [b]; split_ifs <;> [exact signBit3_le_one s3 2; omega]
    omega⟩
theorem signBit3_negSign3_22 (u22 : Fin 4194304) (s3 : Fin 8) (w : Fin 3) : signBit3
    (negSign3_22 u22 s3) w =
    if shellMagCoord3 u22 w = 0 then signBit3 s3 w else 1 - signBit3 s3 w := by
  have hb : ∀ j : Fin 3,
      (if shellMagCoord3 u22 j = 0 then signBit3 s3 j else 1 - signBit3 s3 j) ≤ 1 := fun j ↦ by
    split_ifs <;> [exact signBit3_le_one s3 j; omega]
  unfold negSign3_22
  rw [signBit3_mk (hb 0) (hb 1) (hb 2) w]
  fin_cases w <;> rfl
theorem negSign3_22_involutive (u22 : Fin 4194304) (s3 : Fin 8) : negSign3_22 u22
    (negSign3_22 u22 s3) = s3 := by
  apply Fin.ext
  rw [s3_eq_sum_signBit3 (negSign3_22 u22 (negSign3_22 u22 s3)), s3_eq_sum_signBit3 s3]
  have hw : ∀ w : Fin 3, signBit3 (negSign3_22 u22 (negSign3_22 u22 s3)) w = signBit3 s3 w :=
    fun w ↦ by
    rw [signBit3_negSign3_22, signBit3_negSign3_22]
    have hle := signBit3_le_one s3 w
    split_ifs <;> omega
  rw [hw 0, hw 1, hw 2]
def validShellNu3 (u22 : Fin 4194304) (s3 : Fin 8) : Bool := decide (32768 ≤ u22.val) &&
    decide (2 ^ shellMu3 u22 ≤ max (shellMagCoord3 u22 0) (max (shellMagCoord3 u22 1)
    (shellMagCoord3 u22 2))) && decide
    (∀ w : Fin 3, ¬(shellMagCoord3 u22 w = 0 ∧ signBit3 s3 w = 1))
def decodeShellNu3 (u22 : Fin 4194304) (s3 : Fin 8) : Fin 3 → ℤ :=
  fun w ↦ if signBit3 s3 w = 1 then -(shellMagCoord3 u22 w : ℤ) else (shellMagCoord3 u22 w : ℤ)
theorem natAbs_decodeShellNu3 (u22 : Fin 4194304) (s3 : Fin 8) (w : Fin 3) :
    (decodeShellNu3 u22 s3 w).natAbs = shellMagCoord3 u22 w := by
  unfold decodeShellNu3
  split_ifs <;> simp
theorem validShellNu3_negSign3_22 (u22 : Fin 4194304) (s3 : Fin 8) : validShellNu3 u22
    (negSign3_22 u22 s3) = validShellNu3 u22 s3 := by
  unfold validShellNu3
  congr 1
  apply decide_eq_decide.mpr
  refine forall_congr' fun w ↦ ?_
  rw [signBit3_negSign3_22]
  by_cases hm : shellMagCoord3 u22 w = 0 <;> simp [hm]
theorem decodeShellNu3_negSign3_22 {u22 : Fin 4194304} {s3 : Fin 8} (hv : validShellNu3 u22 s3 =
    true) :
    decodeShellNu3 u22 (negSign3_22 u22 s3) = -decodeShellNu3 u22 s3 := by
  unfold validShellNu3 at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  ext w; unfold decodeShellNu3; rw [Pi.neg_apply, signBit3_negSign3_22]
  have hw := hv.2 w; have hs := signBit3_le_one s3 w
  by_cases hm : shellMagCoord3 u22 w = 0
  · simp [hm, show signBit3 s3 w = 0 by omega]
  · rcases (by omega : signBit3 s3 w = 0 ∨ signBit3 s3 w = 1) with hs0 | hs1 <;> simp [*]
theorem shellMagCoord3_lt (u22 : Fin 4194304) (w : Fin 3) : shellMagCoord3 u22 w <
    2 ^ (shellMu3 u22 + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
private theorem maxCoordNatAbs_decodeShellNu3 (u22 : Fin 4194304) (s3 : Fin 8) : maxCoordNatAbs
    (decodeShellNu3 u22 s3) =
    max (shellMagCoord3 u22 0) (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2)) := by
  unfold maxCoordNatAbs
  rw [natAbs_decodeShellNu3, natAbs_decodeShellNu3, natAbs_decodeShellNu3]
theorem decodeShellNu3_mem_and_shellIndex {u22 : Fin 4194304} {s3 : Fin 8}
    (hv : validShellNu3 u22 s3 = true) : decodeShellNu3 u22 s3 ∈ nonzeroBox3D (127 : ℤ) ∧
      shellIndex (decodeShellNu3 u22 s3) = shellMu3 u22 := by
  unfold validShellNu3 at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with ⟨⟨_, hmax_lo⟩, _⟩
  set μ := shellMu3 u22
  set M := max (shellMagCoord3 u22 0) (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2))
  have hμ7 : μ < 7 := shellMu3_lt_seven u22
  have hmax_hi : M < 2 ^ (μ + 1) := max_lt (shellMagCoord3_lt u22 0)
    (max_lt (shellMagCoord3_lt u22 1) (shellMagCoord3_lt u22 2))
  have h2 : 2 ^ (μ + 1) ≤ 128 := by
    calc 2 ^ (μ + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 128 := by norm_num
  have hpos : 1 ≤ M := le_trans Nat.one_le_two_pow hmax_lo
  have hne0 : decodeShellNu3 u22 s3 ≠ 0 := fun h0 ↦ by
    have hmx := maxCoordNatAbs_decodeShellNu3 u22 s3
    rw [h0] at hmx; unfold maxCoordNatAbs at hmx; simp at hmx; omega
  refine ⟨(mem_nonzeroBox3D 127 _).mpr ⟨hne0, fun w ↦ ?_⟩, ?_⟩
  · have hnat : (decodeShellNu3 u22 s3 w).natAbs ≤ M := by
      rw [natAbs_decodeShellNu3]
      fin_cases w
      · exact le_max_left _ _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  · unfold shellIndex; rw [maxCoordNatAbs_decodeShellNu3 u22 s3]
    change Nat.log 2 M = μ
    have hlt1 : Nat.log 2 M < μ + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp
      (lt_of_le_of_lt (Nat.pow_log_le_self 2 (by omega : M ≠ 0)) hmax_hi)
    have hlt2 : μ < Nat.log 2 M + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp
      (lt_of_le_of_lt hmax_lo (Nat.lt_pow_succ_log_self (by norm_num) M))
    omega
theorem shellIndex_lt_seven_of_mem_nonzeroBox3D_127 {ν : Fin 3 →
    ℤ} (hν : ν ∈ nonzeroBox3D (127 : ℤ)) : shellIndex ν < 7 := by
  rcases (mem_nonzeroBox3D 127 ν).mp hν with ⟨hne, hbox⟩
  have hmx_le : maxCoordNatAbs ν ≤ 127 := by
    unfold maxCoordNatAbs; have := hbox 0; have := hbox 1; have := hbox 2; omega
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt
    (Nat.pow_log_le_self 2 (maxCoordNatAbs_pos_of_ne_zero hne).ne') (by omega : _ < 2 ^ 7))
theorem natAbs_lt_shell_of_mem_nonzeroBox3D_127 {ν : Fin 3 → ℤ}
    (hν : ν ∈ nonzeroBox3D (127 : ℤ)) : 2 ^ shellIndex ν ≤ maxCoordNatAbs ν ∧ ∀ w : Fin 3,
      (ν w).natAbs < 2 ^ (shellIndex ν + 1) := by
  refine ⟨Nat.pow_log_le_self 2
      (maxCoordNatAbs_pos_of_ne_zero ((mem_nonzeroBox3D 127 ν).mp hν).1).ne',
    fun w ↦ lt_of_le_of_lt ?_ (Nat.lt_pow_succ_log_self (by norm_num) _)⟩
  unfold maxCoordNatAbs; fin_cases w
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)
lemma shellPack3_extract {m fv m0 m1 m2 : ℕ} (hm : m < 7)
    (hfv : fv < 2 ^ (12 - 2 * m))
    (hm0 : m0 < 2 ^ (m + 1)) (hm1 : m1 < 2 ^ (m + 1)) (hm2 : m2 < 2 ^ (m + 1)) :
    let u := 2 ^ (15 + m) + 2 ^ (3 * (m + 1)) * fv +
      (m0 + 2 ^ (m + 1) * m1 + 2 ^ (2 * (m + 1)) * m2)
    2 ^ (15 + m) ≤ u ∧ u < 2 ^ (16 + m) ∧ u % 2 ^ (m + 1) = m0 ∧
      u / 2 ^ (m + 1) % 2 ^ (m + 1) = m1 ∧ u / 2 ^ (2 * (m + 1)) % 2 ^ (m + 1) = m2 ∧
      (u - 2 ^ (15 + m)) / 2 ^ (3 * (m + 1)) = fv := by
  intro u; dsimp only [u]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num at *; omega)
private lemma shellUnpack3_reconstruct {m u : ℕ} (hm : m < 7) (hlo : 2 ^ (15 + m) ≤ u)
    (hhi : u < 2 ^ (16 + m)) : (u - 2 ^ (15 + m)) / 2 ^ (3 * (m + 1)) < 2 ^ (12 - 2 * m) ∧ 2 ^
    (15 + m) + 2 ^ (3 * (m + 1)) * ((u - 2 ^ (15 + m)) / 2 ^ (3 * (m + 1))) + (u % 2 ^ (m + 1)
    + 2 ^ (m + 1) * (u / 2 ^ (m + 1) % 2 ^ (m + 1)) + 2 ^ (2 * (m + 1)) *
      (u / 2 ^ (2 * (m + 1)) % 2 ^ (m + 1))) = u := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num at *; omega)
def encodeShellNu3 (ν : Fin 3 →
    ℤ) (hν : ν ∈ nonzeroBox3D (127 : ℤ)) (free : Fin (2 ^ (12 - 2 *
    shellIndex ν))) : Fin 4194304 × Fin 8 :=
  let μ := shellIndex ν; let b := μ + 1
  let sb : Fin 3 → ℕ := fun w ↦ if ν w < 0 then 1 else 0
  (⟨2 ^ (15 + μ) + 2 ^ (3 * b) * free.val +
      ((ν 0).natAbs + 2 ^ b * (ν 1).natAbs + 2 ^ (2 * b) * (ν 2).natAbs), by
      have hμ7 := shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν
      have hna := (natAbs_lt_shell_of_mem_nonzeroBox3D_127 hν).2
      exact lt_of_lt_of_le (shellPack3_extract hμ7 free.isLt (hna 0) (hna 1) (hna 2)).2.1
        (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : 16 + μ ≤ 22))
          (by norm_num))⟩,
   ⟨sb 0 + 2 * sb 1 + 4 * sb 2, by dsimp only [sb]; split_ifs <;> omega⟩)
private theorem encodeShellNu3_spec {ν : Fin 3 → ℤ} (hν : ν ∈ nonzeroBox3D (127 : ℤ))
    (free : Fin (2 ^ (12 - 2 * shellIndex ν))) :
    let p := encodeShellNu3 ν hν free
    validShellNu3 p.1 p.2 = true ∧ decodeShellNu3 p.1 p.2 = ν ∧
      shellFree3 p.1 = free.val := by
  intro p
  have hμ7 := shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν
  rcases natAbs_lt_shell_of_mem_nonzeroBox3D_127 hν with ⟨hmx_lo, hna⟩
  have hex := shellPack3_extract hμ7 free.isLt (hna 0) (hna 1) (hna 2)
  have hmu_eq : shellMu3 p.1 = shellIndex ν := shellMu3_eq_of_mem_range hμ7 hex.1 hex.2.1
  have hm_eq : shellMagCoord3 p.1 0 = (ν 0).natAbs ∧ shellMagCoord3 p.1 1 = (ν 1).natAbs ∧
      shellMagCoord3 p.1 2 = (ν 2).natAbs ∧ shellFree3 p.1 = free.val := by
    unfold shellMagCoord3 shellFree3; rw [hmu_eq]
    norm_num [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.div_one]; exact hex.2.2
  have hmw (w : Fin 3) : shellMagCoord3 p.1 w = (ν w).natAbs := by
    fin_cases w
    · exact hm_eq.1
    · exact hm_eq.2.1
    · exact hm_eq.2.2.1
  have hsb (w : Fin 3) : signBit3 p.2 w = if ν w < 0 then 1 else 0 := by
    have hb (j : Fin 3) : (if ν j < 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    dsimp [p, encodeShellNu3]; rw [signBit3_mk (hb 0) (hb 1) (hb 2) w]; fin_cases w <;> rfl
  refine ⟨?_, ?_, hm_eq.2.2.2⟩
  · unfold validShellNu3; simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hmu_eq, hm_eq.1, hm_eq.2.1, hm_eq.2.2.1]
    refine ⟨⟨le_trans (le_trans (by norm_num : 32768 ≤ 2 ^ 15)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right 15 _))) hex.1, hmx_lo⟩,
      fun w ⟨hz, hlt⟩ ↦ ?_⟩
    rw [hmw w] at hz; rw [hsb w, Int.natAbs_eq_zero.mp hz] at hlt; simp at hlt
  · ext w; unfold decodeShellNu3; rw [hsb w, hmw w]
    by_cases hneg : ν w < 0
    · simp [hneg, Int.ofNat_natAbs_of_nonpos hneg.le]
    · simp [hneg, Int.natAbs_of_nonneg (not_lt.mp hneg)]
private def decodeShellNu3FiberEquiv (ν : Fin 3 → ℤ) (hν : ν ∈ nonzeroBox3D (127 : ℤ)) :
    { p : Fin 4194304 × Fin 8 // validShellNu3 p.1 p.2 = true ∧ decodeShellNu3 p.1 p.2 =
      ν } ≃ Fin (2 ^ (12 - 2 * shellIndex ν)) where
  toFun p := ⟨shellFree3 p.1.1, by
    rcases p with ⟨⟨u22, s3⟩, hv, rfl⟩
    rw [(decodeShellNu3_mem_and_shellIndex hv).2]
    unfold validShellNu3 at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases two_pow_15_add_shellMu3_bounds hv.1.1 with ⟨hlo, hhi⟩
    exact (shellUnpack3_reconstruct (shellMu3_lt_seven _) hlo hhi).1⟩
  invFun free := ⟨encodeShellNu3 ν hν free, (encodeShellNu3_spec hν free).1,
    (encodeShellNu3_spec hν free).2.1⟩
  left_inv := fun ⟨⟨u22, s3⟩, hv, hdec⟩ ↦ by
    subst hdec; have hmu := (decodeShellNu3_mem_and_shellIndex hv).2
    unfold validShellNu3 at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    rcases two_pow_15_add_shellMu3_bounds hv.1.1 with ⟨hlo, hhi⟩
    apply Subtype.ext; apply Prod.ext
    · apply Fin.ext; dsimp [encodeShellNu3]
      rw [hmu, natAbs_decodeShellNu3, natAbs_decodeShellNu3, natAbs_decodeShellNu3]
      unfold shellFree3 shellMagCoord3
      norm_num [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.div_one]
      exact (shellUnpack3_reconstruct (shellMu3_lt_seven u22) hlo hhi).2
    · apply Fin.ext; dsimp [encodeShellNu3]; rw [s3_eq_sum_signBit3 s3]
      have hsb (w : Fin 3) : (if decodeShellNu3 u22 s3 w < 0 then 1 else 0) = signBit3 s3 w := by
        unfold decodeShellNu3; have hw := hv.2 w; have hs := signBit3_le_one s3 w
        by_cases hs1 : signBit3 s3 w = 1
        · have hne0 : shellMagCoord3 u22 w ≠ 0 := fun h0 ↦ hw ⟨h0, hs1⟩
          rw [ite_eq_left hs1, ite_eq_left (by omega), hs1]
        · have hs0 : signBit3 s3 w = 0 := by omega
          rw [ite_eq_right hs1, ite_eq_right (by omega), hs0]
      rw [hsb 0, hsb 1, hsb 2]
  right_inv free := Fin.ext (encodeShellNu3_spec hν free).2.2
theorem card_fiber_decodeShellNu3 (ν : Fin 3 → ℤ) (hν : ν ∈ nonzeroBox3D (127 : ℤ)) :
    Fintype.card { p : Fin 4194304 × Fin 8 // validShellNu3 p.1 p.2 = true ∧
      decodeShellNu3 p.1 p.2 = ν } = 2 ^ (12 - 2 * shellIndex ν) := by
  rw [Fintype.card_congr (decodeShellNu3FiberEquiv ν hν), Fintype.card_fin]
private theorem coarseEnv8Count_lt_256_of_mem_nonzeroBox3D_127 {ν : Fin 3 →
    ℤ} (hν : ν ∈ nonzeroBox3D (127 : ℤ)) :
    coarseEnv8Count (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν) < 256 := by
  have hμ7 := shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν
  have hle2 (x y : ℕ) : max x y ^ 2 ≤ x ^ 2 + y ^ 2 := by
    rcases le_total x y with h | h <;> [rw [max_eq_right h]; rw [max_eq_left h]] <;> nlinarith
  have hs_lo : (2 ^ shellIndex ν) ^ 2 ≤ sumNatAbsSq ν := by
    refine le_trans (Nat.pow_le_pow_left (natAbs_lt_shell_of_mem_nonzeroBox3D_127 hν).1 2) ?_
    unfold maxCoordNatAbs sumNatAbsSq; rw [Fin.sum_univ_three, add_assoc]
    exact le_trans (hle2 _ _) (Nat.add_le_add_left (hle2 _ _) _)
  have hc36 := (c36Lb7_le_boxRadConst_and_le_c36Ub7 (shellIndex ν)).2
  have hs_pos : 0 < sumNatAbsSq ν := lt_of_lt_of_le (by positivity) hs_lo
  unfold coarseEnv8Count; rw [Nat.div_lt_iff_lt_mul (by positivity)]
  generalize shellIndex ν = m at hμ7 hs_lo hc36
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num [c36Ub7] at hs_lo hc36; omega)
noncomputable def coarseGood3 (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256) : Bool :=
    validShellNu3 u22 s3 && decide (c8.val < coarseEnv8Count (boxRadConst 36 (1 / 42) 1
    (shellIndex (decodeShellNu3 u22 s3))) (sumNatAbsSq (decodeShellNu3 u22 s3)))
def coarseGood3Computable (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256) : Bool :=
  let s_fold := (shellMagCoord3 u22 0) ^ 2 + (shellMagCoord3 u22 1) ^ 2 + (shellMagCoord3 u22 2) ^ 2
  validShellNu3 u22 s3 &&
    decide (c8.val * s_fold < coarseRadCeilVal7 (shellMu3 u22) + 1)
private theorem coarseGood3Computable_eq_coarseGood3 (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256)
    :
    coarseGood3Computable u22 s3 c8 = coarseGood3 u22 s3 c8 := by
  unfold coarseGood3Computable coarseGood3
  by_cases hv : validShellNu3 u22 s3 = true
  · rw [hv]; simp only [Bool.true_and, decide_eq_decide]
    rcases decodeShellNu3_mem_and_shellIndex hv with ⟨hmem, hsh⟩
    have hs_pos := sumNatAbsSq_pos_of_ne_zero ((mem_nonzeroBox3D 127 _).mp hmem).1
    have hs_eq : (shellMagCoord3 u22 0) ^ 2 + (shellMagCoord3 u22 1) ^ 2 +
      (shellMagCoord3 u22 2) ^ 2 = sumNatAbsSq (decodeShellNu3 u22 s3) := by
      unfold sumNatAbsSq
      rw [Fin.sum_univ_three, natAbs_decodeShellNu3, natAbs_decodeShellNu3, natAbs_decodeShellNu3]
    rw [hs_eq, hsh,
      coarseEnv8Count_eq_coarseRadCeilVal7 (Nat.le_of_lt_succ (shellMu3_lt_seven u22)) hs_pos,
      Nat.lt_succ_iff, Nat.add_div_right _ hs_pos, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hs_pos]
  · have hvf : validShellNu3 u22 s3 = false := Bool.eq_false_iff.mpr hv
    simp [hvf]
private theorem card_prod_lt_eq_sum_fiber3 {α β : Type*} {m : ℕ} (V : α → Bool) (f : α →
    β) (S : Finset β) (F E : β → ℕ)
    [Fintype { y : α × Fin m // (V y.1 && decide (y.2.val < E (f y.1))) = true }] (hf_mem : ∀ a : α,
      V a = true → f a ∈ S) (hE_le : ∀ b ∈ S, E b ≤ m)
    (fibEquiv : ∀ b : β, b ∈ S → { a : α // V a = true ∧ f a = b } ≃ Fin (F b)) :
    Fintype.card { y : α × Fin m // (V y.1 && decide (y.2.val < E (f y.1))) = true } = ∑ b ∈ S,
      F b * E b := by
  let e : { y : α × Fin m // (V y.1 && decide (y.2.val < E (f y.1))) = true } ≃
      (b : { b : β // b ∈ S }) × (Fin (F b.1) × Fin (E b.1)) :=
    { toFun := fun y ↦
        have hv : V y.1.1 = true := (Bool.and_eq_true _ _ |>.mp y.2).1
        have hc : y.1.2.val < E (f y.1.1) :=
          of_decide_eq_true (Bool.and_eq_true _ _ |>.mp y.2).2
        have hb : f y.1.1 ∈ S := hf_mem y.1.1 hv
        ⟨⟨f y.1.1, hb⟩, (fibEquiv (f y.1.1) hb ⟨y.1.1, hv, rfl⟩, ⟨y.1.2.val, hc⟩)⟩
      invFun := fun z ↦
        let a := (fibEquiv z.1.1 z.1.2).symm z.2.1
        ⟨(a.1, ⟨z.2.2.val, lt_of_lt_of_le z.2.2.isLt (hE_le z.1.1 z.1.2)⟩), by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨a.2.1, by rw [a.2.2]; exact z.2.2.isLt⟩⟩
      left_inv := fun ⟨⟨a, _⟩, _⟩ ↦ Subtype.ext <| Prod.ext
        (congrArg Subtype.val ((fibEquiv (f a) _).symm_apply_apply _)) (Fin.ext rfl)
      right_inv := fun ⟨⟨b, hb⟩, ⟨q, r⟩⟩ ↦ by
        dsimp only
        generalize ha : (fibEquiv b hb).symm q = a
        rcases a with ⟨a0, hv0, rfl⟩
        have hq : fibEquiv (f a0) hb ⟨a0, hv0, rfl⟩ = q := by
          rw [← ha]; exact (fibEquiv (f a0) hb).apply_symm_apply q
        exact congrArg (fun q' ↦ (⟨⟨f a0, hb⟩, (q', r)⟩ :
          (b : { b : β // b ∈ S }) × (Fin (F b.1) × Fin (E b.1)))) hq }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_coe_sort S (fun b ↦ F b * E b)
private theorem card_coarseGood3_div_two_pow_33_eq :
    (Fintype.card { x : Fin 4194304 × Fin 8 × Fin 256 //
    coarseGood3 x.1 x.2.1 x.2.2 = true } : ℝ) / (2 ^ 33 : ℝ) = coulombCoarse8PreOAAProb 127 8192 :=
      by
  let assocE :
      { x : Fin 4194304 × Fin 8 × Fin 256 // coarseGood3 x.1 x.2.1 x.2.2 = true } ≃
      { y : (Fin 4194304 × Fin 8) × Fin 256 // coarseGood3 y.1.1 y.1.2 y.2 = true } :=
    ⟨fun x ↦ ⟨((x.1.1, x.1.2.1), x.1.2.2), x.2⟩,
     fun y ↦ ⟨(y.1.1.1, y.1.1.2, y.1.2), y.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hpart : (Fintype.card { x : Fin 4194304 × Fin 8 × Fin 256 // coarseGood3 x.1 x.2.1 x.2.2 =
    true } : ℕ) =
      ∑ ν ∈ nonzeroBox3D (127 : ℤ),
        2 ^ (12 - 2 * shellIndex ν) *
        coarseEnv8Count (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν) := by
    rw [Fintype.card_congr assocE]
    exact card_prod_lt_eq_sum_fiber3 (fun p : Fin 4194304 × Fin 8 ↦ validShellNu3 p.1 p.2)
      (fun p : Fin 4194304 × Fin 8 ↦ decodeShellNu3 p.1 p.2) (nonzeroBox3D (127 : ℤ))
      (fun ν ↦ 2 ^ (12 - 2 * shellIndex ν))
      (fun ν ↦ coarseEnv8Count (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν))
      (fun _ hv ↦ (decodeShellNu3_mem_and_shellIndex hv).1)
      (fun _ hν ↦ (coarseEnv8Count_lt_256_of_mem_nonzeroBox3D_127 hν).le)
      decodeShellNu3FiberEquiv
  rw [hpart, Nat.cast_sum, Finset.sum_div]
  unfold coulombCoarse8PreOAAProb coarseBoxRadKernel8
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ν hν ↦ ?_
  have hμ7 : 2 * shellIndex ν ≤ 12 := by
    have := shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν; omega
  push_cast
  have hpow : ((2 : ℝ) ^ (12 - 2 * shellIndex ν)) / (2 ^ 33 : ℝ) = (1 / 8192 : ℝ) /
    (2 : ℝ) ^ (2 * shellIndex ν + 8) := by
    have hsplit : (2 : ℝ) ^ 33 = (2 : ℝ) ^ (12 - 2 * shellIndex ν) *
      (8192 * (2 : ℝ) ^ (2 * shellIndex ν + 8)) := by
      rw [show 33 = (12 - 2 * shellIndex ν) + 13 + (2 * shellIndex ν + 8) by omega,
        pow_add, pow_add]; norm_num; ring
    rw [hsplit]; field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [mul_div_right_comm, hpow]; ring
theorem coulombCoarse8PreOAAProb_127_8192_le_one : coulombCoarse8PreOAAProb 127 8192 ≤ 1 := by
  rw [← card_coarseGood3_div_two_pow_33_eq]
  refine (div_le_one (by positivity)).mpr ?_
  exact_mod_cast (Fintype.card_subtype_le _).trans_eq
    (by norm_num [Fintype.card_prod, Fintype.card_fin])
end ShellDecoder3
section ScaleAndOperatorBridge
lemma ne_zero_of_mem_nonzeroBox3D3 {M : ℤ} {ν : Fin 3 → ℤ} (h : ν ∈ nonzeroBox3D M) : ν ≠ 0 :=
    ((mem_nonzeroBox3D M ν).mp h).1
lemma bounds_of_mem_box3D3 {M : ℤ} {ν : Fin 3 → ℤ} (h : ν ∈ box3D M) (w : Fin 3) : -M ≤ ν w ∧ ν w ≤
    M := (mem_box3D M ν).mp h w
lemma mk_mem_box3D3 {M : ℤ} {ν : Fin 3 → ℤ} (h : ∀ w, -M ≤ ν w ∧ ν w ≤ M) : ν ∈ box3D M :=
    (mem_box3D M ν).mpr h
lemma mk_mem_nonzeroBox3D3 {M : ℤ} {ν : Fin 3 → ℤ} (hne : ν ≠ 0) (h : ∀ w,
    -M ≤ ν w ∧ ν w ≤ M) : ν ∈ nonzeroBox3D M := (mem_nonzeroBox3D M ν).mpr ⟨hne, h⟩
attribute [local irreducible] box3D nonzeroBox3D
def ProjTwosGridState (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : Prop :=
  ∀ w : Fin 3, (projAxisField x w).val ≠ 128
theorem twosMomentum_proj_mem_box3D_127 {x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)}
    (hx : ProjTwosGridState x) : twosMomentum x .projectile ∈ box3D (127 : ℤ) :=
  mk_mem_box3D3 fun w ↦ by
    dsimp [twosMomentum, twosComp8Int]
    have := (projAxisField x w).isLt
    have := hx w
    omega
theorem twosComp8Int_injective : Function.Injective twosComp8Int := fun a b hab ↦
  Fin.ext <| by
    dsimp [twosComp8Int] at hab
    have := a.isLt
    have := b.isLt
    omega
theorem twosComp6Int_injective : Function.Injective twosComp6Int := fun a b hab ↦
  Fin.ext <| by
    dsimp [twosComp6Int] at hab
    have := a.isLt
    have := b.isLt
    omega
theorem systemQubits_eq_of_fields {y₁ y₂ : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)} (he : ∀ i :
    Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3, elecAxisField y₁ i w = elecAxisField y₂ i w)
    (hp : ∀ w : Fin 3, projAxisField y₁ w = projAxisField y₂ w) : y₁ = y₂ := by
  apply (basisBitsEquiv SpecsAux.SpecMirror.systemQubits).injective; funext k
  change basisBits SpecsAux.SpecMirror.systemQubits y₁ k =
    basisBits SpecsAux.SpecMirror.systemQubits y₂ k
  have hk_lt : k.val < 3948 := k.isLt
  have h218 : SpecsAux.SpecMirror.numElectrons = 218 := rfl
  by_cases hke : k.val < 3924
  · let i : Fin SpecsAux.SpecMirror.numElectrons := ⟨(k.val / 6) / 3, by omega⟩
    let w : Fin 3 := ⟨(k.val / 6) % 3, by omega⟩
    let b : Fin 6 := ⟨k.val % 6, by omega⟩
    let axIdx : Fin 654 := ⟨3 * i.val + w.val, by have := i.isLt; have := w.isLt; omega⟩
    have hk_eq : k = elec654Axes axIdx b := Fin.ext (by
      change k.val = 6 * (3 * ((k.val / 6) / 3) + (k.val / 6) % 3) + k.val % 6; omega)
    rw [hk_eq, ← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex]
    exact congrArg (fun u ↦ basisBits 6 u b) (he i w)
  · let w : Fin 3 := ⟨(k.val - 3924) / 8, by omega⟩
    let b : Fin 8 := ⟨(k.val - 3924) % 8, by omega⟩
    have hk_eq : k = proj3Axes w b := Fin.ext (by
      change k.val = 3924 + 8 * ((k.val - 3924) / 8) + (k.val - 3924) % 8; omega)
    rw [hk_eq, ← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex]
    exact congrArg (fun u ↦ basisBits 8 u b) (hp w)
lemma fermionicProjector_sandwich_congr_on_grid
    (spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons))
    (A B : Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hAB : ∀ x y,
      IsGridState x → IsGridState y → A x y = B x y) : fermionicProjector spinUp * A *
      fermionicProjector spinUp =
    fermionicProjector spinUp * B * fermionicProjector spinUp := by
  have hG : SpecsAux.BridgeFermionicComm.SpecInner.gridProjector * A *
    SpecsAux.BridgeFermionicComm.SpecInner.gridProjector =
    SpecsAux.BridgeFermionicComm.SpecInner.gridProjector * B *
    SpecsAux.BridgeFermionicComm.SpecInner.gridProjector := by
    unfold SpecsAux.BridgeFermionicComm.SpecInner.gridProjector predProjector; ext x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hx : IsGridState x <;> by_cases hy : IsGridState y <;> simp [hx, hy, hAB]
  have hGP : SpecsAux.BridgeFermionicComm.SpecInner.gridProjector = SpecsAux.gridProjector := rfl
  have hF (M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) : fermionicProjector spinUp * M *
    fermionicProjector spinUp = fermionicProjector spinUp *
      (SpecsAux.BridgeFermionicComm.SpecInner.gridProjector * M *
        SpecsAux.BridgeFermionicComm.SpecInner.gridProjector) * fermionicProjector spinUp := by
    calc fermionicProjector spinUp * M * fermionicProjector spinUp
        = (fermionicProjector spinUp * SpecsAux.BridgeFermionicComm.SpecInner.gridProjector) * M *
            (SpecsAux.BridgeFermionicComm.SpecInner.gridProjector * fermionicProjector spinUp) := by
          rw [hGP, fermionicProjector_mul_gridProjector, gridProjector_mul_fermionicProjector]
      _ = fermionicProjector spinUp *
            (SpecsAux.BridgeFermionicComm.SpecInner.gridProjector * M *
              SpecsAux.BridgeFermionicComm.SpecInner.gridProjector) *
            fermionicProjector spinUp := by simp only [Matrix.mul_assoc]
  rw [hF A, hG, ← hF B]
end ScaleAndOperatorBridge
namespace Slot3CleanPrim
open DyadicQft64WalkCircuit
theorem neg_one_pow_bit_mul_self (k : ℕ) : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num
section Slot1CleanCircuit
noncomputable abbrev ket {K : ℕ} (β : BitAssignment K) : Fin (2 ^ K) → ℂ :=
  basisState ((basisBitsEquiv K).symm β)
theorem basisBits_symm_apply_s1 {K : ℕ} (β : BitAssignment K) : basisBits K
    ((basisBitsEquiv K).symm β) = β := (basisBitsEquiv K).apply_symm_apply β
theorem single_eq_ket {K : ℕ} (g : Fin (2 ^ K)) : (Pi.single g 1 : Fin (2 ^ K) → ℂ) =
    ket (basisBits K g) := by
  simp [ket, basisState]
theorem zmod2_eq_or : ∀ x : ZMod 2, x = 0 ∨ x = 1
  | 0 => .inl rfl
  | 1 => .inr rfl
theorem zmod2_val_le_one (x : ZMod 2) : x.val ≤ 1 := by
  rcases zmod2_eq_or x with rfl | rfl <;> decide
noncomputable def writeReg {K m : ℕ} (β : BitAssignment K) (r : QRegister m K) (γ : BitAssignment m)
    : BitAssignment K :=
  basisBits K (r.replaceIndex ((basisBitsEquiv K).symm β) ((basisBitsEquiv m).symm γ))
theorem writeReg_apply_of_not_mem {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) (w : Wire K) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
noncomputable abbrev localIdx {K m : ℕ} (r : QRegister m K) (β : BitAssignment K) : Fin (2 ^ m) :=
  (basisBitsEquiv m).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {K m : ℕ} (r : QRegister m K)
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (β : BitAssignment K) :
    (r.embedMatrix A).mulVec (ket β) = ∑ l : Fin (2 ^ m),
      A l (localIdx r β) • ket (writeReg β r (basisBits m l)) := by
  have hext : r.extractIndex ((basisBitsEquiv K).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ m)) : A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ m),
    A l j • Pi.single l 1 :=
    funext fun _ ↦ by simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]
inductive RevProg (K : ℕ) : Type
  | nil : RevProg K
  | x (t : Wire K) : RevProg K
  | cnot (c t : Wire K) (h : c ≠ t) : RevProg K
  | toff (c₁ c₂ t : Wire K) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : RevProg K
  | seq (p₁ p₂ : RevProg K) : RevProg K
namespace RevProg
def eval {K : ℕ} : RevProg K → BitAssignment K → BitAssignment K
  | .nil, β => β
  | .x t, β => Function.update β t (β t + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .toff c₁ c₂ t _ _ _, β => Function.update β t (β t + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.eval (p₁.eval β)
@[simp] theorem eval_seq {K : ℕ} (p₁ p₂ : RevProg K) (β : BitAssignment K) : (p₁.seq p₂).eval β =
    p₂.eval (p₁.eval β) := rfl
end RevProg
noncomputable def phaseDiagUnitary {kAct : ℕ} (pred : BitAssignment kAct →
    ZMod 2) : Unitary (2 ^ kAct) :=
  let M : Matrix (Fin (2 ^ kAct)) (Fin (2 ^ kAct)) ℂ :=
    Matrix.diagonal fun g ↦ ((-1 : ℂ) ^ (pred (basisBits kAct g)).val)
  ⟨M, mem_unitaryGroup_iff.mpr <| by
    rw [Matrix.star_eq_conjTranspose, show Mᴴ = M by
      ext i j; by_cases hij : i = j
      · subst hij; simp [M]
      · simp [M, hij, Ne.symm hij]]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ neg_one_pow_bit_mul_self _)⟩
@[simp] theorem slice_one_succ {K m : ℕ} (r : QRegister (m + 1) K) (h : 1 + m ≤ m +
    1) (j : Fin m) : (r.slice 1 m h) j = r j.succ :=
  congrArg r (Fin.ext (by dsimp [MomSlots35Slot3HelpersAlt.qreg_block_apply,
    MomSlots35Slot3HelpersAlt.qreg_block_wires_apply, MomSlots35Slot3HelpersAlt.qreg_whole_wires,
    MomSlots35Slot3HelpersAlt.emb_trans_apply, MomSlots35Slot3HelpersAlt.emb_refl_apply,
    MomSlots35Slot3HelpersAlt.emb_mk_apply]; omega))
theorem phaseDiagUnitary_inv {kAct : ℕ} (pred : BitAssignment kAct →
    ZMod 2) : (phaseDiagUnitary pred)⁻¹ = phaseDiagUnitary pred :=
  mul_eq_one_iff_inv_eq.mp <| Subtype.ext <| by
    change (phaseDiagUnitary pred).1 * (phaseDiagUnitary pred).1 = 1
    simp only [phaseDiagUnitary, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ neg_one_pow_bit_mul_self _)
theorem ket_apply_eq {K : ℕ} (β : BitAssignment K) (l : Fin (2 ^ K)) : ket β l = if l =
    (basisBitsEquiv K).symm β then (1 : ℂ) else 0 := by
  by_cases hl : l = (basisBitsEquiv K).symm β <;> simp [ket, basisState, hl]
end Slot1CleanCircuit
end Slot3CleanPrim
end MomSlots35Slot3ProjNuclear
end
end ModMomSlots35Slot3Helpers

section ModMomSlots35Slot3ProjNuclear
@[expose] public section
namespace MomSlots35Slot3ProjNuclearAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) : (f.trans g) x = g (f x) :=
  rfl
end MomSlots35Slot3ProjNuclearAlt
namespace MomSlots35Slot3ProjNuclear
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectSandwich
open PosMomSelectDynamic
open FullSysPrepare6Slot
open FullSysMomSlots0135Concrete
open MomSlots35Coulomb
open ModWrapCoarse8PureMomentum
open Slot5MatrixAndScaleCert
open SpecsAux.DyadicSubgridToeplitz512AndShift
open TwosCompAndWire0Cancel DyadicQft64 DyadicQft64.PhasePerm
open MomSlots35Slot3ProjNuclear.Slot3CleanPrim
open OctahedralOrbit
open scoped Matrix BigOperators Matrix.Norms.L2Operator
instance (priority := 100000) instNeZeroTwoPowSlot3 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
attribute [local irreducible] box3D nonzeroBox3D
theorem s3ItePos {P : Prop} [Decidable P] {α : Type*} {a b : α} (h : P) : (if P then a else b) =
    a := ite_eq_left h
theorem s3IteNeg {P : Prop} [Decidable P] {α : Type*} {a b : α} (h : ¬P) : (if P then a else b) =
    b := ite_eq_right h
theorem s3DitePos {P : Prop} [Decidable P] {α : Type*} {a : P → α} {b : ¬P →
    α} (h : P) : (dite P a b) = a h := dite_eq_left h
theorem s3DiteNeg {P : Prop} [Decidable P] {α : Type*} {a : P → α} {b : ¬P →
    α} (h : ¬P) : (dite P a b) = b h := dite_eq_right h
theorem s3Unitary_inv_val {N : ℕ} (U : Unitary N) : (U⁻¹).1 = U.1ᴴ :=
  Matrix.star_eq_conjTranspose U.1
theorem s3Sum_zero_of_neg_involution {α : Type*} (S : Finset α) (e : α ≃ α)
    (term : α → ℂ) (hInv : ∀ x, e (e x) = x) (hMem : ∀ x ∈ S, e x ∈ S) (hNeg : ∀ x ∈ S,
      term (e x) = -term x) : ∑ x ∈ S, term x = 0 := by
  have hSumEq : ∑ x ∈ S, term x = ∑ x ∈ S, term (e x) :=
    Finset.sum_bij (fun x _ ↦ e x) hMem (fun _ _ _ _ h ↦ e.injective h)
      (fun b hb ↦ ⟨e b, hMem b hb, hInv b⟩) (fun a _ ↦ by rw [hInv a])
  have h2 : (2 : ℂ) * ∑ x ∈ S, term x = 0 := by
    calc (2 : ℂ) * ∑ x ∈ S, term x
        = (∑ x ∈ S, term x) + (∑ x ∈ S, term x) := two_mul _
      _ = (∑ x ∈ S, term x) + (∑ x ∈ S, term (e x)) := by rw [← hSumEq]
      _ = 0 := by rw [Finset.sum_congr rfl hNeg, Finset.sum_neg_distrib, add_neg_cancel]
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
theorem s3FilterSubtypeEquivSum {α β : Type*} [Fintype α] [Fintype β]
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (f : α → ℂ)
    (term : α → ℂ) (hTerm : ∀ z, P z → term z = if Q z ∧ R z then f z else 0)
    (e : β ≃ { z : α // Q z }) : (∑ z ∈ Finset.univ.filter P, term z) = ∑ t : β,
      if P (e t).1 ∧ R (e t).1 then f (e t).1 else 0 := by
  have hfilt : (Finset.univ.filter P).filter (fun z : α ↦
    Q z ∧ R z) = (Finset.univ.filter Q).filter (fun z ↦ P z ∧ R z) := by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [Finset.sum_congr rfl (fun z hz ↦ hTerm z (Finset.mem_filter.mp hz).2),
    ← Finset.sum_filter, hfilt, Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter Q)
      (fun _ ↦ Finset.mem_filter.trans ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩),
    ← e.sum_comp (fun z : { z : α // Q z } ↦ if P z.1 ∧ R z.1 then f z.1 else 0)]
section Slot3HardwareAndCore
theorem s3TwosComp8Int_eq (u : Fin 256) : twosComp8Int u = if u.val < 128 then (u.val : ℤ) else
    (u.val : ℤ) - 256 := by
  unfold twosComp8Int
  have hu : u.val < 256 := u.isLt
  have hdiv : u.val % 128 + 128 * (u.val / 128) = u.val := Nat.mod_add_div u.val 128
  have hrem : u.val % 128 < 128 := Nat.mod_lt u.val (by omega)
  split_ifs <;> omega
theorem twosComp8Int_bounds_of_ne128 {u : Fin 256} (hu : u.val ≠ 128) : -127 ≤ twosComp8Int u ∧
    twosComp8Int u ≤ 127 := by
  have := u.isLt
  rw [s3TwosComp8Int_eq]
  split_ifs <;> omega
theorem s3TwosComp8Int_sub_abs_le {p q : Fin 256} (hp : p.val ≠ 128) (hq : q.val ≠ 128) :
    |twosComp8Int p - twosComp8Int q| ≤ 2 * (127 : ℤ) := by
  have h1 := twosComp8Int_bounds_of_ne128 hp
  have h2 := twosComp8Int_bounds_of_ne128 hq
  rw [abs_le]
  constructor <;> omega
def s3ProjStepHw (p : Fin 256) (m s : ℕ) : Fin 256 × ℕ × ℕ :=
  let pFlip := if p.val < 128 then p.val + 128 else p.val - 128
  let raw9 := pFlip + (if s = 1 then 127 - m else m) + (if s = 1 then 0 else 127)
  let wHi := if 383 ≤ raw9 then 1 else 0
  let wNoWrap := if 128 ≤ raw9 ∧ raw9 < 383 then 1 else 0
  let xPre := ((raw9 % 256) + (128 + wNoWrap + 2 * wHi)) % 256
  (⟨if xPre < 128 then xPre + 128 else xPre - 128,
    by have := Nat.mod_lt ((raw9 % 256) + (128 + wNoWrap + 2 * wHi)) (by decide : 0 < 256)
       dsimp only [xPre]; split_ifs <;> omega⟩,
   if raw9 < 128 ∨ 383 ≤ raw9 then 255 - m else m, (wHi + wNoWrap * s) % 2)
theorem s3SignBit3_le_one (s3 : Fin 8) (w : Fin 3) : signBit3 s3 w ≤ 1 := by
  unfold signBit3; omega
theorem s3ModWrap127_of_raw9 {tp ν : ℤ} {raw9 : ℕ} (hlin : (raw9 : ℤ) = tp + ν + 255)
    (hle : raw9 ≤ 509) : modWrapCoord 127 tp ν = if raw9 < 128 then (raw9 : ℤ) else if raw9 <
      383 then (raw9 : ℤ) - 255 else (raw9 : ℤ) - 510 := by
  unfold modWrapCoord
  split_ifs <;> omega
theorem s3NatAbs_eq_of_signed {z : ℤ} {d s : ℕ} (hz : z = if s = 1 then -(d : ℤ) else (d : ℤ)) : d =
    z.natAbs := by
  by_cases hs : s = 1
  · rw [s3ItePos hs] at hz; subst hz; rw [Int.natAbs_neg, Int.natAbs_natCast]
  · rw [s3IteNeg hs] at hz; subst hz; exact (Int.natAbs_natCast d).symm
theorem extractIndex_of_bits {n w : ℕ} (r : QRegister w n) (z : Fin (2 ^ n)) (u : Fin (2 ^ w))
    (hz : ∀ b : Fin w, basisBits n z (r b) = basisBits w u b) : r.extractIndex z = u :=
  (basisBitsEquiv w).injective
    (funext fun b ↦ (QRegister.basisBits_extractIndex r z b).trans (hz b))
theorem basisBits_extractIndex_block_eq {n off w : ℕ} (h : off + w ≤
    n) (z : Fin (2 ^ n)) {k : Wire n} {j : ℕ} (hj : j < w) (hk : off + j = k.val) :
    basisBits w ((QRegister.block off w h).extractIndex z) ⟨j, hj⟩ = basisBits n z k :=
  (QRegister.basisBits_extractIndex _ z ⟨j, hj⟩).trans (congrArg (basisBits n z) (Fin.ext hk))
private theorem extractIndex_block_sub {n o1 w1 o2 w2 : ℕ} (h1 : o1 + w1 ≤ n) (h2 : o2 + w2 ≤
    w1) (h3 : (o1 + o2) + w2 ≤ n) (z : Fin (2 ^ n)) :
    (QRegister.block o2 w2 h2).extractIndex ((QRegister.block o1 w1 h1).extractIndex z) =
      (QRegister.block (o1 + o2) w2 h3).extractIndex z := by
  refine extractIndex_of_bits _ _ _ fun b ↦ ?_
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  have hv1 : (QRegister.block o1 w1 h1 (QRegister.block o2 w2 h2 b)).val =
      o1 + (o2 + b.val) := rfl
  have hv2 : (QRegister.block (o1 + o2) w2 h3 b).val = (o1 + o2) + b.val := rfl
  exact congrArg (basisBits n z) (Fin.ext (by omega))
theorem s3ProjStepHw_spec {p : Fin 256} (hp : p.val ≠ 128)
    {m s : ℕ} (hm : m < 128) (hs : s ≤ 1) (hng : ¬(m = 0 ∧ s = 1)) :
    let ν : ℤ := if s = 1 then -(m : ℤ) else (m : ℤ)
    let st := s3ProjStepHw p m s
    st.1.val ≠ 128 ∧ twosComp8Int st.1 = modWrapCoord 127 (twosComp8Int p) ν ∧
      st.2.1 < 255 ∧ st.2.2 ≤ 1 ∧
      twosComp8Int st.1 - twosComp8Int p =
        (if st.2.2 = 1 then -(st.2.1 : ℤ) else (st.2.1 : ℤ)) ∧
      st.2.1 = (twosComp8Int st.1 - twosComp8Int p).natAbs := by
  intro ν st
  have hpLt := p.isLt
  have hpBds := twosComp8Int_bounds_of_ne128 hp
  let pFlip := if p.val < 128 then p.val + 128 else p.val - 128
  let raw9 := pFlip + (if s = 1 then 127 - m else m) + (if s = 1 then 0 else 127)
  let wHi := if 383 ≤ raw9 then 1 else 0
  let wNoWrap := if 128 ≤ raw9 ∧ raw9 < 383 then 1 else 0
  let xPre := ((raw9 % 256) + (128 + wNoWrap + 2 * wHi)) % 256
  let xOut := if xPre < 128 then xPre + 128 else xPre - 128
  let dMag := if raw9 < 128 ∨ 383 ≤ raw9 then 255 - m else m
  let dSign := (wHi + wNoWrap * s) % 2
  have hst1 : st.1.val = xOut := rfl
  have hst21 : st.2.1 = dMag := rfl
  have hst22 : st.2.2 = dSign := rfl
  have htst : twosComp8Int st.1 = if xOut < 128 then (xOut : ℤ) else (xOut : ℤ) - 256 :=
    (s3TwosComp8Int_eq st.1).trans (by rw [hst1])
  have hLinRaw : (raw9 : ℤ) = twosComp8Int p + ν + 255 ∧ raw9 ≤ 509 ∧ (raw9 < 128 → s = 1) ∧
    (383 ≤ raw9 → s = 0) := by
    dsimp only [raw9, pFlip, ν]
    rw [s3TwosComp8Int_eq p]
    split_ifs
    all_goals omega
  rcases hLinRaw with ⟨hlin, hrle, hLow, hHigh⟩
  have hRawOut : xOut ≠ 128 ∧ twosComp8Int st.1 = if raw9 < 128 then (raw9 : ℤ) else if raw9 <
    383 then (raw9 : ℤ) - 255 else (raw9 : ℤ) - 510 := by
    rw [htst]
    dsimp only [xOut, xPre, wHi, wNoWrap]
    split_ifs
    all_goals omega
  have hDiff : dMag < 255 ∧ dSign ≤ 1 ∧ twosComp8Int st.1 - twosComp8Int p = if dSign = 1 then
    -(dMag : ℤ) else (dMag : ℤ) := by
    rw [hRawOut.2]
    dsimp only [ν] at hlin
    by_cases hr1 : raw9 < 128
    · have hdm : dMag = 255 - m := s3ItePos (Or.inl hr1)
      have hds : dSign = 0 := by
        dsimp only [dSign, wHi, wNoWrap]
        rw [s3IteNeg (by omega), s3IteNeg (by omega)]
        omega
      rw [s3ItePos hr1, hdm, hds]
      rw [s3ItePos (hLow hr1)] at hlin
      omega
    · by_cases hr2 : raw9 < 383
      · have hdm : dMag = m := s3IteNeg (by omega)
        have hds : dSign = s := by
          dsimp only [dSign, wHi, wNoWrap]
          rw [s3IteNeg (by omega), s3ItePos ⟨by omega, hr2⟩]
          omega
        rw [s3IteNeg hr1, s3ItePos hr2, hdm, hds]
        by_cases hs1 : s = 1
        · rw [s3ItePos hs1] at hlin ⊢
          omega
        · rw [s3IteNeg hs1] at hlin ⊢
          omega
      · have hs0 : s = 0 := hHigh (by omega)
        have hdm : dMag = 255 - m := s3ItePos (Or.inr (by omega))
        have hds : dSign = 1 := by
          dsimp only [dSign, wHi, wNoWrap]
          rw [s3ItePos (by omega), s3IteNeg (by omega)]
          omega
        rw [s3IteNeg hr1, s3IteNeg hr2, hdm, hds]
        rw [s3IteNeg (by omega : ¬(s = 1))] at hlin
        omega
  rw [hst1, hst21, hst22]
  exact ⟨hRawOut.1, hRawOut.2.trans (s3ModWrap127_of_raw9 hlin hrle).symm,
    hDiff.1, hDiff.2.1, hDiff.2.2, s3NatAbs_eq_of_signed hDiff.2.2⟩
theorem modWrapCoord127_eq_iff_modFoldCoord {a b ν : ℤ} (ha : -127 ≤ a ∧ a ≤ 127) (_hb : -127 ≤ b ∧
    b ≤ 127) (hν : -127 ≤ ν ∧ ν ≤ 127) :
    a = modWrapCoord 127 b ν ↔ modFoldCoord 127 (a - b) = ν := by
  unfold modFoldCoord modWrapCoord
  omega
theorem s3ProjAxisIdx_lt {k : Fin SpecsAux.SpecMirror.systemQubits} (hk : ¬k.val < 3924) : (k.val -
    3924) / 8 < 3 := by
  have := k.isLt
  change k.val < 3948 at this
  omega
theorem s3ProjBitIdx_lt (n : ℕ) : n % 8 < 8 := Nat.mod_lt n (by decide)
noncomputable def s3UpdateSysProj (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (pNew : Fin 3 →
    Fin 256) : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) :=
    (basisBitsEquiv SpecsAux.SpecMirror.systemQubits).symm fun k ↦ if hk : k.val < 3924 then
    basisBits SpecsAux.SpecMirror.systemQubits x k else basisBits 8
    (pNew ⟨(k.val - 3924) / 8, s3ProjAxisIdx_lt hk⟩) ⟨(k.val - 3924) % 8, s3ProjBitIdx_lt _⟩
theorem s3UpdateSysProj_fields (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (pNew : Fin 3 →
    Fin 256) : (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
    elecAxisField (s3UpdateSysProj x pNew) i w = elecAxisField x i w) ∧ (∀ w : Fin 3,
      projAxisField (s3UpdateSysProj x pNew) w = pNew w) := by
  have hbits (k : Wire SpecsAux.SpecMirror.systemQubits) : basisBits
    SpecsAux.SpecMirror.systemQubits (s3UpdateSysProj x pNew) k =
      if hk : k.val < 3924 then basisBits SpecsAux.SpecMirror.systemQubits x k else
        basisBits 8 (pNew ⟨(k.val - 3924) / 8, s3ProjAxisIdx_lt hk⟩)
      ⟨(k.val - 3924) % 8, s3ProjBitIdx_lt _⟩ :=
    congrFun ((basisBitsEquiv SpecsAux.SpecMirror.systemQubits).apply_symm_apply _) k
  refine ⟨fun i w ↦ ?_, fun w ↦ ?_⟩
  · let axIdx : Fin 654 := ⟨3 * i.val + w.val, by
      have : SpecsAux.SpecMirror.numElectrons = 218 := rfl; have := i.isLt; have := w.isLt; omega⟩
    refine extractIndex_of_bits (elec654Axes axIdx) _ ((elec654Axes axIdx).extractIndex x)
      fun b ↦ ?_
    have hval : (elec654Axes axIdx b).val = 6 * axIdx.val + b.val := rfl
    have := axIdx.isLt; have := b.isLt
    rw [hbits (elec654Axes axIdx b), s3DitePos (by omega), QRegister.basisBits_extractIndex]
  · refine extractIndex_of_bits (proj3Axes w) _ _ fun b ↦ ?_
    have hval : (proj3Axes w b).val = 3924 + 8 * w.val + b.val := rfl
    have := w.isLt; have := b.isLt
    have hwEq : (⟨((proj3Axes w b).val - 3924) / 8, s3ProjAxisIdx_lt (by omega)⟩ : Fin 3) = w :=
      Fin.ext <| by
        rw [Fin.val_mk, hval]
        omega
    have hbEq : (⟨((proj3Axes w b).val - 3924) % 8, s3ProjBitIdx_lt _⟩ : Fin 8) = b :=
      Fin.ext <| by
        rw [Fin.val_mk, hval]
        omega
    rw [hbits (proj3Axes w b), s3DiteNeg (by omega), hwEq, hbEq]
theorem s3UpdateSysProj_eq_iff {x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)} {pNew : Fin 3 →
    Fin 256} : s3UpdateSysProj x pNew = y ↔ (∀ i : Fin
    SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
      elecAxisField x i w = elecAxisField y i w) ∧ (∀ w : Fin 3, pNew w = projAxisField y w) := by
  obtain ⟨he, hp⟩ := s3UpdateSysProj_fields x pNew
  refine ⟨?_, fun ⟨he', hp'⟩ ↦ systemQubits_eq_of_fields
    (fun i w ↦ (he i w).trans (he' i w)) (fun w ↦ (hp w).trans (hp' w))⟩
  rintro rfl
  exact ⟨fun i w ↦ (he i w).symm, fun w ↦ (hp w).symm⟩
theorem s3MomCoreWires_eq (mPayload : ℕ) : momCoreWires mPayload = 3954 + mPayload := by
  dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega
theorem s3MomCore_ge_4034 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : 4034 ≤ momCoreWires mPayload :=
  by
  rw [s3MomCoreWires_eq]; omega
theorem s3SysQubits_eq : SpecsAux.SpecMirror.systemQubits = 3948 := rfl
abbrev s3U22Core {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : QRegister 22 (momCoreWires mPayload) :=
  QRegister.block 3954 22 (by have := s3MomCore_ge_4034 hmPay; omega)
abbrev s3S3Core {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : QRegister 3 (momCoreWires mPayload) :=
  QRegister.block 3976 3 (by have := s3MomCore_ge_4034 hmPay; omega)
abbrev s3C8Core {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : QRegister 8 (momCoreWires mPayload) :=
  QRegister.block 3979 8 (by have := s3MomCore_ge_4034 hmPay; omega)
abbrev s3Coarse33Core {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) : QRegister 33 (momCoreWires mPayload) :=
  QRegister.block 3954 33 (by have := s3MomCore_ge_4034 hmPay; omega)
abbrev s3Fine30Core {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : QRegister 30 (momCoreWires mPayload) :=
  QRegister.block 3987 30 (by have := s3MomCore_ge_4034 hmPay; omega)
abbrev s3BParCore {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Wire (momCoreWires mPayload) :=
  ⟨4017, by have := s3MomCore_ge_4034 hmPay; omega⟩
abbrev s3U16Core {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : QRegister 16 (momCoreWires mPayload) :=
  QRegister.block 4018 16 (by have := s3MomCore_ge_4034 hmPay; omega)
def cRad7Computable (μ : ℕ) : ℕ := cRad38True μ
def s3ProjGridBool (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : Bool := decide
    ((projAxisField x 0).val ≠ 128) && decide ((projAxisField x 1).val ≠ 128) && decide
    ((projAxisField x 2).val ≠ 128)
theorem s3ProjGridBool_eq_true_iff (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : s3ProjGridBool
    x = true ↔ ProjTwosGridState x := by
  unfold s3ProjGridBool ProjTwosGridState
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ w
    fin_cases w
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩
theorem s3ShellMagCoord3_lt_128 (u22 : Fin 4194304) (w : Fin 3) : shellMagCoord3 u22 w < 128 := by
  have hlt := shellMagCoord3_lt u22 w
  have hmu := shellMu3_lt_seven u22
  have hpow : 2 ^ (shellMu3 u22 + 1) ≤ 128 := by
    have hmc : shellMu3 u22 = 0 ∨ shellMu3 u22 = 1 ∨ shellMu3 u22 = 2 ∨
        shellMu3 u22 = 3 ∨ shellMu3 u22 = 4 ∨ shellMu3 u22 = 5 ∨ shellMu3 u22 = 6 := by omega
    rcases hmc with h | h | h | h | h | h | h <;> rw [h] <;> decide
  omega
theorem s3AxisStep_involutive {p : Fin 256} (hp : p.val ≠ 128) {u22 : Fin 4194304} {s3 : Fin 8}
    (hvsh : validShellNu3 u22 s3 = true) (w : Fin 3) :
    (s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)).1.val ≠ 128 ∧ (s3ProjStepHw
    (s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)).1 (shellMagCoord3 u22 w) (signBit3
    (negSign3_22 u22 s3) w)).1 = p ∧ (s3ProjStepHw (s3ProjStepHw p (shellMagCoord3 u22 w)
    (signBit3 s3 w)).1 (shellMagCoord3 u22 w) (signBit3 (negSign3_22 u22 s3) w)).2.1 =
      (s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)).2.1 := by
  have hvsh' : validShellNu3 u22 (negSign3_22 u22 s3) = true :=
    (validShellNu3_negSign3_22 u22 s3).trans hvsh
  have hmLt := s3ShellMagCoord3_lt_128 u22 w
  have hng_of {s : Fin 8} (hv : validShellNu3 u22 s = true) : ¬(shellMagCoord3 u22 w = 0 ∧
    signBit3 s w = 1) := by
    unfold validShellNu3 at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.2 w
  rcases s3ProjStepHw_spec hp hmLt (s3SignBit3_le_one s3 w) (hng_of hvsh) with
    ⟨hp'128, hwrap1, _, _, _, hmag1⟩
  rcases s3ProjStepHw_spec hp'128 hmLt (s3SignBit3_le_one _ w) (hng_of hvsh') with
    ⟨_, hwrap2, _, _, _, hmag2⟩
  have hnu_neg : (if signBit3 (negSign3_22 u22 s3) w = 1 then -(shellMagCoord3 u22 w : ℤ) else
    (shellMagCoord3 u22 w : ℤ)) = -(decodeShellNu3 u22 s3 w) :=
    congrFun (decodeShellNu3_negSign3_22 hvsh) w
  have ha_bds := twosComp8Int_bounds_of_ne128 hp
  have hb_bds := twosComp8Int_bounds_of_ne128 hp'128
  have hna : (decodeShellNu3 u22 s3 w).natAbs < 128 := by
    rw [natAbs_decodeShellNu3]
    exact hmLt
  have hf1 : modFoldCoord 127
    (twosComp8Int (s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)).1 - twosComp8Int p) =
    decodeShellNu3 u22 s3 w :=
    (modWrapCoord127_eq_iff_modFoldCoord hb_bds ha_bds ⟨by omega, by omega⟩).mp hwrap1
  have hf2 : modFoldCoord 127 (twosComp8Int p -
    twosComp8Int (s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)).1) =
    -(decodeShellNu3 u22 s3 w) := by
    unfold modFoldCoord modWrapCoord at hf1 ⊢; omega
  have hback :=
    (modWrapCoord127_eq_iff_modFoldCoord ha_bds hb_bds ⟨by omega, by omega⟩).mpr hf2
  have hst1_eq :
    (s3ProjStepHw (s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)).1 (shellMagCoord3 u22 w)
    (signBit3 (negSign3_22 u22 s3) w)).1 = p :=
    twosComp8Int_injective (hwrap2.trans (by rw [hnu_neg]; exact hback.symm))
  exact ⟨hp'128, hst1_eq,
    by rw [hmag2, hst1_eq, hmag1, ← Int.natAbs_neg]; exact congrArg _ (by ring)⟩
theorem s3Bound_0_22 : 0 + 22 ≤ 33 := by decide
theorem s3Bound_22_3 : 22 + 3 ≤ 33 := by decide
theorem s3Bound_25_8 : 25 + 8 ≤ 33 := by decide
def predCoarseGood33 (α : BitAssignment 33) : ZMod 2 :=
  let idx := (basisBitsEquiv 33).symm α
  let u22 : Fin 4194304 := (QRegister.block 0 22 s3Bound_0_22).extractIndex idx
  let s3 : Fin 8 := (QRegister.block 22 3 s3Bound_22_3).extractIndex idx
  let c8 : Fin 256 := (QRegister.block 25 8 s3Bound_25_8).extractIndex idx
  if coarseGood3Computable u22 s3 c8 then 1 else 0
def predNotZero33 (α : BitAssignment 33) : ZMod 2 :=
  if ((basisBitsEquiv 33).symm α).val = 0 then 0 else 1
noncomputable def h33Unitary : Unitary (2 ^ 33) :=
  (PhaseGradCatalystCore.hadamardAll (QRegister.whole 33)).eval
theorem h33Unitary_def : h33Unitary =
    (PhaseGradCatalystCore.hadamardAll (QRegister.whole 33)).eval := rfl
noncomputable def uOaa33 : Unitary (2 ^ 33) :=
  (h33Unitary * phaseDiagUnitary predNotZero33 * h33Unitary) * phaseDiagUnitary predCoarseGood33
theorem h33Unitary_inv : h33Unitary⁻¹ = h33Unitary :=
  FullSysPrepare6Slot.hadamardAll_eval_inv (QRegister.whole 33)
theorem uOaa33_inv_eq : uOaa33⁻¹ = phaseDiagUnitary predCoarseGood33 *
    (h33Unitary * phaseDiagUnitary predNotZero33 * h33Unitary) := by
  unfold uOaa33
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, phaseDiagUnitary_inv,
    phaseDiagUnitary_inv, h33Unitary_inv]
  simp only [mul_assoc]
noncomputable def uPrep3 {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) : Unitary (2 ^ (momCoreWires mPayload)) := (s3Coarse33Core hmPay).embedUnitary uOaa33
theorem uPrep3_comm_slotBitProj {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) {w : Wire (momCoreWires mPayload)} (hw : w.val < 3954) (b : Fin 2) :
    (uPrep3 hmPay).1 * slotBitProj w b = slotBitProj w b * (uPrep3 hmPay).1 := by
  have hwOut : w ∉ Set.range (s3Coarse33Core hmPay).wires := by
    rintro ⟨idx, hi⟩
    have hv := congrArg Fin.val hi
    dsimp [s3Coarse33Core, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply,
      MomSlots35Slot3ProjNuclearAlt.qreg_block_wires_apply,
      MomSlots35Slot3ProjNuclearAlt.qreg_whole_wires, MomSlots35Slot3ProjNuclearAlt.emb_trans_apply,
      MomSlots35Slot3ProjNuclearAlt.emb_refl_apply,
      MomSlots35Slot3ProjNuclearAlt.emb_mk_apply] at hv
    omega
  rw [uPrep3, QRegister.embedUnitary_val, slotBitProj]
  refine embedMatrix_comm_diagonal_of_outside (s3Coarse33Core hmPay) uOaa33.1 _ (fun i j hOut ↦ ?_)
  rw [hOut w hwOut]
theorem s3IntertwinesCat_mul {N : ℕ} (U_cat P_cat : Operator N)
    {A_cat A_eff B_cat B_eff : Operator N}
    (hA : PhaseGradCatalystCore.IntertwinesCat U_cat P_cat A_cat A_eff)
      (hB : PhaseGradCatalystCore.IntertwinesCat U_cat P_cat B_cat B_eff) :
    PhaseGradCatalystCore.IntertwinesCat U_cat P_cat (A_cat * B_cat) (A_eff * B_eff) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc A_cat B_cat U_cat, Matrix.mul_assoc A_cat _ P_cat, hB.1,
      Matrix.mul_assoc U_cat B_eff P_cat, hB.2.2, ← Matrix.mul_assoc U_cat P_cat B_eff,
      ← Matrix.mul_assoc A_cat _ B_eff, ← Matrix.mul_assoc A_cat U_cat P_cat, hA.1]
    simp only [Matrix.mul_assoc, ← hB.2.2]
  · rw [Matrix.mul_assoc, hB.2.1, ← Matrix.mul_assoc, hA.2.1, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hB.2.2, ← Matrix.mul_assoc, hA.2.2, Matrix.mul_assoc]
def s3SamePrefix3954 {mPayload : ℕ} (z g : Fin (2 ^ (momCoreWires mPayload))) : Prop := ∀ w :
    Wire (momCoreWires mPayload), w.val < 3954 → basisBits (momCoreWires mPayload) z w =
    basisBits (momCoreWires mPayload) g w
noncomputable instance instDecidableS3SamePrefix3954 {mPayload : ℕ}
    (z g : Fin (2 ^ (momCoreWires mPayload))) : Decidable (s3SamePrefix3954 z g) :=
  Classical.propDecidable _
theorem s3BasisBits_zero_wire {q : ℕ} (w : Wire q) : basisBits q (0 : Fin (2 ^ q)) w = 0 := by
  rw [basisBits_eq_testBit]
  simp
open Classical in
private theorem s3HadamardAll_mulVec_ket_zero {K : ℕ} :
    ∀ {m : ℕ} (r : QRegister m K) (β : BitAssignment K), (∀ i : Fin m, β (r i) = 0) →
      ∀ g : Fin (2 ^ K),
        ((PhaseGradCatalystCore.hadamardAll r).eval.1.mulVec (Slot3CleanPrim.ket β)) g =
          if ∀ w : Wire K, w ∉ Set.range r.wires → basisBits K g w = β w then
            (((1 / √2 : ℝ) ^ m : ℝ) : ℂ) else 0
  | 0, r, β, _, g => by
      rw [show (PhaseGradCatalystCore.hadamardAll r).eval.1 = 1 by
        unfold PhaseGradCatalystCore.hadamardAll; rw [List.ofFn_zero]; rfl,
        Matrix.one_mulVec, Slot3CleanPrim.ket_apply_eq]
      have hiff : g = (basisBitsEquiv K).symm β ↔ ∀ w : Wire K,
        w ∉ Set.range r.wires → basisBits K g w = β w :=
        ⟨fun hEq w _ ↦ (congrArg (fun x ↦ basisBits K x w) hEq).trans
          (congrFun (Slot3CleanPrim.basisBits_symm_apply_s1 β) w),
         fun hall ↦ (basisBitsEquiv K).injective (funext fun w ↦
          (hall w fun ⟨i, _⟩ ↦ Fin.elim0 i).trans
            (congrFun (Slot3CleanPrim.basisBits_symm_apply_s1 β) w).symm)⟩
      by_cases hall : ∀ w : Wire K, w ∉ Set.range r.wires → basisBits K g w = β w
      · rw [s3ItePos (hiff.mpr hall), s3ItePos hall]; norm_num
      · rw [s3IteNeg (mt hiff.mp hall), s3IteNeg hall]
  | m + 1, r, β, hz, g => by
      let rTail := r.slice 1 m (by omega)
      have hw0 : r 0 ∉ Set.range rTail.wires := fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j
        (r.wires.injective ((Slot3CleanPrim.slice_one_succ r _ j).symm.trans hj))
      have hz0 : β (r 0) = 0 := hz 0
      have hH : ((Circuit.H (r 0)).eval.1.mulVec (Slot3CleanPrim.ket β)) = ((1 / √2 : ℝ) : ℂ) •
          (Slot3CleanPrim.ket β + Slot3CleanPrim.ket (Function.update β (r 0) 1)) := by
        rw [eval_H_ket,
          show Function.update β (r 0) 0 = β by rw [← hz0, Function.update_eq_self],
          show (β (r 0)).val = 0 by rw [hz0]; rfl, s3ItePos (rfl : (0 : ℕ) = 0), ← smul_add]
      have hz_b0 (i : Fin m) : β (rTail i) = 0 :=
        (congrArg β (Slot3CleanPrim.slice_one_succ r _ i)).trans (hz i.succ)
      have hz_b1 (i : Fin m) : (Function.update β (r 0) 1) (rTail i) = 0 := by
        rw [Function.update_of_ne (fun h ↦ hw0 ⟨i, h⟩)]; exact hz_b0 i
      have hStep : (PhaseGradCatalystCore.hadamardAll r).eval.1 =
        (PhaseGradCatalystCore.hadamardAll rTail).eval.1 * (Circuit.H (r 0)).eval.1 := by
        unfold PhaseGradCatalystCore.hadamardAll
        rw [List.ofFn_succ, show (fun i : Fin m ↦ Circuit.H (r i.succ)) =
          (fun i : Fin m ↦ Circuit.H (rTail i)) from
          funext fun i ↦ congrArg Circuit.H (Slot3CleanPrim.slice_one_succ r _ i).symm]; rfl
      rw [hStep, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.mulVec_add,
        Pi.smul_apply, Pi.add_apply, s3HadamardAll_mulVec_ket_zero rTail β hz_b0 g,
          s3HadamardAll_mulVec_ket_zero rTail (Function.update β (r 0) 1) hz_b1 g]
      have hRE (w) : w ∈ Set.range r.wires ↔ w = r 0 ∨ w ∈ Set.range rTail.wires := by
        constructor
        · rintro ⟨idx, rfl⟩
          cases idx using Fin.cases with
          | zero => exact Or.inl rfl
          | succ j => exact Or.inr ⟨j, Slot3CleanPrim.slice_one_succ r _ j⟩
        · rintro (rfl | ⟨j, rfl⟩)
          · exact ⟨0, rfl⟩
          · exact ⟨j.succ, (Slot3CleanPrim.slice_one_succ r _ j).symm⟩
      have hTI (β' : BitAssignment K) (hβ' : ∀ w, w ≠ r 0 → β' w = β w) : (∀ w : Wire K,
        w ∉ Set.range rTail.wires → basisBits K g w = β' w) ↔
          (∀ w : Wire K,
            w ∉ Set.range r.wires → basisBits K g w = β w) ∧ basisBits K g (r 0) = β' (r 0) :=
        ⟨fun h ↦ ⟨fun w hw ↦ (h w fun ht ↦ hw ((hRE w).mpr (Or.inr ht))).trans
          (hβ' w fun heq ↦ hw (heq ▸ ⟨0, rfl⟩)), h (r 0) hw0⟩,
         fun ⟨hout, hr0⟩ w hw ↦ if hw0' : w = r 0 then hw0' ▸ hr0 else
          (hout w fun hr ↦ (hRE w).mp hr |>.elim hw0' hw).trans (hβ' w hw0').symm⟩
      by_cases hout : ∀ w : Wire K, w ∉ Set.range r.wires → basisBits K g w = β w
      · rcases Slot3CleanPrim.zmod2_eq_or (basisBits K g (r 0)) with hb | hb
        · rw [s3ItePos hout, s3ItePos ((hTI β fun _ _ ↦ rfl).mpr ⟨hout, hb.trans hz0.symm⟩),
            s3IteNeg (fun h ↦ zero_ne_one (hb ▸ Function.update_self (r 0) (1 : ZMod 2) β ▸
              ((hTI _ fun _ hw ↦ Function.update_of_ne hw 1 β).mp h).2)),
            add_zero, smul_eq_mul, ← Complex.ofReal_mul, pow_succ']
        · rw [s3ItePos hout, s3IteNeg (fun h ↦ one_ne_zero (hb ▸ hz0 ▸
              ((hTI β fun _ _ ↦ rfl).mp h).2)),
            s3ItePos ((hTI _ fun _ hw ↦ Function.update_of_ne hw 1 β).mpr
              ⟨hout, by rw [Function.update_self, hb]⟩),
            zero_add, smul_eq_mul, ← Complex.ofReal_mul, pow_succ']
      · rw [s3IteNeg hout, s3IteNeg (fun h ↦ hout ((hTI β fun _ _ ↦ rfl).mp h).1),
          s3IteNeg (fun h ↦ hout ((hTI _ fun _ hw ↦ Function.update_of_ne hw 1 β).mp h).1),
          add_zero, smul_zero]
theorem s3Coarse33_sub22 {j : Fin 33} (h1 : ¬j.val < 22) (h2 : j.val < 25) : j.val - 22 < 3 := by
  omega
theorem s3Coarse33_sub25 {j : Fin 33} (h2 : ¬j.val < 25) : j.val - 25 < 8 := by
  have := j.isLt; omega
noncomputable def coarse33EquivToFun (k : Fin (2 ^ 33)) : Fin 4194304 × Fin 8 × Fin 256 :=
    ((QRegister.block 0 22 s3Bound_0_22).extractIndex k, (QRegister.block 22 3
    s3Bound_22_3).extractIndex k, (QRegister.block 25 8 s3Bound_25_8).extractIndex k)
noncomputable def coarse33EquivInvFun (t : Fin 4194304 × Fin 8 × Fin 256) : Fin (2 ^ 33) :=
    (basisBitsEquiv 33).symm fun j ↦ if hj1 : j.val < 22 then basisBits 22 t.1 ⟨j.val, hj1⟩
    else if hj2 : j.val < 25 then basisBits 3 t.2.1 ⟨j.val - 22, s3Coarse33_sub22 hj1 hj2⟩
    else basisBits 8 t.2.2 ⟨j.val - 25, s3Coarse33_sub25 hj2⟩
noncomputable def coarse33Equiv : Fin (2 ^ 33) ≃ Fin 4194304 × Fin 8 × Fin 256 :=
  ⟨coarse33EquivToFun, coarse33EquivInvFun,
    fun k ↦ (basisBitsEquiv 33).injective <| funext fun j ↦ by
      change basisBits 33 _ j = basisBits 33 k j
      have := j.isLt; dsimp only [coarse33EquivInvFun]
      rw [Slot3CleanPrim.basisBits_symm_apply_s1]; split_ifs with h1 h2
      all_goals exact basisBits_extractIndex_block_eq _ k _ (by omega),
    fun ⟨u22, s3, c8⟩ ↦ by
      refine Prod.ext
        (extractIndex_of_bits (QRegister.block 0 22 s3Bound_0_22) _ u22 fun b ↦ ?_)
        (Prod.ext (extractIndex_of_bits (QRegister.block 22 3 s3Bound_22_3) _ s3 fun b ↦ ?_)
          (extractIndex_of_bits (QRegister.block 25 8 s3Bound_25_8) _ c8 fun b ↦ ?_))
      all_goals
        have := b.isLt
        simp only [coarse33EquivInvFun, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply,
          Slot3CleanPrim.basisBits_symm_apply_s1]
        split_ifs
        all_goals try omega
        refine congrArg (basisBits _ _) (Fin.ext ?_)
        dsimp
        omega⟩
theorem uOaa33_row_sum_good {k : Fin (2 ^ 33)} (hk : coarseGood3 (coarse33Equiv k).1
    (coarse33Equiv k).2.1 (coarse33Equiv k).2.2 = true) : (∑ l : Fin (2 ^ 33),
      uOaa33.1 k l) = ((3 - 4 * coulombCoarse8PreOAAProb 127 8192 : ℝ) : ℂ) := by
  have hz0_ket : ∀ j : Fin (2 ^ 33), h33Unitary.1 j 0 = (((1 / √2 : ℝ) ^ 33 : ℝ) : ℂ) := fun j ↦ by
    have hmv := s3HadamardAll_mulVec_ket_zero (QRegister.whole 33) (basisBits 33 0)
      (fun _ ↦ s3BasisBits_zero_wire _) j
    rw [s3ItePos fun w hw ↦ (hw ⟨w, rfl⟩).elim] at hmv
    have hcol : ((PhaseGradCatalystCore.hadamardAll (QRegister.whole 33)).eval.1.mulVec
        (Slot3CleanPrim.ket (basisBits 33 0))) j = h33Unitary.1 j 0 := by
      rw [← h33Unitary_def, ← Slot3CleanPrim.single_eq_ket, Matrix.mulVec_single_one,
        Matrix.col_apply]
    exact hcol.symm.trans hmv
  have h33_sa : h33Unitary.1ᴴ = h33Unitary.1 :=
    (s3Unitary_inv_val h33Unitary).symm.trans (congrArg Subtype.val h33Unitary_inv)
  have hz0_row : ∀ l : Fin (2 ^ 33), h33Unitary.1 0 l = (((1 / √2 : ℝ) ^ 33 : ℝ) : ℂ) := fun l ↦ by
    rw [← congrFun (congrFun h33_sa 0) l, Matrix.conjTranspose_apply, hz0_ket l]
    exact Complex.conj_ofReal _
  have h33_sq : h33Unitary.1 * h33Unitary.1 = 1 := by
    have h1 : (h33Unitary⁻¹ * h33Unitary).1 = 1 :=
      congrArg Subtype.val (inv_mul_cancel h33Unitary)
    rwa [h33Unitary_inv] at h1
  have hrefl_entry : ∀ l : Fin (2 ^ 33),
    (h33Unitary * phaseDiagUnitary predNotZero33 * h33Unitary).1 k l =
      (2 : ℂ) * (((1 / 2 : ℝ) ^ 33 : ℝ) : ℂ) - if k = l then 1 else 0 := by
    intro l
    have hd0 : ∀ y : Fin (2 ^ 33),
      ((-1 : ℂ) ^ (predNotZero33 (basisBits 33 y)).val) = (if y = 0 then (2 : ℂ) else 0) - 1 := by
      intro y
      unfold predNotZero33
      rw [symm_basisBits_apply _]
      by_cases hy0 : y = 0
      · subst hy0
        have hvz : (0 : Fin (2 ^ 33)).val = 0 := Fin.val_zero (2 ^ 33)
        rw [s3ItePos hvz, s3ItePos rfl]; norm_num
      · have hv0 : y.val ≠ 0 := fun hv ↦ hy0 (Fin.ext hv)
        rw [s3IteNeg hv0, s3IteNeg hy0]; norm_num
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    change (h33Unitary.1 * Matrix.diagonal (fun y ↦
      (-1 : ℂ) ^ (predNotZero33 (basisBits 33 y)).val) *
      h33Unitary.1) k l = _
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal, hd0, mul_sub, sub_mul, Finset.sum_sub_distrib]
    have hsum1 : (∑ x : Fin (2 ^ 33),
      h33Unitary.1 k x * (if x = 0 then (2 : ℂ) else 0) * h33Unitary.1 x l) = (2 : ℂ) *
      (((1 / 2 : ℝ) ^ 33 : ℝ) : ℂ) := by
      have hite : ∀ x : Fin (2 ^ 33),
        h33Unitary.1 k x * (if x = 0 then (2 : ℂ) else 0) * h33Unitary.1 x l =
          if x = 0 then (2 : ℂ) * h33Unitary.1 k 0 * h33Unitary.1 0 l else 0 := by
        intro x; by_cases hx : x = 0
        · subst hx; simp [mul_comm]
        · simp [hx]
      simp_rw [hite]
      rw [Finset.sum_ite_eq', s3ItePos (Finset.mem_univ _), hz0_ket k, hz0_row l]
      rw [mul_assoc, ← Complex.ofReal_mul, ← mul_pow, show (1 / √2 : ℝ) * (1 / √2 : ℝ) = 1 / 2 by
        field_simp
        exact (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)).symm]
    have hsum2 : (∑ x : Fin (2 ^ 33), h33Unitary.1 k x * 1 * h33Unitary.1 x l) =
        if k = l then (1 : ℂ) else 0 := by
      simp_rw [mul_one]
      rw [← Matrix.mul_apply, h33_sq, Matrix.one_apply]
    rw [hsum1, hsum2]
  let dG : Fin (2 ^ 33) → ℂ := fun l ↦
    if coarseGood3 (coarse33Equiv l).1 (coarse33Equiv l).2.1 (coarse33Equiv l).2.2 = true then
      -1 else 1
  have hdG_eq : ∀ l : Fin (2 ^ 33), ((-1 : ℂ) ^ (predCoarseGood33 (basisBits 33 l)).val) = dG l :=
    by
    intro l
    unfold predCoarseGood33
    rw [symm_basisBits_apply l]
    change ((-1 : ℂ) ^ (if coarseGood3Computable (coarse33Equiv l).1
      (coarse33Equiv l).2.1 (coarse33Equiv l).2.2 = true then (1 : ZMod 2) else 0).val) = dG l
    rw [coarseGood3Computable_eq_coarseGood3]
    by_cases hg : coarseGood3 (coarse33Equiv l).1 (coarse33Equiv l).2.1 (coarse33Equiv l).2.2 = true
    · rw [s3ItePos hg]; simp [dG, hg]
    · rw [s3IteNeg hg]; simp [dG, hg]
  have hOaaEntry : ∀ l : Fin (2 ^ 33),
    uOaa33.1 k l = ((2 : ℂ) * (((1 / 2 : ℝ) ^ 33 : ℝ) : ℂ)) * dG l - if k = l then dG l else 0 := by
    intro l
    unfold uOaa33
    change ((h33Unitary * phaseDiagUnitary predNotZero33 * h33Unitary).1 *
      Matrix.diagonal (fun y ↦ (-1 : ℂ) ^ (predCoarseGood33 (basisBits 33 y)).val)) k l = _
    rw [Matrix.mul_diagonal, hrefl_entry l, hdG_eq l, sub_mul]
    by_cases hkl : k = l
    · rw [s3ItePos hkl, s3ItePos hkl, one_mul]
    · rw [s3IteNeg hkl, s3IteNeg hkl, zero_mul]
  simp_rw [hOaaEntry, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq, s3ItePos (Finset.mem_univ k)]
  have hdG_k : dG k = -1 := by simp [dG, hk]
  have hsum_dG : (∑ l : Fin (2 ^ 33),
    dG l) = (((2 ^ 33 : ℕ) : ℂ) - 2 * ((Finset.univ.filter fun t : Fin 4194304 × Fin 8 × Fin 256 ↦
      coarseGood3 t.1 t.2.1 t.2.2 = true).card : ℂ)) := by
    rw [Fintype.sum_equiv coarse33Equiv _
      (fun t : Fin 4194304 × Fin 8 × Fin 256 ↦ dG (coarse33Equiv.symm t))
      (fun l ↦ (congrArg dG (coarse33Equiv.symm_apply_apply l)).symm)]
    have h12 : ∀ t : Fin 4194304 × Fin 8 × Fin 256,
      dG (coarse33Equiv.symm t) = 1 - if coarseGood3 t.1 t.2.1 t.2.2 = true then (2 : ℂ) else 0 :=
      by
      intro t
      dsimp only [dG]
      rw [coarse33Equiv.apply_symm_apply]
      by_cases ht : coarseGood3 t.1 t.2.1 t.2.2 = true
      · rw [s3ItePos ht, s3ItePos ht]; norm_num
      · rw [s3IteNeg ht, s3IteNeg ht]; norm_num
    rw [Finset.sum_congr rfl (fun t _ ↦ h12 t), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      nsmul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    generalize (Finset.univ.filter fun x : Fin 4194304 × Fin 8 × Fin 256 ↦
      coarseGood3 x.1 x.2.1 x.2.2 = true).card = M
    have hcard33 : (((4194304 * (8 * 256) : ℕ) : ℂ)) = ((2 ^ 33 : ℕ) : ℂ) := by norm_num
    rw [hcard33, mul_comm (M : ℂ) 2]
  rw [hsum_dG, hdG_k]
  have hcard := card_coarseGood3_div_two_pow_33_eq
  rw [Fintype.card_subtype] at hcard
  generalize (Finset.univ.filter fun x : Fin 4194304 × Fin 8 × Fin 256 ↦
    coarseGood3 x.1 x.2.1 x.2.2 = true).card = N at hcard ⊢
  have hN_real : (N : ℝ) = coulombCoarse8PreOAAProb 127 8192 * (2 ^ 33 : ℝ) :=
    (div_eq_iff (by norm_num : ((2 ^ 33 : ℝ)) ≠ 0)).mp hcard
  have hreal_eq : (2 : ℝ) * (1 / 2 : ℝ) ^ 33 * ((2 ^ 33 : ℝ) - 2 * (N : ℝ)) - (-1 : ℝ) = 3 - 4 *
    coulombCoarse8PreOAAProb 127 8192 := by
    rw [hN_real]
    norm_num
    ring
  have hcast : (2 : ℂ) * (((1 / 2 : ℝ) ^ 33 : ℝ) : ℂ) * (((2 ^ 33 : ℕ) : ℂ) - 2 * (N : ℂ)) -
    (-1 : ℂ) =
      (((2 : ℝ) * (1 / 2 : ℝ) ^ 33 * ((2 ^ 33 : ℝ) - 2 * (N : ℝ)) - (-1 : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, hreal_eq]
private theorem momAnc_bit_zero_of_ge3951 {mPayload : ℕ} {g : Fin (2 ^ (momCoreWires mPayload))}
    (hgAnc : (momAncReg mPayload).extractIndex g =
    coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) (w : Wire (momCoreWires mPayload))
      (hw : 3951 ≤ w.val) :
    basisBits (momCoreWires mPayload) g w = 0 := by
  let idxSel : Fin (momSelWires mPayload) := ⟨w.val - 3948, by
    have := w.isLt; have := s3MomCoreWires_eq mPayload; dsimp [momSelWires]; omega⟩
  have hwEq : w = momAncReg mPayload idxSel :=
    Fin.ext (by change w.val = 3948 + (w.val - 3948); omega)
  have hnot : idxSel ∉ (momCoin3Sel mPayload).image := fun hmem ↦ by
    rw [QRegister.image] at hmem
    rcases Finset.mem_map.mp hmem with ⟨j, _, hj⟩
    have hv : 0 + j.val = w.val - 3948 := congrArg Fin.val hj
    have := j.isLt; omega
  rw [hwEq, ← QRegister.basisBits_extractIndex, hgAnc, basisBits_coinSelOutcome_outside _ _ hnot]
theorem s3EmbedSub_mul_coreHadamard_apply {k mPayload : ℕ}
    (rSub : QRegister k (momCoreWires mPayload))
    (hrSub : ∀ idx : Fin k, 3954 ≤ (rSub idx).val) (U : Unitary (2 ^ k))
    (z g : Fin (2 ^ (momCoreWires mPayload))) (hgAnc : (momAncReg mPayload).extractIndex g =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) :
    (rSub.embedUnitary U * coreHadamardMom mPayload).1 z g = if s3SamePrefix3954 z g then
    (∑ l : Fin (2 ^ k), U.1 (rSub.extractIndex z) l) * (((1 / √2 : ℝ) ^ mPayload : ℝ) : ℂ) else 0 :=
      by
  have hgPayZero (i : Fin mPayload) : basisBits (momCoreWires mPayload) g (momPayloadReg mPayload i)
    = 0 :=
    momAnc_bit_zero_of_ge3951 hgAnc _ (by change 3951 ≤ 3954 + i.val; omega)
  have hHad (y : Fin (2 ^ (momCoreWires mPayload))) : (coreHadamardMom mPayload).1 y g =
      if s3SamePrefix3954 y g then (((1 / √2 : ℝ) ^ mPayload : ℝ) : ℂ) else 0 := by
    have hmv := s3HadamardAll_mulVec_ket_zero (momPayloadReg mPayload)
      (basisBits (momCoreWires mPayload) g) hgPayZero y
    rw [← Slot3CleanPrim.single_eq_ket, Matrix.mulVec_single_one, Matrix.col_apply] at hmv
    have hiff : (∀ w : Wire (momCoreWires mPayload), w ∉ Set.range (momPayloadReg
        mPayload).wires → basisBits (momCoreWires mPayload) y w =
          basisBits (momCoreWires mPayload) g w) ↔ s3SamePrefix3954 y g :=
      ⟨fun h w hw ↦ h w fun ⟨i, hi⟩ ↦ by
        have hv : 3954 + i.val = w.val := congrArg Fin.val hi; omega,
       fun h w hwOut ↦ if hw : w.val < 3954 then h w hw else
        (hwOut ⟨⟨w.val - 3954, by have := w.isLt; have := s3MomCoreWires_eq mPayload; omega⟩,
          Fin.ext (by change 3954 + (w.val - 3954) = w.val; omega)⟩).elim⟩
    rw [hmv]; by_cases hp : s3SamePrefix3954 y g
    · rw [s3ItePos (hiff.mpr hp), s3ItePos hp]
    · rw [s3IteNeg (mt hiff.mp hp), s3IteNeg hp]
  have hRow (y : Fin (2 ^ (momCoreWires mPayload))) : (rSub.embedUnitary U).1 z y = ∑ l : Fin
      (2 ^ k),
        U.1 (rSub.extractIndex z) l *
        Slot3CleanPrim.ket
        (Slot3CleanPrim.writeReg (basisBits (momCoreWires mPayload) z) rSub (basisBits k l)) y := by
    have hc :
      ((rSub.embedMatrix U.1ᴴ).mulVec (Slot3CleanPrim.ket (basisBits (momCoreWires mPayload) z))) y
      = star ((rSub.embedUnitary U).1 z y) := by
      rw [← Slot3CleanPrim.single_eq_ket, Matrix.mulVec_single_one, Matrix.col_apply,
        QRegister.embedMatrix_conjTranspose, Matrix.conjTranspose_apply,
        QRegister.embedUnitary_val]
    have hmv := congrFun (Slot3CleanPrim.embedMatrix_mulVec_ket rSub U.1ᴴ
      (basisBits (momCoreWires mPayload) z)) y
    have hloc : Slot3CleanPrim.localIdx rSub (basisBits (momCoreWires mPayload) z) =
        rSub.extractIndex z := (basisBitsEquiv k).injective (funext fun i ↦
      (congrFun (Slot3CleanPrim.basisBits_symm_apply_s1 _) i).trans
        (QRegister.basisBits_extractIndex rSub z i).symm)
    rw [← star_star ((rSub.embedUnitary U).1 z y), ← hc, hmv, hloc, Finset.sum_apply, star_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', Matrix.conjTranspose_apply, star_star,
      Slot3CleanPrim.ket_apply_eq]
    congr 1; split_ifs <;> simp
  rw [Submonoid.coe_mul, Matrix.mul_apply]
  simp_rw [hRow, Finset.sum_mul]; rw [Finset.sum_comm]
  have hinter (l : Fin (2 ^ k)) : (∑ y : Fin (2 ^ (momCoreWires mPayload)), U.1
      (rSub.extractIndex z) l * Slot3CleanPrim.ket (Slot3CleanPrim.writeReg (basisBits
      (momCoreWires mPayload) z) rSub (basisBits k l)) y * (coreHadamardMom mPayload).1 y g) =
        U.1 (rSub.extractIndex z) l * if s3SamePrefix3954 z g then
      (((1 / √2 : ℝ) ^ mPayload : ℝ) : ℂ) else 0 := by
    let y_l := (basisBitsEquiv (momCoreWires mPayload)).symm (Slot3CleanPrim.writeReg
      (basisBits (momCoreWires mPayload) z) rSub (basisBits k l))
    rw [Finset.sum_eq_single y_l (fun y _ hy ↦ by simp [hy, y_l])
      (fun hm ↦ (hm (Finset.mem_univ _)).elim)]
    rw [Slot3CleanPrim.ket_apply_eq, s3ItePos (rfl : y_l = _), mul_one, hHad y_l]
    have hpref_iff : s3SamePrefix3954 y_l g ↔ s3SamePrefix3954 z g :=
      forall₂_congr fun w hw ↦ by
        have hnot : w ∉ Set.range rSub.wires := fun ⟨idx, hi⟩ ↦ by
          have := congrArg Fin.val hi; have := hrSub idx; omega
        dsimp [y_l]; rw [Slot3CleanPrim.basisBits_symm_apply_s1,
          Slot3CleanPrim.writeReg_apply_of_not_mem _ _ _ _ hnot]
    by_cases hp : s3SamePrefix3954 z g
    · rw [s3ItePos (hpref_iff.mpr hp), s3ItePos hp]
    · rw [s3IteNeg (mt hpref_iff.mp hp), s3IteNeg hp]
  simp_rw [hinter, ← Finset.sum_mul]
  by_cases hp : s3SamePrefix3954 z g
  · rw [s3ItePos hp, s3ItePos hp]
  · rw [s3IteNeg hp, s3IteNeg hp, mul_zero]
theorem uPrep3_mul_coreHadamard_apply {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z g : Fin (2 ^ (momCoreWires mPayload))) (hgAnc : (momAncReg mPayload).extractIndex g =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) :
    (uPrep3 hmPay * coreHadamardMom mPayload).1 z g = if s3SamePrefix3954 z g then (∑ l : Fin
    (2 ^ 33),
      uOaa33.1 ((s3Coarse33Core hmPay).extractIndex z) l) * (((1 / √2 : ℝ) ^ mPayload : ℝ) : ℂ) else
      0 :=
  s3EmbedSub_mul_coreHadamard_apply (s3Coarse33Core hmPay)
    (fun idx ↦
      by dsimp [s3Coarse33Core, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply,
      MomSlots35Slot3ProjNuclearAlt.qreg_block_wires_apply,
      MomSlots35Slot3ProjNuclearAlt.qreg_whole_wires, MomSlots35Slot3ProjNuclearAlt.emb_trans_apply,
      MomSlots35Slot3ProjNuclearAlt.emb_refl_apply,
      MomSlots35Slot3ProjNuclearAlt.emb_mk_apply]; omega)
    uOaa33 z g hgAnc
theorem s3SamePrefix3954_coin6_iff {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {z g : Fin (2 ^ (momCoreWires mPayload))}
    (hgAnc : (momAncReg mPayload).extractIndex g =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) :
    s3SamePrefix3954 z g ↔
      (momSysReg mPayload).extractIndex z = (momSysReg mPayload).extractIndex g ∧
      (momCoinReg mPayload).extractIndex z = 6 ∧
      basisBits (momCoreWires mPayload) z
        ⟨3951, by have := s3MomCore_ge_4034 hmPay; omega⟩ = 0 ∧
      basisBits (momCoreWires mPayload) z
        ⟨3952, by have := s3MomCore_ge_4034 hmPay; omega⟩ = 0 ∧
      basisBits (momCoreWires mPayload) z
        ⟨3953, by have := s3MomCore_ge_4034 hmPay; omega⟩ = 0 := by
  have hgCoin (j : Fin 3) : basisBits (momCoreWires mPayload) g (momCoinReg mPayload j) =
    basisBits 3 (6 : Fin 8) j := by
    have hwEq : momCoinReg mPayload j = momAncReg mPayload (momCoin3Sel mPayload j) :=
      Fin.ext (by change 3948 + j.val = 3948 + (0 + j.val); omega)
    rw [hwEq, ← QRegister.basisBits_extractIndex, hgAnc, basisBits_coinSelOutcome_coin]
    rfl
  constructor
  · intro hp
    refine ⟨extractIndex_of_bits (momSysReg mPayload) z _ fun b ↦
        (hp _ (by
          have hb : b.val < 3948 := b.isLt
          change 0 + b.val < 3954
          omega)).trans (QRegister.basisBits_extractIndex _ g b).symm,
      extractIndex_of_bits (momCoinReg mPayload) z 6 fun j ↦
        (hp _ (by have := j.isLt; change 3948 + j.val < 3954; omega)).trans (hgCoin j),
      (hp _ (by dsimp; omega)).trans (momAnc_bit_zero_of_ge3951 hgAnc _ (by dsimp; omega)),
      (hp _ (by dsimp; omega)).trans (momAnc_bit_zero_of_ge3951 hgAnc _ (by dsimp; omega)),
      (hp _ (by dsimp; omega)).trans (momAnc_bit_zero_of_ge3951 hgAnc _ (by dsimp; omega))⟩
  · rintro ⟨hSys, hCoin, hb51, hb52, hb53⟩ w hw
    by_cases hwSys : w.val < 3948
    · rw [show w = momSysReg mPayload ⟨w.val, hwSys⟩ from
        Fin.ext (by change w.val = 0 + w.val; omega),
        ← QRegister.basisBits_extractIndex, hSys, QRegister.basisBits_extractIndex]
    · by_cases hwCoin : w.val < 3951
      · let j : Fin 3 := ⟨w.val - 3948, by omega⟩
        rw [show w = momCoinReg mPayload j from
          Fin.ext (by change w.val = 3948 + (w.val - 3948); omega),
          ← QRegister.basisBits_extractIndex, hCoin, hgCoin j]
      · rcases (by omega : w.val = 3951 ∨ w.val = 3952 ∨ w.val = 3953) with h | h | h
        · rw [show w = ⟨3951, by have := s3MomCore_ge_4034 hmPay; omega⟩ from Fin.ext h, hb51,
            momAnc_bit_zero_of_ge3951 hgAnc _ (by dsimp; omega)]
        · rw [show w = ⟨3952, by have := s3MomCore_ge_4034 hmPay; omega⟩ from Fin.ext h, hb52,
            momAnc_bit_zero_of_ge3951 hgAnc _ (by dsimp; omega)]
        · rw [show w = ⟨3953, by have := s3MomCore_ge_4034 hmPay; omega⟩ from Fin.ext h, hb53,
            momAnc_bit_zero_of_ge3951 hgAnc _ (by dsimp; omega)]
noncomputable def s3FlipBParFun {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (z : Fin (2 ^ (momCoreWires mPayload))) : Fin (2 ^ (momCoreWires mPayload)) :=
  (basisBitsEquiv (momCoreWires mPayload)).symm
    (Function.update (basisBits (momCoreWires mPayload) z) (s3BParCore hmPay)
      (basisBits (momCoreWires mPayload) z (s3BParCore hmPay) + 1))
theorem s3FlipBParFun_involutive {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) : Function.Involutive (s3FlipBParFun hmPay) := fun z ↦
  (basisBitsEquiv (momCoreWires mPayload)).injective <| funext fun w ↦ by
    change basisBits (momCoreWires mPayload) _ w = basisBits (momCoreWires mPayload) z w
    dsimp only [s3FlipBParFun]; rw [Slot3CleanPrim.basisBits_symm_apply_s1]
    by_cases hw : w = s3BParCore hmPay
    · subst hw; simp only [Function.update_self, Slot3CleanPrim.basisBits_symm_apply_s1]
      rcases Slot3CleanPrim.zmod2_eq_or
          (basisBits (momCoreWires mPayload) z (s3BParCore hmPay)) with h | h <;>
        rw [h] <;> decide
    · rw [Function.update_of_ne hw, Slot3CleanPrim.basisBits_symm_apply_s1,
        Function.update_of_ne hw]
noncomputable def s3FlipBParPerm {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Equiv.Perm
    (Fin (2 ^ (momCoreWires mPayload))) := ⟨s3FlipBParFun hmPay, s3FlipBParFun hmPay,
    s3FlipBParFun_involutive hmPay, s3FlipBParFun_involutive hmPay⟩
abbrev Slot3PayloadTuple (mPayload : ℕ) :=
  Fin 4194304 × Fin 8 × Fin 256 × Fin (2 ^ 30) × Fin 2 × Fin 65536 × Fin (2 ^ (mPayload - 80))
theorem s3CoreBound_rem (mPayload : ℕ) (hmPay : 80 ≤ mPayload) : 4034 + (mPayload - 80) ≤
    momCoreWires mPayload := by
  have := s3MomCoreWires_eq mPayload; omega
noncomputable def s3Prefix3954ToFunVal {mPayload : ℕ} (g : Fin (2 ^ (momCoreWires mPayload)))
    (t : Slot3PayloadTuple mPayload) : Fin (2 ^ (momCoreWires mPayload)) :=
  (basisBitsEquiv (momCoreWires mPayload)).symm fun w ↦
    if h0 : w.val < 3954 then basisBits (momCoreWires mPayload) g w
    else if h1 : w.val < 3976 then basisBits 22 t.1 ⟨w.val - 3954, by omega⟩
    else if h2 : w.val < 3979 then basisBits 3 t.2.1 ⟨w.val - 3976, by omega⟩
    else if h3 : w.val < 3987 then basisBits 8 t.2.2.1 ⟨w.val - 3979, by omega⟩
    else if h4 : w.val < 4017 then basisBits 30 t.2.2.2.1 ⟨w.val - 3987, by omega⟩
    else if h5 : w.val = 4017 then (if t.2.2.2.2.1.val = 1 then 1 else 0)
    else if h6 : w.val < 4034 then basisBits 16 t.2.2.2.2.2.1 ⟨w.val - 4018, by omega⟩
    else basisBits (mPayload - 80) t.2.2.2.2.2.2 ⟨w.val - 4034, by
      have := w.isLt; have := s3MomCoreWires_eq mPayload; omega⟩
noncomputable def s3Prefix3954ToFun {mPayload : ℕ} (g : Fin (2 ^ (momCoreWires mPayload)))
    (t : Slot3PayloadTuple mPayload) :
    { z : Fin (2 ^ (momCoreWires mPayload)) // s3SamePrefix3954 z g } :=
  ⟨s3Prefix3954ToFunVal g t, fun w hw ↦ by
    unfold s3Prefix3954ToFunVal; rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DitePos hw]⟩
noncomputable def s3Prefix3954InvFun {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (g : Fin (2 ^ (momCoreWires mPayload))) (z : { z : Fin (2 ^ (momCoreWires mPayload)) //
      s3SamePrefix3954 z g }) : Slot3PayloadTuple mPayload :=
  ((s3U22Core hmPay).extractIndex z.1, (s3S3Core hmPay).extractIndex z.1,
    (s3C8Core hmPay).extractIndex z.1, (s3Fine30Core hmPay).extractIndex z.1,
    ⟨(basisBits (momCoreWires mPayload) z.1 (s3BParCore hmPay)).val, by
      have := Slot3CleanPrim.zmod2_val_le_one
        (basisBits (momCoreWires mPayload) z.1 (s3BParCore hmPay))
      omega⟩,
    (s3U16Core hmPay).extractIndex z.1,
    (QRegister.block 4034 (mPayload - 80) (s3CoreBound_rem mPayload hmPay)).extractIndex z.1)
private lemma s3FinSubEq {n o : ℕ} {x : ℕ} {b : Fin n} (hv : x = o + b.val) (h : x - o <
    n) : (⟨x - o, h⟩ : Fin n) = b :=
  Fin.ext (by rw [Fin.val_mk, hv, Nat.add_sub_cancel_left])
theorem s3Prefix3954_left_inv {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (g : Fin (2 ^ (momCoreWires mPayload))) :
    Function.LeftInverse (s3Prefix3954InvFun hmPay g) (s3Prefix3954ToFun g) := by
  rintro ⟨u22, s3, c8, f30, bPar, u16, rem⟩
  dsimp only [s3Prefix3954InvFun, s3Prefix3954ToFun]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))))
  · refine extractIndex_of_bits (s3U22Core hmPay) _ u22 fun b ↦ ?_
    have hb : (s3U22Core hmPay b).val = 3954 + b.val ∧ b.val < 22 := ⟨rfl, b.isLt⟩
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DitePos (by omega)]
    exact congrArg (basisBits 22 u22) (s3FinSubEq rfl _)
  · refine extractIndex_of_bits (s3S3Core hmPay) _ s3 fun b ↦ ?_
    have hb : (s3S3Core hmPay b).val = 3976 + b.val ∧ b.val < 3 := ⟨rfl, b.isLt⟩
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DitePos (by omega)]
    exact congrArg (basisBits 3 s3) (s3FinSubEq rfl _)
  · refine extractIndex_of_bits (s3C8Core hmPay) _ c8 fun b ↦ ?_
    have hb : (s3C8Core hmPay b).val = 3979 + b.val ∧ b.val < 8 := ⟨rfl, b.isLt⟩
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DiteNeg (by omega), s3DitePos (by omega)]
    exact congrArg (basisBits 8 c8) (s3FinSubEq rfl _)
  · refine extractIndex_of_bits (s3Fine30Core hmPay) _ f30 fun b ↦ ?_
    have hb : (s3Fine30Core hmPay b).val = 3987 + b.val ∧ b.val < 30 := ⟨rfl, b.isLt⟩
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DiteNeg (by omega), s3DiteNeg (by omega), s3DitePos (by omega)]
    exact congrArg (basisBits 30 f30) (s3FinSubEq rfl _)
  · apply Fin.ext
    rw [Fin.val_mk]
    have hv : (s3BParCore hmPay).val = 4017 := rfl
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DiteNeg (by omega), s3DiteNeg (by omega), s3DiteNeg (by omega), s3DitePos hv]
    have := bPar.isLt
    by_cases hb1 : bPar.val = 1
    · simp [hb1]
    · simp [show bPar.val = 0 by omega]
  · refine extractIndex_of_bits (s3U16Core hmPay) _ u16 fun b ↦ ?_
    have hb : (s3U16Core hmPay b).val = 4018 + b.val ∧ b.val < 16 := ⟨rfl, b.isLt⟩
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DiteNeg (by omega), s3DiteNeg (by omega), s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DitePos (by omega)]
    exact congrArg (basisBits 16 u16) (s3FinSubEq hb.1 _)
  · refine extractIndex_of_bits
      (QRegister.block 4034 (mPayload - 80) (s3CoreBound_rem mPayload hmPay)) _ rem fun b ↦ ?_
    have hb : (QRegister.block 4034 (mPayload - 80) (s3CoreBound_rem mPayload hmPay) b).val =
        4034 + b.val ∧ b.val < mPayload - 80 := ⟨rfl, b.isLt⟩
    unfold s3Prefix3954ToFunVal
    rw [Slot3CleanPrim.basisBits_symm_apply_s1, s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DiteNeg (by omega), s3DiteNeg (by omega), s3DiteNeg (by omega), s3DiteNeg (by omega),
      s3DiteNeg (by omega)]
    exact congrArg (basisBits (mPayload - 80) rem) (s3FinSubEq hb.1 _)
theorem s3Prefix3954_right_inv {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (g : Fin (2 ^ (momCoreWires mPayload))) :
    Function.RightInverse (s3Prefix3954InvFun hmPay g) (s3Prefix3954ToFun g) := fun z ↦
  Subtype.ext <| (basisBitsEquiv (momCoreWires mPayload)).injective <| funext fun w ↦ by
    change basisBits (momCoreWires mPayload) _ w = basisBits (momCoreWires mPayload) z.1 w
    dsimp only [s3Prefix3954ToFun, s3Prefix3954ToFunVal, s3Prefix3954InvFun]
    rw [Slot3CleanPrim.basisBits_symm_apply_s1]
    have hwLt : w.val < 3954 + mPayload := (s3MomCoreWires_eq mPayload) ▸ w.isLt
    by_cases h0 : w.val < 3954
    · rw [s3DitePos h0]; exact (z.2 w h0).symm
    · rw [s3DiteNeg h0]
      by_cases h5 : w.val = 4017
      · rw [s3DiteNeg (by omega), s3DiteNeg (by omega), s3DiteNeg (by omega),
          s3DiteNeg (by omega), s3DitePos h5, show w = s3BParCore hmPay from Fin.ext h5]
        rcases Slot3CleanPrim.zmod2_eq_or
            (basisBits (momCoreWires mPayload) z.1 (s3BParCore hmPay)) with hb | hb <;>
          simp [hb]
      · split_ifs with h1 h2 h3 h4
        all_goals exact basisBits_extractIndex_block_eq _ z.1 _ (by omega)
noncomputable def s3Prefix3954Equiv {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (g : Fin (2 ^ (momCoreWires mPayload))) : Slot3PayloadTuple mPayload ≃
    { z : Fin (2 ^ (momCoreWires mPayload)) // s3SamePrefix3954 z g } := ⟨s3Prefix3954ToFun g,
    s3Prefix3954InvFun hmPay g, s3Prefix3954_left_inv hmPay g, s3Prefix3954_right_inv hmPay g⟩
private theorem s3Tuple6_of_eq {A B C D F G : Type*} {x y : A × B × C × D × Fin 2 × F × G} (h : x =
    y) :
    x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧ x.2.2.2.2.1.val =
      y.2.2.2.2.1.val ∧ x.2.2.2.2.2.1 = y.2.2.2.2.2.1 := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem s3Prefix3954Equiv_fields {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {g : Fin (2 ^ (momCoreWires mPayload))}
    (hg : (momAncReg mPayload).extractIndex g =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3))
    (t : Slot3PayloadTuple mPayload) :
    let z := (s3Prefix3954Equiv hmPay g t).1
    (momCoinReg mPayload).extractIndex z = 6 ∧
    (momSysReg mPayload).extractIndex z = (momSysReg mPayload).extractIndex g ∧
    (s3U22Core hmPay).extractIndex z = t.1 ∧
    (s3S3Core hmPay).extractIndex z = t.2.1 ∧
    (s3C8Core hmPay).extractIndex z = t.2.2.1 ∧
    (s3Fine30Core hmPay).extractIndex z = t.2.2.2.1 ∧
    (basisBits (momCoreWires mPayload) z (s3BParCore hmPay)).val = t.2.2.2.2.1.val ∧
    (s3U16Core hmPay).extractIndex z = t.2.2.2.2.2.1 := by
  have hp := (s3SamePrefix3954_coin6_iff hmPay hg).mp (s3Prefix3954ToFun g t).2
  have h6 := s3Tuple6_of_eq (s3Prefix3954_left_inv hmPay g t)
  exact ⟨hp.2.1, hp.1, h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1, h6.2.2.2.2.2⟩
theorem coarse33Equiv_s3Coarse33Core {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (z : Fin (2 ^ (momCoreWires mPayload))) : coarse33Equiv
    ((s3Coarse33Core hmPay).extractIndex z) = ((s3U22Core hmPay).extractIndex z,
      (s3S3Core hmPay).extractIndex z, (s3C8Core hmPay).extractIndex z) :=
  Prod.ext (extractIndex_block_sub _ s3Bound_0_22 _ z)
    (Prod.ext (extractIndex_block_sub _ s3Bound_22_3 _ z)
      (extractIndex_block_sub _ s3Bound_25_8 _ z))
theorem basisBits_s3FlipBParPerm {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (z : Fin (2 ^ (momCoreWires mPayload))) (w : Wire (momCoreWires mPayload)) :
    basisBits (momCoreWires mPayload) (s3FlipBParPerm hmPay z) w =
      Function.update (basisBits (momCoreWires mPayload) z) (s3BParCore hmPay)
    (basisBits (momCoreWires mPayload) z (s3BParCore hmPay) + 1) w := by
  change basisBits (momCoreWires mPayload) (s3FlipBParFun hmPay z) w = _
  unfold s3FlipBParFun
  exact congrFun (Slot3CleanPrim.basisBits_symm_apply_s1 _) w
theorem s3TwosComp8Int_bounds {p : Fin 256} (hp : p.val ≠ 128) : -127 ≤ twosComp8Int p ∧
    twosComp8Int p ≤ 127 := by
  have := p.isLt; rw [s3TwosComp8Int_eq]; split_ifs <;> omega
theorem s3DecodeShellNu3_bounds (u22 : Fin 4194304) (s3 : Fin 8) (w : Fin 3) : -127 ≤
    decodeShellNu3 u22 s3 w ∧ decodeShellNu3 u22 s3 w ≤ 127 := by
  have hna : (decodeShellNu3 u22 s3 w).natAbs < 128 := by
    rw [natAbs_decodeShellNu3]; exact s3ShellMagCoord3_lt_128 u22 w
  omega
theorem s3ModFoldCoord_zero127 : modFoldCoord 127 0 = 0 := by
  unfold modFoldCoord modWrapCoord; norm_num
theorem s3SumProd7Factor {A B C D E F G : Type} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype F] [Fintype G] (α : ℂ) (f : A → B → C → D → ℂ)
    (g : E → F → ℂ) : (∑ t : A × B × C × D × E × F × G, (α * f t.1 t.2.1 t.2.2.1 t.2.2.2.1) *
    g t.2.2.2.2.1 t.2.2.2.2.2.1) = (((Fintype.card G : ℕ) : ℂ) * α) * (∑ a : A, ∑ b : B, ∑ c : C,
      ∑ d : D, f a b c d) * (∑ x : F, ∑ e : E, g e x) := by
  simp_rw [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    show ∀ u v : ℂ, ((Fintype.card G : ℕ) : ℂ) * ((α * u) * v) =
      ((((Fintype.card G : ℕ) : ℂ) * α) * u) * v from fun _ _ ↦ by ring,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset E))]
theorem diag_proj_mul_eq {I : Type*} [Fintype I] [DecidableEq I] (p : I →
    Prop) [DecidablePred p] (D M₁ M₂ : Matrix I I ℂ)
    (hD : D = Matrix.diagonal fun g ↦
      if p g then (1 : ℂ) else 0) (hEq : ∀ g₁ g₂,
      p g₁ → p g₂ → M₁ g₁ g₂ = M₂ g₁ g₂) : D * M₁ * D = D * M₂ * D := by
  subst hD
  ext g₁ g₂
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h1 : p g₁
  · by_cases h2 : p g₂
    · simp [s3ItePos h1, s3ItePos h2, hEq g₁ g₂ h1 h2]
    · simp [s3IteNeg h2]
  · simp [s3IteNeg h1]
end Slot3HardwareAndCore
end MomSlots35Slot3ProjNuclear
end
end ModMomSlots35Slot3ProjNuclear

section ModMomSlots35Slot5Part1
@[expose] public section
namespace MomSlots35Slot5ElecProj
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open scoped Matrix BigOperators Matrix.Norms.L2Operator
namespace Slot5Internal
section ClassicalAndGatePrimitives
@[simp] theorem basisBits_symm_apply {K : ℕ} (β : BitAssignment K) : basisBits K
    ((basisBitsEquiv K).symm β) = β := (basisBitsEquiv K).apply_symm_apply β
@[simp] theorem symm_basisBits_apply {K : ℕ} (j : Fin (2 ^ K)) : (basisBitsEquiv K).symm
    (basisBits K j) = j := (basisBitsEquiv K).symm_apply_apply j
@[simp] theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl
@[simp] theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl
inductive RevProg (K : ℕ) : Type
  | nil : RevProg K
  | x (t : Wire K) : RevProg K
  | cnot (c t : Wire K) (h : c ≠ t) : RevProg K
  | toff (c₁ c₂ t : Wire K) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : RevProg K
  | seq (p₁ p₂ : RevProg K) : RevProg K
end ClassicalAndGatePrimitives
section UnsignedArithmetic
@[simp] theorem block_wires_eq {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (j : Fin width) :
    (QRegister.block offset width h).wires j = ⟨offset + j.val, by omega⟩ := rfl
end UnsignedArithmetic
end Slot5Internal
end MomSlots35Slot5ElecProj
end
end ModMomSlots35Slot5Part1

section ModUnaryOneHotMeasUncompute
@[expose] public section
namespace UnaryOneHotMeasUncompute
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.
open _root_.DynamicCircuit DynCircuitExt
noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
end UnaryOneHotMeasUncompute
end
end ModUnaryOneHotMeasUncompute

end QuantumComputation.Specs.StoppingPowerSolution
