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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.QubitizationFoundations

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

section

open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotentialDecomp (gridDistSq
    gridDistSq_comm pairPot potentialEnergy_eq_diagReal)

noncomputable section
open QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.ClusterPotSlice
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
section
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix Real QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectApprox
  QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.TelescopeSlice

theorem abs_sum2_le {α β : Type*} [Fintype α] [Fintype β]
    (f g : α → β → ℝ) (hf : ∀ a b, |f a b| ≤ g a b) :
    |∑ a, ∑ b, f a b| ≤ ∑ a, ∑ b, g a b :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ ↦ hf a b))

theorem abs_sum3_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f g : α → β → γ → ℝ) (hf : ∀ a b c, |f a b c| ≤ g a b c) :
    |∑ a, ∑ b, ∑ c, f a b c| ≤ ∑ a, ∑ b, ∑ c, g a b c :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ abs_sum2_le (f a) (g a) (hf a))

theorem abs_add_sub_le {a b c x y z : ℝ} (ha : |a| ≤ x) (hb : |b| ≤ y) (hc : |c| ≤ z) :
    |a + b - c| ≤ x + y + z := by
  linarith [abs_sub (a + b) c, abs_add_le a b]

theorem diagReal_eq_potDiagReal {d : ℕ} (f : Fin d → ℝ) : diagReal f =
    PotentialDecomp.diagReal f := by
  ext x y
  by_cases h : x = y <;> simp [diagReal, PhotochemistrySolution.PotentialDecomp.diagReal, h]
/-! ## Section 3: Canonical Zero-Remainder Block-Encoded Operator & Subnormalization `‖A‖ ≤ 1` -/
/-! ## Section 4a: Screened `S = 2 ^ 35` Residuals, `S42` `.en` Bridge & `.ee` Sum -/

/-! ## Section 4b: `.nn` and `.en` Screened Sector Sum Identities -/

theorem sum_lt_symm_eq {ι : Type*} [Fintype ι] [LinearOrder ι] (F : ι → ι → ℝ)
    (hF : ∀ a b, F a b = F b a) : (∑ a : ι, ∑ b : ι, if a < b then 2 * F a b else 0) = ∑ a : ι,
    ∑ b : ι, if a = b then 0 else F a b := by
  trans (∑ a : ι, ∑ b : ι, if a < b then F a b else 0) +
      ∑ a : ι, ∑ b : ι, if b < a then F a b else 0
  · simp_rw [show ∀ a b : ι, (if a < b then 2 * F a b else 0) =
        (if a < b then F a b else 0) + (if a < b then F a b else 0) from
      fun _ _ ↦ by split_ifs <;> ring, Finset.sum_add_distrib]
    exact congrArg (_ + ·) (Finset.sum_comm.trans <| Finset.sum_congr rfl fun a _ ↦
      Finset.sum_congr rfl fun b _ ↦ by rw [hF b a])
  · simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    rcases eq_or_ne a b with rfl | hab
    · simp
    · rcases lt_or_gt_of_ne hab with h | h <;> simp [hab, h, asymm h]

/--
General ordered-pair screening decomposition for any symmetric pair kernel `P` and 1-body screen `G`
.
-/
theorem ordered_pair_screen_sum {ι : Type*} [Fintype ι] [LinearOrder ι] (W : ι → ℝ)
    (P M : ι → ι → ℝ) (G : ι → ℝ) (hP : ∀ a b, P a b = P b a) :
    (∑ a : ι, ∑ b : ι, if a < b then W a * W b * (P a b - (M a b + G a + G b)) else 0) =
        (∑ a : ι, ∑ b : ι, if a = b then 0 else (W a * W b / 2) * P a b) - (∑ a : ι, ∑ b : ι, if a <
        b then W a * W b * M a b else 0) -
    ∑ a : ι, W a * (∑ b : ι, if a = b then 0 else W b) * G a := by
  simp_rw [show ∀ a b : ι, (if a < b then W a * W b * (P a b - (M a b + G a + G b)) else 0) =
      (if a < b then 2 * ((W a * W b / 2) * P a b) else 0) -
        (if a < b then W a * W b * M a b else 0) -
        (if a < b then 2 * ((W a * W b / 2) * (G a + G b)) else 0) from
    fun _ _ ↦ by split_ifs <;> ring, Finset.sum_sub_distrib]
  rw [sum_lt_symm_eq _ fun a b ↦ by linear_combination (W a * W b / 2) * hP a b,
    sum_lt_symm_eq _ fun _ _ ↦ by ring]
  congr 1
  simp_rw [show ∀ a b : ι, (if a = b then (0 : ℝ) else (W a * W b / 2) * (G a + G b)) =
      (W a * G a / 2) * (if a = b then 0 else W b) +
        (if a = b then 0 else W a) * (W b * G b / 2) from
    fun _ _ ↦ by split_ifs <;> ring, Finset.sum_add_distrib,
    Finset.sum_comm (f := fun a b ↦ (if a = b then 0 else W a) * (W b * G b / 2)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp_rw [show ∀ b : ι, (W a * G a / 2) * (if a = b then 0 else W b) +
        (if b = a then 0 else W b) * (W a * G a / 2) =
      (W a * G a) * (if a = b then 0 else W b) from fun _ ↦ by
    simp only [eq_comm]
    ring, ← Finset.mul_sum]
  ring

theorem card_elec_ordered_pairs : (∑ e1 : Fin 187, ∑ e2 : Fin 187, if e1 < e2 then (1 : ℝ) else 0) =
    17391 := by
  have h :=
      (sum_lt_symm_eq (fun (_ _ : Fin 187) ↦ (1 : ℝ)) fun _ _ ↦ rfl).trans grid_real_sums.2.2.1
  simp_rw [show ∀ a b : Fin 187, (if a < b then (2 : ℝ) * 1 else 0) =
      2 * if a < b then 1 else 0 from fun _ _ ↦ by split_ifs <;> ring, ← Finset.mul_sum] at h
  linarith

theorem abs_sum_ee_le (c : Fin 47 → ℝ) {B : ℝ} (hc : ∀ n1, 0 ≤ c n1)
    (f : Fin 47 → Fin 187 → Fin 187 → ℝ) (hf : ∀ n1 e1 e2, e1 < e2 → |f n1 e1 e2| ≤ B) :
    |∑ n1 : Fin 47, ∑ e1 : Fin 187, ∑ e2 : Fin 187, if e1 < e2 then c n1 * f n1 e1 e2 else 0| ≤
        17391 * B * ∑ n1 : Fin 47, c n1 := by
  refine (abs_sum3_le _ (fun n1 e1 e2 ↦ (c n1 * B) * if e1 < e2 then 1 else 0) fun n1 e1 e2 ↦
    if h : e1 < e2 then by
      simpa [h, abs_mul, abs_of_nonneg (hc n1)] using mul_le_mul_of_nonneg_left (hf _ _ _ h) (hc _)
    else by simp [h]).trans_eq ?_
  simp_rw [← Finset.mul_sum, card_elec_ordered_pairs, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

theorem abs_sum_nn_le (c : Fin 47 → Fin 47 → ℝ) {B : ℝ} (hc : ∀ n1 n2, 0 ≤ c n1 n2)
    (f : Fin 47 → Fin 47 → Fin 187 → ℝ) (hf : ∀ n1 n2 e1, n1 < n2 → |f n1 n2 e1| ≤ B) :
    |∑ n1 : Fin 47, ∑ n2 : Fin 47, ∑ e1 : Fin 187, if n1 < n2 then c n1 n2 * f n1 n2 e1 else 0| ≤
        187 * B * ∑ n1 : Fin 47, ∑ n2 : Fin 47, if n1 < n2 then c n1 n2 else 0 := by
  refine (abs_sum3_le _ (fun n1 n2 _ ↦ if n1 < n2 then c n1 n2 * B else 0) fun n1 n2 e1 ↦
    if h : n1 < n2 then by
      simpa [h, abs_mul, abs_of_nonneg (hc n1 n2)] using
        mul_le_mul_of_nonneg_left (hf _ _ e1 h) (hc _ _)
    else by simp [h]).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

theorem abs_sum_en_le (c : Fin 47 → ℝ) {B : ℝ} (hc : ∀ n1, 0 ≤ c n1) (f : Fin 47 → Fin 187 → ℝ)
    (hf : ∀ n1 e1, |f n1 e1| ≤ B) :
    |∑ n1 : Fin 47, ∑ e1 : Fin 187, c n1 * f n1 e1| ≤ 187 * B * ∑ n1 : Fin 47, c n1 := by
  refine (abs_sum2_le _ (fun n1 _ ↦ c n1 * B) fun n1 e1 ↦ by
    simpa [abs_mul, abs_of_nonneg (hc n1)] using
      mul_le_mul_of_nonneg_left (hf n1 e1) (hc n1)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

theorem charge_nucP_eq_speciesZ (n : Fin 47) : (charge_frozen (nucP n) : ℝ) =
    (speciesZ (nucSpecies n) : ℝ) := by
  simp only [show nucP n < 47 from n.isLt, charge_frozen, ↓reduceIte, Int.cast_natCast]
  exact (congrArg (Nat.cast (R := ℝ)) (speciesZ_nucSpecies_eq n)).symm

theorem sum_speciesZ_nuc_eq : (∑ n : Fin 47, (speciesZ (nucSpecies n) : ℝ)) = 187 := by
  simp_rw [← charge_nucP_eq_speciesZ]
  exact grid_real_sums.1

theorem sum_speciesZ_other_eq (n1 : Fin 47) : (∑ n2 : Fin 47, if n1 =
    n2 then (0 : ℝ) else (speciesZ (nucSpecies n2) : ℝ)) = 187 - (speciesZ (nucSpecies n1) : ℝ)
    := by
  have h : (∑ n2 : Fin 47, ((if n1 = n2 then (0 : ℝ) else (speciesZ (nucSpecies n2) : ℝ)) +
      if n1 = n2 then (speciesZ (nucSpecies n1) : ℝ) else 0)) =
      ∑ n2 : Fin 47, (speciesZ (nucSpecies n2) : ℝ) :=
    Finset.sum_congr rfl fun n2 _ ↦ by by_cases h : n1 = n2 <;> simp [h]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h
  linarith [sum_speciesZ_nuc_eq]

/-! ## Section 4c: Exact `0.000000 Ha` Screening Cancellation & Telescoping Identity -/

theorem pairPot_eq_scaled (x : Fin (2 ^ systemQubits_frozen)) {i j : Particle_frozen} (hne : i ≠ j)
    (s : ℕ) (hs : saturationSq_frozen i j = s) :
    pairPot x i j = (((charge_frozen i : ℝ) * (charge_frozen j : ℝ)) / (2 * gridSpacing_frozen)) /
        √((max (pairOpenDistSq x i j) s : ℕ) : ℝ) := by
  unfold pairPot
  simp only [hne, ↓reduceIte, hs]
  rw [← pairOpenDistSq_cast_eq_gridDistSq, ← Nat.cast_max, Int.cast_natCast]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem potentialEnergy_sum_eq (x : Fin (2 ^ systemQubits_frozen)) : (∑ i : Particle_frozen,
    ∑ j : Particle_frozen, pairPot x i j) = (∑ n1 : Fin 47, ∑ n2 : Fin 47, if n1 = n2 then 0
        else (((speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) : ℕ) : ℝ) /
            (2 * gridSpacing_frozen)) / √((max (pairOpenDistSq x (nucP n1) (nucP n2)) 8 : ℕ) : ℝ)) -
      (∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) / gridSpacing_frozen) /
          √((max (pairOpenDistSq x (nucP n1) (elecP e1)) 1 : ℕ) : ℝ)) + (∑ e1 : Fin 187,
          ∑ e2 : Fin 187, if e1 = e2 then 0
        else (1 / (2 * gridSpacing_frozen)) / √((max (pairOpenDistSq x (elecP e1)
            (elecP e2)) 1 : ℕ) : ℝ)) := by
  have hn (e : Fin 187) : ¬ (elecP e < 47) := not_lt.mpr (Nat.le_add_right 47 e.val)
  have np (a : Fin 47) (e : Fin 187) : nucP a ≠ elecP e := fun h ↦ hn e (h ▸ a.isLt)
  have ce (e : Fin 187) : (charge_frozen (elecP e) : ℝ) = -1 := by simp [charge_frozen, hn e]
  have hsym (e1 : Fin 187) (n1 : Fin 47) :
      pairPot x (elecP e1) (nucP n1) = pairPot x (nucP n1) (elecP e1) := by
    rw [pairPot_eq_scaled x (np n1 e1).symm 1 (ite_eq_right fun h ↦ hn e1 h.1),
      pairPot_eq_scaled x (np n1 e1) 1 (ite_eq_right fun h ↦ hn e1 h.2),
      pairOpenDistSq_comm x (elecP e1) (nucP n1), mul_comm (charge_frozen _ : ℝ)]
  rw [sum_particle_split]
  simp_rw [sum_particle_split, Finset.sum_add_distrib, hsym]
  rw [Finset.sum_comm (f := fun (e1 : Fin 187) (n1 : Fin 47) ↦ pairPot x (nucP n1) (elecP e1)),
    show ∀ a b c : ℝ, (a + b) + (b + c) = a - -(2 * b) + c from fun _ _ _ ↦ by ring]
  simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· - ·)
    (Finset.sum_congr rfl fun n1 _ ↦ Finset.sum_congr rfl fun n2 _ ↦ ?_)
    (Finset.sum_congr rfl fun n1 _ ↦ Finset.sum_congr rfl fun e1 _ ↦ ?_))
    (Finset.sum_congr rfl fun e1 _ ↦ Finset.sum_congr rfl fun e2 _ ↦ ?_)
  · by_cases h : n1 = n2
    · simp [h]
    · rw [pairPot_eq_scaled x (fun hp ↦ h (Fin.ext (congrArg (Fin.val : Particle_frozen → ℕ) hp)))
        8 (ite_eq_left ⟨n1.isLt, n2.isLt⟩)]
      simp only [h, ↓reduceIte, charge_nucP_eq_speciesZ, Nat.cast_mul]
  · rw [pairPot_eq_scaled x (np n1 e1) 1 (ite_eq_right fun h ↦ hn e1 h.2)]
    simp only [charge_nucP_eq_speciesZ, ce e1, div_eq_mul_inv]
    ring
  · by_cases h : e1 = e2
    · simp [h]
    · rw [pairPot_eq_scaled x (fun hp ↦ h (Fin.ext (Nat.add_left_cancel
        (congrArg (Fin.val : Particle_frozen → ℕ) hp)))) 1 (ite_eq_right fun h' ↦ hn e1 h'.1)]
      simp only [h, ↓reduceIte, ce e1, ce e2]
      ring
end QuantumComputation.Specs.PhotochemistrySolution.TelescopeSlice

namespace QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect
open PhotochemistrySolution.TelescopeSlice
theorem nat_div_two41_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) / (2 ^ 41 : ℝ) :=
  div_nonneg (Nat.cast_nonneg n) (by norm_num)

/-- Subnormalization `‖aImplGenZeroNEremOf ...‖ ≤ 1` for ANY 41-bit coin budget. -/
theorem opNorm_aImplGenZeroNEremOf_le_one
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle totEE totNN totEN totKin : ℕ}
    (hsEE : (∑ n1 : Fin 47, 17391 * wEE (nucSpecies n1)) = totEE)
    (hsNN : (∑ n1 : Fin 47, ∑ n2 : Fin 47,
      if n1 < n2 then 187 * wNN (nucSpecies n1) (nucSpecies n2) else 0) = totNN)
    (hsEN : (∑ n1 : Fin 47, 187 * wEN (nucSpecies n1)) = totEN)
    (hsKin : (∑ i : Particle_frozen, ∑ _w : Fin 3, wKin i) = totKin)
    (hBudget : wIdle + totKin + totEE + totNN + totEN ≤ 2 ^ 41)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (hEE : ∀ x n1 e1 e2, e1 < e2 → |vEE x n1 e1 e2| ≤ 1)
    (hNN : ∀ x n1 n2 e1, n1 < n2 → |vNN x n1 n2 e1| ≤ 1)
    (hEN : ∀ x n1 e1, |vEN x n1 e1| ≤ 1) :
    ‖aImplGenZeroNEremOf wEE wNN wEN wKin wIdle vEE vNN vEN‖ ≤ 1 := by
  have bId : ‖(((wIdle : ℝ) / (2 ^ 41 : ℝ)) : ℂ) • (1 : OpSys)‖ ≤ (wIdle : ℝ) / (2 ^ 41 : ℝ) := by
    rw [norm_smul, norm_nat_div_two_pow, show (1 : OpSys) = diagReal fun _ ↦ 1 from
      Matrix.ext fun x y ↦ by by_cases h : x = y <;> simp [diagReal, Matrix.one_apply, h]]
    exact mul_le_of_le_one_right (nat_div_two41_nonneg _)
      (opNorm_diagReal_le _ zero_le_one fun _ ↦ by norm_num)
  have bKin : ‖∑ i : Particle_frozen, ∑ w : Fin 3,
      (((wKin i : ℝ) / (2 ^ 41 : ℝ)) : ℂ) • kinNormOp i w‖ ≤ (totKin : ℝ) / (2 ^ 41 : ℝ) := by
    simpa [tImplOf, mul_one] using ht_zIdle_le_kin 41 totKin wKin 1 zero_lt_one hsKin
  have bPot : ‖diagReal (vDiagGenZeroNErem wEE wNN wEN vEE vNN vEN)‖ ≤
      ((totEE : ℝ) + (totNN : ℝ) + (totEN : ℝ)) / (2 ^ 41 : ℝ) := by
    refine opNorm_diagReal_le _ (div_nonneg (add_nonneg (add_nonneg
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (by norm_num)) fun x ↦ ?_
    unfold vDiagGenZeroNErem
    rw [add_div, add_div]
    have hcast1 {k tot : ℕ} {f : Fin 47 → ℕ} (hs : (∑ n1 : Fin 47, k * f n1) = tot) :
        (k : ℝ) * 1 * ∑ n1 : Fin 47, (f n1 : ℝ) / (2 ^ 41 : ℝ) = (tot : ℝ) / (2 ^ 41 : ℝ) := by
      simp_rw [← hs, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    refine abs_add_sub_le
      ((abs_sum_ee_le _ (fun _ ↦ nat_div_two41_nonneg _) (vEE x) (hEE x)).trans_eq
        (hcast1 hsEE)) ?_
      ((abs_sum_en_le _ (fun _ ↦ nat_div_two41_nonneg _) (vEN x) (hEN x)).trans_eq
        (hcast1 hsEN))
    refine (abs_sum_nn_le _ (fun _ _ ↦ nat_div_two41_nonneg _) (vNN x) (hNN x)).trans_eq ?_
    rw [← hsNN]
    simp only [Nat.cast_sum, apply_ite (Nat.cast (R := ℝ)), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_zero, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
  unfold aImplGenZeroNEremOf
  refine (norm_add_le _ _).trans
    ((add_le_add (((norm_add_le _ _).trans (add_le_add bId bKin)).trans_eq (add_div _ _ _).symm)
      bPot).trans ?_)
  rw [← add_div, div_le_one (by norm_num : (0 : ℝ) < 2 ^ 41)]
  exact_mod_cast (by omega : wIdle + totKin + (totEE + totNN + totEN) ≤ 2 ^ 41)
end QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect
end

namespace QuantumComputation.Specs.PhotochemistrySolution.BlockApprox

theorem sum_speciesZ_nn_pairs_nat : (∑ n1 : Fin 47, ∑ n2 : Fin 47, if n1 <
    n2 then speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) else 0) = 16955 := by decide +kernel
theorem sum_speciesZ_nn_pairs_eq : (∑ n1 : Fin 47, ∑ n2 : Fin 47,
    if n1 < n2 then ((speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) : ℕ) : ℝ) else 0) =
        16955 := by
  simpa only [Nat.cast_sum, apply_ite (Nat.cast (R := ℝ)), Nat.cast_zero, Nat.cast_ofNat] using
    congrArg (Nat.cast (R := ℝ)) sum_speciesZ_nn_pairs_nat
end QuantumComputation.Specs.PhotochemistrySolution.BlockApprox

namespace QuantumComputation.Specs.PhotochemistrySolution.ParametricTelescope
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix Real PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.KinNormSlice
  PhotochemistrySolution.TelescopeSlice PhotochemistrySolution.BlockApprox
open PhotochemistrySolution.GenWeightsSelect PhotochemistrySolution.ScreenFermatCore
/-- Parametric `S = 2 ^ 35`-scaled `.ee` residual for arbitrary `(gEE, midEE)`. -/
def rEEScaledGen (gEE : ℕ → ℝ) (midEE : ℝ) (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47)
    (e1 e2 : Fin 187) : ℝ :=
  (2 ^ 35 : ℝ) / √((max (pairOpenDistSq x (elecP e1) (elecP e2)) 1 : ℕ) : ℝ) -
    (midEE + gEE (pairShortBin x (nucP n1) (elecP e1)) +
      gEE (pairShortBin x (nucP n1) (elecP e2)))
/-- Parametric `S = 2 ^ 35`-scaled `.nn` residual for arbitrary `(gNN, midNN)`. -/
def rNNScaledGen (gNN : ℕ → ℕ → ℝ) (midNN : ℕ → ℕ → ℝ) (x : Fin (2 ^ systemQubits_frozen))
    (n1 n2 : Fin 47) (e1 : Fin 187) : ℝ :=
  let s1 := (nucSpecies n1).val; let s2 := (nucSpecies n2).val
  (2 ^ 35 : ℝ) / √((max (pairOpenDistSq x (nucP n1) (nucP n2)) 8 : ℕ) : ℝ) -
    (midNN s1 s2 + gNN s1 (pairShortBin x (nucP n1) (elecP e1)) +
      gNN s2 (pairShortBin x (nucP n2) (elecP e1)))
/-- Parametric `S = 2 ^ 35`-scaled `.en` residual for arbitrary `(gEE, gNN, midEN0)`. -/
def rENScaledGen (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ)
    (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47) (e1 : Fin 187) : ℝ :=
  let sp := nucSpecies n1; let b := pairShortBin x (nucP n1) (elecP e1)
  (2 ^ 35 : ℝ) / √((max (pairOpenDistSq x (nucP n1) (elecP e1)) 1 : ℕ) : ℝ) -
    (midEN0 sp + ((186 : ℝ) * gEE b + (187 - (speciesZ sp : ℝ)) * gNN sp.val b) / 187)
/-- Parametric potential identity shift for arbitrary `(midEE, midNN, midEN0)`. -/
def shiftPotGen (midEE : ℝ) (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ) : ℝ :=
  ((17391 * midEE) +
    (∑ n1 : Fin 47, ∑ n2 : Fin 47,
      if n1 < n2 then
        ((speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) : ℕ) : ℝ) *
          midNN (nucSpecies n1).val (nucSpecies n2).val
      else 0) -
    187 * ∑ n1 : Fin 47, (speciesZ (nucSpecies n1) : ℝ) * midEN0 (nucSpecies n1)) /
    ((2 ^ 35 : ℝ) * gridSpacing_frozen)
/-- Parametric total Hamiltonian shift for arbitrary `(α, wIdle, midEE, midNN, midEN0)`. -/
def shiftGenParametricOf (α : ℝ) (wIdle : ℕ) (midEE : ℝ) (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ) :
    ℝ := shiftKin + shiftPotGen midEE midNN midEN0 - α * ((wIdle : ℝ) / (2 ^ 41 : ℝ))

/-- Weighted `.ee` potential sum over ordered electron pairs. -/
def potSumEE (F : Fin 47 → Fin 187 → Fin 187 → ℝ) : ℝ :=
  ∑ n1 : Fin 47, ∑ e1 : Fin 187, ∑ e2 : Fin 187,
    if e1 < e2 then ((speciesZ (nucSpecies n1) : ℝ) / (187 * (2 ^ 35 : ℝ) * gridSpacing_frozen)) *
        F n1 e1 e2 else 0

/-- Weighted `.nn` potential sum over ordered nuclear pairs. -/
def potSumNN (F : Fin 47 → Fin 47 → Fin 187 → ℝ) : ℝ :=
  ∑ n1 : Fin 47, ∑ n2 : Fin 47, ∑ e1 : Fin 187,
    if n1 < n2 then (((speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) : ℕ) : ℝ) /
      (187 * (2 ^ 35 : ℝ) * gridSpacing_frozen)) * F n1 n2 e1 else 0

/-- Weighted `.en` potential sum over electron-nucleus pairs. -/
def potSumEN (F : Fin 47 → Fin 187 → ℝ) : ℝ :=
  ∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) / ((2 ^ 35 : ℝ) *
      gridSpacing_frozen)) * F n1 e1

theorem potSumEE_sub (F G : Fin 47 → Fin 187 → Fin 187 → ℝ) : potSumEE F - potSumEE G =
    potSumEE fun n1 e1 e2 ↦ F n1 e1 e2 - G n1 e1 e2 := by
  simp_rw [potSumEE, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

theorem potSumNN_sub (F G : Fin 47 → Fin 47 → Fin 187 → ℝ) : potSumNN F - potSumNN G =
    potSumNN fun n1 n2 e1 ↦ F n1 n2 e1 - G n1 n2 e1 := by
  simp_rw [potSumNN, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring

theorem potSumEN_sub (F G : Fin 47 → Fin 187 → ℝ) : potSumEN F - potSumEN G = potSumEN fun n1 e1 ↦
    F n1 e1 - G n1 e1 := by
  simp_rw [potSumEN, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem ee_gen_sum_eq (gEE : ℕ → ℝ) (midEE : ℝ) (x : Fin (2 ^ systemQubits_frozen)) :
    potSumEE (rEEScaledGen gEE midEE x) = (∑ e1 : Fin 187, ∑ e2 : Fin 187, if e1 = e2 then 0
        else (1 / (2 * gridSpacing_frozen)) / √((max (pairOpenDistSq x (elecP e1)
            (elecP e2)) 1 : ℕ) : ℝ)) - (17391 * midEE) / ((2 ^ 35 : ℝ) * gridSpacing_frozen) -
      ∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) * 186 *
          gEE (pairShortBin x (nucP n1) (elecP e1))) / (187 * (2 ^ 35 : ℝ) * gridSpacing_frozen)
          := by
  have hg : gridSpacing_frozen ≠ 0 := ne_of_gt gridSpacing_pos
  unfold potSumEE
  simp_rw [show ∀ (n1 : Fin 47) (e1 e2 : Fin 187),
      (if e1 < e2 then ((speciesZ (nucSpecies n1) : ℝ) /
        (187 * (2 ^ 35 : ℝ) * gridSpacing_frozen)) *
        rEEScaledGen gEE midEE x n1 e1 e2 else 0) =
      ((speciesZ (nucSpecies n1) : ℝ) / (187 * (2 ^ 35 : ℝ) * gridSpacing_frozen)) *
        if e1 < e2 then (1 : ℝ) * 1 * rEEScaledGen gEE midEE x n1 e1 e2 else 0 from
    fun _ _ _ ↦ by split_ifs <;> ring, ← Finset.mul_sum, rEEScaledGen,
    ordered_pair_screen_sum _
      (fun e1 e2 ↦ (2 ^ 35 : ℝ) / √((max (pairOpenDistSq x (elecP e1) (elecP e2)) 1 : ℕ) : ℝ))
      _ _ fun e1 e2 ↦ by rw [pairOpenDistSq_comm x (elecP e1) (elecP e2)],
    one_mul, (grid_real_sums.2.2.2.1 _).1,
    show ∀ e1 e2 : Fin 187, (if e1 < e2 then midEE else 0) = midEE * if e1 < e2 then 1 else 0 from
      fun _ _ ↦ by split_ifs <;> ring,
    ← Finset.mul_sum, card_elec_ordered_pairs,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, sum_speciesZ_nuc_eq]
  refine congrArg₂ (Sub.sub (α := ℝ)) (congrArg₂ (Sub.sub (α := ℝ)) ?_ ?_) ?_
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      split_ifs <;> field_simp [hg]; try ring
  · field_simp [hg]
  · simp_rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem nn_gen_sum_eq (gNN : ℕ → ℕ → ℝ) (midNN : ℕ → ℕ → ℝ) (x : Fin (2 ^ systemQubits_frozen)) :
    potSumNN (rNNScaledGen gNN midNN x) = (∑ n1 : Fin 47, ∑ n2 : Fin 47, if n1 = n2 then 0
        else (((speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) : ℕ) : ℝ) /
            (2 * gridSpacing_frozen)) / √((max (pairOpenDistSq x (nucP n1) (nucP n2)) 8 : ℕ) : ℝ)) -
            (∑ n1 : Fin 47, ∑ n2 : Fin 47, if n1 < n2 then
        ((speciesZ (nucSpecies n1) * speciesZ (nucSpecies n2) : ℕ) : ℝ) *
            midNN (nucSpecies n1).val (nucSpecies n2).val else 0) / ((2 ^ 35 : ℝ) *
            gridSpacing_frozen) -
      ∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) *
          (187 - (speciesZ (nucSpecies n1) : ℝ)) *
          gNN (nucSpecies n1).val (pairShortBin x (nucP n1) (elecP e1))) / (187 * (2 ^ 35 : ℝ) *
              gridSpacing_frozen) := by
  have hg : gridSpacing_frozen ≠ 0 := ne_of_gt gridSpacing_pos
  unfold potSumNN rNNScaledGen
  rw [(Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans Finset.sum_comm]
  dsimp only
  simp_rw [Nat.cast_mul, show ∀ (z1 z2 d r : ℝ) (p : Prop) [Decidable p],
      (if p then (z1 * z2 / d) * r else 0) = (1 / d) * if p then z1 * z2 * r else 0 from
    fun _ _ _ _ _ _ ↦ by split_ifs <;> ring, ← Finset.mul_sum,
    ordered_pair_screen_sum _
      (fun n1 n2 ↦ (2 ^ 35 : ℝ) / √((max (pairOpenDistSq x (nucP n1) (nucP n2)) 8 : ℕ) : ℝ))
      _ _ fun n1 n2 ↦ by rw [pairOpenDistSq_comm x (nucP n1) (nucP n2)],
    sum_speciesZ_other_eq, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_sub, mul_sub]
  refine congrArg₂ (Sub.sub (α := ℝ)) (congrArg₂ (Sub.sub (α := ℝ)) ?_ ?_) ?_
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      split_ifs <;> field_simp [hg] <;> try ring
  · field_simp [hg]
    try ring
  · rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      field_simp [hg]

theorem en_gen_sum_eq (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ)
    (x : Fin (2 ^ systemQubits_frozen)) : potSumEN (rENScaledGen gEE gNN midEN0 x) =
      (∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) / gridSpacing_frozen) /
          √((max (pairOpenDistSq x (nucP n1) (elecP e1)) 1 : ℕ) : ℝ)) -
      (187 * ∑ n1 : Fin 47, (speciesZ (nucSpecies n1) : ℝ) * midEN0 (nucSpecies n1)) /
          ((2 ^ 35 : ℝ) * gridSpacing_frozen) -
      ∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) * 186 *
          gEE (pairShortBin x (nucP n1) (elecP e1))) / (187 * (2 ^ 35 : ℝ) * gridSpacing_frozen) -
      ∑ n1 : Fin 47, ∑ e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) *
          (187 - (speciesZ (nucSpecies n1) : ℝ)) *
          gNN (nucSpecies n1).val (pairShortBin x (nucP n1) (elecP e1))) / (187 * (2 ^ 35 : ℝ) *
              gridSpacing_frozen) := by
  have hg : gridSpacing_frozen ≠ 0 := ne_of_gt gridSpacing_pos
  have hmid : (187 * ∑ n1 : Fin 47, (speciesZ (nucSpecies n1) : ℝ) * midEN0 (nucSpecies n1)) /
      ((2 ^ 35 : ℝ) * gridSpacing_frozen) =
      ∑ n1 : Fin 47, ∑ _e1 : Fin 187, ((speciesZ (nucSpecies n1) : ℝ) * midEN0 (nucSpecies n1)) /
        ((2 ^ 35 : ℝ) * gridSpacing_frozen) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_div, ← Finset.mul_sum]
    ring
  unfold potSumEN rENScaledGen
  rw [hmid]
  simp_rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  field_simp [hg]
  ring

/--
Exact `0.000000 Ha` potential telescoping theorem across all `2 ^ systemQubits` basis states:
when `vEE`, `vNN`, and `vEN` equal their exact `denom`-normalized `S = 2 ^ 35` residuals, all
`gEEQ`, `gNNQ`, `mid*`, and `w_sec / denom_sec` terms cancel identically to `0`.
-/
theorem potentialEnergy_diag_eq_ideal_gen (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEE : ℝ)
    (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ) (x : Fin (2 ^ systemQubits_frozen)) :
    (∑ i : Particle_frozen, ∑ j : Particle_frozen, pairPot x i j) - shiftPotGen midEE midNN midEN0 =
        potSumEE (rEEScaledGen gEE midEE x) + potSumNN (rNNScaledGen gNN midNN x) -
      potSumEN (rENScaledGen gEE gNN midEN0 x) := by
  rw [ee_gen_sum_eq gEE midEE x, nn_gen_sum_eq gNN midNN x, en_gen_sum_eq gEE gNN midEN0 x,
      potentialEnergy_sum_eq x]
  unfold shiftPotGen
  ring

/-- Potential operator error bound from per-sector `S = 2 ^ 35` ULP bounds `(εEE, εNN, εEN)`. -/
theorem potentialEnergy_diag_err_le_of_ulp (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ)
    (wEN : Fin 4 → ℕ) (α : ℝ) (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEE : ℝ) (midNN : ℕ → ℕ → ℝ)
    (midEN0 : Fin 4 → ℝ) {εEE εNN εEN : ℝ}
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
        (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
        (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (hEEErr : ∀ x n1 e1 e2, e1 < e2 →
      |denomGenEE wEE α (nucSpecies n1) * vEE x n1 e1 e2 - rEEScaledGen gEE midEE x n1 e1 e2| ≤ εEE)
          (hNNErr : ∀ x n1 n2 e1, n1 < n2 →
      |denomGenNN wNN α (nucSpecies n1) (nucSpecies n2) * vNN x n1 n2 e1 -
          rNNScaledGen gNN midNN x n1 n2 e1| ≤ εNN) (hENErr : ∀ x n1 e1,
      |denomGenEN wEN α (nucSpecies n1) * vEN x n1 e1 - rENScaledGen gEE gNN midEN0 x n1 e1| ≤ εEN)
          (x : Fin (2 ^ systemQubits_frozen)) :
    |((∑ i : Particle_frozen, ∑ j : Particle_frozen, pairPot x i j) -
        shiftPotGen midEE midNN midEN0) - vImplGenDiag wEE wNN wEN α vEE vNN vEN x| ≤
      (17391 * εEE + 16955 * εNN + 34969 * εEN) / ((2 ^ 35 : ℝ) * gridSpacing_frozen) := by
  have hg : gridSpacing_frozen ≠ 0 := ne_of_gt gridSpacing_pos
  have h241 : (2 : ℝ) ^ 41 = 64 * (2 : ℝ) ^ 35 := by norm_num
  have himpl : vImplGenDiag wEE wNN wEN α vEE vNN vEN x =
      potSumEE (fun n1 e1 e2 ↦ denomGenEE wEE α (nucSpecies n1) * vEE x n1 e1 e2) +
      potSumNN (fun n1 n2 e1 ↦ denomGenNN wNN α (nucSpecies n1) (nucSpecies n2) * vNN x n1 n2 e1) -
      potSumEN (fun n1 e1 ↦ denomGenEN wEN α (nucSpecies n1) * vEN x n1 e1) := by
    unfold vImplGenDiag vDiagGenZeroNErem potSumEE potSumNN potSumEN
    rw [mul_sub, mul_add]
    simp_rw [Finset.mul_sum]
    refine congrArg₂ HSub.hSub (congrArg₂ HAdd.hAdd
      (Finset.sum_congr rfl fun n1 _ ↦ Finset.sum_congr rfl fun _ _ ↦
        Finset.sum_congr rfl fun _ _ ↦ ?_)
      (Finset.sum_congr rfl fun n1 _ ↦ Finset.sum_congr rfl fun n2 _ ↦
        Finset.sum_congr rfl fun _ _ ↦ ?_))
      (Finset.sum_congr rfl fun n1 _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_)
    · split_ifs <;> simp only [denomGenEE, h241, mul_zero];
        field_simp [hg, speciesZ_cast_ne_zero (nucSpecies n1)]
    · split_ifs <;> simp only [denomGenNN, Nat.cast_mul, h241, mul_zero];
        field_simp [hg, speciesZ_cast_ne_zero (nucSpecies n1),
          speciesZ_cast_ne_zero (nucSpecies n2)]
    · simp only [denomGenEN, h241]
      field_simp [hg, speciesZ_cast_ne_zero (nucSpecies n1)]
  rw [potentialEnergy_diag_eq_ideal_gen gEE gNN midEE midNN midEN0 x, himpl,
    show ∀ a1 b1 c1 a2 b2 c2 : ℝ, (a1 + b1 - c1) - (a2 + b2 - c2) = (a1 - a2) + (b1 - b2) -
        (c1 - c2)
      from fun _ _ _ _ _ _ ↦ by ring,
    potSumEE_sub, potSumNN_sub, potSumEN_sub, add_div, add_div]
  refine abs_add_sub_le
    ((abs_sum_ee_le (B := εEE) _ (fun _ ↦ by positivity) _ fun n1 e1 e2 hlt ↦
      (abs_sub_comm _ _).trans_le (hEEErr x n1 e1 e2 hlt)).trans_eq (by
      rw [← Finset.sum_div, sum_speciesZ_nuc_eq]
      field_simp [hg])) ?_
    ((abs_sum_en_le (B := εEN) _ (fun _ ↦ by positivity) _ fun n1 e1 ↦
      (abs_sub_comm _ _).trans_le (hENErr x n1 e1)).trans_eq (by
      rw [← Finset.sum_div, sum_speciesZ_nuc_eq]
      field_simp [hg]
      ring))
  refine (abs_sum_nn_le (B := εNN) _ (fun _ _ ↦ by positivity) _ fun n1 n2 e1 hlt ↦
    (abs_sub_comm _ _).trans_le (hNNErr x n1 n2 e1 hlt)).trans_eq ?_
  rw [← sum_speciesZ_nn_pairs_eq]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
    split_ifs <;> field_simp [hg]; ring

/--
Potential operator norm bound for arbitrary `(wEE, wNN, wEN, α)` and parametric screening
tables `(gEE, gNN, midEE, midNN, midEN0)`.
-/
theorem opNorm_potentialEnergy_sub_shiftGen_sub_vImplGen_le
    (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ) (α : ℝ)
    (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEE : ℝ) (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ)
    {εEE εNN εEN : ℝ} (hEE0 : 0 ≤ εEE) (hNN0 : 0 ≤ εNN) (hEN0 : 0 ≤ εEN)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (hEEErr : ∀ x n1 e1 e2, e1 < e2 →
      |denomGenEE wEE α (nucSpecies n1) * vEE x n1 e1 e2 -
        rEEScaledGen gEE midEE x n1 e1 e2| ≤ εEE)
    (hNNErr : ∀ x n1 n2 e1, n1 < n2 →
      |denomGenNN wNN α (nucSpecies n1) (nucSpecies n2) * vNN x n1 n2 e1 -
        rNNScaledGen gNN midNN x n1 n2 e1| ≤ εNN)
    (hENErr : ∀ x n1 e1,
      |denomGenEN wEN α (nucSpecies n1) * vEN x n1 e1 -
        rENScaledGen gEE gNN midEN0 x n1 e1| ≤ εEN) :
    ‖potentialEnergy_frozen - (shiftPotGen midEE midNN midEN0 : ℂ) • (1 : OpSys) -
      vImplGenOf wEE wNN wEN α vEE vNN vEN‖ ≤
      (17391 * εEE + 16955 * εNN + 34969 * εEN) / ((2 ^ 35 : ℝ) * gridSpacing_frozen) := by
  rw [potentialEnergy_eq_diagReal,
    ← PhotochemistrySolution.PotentialDecomp.diagReal_const,
    ← PhotochemistrySolution.PotentialDecomp.diagReal_sub, vImplGenOf,
    diagReal_eq_potDiagReal,
    ← PhotochemistrySolution.PotentialDecomp.diagReal_sub]
  exact PhotochemistrySolution.PotentialDecomp.opNorm_diagReal_le _
    (div_nonneg (by linarith) (mul_nonneg (by norm_num) gridSpacing_pos.le))
    (potentialEnergy_diag_err_le_of_ulp wEE wNN wEN α gEE gNN midEE midNN midEN0 vEE vNN vEN
      hEEErr hNNErr hENErr)

/--
Parametric `BlockApproxSpecGen` theorem for arbitrary 41-bit coin weights and arbitrary
short-range screening tables `(gEE, gNN, midEE, midNN, midEN0)`.
-/
theorem blockApproxSpecGen_genWeights_parametric
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle totEE totNN totEN totKin : ℕ}
    {α εKin εEE εNN εEN : ℝ}
    (gEE : ℕ → ℝ) (gNN : ℕ → ℕ → ℝ) (midEE : ℝ) (midNN : ℕ → ℕ → ℝ) (midEN0 : Fin 4 → ℝ)
    (hα0 : 0 < α) (hsCap : α * evolutionTime_frozen ≤ 4231872)
    (hsEE : (∑ n1 : Fin 47, 17391 * wEE (nucSpecies n1)) = totEE)
    (hsNN : (∑ n1 : Fin 47, ∑ n2 : Fin 47,
      if n1 < n2 then 187 * wNN (nucSpecies n1) (nucSpecies n2) else 0) = totNN)
    (hsEN : (∑ n1 : Fin 47, 187 * wEN (nucSpecies n1)) = totEN)
    (hsKin : (∑ i : Particle_frozen, ∑ _w : Fin 3, wKin i) = totKin)
    (hBudget : wIdle + totKin + totEE + totNN + totEN ≤ 2 ^ 41)
    (hKin0 : 0 ≤ εKin) (hEE0 : 0 ≤ εEE) (hNN0 : 0 ≤ εNN) (hEN0 : 0 ≤ εEN)
    (hKinErr : ‖kineticEnergy_frozen - (shiftKin : ℂ) • (1 : OpSys) - tImplOf 41 wKin α‖ ≤ εKin)
    (hCap : 4231872 * epsBlockGenOf α εKin εEE εNN εEN ≤ 100)
    (vEE : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → Fin 187 → ℝ)
    (vNN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 47 → Fin 187 → ℝ)
    (vEN : Fin (2 ^ systemQubits_frozen) → Fin 47 → Fin 187 → ℝ)
    (hEE : ∀ x n1 e1 e2, e1 < e2 → |vEE x n1 e1 e2| ≤ 1)
    (hNN : ∀ x n1 n2 e1, n1 < n2 → |vNN x n1 n2 e1| ≤ 1)
    (hEN : ∀ x n1 e1, |vEN x n1 e1| ≤ 1)
    (hEEErr : ∀ x n1 e1 e2, e1 < e2 →
      |denomGenEE wEE α (nucSpecies n1) * vEE x n1 e1 e2 -
        rEEScaledGen gEE midEE x n1 e1 e2| ≤ εEE)
    (hNNErr : ∀ x n1 n2 e1, n1 < n2 →
      |denomGenNN wNN α (nucSpecies n1) (nucSpecies n2) * vNN x n1 n2 e1 -
        rNNScaledGen gNN midNN x n1 n2 e1| ≤ εNN)
    (hENErr : ∀ x n1 e1,
      |denomGenEN wEN α (nucSpecies n1) * vEN x n1 e1 -
        rENScaledGen gEE gNN midEN0 x n1 e1| ≤ εEN) :
    BlockApproxSpecGen hamiltonian_frozen α (shiftGenParametricOf α wIdle midEE midNN midEN0)
      (epsBlockGenOf α εKin εEE εNN εEN)
      (aImplGenZeroNEremOf wEE wNN wEN wKin wIdle vEE vNN vEN) := by
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα0)
  have hkinEq : (∑ i : Particle_frozen, ∑ w : Fin 3,
      (((wKin i : ℝ) / (2 ^ 41 : ℝ)) : ℂ) • kinNormOp i w) =
      ((α : ℂ)⁻¹) • tImplOf 41 wKin α := by
    unfold tImplOf
    simp_rw [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun w _ ↦
      congrArg (· • kinNormOp i w) ?_
    push_cast
    field_simp [hαc]
  refine ⟨hα0, hsCap, ?_,
    opNorm_aImplGenZeroNEremOf_le_one hsEE hsNN hsEN hsKin hBudget vEE vNN vEN hEE hNN hEN, by
      unfold epsBlockGenOf
      positivity, hCap, ?_⟩
  · unfold aImplGenZeroNEremOf
    rw [hkinEq, diagReal_eq_potDiagReal]
    simp [tImplOf_herm, PhotochemistrySolution.PotentialDecomp.diagReal_conjTranspose]
  · have hvEq0 : ((α : ℂ)⁻¹) • vImplGenOf wEE wNN wEN α vEE vNN vEN =
        diagReal (vDiagGenZeroNErem wEE wNN wEN vEE vNN vEN) :=
      Matrix.ext fun x y ↦ by
        by_cases hxy : x = y <;>
          simp [vImplGenOf, vImplGenDiag, diagReal, hxy, inv_mul_cancel_left₀ hαc]
    have hdiff : aImplGenZeroNEremOf wEE wNN wEN wKin wIdle vEE vNN vEN -
        ((α : ℂ)⁻¹) • (hamiltonian_frozen -
          (shiftGenParametricOf α wIdle midEE midNN midEN0 : ℂ) • (1 : OpSys)) =
        -(((α : ℂ)⁻¹) • ((kineticEnergy_frozen - (shiftKin : ℂ) • (1 : OpSys) -
            tImplOf 41 wKin α) +
          (potentialEnergy_frozen - (shiftPotGen midEE midNN midEN0 : ℂ) • (1 : OpSys) -
            vImplGenOf wEE wNN wEN α vEE vNN vEN))) := by
      unfold aImplGenZeroNEremOf shiftGenParametricOf hamiltonian_frozen
      rw [hkinEq, ← hvEq0, Complex.ofReal_sub, Complex.ofReal_add, sub_smul, add_smul,
        sub_sub_eq_add_sub]
      simp only [smul_sub, smul_add, Complex.ofReal_mul, Complex.ofReal_div, smul_smul,
        inv_mul_cancel_left₀ hαc]
      abel
    rw [hdiff, norm_neg]
    refine (norm_smul_le _ _).trans ?_
    rw [norm_inv, Complex.norm_of_nonneg hα0.le, epsBlockGenOf]
    exact mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add hKinErr
        (opNorm_potentialEnergy_sub_shiftGen_sub_vImplGen_le wEE wNN wEN α gEE gNN midEE midNN
          midEN0 hEE0 hNN0 hEN0 vEE vNN vEN hEEErr hNNErr hENErr)))
      (inv_nonneg.mpr hα0.le)
end QuantumComputation.Specs.PhotochemistrySolution.ParametricTelescope

namespace QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
set_option exponentiation.threshold 8192
open Operator QProg DynamicCircuit Matrix Real PhotochemistrySolution.GenWeightsSelect
  PhotochemistrySolution.TelescopeSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
theorem fin8_sum3sq_ne7_u : ∀ i j k : Fin 8, ¬ ((i.val ^ 2 + j.val ^ 2 + k.val ^ 2) % 8 = 7) := by
  decide +kernel

theorem sum3sq_mod8_ne7_u (a b c : ℕ) : ¬ ((a ^ 2 + b ^ 2 + c ^ 2) % 8 = 7) :=
  by simpa [Nat.add_mod, Nat.pow_mod] using fin8_sum3sq_ne7_u ⟨a % 8, by omega⟩ ⟨b % 8, by omega⟩
       ⟨c % 8, by omega⟩

theorem openBoxDist1D_sq_int_u (a b : Fin 256) : ((openBoxDist1D a b : ℤ)) ^ 2 =
    (twosComplement_frozen a - twosComplement_frozen b) ^ 2 := Int.natAbs_sq _

theorem pairOpenDistSq_comm_fermatCoin_u (x : Fin (2 ^ systemQubits_frozen))
    (i j : Particle_frozen) : pairOpenDistSq x i j = pairOpenDistSq x j i :=
  pairOpenDistSq_comm x i j

theorem pairOpenDistSq_mod8_ne7_u (x : Fin (2 ^ systemQubits_frozen)) (i j : Particle_frozen) :
    ¬ (pairOpenDistSq x i j % 8 = 7) := by
  unfold pairOpenDistSq
  rw [Fin.sum_univ_three]
  exact sum3sq_mod8_ne7_u _ _ _

theorem pairOpenDistSq_lagrange_u (x : Fin (2 ^ systemQubits_frozen)) (p0 p1 p2 : Particle_frozen) :
    ((pairOpenDistSq x p1 p0 : ℤ) + (pairOpenDistSq x p2 p0 : ℤ) -
    (pairOpenDistSq x p1 p2 : ℤ)) ^ 2 ≤
      4 * (pairOpenDistSq x p1 p0 : ℤ) * (pairOpenDistSq x p2 p0 : ℤ) := by
  let c (p : Particle_frozen) (w : Fin 3) : ℤ :=
      twosComplement_frozen ((coordinateRegister_frozen p w).extractIndex x)
  have expand (q r : Particle_frozen) : (pairOpenDistSq x q r : ℤ) = (c q 0 - c r 0) ^ 2 +
      (c q 1 - c r 1) ^ 2 + (c q 2 - c r 2) ^ 2 := by
    unfold pairOpenDistSq
    rw [Fin.sum_univ_three]
    push_cast
    simp only [openBoxDist1D_sq_int_u, c]
  rw [expand p1 p0, expand p2 p0, expand p1 p2]
  nlinarith [sq_nonneg ((c p1 0 - c p0 0) * (c p2 1 - c p0 1) - (c p1 1 - c p0 1) *
      (c p2 0 - c p0 0)), sq_nonneg ((c p1 1 - c p0 1) * (c p2 2 - c p0 2) - (c p1 2 - c p0 2) *
      (c p2 1 - c p0 1)),
    sq_nonneg ((c p1 2 - c p0 2) * (c p2 0 - c p0 0) - (c p1 0 - c p0 0) * (c p2 2 - c p0 2))]

theorem pairOpenDistSq_lt_189_u {x : Fin (2 ^ systemQubits_frozen)} {p0 p1 p2 : Particle_frozen}
    (hA : pairOpenDistSq x p1 p0 < 48) (hB : pairOpenDistSq x p2 p0 < 48) : pairOpenDistSq x p1 p2 <
    189 := by
  have hAn7 := pairOpenDistSq_mod8_ne7_u x p1 p0
  have hBn7 := pairOpenDistSq_mod8_ne7_u x p2 p0
  by_contra hge
  nlinarith [pairOpenDistSq_lagrange_u x p0 p1 p2, Int.natCast_nonneg (pairOpenDistSq x p1 p0),
    Int.natCast_nonneg (pairOpenDistSq x p2 p0),
    (by omega : (pairOpenDistSq x p1 p0 : ℤ) ≤ 46),
    (by omega : (pairOpenDistSq x p2 p0 : ℤ) ≤ 46),
    (by omega : (189 : ℤ) ≤ pairOpenDistSq x p1 p2)]

def binLoUltra : ℕ → ℕ
  | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 16 | 7 => 32 | _ => 48
def binHiUltra : ℕ → ℕ
  | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 14 | 6 => 30 | 7 => 46 | _ => 195075
theorem bin_range_ultra : ∀ d : Fin 48, d.val % 8 = 7 ∨
    ((fin8Bin d.val).val ≥ 1 ∧ binLoUltra (fin8Bin d.val).val ≤ d.val ∧
      d.val ≤ binHiUltra (fin8Bin d.val).val) := by
  decide +kernel
def boxOkUltra (b1 b2 c : ℕ) : Bool :=
  let a0 : ℤ := binLoUltra b1; let a1 : ℤ := binHiUltra b1; let d0 : ℤ := binLoUltra b2;
  let d1 : ℤ := binHiUltra b2; let cz : ℤ := c
  decide ((a1 + d1 ≤ cz → (cz - a1 - d1) ^ 2 ≤ 4 * a1 * d1) ∧
    (d1 + cz ≤ a0 → (a0 - d1 - cz) ^ 2 ≤ 4 * d1 * cz) ∧
    (a1 + cz ≤ d0 → (d0 - a1 - cz) ^ 2 ≤ 4 * a1 * cz))

theorem boxOkUltra_of_lagrange {a b c : ℕ} (ha : binLoUltra (fin8Bin a).val ≤ a ∧ a ≤
    binHiUltra (fin8Bin a).val) (hb : binLoUltra (fin8Bin b).val ≤ b ∧ b ≤
    binHiUltra (fin8Bin b).val)
    (hlag : ((a : ℤ) + (b : ℤ) - (c : ℤ)) ^ 2 ≤ 4 * (a : ℤ) * (b : ℤ)) :
    boxOkUltra (fin8Bin a).val (fin8Bin b).val c = true := by
  unfold boxOkUltra
  simp only [decide_eq_true_eq]
  have hbds : (binLoUltra (fin8Bin a).val : ℤ) ≤ a ∧ (a : ℤ) ≤ binHiUltra (fin8Bin a).val ∧
      (binLoUltra (fin8Bin b).val : ℤ) ≤ b ∧ (b : ℤ) ≤ binHiUltra (fin8Bin b).val ∧ (0 : ℤ) ≤ c :=
    ⟨Int.ofNat_le.mpr ha.1, Int.ofNat_le.mpr ha.2, Int.ofNat_le.mpr hb.1, Int.ofNat_le.mpr hb.2,
      Int.natCast_nonneg c⟩
  refine ⟨fun _ ↦ by nlinarith, fun _ ↦ ?_, fun _ ↦ ?_⟩
  · nlinarith [(by ring : ((a : ℤ) - b - c) ^ 2 - 4 * b * c = (a + b - c) ^ 2 - 4 * a * b)]
  · nlinarith [(by ring : ((b : ℤ) - a - c) ^ 2 - 4 * a * c = (a + b - c) ^ 2 - 4 * a * b)]

theorem fin8Bin_of_ge48_ultra {d : ℕ} (h : 48 ≤ d) : (fin8Bin d).val = 0 := by
  unfold fin8Bin
  simp [h]
end QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse

open PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.Stage1ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
theorem blt_false_of_le {m n : ℕ} (h : n ≤ m) : Nat.blt m n = false :=
  Bool.eq_false_iff.mpr fun ht ↦ by
    have := Nat.blt_eq.mp ht
    omega

theorem sum_topSpill_eq (u1 : ℕ) (s : ZeroNEremSector) : (∑ h1 : Fin 3, ∑ h2 : Fin 3,
    ((Finset.univ : Finset (Fin 31519584)).filter
        (fun u ↦ decodeFermatCell u1 h1.val h2.val (1275068416 + u.val) = s)).card) =
            fermatTopSpill u1 s := by
  let k0 := ZeroNEremSector.kin (mkFin234 (47 + u1)) 0
  have hstrip (h1 h2 : Fin 3) :
      ((Finset.univ : Finset (Fin 31519584)).filter
        (fun u ↦ decodeFermatCell u1 h1.val h2.val (1275068416 + u.val) = s)).card =
      ((Finset.univ : Finset (Fin 31519584)).filter (fun u ↦
        cond ((h1.val == 1) && (h2.val == 0) && Nat.blt u.val 19848333) k0
          (cond ((h1.val == 2) && (h2.val == 0) && Nat.blt u.val 20880606) k0
            (cond ((h1.val == 2) && (h2.val == 2) && Nat.blt u.val 137290) .idle
              (.kin (mkFin234 (47 + u1)) (mkFin3 h1.val)))) = s)).card :=
    congrArg Finset.card <| Finset.filter_congr fun u _ ↦ by
      unfold decodeFermatCell
      rw [blt_false_of_le (by omega), blt_false_of_le (by omega), blt_false_of_le (by omega),
        Bool.cond_false, Bool.cond_false, Bool.cond_false, Nat.add_sub_cancel_left]
  have hconst (tg : ZeroNEremSector) :
      ((Finset.univ : Finset (Fin 31519584)).filter (fun _ ↦ tg = s)).card =
        cond (eqSec tg s) 31519584 0 := by
    rw [show ((Finset.univ : Finset (Fin 31519584)).filter (fun _ ↦ tg = s)) =
        (Finset.univ.filter fun x : Fin 31519584 ↦ cond (Nat.blt x.val 31519584) tg tg = s) from
      Finset.filter_congr fun x _ ↦ by cases Nat.blt x.val 31519584 <;> rfl,
      card_prefix_cond tg tg s 31519584 le_rfl]
    cases eqSec tg s <;> rfl
  simp only [hstrip, Fin.sum_univ_three, k0, Fin.isValue, Fin.val_zero, Fin.val_one,
    show (2 : Fin 3).val = 2 from rfl, show ((0 : ℕ) == 0) = true from rfl,
    show ((0 : ℕ) == 1) = false from rfl, show ((0 : ℕ) == 2) = false from rfl,
    show ((1 : ℕ) == 0) = false from rfl, show ((1 : ℕ) == 1) = true from rfl,
    show ((1 : ℕ) == 2) = false from rfl, show ((2 : ℕ) == 0) = false from rfl,
    show ((2 : ℕ) == 1) = false from rfl, show ((2 : ℕ) == 2) = true from rfl,
    show mkFin3 0 = 0 from rfl, show mkFin3 1 = 1 from rfl, show mkFin3 2 = 2 from rfl,
    Bool.false_and, Bool.true_and, Bool.cond_false, hconst,
    card_prefix_cond (N := 31519584) _ _ s 19848333 (by decide),
    card_prefix_cond (N := 31519584) _ _ s 20880606 (by decide),
    card_prefix_cond (N := 31519584) _ _ s 137290 (by decide)]
  unfold fermatTopSpill
  cases eqSec (.kin (mkFin234 (47 + u1)) 0) s <;> cases eqSec (.kin (mkFin234 (47 + u1)) 1) s <;>
    cases eqSec (.kin (mkFin234 (47 + u1)) 2) s <;> cases eqSec .idle s <;> rfl

theorem card_decodeFermatKinNuc25_eq (s : ZeroNEremSector) :
    ((Finset.univ : Finset (Fin 33554432)).filter (fun w ↦ decodeFermatKinNuc25 w.val = s)).card =
      foldSum 1024 fun b ↦
          cond (eqSec (kinNucBlkFermat b).1 s) (kinNucBlkFermat b).2 0 + cond (eqSec .idle s)
          (32768 - (kinNucBlkFermat b).2) 0 := by
  change ((Finset.univ : Finset (Fin (1024 * 32768))).filter
    (fun w ↦ decodeFermatKinNuc25 w.val = s)).card = _
  rw [card_fin_mul_split (A := 1024) (B := 32768) (Nat.succ_pos _) (decodeFermatKinNuc25 · = s),
    ← sum_fin_eq_foldSum 1024]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← card_prefix_cond (kinNucBlkFermat b.val).1 .idle s (kinNucBlkFermat b.val).2
    (kinNucBlkFermat_snd_le b.val)]
  refine congrArg Finset.card (Finset.filter_congr fun ⟨rv, hrv⟩ _ ↦ ?_)
  dsimp only [decodeFermatKinNuc25]
  rw [show (b.val * 32768 + rv) / 32768 = b.val by omega,
    show (b.val * 32768 + rv) % 32768 = rv by omega]
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end
end

noncomputable section
variable {Var : Type}
namespace QuantumComputation.Specs.PhotochemistrySolution.JacobiAngerTightWalk
open scoped Matrix Matrix.Norms.L2Operator BigOperators Polynomial
open Operator QProg DynamicCircuit _root_.QuantumComputation.Specs.PhotochemistrySolution
  _root_.QuantumComputation.Specs.PhotochemistrySolution.BucketRouterCircuit
  _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationCore
  _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationProgram
  _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationTop
  _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationKapteyn
  _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectSymDyn
  _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectApprox
  _root_.QuantumComputation.Specs.PhotochemistrySolution.GQSP WithLp
open Polynomial Matrix ComplexConjugate
set_option exponentiation.threshold 10000 in
theorem chebyshevOpNat_eq_chebyshevT_pair_tight {I : Type*}
    [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    ∀ k : ℕ, chebyshevOpNat k A = chebyshevT k A ∧
      chebyshevOpNat (k + 1) A = chebyshevT (k + 1) A
  | 0 => ⟨rfl, rfl⟩
  | k + 1 => by
      obtain ⟨ih0, ih1⟩ :=
          chebyshevOpNat_eq_chebyshevT_pair_tight A k; refine ⟨ih1,
          ?_⟩; rw [chebyshevOpNat, chebyshevT_add_two, ih1, ih0]
set_option exponentiation.threshold 10000 in
theorem poly_proj_walk_scaledTruncPoly_gen {I : Type*} [Fintype I] [DecidableEq I] (K D : ℕ)
    {proj0 S A : Matrix I I ℂ} (hPh : proj0ᴴ = proj0) (hP : proj0 * proj0 = proj0) (hS : S * S = 1)
    (hSh : Sᴴ = S) (hblock : proj0 * S * proj0 = A * proj0) (hA : Aᴴ = A) (hAP : Commute A proj0)
    (ε_cheb s δ : ℝ) : proj0 * ((reflectionMatrix proj0 * S)ᴴ ^ K * aeval (reflectionMatrix proj0 *
    S) (scaledPoly ε_cheb δ (truncLaurentPoly K D s))) * proj0 =
    ((1 / (1 + ε_cheb + δ) : ℝ) : ℂ) • (truncChebApprox K D A s * proj0) := by
  let W := reflectionMatrix proj0 * S;
  have hW : W ∈ unitary (Matrix I I ℂ) := walk_mem_unitary hPh hP hS hSh
  have hproj_k : ∀ k : ℕ, proj0 * ((W ^ k + (Wᴴ) ^ k) * proj0) = (2 : ℂ) • (chebyshevT k A * proj0)
      :=
    fun k ↦ by
      have hp1 : proj0 * W ^ k * proj0 = chebyshevOpNat k A * proj0 :=
          walk_pow_proj_eq_chebyshev hP hS hblock k
      have hp2 : proj0 * (Wᴴ) ^ k * proj0 = chebyshevOpNat k A * proj0 := by
        have h :=
            congrArg conjTranspose hp1; rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul,
            hPh, conjTranspose_pow, chebyshevOpNat_conjTranspose hA, ← Matrix.mul_assoc,
            ← (chebyshevOpNat_commute hAP k).eq] at h; exact h
      rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hp1, hp2,
          (chebyshevOpNat_eq_chebyshevT_pair_tight A k).1]
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hscale : (Wᴴ) ^ K * aeval W (scaledPoly ε_cheb δ (truncLaurentPoly K D s)) =
      ((1 / (1 + ε_cheb + δ) : ℝ) : ℂ) • truncChebApprox K D ((1 / 2 : ℂ) • (W + Wᴴ)) s := by
    unfold scaledPoly;
    rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.mul_smul,
        poly_mul_star_pow_aeval_truncLaurentPoly K D s hW]
  rw [hscale, Matrix.mul_smul, smul_mul_assoc]; congr 1; unfold truncChebApprox;
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 : proj0 * chebyshevT k ((1 / 2 : ℂ) • (W + Wᴴ)) * proj0 = chebyshevT k A * proj0 := by
    rw [(chebyshevT_half_add_star_eq hW k).1, Matrix.mul_smul, smul_mul_assoc,
        Matrix.mul_assoc proj0 _ proj0, hproj_k k, smul_smul]; norm_num
  rw [Matrix.mul_smul, smul_mul_assoc, h1, smul_mul_assoc]
end QuantumComputation.Specs.PhotochemistrySolution.JacobiAngerTightWalk
end

end
