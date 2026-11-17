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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sSumLo3018
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sSumHi3018C
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OctantOneNegLoB
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OctantOneNegHiC
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Mobius16Slot3Prep

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspSlot3UltraBkAnd8TierCert

section
namespace GqspSlot3UltraBkAnd8TierCert
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowGqsp (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix NNReal ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
-- Root solution namespace already active.
open TwosCompAndWire0Cancel
open ZeroAncillaUSP (leSqrt2Int_sound)
open ModWrapCoarse8PureMomentum (sq3Nat natSum natSum_congr natSum_add_split fLin sum_fLin_127
  sum_nonzeroBox3D_eq_oct_natSum nearestProtonCoord thetaProtonNearest
  quantizedStructureFactorNearest modWrapProjNucOp modWrapCoord modFoldCoord modFold3D
  modFoldCoord_eq sumNatAbsSq shellIndex nonzeroBox3D box3D mem_box3D mem_nonzeroBox3D
  modFold3D_mem_nonzeroBox3D modFold3D_sub_inj_left modFold3D_sub_inj_right sumNatAbsSq_modFold3D_le
  sumNatAbsSq_pos_of_ne_zero norm_le_of_weightedPartialPerm operator_sum_apply ite_true_eq
  ite_false_eq dampedModWrapKernelApprox dampedModWrapKernelApprox_zero
  dampedModWrapKernelApprox_bounds projectile_sub_mem_box3D_254 norm_exp_ofReal_mul_I_sub_le
  natAbsSum natAbsSum_mul_sumNatAbsSq_modFold3D_le natAbsSum_div_sumNatAbsSq_le_fLin
  forty_two_mul_coulombKernel_le pi_bounds_8digit sum_inv_four_pow_shellIndex_127_eq
  sum_inv_sumNatAbsSq_127_le norm_fermionicProjector_sandwich_le)
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sShiftIdx_eq n1sNatSumFast n1sNatSumFast_eq
  n1s_octSum128_eq_chunks2 n1s_real_sum_eq_octSum128 n1s_nat_add_eq n1s_nat_sub_eq n1s_nat_mul_eq)
open Slot3Norm1s36LatticeLoT2618 (n1s_chunk_t26_18_lo)
open Slot3Norm1s36LatticeHiT2618 (n1s_chunk_t26_18_hi)
open Slot3Norm1s36LatticeLoT2617 (n1s_chunk_t26_17_lo)
open Slot3Norm1s36LatticeHiT2617 (n1s_chunk_t26_17_hi)
open Slot3Norm1s36LatticeLoT2717 (n1s_chunk_t27_17_lo)
open Slot3Norm1s36LatticeHiT2717 (n1s_chunk_t27_17_hi)
open Slot3Norm1s36LatticeLoT2918 (n1s_chunk_t29_18_lo)
open Slot3Norm1s36LatticeHiT2918 (n1s_chunk_t29_18_hi)
open Slot3Norm1s36LatticeLoT2917 (n1s_chunk_t29_17_lo)
open Slot3Norm1s36LatticeHiT2917 (n1s_chunk_t29_17_hi)
open Slot3Norm1s36LatticeCert (eNuNorm1s eNuNorm1s_nonneg eNuNorm1s_bound)
attribute [local irreducible] box3D nonzeroBox3D
section Section1T3018Cert
open GqspSlot3T3018Lo (n1s_chunk_t30_18_lo)
open GqspSlot3T3018Hi (n1s_chunk_t30_18_hi)
/-- Extended 6-tier certified predicate covering all 5 base tiers plus `.t30_18`. -/
def IsCertifiedNorm1sTier6 (t : Norm1sTier) : Prop :=
  Leaf3Slot3Norm1sWidth204.IsCertifiedNorm1sTier t ∨ t = .t30_18
/-- Exact `4096`-scaled integer octant sum `natSum 128 (octShell (n1sOctLattice t))` across all 6
  tiers. -/
def n1sOctSum128CertVal : Norm1sTier → ℕ
  | .t26_18 => 204540094716
  | .t26_17 => 113735084214
  | .t27_17 => 57360849910
  | .t29_18 => 25413533660
  | .t29_17 => 14233709138
  | .t30_18 => 12724436452
  | _ => 0
theorem n1s_real_sum_eq_certVal_tier6 (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t) :
    ∑ ν ∈ nonzeroBox3D (127 : ℤ), eNuNorm1s t ν / (2 : ℝ) ^ (2 * shellIndex ν) =
      (n1sOctSum128CertVal t : ℝ) / 4096 := by
  rw [n1s_real_sum_eq_octSum128 t]
  refine congrArg (fun n : ℕ ↦ (n : ℝ) / 4096) ?_
  rcases ht with (rfl | rfl | rfl | rfl | rfl) | rfl
  · exact n1s_octSum128_eq_chunks2 .t26_18 n1s_chunk_t26_18_lo n1s_chunk_t26_18_hi rfl
  · exact n1s_octSum128_eq_chunks2 .t26_17 n1s_chunk_t26_17_lo n1s_chunk_t26_17_hi rfl
  · exact n1s_octSum128_eq_chunks2 .t27_17 n1s_chunk_t27_17_lo n1s_chunk_t27_17_hi rfl
  · exact n1s_octSum128_eq_chunks2 .t29_18 n1s_chunk_t29_18_lo n1s_chunk_t29_18_hi rfl
  · exact n1s_octSum128_eq_chunks2 .t29_17 n1s_chunk_t29_17_lo n1s_chunk_t29_17_hi rfl
  · exact n1s_octSum128_eq_chunks2 .t30_18 n1s_chunk_t30_18_lo n1s_chunk_t30_18_hi rfl
end Section1T3018Cert
section Section2OctantNuc
open GqspSlot3OctantOneNegBaseAndLo (ceilDiv20Den fOneNegSingle fOneNeg3Sym fOneNeg3Sym_zero
  fOneNeg3Sym_swap12 fOneNeg3Sym_swap23 oneNegShellFast oneNegShellFast_eq)
open Gqsp2_Slot3OctantOneNegLo (oneNeg_chunk_lo)
open GqspSlot3OctantOneNegHiB (oneNeg_chunk_hi)
theorem modFoldCoord_127_neg {d : ℤ} (hd : -254 ≤ d ∧ d ≤ 254) : modFoldCoord 127 (-d) =
    -modFoldCoord 127 d := by
  rw [modFoldCoord_eq 127 (by omega), modFoldCoord_eq 127 (by omega)]
  split_ifs <;> omega
theorem modFoldCoord_127_pos_cases {d : ℤ} {y : ℕ}
    (hd : -254 ≤ d ∧ d ≤ 254) (hy : y ≤ 127) (hm : modFoldCoord 127 d = (y : ℤ)) : (d = (y : ℤ) ∧
      d.natAbs = y) ∨
      (1 ≤ y ∧ d = -((255 - y : ℕ) : ℤ) ∧ d.natAbs = 255 - y) := by
  rw [modFoldCoord_eq 127 (by omega)] at hm
  split_ifs at hm
  · omega
  · exact Or.inr ⟨by omega, by omega, by omega⟩
  · exact Or.inl ⟨by omega, by omega⟩
private theorem abs_int_add3_div_le {d0 d1 d2 : ℤ} {sumSq num den B : ℕ}
    (hnum : (d0 + d1 + d2).natAbs = num) (hden : 0 < den)
    (hle_den : den ≤ sumSq) (hle_B : ceilDiv20Den num den ≤ B) :
    |(d0 : ℝ) + (d1 : ℝ) + (d2 : ℝ)| / (sumSq : ℝ) ≤ (B : ℝ) / 1048576 := by
  have habs : |(d0 : ℝ) + (d1 : ℝ) + (d2 : ℝ)| = (num : ℝ) := by
    rw [← Int.cast_add, ← Int.cast_add]
    rcases Int.natAbs_eq (d0 + d1 + d2) with hk | hk
    · rw [hk, hnum, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg num)]
    · rw [hk, hnum, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg num)]
  rw [habs]
  have hdenR : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have h1 := Nat.div_add_mod (1048576 * num + den - 1) den
  have h2 := Nat.mod_lt (1048576 * num + den - 1) hden
  change den * ceilDiv20Den num den + _ = _ at h1
  have hcast : (1048576 : ℝ) * num ≤ (den : ℝ) * B := by
    exact_mod_cast (by omega : 1048576 * num ≤ den * ceilDiv20Den num den).trans
      (Nat.mul_le_mul_left den hle_B)
  refine (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdenR (Nat.cast_le.mpr hle_den)).trans ?_
  rw [div_le_div_iff₀ hdenR (by norm_num)]
  linarith
set_option maxHeartbeats 800000 in -- Large circuit/arithmetic proof
theorem abs_add3_div_sq3_le_fOneNegSingle {d0 d1 d2 : ℤ} {x y z : ℕ}
    (hd0 : -254 ≤ d0 ∧ d0 ≤ 254) (hd1 : -254 ≤ d1 ∧ d1 ≤ 254) (hd2 : -254 ≤ d2 ∧ d2 ≤ 254)
    (hx : x ≤ 127) (hy : y ≤ 127) (hz : z ≤ 127) (hxyz : 0 < x + y + z)
    (hm0 : modFoldCoord 127 d0 = -(x : ℤ)) (hm1 : modFoldCoord 127 d1 = (y : ℤ))
    (hm2 : modFoldCoord 127 d2 = (z : ℤ)) :
    |(d0 : ℝ) + (d1 : ℝ) + (d2 : ℝ)| / ((d0.natAbs ^ 2 + d1.natAbs ^ 2 + d2.natAbs ^ 2 : ℕ) : ℝ) ≤
      (fOneNegSingle x y z : ℝ) / 1048576 := by
  have hbeq0 {k : ℕ} (hk : 1 ≤ k) : Nat.beq k 0 = false := by
    cases k with
    | zero => omega
    | succ _ => rfl
  have hsq255 {k : ℕ} (hk : k ≤ 127) : 0 < (255 - k) * (255 - k) :=
    Nat.mul_pos (by omega) (by omega)
  have _ := hsq255 hx
  have _ := hsq255 hy
  have _ := hsq255 hz
  have hs0_pos : 0 < x * x + (y * y + z * z) := by
    rcases (show 1 ≤ x ∨ 1 ≤ y ∨ 1 ≤ z by omega) with h | h | h <;> nlinarith
  have hbs0 := hbeq0 hs0_pos
  have hb000 : ceilDiv20Den ((y + z - x) + (x - (y + z))) (x * x + (y * y + z * z)) ≤
      fOneNegSingle x y z := by
    dsimp only [fOneNegSingle]
    rw [hbs0]
    exact le_max_of_le_left (le_max_left _ _)
  have hb100 (hx1 : 1 ≤ x) : ceilDiv20Den ((255 - x) + (y + z))
      ((255 - x) * (255 - x) + (y * y + z * z)) ≤ fOneNegSingle x y z := by
    dsimp only [fOneNegSingle]
    rw [hbs0, hbeq0 hx1]
    exact le_max_of_le_left (le_max_right _ _)
  have hb010 (hy1 : 1 ≤ y) : ceilDiv20Den ((255 + x) - (y + z))
      (x * x + ((255 - y) * (255 - y) + z * z)) ≤ fOneNegSingle x y z := by
    dsimp only [fOneNegSingle]
    rw [hbs0, hbeq0 hy1]
    exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have hb001 (hz1 : 1 ≤ z) : ceilDiv20Den ((255 + x) - (y + z))
      (x * x + (y * y + (255 - z) * (255 - z))) ≤ fOneNegSingle x y z := by
    dsimp only [fOneNegSingle]
    rw [hbs0, hbeq0 hz1]
    exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hb011 (hy1 : 1 ≤ y) (hz1 : 1 ≤ z) : ceilDiv20Den (x + ((255 - y) + (255 - z)))
      (x * x + ((255 - y) * (255 - y) + (255 - z) * (255 - z))) ≤ fOneNegSingle x y z := by
    dsimp only [fOneNegSingle]
    rw [hbs0, hbeq0 hy1, hbeq0 hz1]
    exact le_max_of_le_right (le_max_right _ _)
  have hneg0 : (d0 = -(x : ℤ) ∧ d0.natAbs = x) ∨
      (1 ≤ x ∧ d0 = ((255 - x : ℕ) : ℤ) ∧ d0.natAbs = 255 - x) := by
    rw [modFoldCoord_eq 127 (by omega)] at hm0
    split_ifs at hm0
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · omega
    · exact Or.inl ⟨by omega, by omega⟩
  rcases hneg0 with ⟨rfl, ha0⟩ | ⟨hx1, rfl, ha0⟩ <;>
    rcases modFoldCoord_127_pos_cases hd1 hy hm1 with ⟨rfl, ha1⟩ | ⟨hy1, rfl, ha1⟩ <;>
    rcases modFoldCoord_127_pos_cases hd2 hz hm2 with ⟨rfl, ha2⟩ | ⟨hz1, rfl, ha2⟩ <;>
    simp only [ha0, ha1, ha2]
  · exact abs_int_add3_div_le (by omega) hs0_pos (by nlinarith) hb000
  · exact abs_int_add3_div_le (by omega) (by omega) (by nlinarith) (hb001 hz1)
  · exact abs_int_add3_div_le (by omega) (by omega) (by nlinarith) (hb010 hy1)
  · exact abs_int_add3_div_le (by omega) (by omega) (by nlinarith) (hb011 hy1 hz1)
  · exact abs_int_add3_div_le (by omega) (by omega) (by nlinarith) (hb100 hx1)
  · refine abs_int_add3_div_le (by omega) hs0_pos ?_ hb000
    zify [show x ≤ 255 by omega, show z ≤ 255 by omega]
    nlinarith
  · refine abs_int_add3_div_le (by omega) hs0_pos ?_ hb000
    zify [show x ≤ 255 by omega, show y ≤ 255 by omega]
    nlinarith
  · refine abs_int_add3_div_le (by omega) (by omega) ?_ (hb010 hy1)
    zify [show x ≤ 255 by omega, show y ≤ 255 by omega, show z ≤ 255 by omega]
    nlinarith
def gAliasGen3 (F G : ℕ → ℕ → ℕ → ℕ) (u0 u1 u2 : ℤ) : ℕ :=
  let a := u0.natAbs
  let b := u1.natAbs
  let c := u2.natAbs
  if (0 ≤ u0 ∧ 0 ≤ u1 ∧ 0 ≤ u2) ∨ (u0 ≤ 0 ∧ u1 ≤ 0 ∧ u2 ≤ 0) then F a b c
  else if (u0 < 0 ∧ 0 ≤ u1 ∧ 0 ≤ u2) ∨ (0 < u0 ∧ u1 < 0 ∧ u2 < 0) then G a b c
  else if (0 ≤ u0 ∧ u1 < 0 ∧ 0 ≤ u2) ∨ (u0 < 0 ∧ 0 < u1 ∧ u2 < 0) then G b a c
  else G c a b
/-- Per-octant `2^20`-scaled alias-sum bound on `|Δ_0 + Δ_1 + Δ_2| / ‖Δ‖^2` at `μ = modFold3D 127
  Δ`. -/
def gAliasNat (μ : Fin 3 → ℤ) : ℕ := gAliasGen3 fLin fOneNegSingle (μ 0) (μ 1) (μ 2)
/-- Real-valued per-coset octant alias bound `gAliasNat μ / 2^20`. -/
noncomputable def gAlias (μ : Fin 3 → ℤ) : ℝ := (gAliasNat μ : ℝ) / 1048576
theorem gAlias_nonneg (μ : Fin 3 → ℤ) : 0 ≤ gAlias μ := by
  unfold gAlias
  positivity
private theorem abs_add3_div_sq3_le_fOneNegSingle_signed {d0 d1 d2 u0 u1 u2 : ℤ}
    (hd0 : -254 ≤ d0 ∧ d0 ≤ 254) (hd1 : -254 ≤ d1 ∧ d1 ≤ 254) (hd2 : -254 ≤ d2 ∧ d2 ≤ 254)
    (hu0 : -127 ≤ u0 ∧ u0 ≤ 127) (hu1 : -127 ≤ u1 ∧ u1 ≤ 127) (hu2 : -127 ≤ u2 ∧ u2 ≤ 127)
    (habc : 0 < u0.natAbs + u1.natAbs + u2.natAbs)
    (hm0 : modFoldCoord 127 d0 = u0) (hm1 : modFoldCoord 127 d1 = u1) (hm2 : modFoldCoord 127 d2 =
      u2)
    (hsign : (u0 < 0 ∧ 0 ≤ u1 ∧ 0 ≤ u2) ∨ (0 < u0 ∧ u1 < 0 ∧ u2 < 0)) :
    |(d0 : ℝ) + (d1 : ℝ) + (d2 : ℝ)| / ((d0.natAbs ^ 2 + d1.natAbs ^ 2 + d2.natAbs ^ 2 : ℕ) : ℝ) ≤
      (fOneNegSingle u0.natAbs u1.natAbs u2.natAbs : ℝ) / 1048576 := by
  rcases hsign with hpos | hneg
  · exact abs_add3_div_sq3_le_fOneNegSingle hd0 hd1 hd2 (by omega) (by omega) (by omega) habc (by
    omega) (by omega) (by omega)
  · have h := abs_add3_div_sq3_le_fOneNegSingle (d0 := -d0) (d1 := -d1) (d2 := -d2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) habc
      (by
        rw [modFoldCoord_127_neg hd0]
        omega)
      (by
        rw [modFoldCoord_127_neg hd1]
        omega)
      (by
        rw [modFoldCoord_127_neg hd2]
        omega)
    have hnegSum : -(d0 : ℝ) + -(d1 : ℝ) + -(d2 : ℝ) = -((d0 : ℝ) + (d1 : ℝ) + (d2 : ℝ)) := by ring
    simpa only [Int.natAbs_neg, Int.cast_neg, hnegSum, abs_neg] using h
/-- Boolean sign `(false ↦ +1, true ↦ -1)` for the 8 cube/octant vertices. -/
def sgnBool (b : Bool) : ℤ := if b then -1 else 1
/-- Coordinatewise sign-flip involution on `Fin 3 → ℤ`. -/
def signFlip3 (s : Bool × Bool × Bool) (v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![sgnBool s.1 * v 0, sgnBool s.2.1 * v 1, sgnBool s.2.2 * v 2]
theorem signFlip3_invol (s : Bool × Bool × Bool) (v : Fin 3 → ℤ) : signFlip3 s (signFlip3 s v) =
    v := by
  ext i; fin_cases i <;> simp [signFlip3, sgnBool] <;> split_ifs <;> ring
theorem signFlip3_mem_nonzeroBox3D {s : Bool × Bool × Bool} {ν : Fin 3 →
    ℤ} (hν : ν ∈ nonzeroBox3D (127 : ℤ)) :
    signFlip3 s ν ∈ nonzeroBox3D (127 : ℤ) := by
  rcases (mem_nonzeroBox3D 127 ν).mp hν with ⟨hne, hbox⟩
  refine (mem_nonzeroBox3D 127 _).mpr ⟨fun h0 ↦ hne ?_, fun i ↦ ?_⟩
  · rw [← signFlip3_invol s ν, h0]
    ext i; fin_cases i <;> simp [signFlip3]
  · fin_cases i <;> [have hb := hbox 0; have hb := hbox 1; have hb := hbox 2] <;>
      simp [signFlip3, sgnBool] <;> split_ifs <;> omega
private theorem sum_bool_sgnBool_mul (x : ℤ) (f : ℤ → ℕ) :
    (∑ b : Bool, f (sgnBool b * x)) = f (-((x.natAbs : ℤ))) + f ((x.natAbs : ℤ)) := by
  rw [Fintype.sum_bool]
  rcases Int.natAbs_eq x with hx | hx
  · conv_lhs =>
      rw [hx]
      simp only [sgnBool, ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul]
  · conv_lhs =>
      rw [hx]
      simp only [sgnBool, ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul, neg_neg]
    exact Nat.add_comm _ _
theorem sum_signFlip3_involution (s : Bool × Bool × Bool) (f : (Fin 3 → ℤ) → ℝ) :
    ∑ ν ∈ nonzeroBox3D (127 : ℤ), f (signFlip3 s ν) = ∑ μ ∈ nonzeroBox3D (127 : ℤ), f μ := by
  refine Finset.sum_bij (fun ν _ ↦ signFlip3 s ν) (fun ν hν ↦ signFlip3_mem_nonzeroBox3D hν)
    (fun ν₁ _ ν₂ _ h ↦ by rw [← signFlip3_invol s ν₁, h, signFlip3_invol])
    (fun μ hμ ↦ ⟨signFlip3 s μ, signFlip3_mem_nonzeroBox3D hμ, signFlip3_invol s μ⟩) (fun _ _ ↦ rfl)
private theorem sum_signFlip3_gAliasGen_le (F G : ℕ → ℕ → ℕ → ℕ)
    (h0L : ∀ y z, F 0 y z ≤ G 0 y z) (h0YZ : ∀ x, F x 0 0 ≤ G x 0 0)
    (hf10 : ∀ x z, F x 0 z = F 0 x z) (hf12 : ∀ x y, F x y 0 = F 0 x y) (hfSwap : ∀ y z,
      F 0 y z = F 0 z y) (ν : Fin 3 → ℤ) :
    (∑ s : Bool × Bool × Bool,
      gAliasGen3 F G (sgnBool s.1 * ν 0) (sgnBool s.2.1 * ν 1) (sgnBool s.2.2 * ν 2)) ≤
      2 * (F (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs + (G (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs +
          (G (ν 1).natAbs (ν 0).natAbs (ν 2).natAbs + G (ν 2).natAbs (ν 0).natAbs (ν 1).natAbs))) :=
            by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,
    fun x0 x1 ↦ sum_bool_sgnBool_mul (ν 2) (fun u2 ↦
      gAliasGen3 F G x0 x1 u2), Finset.sum_add_distrib,
    fun x0 u2 ↦ sum_bool_sgnBool_mul (ν 1) (fun u1 ↦
      gAliasGen3 F G x0 u1 u2), Finset.sum_add_distrib,
    fun u1 u2 ↦ sum_bool_sgnBool_mul (ν 0) (fun u0 ↦ gAliasGen3 F G u0 u1 u2)]
  set a := (ν 0).natAbs
  set b := (ν 1).natAbs
  set c := (ν 2).natAbs
  have hp1 (n : ℕ) : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) ∧ (0 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) ∧
      ¬ (((n + 1 : ℕ) : ℤ) < 0) ∧ ¬ (((n + 1 : ℕ) : ℤ) ≤ 0) :=
    ⟨by omega, by omega, by omega, by omega⟩
  have hn1 (n : ℕ) : -((n + 1 : ℕ) : ℤ) < 0 ∧ -((n + 1 : ℕ) : ℤ) ≤ 0 ∧
      ¬ ((0 : ℤ) < -((n + 1 : ℕ) : ℤ)) ∧ ¬ ((0 : ℤ) ≤ -((n + 1 : ℕ) : ℤ)) :=
    ⟨by omega, by omega, by omega, by omega⟩
  rcases a with _ | a' <;> rcases b with _ | b' <;> rcases c with _ | c' <;>
    simp only [gAliasGen3, Nat.cast_zero, neg_zero, Int.natAbs_zero, Int.natAbs_neg,
      Int.natAbs_natCast, lt_self_iff_false, le_refl, fun n ↦ (hp1 n).1, fun n ↦
      (hp1 n).2.1, fun n ↦ (hp1 n).2.2.1, fun n ↦ (hp1 n).2.2.2, fun n ↦ (hn1 n).1, fun n ↦
      (hn1 n).2.1, fun n ↦ (hn1 n).2.2.1, fun n ↦
      (hn1 n).2.2.2, and_true, and_false, or_true, or_false, ite_true, ite_false]
  · linarith [h0L 0 0]
  · linarith [h0L 0 (c' + 1), h0YZ (c' + 1), hf12 (c' + 1) 0, hfSwap 0 (c' + 1)]
  · linarith [h0L (b' + 1) 0, h0L 0 (b' + 1), h0YZ (b' + 1), hf12 (b' + 1) 0, hfSwap (b' + 1) 0]
  · linarith [h0L (b' + 1) (c' + 1)]
  · linarith [h0L (a' + 1) 0, h0YZ (a' + 1), hf12 (a' + 1) 0]
  · linarith [h0L (a' + 1) (c' + 1), hf10 (a' + 1) (c' + 1)]
  · linarith [h0L (a' + 1) (b' + 1), hf12 (a' + 1) (b' + 1)]
  · omega
theorem sum_gAlias_127_le : ∑ μ ∈ nonzeroBox3D (127 : ℤ), gAlias μ ≤ 714141984672 / 4194304 := by
  have h0L (y z : ℕ) : fLin 0 y z ≤ fOneNegSingle 0 y z := by
    rcases h : y * y + z * z with _ | s'
    · rcases (⟨by nlinarith, by nlinarith⟩ : y = 0 ∧ z = 0) with ⟨rfl, rfl⟩
      rfl
    · dsimp only [fLin, fOneNegSingle, sq3Nat, ceilDiv20Den]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.zero_sub, Nat.add_zero,
        n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq]
      rw [h, (show Nat.beq (s' + 1) 0 = false from rfl), Nat.mul_comm (y + z) 1048576]
      exact le_max_of_le_left (le_max_left _ _)
  have h0YZ (x : ℕ) : fLin x 0 0 ≤ fOneNegSingle x 0 0 := by
    rcases x with _ | x'
    · rfl
    · dsimp only [fLin, fOneNegSingle, sq3Nat, ceilDiv20Den]
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_sub, Nat.zero_add, Nat.sub_zero,
        n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq]
      rw [show (x' + 1) * (x' + 1) = x' * x' + 2 * x' + 1 by ring,
        (show Nat.beq (x' * x' + 2 * x' + 1) 0 = false from rfl), Nat.mul_comm (x' + 1) 1048576]
      exact le_max_of_le_left (le_max_left _ _)
  have hf10 (x z : ℕ) : fLin x 0 z = fLin 0 x z := by
    dsimp only [fLin, sq3Nat]
    rw [show x + 0 + z = 0 + x + z by omega, show x * x + 0 * 0 + z * z = 0 * 0 + x * x + z * z by
      omega]
  have hf12 (x y : ℕ) : fLin x y 0 = fLin 0 x y := by
    dsimp only [fLin, sq3Nat]
    rw [show x + y + 0 = 0 + x + y by omega, show x * x + y * y + 0 * 0 = 0 * 0 + x * x + y * y by
      omega]
  have hfSwap (y z : ℕ) : fLin 0 y z = fLin 0 z y := by
    dsimp only [fLin, sq3Nat]
    rw [show 0 + y + z = 0 + z + y by omega, show 0 * 0 + y * y + z * z = 0 * 0 + z * z + y * y by
      omega]
  have h8 : 8 * (∑ μ ∈ nonzeroBox3D (127 : ℤ), gAlias μ) =
      ∑ ν ∈ nonzeroBox3D (127 : ℤ), ∑ s : Bool × Bool × Bool, gAlias (signFlip3 s ν) := by
    rw [Finset.sum_comm, ← (
      show (∑ _s : Bool × Bool × Bool, (∑ μ ∈ nonzeroBox3D (127 : ℤ),
        gAlias μ)) =
          8 * (∑ μ ∈ nonzeroBox3D (127 : ℤ), gAlias μ) by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        norm_num)]
    exact Finset.sum_congr rfl fun s _ ↦ (sum_signFlip3_involution s gAlias).symm
  have hpt (ν : Fin 3 → ℤ) : ∑ s : Bool × Bool × Bool, gAlias (signFlip3 s ν) ≤
        2 * ((fLin (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) +
          (fOneNeg3Sym (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ)) / 1048576 := by
    unfold gAlias
    rw [← Finset.sum_div]
    have hNat : ∑ s : Bool × Bool × Bool, gAliasNat (signFlip3 s ν) ≤
        2 * (fLin (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs +
          fOneNeg3Sym (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs) :=
      sum_signFlip3_gAliasGen_le fLin fOneNegSingle h0L h0YZ hf10 hf12 hfSwap ν
    have hnat : ((∑ s : Bool × Bool × Bool, gAliasNat (signFlip3 s ν) : ℕ) : ℝ) ≤
        ((2 * (fLin (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs +
          fOneNeg3Sym (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs) : ℕ) : ℝ) := by exact_mod_cast hNat
    push_cast at hnat
    linarith
  have hsum : ∑ ν ∈ nonzeroBox3D (127 : ℤ), ∑ s : Bool × Bool × Bool, gAlias (signFlip3 s ν) ≤
      2 * (248519819946 + 465622164726) / 1048576 := by
    refine (Finset.sum_le_sum fun ν _ ↦ hpt ν).trans ?_
    rw [← Finset.sum_div]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_fLin_127,
      show ∑ ν ∈ nonzeroBox3D (127 : ℤ),
        (fOneNeg3Sym (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) = 465622164726 by
        rw [(show (127 : ℤ) = ((127 : ℕ) : ℤ) from rfl),
          sum_nonzeroBox3D_eq_oct_natSum 127 fOneNeg3Sym
          fOneNeg3Sym_zero fOneNeg3Sym_swap12 fOneNeg3Sym_swap23, (show 127 + 1 = 128 from rfl),
          natSum_congr (fun k hk ↦
            (oneNegShellFast_eq (by omega)).symm), show natSum 128 oneNegShellFast =
            n1sNatSumFast 64 oneNegShellFast + n1sNatSumFast 64 (n1sShiftIdx 64 oneNegShellFast) by
              rw [n1sNatSumFast_eq, n1sNatSumFast_eq, n1sShiftIdx_eq]
              exact natSum_add_split 64 64 oneNegShellFast,
          Nat.eq_of_beq_eq_true oneNeg_chunk_lo, Nat.eq_of_beq_eq_true oneNeg_chunk_hi]
        norm_num]
  linarith
open MomSlots35Coulomb
open ModWrapCoarse8PureMomentum (projectile_momentum_mem_box3D)
open Slot3NuclearTruncBkPhysics (slot3ModWrapPieceBk)
/-- Normalized signed rounding residual `u_l(w) ∈ [-1, 1]` of nucleus `l` along axis `w` at `bk`
  bits. -/
noncomputable def uProton (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216) (w : Fin 3)
    : ℝ :=
  2 * ((nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) (c.nuclei l w) : ℝ) -
    (2 : ℝ) ^ bk * (c.nuclei l w / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)))
theorem uProton_bounds (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216) (w : Fin 3) :
    -1 ≤ uProton bk c l w ∧ uProton bk c l w ≤ 1 := by
  unfold uProton nearestProtonCoord
  set t : ℝ := (2 : ℝ) ^ bk * (c.nuclei l w / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
  have hle := Int.floor_le (t + 1 / 2)
  have hlt := Int.lt_floor_add_one (t + 1 / 2)
  exact ⟨by linarith, by linarith⟩
/-- Trilinear convex weight of `u ∈ [-1, 1]^3` at cube vertex `(sgnBool s.1, sgnBool s.2.1,
  sgnBool s.2.2)`. -/
noncomputable def cubeWt (u : Fin 3 → ℝ) (s : Bool × Bool × Bool) : ℝ :=
  ((1 + (sgnBool s.1 : ℝ) * u 0) / 2) * ((1 + (sgnBool s.2.1 : ℝ) * u 1) / 2) * ((1 +
    (sgnBool s.2.2 : ℝ) * u 2) / 2)
theorem cubeWt_nonneg {u : Fin 3 → ℝ} (hu : ∀ w,
    -1 ≤ u w ∧ u w ≤ 1) (s : Bool × Bool × Bool) : 0 ≤ cubeWt u s := by
  have hf (b : Bool) (w : Fin 3) : 0 ≤ (1 + (sgnBool b : ℝ) * u w) / 2 := by
    cases b <;> dsimp [sgnBool] <;> push_cast <;> linarith [hu w]
  exact mul_nonneg (mul_nonneg (hf s.1 0) (hf s.2.1 1)) (hf s.2.2 2)
theorem sum_cubeWt_eq_one (u : Fin 3 → ℝ) : ∑ s : Bool × Bool × Bool, cubeWt u s = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [cubeWt, sgnBool]
  push_cast; ring
theorem norm_quantizedStructureFactorNearest_sub_div_le_cubeWt (bk : ℕ) (c :
    SpecsAux.SpecMirror.Configuration) {Δ ν : Fin 3 → ℤ}
    (hbox : Δ ∈ box3D (2 * (127 : ℤ))) (hν : ν ∈ nonzeroBox3D (127 : ℤ)) (hm : modFold3D 127 Δ =
      ν) :
    ‖quantizedStructureFactorNearest bk c Δ - structureFactor c Δ‖ / (sumNatAbsSq Δ : ℝ) ≤ (π /
      (2 : ℝ) ^ bk) *
        ∑ l : Fin 216, ∑ s : Bool × Bool × Bool,
          cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν) := by
  have hFoldNe {v u : Fin 3 → ℤ} (hu : u ≠ 0) (hf : modFold3D 127 v = u) : v ≠ 0 := fun h0 ↦ hu (by
    rw [← hf, h0]
    ext w
    simp [modFold3D, modFoldCoord, modWrapCoord])
  have hΔ_ne : Δ ≠ 0 := hFoldNe ((mem_nonzeroBox3D 127 ν).mp hν).1 hm
  have hSΔ_pos : (0 : ℝ) < (sumNatAbsSq Δ : ℝ) :=
    Nat.cast_pos.mpr (sumNatAbsSq_pos_of_ne_zero hΔ_ne)
  set L : ℝ := SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)
  have hL_pos : 0 < L := by
    dsimp [L]
    unfold SpecsAux.SpecMirror.cellVolume
    positivity
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ bk := by positivity
  have hAlias {Δ' μ : Fin 3 → ℤ} (hb' : Δ' ∈ box3D (2 * (127 : ℤ)))
      (hμ : μ ∈ nonzeroBox3D (127 : ℤ)) (hm' : modFold3D 127 Δ' = μ) :
      |(Δ' 0 : ℝ) + (Δ' 1 : ℝ) + (Δ' 2 : ℝ)| / (sumNatAbsSq Δ' : ℝ) ≤ gAlias μ := by
    have hd := (mem_box3D _ _).mp hb'
    have _ := hd 0
    have _ := hd 1
    have _ := hd 2
    rcases (mem_nonzeroBox3D 127 μ).mp hμ with ⟨hμ_ne, hμ_box⟩
    have _ := hμ_box 0
    have _ := hμ_box 1
    have _ := hμ_box 2
    have habc : 0 < (μ 0).natAbs + (μ 1).natAbs + (μ 2).natAbs := by
      by_contra h0
      exact hμ_ne (funext fun i ↦ by fin_cases i <;> simp <;> omega)
    have hsqΔ : sumNatAbsSq Δ' = (Δ' 0).natAbs ^ 2 + (Δ' 1).natAbs ^ 2 + (Δ' 2).natAbs ^ 2 :=
      Fin.sum_univ_three _
    unfold gAlias gAliasNat gAliasGen3
    dsimp only
    split_ifs with hc1 hc2 hc3
    · have hSΔ'_pos : (0 : ℝ) < (sumNatAbsSq Δ' : ℝ) :=
        Nat.cast_pos.mpr (sumNatAbsSq_pos_of_ne_zero (hFoldNe hμ_ne hm'))
      have hSμ_pos : (0 : ℝ) < (sumNatAbsSq μ : ℝ) :=
        Nat.cast_pos.mpr (sumNatAbsSq_pos_of_ne_zero hμ_ne)
      have htri : |(Δ' 0 : ℝ) + (Δ' 1 : ℝ) + (Δ' 2 : ℝ)| ≤ (natAbsSum Δ' : ℝ) := by
        unfold natAbsSum
        rw [Fin.sum_univ_three]
        push_cast
        have habs (z : ℤ) : |(z : ℝ)| = (z.natAbs : ℝ) := by
          rcases Int.natAbs_eq z with hz | hz <;> conv_lhs => rw [hz]
          · rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
          · rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
        linarith [habs (Δ' 0), habs (Δ' 1), habs (Δ' 2),
          abs_add_le (Δ' 0 : ℝ) (Δ' 1 : ℝ), abs_add_le ((Δ' 0 : ℝ) + (Δ' 1 : ℝ)) (Δ' 2 : ℝ)]
      have h2 : (natAbsSum Δ' : ℝ) / (sumNatAbsSq Δ' : ℝ) ≤ (natAbsSum μ : ℝ) /
        (sumNatAbsSq μ : ℝ) := by
        rw [div_le_div_iff₀ hSΔ'_pos hSμ_pos, ← hm']
        exact_mod_cast natAbsSum_mul_sumNatAbsSq_modFold3D_le 127 hb'
      exact ((div_le_div_of_nonneg_right htri hSΔ'_pos.le).trans h2).trans
        (natAbsSum_div_sumNatAbsSq_le_fLin hμ_ne)
    · rw [hsqΔ]
      exact abs_add3_div_sq3_le_fOneNegSingle_signed (by omega) (by omega) (by omega)
        (hμ_box 0) (hμ_box 1) (hμ_box 2) habc (congrFun hm' 0) (congrFun hm' 1) (congrFun hm' 2) hc2
    · rw [hsqΔ, show (Δ' 0 : ℝ) + (Δ' 1 : ℝ) + (Δ' 2 : ℝ) = (Δ' 1 : ℝ) + (Δ' 0 : ℝ) + (Δ' 2 : ℝ) by
      ring,
        show (Δ' 0).natAbs ^ 2 + (Δ' 1).natAbs ^ 2 + (Δ' 2).natAbs ^ 2 =
          (Δ' 1).natAbs ^ 2 + (Δ' 0).natAbs ^ 2 + (Δ' 2).natAbs ^ 2 by omega]
      exact abs_add3_div_sq3_le_fOneNegSingle_signed (by omega) (by omega) (by omega)
        (hμ_box 1) (hμ_box 0) (hμ_box 2) (by omega) (congrFun hm' 1) (congrFun hm' 0) (congrFun hm'
          2) (by omega)
    · rw [hsqΔ, show (Δ' 0 : ℝ) + (Δ' 1 : ℝ) + (Δ' 2 : ℝ) = (Δ' 2 : ℝ) + (Δ' 0 : ℝ) + (Δ' 1 : ℝ) by
      ring,
        show (Δ' 0).natAbs ^ 2 + (Δ' 1).natAbs ^ 2 + (Δ' 2).natAbs ^ 2 =
          (Δ' 2).natAbs ^ 2 + (Δ' 0).natAbs ^ 2 + (Δ' 1).natAbs ^ 2 by omega]
      exact abs_add3_div_sq3_le_fOneNegSingle_signed (by omega) (by omega) (by omega)
        (hμ_box 2) (hμ_box 0) (hμ_box 1) (by omega) (congrFun hm' 2) (congrFun hm' 0) (congrFun hm'
          1) (by omega)
  have hl_bound (l : Fin 216) : ‖Complex.exp ((thetaProtonNearest bk c l Δ : ℂ) * Complex.I) -
          Complex.exp (-(waveVector Δ ⬝ᵥ c.nuclei l) * Complex.I)‖ / (sumNatAbsSq Δ : ℝ) ≤
        (π / (2 : ℝ) ^ bk) * ∑ s : Bool × Bool × Bool,
          cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν) := by
    have hexp : ‖Complex.exp ((thetaProtonNearest bk c l Δ : ℂ) * Complex.I) -
        Complex.exp (-(waveVector Δ ⬝ᵥ c.nuclei l) * Complex.I)‖ ≤ (π / (2 : ℝ) ^ bk) *
          |(Δ 0 : ℝ) * uProton bk c l 0 + (Δ 1 : ℝ) * uProton bk c l 1 + (Δ 2 : ℝ) *
            uProton bk c l 2| := by
      rw [show -(waveVector Δ ⬝ᵥ c.nuclei l) * Complex.I =
        ((-(waveVector Δ ⬝ᵥ c.nuclei l) : ℝ) : ℂ) * Complex.I by simp]
      refine (norm_exp_ofReal_mul_I_sub_le _ _).trans ?_
      have hdiff : thetaProtonNearest bk c l Δ - (-(waveVector Δ ⬝ᵥ c.nuclei l)) = (-(π /
        (2 : ℝ) ^ bk)) *
            ((Δ 0 : ℝ) * uProton bk c l 0 + (Δ 1 : ℝ) * uProton bk c l 1 + (Δ 2 : ℝ) *
              uProton bk c l 2) := by
        unfold thetaProtonNearest uProton waveVector dotProduct
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        dsimp [L]
        field_simp [hL_pos.ne', h2_pos.ne']
        ring
      rw [hdiff, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    have hcoord : (Δ 0 : ℝ) * uProton bk c l 0 + (Δ 1 : ℝ) * uProton bk c l 1 + (Δ 2 : ℝ) *
      uProton bk c l 2 =
        ∑ s : Bool × Bool × Bool, cubeWt (uProton bk c l) s *
          ((sgnBool s.1 : ℝ) * (Δ 0 : ℝ) + (sgnBool s.2.1 : ℝ) * (Δ 1 : ℝ) + (sgnBool s.2.2 : ℝ) *
            (Δ 2 : ℝ)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [cubeWt, sgnBool]
      push_cast
      ring
    have hcube : |(Δ 0 : ℝ) * uProton bk c l 0 + (Δ 1 : ℝ) * uProton bk c l 1 + (Δ 2 : ℝ) *
      uProton bk c l 2| /
          (sumNatAbsSq Δ : ℝ) ≤ ∑ s : Bool × Bool × Bool,
            cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν) := by
      rw [hcoord]
      have habs : |∑ s : Bool × Bool × Bool, cubeWt (uProton bk c l) s *
              ((sgnBool s.1 : ℝ) * (Δ 0 : ℝ) + (sgnBool s.2.1 : ℝ) * (Δ 1 : ℝ) +
                (sgnBool s.2.2 : ℝ) * (Δ 2 : ℝ))| ≤
            ∑ s : Bool × Bool × Bool, cubeWt (uProton bk c l) s *
              |(sgnBool s.1 : ℝ) * (Δ 0 : ℝ) + (sgnBool s.2.1 : ℝ) * (Δ 1 : ℝ) +
                (sgnBool s.2.2 : ℝ) * (Δ 2 : ℝ)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (cubeWt_nonneg (uProton_bounds bk c l) s)]
      refine (div_le_div_of_nonneg_right habs hSΔ_pos.le).trans ?_
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun s _ ↦ ?_
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (cubeWt_nonneg (uProton_bounds bk c l) s)
      have hsbox : signFlip3 s Δ ∈ box3D (2 * (127 : ℤ)) :=
        (mem_box3D _ _).mpr fun i ↦ by
          have _ := (mem_box3D _ _).mp hbox 0
          have _ := (mem_box3D _ _).mp hbox 1
          have _ := (mem_box3D _ _).mp hbox 2
          fin_cases i <;> simp [signFlip3, sgnBool] <;> split_ifs <;> omega
      have hsq_eq : sumNatAbsSq (signFlip3 s Δ) = sumNatAbsSq Δ :=
        Finset.sum_congr rfl fun i _ ↦ by
          fin_cases i <;> simp [signFlip3, sgnBool] <;> split_ifs <;> simp
      have hmFlip : modFold3D 127 (signFlip3 s Δ) = signFlip3 s ν := by
        rw [← hm]
        have hd (i : Fin 3) : -254 ≤ Δ i ∧ Δ i ≤ 254 := by
          have := (mem_box3D _ _).mp hbox i
          omega
        ext i
        fin_cases i
        · cases hs : s.1 <;> simp [modFold3D, signFlip3, sgnBool, hs, modFoldCoord_127_neg (hd 0)]
        · cases hs : s.2.1 <;> simp [modFold3D, signFlip3, sgnBool, hs, modFoldCoord_127_neg (hd 1)]
        · cases hs : s.2.2 <;> simp [modFold3D, signFlip3, sgnBool, hs, modFoldCoord_127_neg (hd 2)]
      have hg := hAlias hsbox (signFlip3_mem_nonzeroBox3D hν) hmFlip
      rw [hsq_eq] at hg
      simpa [signFlip3] using hg
    exact (div_le_div_of_nonneg_right hexp hSΔ_pos.le).trans
      ((mul_div_assoc _ _ _).trans_le (mul_le_mul_of_nonneg_left hcube (by positivity)))
  unfold quantizedStructureFactorNearest structureFactor
  rw [← Finset.sum_sub_distrib]
  exact (div_le_div_of_nonneg_right (norm_sum_le _ _) hSΔ_pos.le).trans
    ((Finset.sum_div _ _ _).trans_le ((Finset.sum_le_sum fun l _ ↦
      hl_bound l).trans_eq (Finset.mul_sum _ _ _).symm))
open Classical in
/-- Octant sign-cancellation operator-norm bound on `modWrapProjNucOp c 38 36 bk (2 / 42) 1 -
  projNucOp c`:
replaces `248519819946 / 1048576` (`237006.97`) with `714141984672 / 4194304` (`170264.62`,
`1.3921×` smaller)
and `31416 / 10000` with `31415927 / 10000000` (`π ≤ 3.1415927`), at **zero extra T-gates**. -/
theorem slot3_norm_modWrapProjNucOp_bk_sub_le_octant (bk : ℕ) (c :
    SpecsAux.SpecMirror.Configuration) :
    ‖modWrapProjNucOp c 38 36 bk (2 / 42) 1 - projNucOp c‖ ≤
      (216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ)) * (2050880366 / 1048576) +
        (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (219901 / 32) +
        (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
          (714141984672 / 4194304) := by
  let bnd : (Fin 3 → ℤ) → ℝ := fun ν ↦
    (216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ)) * (1 / (sumNatAbsSq ν : ℝ)) +
      (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (1 / (2 : ℝ) ^ (2 * shellIndex ν)) +
      (2 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
        ∑ l : Fin 216, ∑ s : Bool × Bool × Bool, cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν)
  have hPiece {ν : Fin 3 → ℤ} (hν_mem : ν ∈ nonzeroBox3D (127 : ℤ)) : ‖slot3ModWrapPieceBk bk c ν‖ ≤
    bnd ν := by
    have hsum_nn : 0 ≤ ∑ l : Fin 216, ∑ s : Bool × Bool × Bool,
      cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν) :=
      Finset.sum_nonneg fun l _ ↦ Finset.sum_nonneg fun s _ ↦
        mul_nonneg (cubeWt_nonneg (uProton_bounds bk c l) s) (gAlias_nonneg _)
    have hE3_nn : 0 ≤ bnd ν :=
      add_nonneg (add_nonneg (by positivity) (by positivity)) (mul_nonneg (by positivity) hsum_nn)
    have hν_ne : ν ≠ 0 := ((mem_nonzeroBox3D 127 ν).mp hν_mem).1
    apply norm_le_of_weightedPartialPerm (slot3ModWrapPieceBk bk c ν) hE3_nn
    · intro x y₁ y₂ h1 h2
      simp only [slot3ModWrapPieceBk, Matrix.of_apply, ne_eq, ite_eq_right_iff,
        Classical.not_imp] at h1 h2
      refine (momentum_eq_iff_eq_of_isGridState h1.1.2.1 h2.1.2.1).mp fun a ↦ ?_
      by_cases hap : a = .projectile
      · exact hap ▸ modFold3D_sub_inj_right 127 (projectile_momentum_mem_box3D x)
          (projectile_momentum_mem_box3D y₁) (projectile_momentum_mem_box3D y₂)
          (h1.1.2.2.2.trans h2.1.2.2.2.symm)
      · exact (h1.1.2.2.1 a hap).symm.trans (h2.1.2.2.1 a hap)
    · intro x₁ x₂ y h1 h2
      simp only [slot3ModWrapPieceBk, Matrix.of_apply, ne_eq, ite_eq_right_iff,
        Classical.not_imp] at h1 h2
      refine (momentum_eq_iff_eq_of_isGridState h1.1.1 h2.1.1).mp fun a ↦ ?_
      by_cases hap : a = .projectile
      · exact hap ▸ modFold3D_sub_inj_left 127 (projectile_momentum_mem_box3D x₁)
          (projectile_momentum_mem_box3D x₂) (projectile_momentum_mem_box3D y)
          (h1.1.2.2.2.trans h2.1.2.2.2.symm)
      · exact (h1.1.2.2.1 a hap).trans (h2.1.2.2.1 a hap).symm
    · intro x y
      dsimp [slot3ModWrapPieceBk]
      split_ifs with hc
      · set Δ : Fin 3 → ℤ :=
        SpecsAux.SpecMirror.momentum x .projectile - SpecsAux.SpecMirror.momentum y .projectile
        have hbox : Δ ∈ box3D (2 * (127 : ℤ)) := projectile_sub_mem_box3D_254 x y
        have hΔ : Δ ≠ 0 := fun h0 ↦ hν_ne (by
          rw [← hc.2.2.2, h0]
          ext w
          simp [modFold3D, modFoldCoord, modWrapCoord])
        rcases dampedModWrapKernelApprox_bounds 38 36 127
            (by norm_num : (0 : ℝ) < 2 / 42) (by norm_num : (0 : ℝ) ≤ 2) hΔ with ⟨hk_nn, hk_le,
              hk_err⟩
        set Sq : ℂ := quantizedStructureFactorNearest bk c Δ
        set St : ℂ := structureFactor c Δ
        set Ka : ℝ := dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 Δ
        have hdecomp : (1 : ℂ) * Sq * (Ka : ℂ) -
            (SpecsAux.SpecMirror.charge SpecsAux.SpecMirror.Particle.projectile : ℂ) * St *
              (coulombKernel Δ : ℂ) =
            (Sq - St) * (Ka : ℂ) + St * ((Ka - 2 * coulombKernel Δ : ℝ) : ℂ) := by
          unfold SpecsAux.SpecMirror.charge
          push_cast
          ring
        rw [hdecomp]
        have htri : ‖(Sq - St) * (Ka : ℂ) + St * ((Ka - 2 * coulombKernel Δ : ℝ) : ℂ)‖ ≤
            ‖Sq - St‖ * Ka + 216 * (2 * coulombKernel Δ - Ka) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk_nn]
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hk_le)]
            exact mul_le_mul_of_nonneg_right (norm_structureFactor_le c Δ) (sub_nonneg.mpr hk_le)
        refine htri.trans ?_
        · have hdom : sumNatAbsSq ν ≤ sumNatAbsSq Δ := hc.2.2.2 ▸ sumNatAbsSq_modFold3D_le 127 hbox
          have hinv_le : (1 : ℝ) / (sumNatAbsSq Δ : ℝ) ≤ (1 : ℝ) / (sumNatAbsSq ν : ℝ) :=
            one_div_le_one_div_of_le (Nat.cast_pos.mpr (sumNatAbsSq_pos_of_ne_zero hν_ne)) (by
              exact_mod_cast hdom)
          have hck42_raw := forty_two_mul_coulombKernel_le Δ
          have hck2_Δ : Ka ≤ 2 * (4200000 / 4217638 : ℝ) / 42 * (1 / (sumNatAbsSq Δ : ℝ)) := by
            linarith [hk_le]
          have hpi_step := mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right pi_bounds_8digit.2 (by positivity : (0 : ℝ) ≤
              (2 : ℝ) ^ bk)) hsum_nn
          have hterm2 : ‖Sq - St‖ * Ka ≤ (2 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) /
            (42 * (2 : ℝ) ^ bk)) *
                ∑ l : Fin 216, ∑ s : Bool × Bool × Bool,
                  cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν) :=
            (mul_le_mul_of_nonneg_left hck2_Δ (norm_nonneg _)).trans
              ((by ring : ‖Sq - St‖ * (2 * (4200000 / 4217638 : ℝ) / 42 * (1 /
                (sumNatAbsSq Δ : ℝ))) =
                  (2 * (4200000 / 4217638 : ℝ) / 42) * (‖Sq - St‖ /
                    (sumNatAbsSq Δ : ℝ))).trans_le ((mul_le_mul_of_nonneg_left
                  ((norm_quantizedStructureFactorNearest_sub_div_le_cubeWt bk c hbox hν_mem
                    hc.2.2.2).trans hpi_step)
                  (by positivity)).trans_eq (by ring)))
          have herr216 := mul_le_mul_of_nonneg_left hk_err (by norm_num : (0 : ℝ) ≤ 216)
          rw [hc.2.2.2, pow_add] at herr216
          have hbd_part :=
            mul_le_mul_of_nonneg_left (hck42_raw.trans (mul_le_mul_of_nonneg_left hinv_le (by
            norm_num)))
            (by positivity : (0 : ℝ) ≤ 216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36))
          dsimp only [bnd]
          linarith [
            show 216 * ((2 / 42 : ℝ) / ((2 : ℝ) ^ (2 * shellIndex ν) * (2 : ℝ) ^ 38)) =
              (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (1 / (2 : ℝ) ^ (2 * shellIndex ν)) by ring]
      · rw [norm_zero]
        exact hE3_nn
  have hpart : modWrapProjNucOp c 38 36 bk (2 / 42) 1 - projNucOp c =
      ∑ ν ∈ nonzeroBox3D (127 : ℤ), slot3ModWrapPieceBk bk c ν := by
    unfold modWrapProjNucOp projNucOp
    ext x y
    rw [Matrix.sub_apply, operator_sum_apply, Matrix.of_apply, Matrix.of_apply]
    by_cases hcond : IsGridState x ∧ IsGridState y ∧
        (∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
          SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y b)
    · rw [ite_true_eq hcond, ite_true_eq hcond]
      set Δ : Fin 3 → ℤ :=
        SpecsAux.SpecMirror.momentum x .projectile - SpecsAux.SpecMirror.momentum y .projectile
      by_cases hΔ : Δ = 0
      · have hfold0 : modFold3D 127 Δ = 0 := by
          rw [hΔ]
          ext w
          simp [modFold3D, modFoldCoord, modWrapCoord]
        have hrhs0 : (∑ ν ∈ nonzeroBox3D (127 : ℤ), slot3ModWrapPieceBk bk c ν x y) = 0 := by
          refine Finset.sum_eq_zero fun ν hν ↦ ?_
          dsimp [slot3ModWrapPieceBk]
          rw [ite_false_eq]
          rintro ⟨_, _, _, heq⟩
          exact ((mem_nonzeroBox3D 127 ν).mp hν).1 (heq.symm.trans hfold0)
        rw [hrhs0, hΔ, dampedModWrapKernelApprox_zero]
        unfold coulombKernel waveNumberSq waveVector dotProduct
        simp
      · rw [Finset.sum_eq_single (modFold3D 127 Δ)]
        · dsimp [slot3ModWrapPieceBk]
          rw [ite_true_eq ⟨hcond.1, hcond.2.1, hcond.2.2, rfl⟩]
        · intro ν _ hne
          dsimp [slot3ModWrapPieceBk]
          exact ite_false_eq (fun ⟨_, _, _, heq⟩ ↦ hne heq.symm) _ _
        · exact fun hnot ↦ (hnot (modFold3D_mem_nonzeroBox3D 127
            ((mem_nonzeroBox3D (2 * (127 : ℤ)) Δ).mpr
              ⟨hΔ, (mem_box3D _ _).mp (projectile_sub_mem_box3D_254 x y)⟩))).elim
    · rw [ite_false_eq hcond, ite_false_eq hcond, sub_zero, eq_comm]
      refine Finset.sum_eq_zero fun ν _ ↦ ?_
      dsimp [slot3ModWrapPieceBk]
      exact ite_false_eq (fun ⟨h1, h2, h3, _⟩ ↦ hcond ⟨h1, h2, h3⟩) _ _
  rw [hpart]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ν hν ↦ hPiece hν).trans ?_)
  have hsplit : ∑ ν ∈ nonzeroBox3D (127 : ℤ),
    bnd ν = (216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ)) *
        (∑ ν ∈ nonzeroBox3D (127 : ℤ),
          (1 : ℝ) / (sumNatAbsSq ν : ℝ)) + (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) *
        (∑ ν ∈ nonzeroBox3D (127 : ℤ), (1 : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν)) +
      (2 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
        (∑ ν ∈ nonzeroBox3D (127 : ℤ), ∑ l : Fin 216, ∑ s : Bool × Bool × Bool,
          cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν)) := by
    dsimp only [bnd]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hcube_sum : (∑ ν ∈ nonzeroBox3D (127 : ℤ), ∑ l : Fin 216, ∑ s : Bool × Bool × Bool,
        cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν)) = 216 * (∑ μ ∈ nonzeroBox3D (127 : ℤ),
          gAlias μ) := by
    rw [Finset.sum_comm]
    have hl (l : Fin 216) : (∑ ν ∈ nonzeroBox3D (127 : ℤ), ∑ s : Bool × Bool × Bool,
          cubeWt (uProton bk c l) s * gAlias (signFlip3 s ν)) = ∑ μ ∈ nonzeroBox3D (127 : ℤ),
            gAlias μ := by
      rw [Finset.sum_comm]
      simp_rw [fun s ↦ (Finset.mul_sum _ _ _).symm.trans
        (congrArg (cubeWt (uProton bk c l) s * ·) (sum_signFlip3_involution s gAlias)),
        ← Finset.sum_mul, sum_cubeWt_eq_one, one_mul]
    simp_rw [hl]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hsplit, hcube_sum, sum_inv_four_pow_shellIndex_127_eq]
  have h1 := mul_le_mul_of_nonneg_left sum_inv_sumNatAbsSq_127_le
    (by positivity : (0 : ℝ) ≤ 216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ))
  have h2 := mul_le_mul_of_nonneg_left sum_gAlias_127_le
    (by positivity : (0 : ℝ) ≤ 432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 *
      (2 : ℝ) ^ bk))
  linarith [
      show (2 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
        (216 * ∑ μ ∈ nonzeroBox3D (127 : ℤ), gAlias μ) =
    (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
      (∑ μ ∈ nonzeroBox3D (127 : ℤ), gAlias μ) by ring]
end Section2OctantNuc
section Section3UltraBk
open SubvoxelNuclearTrunc36Physics (trunc36Cfg)
open Slot3NuclearTruncBkPhysics (truncBkNucCfg modWrapProjNucOp_trunc36Cfg_truncBkNucCfg)
open MomSlots35Coulomb
open Slot5MatrixAndScaleCert
open MomSlots35Slot3ProjNuclear
open MomSlots35Slot3ProjNuclear.Slot3CleanPrim
open Slot3Exact216Oracle80
open Slot3Norm1s36Physics80
open Slot3Norm1s36CoreWide
open Slot3Prep273AndSwap3
open Slot3PrepWideAndSwap3 (mkSlot3Swap3MomOracle80Gen_Wide)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysCoreWires)
open OraAndPrepBundle (castNatUnitary castNatUnitary_embedUnitary catUnitaryToFullSys
  momCatWires_eq_fullSysCatWires)
open SingleCatSpine (rTopCatSlice)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle momCoreWires)
open ZeroSubwireCoinPrep80 (wIdealRat)
open InterWalkRSum42Hoist (qreg_ext FixesLow3924 h3924_momCore)
open StepBBlock0 (sel107_80 sel107_80_val s3ItePos s3IteNeg)
open Leaf3Slot3Norm1sWidth204 (coreWires80 rCore0_36 rCat0_36 sel143_80_36 r143In149
  r143In149_embed_uCore143Norm1s uSlot3Cat36Norm1s uSlot3Swap3Cat36Norm1s
  fixesLow3924_uSlot3EffNorm1s)
open Slot3Exact216Oracle80_Wide (uPiSwap3Core_prep273_eq_streamUnc)
open Leaf4Ext48TopStitch (CommutesWithReg rCtrl3InCoreCat)
open Barrel3PassSelectStitch (rCoreInCT80)
open Slot3StreamUncK35Shift3 (rEC80)
open Leaf3HadCutBridge (hCoreCat36_eq rCoreInCoreCat36 uSlot3HadCutCat36FullSys
  commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut)
open SelectStitch (rCoreTopCatInCT)
/-- Tight unrounded nano-Ha (`10^-9` Ha) Slot-3 intrinsic error ceiling combining:
- Exact certified `(t, kBits)` lattice discrepancy sum (`n1sOctSum128CertVal t`, 6 tiers including
`.t30_18`),
- Tight `506 / 2^37` `216`-nucleus qutrit state-preparation bound, and
- Octant sign-cancellation `bk`-bit nuclear truncation bound (`714141984672 / 4194304`, `π ≤
3.1415927`). -/
def s3EpsUltraBkNano (t : Norm1sTier) (bk : ℕ) : ℕ :=
  let row : List ℕ := match t with
    | .t26_18 => [1949206, 2028934, 2188389, 2507300, 3145121, 4420764, 6972050, 12074622, 22279765,
        42690052, 83510626, 165151773, 328434067, 654998656, 1308127834, 2614386189, 5226902900]
    | .t26_17 => [1119652, 1199380, 1358835, 1677746, 2315568, 3591210, 6142496, 11245068, 21450211,
        41860498, 82681072, 164322219, 327604513, 654169102, 1307298280, 2613556635, 5226073346]
    | .t27_17 => [604643, 684370, 843826, 1162736, 1800558, 3076201, 5627487, 10730058, 20935202,
        41345489, 82166062, 163807209, 327089504, 653654093, 1306783270, 2613041626, 5225558336]
    | .t29_18 => [312786, 392514, 551969, 870880, 1508702, 2784345, 5335630, 10438202, 20643346,
        41053632, 81874206, 163515353, 326797648, 653362236, 1306491414, 2612749769, 5225266480]
    | .t29_17 => [210653, 290380, 449836, 768746, 1406568, 2682211, 5233497, 10336068, 20541212,
        40951499, 81772072, 163413219, 326695514, 653260103, 1306389280, 2612647636, 5225164346]
    | .t30_18 => [196865, 276592, 436048, 754958, 1392780, 2668423, 5219709, 10322280, 20527424,
        40937710, 81758284, 163399431, 326681726, 653246315, 1306375492, 2612633848, 5225150558]
    | _ => List.replicate 17 5226902900
  row.getD (if 20 ≤ bk ∧ bk ≤ 36 then 36 - bk else 16) 5226902900
def s3BaseNum : Norm1sTier → ℕ
  | .t26_18 => 104865159059105286985
  | .t26_17 => 58332765518743722451
  | .t27_17 => 29444182810937067283
  | .t29_18 => 13073003686733941033
  | .t29_17 => 7343980679149678159
  | .t30_18 => 6570564430460144497
  | _ => 0
/-- Unrounded 6-tier `(t, bk)` (`20 ≤ bk ∧ bk ≤ 36`) `Swap-3` `MomSingleSlotOracle 80 48 3`
with `epsIntr := (s3EpsUltraBkNano t bk : ℝ) / 1000000000`. -/
noncomputable def s3Swap3OracleNorm1sUltraBk_20 (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 20 ≤ bk ∧ bk ≤ 36) : MomSingleSlotOracle 80 48 3 :=
  mkSlot3Swap3MomOracle80Gen_Wide
    (fun _ ↦ wIdealRat 3) (fun _ ↦ 0) ((s3EpsUltraBkNano t bk : ℝ) / 1000000000)
    (fun cfg ↦ uCore149Norm1s t (truncBkNucCfg bk cfg))
    (fun cfg ↦ uCore3EffNorm1s t (truncBkNucCfg bk cfg) (le_refl 80))
    (fun cfg ↦ bUnitTwosNorm1sGen t (truncBkNucCfg bk cfg))
    (fun _ ↦ alphaSlot3_216_eq_wIdealRat3 ▸ alphaSlot3_216_pos_and_le_20123.1.le)
    (fun cfg U_catTwist hcol ↦
      uCore149Norm1s_intertwines t (truncBkNucCfg bk cfg) (le_refl 80) U_catTwist hcol)
    (fun cfg ↦ uSlot3EffNorm1s_sa t (truncBkNucCfg bk cfg) (le_refl 80))
    (fun cfg ↦ uSlot3EffNorm1s_offCoin6 t (truncBkNucCfg bk cfg) (le_refl 80))
    (fun cfg ↦ s3_hadamard_topBlock_coin6_norm1s t (truncBkNucCfg bk cfg) (le_refl 80))
    (fun cfg ↦ norm_bUnitTwosNorm1sGen_le_one t (truncBkNucCfg bk cfg))
    (fun cfg ↦ bUnitTwosNorm1sGen_permSm t (truncBkNucCfg bk cfg)) (fun cfg spinUp ↦ by
      intro E_vec
      rw [← alphaSlot3_216_eq_wIdealRat3]
      have h506 : (∑ l : Fin 216, |(27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by
        omega⟩ - 1|) ≤ 506 / (2 : ℝ) ^ 37 := by
        rw [← s3Fin27Mul8Equiv.sum_comp, Fintype.sum_prod_type]
        have hinner (q : Fin 27) :
            (∑ m : Fin 8,
              |(27 : ℝ) * s3NucleusProb27 ⟨(s3Fin27Mul8Equiv (q, m)).val / 8, by omega⟩ - 1|) =
              (8 : ℝ) * |(27 : ℝ) * s3NucleusProb27 q - 1| := by
          have hcongr (m : Fin 8) : (⟨(s3Fin27Mul8Equiv (q, m)).val / 8, by omega⟩ : Fin 27) = q :=
            Fin.ext (by
              dsimp [s3Fin27Mul8Equiv]
              have _ := m.isLt
              omega)
          simp [hcongr]
        simp_rw [hinner, ← Finset.mul_sum]
        rw [← s3Fin3CubeEquiv.sum_comp]
        simp_rw [Fintype.sum_prod_type]
        have hterm (t0 t1 t2 : Fin 3) :
            s3NucleusProb27 (s3Fin3CubeEquiv (t0, t1, t2)) = qProb t0 * qProb t1 * qProb t2 := by
          have _ := t0.isLt
          have _ := t1.isLt
          have _ := t2.isLt
          unfold s3NucleusProb27
          refine congrArg₂ (· * ·)
            (congrArg₂ (· * ·) (congrArg qProb (Fin.ext ?_)) (congrArg qProb (Fin.ext ?_)))
            (congrArg qProb (Fin.ext ?_)) <;>
            · dsimp [s3Fin3CubeEquiv]
              omega
        simp_rw [hterm]
        simp only [Fin.sum_univ_three]
        rw [show qProb 0 = (1 - pThird) / 2 from rfl, show qProb 1 = (1 - pThird) / 2 from rfl,
          show qProb 2 = pThird from rfl]
        have hpow37 : (2 : ℝ) ^ 37 = 137438953472 := by norm_num
        have hδ : 0 ≤ pThird - 1 / 3 ∧ pThird - 1 / 3 ≤ (877 / 1000 : ℝ) / (2 : ℝ) ^ 37 := by
          rw [pThird_eq, (by norm_num : (2 : ℝ) ^ 38 = 274877906944), hpow37]
          have hlo := leSqrt2Int_sound (-157007216640000) (-222041735162738) (by decide)
          have hhi := leSqrt2Int_sound 157007216640000 222041735162739 (by decide)
          push_cast at hlo hhi
          exact ⟨by linarith, by linarith⟩
        set δ : ℝ := pThird - 1 / 3 with hδ_def
        change 0 ≤ δ ∧ δ ≤ (877 / 1000 : ℝ) / (2 : ℝ) ^ 37 at hδ
        rw [hpow37] at hδ ⊢
        rcases hδ with ⟨hδ1, hδ2⟩
        have hδ2_nn : 0 ≤ δ ^ 2 := sq_nonneg δ
        have hδ2_le : δ ^ 2 ≤ (1 / 137438953472 : ℝ) ^ 2 := by nlinarith [hδ1, hδ2]
        have hδ3_lo : 0 ≤ δ ^ 3 := pow_nonneg hδ1 3
        have hδ3_hi : δ ^ 3 ≤ (1 / 137438953472 : ℝ) ^ 3 := by
          have _ := mul_nonneg (show 0 ≤ 1 / 137438953472 - δ by linarith [hδ2]) hδ2_nn
          nlinarith [hδ2_le]
        have hp : pThird = 1 / 3 + δ := by linarith
        have ha : (1 - pThird) / 2 = 1 / 3 - δ / 2 := by linarith
        rw [ha, hp]
        have hbound (u v w c p : ℝ) (hlo : -c ≤ p) (hhi : p ≤ c) (heq : (27 : ℝ) * (u * v * w) - 1 =
          p) :
            |(27 : ℝ) * (u * v * w) - 1| ≤ c := heq ▸ abs_le.mpr ⟨hlo, hhi⟩
        have hb0 :=
          hbound (1 / 3 - δ / 2) (1 / 3 - δ / 2) (1 / 3 - δ / 2) ((3947 / 1000 : ℝ) / 137438953472)
          (-(9 / 2 : ℝ) * δ + (27 / 4) * δ ^ 2 - (27 / 8) *
            δ ^ 3) (by linarith) (by linarith) (by ring)
        have hb1a :=
          hbound (1 / 3 - δ / 2) (1 / 3 - δ / 2) (1 / 3 + δ) ((1 / 1000 : ℝ) / 137438953472)
          (-(27 / 4 : ℝ) * δ ^ 2 + (27 / 4) * δ ^ 3) (by linarith) (by linarith) (by ring)
        have hb2a :=
          hbound (1 / 3 - δ / 2) (1 / 3 + δ) (1 / 3 + δ) ((3947 / 1000 : ℝ) / 137438953472)
          ((9 / 2 : ℝ) * δ - (27 / 2) * δ ^ 3) (by linarith) (by linarith) (by ring)
        have hb3 := hbound (1 / 3 + δ) (1 / 3 + δ) (1 / 3 + δ) ((7894 / 1000 : ℝ) / 137438953472)
          ((9 : ℝ) * δ + 27 * δ ^ 2 + 27 * δ ^ 3) (by linarith) (by linarith) (by ring)
        rw [show (1 / 3 - δ / 2) * (1 / 3 + δ) * (1 / 3 - δ / 2) = (1 / 3 - δ / 2) * (1 / 3 - δ /
          2) * (1 / 3 + δ) by ring,
          show (1 / 3 + δ) * (1 / 3 - δ / 2) * (1 / 3 - δ / 2) = (1 / 3 - δ / 2) * (1 / 3 - δ / 2) *
            (1 / 3 + δ) by ring,
          show (1 / 3 + δ) * (1 / 3 - δ / 2) * (1 / 3 + δ) = (1 / 3 - δ / 2) * (1 / 3 + δ) * (1 /
            3 + δ) by ring,
          show (1 / 3 + δ) * (1 / 3 + δ) * (1 / 3 - δ / 2) = (1 / 3 - δ / 2) * (1 / 3 + δ) * (1 /
            3 + δ) by ring]
        linarith
      have hSynth (c0 : SpecsAux.SpecMirror.Configuration) (Δ : Fin 3 → ℤ) :
          ‖s3SynthStructureFactor216 42 c0 Δ - quantizedStructureFactorNearest 42 c0 Δ‖ ≤ 506 /
            (2 : ℝ) ^ 37 := by
        unfold s3SynthStructureFactor216 quantizedStructureFactorNearest
        rw [← Finset.sum_sub_distrib]
        have hsub (l : Fin 216) : (((27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by omega⟩ : ℝ) : ℂ) *
                Complex.exp ((thetaProtonNearest 42 c0 l Δ : ℂ) * Complex.I) -
              Complex.exp ((thetaProtonNearest 42 c0 l Δ : ℂ) * Complex.I) =
            ((((27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by omega⟩ - 1 : ℝ) : ℂ)) *
              Complex.exp ((thetaProtonNearest 42 c0 l Δ : ℂ) * Complex.I) := by
          push_cast
          ring
        simp_rw [hsub]
        refine (norm_sum_le _ _).trans ((Finset.sum_congr rfl fun l _ ↦ ?_).trans_le h506)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
      set c' := truncBkNucCfg bk cfg
      have hbTwos506 : ‖bTwosSlot3_216 (trunc36Cfg c') - bTwosSlot3 (trunc36Cfg c')‖ ≤
          ((506 / 216 : ℝ) / (2 : ℝ) ^ 37) * 20123 := by
        refine (le_of_eq (congrArg Norm.norm ?_)).trans (((norm_s3ProjWeightedOp_le
          (fun Δ ↦ s3SynthStructureFactor216 42 (trunc36Cfg c') Δ -
            quantizedStructureFactorNearest 42 (trunc36Cfg c') Δ)
          (506 / (2 : ℝ) ^ 37) (by positivity) (hSynth (trunc36Cfg c'))).trans_eq (by ring)).trans
          ((mul_le_mul_of_nonneg_left slot3_216_alpha_cheb_step (by positivity)).trans
            (mul_le_mul_of_nonneg_left alphaSlot3_216_pos_and_le_20123.2 (by positivity))))
        classical
        ext x y
        simp only [bTwosSlot3_216, bTwosSlot3, Matrix.sub_apply, Matrix.of_apply]
        split_ifs <;> ring
      have hshift : sixChannelShifted cfg E_vec 3 = projNucOp cfg := by
        change projNucOp cfg - ((0 : ℝ) : ℂ) •
          SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector =
          projNucOp cfg
        rw [Complex.ofReal_zero, zero_smul, sub_zero]
      have hne : (alphaSlot3_216 : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr alphaSlot3_216_pos_and_le_20123.1.ne'
      have hscale : (alphaSlot3_216 : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosNorm1sGen t c' *
        smToTwosSysUnitary.1) =
          smToTwosSysUnitary.1 * bTwosNorm1sGen t c' * smToTwosSysUnitary.1 := by
        unfold bUnitTwosNorm1sGen
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hne, one_smul]
      have hsplit : smToTwosSysUnitary.1 * bTwosNorm1sGen t c' * smToTwosSysUnitary.1 -
        projNucOp cfg =
          smToTwosSysUnitary.1 * (bTwosNorm1sGen t c' - bTwosSlot3_216 (trunc36Cfg c')) *
            smToTwosSysUnitary.1 +
          (smToTwosSysUnitary.1 * bTwosSlot3_216 (trunc36Cfg c') * smToTwosSysUnitary.1 -
            projNucOp cfg) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_cancel]
      rw [hshift, hscale, hsplit, Matrix.mul_add, Matrix.add_mul]
      have hterm1 : ‖fermionicProjector spinUp *
          (smToTwosSysUnitary.1 * (bTwosNorm1sGen t c' - bTwosSlot3_216 (trunc36Cfg c')) *
            smToTwosSysUnitary.1) *
          fermionicProjector spinUp‖ ≤ (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) *
            ((n1sOctSum128CertVal t : ℝ) / 4096) := by
        rw [← n1s_real_sum_eq_certVal_tier6 t ht]
        exact (norm_fermionicProjector_sandwich_le spinUp _).1.trans ((norm_unitary_conj_le
          smToTwosSysUnitary _).trans
            (norm_bTwosNorm1sGen_sub_bTwosSlot3_216_trunc36Cfg_le_of_kernelDiff t c'
              (eNuNorm1s t) (eNuNorm1s_nonneg t) (eNuNorm1s_bound t)))
      have hgrid_eq : ∀ x y, IsGridState x → IsGridState y →
          (smToTwosSysUnitary.1 * bTwosSlot3_216 (trunc36Cfg c') * smToTwosSysUnitary.1 -
            projNucOp cfg) x y =
            ((smToTwosSysUnitary.1 * (bTwosSlot3_216 (trunc36Cfg c') - bTwosSlot3 (trunc36Cfg c')) *
              smToTwosSysUnitary.1) +
              (modWrapProjNucOp cfg 38 36 bk (2 / 42) 1 - projNucOp cfg)) x y := fun x y hx hy ↦ by
        rw [Matrix.sub_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.sub_apply,
          smToTwosSysUnitary_conj_bTwosSlot3_on_grid (trunc36Cfg c') hx hy,
          congrFun (congrFun (modWrapProjNucOp_trunc36Cfg_truncBkNucCfg bk hbk.2 cfg) x) y]
        ring
      have hterm2 : ‖fermionicProjector spinUp *
          (smToTwosSysUnitary.1 * bTwosSlot3_216 (trunc36Cfg c') * smToTwosSysUnitary.1 -
            projNucOp cfg) *
          fermionicProjector spinUp‖ ≤ ((506 / 216 : ℝ) / (2 : ℝ) ^ 37) * 20123 +
            ((216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ)) * (2050880366 /
              1048576) +
              (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (219901 / 32) +
              (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
                (714141984672 / 4194304)) := by
        rw [fermionicProjector_sandwich_congr_on_grid spinUp _ _ hgrid_eq, Matrix.mul_add,
          Matrix.add_mul]
        exact (norm_add_le _ _).trans (add_le_add ((norm_fermionicProjector_sandwich_le spinUp
          _).1.trans
            ((norm_unitary_conj_le smToTwosSysUnitary _).trans hbTwos506))
          ((norm_fermionicProjector_sandwich_le spinUp _).1.trans
            (slot3_norm_modWrapProjNucOp_bk_sub_le_octant bk cfg)))
      refine (norm_add_le _ _).trans ((add_le_add hterm1 hterm2).trans ?_)
      have hbase : (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * ((n1sOctSum128CertVal t : ℝ) / 4096) +
          ((506 / 216 : ℝ) / (2 : ℝ) ^ 37) * 20123 +
          (216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ)) * (2050880366 / 1048576) +
          (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (219901 / 32) = (s3BaseNum t : ℝ) /
            56093289107182948712448 := by
        rcases ht with (rfl | rfl | rfl | rfl | rfl) | rfl <;>
          norm_num [n1sOctSum128CertVal, s3BaseNum]
      have hnuc : (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 *
        (2 : ℝ) ^ bk)) *
          (714141984672 / 4194304) = (18929896136514003609 : ℝ) / ((3455089049600 *
            2 ^ bk : ℕ) : ℝ) := by
        rw [show (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
            (714141984672 / 4194304) = ((432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) /
              42) *
            (714141984672 / 4194304)) / (2 : ℝ) ^ bk by ring,
          (by norm_num : (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / 42) *
            (714141984672 / 4194304) = (18929896136514003609 : ℝ) / 3455089049600), div_div]
        push_cast
        rfl
      have hNatCert : ([Norm1sTier.t26_18, .t26_17, .t27_17, .t29_18, .t29_17, .t30_18].all fun t0 ↦
          (List.range 17).all fun idx ↦
            let bk0 := 36 - idx
            let nd := 3455089049600 * 2 ^ bk0
            let bd := 56093289107182948712448
            decide ((s3BaseNum t0 * nd + 18929896136514003609 * bd) * 1000000000 ≤
              s3EpsUltraBkNano t0 bk0 * (bd * nd))) = true := by decide
      have hmem_t : t ∈ [Norm1sTier.t26_18, .t26_17, .t27_17, .t29_18, .t29_17, .t30_18] := by
        rcases ht with (rfl | rfl | rfl | rfl | rfl) | rfl <;> simp
      have hcell :=
        of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp hNatCert) t hmem_t))
        (36 - bk) (List.mem_range.mpr (by omega)))
      rw [show 36 - (36 - bk) = bk by omega] at hcell
      have hnd_pos : (0 : ℝ) < ((3455089049600 * 2 ^ bk : ℕ) : ℝ) := by positivity
      have hreal : ((s3BaseNum t : ℝ) * ((3455089049600 * 2 ^ bk : ℕ) : ℝ) +
          18929896136514003609 * 56093289107182948712448) * 1000000000 ≤
          (s3EpsUltraBkNano t bk : ℝ) * (56093289107182948712448 * ((3455089049600 *
            2 ^ bk : ℕ) : ℝ)) := by
        exact_mod_cast hcell
      set ndR : ℝ := ((3455089049600 * 2 ^ bk : ℕ) : ℝ)
      have hsum_eq : (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * ((n1sOctSum128CertVal t : ℝ) / 4096) +
          (((506 / 216 : ℝ) / (2 : ℝ) ^ 37) * 20123 +
            ((216 * ((2 / 42 : ℝ) / (2 : ℝ) ^ 36) * (4200000 / 4217638 : ℝ)) * (2050880366 /
              1048576) +
              (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (219901 / 32) +
              (432 * (31415927 / 10000000 : ℝ) * (4200000 / 4217638 : ℝ) / (42 * (2 : ℝ) ^ bk)) *
                (714141984672 / 4194304))) =
          (s3BaseNum t : ℝ) / 56093289107182948712448 + 18929896136514003609 / ndR := by
            linarith [hbase, hnuc]
      rw [hsum_eq]
      refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 56093289107182948712448 * ndR)
      rw [show ((s3BaseNum t : ℝ) / 56093289107182948712448 + 18929896136514003609 / ndR) *
        (56093289107182948712448 * ndR) =
          (s3BaseNum t : ℝ) * ndR + 18929896136514003609 * 56093289107182948712448 by
            field_simp [hnd_pos.ne']]
      linarith)
/-- Drop-in 6-tier `21 ≤ bk ∧ bk ≤ 36` `MomSingleSlotOracle 80 48 3` matching
  `s3Swap3OracleNorm1sBk`'s
domain while unlocking `.t30_18` and `s3EpsUltraBkNano t bk / 10^9`. -/
noncomputable def s3Swap3OracleNorm1sUltraBk (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36) : MomSingleSlotOracle 80 48 3 :=
  s3Swap3OracleNorm1sUltraBk_20 t ht bk ⟨by omega, hbk.2⟩
theorem s3Swap3OracleNorm1sUltraBk_wSlot (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36) (cfg : SpecsAux.SpecMirror.Configuration) :
    (s3Swap3OracleNorm1sUltraBk t ht bk hbk).wSlot cfg = wIdealRat 3 :=
  rfl
theorem s3Swap3OracleNorm1sUltraBk_epsIntr_le (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36) : (s3Swap3OracleNorm1sUltraBk t ht bk hbk).epsIntr ≤
      (s3EpsUltraBkNano t bk : ℝ) / 1000000000 := le_rfl
theorem s3Swap3OracleNorm1sUltraBk_fixesLowEff (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36) (cfg : SpecsAux.SpecMirror.Configuration) :
    FixesLow3924 h3924_momCore ((s3Swap3OracleNorm1sUltraBk t ht bk hbk).uSlotEff cfg).1 :=
  Slot3PrepWideAndSwap3.fixesLow3924_swap3PiOracle80_eff _
    cfg (fixesLow3924_uSlot3EffNorm1s t (truncBkNucCfg bk cfg))
theorem s3Swap3OracleNorm1sUltraBk_20_commEC (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 20 ≤ bk ∧ bk ≤ 36) (cfg : SpecsAux.SpecMirror.Configuration) :
    Slot3StreamUncK35Shift3.CommutesWithReg rEC80 ((s3Swap3OracleNorm1sUltraBk_20 t ht bk
      hbk).uSlotEff cfg).1 :=
  commutesWithReg_rEC80_of_eq_uPiSwap3Core_norm1s t uPiSwap3Core_prep273_eq_streamUnc (truncBkNucCfg
    bk cfg)
set_option exponentiation.threshold 8192 in
theorem s3Swap3OracleNorm1sUltraBk_commEC (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36) (cfg : SpecsAux.SpecMirror.Configuration) :
    Slot3StreamUncK35Shift3.CommutesWithReg rEC80
      ((s3Swap3OracleNorm1sUltraBk t ht bk hbk).uSlotEff cfg).1 :=
  s3Swap3OracleNorm1sUltraBk_20_commEC t ht bk ⟨by omega, hbk.2⟩ cfg
set_option exponentiation.threshold 8192 in
theorem embed_uSlot3HadCutCat36FullSys_ultraBk_20_top
    (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t) (bk : ℕ) (hbk : 20 ≤ bk ∧ bk ≤
      36) (cfg : SpecsAux.SpecMirror.Configuration) :
    (rCoreTopCatInCT 36 (by decide)).embedUnitary (uSlot3HadCutCat36FullSys t (truncBkNucCfg bk
      cfg)) =
      unitaryConj (rCoreInCT80.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
        (catUnitaryToFullSys ((s3Swap3OracleNorm1sUltraBk_20 t ht bk hbk).uSlotCat cfg)) := by
  set c' := truncBkNucCfg bk cfg
  let rSub36 :=
    rCore0_80.concat (rCat0_80.compose (rTopCatSlice 36 48 (by decide)))
    (hCoreCatDisj80.compose_right _)
  let rFull48 := rCore0_80.concat rCat0_80 hCoreCatDisj80
  have hSubEq : rSub36.embedUnitary (uSlot3Swap3Cat36Norm1s t c') =
      (s3Swap3OracleNorm1sUltraBk_20 t ht bk hbk).uSlotCat cfg := by
    have hCoreComp0 : rSub36.compose rCore0_36 = rFull48.compose rCore0_80 :=
      qreg_ext fun i ↦ by
        change rSub36 (rCore0_36 i) = rFull48 (rCore0_80 i)
        rw [show rCore0_36 i = Fin.castAdd 36 i from Fin.ext (Nat.zero_add i.val),
          show rCore0_80 i = Fin.castAdd 48 i from Fin.ext (Nat.zero_add i.val),
          QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hSelComp : rSub36.compose sel143_80_36 =
        (rFull48.compose (StepBBlock0.sel149 (le_refl 80))).compose r143In149 := by
      have hSel149Val (u : Fin 149) : (StepBBlock0.sel149 (le_refl 80) u).val =
          if u.val < 24 then 3924 + u.val
          else if u.val < 27 then 3948 + (u.val - 24)
          else if u.val < 107 then 3954 + (u.val - 27)
          else momCoreWires 80 + 6 + (u.val - 107) := rfl
      refine qreg_ext fun (idx : Fin (107 + 36)) ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · have hi := i.isLt
        change rSub36 (sel143_80_36 (Fin.castAdd 36 i)) =
          rFull48 (StepBBlock0.sel149 (le_refl 80) (r143In149 (Fin.castAdd 36 i)))
        unfold sel143_80_36
        rw [QRegister.concat_apply_left]
        have hL : rSub36 (rCore0_36.compose sel107_80 i) = rCore0_80 (sel107_80 i) := by
          change rSub36 (rCore0_36 (sel107_80 i)) = rCore0_80 (sel107_80 i)
          rw [show rCore0_36 (sel107_80 i) =
            Fin.castAdd 36 (sel107_80 i) from Fin.ext (Nat.zero_add _),
            QRegister.concat_apply_left]
        have hR : StepBBlock0.sel149 (le_refl 80) (r143In149 (Fin.castAdd 36 i)) =
          Fin.castAdd 48 (sel107_80 i) := by
          apply Fin.ext
          rw [hSel149Val,
            show (r143In149 (Fin.castAdd 36 i)).val = i.val from StepBBlock0.s3ItePos hi,
            Fin.val_castAdd, sel107_80_val i]
          split_ifs <;> omega
        rw [hL, hR, QRegister.concat_apply_left]
      · have hj := j.isLt
        change rSub36 (sel143_80_36 (Fin.natAdd 107 j)) =
          rFull48 (StepBBlock0.sel149 (le_refl 80) (r143In149 (Fin.natAdd 107 j)))
        unfold sel143_80_36
        rw [QRegister.concat_apply_right]
        have hL : rSub36 (rCat0_36 j) = rCat0_80 (rTopCatSlice 36 48 (by decide) j) := by
          rw [show rCat0_36 j = Fin.natAdd coreWires80 j from rfl, QRegister.concat_apply_right]
          rfl
        have hR : StepBBlock0.sel149 (le_refl 80) (r143In149 (Fin.natAdd 107 j)) =
            Fin.natAdd coreWires80 (rTopCatSlice 36 48 (by decide) j) := by
          apply Fin.ext
          have hr : (r143In149 (Fin.natAdd 107 j)).val = 113 + j.val := by
            change (if 107 + j.val < 107 then 107 + j.val else (107 + j.val) + 6) = 113 + j.val
            rw [StepBBlock0.s3IteNeg (by omega)]
            omega
          rw [hSel149Val, hr]
          dsimp [coreWires80, momCoreWires, rTopCatSlice]
          split_ifs <;> omega
        rw [hL, hR, QRegister.concat_apply_right]
    have hWhole : rFull48 = QRegister.whole (momCoreWires 80 + 48) :=
      qreg_ext fun idx ↦ Fin.addCases
        (fun i ↦
          Fin.ext ((congrArg Fin.val (QRegister.concat_apply_left _ _ _ i)).trans (Nat.zero_add
          i.val)))
        (fun j ↦ Fin.ext (congrArg Fin.val (QRegister.concat_apply_right _ _ _ j))) idx
    have hMain : rSub36.embedUnitary (uSlot3Swap3Cat36Norm1s t c') = rFull48.embedUnitary
          (PosMomSelectDynamic.unitaryConj (rCore0_80.embedUnitary uPiSwap3Core)
            (PosMomSelectDynamic.unitaryConj (rCore0_80.embedUnitary (uPrep3_216 (le_refl 80)))
              ((StepBBlock0.sel149 (le_refl 80)).embedUnitary (uCore149Norm1s t c')))) := by
      unfold uSlot3Swap3Cat36Norm1s uSlot3Cat36Norm1s
      rw [Leaf3Slot3Norm1sWidth204.Internal.embedUnitary_unitaryConj,
        Leaf3Slot3Norm1sWidth204.Internal.embedUnitary_unitaryConj,
        Leaf3Slot3Norm1sWidth204.Internal.embedUnitary_unitaryConj,
        Leaf3Slot3Norm1sWidth204.Internal.embedUnitary_unitaryConj,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, hCoreComp0, hSelComp,
        QRegister.embedUnitary_compose (rFull48.compose (StepBBlock0.sel149 (le_refl 80)))
          r143In149,
        r143In149_embed_uCore143Norm1s]
    rwa [hWhole, QRegister.whole_embedUnitary] at hMain
  have hCoreComp : (rCoreTopCatInCT 36 (by decide)).compose rCoreInCoreCat36 = rCoreInCT80 :=
    qreg_ext fun i ↦ by
      change (rCoreTopCatInCT 36 (by decide)) (rCoreInCoreCat36 i) = rCoreInCT80 i
      rw [show rCoreInCoreCat36 i = Fin.castAdd 36 i from Fin.ext (Nat.zero_add i.val),
        rCoreTopCatInCT, QRegister.concat_apply_left]
  have hCatCast :
      catUnitaryToFullSys ((s3Swap3OracleNorm1sUltraBk_20 t ht bk hbk).uSlotCat cfg) =
        (rCoreTopCatInCT 36 (by decide)).embedUnitary
          (castNatUnitary hCoreCat36_eq (uSlot3Swap3Cat36Norm1s t c')) := by
    rw [catUnitaryToFullSys, ← hSubEq]
    refine castNatUnitary_embedUnitary hCoreCat36_eq (momCatWires_eq_fullSysCatWires 80 48)
      _ (rCoreTopCatInCT 36 (by decide)) (fun idx ↦ ?_) (uSlot3Swap3Cat36Norm1s t c')
    rw [Subsingleton.elim hCoreCat36_eq rfl]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · change (rSub36 (Fin.castAdd 36 i)).val =
        ((rCoreTopCatInCT 36 (by decide)) (Fin.castAdd 36 i)).val
      unfold rCoreTopCatInCT
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      rfl
    · change (rSub36 (Fin.natAdd coreWires80 j)).val =
        ((rCoreTopCatInCT 36 (by decide)) (Fin.natAdd (fullSysCoreWires 80) j)).val
      unfold rCoreTopCatInCT
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
      rfl
  unfold uSlot3HadCutCat36FullSys
  simp only [unitaryConj, QRegister.embedUnitary_mul, QRegister.embedUnitary_inv,
    ← QRegister.embedUnitary_compose, hCoreComp, hCatCast]
section HpowUltraBkTop
attribute [local irreducible] HPow.hPow
theorem embed_uSlot3HadCutCat36FullSys_ultraBk_top (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36) (cfg : SpecsAux.SpecMirror.Configuration) :
    (rCoreTopCatInCT 36 (by decide)).embedUnitary (uSlot3HadCutCat36FullSys t (truncBkNucCfg bk
      cfg)) = unitaryConj
        (rCoreInCT80.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
        (catUnitaryToFullSys ((s3Swap3OracleNorm1sUltraBk t ht bk hbk).uSlotCat cfg)) :=
  embed_uSlot3HadCutCat36FullSys_ultraBk_20_top t ht bk ⟨by omega, hbk.2⟩ cfg
end HpowUltraBkTop
theorem commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut_ultra
    (t : Norm1sTier) (bk : ℕ) (cfg : SpecsAux.SpecMirror.Configuration) : CommutesWithReg
      (rCtrl3InCoreCat 36)
      (uSlot3HadCutCat36FullSys t (truncBkNucCfg bk cfg)).1 :=
  commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut t (truncBkNucCfg bk cfg)
end Section3UltraBk
end GqspSlot3UltraBkAnd8TierCert
end
end GqspSlot3UltraBkAnd8TierCert

end QuantumComputation.Specs.StoppingPowerSolution
end
