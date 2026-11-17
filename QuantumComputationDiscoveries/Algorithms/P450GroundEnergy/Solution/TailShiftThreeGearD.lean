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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE46687
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearA
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearB
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearC

@[expose] public section

/-!
# Tail-Shifted Three-Gear Dihedral QPE End-to-End Closure (`TailShiftThreeGear`)

Completes the polymorphic Tail-Shifted Three-Gear Bond-Deferred QPE engine (`StageC + StageM +
StageF`), re-exporting `TailShiftThreeGearA`, `TailShiftThreeGearB`, and
`TailShiftThreeGearC`, and providing:
1. `K`-step super-reflection invariant-subspace contract `WalkKStepRefl2InvErrLe` and single-step
   bridge `walkKStepRefl2InvErrLe_of_walkRefl2InvErrLe` + `tailShiftSuperRefl2Dyn`.
2. Exact `16`-bit dihedral schedule identity `tailShiftThreeGear_ideal_fiber_mul_eq` on `0 .. M`
   and `L²` perturbation certificate `tailShiftThreeGear_implQPEPertHyp`.
3. Turnkey `Ray1036 + Hi14247` and `Ray1036 + Fast12603` programs, `Q × T` cost lemmas, and
   `RealizesP450GroundQPE` theorems consuming `TailShiftRayQuantSuperBox`.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open BlockEncodingCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open TopIntegrationBridge Cat11CompactPhase2Bridge
open DihedralWalkQPE BlockEncodingCircuit
open DihedralWalkQPE.BlockReflection
open DihedralWalkQPE.SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outZeroPrefixReg combARem CleanWalkRefl2)
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox hiding
  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open TailShiftBox TwoGearQPEPhase5
open TwoGearBondDefer
open TailShiftWindow46847
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators hiding CleanRealizes
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 3A: `K`-Step Super-Reflection Contract & Single-Step Builder -/

theorem invCatRel_reflInUnitary (mOut mMid : ℕ)
    {P_inv : (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop} {cat : Fin (2 ^ 11) → ℂ}
    (hR1 : ∀ x, P_inv x → P_inv ((QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)).1 *ᵥ x)) :
    InvCatRel P_inv cat (QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid))
      (QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)) 0 := by
  refine ⟨hR1, fun x _ ↦ ?_⟩
  rw [zero_mul]
  have heq : (QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)).1 *ᵥ tensorWalkCat x cat =
      tensorWalkCat ((QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)).1 *ᵥ x) cat := by
    rw [tgEmbedUnitary_rWalkInWalkCat_reflIn, QRegister.embedUnitary_val]
    exact embedMatrix_rWalkInWalkCat_mulVec _ x cat
  rw [heq, sub_self, WithLp.toLp_zero, norm_zero]

/-- Invariant-subspace `L²` relative error contract for a `K`-step dihedral super-reflection
approximating `R₁ * (R₁ * R₂) ^ K` on `P_inv ⊗ |phaseGradientLowFactor 11 3⟩`. -/
noncomputable def WalkKStepRefl2InvErrLe (wOuter wInner2 K : ℕ) (uB : Unitary (2 ^ nUB wOuter
    wInner2))
    (uSuper : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))) (δSuper : ℝ) : Prop :=
  ∃ P_inv : (Fin (2 ^ nUB wOuter wInner2) → ℂ) → Prop,
    (∀ ψ : Fin (2 ^ (2 * 58)) → ℂ,
      P_inv ((rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1))) ∧
    (∀ x, P_inv x →
      P_inv ((QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))).1 *ᵥ x)) ∧
    (∀ x, P_inv x →
      P_inv ((QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB).1 *ᵥ
        x)) ∧
    (∀ x, P_inv x →
      let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))
      let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB
      let R_K := R₁ * (R₁ * R₂) ^ K
      ‖WithLp.toLp 2 (uSuper.1 *ᵥ tensorWalkCat x (CircuitModular.phaseGradientLowFactor 11 3) -
          tensorWalkCat (R_K.1 *ᵥ x) (CircuitModular.phaseGradientLowFactor 11 3))‖ ≤
        δSuper * ‖WithLp.toLp 2 (tensorWalkCat x (CircuitModular.phaseGradientLowFactor 11 3))‖)

/-! ## Section 3B: Dihedral Schedule Identity & `L²` Perturbation Closure -/

theorem refl_conj_walk_pow_eq_zpow_neg {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (k : ℕ) :
    (R₁ * (R₁ * R₂) ^ k) * R₁ = (R₁ * R₂) ^ (-(k : ℤ)) := by
  let W := R₁ * R₂
  have h1 : R₁ * W * R₁ = W⁻¹ := by
    have hmul : W * (R₁ * W * R₁) = 1 := by
      calc R₁ * R₂ * (R₁ * (R₁ * R₂) * R₁)
          = R₁ * R₂ * ((R₁ * R₁) * R₂ * R₁) := by simp only [mul_assoc]
        _ = R₁ * (R₂ * R₂) * R₁ := by
            rw [hR₁, one_mul]
            simp only [mul_assoc]
        _ = 1 := by rw [hR₂, mul_one, hR₁]
    calc R₁ * W * R₁ = W⁻¹ * (W * (R₁ * W * R₁)) := (inv_mul_cancel_left W _).symm
      _ = W⁻¹ * 1 := by rw [hmul]
      _ = W⁻¹ := mul_one _
  have hpow : ∀ n : ℕ, R₁ * W ^ n * R₁ = (W⁻¹) ^ n := by
    intro n
    induction n with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, mul_one, hR₁]
    | succ m ih =>
      calc R₁ * W ^ (m + 1) * R₁
          = R₁ * (W ^ m * W) * R₁ := by rw [pow_succ]
        _ = (R₁ * W ^ m * R₁) * (R₁ * W * R₁) := by
            calc R₁ * (W ^ m * W) * R₁
                = R₁ * W ^ m * 1 * W * R₁ := by simp only [mul_one, mul_assoc]
              _ = R₁ * W ^ m * (R₁ * R₁) * W * R₁ := by rw [hR₁]
              _ = (R₁ * W ^ m * R₁) * (R₁ * W * R₁) := by simp only [mul_assoc]
        _ = (W⁻¹) ^ m * W⁻¹ := by rw [ih, h1]
        _ = (W⁻¹) ^ (m + 1) := (pow_succ W⁻¹ m).symm
  change R₁ * W ^ k * R₁ = W ^ (-(k : ℤ))
  rw [hpow k, inv_pow, ← _root_.zpow_natCast W k, _root_.zpow_neg]

theorem TailShiftParams.hM_lo {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : 2 ^ 15 ≤ M := by
  have hp : 2 ^ (16 - m2 - 1) * 2 ^ m2 = 2 ^ 15 := by
    rw [← pow_add]
    have := ts.hm2_le14
    congr 1
    omega
  have hle : 2 ^ 15 + 2 ^ m2 ≤ (nStd + 1) * 2 ^ m2 := by
    calc 2 ^ 15 + 2 ^ m2 = (2 ^ (16 - m2 - 1) + 1) * 2 ^ m2 := by
          rw [← hp]
          ring
      _ ≤ (nStd + 1) * 2 ^ m2 := Nat.mul_le_mul_right _ (Nat.add_le_add_right ts.hnStd_lo 1)
  have hp2 : 0 < 2 ^ m2 := Nat.two_pow_pos m2
  have hpos := ts.hkTail_pos
  have hMeq := ts.hM_eq
  omega

/-- Exact `16`-bit dihedral schedule identity on `0 .. M`: multiplying fine `StageF`, shifted
middle `StageM`, and tail-fused coarse `StageC` recovers `affineScheduleFiber 16 M (R₁ * R₂) R₁ m`
for every `m.val ≤ M`. -/
theorem tailShiftThreeGear_ideal_fiber_mul_eq {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) {M m2 m1 nStd kTail tShift : ℕ} (hm1_1 : 1 ≤ m1)
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (m : Fin (2 ^ 16)) (hm : m.val ≤ M) :
    let bM := m2 - m1
    let bC := 16 - m2
    let W := R₁ * R₂
    let R₂_std := R₁ * W ^ (2 ^ m2)
    let R₂_tail := R₁ * W ^ kTail
    let R₂_mid := R₁ * W ^ (2 ^ m1)
    let xh : Fin (2 ^ (16 - m1)) := (rHiInQPE16 m1 ts.hm1_le16).extractIndex m
    let xl : Fin (2 ^ m1) := ⟨m.val % 2 ^ m1, Nat.mod_lt _ (Nat.two_pow_pos m1)⟩
    let rSliceC : QRegister bC (16 - m1) := QRegister.block bM bC ts.hSubM_le
    let rSliceM : QRegister bM (16 - m1) := QRegister.block 0 bM ts.hBlock0SubM_le
    affineScheduleFiber (bQPE := m1) m1 (2 ^ m1 - 1) W R₁ xl *
      (affineScheduleFiber (bQPE := bM) bM (2 ^ bM - 1) (R₁ * R₂_mid) R₁
          (rSliceM.extractIndex (tailShiftClockPerm ts xh)) *
        tailFusedScheduleFiber nStd R₂_std R₂_tail R₁ (rSliceC.extractIndex xh)) =
      affineScheduleFiber (bQPE := 16) 16 M W R₁ m := by
  intro bM bC W R₂_std R₂_tail R₂_mid xh xl rSliceC rSliceM
  have hm12 := ts.hm1_lt_m2
  have hm2_14 := ts.hm2_le14
  have hMlo := ts.hM_lo
  have hMlt := ts.hM_lt
  have hxh_val : xh.val = m.val / 2 ^ m1 := by
    dsimp only [xh, rHiInQPE16]
    rw [block_extractIndex_val_tg]
    refine Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul ?_)
    rw [← pow_add, Nat.add_sub_of_le ts.hm1_le16]
    exact m.isLt
  let x_c := rSliceC.extractIndex xh
  let xc := x_c.val
  have hxc_eq_div : xc = xh.val / 2 ^ bM := by
    dsimp only [xc, x_c, rSliceC]
    rw [block_extractIndex_val_tg]
    refine Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul ?_)
    rw [← pow_add, ts.hSubM_eq]
    exact xh.isLt
  have hxc_m : xc = m.val / 2 ^ m2 := by
    rw [hxc_eq_div, hxh_val, Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le hm12.le]
  let xm := xh.val % 2 ^ bM
  have hxh_decomp : xh.val = xm + xc * 2 ^ bM := by
    dsimp only [xm]
    rw [hxc_eq_div, mul_comm _ (2 ^ bM), Nat.mod_add_div]
  have hp : 2 ^ bM * 2 ^ m1 = 2 ^ m2 := by
    rw [← pow_add]
    exact congrArg (2 ^ ·) (Nat.sub_add_cancel hm12.le)
  have hm_decomp : m.val = xc * 2 ^ m2 + xm * 2 ^ m1 + xl.val := by
    have h1 : m.val = xh.val * 2 ^ m1 + xl.val := by
      dsimp only [xl]
      rw [hxh_val, mul_comm _ (2 ^ m1)]
      exact (Nat.div_add_mod _ _).symm
    calc m.val = (xm + xc * 2 ^ bM) * 2 ^ m1 + xl.val := by rw [← hxh_decomp, h1]
      _ = xc * (2 ^ bM * 2 ^ m1) + xm * 2 ^ m1 + xl.val := by ring
      _ = xc * 2 ^ m2 + xm * 2 ^ m1 + xl.val := by rw [hp]
  have hxc_le_top : xc ≤ nStd + 1 := by
    rw [hxc_m]
    have h1 := ts.hM_eq
    have h2 := ts.hkTail_lt
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by nlinarith))
  let qShift := ts.mode.cFwd * 2 ^ (ts.mShift - m1)
  let xm2 := rSliceM.extractIndex (tailShiftClockPerm ts xh)
  have hxm_val : xm2.val = if xc = nStd + 1 then (xm + qShift) % 2 ^ bM else xm := by
    dsimp only [xm2, rSliceM]
    rw [block_extractIndex_val_tg, _root_.pow_zero, Nat.div_one]
    dsimp only [tailShiftClockPerm]
    change tailShiftClockMapVal bM bC nStd qShift xh.val % 2 ^ bM = _
    dsimp only [tailShiftClockMapVal]
    rw [← hxc_eq_div, Nat.add_mul_mod_self_right]
    refine Nat.mod_eq_of_lt ?_
    split_ifs <;> exact Nat.mod_lt _ (Nat.two_pow_pos bM)
  have hFlo : 2 ^ (m1 - 1) ≤ 2 ^ m1 - 1 := two_pow_pred_le_two_pow_sub_one hm1_1
  have hMlo_bM : 2 ^ (bM - 1) ≤ 2 ^ bM - 1 := two_pow_pred_le_two_pow_sub_one (by omega)
  have hR₂_mid : R₂_mid * R₂_mid = 1 := superRefl_involutive hR₁ hR₂ (2 ^ m1)
  have hW_mid : R₁ * R₂_mid = W ^ (2 ^ m1) := by
    dsimp only [R₂_mid]
    rw [← mul_assoc, hR₁, one_mul]
  have hR₂_std : R₂_std * R₂_std = 1 := superRefl_involutive hR₁ hR₂ (2 ^ m2)
  have hW_std : R₁ * R₂_std = W ^ (2 ^ m2) := by
    dsimp only [R₂_std]
    rw [← mul_assoc, hR₁, one_mul]
  have hp_m1 := Nat.two_pow_pos m1
  have hp_bM := Nat.two_pow_pos bM
  have hxl_lt := xl.isLt
  have hxms_lt := xm2.isLt
  have hzF := affineScheduleFiber_ideal_eq_zpow (m := xl) hR₁ hR₂ hm1_1 le_rfl hFlo
    (by omega) (by omega)
  have hzM := affineScheduleFiber_ideal_eq_zpow (m := xm2) hR₁ hR₂_mid (by omega) le_rfl
    hMlo_bM (by omega) (by omega)
  have hz16 := affineScheduleFiber_ideal_eq_zpow (m := m) hR₁ hR₂ (by decide) le_rfl hMlo hMlt hm
  rw [hzF, hzM, hz16, hW_mid, ← _root_.zpow_natCast W (2 ^ m1), ← _root_.zpow_mul]
  have hperm_val : (qpeAffinePerm bC bC nStd x_c).val =
      affineFoldVal (bC - 1) (nStd + 1 - 2 ^ (bC - 1)) xc := by
    dsimp only [xc, qpeAffinePerm]
    rw [dite_eq_left ⟨by omega, le_rfl⟩]
    rfl
  have hc1 : ((2 ^ m1 - 1 : ℕ) : ℤ) = ((2 ^ m1 : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]
  have hcM : ((2 ^ bM - 1 : ℕ) : ℤ) = ((2 ^ bM : ℕ) : ℤ) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]
  have hpow_m2 : ((2 ^ m1 : ℕ) : ℤ) * ((2 ^ bM : ℕ) : ℤ) = ((2 ^ m2 : ℕ) : ℤ) := by
    exact_mod_cast (pow_add 2 m1 bM).symm.trans (congrArg (2 ^ ·) (by omega))
  have hM_z : (M : ℤ) + 1 = ((nStd : ℤ) + 1) * ((2 ^ m2 : ℕ) : ℤ) + (kTail : ℤ) := by
    exact_mod_cast ts.hM_eq
  have hm_z : (m.val : ℤ) =
      (xc : ℤ) * ((2 ^ m2 : ℕ) : ℤ) + (xm : ℤ) * ((2 ^ m1 : ℕ) : ℤ) + (xl.val : ℤ) := by
    conv_lhs => rw [hm_decomp]
    push_cast
    ring
  have hnStd_hi := ts.hnStd_hi
  by_cases hxc_le : xc ≤ nStd
  · have hy_lt : (qpeAffinePerm bC bC nStd x_c).val < 2 ^ bC - 1 := by
      rw [hperm_val]
      exact ts.hFoldStd x_c hxc_le
    have hC : tailFusedScheduleFiber nStd R₂_std R₂_tail R₁ x_c =
        W ^ (-(kTail : ℤ) + ((2 ^ m2 : ℕ) : ℤ) * (2 * (xc : ℤ) - (nStd : ℤ))) := by
      unfold tailFusedScheduleFiber tailFusedBodyFiber
      rw [ite_eq_right (ne_of_lt hy_lt)]
      change (R₂_tail * R₁) * affineScheduleFiber bC nStd (R₁ * R₂_std) R₁ x_c = _
      have hzC := affineScheduleFiber_ideal_eq_zpow (m := x_c) hR₁ hR₂_std (by omega) le_rfl
        ts.hnStd_lo (by omega) hxc_le
      rw [hzC, hW_std, refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kTail,
        ← _root_.zpow_natCast W (2 ^ m2), ← _root_.zpow_mul, ← _root_.zpow_add]
    have hxm_eq : xm2.val = xm := by rw [hxm_val, ite_eq_right (by omega)]
    rw [hC, hxm_eq, ← _root_.zpow_add, ← _root_.zpow_add]
    congr 1
    rw [hc1, hcM, hm_z]
    linear_combination -hpow_m2 + hM_z
  · have hxc_top : xc = nStd + 1 := by omega
    have hy_eq : (qpeAffinePerm bC bC nStd x_c).val = 2 ^ bC - 1 := by
      rw [hperm_val, hxc_top]
      exact ts.hFoldTop
    have hC : tailFusedScheduleFiber nStd R₂_std R₂_tail R₁ x_c =
        W ^ ((kTail : ℤ) + ((2 ^ m2 : ℕ) : ℤ) * (nStd : ℤ)) := by
      unfold tailFusedScheduleFiber
      rw [tailFusedBodyFiber_allOnes_eq (by omega) ts.hnStd_lo R₂_std R₂_tail R₁ hR₁ _ hy_eq,
        hW_std]
      have hrt : R₁ * R₂_tail = W ^ kTail := by
        dsimp only [R₂_tail]
        rw [← mul_assoc, hR₁, one_mul]
      rw [hrt, ← pow_mul, ← pow_add, ← _root_.zpow_natCast]
      congr 1
    have hxm_lt : xm + qShift < 2 ^ bM := by
      have hk_rem : xm * 2 ^ m1 < kTail := by
        have hMeq := ts.hM_eq
        rw [hxc_top] at hm_decomp
        omega
      have hmul_lt : (xm + qShift) * 2 ^ m1 < 2 ^ bM * 2 ^ m1 := by
        calc (xm + qShift) * 2 ^ m1
            = xm * 2 ^ m1 + qShift * 2 ^ m1 := by ring
          _ < kTail + (2 ^ m2 - kTail) := Nat.add_lt_add_of_lt_of_le hk_rem ts.hqShift_eq.le
          _ = 2 ^ m2 := Nat.add_sub_of_le ts.hkTail_lt.le
          _ = 2 ^ bM * 2 ^ m1 := hp.symm
      exact Nat.lt_of_mul_lt_mul_right hmul_lt
    have hxm_eq : xm2.val = xm + qShift := by
      rw [hxm_val, ite_eq_left hxc_top, Nat.mod_eq_of_lt hxm_lt]
    have hq_z : (qShift : ℤ) * ((2 ^ m1 : ℕ) : ℤ) = ((2 ^ m2 : ℕ) : ℤ) - (kTail : ℤ) := by
      have h1 : ((qShift * 2 ^ m1 : ℕ) : ℤ) = ((2 ^ m2 - kTail : ℕ) : ℤ) :=
        congrArg Nat.cast ts.hqShift_eq
      rw [Nat.cast_mul, Nat.cast_sub ts.hkTail_lt.le] at h1
      exact h1
    rw [hC, hxm_eq, Nat.cast_add, ← _root_.zpow_add, ← _root_.zpow_add]
    congr 1
    rw [hc1, hcM, hm_z, hxc_top, Nat.cast_add, Nat.cast_one]
    linear_combination -hpow_m2 + 2 * hq_z + hM_z

theorem sys_le_actWidth (mOut mMid : ℕ) : systemQubits_local ≤ actWidth 16 11 mOut mMid := by
  dsimp [actWidth, systemQubits_local]
  omega

theorem norm_unitary_mulVec_sub_le {k : ℕ} (U V : Unitary (2 ^ k)) (a b : Fin (2 ^ k) → ℂ)
    {δ₁ δ₂ : ℝ} (h1 : ‖WithLp.toLp 2 (a - b)‖ ≤ δ₁)
    (h2 : ‖WithLp.toLp 2 (U.1 *ᵥ b - V.1 *ᵥ b)‖ ≤ δ₂) :
    ‖WithLp.toLp 2 (U.1 *ᵥ a - V.1 *ᵥ b)‖ ≤ δ₁ + δ₂ := by
  have hsplit : WithLp.toLp 2 (U.1 *ᵥ a - V.1 *ᵥ b) =
      WithLp.toLp 2 (U.1 *ᵥ (a - b)) + WithLp.toLp 2 (U.1 *ᵥ b - V.1 *ᵥ b) := by
    ext g
    rw [Matrix.mulVec_sub]
    simp only [WithLp.ofLp_add, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ h2)
  rw [tgL2_norm_unitary_mulVec U]
  exact h1

theorem threeGearDeferBlockedPart3Prog_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 ko km M m2 m1 nDirtyLo sRem : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hm1_1 : 1 ≤ m1) (hDirty : nDirtyLo ≤ m1 - 1) (v : Var) (cIqft : Circuit 16)
    (hIqftToff : cIqft.count .TOFF = 0) (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo)
    {uRefl2F : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    {pRefl2F : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)}
    (hCleanF : CleanWalkRefl2 wOuter wInner2 ko km 0 sRem hkOut hkMid v uRefl2F pRefl2F) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let hm1_15 := spec_hm1_15 w
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rCombFull := rQPE.concat (rWalkCatInAct 16 11 mOut mMid)
      (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    let uF := rCombFull.embedUnitary
      (QubitisedWalk.qpeMuxUnitary (affineScheduleFiber m1 (2 ^ m1 - 1) (R₁c * uRefl2F) R₁c))
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid)
      (rQPE.embedUnitary cIqft.eval * uF *
        (rQPE.compose (rLoInQPE16 m1 (spec_hm1_16 w))).embedUnitary w.base.cWinLo.eval *
        (rQPE.compose (rBondHiInQPE16 m1 hm1_1 hm1_15)).embedUnitary w.cBond.eval)
      (threeGearDeferBlockedPart3Prog wOuter wInner2 ko km M m2 m1 nDirtyLo sRem
        hkOut hkMid hm1_1 hDirty v cIqft w pRefl2F) := by
  intro mOut mMid aRem mRem hm1_15 R₁c rQPE rCombFull uF
  let rAncZ := liftOutMidZeroToAnc mOut mMid
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  have hBond_raw := tgCleanRealizes_subcircuit 16 11 mOut mMid 0 aRem mRem sRem v rAncZ
    (rQPE.compose (rBondHiInQPE16 m1 hm1_1 hm1_15)) (fun j ↦ Or.inr (by
      simp only [rQPE, rQPEInAct, rBondHiInQPE16, QRegister.compose_apply,
        QRegister.block_apply_val]
      dsimp only [walkCatWidth]
      omega)) w.cBond w.count_bond_toff
  have hr : (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
      (rQPE.compose (rBondHiInQPE16 m1 hm1_1 hm1_15)) =
      (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose (rBondHiInQPE16 m1 hm1_1 hm1_15) := by
    ext
    rfl
  have hBond : XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rFullZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ)
      ((rQPE.compose (rBondHiInQPE16 m1 hm1_1 hm1_15)).embedUnitary w.cBond.eval)
      (.circuit (w.cBond.onRegister ((rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose
        (rBondHiInQPE16 m1 hm1_1 hm1_15)))) := hr ▸ hBond_raw
  have hP2 := twoGearBlockedPart2Prog_cleanRealizes wOuter wInner2 ko km M m1 nDirtyLo sRem
    hkOut hkMid hm1_1 hm1_15 v cIqft hIqftToff w.base hCleanF
  dsimp only at hP2
  exact cleanRealizes_of_eq (hBond.seq hP2)
    (by simp only [mOut, mMid, rQPE, rCombFull, R₁c, uF, mul_assoc])

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
end
