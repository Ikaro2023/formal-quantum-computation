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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3OuterShellB

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot3Norm1s36Physics80
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36Physics80 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace Slot3Norm1s36Physics80

section ConfigSlot3Norm1s36Physics80

set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

local instance (priority :=
  10) instLoc_Slot3Norm1s36Physics80_1InstNeZeroTwoPowNorm (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix NNReal ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open Slot3MicroEngineAux (allBelow allBelow_iff)
open Slot3Norm1s36_161w
  (Norm1sTier clz18Log2 clz18Log2_le_17 clz18Log2_bounds
   norm1sMant18 norm1sMant18_bounds norm1sRowVal norm1sHwRowsAux norm1sHwProd
   wc2TrueNat errBoundD q19 accThr)
open ModWrapCoarse8PureMomentum (nearestProtonCoord thetaProtonNearest modWrapCoord modFoldCoord
  modFold3D sumNatAbsSq maxCoordNatAbs shellIndex nonzeroBox3D box3D modFold3D_mem_nonzeroBox3D
  modFold3D_sub_inj_left modFold3D_sub_inj_right sumNatAbsSq_modFold3D_le sumNatAbsSq_pos_of_ne_zero
  norm_le_of_weightedPartialPerm operator_sum_apply ite_true_eq ite_false_eq boxRadConst
  coarseEnv8Count coarseBoxRadKernel8 coarseRadCeilVal7 coarseEnv8Count_eq_coarseRadCeilVal7
  coulombCoarse8PreOAAProb boost127_coarse8_w13 dampedModWrapKernelApprox
  dampedModWrapKernelApprox_zero)
open SubvoxelNuclearTrunc36Physics (nuclearM36 trunc36Cfg)
open Slot3MidKick36_161w (nearestProtonCoord_42_trunc36Cfg)
open Slot3MidKick36_161w (exp_thetaProtonNearest_42_trunc36Cfg)
open Slot3MidKick36_161w (int_mul64_emod_two_pow42_toNat)
open Slot3Exact216Oracle80
open Slot3StreamUncK35Shift3
  (CommutesWithReg basisBits_symm_apply piSwap3Wire piSwap3WireFun_involutive piSwap3CorePerm
    basisBits_piSwap3CorePerm uPiSwap3Core rEC80 rECPre80 rECPre80_val_cases not_mem_rECPre80_of_mid
    mem_rECPre80_of_lt_3924 disjoint_rECPre80_of_mid extractIndex_eq_of_agreeOutside_rECPre80
    projAxisField_eq_of_agreeOutside_rECPre80)
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open SpecsAux.DyadicSubgridToeplitz512AndShift DyadicQft64
open DyadicQft64.PhasePerm
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysPrepare6Slot (coinSelOutcome fullSysCoinIdx)
open FullSysMomSlots0135Concrete
open MomSlots35Coulomb
open Slot5MatrixAndScaleCert
open TwosCompAndWire0Cancel
open MomSlots35Slot3ProjNuclear
open MomSlots35Slot3ProjNuclear.Slot3CleanPrim
open StepBBlock0
  (sel149 sel107 sel107_80 sel107_80_val hmPay80 embedAlphaCore80 embedAlpha107
   embedAlpha107_sel107_80 embedAlpha107_fields dummyCfgS3
   bitsVal_eq_of_testBit bitsVal_slice_linear symm_basisBits basisBits_symm)
open MeasureBranchHadamardSem (bit_cases)

attribute [local irreducible] box3D nonzeroBox3D

/-- Mathematical 1-sided normalized radial acceptance test for `(t : Norm1sTier)` on `(mu, sTrue,
  u38)`. -/
def norm1sRadAccept (t : Norm1sTier) (mu sTrue u38 : ℕ) : Bool := decide
    (2 * mu ≤ clz18Log2 sTrue) && decide (norm1sHwProd t.kBits t.dCut (norm1sMant18 sTrue)
    (u38 / 2 ^ (38 - t.kBits)) < accThr t.kBits t.dCut (clz18Log2 sTrue - 2 * mu))

/-- Per-bit constant offset contribution at bit `m` matching `norm1sRowVal dCut m`. -/
def wc2RowVal (dCut m : ℕ) : ℕ :=
  if m < dCut then
    let sh := dCut - m
    if sh = 18 then 1
    else if sh < 18 then 2 * 2 ^ (18 - sh) - 1
    else 0
  else
    2 ^ 19 * 2 ^ (m - dCut)

/-- Prefix sum of `wc2RowVal dCut` over bits `0 .. n - 1`. -/
def wc2RowsAux (dCut : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => wc2RowsAux dCut n + wc2RowVal dCut n

theorem wc2RowsAux_eq_wc2TrueNat (t : Norm1sTier) :
    wc2RowsAux t.dCut t.kBits = wc2TrueNat t.kBits t.dCut := by
  cases t <;> decide

/-- Per-bit truncation remainder in `ℤ` at bit `m` (`0` for `m >= dCut`). -/
def deltaBitTerm (dCut m mS : ℕ) (uBit : Bool) : ℤ :=
  if m < dCut then
    let sh := dCut - m
    (if uBit then (-1 : ℤ) else 1) *
      (2 * ((mS % 2 ^ sh : ℕ) : ℤ) - (2 ^ sh : ℤ)) * (2 ^ m : ℤ)
  else 0

/-- Prefix sum of `deltaBitTerm dCut` over bits `0 .. n - 1` of `uK`. -/
def deltaNorm1sAux (dCut mS uK : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => deltaNorm1sAux dCut mS uK n + deltaBitTerm dCut n mS (uK.testBit n)

/-- Total signed truncation residual `Δ_norm1s(dCut, mS, uK)` in `ℤ`. -/
def deltaNorm1s (dCut mS uK : ℕ) : ℤ := 2 * (mS : ℤ) + deltaNorm1sAux dCut mS uK dCut

/-- Exact worst-case magnitude sum `∑_{m < n} |2 * (mS % 2^(dCut - m)) - 2^(dCut - m)| * 2^m`. -/
def deltaAbsSum (dCut mS : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      deltaAbsSum dCut mS n +
        (if n < dCut then
          |2 * ((mS % 2 ^ (dCut - n) : ℕ) : ℤ) - (2 ^ (dCut - n) : ℤ)| * (2 ^ n : ℤ)
         else 0)

theorem tier_dCut_le_18 (t : Norm1sTier) : t.dCut ≤ 18 := by
  cases t <;> decide

theorem tier_dCut_le_kBits (t : Norm1sTier) : t.dCut ≤ t.kBits := by
  cases t <;> decide

theorem tier_eight_le_kBits (t : Norm1sTier) : 8 ≤ t.kBits := by
  cases t <;> decide

theorem tier_kBits_le_30 (t : Norm1sTier) : t.kBits ≤ 30 := by
  cases t <;> decide

theorem norm1sRowVal_int_eq {dCut m mS : ℕ} (hd : dCut ≤ 18) (hmS : mS < 2 ^ 18) (uBit : Bool) :
    ((2 * norm1sRowVal dCut m mS uBit : ℤ) - (wc2RowVal dCut m : ℤ)) * (2 ^ dCut : ℤ) =
      (if uBit then (1 : ℤ) else -1) * 2 * (mS : ℤ) * (2 ^ m : ℤ) +
        deltaBitTerm dCut m mS uBit := by
  unfold norm1sRowVal wc2RowVal deltaBitTerm
  dsimp only
  by_cases hlt : m < dCut
  · simp only [hlt, ite_true]
    by_cases h18 : dCut - m = 18
    · obtain ⟨rfl, rfl⟩ : m = 0 ∧ dCut = 18 := ⟨by omega, by omega⟩
      simp only [Nat.sub_zero, ite_true, pow_zero, Nat.mod_eq_of_lt hmS]
      cases uBit with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        ring
      | true => simp
    · have hsh_lt : dCut - m < 18 := by omega
      simp only [h18, hsh_lt, ite_false, ite_true]
      set sh := dCut - m
      set w := 18 - sh
      set q := mS / 2 ^ sh
      have hpow_d : (2 ^ dCut : ℤ) = (2 ^ sh : ℤ) * (2 ^ m : ℤ) := by
        rw [← pow_add]
        exact congrArg ((2 : ℤ) ^ ·) (by omega)
      have hxm_lt : q < 2 ^ w := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos sh), ← pow_add, show w + sh = 18 from by omega]
        exact hmS
      have hw1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
      have hsub1 : ((2 * 2 ^ w - 1 : ℕ) : ℤ) = 2 * (2 ^ w : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_pow]
        norm_num
      have hmS_z : (mS : ℤ) = (q : ℤ) * (2 ^ sh : ℤ) + ((mS % 2 ^ sh : ℕ) : ℤ) := by
        conv_lhs => rw [(Nat.div_add_mod' mS (2 ^ sh)).symm]
        push_cast
        rfl
      cases uBit with
      | false =>
        simp only [Bool.false_eq_true, ite_false, Nat.cast_sub (by omega : q ≤ 2 ^ w - 1),
          Nat.cast_sub hw1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hsub1, hpow_d, hmS_z]
        ring
      | true =>
        simp only [ite_true, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, hsub1, hpow_d, hmS_z]
        ring
  · simp only [hlt, ite_false]
    have hpow_m : (2 ^ m : ℤ) = (2 ^ (m - dCut) : ℤ) * (2 ^ dCut : ℤ) := by
      rw [← pow_add]
      exact congrArg ((2 : ℤ) ^ ·) (by omega)
    cases uBit with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Nat.cast_mul, Nat.cast_sub (le_of_lt hmS),
        Nat.cast_pow, Nat.cast_ofNat, hpow_m]
      ring
    | true =>
      simp only [ite_true, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, hpow_m]
      ring

theorem testBit_sgn_eq (uK m : ℕ) : (if uK.testBit m then (1 : ℤ) else -1) * (2 ^ m : ℤ) = 2 *
    ((uK % 2 ^ (m + 1) : ℕ) : ℤ) - 2 * ((uK % 2 ^ m : ℕ) : ℤ) - (2 ^ m : ℤ) := by
  have hmod : uK % 2 ^ (m + 1) = uK % 2 ^ m + 2 ^ m * ((uK / 2 ^ m) % 2) := Nat.mod_pow_succ
  have htb : uK.testBit m = decide ((uK / 2 ^ m) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  rw [htb, hmod]
  rcases Nat.mod_two_eq_zero_or_one (uK / 2 ^ m) with h0 | h1
  · simp [h0]
  · simp [h1]; ring

theorem norm1sHwRowsAux_int_eq {dCut mS : ℕ} (uK : ℕ) (hd : dCut ≤ 18) (hmS : mS < 2 ^ 18) :
    ∀ n : ℕ,
      ((2 * norm1sHwRowsAux dCut mS uK n : ℤ) - (wc2RowsAux dCut n : ℤ)) * (2 ^ dCut : ℤ) =
        2 * (mS : ℤ) * (2 * ((uK % 2 ^ n : ℕ) : ℤ) - (2 ^ n : ℤ) + 1) +
          deltaNorm1sAux dCut mS uK n
  | 0 => by simp [norm1sHwRowsAux, wc2RowsAux, deltaNorm1sAux]
  | n + 1 => by
      have ih := norm1sHwRowsAux_int_eq uK hd hmS n
      have hrow := norm1sRowVal_int_eq (m := n) hd hmS (uK.testBit n)
      have hsgn : (if uK.testBit n then (1 : ℤ) else -1) * 2 * (mS : ℤ) * (2 ^ n : ℤ) =
          2 * (mS : ℤ) * (2 * ((uK % 2 ^ (n + 1) : ℕ) : ℤ) -
            2 * ((uK % 2 ^ n : ℕ) : ℤ) - (2 ^ n : ℤ)) := by
        rw [← testBit_sgn_eq uK n]
        ring
      have hp2 : (2 ^ (n + 1) : ℤ) = 2 * (2 ^ n : ℤ) := by ring
      simp only [norm1sHwRowsAux, wc2RowsAux, deltaNorm1sAux, Nat.cast_add]
      calc (2 * ((norm1sHwRowsAux dCut mS uK n : ℤ) +
              (norm1sRowVal dCut n mS (uK.testBit n) : ℤ)) -
              ((wc2RowsAux dCut n : ℤ) + (wc2RowVal dCut n : ℤ))) * (2 ^ dCut : ℤ)
          = (2 * (norm1sHwRowsAux dCut mS uK n : ℤ) - (wc2RowsAux dCut n : ℤ)) * (2 ^ dCut : ℤ) +
            (2 * (norm1sRowVal dCut n mS (uK.testBit n) : ℤ) - (wc2RowVal dCut n : ℤ)) *
              (2 ^ dCut : ℤ) := by ring
        _ = _ := by rw [ih, hrow, hsgn, hp2]; ring

theorem deltaNorm1sAux_eq_dCut (dCut mS uK : ℕ) :
    ∀ k : ℕ, deltaNorm1sAux dCut mS uK (dCut + k) = deltaNorm1sAux dCut mS uK dCut
  | 0 => rfl
  | k + 1 => by
      rw [Nat.add_succ, deltaNorm1sAux, deltaNorm1sAux_eq_dCut dCut mS uK k]
      simp [deltaBitTerm]

theorem norm1sHwProd_int_eq (t : Norm1sTier) {mS uK : ℕ} (hmS : mS < 2 ^ 18)
    (huK : uK < 2 ^ t.kBits) : ((2 * norm1sHwProd t.kBits t.dCut mS uK : ℤ) - (wc2TrueNat
    t.kBits t.dCut : ℤ)) * (2 ^ t.dCut : ℤ) = 4 * (mS : ℤ) * (uK : ℤ) + deltaNorm1s t.dCut mS
    uK := by
  have hdk : t.dCut ≤ t.kBits := tier_dCut_le_kBits t
  have hrows := norm1sHwRowsAux_int_eq uK (tier_dCut_le_18 t) hmS t.kBits
  have hdel : deltaNorm1sAux t.dCut mS uK t.kBits = deltaNorm1sAux t.dCut mS uK t.dCut := by
    rw [show t.kBits = t.dCut + (t.kBits - t.dCut) from by omega, deltaNorm1sAux_eq_dCut]
  rw [wc2RowsAux_eq_wc2TrueNat t, Nat.mod_eq_of_lt huK, hdel] at hrows
  have hpow : 2 * (mS : ℤ) * (2 ^ (t.kBits - t.dCut) : ℤ) * (2 ^ t.dCut : ℤ) =
      2 * (mS : ℤ) * (2 ^ t.kBits : ℤ) := by
    rw [mul_assoc, ← pow_add, show t.kBits - t.dCut + t.dCut = t.kBits from by omega]
  unfold norm1sHwProd deltaNorm1s
  push_cast
  linarith

theorem deltaNorm1sAux_abs_le (dCut mS uK : ℕ) :
    ∀ n : ℕ, |deltaNorm1sAux dCut mS uK n| ≤ deltaAbsSum dCut mS n
  | 0 => by simp [deltaNorm1sAux, deltaAbsSum]
  | n + 1 => by
      have ih := deltaNorm1sAux_abs_le dCut mS uK n
      simp only [deltaNorm1sAux, deltaAbsSum]
      by_cases hlt : n < dCut
      · simp only [hlt, ite_true]
        have hp_nn : (0 : ℤ) ≤ (2 ^ n : ℤ) := by positivity
        have hbt : |deltaBitTerm dCut n mS (uK.testBit n)| =
            |2 * ((mS % 2 ^ (dCut - n) : ℕ) : ℤ) - (2 ^ (dCut - n) : ℤ)| * (2 ^ n : ℤ) := by
          unfold deltaBitTerm
          cases uK.testBit n with
          | false => simp [hlt, abs_mul, abs_of_nonneg hp_nn]
          | true => simp [hlt, abs_mul, abs_of_nonneg hp_nn, abs_sub_comm]
        linarith [abs_add_le (deltaNorm1sAux dCut mS uK n)
          (deltaBitTerm dCut n mS (uK.testBit n)), ih, hbt]
      · simp [deltaBitTerm, hlt, ih]

theorem deltaAbsSum_succ_shift (d mS : ℕ) :
    ∀ k : ℕ, deltaAbsSum (d + 1) mS (k + 1) =
      |2 * ((mS % 2 ^ (d + 1) : ℕ) : ℤ) - (2 ^ (d + 1) : ℤ)| + 2 * deltaAbsSum d mS k
  | 0 => by simp [deltaAbsSum]
  | k + 1 => by
      rw [deltaAbsSum, deltaAbsSum_succ_shift d mS k, deltaAbsSum]
      simp only [Nat.add_lt_add_iff_right, Nat.succ_sub_succ_eq_sub, pow_succ]
      split_ifs <;> ring

theorem two_mul_mod_add_deltaAbsSum_le (mS : ℕ) :
    ∀ d : ℕ, 2 * ((mS % 2 ^ d : ℕ) : ℤ) + deltaAbsSum d mS d ≤ (d : ℤ) * (2 ^ d : ℤ)
  | 0 => by simp [deltaAbsSum]
  | d + 1 => by
      have ih := two_mul_mod_add_deltaAbsSum_le mS d
      rw [deltaAbsSum_succ_shift d mS d]
      have hmod : mS % 2 ^ (d + 1) = mS % 2 ^ d + 2 ^ d * ((mS / 2 ^ d) % 2) := Nat.mod_pow_succ
      have hr_lt : ((mS % 2 ^ d : ℕ) : ℤ) < (2 ^ d : ℤ) :=
        Nat.cast_lt.mpr (Nat.mod_lt mS (Nat.two_pow_pos d))
      have hpow_succ : (2 ^ (d + 1) : ℤ) = 2 * (2 ^ d : ℤ) := by ring
      rcases Nat.mod_two_eq_zero_or_one (mS / 2 ^ d) with h0 | h1
      · rw [show mS % 2 ^ (d + 1) = mS % 2 ^ d from by rw [hmod, h0]; omega,
          abs_of_nonpos (by linarith), Nat.cast_add, Nat.cast_one, hpow_succ]
        linarith
      · have hmod1 : ((mS % 2 ^ (d + 1) : ℕ) : ℤ) = ((mS % 2 ^ d : ℕ) : ℤ) + (2 ^ d : ℤ) := by
          rw [hmod, h1, Nat.mul_one]
          push_cast
          rfl
        rw [hmod1, abs_of_nonneg (by linarith), Nat.cast_add, Nat.cast_one, hpow_succ]
        linarith

theorem abs_deltaNorm1s_le (t : Norm1sTier) {mS : ℕ} (hmS : mS < 2 ^ 18) (uK : ℕ) :
    |deltaNorm1s t.dCut mS uK| ≤ (errBoundD t.dCut : ℤ) * (2 ^ t.dCut : ℤ) := by
  unfold deltaNorm1s
  have h1 := abs_add_le (2 * (mS : ℤ)) (deltaNorm1sAux t.dCut mS uK t.dCut)
  have h2 : |2 * (mS : ℤ)| = 2 * (mS : ℤ) := abs_of_nonneg (by positivity)
  have h3 := deltaNorm1sAux_abs_le t.dCut mS uK t.dCut
  have h4 := two_mul_mod_add_deltaAbsSum_le mS t.dCut
  have hdiv : (mS : ℤ) = ((mS / 2 ^ t.dCut : ℕ) : ℤ) * (2 ^ t.dCut : ℤ) +
      ((mS % 2 ^ t.dCut : ℕ) : ℤ) := by
    conv_lhs => rw [(Nat.div_add_mod' mS (2 ^ t.dCut)).symm]
    push_cast
    rfl
  have hcoef : 2 * ((mS / 2 ^ t.dCut : ℕ) : ℤ) + (t.dCut : ℤ) ≤ (errBoundD t.dCut : ℤ) := by
    cases t <;> dsimp [Norm1sTier.dCut, errBoundD] <;> omega
  linarith [mul_le_mul_of_nonneg_right hcoef (show (0 : ℤ) ≤ 2 ^ t.dCut by positivity)]

/-- Exact mathematical count of accepted `uK < 2 ^ t.kBits` at `(mu, sTrue)`. -/
def norm1sAcceptCountK (t : Norm1sTier) (mu sTrue : ℕ) : ℕ := if 2 * mu ≤ clz18Log2 sTrue then
    ((Finset.range (2 ^ t.kBits)).filter (fun uK ↦ norm1sHwProd t.kBits t.dCut (norm1sMant18
    sTrue) uK < accThr t.kBits t.dCut (clz18Log2 sTrue - 2 * mu))).card else 0

theorem finK_low_lt_38 (t : Norm1sTier) (uK : ℕ) (huK : uK < 2 ^ t.kBits)
    (uLo : Fin (2 ^ (38 - t.kBits))) : uLo.val + 2 ^ (38 - t.kBits) * uK < 2 ^ 38 := by
  have hk30 : t.kBits ≤ 30 := tier_kBits_le_30 t
  have hpow : 2 ^ 38 = 2 ^ (38 - t.kBits) * 2 ^ t.kBits := by rw [← pow_add]; congr 1; omega
  have hlo := uLo.isLt
  nlinarith

theorem norm1sAcceptCount38_eq (t : Norm1sTier) (mu sTrue : ℕ) : ((Finset.univ : Finset (Fin
    256 × Fin (2 ^ 30))).filter (fun p ↦ norm1sRadAccept t mu sTrue (p.2.val + 2 ^ 30 *
    p.1.val) = true)).card = 2 ^ (38 - t.kBits) * norm1sAcceptCountK t mu sTrue := by
  have hk30 : t.kBits ≤ 30 := tier_kBits_le_30 t
  unfold norm1sAcceptCountK
  by_cases hge : 2 * mu ≤ clz18Log2 sTrue
  · simp only [hge, ite_true]
    set S_K := (Finset.range (2 ^ t.kBits)).filter (fun uK ↦
      norm1sHwProd t.kBits t.dCut (norm1sMant18 sTrue) uK <
        accThr t.kBits t.dCut (clz18Log2 sTrue - 2 * mu))
    set S_lo : Finset (Fin (2 ^ (38 - t.kBits))) := Finset.univ
    have hdiv (a : Fin (2 ^ (38 - t.kBits))) (b : ℕ) :
        (a.val + 2 ^ (38 - t.kBits) * b) / 2 ^ (38 - t.kBits) = b := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt a.isLt, zero_add]
    suffices hbij :
        ((Finset.univ : Finset (Fin 256 × Fin (2 ^ 30))).filter
          (fun p ↦ norm1sRadAccept t mu sTrue (p.2.val + 2 ^ 30 * p.1.val) = true)).card =
          (S_lo ×ˢ S_K).card by
      rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    symm
    refine Finset.card_bij
      (fun q hq ↦
        let u38 := q.1.val + 2 ^ (38 - t.kBits) * q.2
        (⟨u38 / 2 ^ 30, by
          have hlt := finK_low_lt_38 t q.2
            (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).1) q.1
          omega⟩,
         ⟨u38 % 2 ^ 30, Nat.mod_lt _ (Nat.two_pow_pos 30)⟩))
      (fun q hq ↦ ?_) (fun q₁ _ q₂ _ heq ↦ ?_) (fun p hp ↦ ?_)
    · rcases Finset.mem_filter.mp (Finset.mem_product.mp hq).2 with ⟨_, hprod⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      unfold norm1sRadAccept
      rw [show (q.1.val + 2 ^ (38 - t.kBits) * q.2) % 2 ^ 30 +
          2 ^ 30 * ((q.1.val + 2 ^ (38 - t.kBits) * q.2) / 2 ^ 30) =
          q.1.val + 2 ^ (38 - t.kBits) * q.2 from by omega, hdiv]
      simp [hge, hprod]
    · have h1 := congrArg (fun x : Fin 256 × Fin (2 ^ 30) ↦ x.2.val + 2 ^ 30 * x.1.val) heq
      dsimp only at h1
      have hu_eq : q₁.1.val + 2 ^ (38 - t.kBits) * q₁.2 =
          q₂.1.val + 2 ^ (38 - t.kBits) * q₂.2 := by omega
      have hq2 : q₁.2 = q₂.2 := by rw [← hdiv q₁.1 q₁.2, hu_eq, hdiv q₂.1 q₂.2]
      exact Prod.ext (Fin.ext (by rw [hq2] at hu_eq; omega)) hq2
    · have hacc := (Finset.mem_filter.mp hp).2
      unfold norm1sRadAccept at hacc
      simp only [hge, decide_true, Bool.true_and, decide_eq_true_eq] at hacc
      set u38 := p.2.val + 2 ^ 30 * p.1.val
      have huK_lt : u38 / 2 ^ (38 - t.kBits) < 2 ^ t.kBits := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), mul_comm, ← pow_add,
          show 38 - t.kBits + t.kBits = 38 from by omega]
        have := p.1.isLt
        have := p.2.isLt
        omega
      refine ⟨(⟨u38 % 2 ^ (38 - t.kBits), Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
        u38 / 2 ^ (38 - t.kBits)),
        Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huK_lt, hacc⟩⟩, ?_⟩
      have hmd := Nat.mod_add_div u38 (2 ^ (38 - t.kBits))
      have hp1 := p.1.isLt
      have hp2 := p.2.isLt
      exact Prod.ext (Fin.ext (by dsimp only; rw [hmd]; dsimp [u38]; omega))
        (Fin.ext (by dsimp only; rw [hmd]; dsimp [u38]; omega))
  · simp only [hge, ite_false, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    simp [norm1sRadAccept, hge]

/-- Maximum folded squared norm `3 * (2^(mu + 1) - 1)^2` on dyadic shell `mu`. -/
def shellSqCap (mu : ℕ) : ℕ := 3 * (2 ^ (mu + 1) - 1) ^ 2

theorem sumNatAbsSq_le_shellSqCap (ν : Fin 3 → ℤ) :
    sumNatAbsSq ν ≤ shellSqCap (shellIndex ν) := by
  have hm_lt : maxCoordNatAbs ν < 2 ^ (shellIndex ν + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (maxCoordNatAbs ν)
  have hm_le : maxCoordNatAbs ν ≤ 2 ^ (shellIndex ν + 1) - 1 := by omega
  have h0 : (ν 0).natAbs ^ 2 ≤ (2 ^ (shellIndex ν + 1) - 1) ^ 2 :=
    Nat.pow_le_pow_left ((le_max_left _ _).trans hm_le) 2
  have h1 : (ν 1).natAbs ^ 2 ≤ (2 ^ (shellIndex ν + 1) - 1) ^ 2 :=
    Nat.pow_le_pow_left (((le_max_left _ _).trans (le_max_right _ _)).trans hm_le) 2
  have h2 : (ν 2).natAbs ^ 2 ≤ (2 ^ (shellIndex ν + 1) - 1) ^ 2 :=
    Nat.pow_le_pow_left (((le_max_right _ _).trans (le_max_right _ _)).trans hm_le) 2
  unfold sumNatAbsSq shellSqCap
  rw [Fin.sum_univ_three]
  omega

/-- Boolean check helper certifying `c8 * sFold <= coarseRadCeilVal7 mu` across all `(mu, d)`. -/
def coarseEnvPairOk (kBits dCut mu d : ℕ) : Bool :=
  decide (2 * mu + d ≤ 17 →
    let e := 2 * mu + d
    let sCap := shellSqCap mu
    let ceil := coarseRadCeilVal7 mu
    let num := ((q19 kBits dCut d + errBoundD dCut) * 2 ^ (dCut + e)) / 2 ^ (11 + kBits)
    (num / max (2 ^ e) (sCap + 1)) * sCap ≤ ceil ∧
      (2 ^ e ≤ sCap →
        num ≤ ceil ∨
          (num = ceil + 1 ∧
            allBelow (num / 2 ^ e + 1) (fun c ↦
              decide (0 < c → num % c ≠ 0 ∨ num / c < 2 ^ e ∨ sCap < num / c)) = true)))

theorem norm1s_coarseEnv_num_check (t : Norm1sTier) :
    allBelow 7 (fun mu ↦ allBelow 18 (fun d ↦ coarseEnvPairOk t.kBits t.dCut mu d)) = true := by
  cases t <;> decide

theorem norm1sRadAccept_imp_coarseEnv8_lt (t : Norm1sTier) {mu sFold sTrue : ℕ} (hmu : mu ≤ 6)
    (hs0 : 0 < sFold) (hs_cap : sFold ≤ shellSqCap mu) (hs_le : sFold ≤ sTrue)
    (hs18 : sTrue < 2 ^ 18) (c8 : Fin 256) (f30 : Fin (2 ^ 30)) (hacc : norm1sRadAccept t mu
    sTrue (f30.val + 2 ^ 30 * c8.val) = true) : c8.val < coarseEnv8Count
    (boxRadConst 36 (1 / 42) 1 mu) sFold := by
  have hsTrue0 : 0 < sTrue := lt_of_lt_of_le hs0 hs_le
  obtain ⟨heLo, _⟩ := clz18Log2_bounds hsTrue0 hs18
  have he17 : clz18Log2 sTrue ≤ 17 := clz18Log2_le_17 sTrue
  have hmHi : norm1sMant18 sTrue < 2 ^ 18 := (norm1sMant18_bounds hsTrue0 hs18).2
  unfold norm1sRadAccept at hacc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
  rcases hacc with ⟨hge, hprod⟩
  set e := clz18Log2 sTrue
  set d := e - 2 * mu
  set u38 := f30.val + 2 ^ 30 * c8.val
  set uK := u38 / 2 ^ (38 - t.kBits)
  have hk8 : 8 ≤ t.kBits := tier_eight_le_kBits t
  have hk30 : t.kBits ≤ 30 := tier_kBits_le_30 t
  have hu38_lt : u38 < 2 ^ 38 := by dsimp [u38]; have := c8.isLt; have := f30.isLt; omega
  have hpow38 : 2 ^ 38 = 2 ^ t.kBits * 2 ^ (38 - t.kBits) := by rw [← pow_add]; congr 1; omega
  have huK_lt : uK < 2 ^ t.kBits := by
    dsimp [uK]; rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hpow38]; exact hu38_lt
  have hc8_le_uK : c8.val * 2 ^ (t.kBits - 8) ≤ uK := by
    dsimp [uK]
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    have hpow30 : 2 ^ (t.kBits - 8) * 2 ^ (38 - t.kBits) = 2 ^ 30 := by
      rw [← pow_add]; congr 1; omega
    calc c8.val * 2 ^ (t.kBits - 8) * 2 ^ (38 - t.kBits)
      _ = 2 ^ 30 * c8.val := by rw [mul_assoc, hpow30, mul_comm]
      _ ≤ u38 := by dsimp [u38]; omega
  have hid := norm1sHwProd_int_eq t hmHi huK_lt
  have habs := (abs_le.mp (abs_deltaNorm1s_le t hmHi uK)).1
  have hthr_le : 2 * accThr t.kBits t.dCut d ≤
      q19 t.kBits t.dCut d + wc2TrueNat t.kBits t.dCut + 2 := by
    unfold accThr; have :=
      Nat.div_mul_le_self (q19 t.kBits t.dCut d + wc2TrueNat t.kBits t.dCut + 2) 2
    omega
  have h2p : (2 * norm1sHwProd t.kBits t.dCut (norm1sMant18 sTrue) uK : ℤ) -
      (wc2TrueNat t.kBits t.dCut : ℤ) ≤ (q19 t.kBits t.dCut d : ℤ) := by omega
  have hprod_z : 4 * (norm1sMant18 sTrue : ℤ) * (uK : ℤ) ≤
      ((q19 t.kBits t.dCut d + errBoundD t.dCut : ℕ) : ℤ) * (2 ^ t.dCut : ℤ) := by
    have hle := mul_le_mul_of_nonneg_right h2p (show (0 : ℤ) ≤ (2 ^ t.dCut : ℤ) by positivity)
    push_cast; linarith
  have hprod_nat : 4 * norm1sMant18 sTrue * uK ≤
      (q19 t.kBits t.dCut d + errBoundD t.dCut) * 2 ^ t.dCut := by exact_mod_cast hprod_z
  have hmul11 : (c8.val * sTrue) * 2 ^ (11 + t.kBits) ≤
      (q19 t.kBits t.dCut d + errBoundD t.dCut) * 2 ^ (t.dCut + e) := by
    have hpow_comb : 4 * 2 ^ (17 - e) * 2 ^ (t.kBits - 8) * 2 ^ e = 2 ^ (11 + t.kBits) := by
      have h4 : (4 : ℕ) = 2 ^ 2 := rfl
      rw [h4, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
    calc (c8.val * sTrue) * 2 ^ (11 + t.kBits)
      _ = 4 * (sTrue * 2 ^ (17 - e)) * (c8.val * 2 ^ (t.kBits - 8)) * 2 ^ e := by
            rw [← hpow_comb]; ring
      _ ≤ 4 * norm1sMant18 sTrue * uK * 2 ^ e := by
            dsimp [norm1sMant18, e]
            exact Nat.mul_le_mul_right (2 ^ e) (Nat.mul_le_mul_left _ hc8_le_uK)
      _ ≤ (q19 t.kBits t.dCut d + errBoundD t.dCut) * 2 ^ t.dCut * 2 ^ e :=
            Nat.mul_le_mul_right _ hprod_nat
      _ = (q19 t.kBits t.dCut d + errBoundD t.dCut) * 2 ^ (t.dCut + e) := by
            rw [mul_assoc, ← pow_add]
  set num := ((q19 t.kBits t.dCut d + errBoundD t.dCut) * 2 ^ (t.dCut + e)) / 2 ^ (11 + t.kBits)
  have hc8_sTrue : c8.val * sTrue ≤ num :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hmul11
  have he_eq : 2 * mu + d = e := by omega
  have hchk1 := (allBelow_iff 7 _).mp (norm1s_coarseEnv_num_check t) mu (by omega)
  have hchk2 := (allBelow_iff 18 _).mp hchk1 d (by omega)
  unfold coarseEnvPairOk at hchk2
  have hpair := (of_decide_eq_true hchk2) (by omega)
  dsimp only at hpair
  rw [he_eq] at hpair
  rcases hpair with ⟨hbig, hsmall⟩
  have hc8_ceil : c8.val * sFold ≤ coarseRadCeilVal7 mu := by
    by_cases hgt : shellSqCap mu < sTrue
    · have hmax_le : max (2 ^ e) (shellSqCap mu + 1) ≤ sTrue := max_le heLo (by omega)
      have hc8_div : c8.val ≤ num / max (2 ^ e) (shellSqCap mu + 1) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        exact (Nat.mul_le_mul_left c8.val hmax_le).trans hc8_sTrue
      exact (Nat.mul_le_mul hc8_div hs_cap).trans hbig
    · have hle_cap : sTrue ≤ shellSqCap mu := by omega
      have he_cap : 2 ^ e ≤ shellSqCap mu := heLo.trans hle_cap
      rcases hsmall he_cap with hle_c | ⟨hnum_eq, hallB⟩
      · exact (Nat.mul_le_mul_left c8.val hs_le).trans (hc8_sTrue.trans hle_c)
      · by_cases hc0 : c8.val = 0
        · rw [hc0, zero_mul]; exact Nat.zero_le _
        · have hc_div : c8.val < num / 2 ^ e + 1 := by
            have hle_d : c8.val ≤ num / 2 ^ e :=
              (Nat.le_div_iff_mul_le (Nat.two_pow_pos e)).mpr
                ((Nat.mul_le_mul_left c8.val heLo).trans hc8_sTrue)
            omega
          have hc_ok := (of_decide_eq_true
            ((allBelow_iff _ _).mp hallB c8.val hc_div)) (by omega)
          have hnot_eq : c8.val * sTrue ≠ num := by
            intro heq
            have hmod0 : num % c8.val = 0 := by rw [← heq]; exact Nat.mul_mod_right _ _
            have hquot : num / c8.val = sTrue := by
              rw [← heq, mul_comm]; exact Nat.mul_div_left sTrue (by omega)
            rcases hc_ok with h1 | h2 | h3
            · exact h1 hmod0
            · rw [hquot] at h2; omega
            · rw [hquot] at h3; omega
          have hlt_num : c8.val * sTrue < num := lt_of_le_of_ne hc8_sTrue hnot_eq
          exact (Nat.mul_le_mul_left c8.val hs_le).trans (by omega)
  rw [coarseEnv8Count_eq_coarseRadCeilVal7 hmu hs0]
  have hstep : (c8.val + 1) * sFold ≤ coarseRadCeilVal7 mu + sFold := by nlinarith
  have hdiv_le : c8.val + 1 ≤ (coarseRadCeilVal7 mu + sFold) / sFold :=
    (Nat.le_div_iff_mul_le hs0).mpr hstep
  omega

/-- Parametric 1-sided normalized Slot-3 core acceptance predicate for `(t : Norm1sTier)`
(`coin = 6`, `ProjTwosGridState xSys`, `validShellNu3 u22 s3`, and
`norm1sRadAccept t (shellMu3 u22) sTrue u38`). -/
noncomputable def s3AcceptNorm1s (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : Bool :=
  let coin := (momCoinReg mPayload).extractIndex z
  let xSys := (momSysReg mPayload).extractIndex z
  let u22 := (s3U22Core hmPay).extractIndex z
  let s3 := (s3S3Core hmPay).extractIndex z
  let c8 := (s3C8Core hmPay).extractIndex z
  let f30 := (s3Fine30Core hmPay).extractIndex z
  let st0 := s3ProjStepHw (projAxisField xSys 0) (shellMagCoord3 u22 0) (signBit3 s3 0)
  let st1 := s3ProjStepHw (projAxisField xSys 1) (shellMagCoord3 u22 1) (signBit3 s3 1)
  let st2 := s3ProjStepHw (projAxisField xSys 2) (shellMagCoord3 u22 2) (signBit3 s3 2)
  let sTrue := st0.2.1 * st0.2.1 + st1.2.1 * st1.2.1 + st2.2.1 * st2.2.1
  let u38 := f30.val + 2 ^ 30 * c8.val
  decide (coin.val = 6) &&
    s3ProjGridBool xSys &&
    validShellNu3 u22 s3 &&
    norm1sRadAccept t (shellMu3 u22) sTrue u38

/-- Parametric 1-sided normalized Slot-3 core basis permutation map on `momCoreWires mPayload`. -/
noncomputable def s3CoreMapNorm1s (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : Fin (2 ^ (momCoreWires mPayload)) :=
  if s3AcceptNorm1s t hmPay z = true then
    let xSys := (momSysReg mPayload).extractIndex z
    let u22 := (s3U22Core hmPay).extractIndex z
    let s3 := (s3S3Core hmPay).extractIndex z
    let xNew := s3UpdateSysProj xSys fun w ↦
      (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1
    let s3New := negSign3_22 u22 s3
    (basisBitsEquiv (momCoreWires mPayload)).symm fun k ↦
      if hkSys : k.val < SpecsAux.SpecMirror.systemQubits then
        basisBits SpecsAux.SpecMirror.systemQubits xNew ⟨k.val, hkSys⟩
      else if hkS3 : 3976 ≤ k.val ∧ k.val < 3979 then
        basisBits 3 s3New ⟨k.val - 3976, Nat.sub_lt_left_of_lt_add hkS3.1 hkS3.2⟩
      else
        basisBits (momCoreWires mPayload) z k
  else z

theorem s3CoreMapNorm1s_fields {t : Norm1sTier} {mPayload : ℕ} {hmPay : 80 ≤ mPayload}
    {z : Fin (2 ^ (momCoreWires mPayload))} (hz : s3AcceptNorm1s t hmPay z = true) :
    let z' := s3CoreMapNorm1s t hmPay z
    let xSys := (momSysReg mPayload).extractIndex z
    let u22 := (s3U22Core hmPay).extractIndex z
    let s3 := (s3S3Core hmPay).extractIndex z
    (momCoinReg mPayload).extractIndex z' = (momCoinReg mPayload).extractIndex z ∧
    (momSysReg mPayload).extractIndex z' =
      s3UpdateSysProj xSys (fun w ↦
        (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1) ∧
    (s3U22Core hmPay).extractIndex z' = u22 ∧
    (s3S3Core hmPay).extractIndex z' = negSign3_22 u22 s3 ∧
    (s3C8Core hmPay).extractIndex z' = (s3C8Core hmPay).extractIndex z ∧
    (s3Fine30Core hmPay).extractIndex z' = (s3Fine30Core hmPay).extractIndex z ∧
    basisBits (momCoreWires mPayload) z' (s3BParCore hmPay) =
      basisBits (momCoreWires mPayload) z (s3BParCore hmPay) ∧
    (s3U16Core hmPay).extractIndex z' = (s3U16Core hmPay).extractIndex z ∧
    (∀ w : Wire (momCoreWires mPayload), 4034 ≤ w.val →
      basisBits (momCoreWires mPayload) z' w = basisBits (momCoreWires mPayload) z w) ∧
    (∀ w : Wire (momCoreWires mPayload), 3951 ≤ w.val → w.val < 3954 →
      basisBits (momCoreWires mPayload) z' w = basisBits (momCoreWires mPayload) z w) := by
  intro z' xSys u22 s3
  have hbits : ∀ k : Wire (momCoreWires mPayload),
      basisBits (momCoreWires mPayload) z' k =
        if hkSys : k.val < SpecsAux.SpecMirror.systemQubits then
          basisBits SpecsAux.SpecMirror.systemQubits
            (s3UpdateSysProj xSys (fun w ↦
              (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1))
            ⟨k.val, hkSys⟩
        else if hkS3 : 3976 ≤ k.val ∧ k.val < 3979 then
          basisBits 3 (negSign3_22 u22 s3) ⟨k.val - 3976, by omega⟩
        else
          basisBits (momCoreWires mPayload) z k := by
    intro k
    dsimp only [z', s3CoreMapNorm1s]
    rw [s3ItePos hz]
    exact congrFun ((basisBitsEquiv (momCoreWires mPayload)).apply_symm_apply _) k
  have hext : ∀ {qLen : ℕ} (r : QRegister qLen (momCoreWires mPayload)) (u : Fin (2 ^ qLen)),
      (∀ b : Fin qLen, basisBits (momCoreWires mPayload) z' (r b) = basisBits qLen u b) →
      r.extractIndex z' = u := fun {qLen} r u h ↦ by
    apply (basisBitsEquiv qLen).injective; funext b
    change basisBits qLen (r.extractIndex z') b = basisBits qLen u b
    rw [QRegister.basisBits_extractIndex]; exact h b
  have hw_keep : ∀ w : Wire (momCoreWires mPayload), 3948 ≤ w.val →
      (w.val < 3976 ∨ 3979 ≤ w.val) →
      basisBits (momCoreWires mPayload) z' w = basisBits (momCoreWires mPayload) z w :=
    fun w hlo hdisj ↦ by
      rw [hbits w, s3DiteNeg (by rw [s3SysQubits_eq]; omega),
        s3DiteNeg (by rcases hdisj with h | h <;> omega)]
  have hkeep : ∀ {q : ℕ} (r : QRegister q (momCoreWires mPayload)) (off : ℕ),
      (∀ b : Fin q, (r b).val = off + b.val) → 3948 ≤ off → (off + q ≤ 3976 ∨ 3979 ≤ off) →
      r.extractIndex z' = r.extractIndex z := fun r off hv hlo hdisj ↦
    hext r (r.extractIndex z) fun b ↦ by
      have hb := b.isLt
      rw [hw_keep (r b) (by rw [hv b]; omega)
        (by rw [hv b]; rcases hdisj with h | h <;> omega), QRegister.basisBits_extractIndex]
  have hvBp : (s3BParCore hmPay).val = 4017 := rfl
  refine ⟨hkeep (momCoinReg mPayload) 3948 (fun _ ↦ rfl) (by decide) (Or.inl (by decide)), ?_,
    hkeep (s3U22Core hmPay) 3954 (fun _ ↦ rfl) (by decide) (Or.inl (by decide)), ?_,
    hkeep (s3C8Core hmPay) 3979 (fun _ ↦ rfl) (by decide) (Or.inr (by decide)),
    hkeep (s3Fine30Core hmPay) 3987 (fun _ ↦ rfl) (by decide) (Or.inr (by decide)),
    hw_keep (s3BParCore hmPay) (by rw [hvBp]; decide) (Or.inr (by rw [hvBp]; decide)),
    hkeep (s3U16Core hmPay) 4018 (fun _ ↦ rfl) (by decide) (Or.inr (by decide)),
    fun w hwge ↦ hw_keep w (by omega) (Or.inr (by omega)),
    fun w hwlo hwhi ↦ hw_keep w (by omega) (Or.inl (by omega))⟩
  · refine hext (momSysReg mPayload) _ fun b ↦ ?_
    have hbVal : (momSysReg mPayload b).val = b.val := Nat.zero_add b.val
    rw [hbits (momSysReg mPayload b), s3DitePos (by rw [hbVal]; exact b.isLt)]
    exact congrArg _ (Fin.ext hbVal)
  · refine hext (s3S3Core hmPay) (negSign3_22 u22 s3) fun b ↦ ?_
    have hb := b.isLt
    have hbVal : (s3S3Core hmPay b).val = 3976 + b.val := rfl
    rw [hbits (s3S3Core hmPay b), s3DiteNeg (by rw [hbVal, s3SysQubits_eq]; omega),
      s3DitePos (by rw [hbVal]; omega)]
    exact congrArg (basisBits 3 (negSign3_22 u22 s3)) (Fin.ext (by dsimp only; rw [hbVal]; omega))

theorem s3AcceptNorm1s_and_involutive (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) :
    s3AcceptNorm1s t hmPay (s3CoreMapNorm1s t hmPay z) = s3AcceptNorm1s t hmPay z ∧
      s3CoreMapNorm1s t hmPay (s3CoreMapNorm1s t hmPay z) = z ∧
      s3NucleusIdx216 hmPay (s3CoreMapNorm1s t hmPay z) = s3NucleusIdx216 hmPay z := by
  by_cases hz : s3AcceptNorm1s t hmPay z = true
  · obtain ⟨hCoin, hSys, hU22, hS3, hC8, hF30, hBPar, hU16, _, _⟩ := s3CoreMapNorm1s_fields hz
    have hzUnf : s3AcceptNorm1s t hmPay z = true := hz
    unfold s3AcceptNorm1s at hzUnf
    obtain ⟨hc6B, hgridB, hvsh, hfineB⟩ := s3And4.mp hzUnf
    have hgrid : ProjTwosGridState ((momSysReg mPayload).extractIndex z) :=
      (s3ProjGridBool_eq_true_iff _).mp hgridB
    set xSys := (momSysReg mPayload).extractIndex z
    set u22 := (s3U22Core hmPay).extractIndex z
    set s3 := (s3S3Core hmPay).extractIndex z
    set z' := s3CoreMapNorm1s t hmPay z
    rcases s3UpdateSysProj_fields xSys (fun w ↦
      (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1) with
      ⟨heZ', hpZ'⟩
    have hvsh' : validShellNu3 u22 (negSign3_22 u22 s3) = true := by
      rw [validShellNu3_negSign3_22]; exact hvsh
    have hax : ∀ w : Fin 3,
        (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1.val ≠ 128 ∧
        (s3ProjStepHw (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1
          (shellMagCoord3 u22 w) (signBit3 (negSign3_22 u22 s3) w)).1 = projAxisField xSys w ∧
        (s3ProjStepHw (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1
          (shellMagCoord3 u22 w) (signBit3 (negSign3_22 u22 s3) w)).2.1 =
          (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).2.1 :=
      fun w ↦ s3AxisStep_involutive (hgrid w) hvsh w
    have hz'Acc : s3AcceptNorm1s t hmPay z' = true := by
      have hgrid' : s3ProjGridBool (s3UpdateSysProj xSys (fun w ↦
          (s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1)) = true :=
        (s3ProjGridBool_eq_true_iff _).mpr fun w ↦ by rw [hpZ' w]; exact (hax w).1
      unfold s3AcceptNorm1s
      dsimp only
      rw [hCoin, hSys, hU22, hS3, hC8, hF30,
        hpZ' 0, hpZ' 1, hpZ' 2, (hax 0).2.2, (hax 1).2.2, (hax 2).2.2]
      exact s3And4.mpr ⟨hc6B, hgrid', hvsh', hfineB⟩
    refine ⟨hz'Acc.trans hz.symm, ?_, ?_⟩
    · rcases s3CoreMapNorm1s_fields hz'Acc with
        ⟨_, hSys'', _, hS3'', _, _, _, _, _, _⟩
      apply (basisBitsEquiv (momCoreWires mPayload)).injective
      funext k
      have hk_lt : k.val < 3954 + mPayload := by rw [← s3MomCoreWires_eq]; exact k.isLt
      by_cases hkSys : k.val < SpecsAux.SpecMirror.systemQubits
      · have hx'' : (momSysReg mPayload).extractIndex (s3CoreMapNorm1s t hmPay z') = xSys := by
          rw [hSys'', hSys, hU22, hS3]
          refine s3UpdateSysProj_eq_iff.mpr ⟨heZ', fun w ↦ ?_⟩
          rw [hpZ' w]; exact (hax w).2.1
        have hb1 := QRegister.basisBits_extractIndex (momSysReg mPayload)
          (s3CoreMapNorm1s t hmPay z') ⟨k.val, hkSys⟩
        have hb2 := QRegister.basisBits_extractIndex (momSysReg mPayload) z ⟨k.val, hkSys⟩
        have hkEq : momSysReg mPayload ⟨k.val, hkSys⟩ = k := Fin.ext (Nat.zero_add k.val)
        rw [hkEq] at hb1 hb2
        exact hb1.symm.trans ((congrArg (fun u ↦
          basisBits SpecsAux.SpecMirror.systemQubits u ⟨k.val, hkSys⟩)
          hx'').trans hb2)
      · by_cases hkS3 : 3976 ≤ k.val ∧ k.val < 3979
        · have hs'' : (s3S3Core hmPay).extractIndex (s3CoreMapNorm1s t hmPay z') = s3 := by
            rw [hS3'', hU22, hS3]; exact negSign3_22_involutive u22 s3
          let idx3 : Fin 3 := ⟨k.val - 3976, by omega⟩
          have hb1 := QRegister.basisBits_extractIndex (s3S3Core hmPay)
            (s3CoreMapNorm1s t hmPay z') idx3
          have hb2 := QRegister.basisBits_extractIndex (s3S3Core hmPay) z idx3
          have hkEq : s3S3Core hmPay idx3 = k := Fin.ext (by
            change 3976 + idx3.val = k.val; dsimp [idx3]; omega)
          rw [hkEq] at hb1 hb2
          exact hb1.symm.trans ((congrArg (fun u ↦ basisBits 3 u idx3) hs'').trans hb2)
        · have hstep1 : basisBits (momCoreWires mPayload) (s3CoreMapNorm1s t hmPay z') k =
              basisBits (momCoreWires mPayload) z' k := by
            unfold s3CoreMapNorm1s
            rw [s3ItePos hz'Acc, congrFun (Slot3CleanPrim.basisBits_symm_apply_s1 _) k,
              s3DiteNeg hkSys, s3DiteNeg hkS3]
          have hstep2 : basisBits (momCoreWires mPayload) z' k =
              basisBits (momCoreWires mPayload) z k := by
            dsimp only [z', s3CoreMapNorm1s]
            rw [s3ItePos hz, congrFun (Slot3CleanPrim.basisBits_symm_apply_s1 _) k,
              s3DiteNeg hkSys, s3DiteNeg hkS3]
          exact hstep1.trans hstep2
    · apply Fin.ext
      unfold s3NucleusIdx216
      dsimp only
      rw [hU16, hBPar]
  · have hmap : s3CoreMapNorm1s t hmPay z = z := by unfold s3CoreMapNorm1s; rw [s3IteNeg hz]
    rw [hmap, hmap]
    exact ⟨rfl, rfl, rfl⟩

/-- Involutive equivalence `s3CorePermNorm1s t hmPay` on `Fin (2 ^ (momCoreWires mPayload))`. -/
noncomputable def s3CorePermNorm1s (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Equiv.Perm (Fin (2 ^ (momCoreWires mPayload))) where
  toFun := s3CoreMapNorm1s t hmPay
  invFun := s3CoreMapNorm1s t hmPay
  left_inv z := (s3AcceptNorm1s_and_involutive t hmPay z).2.1
  right_inv z := (s3AcceptNorm1s_and_involutive t hmPay z).2.1

/-- Real `±1` rejection phase on `s3SwapRejUnitaryNorm1s` (`(-1)^{bPar}` on rejected `coin = 6`
  states). -/
noncomputable def s3RejPhaseNorm1s (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : ℝ := if
    ((momCoinReg mPayload).extractIndex z).val = 6 ∧ s3AcceptNorm1s t hmPay z = false then if
    basisBits (momCoreWires mPayload) z (s3BParCore hmPay) = 1 then -1 else 1 else 1

theorem s3RejPhaseNorm1s_symm (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) :
    s3RejPhaseNorm1s t hmPay (s3CorePermNorm1s t hmPay z) = s3RejPhaseNorm1s t hmPay z := by
  by_cases hz : s3AcceptNorm1s t hmPay z = true
  · have hz' : s3AcceptNorm1s t hmPay (s3CoreMapNorm1s t hmPay z) = true :=
      ((s3AcceptNorm1s_and_involutive t hmPay z).1).trans hz
    change s3RejPhaseNorm1s t hmPay (s3CoreMapNorm1s t hmPay z) = s3RejPhaseNorm1s t hmPay z
    unfold s3RejPhaseNorm1s; simp [hz, hz']
  · have hmap : s3CoreMapNorm1s t hmPay z = z := by unfold s3CoreMapNorm1s; rw [s3IteNeg hz]
    change s3RejPhaseNorm1s t hmPay (s3CoreMapNorm1s t hmPay z) = s3RejPhaseNorm1s t hmPay z
    rw [hmap]

theorem s3RejPhaseNorm1s_sq (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) :
    s3RejPhaseNorm1s t hmPay z * s3RejPhaseNorm1s t hmPay z = 1 := by
  unfold s3RejPhaseNorm1s
  split_ifs <;> norm_num

/-- Real signed-involution unitary `s3SwapRejUnitaryNorm1s` (`Stage C` of core SELECT). -/
noncomputable def s3SwapRejUnitaryNorm1s (t : Norm1sTier) {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) : Unitary (2 ^ (momCoreWires mPayload)) := signedInvolutionUnitary
    (s3CorePermNorm1s t hmPay) (s3RejPhaseNorm1s t hmPay)
    (fun z ↦ (s3AcceptNorm1s_and_involutive t hmPay z).2.1) (s3RejPhaseNorm1s_symm t hmPay)
    (s3RejPhaseNorm1s_sq t hmPay)

/-- Unsigned 48-bit catalyst modular shift `s3Shift48_36 t cfg hmPay` at `Bk = 36`
(`trunc36Cfg cfg` in `nearestProtonCoord 42`, equivalent to `64 * nuclearM36 cfg l w`). -/
noncomputable def s3Shift48_36 (t : Norm1sTier) {mPayload : ℕ} (cfg :
    SpecsAux.SpecMirror.Configuration)
    (hmPay : 80 ≤ mPayload) (γ : BitAssignment (momCoreWires mPayload)) : ℕ :=
  let z := (basisBitsEquiv (momCoreWires mPayload)).symm γ
  if s3AcceptNorm1s t hmPay z = true then
    let z' := s3CoreMapNorm1s t hmPay z
    let ySys := (momSysReg mPayload).extractIndex z
    let xSys := (momSysReg mPayload).extractIndex z'
    let Δ := twosMomentum xSys .projectile - twosMomentum ySys .projectile
    let l := s3NucleusIdx216 hmPay z
    let kInt : ℤ := -∑ w : Fin 3, Δ w * nearestProtonCoord 42
        (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ((trunc36Cfg cfg).nuclei l w)
    64 * (kInt.emod (2 ^ 42 : ℤ)).toNat
  else 0

theorem s3Shift48_36_eq_nuclearM36 (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (momCoreWires mPayload)) :
    let z := (basisBitsEquiv (momCoreWires mPayload)).symm γ
    s3Shift48_36 t cfg hmPay γ =
      if s3AcceptNorm1s t hmPay z = true then
        let z' := s3CoreMapNorm1s t hmPay z
        let Δ := twosMomentum ((momSysReg mPayload).extractIndex z') .projectile -
          twosMomentum ((momSysReg mPayload).extractIndex z) .projectile
        let l := s3NucleusIdx216 hmPay z
        4096 * ((-∑ w : Fin 3, Δ w * (nuclearM36 cfg l w : ℤ)).emod (2 ^ 36 : ℤ)).toNat
      else 0 := by
  intro z
  unfold s3Shift48_36
  dsimp only
  by_cases hz : s3AcceptNorm1s t hmPay z = true
  · rw [s3ItePos hz, s3ItePos hz]
    set Δ :=
      twosMomentum ((momSysReg mPayload).extractIndex (s3CoreMapNorm1s t hmPay z)) .projectile -
      twosMomentum ((momSysReg mPayload).extractIndex z) .projectile
    set l := s3NucleusIdx216 hmPay z
    have hsum : (-∑ w : Fin 3, Δ w * nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3
        : ℝ)) ((trunc36Cfg cfg).nuclei l w)) = 64 *
        (-∑ w : Fin 3, Δ w * (nuclearM36 cfg l w : ℤ)) := by
      simp_rw [nearestProtonCoord_42_trunc36Cfg cfg l]
      simp only [Fin.sum_univ_three]
      ring
    rw [hsum, int_mul64_emod_two_pow42_toNat]
    omega
  · rw [s3IteNeg hz, s3IteNeg hz]

theorem s3DyadicTurn_shift48_36_eq (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : dyadicTurn 48
    (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) z) : ℤ) = if s3AcceptNorm1s t
    hmPay z = true then Complex.exp ((thetaProtonNearest 36 cfg (s3NucleusIdx216 hmPay z)
    (twosMomentum ((momSysReg mPayload).extractIndex (s3CoreMapNorm1s t hmPay z)) .projectile
    - twosMomentum ((momSysReg mPayload).extractIndex z) .projectile) : ℂ) * Complex.I) else 1
    := by
  unfold s3Shift48_36
  dsimp only
  rw [symm_basisBits_apply z]
  by_cases hz : s3AcceptNorm1s t hmPay z = true
  · rw [s3ItePos hz, s3ItePos hz, ← exp_thetaProtonNearest_42_trunc36Cfg]
    set Δ :=
      twosMomentum ((momSysReg mPayload).extractIndex (s3CoreMapNorm1s t hmPay z)) .projectile -
      twosMomentum ((momSysReg mPayload).extractIndex z) .projectile
    set l := s3NucleusIdx216 hmPay z
    set kInt : ℤ := -∑ w : Fin 3,
      Δ w * nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
        ((trunc36Cfg cfg).nuclei l w)
    have hmod_nn : 0 ≤ kInt.emod (2 ^ 42 : ℤ) := Int.emod_nonneg kInt (by positivity)
    have hcast : ((64 * (kInt.emod (2 ^ 42 : ℤ)).toNat : ℕ) : ℤ) =
        64 * (kInt.emod (2 ^ 42 : ℤ)) := by
      push_cast
      exact congrArg (64 * ·) (Int.toNat_of_nonneg hmod_nn)
    have heq48 : (((64 * (kInt.emod (2 ^ 42 : ℤ)).toNat : ℕ) : ℤ)).emod (2 ^ 48 : ℤ) =
        (64 * kInt).emod (2 ^ 48 : ℤ) := by
      rw [hcast]
      have hd : kInt % (2 ^ 42 : ℤ) + (2 ^ 42 : ℤ) * (kInt / (2 ^ 42 : ℤ)) = kInt :=
        Int.emod_add_mul_ediv kInt (2 ^ 42 : ℤ)
      have hm : 64 * kInt = 64 * (kInt % (2 ^ 42 : ℤ)) + (kInt / (2 ^ 42 : ℤ)) * (2 ^ 48 : ℤ) :=
        calc 64 * kInt = 64 * (kInt % (2 ^ 42 : ℤ) + (2 ^ 42 : ℤ) * (kInt / (2 ^ 42 : ℤ))) :=
              congrArg (64 * ·) hd.symm
          _ = 64 * (kInt % (2 ^ 42 : ℤ)) + (kInt / (2 ^ 42 : ℤ)) * (2 ^ 48 : ℤ) := by ring
      change (64 * (kInt % (2 ^ 42 : ℤ))) % (2 ^ 48 : ℤ) = (64 * kInt) % (2 ^ 48 : ℤ)
      conv_rhs => rw [hm, Int.add_mul_emod_self_right]
    rw [dyadicTurn_eq_of_emod_eq 48 heq48]
    unfold dyadicTurn thetaProtonNearest
    congr 1
    dsimp only [kInt]
    simp only [Fin.sum_univ_three]
    have hne48 : ((2 : ℂ) ^ 48) ≠ 0 := pow_ne_zero 48 (by norm_num)
    have hne42 : ((2 : ℂ) ^ 42) ≠ 0 := pow_ne_zero 42 (by norm_num)
    push_cast
    field_simp [hne48, hne42]
    ring
  · rw [s3IteNeg hz, s3IteNeg hz]
    simp [dyadicTurn]

/-- Effective diagonal kick unitary on `momCoreWires mPayload` at `Bk = 36` for `(t :
  Norm1sTier)`. -/
noncomputable def s3KickEffUnitaryNorm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (momCoreWires mPayload)) :=
  dyadicDiagUnitary (momCoreWires mPayload) 48 (fun γ ↦ (s3Shift48_36 t cfg hmPay γ : ℤ))

/-- Core effective unitary `uCore3EffNorm1s t cfg hmPay := s3SwapRejUnitaryNorm1s *
  s3KickEffUnitaryNorm1s`. -/
noncomputable def uCore3EffNorm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (momCoreWires mPayload)) :=
  s3SwapRejUnitaryNorm1s t hmPay * s3KickEffUnitaryNorm1s t cfg hmPay

/-- Core catalyst unitary `uCore3CatNorm1s t cfg hmPay` on `momCoreWires mPayload + 48`. -/
noncomputable def uCore3CatNorm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (momCoreWires mPayload + 48)) :=
  let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
    .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
  rCore0.embedUnitary (s3SwapRejUnitaryNorm1s t hmPay) *
    catModAddUnitary (momCoreWires mPayload) 48 (s3Shift48_36 t cfg hmPay)

theorem s3Qreg_ext {m n : ℕ} {r1 r2 : QRegister m n} (h : ∀ i : Fin m, r1 i = r2 i) :
    r1 = r2 := by
  cases r1; cases r2; congr 1; apply Function.Embedding.ext; exact h

theorem uCore3EffNorm1s_entry (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (i j : Fin (2 ^ (momCoreWires mPayload))) : (uCore3EffNorm1s t cfg hmPay).1 i j = if i =
    s3CoreMapNorm1s t hmPay j then ((s3RejPhaseNorm1s t hmPay j : ℝ) : ℂ) * dyadicTurn 48
    (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) j) : ℤ) else 0 := by
  change ((s3SwapRejUnitaryNorm1s t hmPay).1 * (s3KickEffUnitaryNorm1s t cfg hmPay).1) i j = _
  unfold s3KickEffUnitaryNorm1s dyadicDiagUnitary
  dsimp only
  rw [Matrix.mul_diagonal]
  change signedPermMatrix (s3CorePermNorm1s t hmPay) (s3RejPhaseNorm1s t hmPay) i j *
      dyadicTurn 48 (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) j) : ℤ) = _
  rw [signedPermMatrix_apply]
  change (if s3CoreMapNorm1s t hmPay j = i then ((s3RejPhaseNorm1s t hmPay i : ℝ) : ℂ) else 0) * _ =
    _
  by_cases hij : i = s3CoreMapNorm1s t hmPay j
  · subst hij
    rw [s3ItePos rfl, s3ItePos rfl]
    exact congrArg (fun r : ℝ ↦ (r : ℂ) * _) (s3RejPhaseNorm1s_symm t hmPay j)
  · have hne : s3CoreMapNorm1s t hmPay j ≠ i := Ne.symm hij
    rw [s3IteNeg hne, s3IteNeg hij, zero_mul]

theorem uCore3EffNorm1s_sa (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    (uCore3EffNorm1s t cfg hmPay).1ᴴ = (uCore3EffNorm1s t cfg hmPay).1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, uCore3EffNorm1s_entry, uCore3EffNorm1s_entry]
  have hinv_iff : j = s3CoreMapNorm1s t hmPay i ↔ i = s3CoreMapNorm1s t hmPay j := by
    constructor
    · rintro rfl; exact ((s3AcceptNorm1s_and_involutive t hmPay i).2.1).symm
    · rintro rfl; exact ((s3AcceptNorm1s_and_involutive t hmPay j).2.1).symm
  by_cases hij : i = s3CoreMapNorm1s t hmPay j
  · suffices hTurn :
        (starRingEnd ℂ) (dyadicTurn 48 (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload)
          i))) =
          dyadicTurn 48 (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) j)) by
      rw [s3ItePos (hinv_iff.mpr hij), s3ItePos hij, RCLike.star_def, map_mul,
        Complex.conj_ofReal, hTurn, show s3RejPhaseNorm1s t hmPay i = s3RejPhaseNorm1s t hmPay j by
          rw [hij]; exact s3RejPhaseNorm1s_symm t hmPay j]
    rw [s3DyadicTurn_shift48_36_eq, s3DyadicTurn_shift48_36_eq]
    by_cases hjAcc : s3AcceptNorm1s t hmPay j = true
    · have hiAcc : s3AcceptNorm1s t hmPay i = true := by
        rw [hij]; exact ((s3AcceptNorm1s_and_involutive t hmPay j).1).trans hjAcc
      rw [s3ItePos hiAcc, s3ItePos hjAcc, ← Complex.exp_conj]
      refine congrArg Complex.exp ?_
      have hl : s3NucleusIdx216 hmPay i = s3NucleusIdx216 hmPay j := by
        rw [hij]; exact (s3AcceptNorm1s_and_involutive t hmPay j).2.2
      have hij' : s3CoreMapNorm1s t hmPay i = j := by
        rw [hij]; exact (s3AcceptNorm1s_and_involutive t hmPay j).2.1
      rw [hl, hij', ← hij]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
      have hSubNeg : thetaProtonNearest 36 cfg (s3NucleusIdx216 hmPay j) (twosMomentum
          ((momSysReg mPayload).extractIndex j) .projectile - twosMomentum ((momSysReg
          mPayload).extractIndex i) .projectile) = -thetaProtonNearest 36 cfg
          (s3NucleusIdx216 hmPay j) (twosMomentum ((momSysReg mPayload).extractIndex i)
          .projectile - twosMomentum ((momSysReg mPayload).extractIndex j) .projectile) := by
        unfold thetaProtonNearest
        simp only [Pi.sub_apply]
        push_cast
        rw [← mul_neg, ← Finset.sum_neg_distrib]
        refine congrArg _ (Finset.sum_congr rfl fun w _ ↦ ?_)
        ring
      rw [hSubNeg]
      push_cast
      ring
    · have hiAcc : ¬(s3AcceptNorm1s t hmPay i = true) := by
        rw [hij, (s3AcceptNorm1s_and_involutive t hmPay j).1]; exact hjAcc
      rw [s3IteNeg hiAcc, s3IteNeg hjAcc, map_one]
  · rw [s3IteNeg (fun h ↦ hij (hinv_iff.mp h)), s3IteNeg hij, star_zero]

theorem uCore3EffNorm1s_offCoin6 (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    (uCore3EffNorm1s t cfg hmPay).1 * (1 - momCoinProj mPayload (fullSysCoinIdx 3)) =
      1 - momCoinProj mPayload (fullSysCoinIdx 3) := by
  have hc6 : fullSysCoinIdx 3 = (6 : Fin 8) := rfl
  rw [hc6, momCoinProj_eq_diagonal mPayload 6]
  set d := fun x : Fin (2 ^ (momCoreWires mPayload)) ↦
    ((if (basisBits (momCoreWires mPayload) x (iSlot0Mom mPayload)).val = (coinBitFin2 6 0).val
        then (1 : ℂ) else 0) *
      if (basisBits (momCoreWires mPayload) x (iSlot1Mom mPayload)).val = (coinBitFin2 6 1).val
        then (1 : ℂ) else 0) *
    if (basisBits (momCoreWires mPayload) x (iSlot2Mom mPayload)).val = (coinBitFin2 6 2).val
      then (1 : ℂ) else 0
  have h1sub : (1 : Operator (2 ^ (momCoreWires mPayload))) - Matrix.diagonal d =
      Matrix.diagonal (fun x ↦ 1 - d x) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, h]
  rw [h1sub]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases hd : 1 - d j = 0
  · rw [hd, mul_zero]
    by_cases hij : i = j
    · subst hij; rw [s3ItePos rfl, hd]
    · exact (s3IteNeg hij).symm
  · have hne6 : ((momCoinReg mPayload).extractIndex j).val ≠ 6 := by
      intro hv
      have heq6 : (momCoinReg mPayload).extractIndex j = (6 : Fin 8) := Fin.ext hv
      have hb0 : basisBits (momCoreWires mPayload) j (iSlot0Mom mPayload) = 0 := by
        have h := QRegister.basisBits_extractIndex (momCoinReg mPayload) j 0
        rw [heq6] at h
        exact h.symm
      have hb1 : basisBits (momCoreWires mPayload) j (iSlot1Mom mPayload) = 1 := by
        have h := QRegister.basisBits_extractIndex (momCoinReg mPayload) j 1
        rw [heq6] at h
        exact h.symm
      have hb2 : basisBits (momCoreWires mPayload) j (iSlot2Mom mPayload) = 1 := by
        have h := QRegister.basisBits_extractIndex (momCoinReg mPayload) j 2
        rw [heq6] at h
        exact h.symm
      have hv0 : (basisBits (momCoreWires mPayload) j (iSlot0Mom mPayload)).val =
          (coinBitFin2 6 0).val := by rw [hb0]; decide
      have hv1 : (basisBits (momCoreWires mPayload) j (iSlot1Mom mPayload)).val =
          (coinBitFin2 6 1).val := by rw [hb1]; decide
      have hv2 : (basisBits (momCoreWires mPayload) j (iSlot2Mom mPayload)).val =
          (coinBitFin2 6 2).val := by rw [hb2]; decide
      exact hd (by
        dsimp only [d]; rw [hv0, hv1, hv2, s3ItePos rfl, s3ItePos rfl, s3ItePos rfl]; norm_num)
    have hzFalse : s3AcceptNorm1s t hmPay j = false := by
      unfold s3AcceptNorm1s; simp [hne6]
    have hmap : s3CoreMapNorm1s t hmPay j = j := by
      unfold s3CoreMapNorm1s; rw [s3IteNeg (by simp [hzFalse])]
    have hrej1 : s3RejPhaseNorm1s t hmPay j = 1 := by
      unfold s3RejPhaseNorm1s; simp [hzFalse, hne6]
    have hturn1 : dyadicTurn 48 (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) j) : ℤ)
      = 1 := by
      rw [s3DyadicTurn_shift48_36_eq, s3IteNeg (by simp [hzFalse])]
    rw [uCore3EffNorm1s_entry, hmap, hrej1, hturn1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

/-- Prep-conjugated Slot-3 effective unitary `uSlot3EffNorm1s t cfg hmPay` on `momCoreWires
  mPayload`. -/
noncomputable def uSlot3EffNorm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (momCoreWires mPayload)) :=
  unitaryConj (uPrep3_216 hmPay) (uCore3EffNorm1s t cfg hmPay)

/-- Prep-conjugated Slot-3 catalyst unitary `uSlot3CatNorm1s t cfg hmPay` on `momCoreWires
  mPayload + 48`. -/
noncomputable def uSlot3CatNorm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (momCoreWires mPayload + 48)) :=
  let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
    .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
  unitaryConj (rCore0.embedUnitary (uPrep3_216 hmPay)) (uCore3CatNorm1s t cfg hmPay)

theorem uSlot3EffNorm1s_sa (t : Norm1sTier) {mPayload : ℕ} (cfg : SpecsAux.SpecMirror.Configuration)
    (hmPay : 80 ≤ mPayload) : (uSlot3EffNorm1s t cfg hmPay).1ᴴ =
    (uSlot3EffNorm1s t cfg hmPay).1 := (unitaryConj_sa_and_offProj (uPrep3_216 hmPay)
    (uCore3EffNorm1s t cfg hmPay) (uPrep3_216_comm_momCoinProj hmPay (fullSysCoinIdx 3))
    (uCore3EffNorm1s_sa t cfg hmPay) (uCore3EffNorm1s_offCoin6 t cfg hmPay)).1

theorem uSlot3EffNorm1s_offCoin6 (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    (uSlot3EffNorm1s t cfg hmPay).1 * (1 - momCoinProj mPayload (fullSysCoinIdx 3)) = 1 -
    momCoinProj mPayload (fullSysCoinIdx 3) := (unitaryConj_sa_and_offProj (uPrep3_216 hmPay)
    (uCore3EffNorm1s t cfg hmPay) (uPrep3_216_comm_momCoinProj hmPay (fullSysCoinIdx 3))
    (uCore3EffNorm1s_sa t cfg hmPay) (uCore3EffNorm1s_offCoin6 t cfg hmPay)).2

private theorem s3Block_concat_whole {n a : ℕ} (h1 : 0 + n ≤ n + a) (h2 : n + a ≤ n + a)
    (hdisj : (QRegister.block 0 n h1).DisjointWires (QRegister.block n a h2)) :
    (QRegister.block 0 n h1).concat (QRegister.block n a h2) hdisj = QRegister.whole (n + a) := by
  apply s3Qreg_ext
  intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · apply Fin.ext; rw [QRegister.concat_apply_left]; simp
  · apply Fin.ext; rw [QRegister.concat_apply_right]; simp

theorem uSlot3CatNorm1s_intertwines (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (U_catTwist : Unitary (2 ^ 48))
    (hcol : ∀ m : Fin (2 ^ 48), U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) :
    IntertwinesMomCat U_catTwist (uSlot3CatNorm1s t cfg hmPay) (uSlot3EffNorm1s t cfg hmPay) := by
  let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
    .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
  let rCat0 : QRegister 48 (momCoreWires mPayload + 48) := .block (momCoreWires mPayload) 48 le_rfl
  have hdisj : rCore0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 (momCoreWires mPayload) (momCoreWires mPayload) 48
      (mom_zero_add_le _ 48) le_rfl (mom_zero_add_le_self _)
  have hConcatId : rCore0.concat rCat0 hdisj = QRegister.whole (momCoreWires mPayload + 48) :=
    s3Block_concat_whole _ _ hdisj
  have hWholeEmbed : ∀ (U : Unitary (2 ^ (momCoreWires mPayload + 48))),
      (QRegister.whole (momCoreWires mPayload + 48)).embedUnitary U = U :=
    QRegister.whole_embedUnitary
  have hColKet : U_catTwist.1.mulVec (Pi.single 0 1) = phaseGradKet 48 := by
    funext m
    rw [Matrix.mulVec_single_one, Matrix.col_apply, hcol m]
    unfold PhaseGradCatalystCore.phaseGradientState phaseGradKet
      PhaseGradCatalystCore.instHPowComplexRealCompat
    rfl
  have hKick : PhaseGradCatalystCore.IntertwinesCat
      (rCat0.embedUnitary U_catTwist).1 (rCat0.basisOutcomeProjector 0)
      (catModAddUnitary (momCoreWires mPayload) 48 (s3Shift48_36 t cfg hmPay)).1
      (rCore0.embedUnitary (s3KickEffUnitaryNorm1s t cfg hmPay)).1 := by
    have h0 := catModAddUnitary_intertwinesCat rCore0 rCat0 hdisj U_catTwist hColKet
      (s3Shift48_36 t cfg hmPay)
    rw [hConcatId] at h0
    rw [hWholeEmbed] at h0
    exact h0
  have hSwap : PhaseGradCatalystCore.IntertwinesCat (rCat0.embedUnitary U_catTwist).1
      (rCat0.basisOutcomeProjector 0) (rCore0.embedUnitary (s3SwapRejUnitaryNorm1s t hmPay)).1
      (rCore0.embedUnitary (s3SwapRejUnitaryNorm1s t hmPay)).1 :=
      intertwinesMomCat_of_coreOnly U_catTwist (s3SwapRejUnitaryNorm1s t hmPay)
  have hPrep : PhaseGradCatalystCore.IntertwinesCat (rCat0.embedUnitary U_catTwist).1
      (rCat0.basisOutcomeProjector 0) (rCore0.embedUnitary (uPrep3_216 hmPay)).1
      (rCore0.embedUnitary (uPrep3_216 hmPay)).1 := intertwinesMomCat_of_coreOnly U_catTwist
      (uPrep3_216 hmPay)
  have hPrepInv : PhaseGradCatalystCore.IntertwinesCat (rCat0.embedUnitary U_catTwist).1
      (rCat0.basisOutcomeProjector 0) (rCore0.embedUnitary (uPrep3_216 hmPay)⁻¹).1
      (rCore0.embedUnitary (uPrep3_216 hmPay)⁻¹).1 := intertwinesMomCat_of_coreOnly U_catTwist
      (uPrep3_216 hmPay)⁻¹
  have hAll := s3IntertwinesCat_mul _ _ hPrepInv
    (s3IntertwinesCat_mul _ _ hSwap (s3IntertwinesCat_mul _ _ hKick hPrep))
  have hCatEq : (uSlot3CatNorm1s t cfg hmPay).1 = (rCore0.embedUnitary (uPrep3_216 hmPay)⁻¹).1
      * ((rCore0.embedUnitary (s3SwapRejUnitaryNorm1s t hmPay)).1 * ((catModAddUnitary
      (momCoreWires mPayload) 48 (s3Shift48_36 t cfg hmPay)).1 * (rCore0.embedUnitary
      (uPrep3_216 hmPay)).1)) := by
    have hInv : (rCore0.embedUnitary (uPrep3_216 hmPay)⁻¹).1 =
        (rCore0.embedUnitary (uPrep3_216 hmPay)).1ᴴ := by
      change rCore0.embedMatrix ((uPrep3_216 hmPay)⁻¹).1 =
        (rCore0.embedMatrix (uPrep3_216 hmPay).1)ᴴ
      rw [s3Unitary_inv_val, QRegister.embedMatrix_conjTranspose]
    rw [hInv]
    unfold uSlot3CatNorm1s uCore3CatNorm1s
    dsimp only [rCore0]
    rw [unitaryConj_val]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have hEffEq : (rCore0.embedUnitary (uSlot3EffNorm1s t cfg hmPay)).1 =
      (rCore0.embedUnitary (uPrep3_216 hmPay)⁻¹).1 * ((rCore0.embedUnitary
      (s3SwapRejUnitaryNorm1s t hmPay)).1 * ((rCore0.embedUnitary (s3KickEffUnitaryNorm1s t
      cfg hmPay)).1 * (rCore0.embedUnitary (uPrep3_216 hmPay)).1)) := by
    have hConj : (uSlot3EffNorm1s t cfg hmPay).1 = ((uPrep3_216 hmPay)⁻¹).1 *
        ((s3SwapRejUnitaryNorm1s t hmPay).1 * ((s3KickEffUnitaryNorm1s t cfg hmPay).1 *
        (uPrep3_216 hmPay).1)) := by
      unfold uSlot3EffNorm1s uCore3EffNorm1s
      rw [unitaryConj_val, s3Unitary_inv_val]
      simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    change rCore0.embedMatrix (uSlot3EffNorm1s t cfg hmPay).1 = _
    rw [hConj, rCore0.embedMatrix_mul, rCore0.embedMatrix_mul, rCore0.embedMatrix_mul]
    rfl
  rwa [← hCatEq, ← hEffEq] at hAll

theorem s3Qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i =
      ⟨offset + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt offset) h⟩ := rfl

theorem s3Qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤
    n) (i : Fin width) :
    (QRegister.block offset width h).wires i =
      ⟨offset + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt offset) h⟩ := rfl

theorem s3Qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) : (r.slice offset width h).wires i = r.wires
    ⟨offset + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt offset) h⟩ := rfl

theorem s3Qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m)
    :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl

theorem s3Qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl

theorem s3Emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl

theorem s3Emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl

theorem s3Emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl

private theorem s3Sel149_core_fields_eq {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (β : BitAssignment (momCoreWires mPayload + 48)) :
    let γ : BitAssignment (momCoreWires mPayload) :=
      fun q ↦ β ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ 48)⟩
    let α : BitAssignment 149 := fun k ↦ β (sel149 hmPay k)
    let zM := (basisBitsEquiv (momCoreWires mPayload)).symm γ
    let z80c := (basisBitsEquiv (momCoreWires 80)).symm (embedAlphaCore80 α)
    (momCoinReg mPayload).extractIndex zM = (momCoinReg 80).extractIndex z80c ∧
      (∀ w : Fin 3,
        projAxisField ((momSysReg mPayload).extractIndex zM) w =
          projAxisField ((momSysReg 80).extractIndex z80c) w) ∧
      (s3U22Core hmPay).extractIndex zM = (s3U22Core hmPay80).extractIndex z80c ∧
      (s3S3Core hmPay).extractIndex zM = (s3S3Core hmPay80).extractIndex z80c ∧
      (s3C8Core hmPay).extractIndex zM = (s3C8Core hmPay80).extractIndex z80c ∧
      (s3Fine30Core hmPay).extractIndex zM = (s3Fine30Core hmPay80).extractIndex z80c ∧
      (s3U16Core hmPay).extractIndex zM = (s3U16Core hmPay80).extractIndex z80c ∧
      basisBits (momCoreWires mPayload) zM (s3BParCore hmPay) =
        basisBits (momCoreWires 80) z80c (s3BParCore hmPay80) := by
  intro γ α zM z80c
  have hbb : ∀ {n : ℕ} (δ : BitAssignment n), basisBits n ((basisBitsEquiv n).symm δ) = δ :=
    fun δ ↦ (basisBitsEquiv _).apply_symm_apply δ
  have hext_eq : ∀ {q : ℕ} (rM : QRegister q (momCoreWires mPayload))
      (r80 : QRegister q (momCoreWires 80)),
      (∀ b : Fin q, γ (rM b) = embedAlphaCore80 α (r80 b)) →
      rM.extractIndex zM = r80.extractIndex z80c := by
    intro q rM r80 hEq
    apply (basisBitsEquiv q).injective
    funext b
    change basisBits q _ b = basisBits q _ b
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hbb, hbb]
    exact hEq b
  have hPay : ∀ {q off : ℕ} (_ : off + q ≤ 80)
      (hBM : (3954 + off) + q ≤ momCoreWires mPayload)
      (hB80 : (3954 + off) + q ≤ momCoreWires 80),
      (QRegister.block (3954 + off) q hBM).extractIndex zM =
        (QRegister.block (3954 + off) q hB80).extractIndex z80c := fun {q off} hoff hBM hB80 ↦
    hext_eq _ _ fun b ↦ by
      have hb := b.isLt
      have hvB80 : (QRegister.block (3954 + off) q hB80 b).val = 3954 + off + b.val := rfl
      have hsel : β (sel149 hmPay ⟨27 + (off + b.val), by omega⟩) =
          γ (QRegister.block (3954 + off) q hBM b) := by
        congr 1
        apply Fin.ext
        dsimp [sel149]
        split_ifs <;> omega
      unfold embedAlphaCore80
      rw [s3DiteNeg (by rw [hvB80]; omega), s3DiteNeg (by rw [hvB80]; omega),
        s3DitePos (by rw [hvB80]; omega)]
      have hk : (⟨27 + ((QRegister.block (3954 + off) q hB80 b).val - 3954), by
          rw [hvB80]; omega⟩ : Fin 149) = ⟨27 + (off + b.val), by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      rw [hk]
      simpa [α] using hsel.symm
  refine ⟨?_, ?_, hPay (off := 0) (by decide) _ _, hPay (off := 22) (by decide) _ _,
    hPay (off := 25) (by decide) _ _, hPay (off := 33) (by decide) _ _,
    hPay (off := 64) (by decide) _ _, ?_⟩
  · exact hext_eq _ _ fun b ↦ by
      have hb := b.isLt
      have hsel : β (sel149 hmPay ⟨24 + b.val, by omega⟩) = γ (momCoinReg mPayload b) := by
        congr 1
        apply Fin.ext
        dsimp [sel149]
        split_ifs <;> omega
      have hval80 : (momCoinReg 80 b).val = 3948 + b.val := rfl
      unfold embedAlphaCore80
      rw [s3DiteNeg (by rw [hval80]; omega), s3DitePos (by rw [hval80]; omega)]
      simpa [α] using hsel.symm
  · intro w
    apply (basisBitsEquiv 8).injective
    funext b
    change basisBits 8 ((proj3Axes w).extractIndex _) b =
      basisBits 8 ((proj3Axes w).extractIndex _) b
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hbb, hbb]
    have hw := w.isLt
    have hb := b.isLt
    have hidx : (proj3Axes w b).val = 3924 + 8 * w.val + b.val := by
      dsimp [proj3Axes, s3Qreg_block_apply, s3Qreg_block_wires_apply, s3Qreg_whole_wires,
        s3Emb_trans_apply, s3Emb_refl_apply, s3Emb_mk_apply,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits]
    have hsel : β (sel149 hmPay ⟨8 * w.val + b.val, by omega⟩) =
        γ (momSysReg mPayload (proj3Axes w b)) := by
      congr 1
      apply Fin.ext
      dsimp [sel149]
      rw [hidx]
      split_ifs <;> omega
    have hval80 : (momSysReg 80 (proj3Axes w b)).val = 3924 + 8 * w.val + b.val :=
      (Nat.zero_add _).trans hidx
    unfold embedAlphaCore80
    rw [s3DitePos (by rw [hval80]; omega)]
    refine hsel.symm.trans (congrArg α (Fin.ext ?_))
    dsimp
    rw [hidx]
    omega
  · rw [hbb, hbb]
    have hsel : β (sel149 hmPay ⟨90, by decide⟩) = γ (s3BParCore hmPay) := congrArg β (Fin.ext rfl)
    dsimp [embedAlphaCore80, s3BParCore]
    simpa [α, s3BParCore] using hsel.symm

theorem s3AcceptNorm1s_dep_only_on_sel149 (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (β : BitAssignment (momCoreWires mPayload + 48)) :
    let γ : BitAssignment (momCoreWires mPayload) :=
      fun q ↦ β ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ 48)⟩
    let α : BitAssignment 149 := fun k ↦ β (sel149 hmPay k)
    s3AcceptNorm1s t hmPay ((basisBitsEquiv (momCoreWires mPayload)).symm γ) =
      s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlphaCore80 α)) ∧
    s3Shift48_36 t cfg hmPay γ = s3Shift48_36 t cfg hmPay80 (embedAlphaCore80 α) := by
  intro γ α
  obtain ⟨hCoin, hProj, hU22, hS3, hC8, hF30, hU16, hBPar⟩ := s3Sel149_core_fields_eq hmPay β
  have hGrid : s3ProjGridBool ((momSysReg mPayload).extractIndex ((basisBitsEquiv _).symm γ)) =
      s3ProjGridBool ((momSysReg 80).extractIndex ((basisBitsEquiv _).symm (embedAlphaCore80 α))) :=
        by
    unfold s3ProjGridBool
    rw [hProj 0, hProj 1, hProj 2]
  have hAcc : s3AcceptNorm1s t hmPay ((basisBitsEquiv (momCoreWires mPayload)).symm γ) =
      s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlphaCore80 α)) := by
    unfold s3AcceptNorm1s
    dsimp only
    rw [hCoin, hU22, hS3, hC8, hF30, hGrid, hProj 0, hProj 1, hProj 2]
  refine ⟨hAcc, ?_⟩
  unfold s3Shift48_36
  dsimp only
  by_cases hz : s3AcceptNorm1s t hmPay ((basisBitsEquiv (momCoreWires mPayload)).symm γ) = true
  · have hz80 : s3AcceptNorm1s t hmPay80
        ((basisBitsEquiv (momCoreWires 80)).symm (embedAlphaCore80 α)) = true :=
      hAcc.symm.trans hz
    rw [s3ItePos hz, s3ItePos hz80]
    have hNuc : s3NucleusIdx216 hmPay ((basisBitsEquiv _).symm γ) =
        s3NucleusIdx216 hmPay80 ((basisBitsEquiv _).symm (embedAlphaCore80 α)) := by
      apply Fin.ext; unfold s3NucleusIdx216; dsimp only; rw [hU16, hBPar]
    rcases s3CoreMapNorm1s_fields hz with ⟨_, hSysM, _, _, _, _, _, _, _, _⟩
    rcases s3CoreMapNorm1s_fields hz80 with ⟨_, hSys80, _, _, _, _, _, _, _, _⟩
    rcases s3UpdateSysProj_fields ((momSysReg mPayload).extractIndex ((basisBitsEquiv _).symm γ))
      _ with ⟨_, hpM⟩
    rcases s3UpdateSysProj_fields ((momSysReg 80).extractIndex
      ((basisBitsEquiv _).symm (embedAlphaCore80 α))) _ with ⟨_, hp80⟩
    have hΔ : twosMomentum ((momSysReg mPayload).extractIndex (s3CoreMapNorm1s t hmPay
        ((basisBitsEquiv _).symm γ))) .projectile - twosMomentum
        ((momSysReg mPayload).extractIndex ((basisBitsEquiv _).symm γ)) .projectile =
        twosMomentum ((momSysReg 80).extractIndex (s3CoreMapNorm1s t hmPay80 ((basisBitsEquiv
        _).symm (embedAlphaCore80 α)))) .projectile - twosMomentum ((momSysReg
        80).extractIndex ((basisBitsEquiv _).symm (embedAlphaCore80 α))) .projectile := by
      ext w
      dsimp [twosMomentum]
      rw [hSysM, hSys80, hpM w, hp80 w, hProj w, hU22, hS3]
    rw [hNuc, hΔ]
  · have hz80 : ¬(s3AcceptNorm1s t hmPay80
        ((basisBitsEquiv (momCoreWires 80)).symm (embedAlphaCore80 α)) = true) := by
      rw [← hAcc]; exact hz
    rw [s3IteNeg hz, s3IteNeg hz80]

/-- Active `107`-wire involution map for `(t : Norm1sTier)` Slot-3 synthesis. -/
noncomputable def swapRejMap107Norm1s (t : Norm1sTier) (α : BitAssignment 107) : BitAssignment 107
    :=
  let z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α)
  let z80' := s3CoreMapNorm1s t hmPay80 z80
  fun k ↦ basisBits (momCoreWires 80) z80' (sel107_80 k)

private theorem sel107_80_sub0 {v : ℕ} (h : 3924 ≤ v ∧ v < 3948) :
    (sel107_80 ⟨v - 3924, by omega⟩).val = v := by
  have hv := sel107_80_val ⟨v - 3924, by omega⟩
  rw [s3ItePos (by dsimp; omega)] at hv; dsimp at hv; omega

private theorem sel107_80_sub1 {v : ℕ} (h : 3948 ≤ v ∧ v < 3951) :
    (sel107_80 ⟨24 + (v - 3948), by omega⟩).val = v := by
  have hv := sel107_80_val ⟨24 + (v - 3948), by omega⟩
  rw [s3IteNeg (by dsimp; omega), s3ItePos (by dsimp; omega)] at hv; dsimp at hv; omega

private theorem sel107_80_sub2 {v : ℕ} (h : 3954 ≤ v ∧ v < 4034) :
    (sel107_80 ⟨27 + (v - 3954), by omega⟩).val = v := by
  have hv := sel107_80_val ⟨27 + (v - 3954), by omega⟩
  rw [s3IteNeg (by dsimp; omega), s3IteNeg (by dsimp; omega)] at hv; dsimp at hv; omega

private theorem sel107_80_s3 {v : ℕ} (h : 3976 ≤ v ∧ v < 3979) :
    (sel107_80 ⟨49 + (v - 3976), by omega⟩).val = v := by
  have hv := sel107_80_val ⟨49 + (v - 3976), by omega⟩
  rw [s3IteNeg (by dsimp; omega), s3IteNeg (by dsimp; omega)] at hv; dsimp at hv; omega

private theorem sel107_hmPay_val {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (k : Fin 107) :
    (sel107 hmPay k).val = (sel107_80 k).val := by
  have hklt := k.isLt; have hv80 := sel107_80_val k
  dsimp [sel107, QRegister.slice, QRegister.slice_apply, s3Qreg_whole_wires,
    s3Emb_trans_apply, s3Emb_refl_apply, s3Emb_mk_apply, sel149,
    s3Qreg_slice_wires, s3Qreg_compose_wires, s3Qreg_block_wires_apply, s3Qreg_block_apply]
  split_ifs at hv80 ⊢ <;> omega

theorem embedAlpha107_swapRejMap107Norm1s (t : Norm1sTier) (α : BitAssignment 107) :
    embedAlpha107 (swapRejMap107Norm1s t α) = basisBits (momCoreWires 80) (s3CoreMapNorm1s t
    hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α))) := by
  set z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α)
  let g80 := basisBits (momCoreWires 80) (s3CoreMapNorm1s t hmPay80 z80)
  have hbb : basisBits (momCoreWires 80) z80 = embedAlpha107 α :=
    (basisBitsEquiv _).apply_symm_apply _
  funext q
  have hq_lt : q.val < 4034 := lt_of_lt_of_eq q.isLt (s3MomCoreWires_eq 80)
  by_cases h1 : 3924 ≤ q.val ∧ q.val < 3948
  · unfold embedAlpha107 embedAlphaCore80
    rw [s3DitePos h1]; dsimp only; rw [s3DitePos (by omega)]
    exact congrArg g80 (Fin.ext (sel107_80_sub0 h1))
  · by_cases h2 : 3948 ≤ q.val ∧ q.val < 3951
    · unfold embedAlpha107 embedAlphaCore80
      rw [s3DiteNeg h1, s3DitePos h2]; dsimp only; rw [s3DitePos (by omega)]
      exact congrArg g80 (Fin.ext (sel107_80_sub1 h2))
    · by_cases h3 : 3954 ≤ q.val ∧ q.val < 4034
      · unfold embedAlpha107 embedAlphaCore80
        rw [s3DiteNeg h1, s3DiteNeg h2, s3DitePos h3]; dsimp only; rw [s3DitePos (by omega)]
        exact congrArg g80 (Fin.ext (sel107_80_sub2 h3))
      · dsimp [embedAlpha107, embedAlphaCore80]
        rw [s3DiteNeg h1, s3DiteNeg h2, s3DiteNeg h3]
        have h0 : basisBits (momCoreWires 80) z80 q = 0 := by
          rw [hbb]; dsimp [embedAlpha107, embedAlphaCore80]
          rw [s3DiteNeg h1, s3DiteNeg h2, s3DiteNeg h3]
        by_cases hz : s3AcceptNorm1s t hmPay80 z80 = true
        · by_cases hltSys : q.val < 3924
          · rcases s3CoreMapNorm1s_fields hz with ⟨_, hSys, _, _, _, _, _, _, _, _⟩
            let pNewFn : Fin 3 → Fin 256 := fun w ↦ (s3ProjStepHw (projAxisField ((momSysReg
                80).extractIndex z80) w) (shellMagCoord3 ((s3U22Core hmPay80).extractIndex
                z80) w) (signBit3 ((s3S3Core hmPay80).extractIndex z80) w)).1
            have hb_z' :=
              QRegister.basisBits_extractIndex (momSysReg 80) (s3CoreMapNorm1s t hmPay80 z80)
              ⟨q.val, lt_trans hltSys (by decide)⟩
            have hb_z := QRegister.basisBits_extractIndex (momSysReg 80) z80
              ⟨q.val, lt_trans hltSys (by decide)⟩
            have hqEq : momSysReg 80 ⟨q.val, lt_trans hltSys (by decide)⟩ = q :=
              Fin.ext (Nat.zero_add q.val)
            rw [hqEq] at hb_z' hb_z
            rw [← hb_z', hSys]
            have hbitsU : basisBits SpecsAux.SpecMirror.systemQubits
                (s3UpdateSysProj ((momSysReg 80).extractIndex z80) pNewFn)
                ⟨q.val, lt_trans hltSys (by decide)⟩ = basisBits SpecsAux.SpecMirror.systemQubits
                ((momSysReg 80).extractIndex z80) ⟨q.val, lt_trans hltSys (by decide)⟩ := by
              unfold s3UpdateSysProj
              rw [congrFun (basisBits_symm _) _, s3DitePos hltSys]
            rw [hbitsU, hb_z, h0]
          · rcases s3CoreMapNorm1s_fields hz with ⟨_, _, _, _, _, _, _, _, _, hMid⟩
            rw [hMid q (by omega) (by omega), h0]
        · have hmap : s3CoreMapNorm1s t hmPay80 z80 = z80 := by
            unfold s3CoreMapNorm1s; rw [s3IteNeg hz]
          rw [hmap, h0]

theorem swapRejMap107Norm1s_involutive (t : Norm1sTier) (α : BitAssignment 107) :
    swapRejMap107Norm1s t (swapRejMap107Norm1s t α) = α := by
  funext k
  change basisBits (momCoreWires 80) (s3CoreMapNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires
    80)).symm (embedAlpha107 (swapRejMap107Norm1s t α)))) (sel107_80 k) = α k
  rw [embedAlpha107_swapRejMap107Norm1s t α, symm_basisBits,
    (s3AcceptNorm1s_and_involutive t hmPay80 _).2.1,
    basisBits_symm, embedAlpha107_sel107_80]

/-- Active `107`-wire permutation on `Fin (2 ^ 107)` for `(t : Norm1sTier)` Slot-3 synthesis. -/
noncomputable def swapRejPerm107Norm1s (t : Norm1sTier) : Equiv.Perm (Fin (2 ^ 107)) where
  toFun idx := (basisBitsEquiv 107).symm (swapRejMap107Norm1s t (basisBits 107 idx))
  invFun idx := (basisBitsEquiv 107).symm (swapRejMap107Norm1s t (basisBits 107 idx))
  left_inv idx := by
    change (basisBitsEquiv 107).symm (swapRejMap107Norm1s t (basisBits 107 _)) = idx
    rw [basisBits_symm, swapRejMap107Norm1s_involutive]
    exact (basisBitsEquiv 107).symm_apply_apply idx
  right_inv idx := by
    change (basisBitsEquiv 107).symm (swapRejMap107Norm1s t (basisBits 107 _)) = idx
    rw [basisBits_symm, swapRejMap107Norm1s_involutive]
    exact (basisBitsEquiv 107).symm_apply_apply idx

/-- Active `107`-wire rejection sign phase on `Fin (2 ^ 107)` for `(t : Norm1sTier)`. -/
noncomputable def swapRejPhase107Norm1s (t : Norm1sTier) (idx : Fin (2 ^ 107)) : ℝ :=
  s3RejPhaseNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 (basisBits 107
    idx)))

theorem swapRejPhase107Norm1s_symm (t : Norm1sTier) (idx : Fin (2 ^ 107)) :
    swapRejPhase107Norm1s t (swapRejPerm107Norm1s t idx) = swapRejPhase107Norm1s t idx := by
  change s3RejPhaseNorm1s t hmPay80 ((basisBitsEquiv _).symm
      (embedAlpha107 (basisBits 107 ((basisBitsEquiv 107).symm (swapRejMap107Norm1s t (basisBits 107
        idx)))))) = _
  rw [basisBits_symm, embedAlpha107_swapRejMap107Norm1s, symm_basisBits]
  exact s3RejPhaseNorm1s_symm t hmPay80 _

theorem swapRejPhase107Norm1s_sq (t : Norm1sTier) (idx : Fin (2 ^ 107)) :
    swapRejPhase107Norm1s t idx * swapRejPhase107Norm1s t idx = 1 :=
  s3RejPhaseNorm1s_sq t hmPay80 _

/-- Active `107`-wire signed involution unitary for `(t : Norm1sTier)` Slot-3 synthesis. -/
noncomputable def uSwapRej107Norm1s (t : Norm1sTier) : Unitary (2 ^ 107) :=
    signedInvolutionUnitary (swapRejPerm107Norm1s t) (swapRejPhase107Norm1s t)
    (fun idx ↦ (swapRejPerm107Norm1s t).left_inv idx) (swapRejPhase107Norm1s_symm t)
    (swapRejPhase107Norm1s_sq t)

/-- Active `42`-bit catalyst modular-addition shift on `107` core wires at `Bk = 36` for `(t :
  Norm1sTier)`. -/
noncomputable def s3Shift42Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α107 : BitAssignment 107) : ℕ := s3Shift48_36 t cfg hmPay80 (embedAlpha107 α107) / 64

theorem s3Shift42Norm1s_eq_nuclearM36 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α107 : BitAssignment 107) :
    let z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
    s3Shift42Norm1s t cfg α107 =
      if s3AcceptNorm1s t hmPay80 z80 = true then
        let z80' := s3CoreMapNorm1s t hmPay80 z80
        let Δ := twosMomentum ((momSysReg 80).extractIndex z80') .projectile -
          twosMomentum ((momSysReg 80).extractIndex z80) .projectile
        let l := s3NucleusIdx216 hmPay80 z80
        64 * ((-∑ w : Fin 3, Δ w * (nuclearM36 cfg l w : ℤ)).emod (2 ^ 36 : ℤ)).toNat
      else 0 := by
  intro z80
  unfold s3Shift42Norm1s
  rw [s3Shift48_36_eq_nuclearM36 t cfg hmPay80 (embedAlpha107 α107)]
  dsimp only [z80]
  split_ifs <;> omega

private theorem embedAlphaCore80_sel149_eq {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (β : BitAssignment (momCoreWires mPayload + 48)) :
    embedAlphaCore80 (fun k ↦ β (sel149 hmPay k)) =
      embedAlpha107 (fun k ↦ β (sel107 hmPay k)) := by
  funext q
  unfold embedAlpha107 embedAlphaCore80
  by_cases h1 : 3924 ≤ q.val ∧ q.val < 3948
  · rw [s3DitePos h1, s3DitePos h1]; dsimp only; rw [s3DitePos (by omega)]
    exact congrArg β (congrArg (sel149 hmPay) (Fin.ext (by dsimp; omega)))
  · rw [s3DiteNeg h1, s3DiteNeg h1]
    by_cases h2 : 3948 ≤ q.val ∧ q.val < 3951
    · rw [s3DitePos h2, s3DitePos h2]; dsimp only; rw [s3DitePos (by omega)]
      exact congrArg β (congrArg (sel149 hmPay) (Fin.ext (by dsimp; omega)))
    · rw [s3DiteNeg h2, s3DiteNeg h2]
      by_cases h3 : 3954 ≤ q.val ∧ q.val < 4034
      · rw [s3DitePos h3, s3DitePos h3]; dsimp only; rw [s3DitePos (by omega)]
        exact congrArg β (congrArg (sel149 hmPay) (Fin.ext (by dsimp; omega)))
      · rw [s3DiteNeg h3, s3DiteNeg h3]

theorem s3Shift48_36_eq_64_mul_shift42Norm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (β : BitAssignment (momCoreWires mPayload + 48)) : s3Shift48_36 t cfg hmPay (fun q ↦ β
    ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ 48)⟩) = 64 * s3Shift42Norm1s t cfg
    (fun k ↦ β (sel107 hmPay k)) := by
  rw [(s3AcceptNorm1s_dep_only_on_sel149 t cfg hmPay β).2, embedAlphaCore80_sel149_eq hmPay β]
  unfold s3Shift42Norm1s s3Shift48_36
  dsimp only
  split_ifs <;> omega

/-- Active `149`-wire catalyst modular-addition kick unitary at `Bk = 36` for `(t : Norm1sTier)`. -/
noncomputable def uKick149Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ 149) :=
  catModAddUnitary 107 42 (s3Shift42Norm1s t cfg)

private theorem catModAdd42_writeReg_ket {N : ℕ} (rSub : QRegister 107 N) (rTop : QRegister 42 N)
    (hdisj : rSub.DisjointWires rTop) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (β : BitAssignment N) :
    let vNew := (regVal rTop β + s3Shift42Norm1s t cfg (fun i ↦ β (rSub i))) % 2 ^ 42
    let fBits : BitAssignment 42 := fun j ↦ if vNew.testBit j.val then 1 else 0
    let f : BitAssignment N → BitAssignment N := fun δ ↦ writeRegProg δ rTop fBits
    regVal rTop (f β) = vNew ∧ (∀ w, w ∉ rTop.image → f β w = β w) ∧
      basisKet (f β) =
        ((rSub.concat rTop hdisj).embedUnitary (uKick149Norm1s t cfg)).1.mulVec (basisKet β) := by
  intro vNew fBits f
  have hfVal : regVal rTop (f β) = vNew := by
    unfold regVal f
    rw [show (fun j ↦ writeRegProg β rTop fBits (rTop j)) = fBits from
      funext (writeRegProg_apply_reg β rTop fBits)]
    exact bitsVal_eq_of_testBit fBits vNew (Nat.mod_lt _ (by positivity)) (fun _ ↦ rfl)
  have hout : ∀ w, w ∉ rTop.image → f β w = β w := fun w hw ↦
    writeRegProg_apply_of_not_mem β rTop fBits w (by simpa [QRegister.mem_image] using hw)
  exact ⟨hfVal, hout,
    catModAddUnitary_mulVec_basisKet rSub rTop hdisj (s3Shift42Norm1s t cfg) f β hout hfVal⟩

theorem uKick149Norm1s_embed (t : Norm1sTier) {mPayload : ℕ} (cfg :
    SpecsAux.SpecMirror.Configuration)
    (hmPay : 80 ≤ mPayload) :
    (sel149 hmPay).embedUnitary (uKick149Norm1s t cfg) =
      catModAddUnitary (momCoreWires mPayload) 48 (s3Shift48_36 t cfg hmPay) := by
  apply Subtype.ext
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
    .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
  let rCat0 : QRegister 48 (momCoreWires mPayload + 48) :=
    .block (momCoreWires mPayload) 48 le_rfl
  have hdisj0 : rCore0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 (momCoreWires mPayload) (momCoreWires mPayload) 48
      (mom_zero_add_le _ 48) le_rfl (mom_zero_add_le_self _)
  let rSub107 : QRegister 107 (momCoreWires mPayload + 48) := sel107 hmPay
  let rTop42 : QRegister 42 (momCoreWires mPayload + 48) := (sel149 hmPay).slice 107 42 le_rfl
  have hdisj149 : rSub107.DisjointWires rTop42 :=
    QRegister.slice_disjoint_of_le (sel149 hmPay) 0 107 107 42 (by decide) le_rfl le_rfl
  have hConcat149 : rSub107.concat rTop42 hdisj149 = sel149 hmPay := by
    apply s3Qreg_ext
    intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact congrArg (sel149 hmPay) (Fin.ext (Nat.zero_add i.val))
    · rw [QRegister.concat_apply_right]
      exact congrArg (sel149 hmPay) (Fin.ext rfl)
  have hrTop_eq (j : Fin 42) : rTop42 j = rCat0 ⟨6 + j.val, by omega⟩ := by
    apply Fin.ext
    have hj := j.isLt
    dsimp [rTop42, rCat0, QRegister.slice, QRegister.slice_apply, s3Qreg_whole_wires,
      s3Emb_trans_apply, s3Emb_refl_apply, s3Emb_mk_apply, sel149,
      s3Qreg_slice_wires, s3Qreg_compose_wires, s3Qreg_block_wires_apply, s3Qreg_block_apply]
    split_ifs <;> omega
  let vNew42 : ℕ := (regVal rTop42 β + s3Shift42Norm1s t cfg (fun i ↦ β (rSub107 i))) % 2 ^ 42
  let fBits42 : BitAssignment 42 := fun j ↦ if vNew42.testBit j.val then 1 else 0
  let f : BitAssignment (momCoreWires mPayload + 48) →
      BitAssignment (momCoreWires mPayload + 48) := fun δ ↦ writeRegProg δ rTop42 fBits42
  obtain ⟨hfVal42, hout42, hLhs0⟩ := catModAdd42_writeReg_ket rSub107 rTop42 hdisj149 t cfg β
  have hLhs : basisKet (f β) =
      ((sel149 hmPay).embedUnitary (uKick149Norm1s t cfg)).1.mulVec (basisKet β) := by
    rwa [hConcat149] at hLhs0
  have hlow6 (m : Fin 48) (hm6 : m.val < 6) : f β (rCat0 m) = β (rCat0 m) :=
    hout42 (rCat0 m) (by
      rw [QRegister.mem_image]
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val ((hrTop_eq j).symm.trans hj)
      dsimp [rCat0] at hv
      omega)
  have hout48 (w : Wire (momCoreWires mPayload + 48)) (hw : w ∉ rCat0.image) : f β w = β w :=
    hout42 w fun hmem ↦ hw (by
      rw [QRegister.mem_image] at hmem ⊢
      obtain ⟨j, rfl⟩ := hmem
      exact ⟨⟨6 + j.val, by omega⟩, (hrTop_eq j).symm⟩)
  have hfVal48 : regVal rCat0 (f β) =
      (regVal rCat0 β + s3Shift48_36 t cfg hmPay (fun i ↦ β (rCore0 i))) % 2 ^ 48 := by
    obtain ⟨hlin, h2⟩ := bitsVal_slice_linear (N := 48) (W := 42) (k := 6) le_rfl
      (fun m ↦ β (rCat0 m)) (fun m ↦ f β (rCat0 m))
      (fun m hm ↦ hlow6 m (hm.resolve_right (by have := m.isLt; omega)))
    have htopEq (δ : BitAssignment (momCoreWires mPayload + 48)) :
        bitsVal (fun j : Fin 42 ↦ δ (rCat0 ⟨6 + j.val, by omega⟩)) = regVal rTop42 δ :=
      congrArg bitsVal (funext fun j ↦ congrArg δ (hrTop_eq j).symm)
    rw [htopEq β, htopEq (f β), hfVal42] at hlin
    rw [htopEq β] at h2
    have hrc : regVal rCat0 β < 2 ^ 48 := bitsVal_lt_two_pow _
    have hrt : regVal rTop42 β < 2 ^ 42 := bitsVal_lt_two_pow _
    have hrcf : regVal rCat0 (f β) < 2 ^ 48 := bitsVal_lt_two_pow _
    have hshEq : s3Shift48_36 t cfg hmPay (fun i ↦ β (rCore0 i)) =
        64 * s3Shift42Norm1s t cfg (fun i ↦ β (rSub107 i)) := by
      rw [show (fun i ↦ β (rCore0 i)) =
          fun q : Fin (momCoreWires mPayload) ↦
            β ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ 48)⟩
        from funext fun i ↦ congrArg β (Fin.ext (Nat.zero_add i.val))]
      exact s3Shift48_36_eq_64_mul_shift42Norm1s t cfg hmPay β
    change regVal rCat0 (f β) + 2 ^ 6 * regVal rTop42 β =
      regVal rCat0 β + 2 ^ 6 *
        ((regVal rTop42 β + s3Shift42Norm1s t cfg (fun i ↦ β (rSub107 i))) % 2 ^ 42) at hlin
    have h2_6 : (2 : ℕ) ^ 6 = 64 := by decide
    have h2_42 : (2 : ℕ) ^ 42 = 4398046511104 := by decide
    have h2_48 : (2 : ℕ) ^ 48 = 281474976710656 := by decide
    rw [hshEq]
    rw [h2_6] at hlin h2
    rw [h2_42] at hrt hlin
    rw [h2_48] at hrc hrcf ⊢
    omega
  have hRhs := catModAddUnitary_mulVec_basisKet rCore0 rCat0 hdisj0
    (s3Shift48_36 t cfg hmPay) f β hout48 hfVal48
  rw [s3Block_concat_whole _ _ hdisj0,
    congrArg Subtype.val (QRegister.whole_embedUnitary _)] at hRhs
  exact hLhs.symm.trans hRhs

theorem s3CoreMapNorm1s_bits_of_accept (t : Norm1sTier) {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (β : BitAssignment (momCoreWires mPayload + 48))
    (hz : s3AcceptNorm1s t hmPay
      ((basisBitsEquiv (momCoreWires mPayload)).symm
        (fun q ↦ β (QRegister.block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48) q))) = true)
    (hz80 : s3AcceptNorm1s t hmPay80
      ((basisBitsEquiv (momCoreWires 80)).symm
        (embedAlpha107 (fun k ↦ β (sel107 hmPay k)))) = true)
    (q : Wire (momCoreWires mPayload)) :
    let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
      .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
    let α107 : BitAssignment 107 := fun k ↦ β (sel107 hmPay k)
    let γ : BitAssignment (momCoreWires mPayload) := fun q ↦ β (rCore0 q)
    let zM := (basisBitsEquiv (momCoreWires mPayload)).symm γ
    basisBits (momCoreWires mPayload) (s3CorePermNorm1s t hmPay zM) q =
      if _ : 3924 ≤ q.val ∧ q.val < 3948 then
        swapRejMap107Norm1s t α107 ⟨q.val - 3924, by omega⟩
      else if _ : 3976 ≤ q.val ∧ q.val < 3979 then
        swapRejMap107Norm1s t α107 ⟨49 + (q.val - 3976), by omega⟩
      else γ q := by
  intro rCore0 α107 γ zM
  set z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
  have hbbM : basisBits (momCoreWires mPayload) zM = γ := basisBits_symm _
  have hbb80 : basisBits (momCoreWires 80) z80 = embedAlpha107 α107 := basisBits_symm _
  change basisBits (momCoreWires mPayload) (s3CoreMapNorm1s t hmPay zM) q = _
  unfold s3CoreMapNorm1s
  rw [s3ItePos hz]
  dsimp +zeta only
  rw [congrFun (basisBits_symm _) q]
  have h80q : ∀ (k : Fin 107), swapRejMap107Norm1s t α107 k =
      basisBits (momCoreWires 80) (s3CoreMapNorm1s t hmPay80 z80) (sel107_80 k) := fun _ ↦ rfl
  obtain ⟨_, hProjC, hU22C, hS3C, _, _, _, _⟩ := s3Sel149_core_fields_eq hmPay β
  have hγEq : γ = fun w ↦ β ⟨w.val, Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ 48)⟩ :=
    funext fun w ↦ congrArg β (Fin.ext (Nat.zero_add w.val))
  have hzM_eq : zM = (basisBitsEquiv (momCoreWires mPayload)).symm
      (fun w ↦ β ⟨w.val, Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ 48)⟩) :=
    congrArg (basisBitsEquiv (momCoreWires mPayload)).symm hγEq
  have hz80_eq : z80 = (basisBitsEquiv (momCoreWires 80)).symm
      (embedAlphaCore80 (fun k ↦ β (sel149 hmPay k))) :=
    congrArg (basisBitsEquiv (momCoreWires 80)).symm (embedAlphaCore80_sel149_eq hmPay β).symm
  have hProjEq : ∀ ax : Fin 3, projAxisField ((momSysReg mPayload).extractIndex zM) ax =
      projAxisField ((momSysReg 80).extractIndex z80) ax := by rw [hzM_eq, hz80_eq]; exact hProjC
  have hU22Eq : (s3U22Core hmPay).extractIndex zM = (s3U22Core hmPay80).extractIndex z80 := by
    rw [hzM_eq, hz80_eq]; exact hU22C
  have hS3Eq : (s3S3Core hmPay).extractIndex zM = (s3S3Core hmPay80).extractIndex z80 := by
    rw [hzM_eq, hz80_eq]; exact hS3C
  by_cases h1 : 3924 ≤ q.val ∧ q.val < 3948
  · have hsys : q.val < SpecsAux.SpecMirror.systemQubits := by rw [s3SysQubits_eq]; omega
    rw [s3DitePos hsys, s3DitePos h1, h80q]
    unfold s3CoreMapNorm1s
    rw [s3ItePos hz80]; dsimp +zeta only
    rw [congrFun (basisBits_symm _) _]
    have hsel80 := sel107_80_sub0 h1
    rw [s3DitePos (by rw [hsel80]; exact hsys)]
    unfold s3UpdateSysProj
    rw [congrFun (basisBits_symm _) _, congrFun (basisBits_symm _) _,
      s3DiteNeg (by dsimp; omega), s3DiteNeg (by dsimp; rw [hsel80]; omega)]
    simp_rw [hProjEq, hU22Eq, hS3Eq, hsel80]
  · rw [s3DiteNeg h1]
    by_cases h2 : 3976 ≤ q.val ∧ q.val < 3979
    · have hnsys : ¬(q.val < SpecsAux.SpecMirror.systemQubits) := by rw [s3SysQubits_eq]; omega
      rw [s3DiteNeg hnsys, s3DitePos h2, s3DitePos h2, h80q]
      unfold s3CoreMapNorm1s
      rw [s3ItePos hz80]; dsimp +zeta only
      rw [congrFun (basisBits_symm _) _]
      have hsel80 := sel107_80_s3 h2
      rw [s3DiteNeg (by rw [hsel80]; exact hnsys), s3DitePos (by rw [hsel80]; exact h2)]
      simp_rw [hU22Eq, hS3Eq, hsel80]
    · rw [s3DiteNeg h2, s3DiteNeg h2]
      by_cases hsys : q.val < SpecsAux.SpecMirror.systemQubits
      · rw [s3DitePos hsys]
        unfold s3UpdateSysProj
        rw [congrFun (basisBits_symm _) _, s3DitePos (by dsimp; rw [s3SysQubits_eq] at hsys; omega)]
        have hb := QRegister.basisBits_extractIndex (momSysReg mPayload) zM ⟨q.val, hsys⟩
        have hqEq : momSysReg mPayload ⟨q.val, hsys⟩ = q := Fin.ext (Nat.zero_add q.val)
        rw [hqEq] at hb; rw [hb, hbbM]
      · rw [s3DiteNeg hsys, hbbM]

private theorem signedPermMatrix_col_eq {N : ℕ} (perm : Equiv.Perm (Fin N)) (φ : Fin N → ℝ)
    (hφ : ∀ x, φ (perm x) = φ x) (x l : Fin N) :
    signedPermMatrix perm φ l x = if l = perm x then ((φ x : ℝ) : ℂ) else 0 := by
  rw [signedPermMatrix_apply]
  by_cases hl : l = perm x
  · subst hl; rw [s3ItePos rfl, s3ItePos rfl, hφ]
  · rw [s3IteNeg (Ne.symm hl), s3IteNeg hl]

private theorem writeRegProg_self_reg {M k : ℕ} (β : BitAssignment M) (r : QRegister k M) :
    writeRegProg β r (fun i ↦ β (r i)) = β := by
  funext u
  by_cases hm : u ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hm; exact writeRegProg_apply_reg β r (fun j ↦ β (r j)) i
  · exact writeRegProg_apply_of_not_mem β r (fun j ↦ β (r j)) u hm

theorem uSwapRej107Norm1s_embed (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
      .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
    (sel107 hmPay).embedUnitary (uSwapRej107Norm1s t) =
      rCore0.embedUnitary (s3SwapRejUnitaryNorm1s t hmPay) := by
  intro rCore0
  apply Subtype.ext
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    embedMatrix_mulVec_ket_prog, embedMatrix_mulVec_ket_prog]
  let α107 : BitAssignment 107 := fun k ↦ β (sel107 hmPay k)
  let γ : BitAssignment (momCoreWires mPayload) := fun q ↦ β (rCore0 q)
  have hlocL : localIdxProg (sel107 hmPay) β = (basisBitsEquiv 107).symm α107 := rfl
  have hlocR : localIdxProg rCore0 β = (basisBitsEquiv (momCoreWires mPayload)).symm γ := rfl
  rw [hlocL, hlocR]
  set idx107 := (basisBitsEquiv 107).symm α107
  set zM := (basisBitsEquiv (momCoreWires mPayload)).symm γ
  set z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
  have hbb107 : basisBits 107 idx107 = α107 := basisBits_symm _
  have hbbM : basisBits (momCoreWires mPayload) zM = γ := basisBits_symm _
  have hbb80 : basisBits (momCoreWires 80) z80 = embedAlpha107 α107 := basisBits_symm _
  have hembEq : embedAlphaCore80 (fun k ↦ β (sel149 hmPay k)) = embedAlpha107 α107 :=
    embedAlphaCore80_sel149_eq hmPay β
  have hγEq : γ = fun q ↦ β ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ 48)⟩ :=
    funext fun q ↦ congrArg β (Fin.ext (Nat.zero_add q.val))
  have hAccEq : s3AcceptNorm1s t hmPay zM = s3AcceptNorm1s t hmPay80 z80 := by
    dsimp only [zM, z80]
    rw [← hembEq, hγEq]
    exact (s3AcceptNorm1s_dep_only_on_sel149 t dummyCfgS3 hmPay β).1
  have hL : ∀ l : Fin (2 ^ 107), (uSwapRej107Norm1s t).1 l idx107 =
      if l = swapRejPerm107Norm1s t idx107 then ((swapRejPhase107Norm1s t idx107 : ℝ) : ℂ) else 0 :=
        by
    intro l
    change signedPermMatrix (swapRejPerm107Norm1s t) (swapRejPhase107Norm1s t) l idx107 = _
    exact signedPermMatrix_col_eq (swapRejPerm107Norm1s t) (swapRejPhase107Norm1s t)
      (swapRejPhase107Norm1s_symm t) idx107 l
  have hR : ∀ l : Fin (2 ^ (momCoreWires mPayload)), (s3SwapRejUnitaryNorm1s t hmPay).1 l zM =
      if l = s3CorePermNorm1s t hmPay zM then ((s3RejPhaseNorm1s t hmPay zM : ℝ) : ℂ) else 0 := by
    intro l
    change signedPermMatrix (s3CorePermNorm1s t hmPay) (s3RejPhaseNorm1s t hmPay) l zM = _
    exact signedPermMatrix_col_eq (s3CorePermNorm1s t hmPay) (s3RejPhaseNorm1s t hmPay)
      (s3RejPhaseNorm1s_symm t hmPay) zM l
  simp_rw [hL, hR, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hperm107_bits : basisBits 107 (swapRejPerm107Norm1s t idx107) = swapRejMap107Norm1s t α107 :=
    by
    unfold swapRejPerm107Norm1s; dsimp -failIfUnchanged only [Equiv.coe_fn_mk];
      rw [hbb107, basisBits_symm]
  rw [hperm107_bits]
  obtain ⟨hCoinC, _, _, _, _, _, _, hBParC⟩ := s3Sel149_core_fields_eq hmPay β
  have hzM_eq : zM = (basisBitsEquiv (momCoreWires mPayload)).symm
      (fun q ↦ β ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.le_add_right _ 48)⟩) :=
    congrArg (basisBitsEquiv (momCoreWires mPayload)).symm hγEq
  have hz80_eq : z80 = (basisBitsEquiv (momCoreWires 80)).symm
      (embedAlphaCore80 (fun k ↦ β (sel149 hmPay k))) :=
    congrArg (basisBitsEquiv (momCoreWires 80)).symm hembEq.symm
  have hCoinEq : (momCoinReg mPayload).extractIndex zM = (momCoinReg 80).extractIndex z80 := by
    rw [hzM_eq, hz80_eq]; exact hCoinC
  have hBParEq : basisBits (momCoreWires mPayload) zM (s3BParCore hmPay) =
      basisBits (momCoreWires 80) z80 (s3BParCore hmPay80) := by
    rw [hzM_eq, hz80_eq]; exact hBParC
  have hSignEq : swapRejPhase107Norm1s t idx107 = s3RejPhaseNorm1s t hmPay zM := by
    unfold swapRejPhase107Norm1s
    rw [hbb107]
    change s3RejPhaseNorm1s t hmPay80 z80 = s3RejPhaseNorm1s t hmPay zM
    unfold s3RejPhaseNorm1s
    rw [hCoinEq, hAccEq, hBParEq]
  rw [hSignEq]
  refine congrArg (fun x ↦ ((s3RejPhaseNorm1s t hmPay zM : ℝ) : ℂ) •
    MeasureBranchHadamardSem.ket x) ?_
  funext w
  by_cases hz : s3AcceptNorm1s t hmPay zM = true
  · have hz80 : s3AcceptNorm1s t hmPay80 z80 = true := hAccEq.symm.trans hz
    have hwCore := s3CoreMapNorm1s_bits_of_accept t hmPay β hz hz80
    by_cases hwC : w.val < momCoreWires mPayload
    · let q : Wire (momCoreWires mPayload) := ⟨w.val, hwC⟩
      have hr : rCore0 q = w := Fin.ext (Nat.zero_add w.val)
      rw [← hr, writeRegProg_apply_reg, hwCore q]
      have hsel_eq (k : Fin 107) (hkv : (sel107_80 k).val = q.val) : sel107 hmPay k = rCore0 q :=
        Fin.ext ((sel107_hmPay_val hmPay k).trans (hkv.trans (Nat.zero_add q.val).symm))
      by_cases h1 : 3924 ≤ q.val ∧ q.val < 3948
      · rw [s3DitePos h1, ← hsel_eq _ (sel107_80_sub0 h1), writeRegProg_apply_reg]
      · rw [s3DiteNeg h1]
        by_cases h2 : 3976 ≤ q.val ∧ q.val < 3979
        · rw [s3DitePos h2, ← hsel_eq _ (sel107_80_s3 h2), writeRegProg_apply_reg]
        · rw [s3DiteNeg h2]
          by_cases hmem : rCore0 q ∈ Set.range (sel107 hmPay).wires
          · obtain ⟨k, hk⟩ := hmem
            rw [← hk, writeRegProg_apply_reg]
            have hkval : (sel107_80 k).val = q.val :=
              ((sel107_hmPay_val hmPay k).symm.trans (congrArg Fin.val hk)).trans (Nat.zero_add _)
            unfold swapRejMap107Norm1s s3CoreMapNorm1s
            rw [s3ItePos hz80]; dsimp +zeta only
            rw [congrFun (basisBits_symm _) _,
              s3DiteNeg (by
                rw [hkval, s3SysQubits_eq]
                have hv80 := sel107_80_val k; have := k.isLt; split_ifs at hv80 <;> omega),
              s3DiteNeg (by rw [hkval]; exact h2), hbb80, embedAlpha107_sel107_80]
            simp only [α107, hk]; rfl
          · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem]
    · have hnotR : w ∉ Set.range rCore0.wires := by
        rintro ⟨q, rfl⟩; have hv : (rCore0 q).val = 0 + q.val := rfl; have := q.isLt; omega
      have hnotL : w ∉ Set.range (sel107 hmPay).wires := by
        rintro ⟨k, rfl⟩; apply hwC; rw [sel107_hmPay_val]
        exact lt_of_lt_of_le (lt_of_lt_of_eq (sel107_80 k).isLt (s3MomCoreWires_eq 80))
          (s3MomCore_ge_4034 hmPay)
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnotL, writeRegProg_apply_of_not_mem _ _ _ _ hnotR]
  · have hz80 : ¬(s3AcceptNorm1s t hmPay80 z80 = true) := by rw [← hAccEq]; exact hz
    have hm80 : swapRejMap107Norm1s t α107 = α107 := by
      funext k; unfold swapRejMap107Norm1s
      have hid : s3CoreMapNorm1s t hmPay80 z80 = z80 := by
        unfold s3CoreMapNorm1s; rw [s3IteNeg hz80]
      rw [hid, hbb80, embedAlpha107_sel107_80]
    have hmM : basisBits (momCoreWires mPayload) (s3CorePermNorm1s t hmPay zM) = γ := by
      have hid : s3CorePermNorm1s t hmPay zM = zM := by
        change s3CoreMapNorm1s t hmPay zM = zM; unfold s3CoreMapNorm1s; rw [s3IteNeg hz]
      rw [hid, hbbM]
    rw [hm80, hmM]
    rw [writeRegProg_self_reg β (sel107 hmPay), writeRegProg_self_reg β rCore0]

theorem swapRejMap107Norm1s_of_accept (t : Norm1sTier) (α107 : BitAssignment 107)
    (hz : s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)) =
      true) :
    let u22 : Fin 4194304 :=
      ⟨bitsVal (fun i : Fin 22 ↦ α107 ⟨27 + i.val, by omega⟩), bitsVal_lt_two_pow _⟩
    (∀ (w : Fin 3) (b : Fin 8),
      let pVal : Fin 256 :=
        ⟨bitsVal (fun j : Fin 8 ↦ α107 ⟨8 * w.val + j.val, by omega⟩), bitsVal_lt_two_pow _⟩
      let st := s3ProjStepHw pVal (shellMagCoord3 u22 w) (α107 ⟨49 + w.val, by omega⟩).val
      swapRejMap107Norm1s t α107 ⟨8 * w.val + b.val, by omega⟩ =
        if st.1.val.testBit b.val then 1 else 0) ∧
    (∀ (w : Fin 3),
      swapRejMap107Norm1s t α107 ⟨49 + w.val, by omega⟩ =
        α107 ⟨49 + w.val, by omega⟩ + (if shellMagCoord3 u22 w = 0 then 0 else 1)) ∧
    (∀ (k : Fin 107), ¬(k.val < 24) → ¬(49 ≤ k.val ∧ k.val < 52) →
      swapRejMap107Norm1s t α107 k = α107 k) := by
  intro u22
  set z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
  obtain ⟨hProj80, _, hU22_80, hS3_80, _, _, _, _⟩ := embedAlpha107_fields α107
  have huEq : (s3U22Core hmPay80).extractIndex z80 = u22 := Fin.ext hU22_80
  refine ⟨fun w b ↦ ?_, fun w ↦ ?_, fun k hn24 hn49 ↦ ?_⟩
  · intro pVal st
    have hpEq : projAxisField ((momSysReg 80).extractIndex z80) w = pVal := Fin.ext (hProj80 w)
    have hsel : (sel107_80 ⟨8 * w.val + b.val, by omega⟩).val = 3924 + 8 * w.val + b.val := by
      have hw := w.isLt; have hb := b.isLt
      have hv := sel107_80_val ⟨8 * w.val + b.val, by omega⟩
      rw [s3ItePos (by dsimp; omega)] at hv; dsimp at hv; omega
    have hselFin : sel107_80 ⟨8 * w.val + b.val, by omega⟩ =
        ⟨3924 + 8 * w.val + b.val, by
          rw [s3MomCoreWires_eq]; have := w.isLt; have := b.isLt; omega⟩ :=
      Fin.ext hsel
    have hsys : 3924 + 8 * w.val + b.val < SpecsAux.SpecMirror.systemQubits := by
      rw [s3SysQubits_eq]; have := w.isLt; have := b.isLt; omega
    let kSys : Fin SpecsAux.SpecMirror.systemQubits := ⟨3924 + 8 * w.val + b.val, hsys⟩
    have hnkSys : ¬(kSys.val < 3924) := by dsimp [kSys]; omega
    let pNew80 : Fin 3 → Fin 256 := fun w' ↦ (s3ProjStepHw (projAxisField ((momSysReg
        80).extractIndex z80) w') (shellMagCoord3 ((s3U22Core hmPay80).extractIndex z80) w')
        (signBit3 ((s3S3Core hmPay80).extractIndex z80) w')).1
    unfold swapRejMap107Norm1s s3CoreMapNorm1s
    rw [s3ItePos hz]; dsimp +zeta only
    rw [congrFun (basisBits_symm _) _, hselFin, s3DitePos hsys]
    change basisBits SpecsAux.SpecMirror.systemQubits
      (s3UpdateSysProj ((momSysReg 80).extractIndex z80) pNew80) kSys = _
    unfold s3UpdateSysProj
    rw [congrFun (basisBits_symm _) kSys, s3DiteNeg hnkSys]
    have hwF : (⟨(kSys.val - 3924) / 8, s3ProjAxisIdx_lt hnkSys⟩ : Fin 3) = w :=
      Fin.ext (by dsimp [kSys]; have := b.isLt; omega)
    have hbF : (⟨(kSys.val - 3924) % 8, s3ProjBitIdx_lt (kSys.val - 3924)⟩ : Fin 8) = b :=
      Fin.ext (by dsimp [kSys]; have := b.isLt; omega)
    dsimp only [pNew80]
    rw [hwF, hbF, hpEq, huEq, hS3_80 w]
    exact basisBits_eq_testBit 8 st.1 b
  · have hsel : (sel107_80 ⟨49 + w.val, by omega⟩).val = 3976 + w.val := by
      have := w.isLt
      have hv := sel107_80_val ⟨49 + w.val, by omega⟩
      rw [s3IteNeg (by dsimp; omega), s3IteNeg (by dsimp; omega)] at hv; dsimp at hv; omega
    have hselFin : sel107_80 ⟨49 + w.val, by omega⟩ =
        ⟨3976 + w.val, by rw [s3MomCoreWires_eq]; have := w.isLt; omega⟩ :=
      Fin.ext hsel
    have hnsys : ¬(3976 + w.val < SpecsAux.SpecMirror.systemQubits) := by rw [s3SysQubits_eq]; omega
    have hS3r : 3976 ≤ 3976 + w.val ∧ 3976 + w.val < 3979 := by have := w.isLt; omega
    unfold swapRejMap107Norm1s s3CoreMapNorm1s
    rw [s3ItePos hz]; dsimp +zeta only
    rw [congrFun (basisBits_symm _) _, hselFin, s3DiteNeg hnsys, s3DitePos hS3r]
    have hwF : (⟨3976 + w.val - 3976, by omega⟩ : Fin 3) = w := Fin.ext (by dsimp; omega)
    rw [hwF, huEq]
    generalize hs3 : (s3S3Core hmPay80).extractIndex z80 = s3
    have hs3w := hS3_80 w; rw [hs3] at hs3w
    have hsVal : α107 ⟨49 + w.val, by omega⟩ = if signBit3 s3 w = 1 then 1 else 0 := by
      rcases bit_cases (α107 ⟨49 + w.val, by omega⟩) with hbit | hbit
      · rw [hbit] at hs3w ⊢; change signBit3 s3 w = 0 at hs3w; rw [s3IteNeg (by omega)]
      · rw [hbit] at hs3w ⊢; change signBit3 s3 w = 1 at hs3w; rw [s3ItePos hs3w]
    have hbb3 : ∀ (x : Fin 8) (j : Fin 3),
        basisBits 3 x j = if signBit3 x j = 1 then 1 else 0 := by
      intro x j; rw [basisBits_eq_testBit 3 x j]; fin_cases x <;> fin_cases j <;> decide
    rw [hsVal, hbb3 (negSign3_22 u22 s3) w, signBit3_negSign3_22]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (signBit3_le_one s3 w) with hsb | hsb <;>
    by_cases hm : shellMagCoord3 u22 w = 0 <;>
    simp only [hsb, hm, ↓reduceIte] <;> decide
  · have hnsys : ¬((sel107_80 k).val < SpecsAux.SpecMirror.systemQubits) := by
      have hk := k.isLt; have hv := sel107_80_val k; rw [s3SysQubits_eq]; split_ifs at hv <;> omega
    have hnS3 : ¬(3976 ≤ (sel107_80 k).val ∧ (sel107_80 k).val < 3979) := by
      have hk := k.isLt; have hv := sel107_80_val k; split_ifs at hv <;> omega
    unfold swapRejMap107Norm1s s3CoreMapNorm1s
    rw [s3ItePos hz]; dsimp +zeta only
    rw [congrFun (basisBits_symm _) _, s3DiteNeg hnsys, s3DiteNeg hnS3,
      basisBits_symm, embedAlpha107_sel107_80]

/-- Active `149`-wire embedding of `uSwapRej107Norm1s t` on the low `107` active wires. -/
noncomputable def uSwapRej149Norm1s (t : Norm1sTier) : Unitary (2 ^ 149) :=
  (QRegister.block 0 107 (by decide)).embedUnitary (uSwapRej107Norm1s t)

/-- Combined `149`-wire active core unitary `uSwapRej149Norm1s t * uKick149Norm1s t cfg`. -/
noncomputable def uCore149Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ 149) :=
  uSwapRej149Norm1s t * uKick149Norm1s t cfg

theorem uCore149Norm1s_embed (t : Norm1sTier) {mPayload : ℕ} (cfg :
    SpecsAux.SpecMirror.Configuration)
    (hmPay : 80 ≤ mPayload) :
    (sel149 hmPay).embedUnitary (uCore149Norm1s t cfg) = uCore3CatNorm1s t cfg hmPay := by
  unfold uCore149Norm1s uSwapRej149Norm1s uCore3CatNorm1s
  rw [QRegister.embedUnitary_mul, uKick149Norm1s_embed, ← QRegister.embedUnitary_compose]
  have hcomp : (sel149 hmPay).compose (QRegister.block 0 107 (by decide)) = sel107 hmPay := by
    apply s3Qreg_ext
    intro i
    dsimp [sel107, QRegister.slice, QRegister.slice_apply, s3Qreg_whole_wires,
      s3Emb_trans_apply, s3Emb_refl_apply, s3Emb_mk_apply, s3Qreg_slice_wires,
      s3Qreg_compose_wires, s3Qreg_block_wires_apply, s3Qreg_block_apply]
  rw [hcomp, uSwapRej107Norm1s_embed]

theorem uCore149Norm1s_intertwines (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (U_catTwist : Unitary (2 ^ 48))
    (hcol : ∀ m : Fin (2 ^ 48), U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) :
    let rCore0 : QRegister (momCoreWires mPayload) (momCoreWires mPayload + 48) :=
      .block 0 (momCoreWires mPayload) (mom_zero_add_le _ 48)
    IntertwinesMomCat U_catTwist
      (PosMomSelectDynamic.unitaryConj
        (rCore0.embedUnitary (uPrep3_216 hmPay))
        ((sel149 hmPay).embedUnitary (uCore149Norm1s t cfg)))
      (PosMomSelectDynamic.unitaryConj (uPrep3_216 hmPay) (uCore3EffNorm1s t cfg hmPay)) := by
  dsimp only
  rw [uCore149Norm1s_embed t cfg hmPay]
  exact uSlot3CatNorm1s_intertwines t cfg hmPay U_catTwist hcol

/-- Active `149`-wire basis permutation of `uCore149Norm1s t cfg` on `α`. -/
noncomputable def corePerm149Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) : BitAssignment 149 :=
  let α107 : BitAssignment 107 := fun i ↦ α (Fin.castLE (by decide) i)
  let vNew42 : ℕ :=
    (bitsVal (fun j : Fin 42 ↦ α (Fin.natAdd 107 j)) + s3Shift42Norm1s t cfg α107) % 2 ^ 42
  fun k ↦
    if h : k.val < 107 then swapRejMap107Norm1s t α107 ⟨k.val, h⟩
    else if vNew42.testBit (k.val - 107) then 1 else 0

/-- Active `149`-wire `ZMod 2` phase exponent of `uCore149Norm1s t cfg` on `α`. -/
noncomputable def corePhase149Norm1s (t : Norm1sTier) (α : BitAssignment 149) : ZMod 2 :=
  let α107 : BitAssignment 107 := fun i ↦ α (Fin.castLE (by decide) i)
  let z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
  if ((momCoinReg 80).extractIndex z80).val = 6 ∧
     s3AcceptNorm1s t hmPay80 z80 = false ∧
     basisBits (momCoreWires 80) z80 (s3BParCore hmPay80) = 1
  then 1 else 0

theorem corePhase149Norm1s_pow_eq (t : Norm1sTier) (α : BitAssignment 149) :
    let α107 : BitAssignment 107 := fun i ↦ α ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
    ((-1 : ℂ) ^ (corePhase149Norm1s t α).val) =
      ((swapRejPhase107Norm1s t ((basisBitsEquiv 107).symm α107) : ℝ) : ℂ) := by
  intro α107
  have hα : (fun i : Fin 107 ↦ α (Fin.castLE (by decide) i)) = α107 := rfl
  unfold corePhase149Norm1s swapRejPhase107Norm1s s3RejPhaseNorm1s
  dsimp +zeta only
  rw [hα, basisBits_symm α107, basisBits_symm (embedAlpha107 α107)]
  generalize ((momCoinReg 80).extractIndex ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107
    α107))).val = cVal
  generalize s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107))
    = accB
  generalize embedAlpha107 α107 (s3BParCore hmPay80) = bpar
  by_cases hc : cVal = 6 <;>
  cases accB <;>
  rcases bit_cases bpar with hb | hb <;>
  simp [hc, hb]

theorem uCore149Norm1s_mulVec (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) :
    (uCore149Norm1s t cfg).1.mulVec (MeasureBranchHadamardSem.ket α) =
      ((-1 : ℂ) ^ (corePhase149Norm1s t α).val) •
        MeasureBranchHadamardSem.ket (corePerm149Norm1s t cfg α) := by
  rw [uCore149Norm1s, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  let rSub107 : QRegister 107 149 := QRegister.block 0 107 (by decide)
  let rTop42 : QRegister 42 149 := QRegister.block 107 42 (by decide)
  have hdisj149 : rSub107.DisjointWires rTop42 :=
    QRegister.block_disjoint_of_le 0 107 107 42 (by decide) (by decide) (by decide)
  have hWhole149 : rSub107.concat rTop42 hdisj149 = QRegister.whole 149 :=
    s3Block_concat_whole _ _ hdisj149
  have hWholeId149 : ((QRegister.whole 149).embedUnitary (uKick149Norm1s t cfg)).1 =
      (uKick149Norm1s t cfg).1 :=
    congrArg Subtype.val (QRegister.whole_embedUnitary (uKick149Norm1s t cfg))
  let α107 : BitAssignment 107 := fun i ↦ α ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  let vNew42 : ℕ := (regVal rTop42 α + s3Shift42Norm1s t cfg (fun i ↦ α (rSub107 i))) % 2 ^ 42
  let fBits42 : BitAssignment 42 := fun j ↦ if vNew42.testBit j.val then 1 else 0
  let f : BitAssignment 149 → BitAssignment 149 := fun δ ↦ writeRegProg δ rTop42 fBits42
  obtain ⟨_, hout42, hKick0⟩ := catModAdd42_writeReg_ket rSub107 rTop42 hdisj149 t cfg α
  have hKick : MeasureBranchHadamardSem.ket (f α) =
      (uKick149Norm1s t cfg).1.mulVec (MeasureBranchHadamardSem.ket α) := by
    rwa [hWhole149, hWholeId149] at hKick0
  rw [← hKick, show uSwapRej149Norm1s t = rSub107.embedUnitary (uSwapRej107Norm1s t) from rfl,
    QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
  have hfSub : (fun i : Fin 107 ↦ f α (rSub107 i)) = α107 := funext fun i ↦ by
    have hnot : rSub107 i ∉ rTop42.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩
      have hv : 107 + j.val = 0 + i.val := congrArg Fin.val hj
      have := i.isLt; omega
    exact (hout42 _ hnot).trans (congrArg α (Fin.ext (Nat.zero_add i.val)))
  set idx107 := (basisBitsEquiv 107).symm α107
  have hloc : localIdxProg rSub107 (f α) = idx107 := congrArg (basisBitsEquiv 107).symm hfSub
  rw [hloc]
  have hEntry : ∀ l : Fin (2 ^ 107), (uSwapRej107Norm1s t).1 l idx107 =
      if l = swapRejPerm107Norm1s t idx107 then ((swapRejPhase107Norm1s t idx107 : ℝ) : ℂ) else 0 :=
        by
    intro l
    change signedPermMatrix (swapRejPerm107Norm1s t) (swapRejPhase107Norm1s t) l idx107 = _
    exact signedPermMatrix_col_eq (swapRejPerm107Norm1s t) (swapRejPhase107Norm1s t)
      (swapRejPhase107Norm1s_symm t) idx107 l
  simp_rw [hEntry, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hperm107 : basisBits 107 (swapRejPerm107Norm1s t idx107) = swapRejMap107Norm1s t α107 := by
    unfold swapRejPerm107Norm1s; dsimp -failIfUnchanged only [Equiv.coe_fn_mk]
    rw [basisBits_symm, basisBits_symm]
  rw [hperm107, ← corePhase149Norm1s_pow_eq t α]
  refine congrArg (fun x ↦ ((-1 : ℂ) ^ (corePhase149Norm1s t α).val) •
    MeasureBranchHadamardSem.ket x) ?_
  funext k
  by_cases hk : k.val < 107
  · have hLk : writeRegProg (f α) rSub107 (swapRejMap107Norm1s t α107) k =
        swapRejMap107Norm1s t α107 ⟨k.val, hk⟩ := by
      have hrk : k = rSub107 ⟨k.val, hk⟩ := Fin.ext (Nat.zero_add k.val).symm
      conv_lhs => rw [hrk]
      exact writeRegProg_apply_reg _ _ _ _
    rw [hLk]; unfold corePerm149Norm1s; rw [s3DitePos hk]; rfl
  · have hnot : k ∉ Set.range rSub107.wires := by
      rintro ⟨i, rfl⟩; have hv : (rSub107 i).val = 0 + i.val := rfl; have := i.isLt; omega
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot]
    let j : Fin 42 := ⟨k.val - 107, by have := k.isLt; omega⟩
    have hfk : f α k = fBits42 j := by
      have hrk : k = rTop42 j := Fin.ext (by
        have hv : (rTop42 j).val = 107 + (k.val - 107) := rfl; omega)
      conv_lhs => rw [hrk]
      exact writeRegProg_apply_reg α rTop42 fBits42 j
    rw [hfk]; unfold corePerm149Norm1s; rw [s3DiteNeg hk]
    have hvEq : (bitsVal (fun j' : Fin 42 ↦ α (Fin.natAdd 107 j')) +
        s3Shift42Norm1s t cfg (fun i ↦ α (Fin.castLE (by decide) i))) % 2 ^ 42 = vNew42 :=
      congrArg₂ (fun x y ↦ (x + s3Shift42Norm1s t cfg y) % 2 ^ 42)
        (congrArg bitsVal (funext fun j' ↦ congrArg α (Fin.ext (by dsimp [Fin.natAdd]; rfl))))
        (funext fun i ↦ congrArg α (Fin.ext (Nat.zero_add i.val).symm))
    dsimp only [fBits42, j]
    rw [hvEq]

theorem s3SynthStructureFactor216_42_trunc36Cfg (cfg : SpecsAux.SpecMirror.Configuration)
    (Δ : Fin 3 → ℤ) :
    s3SynthStructureFactor216 42 (trunc36Cfg cfg) Δ = s3SynthStructureFactor216 36 cfg Δ := by
  unfold s3SynthStructureFactor216
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [exp_thetaProtonNearest_42_trunc36Cfg]

/-- Hardware 1-sided normalized Slot-3 radial kernel approximation for `(t : Norm1sTier)`. -/
noncomputable def dampedNorm1sKernelApprox (t : Norm1sTier) (Δ : Fin 3 → ℤ) : ℝ :=
  if Δ = 0 then 0
  else
    let μ := shellIndex (modFold3D 127 Δ)
    let cnt38 : ℕ := 2 ^ (38 - t.kBits) * norm1sAcceptCountK t μ (sumNatAbsSq Δ)
    (2 / 42 : ℝ) * ((cnt38 : ℝ) / (2 : ℝ) ^ (2 * μ + 38))

theorem dampedNorm1sKernelApprox_zero (t : Norm1sTier) :
    dampedNorm1sKernelApprox t 0 = 0 := rfl

theorem dampedNorm1sKernelApprox_nonneg (t : Norm1sTier) (Δ : Fin 3 → ℤ) :
    0 ≤ dampedNorm1sKernelApprox t Δ := by
  unfold dampedNorm1sKernelApprox
  split_ifs with h0
  · exact le_rfl
  · dsimp only
    positivity

theorem sumNatAbsSq_lt_two_pow_18_of_mem_box3D_254 {Δ : Fin 3 → ℤ}
    (hbox : Δ ∈ box3D (2 * (127 : ℤ))) : sumNatAbsSq Δ < 2 ^ 18 := by
  have hb0 := bounds_of_mem_box3D3 hbox 0
  have hb1 := bounds_of_mem_box3D3 hbox 1
  have hb2 := bounds_of_mem_box3D3 hbox 2
  have ha0 : (Δ 0).natAbs ≤ 254 := by omega
  have ha1 : (Δ 1).natAbs ≤ 254 := by omega
  have ha2 : (Δ 2).natAbs ≤ 254 := by omega
  have hsq0 : (Δ 0).natAbs ^ 2 ≤ 254 ^ 2 := Nat.pow_le_pow_left ha0 2
  have hsq1 : (Δ 1).natAbs ^ 2 ≤ 254 ^ 2 := Nat.pow_le_pow_left ha1 2
  have hsq2 : (Δ 2).natAbs ^ 2 ≤ 254 ^ 2 := Nat.pow_le_pow_left ha2 2
  unfold sumNatAbsSq
  rw [Fin.sum_univ_three]
  omega

theorem dampedNorm1sKernelApprox_le_two_mul_coarseBoxRadKernel8 (t : Norm1sTier)
    {ν Δ : Fin 3 → ℤ} (hν : ν ∈ nonzeroBox3D (127 : ℤ))
    (hbox : Δ ∈ box3D (2 * (127 : ℤ))) (hfold : modFold3D 127 Δ = ν) :
    dampedNorm1sKernelApprox t Δ ≤ 2 * coarseBoxRadKernel8 ν := by
  have hν_ne : ν ≠ 0 := ne_zero_of_mem_nonzeroBox3D3 hν
  have hΔ_ne : Δ ≠ 0 := fun h0 ↦ hν_ne (by
    rw [← hfold, h0]; ext w; simp [modFold3D, modFoldCoord, modWrapCoord])
  have hs_pos : 0 < sumNatAbsSq ν := sumNatAbsSq_pos_of_ne_zero hν_ne
  have hs_cap : sumNatAbsSq ν ≤ shellSqCap (shellIndex ν) := sumNatAbsSq_le_shellSqCap ν
  have hs_le : sumNatAbsSq ν ≤ sumNatAbsSq Δ := by
    rw [← hfold]; exact sumNatAbsSq_modFold3D_le 127 hbox
  have hs18 : sumNatAbsSq Δ < 2 ^ 18 := sumNatAbsSq_lt_two_pow_18_of_mem_box3D_254 hbox
  have hμ6 : shellIndex ν ≤ 6 :=
    Nat.lt_succ_iff.mp (shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν)
  let M : ℕ := coarseEnv8Count (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν)
  let S_acc := (Finset.univ : Finset (Fin 256 × Fin (2 ^ 30))).filter
    (fun p ↦ norm1sRadAccept t (shellIndex ν) (sumNatAbsSq Δ) (p.2.val + 2 ^ 30 * p.1.val) = true)
  let S_c8 := (Finset.univ : Finset (Fin 256)).filter (fun c ↦ c.val < M)
  have hsub : S_acc ⊆ S_c8 ×ˢ (Finset.univ : Finset (Fin (2 ^ 30))) := by
    intro p hp
    have hacc := (Finset.mem_filter.mp hp).2
    have hc_lt : p.1.val < M :=
      norm1sRadAccept_imp_coarseEnv8_lt t hμ6 hs_pos hs_cap hs_le hs18 p.1 p.2 hacc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_lt⟩, Finset.mem_univ _⟩
  have hc8_card : S_c8.card ≤ M := by
    calc S_c8.card
        = (S_c8.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.range M).card := Finset.card_le_card (by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hc).2)
      _ = M := Finset.card_range M
  have hcnt_le :
      2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) ≤ M * 2 ^ 30 := by
    rw [← norm1sAcceptCount38_eq]
    calc S_acc.card
        ≤ (S_c8 ×ˢ (Finset.univ : Finset (Fin (2 ^ 30)))).card := Finset.card_le_card hsub
      _ = S_c8.card * 2 ^ 30 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ M * 2 ^ 30 := Nat.mul_le_mul_right _ hc8_card
  unfold dampedNorm1sKernelApprox coarseBoxRadKernel8
  rw [s3IteNeg hΔ_ne, hfold]
  dsimp only
  have hcnt_r :
      ((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) ≤
        (M : ℝ) * (2 : ℝ) ^ 30 := by exact_mod_cast hcnt_le
  have hpow : (2 : ℝ) ^ (2 * shellIndex ν + 38) =
      (2 : ℝ) ^ (2 * shellIndex ν + 8) * (2 : ℝ) ^ 30 := by
    rw [← pow_add]
  have hdiv : ((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ)
      : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν + 38) ≤ (M : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν + 8)
      := by
    rw [hpow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) *
          (2 : ℝ) ^ (2 * shellIndex ν + 8)
        ≤ ((M : ℝ) * (2 : ℝ) ^ 30) * (2 : ℝ) ^ (2 * shellIndex ν + 8) :=
          mul_le_mul_of_nonneg_right hcnt_r (by positivity)
      _ = (M : ℝ) * ((2 : ℝ) ^ (2 * shellIndex ν + 8) * (2 : ℝ) ^ 30) := by ring
  calc (2 / 42 : ℝ) *
        (((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) /
          (2 : ℝ) ^ (2 * shellIndex ν + 38))
      ≤ (2 / 42 : ℝ) * ((M : ℝ) / (2 : ℝ) ^ (2 * shellIndex ν + 8)) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2 / 42)
    _ = 2 * ((1 / 42 : ℝ) *
          (coarseEnv8Count (boxRadConst 36 (1 / 42) 1 (shellIndex ν)) (sumNatAbsSq ν) : ℝ) /
          (2 : ℝ) ^ (2 * shellIndex ν + 8)) := by
        dsimp only [M]; ring

open Classical in
/-- Hardware two's-complement unnormalized 1-sided normalized Slot-3 operator at `Bk = 36`. -/
noncomputable def bTwosNorm1sGen (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.of fun x y ↦ if ProjTwosGridState x ∧
    ProjTwosGridState y ∧ (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3, elecAxisField x
    i w = elecAxisField y i w) then s3SynthStructureFactor216 36 cfg
    (twosMomentum x .projectile - twosMomentum y .projectile) * (dampedNorm1sKernelApprox t
    (twosMomentum x .projectile - twosMomentum y .projectile) : ℂ) else 0

/-- Unit-scaled hardware two's-complement 1-sided normalized Slot-3 block at `Bk = 36`. -/
noncomputable def bUnitTwosNorm1sGen (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  ((alphaSlot3_216 : ℂ)⁻¹) • bTwosNorm1sGen t cfg

open Classical in
/-- Sign-magnitude grid-state operator corresponding to `bTwosNorm1sGen t cfg`. -/
noncomputable def modWrapProjNucOpNorm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.of fun x y ↦ if IsGridState x ∧
    IsGridState y ∧ (∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
      SpecsAux.SpecMirror.momentum x b =
    SpecsAux.SpecMirror.momentum y b) then
      s3SynthStructureFactor216 36 cfg (SpecsAux.SpecMirror.momentum
    x .projectile - SpecsAux.SpecMirror.momentum y .projectile) * (dampedNorm1sKernelApprox t
    (SpecsAux.SpecMirror.momentum x .projectile -
      SpecsAux.SpecMirror.momentum y .projectile) : ℂ) else 0

open Classical in
private theorem norm_projTwosGrid_foldedOp_le
    (G : (Fin 3 → ℤ) → ℂ) (hG0 : G 0 = 0)
    (B : (Fin 3 → ℤ) → ℝ)
    (hB_nn : ∀ ν ∈ nonzeroBox3D (127 : ℤ), 0 ≤ B ν)
    (hG_le : ∀ ν ∈ nonzeroBox3D (127 : ℤ), ∀ Δ ∈ box3D (2 * (127 : ℤ)),
      modFold3D 127 Δ = ν → ‖G Δ‖ ≤ B ν) :
    ‖(Matrix.of fun x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) ↦
      if ProjTwosGridState x ∧ ProjTwosGridState y ∧
          (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
            elecAxisField x i w = elecAxisField y i w) then
        G (twosMomentum x .projectile - twosMomentum y .projectile)
      else 0 : Operator (2 ^ SpecsAux.SpecMirror.systemQubits))‖ ≤
      ∑ ν ∈ nonzeroBox3D (127 : ℤ), B ν := by
  let A : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.of fun x y ↦
    if ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w) then
      G (twosMomentum x .projectile - twosMomentum y .projectile)
    else 0
  let M_val : (Fin 3 → ℤ) → Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := fun ν ↦
    Matrix.of fun x y ↦
      if ProjTwosGridState x ∧ ProjTwosGridState y ∧
          (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
            elecAxisField x i w = elecAxisField y i w) ∧
          modFold3D 127 (twosMomentum x .projectile - twosMomentum y .projectile) = ν then
        G (twosMomentum x .projectile - twosMomentum y .projectile)
      else 0
  have hsub_box {x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)}
      (hx : ProjTwosGridState x) (hy : ProjTwosGridState y) :
      twosMomentum x .projectile - twosMomentum y .projectile ∈ box3D (2 * (127 : ℤ)) :=
    mk_mem_box3D3 fun w ↦ by
      have := bounds_of_mem_box3D3 (twosMomentum_proj_mem_box3D_127 hx) w
      have := bounds_of_mem_box3D3 (twosMomentum_proj_mem_box3D_127 hy) w
      dsimp
      omega
  have hpart : A = ∑ ν ∈ nonzeroBox3D (127 : ℤ), M_val ν := by
    ext x y
    dsimp only [A]
    rw [operator_sum_apply, Matrix.of_apply]
    by_cases hcond : ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w)
    · rw [ite_true_eq hcond]
      set Δ : Fin 3 → ℤ := twosMomentum x .projectile - twosMomentum y .projectile
      by_cases hΔ : Δ = 0
      · have hfold0 : modFold3D 127 Δ = 0 := by
          rw [hΔ]
          ext w
          simp [modFold3D, modFoldCoord, modWrapCoord]
        rw [Finset.sum_eq_zero (fun ν hν ↦ by
          dsimp [M_val]
          rw [ite_false_eq]
          rintro ⟨_, _, _, heq⟩
          exact (ne_zero_of_mem_nonzeroBox3D3 hν) (heq.symm.trans hfold0)), hΔ, hG0]
      · have hmem : modFold3D 127 Δ ∈ nonzeroBox3D (127 : ℤ) :=
          modFold3D_mem_nonzeroBox3D 127
            (mk_mem_nonzeroBox3D3 hΔ (bounds_of_mem_box3D3 (hsub_box hcond.1 hcond.2.1)))
        rw [Finset.sum_eq_single (modFold3D 127 Δ)
          (fun ν _ hne ↦ by
            dsimp [M_val]
            rw [ite_false_eq]
            rintro ⟨_, _, _, heq⟩
            exact hne heq.symm)
          (fun hnot ↦ (hnot hmem).elim)]
        dsimp [M_val]
        rw [ite_true_eq ⟨hcond.1, hcond.2.1, hcond.2.2, rfl⟩]
    · rw [ite_false_eq hcond, eq_comm]
      refine Finset.sum_eq_zero fun ν _ ↦ ?_
      dsimp [M_val]
      rw [ite_false_eq]
      rintro ⟨h1, h2, h3, _⟩
      exact hcond ⟨h1, h2, h3⟩
  change ‖A‖ ≤ _
  rw [hpart]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν hν_mem ↦ ?_)
  have hM_nz {x y} (h : M_val ν x y ≠ 0) :
      ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w) ∧
        modFold3D 127 (twosMomentum x .projectile - twosMomentum y .projectile) = ν := by
    dsimp [M_val] at h
    split_ifs at h with hc
    · exact hc
    · exact (h rfl).elim
  apply norm_le_of_weightedPartialPerm (M_val ν) (hB_nn ν hν_mem)
  · intro x y₁ y₂ h1 h2
    obtain ⟨hx, hy1, he1, hm1⟩ := hM_nz h1
    obtain ⟨_, hy2, he2, hm2⟩ := hM_nz h2
    have hp_eq := modFold3D_sub_inj_right 127 (twosMomentum_proj_mem_box3D_127 hx)
      (twosMomentum_proj_mem_box3D_127 hy1) (twosMomentum_proj_mem_box3D_127 hy2)
      (hm1.trans hm2.symm)
    exact systemQubits_eq_of_fields (fun i w ↦ (he1 i w).symm.trans (he2 i w))
      (fun w ↦ twosComp8Int_injective (congrFun hp_eq w))
  · intro x₁ x₂ y h1 h2
    obtain ⟨hx1, hy, he1, hm1⟩ := hM_nz h1
    obtain ⟨hx2, _, he2, hm2⟩ := hM_nz h2
    have hp_eq := modFold3D_sub_inj_left 127 (twosMomentum_proj_mem_box3D_127 hx1)
      (twosMomentum_proj_mem_box3D_127 hx2) (twosMomentum_proj_mem_box3D_127 hy)
      (hm1.trans hm2.symm)
    exact systemQubits_eq_of_fields (fun i w ↦ (he1 i w).trans (he2 i w).symm)
      (fun w ↦ twosComp8Int_injective (congrFun hp_eq w))
  · intro x y
    dsimp [M_val]
    clear hM_nz M_val hpart A
    split_ifs with hc
    · exact hG_le ν hν_mem _ (hsub_box hc.1 hc.2.1) hc.2.2.2
    · rw [norm_zero]
      exact hB_nn ν hν_mem

open Classical in
theorem norm_s3ProjWeightedOpNorm1s_le (t : Norm1sTier)
    (F : (Fin 3 → ℤ) → ℂ) (C : ℝ) (hC_nn : 0 ≤ C)
    (hF_le : ∀ Δ : Fin 3 → ℤ, ‖F Δ‖ ≤ C) :
    let A : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.of fun x y ↦ if
        ProjTwosGridState x ∧ ProjTwosGridState y ∧ (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w
        : Fin 3, elecAxisField x i w = elecAxisField y i w) then F
        (twosMomentum x .projectile - twosMomentum y .projectile) * (dampedNorm1sKernelApprox
        t (twosMomentum x .projectile - twosMomentum y .projectile) : ℂ) else 0
    ‖A‖ ≤ (8192 * C * (2 / 42 : ℝ)) * coulombCoarse8PreOAAProb 127 8192 := by
  intro A
  have h1 : ‖A‖ ≤ ∑ ν ∈ nonzeroBox3D (127 : ℤ), C * (2 * coarseBoxRadKernel8 ν) := by
    refine norm_projTwosGrid_foldedOp_le
      (fun Δ ↦ F Δ * (dampedNorm1sKernelApprox t Δ : ℂ))
      (by simp [dampedNorm1sKernelApprox_zero])
      (fun ν ↦ C * (2 * coarseBoxRadKernel8 ν))
      (fun ν _ ↦ mul_nonneg hC_nn (by unfold coarseBoxRadKernel8; positivity))
      fun ν hν_mem Δ hsub_box hfold ↦ ?_
    have hk_nn : 0 ≤ dampedNorm1sKernelApprox t Δ := dampedNorm1sKernelApprox_nonneg t Δ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk_nn]
    exact mul_le_mul (hF_le Δ)
      (dampedNorm1sKernelApprox_le_two_mul_coarseBoxRadKernel8 t hν_mem hsub_box hfold) hk_nn hC_nn
  refine h1.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold coulombCoarse8PreOAAProb
  ring

theorem norm_bTwosNorm1sGen_le_alphaSlot3_216 (t : Norm1sTier) (cfg :
    SpecsAux.SpecMirror.Configuration) :
    ‖bTwosNorm1sGen t cfg‖ ≤ alphaSlot3_216 :=
  (norm_s3ProjWeightedOpNorm1s_le t (s3SynthStructureFactor216 36 cfg) 216 (by positivity)
    (norm_s3SynthStructureFactor216_le_216 36 cfg)).trans slot3_216_alpha_cheb_step

theorem norm_bUnitTwosNorm1sGen_le_one (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    ‖bUnitTwosNorm1sGen t cfg‖ ≤ 1 := by
  unfold bUnitTwosNorm1sGen
  have hpos := alphaSlot3_216_pos_and_le_20123.1
  have hinv_eq : ((alphaSlot3_216 : ℂ)⁻¹) = ((alphaSlot3_216⁻¹ : ℝ) : ℂ) :=
    (Complex.ofReal_inv alphaSlot3_216).symm
  rw [hinv_eq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_mul_le_iff₀ hpos).mpr
    (by simpa only [mul_one] using norm_bTwosNorm1sGen_le_alphaSlot3_216 t cfg)

theorem modWrapProjNucOpNorm1s_permElectron (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) (g : Equiv.Perm (Fin
      SpecsAux.SpecMirror.numElectrons))
    (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : modWrapProjNucOpNorm1s t cfg
    (BridgeFermionicComm.SpecInner.permElectron g x)
    (BridgeFermionicComm.SpecInner.permElectron g y) = modWrapProjNucOpNorm1s t cfg x y
    := by
  classical
  simp only [modWrapProjNucOpNorm1s, Matrix.of_apply,
    BridgeFermionicComm.SpecInner.isGridState_permElectron,
    BridgeFermionicComm.SpecInner.momentum_permElectron_projectile]
  have hcond : (∀ b ≠ SpecsAux.SpecMirror.Particle.projectile, SpecsAux.SpecMirror.momentum
      (BridgeFermionicComm.SpecInner.permElectron g x) b = SpecsAux.SpecMirror.momentum
      (BridgeFermionicComm.SpecInner.permElectron g y) b) ↔ (∀ b ≠
      SpecsAux.SpecMirror.Particle.projectile,
        SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y
      b) := by
    constructor
    · intro h b hb
      cases b with
      | electron i =>
        have h' := h (.electron (g.symm i)) (by simp)
        simpa [BridgeFermionicComm.SpecInner.momentum_permElectron_electron] using h'
      | projectile => exact (hb rfl).elim
    · intro h b hb
      cases b with
      | electron i =>
        simp only [BridgeFermionicComm.SpecInner.momentum_permElectron_electron]
        exact h (.electron (g i)) (by simp)
      | projectile => exact (hb rfl).elim
  simp only [hcond]

theorem smToTwosSysUnitary_conj_bTwosNorm1sGen_on_grid (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) {x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)}
    (hx : IsGridState x) (hy : IsGridState y) :
    (smToTwosSysUnitary.1 * bTwosNorm1sGen t cfg * smToTwosSysUnitary.1) x y =
    modWrapProjNucOpNorm1s t cfg x y := by
  classical
  have hentry : ∀ a b,
      (TwosCompAndWire0Cancel.fwdPermUnitary TwosCompAndWire0Cancel.smToTwosSysPerm).1 a b =
        if TwosCompAndWire0Cancel.smToTwosSysPerm b = a then 1 else 0 :=
    TwosCompAndWire0Cancel.fwdPermUnitary_apply TwosCompAndWire0Cancel.smToTwosSysPerm
  change ((TwosCompAndWire0Cancel.fwdPermUnitary TwosCompAndWire0Cancel.smToTwosSysPerm).1 *
      bTwosNorm1sGen t cfg *
      (TwosCompAndWire0Cancel.fwdPermUnitary TwosCompAndWire0Cancel.smToTwosSysPerm).1) x y = _
  rw [Matrix.mul_apply, Finset.sum_eq_single (TwosCompAndWire0Cancel.smToTwosSysPerm y)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (TwosCompAndWire0Cancel.smToTwosSysPerm x)]
    · have h1 : (TwosCompAndWire0Cancel.fwdPermUnitary TwosCompAndWire0Cancel.smToTwosSysPerm).1
          x (TwosCompAndWire0Cancel.smToTwosSysPerm x) = 1 := by
        rw [hentry, ite_true_eq (TwosCompAndWire0Cancel.smToTwosSysPerm_self x)]
      have h2 : (TwosCompAndWire0Cancel.fwdPermUnitary TwosCompAndWire0Cancel.smToTwosSysPerm).1
          (TwosCompAndWire0Cancel.smToTwosSysPerm y) y = 1 := by
        rw [hentry, ite_true_eq rfl]
      rw [h1, h2, one_mul, mul_one]
      have hpx : ProjTwosGridState (TwosCompAndWire0Cancel.smToTwosSysPerm x) :=
        ((isTwosGridState_smToTwosSysPerm_iff x).mpr hx).2
      have hpy : ProjTwosGridState (TwosCompAndWire0Cancel.smToTwosSysPerm y) :=
        ((isTwosGridState_smToTwosSysPerm_iff y).mpr hy).2
      have hmx : ∀ d,
        twosMomentum (TwosCompAndWire0Cancel.smToTwosSysPerm x) d =
        SpecsAux.SpecMirror.momentum x d :=
        Slot5MatrixAndScaleCert.twosMomentum_smToTwosSysPerm hx
      have hmy : ∀ d,
        twosMomentum (TwosCompAndWire0Cancel.smToTwosSysPerm y) d =
        SpecsAux.SpecMirror.momentum y d :=
        Slot5MatrixAndScaleCert.twosMomentum_smToTwosSysPerm hy
      have he_iff : (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3, elecAxisField
          (TwosCompAndWire0Cancel.smToTwosSysPerm x) i w = elecAxisField
          (TwosCompAndWire0Cancel.smToTwosSysPerm y) i w) ↔ (∀ b ≠
          SpecsAux.SpecMirror.Particle.projectile, SpecsAux.SpecMirror.momentum x b =
          SpecsAux.SpecMirror.momentum y b) := by
        constructor
        · intro he b hb
          cases b with
          | projectile => exact (hb rfl).elim
          | electron i =>
              rw [← hmx (.electron i), ← hmy (.electron i)]
              ext w
              dsimp [twosMomentum]
              rw [he i w]
        · intro hm i w
          have hmi : twosMomentum (TwosCompAndWire0Cancel.smToTwosSysPerm x) (.electron i) =
              twosMomentum (TwosCompAndWire0Cancel.smToTwosSysPerm y) (.electron i) := by
            rw [hmx, hmy]
            exact hm (.electron i) (fun h ↦ SpecsAux.SpecMirror.Particle.noConfusion h)
          exact twosComp6Int_injective (congrFun hmi w)
      unfold bTwosNorm1sGen modWrapProjNucOpNorm1s
      rw [Matrix.of_apply, Matrix.of_apply]
      by_cases he : ∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
          SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y b
      · rw [ite_true_eq ⟨hpx, hpy, he_iff.mpr he⟩, ite_true_eq ⟨hx, hy, he⟩,
          hmx .projectile, hmy .projectile]
      · have hnotL : ¬(ProjTwosGridState (TwosCompAndWire0Cancel.smToTwosSysPerm x) ∧
            ProjTwosGridState (TwosCompAndWire0Cancel.smToTwosSysPerm y) ∧
            ∀ i w, elecAxisField (TwosCompAndWire0Cancel.smToTwosSysPerm x) i w =
              elecAxisField (TwosCompAndWire0Cancel.smToTwosSysPerm y) i w) := fun hc ↦
                he (he_iff.mp hc.2.2)
        have hnotR : ¬(IsGridState x ∧ IsGridState y ∧
            ∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
              SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y b) := fun hc ↦
                he hc.2.2
        rw [ite_false_eq hnotL, ite_false_eq hnotR]
    · intro a _ ha
      have hne : ¬(TwosCompAndWire0Cancel.smToTwosSysPerm a = x) := fun heq ↦
        ha (by rw [← heq, TwosCompAndWire0Cancel.smToTwosSysPerm_self a])
      rw [hentry, ite_false_eq hne, zero_mul]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  · intro b _ hb
    rw [hentry, ite_false_eq hb.symm, mul_zero]
  · intro hm; exact (hm (Finset.mem_univ _)).elim

theorem bUnitTwosNorm1sGen_permSm (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (g : Equiv.Perm (Fin SpecsAux.SpecMirror.numElectrons))
    (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (hx : IsGridState x) (hy : IsGridState y) :
    (smToTwosSysUnitary.1 * bUnitTwosNorm1sGen t cfg * smToTwosSysUnitary.1)
    (BridgeFermionicComm.SpecInner.permElectron g x)
    (BridgeFermionicComm.SpecInner.permElectron g y) = (smToTwosSysUnitary.1 *
    bUnitTwosNorm1sGen t cfg * smToTwosSysUnitary.1) x y := by
  have hgx : IsGridState (BridgeFermionicComm.SpecInner.permElectron g x) :=
    (BridgeFermionicComm.SpecInner.isGridState_permElectron g x).mpr hx
  have hgy : IsGridState (BridgeFermionicComm.SpecInner.permElectron g y) :=
    (BridgeFermionicComm.SpecInner.isGridState_permElectron g y).mpr hy
  unfold bUnitTwosNorm1sGen
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.smul_apply,
    smToTwosSysUnitary_conj_bTwosNorm1sGen_on_grid t cfg hgx hgy,
    smToTwosSysUnitary_conj_bTwosNorm1sGen_on_grid t cfg hx hy,
    modWrapProjNucOpNorm1s_permElectron t cfg g x y]

private theorem s3ProjStepHw_of_validShellNu3 {p : Fin (2 ^ 8)} (hp : p.val ≠ 128)
    {u22 : Fin (2 ^ 22)} {s3 : Fin (2 ^ 3)} (hv : validShellNu3 u22 s3 = true) (w : Fin 3) :
    let res := s3ProjStepHw p (shellMagCoord3 u22 w) (signBit3 s3 w)
    res.1.val ≠ 128 ∧
      twosComp8Int res.1 = modWrapCoord 127 (twosComp8Int p) (decodeShellNu3 u22 s3 w) ∧
      res.2.1 = (twosComp8Int res.1 - twosComp8Int p).natAbs := by
  have hng : ¬(shellMagCoord3 u22 w = 0 ∧ signBit3 s3 w = 1) := by
    unfold validShellNu3 at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.2 w
  rcases s3ProjStepHw_spec hp (s3ShellMagCoord3_lt_128 u22 w) (s3SignBit3_le_one s3 w) hng
    with ⟨h1, h2, _, _, _, h6⟩
  exact ⟨h1, h2, h6⟩

theorem s3AcceptNorm1s_imp_coarseGood3_one (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {z : Fin (2 ^ (momCoreWires mPayload))} (hz : s3AcceptNorm1s t hmPay z = true) :
    let tup := coarse33Equiv ((s3Coarse33Core hmPay).extractIndex z)
    coarseGood3 tup.1 tup.2.1 tup.2.2 = true := by
  intro tup
  dsimp only [tup]
  rw [coarse33Equiv_s3Coarse33Core hmPay z]
  let xSys := (momSysReg mPayload).extractIndex z
  let u22 := (s3U22Core hmPay).extractIndex z
  let s3 := (s3S3Core hmPay).extractIndex z
  let c8 := (s3C8Core hmPay).extractIndex z
  let f30 := (s3Fine30Core hmPay).extractIndex z
  let st := fun w : Fin 3 ↦
    s3ProjStepHw (projAxisField xSys w) (shellMagCoord3 u22 w) (signBit3 s3 w)
  have hacc : s3AcceptNorm1s t hmPay z = true := hz
  unfold s3AcceptNorm1s at hacc
  rcases s3And4.mp hacc with ⟨_, hgridB, hv, hrad⟩
  have hgrid : ProjTwosGridState xSys := (s3ProjGridBool_eq_true_iff xSys).mp hgridB
  let ν := decodeShellNu3 u22 s3
  rcases decodeShellNu3_mem_and_shellIndex hv with ⟨hν_mem, hμ_eq⟩
  have hν_ne : ν ≠ 0 := ne_zero_of_mem_nonzeroBox3D3 hν_mem
  have hs_pos : 0 < sumNatAbsSq ν := sumNatAbsSq_pos_of_ne_zero hν_ne
  have hs_cap : sumNatAbsSq ν ≤ shellSqCap (shellIndex ν) := sumNatAbsSq_le_shellSqCap ν
  have hax : ∀ w : Fin 3,
      modFoldCoord 127 (twosComp8Int (st w).1 - twosComp8Int (projAxisField xSys w)) = ν w ∧
      (st w).2.1 = (twosComp8Int (st w).1 - twosComp8Int (projAxisField xSys w)).natAbs ∧
      |twosComp8Int (st w).1 - twosComp8Int (projAxisField xSys w)| ≤ 254 := by
    intro w
    rcases s3ProjStepHw_of_validShellNu3 (hgrid w) hv w with ⟨hst_ne, hwrap, hd_eq⟩
    have hb_bds := twosComp8Int_bounds_of_ne128 (hgrid w)
    have ha_bds := twosComp8Int_bounds_of_ne128 hst_ne
    have hν_bds := s3DecodeShellNu3_bounds u22 s3 w
    exact ⟨(modWrapCoord127_eq_iff_modFoldCoord ha_bds hb_bds hν_bds).mp hwrap, hd_eq,
      s3TwosComp8Int_sub_abs_le hst_ne (hgrid w)⟩
  let Δ : Fin 3 → ℤ := fun w ↦ twosComp8Int (st w).1 - twosComp8Int (projAxisField xSys w)
  have hfoldΔ : modFold3D 127 Δ = ν := funext fun w ↦ (hax w).1
  have hboxΔ : Δ ∈ box3D (2 * (127 : ℤ)) := mk_mem_box3D3 fun w ↦ abs_le.mp (hax w).2.2
  have hsTrue_eq : (st 0).2.1 * (st 0).2.1 + (st 1).2.1 * (st 1).2.1 + (st 2).2.1 * (st 2).2.1 =
      sumNatAbsSq Δ := by
    unfold sumNatAbsSq
    rw [Fin.sum_univ_three, (hax 0).2.1, (hax 1).2.1, (hax 2).2.1]
    ring
  have hdom : sumNatAbsSq ν ≤ sumNatAbsSq Δ := by
    rw [← hfoldΔ]; exact sumNatAbsSq_modFold3D_le 127 hboxΔ
  have hs18 : sumNatAbsSq Δ < 2 ^ 18 := sumNatAbsSq_lt_two_pow_18_of_mem_box3D_254 hboxΔ
  have hμ6 : shellIndex ν ≤ 6 :=
    Nat.lt_succ_iff.mp (shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν_mem)
  change norm1sRadAccept t (shellMu3 u22) ((st 0).2.1 * (st 0).2.1 + (st 1).2.1 * (st 1).2.1 +
    (st 2).2.1 * (st 2).2.1) (f30.val + 2 ^ 30 * c8.val) = true at hrad
  rw [hsTrue_eq, ← hμ_eq] at hrad
  have hc8_lt : c8.val < coarseEnv8Count (boxRadConst 36 (1 /
    42) 1 (shellIndex ν)) (sumNatAbsSq ν) :=
    norm1sRadAccept_imp_coarseEnv8_lt t hμ6 hs_pos hs_cap hdom hs18 c8 f30 hrad
  unfold coarseGood3
  rw [hv, Bool.true_and, decide_eq_true_eq]
  exact hc8_lt

theorem s3AcceptNorm1s_imp_coarseGood3_both (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {z : Fin (2 ^ (momCoreWires mPayload))} (hz : s3AcceptNorm1s t hmPay z = true) :
    let tup := coarse33Equiv ((s3Coarse33Core hmPay).extractIndex z)
    let tup' := coarse33Equiv ((s3Coarse33Core hmPay).extractIndex (s3CoreMapNorm1s t hmPay z))
    coarseGood3 tup.1 tup.2.1 tup.2.2 = true ∧ coarseGood3 tup'.1 tup'.2.1 tup'.2.2 = true :=
  ⟨s3AcceptNorm1s_imp_coarseGood3_one t hmPay hz,
    s3AcceptNorm1s_imp_coarseGood3_one t hmPay ((s3AcceptNorm1s_and_involutive t hmPay z).1.trans
      hz)⟩

theorem s3TopBlockNorm1s_rejected_sum_zero (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (g₁ g₂ : Fin (2 ^ (momCoreWires mPayload)))
    (hg1 : (momAncReg mPayload).extractIndex g₁ =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3))
    (hg2 : (momAncReg mPayload).extractIndex g₂ =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) :
    let W : Unitary (2 ^ (momCoreWires mPayload)) := uPrep3_216 hmPay * coreHadamardMom mPayload
    let corePh : Fin (2 ^ (momCoreWires mPayload)) → ℂ := fun z ↦
      ((s3RejPhaseNorm1s t hmPay z : ℝ) : ℂ) *
        dyadicTurn 48 (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) z) : ℤ)
    let term : Fin (2 ^ (momCoreWires mPayload)) → ℂ := fun z ↦
      star (W.1 (s3CoreMapNorm1s t hmPay z) g₁) * corePh z * W.1 z g₂
    (∑ z ∈ Finset.univ.filter (fun z ↦ ¬(s3AcceptNorm1s t hmPay z = true)), term z) = 0 := by
  intro W corePh term
  let u₀ := coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)
  set S := Finset.univ.filter
    (fun z : Fin (2 ^ (momCoreWires mPayload)) ↦ ¬(s3AcceptNorm1s t hmPay z = true))
  have hvBp : (s3BParCore hmPay).val = 4017 := rfl
  have hbits_ne : ∀ (z : Fin (2 ^ (momCoreWires mPayload))) (w : Wire (momCoreWires mPayload)),
      w ≠ s3BParCore hmPay →
      basisBits (momCoreWires mPayload) (s3FlipBParPerm hmPay z) w =
        basisBits (momCoreWires mPayload) z w := fun z w hw ↦ by
    rw [basisBits_s3FlipBParPerm, Function.update_of_ne hw]
  have hext_ne : ∀ (z : Fin (2 ^ (momCoreWires mPayload))) {q : ℕ}
      (r : QRegister q (momCoreWires mPayload)),
      (∀ b : Fin q, (r b).val ≠ 4017) →
      r.extractIndex (s3FlipBParPerm hmPay z) = r.extractIndex z := fun z {_} r hne ↦ by
    apply (basisBitsEquiv _).injective
    funext b
    change basisBits _ _ b = basisBits _ _ b
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    exact hbits_ne z (r b) fun h ↦ hne b (by rw [congrArg Fin.val h, hvBp])
  have hCoin_flip (z) := hext_ne z (momCoinReg mPayload) fun b ↦ by
    have := b.isLt
    change 3948 + b.val ≠ 4017
    omega
  have hFlipMem : ∀ z, z ∈ S → s3FlipBParPerm hmPay z ∈ S := fun z hzS ↦ by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    unfold s3AcceptNorm1s
    dsimp only
    rw [hCoin_flip z,
      hext_ne z (momSysReg mPayload) (fun b ↦ by
        have := b.isLt
        have := s3SysQubits_eq
        change 0 + b.val ≠ 4017
        omega),
      hext_ne z (s3U22Core hmPay) (fun b ↦ by have := b.isLt; change 3954 + b.val ≠ 4017; omega),
      hext_ne z (s3S3Core hmPay) (fun b ↦ by have := b.isLt; change 3976 + b.val ≠ 4017; omega),
      hext_ne z (s3C8Core hmPay) (fun b ↦ by have := b.isLt; change 3979 + b.val ≠ 4017; omega),
      hext_ne z (s3Fine30Core hmPay) (fun b ↦ by
        have := b.isLt
        change 3987 + b.val ≠ 4017
        omega)]
    exact (Finset.mem_filter.mp hzS).2
  have hNegTerm : ∀ z ∈ S, term (s3FlipBParPerm hmPay z) = -term z := by
    intro z hzS
    have hzRej := (Finset.mem_filter.mp hzS).2
    have hzfRej := (Finset.mem_filter.mp (hFlipMem z hzS)).2
    have hmap {u} (hu : ¬(s3AcceptNorm1s t hmPay u = true)) :
        s3CoreMapNorm1s t hmPay u = u := by
      unfold s3CoreMapNorm1s
      rw [s3IteNeg hu]
    have hW_same : ∀ g, (momAncReg mPayload).extractIndex g = u₀ →
        W.1 (s3FlipBParPerm hmPay z) g = W.1 z g := fun g hg ↦ by
      dsimp only [W]
      rw [uPrep3_216_mul_coreHadamard_apply hmPay _ g hg,
        uPrep3_216_mul_coreHadamard_apply hmPay _ g hg]
      have hpref : s3SamePrefix3954 (s3FlipBParPerm hmPay z) g ↔ s3SamePrefix3954 z g :=
        forall₂_congr fun w hw ↦ by
          rw [hbits_ne z w (fun h ↦ by have hv := congrArg Fin.val h; rw [hvBp] at hv; omega)]
      rw [hext_ne z (s3Coarse33Core hmPay) (fun b ↦ by
            have := b.isLt; dsimp [s3Coarse33Core, s3Qreg_block_apply]; omega),
          s3QutritFactor_congr_u16 hmPay (hext_ne z (s3U16Core hmPay) fun b ↦ by
            change 4018 + b.val ≠ 4017; omega)]
      by_cases hp : s3SamePrefix3954 z g
      · rw [s3ItePos (hpref.mpr hp), s3ItePos hp]
      · rw [s3IteNeg (fun h ↦ hp (hpref.mp h)), s3IteNeg hp]
    by_cases hp2 : s3SamePrefix3954 z g₂
    · have hc6 : ((momCoinReg mPayload).extractIndex z).val = 6 :=
        congrArg Fin.val ((s3SamePrefix3954_coin6_iff hmPay hg2).mp hp2).2.1
      have hc6' : ((momCoinReg mPayload).extractIndex (s3FlipBParPerm hmPay z)).val = 6 :=
        (congrArg Fin.val (hCoin_flip z)).trans hc6
      have hph : corePh (s3FlipBParPerm hmPay z) = -corePh z := by
        dsimp only [corePh]
        rw [s3DyadicTurn_shift48_36_eq, s3DyadicTurn_shift48_36_eq,
          s3IteNeg hzfRej, s3IteNeg hzRej, mul_one, mul_one]
        unfold s3RejPhaseNorm1s
        rw [s3ItePos (P := _ ∧ _) ⟨hc6', Bool.eq_false_iff.mpr hzfRej⟩,
          s3ItePos (P := _ ∧ _) ⟨hc6, Bool.eq_false_iff.mpr hzRej⟩,
          basisBits_s3FlipBParPerm, Function.update_self]
        rcases Slot3CleanPrim.zmod2_eq_or
            (basisBits (momCoreWires mPayload) z (s3BParCore hmPay)) with hb | hb
        · rw [hb, show (0 : ZMod 2) + 1 = 1 from rfl]
          simp
        · rw [hb, show (1 : ZMod 2) + 1 = 0 from by decide]
          simp
      dsimp only [term]
      rw [hmap hzRej, hmap hzfRej, hW_same g₁ hg1, hW_same g₂ hg2, hph]
      ring
    · have hW0 : W.1 z g₂ = 0 := by
        dsimp only [W]
        rw [uPrep3_216_mul_coreHadamard_apply hmPay z g₂ hg2, s3IteNeg hp2]
      dsimp only [term]
      rw [hmap hzRej, hmap hzfRej, hW_same g₂ hg2, hW0]
      ring
  exact s3Sum_zero_of_neg_involution S (s3FlipBParPerm hmPay) term
    (fun b ↦ (s3FlipBParPerm hmPay).left_inv b) hFlipMem hNegTerm

/-- Accepted kinematic predicate for 1-sided normalized Slot-3 transitions on `(u22, s3, c8,
  f30)`. -/
def s3KinOKNorm1s (t : Norm1sTier) (x₁ x₂ : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256) (f30 : Fin (2 ^ 30)) : Prop :=
  let st := fun w : Fin 3 ↦ s3ProjStepHw (projAxisField x₂ w) (shellMagCoord3 u22 w) (signBit3 s3 w)
  ProjTwosGridState x₂ ∧
    validShellNu3 u22 s3 = true ∧
    norm1sRadAccept t (shellMu3 u22)
      ((st 0).2.1 * (st 0).2.1 + (st 1).2.1 * (st 1).2.1 + (st 2).2.1 * (st 2).2.1)
      (f30.val + 2 ^ 30 * c8.val) = true ∧
    s3UpdateSysProj x₂ (fun w ↦ (st w).1) = x₁

theorem s3RealComplexKernelNorm1s_eq (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (Δ : Fin 3 → ℤ) (hΔ_ne : Δ ≠ 0) (hμ7 : shellIndex (modFold3D 127 Δ) < 7) :
    let ν₀ : Fin 3 → ℤ := modFold3D 127 Δ
    let cnt38 : ℕ := 2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν₀) (sumNatAbsSq Δ)
    (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
      (((2 ^ (12 - 2 * shellIndex ν₀) * cnt38 : ℕ) : ℂ)) *
      ((((16384 / 27 : ℝ) : ℂ)) * s3SynthStructureFactor216 36 cfg Δ) =
    (alphaSlot3_216 : ℂ)⁻¹ •
      (s3SynthStructureFactor216 36 cfg Δ *
        (dampedNorm1sKernelApprox t Δ : ℂ)) := by
  intro ν₀ cnt38
  have hRealKernel : (boost127_coarse8_w13 / (2 : ℝ) ^ 80) *
      ((2 ^ (12 - 2 * shellIndex ν₀) * cnt38 : ℕ) : ℝ) * (16384 / 27 : ℝ) = alphaSlot3_216⁻¹ *
      dampedNorm1sKernelApprox t Δ := by
    unfold dampedNorm1sKernelApprox alphaSlot3_216
    rw [s3IteNeg hΔ_ne]
    dsimp only
    have hb_pos : 0 < boost127_coarse8_w13 := by
      by_contra hle
      have hle0 : alphaSlot3_216 ≤ 0 := by
        unfold alphaSlot3_216
        exact div_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hle)
      linarith [alphaSlot3_216_pos_and_le_20123.1]
    have hpow_split : (2 : ℝ) ^ (12 - 2 * shellIndex ν₀) * (2 : ℝ) ^ (2 * shellIndex ν₀ + 38) =
        (2 : ℝ) ^ 50 := by
      rw [← pow_add]; congr 1; dsimp only [ν₀]; omega
    dsimp only [cnt38, ν₀] at hpow_split ⊢
    push_cast
    field_simp [hb_pos.ne', pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
    calc (2 : ℝ) ^ (12 - 2 * shellIndex (modFold3D 127 Δ)) *
          (norm1sAcceptCountK t (shellIndex (modFold3D 127 Δ)) (sumNatAbsSq Δ) : ℝ) *
          16384 * 8192 * 216 * (2 : ℝ) ^ (2 * shellIndex (modFold3D 127 Δ) + 38)
        = ((2 : ℝ) ^ (12 - 2 * shellIndex (modFold3D 127 Δ)) *
            (2 : ℝ) ^ (2 * shellIndex (modFold3D 127 Δ) + 38)) *
          (16384 * 8192 * 216 *
            (norm1sAcceptCountK t (shellIndex (modFold3D 127 Δ)) (sumNatAbsSq Δ) : ℝ)) := by ring
      _ = (2 : ℝ) ^ 50 *
          (16384 * 8192 * 216 *
            (norm1sAcceptCountK t (shellIndex (modFold3D 127 Δ)) (sumNatAbsSq Δ) : ℝ)) := by
          rw [hpow_split]
      _ = (2 : ℝ) ^ 80 *
          (norm1sAcceptCountK t (shellIndex (modFold3D 127 Δ)) (sumNatAbsSq Δ) : ℝ) * 27 := by ring
  have h1 : (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
      (((2 ^ (12 - 2 * shellIndex ν₀) * cnt38 : ℕ) : ℂ)) * (((16384 / 27 : ℝ) : ℂ)) =
      (((alphaSlot3_216⁻¹ * dampedNorm1sKernelApprox t Δ : ℝ) : ℂ)) := by
    exact_mod_cast hRealKernel
  change (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
    (((2 ^ (12 - 2 * shellIndex ν₀) * cnt38 : ℕ) : ℂ)) *
    ((((16384 / 27 : ℝ) : ℂ)) * s3SynthStructureFactor216 36 cfg Δ) = (alphaSlot3_216 : ℂ)⁻¹ *
    (s3SynthStructureFactor216 36 cfg Δ * (dampedNorm1sKernelApprox t Δ : ℂ))
  calc (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
        (((2 ^ (12 - 2 * shellIndex ν₀) * cnt38 : ℕ) : ℂ)) *
        ((((16384 / 27 : ℝ) : ℂ)) * s3SynthStructureFactor216 36 cfg Δ)
      = ((((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
          (((2 ^ (12 - 2 * shellIndex ν₀) * cnt38 : ℕ) : ℂ)) * (((16384 / 27 : ℝ) : ℂ))) *
          s3SynthStructureFactor216 36 cfg Δ := by ring
    _ = (((alphaSlot3_216⁻¹ * dampedNorm1sKernelApprox t Δ : ℝ) : ℂ)) *
          s3SynthStructureFactor216 36 cfg Δ := by rw [h1]
    _ = (alphaSlot3_216 : ℂ)⁻¹ *
          (s3SynthStructureFactor216 36 cfg Δ * (dampedNorm1sKernelApprox t Δ : ℂ)) := by
          push_cast; ring

theorem s3KinOKNorm1s_iff_of_condProj (t : Norm1sTier)
    {x₁ x₂ : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)}
    (hx1 : ProjTwosGridState x₁) (hx2 : ProjTwosGridState x₂)
    (heEq : ∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
      elecAxisField x₁ i w = elecAxisField x₂ i w)
    (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256) (f30 : Fin (2 ^ 30)) :
    let Δ := twosMomentum x₁ .projectile - twosMomentum x₂ .projectile
    let ν₀ := modFold3D 127 Δ
    s3KinOKNorm1s t x₁ x₂ u22 s3 c8 f30 ↔
      (validShellNu3 u22 s3 = true ∧ decodeShellNu3 u22 s3 = ν₀) ∧
      norm1sRadAccept t (shellIndex ν₀) (sumNatAbsSq Δ) (f30.val + 2 ^ 30 * c8.val) = true := by
  intro Δ ν₀
  unfold s3KinOKNorm1s
  dsimp only
  let st := fun w : Fin 3 ↦ s3ProjStepHw (projAxisField x₂ w) (shellMagCoord3 u22 w) (signBit3 s3 w)
  have hrad_eq (hv : validShellNu3 u22 s3 = true) (hdec : decodeShellNu3 u22 s3 = ν₀)
      (hd : ∀ w : Fin 3, (st w).2.1 = (Δ w).natAbs) :
      norm1sRadAccept t (shellMu3 u22)
        ((st 0).2.1 * (st 0).2.1 + (st 1).2.1 * (st 1).2.1 + (st 2).2.1 * (st 2).2.1)
        (f30.val + 2 ^ 30 * c8.val) =
      norm1sRadAccept t (shellIndex ν₀) (sumNatAbsSq Δ) (f30.val + 2 ^ 30 * c8.val) := by
    have hs : (st 0).2.1 * (st 0).2.1 + (st 1).2.1 * (st 1).2.1 + (st 2).2.1 * (st 2).2.1 =
        sumNatAbsSq Δ := by
      unfold sumNatAbsSq
      rw [Fin.sum_univ_three, hd 0, hd 1, hd 2]
      ring
    rw [hs, ← (decodeShellNu3_mem_and_shellIndex hv).2, hdec]
  constructor
  · rintro ⟨_, hv, hrad, hupd⟩
    rcases s3UpdateSysProj_eq_iff.mp hupd with ⟨_, hpEq⟩
    have hax : ∀ w : Fin 3, decodeShellNu3 u22 s3 w = ν₀ w ∧ (st w).2.1 = (Δ w).natAbs := fun w ↦ by
      rcases s3ProjStepHw_of_validShellNu3 (hx2 w) hv w with ⟨_, hwrap, hd_eq⟩
      rw [hpEq w] at hwrap hd_eq
      exact ⟨((modWrapCoord127_eq_iff_modFoldCoord (s3TwosComp8Int_bounds (hx1 w))
        (s3TwosComp8Int_bounds (hx2 w)) (s3DecodeShellNu3_bounds u22 s3 w)).mp hwrap).symm, hd_eq⟩
    have hdec : decodeShellNu3 u22 s3 = ν₀ := funext fun w ↦ (hax w).1
    exact ⟨⟨hv, hdec⟩, (hrad_eq hv hdec fun w ↦ (hax w).2).symm.trans hrad⟩
  · rintro ⟨⟨hv, hdec⟩, hrad⟩
    have hax : ∀ w : Fin 3, (st w).1 = projAxisField x₁ w ∧ (st w).2.1 = (Δ w).natAbs := fun w ↦ by
      rcases s3ProjStepHw_of_validShellNu3 (hx2 w) hv w with ⟨_, hwrap, hd_eq⟩
      have hp_twos := (modWrapCoord127_eq_iff_modFoldCoord (s3TwosComp8Int_bounds (hx1 w))
        (s3TwosComp8Int_bounds (hx2 w)) (s3DecodeShellNu3_bounds u22 s3 w)).mpr
        (congrFun hdec w).symm
      have hst1 : (st w).1 = projAxisField x₁ w := twosComp8Int_injective (hwrap.trans hp_twos.symm)
      rw [hst1] at hd_eq
      exact ⟨hst1, hd_eq⟩
    exact ⟨hx2, hv, (hrad_eq hv hdec fun w ↦ (hax w).2).trans hrad,
      s3UpdateSysProj_eq_iff.mpr ⟨fun i w ↦ (heEq i w).symm, fun w ↦ (hax w).1⟩⟩

open Classical in
theorem s3TopBlockNorm1s_kernel_match (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (x₁ x₂ : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    let Δ := twosMomentum x₁ .projectile - twosMomentum x₂ .projectile
    (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
      (∑ u22 : Fin 4194304, ∑ s3 : Fin 8, ∑ c8 : Fin 256, ∑ f30 : Fin (2 ^ 30),
        if s3KinOKNorm1s t x₁ x₂ u22 s3 c8 f30 then (1 : ℂ) else 0) *
      ((((16384 / 27 : ℝ) : ℂ)) * s3SynthStructureFactor216 36 cfg Δ) =
    bUnitTwosNorm1sGen t cfg x₁ x₂ := by
  intro Δ
  let KinOK := s3KinOKNorm1s t x₁ x₂
  change (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
    (∑ u22 : Fin 4194304, ∑ s3 : Fin 8, ∑ c8 : Fin 256, ∑ f30 : Fin (2 ^ 30),
      if KinOK u22 s3 c8 f30 then (1 : ℂ) else 0) *
    ((((16384 / 27 : ℝ) : ℂ)) * s3SynthStructureFactor216 36 cfg Δ) =
    bUnitTwosNorm1sGen t cfg x₁ x₂
  unfold bUnitTwosNorm1sGen bTwosNorm1sGen
  rw [Matrix.smul_apply]
  dsimp only [Matrix.of_apply]
  set CondProj : Prop :=
    ProjTwosGridState x₁ ∧ ProjTwosGridState x₂ ∧
      (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
        elecAxisField x₁ i w = elecAxisField x₂ i w)
  by_cases hCase : CondProj ∧ Δ ≠ 0
  · rcases hCase with ⟨hCond, hΔ_ne⟩
    rw [s3ItePos hCond]
    rcases hCond with ⟨hx1, hx2, heEq⟩
    let ν₀ : Fin 3 → ℤ := modFold3D 127 Δ
    have hν₀_mem : ν₀ ∈ nonzeroBox3D (127 : ℤ) :=
      modFold3D_mem_nonzeroBox3D 127 (mk_mem_nonzeroBox3D3 hΔ_ne fun w ↦
        abs_le.mp (s3TwosComp8Int_sub_abs_le (hx1 w) (hx2 w)))
    let cnt38 : ℕ := 2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν₀) (sumNatAbsSq Δ)
    have h1 : ∀ u22 s3 c8 f30, (if KinOK u22 s3 c8 f30 then (1 : ℂ) else 0) =
        (if validShellNu3 u22 s3 = true ∧ decodeShellNu3 u22 s3 = ν₀ then (1 : ℂ) else 0) *
        (if norm1sRadAccept t (shellIndex ν₀) (sumNatAbsSq Δ) (f30.val + 2 ^ 30 * c8.val) = true
          then (1 : ℂ) else 0) := fun u22 s3 c8 f30 ↦ by
      have hiff := s3KinOKNorm1s_iff_of_condProj t hx1 hx2 heEq u22 s3 c8 f30
      by_cases hK : KinOK u22 s3 c8 f30
      · rcases hiff.mp hK with ⟨hA, hB⟩
        rw [s3ItePos hK, s3ItePos hA, s3ItePos hB, mul_one]
      · rw [s3IteNeg hK]
        by_cases hA : validShellNu3 u22 s3 = true ∧ decodeShellNu3 u22 s3 = ν₀
        · rw [s3ItePos hA, s3IteNeg (fun hb ↦ hK (hiff.mpr ⟨hA, hb⟩)), mul_zero]
        · rw [s3IteNeg hA, zero_mul]
    have hFineCard : (∑ c8 : Fin 256, ∑ f30 : Fin (2 ^ 30),
        if norm1sRadAccept t (shellIndex ν₀) (sumNatAbsSq Δ) (f30.val + 2 ^ 30 * c8.val) = true
          then (1 : ℂ) else 0) = (cnt38 : ℂ) := by
      dsimp only [cnt38]
      rw [← Fintype.sum_prod_type', Finset.sum_boole,
        norm1sAcceptCount38_eq t (shellIndex ν₀) (sumNatAbsSq Δ)]
    have hShCard : (∑ u22 : Fin 4194304, ∑ s3 : Fin 8,
        if validShellNu3 u22 s3 = true ∧ decodeShellNu3 u22 s3 = ν₀ then (1 : ℂ) else 0) =
        (((2 ^ (12 - 2 * shellIndex ν₀) : ℕ) : ℂ)) := by
      rw [← Fintype.sum_prod_type', Finset.sum_boole, ← Fintype.card_subtype,
        card_fiber_decodeShellNu3 ν₀ hν₀_mem]
    simp_rw [h1, ← Finset.mul_sum, hFineCard, ← Finset.sum_mul, hShCard, ← Nat.cast_mul]
    exact s3RealComplexKernelNorm1s_eq t cfg Δ hΔ_ne
      (shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν₀_mem)
  · have hKinFalse : ∀ u22 s3 c8 f30, ¬KinOK u22 s3 c8 f30 := by
      unfold KinOK s3KinOKNorm1s
      rintro u22 s3 c8 f30 ⟨hx2, hv, _, hupd⟩
      rcases s3UpdateSysProj_eq_iff.mp hupd with ⟨he', hp'⟩
      have hx1 : ProjTwosGridState x₁ := fun w ↦
        (hp' w) ▸ (s3ProjStepHw_of_validShellNu3 (hx2 w) hv w).1
      refine hCase ⟨⟨hx1, hx2, fun i w ↦ (he' i w).symm⟩, fun hΔ0 ↦
        ne_zero_of_mem_nonzeroBox3D3 (decodeShellNu3_mem_and_shellIndex hv).1 (funext fun w ↦ ?_)⟩
      rcases s3ProjStepHw_of_validShellNu3 (hx2 w) hv w with ⟨_, hwrap, _⟩
      rw [hp' w] at hwrap
      have hf0 := (modWrapCoord127_eq_iff_modFoldCoord (s3TwosComp8Int_bounds (hx1 w))
        (s3TwosComp8Int_bounds (hx2 w)) (s3DecodeShellNu3_bounds u22 s3 w)).mp hwrap
      have hdw : twosComp8Int (projAxisField x₁ w) - twosComp8Int (projAxisField x₂ w) = 0 :=
        congrFun hΔ0 w
      rw [hdw] at hf0
      exact hf0.symm.trans s3ModFoldCoord_zero127
    simp_rw [show ∀ u22 s3 c8 f30, (if KinOK u22 s3 c8 f30 then (1 : ℂ) else 0) = 0 from
      fun u22 s3 c8 f30 ↦ s3IteNeg (hKinFalse u22 s3 c8 f30)]
    simp only [Finset.sum_const_zero, mul_zero, zero_mul]
    by_cases hC : CondProj
    · rw [s3ItePos hC]
      have hΔ0 : Δ = 0 := by_contra fun hne ↦ hCase ⟨hC, hne⟩
      change (0 : ℂ) = (alphaSlot3_216 : ℂ)⁻¹ • (s3SynthStructureFactor216 36 cfg Δ *
        (dampedNorm1sKernelApprox t Δ : ℂ))
      rw [hΔ0, dampedNorm1sKernelApprox_zero, Complex.ofReal_zero, mul_zero, smul_zero]
    · rw [s3IteNeg hC, smul_zero]

theorem s3TopBlockNorm1s_step_collapse (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (g₁ g₂ : Fin (2 ^ (momCoreWires mPayload))) (hg1 : (momAncReg mPayload).extractIndex g₁ =
    coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) (hg2 : (momAncReg
    mPayload).extractIndex g₂ = coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) :
    (unitaryConj (coreHadamardMom mPayload) (uSlot3EffNorm1s t cfg hmPay)).1 g₁ g₂ = ∑ tup :
    Slot3PayloadTuple mPayload, if s3AcceptNorm1s t hmPay (s3Prefix3954Equiv hmPay g₂ tup).1 =
    true ∧ s3SamePrefix3954 (s3CoreMapNorm1s t hmPay (s3Prefix3954Equiv hmPay g₂ tup).1) g₁
    then ((boost127_coarse8_w13 * (1 / 2 : ℝ) ^ mPayload : ℝ) : ℂ) * ((s3U16QutritWeight
    ((s3U16Core hmPay).extractIndex (s3Prefix3954Equiv hmPay g₂ tup).1) : ℝ) : ℂ) *
    Complex.exp ((thetaProtonNearest 36 cfg (s3NucleusIdx216 hmPay (s3Prefix3954Equiv hmPay g₂
    tup).1) (twosMomentum ((momSysReg mPayload).extractIndex g₁) .projectile - twosMomentum
    ((momSysReg mPayload).extractIndex g₂) .projectile) : ℂ) * Complex.I) else 0 := by
  let x₁ := (momSysReg mPayload).extractIndex g₁
  let x₂ := (momSysReg mPayload).extractIndex g₂
  let W : Unitary (2 ^ (momCoreWires mPayload)) := uPrep3_216 hmPay * coreHadamardMom mPayload
  have hConjEq : unitaryConj (coreHadamardMom mPayload) (uSlot3EffNorm1s t cfg hmPay) =
      unitaryConj W (uCore3EffNorm1s t cfg hmPay) := by
    apply Subtype.ext
    simp only [uSlot3EffNorm1s, unitaryConj_val, W, Submonoid.coe_mul, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  rw [hConjEq, unitaryConj_val]
  let corePh : Fin (2 ^ (momCoreWires mPayload)) → ℂ := fun z ↦
    ((s3RejPhaseNorm1s t hmPay z : ℝ) : ℂ) *
      dyadicTurn 48 (s3Shift48_36 t cfg hmPay (basisBits (momCoreWires mPayload) z) : ℤ)
  let term : Fin (2 ^ (momCoreWires mPayload)) → ℂ := fun z ↦
    star (W.1 (s3CoreMapNorm1s t hmPay z) g₁) * corePh z * W.1 z g₂
  have hLHS : (W.1ᴴ * (uCore3EffNorm1s t cfg hmPay).1 * W.1) g₁ g₂ = ∑ z, term z := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    simp_rw [uCore3EffNorm1s_entry, ← mul_assoc]
    rw [Finset.sum_congr rfl fun z' _ ↦ (by
      by_cases h : z' = s3CoreMapNorm1s t hmPay z
      · subst h
        simp [corePh, term]
      · simp [h] :
        star (W.1 z' g₁) * (if z' = s3CoreMapNorm1s t hmPay z then corePh z else 0) * W.1 z g₂ =
          if z' = s3CoreMapNorm1s t hmPay z then term z else 0),
      Finset.sum_ite_eq', s3ItePos (Finset.mem_univ _)]
  rw [hLHS, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun z ↦ s3AcceptNorm1s t hmPay z = true) term,
    s3TopBlockNorm1s_rejected_sum_zero t cfg hmPay g₁ g₂ hg1 hg2, add_zero]
  let ampReal : ℝ := boost127_coarse8_w13 * (1 / 2 : ℝ) ^ mPayload
  refine s3FilterSubtypeEquivSum (fun z ↦ s3AcceptNorm1s t hmPay z = true)
    (fun z ↦ s3SamePrefix3954 z g₂) (fun z ↦ s3SamePrefix3954 (s3CoreMapNorm1s t hmPay z) g₁)
    (fun z ↦ (ampReal : ℂ) * ((s3U16QutritWeight ((s3U16Core hmPay).extractIndex z) : ℝ) : ℂ) *
      Complex.exp ((thetaProtonNearest 36 cfg (s3NucleusIdx216 hmPay z)
        (twosMomentum x₁ .projectile - twosMomentum x₂ .projectile) : ℂ) * Complex.I))
    term (fun z hz ↦ ?_) (s3Prefix3954Equiv hmPay g₂)
  rcases s3AcceptNorm1s_imp_coarseGood3_both t hmPay hz with ⟨hcg, hcg'⟩
  have hqf_map : s3QutritFactor hmPay (s3CoreMapNorm1s t hmPay z) = s3QutritFactor hmPay z :=
    s3QutritFactor_congr_u16 hmPay (s3CoreMapNorm1s_fields hz).2.2.2.2.2.2.2.1
  dsimp only [term, W, corePh]
  rw [uPrep3_216_mul_coreHadamard_apply hmPay (s3CoreMapNorm1s t hmPay z) g₁ hg1,
    uPrep3_216_mul_coreHadamard_apply hmPay z g₂ hg2,
    s3DyadicTurn_shift48_36_eq t cfg hmPay z, s3ItePos hz,
    show s3RejPhaseNorm1s t hmPay z = 1 from by unfold s3RejPhaseNorm1s; simp [hz]]
  by_cases hp : s3SamePrefix3954 z g₂ ∧ s3SamePrefix3954 (s3CoreMapNorm1s t hmPay z) g₁
  · rw [s3ItePos hp.2, s3ItePos hp.1, s3ItePos hp, uOaa33_row_sum_good hcg',
      uOaa33_row_sum_good hcg, hqf_map, ((s3SamePrefix3954_coin6_iff hmPay hg1).mp hp.2).1,
      ((s3SamePrefix3954_coin6_iff hmPay hg2).mp hp.1).1]
    have hboost : (3 - 4 * coulombCoarse8PreOAAProb 127 8192) *
        (3 - 4 * coulombCoarse8PreOAAProb 127 8192) = boost127_coarse8_w13 := by
      unfold boost127_coarse8_w13
      ring
    have hsqrt : ((1 / √2 : ℝ) ^ mPayload) * ((1 / √2 : ℝ) ^ mPayload) = (1 / 2 : ℝ) ^ mPayload :=
      by
      rw [← mul_pow, show (1 / √2 : ℝ) * (1 / √2 : ℝ) = 1 / 2 from by
        field_simp; exact (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)).symm]
    let qf := s3QutritFactor hmPay z
    let cOaa : ℂ := ((3 - 4 * coulombCoarse8PreOAAProb 127 8192 : ℝ) : ℂ)
    let cH : ℂ := (((1 / √2 : ℝ) ^ mPayload : ℝ) : ℂ)
    let ePh : ℂ := Complex.exp ((thetaProtonNearest 36 cfg (s3NucleusIdx216 hmPay z)
      (twosMomentum x₁ .projectile - twosMomentum x₂ .projectile) : ℂ) * Complex.I)
    change star (qf * cOaa * cH) * (((1 : ℝ) : ℂ) * ePh) * (qf * cOaa * cH) = _
    have hsc1 : star cOaa = cOaa := Complex.conj_ofReal _
    have hsc2 : star cH = cH := Complex.conj_ofReal _
    have hreal_amp : cOaa * cOaa * (cH * cH) = (ampReal : ℂ) := by
      dsimp [cOaa, cH, ampReal]
      rw [← hboost, ← hsqrt]
      push_cast
      ring
    calc star (qf * cOaa * cH) * (((1 : ℝ) : ℂ) * ePh) * (qf * cOaa * cH)
        = (cOaa * cOaa * (cH * cH)) * (star qf * qf) * ePh := by
            simp only [star_mul, hsc1, hsc2, Complex.ofReal_one, one_mul]
            ring
      _ = _ := by rw [hreal_amp, star_s3QutritFactor_mul_self hmPay z]
  · rw [s3IteNeg hp]
    by_cases hp1 : s3SamePrefix3954 z g₂
    · simp only [s3IteNeg (fun h ↦ hp ⟨hp1, h⟩), star_zero, zero_mul]
    · simp only [s3IteNeg hp1, mul_zero]

open Classical in
theorem s3TopBlockNorm1s_step_tuple_summand (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload)
    (g₁ g₂ : Fin (2 ^ (momCoreWires mPayload)))
    (hg1 : (momAncReg mPayload).extractIndex g₁ =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3))
    (hg2 : (momAncReg mPayload).extractIndex g₂ =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3))
    (tup : Slot3PayloadTuple mPayload) :
    let x₁ := (momSysReg mPayload).extractIndex g₁
    let x₂ := (momSysReg mPayload).extractIndex g₂
    let ampReal : ℝ := boost127_coarse8_w13 * (1 / 2 : ℝ) ^ mPayload
    (if s3AcceptNorm1s t hmPay (s3Prefix3954Equiv hmPay g₂ tup).1 = true ∧
        s3SamePrefix3954 (s3CoreMapNorm1s t hmPay (s3Prefix3954Equiv hmPay g₂ tup).1) g₁ then
      (ampReal : ℂ) *
        ((s3U16QutritWeight ((s3U16Core hmPay).extractIndex (s3Prefix3954Equiv hmPay g₂ tup).1) : ℝ)
          : ℂ) *
        Complex.exp ((thetaProtonNearest 36 cfg
          (s3NucleusIdx216 hmPay (s3Prefix3954Equiv hmPay g₂ tup).1)
          (twosMomentum x₁ .projectile - twosMomentum x₂ .projectile) : ℂ) * Complex.I)
    else 0) =
    (if s3KinOKNorm1s t x₁ x₂ tup.1 tup.2.1 tup.2.2.1 tup.2.2.2.1 then (ampReal : ℂ) else 0) *
    (((s3U16QutritWeight tup.2.2.2.2.2.1 : ℝ) : ℂ) *
      Complex.exp ((thetaProtonNearest 42 (trunc36Cfg cfg)
        ⟨2 * ((tup.2.2.2.2.2.1.val % 4) + 4 * s3NucleusQ27 (basisBits 16 tup.2.2.2.2.2.1)) +
            tup.2.2.2.2.1.val,
          by have := Nat.mod_lt tup.2.2.2.2.2.1.val (by decide : 0 < 4)
             have := s3NucleusQ27_lt (basisBits 16 tup.2.2.2.2.2.1)
             have := tup.2.2.2.2.1.isLt; omega⟩
        (twosMomentum x₁ .projectile - twosMomentum x₂ .projectile) : ℂ) * Complex.I)) := by
  intro x₁ x₂ ampReal
  let z := (s3Prefix3954Equiv hmPay g₂ tup).1
  rcases s3Prefix3954Equiv_fields hmPay hg2 tup with ⟨hc6, hsys, hu22, hs3, hc8, hf30, hbPar, hu16⟩
  have hp_z := (s3SamePrefix3954_coin6_iff hmPay hg2).mp (s3Prefix3954Equiv hmPay g₂ tup).2
  have hTupleIff : (s3AcceptNorm1s t hmPay z = true ∧ s3SamePrefix3954 (s3CoreMapNorm1s t
      hmPay z) g₁) ↔ s3KinOKNorm1s t x₁ x₂ tup.1 tup.2.1 tup.2.2.1 tup.2.2.2.1 := by
    unfold s3KinOKNorm1s
    constructor
    · rintro ⟨hz, hp1⟩
      have hf := s3CoreMapNorm1s_fields hz
      have hp1_f := (s3SamePrefix3954_coin6_iff hmPay hg1).mp hp1
      have hupd := hf.2.1.symm.trans hp1_f.1
      unfold s3AcceptNorm1s at hz
      dsimp only at hz
      rcases s3And4.mp hz with ⟨_, hgridB, hv, hradB⟩
      rw [hsys] at hgridB
      rw [hu22, hs3] at hv
      rw [hsys, hu22, hs3, hc8, hf30] at hradB
      rw [hsys, hu22, hs3] at hupd
      exact ⟨(s3ProjGridBool_eq_true_iff x₂).mp hgridB, hv, hradB, hupd⟩
    · rintro ⟨hgrid2, hv, hrad, hupd⟩
      have hz : s3AcceptNorm1s t hmPay z = true := by
        unfold s3AcceptNorm1s
        dsimp only
        rw [hc6, hsys, hu22, hs3, hc8, hf30]
        exact s3And4.mpr ⟨by decide,
          (s3ProjGridBool_eq_true_iff x₂).mpr hgrid2, hv, hrad⟩
      refine ⟨hz, ?_⟩
      have hf := s3CoreMapNorm1s_fields hz
      refine (s3SamePrefix3954_coin6_iff hmPay hg1).mpr ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hf.2.1, hsys, hu22, hs3]; exact hupd
      · rw [hf.1]; exact hc6
      · exact (hf.2.2.2.2.2.2.2.2.2 ⟨3951, by have := s3MomCore_ge_4034 hmPay; omega⟩
          (by dsimp; omega) (by dsimp; omega)).trans hp_z.2.2.1
      · exact (hf.2.2.2.2.2.2.2.2.2 ⟨3952, by have := s3MomCore_ge_4034 hmPay; omega⟩
          (by dsimp; omega) (by dsimp; omega)).trans hp_z.2.2.2.1
      · exact (hf.2.2.2.2.2.2.2.2.2 ⟨3953, by have := s3MomCore_ge_4034 hmPay; omega⟩
          (by dsimp; omega) (by dsimp; omega)).trans hp_z.2.2.2.2
  have hNucEq : s3NucleusIdx216 hmPay z =
      ⟨2 * ((tup.2.2.2.2.2.1.val % 4) + 4 * s3NucleusQ27 (basisBits 16 tup.2.2.2.2.2.1)) +
          tup.2.2.2.2.1.val,
        by have := Nat.mod_lt tup.2.2.2.2.2.1.val (by decide : 0 < 4)
           have := s3NucleusQ27_lt (basisBits 16 tup.2.2.2.2.2.1)
           have := tup.2.2.2.2.1.isLt; omega⟩ := by
    apply Fin.ext
    unfold s3NucleusIdx216
    dsimp only
    rw [hu16, hbPar]
  by_cases hL : s3AcceptNorm1s t hmPay z = true ∧ s3SamePrefix3954 (s3CoreMapNorm1s t hmPay z) g₁
  · have hK := hTupleIff.mp hL
    rw [s3ItePos hL, s3ItePos hK, hNucEq, hu16, ← exp_thetaProtonNearest_42_trunc36Cfg cfg]
    ring
  · have hnK : ¬s3KinOKNorm1s t x₁ x₂ tup.1 tup.2.1 tup.2.2.1 tup.2.2.2.1 :=
      fun hk ↦ hL (hTupleIff.mpr hk)
    rw [s3IteNeg hL, s3IteNeg hnK, zero_mul]

open Classical in
theorem s3_hadamard_topBlock_coin6_norm1s (t : Norm1sTier) {mPayload : ℕ}
    (cfg : SpecsAux.SpecMirror.Configuration) (hmPay : 80 ≤ mPayload) :
    let c := fullSysCoinIdx 3
    let P_anc := (momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (momCoin3Sel mPayload) c)
    P_anc * (unitaryConj (coreHadamardMom mPayload) (uSlot3EffNorm1s t cfg hmPay)).1 * P_anc =
      P_anc * (momSysReg mPayload).embedMatrix (bUnitTwosNorm1sGen t cfg) * P_anc := by
  intro c P_anc
  let u₀ := coinSelOutcome (momCoin3Sel mPayload) c
  refine diag_proj_mul_eq (fun g ↦ (momAncReg mPayload).extractIndex g = u₀) P_anc
    (unitaryConj (coreHadamardMom mPayload) (uSlot3EffNorm1s t cfg hmPay)).1
    ((momSysReg mPayload).embedMatrix (bUnitTwosNorm1sGen t cfg))
    (QRegister.basisOutcomeProjector_eq_diagonal (momAncReg mPayload) u₀) fun g₁ g₂ hg1 hg2 ↦
    ?_
  let x₁ := (momSysReg mPayload).extractIndex g₁
  let x₂ := (momSysReg mPayload).extractIndex g₂
  have hAgreeSys : (momSysReg mPayload).AgreeOutside g₁ g₂ := by
    intro w hwOut
    have hwGe : SpecsAux.SpecMirror.systemQubits ≤ w.val := by
      by_contra hlt
      exact hwOut ⟨⟨w.val, Nat.lt_of_not_le hlt⟩,
        Fin.ext (by dsimp [momSysReg, s3Qreg_block_apply, s3Qreg_block_wires_apply,
          s3Qreg_whole_wires, s3Emb_trans_apply, s3Emb_refl_apply, s3Emb_mk_apply]; omega)⟩
    let idxAnc : Fin (momSelWires mPayload) :=
      ⟨w.val - SpecsAux.SpecMirror.systemQubits, by
        have hwLt := w.isLt
        dsimp [momCoreWires] at hwLt
        omega⟩
    have hwEq : w = momAncReg mPayload idxAnc :=
      Fin.ext (by dsimp [momAncReg, idxAnc, s3Qreg_block_apply, s3Qreg_block_wires_apply,
        s3Qreg_whole_wires, s3Emb_trans_apply, s3Emb_refl_apply, s3Emb_mk_apply]; omega)
    rw [hwEq]
    have hb1 := QRegister.basisBits_extractIndex (momAncReg mPayload) g₁ idxAnc
    have hb2 := QRegister.basisBits_extractIndex (momAncReg mPayload) g₂ idxAnc
    rw [hg1] at hb1
    rw [hg2] at hb2
    exact hb1.symm.trans hb2
  have hRHS : (momSysReg mPayload).embedMatrix (bUnitTwosNorm1sGen t cfg) g₁ g₂ =
      bUnitTwosNorm1sGen t cfg x₁ x₂ := by
    rw [QRegister.embedMatrix_apply_of_agreeOutside, s3ItePos hAgreeSys, mul_one]
  refine (s3TopBlockNorm1s_step_collapse t cfg hmPay g₁ g₂ hg1 hg2).trans ?_
  refine (Finset.sum_congr rfl fun tup _ ↦
    s3TopBlockNorm1s_step_tuple_summand t cfg hmPay g₁ g₂ hg1 hg2 tup).trans ?_
  refine (s3TopBlock216_step_factor_abstract (trunc36Cfg cfg) hmPay
    (twosMomentum x₁ .projectile - twosMomentum x₂ .projectile) (s3KinOKNorm1s t x₁ x₂)).trans ?_
  rw [s3SynthStructureFactor216_42_trunc36Cfg cfg]
  exact (s3TopBlockNorm1s_kernel_match t cfg x₁ x₂).trans hRHS.symm

/-- Core effective 1-sided normalized Slot-3 unitary conjugated by `uPiSwap3Core`. -/
noncomputable def uSlot3Norm1sSwap3Eff (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ (momCoreWires 80)) :=
  PosMomSelectDynamic.unitaryConj uPiSwap3Core (uSlot3EffNorm1s t cfg (le_refl 80))

private theorem rECPre80_core_fields_eq {x y : Fin (2 ^ (momCoreWires 80))}
    (hAg : rECPre80.AgreeOutside x y) :
    (momCoinReg 80).extractIndex x = (momCoinReg 80).extractIndex y ∧
      (s3U22Core (le_refl 80)).extractIndex x = (s3U22Core (le_refl 80)).extractIndex y ∧
      (s3S3Core (le_refl 80)).extractIndex x = (s3S3Core (le_refl 80)).extractIndex y :=
  ⟨extractIndex_eq_of_agreeOutside_rECPre80 (momCoinReg 80)
      (fun i ↦ by have := i.isLt; change 3924 ≤ 3948 + i.val ∧ 3948 + i.val < 4026; omega) hAg,
    extractIndex_eq_of_agreeOutside_rECPre80 (s3U22Core (le_refl 80))
      (fun i ↦ by have := i.isLt; change 3924 ≤ 3954 + i.val ∧ 3954 + i.val < 4026; omega) hAg,
    extractIndex_eq_of_agreeOutside_rECPre80 (s3S3Core (le_refl 80))
      (fun i ↦ by have := i.isLt; change 3924 ≤ 3976 + i.val ∧ 3976 + i.val < 4026; omega) hAg⟩

theorem s3AcceptNorm1s_and_nuc_eq_of_agreeOutside_rECPre80 (t : Norm1sTier)
    {x y : Fin (2 ^ (momCoreWires 80))} (hAg : rECPre80.AgreeOutside x y) :
    s3AcceptNorm1s t (le_refl 80) x = s3AcceptNorm1s t (le_refl 80) y ∧
      s3NucleusIdx216 (le_refl 80) x = s3NucleusIdx216 (le_refl 80) y := by
  rcases rECPre80_core_fields_eq hAg with ⟨hCoin, hU22, hS3⟩
  have hC8 := extractIndex_eq_of_agreeOutside_rECPre80 (s3C8Core (le_refl 80))
    (fun i ↦ by have := i.isLt; change 3924 ≤ 3979 + i.val ∧ 3979 + i.val < 4026; omega) hAg
  have hF30 := extractIndex_eq_of_agreeOutside_rECPre80 (s3Fine30Core (le_refl 80))
    (fun i ↦ by have := i.isLt; change 3924 ≤ 3987 + i.val ∧ 3987 + i.val < 4026; omega) hAg
  have hP0 := projAxisField_eq_of_agreeOutside_rECPre80 hAg 0
  have hP1 := projAxisField_eq_of_agreeOutside_rECPre80 hAg 1
  have hP2 := projAxisField_eq_of_agreeOutside_rECPre80 hAg 2
  have hGrid : s3ProjGridBool ((momSysReg 80).extractIndex x) =
      s3ProjGridBool ((momSysReg 80).extractIndex y) := by unfold s3ProjGridBool; rw [hP0, hP1, hP2]
  refine ⟨by
    unfold s3AcceptNorm1s; dsimp only; rw [hCoin, hU22, hS3, hC8, hF30, hP0, hP1, hP2, hGrid],
    (Slot3StreamUncK35Shift3.s3Accept216_and_nuc_eq_of_agreeOutside_rECPre80 hAg).2⟩

theorem commutesWithReg_rECPre80_uSlot3EffNorm1s (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) :
    CommutesWithReg rECPre80 (uSlot3EffNorm1s t cfg (le_refl 80)).1 := by
  have hPrep : CommutesWithReg rECPre80 (uPrep3_216 (le_refl 80)).1 := by
    have hQ (j : Fin 3) : CommutesWithReg rECPre80
        ((s3QutritPairCore (le_refl 80) j).embedUnitary cPrepQutrit2.eval).1 :=
      CommutesWithReg.of_disjoint_embed (disjoint_rECPre80_of_mid _ fun i ↦ by
        have := j.isLt; have := i.isLt; dsimp [s3QutritPairCore, s3Qreg_block_apply]; omega) _
    have hP3 : CommutesWithReg rECPre80 (uPrep3 (le_refl 80)).1 :=
      CommutesWithReg.of_disjoint_embed (disjoint_rECPre80_of_mid _ fun i ↦ by
        have := i.isLt; dsimp [s3Coarse33Core, s3Qreg_block_apply]; omega) _
    exact ((hQ 2).mul ((hQ 1).mul (hQ 0))).mul hP3
  have hSwap : CommutesWithReg rECPre80 (s3SwapRejUnitaryNorm1s t (le_refl 80)).1 := by
    refine CommutesWithReg.of_signedInvolution (s3CorePermNorm1s t (le_refl 80))
      (s3RejPhaseNorm1s t (le_refl 80))
      (fun z ↦ (s3AcceptNorm1s_and_involutive t (le_refl 80) z).2.1)
      (s3RejPhaseNorm1s_symm t (le_refl 80)) (s3RejPhaseNorm1s_sq t (le_refl 80))
      (fun z ↦ ?_) (fun x y hAg ↦ ?_) (fun x y hAg ↦ ?_)
    · apply (basisBitsEquiv (3924 + 3)).injective; funext idx
      change basisBits _ (rECPre80.extractIndex (s3CoreMapNorm1s t (le_refl 80) z)) idx =
        basisBits _ (rECPre80.extractIndex z) idx
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      by_cases hz : s3AcceptNorm1s t (le_refl 80) z = true
      · dsimp only [s3CoreMapNorm1s]; rw [s3ItePos hz, basisBits_symm_apply _ (rECPre80 idx)]
        rcases rECPre80_val_cases idx with ⟨hi, hv⟩ | ⟨hlo, hhi⟩
        · have hkSys : (rECPre80 idx).val < SpecsAux.SpecMirror.systemQubits := by
            rw [s3SysQubits_eq]; omega
          rw [s3DitePos hkSys]; dsimp only [s3UpdateSysProj]
          rw [basisBits_symm_apply _ ⟨(rECPre80 idx).val, hkSys⟩, s3DitePos (by dsimp; omega),
            QRegister.basisBits_extractIndex (momSysReg 80) z ⟨(rECPre80 idx).val, hkSys⟩]
          exact congrArg (basisBits (momCoreWires 80) z)
            (Fin.ext (by change 0 + (rECPre80 idx).val = (rECPre80 idx).val; omega))
        · rw [s3DiteNeg (by rw [s3SysQubits_eq]; omega), s3DiteNeg (by omega)]
      · dsimp only [s3CoreMapNorm1s]; rw [s3IteNeg hz]
    · intro w hw
      have hwGe : 3924 ≤ w.val := by
        by_contra hlt; exact hw (mem_rECPre80_of_lt_3924 (Nat.lt_of_not_ge hlt))
      have hAccEq := (s3AcceptNorm1s_and_nuc_eq_of_agreeOutside_rECPre80 t hAg).1
      rcases rECPre80_core_fields_eq hAg with ⟨_, hU22, hS3⟩
      by_cases hx : s3AcceptNorm1s t (le_refl 80) x = true
      · have hy : s3AcceptNorm1s t (le_refl 80) y = true := hAccEq.symm.trans hx
        change basisBits _ (s3CoreMapNorm1s t (le_refl 80) x) w =
          basisBits _ (s3CoreMapNorm1s t (le_refl 80) y) w
        dsimp only [s3CoreMapNorm1s]
        rw [s3ItePos hx, s3ItePos hy, basisBits_symm_apply _ w, basisBits_symm_apply _ w]
        by_cases hkSys : w.val < SpecsAux.SpecMirror.systemQubits
        · rw [s3DitePos hkSys, s3DitePos hkSys]; dsimp only [s3UpdateSysProj]
          rw [basisBits_symm_apply _ ⟨w.val, hkSys⟩, basisBits_symm_apply _ ⟨w.val, hkSys⟩,
            s3DiteNeg (by dsimp; omega), s3DiteNeg (by dsimp; omega),
            projAxisField_eq_of_agreeOutside_rECPre80 hAg, hU22, hS3]
        · rw [s3DiteNeg hkSys, s3DiteNeg hkSys]
          by_cases hkS3 : 3976 ≤ w.val ∧ w.val < 3979
          · rw [s3DitePos hkS3, s3DitePos hkS3, hU22, hS3]
          · rw [s3DiteNeg hkS3, s3DiteNeg hkS3, hAg w hw]
      · have hy : ¬(s3AcceptNorm1s t (le_refl 80) y = true) := fun h ↦ hx (hAccEq.trans h)
        change basisBits _ (s3CoreMapNorm1s t (le_refl 80) x) w =
          basisBits _ (s3CoreMapNorm1s t (le_refl 80) y) w
        dsimp only [s3CoreMapNorm1s]; rw [s3IteNeg hx, s3IteNeg hy, hAg w hw]
    · unfold s3RejPhaseNorm1s
      rcases rECPre80_core_fields_eq hAg with ⟨hCoin, _, _⟩
      have hAcc := (s3AcceptNorm1s_and_nuc_eq_of_agreeOutside_rECPre80 t hAg).1
      have hBPar := hAg (s3BParCore (le_refl 80))
        (not_mem_rECPre80_of_mid (by change 3924 ≤ 4017; decide) (by change 4017 < 4026; decide))
      rw [hCoin, hAcc, hBPar]
  have hKick : CommutesWithReg rECPre80 (s3KickEffUnitaryNorm1s t cfg (le_refl 80)).1 := by
    unfold s3KickEffUnitaryNorm1s dyadicDiagUnitary
    refine CommutesWithReg.of_diagonal fun x y hAg ↦ ?_
    rw [s3DyadicTurn_shift48_36_eq, s3DyadicTurn_shift48_36_eq]
    rcases s3AcceptNorm1s_and_nuc_eq_of_agreeOutside_rECPre80 t hAg with ⟨hAcc, hNuc⟩
    rcases rECPre80_core_fields_eq hAg with ⟨_, hU22, hS3⟩
    by_cases hx : s3AcceptNorm1s t (le_refl 80) x = true
    · have hy : s3AcceptNorm1s t (le_refl 80) y = true := hAcc.symm.trans hx
      rw [s3ItePos hx, s3ItePos hy, hNuc]
      have hDelta : twosMomentum ((momSysReg 80).extractIndex (s3CoreMapNorm1s t (le_refl 80) x))
        .projectile -
            twosMomentum ((momSysReg 80).extractIndex x) .projectile =
          twosMomentum ((momSysReg 80).extractIndex (s3CoreMapNorm1s t (le_refl 80) y)) .projectile
            -
            twosMomentum ((momSysReg 80).extractIndex y) .projectile := by
        funext a; simp only [Pi.sub_apply, twosMomentum]
        rw [(s3CoreMapNorm1s_fields hx).2.1, (s3CoreMapNorm1s_fields hy).2.1,
          (s3UpdateSysProj_fields _ _).2 a, (s3UpdateSysProj_fields _ _).2 a,
          projAxisField_eq_of_agreeOutside_rECPre80 hAg a, hU22, hS3]
      rw [hDelta]
    · have hy : ¬(s3AcceptNorm1s t (le_refl 80) y = true) := fun h ↦ hx (hAcc.trans h)
      rw [s3IteNeg hx, s3IteNeg hy]
  exact CommutesWithReg.unitaryConj hPrep (hSwap.mul hKick)

theorem commutesWithReg_rEC80_uSlot3Norm1sSwap3Eff (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) :
    CommutesWithReg rEC80 (uSlot3Norm1sSwap3Eff t cfg).1 :=
  CommutesWithReg.unitaryConj_wirePerm piSwap3Wire piSwap3WireFun_involutive
    piSwap3CorePerm basisBits_piSwap3CorePerm rfl (commutesWithReg_rECPre80_uSlot3EffNorm1s t cfg)

theorem commutesWithReg_rEC80_of_eq_uPiSwap3Core_norm1s (t : Norm1sTier)
    {uSwap : Unitary (2 ^ (momCoreWires 80))}
    (hSwap : uSwap = uPiSwap3Core) (cfg : SpecsAux.SpecMirror.Configuration) :
    CommutesWithReg rEC80 (PosMomSelectDynamic.unitaryConj uSwap (uSlot3EffNorm1s t cfg (le_refl
      80))).1 := by
  rw [hSwap]; exact commutesWithReg_rEC80_uSlot3Norm1sSwap3Eff t cfg

theorem abs_dampedNorm1sKernelApprox_sub_le (t : Norm1sTier)
    {ν Δ : Fin 3 → ℤ} (hν_mem : ν ∈ nonzeroBox3D (127 : ℤ))
    (hfold : modFold3D 127 Δ = ν) {E : ℝ}
    (hbd : |((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) -
      ((cRad7Computable (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ)| ≤ E) :
    |dampedNorm1sKernelApprox t Δ - dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 Δ| ≤
      ((2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (E / (2 : ℝ) ^ (2 * shellIndex ν)) := by
  have hν_ne : ν ≠ 0 := ne_zero_of_mem_nonzeroBox3D3 hν_mem
  have hΔ_ne : Δ ≠ 0 := fun h0 ↦ hν_ne (by
    rw [← hfold, h0]; ext w; simp [modFold3D, modFoldCoord, modWrapCoord])
  have hμ7 : shellIndex ν < 7 := shellIndex_lt_seven_of_mem_nonzeroBox3D_127 hν_mem
  have hcRad : boxRadConst 38 (1 / 42) 1 (shellIndex ν) = cRad7Computable (shellIndex ν) := by
    unfold cRad7Computable; exact boxRadConst_38_eq_cRad38True hμ7
  have hdiff : dampedNorm1sKernelApprox t Δ - dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 Δ =
      ((2 / 42 : ℝ) / ((2 : ℝ) ^ (2 * shellIndex ν) * (2 : ℝ) ^ 38)) *
        (((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) -
          ((cRad7Computable (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ)) := by
    rw [dampedModWrapKernelApprox_38_36_127_eq]
    unfold dampedNorm1sKernelApprox ModWrapCoarse8PureMomentum.modWrapRadKernelApprox
    rw [s3IteNeg hΔ_ne, hfold, hcRad, pow_add]
    dsimp only
    ring
  rw [hdiff, abs_mul, abs_of_pos (by positivity)]
  calc ((2 / 42 : ℝ) / ((2 : ℝ) ^ (2 * shellIndex ν) * (2 : ℝ) ^ 38)) * _
      ≤ ((2 / 42 : ℝ) / ((2 : ℝ) ^ (2 * shellIndex ν) * (2 : ℝ) ^ 38)) * E :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = ((2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (E / (2 : ℝ) ^ (2 * shellIndex ν)) := by ring

open Classical in
theorem norm_bTwosNorm1sGen_sub_bTwosSlot3_216_trunc36Cfg_le_of_kernelDiff
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (E_nu : (Fin 3 → ℤ) → ℝ)
    (hEnn : ∀ ν ∈ nonzeroBox3D (127 : ℤ), 0 ≤ E_nu ν)
    (hEbd : ∀ ν ∈ nonzeroBox3D (127 : ℤ), ∀ Δ ∈ box3D (2 * (127 : ℤ)),
      modFold3D 127 Δ = ν →
        |((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) -
          ((cRad7Computable (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ)| ≤ E_nu ν) :
    ‖bTwosNorm1sGen t cfg - bTwosSlot3_216 (trunc36Cfg cfg)‖ ≤
      (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) *
        (∑ ν ∈ nonzeroBox3D (127 : ℤ), E_nu ν / (2 : ℝ) ^ (2 * shellIndex ν)) := by
  let G : (Fin 3 → ℤ) → ℂ := fun Δ ↦
    s3SynthStructureFactor216 36 cfg Δ *
      ((dampedNorm1sKernelApprox t Δ - dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 Δ : ℝ) : ℂ)
  have hDiff : bTwosNorm1sGen t cfg - bTwosSlot3_216 (trunc36Cfg cfg) =
      Matrix.of fun x y ↦
        if ProjTwosGridState x ∧ ProjTwosGridState y ∧
            (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
              elecAxisField x i w = elecAxisField y i w) then
          G (twosMomentum x .projectile - twosMomentum y .projectile)
        else 0 := by
    unfold bTwosNorm1sGen bTwosSlot3_216; ext x y
    rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply]
    by_cases hcond : ProjTwosGridState x ∧ ProjTwosGridState y ∧
        (∀ i : Fin SpecsAux.SpecMirror.numElectrons, ∀ w : Fin 3,
          elecAxisField x i w = elecAxisField y i w)
    · rw [ite_true_eq hcond, ite_true_eq hcond, ite_true_eq hcond]
      set Δ : Fin 3 → ℤ := twosMomentum x .projectile - twosMomentum y .projectile
      rw [s3SynthStructureFactor216_42_trunc36Cfg cfg Δ]; dsimp only [G]; push_cast; ring
    · rw [ite_false_eq hcond, ite_false_eq hcond, ite_false_eq hcond, sub_zero]
  rw [hDiff, Finset.mul_sum]
  refine norm_projTwosGrid_foldedOp_le G
    (by simp [G, dampedNorm1sKernelApprox_zero, dampedModWrapKernelApprox_zero])
    (fun ν ↦ (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (E_nu ν / (2 : ℝ) ^ (2 * shellIndex ν)))
    (fun ν hν ↦ mul_nonneg (by positivity) (div_nonneg (hEnn ν hν) (by positivity)))
    fun ν hν_mem Δ hsub_box hfold ↦ ?_
  have hk_bd := abs_dampedNorm1sKernelApprox_sub_le t hν_mem hfold (hEbd ν hν_mem Δ hsub_box hfold)
  have hS_le := norm_s3SynthStructureFactor216_le_216 36 cfg Δ
  dsimp only [G]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖s3SynthStructureFactor216 36 cfg Δ‖ *
        |dampedNorm1sKernelApprox t Δ - dampedModWrapKernelApprox 38 36 127 (2 / 42) 2 Δ|
      ≤ 216 * (((2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (E_nu ν / (2 : ℝ) ^ (2 * shellIndex ν))) :=
        mul_le_mul hS_le hk_bd (abs_nonneg _) (by positivity)
    _ = (216 * (2 / 42 : ℝ) / (2 : ℝ) ^ 38) * (E_nu ν / (2 : ℝ) ^ (2 * shellIndex ν)) := by ring

end

end ConfigSlot3Norm1s36Physics80

end Slot3Norm1s36Physics80
end
set_option exponentiation.threshold 256
end Slot3Norm1s36Physics80

section Slot3Norm1s36CoreWideBooth
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36CoreWideBooth (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace Slot3Norm1s36CoreWideBooth

section ConfigSlot3Norm1s36CoreWideBooth

set_option maxRecDepth 4096
set_option exponentiation.threshold 256

local instance (priority :=
  10) instLoc_Slot3Norm1s36CoreWideBooth_1InstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (wire_ne_of_lt wire_ne_of_gt CliffProg TempPhaseProg cleanRem cleanRem_anti ValidCleanRem
    validCleanRem_mono TempCtx ctxCliffAlloc RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem (bit_cases RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMagCoord3)
open MomSlots35Slot3ProjNuclear (s3ShellMagCoord3_lt_128)
open StepBBlock0 (bitsVal_eq_of_testBit bitsVal_slice_linear)
open StepBBlock0 (bitsVal_split_add)
open Prod57BoothHoist
  (bitsVal_injective bitsVal_slice_eq_div_mod p57ProjW p57S3W p57U38W p57MW sTrue18WDefault
    axisCmpDMag sTrueRawVal p57CleanDiagProj p57CleanDiagProj_conjTranspose p57CleanDiagProj_mono
    p57SeqClean_prog_inv inPlaceAddMod1 inPlaceAddMod1_countTempAnd inPlaceAddMod1_spec
    cleanMsbSubStatic ctxCleanMsbSub_spec dCleanMsbSub dCleanMsbSub_count_t dCleanMsbSub_count_toff
    dCleanMsbSub_preservesStore dCleanMsbSub_realizes_static p57ToDynWith p57ToDynWith_count_t
    p57ToDynWith_count_toff p57ToDynWith_preservesStore validSTrueMap_default cliffInv_comp_eval
    bitsVal_castSucc_split p57WithTempAnd_cleanDiagProj withCliffAlloc_valid_and_eval)
open StepBOuter (getU22)
open Slot3Exact216Oracle80
  (validStaticVal216 sTrue18WDefault216_bounds p57U38W216_lt107)
open Slot3MicroEngineAux
  (MicroOp microValid microAllocs microAnds boolToZMod2 boolToZMod2_decide_eq_one getBoolAt
    setBoolAt getBoolAt_setBoolAt length_setBoolAt initBoolList bitsVal_testBit_eq evalMicroList
    evalMicroListStrict evalMicroListStrict_eq allBelow allBelow_iff allBelowFrom allBelowFrom_add
    allBelowFrom_chunks4 ctxMicro ctxMicro_scoped)
open Slot3Norm1s36_161w

theorem axisCmpDMag_bounds_of_lt_128 (p m s : ℕ) (hm : m < 128) :
    m ≤ axisCmpDMag p m s ∧ axisCmpDMag p m s ≤ 255 := by
  unfold axisCmpDMag
  dsimp only
  generalize (if 255 - (if p < 128 then p + 128 else p - 128) <
      (if s = 1 then 255 - m else m) then 1 - s else s) = w
  by_cases hw : w = 1 <;> simp only [hw, ↓reduceIte] <;> omega

theorem sTrueRawVal_lt_two_pow_18 (γ : BitAssignment 437) : sTrueRawVal γ < 2 ^ 18 := by
  unfold sTrueRawVal
  rw [Fin.sum_univ_three]
  have h0 : bitsVal (fun b ↦ γ (p57MW 0 b)) < 128 := bitsVal_lt_two_pow _
  have h1 : bitsVal (fun b ↦ γ (p57MW 1 b)) < 128 := bitsVal_lt_two_pow _
  have h2 : bitsVal (fun b ↦ γ (p57MW 2 b)) < 128 := bitsVal_lt_two_pow _
  have d0 := (axisCmpDMag_bounds_of_lt_128 (bitsVal fun b ↦ γ (p57ProjW 0 b)) (bitsVal fun b ↦
    γ (p57MW 0 b)) (γ (p57S3W 0)).val h0).2
  have d1 := (axisCmpDMag_bounds_of_lt_128 (bitsVal fun b ↦ γ (p57ProjW 1 b)) (bitsVal fun b ↦
    γ (p57MW 1 b)) (γ (p57S3W 1)).val h1).2
  have d2 := (axisCmpDMag_bounds_of_lt_128 (bitsVal fun b ↦ γ (p57ProjW 2 b)) (bitsVal fun b ↦
    γ (p57MW 2 b)) (γ (p57S3W 2)).val h2).2
  dsimp only
  nlinarith

theorem two_mul_mu_le_clz18Log2 {γ : BitAssignment 437} (hvs : validStaticVal216 γ = 1)
    (hm : ∀ w : Fin 3, bitsVal (fun b ↦ γ (p57MW w b)) = shellMagCoord3 (getU22 γ) w) : 2
    * shellMu3 (getU22 γ) ≤ clz18Log2 (sTrueRawVal γ) := by
  unfold validStaticVal216 at hvs
  by_cases hcond : 32768 ≤ (getU22 γ).val ∧
      2 ^ shellMu3 (getU22 γ) ≤ max (shellMagCoord3 (getU22 γ) 0)
        (max (shellMagCoord3 (getU22 γ) 1) (shellMagCoord3 (getU22 γ) 2)) ∧
      (∀ w : Fin 3, ¬(shellMagCoord3 (getU22 γ) w = 0 ∧ (γ (p57S3W w)).val = 1))
  · set u22 := getU22 γ
    set mu := shellMu3 u22
    have hmax := hcond.2.1
    have hpow_sq : 2 ^ (2 * mu) = 2 ^ mu * 2 ^ mu := by rw [← pow_add, two_mul]
    have hs_ge : 2 ^ (2 * mu) ≤ sTrueRawVal γ := by
      unfold sTrueRawVal
      rw [Fin.sum_univ_three, hpow_sq]
      dsimp only
      rw [hm 0, hm 1, hm 2]
      have b0 := (axisCmpDMag_bounds_of_lt_128 (bitsVal fun b ↦
        γ (p57ProjW 0 b)) (shellMagCoord3 u22 0) (γ (p57S3W 0)).val (s3ShellMagCoord3_lt_128 u22
        0)).1
      have b1 := (axisCmpDMag_bounds_of_lt_128 (bitsVal fun b ↦
        γ (p57ProjW 1 b)) (shellMagCoord3 u22 1) (γ (p57S3W 1)).val (s3ShellMagCoord3_lt_128 u22
        1)).1
      have b2 := (axisCmpDMag_bounds_of_lt_128 (bitsVal fun b ↦
        γ (p57ProjW 2 b)) (shellMagCoord3 u22 2) (γ (p57S3W 2)).val (s3ShellMagCoord3_lt_128 u22
        2)).1
      rcases le_max_iff.mp hmax with hm0 | hm12
      · have hle := le_trans hm0 b0
        have hsq := Nat.mul_le_mul hle hle
        omega
      · rcases le_max_iff.mp hm12 with hm1 | hm2
        · have hle := le_trans hm1 b1
          have hsq := Nat.mul_le_mul hle hle
          omega
        · have hle := le_trans hm2 b2
          have hsq := Nat.mul_le_mul hle hle
          omega
    have hs0 : 0 < sTrueRawVal γ := lt_of_lt_of_le (Nat.two_pow_pos (2 * mu)) hs_ge
    have hs18 : sTrueRawVal γ < 2 ^ 18 := sTrueRawVal_lt_two_pow_18 γ
    have hhi := (clz18Log2_bounds hs0 hs18).2
    by_contra hlt
    have hle_exp : clz18Log2 (sTrueRawVal γ) + 1 ≤ 2 * mu := by omega
    have hpow_le : 2 ^ (clz18Log2 (sTrueRawVal γ) + 1) ≤ 2 ^ (2 * mu) :=
      Nat.pow_le_pow_right (by decide) hle_exp
    omega
  · rw [ite_eq_right hcond, mul_zero] at hvs
    exact absurd hvs zero_ne_one

/-- `59`-`TempAnd` (`82`-alloc) left-normalizing barrel shifter following `clz18Ops` (`top =
  40`). -/
def barrel59Ops : List MicroOp := [ .zeroAlloc, .cnotW 18 40, .cnotW 33 40, .cnotW 31 40,
    .cnotW 29 40, .cnotW 27 40, .cnotW 25 40, .cnotW 23 40, .cnotW 21 40, .cnotW 19 40,
    .zeroAlloc, .cnotW 33 41, .cnotW 32 41, .cnotW 29 41, .cnotW 28 41, .cnotW 25 41, .cnotW
    24 41, .cnotW 21 41, .cnotW 20 41, .zeroAlloc, .cnotW 33 42, .cnotW 32 42, .cnotW 31 42,
    .cnotW 30 42, .cnotW 25 42, .cnotW 24 42, .cnotW 23 42, .cnotW 22 42, .zeroAlloc, .cnotW
    33 43, .cnotW 32 43, .cnotW 31 43, .cnotW 30 43, .cnotW 29 43, .cnotW 28 43, .cnotW 27 43,
    .cnotW 26 43, .zeroAlloc, .cnotW 18 44, .cnotW 34 44, .zeroAlloc, .cnotW 0 45, .zeroAlloc,
    .cnotW 1 46, .zeroAlloc, .cnotW 2 47, .zeroAlloc, .cnotW 3 48, .zeroAlloc, .cnotW 4 49,
    .zeroAlloc, .cnotW 5 50, .zeroAlloc, .cnotW 6 51, .zeroAlloc, .cnotW 7 52, .zeroAlloc,
    .cnotW 8 53, .zeroAlloc, .cnotW 9 54, .zeroAlloc, .cnotW 10 55, .zeroAlloc, .cnotW 11 56,
    .zeroAlloc, .cnotW 12 57, .zeroAlloc, .cnotW 13 58, .zeroAlloc, .cnotW 14 59, .zeroAlloc,
    .cnotW 15 60, .zeroAlloc, .cnotW 16 61, .zeroAlloc, .cnotW 17 62, .andAlloc 44 45,
    .andAlloc 44 46, .cnotW 63 45, .cnotW 64 46, .cnotW 63 61, .cnotW 64 62, .andAlloc 43 45,
    .andAlloc 43 46, .andAlloc 43 47, .andAlloc 43 48, .andAlloc 43 49, .andAlloc 43 50,
    .andAlloc 43 51, .andAlloc 43 52, .andAlloc 43 53, .andAlloc 43 54, .cnotW 65 45, .cnotW
    66 46, .cnotW 67 47, .cnotW 68 48, .cnotW 69 49, .cnotW 70 50, .cnotW 71 51, .cnotW 72 52,
    .cnotW 73 53, .cnotW 65 53, .cnotW 74 54, .cnotW 66 54, .cnotW 67 55, .cnotW 68 56, .cnotW
    69 57, .cnotW 70 58, .cnotW 71 59, .cnotW 72 60, .cnotW 73 61, .cnotW 74 62, .andAlloc 42
    45, .andAlloc 42 46, .andAlloc 42 47, .andAlloc 42 48, .andAlloc 42 49, .andAlloc 42 50,
    .andAlloc 42 51, .andAlloc 42 52, .andAlloc 42 53, .andAlloc 42 54, .andAlloc 42 55,
    .andAlloc 42 56, .andAlloc 42 57, .andAlloc 42 58, .cnotW 75 45, .cnotW 76 46, .cnotW 77
    47, .cnotW 78 48, .cnotW 79 49, .cnotW 75 49, .cnotW 80 50, .cnotW 76 50, .cnotW 81 51,
    .cnotW 77 51, .cnotW 82 52, .cnotW 78 52, .cnotW 83 53, .cnotW 79 53, .cnotW 84 54, .cnotW
    80 54, .cnotW 85 55, .cnotW 81 55, .cnotW 86 56, .cnotW 82 56, .cnotW 87 57, .cnotW 83 57,
    .cnotW 88 58, .cnotW 84 58, .cnotW 85 59, .cnotW 86 60, .cnotW 87 61, .cnotW 88 62,
    .andAlloc 41 45, .andAlloc 41 46, .andAlloc 41 47, .andAlloc 41 48, .andAlloc 41 49,
    .andAlloc 41 50, .andAlloc 41 51, .andAlloc 41 52, .andAlloc 41 53, .andAlloc 41 54,
    .andAlloc 41 55, .andAlloc 41 56, .andAlloc 41 57, .andAlloc 41 58, .andAlloc 41 59,
    .andAlloc 41 60, .cnotW 89 45, .cnotW 90 46, .cnotW 91 47, .cnotW 89 47, .cnotW 92 48,
    .cnotW 90 48, .cnotW 93 49, .cnotW 91 49, .cnotW 94 50, .cnotW 92 50, .cnotW 95 51, .cnotW
    93 51, .cnotW 96 52, .cnotW 94 52, .cnotW 97 53, .cnotW 95 53, .cnotW 98 54, .cnotW 96 54,
    .cnotW 99 55, .cnotW 97 55, .cnotW 100 56, .cnotW 98 56, .cnotW 101 57, .cnotW 99 57,
    .cnotW 102 58, .cnotW 100 58, .cnotW 103 59, .cnotW 101 59, .cnotW 104 60, .cnotW 102 60,
    .cnotW 103 61, .cnotW 104 62, .andAlloc 40 45, .andAlloc 40 46, .andAlloc 40 47, .andAlloc
    40 48, .andAlloc 40 49, .andAlloc 40 50, .andAlloc 40 51, .andAlloc 40 52, .andAlloc 40
    53, .andAlloc 40 54, .andAlloc 40 55, .andAlloc 40 56, .andAlloc 40 57, .andAlloc 40 58,
    .andAlloc 40 59, .andAlloc 40 60, .andAlloc 40 61, .cnotW 105 45, .cnotW 106 46, .cnotW
    105 46, .cnotW 107 47, .cnotW 106 47, .cnotW 108 48, .cnotW 107 48, .cnotW 109 49, .cnotW
    108 49, .cnotW 110 50, .cnotW 109 50, .cnotW 111 51, .cnotW 110 51, .cnotW 112 52, .cnotW
    111 52, .cnotW 113 53, .cnotW 112 53, .cnotW 114 54, .cnotW 113 54, .cnotW 115 55, .cnotW
    114 55, .cnotW 116 56, .cnotW 115 56, .cnotW 117 57, .cnotW 116 57, .cnotW 118 58, .cnotW
    117 58, .cnotW 119 59, .cnotW 118 59, .cnotW 120 60, .cnotW 119 60, .cnotW 121 61, .cnotW
    120 61, .cnotW 121 62 ]

theorem barrel59Ops_meta : microValid 40 barrel59Ops = true ∧ microAllocs barrel59Ops = 82 ∧
    microAnds barrel59Ops = 59 := by
  decide

/-- Compact `20`-alloc (`15`-`TempAnd`) `e - 2 * mu` subtractor and `18`-output one-hot decoder
  (`top = 8`). -/
def subDOh18_15Ops : List MicroOp := [ .zeroAlloc, .cnotW 4 8, .cnotW 0 8, .notW 4, .andAlloc
    4 0, .notW 4, .zeroAlloc, .cnotW 1 10, .cnotW 9 10, .notW 9, .cnotW 5 9, .andAlloc 9 10,
    .cnotW 5 9, .notW 9, .cnotW 9 11, .cnotW 5 10, .zeroAlloc, .cnotW 2 12, .cnotW 11 12,
    .notW 11, .cnotW 6 11, .andAlloc 11 12, .cnotW 6 11, .notW 11, .cnotW 11 13, .cnotW 6 12,
    .cnotW 7 13, .andAlloc 10 8, .zeroAlloc, .notW 15, .cnotW 10 15, .cnotW 8 15, .cnotW 14
    15, .cnotW 14 8, .cnotW 14 10, .andAlloc 12 15, .andAlloc 12 8, .andAlloc 12 10, .cnotW 16
    12, .cnotW 17 12, .cnotW 18 12, .cnotW 16 15, .cnotW 13 15, .cnotW 17 8, .cnotW 18 10,
    .cnotW 12 14, .andAlloc 15 3, .andAlloc 8 3, .andAlloc 10 3, .andAlloc 14 3, .andAlloc 16
    3, .andAlloc 17 3, .andAlloc 18 3, .andAlloc 12 3, .zeroAlloc, .cnotW 3 27, .cnotW 19 27,
    .cnotW 20 27, .cnotW 21 27, .cnotW 22 27, .cnotW 23 27, .cnotW 24 27, .cnotW 25 27, .cnotW
    26 27, .cnotW 19 15, .cnotW 20 8, .cnotW 21 10, .cnotW 22 14, .cnotW 23 16, .cnotW 24 17,
    .cnotW 25 18, .cnotW 26 12, .cnotW 27 13 ]

/-- Output slot indices `oh_0 .. oh_17` produced by `subDOh18_15Ops` (`top = 8`). -/
def subDOh18_15Slot (d : Fin 18) : ℕ :=
  let slots : List ℕ := [15, 19, 8, 20, 10, 21, 14, 22, 16, 23, 17, 24, 18, 25, 12, 26, 13, 27]
  slots.getD d.val 0

theorem subDOh18_15Ops_meta : microValid 8 subDOh18_15Ops = true ∧ microAllocs subDOh18_15Ops
    = 20 ∧ microAnds subDOh18_15Ops = 15 := by
  decide

/-- Per-input check predicate for `subDOh18_15Ops` on valid `(mu < 7, 2 * mu <= e <= 17)`. -/
def subDOh18_15Check (m : ℕ) : Bool :=
  let st := evalMicroList 8 subDOh18_15Ops (initBoolList 8 (8 + 20) m)
  let mu := m % 8
  let e := m / 8
  allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) &&
  decide (mu < 7 ∧ 2 * mu ≤ e ∧ e ≤ 17 →
    allBelow 18 (fun d ↦
      getBoolAt st (subDOh18_15Slot ⟨d % 18, Nat.mod_lt d (by decide)⟩) ==
        decide (e - 2 * mu = d)))

/-- Strict counterpart of `subDOh18_15Check` avoiding `let` zeta-duplication in `whnf`. -/
def subDOh18_15CheckStrict (m : ℕ) : Bool :=
  match some (evalMicroListStrict 8 subDOh18_15Ops (initBoolList 8 (8 + 20) m)) with
  | none => false
  | some st =>
      let mu := m % 8
      let e := m / 8
      allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) &&
      decide (mu < 7 ∧ 2 * mu ≤ e ∧ e ≤ 17 →
        allBelow 18 (fun d ↦
          getBoolAt st (subDOh18_15Slot ⟨d % 18, Nat.mod_lt d (by decide)⟩) ==
            decide (e - 2 * mu = d)))

theorem subDOh18_15CheckStrict_eq (m : ℕ) : subDOh18_15CheckStrict m = subDOh18_15Check m := by
  simp only [subDOh18_15CheckStrict, subDOh18_15Check, evalMicroListStrict_eq]

set_option maxHeartbeats 800000 in
-- Chunked 256-case evaluation certificate for 15-op sub-DOh18 block.
theorem subDOh18_15Ops_eval_ok : allBelow 256 subDOh18_15Check = true := by
  have hok : allBelow 256 subDOh18_15CheckStrict = true :=
    allBelowFrom_chunks4 0 64 subDOh18_15CheckStrict
      (allBelowFrom_chunks4 0 16 subDOh18_15CheckStrict
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (allBelowFrom_chunks4 64 16 subDOh18_15CheckStrict
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (allBelowFrom_chunks4 128 16 subDOh18_15CheckStrict
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (allBelowFrom_chunks4 192 16 subDOh18_15CheckStrict
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  rw [allBelow_iff]
  intro m hm
  rw [← subDOh18_15CheckStrict_eq]
  exact (allBelow_iff 256 subDOh18_15CheckStrict).mp hok m hm

theorem subDOh18_15Ops_spec (m : ℕ) (hm : m < 256) :
    let st := evalMicroList 8 subDOh18_15Ops (initBoolList 8 (8 + 20) m)
    let mu := m % 8
    let e := m / 8
    allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) = true ∧
    (mu < 7 → 2 * mu ≤ e → e ≤ 17 →
      ∀ d : Fin 18, getBoolAt st (subDOh18_15Slot d) = decide (e - 2 * mu = d.val)) := by
  have h := (allBelow_iff 256 subDOh18_15Check).mp subDOh18_15Ops_eval_ok m hm
  dsimp only [subDOh18_15Check] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun hmu hle he17 d ↦ ?_⟩
  have hd := (allBelow_iff 18 _).mp (h.2 ⟨hmu, hle, he17⟩) d.val d.isLt
  have hd_eq : (⟨d.val % 18, Nat.mod_lt d.val (by decide)⟩ : Fin 18) = d :=
    Fin.ext (Nat.mod_eq_of_lt d.isLt)
  rw [hd_eq] at hd
  simpa [beq_iff_eq] using hd

theorem projNe128Ops_spec (m : ℕ) (hm : m < 256) :
    let st := evalMicroList 8 projNe128Ops (initBoolList 8 (8 + 7) m)
    allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) = true ∧
    getBoolAt st projNe128OutSlot = decide (m ≠ 128) := by
  have h := (allBelow_iff 256 _).mp projNe128Ops_eval_check m hm
  dsimp only at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem evalMicroList_append :
    ∀ (ops₁ ops₂ : List MicroOp) (top : ℕ) (st : List Bool),
      evalMicroList top (ops₁ ++ ops₂) st =
        evalMicroList (top + microAllocs ops₁) ops₂ (evalMicroList top ops₁ st)
  | [], _, top, st => by simp [evalMicroList, microAllocs]
  | .notW a :: rest, ops₂, top, st => by
      simpa [evalMicroList, microAllocs] using evalMicroList_append rest ops₂ top _
  | .cnotW a b :: rest, ops₂, top, st => by
      simpa [evalMicroList, microAllocs] using evalMicroList_append rest ops₂ top _
  | .andAlloc a b :: rest, ops₂, top, st => by
      have ih := evalMicroList_append rest ops₂ (top + 1)
        (setBoolAt st top (getBoolAt st a && getBoolAt st b))
      have htop : top + 1 + microAllocs rest = top + microAllocs (.andAlloc a b :: rest) := by
        dsimp [microAllocs]; omega
      rw [htop] at ih
      exact ih
  | .zeroAlloc :: rest, ops₂, top, st => by
      have ih := evalMicroList_append rest ops₂ (top + 1) (setBoolAt st top false)
      have htop : top + 1 + microAllocs rest = top + microAllocs (.zeroAlloc :: rest) := by
        dsimp [microAllocs]; omega
      rw [htop] at ih
      exact ih

private theorem getBoolAt_setBoolAt_congr {st₁ st₂ : List Bool} {idx top' : ℕ} {v₁ v₂ : Bool}
    (hidx : idx < top') (hl₁ : top' ≤ st₁.length) (hl₂ : top' ≤ st₂.length) (hv : v₁ = v₂)
    (hEq : ∀ k, k < top' → k ≠ idx → getBoolAt st₁ k = getBoolAt st₂ k)
    {k : ℕ} (hk : k < top') :
    getBoolAt (setBoolAt st₁ idx v₁) k = getBoolAt (setBoolAt st₂ idx v₂) k := by
  rw [getBoolAt_setBoolAt st₁ idx k (lt_of_lt_of_le hidx hl₁),
    getBoolAt_setBoolAt st₂ idx k (lt_of_lt_of_le hidx hl₂)]
  by_cases hki : k = idx
  · simp only [hki, ↓reduceIte, hv]
  · simp only [hki, ↓reduceIte, hEq k hk hki]

theorem evalMicroList_ext_below :
    ∀ (ops : List MicroOp) (top : ℕ) (st₁ st₂ : List Bool),
      microValid top ops = true →
      top + microAllocs ops ≤ st₁.length →
      top + microAllocs ops ≤ st₂.length →
      (∀ i, i < top → getBoolAt st₁ i = getBoolAt st₂ i) →
      ∀ i, i < top + microAllocs ops →
        getBoolAt (evalMicroList top ops st₁) i = getBoolAt (evalMicroList top ops st₂) i
  | [], top, _, _, _, _, _, hEq, i, hi => by
      dsimp [microAllocs] at hi
      exact hEq i (by omega)
  | .notW a :: rest, top, st₁, st₂, hv, hl₁, hl₂, hEq, i, hi => by
      dsimp [microValid] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      refine evalMicroList_ext_below rest top _ _ hv.2
        (by rw [length_setBoolAt]; exact hl₁) (by rw [length_setBoolAt]; exact hl₂)
        (fun k hk ↦ getBoolAt_setBoolAt_congr hv.1 (by omega) (by omega) (by rw [hEq a hv.1])
          (fun m hm _ ↦ hEq m hm) hk) i hi
  | .cnotW a b :: rest, top, st₁, st₂, hv, hl₁, hl₂, hEq, i, hi => by
      dsimp [microValid] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      refine evalMicroList_ext_below rest top _ _ hv.2
        (by rw [length_setBoolAt]; exact hl₁) (by rw [length_setBoolAt]; exact hl₂)
        (fun k hk ↦ getBoolAt_setBoolAt_congr hv.1.1.2 (by omega) (by omega)
          (by rw [hEq b hv.1.1.2, hEq a hv.1.1.1]) (fun m hm _ ↦ hEq m hm) hk) i hi
  | .andAlloc a b :: rest, top, st₁, st₂, hv, hl₁, hl₂, hEq, i, hi => by
      dsimp [microValid] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      dsimp [microAllocs] at hl₁ hl₂ hi
      refine evalMicroList_ext_below rest (top + 1) _ _ hv.2
        (by rw [length_setBoolAt]; omega) (by rw [length_setBoolAt]; omega)
        (fun k hk ↦ getBoolAt_setBoolAt_congr (Nat.lt_succ_self top) (by omega) (by omega)
          (by rw [hEq a hv.1.1.1, hEq b hv.1.1.2])
          (fun m hm hne ↦ hEq m (by omega)) hk) i (by omega)
  | .zeroAlloc :: rest, top, st₁, st₂, hv, hl₁, hl₂, hEq, i, hi => by
      dsimp [microValid] at hv
      dsimp [microAllocs] at hl₁ hl₂ hi
      refine evalMicroList_ext_below rest (top + 1) _ _ hv
        (by rw [length_setBoolAt]; omega) (by rw [length_setBoolAt]; omega)
        (fun k hk ↦ getBoolAt_setBoolAt_congr (Nat.lt_succ_self top) (by omega) (by omega) rfl
          (fun m hm hne ↦ hEq m (by omega)) hk) i (by omega)

/-- Full `75`-`TempAnd` (`104`-alloc) `clz18Ops ++ barrel59Ops` list. -/
def clzBarrelOps : List MicroOp := clz18Ops ++ barrel59Ops

/-- Symbolic affine `GF(2)` expression `c ^^ sum_i (cs[i] && x_i)` for `18`-branch priority
  verification. -/
abbrev Aff18 := Bool × List Bool

/-- Constant-`false` `Aff18` expression. -/
def affZero : Aff18 := (false, [])

/-- Constant `Aff18` expression. -/
def affConst (b : Bool) : Aff18 := (b, [])

/-- Coordinate variable `x_i` as an `Aff18` expression. -/
def affVar (i : ℕ) : Aff18 := (false, List.replicate i false ++ [true])

/-- Evaluate a coefficient list against bit assignment `x` starting at variable `idx`. -/
def evalCoeffs (x : ℕ → Bool) : ℕ → List Bool → Bool
  | _, [] => false
  | idx, c :: cs => (c && x idx) ^^ evalCoeffs x (idx + 1) cs

/-- Evaluate an `Aff18` expression against bit assignment `x`. -/
def evalAff (x : ℕ → Bool) (a : Aff18) : Bool := a.1 ^^ evalCoeffs x 0 a.2

/-- Pointwise XOR of two `GF(2)` coefficient lists. -/
def xorCoeffs : List Bool → List Bool → List Bool
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ^^ y) :: xorCoeffs xs ys

/-- Negation of an `Aff18` expression. -/
def affNot (a : Aff18) : Aff18 := (Bool.not a.1, a.2)

/-- XOR of two `Aff18` expressions. -/
def affXor (a b : Aff18) : Aff18 := (a.1 ^^ b.1, xorCoeffs a.2 b.2)

/-- Check that all variable coefficients are `false`. -/
def isConstCoeffs : List Bool → Bool
  | [] => true
  | false :: cs => isConstCoeffs cs
  | true :: _ => false

/-- Check that an `Aff18` expression has zero variable dependence. -/
def isConstAff (a : Aff18) : Bool := isConstCoeffs a.2

/-- Extensional equality of coefficient lists up to trailing `false`s. -/
def eqCoeffs : List Bool → List Bool → Bool
  | [], ys => isConstCoeffs ys
  | xs, [] => isConstCoeffs xs
  | x :: xs, y :: ys => (x == y) && eqCoeffs xs ys

/-- Extensional equality of `Aff18` expressions. -/
def eqAff (a b : Aff18) : Bool := (a.1 == b.1) && eqCoeffs a.2 b.2

/-- Lookup slot `k` in a `List Aff18` (defaulting to `affZero`). -/
def getAffAt : List Aff18 → ℕ → Aff18
  | [], _ => affZero
  | a :: _, 0 => a
  | _ :: as, k + 1 => getAffAt as k

/-- Update slot `k` in a `List Aff18`. -/
def setAffAt : List Aff18 → ℕ → Aff18 → List Aff18
  | [], _, _ => []
  | _ :: as, 0, v => v :: as
  | a :: as, k + 1, v => a :: setAffAt as k v

/-- WHNF-strict normalizer for `List Bool`. -/
def strictBoolList : List Bool → List Bool
  | [] => []
  | true :: bs => match strictBoolList bs with | bs' => true :: bs'
  | false :: bs => match strictBoolList bs with | bs' => false :: bs'

/-- WHNF-strict normalizer for `Aff18`. -/
def strictAff : Aff18 → Aff18
  | (true, bs) => match strictBoolList bs with | bs' => (true, bs')
  | (false, bs) => match strictBoolList bs with | bs' => (false, bs')

/-- WHNF-strict update on `List Aff18` preventing symbolic AST buildup during `decide`. -/
def setAffAtStrict : List Aff18 → ℕ → Aff18 → List Aff18
  | [], _, _ => []
  | _ :: as, 0, v => match strictAff v with | v' => v' :: as
  | a :: as, k + 1, v => match setAffAtStrict as k v with | as' => a :: as'

theorem strictBoolList_eq : ∀ bs : List Bool, strictBoolList bs = bs
  | [] => rfl
  | true :: bs => by dsimp [strictBoolList]; rw [strictBoolList_eq bs]
  | false :: bs => by dsimp [strictBoolList]; rw [strictBoolList_eq bs]

theorem strictAff_eq : ∀ v : Aff18, strictAff v = v
  | (true, bs) => by dsimp [strictAff]; rw [strictBoolList_eq bs]
  | (false, bs) => by dsimp [strictAff]; rw [strictBoolList_eq bs]

theorem setAffAtStrict_eq : ∀ (st : List Aff18) (k : ℕ) (v : Aff18),
    setAffAtStrict st k v = setAffAt st k v
  | [], _, _ => rfl
  | _ :: _, 0, v => by dsimp [setAffAtStrict, setAffAt]; rw [strictAff_eq v]
  | _ :: as, k + 1, v => by dsimp [setAffAtStrict, setAffAt]; rw [setAffAtStrict_eq as k v]

/-- Symbolic affine evaluator for `List MicroOp` (succeeds whenever every AND has a constant
  operand). -/
def evalMicroAff : ℕ → List MicroOp → List Aff18 → Option (List Aff18)
  | _, [], st => some st
  | top, .notW a :: rest, st =>
      evalMicroAff top rest (setAffAt st a (affNot (getAffAt st a)))
  | top, .cnotW a b :: rest, st =>
      evalMicroAff top rest (setAffAt st b (affXor (getAffAt st b) (getAffAt st a)))
  | top, .andAlloc a b :: rest, st =>
      let va := getAffAt st a
      let vb := getAffAt st b
      if isConstAff va then
        evalMicroAff (top + 1) rest (setAffAt st top (if va.1 then vb else affZero))
      else if isConstAff vb then
        evalMicroAff (top + 1) rest (setAffAt st top (if vb.1 then va else affZero))
      else none
  | top, .zeroAlloc :: rest, st =>
      evalMicroAff (top + 1) rest (setAffAt st top affZero)

/-- WHNF-strict counterpart of `evalMicroAff` for fast kernel `decide`. -/
def evalMicroAffStrict : ℕ → List MicroOp → List Aff18 → Option (List Aff18)
  | _, [], st => some st
  | top, .notW a :: rest, st =>
      evalMicroAffStrict top rest (setAffAtStrict st a (affNot (getAffAt st a)))
  | top, .cnotW a b :: rest, st =>
      evalMicroAffStrict top rest (setAffAtStrict st b (affXor (getAffAt st b) (getAffAt st a)))
  | top, .andAlloc a b :: rest, st =>
      let va := getAffAt st a
      let vb := getAffAt st b
      if isConstAff va then
        evalMicroAffStrict (top + 1) rest (setAffAtStrict st top (if va.1 then vb else affZero))
      else if isConstAff vb then
        evalMicroAffStrict (top + 1) rest (setAffAtStrict st top (if vb.1 then va else affZero))
      else none
  | top, .zeroAlloc :: rest, st =>
      evalMicroAffStrict (top + 1) rest (setAffAtStrict st top affZero)

theorem evalMicroAffStrict_eq :
    ∀ (ops : List MicroOp) (top : ℕ) (st : List Aff18),
      evalMicroAffStrict top ops st = evalMicroAff top ops st
  | [], _, _ => rfl
  | .notW _ :: rest, top, _ => by
      simp only [evalMicroAffStrict, evalMicroAff, setAffAtStrict_eq]
      exact evalMicroAffStrict_eq rest top _
  | .cnotW _ _ :: rest, top, _ => by
      simp only [evalMicroAffStrict, evalMicroAff, setAffAtStrict_eq]
      exact evalMicroAffStrict_eq rest top _
  | .andAlloc a b :: rest, top, st => by
      dsimp only [evalMicroAffStrict, evalMicroAff]
      by_cases ha : isConstAff (getAffAt st a)
      · simp only [ha, ↓reduceIte, setAffAtStrict_eq, evalMicroAffStrict_eq rest (top + 1)]
      · by_cases hb : isConstAff (getAffAt st b) <;>
          simp only [ha, hb, Bool.false_eq_true, ↓reduceIte, setAffAtStrict_eq,
            evalMicroAffStrict_eq rest (top + 1)]
  | .zeroAlloc :: rest, top, _ => by
      simp only [evalMicroAffStrict, evalMicroAff, setAffAtStrict_eq]
      exact evalMicroAffStrict_eq rest (top + 1) _

theorem evalCoeffs_var (x : ℕ → Bool) :
    ∀ (i idx : ℕ), evalCoeffs x idx (List.replicate i false ++ [true]) = x (idx + i)
  | 0, idx => by simp [evalCoeffs]
  | i + 1, idx => by
      simp [List.replicate_succ, evalCoeffs, evalCoeffs_var x i (idx + 1), Nat.add_right_comm,
        Nat.add_assoc]

theorem evalAff_zero (x : ℕ → Bool) : evalAff x affZero = false := rfl

theorem evalAff_const (x : ℕ → Bool) (b : Bool) : evalAff x (affConst b) = b := by
  cases b <;> rfl

theorem evalAff_var (x : ℕ → Bool) (i : ℕ) : evalAff x (affVar i) = x i := by
  simp [evalAff, affVar, evalCoeffs_var]

theorem evalCoeffs_xor (x : ℕ → Bool) :
    ∀ (xs ys : List Bool) (idx : ℕ),
      evalCoeffs x idx (xorCoeffs xs ys) = (evalCoeffs x idx xs ^^ evalCoeffs x idx ys)
  | [], ys, idx => by simp [xorCoeffs, evalCoeffs]
  | x0 :: xs, [], idx => by simp [xorCoeffs, evalCoeffs]
  | x0 :: xs, y0 :: ys, idx => by
      dsimp only [xorCoeffs, evalCoeffs]
      rw [evalCoeffs_xor x xs ys (idx + 1)]
      cases x0 <;> cases y0 <;> cases x idx <;>
        cases evalCoeffs x (idx + 1) xs <;> cases evalCoeffs x (idx + 1) ys <;> rfl

theorem evalAff_not (x : ℕ → Bool) (a : Aff18) : evalAff x (affNot a) = Bool.not (evalAff x a) := by
  dsimp [evalAff, affNot]
  cases a.1 <;> cases evalCoeffs x 0 a.2 <;> rfl

theorem evalAff_xor (x : ℕ → Bool) (a b : Aff18) :
    evalAff x (affXor a b) = (evalAff x a ^^ evalAff x b) := by
  dsimp [evalAff, affXor]
  rw [evalCoeffs_xor]
  cases a.1 <;> cases b.1 <;> cases evalCoeffs x 0 a.2 <;> cases evalCoeffs x 0 b.2 <;> rfl

theorem evalCoeffs_of_isConst (x : ℕ → Bool) :
    ∀ (cs : List Bool) (idx : ℕ), isConstCoeffs cs = true → evalCoeffs x idx cs = false
  | [], _, _ => rfl
  | false :: cs, idx, h => by
      simp only [evalCoeffs, Bool.false_and, Bool.false_xor]
      exact evalCoeffs_of_isConst x cs (idx + 1) h
  | true :: _, _, h => Bool.noConfusion h

theorem evalAff_of_isConst (x : ℕ → Bool) {a : Aff18} (ha : isConstAff a = true) :
    evalAff x a = a.1 := by
  dsimp [evalAff, isConstAff] at ha ⊢
  rw [evalCoeffs_of_isConst x a.2 0 ha, Bool.xor_false]

theorem evalCoeffs_of_eqCoeffs (x : ℕ → Bool) :
    ∀ (xs ys : List Bool) (idx : ℕ),
      eqCoeffs xs ys = true → evalCoeffs x idx xs = evalCoeffs x idx ys
  | [], ys, idx, h => (evalCoeffs_of_isConst x ys idx h).symm
  | x0 :: xs, [], idx, h => evalCoeffs_of_isConst x (x0 :: xs) idx h
  | x0 :: xs, y0 :: ys, idx, h => by
      dsimp [eqCoeffs] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      dsimp [evalCoeffs]
      rw [h.1, evalCoeffs_of_eqCoeffs x xs ys (idx + 1) h.2]

theorem evalAff_of_eqAff (x : ℕ → Bool) {a b : Aff18} (h : eqAff a b = true) :
    evalAff x a = evalAff x b := by
  dsimp [eqAff, evalAff] at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, evalCoeffs_of_eqCoeffs x a.2 b.2 0 h.2]

theorem getBoolAt_map_evalAff (x : ℕ → Bool) :
    ∀ (st : List Aff18) (k : ℕ),
      getBoolAt (st.map (evalAff x)) k = evalAff x (getAffAt st k)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, k + 1 => getBoolAt_map_evalAff x as k

theorem map_setAffAt_evalAff (x : ℕ → Bool) :
    ∀ (st : List Aff18) (k : ℕ) (v : Aff18),
      (setAffAt st k v).map (evalAff x) = setBoolAt (st.map (evalAff x)) k (evalAff x v)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, k + 1, v => by simp [setAffAt, setBoolAt, map_setAffAt_evalAff x as k v]

theorem evalMicroAff_sound (x : ℕ → Bool) :
    ∀ (ops : List MicroOp) (top : ℕ) (st stOut : List Aff18),
      evalMicroAff top ops st = some stOut →
      stOut.map (evalAff x) = evalMicroList top ops (st.map (evalAff x))
  | [], _, st, stOut, h => by injection h with h'; subst h'; rfl
  | .notW a :: rest, top, st, stOut, h => by
      dsimp only [evalMicroAff] at h
      dsimp only [evalMicroList]
      rw [evalMicroAff_sound x rest top _ stOut h, map_setAffAt_evalAff,
        getBoolAt_map_evalAff, evalAff_not]
  | .cnotW a b :: rest, top, st, stOut, h => by
      dsimp only [evalMicroAff] at h
      dsimp only [evalMicroList]
      rw [evalMicroAff_sound x rest top _ stOut h, map_setAffAt_evalAff,
        getBoolAt_map_evalAff, getBoolAt_map_evalAff, evalAff_xor]
  | .andAlloc a b :: rest, top, st, stOut, h => by
      dsimp only [evalMicroAff] at h
      dsimp only [evalMicroList]
      by_cases ha : isConstAff (getAffAt st a) = true
      · rw [ite_eq_left ha] at h
        rw [evalMicroAff_sound x rest (top + 1) _ stOut h, map_setAffAt_evalAff,
          getBoolAt_map_evalAff, getBoolAt_map_evalAff, evalAff_of_isConst x ha]
        cases (getAffAt st a).1 <;> simp [evalAff_zero]
      · rw [ite_eq_right ha] at h
        by_cases hb : isConstAff (getAffAt st b) = true
        · rw [ite_eq_left hb] at h
          rw [evalMicroAff_sound x rest (top + 1) _ stOut h, map_setAffAt_evalAff,
            getBoolAt_map_evalAff, getBoolAt_map_evalAff, evalAff_of_isConst x hb]
          cases (getAffAt st b).1 <;> simp [evalAff_zero]
        · rw [ite_eq_right hb] at h
          cases h
  | .zeroAlloc :: rest, top, st, stOut, h => by
      dsimp only [evalMicroAff] at h
      dsimp only [evalMicroList]
      rw [evalMicroAff_sound x rest (top + 1) _ stOut h, map_setAffAt_evalAff, evalAff_zero]

/-- Expected `Aff18` input slot `i` on priority branch `k = clz18Log2 s`. -/
def expectedInAff18 (k i : ℕ) : Aff18 :=
  if i < k then affVar i else if i = k then affConst true else affZero

/-- Initial `122`-slot `Aff18` state on priority branch `k = clz18Log2 s`. -/
def initAff18 (k : ℕ) : List Aff18 := List.ofFn fun idx : Fin 122 ↦ expectedInAff18 k idx.val

/-- Expected `Aff18` mantissa bit `j` on priority branch `k = clz18Log2 s`. -/
def expectedMantAff18 (k j : ℕ) : Aff18 :=
  let sh := 17 - k
  if j < sh then affZero
  else if j - sh < k then affVar (j - sh)
  else affConst true

/-- Postcondition predicate on the symbolic output state of `clzBarrelOps` for branch `k`. -/
def clzBarrelAffPost (k : ℕ) (st : List Aff18) : Bool :=
  allBelow 18 (fun i ↦ eqAff (getAffAt st i) (expectedInAff18 k i)) &&
  allBelow 5 (fun b ↦ eqAff (getAffAt st (35 + b)) (affConst (k.testBit b))) &&
  allBelow 18 (fun j ↦ eqAff (getAffAt st (45 + j)) (expectedMantAff18 k j))

/-- Branch check for `0 <= k < 18` using `match` (never duplicating `st` under `whnf`). -/
def clzBarrelAffCheck (k : ℕ) : Bool :=
  match evalMicroAffStrict 18 clzBarrelOps (initAff18 k) with
  | none => false
  | some st => clzBarrelAffPost k st

/-- Postcondition predicate for `s = 0`. -/
def clzBarrelZeroPost (st : List Bool) : Bool := allBelow 18 (fun i ↦ getBoolAt st i == false)
    && allBelow 5 (fun b ↦ getBoolAt st (35 + b) == false) && allBelow 18
    (fun j ↦ getBoolAt st (45 + j) == false)

/-- Concrete `s = 0` check for `clzBarrelOps`. -/
def clzBarrelZeroCheck : Bool :=
  match some (evalMicroListStrict 18 clzBarrelOps (initBoolList 18 122 0)) with
  | none => false
  | some st => clzBarrelZeroPost st

theorem clzBarrelZero_ok : clzBarrelZeroCheck = true := by decide

set_option maxHeartbeats 800000 in
-- 18-case affine CLZ barrel evaluation check.
theorem clzBarrelAff_ok : allBelow 18 clzBarrelAffCheck = true := by
  change allBelowFrom clzBarrelAffCheck 0 (16 + 2) = true
  rw [allBelowFrom_add]
  have h0 : allBelowFrom clzBarrelAffCheck 0 16 = true :=
    allBelowFrom_chunks4 0 4 clzBarrelAffCheck
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h1 : allBelowFrom clzBarrelAffCheck 16 2 = true := by decide +kernel
  rw [h0, h1]
  rfl

theorem clz18Log2_testBit_top {s : ℕ} (hs0 : 0 < s) (hs18 : s < 2 ^ 18) : s.testBit
    (clz18Log2 s) = true ∧ ∀ i, clz18Log2 s < i → s.testBit i = false := by
  obtain ⟨hlo, hhi⟩ := clz18Log2_bounds hs0 hs18
  set k := clz18Log2 s
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdiv_ge : 1 ≤ s / 2 ^ k := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  have hdiv_lt : s / 2 ^ k < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by
    have hsucc : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    omega)
  have hdiv1 : s / 2 ^ k = 1 := by omega
  refine ⟨?_, fun i hik ↦ ?_⟩
  · rw [Nat.testBit_eq_decide_div_mod_eq, hdiv1]
    decide
  · have hpow : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hhi hpow)

theorem initAff18_map_eq {s : ℕ} (hs0 : 0 < s) (hs18 : s < 2 ^ 18) :
    (initAff18 (clz18Log2 s)).map (evalAff s.testBit) = initBoolList 18 122 s := by
  obtain ⟨htop, hhi0⟩ := clz18Log2_testBit_top hs0 hs18
  set k := clz18Log2 s
  have hk17 : k ≤ 17 := clz18Log2_le_17 s
  apply List.ext_getElem
  · simp [initAff18, initBoolList, Slot3MicroEngineAux.length_mkBoolList]
  · intro idx h1 h2
    have hidx : idx < 122 := by simpa [initAff18] using h1
    have hget_aux : ∀ (xs : List Bool) (i : ℕ) (hi : i < xs.length), xs[i] = getBoolAt xs i := by
      intro xs
      induction xs with
      | nil => intro _ hi; cases hi
      | cons x xs ih =>
          intro i hi
          cases i with
          | zero => rfl
          | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)
    have hL : ((initAff18 k).map (evalAff s.testBit))[idx]'h1 =
      evalAff s.testBit (expectedInAff18 k idx) := by
      simp only [initAff18, List.getElem_map, List.getElem_ofFn]
    have hR : (initBoolList 18 122 s)[idx]'h2 = (decide (idx < 18) && s.testBit idx) := by
      rw [hget_aux (initBoolList 18 122 s) idx h2]
      simpa [initBoolList] using
        Slot3MicroEngineAux.getBoolAt_mkBoolList 18 s 0 122 idx hidx
    rw [hL, hR]
    dsimp only [expectedInAff18]
    by_cases hlt : idx < k
    · have h18 : idx < 18 := by omega
      simp only [hlt, ↓reduceIte, h18, decide_true, Bool.true_and, evalAff_var]
    · by_cases heq : idx = k
      · have h18 : idx < 18 := by omega
        rw [ite_eq_right hlt, ite_eq_left heq, evalAff_const, decide_eq_true h18,
          Bool.true_and, heq, htop]
      · simp only [hlt, heq, ↓reduceIte, evalAff_zero]
        by_cases h18 : idx < 18
        · simp only [h18, decide_true, Bool.true_and, hhi0 idx (by omega)]
        · simp only [h18, decide_false, Bool.false_and]

theorem clzBarrelOps_spec (s : ℕ) (hs : s < 2 ^ 18) :
    let st := evalMicroList 18 clzBarrelOps (initBoolList 18 122 s)
    allBelow 18 (fun i ↦ getBoolAt st i == s.testBit i) = true ∧
    (∀ b : Fin 5, getBoolAt st (35 + b.val) = (clz18Log2 s).testBit b.val) ∧
    (∀ j : Fin 18, getBoolAt st (45 + j.val) = (norm1sMant18 s).testBit j.val) := by
  by_cases hs0 : s = 0
  · subst hs0
    have h := clzBarrelZero_ok
    dsimp only [clzBarrelZeroCheck, clzBarrelZeroPost] at h
    rw [evalMicroListStrict_eq] at h
    simp only [Bool.and_eq_true] at h
    have he0 : clz18Log2 0 = 0 := by decide
    have hm0 : norm1sMant18 0 = 0 := by decide
    refine ⟨?_, fun b ↦ ?_, fun j ↦ ?_⟩
    · rw [allBelow_iff]
      intro i hi
      have hi0 := (allBelow_iff 18 _).mp h.1.1 i hi
      simpa [Nat.zero_testBit] using hi0
    · have hb0 := of_decide_eq_true ((allBelow_iff 5 _).mp h.1.2 b.val b.isLt)
      rw [hb0, he0, Nat.zero_testBit]
    · have hj0 := of_decide_eq_true ((allBelow_iff 18 _).mp h.2 j.val j.isLt)
      rw [hj0, hm0, Nat.zero_testBit]
  · have hs_pos : 0 < s := Nat.pos_of_ne_zero hs0
    obtain ⟨htop, hhi0⟩ := clz18Log2_testBit_top hs_pos hs
    set k := clz18Log2 s
    have hk18 : k < 18 := Nat.lt_succ_of_le (clz18Log2_le_17 s)
    have hchk := (allBelow_iff 18 clzBarrelAffCheck).mp clzBarrelAff_ok k hk18
    dsimp only [clzBarrelAffCheck] at hchk
    rw [evalMicroAffStrict_eq] at hchk
    cases hAff : evalMicroAff 18 clzBarrelOps (initAff18 k) with
    | none => rw [hAff] at hchk; exact Bool.noConfusion hchk
    | some stA =>
        rw [hAff] at hchk
        dsimp only [clzBarrelAffPost] at hchk
        simp only [Bool.and_eq_true] at hchk
        have hMap : stA.map (evalAff s.testBit) =
            evalMicroList 18 clzBarrelOps (initBoolList 18 122 s) := by
          rw [evalMicroAff_sound s.testBit clzBarrelOps 18 (initAff18 k) stA hAff,
            initAff18_map_eq hs_pos hs]
        have hBit : ∀ idx : ℕ,
            getBoolAt (evalMicroList 18 clzBarrelOps (initBoolList 18 122 s)) idx =
              evalAff s.testBit (getAffAt stA idx) := by
          intro idx
          rw [← hMap, getBoolAt_map_evalAff]
        refine ⟨?_, fun b ↦ ?_, fun j ↦ ?_⟩
        · rw [allBelow_iff]
          intro i hi18
          rw [beq_iff_eq, hBit i,
            evalAff_of_eqAff s.testBit ((allBelow_iff 18 _).mp hchk.1.1 i hi18)]
          dsimp only [expectedInAff18]
          by_cases hik : i < k
          · simp only [hik, ↓reduceIte, evalAff_var]
          · by_cases heq : i = k
            · subst heq; simp only [hik, ↓reduceIte, evalAff_const, htop]
            · simp only [hik, heq, ↓reduceIte, evalAff_zero, hhi0 i (by omega)]
        · rw [hBit (35 + b.val),
            evalAff_of_eqAff s.testBit ((allBelow_iff 5 _).mp hchk.1.2 b.val b.isLt),
            evalAff_const]
        · rw [hBit (45 + j.val),
            evalAff_of_eqAff s.testBit ((allBelow_iff 18 _).mp hchk.2 j.val j.isLt)]
          unfold norm1sMant18 expectedMantAff18
          change _ = (s * 2 ^ (17 - k)).testBit j.val
          set sh := 17 - k
          rw [Nat.testBit_mul_two_pow]
          by_cases hjsh : j.val < sh
          · have hnot : ¬(sh ≤ j.val) := by omega
            simp only [hjsh, ↓reduceIte, evalAff_zero, hnot, decide_false, Bool.false_and]
          · have hle : sh ≤ j.val := by omega
            simp only [hjsh, ↓reduceIte, hle, decide_true, Bool.true_and]
            by_cases hjk : j.val - sh < k
            · simp only [hjk, ↓reduceIte, evalAff_var]
            · have heq : j.val - sh = k := by have := j.isLt; omega
              rw [heq]
              simp only [Nat.lt_irrefl, ↓reduceIte, evalAff_const, htop]

theorem accLoadRowCliff_eval {M : ℕ} (val : ℕ) (oh : Wire M) :
    ∀ (w : ℕ) (thrW : Fin w → Wire M) (_hthr_inj : Function.Injective thrW)
      (hne : ∀ j : Fin w, oh ≠ thrW j) (β : BitAssignment M),
      (∀ q : Wire M, (∀ j : Fin w, q ≠ thrW j) →
        (accLoadRowCliff val oh w thrW hne).eval β q = β q) ∧
      (∀ j : Fin w,
        (accLoadRowCliff val oh w thrW hne).eval β (thrW j) =
          β (thrW j) + if val.testBit j.val then β oh else 0)
  | 0, _, _, _, _ => ⟨fun _ _ ↦ rfl, fun j ↦ Fin.elim0 j⟩
  | w + 1, thrW, hthr_inj, hne, β => by
      have hinj' : Function.Injective (fun j : Fin w ↦ thrW j.succ) :=
        fun a b hab ↦ Fin.succ_injective _ (hthr_inj hab)
      have h0_not_succ : ∀ j : Fin w, thrW 0 ≠ thrW j.succ :=
        fun j h ↦ Fin.succ_ne_zero j (hthr_inj h.symm)
      dsimp only [accLoadRowCliff]
      by_cases hv : val % 2 = 1
      · rw [ite_eq_left hv]
        let β₁ := (CliffProg.cnot oh (thrW 0) (hne 0)).eval β
        obtain ⟨hOut, hIn⟩ := accLoadRowCliff_eval (val / 2) oh w
          (fun j ↦ thrW j.succ) hinj' (fun j ↦ hne j.succ) β₁
        have hβ₁_oh : β₁ oh = β oh := Function.update_of_ne (hne 0) _ _
        refine ⟨fun q hq ↦ ?_, fun j ↦ ?_⟩
        · rw [CliffProg.eval, hOut q (fun j ↦ hq j.succ)]
          exact Function.update_of_ne (hq 0) _ _
        · cases j using Fin.cases with
          | zero =>
              rw [CliffProg.eval, hOut (thrW 0) h0_not_succ]
              dsimp [β₁, CliffProg.eval]
              simp only [Function.update_self, Nat.testBit_zero, hv, decide_true, ↓reduceIte]
          | succ j =>
              rw [CliffProg.eval, hIn j, hβ₁_oh]
              have hβ₁_j : β₁ (thrW j.succ) = β (thrW j.succ) :=
                Function.update_of_ne (h0_not_succ j).symm _ _
              rw [hβ₁_j, Fin.val_succ, Nat.testBit_succ]
      · rw [ite_eq_right hv]
        obtain ⟨hOut, hIn⟩ := accLoadRowCliff_eval (val / 2) oh w
          (fun j ↦ thrW j.succ) hinj' (fun j ↦ hne j.succ) β
        refine ⟨fun q hq ↦ hOut q (fun j ↦ hq j.succ), fun j ↦ ?_⟩
        cases j using Fin.cases with
        | zero =>
            rw [hOut (thrW 0) h0_not_succ, Fin.val_zero, Nat.testBit_zero]
            simp [hv]
        | succ j =>
            rw [hIn j, Fin.val_succ, Nat.testBit_succ]

theorem accLoadThrLoop_eval {M : ℕ} (kBits dCut wAcc : ℕ)
    (thrW : Fin wAcc → Wire M) (hthr_inj : Function.Injective thrW)
    (ohW : Fin 18 → Wire M) (hne : ∀ (d : Fin 18) (j : Fin wAcc), ohW d ≠ thrW j) :
    ∀ (rem : ℕ) (hrem : rem ≤ 18) (β : BitAssignment M),
      let p := accLoadThrLoop kBits dCut wAcc thrW rem hrem ohW hne
      (∀ q : Wire M, (∀ j : Fin wAcc, q ≠ thrW j) → p.eval β q = β q) ∧
      (∀ j : Fin wAcc, p.eval β (thrW j) =
        β (thrW j) +
          ∑ d : Fin 18,
            if 18 - rem ≤ d.val then
              if (accThr kBits dCut d.val).testBit j.val then β (ohW d) else 0
            else 0) := by
  intro rem
  induction rem with
  | zero =>
      intro _ β
      refine ⟨fun _ _ ↦ rfl, fun j ↦ ?_⟩
      have h0 : (∑ d : Fin 18, if 18 - 0 ≤ d.val then if (accThr kBits dCut d.val).testBit
          j.val then β (ohW d) else 0 else 0) = 0 := by
        refine Finset.sum_eq_zero fun d _ ↦ ?_
        have := d.isLt
        rw [ite_eq_right (by omega)]
      rw [h0, add_zero]
      rfl
  | succ rem ih =>
      intro hrem β
      dsimp only [accLoadThrLoop]
      let dIdx : Fin 18 := ⟨18 - (rem + 1), by omega⟩
      obtain ⟨hOut1, hIn1⟩ := accLoadRowCliff_eval (accThr kBits dCut dIdx.val) (ohW dIdx)
        wAcc thrW hthr_inj (fun j ↦ hne dIdx j) β
      let β₁ := (accLoadRowCliff (accThr kBits dCut dIdx.val) (ohW dIdx) wAcc thrW
        (fun j ↦ hne dIdx j)).eval β
      obtain ⟨hOut2, hIn2⟩ := ih (by omega) β₁
      refine ⟨fun q hq ↦ (hOut2 q hq).trans (hOut1 q hq), fun j ↦ ?_⟩
      change (accLoadThrLoop kBits dCut wAcc thrW rem (by omega) ohW hne).eval β₁ (thrW j) = _
      rw [hIn2 j]
      have hβ₁_thr : β₁ (thrW j) = β (thrW j) +
          if (accThr kBits dCut dIdx.val).testBit j.val then β (ohW dIdx) else 0 := hIn1 j
      rw [hβ₁_thr]
      have hoh_pres : ∀ d : Fin 18, β₁ (ohW d) = β (ohW d) := fun d ↦ hOut1 (ohW d) (hne d)
      have hsum_oh : (∑ d : Fin 18, if 18 - rem ≤ d.val then if (accThr kBits dCut
          d.val).testBit j.val then β₁ (ohW d) else 0 else 0) = (∑ d : Fin 18, if 18 - rem ≤
          d.val then if (accThr kBits dCut d.val).testBit j.val then β (ohW d) else 0 else 0)
          :=
        Finset.sum_congr rfl fun d _ ↦ by rw [hoh_pres d]
      rw [hsum_oh, add_assoc]
      apply congrArg (β (thrW j) + ·)
      have hsplit : ∀ d : Fin 18, (if 18 - (rem + 1) ≤ d.val then if (accThr kBits dCut
          d.val).testBit j.val then β (ohW d) else 0 else 0) = (if d = dIdx then if (accThr
          kBits dCut dIdx.val).testBit j.val then β (ohW dIdx) else 0 else 0) + (if 18 - rem ≤
          d.val then if (accThr kBits dCut d.val).testBit j.val then β (ohW d) else 0 else 0)
          := by
        intro d
        by_cases hd : d = dIdx
        · subst hd
          have h1 : 18 - (rem + 1) ≤ dIdx.val := by dsimp [dIdx]; omega
          have h2 : ¬(18 - rem ≤ dIdx.val) := by dsimp [dIdx]; omega
          rw [ite_eq_left h1, ite_eq_left rfl, ite_eq_right h2, add_zero]
        · have hd_ne : d.val ≠ 18 - (rem + 1) := fun hv ↦ hd (Fin.ext hv)
          rw [ite_eq_right hd, zero_add]
          by_cases hle : 18 - rem ≤ d.val
          · have hle' : 18 - (rem + 1) ≤ d.val := by omega
            rw [ite_eq_left hle', ite_eq_left hle]
          · have hle' : ¬(18 - (rem + 1) ≤ d.val) := by omega
            rw [ite_eq_right hle', ite_eq_right hle]
      rw [Finset.sum_congr rfl (fun d _ ↦ hsplit d), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ dIdx
          (fun _ ↦ if (accThr kBits dCut dIdx.val).testBit j.val then β (ohW dIdx) else 0),
        ite_eq_left (Finset.mem_univ dIdx)]

set_option backward.isDefEq.respectTransparency false

theorem n1s_tier_bounds (t : Norm1sTier) : 26 ≤ t.kBits ∧ t.kBits ≤ 30 ∧ 16 ≤ t.dCut ∧ t.dCut
    ≤ 18 ∧ t.wAcc = 20 + t.kBits - t.dCut ∧ t.wAcc ≤ 32 := by
  cases t <;> decide

theorem n1s_norm1sMant18_lt (s : ℕ) (hs : s < 2 ^ 18) : norm1sMant18 s < 2 ^ 18 := by
  by_cases hs0 : s = 0
  · subst hs0; decide
  · exact (norm1sMant18_bounds (Nat.pos_of_ne_zero hs0) hs).2

/-- Check that no `.notW` or `.cnotW` in `ops` mutates a slot `< bound`. -/
def n1sNoMutBelow (bound : ℕ) : List MicroOp → Bool
  | [] => true
  | .notW a :: rest => decide (bound ≤ a) && n1sNoMutBelow bound rest
  | .cnotW _ b :: rest => decide (bound ≤ b) && n1sNoMutBelow bound rest
  | .andAlloc _ _ :: rest => n1sNoMutBelow bound rest
  | .zeroAlloc :: rest => n1sNoMutBelow bound rest

theorem n1s_getBoolAt_setBoolAt_of_ne :
    ∀ (st : List Bool) (k i : ℕ), i ≠ k → ∀ (v : Bool),
      getBoolAt (setBoolAt st k v) i = getBoolAt st i
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, h, _ => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: bs, k + 1, i + 1, h, v =>
      n1s_getBoolAt_setBoolAt_of_ne bs k i (fun heq ↦ h (congrArg Nat.succ heq)) v

theorem n1s_evalMicroList_pres_below :
    ∀ (ops : List MicroOp) (bound top : ℕ) (st : List Bool),
      bound ≤ top →
      n1sNoMutBelow bound ops = true →
      ∀ i, i < bound → getBoolAt (evalMicroList top ops st) i = getBoolAt st i
  | [], _, _, _, _, _, _, _ => rfl
  | .notW a :: rest, bound, top, st, hbt, hnm, i, hi => by
      dsimp [n1sNoMutBelow] at hnm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hnm
      rw [evalMicroList, n1s_evalMicroList_pres_below rest bound top _ hbt hnm.2 i hi,
        n1s_getBoolAt_setBoolAt_of_ne st a i (by omega)]
  | .cnotW a b :: rest, bound, top, st, hbt, hnm, i, hi => by
      dsimp [n1sNoMutBelow] at hnm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hnm
      rw [evalMicroList, n1s_evalMicroList_pres_below rest bound top _ hbt hnm.2 i hi,
        n1s_getBoolAt_setBoolAt_of_ne st b i (by omega)]
  | .andAlloc a b :: rest, bound, top, st, hbt, hnm, i, hi => by
      dsimp [n1sNoMutBelow] at hnm
      rw [evalMicroList, n1s_evalMicroList_pres_below rest bound (top + 1) _ (by omega) hnm i hi,
        n1s_getBoolAt_setBoolAt_of_ne st top i (by omega)]
  | .zeroAlloc :: rest, bound, top, st, hbt, hnm, i, hi => by
      dsimp [n1sNoMutBelow] at hnm
      rw [evalMicroList, n1s_evalMicroList_pres_below rest bound (top + 1) _ (by omega) hnm i hi,
        n1s_getBoolAt_setBoolAt_of_ne st top i (by omega)]

theorem n1s_allBelow_of_noMutBelow (nIn nAlloc m : ℕ) (ops : List MicroOp)
    (_hAllocs : microAllocs ops = nAlloc) (hnm : n1sNoMutBelow nIn ops = true) : allBelow nIn
    (fun i ↦ getBoolAt (evalMicroList nIn ops (initBoolList nIn (nIn + nAlloc) m)) i ==
    m.testBit i) = true := by
  rw [allBelow_iff]
  intro i hi
  rw [beq_iff_eq, n1s_evalMicroList_pres_below ops nIn nIn _ le_rfl hnm i hi]
  dsimp [initBoolList]
  rw [Slot3MicroEngineAux.getBoolAt_mkBoolList nIn m 0 (nIn + nAlloc) i
    (by omega)]
  simp [hi]

/-- Projectile axis wire `(w, b)` on `Wire 411` (`[0..24)`). -/
def n1sProjW411 (w : Fin 3) (b : Fin 8) : Wire 411 := ⟨8 * w.val + b.val, by omega⟩

/-- Combined `38`-bit uniform wire `u38` on `Wire 411` (`[52..90)`). -/
def n1sU38W411 (k : Fin 38) : Wire 411 :=
  ⟨(p57U38W k).val, by have := p57U38W216_lt107 k; omega⟩

/-- Top `t.kBits` bits `uK = u38 / 2 ^ (38 - t.kBits)` on `Wire 411`. -/
def n1sUKW411 (t : Norm1sTier) (m : Fin t.kBits) : Wire 411 :=
  n1sU38W411 ⟨(38 - t.kBits) + m.val, by have := n1s_tier_bounds t; omega⟩

/-- Acceptance flag wire `149` on `Wire 411`. -/
def n1sAccFlagW411 : Wire 411 := ⟨149, by decide⟩

/-- Retained shell-index `mu` wires `[174..177)` on `Wire 411`. -/
def n1sMuW411 (j : Fin 3) : Wire 411 := ⟨174 + j.val, by omega⟩

/-- `32`-bit hardware product output slice `[201..233)` on `Wire 411`. -/
def n1sOut32W411 (j : Fin 32) : Wire 411 := ⟨201 + j.val, by omega⟩

/-- Retained static validity flag wire `258` on `Wire 411`. -/
def n1sValidStaticW411 : Wire 411 := ⟨258, by decide⟩

/-- Hoisted `sTrue18` wires `[199, 200] ∪ [259..275)` on `Wire 411`. -/
def n1sSTrue18W411 (j : Fin 18) : Wire 411 :=
  ⟨(sTrue18WDefault j).val, by have := sTrue18WDefault216_bounds j; omega⟩

/-- Shared `clz18Log2 sTrue` 5-bit exponent wires `[292..297)` allocated by `n1sCtxClz411`. -/
def n1sEW411 (b : Fin 5) : Wire 411 := ⟨292 + b.val, by omega⟩

/-- `40`-input wire map `sTrue18 ++ [275..297)` feeding `n1sCtxBarrel411`. -/
def n1sInBarrelW411 (i : Fin 40) : Wire 411 :=
  if h : i.val < 18 then n1sSTrue18W411 ⟨i.val, h⟩ else ⟨275 + (i.val - 18), by omega⟩

/-- Normalized `18`-bit mantissa wires `[302..320)` allocated by `n1sCtxBarrel411`. -/
def n1sMantW411 (j : Fin 18) : Wire 411 := ⟨302 + j.val, by omega⟩

/-- Booth sign-extension scratch wire `379` (`< 383`). -/
def n1sInvW411 : Wire 411 := ⟨379, by decide⟩

/-- Clean zero-pad wire `380` (`< 383`). -/
def n1sZPad1W411 : Wire 411 := ⟨380, by decide⟩

/-- Clean zero-pad wire `381` (`< 383`). -/
def n1sZPad2W411 : Wire 411 := ⟨381, by decide⟩

/-- Booth carry-in / bitwise-flip scratch wire `382` (`< 383`). -/
def n1sCinW411 : Wire 411 := ⟨382, by decide⟩

theorem n1s_u38W411_range (k : Fin 38) :
    52 ≤ (n1sU38W411 k).val ∧ (n1sU38W411 k).val < 90 := by
  fin_cases k <;> decide

theorem n1s_uKW411_range (t : Norm1sTier) (m : Fin t.kBits) : 52 ≤ (n1sUKW411 t m).val ∧
    (n1sUKW411 t m).val < 90 := n1s_u38W411_range _

theorem n1s_sTrue18W411_range (j : Fin 18) :
    (n1sSTrue18W411 j).val = 199 ∨ (n1sSTrue18W411 j).val = 200 ∨
    (259 ≤ (n1sSTrue18W411 j).val ∧ (n1sSTrue18W411 j).val < 275) := by
  fin_cases j <;> decide

theorem n1s_sTrue18W411_lt_275 (j : Fin 18) : (n1sSTrue18W411 j).val < 275 := by
  rcases n1s_sTrue18W411_range j with h | h | h <;> omega

theorem n1s_sTrue18W411_inj : Function.Injective n1sSTrue18W411 := by
  intro i j h
  have hv : (n1sSTrue18W411 i).val = (n1sSTrue18W411 j).val := congrArg (@Fin.val 411) h
  exact validSTrueMap_default.1 (Fin.ext hv)

theorem n1s_out32W411_inj : Function.Injective n1sOut32W411 := by
  intro i j h
  have hv := congrArg Fin.val h; dsimp [n1sOut32W411] at hv; exact Fin.ext (by omega)

theorem n1s_mantW411_inj : Function.Injective n1sMantW411 := by
  intro i j h
  have hv := congrArg Fin.val h; dsimp [n1sMantW411] at hv; exact Fin.ext (by omega)

theorem n1s_inBarrelW411_lt_297 (i : Fin 40) : (n1sInBarrelW411 i).val < 297 := by
  dsimp [n1sInBarrelW411]
  by_cases h : i.val < 18
  · rw [dite_eq_left h]; exact lt_trans (n1s_sTrue18W411_lt_275 _) (by decide)
  · rw [dite_eq_right h]; dsimp; omega

theorem n1s_inBarrelW411_inj : Function.Injective n1sInBarrelW411 := by
  intro i j hij
  dsimp [n1sInBarrelW411] at hij
  by_cases hi : i.val < 18
  · rw [dite_eq_left hi] at hij
    by_cases hj : j.val < 18
    · rw [dite_eq_left hj] at hij
      exact Fin.ext (congrArg (@Fin.val 18) (n1s_sTrue18W411_inj hij))
    · rw [dite_eq_right hj] at hij
      have hlt := n1s_sTrue18W411_lt_275 ⟨i.val, hi⟩
      have hv := congrArg Fin.val hij; dsimp at hv; omega
  · rw [dite_eq_right hi] at hij
    by_cases hj : j.val < 18
    · rw [dite_eq_left hj] at hij
      have hlt := n1s_sTrue18W411_lt_275 ⟨j.val, hj⟩
      have hv := congrArg Fin.val hij; dsimp at hv; omega
    · rw [dite_eq_right hj] at hij
      have hv := congrArg Fin.val hij; dsimp at hv; exact Fin.ext (by omega)

private theorem bitsVal_dropLow_eq_div {N : ℕ} (L K : ℕ) (hLK : L + K = N)
    (g : Fin N → ZMod 2) :
    bitsVal (fun j : Fin K ↦ g ⟨L + j.val, by omega⟩) = bitsVal g / 2 ^ L := by
  let f : Fin (L + K) → ZMod 2 := fun i ↦ g ⟨i.val, by omega⟩
  have hN : bitsVal g = bitsVal f := by
    unfold bitsVal
    exact Finset.sum_nbij (fun k : Fin N ↦ (⟨k.val, by omega⟩ : Fin (L + K)))
      (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ Fin.ext (Fin.mk.inj h))
      (fun y _ ↦ ⟨⟨y.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun _ _ ↦ rfl)
  rw [hN, bitsVal_split_add L K f, mul_comm (2 ^ L),
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos L),
    Nat.div_eq_of_lt (bitsVal_lt_two_pow _), zero_add]

theorem n1s_uKW411_bitsVal (t : Norm1sTier) (β : BitAssignment 411) :
    bitsVal (fun m : Fin t.kBits ↦ β (n1sUKW411 t m)) =
      bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits) := by
  have hb := n1s_tier_bounds t
  exact bitsVal_dropLow_eq_div (38 - t.kBits) t.kBits (by omega)
    (fun k : Fin 38 ↦ β (n1sU38W411 k))

/-- Shared `16`-`TempAnd` (`22`-alloc) `clz18Ops` context on `[275..297)`. -/
def n1sCtxClz411 : TempCtx 411 := ctxMicro n1sSTrue18W411 n1s_sTrue18W411_inj 275 22 16
    n1s_sTrue18W411_lt_275 clz18Ops clz18Ops_meta (by decide)

/-- `59`-`TempAnd` (`82`-alloc) `barrel59Ops` context on `[297..379)`. -/
def n1sCtxBarrel411 : TempCtx 411 := ctxMicro n1sInBarrelW411 n1s_inBarrelW411_inj 297 82 59
    n1s_inBarrelW411_lt_297 barrel59Ops barrel59Ops_meta (by decide)

theorem n1s_clz18Ops_noMut : n1sNoMutBelow 18 clz18Ops = true := by decide
theorem n1s_barrel59Ops_noMut : n1sNoMutBelow 40 barrel59Ops = true := by decide

theorem n1s_ctxClz_and_barrel_fwd (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 275) β) :
    let s := bitsVal (fun i ↦ β (n1sSTrue18W411 i))
    let β₁ := n1sCtxClz411.fwdBits β
    let β₂ := n1sCtxBarrel411.fwdBits β₁
    cleanRem 411 (411 - 297) β₁ ∧
    (∀ w : Wire 411, w.val < 275 → β₁ w = β w) ∧
    bitsVal (fun b : Fin 5 ↦ β₁ (n1sEW411 b)) = clz18Log2 s ∧
    cleanRem 411 (411 - 379) β₂ ∧
    (∀ w : Wire 411, w.val < 297 → β₂ w = β₁ w) ∧
    bitsVal (fun j : Fin 18 ↦ β₂ (n1sMantW411 j)) = norm1sMant18 s := by
  intro s β₁ β₂
  have hs : s < 2 ^ 18 := bitsVal_lt_two_pow _
  obtain ⟨_, _, _, hClzEv⟩ := ctxMicro_scoped n1sSTrue18W411 n1s_sTrue18W411_inj 275 22 16
    n1s_sTrue18W411_lt_275 clz18Ops clz18Ops_meta (by decide)
  obtain ⟨hcl₁, hpres₁_raw, hout₁⟩ := hClzEv β hβ
  have hpres₁ : ∀ w : Wire 411, w.val < 275 → β₁ w = β w :=
    hpres₁_raw (n1s_allBelow_of_noMutBelow 18 22 s clz18Ops clz18Ops_meta.2.1 n1s_clz18Ops_noMut)
  obtain ⟨_, _, _, hBarEv⟩ := ctxMicro_scoped n1sInBarrelW411 n1s_inBarrelW411_inj 297 82 59
    n1s_inBarrelW411_lt_297 barrel59Ops barrel59Ops_meta (by decide)
  obtain ⟨hcl₂, hpres₂_raw, hout₂⟩ := hBarEv β₁ hcl₁
  let m40 := bitsVal (fun i ↦ β₁ (n1sInBarrelW411 i))
  have hpres₂ : ∀ w : Wire 411, w.val < 297 → β₂ w = β₁ w :=
    hpres₂_raw (n1s_allBelow_of_noMutBelow 40 82 m40 barrel59Ops barrel59Ops_meta.2.1
      n1s_barrel59Ops_noMut)
  let stClz40 := evalMicroList 18 clz18Ops (initBoolList 18 40 s)
  let stClz122 := evalMicroList 18 clz18Ops (initBoolList 18 122 s)
  let stFull := evalMicroList 18 clzBarrelOps (initBoolList 18 122 s)
  have hClz40_eq_122 : ∀ i, i < 40 → getBoolAt stClz40 i = getBoolAt stClz122 i := by
    apply evalMicroList_ext_below clz18Ops 18 (initBoolList 18 40 s) (initBoolList 18 122 s)
      clz18Ops_meta.1
    · dsimp [initBoolList]; rw [Slot3MicroEngineAux.length_mkBoolList, clz18Ops_meta.2.1]
    · dsimp [initBoolList]; rw [Slot3MicroEngineAux.length_mkBoolList, clz18Ops_meta.2.1]; omega
    · intro k hk
      dsimp [initBoolList]
      rw [Slot3MicroEngineAux.getBoolAt_mkBoolList 18 s 0 40 k (by omega),
        Slot3MicroEngineAux.getBoolAt_mkBoolList 18 s 0 122 k (by omega)]
  have hInit40_eq : ∀ i, i < 40 → getBoolAt (initBoolList 40 122 m40) i = getBoolAt stClz122 i := by
    intro i hi
    dsimp [initBoolList]
    rw [Slot3MicroEngineAux.getBoolAt_mkBoolList 40 m40 0 122 i (by omega)]
    simp only [Nat.zero_add, hi, decide_true, Bool.true_and]
    rw [show m40.testBit i = decide (β₁ (n1sInBarrelW411 ⟨i, hi⟩) = 1) from
      bitsVal_testBit_eq (fun k ↦ β₁ (n1sInBarrelW411 k)) ⟨i, hi⟩,
      ← hClz40_eq_122 i hi]
    by_cases hi18 : i < 18
    · have hw_eq : n1sInBarrelW411 ⟨i, hi⟩ = n1sSTrue18W411 ⟨i, hi18⟩ := dite_eq_left hi18
      rw [hw_eq, hpres₁ _ (n1s_sTrue18W411_lt_275 _),
        ← bitsVal_testBit_eq (fun k ↦ β (n1sSTrue18W411 k)) ⟨i, hi18⟩,
        n1s_evalMicroList_pres_below clz18Ops 18 18 _ le_rfl n1s_clz18Ops_noMut i hi18]
      dsimp only [initBoolList]
      rw [Slot3MicroEngineAux.getBoolAt_mkBoolList 18 s 0 40 i (by omega)]
      simp only [Nat.zero_add, hi18, decide_true, Bool.true_and]
      rfl
    · have hw_eq : n1sInBarrelW411 ⟨i, hi⟩ = ⟨275 + (i - 18), by omega⟩ := dite_eq_right hi18
      have hβ₁_i : β₁ ⟨275 + (i - 18), by omega⟩ = boolToZMod2 (getBoolAt stClz40 i) :=
        hout₁ i (by omega) hi
      rw [hw_eq, hβ₁_i, boolToZMod2_decide_eq_one]
  have hBar_eq_Full : ∀ idx, idx < 122 →
      getBoolAt (evalMicroList 40 barrel59Ops (initBoolList 40 122 m40)) idx =
        getBoolAt stFull idx := by
    intro idx hidx
    have happ : stFull = evalMicroList 40 barrel59Ops stClz122 := by
      dsimp [stFull, clzBarrelOps, stClz122]
      rw [evalMicroList_append, clz18Ops_meta.2.1]
    rw [happ]
    exact evalMicroList_ext_below barrel59Ops 40 (initBoolList 40 122 m40) stClz122
      barrel59Ops_meta.1
      (by dsimp [initBoolList]; rw [Slot3MicroEngineAux.length_mkBoolList, barrel59Ops_meta.2.1])
      (by dsimp [stClz122]
          have hlen_pres : ∀ (ops : List MicroOp) (top : ℕ) (st : List Bool),
              (evalMicroList top ops st).length = st.length := by
            intro ops; induction ops with
            | nil => intro _ _; rfl
            | cons op rest ih =>
                intro top st; cases op <;> simp [evalMicroList, ih, length_setBoolAt]
          rw [hlen_pres, show (initBoolList 18 122 s).length = 122 from by
            dsimp [initBoolList]; exact Slot3MicroEngineAux.length_mkBoolList 18 s 0 122,
            barrel59Ops_meta.2.1])
      hInit40_eq idx (by rw [barrel59Ops_meta.2.1]; exact hidx)
  obtain ⟨_, heSpec, hmSpec⟩ := clzBarrelOps_spec s hs
  have heVal : bitsVal (fun b : Fin 5 ↦ β₁ (n1sEW411 b)) = clz18Log2 s := by
    apply bitsVal_eq_of_testBit _ _ (lt_of_le_of_lt (clz18Log2_le_17 s) (by decide))
    intro b
    have hwire : n1sEW411 b = ⟨275 + ((35 + b.val) - 18), by omega⟩ :=
      Fin.ext (by dsimp [n1sEW411]; omega)
    have hβ₁_b : β₁ ⟨275 + ((35 + b.val) - 18), by omega⟩ =
        boolToZMod2 (getBoolAt stClz40 (35 + b.val)) :=
      hout₁ (35 + b.val) (by omega) (by omega)
    rw [hwire, hβ₁_b, hClz40_eq_122 (35 + b.val) (by omega)]
    have h35 : getBoolAt stClz122 (35 + b.val) = getBoolAt stFull (35 + b.val) := by
      have happ : stFull = evalMicroList 40 barrel59Ops stClz122 := by
        dsimp [stFull, clzBarrelOps, stClz122]
        rw [evalMicroList_append, clz18Ops_meta.2.1]
      rw [happ, n1s_evalMicroList_pres_below barrel59Ops 40 40 stClz122 le_rfl
        n1s_barrel59Ops_noMut (35 + b.val) (by omega)]
    rw [h35, heSpec b]
    cases (clz18Log2 s).testBit b.val <;> rfl
  have hmVal : bitsVal (fun j : Fin 18 ↦ β₂ (n1sMantW411 j)) = norm1sMant18 s := by
    apply bitsVal_eq_of_testBit _ _ (n1s_norm1sMant18_lt s hs)
    intro j
    have hwire : n1sMantW411 j = ⟨297 + ((45 + j.val) - 40), by omega⟩ :=
      Fin.ext (by dsimp [n1sMantW411]; omega)
    have hβ₂_j : β₂ ⟨297 + ((45 + j.val) - 40), by omega⟩ =
        boolToZMod2 (getBoolAt (evalMicroList 40 barrel59Ops (initBoolList 40 122 m40)) (45 +
          j.val)) :=
      hout₂ (45 + j.val) (by omega) (by omega)
    rw [hwire, hβ₂_j, hBar_eq_Full (45 + j.val) (by omega), hmSpec j]
    cases (norm1sMant18 s).testBit j.val <;> rfl
  exact ⟨hcl₁, hpres₁, heVal, hcl₂, hpres₂, hmVal⟩

/-- Structural XOR flip of `w` mantissa wires `[off .. off + w)` controlled by `cinW411`. -/
def n1sFlipMantSlice (off : ℕ) : (w : ℕ) → (hoff : off + w ≤ 18) → CliffProg 411
  | 0, _ => .nil
  | w + 1, hoff =>
      .seq (.cnot n1sCinW411 (n1sMantW411 ⟨off + w, by omega⟩)
        (wire_ne_of_gt (by dsimp [n1sCinW411, n1sMantW411]; omega)))
        (n1sFlipMantSlice off w (by omega))

theorem n1s_flipMantSlice_supports (off : ℕ) :
    ∀ (w : ℕ) (hoff : off + w ≤ 18), (n1sFlipMantSlice off w hoff).SupportsBelow 383
  | 0, _ => trivial
  | w + 1, hoff =>
      ⟨⟨by decide, by dsimp [n1sMantW411]; omega⟩, n1s_flipMantSlice_supports off w (by omega)⟩

theorem n1s_flipMantSlice_eval (off : ℕ) :
    ∀ (w : ℕ) (hoff : off + w ≤ 18) (β : BitAssignment 411),
      (∀ q : Wire 411, (∀ j : Fin w, q ≠ n1sMantW411 ⟨off + j.val, by omega⟩) →
        (n1sFlipMantSlice off w hoff).eval β q = β q) ∧
      (∀ j : Fin w,
        (n1sFlipMantSlice off w hoff).eval β (n1sMantW411 ⟨off + j.val, by omega⟩) =
          β (n1sMantW411 ⟨off + j.val, by omega⟩) + β n1sCinW411)
  | 0, _, _ => ⟨fun _ _ ↦ rfl, fun j ↦ Fin.elim0 j⟩
  | w + 1, hoff, β => by
      dsimp only [n1sFlipMantSlice]
      let topM := n1sMantW411 ⟨off + w, by omega⟩
      let β₁ := (CliffProg.cnot n1sCinW411 topM
        (wire_ne_of_gt (by simp only [topM, n1sCinW411, n1sMantW411]; omega))).eval β
      obtain ⟨hOut, hIn⟩ := n1s_flipMantSlice_eval off w (by omega) β₁
      have hcin : β₁ n1sCinW411 = β n1sCinW411 :=
        Function.update_of_ne (wire_ne_of_gt (by
          simp only [n1sCinW411, topM, n1sMantW411]; omega)) _ _
      refine ⟨fun q hq ↦ ?_, fun j ↦ ?_⟩
      · rw [CliffProg.eval, hOut q (fun j ↦ hq j.castSucc)]
        exact Function.update_of_ne (hq (Fin.last w)) _ _
      · cases j using Fin.lastCases with
        | last =>
            have hlast : (n1sMantW411 ⟨off + (Fin.last w).val, by omega⟩) = topM :=
              Fin.ext (by simp [topM, n1sMantW411])
            rw [hlast]
            change (n1sFlipMantSlice off w (by omega)).eval β₁ topM = β topM + β n1sCinW411
            rw [hOut topM (fun j h ↦ by
              have hv := congrArg (@Fin.val 18) (n1s_mantW411_inj h); dsimp at hv; omega)]
            simp [β₁, CliffProg.eval, Function.update_self]
        | cast j =>
            have hcast : (n1sMantW411 ⟨off + j.castSucc.val, by omega⟩) =
                n1sMantW411 ⟨off + j.val, by omega⟩ :=
              Fin.ext (by simp [n1sMantW411])
            rw [hcast]
            change (n1sFlipMantSlice off w (by
              omega)).eval β₁ (n1sMantW411 ⟨off + j.val, by omega⟩) = _
            rw [hIn j, hcin]
            have hne : n1sMantW411 ⟨off + j.val, by omega⟩ ≠ topM := fun h ↦ by
              have hv := congrArg (@Fin.val 18) (n1s_mantW411_inj h); dsimp at hv; omega
            rw [show β₁ (n1sMantW411 ⟨off + j.val, by omega⟩) =
              β (n1sMantW411 ⟨off + j.val, by omega⟩) from Function.update_of_ne hne _ _]

/-- Setup Clifford on `[379, 382]` and `mant[off .. off + w)`: sets `cinW411 = 1 + u`, `invW411 =
  u`,
and XORs `cinW411` into `mant[off .. off + w)`. -/
def n1sCRowSetup (uW : Wire 411) (hu : uW.val < 379) (off w : ℕ) (hoff : off + w ≤ 18) :
    CliffProg 411 := .seq (.x n1sCinW411) (.seq (.cnot uW n1sCinW411 (wire_ne_of_lt (lt_trans
    hu (by decide)))) (.seq (.cnot uW n1sInvW411 (wire_ne_of_lt hu)) (n1sFlipMantSlice off w
    hoff)))

theorem n1s_cRowSetup_supports (uW : Wire 411) (hu : uW.val < 379) (off w : ℕ)
    (hoff : off + w ≤ 18) : (n1sCRowSetup uW hu off w hoff).SupportsBelow 383 :=
  ⟨by simp [CliffProg.SupportsBelow, n1sCinW411],
   ⟨by omega, by simp [n1sCinW411]⟩,
   ⟨by omega, by simp [n1sInvW411]⟩,
   n1s_flipMantSlice_supports off w hoff⟩

theorem n1s_cRowSetup_eval (uW : Wire 411) (hu : uW.val < 201) (off w : ℕ) (hoff : off + w ≤ 18)
    (β : BitAssignment 411) (hcl : cleanRem 411 (411 - 379) β) :
    let γ := (n1sCRowSetup uW (lt_trans hu (by decide)) off w hoff).eval β
    γ n1sCinW411 = 1 + β uW ∧
    γ n1sInvW411 = β uW ∧
    γ n1sZPad1W411 = 0 ∧
    γ n1sZPad2W411 = 0 ∧
    γ uW = β uW ∧
    (∀ j : Fin 32, γ (n1sOut32W411 j) = β (n1sOut32W411 j)) ∧
    (∀ j : Fin w, γ (n1sMantW411 ⟨off + j.val, by omega⟩) =
      β (n1sMantW411 ⟨off + j.val, by omega⟩) + (1 + β uW)) ∧
    (∀ q : Wire 411, (∀ j : Fin w, q ≠ n1sMantW411 ⟨off + j.val, by omega⟩) →
      q ≠ n1sCinW411 → q ≠ n1sInvW411 → γ q = β q) := by
  intro γ
  have hc0 : β n1sCinW411 = 0 := hcl n1sCinW411 (by decide)
  have hi0 : β n1sInvW411 = 0 := hcl n1sInvW411 (by decide)
  have hz1 : β n1sZPad1W411 = 0 := hcl n1sZPad1W411 (by decide)
  have hz2 : β n1sZPad2W411 = 0 := hcl n1sZPad2W411 (by decide)
  let β₁ := (CliffProg.seq (.x n1sCinW411)
    (.seq (.cnot uW n1sCinW411 (wire_ne_of_lt (lt_trans hu (by decide))))
      (.cnot uW n1sInvW411 (wire_ne_of_lt (lt_trans hu (by decide)))))).eval β
  have hβ₁_cin : β₁ n1sCinW411 = 1 + β uW := by
    dsimp [β₁, CliffProg.eval]
    rw [Function.update_of_ne (by decide : n1sCinW411 ≠ n1sInvW411), Function.update_self,
      Function.update_self, Function.update_of_ne (wire_ne_of_lt (lt_trans hu (by decide))),
      hc0, zero_add]
  have hβ₁_inv : β₁ n1sInvW411 = β uW := by
    dsimp [β₁, CliffProg.eval]
    rw[Function.update_self, Function.update_of_ne (by decide : n1sInvW411 ≠ n1sCinW411),
        Function.update_of_ne (wire_ne_of_lt (lt_trans hu (by decide)) : uW ≠ n1sCinW411),
        Function.update_of_ne (by decide : n1sInvW411 ≠ n1sCinW411),
        Function.update_of_ne (wire_ne_of_lt (lt_trans hu (by decide)) : uW ≠ n1sCinW411),
        hi0, zero_add]
  have hβ₁_oth : ∀ q : Wire 411, q ≠ n1sCinW411 → q ≠ n1sInvW411 → β₁ q = β q := by
    intro q hqc hqi
    dsimp [β₁, CliffProg.eval]
    rw [Function.update_of_ne hqi, Function.update_of_ne hqc, Function.update_of_ne hqc]
  obtain ⟨hOut, hIn⟩ := n1s_flipMantSlice_eval off w hoff β₁
  have hγ_eq : γ = (n1sFlipMantSlice off w hoff).eval β₁ := rfl
  rw [hγ_eq]
  have hcin_nm : ∀ j : Fin w, n1sCinW411 ≠ n1sMantW411 ⟨off + j.val, by omega⟩ :=
    fun j ↦ wire_ne_of_gt (by dsimp [n1sCinW411, n1sMantW411]; omega)
  have hinv_nm : ∀ j : Fin w, n1sInvW411 ≠ n1sMantW411 ⟨off + j.val, by omega⟩ :=
    fun j ↦ wire_ne_of_gt (by dsimp [n1sInvW411, n1sMantW411]; omega)
  refine ⟨(hOut n1sCinW411 hcin_nm).trans hβ₁_cin,
    (hOut n1sInvW411 hinv_nm).trans hβ₁_inv,
    (hOut n1sZPad1W411 (fun j ↦ wire_ne_of_gt (by dsimp [n1sZPad1W411, n1sMantW411]; omega))).trans
      ((hβ₁_oth _ (by decide) (by decide)).trans hz1),
    (hOut n1sZPad2W411 (fun j ↦ wire_ne_of_gt (by dsimp [n1sZPad2W411, n1sMantW411]; omega))).trans
      ((hβ₁_oth _ (by decide) (by decide)).trans hz2),
    (hOut uW (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))).trans
      (hβ₁_oth uW (wire_ne_of_lt (lt_trans hu (by
        decide))) (wire_ne_of_lt (lt_trans hu (by decide)))),
    fun j ↦ (hOut (n1sOut32W411 j) (fun i ↦ wire_ne_of_lt (by
      dsimp [n1sOut32W411, n1sMantW411]; omega))).trans
      (hβ₁_oth _ (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sCinW411]; omega))
        (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sInvW411]; omega))),
    fun j ↦ by
      rw [hIn j, hβ₁_cin, hβ₁_oth _ (wire_ne_of_lt (by dsimp [n1sMantW411, n1sCinW411]; omega))
        (wire_ne_of_lt (by dsimp [n1sMantW411, n1sInvW411]; omega))],
    fun q hqm hqc hqi ↦ (hOut q hqm).trans (hβ₁_oth q hqc hqi)⟩

theorem n1s_mantSlice_bitsVal (β : BitAssignment 411) (sh w : ℕ) (hsh : sh + w = 18) :
    bitsVal (fun j : Fin w ↦ β (n1sMantW411 ⟨sh + j.val, by omega⟩)) =
      bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) / 2 ^ sh :=
  bitsVal_dropLow_eq_div sh w hsh (fun i : Fin 18 ↦ β (n1sMantW411 i))

/-- Operand wires `bLowR (w)` (`w + 1` wires: `mant[18 - w .. 18) ++ [invW411]`) for Low Booth
  rows. -/
def n1sBLowR (w : ℕ) (hw : w ≤ 18) : Fin (w + 1) → Wire 411 :=
  Fin.snoc (fun j : Fin w ↦ n1sMantW411 ⟨(18 - w) + j.val, by omega⟩) n1sInvW411

/-- Operand wires `bLowF (w)` (`w + 2` wires: `bLowR w ++ [zPad1W411]`) for Low Booth forward
  rows. -/
def n1sBLowF (w : ℕ) (hw : w ≤ 18) : Fin (w + 2) → Wire 411 :=
  Fin.snoc (n1sBLowR w hw) n1sZPad1W411

theorem n1s_bLowR_lt (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 1)) : (n1sBLowR w hw j).val < 383 := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowR, n1sInvW411]
  | cast j => simp only [n1sBLowR, Fin.snoc_castSucc, n1sMantW411]; omega

theorem n1s_bLowR_ge_302 (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 1)) : 302 ≤ (n1sBLowR w hw j).val := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowR, n1sInvW411]
  | cast j => simp only [n1sBLowR, Fin.snoc_castSucc, n1sMantW411]; omega

theorem n1s_bLowR_le_379 (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 1)) : (n1sBLowR w hw j).val ≤ 379 := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowR, n1sInvW411]
  | cast j => simp only [n1sBLowR, Fin.snoc_castSucc, n1sMantW411]; omega

theorem n1s_bLowF_lt (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 2)) : (n1sBLowF w hw j).val < 383 := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowF, n1sZPad1W411]
  | cast j => simp only [n1sBLowF, Fin.snoc_castSucc]; exact n1s_bLowR_lt w hw j

theorem n1s_bLowF_ge_302 (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 2)) : 302 ≤ (n1sBLowF w hw j).val := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowF, n1sZPad1W411]
  | cast j => simp only [n1sBLowF, Fin.snoc_castSucc]; exact n1s_bLowR_ge_302 w hw j

theorem n1s_bLowF_le_380 (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 2)) : (n1sBLowF w hw j).val ≤ 380 := by
  cases j using Fin.lastCases with
  | last => simp [n1sBLowF, n1sZPad1W411]
  | cast j => simp only [n1sBLowF, Fin.snoc_castSucc]; exact le_trans (n1s_bLowR_le_379 w hw j) (by
    decide)

theorem n1s_bLowR_inj (w : ℕ) (hw : w ≤ 18) : Function.Injective (n1sBLowR w hw) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j' =>
          simp only [n1sBLowR, Fin.snoc_last, Fin.snoc_castSucc] at hij
          have hv := congrArg Fin.val hij; dsimp [n1sInvW411, n1sMantW411] at hv; omega
  | cast i' =>
      cases j using Fin.lastCases with
      | last =>
          simp only [n1sBLowR, Fin.snoc_last, Fin.snoc_castSucc] at hij
          have hv := congrArg Fin.val hij; dsimp [n1sInvW411, n1sMantW411] at hv; omega
      | cast j' =>
          simp only [n1sBLowR, Fin.snoc_castSucc] at hij
          have hv := congrArg Fin.val (n1s_mantW411_inj hij); dsimp at hv
          exact congrArg Fin.castSucc (Fin.ext (by omega))

theorem n1s_bLowF_inj (w : ℕ) (hw : w ≤ 18) : Function.Injective (n1sBLowF w hw) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j' =>
          simp only [n1sBLowF, Fin.snoc_last, Fin.snoc_castSucc] at hij
          have hle := n1s_bLowR_le_379 w hw j'
          have hv := congrArg Fin.val hij; dsimp [n1sZPad1W411] at hv; omega
  | cast i' =>
      cases j using Fin.lastCases with
      | last =>
          simp only [n1sBLowF, Fin.snoc_last, Fin.snoc_castSucc] at hij
          have hle := n1s_bLowR_le_379 w hw i'
          have hv := congrArg Fin.val hij; dsimp [n1sZPad1W411] at hv; omega
      | cast j' =>
          simp only [n1sBLowF, Fin.snoc_castSucc] at hij
          exact congrArg Fin.castSucc (n1s_bLowR_inj w hw hij)

/-- Slice `out32[off .. off + len)` on `Wire 411`. -/
def n1sAccSlice (off len : ℕ) (h : off + len ≤ 32) (j : Fin len) : Wire 411 :=
  n1sOut32W411 ⟨off + j.val, by omega⟩

theorem n1s_accSlice_inj (off len : ℕ) (h : off + len ≤ 32) :
    Function.Injective (n1sAccSlice off len h) := by
  intro i j hij
  have hv := congrArg Fin.val (n1s_out32W411_inj hij); dsimp at hv
  exact Fin.ext (by omega)

theorem n1s_accSlice_lt (off len : ℕ) (h : off + len ≤ 32) (j : Fin len) :
    (n1sAccSlice off len h j).val < 383 := by
  dsimp [n1sAccSlice, n1sOut32W411]; omega

theorem n1s_accSlice_le_232 (off len : ℕ) (h : off + len ≤ 32) (j : Fin len) :
    (n1sAccSlice off len h j).val < 233 := by
  dsimp [n1sAccSlice, n1sOut32W411]; omega

theorem n1s_bitsVal_flip_all (w : ℕ) (f : Fin w → ZMod 2) :
    bitsVal (fun j : Fin w ↦ f j + 1) = 2 ^ w - 1 - bitsVal f := by
  induction w with
  | zero => simp [bitsVal]
  | succ w ih =>
      rw [bitsVal_castSucc_split (fun j : Fin (w + 1) ↦ f j + 1),
        bitsVal_castSucc_split f, ih (fun j ↦ f j.castSucc)]
      have hlt : bitsVal (fun j : Fin w ↦ f j.castSucc) < 2 ^ w := bitsVal_lt_two_pow _
      have hp : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [pow_succ]; ring
      rcases bit_cases (f (Fin.last w)) with h0 | h1
      · have h01 : (0 : ZMod 2) + 1 = 1 := rfl
        simp only [h0, h01, ZMod.val_zero, ZMod.val_one, mul_zero, mul_one, add_zero]
        omega
      · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        simp only [h1, h11, ZMod.val_zero, ZMod.val_one, mul_zero, mul_one, add_zero]
        omega

theorem w14_bLowF_bitsVal_eq (w : ℕ) (hw : w ≤ 18) (η : BitAssignment 411)
    (hz1 : η n1sZPad1W411 = 0) :
    bitsVal (fun j ↦ η (n1sBLowF w hw j)) = bitsVal (fun j ↦ η (n1sBLowR w hw j)) := by
  rw [bitsVal_castSucc_split]
  have hlo : (fun j : Fin (w + 1) ↦ η (n1sBLowF w hw j.castSucc)) =
      fun j ↦ η (n1sBLowR w hw j) := funext fun j ↦ by simp [n1sBLowF, Fin.snoc_castSucc]
  have hhi : η (n1sBLowF w hw (Fin.last (w + 1))) = 0 := by
    simp only [n1sBLowF, Fin.snoc_last]
    exact hz1
  rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero]

theorem w14_mant_flip_msb_val (β : BitAssignment 411) (sh w : ℕ) (hsh : sh + w = 18)
    (u : ZMod 2) :
    bitsVal (fun j : Fin w ↦ β (n1sMantW411 ⟨sh + j.val, by omega⟩) + (1 + u)) +
      2 ^ w * u.val =
    if decide (u = 1) = true then
      2 ^ w + bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) / 2 ^ sh
    else
      2 ^ w - 1 - bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) / 2 ^ sh := by
  have hxm := n1s_mantSlice_bitsVal β sh w hsh
  have hflip := n1s_bitsVal_flip_all w (fun j : Fin w ↦ β (n1sMantW411 ⟨sh + j.val, by omega⟩))
  rcases bit_cases u with rfl | rfl
  · rw [ite_eq_right (by decide : ¬(decide ((0 : ZMod 2) = 1) = true))]
    simp only [show (1 : ZMod 2) + 0 = 1 from rfl, ZMod.val_zero, mul_zero, add_zero, hflip, hxm]
  · rw [ite_eq_left (by decide : decide ((1 : ZMod 2) = 1) = true)]
    simp only [show (1 : ZMod 2) + 1 = 0 from by decide, add_zero, ZMod.val_one, mul_one, hxm]
    exact Nat.add_comm _ _

theorem n1s_bLowR_val_eq_row (dCut m : ℕ) (hm : m < dCut) (_hd : dCut ≤ 18) (hsh : dCut - m < 18)
    (uW : Wire 411) (hu : uW.val < 201) (β : BitAssignment 411) (hcl : cleanRem 411 (411 - 379) β) :
    let sh := dCut - m
    let w := 18 - sh
    let γ := (n1sCRowSetup uW (lt_trans hu (by decide)) sh w (by omega)).eval β
    bitsVal (fun j ↦ γ (n1sBLowR w (by omega) j)) =
      norm1sRowVal dCut m (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β uW = 1)) ∧
    bitsVal (fun j ↦ γ (n1sBLowF w (by omega) j)) =
      norm1sRowVal dCut m (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β uW = 1)) := by
  intro sh w γ
  obtain ⟨_, hinv, hz1, _, _, _, hmant, _⟩ := n1s_cRowSetup_eval uW hu sh w (by omega) β hcl
  have hloR : (fun j : Fin w ↦ γ (n1sBLowR w (by omega) j.castSucc)) =
      fun j : Fin w ↦ β (n1sMantW411 ⟨sh + j.val, by omega⟩) + (1 + β uW) :=
    funext fun j ↦ by
      simp only [n1sBLowR, Fin.snoc_castSucc]
      rw [show (⟨(18 - w) + j.val, by omega⟩ : Fin 18) = ⟨sh + j.val, by omega⟩ from
        Fin.ext (by dsimp [w]; omega)]
      exact hmant j
  have hhiR : γ (n1sBLowR w (by omega) (Fin.last w)) = β uW := by
    simp only [n1sBLowR, Fin.snoc_last]
    exact hinv
  have hR : bitsVal (fun j ↦ γ (n1sBLowR w (by omega) j)) =
      norm1sRowVal dCut m (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β uW = 1)) := by
    rw [bitsVal_castSucc_split, hloR, hhiR, w14_mant_flip_msb_val β sh w (by omega) (β uW)]
    unfold norm1sRowVal
    rw [ite_eq_left hm, ite_eq_right (by omega : ¬(dCut - m = 18)), ite_eq_left hsh]
  exact ⟨hR, (w14_bLowF_bitsVal_eq w (by omega) γ hz1).trans hR⟩

theorem n1s_bHigh_val_eq_row (dCut off : ℕ) (uW : Wire 411) (hu : uW.val < 201)
    (β : BitAssignment 411) (hcl : cleanRem 411 (411 - 379) β) :
    let γ := (n1sCRowSetup uW (lt_trans hu (by decide)) 0 18 (by decide)).eval β
    let mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
    let row0 := if decide (β uW = 1) = true then 2 ^ 18 + mS else 2 ^ 18 - mS
    bitsVal (fun j ↦ γ (n1sBLowR 18 le_rfl j)) + (γ n1sCinW411).val = row0 ∧
    bitsVal (fun j ↦ γ (n1sBLowF 18 le_rfl j)) + (γ n1sCinW411).val = row0 ∧
    norm1sRowVal dCut (dCut + off) mS (decide (β uW = 1)) = row0 * 2 ^ off := by
  intro γ mS row0
  obtain ⟨hcin, hinv, hz1, _, _, _, hmant, _⟩ :=
    n1s_cRowSetup_eval uW hu 0 18 (by decide) β hcl
  have hloR : (fun j : Fin 18 ↦ γ (n1sBLowR 18 le_rfl j.castSucc)) =
      fun j : Fin 18 ↦ β (n1sMantW411 ⟨0 + j.val, by omega⟩) + (1 + β uW) :=
    funext fun j ↦ by
      simp only [n1sBLowR, Fin.snoc_castSucc]
      exact hmant j
  have hhiR : γ (n1sBLowR 18 le_rfl (Fin.last 18)) = β uW := by
    simp only [n1sBLowR, Fin.snoc_last]
    exact hinv
  have hR : bitsVal (fun j ↦ γ (n1sBLowR 18 le_rfl j)) + (γ n1sCinW411).val = row0 := by
    dsimp only [γ] at hloR hhiR ⊢
    rw [bitsVal_castSucc_split, hloR, hhiR, w14_mant_flip_msb_val β 0 18 (by decide) (β uW), hcin]
    dsimp only [row0]
    have hmS_lt : mS < 2 ^ 18 := bitsVal_lt_two_pow _
    have h218 : (2 ^ 18 : ℕ) = 262144 := by decide
    rcases bit_cases (β uW) with hu0 | hu1
    · rw [hu0, ite_eq_right (by decide : ¬(decide ((0 : ZMod 2) = 1) = true)),
        ite_eq_right (by decide : ¬(decide ((0 : ZMod 2) = 1) = true))]
      simp only [show (1 : ZMod 2) + 0 = 1 from rfl, ZMod.val_one, Nat.pow_zero, Nat.div_one]
      omega
    · rw [hu1, ite_eq_left (by decide : decide ((1 : ZMod 2) = 1) = true),
        ite_eq_left (by decide : decide ((1 : ZMod 2) = 1) = true)]
      simp only [show (1 : ZMod 2) + 1 = 0 from by decide, ZMod.val_zero, Nat.pow_zero,
        Nat.div_one, add_zero]
      rfl
  refine ⟨hR, by rw [w14_bLowF_bitsVal_eq 18 le_rfl γ hz1, hR], ?_⟩
  unfold norm1sRowVal
  rw [ite_eq_right (by omega)]
  dsimp only
  rw [show dCut + off - dCut = off from by omega]

/-- Pure Clifford base row `m = 0` when `t.dCut < 18` (`w₀ = 18 - t.dCut` in `{1, 2}`). -/
def n1sCRow0Lt18 (u0 : Wire 411) (hu0 : u0.val < 201) (sh : ℕ) :
    (w : ℕ) → (hsh : sh + w ≤ 18) → CliffProg 411
  | 0, _ => .nil
  | w + 1, hsh =>
      let dst := n1sOut32W411 ⟨w, by omega⟩
      .seq (.x dst)
        (.seq (.cnot u0 dst (wire_ne_of_lt (by simp only [dst, n1sOut32W411]; omega)))
          (.seq (.cnot (n1sMantW411 ⟨sh + w, by omega⟩) dst
            (wire_ne_of_gt (by simp only [dst, n1sOut32W411, n1sMantW411]; omega)))
            (n1sCRow0Lt18 u0 hu0 sh w (by omega))))

/-- Full pure Clifford row `m = 0` for `t.dCut < 18` writing `norm1sRowVal t.dCut 0 mS u_0` into
  `out32`. -/
def n1sCRow0Full (u0 : Wire 411) (hu0 : u0.val < 201) (dCut : ℕ) (hd : 16 ≤ dCut ∧ dCut < 18) :
    CliffProg 411 :=
  let w0 := 18 - dCut
  .seq (.cnot u0 (n1sOut32W411 ⟨w0, by omega⟩)
    (wire_ne_of_lt (by simp only [n1sOut32W411]; omega)))
    (n1sCRow0Lt18 u0 hu0 dCut w0 (by omega))

theorem n1s_cRow0Lt18_supports (u0 : Wire 411) (hu0 : u0.val < 201) (sh : ℕ) :
    ∀ (w : ℕ) (hsh : sh + w ≤ 18), (n1sCRow0Lt18 u0 hu0 sh w hsh).SupportsBelow 379
  | 0, _ => trivial
  | w + 1, hsh => by
      dsimp [n1sCRow0Lt18, CliffProg.SupportsBelow, n1sOut32W411, n1sMantW411]
      exact ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        n1s_cRow0Lt18_supports u0 hu0 sh w (by omega)⟩

theorem n1s_cRow0Lt18_eval (u0 : Wire 411) (hu0 : u0.val < 201) (sh : ℕ) :
    ∀ (w : ℕ) (hsh : sh + w ≤ 18) (β : BitAssignment 411),
      (∀ q : Wire 411, (∀ j : Fin w, q ≠ n1sOut32W411 ⟨j.val, by omega⟩) →
        (n1sCRow0Lt18 u0 hu0 sh w hsh).eval β q = β q) ∧
      (∀ j : Fin w,
        (n1sCRow0Lt18 u0 hu0 sh w hsh).eval β (n1sOut32W411 ⟨j.val, by omega⟩) =
          β (n1sOut32W411 ⟨j.val, by omega⟩) +
            (β (n1sMantW411 ⟨sh + j.val, by omega⟩) + (1 + β u0)))
  | 0, _, _ => ⟨fun _ _ ↦ rfl, fun j ↦ Fin.elim0 j⟩
  | w + 1, hsh, β => by
      dsimp only [n1sCRow0Lt18]
      let dst := n1sOut32W411 ⟨w, by omega⟩
      let mW := n1sMantW411 ⟨sh + w, by omega⟩
      have hm_ne : mW ≠ dst := wire_ne_of_gt (by
        simp only [dst, mW, n1sOut32W411, n1sMantW411]; omega)
      have hu_ne : u0 ≠ dst := wire_ne_of_lt (by simp only [dst, n1sOut32W411]; omega)
      let β₁ := (CliffProg.seq (.x dst) (.seq (.cnot u0 dst hu_ne) (.cnot mW dst hm_ne))).eval
          β
      have hβ₁_dst : β₁ dst = β dst + (β mW + (1 + β u0)) := by
        simp only [β₁, CliffProg.eval, Function.update_self,
          Function.update_of_ne hm_ne, Function.update_of_ne hu_ne]
        ring
      have hβ₁_oth : ∀ q : Wire 411, q ≠ dst → β₁ q = β q := fun q hq ↦ by
        dsimp [β₁, CliffProg.eval]
        rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
      obtain ⟨hOut, hIn⟩ := n1s_cRow0Lt18_eval u0 hu0 sh w (by omega) β₁
      refine ⟨fun q hq ↦ ?_, fun j ↦ ?_⟩
      · exact (hOut q (fun j ↦ hq j.castSucc)).trans (hβ₁_oth q (hq (Fin.last w)))
      · cases j using Fin.lastCases with
        | last =>
            have hlast : (n1sOut32W411 ⟨(Fin.last w).val, by omega⟩) = dst :=
              Fin.ext (by simp [dst, n1sOut32W411])
            rw [hlast]
            change (n1sCRow0Lt18 u0 hu0 sh w (by omega)).eval β₁ dst = _
            refine (hOut dst (fun j h ↦ ?_)).trans hβ₁_dst
            have hv := congrArg (@Fin.val 32) (n1s_out32W411_inj h); dsimp at hv; omega
        | cast j =>
            have hj1 : (n1sOut32W411 ⟨j.castSucc.val, by omega⟩) = n1sOut32W411 ⟨j.val, by omega⟩ :=
              Fin.ext (by simp [n1sOut32W411])
            have hj2 : (n1sMantW411 ⟨sh + j.castSucc.val, by omega⟩) = n1sMantW411 ⟨sh + j.val,
              by omega⟩ :=
              Fin.ext (by simp [n1sMantW411])
            rw [hj1, hj2]
            change (n1sCRow0Lt18 u0 hu0 sh w (by
              omega)).eval β₁ (n1sOut32W411 ⟨j.val, by omega⟩) = _
            rw [hIn j,
              hβ₁_oth (n1sOut32W411 ⟨j.val, by omega⟩) (fun h ↦ by
                have hv := congrArg (@Fin.val 32) (n1s_out32W411_inj h); dsimp at hv; omega),
              hβ₁_oth (n1sMantW411 ⟨sh + j.val, by omega⟩)
                (wire_ne_of_gt (by simp only [dst, n1sOut32W411, n1sMantW411]; omega)),
              hβ₁_oth u0 hu_ne]

theorem n1s_cRow0Full_spec (u0 : Wire 411) (hu0 : u0.val < 201) (dCut : ℕ)
    (hd : 16 ≤ dCut ∧ dCut < 18) (β : BitAssignment 411)
    (hout0 : ∀ j : Fin 32, β (n1sOut32W411 j) = 0) :
    let c := n1sCRow0Full u0 hu0 dCut hd
    c.SupportsBelow 379 ∧
    (∀ q : Wire 411, (∀ j : Fin 32, q ≠ n1sOut32W411 j) → c.eval β q = β q) ∧
    bitsVal (fun j : Fin 32 ↦ c.eval β (n1sOut32W411 j)) =
      norm1sRowVal dCut 0 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β u0 = 1)) := by
  intro c
  let w0 := 18 - dCut
  have hsupp : c.SupportsBelow 379 :=
    ⟨⟨by omega, by dsimp [n1sOut32W411]; omega⟩, n1s_cRow0Lt18_supports u0 hu0 dCut w0 (by omega)⟩
  let β₁ := (CliffProg.cnot u0 (n1sOut32W411 ⟨w0, by omega⟩)
    (wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))).eval β
  obtain ⟨hOut, hIn⟩ := n1s_cRow0Lt18_eval u0 hu0 dCut w0 (by omega) β₁
  have hnon : ∀ q : Wire 411, (∀ j : Fin 32, q ≠ n1sOut32W411 j) → c.eval β q = β q :=
    fun q hq ↦ (hOut q (fun j ↦ hq ⟨j.val, by omega⟩)).trans
      (Function.update_of_ne (hq ⟨w0, by omega⟩) _ _)
  refine ⟨hsupp, hnon, ?_⟩
  let g : Fin 32 → ZMod 2 := fun j ↦ c.eval β (n1sOut32W411 j)
  have hc_ev : ∀ q, c.eval β q = (n1sCRow0Lt18 u0 hu0 dCut w0 (by omega)).eval β₁ q := fun _ ↦ rfl
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := w0 + 1) (k := 0) (by omega)
    (fun _ ↦ 0) g fun k hk ↦ by
      dsimp only [g]
      rw [hc_ev, hOut _ (fun i h ↦ by
        have hv := congrArg (@Fin.val 32) (n1s_out32W411_inj h); dsimp at hv; omega)]
      dsimp [β₁, CliffProg.eval]
      rw [Function.update_of_ne (fun h ↦ by
        have hv := congrArg (@Fin.val 32) (n1s_out32W411_inj h); dsimp at hv; omega), hout0 _]
  have hg_sl : bitsVal g = bitsVal (fun i : Fin (w0 + 1) ↦ g ⟨i.val, by omega⟩) := by
    have hz32 : bitsVal (fun _ : Fin 32 ↦ (0 : ZMod 2)) = 0 := by simp [bitsVal]
    have hzw : bitsVal (fun _ : Fin (w0 + 1) ↦ (0 : ZMod 2)) = 0 := by simp [bitsVal]
    have h0j : (fun j : Fin (w0 + 1) ↦ g ⟨0 + j.val, by omega⟩) =
        fun j : Fin (w0 + 1) ↦ g ⟨j.val, by omega⟩ :=
      funext fun j ↦ congrArg g (Fin.ext (Nat.zero_add j.val))
    rw [hz32, hzw, h0j] at hlin
    omega
  rw [hg_sl, bitsVal_castSucc_split]
  have hlo : (fun j : Fin w0 ↦ g ⟨j.val, by omega⟩) =
      fun j : Fin w0 ↦ β (n1sMantW411 ⟨dCut + j.val, by omega⟩) + (1 + β u0) :=
    funext fun j ↦ by
      dsimp only [g]
      rw [hc_ev, hIn j]
      dsimp [β₁, CliffProg.eval]
      rw [Function.update_of_ne (fun h ↦ by
          have hv := congrArg (@Fin.val 32) (n1s_out32W411_inj h); dsimp at hv; omega),
        hout0 _, zero_add,
        Function.update_of_ne (wire_ne_of_gt (by dsimp [n1sOut32W411, n1sMantW411]; omega)),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))]
  have htop : g ⟨w0, by omega⟩ = β u0 := by
    dsimp only [g]
    rw [hc_ev, hOut (n1sOut32W411 ⟨w0, by omega⟩) (fun i h ↦ by
      have hv := congrArg (@Fin.val 32) (n1s_out32W411_inj h); dsimp at hv; omega)]
    dsimp [β₁, CliffProg.eval]
    rw [Function.update_self, hout0 _, zero_add]
  change bitsVal (fun j : Fin w0 ↦ g ⟨j.val, by omega⟩) + 2 ^ w0 * (g ⟨w0, by omega⟩).val = _
  rw [hlo, htop, w14_mant_flip_msb_val β dCut w0 (by omega) (β u0)]
  unfold norm1sRowVal
  rw [ite_eq_left (by omega : 0 < dCut), show dCut - 0 = dCut from rfl,
    ite_eq_right (by omega : ¬(dCut = 18)), ite_eq_left hd.2]

theorem n1s_accSlice_ne_bLowF (off len w : ℕ) (hlen : off + len ≤ 32) (hw : w ≤ 18)
    (i : Fin len) (j : Fin (w + 2)) : n1sAccSlice off len hlen i ≠ n1sBLowF w hw j :=
  wire_ne_of_lt (lt_of_lt_of_le (n1s_accSlice_le_232 off len hlen i)
    (le_trans (by decide : 233 ≤ 302) (n1s_bLowF_ge_302 w hw j)))

theorem n1s_accSlice_ne_bLowR (off len w : ℕ) (hlen : off + len ≤ 32) (hw : w ≤ 18)
    (i : Fin len) (j : Fin (w + 1)) : n1sAccSlice off len hlen i ≠ n1sBLowR w hw j :=
  wire_ne_of_lt (lt_of_lt_of_le (n1s_accSlice_le_232 off len hlen i)
    (le_trans (by decide : 233 ≤ 302) (n1s_bLowR_ge_302 w hw j)))

theorem n1s_bitsVal_of_nat (w X : ℕ) (hX : X < 2 ^ w) :
    bitsVal (fun j : Fin w ↦ boolToZMod2 (X.testBit j.val)) = X := by
  apply bitsVal_eq_of_testBit _ _ hX
  intro j
  cases X.testBit j.val <;> rfl

theorem n1s_accSlice_ne_msb (off W : ℕ) (h : off + W + 2 ≤ 32) (j : Fin (W + 1)) :
    n1sAccSlice off (W + 1) (by omega) j ≠ n1sOut32W411 ⟨off + W + 1, by omega⟩ :=
  wire_ne_of_lt (by dsimp [n1sAccSlice, n1sOut32W411]; omega)

theorem n1s_bLowR_ne_out32 (w : ℕ) (hw : w ≤ 18) (j : Fin (w + 1)) (k : Fin 32) :
    n1sBLowR w hw j ≠ n1sOut32W411 k :=
  wire_ne_of_gt (lt_of_lt_of_le (by dsimp [n1sOut32W411]; omega : (n1sOut32W411 k).val < 302)
    (n1s_bLowR_ge_302 w hw j))

/-- Carry-in wire `cin` lies in `u_K` (`< 90`) or `{zPad2, cinW}` (`381, 382`). -/
def n1sValidCin (cin : Wire 411) : Prop :=
  cin.val < 90 ∨ (381 ≤ cin.val ∧ cin.val < 383)

theorem n1s_zPad2_validCin : n1sValidCin n1sZPad2W411 := Or.inr ⟨by decide, by decide⟩

theorem n1s_cinW_validCin : n1sValidCin n1sCinW411 := Or.inr ⟨by decide, by decide⟩

theorem n1s_validCin_lt {cin : Wire 411} (hc : n1sValidCin cin) : cin.val < 383 := by
  rcases hc with h | ⟨_, h⟩ <;> omega

theorem n1s_out32_ne_validCin (k : Fin 32) {cin : Wire 411} (hc : n1sValidCin cin) :
    n1sOut32W411 k ≠ cin := by
  rcases hc with h | ⟨h, _⟩
  · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
  · exact wire_ne_of_lt (by dsimp [n1sOut32W411]; omega)

theorem n1s_accSlice_ne_validCin (off len : ℕ) (hlen : off + len ≤ 32)
    {cin : Wire 411} (hc : n1sValidCin cin) (j : Fin len) :
    n1sAccSlice off len hlen j ≠ cin :=
  n1s_out32_ne_validCin ⟨off + j.val, by omega⟩ hc

theorem n1s_bLowF_ne_validCin (w : ℕ) (hw : w ≤ 18)
    {cin : Wire 411} (hc : n1sValidCin cin) (j : Fin (w + 2)) :
    n1sBLowF w hw j ≠ cin := by
  rcases hc with h | ⟨h, _⟩
  · exact wire_ne_of_gt (lt_of_lt_of_le (lt_trans h (by decide : 90 < 302))
      (n1s_bLowF_ge_302 w hw j))
  · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowF_le_380 w hw j) h)

theorem n1s_bLowR_ne_validCin (w : ℕ) (hw : w ≤ 18)
    {cin : Wire 411} (hc : n1sValidCin cin) (j : Fin (w + 1)) :
    n1sBLowR w hw j ≠ cin := by
  rcases hc with h | ⟨h, _⟩
  · exact wire_ne_of_gt (lt_of_lt_of_le (lt_trans h (by decide : 90 < 302))
      (n1s_bLowR_ge_302 w hw j))
  · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 w hw j)
      (lt_of_lt_of_le (by decide : 379 < 381) h))

/-- Shared `inPlaceAddMod1` instantiation on `n1sBLowF` and `n1sAccSlice`. -/
abbrev n1sMkInPlaceAdd (off w : ℕ) (hw18 : w ≤ 18)
    (hcur : 383 + (w + 1) ≤ 411) (hacc : off + (w + 2) ≤ 32)
    (cin : Wire 411) (hcin : n1sValidCin cin) : TempPhaseProg 411 :=
  inPlaceAddMod1 (w + 1) 383 hcur (n1sBLowF w hw18) (n1sAccSlice off (w + 2) hacc) cin
    (fun j ↦ n1s_accSlice_ne_bLowF off (w + 2) w hacc hw18 j j)
    (n1s_accSlice_ne_validCin off (w + 2) hacc hcin) (n1s_bLowF_ne_validCin w hw18 hcin)
    (n1s_bLowF_lt w hw18) (n1s_accSlice_lt off (w + 2) hacc) (n1s_validCin_lt hcin)

/-- Shared `cleanMsbSubStatic` instantiation on `n1sBLowR` and `n1sAccSlice`. -/
abbrev n1sMkCleanMsbSub (off w : ℕ) (hw18 : w ≤ 18)
    (hcur : 383 + w + 1 ≤ 411) (hacc : off + (w + 1) ≤ 32)
    (msbIdx : Fin 32) (cin : Wire 411) (hcin : n1sValidCin cin) : TempPhaseProg 411 :=
  cleanMsbSubStatic w 383 hcur (n1sBLowR w hw18) (n1sAccSlice off (w + 1) hacc)
    (n1sOut32W411 msbIdx) cin (fun j ↦ n1s_accSlice_ne_bLowR off (w + 1) w hacc hw18 j j)
    (n1s_accSlice_ne_validCin off (w + 1) hacc hcin) (n1s_bLowR_ne_validCin w hw18 hcin)
    (n1s_out32_ne_validCin msbIdx hcin) (n1s_bLowR_lt w hw18) (n1s_accSlice_lt off (w + 1) hacc)
    (by dsimp [n1sOut32W411]; omega) (n1s_validCin_lt hcin)

/-- Shared `dCleanMsbSub` instantiation on `n1sBLowR` and `n1sAccSlice`. -/
abbrev n1sMkDCleanMsbSub {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n)
    (off w : ℕ) (hw18 : w ≤ 18) (hcur : 383 + w ≤ 411) (hacc : off + (w + 1) ≤ 32)
    (msbIdx : Fin 32) (cin : Wire 411) (hcin : n1sValidCin cin) : DynamicCircuit Var n :=
  dCleanMsbSub v rComb w 383 hcur (n1sBLowR w hw18) (n1sAccSlice off (w + 1) hacc)
    (n1sOut32W411 msbIdx) cin (fun j ↦ n1s_accSlice_ne_bLowR off (w + 1) w hacc hw18 j j)
    (n1s_accSlice_ne_validCin off (w + 1) hacc hcin) (n1s_bLowR_ne_validCin w hw18 hcin)
    (n1s_out32_ne_validCin msbIdx hcin) (n1s_bLowR_lt w hw18) (n1s_accSlice_lt off (w + 1) hacc)
    (by dsimp [n1sOut32W411]; omega) (n1s_validCin_lt hcin)

/-- Forward combined `m = 0, 1` base step for `t.dCut = 18` (`2` `TempAnd`s, `cin = u_0`). -/
def n1sBaseFwdD18 (t : Norm1sTier) : TempPhaseProg 411 :=
  let u0 := n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩
  let u1 := n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩
  have hu1 : u1.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc (n1sCRowSetup u1 hu1 17 1 (by decide))
    (n1sMkInPlaceAdd 0 1 (by decide) (by decide) (by decide) u0
      (Or.inl (n1s_uKW411_range t _).2))

/-- Reverse static combined `m = 0, 1` base step for `t.dCut = 18` (`W = 1`, `4 T` dynamic). -/
def n1sBaseRevStaticD18 (t : Norm1sTier) : TempPhaseProg 411 :=
  let u0 := n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩
  let u1 := n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩
  have hu1 : u1.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc (n1sCRowSetup u1 hu1 17 1 (by decide))
    (n1sMkCleanMsbSub 0 1 (by decide) (by decide) (by decide) ⟨2, by decide⟩ u0
      (Or.inl (n1s_uKW411_range t _).2))

/-- Dynamic `4 T` (`0 .TOFF`) reverse combined `m = 0, 1` base step for `t.dCut = 18`. -/
def n1sDBaseRevD18 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  let u0 := n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩
  let u1 := n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩
  have hu1 : u1.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  p57ToDynWith v rComb
    (n1sMkDCleanMsbSub v rComb 0 1 (by decide) (by decide) (by decide) ⟨2, by decide⟩ u0
      (Or.inl (n1s_uKW411_range t _).2))
    (ctxCliffAlloc (n1sCRowSetup u1 hu1 17 1 (by decide)))

/-- Single Low Booth forward row `m` (`1 <= m < t.dCut`, `w = 18 - (t.dCut - m) >= 2`, `w + 1`
  `TempAnd`s). -/
def n1sLowRowFwd (t : Norm1sTier) (m : ℕ) (_hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (_hw2 : 2 ≤ 18 - (t.dCut - m)) : TempPhaseProg 411 :=
  let sh := t.dCut - m
  let w := 18 - sh
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc (n1sCRowSetup uW hu sh w (by have := n1s_tier_bounds t; dsimp [w, sh]; omega))
    (n1sMkInPlaceAdd 0 w (by dsimp [w]; omega) (by dsimp [w]; omega) (by dsimp [w]; omega)
      n1sZPad2W411 n1s_zPad2_validCin)

/-- Single Low Booth reverse static row `m` (`w` `TempAnd`s). -/
def n1sLowRowRevStatic (t : Norm1sTier) (m : ℕ) (_hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (_hw2 : 2 ≤ 18 - (t.dCut - m)) : TempPhaseProg 411 :=
  let sh := t.dCut - m
  let w := 18 - sh
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc (n1sCRowSetup uW hu sh w (by have := n1s_tier_bounds t; dsimp [w, sh]; omega))
    (n1sMkCleanMsbSub 0 w (by dsimp [w]; omega) (by dsimp [w]; omega) (by dsimp [w]; omega)
      ⟨w + 1, by dsimp [w]; omega⟩ n1sZPad2W411 n1s_zPad2_validCin)

/-- Dynamic `4 * w` `T` (`0 .TOFF`) reverse Low Booth row `m`. -/
def n1sDLowRowRev (t : Norm1sTier) (m : ℕ) (_hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (_hw2 : 2 ≤ 18 - (t.dCut - m)) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  let sh := t.dCut - m
  let w := 18 - sh
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  p57ToDynWith v rComb
    (n1sMkDCleanMsbSub v rComb 0 w (by dsimp [w]; omega)
      (by dsimp [w]; omega) (by dsimp [w]; omega)
      ⟨w + 1, by dsimp [w]; omega⟩ n1sZPad2W411 n1s_zPad2_validCin)
    (ctxCliffAlloc (n1sCRowSetup uW hu sh w (by have := n1s_tier_bounds t; dsimp [w, sh]; omega)))

/-- Single High Booth forward row `off = m - t.dCut` (`0 <= off < t.kBits - t.dCut`, `19`
  `TempAnd`s). -/
def n1sHighRowFwd (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc (n1sCRowSetup uW hu 0 18 (by decide))
    (n1sMkInPlaceAdd off 18 le_rfl (by decide) (by omega) n1sCinW411 n1s_cinW_validCin)

/-- Single High Booth reverse static row `off` (`18` `TempAnd`s). -/
def n1sHighRowRevStatic (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut) :
    TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc (n1sCRowSetup uW hu 0 18 (by decide))
    (n1sMkCleanMsbSub off 18 le_rfl (by decide) (by omega) ⟨off + 19, by omega⟩
      n1sCinW411 n1s_cinW_validCin)

/-- Dynamic `72 T` (`0 .TOFF`) reverse High Booth row `off`. -/
def n1sDHighRowRev (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut)
    {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) : DynamicCircuit Var n :=
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  p57ToDynWith v rComb
    (n1sMkDCleanMsbSub v rComb off 18 le_rfl (by decide) (by omega) ⟨off + 19, by omega⟩
      n1sCinW411 n1s_cinW_validCin)
    (ctxCliffAlloc (n1sCRowSetup uW hu 0 18 (by decide)))

/-- Top unsigned `+ mS * 2 ^ (kBits - dCut)` forward row (`19` `TempAnd`s). -/
def n1sTopRowFwd (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  n1sMkInPlaceAdd (t.kBits - t.dCut) 18 le_rfl (by decide) (by omega)
    n1sZPad2W411 n1s_zPad2_validCin

/-- Top unsigned reverse static row (`18` `TempAnd`s). -/
def n1sTopRowRevStatic (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  n1sMkCleanMsbSub (t.kBits - t.dCut) 18 le_rfl (by decide) (by omega)
    ⟨(t.kBits - t.dCut) + 19, by omega⟩ n1sZPad2W411 n1s_zPad2_validCin

/-- Dynamic `72 T` (`0 .TOFF`) reverse Top Booth row. -/
def n1sDTopRowRev (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  have hb := n1s_tier_bounds t
  n1sMkDCleanMsbSub v rComb (t.kBits - t.dCut) 18 le_rfl (by decide) (by omega)
    ⟨(t.kBits - t.dCut) + 19, by omega⟩ n1sZPad2W411 n1s_zPad2_validCin

/-- Prefix forward Booth loop up to row `m <= t.kBits` (`m >= mMin`, where `mMin = 2` for `dCut =
  18` else `1`). -/
def n1sBoothPrefixFwd (t : Norm1sTier) : (m : ℕ) → (hm : m ≤ t.kBits) → TempPhaseProg 411
  | 0, _ => .cliff .nil
  | 1, _ =>
      if hd18 : t.dCut = 18 then .cliff .nil
      else
        have hb := n1s_tier_bounds t
        let u0 := n1sUKW411 t ⟨0, by omega⟩
        .cliff (n1sCRow0Full u0 (lt_trans (n1s_uKW411_range t _).2 (by
          decide)) t.dCut ⟨hb.2.2.1, by omega⟩)
  | 2, _ =>
      if hd18 : t.dCut = 18 then n1sBaseFwdD18 t
      else
        have hb := n1s_tier_bounds t
        .seq (n1sBoothPrefixFwd t 1 (by omega))
          (n1sLowRowFwd t 1 le_rfl (by omega) (by omega))
  | m + 3, hm =>
      have hb := n1s_tier_bounds t
      let prev := n1sBoothPrefixFwd t (m + 2) (by omega)
      if hlow : m + 2 < t.dCut then
        .seq prev (n1sLowRowFwd t (m + 2) (by omega) hlow (by omega))
      else
        .seq prev (n1sHighRowFwd t ((m + 2) - t.dCut) (by omega))

/-- Full forward Booth accumulator (`n1sBoothPrefixFwd t t.kBits` + `n1sTopRowFwd t`). -/
def n1sBoothFwd411 (t : Norm1sTier) : TempPhaseProg 411 :=
  .seq (n1sBoothPrefixFwd t t.kBits le_rfl) (n1sTopRowFwd t)

/-- Prefix reverse static Booth loop from `m <= t.kBits` down to `0`. -/
def n1sBoothPrefixRevStatic (t : Norm1sTier) : (m : ℕ) → (hm : m ≤ t.kBits) → TempPhaseProg 411
  | 0, _ => .cliff .nil
  | 1, _ =>
      if hd18 : t.dCut = 18 then .cliff .nil
      else
        have hb := n1s_tier_bounds t
        let u0 := n1sUKW411 t ⟨0, by omega⟩
        .cliff (n1sCRow0Full u0 (lt_trans (n1s_uKW411_range t _).2 (by
          decide)) t.dCut ⟨hb.2.2.1, by omega⟩).inv
  | 2, _ =>
      if hd18 : t.dCut = 18 then n1sBaseRevStaticD18 t
      else
        have hb := n1s_tier_bounds t
        .seq (n1sLowRowRevStatic t 1 le_rfl (by omega) (by omega))
          (n1sBoothPrefixRevStatic t 1 (by omega))
  | m + 3, hm =>
      have hb := n1s_tier_bounds t
      let rest := n1sBoothPrefixRevStatic t (m + 2) (by omega)
      if hlow : m + 2 < t.dCut then
        .seq (n1sLowRowRevStatic t (m + 2) (by omega) hlow (by omega)) rest
      else
        .seq (n1sHighRowRevStatic t ((m + 2) - t.dCut) (by omega)) rest

/-- Full reverse static Booth accumulator (`n1sTopRowRevStatic t` + `n1sBoothPrefixRevStatic t
  t.kBits`). -/
def n1sBoothRevStatic411 (t : Norm1sTier) : TempPhaseProg 411 :=
  .seq (n1sTopRowRevStatic t) (n1sBoothPrefixRevStatic t t.kBits le_rfl)

/-- Prefix dynamic `0 .TOFF` reverse Booth loop from `m <= t.kBits` down to `0`. -/
def n1sDBoothPrefixRev (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    (m : ℕ) → (hm : m ≤ t.kBits) → DynamicCircuit Var n
  | 0, _ => .circuit (((CliffProg.nil : CliffProg 411).onRegister rComb).toCircuit)
  | 1, _ =>
      if hd18 : t.dCut = 18 then
        .circuit (((CliffProg.nil : CliffProg 411).onRegister rComb).toCircuit)
      else
        have hb := n1s_tier_bounds t
        let u0 := n1sUKW411 t ⟨0, by omega⟩
        let c0 := (n1sCRow0Full u0 (lt_trans (n1s_uKW411_range t _).2 (by
          decide)) t.dCut ⟨hb.2.2.1, by omega⟩).inv
        .circuit ((c0.onRegister rComb).toCircuit)
  | 2, _ =>
      if hd18 : t.dCut = 18 then n1sDBaseRevD18 t v rComb
      else
        have hb := n1s_tier_bounds t
        .seq (n1sDLowRowRev t 1 le_rfl (by omega) (by omega) v rComb)
          (n1sDBoothPrefixRev t v rComb 1 (by omega))
  | m + 3, hm =>
      have hb := n1s_tier_bounds t
      let rest := n1sDBoothPrefixRev t v rComb (m + 2) (by omega)
      if hlow : m + 2 < t.dCut then
        .seq (n1sDLowRowRev t (m + 2) (by omega) hlow (by omega) v rComb) rest
      else
        .seq (n1sDHighRowRev t ((m + 2) - t.dCut) (by omega) v rComb) rest

theorem n1s_rowVal_max (dCut m mS : ℕ) (hmS : mS < 2 ^ 18) (_hd : 16 ≤ dCut ∧ dCut ≤ 18)
    (uBit : Bool) : (m < dCut → dCut - m = 18 → norm1sRowVal dCut m mS uBit ≤ 1) ∧ (m < dCut →
    dCut - m < 18 → norm1sRowVal dCut m mS uBit + 1 ≤ 2 ^ (18 - (dCut - m) + 1)) ∧ (dCut ≤ m →
    norm1sRowVal dCut m mS uBit + 2 ^ (m - dCut) ≤ 2 ^ (m - dCut + 19)) := by
  refine ⟨fun hm h18 ↦ ?_, fun hm hlt18 ↦ ?_, fun hge ↦ ?_⟩
  · unfold norm1sRowVal
    rw [ite_eq_left hm, ite_eq_left h18]
    cases uBit <;> decide
  · unfold norm1sRowVal
    rw [ite_eq_left hm]
    rw [ite_eq_right (by omega : ¬(dCut - m = 18)), ite_eq_left hlt18]
    set sh := dCut - m
    set w := 18 - sh
    have hxm : mS / 2 ^ sh < 2 ^ w := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_add]
      have hsum : sh + w = 18 := by omega
      rw [hsum]; exact hmS
    have hp : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [pow_succ]; ring
    change (if uBit = true then 2 ^ w + mS / 2 ^ sh else 2 ^ w - 1 - mS / 2 ^ sh) + 1 ≤ 2 ^ (w + 1)
    rw [hp]
    generalize mS / 2 ^ sh = x, 2 ^ w = P at hxm ⊢
    cases uBit <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  · unfold norm1sRowVal
    rw [ite_eq_right (by omega : ¬(m < dCut))]
    set off := m - dCut
    have hp : 2 ^ (off + 19) = (2 * 2 ^ 18) * 2 ^ off := by ring
    rw [hp]
    have h218 : (2 ^ 18 : ℕ) = 262144 := by decide
    cases uBit <;> simp only [↓reduceIte, Bool.false_eq_true]
    · have hle : (2 ^ 18 - mS) + 1 ≤ 2 * 2 ^ 18 := by omega
      have hm := Nat.mul_le_mul_right (2 ^ off) hle
      simpa [Nat.add_mul, one_mul] using hm
    · have hle : (2 ^ 18 + mS) + 1 ≤ 2 * 2 ^ 18 := by omega
      have hm := Nat.mul_le_mul_right (2 ^ off) hle
      simpa [Nat.add_mul, one_mul] using hm

theorem n1s_rowsAux_bounds (t : Norm1sTier) (mS uK : ℕ) (hmS : mS < 2 ^ 18) : ∀ (m : ℕ), m ≤
    t.kBits → (t.dCut = 18 → m = 2 → norm1sHwRowsAux t.dCut mS uK 2 + 2 ≤ 2 ^ 3) ∧ (t.dCut <
    18 → m = 1 → norm1sHwRowsAux t.dCut mS uK 1 + 2 ≤ 2 ^ ((18 - t.dCut) + 2)) ∧ ((if t.dCut =
    18 then 2 else 1) ≤ m → m ≤ t.dCut → norm1sHwRowsAux t.dCut mS uK m + 2 ≤ 2 ^ ((18 -
    t.dCut) + m + 1)) ∧ (t.dCut ≤ m → norm1sHwRowsAux t.dCut mS uK m + 2 ^ (m - t.dCut) + 1 ≤
    2 ^ ((m - t.dCut) + 19)) := by
  have hb := n1s_tier_bounds t
  have hd : 16 ≤ t.dCut ∧ t.dCut ≤ 18 := ⟨hb.2.2.1, hb.2.2.2.1⟩
  have hBaseD18 : t.dCut = 18 → norm1sHwRowsAux t.dCut mS uK 2 + 2 ≤ 2 ^ 3 := fun hd18 ↦ by
    rw [hd18]
    dsimp [norm1sHwRowsAux]
    have r0 := (n1s_rowVal_max 18 0 mS hmS ⟨by decide, by decide⟩ (uK.testBit 0)).1
      (by decide) rfl
    have r1 := (n1s_rowVal_max 18 1 mS hmS ⟨by decide, by decide⟩ (uK.testBit 1)).2.1
      (by decide) (by decide)
    have h4 : (2 ^ (18 - (18 - 1) + 1) : ℕ) = 4 := by decide
    omega
  have hBaseLt18 : t.dCut < 18 → norm1sHwRowsAux t.dCut mS uK 1 + 2 ≤ 2 ^ ((18 - t.dCut) + 2) :=
    fun hlt ↦ by
      dsimp [norm1sHwRowsAux]
      have r0 := (n1s_rowVal_max t.dCut 0 mS hmS hd (uK.testBit 0)).2.1 (by omega) (by omega)
      rw [show t.dCut - 0 = t.dCut from rfl] at r0
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ 18 - t.dCut + 1)
      have hp : 2 ^ ((18 - t.dCut) + 2) = 2 * 2 ^ (18 - t.dCut + 1) := by ring
      omega
  have hLow : ∀ m, (if t.dCut = 18 then 2 else 1) ≤ m → m ≤ t.dCut →
      norm1sHwRowsAux t.dCut mS uK m + 2 ≤ 2 ^ ((18 - t.dCut) + m + 1) := by
    intro m hlo hhi
    induction m with
    | zero => by_cases hd18 : t.dCut = 18 <;> simp [hd18] at hlo
    | succ k ih =>
        by_cases hbase : (t.dCut = 18 ∧ k = 1) ∨ (t.dCut ≠ 18 ∧ k = 0)
        · rcases hbase with ⟨hd18, rfl⟩ | ⟨_, rfl⟩
          · simpa [hd18] using hBaseD18 hd18
          · simpa [Nat.add_assoc] using hBaseLt18 (by omega)
        · have hk_lo : (if t.dCut = 18 then 2 else 1) ≤ k := by
            split_ifs with hd18 <;> simp only [hd18, ↓reduceIte] at hlo <;> omega
          have ihk := ih hk_lo (by omega)
          dsimp [norm1sHwRowsAux]
          have rk := (n1s_rowVal_max t.dCut k mS hmS hd (uK.testBit k)).2.1 (by omega)
            (by split_ifs at hk_lo <;> omega)
          rw [show 18 - (t.dCut - k) + 1 = (18 - t.dCut) + k + 1 from by omega] at rk
          have hp : 2 ^ ((18 - t.dCut) + (k + 1) + 1) = 2 * 2 ^ ((18 - t.dCut) + k + 1) := by
            rw [show (18 - t.dCut) + (k + 1) + 1 = ((18 - t.dCut) + k + 1) + 1 from by omega]
            ring
          omega
  have hHigh : ∀ m, t.dCut ≤ m → m ≤ t.kBits →
      norm1sHwRowsAux t.dCut mS uK m + 2 ^ (m - t.dCut) + 1 ≤ 2 ^ ((m - t.dCut) + 19) := by
    intro m hge hmk
    induction m with
    | zero => omega
    | succ k ih =>
        by_cases m_eq : k + 1 = t.dCut
        · rw [m_eq]
          have hL := hLow t.dCut (by
            by_cases h18 : t.dCut = 18
            · simp [h18]
            · simp [h18]; omega) le_rfl
          rw [show (18 - t.dCut) + t.dCut + 1 = 19 from by omega] at hL
          simp only [Nat.sub_self, _root_.pow_zero, Nat.zero_add]
          omega
        · have ihk := ih (by omega) (by omega)
          dsimp [norm1sHwRowsAux]
          have rk := (n1s_rowVal_max t.dCut k mS hmS hd (uK.testBit k)).2.2 (by omega)
          set off := k - t.dCut
          rw [show k + 1 - t.dCut = off + 1 from by omega]
          have hp1 : 2 ^ (off + 1) = 2 * 2 ^ off := by ring
          have hp2 : 2 ^ ((off + 1) + 19) = 2 * 2 ^ (off + 19) := by
            rw [show (off + 1) + 19 = (off + 19) + 1 from by omega]
            ring
          omega
  exact fun m hm ↦ ⟨fun hd18 _ ↦ hBaseD18 hd18, fun hlt _ ↦ hBaseLt18 hlt,
    fun h1 h2 ↦ hLow m h1 h2, fun hge ↦ hHigh m hge hm⟩

theorem n1s_hwProd_lt_two_pow_wAcc (t : Norm1sTier) (mS uK : ℕ) (hmS : mS < 2 ^ 18) :
    norm1sHwRowsAux t.dCut mS uK t.kBits / 2 ^ (t.kBits - t.dCut) < 2 ^ 19 ∧
    norm1sHwProd t.kBits t.dCut mS uK < 2 ^ t.wAcc := by
  have hb := n1s_tier_bounds t
  have hH := (n1s_rowsAux_bounds t mS uK hmS t.kBits le_rfl).2.2.2 (by omega)
  unfold norm1sHwProd
  set topOff := t.kBits - t.dCut
  have hlt : norm1sHwRowsAux t.dCut mS uK t.kBits < 2 ^ topOff * 2 ^ 19 := by
    have hp : 2 ^ (topOff + 19) = 2 ^ topOff * 2 ^ 19 := by ring
    have := Nat.two_pow_pos topOff
    omega
  refine ⟨Nat.div_lt_of_lt_mul hlt, ?_⟩
  rw [hb.2.2.2.2.1]
  have hw_eq : 20 + t.kBits - t.dCut = topOff + 20 := by dsimp [topOff]; omega
  rw [hw_eq]
  have hp20 : 2 ^ (topOff + 20) = 2 ^ topOff * 2 ^ 19 + 2 ^ topOff * 2 ^ 19 := by
    have ha : topOff + 20 = topOff + 19 + 1 := by omega
    rw [ha, pow_succ, pow_add]; ring
  have hmS_mul : mS * 2 ^ topOff < 2 ^ topOff * 2 ^ 19 := by
    have hm19 : mS < 2 ^ 19 := lt_trans hmS (by decide)
    have hmul := Nat.mul_lt_mul_of_pos_left hm19 (Nat.two_pow_pos topOff)
    rwa [mul_comm (2 ^ topOff) mS] at hmul
  omega

/-- Booth prefix invariant on `M = 411`: `cleanRem 411 (411 - 379)` and `out32 = norm1sHwRowsAux
  ... m`. -/
def n1sBoothInv (t : Norm1sTier) (m : ℕ) (γ : BitAssignment 411) : Prop := bitsVal
    (fun j : Fin 32 ↦ γ (n1sOut32W411 j)) = norm1sHwRowsAux t.dCut
    (bitsVal (fun i : Fin 18 ↦ γ (n1sMantW411 i)))
    (bitsVal (fun k : Fin t.kBits ↦ γ (n1sUKW411 t k))) m

/-- Post-Booth invariant on `M = 411`: `out32 = norm1sHwProd t.kBits t.dCut mS uK`. -/
def n1sBoothDoneInv (t : Norm1sTier) (γ : BitAssignment 411) : Prop := bitsVal
    (fun j : Fin 32 ↦ γ (n1sOut32W411 j)) = norm1sHwProd t.kBits t.dCut
    (bitsVal (fun i : Fin 18 ↦ γ (n1sMantW411 i)))
    (bitsVal (fun k : Fin t.kBits ↦ γ (n1sUKW411 t k)))

theorem n1s_toDynWith_realizes_supp
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n)
    (innerProg : TempPhaseProg M) (dInner : DynamicCircuit Var n)
    (InvHole : BitAssignment M → Prop) (curHole : ℕ) (hcurHole : curHole ≤ M)
    (hInner : RealizesCleanUnitary v (p57CleanDiagProj rComb (M - curHole) (by omega) InvHole)
      dInner (((innerProg.onRegister rComb).toToffCircuit).eval)) :
    ∀ (K : TempCtx M), K.SupportsBelowCtx curHole →
      ∀ (rem : ℕ) (hrem : rem ≤ M) (hle : M - curHole ≤ rem) (Inv : BitAssignment M → Prop),
        ValidCleanRem M rem (K.plug innerProg) →
        (∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ → InvHole (K.fwdBits γ)) →
        RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv)
          (p57ToDynWith v rComb dInner K)
          ((((K.plug innerProg).onRegister rComb).toToffCircuit).eval)
  | .hole, _, rem, hrem, hle, Inv, _, hFwd =>
      RealizesCleanUnitary.mono_proj
        (p57CleanDiagProj_conjTranspose rComb (M - curHole) (by omega) InvHole)
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_mono rComb (by omega) hrem hle hFwd)
        hInner
  | .seqPre c K, hSupp, rem, hrem, hle, Inv, ⟨remMid, hmid, _, hv₂, hpres⟩, hFwd => by
      let remMid' := max remMid (M - curHole)
      have hmid' : remMid' ≤ M := max_le hmid (by omega)
      have hle' : M - curHole ≤ remMid' := le_max_right _ _
      have hv₂' : ValidCleanRem M remMid' (K.plug innerProg) :=
        validCleanRem_mono (le_max_left _ _) hv₂
      have hpres' : ∀ γ : BitAssignment M, cleanRem M rem γ → cleanRem M remMid' (c.eval γ) :=
        fun γ hcr w hw ↦ by
          by_cases hw1 : M - remMid ≤ w.val
          · exact hpres γ hcr w hw1
          · have hw2 : curHole ≤ w.val := by dsimp [remMid'] at hw; omega
            rw [c.eval_outside hSupp.1 γ w hw2]
            exact hcr w (by omega)
      let InvMid : BitAssignment M → Prop :=
        fun δ ↦ ∃ γ, cleanRem M rem γ ∧ Inv γ ∧ δ = c.eval γ
      have ih₂ := n1s_toDynWith_realizes_supp v rComb innerProg dInner InvHole curHole hcurHole
        hInner K hSupp.2 remMid' hmid' hle' InvMid hv₂' (fun δ _ ⟨γ, hcr, hi, hδ⟩ ↦ by
          subst hδ; exact hFwd γ hcr hi)
      have hseq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_conjTranspose rComb remMid' hmid' InvMid)
        (RealizesCleanUnitary.circuit v _ ((c.onRegister rComb).toCircuit)) ih₂
        (p57SeqClean_prog_inv rComb (.cliff c) hrem hmid'
          (fun γ hcr hi ↦ ⟨hpres' γ hcr, ⟨γ, hcr, hi, rfl⟩⟩))
      have heq : ((K.plug innerProg).onRegister rComb).toToffCircuit.eval *
          ((c.onRegister rComb).toCircuit).eval =
          ((((TempCtx.seqPre c K).plug innerProg).onRegister rComb).toToffCircuit).eval := by
        simp [TempCtx.plug, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      dsimp only [p57ToDynWith]
      rw [heq] at hseq
      exact hseq
  | .seqPost K c, hSupp, rem, hrem, hle, Inv, ⟨remMid, hmid, hv₁, _, hpres⟩, hFwd => by
      have ih₁ := n1s_toDynWith_realizes_supp v rComb innerProg dInner InvHole curHole hcurHole
        hInner K hSupp.1 rem hrem hle Inv hv₁ hFwd
      have hseq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_conjTranspose rComb remMid hmid (fun _ ↦ True))
        ih₁ (RealizesCleanUnitary.circuit v _ ((c.onRegister rComb).toCircuit))
        (p57SeqClean_prog_inv rComb (K.plug innerProg) hrem hmid
          (fun γ hcr _ ↦ ⟨hpres γ hcr, trivial⟩))
      have heq : ((c.onRegister rComb).toCircuit).eval *
          ((K.plug innerProg).onRegister rComb).toToffCircuit.eval =
          ((((TempCtx.seqPost K c).plug innerProg).onRegister rComb).toToffCircuit).eval := by
        simp [TempCtx.plug, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      dsimp only [p57ToDynWith]
      rw [heq] at hseq
      exact hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, hSupp, rem, hrem, _, Inv, ⟨hanc_lo, hvBody, hpresBody⟩,
    hFwd => by
      have hanc_cur : anc.val < curHole := hSupp.1
      have hanc_lt : anc.val < M := anc.isLt
      let InvBody : BitAssignment M → Prop := fun δ ↦ (cleanRem M rem (Function.update δ anc
          0) ∧ Inv (Function.update δ anc 0)) ∧ δ anc = δ c₁ * δ c₂
      have ihBody := n1s_toDynWith_realizes_supp v rComb innerProg dInner InvHole curHole hcurHole
        hInner K hSupp.2 (M - (anc.val + 1)) (by omega) (by omega) InvBody hvBody
        (fun δ _ ⟨⟨hcr, hi⟩, hbit⟩ ↦ by
          let γ := Function.update δ anc 0
          have hδ_eq : Function.update γ anc (γ anc + γ c₁ * γ c₂) = δ := by
            funext w
            by_cases hw : w = anc
            · subst hw
              simp [γ, Function.update_self, Function.update_of_ne h₁a,
                Function.update_of_ne h₂a, hbit]
            · simp [γ, Function.update_of_ne hw]
          have hstep := hFwd γ hcr hi
          dsimp only [TempCtx.fwdBits] at hstep
          rwa [hδ_eq] at hstep)
      exact p57WithTempAnd_cleanDiagProj v rComb c₁ c₂ anc h₁₂ h₁a h₂a rem hrem hanc_lo Inv
        (K.plug innerProg) (p57ToDynWith v rComb dInner K) hpresBody ihBody

theorem n1s_not_mem_out32 {q : Wire 411} (hq : q.val < 201 ∨ 233 ≤ q.val) :
    ¬ (∃ k : Fin 32, q = n1sOut32W411 k) := by
  rintro ⟨k, rfl⟩
  dsimp [n1sOut32W411] at hq
  omega

theorem n1s_flipMantSlice_disj_ex (off : ℕ) :
    ∀ (w : ℕ) (hoff : off + w ≤ 18),
      CliffDisjoint (fun q : Wire 411 ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
        (n1sFlipMantSlice off w hoff)
  | 0, _ => trivial
  | w + 1, hoff =>
      ⟨⟨n1s_not_mem_out32 (Or.inr (by decide)),
        n1s_not_mem_out32 (Or.inr (by dsimp [n1sMantW411]; omega))⟩,
       n1s_flipMantSlice_disj_ex off w (by omega)⟩

theorem n1s_cRowSetup_disj_ex (uW : Wire 411) (hu : uW.val < 201) (off w : ℕ)
    (hoff : off + w ≤ 18) : CliffDisjoint
    (fun q : Wire 411 ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
    (n1sCRowSetup uW (lt_trans hu (by decide)) off w hoff) := ⟨n1s_not_mem_out32 (Or.inr
    (by decide)), ⟨n1s_not_mem_out32 (Or.inl hu), n1s_not_mem_out32 (Or.inr (by decide))⟩,
    ⟨n1s_not_mem_out32 (Or.inl hu), n1s_not_mem_out32 (Or.inr (by decide))⟩,
    n1s_flipMantSlice_disj_ex off w hoff⟩

theorem n1s_mant_uK_congr (t : Norm1sTier) {β δ : BitAssignment 411} (hnon : ∀ q : Wire 411,
    (∀ k : Fin 32, q ≠ n1sOut32W411 k) → δ q = β q) : bitsVal
    (fun i : Fin 18 ↦ δ (n1sMantW411 i)) = bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) ∧
    bitsVal (fun k : Fin t.kBits ↦ δ (n1sUKW411 t k)) = bitsVal
    (fun k : Fin t.kBits ↦ β (n1sUKW411 t k)) := by
  refine ⟨congrArg bitsVal (funext fun i ↦ hnon _ fun k ↦
      wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega)),
    congrArg bitsVal (funext fun m ↦ hnon _ fun k ↦
      wire_ne_of_lt (by have := (n1s_uKW411_range t m).2; dsimp [n1sOut32W411]; omega))⟩

private theorem n1s_out32_slice_div {W off P : ℕ} (hacc : off + W ≤ 32)
    {β : BitAssignment 411} (hInv : bitsVal (fun k : Fin 32 ↦ β (n1sOut32W411 k)) = P)
    (hlt : P / 2 ^ off < 2 ^ W) :
    bitsVal (fun j : Fin W ↦ β (n1sOut32W411 ⟨off + j.val, by omega⟩)) = P / 2 ^ off := by
  rw [bitsVal_slice_eq_div_mod hacc (fun k ↦ β (n1sOut32W411 k)), hInv, Nat.mod_eq_of_lt hlt]

private theorem n1s_withCliffAlloc_row_lift
    (uW : Wire 411) (hu_201 : uW.val < 201) (hu_379 : uW.val < 379)
    (sh w : ℕ) (hoff_sh : sh + w ≤ 18) (body : TempPhaseProg 411)
    (hvBody : ValidCleanRem 411 (411 - 383) body)
    (hBody : ∀ γ : BitAssignment 411, cleanRem 411 (411 - 383) γ →
      body.evalSign γ = 0 ∧
        ∀ u : Wire 411, (∀ k : Fin 32, u ≠ n1sOut32W411 k) → body.evalBits γ u = γ u) :
    let c := n1sCRowSetup uW hu_379 sh w hoff_sh
    let p := withCliffAlloc c body
    ValidCleanRem 411 (411 - 379) p ∧
      ∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        cleanRem 411 (411 - 383) (c.eval β) ∧
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (∀ k : Fin 32, p.evalBits β (n1sOut32W411 k) = body.evalBits (c.eval β) (n1sOut32W411 k)) ∧
        (∀ k : Fin 32, c.eval β (n1sOut32W411 k) = β (n1sOut32W411 k)) := by
  intro c p
  have hc_supp : c.SupportsBelow (411 - (411 - 383)) :=
    n1s_cRowSetup_supports uW hu_379 sh w hoff_sh
  obtain ⟨hvWrap, hevWrap⟩ := withCliffAlloc_valid_and_eval
    (M := 411) (rem := 411 - 379) (remIn := 411 - 383) (by decide) (by decide)
    c hc_supp body hvBody
  have hDisjOut := n1s_cRowSetup_disj_ex uW hu_201 sh w hoff_sh
  have hDisjInv := CliffDisjoint.inv hDisjOut
  refine ⟨hvWrap, fun β hβ ↦ ?_⟩
  obtain ⟨hcγ, hs1, hev1⟩ := hevWrap β hβ
  obtain ⟨hsB, hnonB⟩ := hBody (c.eval β) hcγ
  have hδ_non : ∀ u : Wire 411, ¬ (∃ k : Fin 32, u = n1sOut32W411 k) →
      body.evalBits (c.eval β) u = c.eval β u := fun u hu ↦ hnonB u (fun k hk ↦ hu ⟨k, hk⟩)
  have hNon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q :=
    fun q hq ↦ by
      rw [hev1, hDisjInv.eval_congr_nonMut hδ_non q (fun ⟨k, hk⟩ ↦ hq k hk)]
      exact congrFun (cliffInv_comp_eval c β) q
  refine ⟨hcγ, hs1.trans hsB, fun q hq ↦ (hNon q fun k ↦
      wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)).trans (hβ q hq), hNon,
    fun k ↦ by rw [hev1]; exact hDisjInv.eval_mut _ ⟨k, rfl⟩,
    fun k ↦ hDisjOut.eval_mut β ⟨k, rfl⟩⟩

private theorem n1s_core_inPlaceAdd_spec
    (off w : ℕ) (hw18 : w ≤ 18) (hcur : 383 + (w + 1) ≤ 411) (hacc : off + (w + 2) ≤ 32)
    (cin : Wire 411) (hcin : n1sValidCin cin) :
    let body := n1sMkInPlaceAdd off w hw18 hcur hacc cin hcin
    ValidCleanRem 411 (411 - 383) body ∧
      ∀ γ : BitAssignment 411, cleanRem 411 (411 - 383) γ →
        body.evalSign γ = 0 ∧
        (∀ u : Wire 411, (∀ k : Fin 32, u ≠ n1sOut32W411 k) → body.evalBits γ u = γ u) ∧
        ∀ A0 R0 P0 P1 : ℕ,
          bitsVal (fun k : Fin 32 ↦ γ (n1sOut32W411 k)) = P0 →
          bitsVal (fun j : Fin (w + 2) ↦ γ (n1sOut32W411 ⟨off + j.val, by omega⟩)) = A0 →
          bitsVal (fun j ↦ γ (n1sBLowF w hw18 j)) + (γ cin).val = R0 →
          A0 + R0 < 2 ^ (w + 2) →
          P0 + 2 ^ off * (A0 + R0) = P1 + 2 ^ off * A0 →
          bitsVal (fun k : Fin 32 ↦ body.evalBits γ (n1sOut32W411 k)) = P1 := by
  intro body
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := inPlaceAddMod1_spec (w + 1) 383 hcur
    (n1sBLowF w hw18) (n1sAccSlice off (w + 2) hacc) cin
    (n1s_accSlice_ne_bLowF off (w + 2) w hacc hw18)
    (n1s_accSlice_ne_validCin off (w + 2) hacc hcin) (n1s_bLowF_ne_validCin w hw18 hcin)
    (n1s_bLowF_inj w hw18) (n1s_accSlice_inj off (w + 2) hacc)
    (n1s_bLowF_lt w hw18) (n1s_accSlice_lt off (w + 2) hacc) (n1s_validCin_lt hcin)
  refine ⟨hvAdd, fun γ hcγ ↦ ?_⟩
  obtain ⟨_, hnonIn, hvalIn⟩ := hAdd γ hcγ
  refine ⟨hsAdd γ hcγ, fun u hu ↦ hnonIn u (fun j hj ↦ hu ⟨off + j.val, by omega⟩ hj),
    fun A0 R0 P0 P1 hP0 hsl₀ hR0 hlt hAlg ↦ ?_⟩
  let g₀ : Fin 32 → ZMod 2 := fun k ↦ γ (n1sOut32W411 k)
  let g₁ : Fin 32 → ZMod 2 := fun k ↦ body.evalBits γ (n1sOut32W411 k)
  have hsl₁ : bitsVal (fun j : Fin (w + 2) ↦ g₁ ⟨off + j.val, by omega⟩) = A0 + R0 := by
    change bitsVal (fun j : Fin (w + 2) ↦ body.evalBits γ (n1sAccSlice off (w + 2) hacc j)) = _
    rw [hvalIn, show (fun j : Fin (w + 2) ↦ γ (n1sAccSlice off (w + 2) hacc j)) =
      fun j : Fin (w + 2) ↦ g₀ ⟨off + j.val, by omega⟩ from rfl,
      hsl₀, Nat.add_assoc, hR0, Nat.mod_eq_of_lt hlt]
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := w + 2) (k := off) hacc g₀ g₁
    fun k hk ↦ hnonIn (n1sOut32W411 k) fun j hj ↦ by
      have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega
  have hsl₀' : bitsVal (fun j : Fin (w + 2) ↦ g₀ ⟨off + j.val, by omega⟩) = A0 := hsl₀
  rw [hsl₀', hsl₁, hP0] at hlin
  exact Nat.add_right_cancel (hlin.trans hAlg)

private theorem n1s_withCliffAlloc_inPlaceAdd_spec
    (t : Norm1sTier) (off sh w : ℕ)
    (hw18 : w ≤ 18) (hoff_sh : sh + w ≤ 18) (hcur : 383 + (w + 1) ≤ 411) (hacc : off + (w + 2) ≤ 32)
    (uW cin : Wire 411) (hu_201 : uW.val < 201) (hu_379 : uW.val < 379) (hcin : n1sValidCin cin)
    (mPre mPost : ℕ) (p : TempPhaseProg 411)
    (hp : p = withCliffAlloc (n1sCRowSetup uW hu_379 sh w hoff_sh)
      (n1sMkInPlaceAdd off w hw18 hcur hacc cin hcin))
    (hStep : ∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
      let mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
      let uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
      let γ := (n1sCRowSetup uW hu_379 sh w hoff_sh).eval β
      bitsVal (fun k : Fin 32 ↦ β (n1sOut32W411 k)) = norm1sHwRowsAux t.dCut mS uK mPre →
      ∃ A0 R0 : ℕ,
        bitsVal (fun j : Fin (w + 2) ↦ β (n1sOut32W411 ⟨off + j.val, by omega⟩)) = A0 ∧
        bitsVal (fun j ↦ γ (n1sBLowF w hw18 j)) + (γ cin).val = R0 ∧
        A0 + R0 < 2 ^ (w + 2) ∧
        norm1sHwRowsAux t.dCut mS uK mPre + 2 ^ off * (A0 + R0) =
          norm1sHwRowsAux t.dCut mS uK mPost + 2 ^ off * A0) :
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t mPre β → n1sBoothInv t mPost (p.evalBits β))) := by
  rw [hp]
  obtain ⟨hvCore, hCore⟩ := n1s_core_inPlaceAdd_spec off w hw18 hcur hacc cin hcin
  obtain ⟨hvWrap, hWrap⟩ := n1s_withCliffAlloc_row_lift uW hu_201 hu_379 sh w hoff_sh _ hvCore
    fun γ hcγ ↦ ⟨(hCore γ hcγ).1, (hCore γ hcγ).2.1⟩
  refine ⟨hvWrap, fun β hβ ↦ ?_⟩
  obtain ⟨hcγ, hs, hClOut, hNon, hOutEq, hγ_out⟩ := hWrap β hβ
  refine ⟨hs, hClOut, hNon, fun hInvPre ↦ ?_⟩
  obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t hNon
  unfold n1sBoothInv at hInvPre ⊢
  rw [hmEq, huEq, show (fun k : Fin 32 ↦ (withCliffAlloc _ _).evalBits β (n1sOut32W411 k)) =
    fun k : Fin 32 ↦ (n1sMkInPlaceAdd off w hw18 hcur hacc cin hcin).evalBits
      ((n1sCRowSetup uW hu_379 sh w hoff_sh).eval β) (n1sOut32W411 k) from funext hOutEq]
  obtain ⟨A0, R0, hsl₀, hR0, hlt, hAlg⟩ := hStep β hβ hInvPre
  exact (hCore _ hcγ).2.2 A0 R0 _ _
    (by rw [show (fun k : Fin 32 ↦ (n1sCRowSetup uW hu_379 sh w hoff_sh).eval β (n1sOut32W411 k)) =
      fun k ↦ β (n1sOut32W411 k) from funext hγ_out]; exact hInvPre)
    (by rw [show (fun j : Fin (w + 2) ↦ (n1sCRowSetup uW hu_379 sh w hoff_sh).eval β
      (n1sOut32W411 ⟨off + j.val, by omega⟩)) = fun j ↦ β (n1sOut32W411 ⟨off + j.val, by omega⟩)
      from funext fun j ↦ hγ_out _]; exact hsl₀) hR0 hlt hAlg

theorem w14_baseD18_rows_eq (t : Norm1sTier) (hd18 : t.dCut = 18)
    (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 379) β) :
    have hb := n1s_tier_bounds t
    let u0 := n1sUKW411 t ⟨0, by omega⟩
    let u1 := n1sUKW411 t ⟨1, by omega⟩
    let γ := (n1sCRowSetup u1 (lt_trans (n1s_uKW411_range t _).2 (by decide))
      17 1 (by decide)).eval β
    let mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
    let uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
    bitsVal (fun j ↦ γ (n1sBLowR 1 (by decide) j)) =
      norm1sRowVal t.dCut 1 mS (uK.testBit 1) ∧
    bitsVal (fun j ↦ γ (n1sBLowF 1 (by decide) j)) =
      norm1sRowVal t.dCut 1 mS (uK.testBit 1) ∧
    (γ u0).val = norm1sRowVal t.dCut 0 mS (uK.testBit 0) := by
  dsimp only
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  have hu0_90 : u0.val < 90 := (n1s_uKW411_range t _).2
  have hu1_201 : u1.val < 201 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  obtain ⟨hr1R, hr1F⟩ := n1s_bLowR_val_eq_row 18 1 (by
    decide) (by decide) (by decide) u1 hu1_201 β hβ
  have hb1 := bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨1, by omega⟩
  have hγ_u0 : (n1sCRowSetup u1 (lt_trans (n1s_uKW411_range t _).2 (by decide))
      17 1 (by decide)).eval β u0 = β u0 :=
    (n1s_cRowSetup_eval u1 hu1_201 17 1 (by decide) β hβ).2.2.2.2.2.2.2 u0
      (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))
      (wire_ne_of_lt (by dsimp [n1sCinW411]; omega))
      (wire_ne_of_lt (by dsimp [n1sInvW411]; omega))
  refine ⟨by rwa [hd18, hb1], by rwa [hd18, hb1], ?_⟩
  rw [hγ_u0, hd18, bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨0, by omega⟩]
  unfold norm1sRowVal
  rw [ite_eq_left (by decide : 0 < 18), ite_eq_left (rfl : 18 - 0 = 18)]
  change (β u0).val = if decide (β u0 = 1) = true then 1 else 0
  rcases bit_cases (β u0) with hb0 | hb0
  · rw [hb0]; decide
  · rw [hb0]; decide

theorem n1s_baseFwdD18_spec (t : Norm1sTier) (hd18 : t.dCut = 18) :
    let p := n1sBaseFwdD18 t
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t 0 β → n1sBoothInv t 2 (p.evalBits β))) := by
  intro p
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  have hu1_90 : u1.val < 90 := (n1s_uKW411_range t _).2
  refine n1s_withCliffAlloc_inPlaceAdd_spec t 0 17 1 (by decide) (by decide) (by decide)
    (by decide) u1 u0 (lt_trans hu1_90 (by decide)) (lt_trans hu1_90 (by decide))
    (Or.inl (n1s_uKW411_range t _).2) 0 2 p rfl fun β hβ hInv0 ↦ ?_
  obtain ⟨_, hrow1, hrow0⟩ := w14_baseD18_rows_eq t hd18 β hβ
  have hbnd2 := (n1s_rowsAux_bounds t (bitsVal fun i ↦ β (n1sMantW411 i))
    (bitsVal fun k ↦ β (n1sUKW411 t k)) (bitsVal_lt_two_pow _) 2 (by omega)).1 hd18 rfl
  have hsl₀ : bitsVal (fun j : Fin 3 ↦ β (n1sOut32W411 ⟨0 + j.val, by omega⟩)) = 0 := by
    rw [n1s_out32_slice_div (by decide) hInv0 (by dsimp [norm1sHwRowsAux]; decide)]
    simp [norm1sHwRowsAux]
  exact ⟨0, _, hsl₀, by rw [hrow1, hrow0], by dsimp [norm1sHwRowsAux] at hbnd2; omega,
    by dsimp [norm1sHwRowsAux]; omega⟩

theorem n1s_lowRowFwd_spec (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) :
    let p := n1sLowRowFwd t m hm1 hmd hw2
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t m β → n1sBoothInv t (m + 1) (p.evalBits β))) := by
  intro p
  have hb := n1s_tier_bounds t
  set sh := t.dCut - m
  set w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  have hoff_w : sh + w ≤ 18 := by dsimp [w, sh]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  have hu_201 : uW.val < 201 := lt_trans hu_90 (by decide)
  refine n1s_withCliffAlloc_inPlaceAdd_spec t 0 sh w hw18 hoff_w (by dsimp [w]; omega)
    (by dsimp [w]; omega) uW n1sZPad2W411 hu_201 (lt_trans hu_90 (by decide)) n1s_zPad2_validCin
    m (m + 1) p rfl fun β hβ hInvm ↦ ?_
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  let γ := (n1sCRowSetup uW (lt_trans hu_90 (by decide)) sh w hoff_w).eval β
  have hγ_z2 := (n1s_cRowSetup_eval uW hu_201 sh w hoff_w β hβ).2.2.2.1
  have hrow : bitsVal (fun j ↦ γ (n1sBLowF w hw18 j)) =
      norm1sRowVal t.dCut m mS (uK.testBit m) := by
    rw [bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨m, lt_trans hmd (by omega)⟩]
    exact (n1s_bLowR_val_eq_row t.dCut m hmd (by omega) (by dsimp [w, sh] at hw2; omega)
      uW hu_201 β hβ).2
  have hbnd_next := (n1s_rowsAux_bounds t mS uK (bitsVal_lt_two_pow _) (m + 1) (by omega)).2.2.1
    (by split_ifs <;> omega) (by omega)
  rw [show (18 - t.dCut) + (m + 1) + 1 = w + 2 from by dsimp [w, sh]; omega] at hbnd_next
  have hsl₀ : bitsVal (fun j : Fin (w + 2) ↦ β (n1sOut32W411 ⟨0 + j.val, by omega⟩)) =
      norm1sHwRowsAux t.dCut mS uK m :=
    (n1s_out32_slice_div (by dsimp [w]; omega) hInvm (by
      rw [Nat.pow_zero, Nat.div_one]; dsimp [norm1sHwRowsAux] at hbnd_next; omega)).trans
      (Nat.div_one _)
  exact ⟨norm1sHwRowsAux t.dCut mS uK m, norm1sRowVal t.dCut m mS (uK.testBit m),
    hsl₀, by rw [hrow, hγ_z2, ZMod.val_zero, add_zero],
    by dsimp [norm1sHwRowsAux] at hbnd_next; omega, by dsimp [norm1sHwRowsAux]; omega⟩

theorem w14_highRow_step_facts (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut)
    (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 379) β) :
    have hb := n1s_tier_bounds t
    let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
    let γ := (n1sCRowSetup uW (lt_trans (n1s_uKW411_range t _).2 (by decide))
      0 18 (by decide)).eval β
    let mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
    let uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
    let row0 := if decide (β uW = 1) = true then 2 ^ 18 + mS else 2 ^ 18 - mS
    let Pm := norm1sHwRowsAux t.dCut mS uK (t.dCut + off)
    bitsVal (fun j ↦ γ (n1sBLowR 18 le_rfl j)) + (γ n1sCinW411).val = row0 ∧
    bitsVal (fun j ↦ γ (n1sBLowF 18 le_rfl j)) + (γ n1sCinW411).val = row0 ∧
    Pm / 2 ^ off < 2 ^ 19 ∧ row0 < 2 ^ 19 ∧
    norm1sHwRowsAux t.dCut mS uK (t.dCut + off + 1) = Pm + row0 * 2 ^ off := by
  dsimp only
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  have hu_201 : uW.val < 201 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hmS : mS < 2 ^ 18 := bitsVal_lt_two_pow _
  obtain ⟨hBR, hBF, hRowEq⟩ := n1s_bHigh_val_eq_row t.dCut off uW hu_201 β hβ
  have hrow0_lt : (if decide (β uW = 1) = true then 2 ^ 18 + mS else 2 ^ 18 - mS) < 2 ^ 19 := by
    have h218 : (2 ^ 18 : ℕ) = 262144 := by decide
    have h219 : (2 ^ 19 : ℕ) = 524288 := by decide
    by_cases hb1 : decide (β uW = 1) = true
    · simp [hb1]; omega
    · simp [hb1]; omega
  have hbnd_m := (n1s_rowsAux_bounds t mS uK hmS (t.dCut + off) (by omega)).2.2.2 (by omega)
  rw [show t.dCut + off - t.dCut = off from by omega] at hbnd_m
  have hdiv_lt : norm1sHwRowsAux t.dCut mS uK (t.dCut + off) / 2 ^ off < 2 ^ 19 := by
    apply Nat.div_lt_of_lt_mul
    have hp : 2 ^ (off + 19) = 2 ^ off * 2 ^ 19 := by ring
    have := Nat.two_pow_pos off
    omega
  refine ⟨hBR, hBF, hdiv_lt, hrow0_lt, ?_⟩
  dsimp [norm1sHwRowsAux]
  rw [bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨t.dCut + off, by omega⟩, hRowEq]
  rfl

theorem n1s_highRowFwd_spec (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut) :
    let p := n1sHighRowFwd t off hoff
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t (t.dCut + off) β → n1sBoothInv t (t.dCut + off + 1) (p.evalBits β))) := by
  intro p
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  refine n1s_withCliffAlloc_inPlaceAdd_spec t off 0 18 le_rfl (by decide) (by decide) (by omega)
    uW n1sCinW411 (lt_trans hu_90 (by decide)) (lt_trans hu_90 (by decide)) n1s_cinW_validCin
    (t.dCut + off) (t.dCut + off + 1) p rfl fun β hβ hInvm ↦ ?_
  obtain ⟨_, hBF, hdiv_lt, hrow0_lt, hPnext⟩ := w14_highRow_step_facts t off hoff β hβ
  have h220 : (2 ^ 19 : ℕ) + 2 ^ 19 = 2 ^ 20 := by decide
  have hsl₀ := n1s_out32_slice_div (by omega) hInvm
    (lt_trans hdiv_lt (by decide : 2 ^ 19 < 2 ^ 20))
  exact ⟨_, _, hsl₀, hBF, by omega, by rw [hPnext]; ring⟩

theorem n1s_bLowR18_clean_val (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 379) β) :
    bitsVal (fun j ↦ β (n1sBLowR 18 le_rfl j)) = bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) ∧
    bitsVal (fun j ↦ β (n1sBLowF 18 le_rfl j)) = bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) := by
  have hR : bitsVal (fun j ↦ β (n1sBLowR 18 le_rfl j)) =
      bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) := by
    rw [bitsVal_castSucc_split]
    have hlo : (fun j : Fin 18 ↦ β (n1sBLowR 18 le_rfl j.castSucc)) =
        fun i : Fin 18 ↦ β (n1sMantW411 i) :=
      funext fun j ↦ by
        simp only [n1sBLowR, Fin.snoc_castSucc]
        exact congrArg β (congrArg n1sMantW411 (Fin.ext (by dsimp; omega)))
    have hhi : β (n1sBLowR 18 le_rfl (Fin.last 18)) = 0 := by
      simp only [n1sBLowR, Fin.snoc_last]
      exact hβ n1sInvW411 (by decide)
    rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero]
  exact ⟨hR, (w14_bLowF_bitsVal_eq 18 le_rfl β (hβ n1sZPad1W411 (by decide))).trans hR⟩

theorem n1s_topRowFwd_spec (t : Norm1sTier) :
    let p := n1sTopRowFwd t
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t t.kBits β → n1sBoothDoneInv t (p.evalBits β))) := by
  intro p
  have hb := n1s_tier_bounds t
  set topOff := t.kBits - t.dCut
  rw [show p = n1sMkInPlaceAdd topOff 18 le_rfl (by decide) (by dsimp [topOff]; omega)
    n1sZPad2W411 n1s_zPad2_validCin from rfl]
  obtain ⟨hvAdd, hCore⟩ := n1s_core_inPlaceAdd_spec topOff 18 le_rfl (by decide)
    (by dsimp [topOff]; omega) n1sZPad2W411 n1s_zPad2_validCin
  refine ⟨validCleanRem_mono (by decide : 411 - 383 ≤ 411 - 379) hvAdd, fun β hβ ↦ ?_⟩
  obtain ⟨hsAdd, hNon, hVal⟩ := hCore β (cleanRem_anti (by decide) hβ)
  refine ⟨hsAdd, fun q hq ↦ (hNon q fun k ↦
      wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)).trans (hβ q hq), hNon, fun hInvK ↦ ?_⟩
  obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t hNon
  unfold n1sBoothInv at hInvK
  unfold n1sBoothDoneInv
  rw [hmEq, huEq]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hmS : mS < 2 ^ 18 := bitsVal_lt_two_pow _
  have hdiv_lt := (n1s_hwProd_lt_two_pow_wAcc t mS uK hmS).1
  exact hVal _ mS _ _ hInvK
    (n1s_out32_slice_div (by dsimp [topOff]; omega) hInvK
      (lt_trans hdiv_lt (by decide : 2 ^ 19 < 2 ^ 20)))
    (by rw [(n1s_bLowR18_clean_val β hβ).2, hβ n1sZPad2W411 (by decide), ZMod.val_zero, add_zero])
    (lt_trans (Nat.add_lt_add hdiv_lt hmS) (by decide))
    (by unfold norm1sHwProd; ring)

private theorem n1s_seq_clean_out32 {p₁ p₂ : TempPhaseProg 411}
    {Q₁ Q₂ R : BitAssignment 411 → Prop}
    (h1 : ValidCleanRem 411 (411 - 379) p₁ ∧
      ∀ β, cleanRem 411 (411 - 379) β → p₁.evalSign β = 0 ∧
        cleanRem 411 (411 - 379) (p₁.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p₁.evalBits β q = β q) ∧
        Q₁ β)
    (h2 : ValidCleanRem 411 (411 - 379) p₂ ∧
      ∀ β₁, cleanRem 411 (411 - 379) β₁ → p₂.evalSign β₁ = 0 ∧
        cleanRem 411 (411 - 379) (p₂.evalBits β₁) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p₂.evalBits β₁ q = β₁ q) ∧
        Q₂ β₁)
    (hImp : ∀ β, Q₁ β → Q₂ (p₁.evalBits β) → R β) :
    ValidCleanRem 411 (411 - 379) (p₁.seq p₂) ∧
      ∀ β, cleanRem 411 (411 - 379) β → (p₁.seq p₂).evalSign β = 0 ∧
        cleanRem 411 (411 - 379) ((p₁.seq p₂).evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → (p₁.seq p₂).evalBits β q = β q) ∧
        R β := by
  obtain ⟨hv1, hEv1⟩ := h1
  obtain ⟨hv2, hEv2⟩ := h2
  refine ⟨⟨411 - 379, by decide, hv1, hv2, fun β hβ ↦ (hEv1 β hβ).2.1⟩, fun β hβ ↦ ?_⟩
  obtain ⟨hs1, hcl1, hnon1, hq1⟩ := hEv1 β hβ
  obtain ⟨hs2, hcl2, hnon2, hq2⟩ := hEv2 (p₁.evalBits β) hcl1
  refine ⟨?_, hcl2, fun q hq ↦ (hnon2 q hq).trans (hnon1 q hq), hImp β hq1 hq2⟩
  change p₁.evalSign β + p₂.evalSign (p₁.evalBits β) = 0
  rw [hs1, zero_add, hs2]

theorem n1s_boothPrefixFwd_spec (t : Norm1sTier) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      let p := n1sBoothPrefixFwd t m hm
      ValidCleanRem 411 (411 - 379) p ∧
        (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
          p.evalSign β = 0 ∧
          cleanRem 411 (411 - 379) (p.evalBits β) ∧
          (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
          ((t.dCut = 18 → m ≠ 1) → n1sBoothInv t 0 β → n1sBoothInv t m (p.evalBits β)))
  | 0, _ => ⟨trivial, fun _ hβ ↦ ⟨rfl, hβ, fun _ _ ↦ rfl, fun _ h0 ↦ h0⟩⟩
  | 1, hm => by
      dsimp only [n1sBoothPrefixFwd]
      by_cases hd18 : t.dCut = 18
      · rw [dite_eq_left hd18]
        exact ⟨trivial, fun _ hβ ↦ ⟨rfl, hβ, fun _ _ ↦ rfl, fun hne _ ↦ absurd rfl (hne hd18)⟩⟩
      · rw [dite_eq_right hd18]
        have hb := n1s_tier_bounds t
        let u0 := n1sUKW411 t ⟨0, by omega⟩
        let c0 := n1sCRow0Full u0 (lt_trans (n1s_uKW411_range t _).2 (by decide))
          t.dCut ⟨hb.2.2.1, by omega⟩
        refine ⟨trivial, fun β hβ ↦ ?_⟩
        have hsupp : c0.SupportsBelow 379 :=
          ⟨⟨by have := (n1s_uKW411_range t ⟨0, by omega⟩).2; omega,
            by dsimp [n1sOut32W411]; omega⟩,
           n1s_cRow0Lt18_supports u0 (lt_trans (n1s_uKW411_range t _).2 (by decide))
             t.dCut (18 - t.dCut) (by omega)⟩
        have hcl' : cleanRem 411 (411 - 379) (c0.eval β) := fun w hw ↦ by
          rw [c0.eval_outside hsupp β w (by omega)]; exact hβ w hw
        obtain ⟨hOut, _⟩ := n1s_cRow0Lt18_eval u0 (lt_trans (n1s_uKW411_range t _).2 (by decide))
          t.dCut (18 - t.dCut) (by omega)
          ((CliffProg.cnot u0 (n1sOut32W411 ⟨18 - t.dCut, by omega⟩) _).eval β)
        have hNon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → c0.eval β q = β q :=
          fun q hq ↦ (hOut q (fun j ↦ hq ⟨j.val, by omega⟩)).trans
            (Function.update_of_ne (hq ⟨18 - t.dCut, by omega⟩) _ _)
        refine ⟨rfl, hcl', hNon, fun _ hInv0 ↦ ?_⟩
        have hout0 : ∀ j : Fin 32, β (n1sOut32W411 j) = 0 := by
          have hz : bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) = bitsVal (fun _ : Fin 32 ↦
            (0 : ZMod 2)) := by
            simpa [n1sBoothInv, norm1sHwRowsAux, bitsVal] using hInv0
          exact congrFun (bitsVal_injective hz)
        obtain ⟨_, _, hVal0⟩ := n1s_cRow0Full_spec u0 (lt_trans (n1s_uKW411_range t _).2 (by
          decide))
          t.dCut ⟨hb.2.2.1, by omega⟩ β hout0
        obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t hNon
        unfold n1sBoothInv
        dsimp only [TempPhaseProg.evalBits]
        rw [hmEq, huEq, hVal0,
          ← bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨0, by omega⟩]
        simp [norm1sHwRowsAux]
  | 2, hm => by
      dsimp only [n1sBoothPrefixFwd]
      by_cases hd18 : t.dCut = 18
      · rw [dite_eq_left hd18]
        obtain ⟨hv, hEv⟩ := n1s_baseFwdD18_spec t hd18
        exact ⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
          fun _ h0 ↦ (hEv β hβ).2.2.2 h0⟩⟩
      · rw [dite_eq_right hd18]
        have hb := n1s_tier_bounds t
        exact n1s_seq_clean_out32 (n1s_boothPrefixFwd_spec t 1 (by omega))
          (n1s_lowRowFwd_spec t 1 le_rfl (by omega) (by omega))
          (fun _ h1 h2 _ h0 ↦ h2 (h1 (fun h ↦ absurd h hd18) h0))
  | m + 3, hm => by
      dsimp only [n1sBoothPrefixFwd]
      have hb := n1s_tier_bounds t
      have hPrev := n1s_boothPrefixFwd_spec t (m + 2) (by omega)
      by_cases hlow : m + 2 < t.dCut
      · rw [dite_eq_left hlow]
        exact n1s_seq_clean_out32 hPrev (n1s_lowRowFwd_spec t (m + 2) (by omega) hlow (by omega))
          (fun _ h1 h2 _ h0 ↦ h2 (h1 (fun _ ↦ by omega) h0))
      · rw [dite_eq_right hlow]
        refine n1s_seq_clean_out32 hPrev (n1s_highRowFwd_spec t ((m + 2) - t.dCut) (by omega))
          (fun β h1 h2 _ h0 ↦ ?_)
        have h1' : n1sBoothInv t (t.dCut + ((m + 2) - t.dCut))
            ((n1sBoothPrefixFwd t (m + 2) (by omega)).evalBits β) := by
          rw [show t.dCut + ((m + 2) - t.dCut) = m + 2 from by omega]
          exact h1 (fun _ ↦ by omega) h0
        have h2' := h2 h1'
        rwa [show t.dCut + ((m + 2) - t.dCut) + 1 = m + 3 from by omega] at h2'

theorem n1s_boothFwd411_spec (t : Norm1sTier) :
    let p := n1sBoothFwd411 t
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        ((∀ k : Fin 32, β (n1sOut32W411 k) = 0) → n1sBoothDoneInv t (p.evalBits β))) := by
  dsimp only [n1sBoothFwd411]; have hb := n1s_tier_bounds t
  refine n1s_seq_clean_out32 (n1s_boothPrefixFwd_spec t t.kBits le_rfl) (n1s_topRowFwd_spec t)
    (fun β h1 h2 hout0 ↦ h2 (h1 (fun _ ↦ by omega) ?_))
  unfold n1sBoothInv; simp [hout0, norm1sHwRowsAux, bitsVal]

private theorem n1s_core_cleanMsbSub_spec
    (off w : ℕ) (hw18 : w ≤ 18) (hcur : 383 + w + 1 ≤ 411)
    (hacc : off + (w + 1) ≤ 32) (hacc2 : off + (w + 2) ≤ 32)
    (msbIdx : Fin 32) (hmsb_val : msbIdx.val = off + (w + 1))
    (cin : Wire 411) (hcin : n1sValidCin cin) :
    let body := n1sMkCleanMsbSub off w hw18 hcur hacc msbIdx cin hcin
    ValidCleanRem 411 (411 - 383) body ∧
      ∀ γ : BitAssignment 411, cleanRem 411 (411 - 383) γ →
        body.evalSign γ = 0 ∧
        (∀ u : Wire 411, (∀ k : Fin 32, u ≠ n1sOut32W411 k) → body.evalBits γ u = γ u) ∧
        ∀ A0 R0 PPost PPre : ℕ,
          A0 < 2 ^ (w + 1) →
          bitsVal (fun k : Fin 32 ↦ γ (n1sOut32W411 k)) = PPost →
          bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ cin).val = R0 →
          bitsVal (fun j : Fin (w + 2) ↦ γ (n1sOut32W411 ⟨off + j.val, by omega⟩)) = A0 + R0 →
          PPost + 2 ^ off * A0 = PPre + 2 ^ off * (A0 + R0) →
          bitsVal (fun k : Fin 32 ↦ body.evalBits γ (n1sOut32W411 k)) = PPre ∧
          bitsVal (fun j ↦ γ (n1sAccSlice off (w + 1) hacc j)) +
            2 ^ (w + 1) * (γ (n1sOut32W411 msbIdx)).val =
            A0 + bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ cin).val := by
  intro body
  have ham : ∀ j, n1sAccSlice off (w + 1) hacc j ≠ n1sOut32W411 msbIdx :=
    fun j ↦ wire_ne_of_lt (by simp only [n1sAccSlice, n1sOut32W411]; omega)
  obtain ⟨hvSub, hUncond, hSum⟩ := ctxCleanMsbSub_spec w 383 hcur
    (n1sBLowR w hw18) (n1sAccSlice off (w + 1) hacc) (n1sOut32W411 msbIdx) cin
    (n1s_accSlice_ne_bLowR off (w + 1) w hacc hw18)
    (n1s_accSlice_ne_validCin off (w + 1) hacc hcin) (n1s_bLowR_ne_validCin w hw18 hcin)
    ham (fun j ↦ n1s_bLowR_ne_out32 w hw18 j msbIdx) (n1s_out32_ne_validCin msbIdx hcin)
    (n1s_bLowR_inj w hw18) (n1s_accSlice_inj off (w + 1) hacc)
    (n1s_bLowR_lt w hw18) (n1s_accSlice_lt off (w + 1) hacc)
    (by dsimp [n1sOut32W411]; omega) (n1s_validCin_lt hcin)
  refine ⟨hvSub, fun γ hcγ ↦ ?_⟩
  obtain ⟨hsSub, _, hnonIn⟩ := hUncond γ hcγ
  refine ⟨hsSub,
    fun u hu ↦ hnonIn u (fun j hj ↦ hu ⟨off + j.val, by omega⟩ hj) (fun hm ↦ hu msbIdx hm),
    fun A0 R0 PPost PPre hA0_lt hPPost hR0 hsl₁_full hAlg ↦ ?_⟩
  let aOrig : Fin (w + 1) → ZMod 2 := fun j ↦ boolToZMod2 (A0.testBit j.val)
  have haOrig_val : bitsVal aOrig = A0 := n1s_bitsVal_of_nat (w + 1) A0 hA0_lt
  let g₁ : Fin 32 → ZMod 2 := fun k ↦ γ (n1sOut32W411 k)
  let g₂ : Fin 32 → ZMod 2 := fun k ↦ body.evalBits γ (n1sOut32W411 k)
  have hmsb_eq : msbIdx = ⟨off + (Fin.last (w + 1)).val, by omega⟩ :=
    Fin.ext (by dsimp [Fin.last]; omega)
  have hWit : bitsVal (fun j ↦ γ (n1sAccSlice off (w + 1) hacc j)) +
      2 ^ (w + 1) * (γ (n1sOut32W411 msbIdx)).val =
      A0 + bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ cin).val := by
    have hsp := bitsVal_castSucc_split (fun j : Fin (w + 2) ↦ g₁ ⟨off + j.val, by omega⟩)
    have hacc_eq : (fun j : Fin (w + 1) ↦ γ (n1sAccSlice off (w + 1) hacc j)) =
        fun j : Fin (w + 1) ↦ g₁ ⟨off + j.castSucc.val, by omega⟩ := funext fun _ ↦ rfl
    have hmsb_g : γ (n1sOut32W411 msbIdx) = g₁ ⟨off + (Fin.last (w + 1)).val, by omega⟩ :=
      congrArg (fun k ↦ γ (n1sOut32W411 k)) hmsb_eq
    rw [hacc_eq, hmsb_g, ← hsp, hsl₁_full, Nat.add_assoc, hR0]
  obtain ⟨_, hRestAcc, hRestMsb⟩ := hSum γ aOrig hcγ (by rwa [haOrig_val])
  have hsl₂ : bitsVal (fun j : Fin (w + 2) ↦ g₂ ⟨off + j.val, by omega⟩) = A0 := by
    rw [bitsVal_castSucc_split,
      show (fun j : Fin (w + 1) ↦ g₂ ⟨off + j.castSucc.val, by omega⟩) = aOrig
        from funext hRestAcc,
      show g₂ ⟨off + (Fin.last (w + 1)).val, by omega⟩ = 0 from by
        rw [hmsb_eq.symm]; exact hRestMsb,
      ZMod.val_zero, mul_zero, add_zero, haOrig_val]
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := w + 2) (k := off) hacc2 g₁ g₂
    fun k hk ↦ hnonIn (n1sOut32W411 k)
      (fun j hj ↦ by have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega)
      (fun hm ↦ by have hv := congrArg Fin.val (n1s_out32W411_inj hm); omega)
  have hsl₁' : bitsVal (fun j : Fin (w + 2) ↦ g₁ ⟨off + j.val, by omega⟩) = A0 + R0 := hsl₁_full
  rw [hsl₁', hsl₂, hPPost] at hlin
  exact ⟨Nat.add_right_cancel (hlin.trans hAlg), hWit⟩

private theorem n1s_withCliffAlloc_cleanMsbSub_spec
    (t : Norm1sTier) (off sh w : ℕ)
    (hw18 : w ≤ 18) (hoff_sh : sh + w ≤ 18) (hcur : 383 + w + 1 ≤ 411)
    (hacc : off + (w + 1) ≤ 32) (hacc2 : off + (w + 2) ≤ 32)
    (msbIdx : Fin 32) (hmsb_val : msbIdx.val = off + (w + 1))
    (uW cin : Wire 411) (hu_201 : uW.val < 201) (hu_379 : uW.val < 379) (hcin : n1sValidCin cin)
    (mPost mPre : ℕ) (p : TempPhaseProg 411)
    (hp : p = withCliffAlloc (n1sCRowSetup uW hu_379 sh w hoff_sh)
      (n1sMkCleanMsbSub off w hw18 hcur hacc msbIdx cin hcin))
    (hStep : ∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
      let mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
      let uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
      let γ := (n1sCRowSetup uW hu_379 sh w hoff_sh).eval β
      bitsVal (fun k : Fin 32 ↦ β (n1sOut32W411 k)) = norm1sHwRowsAux t.dCut mS uK mPost →
      ∃ A0 R0 : ℕ, A0 < 2 ^ (w + 1) ∧
        bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ cin).val = R0 ∧
        bitsVal (fun j : Fin (w + 2) ↦ β (n1sOut32W411 ⟨off + j.val, by omega⟩)) = A0 + R0 ∧
        norm1sHwRowsAux t.dCut mS uK mPost + 2 ^ off * A0 =
          norm1sHwRowsAux t.dCut mS uK mPre + 2 ^ off * (A0 + R0)) :
    let c := n1sCRowSetup uW hu_379 sh w hoff_sh
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t mPost β →
          n1sBoothInv t mPre (p.evalBits β) ∧
          ∃ A₀ : ℕ, A₀ < 2 ^ (w + 1) ∧
            bitsVal (fun j ↦ c.eval β (n1sAccSlice off (w + 1) hacc j)) +
              2 ^ (w + 1) * (c.eval β (n1sOut32W411 msbIdx)).val =
              A₀ + bitsVal (fun j ↦ c.eval β (n1sBLowR w hw18 j)) + (c.eval β cin).val)) := by
  intro c
  rw [hp]
  obtain ⟨hvCore, hCore⟩ := n1s_core_cleanMsbSub_spec off w hw18 hcur hacc hacc2 msbIdx hmsb_val
    cin hcin
  obtain ⟨hvWrap, hWrap⟩ := n1s_withCliffAlloc_row_lift uW hu_201 hu_379 sh w hoff_sh _ hvCore
    fun γ hcγ ↦ ⟨(hCore γ hcγ).1, (hCore γ hcγ).2.1⟩
  refine ⟨hvWrap, fun β hβ ↦ ?_⟩
  obtain ⟨hcγ, hs, hClOut, hNon, hOutEq, hγ_out⟩ := hWrap β hβ
  refine ⟨hs, hClOut, hNon, fun hInvPost ↦ ?_⟩
  obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t hNon
  unfold n1sBoothInv at hInvPost ⊢
  rw [hmEq, huEq, show (fun k : Fin 32 ↦ (withCliffAlloc c _).evalBits β (n1sOut32W411 k)) =
    fun k : Fin 32 ↦ (n1sMkCleanMsbSub off w hw18 hcur hacc msbIdx cin hcin).evalBits
      (c.eval β) (n1sOut32W411 k) from funext hOutEq]
  obtain ⟨A0, R0, hA0_lt, hR0, hsl₁_full, hAlg⟩ := hStep β hβ hInvPost
  obtain ⟨hPre, hWit⟩ := (hCore (c.eval β) hcγ).2.2 A0 R0 _ _ hA0_lt
    (by rw [show (fun k : Fin 32 ↦ c.eval β (n1sOut32W411 k)) = fun k ↦ β (n1sOut32W411 k)
      from funext hγ_out]; exact hInvPost) hR0
    (by
      rw [show (fun j : Fin (w + 2) ↦ c.eval β (n1sOut32W411 ⟨off + j.val, by omega⟩)) =
        fun j ↦ β (n1sOut32W411 ⟨off + j.val, by omega⟩) from funext fun _ ↦ hγ_out _]
      exact hsl₁_full)
    hAlg
  exact ⟨hPre, A0, hA0_lt, hWit⟩

private theorem n1s_mkDCleanMsbSub_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 411 n) (off w : ℕ) (hw18 : w ≤ 18)
    (hcur : 383 + w + 1 ≤ 411) (hacc : off + (w + 1) ≤ 32)
    (msbIdx : Fin 32) (hmsb_val : msbIdx.val = off + (w + 1))
    (cin : Wire 411) (hcin : n1sValidCin cin)
    (rem : ℕ) (hrem_le : rem ≤ 411) (hrem_cur : 411 - 383 ≤ rem)
    (Inv : BitAssignment 411 → Prop)
    (hWit : ∀ γ, cleanRem 411 rem γ → Inv γ →
      ∃ A₀ : ℕ, A₀ < 2 ^ (w + 1) ∧
        bitsVal (fun j ↦ γ (n1sAccSlice off (w + 1) hacc j)) +
          2 ^ (w + 1) * (γ (n1sOut32W411 msbIdx)).val =
          A₀ + bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ cin).val) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem_le Inv)
      (n1sMkDCleanMsbSub v rComb off w hw18 (by omega) hacc msbIdx cin hcin)
      ((((n1sMkCleanMsbSub off w hw18 hcur hacc msbIdx cin hcin).onRegister
        rComb).toToffCircuit).eval) :=
  dCleanMsbSub_realizes_static v rComb w 383 hcur
    (n1sBLowR w hw18) (n1sAccSlice off (w + 1) hacc) (n1sOut32W411 msbIdx) cin
    (n1s_accSlice_ne_bLowR off (w + 1) w hacc hw18)
    (n1s_accSlice_ne_validCin off (w + 1) hacc hcin) (n1s_bLowR_ne_validCin w hw18 hcin)
    (fun j ↦ wire_ne_of_lt (by simp only [n1sAccSlice, n1sOut32W411]; omega))
    (fun j ↦ n1s_bLowR_ne_out32 w hw18 j msbIdx) (n1s_out32_ne_validCin msbIdx hcin)
    (n1s_bLowR_inj w hw18) (n1s_accSlice_inj off (w + 1) hacc)
    (n1s_bLowR_lt w hw18) (n1s_accSlice_lt off (w + 1) hacc)
    (by dsimp [n1sOut32W411]; omega) (n1s_validCin_lt hcin) rem hrem_le hrem_cur Inv hWit

private theorem n1s_dRowRev_withCliff_props
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 411 n)
    (off sh w : ℕ) (hw18 : w ≤ 18) (hoff_sh : sh + w ≤ 18)
    (hcur : 383 + w + 1 ≤ 411) (hacc : off + (w + 1) ≤ 32)
    (msbIdx : Fin 32) (hmsb_val : msbIdx.val = off + (w + 1))
    (uW cin : Wire 411) (hu_379 : uW.val < 379) (hcin : n1sValidCin cin)
    (InvPost : BitAssignment 411 → Prop)
    (d : DynamicCircuit Var n) (p : TempPhaseProg 411)
    (hd : d = p57ToDynWith v rComb
      (n1sMkDCleanMsbSub v rComb off w hw18 (by omega) hacc msbIdx cin hcin)
      (ctxCliffAlloc (n1sCRowSetup uW hu_379 sh w hoff_sh)))
    (hp : p = withCliffAlloc (n1sCRowSetup uW hu_379 sh w hoff_sh)
      (n1sMkCleanMsbSub off w hw18 hcur hacc msbIdx cin hcin))
    (hvStatic : ValidCleanRem 411 (411 - 379) p)
    (hWit : ∀ β, cleanRem 411 (411 - 379) β → InvPost β →
      ∃ A₀ : ℕ, A₀ < 2 ^ (w + 1) ∧
        bitsVal (fun j ↦ (n1sCRowSetup uW hu_379 sh w hoff_sh).eval β
            (n1sAccSlice off (w + 1) hacc j)) +
          2 ^ (w + 1) * ((n1sCRowSetup uW hu_379 sh w hoff_sh).eval β (n1sOut32W411 msbIdx)).val =
          A₀ + bitsVal (fun j ↦ (n1sCRowSetup uW hu_379 sh w hoff_sh).eval β (n1sBLowR w hw18 j)) +
            ((n1sCRowSetup uW hu_379 sh w hoff_sh).eval β cin).val) :
    d.count PrimitiveGate.T = 4 * w ∧ d.count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst d ∧
      RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 379) (by decide) InvPost) d
        (((p.onRegister rComb).toToffCircuit).eval) := by
  let c := n1sCRowSetup uW hu_379 sh w hoff_sh
  rw [hd, hp]
  refine ⟨by
    rw [p57ToDynWith_count_t, dCleanMsbSub_count_t]; simp [ctxCliffAlloc, TempCtx.countTempAnd],
    p57ToDynWith_count_toff v rComb _ (dCleanMsbSub_count_toff v rComb w 383 _ _ _ _ _ _ _ _ _ _ _ _
      _) _,
    p57ToDynWith_preservesStore v rComb _
      (dCleanMsbSub_preservesStore v rComb w 383 _ _ _ _ _ _ _ _ _ _ _ _ _) _, ?_⟩
  rw [← ctxCliffAlloc_plug]
  exact n1s_toDynWith_realizes_supp v rComb _ _ _ 383 (by decide)
    (n1s_mkDCleanMsbSub_realizes v rComb off w hw18 hcur hacc msbIdx hmsb_val cin hcin
      (411 - 383) (by decide) le_rfl _ (fun _ _ hi ↦ hi))
    (ctxCliffAlloc c) (ctxCliffAlloc_supports (n1s_cRowSetup_supports uW hu_379 sh w hoff_sh))
    (411 - 379) (by
      decide) (by decide) InvPost (by rw [ctxCliffAlloc_plug]; rwa [hp] at hvStatic) hWit

theorem n1s_baseRevD18_spec (t : Norm1sTier) (hd18 : t.dCut = 18) :
    let p := n1sBaseRevStaticD18 t
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t 2 β → n1sBoothInv t 0 (p.evalBits β) ∧
          ∃ A₀ : ℕ, A₀ < 2 ^ 2 ∧
            bitsVal (fun j ↦ (n1sCRowSetup (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩)
              (lt_trans (n1s_uKW411_range t _).2 (by decide)) 17 1 (by decide)).eval β
              (n1sAccSlice 0 2 (by decide) j)) +
              2 ^ 2 * ((n1sCRowSetup (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩)
                (lt_trans (n1s_uKW411_range t _).2 (by decide)) 17 1 (by decide)).eval β
                (n1sOut32W411 ⟨2, by decide⟩)).val =
              A₀ + bitsVal (fun j ↦ (n1sCRowSetup (n1sUKW411 t ⟨1, by
                have := n1s_tier_bounds t; omega⟩)
                (lt_trans (n1s_uKW411_range t _).2 (by decide)) 17 1 (by decide)).eval β
                (n1sBLowR 1 (by decide) j)) +
              ((n1sCRowSetup (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩)
                (lt_trans (n1s_uKW411_range t _).2 (by decide)) 17 1 (by decide)).eval β
                (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩)).val)) := by
  intro p
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  have hu1_90 : u1.val < 90 := (n1s_uKW411_range t _).2
  refine n1s_withCliffAlloc_cleanMsbSub_spec t 0 17 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) ⟨2, by decide⟩ rfl u1 u0 (lt_trans hu1_90 (by decide))
    (lt_trans hu1_90 (by decide)) (Or.inl (n1s_uKW411_range t _).2) 2 0 p rfl fun β hβ hInv2 ↦ ?_
  obtain ⟨hrow1, _, hrow0⟩ := w14_baseD18_rows_eq t hd18 β hβ
  have hbnd2 := (n1s_rowsAux_bounds t (bitsVal fun i ↦ β (n1sMantW411 i))
    (bitsVal fun k ↦ β (n1sUKW411 t k)) (bitsVal_lt_two_pow _) 2 (by omega)).1 hd18 rfl
  have hsl₁_3 : bitsVal (fun j : Fin 3 ↦ β (n1sOut32W411 ⟨0 + j.val, by omega⟩)) =
      norm1sHwRowsAux t.dCut (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
        (bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))) 2 :=
    (n1s_out32_slice_div (by decide) hInv2 (by rw [Nat.pow_zero, Nat.div_one]; omega)).trans
      (Nat.div_one _)
  exact ⟨0, _, by decide, by rw [hrow1, hrow0],
    by rw [hsl₁_3]; dsimp [norm1sHwRowsAux]; omega, by dsimp [norm1sHwRowsAux]; omega⟩

theorem n1s_dBaseRevD18_props (t : Norm1sTier) (hd18 : t.dCut = 18) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (n1sDBaseRevD18 t v rComb).count PrimitiveGate.T = 4 ∧ (n1sDBaseRevD18 t v rComb).count
    PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst (n1sDBaseRevD18 t v rComb) ∧
    RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 379) (by decide) (n1sBoothInv t 2))
    (n1sDBaseRevD18 t v rComb)
    ((((n1sBaseRevStaticD18 t).onRegister rComb).toToffCircuit).eval) := by
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  obtain ⟨hv, hEv⟩ := n1s_baseRevD18_spec t hd18
  exact n1s_dRowRev_withCliff_props v rComb 0 17 1 (by decide) (by decide) (by decide) (by decide)
    ⟨2, by decide⟩ rfl u1 u0 (lt_trans (n1s_uKW411_range t _).2 (by decide))
    (Or.inl (n1s_uKW411_range t _).2) (n1sBoothInv t 2) (n1sDBaseRevD18 t v rComb)
    (n1sBaseRevStaticD18 t) rfl rfl hv (fun β hβ hInv2 ↦ ((hEv β hβ).2.2.2 hInv2).2)

theorem n1s_lowRowRev_spec (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) :
    let p := n1sLowRowRevStatic t m hm1 hmd hw2
    let sh := t.dCut - m; let w := 18 - sh
    have hw18 : w ≤ 18 := by dsimp [w]; omega
    let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
    let c := n1sCRowSetup uW (lt_trans (n1s_uKW411_range t _).2 (by decide)) sh w
      (by have := n1s_tier_bounds t; dsimp [w, sh]; omega)
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t (m + 1) β → n1sBoothInv t m (p.evalBits β) ∧
          ∃ A₀ : ℕ, A₀ < 2 ^ (w + 1) ∧
            bitsVal (fun j ↦ c.eval β (n1sAccSlice 0 (w + 1) (by dsimp [w]; omega) j)) +
              2 ^ (w + 1) * (c.eval β (n1sOut32W411 ⟨w + 1, by dsimp [w]; omega⟩)).val =
              A₀ + bitsVal (fun j ↦ c.eval β (n1sBLowR w hw18 j)) + (c.eval β n1sZPad2W411).val)) :=
                by
  dsimp only
  have hb := n1s_tier_bounds t
  set sh := t.dCut - m
  set w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  have hoff_w : sh + w ≤ 18 := by dsimp [w, sh]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  have hu_201 : uW.val < 201 := lt_trans hu_90 (by decide)
  refine n1s_withCliffAlloc_cleanMsbSub_spec t 0 sh w hw18 hoff_w (by dsimp [w]; omega)
    (by dsimp [w]; omega) (by dsimp [w]; omega) ⟨w + 1, by dsimp [w]; omega⟩ (Nat.zero_add _).symm
    uW n1sZPad2W411 hu_201 (lt_trans hu_90 (by decide)) n1s_zPad2_validCin
    (m + 1) m (n1sLowRowRevStatic t m hm1 hmd hw2) rfl fun β hβ hInvNext ↦ ?_
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  let γ := (n1sCRowSetup uW (lt_trans hu_90 (by decide)) sh w hoff_w).eval β
  have hmS : mS < 2 ^ 18 := bitsVal_lt_two_pow _
  have hγ_z2 := (n1s_cRowSetup_eval uW hu_201 sh w hoff_w β hβ).2.2.2.1
  have hrow : bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) = norm1sRowVal t.dCut m mS (uK.testBit m) :=
    by
    rw [bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨m, lt_trans hmd (by omega)⟩]
    exact (n1s_bLowR_val_eq_row t.dCut m hmd (by
      omega) (by dsimp [w, sh] at hw2; omega) uW hu_201 β hβ).1
  have hbnd_next := (n1s_rowsAux_bounds t mS uK hmS (m + 1) (by omega)).2.2.1
    (by split_ifs <;> omega) (by omega)
  rw [show (18 - t.dCut) + (m + 1) + 1 = w + 2 from by dsimp [w, sh]; omega] at hbnd_next
  set Pm := norm1sHwRowsAux t.dCut mS uK m
  have hPm_lt : Pm < 2 ^ (w + 1) := by
    have hb_m := (n1s_rowsAux_bounds t mS uK hmS m (by omega)).2.2.1
      (by by_cases h18 : t.dCut = 18 <;> simp [h18] <;> dsimp [w, sh] at hw2 <;> omega) (by omega)
    rw [show (18 - t.dCut) + m + 1 = w + 1 from by dsimp [w, sh]; omega] at hb_m
    omega
  have hsl₁_full : bitsVal (fun j : Fin (w + 2) ↦ β (n1sOut32W411 ⟨0 + j.val, by omega⟩)) =
      Pm + norm1sRowVal t.dCut m mS (uK.testBit m) :=
    (n1s_out32_slice_div (by dsimp [w]; omega) hInvNext (by
      rw [Nat.pow_zero, Nat.div_one]; omega)).trans (Nat.div_one _)
  exact ⟨Pm, norm1sRowVal t.dCut m mS (uK.testBit m), hPm_lt,
    by rw [hrow, hγ_z2, ZMod.val_zero, add_zero], hsl₁_full, by dsimp [norm1sHwRowsAux]; omega⟩

theorem n1s_dLowRowRev_props (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (n1sDLowRowRev t m hm1 hmd hw2 v rComb).count PrimitiveGate.T = 4 * (18 - (t.dCut - m)) ∧
    (n1sDLowRowRev t m hm1 hmd hw2 v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (n1sDLowRowRev t m hm1 hmd hw2 v rComb) ∧ RealizesCleanUnitary v (p57CleanDiagProj rComb
    (411 - 379) (by decide) (n1sBoothInv t (m + 1))) (n1sDLowRowRev t m hm1 hmd hw2 v rComb)
    ((((n1sLowRowRevStatic t m hm1 hmd hw2).onRegister rComb).toToffCircuit).eval) := by
  have hb := n1s_tier_bounds t
  set sh := t.dCut - m
  set w := 18 - sh
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩
  obtain ⟨hv, hEv⟩ := n1s_lowRowRev_spec t m hm1 hmd hw2
  exact n1s_dRowRev_withCliff_props v rComb 0 sh w (by dsimp [w]; omega) (by dsimp [w, sh]; omega)
    (by dsimp [w]; omega) (by dsimp [w]; omega) ⟨w + 1, by dsimp [w]; omega⟩ (Nat.zero_add _).symm
    uW n1sZPad2W411 (lt_trans (n1s_uKW411_range t _).2 (by decide)) n1s_zPad2_validCin
    (n1sBoothInv t (m + 1)) (n1sDLowRowRev t m hm1 hmd hw2 v rComb)
    (n1sLowRowRevStatic t m hm1 hmd hw2) rfl rfl hv (fun β hβ hInv ↦ ((hEv β hβ).2.2.2 hInv).2)

theorem n1s_highRowRev_spec (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut) :
    let p := n1sHighRowRevStatic t off hoff
    have hb := n1s_tier_bounds t
    let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
    let c := n1sCRowSetup uW (lt_trans (n1s_uKW411_range t _).2 (by decide)) 0 18 (by decide)
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothInv t (t.dCut + off + 1) β → n1sBoothInv t (t.dCut + off) (p.evalBits β) ∧
          ∃ A₀ : ℕ, A₀ < 2 ^ 19 ∧
            bitsVal (fun j ↦ c.eval β (n1sAccSlice off 19 (by omega) j)) +
              2 ^ 19 * (c.eval β (n1sOut32W411 ⟨off + 19, by omega⟩)).val =
              A₀ + bitsVal (fun j ↦
                c.eval β (n1sBLowR 18 le_rfl j)) + (c.eval β n1sCinW411).val)) := by
  dsimp only
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  refine n1s_withCliffAlloc_cleanMsbSub_spec t off 0 18 le_rfl (by decide) (by decide)
    (by omega) (by omega) ⟨off + 19, by omega⟩ rfl uW n1sCinW411 (lt_trans hu_90 (by decide))
    (lt_trans hu_90 (by decide)) n1s_cinW_validCin
    (t.dCut + off + 1) (t.dCut + off) (n1sHighRowRevStatic t off hoff) rfl fun β hβ hInvNext ↦ ?_
  obtain ⟨hBR, _, hdiv_lt, hrow0_lt, hPnext_eq⟩ := w14_highRow_step_facts t off hoff β hβ
  have h220 : (2 ^ 19 : ℕ) + 2 ^ 19 = 2 ^ 20 := by decide
  refine ⟨_, _, hdiv_lt, hBR, ?_, by rw [hPnext_eq]; ring⟩
  rw [bitsVal_slice_eq_div_mod (by omega) (fun k ↦ β (n1sOut32W411 k)), hInvNext, hPnext_eq,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos off), Nat.mod_eq_of_lt (by omega)]

theorem n1s_dHighRowRev_props (t : Norm1sTier) (off : ℕ) (hoff : off < t.kBits - t.dCut)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rComb : QRegister 411 n) : (n1sDHighRowRev t off hoff v rComb).count PrimitiveGate.T = 72
    ∧ (n1sDHighRowRev t off hoff v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (n1sDHighRowRev t off hoff v rComb) ∧ RealizesCleanUnitary v (p57CleanDiagProj rComb (411
    - 379) (by decide) (n1sBoothInv t (t.dCut + off + 1))) (n1sDHighRowRev t off hoff v rComb)
    ((((n1sHighRowRevStatic t off hoff).onRegister rComb).toToffCircuit).eval) := by
  have hb := n1s_tier_bounds t
  let uW := n1sUKW411 t ⟨t.dCut + off, by omega⟩
  obtain ⟨hv, hEv⟩ := n1s_highRowRev_spec t off hoff
  exact n1s_dRowRev_withCliff_props v rComb off 0 18 le_rfl (by decide) (by decide) (by omega)
    ⟨off + 19, by omega⟩ rfl uW n1sCinW411 (lt_trans (n1s_uKW411_range t _).2 (by decide))
    n1s_cinW_validCin (n1sBoothInv t (t.dCut + off + 1)) (n1sDHighRowRev t off hoff v rComb)
    (n1sHighRowRevStatic t off hoff) rfl rfl hv (fun β hβ hInv ↦ ((hEv β hβ).2.2.2 hInv).2)

theorem n1s_topRowRev_spec (t : Norm1sTier) :
    let p := n1sTopRowRevStatic t
    have hb := n1s_tier_bounds t
    let topOff := t.kBits - t.dCut
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧ cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothDoneInv t β →
          n1sBoothInv t t.kBits (p.evalBits β) ∧
          ∃ A₀ : ℕ, A₀ < 2 ^ 19 ∧
            bitsVal (fun j ↦ β (n1sAccSlice topOff 19 (by dsimp [topOff]; omega) j)) +
              2 ^ 19 * (β (n1sOut32W411 ⟨topOff + 19, by dsimp [topOff]; omega⟩)).val =
              A₀ + bitsVal (fun j ↦ β (n1sBLowR 18 le_rfl j)) + (β n1sZPad2W411).val)) := by
  dsimp only
  have hb := n1s_tier_bounds t
  set topOff := t.kBits - t.dCut
  rw [show n1sTopRowRevStatic t = n1sMkCleanMsbSub topOff 18 le_rfl (by decide)
    (by dsimp [topOff]; omega) ⟨topOff + 19, by dsimp [topOff]; omega⟩
    n1sZPad2W411 n1s_zPad2_validCin from rfl]
  obtain ⟨hvSub, hCore⟩ := n1s_core_cleanMsbSub_spec topOff 18 le_rfl (by decide)
    (by dsimp [topOff]; omega) (by dsimp [topOff]; omega) ⟨topOff + 19, by dsimp [topOff]; omega⟩
    rfl n1sZPad2W411 n1s_zPad2_validCin
  refine ⟨validCleanRem_mono (by decide : 411 - 383 ≤ 411 - 379) hvSub, fun β hβ ↦ ?_⟩
  obtain ⟨hsSub, hNon, hVal⟩ := hCore β (cleanRem_anti (by decide) hβ)
  refine ⟨hsSub, fun q hq ↦ (hNon q fun k ↦
      wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)).trans (hβ q hq), hNon, fun hDone ↦ ?_⟩
  obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t hNon
  unfold n1sBoothDoneInv at hDone
  unfold n1sBoothInv
  rw [hmEq, huEq]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hmS : mS < 2 ^ 18 := bitsVal_lt_two_pow _
  set PK := norm1sHwRowsAux t.dCut mS uK t.kBits
  have hdiv_lt : PK / 2 ^ topOff < 2 ^ 19 := (n1s_hwProd_lt_two_pow_wAcc t mS uK hmS).1
  have hsl₁_full : bitsVal (fun j : Fin 20 ↦ β (n1sOut32W411 ⟨topOff + j.val, by omega⟩)) =
      PK / 2 ^ topOff + mS := by
    rw [bitsVal_slice_eq_div_mod (by dsimp [topOff]; omega) (fun k ↦ β (n1sOut32W411 k)), hDone,
      show norm1sHwProd t.kBits t.dCut mS uK = PK + mS * 2 ^ topOff from rfl,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos topOff),
      Nat.mod_eq_of_lt (lt_trans (Nat.add_lt_add hdiv_lt hmS) (by decide))]
  obtain ⟨hPre, hWit⟩ := hVal (PK / 2 ^ topOff) mS _ PK hdiv_lt hDone
    (by rw [(n1s_bLowR18_clean_val β hβ).1, hβ n1sZPad2W411 (by decide), ZMod.val_zero, add_zero])
    hsl₁_full (by unfold norm1sHwProd; ring)
  exact ⟨hPre, PK / 2 ^ topOff, hdiv_lt, hWit⟩

theorem n1s_dTopRowRev_props (t : Norm1sTier) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (n1sDTopRowRev t v rComb).count PrimitiveGate.T = 72 ∧ (n1sDTopRowRev t v rComb).count
    PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst (n1sDTopRowRev t v rComb) ∧
    RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 379) (by decide) (n1sBoothDoneInv t))
    (n1sDTopRowRev t v rComb) ((((n1sTopRowRevStatic t).onRegister rComb).toToffCircuit).eval)
    := by
  dsimp only [n1sDTopRowRev, n1sTopRowRevStatic]
  have hb := n1s_tier_bounds t
  set topOff := t.kBits - t.dCut
  obtain ⟨_, hEv⟩ := n1s_topRowRev_spec t
  exact ⟨by rw [n1sMkDCleanMsbSub, dCleanMsbSub_count_t],
    dCleanMsbSub_count_toff v rComb 18 383 _ _ _ _ _ _ _ _ _ _ _ _ _,
    dCleanMsbSub_preservesStore v rComb 18 383 _ _ _ _ _ _ _ _ _ _ _ _ _,
    n1s_mkDCleanMsbSub_realizes v rComb topOff 18 le_rfl (by decide) (by dsimp [topOff]; omega)
      ⟨topOff + 19, by dsimp [topOff]; omega⟩ rfl n1sZPad2W411 n1s_zPad2_validCin
      (411 - 379) (by decide) (by decide) (n1sBoothDoneInv t)
      (fun β hβ hDone ↦ ((hEv β hβ).2.2.2 hDone).2)⟩

/-- Symbolic `TempAnd` count of `n1sBoothPrefixFwd t m`. -/
def n1sBoothPrefixFwdAnds (t : Norm1sTier) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => if t.dCut = 18 then 2 else (18 - (t.dCut - 1)) + 1
  | m + 3 =>
      n1sBoothPrefixFwdAnds t (m + 2) +
        if m + 2 < t.dCut then (18 - (t.dCut - (m + 2))) + 1 else 19

/-- Symbolic `TempAnd` count of `n1sBoothFwd411 t`. -/
def n1sBoothFwdAnds (t : Norm1sTier) : ℕ := n1sBoothPrefixFwdAnds t t.kBits + 19

/-- Symbolic `T`-gate count of `n1sDBoothPrefixRev t v rComb m`. -/
def n1sBoothPrefixRevT (t : Norm1sTier) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => if t.dCut = 18 then 4 else 4 * (18 - (t.dCut - 1))
  | m + 3 =>
      (if m + 2 < t.dCut then 4 * (18 - (t.dCut - (m + 2))) else 72) +
        n1sBoothPrefixRevT t (m + 2)

/-- Symbolic `T`-gate count of `n1sDBoothRev411 t v rComb`. -/
def n1sBoothRevT (t : Norm1sTier) : ℕ := 72 + n1sBoothPrefixRevT t t.kBits

theorem n1s_boothPrefixFwd_countTempAnd (t : Norm1sTier) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      (n1sBoothPrefixFwd t m hm).countTempAnd = n1sBoothPrefixFwdAnds t m
  | 0, _ => rfl
  | 1, _ => by
      dsimp only [n1sBoothPrefixFwd, n1sBoothPrefixFwdAnds]
      by_cases hd18 : t.dCut = 18 <;> simp [hd18, TempPhaseProg.countTempAnd]
  | 2, _ => by
      dsimp only [n1sBoothPrefixFwd, n1sBoothPrefixFwdAnds]
      by_cases hd18 : t.dCut = 18
      · simp [hd18, n1sBaseFwdD18, inPlaceAddMod1_countTempAnd]
      · simp[hd18, TempPhaseProg.countTempAnd, n1sLowRowFwd, inPlaceAddMod1_countTempAnd]
  | m + 3, hm => by
      dsimp only [n1sBoothPrefixFwd, n1sBoothPrefixFwdAnds]
      by_cases hlow : m + 2 < t.dCut
      · simp [hlow, TempPhaseProg.countTempAnd, n1s_boothPrefixFwd_countTempAnd t (m + 2),
          n1sLowRowFwd, inPlaceAddMod1_countTempAnd]
      · simp [hlow, TempPhaseProg.countTempAnd, n1s_boothPrefixFwd_countTempAnd t (m + 2),
          n1sHighRowFwd, inPlaceAddMod1_countTempAnd]

theorem n1s_boothFwd411_countTempAnd (t : Norm1sTier) :
    (n1sBoothFwd411 t).countTempAnd = n1sBoothFwdAnds t := by
  simp [n1sBoothFwd411, n1sBoothFwdAnds, TempPhaseProg.countTempAnd,
    n1s_boothPrefixFwd_countTempAnd, n1sTopRowFwd, inPlaceAddMod1_countTempAnd]

theorem n1s_boothPrefixRev_spec (t : Norm1sTier) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      let p := n1sBoothPrefixRevStatic t m hm
      ValidCleanRem 411 (411 - 379) p ∧
        (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
          p.evalSign β = 0 ∧
          cleanRem 411 (411 - 379) (p.evalBits β) ∧
          (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
          ((t.dCut = 18 → m ≠ 1) → n1sBoothInv t m β → n1sBoothInv t 0 (p.evalBits β)))
  | 0, _ => ⟨trivial, fun _ hβ ↦ ⟨rfl, hβ, fun _ _ ↦ rfl, fun _ h0 ↦ h0⟩⟩
  | 1, _ => by
      dsimp only [n1sBoothPrefixRevStatic]
      by_cases hd18 : t.dCut = 18
      · rw [dite_eq_left hd18]
        exact ⟨trivial, fun _ hβ ↦ ⟨rfl, hβ, fun _ _ ↦ rfl, fun hne _ ↦ absurd rfl (hne hd18)⟩⟩
      · rw [dite_eq_right hd18]
        have hb := n1s_tier_bounds t
        let u0 := n1sUKW411 t ⟨0, by omega⟩
        let c0 := n1sCRow0Full u0 (lt_trans (n1s_uKW411_range t _).2 (by decide))
          t.dCut ⟨hb.2.2.1, by omega⟩
        have hsub : ∀ (w : ℕ) (hw : t.dCut + w ≤ 18) (η : BitAssignment 411) (q : Wire 411),
            (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
            (n1sCRow0Lt18 u0 (lt_trans (n1s_uKW411_range t _).2 (by
              decide)) t.dCut w hw).inv.eval η q = η q := by
          intro w hw; induction w with
          | zero => intro _ _ _; rfl
          | succ w ih =>
              intro η q hq
              have hne : q ≠ n1sOut32W411 ⟨w, by omega⟩ := hq ⟨w, by omega⟩
              dsimp only [n1sCRow0Lt18, CliffProg.inv, CliffProg.eval]
              simp only [Function.update_of_ne hne]
              exact ih (by omega) η q hq
        refine ⟨trivial, fun β hβ ↦ ?_⟩
        have hNon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → c0.inv.eval β q = β q := by
          intro q hq
          dsimp only [c0, n1sCRow0Full, CliffProg.inv, CliffProg.eval]
          rw [Function.update_of_ne (hq ⟨18 - t.dCut, by omega⟩)]
          exact hsub (18 - t.dCut) (by omega) β q hq
        have hCl : cleanRem 411 (411 - 379) (c0.inv.eval β) := fun q hq ↦ by
          rw [hNon q (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))]; exact hβ q hq
        refine ⟨rfl, hCl, hNon, fun _ hInv1 ↦ ?_⟩
        let β₀ : BitAssignment 411 := fun q ↦ if ∃ k : Fin 32, q = n1sOut32W411 k then 0 else β q
        have hβ₀_out0 : ∀ j : Fin 32, β₀ (n1sOut32W411 j) = 0 := fun j ↦ ite_eq_left ⟨j, rfl⟩
        have hβ₀_non : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → β₀ q = β q :=
          fun q hq ↦ ite_eq_right (fun ⟨k, hk⟩ ↦ hq k hk)
        obtain ⟨_, hNon0, hVal0⟩ := n1s_cRow0Full_spec u0
          (lt_trans (n1s_uKW411_range t _).2 (by decide)) t.dCut ⟨hb.2.2.1, by omega⟩ β₀ hβ₀_out0
        obtain ⟨hm0, hu0_eq⟩ := n1s_mant_uK_congr t hβ₀_non
        have hβ₀_u0 : β₀ u0 = β u0 := hβ₀_non u0
          (fun k ↦ wire_ne_of_lt (lt_of_lt_of_le (n1s_uKW411_range t _).2 (by
            dsimp [n1sOut32W411]; omega)))
        have hc0_eq : c0.eval β₀ = β := by
          have hvEq : bitsVal (fun j : Fin 32 ↦ c0.eval β₀ (n1sOut32W411 j)) =
              bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) := by
            rw [hVal0, hm0, hβ₀_u0, hInv1]
            dsimp [norm1sHwRowsAux]
            rw [bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨0, by omega⟩, zero_add]
          have hOutEq := congrFun (bitsVal_injective hvEq)
          funext q
          by_cases hq : ∃ k : Fin 32, q = n1sOut32W411 k
          · obtain ⟨k, rfl⟩ := hq; exact hOutEq k
          · exact (hNon0 q (fun k hk ↦ hq ⟨k, hk⟩)).trans (ite_eq_right hq)
        have hinv_eq : c0.inv.eval β = β₀ := by
          rw [← hc0_eq]; exact cliffInv_comp_eval c0 β₀
        change n1sBoothInv t 0 (c0.inv.eval β)
        rw [hinv_eq]
        simp [n1sBoothInv, hβ₀_out0, norm1sHwRowsAux, bitsVal]
  | 2, _ => by
      dsimp only [n1sBoothPrefixRevStatic]
      by_cases hd18 : t.dCut = 18
      · rw [dite_eq_left hd18]
        obtain ⟨hv, hEv⟩ := n1s_baseRevD18_spec t hd18
        exact ⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
          fun _ h2 ↦ ((hEv β hβ).2.2.2 h2).1⟩⟩
      · rw [dite_eq_right hd18]
        have hb := n1s_tier_bounds t
        exact n1s_seq_clean_out32 (n1s_lowRowRev_spec t 1 le_rfl (by omega) (by omega))
          (n1s_boothPrefixRev_spec t 1 (by omega))
          (fun _ h1 h2 _ h2Inv ↦ h2 (fun h ↦ absurd h hd18) (h1 h2Inv).1)
  | m + 3, hm => by
      dsimp only [n1sBoothPrefixRevStatic]
      have hb := n1s_tier_bounds t
      have hNext := n1s_boothPrefixRev_spec t (m + 2) (by omega)
      by_cases hlow : m + 2 < t.dCut
      · rw [dite_eq_left hlow]
        exact n1s_seq_clean_out32 (n1s_lowRowRev_spec t (m + 2) (by omega) hlow (by omega)) hNext
          (fun _ h1 h2 _ h3 ↦ h2 (fun _ ↦ by omega) (h1 h3).1)
      · rw [dite_eq_right hlow]
        refine n1s_seq_clean_out32 (n1s_highRowRev_spec t ((m + 2) - t.dCut) (by omega)) hNext
          (fun β h1 h2 _ h3 ↦ ?_)
        have h3' : n1sBoothInv t (t.dCut + ((m + 2) - t.dCut) + 1) β := by
          rwa [show t.dCut + ((m + 2) - t.dCut) + 1 = m + 3 from by omega]
        have h1' := (h1 h3').1
        rw [show t.dCut + ((m + 2) - t.dCut) = m + 2 from by omega] at h1'
        exact h2 (fun _ ↦ by omega) h1'
end

end ConfigSlot3Norm1s36CoreWideBooth

end Slot3Norm1s36CoreWideBooth
end
set_option exponentiation.threshold 256
end Slot3Norm1s36CoreWideBooth

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
