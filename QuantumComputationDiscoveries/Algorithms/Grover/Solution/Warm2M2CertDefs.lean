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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseWarmR1

@[expose] public section
/-
# Warm `m = 2` Multi-Stage Certificate Definitions (`Warm2M2CertDefs`)
-/
section Sec_PipelinedFuseWarmR1CertDefs
namespace QuantumComputation.Specs.GroverFindAll.PipeFuseWarmR1Cert
open Real
open QuantumComputation.Specs.GroverFindAll.PipeFuseCert
/- ## 1. Pure-Integer Warm `r = 1` & Cell Checkers -/
/-- Scale-`10^12` ceiling product `⌈x * y / 10^12⌉`. -/
def mulCeil12 (x y : ℕ) : ℕ := (x * y + 999999999999) / 1000000000000
/-- Auxiliary repeated-squaring loop computing an upper bound on `acc * sq ^ (2 ^ d - 1)` at
  scale
  `10^12`. -/
def powPredPow2Aux (sq acc : ℕ) : ℕ → ℕ
  | 0 => acc
  | d + 1 =>
    withForcedNat (mulCeil12 acc sq) fun acc' ↦ withForcedNat (mulCeil12 sq sq) fun sq' ↦
      powPredPow2Aux sq' acc' d
/-- Certified upper bound on `(a / 10^12) ^ (2 ^ d - 1)` at scale `10^12`. -/
def powPredPow2Ceil12 (a d : ℕ) : ℕ := powPredPow2Aux a 1000000000000 d
/-- Certified lower bound on `10^12 * arctan (p / q)` for `p ≤ q` and `0 < q`, using `[5/6]`
  Padé
  on `[0, 5/12]` and octant reflection with `[5/4]` Padé on `(5/12, 1]`. -/
def atanRatioLo12 (p q : ℕ) : ℕ :=
  if 12 * p ≤ 5 * q then
    withForcedNat (p * p) fun p2 ↦ withForcedNat (q * q) fun q2 ↦
    withForcedNat (p * q * (1155 * q2 * q2 + 1190 * p2 * q2 + 231 * p2 * p2)) fun pHom ↦
    withForcedNat (1155 * q2 * q2 * q2 + 1575 * p2 * q2 * q2 +
      525 * p2 * p2 * q2 + 25 * p2 * p2 * p2) fun qHom ↦ (1000000000000 * pHom) / qHom
  else
    withForcedNat (q - p) fun a ↦ withForcedNat (q + p) fun b ↦ withForcedNat (a * a) fun a2 ↦
    withForcedNat (b * b) fun b2 ↦
    withForcedNat (a * (945 * b2 * b2 + 735 * a2 * b2 + 64 * a2 * a2)) fun p54 ↦
    withForcedNat (b * (945 * b2 * b2 + 1050 * a2 * b2 + 225 * a2 * a2)) fun q54 ↦
    withForcedNat ((1000000000000 * p54 + q54 - 1) / q54) fun padeCeil ↦ 785398163397 - padeCeil
/-- Precomputed upper table `⌈10^12 * (100000004 / 10^8) * (4091549431 / 5e9) * (π / 4) /
  √(2^d)⌉`
  for `d ∈ {0,..., 10}`. -/
def cWarmHiNat (d : ℕ) : ℕ := cond (Nat.blt d 5)
    (cond (Nat.blt d 2) (cond (Nat.blt d 1) 642699107420 454456897120)
      (cond (Nat.blt d 3) 321349553710 (cond (Nat.blt d 4) 227228448560 160674776855)))
    (cond (Nat.blt d 8)
      (cond (Nat.blt d 6) 113614224280 (cond (Nat.blt d 7) 80337388428 56807112140))
      (cond (Nat.blt d 9) 40168694214 (cond (Nat.blt d 10) 28403556070
        (cond (Nat.blt d 11) 20084347107 0))))
/-- Check `cWarmHiNat d` upper square inequality against the inflated Stationary-chord warm
  `r = 1` factor. -/
def checkCWarmItem (d : ℕ) : Bool := withForcedNat (cWarmHiNat d) fun c ↦
  withForcedNat (100000004 * 4091549431 * 785398163398) fun num ↦
  withForcedNat (100000000 * 5000000000) fun den ↦ decide (num * num ≤ (2 ^ d) * den * den * c * c)
/-- Master certificate for `cWarmHiNat` over `d ∈ {0,..., 10}`. -/
def checkCWarmTable : Bool := allRange checkCWarmItem 11
theorem cert_cWarmTable : checkCWarmTable = true := by decide +kernel
/-- Check tangent-majorized convex endpoint bounds on segment `s ∈ {0,..., 31}` of
  `[0, arctan(t2 / 10^5)]` for `m = 2 ^ d`. -/
def checkWarmR1Seg (d t2 warmNet s : ℕ) : Bool :=
  let m := 2 ^ d
  withForcedNat ((s * t2) / 32) fun tau0 ↦ withForcedNat (((s + 1) * t2) / 32) fun tau1 ↦
  withForcedNat (10000000000 + tau0 * tau0) fun den0 ↦
  withForcedNat (((20000000000 + tau0 * tau0) * 1000000000000 + 2 * den0 - 1) / (2 * den0))
    fun g0Hi ↦
  withForcedNat (atanRatioLo12 ((tau1 - tau0) * 100000) (10000000000 + tau1 * tau0)) fun dbLo ↦
  withForcedNat ((100000 * tau0 * dbLo) / den0) fun dropLo ↦
  withForcedNat (g0Hi - dropLo) fun g1Hi ↦ withForcedNat (powPredPow2Ceil12 g0Hi d) fun p0 ↦
  withForcedNat (powPredPow2Ceil12 g1Hi d) fun p1 ↦
  withForcedNat (((m - 1) * atanRatioLo12 ((t2 - tau0) * 100000) (10000000000 + t2 * tau0) *
      353553390592) / (m * 1000000000000)) fun cred0 ↦
  withForcedNat (((m - 1) * atanRatioLo12 ((t2 - tau1) * 100000) (10000000000 + t2 * tau1) *
      353553390592) / (m * 1000000000000)) fun cred1 ↦
  withForcedNat (cWarmHiNat d) fun cWarm ↦ decide (mulCeil12 cWarm p0 ≤ warmNet + cred0) &&
    decide (mulCeil12 cWarm p1 ≤ warmNet + cred1)
/-- Check stage `r = 2` warm-`r = 1` certificate row for `m = 2 ^ d` (`500 ≤ t2 ≤ 100000`). -/
def checkWarmR1Stage2 (d : ℕ) (rw2 : FuseStageRow) : Bool :=
  match rw2 with
  | ⟨v2, t2, phiHi2, _, _, _, stepNum2, _, _⟩ =>
    decide (d < 11) && decide (500 ≤ t2) && decide (t2 ≤ 100000) && checkOctantAtan t2 phiHi2 &&
    checkClickRow (2 ^ d) 2 t2 stepNum2 && decide (stepNum2 + 1 ≤ v2) &&
    withForcedNat (v2 - stepNum2 - 1) fun warmNet ↦ allRange (checkWarmR1Seg d t2 warmNet) 32
/-- Dispatch stage index `i = r - 1`: trivial at `i = 0`, warm stage-2 check at `i = 1`, and
  standard `checkFuseStageIdx` for `i ≥ 2` (`r ≥ 3`). -/
def checkWarmR1StageIdx (rowFn : ℕ → FuseStageRow) (d i : ℕ) : Bool :=
  if i == 0 then true
  else if i == 1 then checkWarmR1Stage2 d (rowFn 2)
  else checkFuseStageIdx rowFn d i
/-- Full cell certificate check for `(m, k) = (2 ^ d, 2 ^ kIdx)` with `1 ≤ kIdx < 11` (`2 ≤
  k`)
  under `PipelinedFuseWarmR1` (`relCost = relCostNum / 10^10`). -/
def checkWarmR1CellRow (rowFn : ℕ → FuseStageRow) (d kIdx topR relCostNum : ℕ) : Bool :=
  let k := 2 ^ kIdx
  match rowFn 0, rowFn k with
  | ⟨v0, _, _, _, _, _, _, _, _⟩, ⟨vK, tK, phiHiK, _, _, _, _, _, _⟩ =>
    (v0 == 0) && decide (d < 11) && decide (1 ≤ kIdx) && decide (kIdx < 11) &&
    allRange (checkWarmR1StageIdx rowFn d) k && decide (1 ≤ topR) &&
    decide (500 ≤ tK) && decide (tK ≤ 100000) && checkOctantAtan tK phiHiK &&
    decide (phiHiK * phiHiK ≤ 4 * k * (topR - 1) * (topR - 1)) &&
    decide ((vK + topR) * 10000000000 * sqrtMUpNat d ≤ relCostNum * 785398163397 * harmSumPow2 kIdx)
/- ## 2. Arithmetic & Rational-Arctan Soundness Helpers -/
theorem le_ceil_div_mul {a b : ℕ} (hb : 0 < b) :
    a ≤ ((a + b - 1) / b) * b := by
  have hdiv := Nat.mod_add_div (a + b - 1) b; have hmod := Nat.mod_lt (a + b - 1) hb
  rw [Nat.mul_comm] at hdiv; omega
theorem le_mulCeil12 {x y : ℕ} : ((x : ℝ) / 1000000000000) * ((y : ℝ) / 1000000000000) ≤
      (mulCeil12 x y : ℝ) / 1000000000000 := by
  have hnat : x * y ≤ mulCeil12 x y * 1000000000000 := by
    unfold mulCeil12; have hdiv := Nat.mod_add_div (x * y + 999999999999) 1000000000000
    have hmod := Nat.mod_lt (x * y + 999999999999) (by omega : 0 < 1000000000000)
    rw [Nat.mul_comm] at hdiv; omega
  have hcast : (x : ℝ) * y ≤ (mulCeil12 x y : ℝ) * 1000000000000 := (by exact_mod_cast hnat)
  linarith [hcast, show ((x : ℝ) / 1000000000000) * ((y : ℝ) / 1000000000000) =
      ((x : ℝ) * y) / ((10 : ℝ) ^ 24) by ring,
    show (mulCeil12 x y : ℝ) / 1000000000000 =
      ((mulCeil12 x y : ℝ) * 1000000000000) / ((10 : ℝ) ^ 24) by ring]
theorem powPredPow2Aux_sound (d : ℕ) (sq acc : ℕ) :
    ((acc : ℝ) / 1000000000000) * ((sq : ℝ) / 1000000000000) ^ (2 ^ d - 1) ≤
      (powPredPow2Aux sq acc d : ℝ) / 1000000000000 := by
  induction d generalizing sq acc with
  | zero => simp [powPredPow2Aux]
  | succ d ih =>
      simp only [powPredPow2Aux, withForcedNat_eq]; set s : ℝ := (sq : ℝ) / 1000000000000
      set a : ℝ := (acc : ℝ) / 1000000000000; have hs0 : 0 ≤ s := (by positivity)
      have ha0 : 0 ≤ a := (by positivity)
      have hacc : a * s ≤ (mulCeil12 acc sq : ℝ) / 1000000000000 := le_mulCeil12
      have hsq : s ^ 2 ≤ (mulCeil12 sq sq : ℝ) / 1000000000000 := by
        rw [pow_two]; exact le_mulCeil12
      have hpow : (s ^ 2) ^ (2 ^ d - 1) ≤ ((mulCeil12 sq sq : ℝ) / 1000000000000) ^ (2 ^ d - 1) :=
        pow_le_pow_left₀ (by positivity) hsq (2 ^ d - 1)
      have hmul : (a * s) * (s ^ 2) ^ (2 ^ d - 1) ≤ ((mulCeil12 acc sq : ℝ) / 1000000000000) *
            ((mulCeil12 sq sq : ℝ) / 1000000000000) ^ (2 ^ d - 1) :=
        mul_le_mul hacc hpow (by positivity) (by positivity)
      have hexp : 1 + 2 * (2 ^ d - 1) = 2 ^ (d + 1) - 1 := by
        have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow; rw [pow_succ]; omega
      have hlhs : a * s ^ (2 ^ (d + 1) - 1) = (a * s) * (s ^ 2) ^ (2 ^ d - 1) := by
        rw [← hexp, pow_add, pow_one, ← pow_mul]; ring
      rw [hlhs]; exact hmul.trans (ih (mulCeil12 sq sq) (mulCeil12 acc sq))
theorem powPredPow2Ceil12_sound {u : ℝ} {a d : ℕ} (hu0 : 0 ≤ u)
    (hua : u ≤ (a : ℝ) / 1000000000000) :
    u ^ (2 ^ d - 1) ≤ (powPredPow2Ceil12 a d : ℝ) / 1000000000000 := by
  have h1 : u ^ (2 ^ d - 1) ≤ ((a : ℝ) / 1000000000000) ^ (2 ^ d - 1) :=
    pow_le_pow_left₀ hu0 hua (2 ^ d - 1)
  have h2 := powPredPow2Aux_sound d a 1000000000000
  have h3 : ((1000000000000 : ℕ) : ℝ) / 1000000000000 = 1 := (by norm_num); rw [h3, one_mul] at h2
  exact h1.trans h2
theorem cWarmHiNat_sound {d : ℕ} (hd : d < 11) :
    (100000004 / 100000000 : ℝ) * (4091549431 / 5000000000) * (π / 4) / √((2 : ℝ) ^ d) ≤
      (cWarmHiNat d : ℝ) / 1000000000000 := by
  have hitem := of_allRange cert_cWarmTable hd
  simp only [checkCWarmItem, withForcedNat_eq] at hitem; have hsq_nat := of_decide_eq_true hitem
  have hpi : π / 4 ≤ (785398163398 : ℝ) / 1000000000000 := (by linarith [Real.pi_lt_d20])
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := (by positivity)
  have hs2d_pos : (0 : ℝ) < √((2 : ℝ) ^ d) := Real.sqrt_pos.2 h2d_pos
  have hstep1 : (100000004 / 100000000 : ℝ) * (4091549431 / 5000000000) * (π / 4) / √((2 : ℝ) ^ d) ≤
        ((100000004 * 4091549431 * 785398163398 : ℝ) /
          (100000000 * 5000000000 * √((2 : ℝ) ^ d))) / 1000000000000 := by
    have hm := mul_le_mul_of_nonneg_left hpi
      (by positivity : (0 : ℝ) ≤ (100000004 / 100000000) * (4091549431 / 5000000000))
    have hd1 := div_le_div_of_nonneg_right hm hs2d_pos.le; refine hd1.trans (le_of_eq ?_)
    field_simp [hs2d_pos.ne']
  refine hstep1.trans (div_le_div_of_nonneg_right ?_ (by norm_num))
  rw [div_le_iff₀ (by positivity)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
  have hcast : ((100000004 * 4091549431 * 785398163398 : ℝ)) *
      (100000004 * 4091549431 * 785398163398) ≤
      ((2 : ℝ) ^ d) * (100000000 * 5000000000) * (100000000 * 5000000000) *
        cWarmHiNat d * cWarmHiNat d := by exact_mod_cast hsq_nat
  have hrhs_sq : ((cWarmHiNat d : ℝ) * (100000000 * 5000000000 * √((2 : ℝ) ^ d))) ^ 2 =
        ((2 : ℝ) ^ d) * (100000000 * 5000000000) * (100000000 * 5000000000) *
          cWarmHiNat d * cWarmHiNat d := by
    calc ((cWarmHiNat d : ℝ) * (100000000 * 5000000000 * √((2 : ℝ) ^ d))) ^ 2
        = (cWarmHiNat d : ℝ) ^ 2 * (100000000 * 5000000000) ^ 2 * (√((2 : ℝ) ^ d)) ^ 2 := by ring
      _ = (cWarmHiNat d : ℝ) ^ 2 * (100000000 * 5000000000) ^ 2 * ((2 : ℝ) ^ d) := by
            rw [Real.sq_sqrt h2d_pos.le]
      _ = ((2 : ℝ) ^ d) * (100000000 * 5000000000) * (100000000 * 5000000000) *
            cWarmHiNat d * cWarmHiNat d := by ring
  rw [hrhs_sq]
  linarith [hcast, show ((100000004 * 4091549431 * 785398163398 : ℝ)) ^ 2 =
      (100000004 * 4091549431 * 785398163398 : ℝ) *
        (100000004 * 4091549431 * 785398163398) by ring]
/-- Octant reflection lower bound `π / 4 - arctan ((1 - x) / (1 + x)) ≤ arctan x`
  for `0 ≤ x ≤ 1`. -/
theorem pi_div_four_sub_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    π / 4 - Real.arctan ((1 - x) / (1 + x)) ≤ Real.arctan x := by
  let G : ℝ → ℝ := fun z ↦ -(Real.arctan z + Real.arctan ((1 + (-1 : ℝ) * z) / (1 + z)))
  have hd : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt G 0 z := fun z hz ↦ by
    have hz0 : 0 ≤ z := hz; have h1z : 0 < 1 + z := (by linarith)
    have hnum : HasDerivAt (fun w : ℝ ↦ 1 + (-1 : ℝ) * w) (-1) z :=
      ((hasDerivAt_id' z).const_mul (-1)).const_add 1 |>.congr_deriv (by ring)
    have hden : HasDerivAt (fun w : ℝ ↦ 1 + w) 1 z := (hasDerivAt_id' z).const_add 1
    have hq := hnum.div hden h1z.ne'
    have hcomp := (Real.hasDerivAt_arctan ((1 + (-1 : ℝ) * z) / (1 + z))).comp z hq
    refine (((Real.hasDerivAt_arctan z).add hcomp).neg).congr_deriv ?_
    have hden2 : 0 < 1 + ((1 + (-1 : ℝ) * z) / (1 + z)) ^ 2 := (by positivity)
    have h1z2 : 0 < 1 + z ^ 2 := (by positivity); field_simp [h1z.ne', hden2.ne', h1z2.ne']; ring
  have hcont : ContinuousOn G (Set.Ici 0) := fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Set.Ici (0 : ℝ))) := fun z hz ↦ by
    rw [interior_Ici] at hz; exact (hd z hz.le).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff fun z hz ↦ by
    rw [interior_Ici] at hz; rw [(hd z hz.le).deriv]
  have hle := hmono hx0 (by norm_num : (0 : ℝ) ≤ 1) hx1
  have hG1 : G 1 = -(π / 4) := (by dsimp only [G]; norm_num [Real.arctan_one])
  rw [hG1] at hle; dsimp only [G] at hle
  have hrew : (1 + (-1 : ℝ) * x) / (1 + x) = (1 - x) / (1 + x) := (by ring); rw [hrew] at hle
  linarith
/-- Soundness of `atanRatioLo12`: lower bounds `arctan (p / q)` for `p ≤ q` and `0 < q`. -/
theorem atanRatioLo12_le {p q : ℕ} (hpq : p ≤ q) (hq : 0 < q) :
    (atanRatioLo12 p q : ℝ) / 1000000000000 ≤ Real.arctan ((p : ℝ) / q) := by
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.2 hq; set x : ℝ := (p : ℝ) / q
  have hx0 : 0 ≤ x := (by positivity); unfold atanRatioLo12
  by_cases h12 : 12 * p ≤ 5 * q
  · rw [ite_eq_left h12]; simp only [withForcedNat_eq]
    set pHom : ℕ := p * q * (1155 * (q * q) * (q * q) + 1190 * (p * p) * (q * q) +
      231 * (p * p) * (p * p))
    set qHom : ℕ := 1155 * (q * q) * (q * q) * (q * q) +
      1575 * (p * p) * (q * q) * (q * q) + 525 * (p * p) * (p * p) * (q * q) +
      25 * (p * p) * (p * p) * (p * p)
    have hqHom_pos : 0 < qHom := by
      have hq2 : 0 < q * q := Nat.mul_pos hq hq
      have hq4 : 0 < (q * q) * (q * q) := Nat.mul_pos hq2 hq2
      have hq6 : 0 < 1155 * (q * q) * (q * q) * (q * q) := (by positivity); dsimp only [qHom]; omega
    have hqHom_r : (0 : ℝ) < qHom := Nat.cast_pos.2 hqHom_pos
    have hfl_nat : ((1000000000000 * pHom) / qHom) * qHom ≤ 1000000000000 * pHom :=
      Nat.div_mul_le_self _ _
    have hfl_r : (((1000000000000 * pHom) / qHom : ℕ) : ℝ) * qHom ≤
        1000000000000 * (pHom : ℝ) := by exact_mod_cast hfl_nat
    have hstep1 : (((1000000000000 * pHom) / qHom : ℕ) : ℝ) / 1000000000000 ≤
        (pHom : ℝ) / qHom := by
      rw [div_le_div_iff₀ (by norm_num) hqHom_r]; linarith [hfl_r]
    have hrat : (pHom : ℝ) / qHom = x * (1155 + 1190 * x ^ 2 + 231 * x ^ 4) /
          (1155 + 1575 * x ^ 2 + 525 * x ^ 4 + 25 * x ^ 6) := by
      have hden_x : 0 < 1155 + 1575 * x ^ 2 + 525 * x ^ 4 + 25 * x ^ 6 := (by positivity)
      have hp_eq : (pHom : ℝ) = (p : ℝ) * q *
          (1155 * (q : ℝ) ^ 4 + 1190 * (p : ℝ) ^ 2 * (q : ℝ) ^ 2 + 231 * (p : ℝ) ^ 4) := by
        dsimp only [pHom]; push_cast; ring
      have hq_eq : (qHom : ℝ) = 1155 * (q : ℝ) ^ 6 + 1575 * (p : ℝ) ^ 2 * (q : ℝ) ^ 4 +
          525 * (p : ℝ) ^ 4 * (q : ℝ) ^ 2 + 25 * (p : ℝ) ^ 6 := by
        dsimp only [qHom]; push_cast; ring
      rw [hp_eq, hq_eq]; dsimp only [x]; field_simp [hq_pos.ne', hden_x.ne']
    exact hstep1.trans (hrat.le.trans (pade56_le_arctan hx0))
  · rw [ite_eq_right h12]; simp only [withForcedNat_eq]; set a : ℕ := q - p; set b : ℕ := q + p
    set p54 : ℕ := a * (945 * (b * b) * (b * b) + 735 * (a * a) * (b * b) + 64 * (a * a) * (a * a))
    set q54 : ℕ := b * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b * b) +
      225 * (a * a) * (a * a))
    set padeCeil : ℕ := (1000000000000 * p54 + q54 - 1) / q54
    by_cases hpade : padeCeil ≤ 785398163397
    · have hb_pos_nat : 0 < b := by dsimp only [b]; omega
      have hb_pos : (0 : ℝ) < b := Nat.cast_pos.2 hb_pos_nat
      have hq54_pos_nat : 0 < q54 := by
        have hb2 : 0 < b * b := Nat.mul_pos hb_pos_nat hb_pos_nat
        have hb4 : 0 < (b * b) * (b * b) := Nat.mul_pos hb2 hb2
        have h945 : 0 < 945 * (b * b) * (b * b) := by
          rw [Nat.mul_assoc]; exact Nat.mul_pos (by omega) hb4
        dsimp only [q54]; exact Nat.mul_pos hb_pos_nat (by omega)
      have hq54_pos : (0 : ℝ) < q54 := Nat.cast_pos.2 hq54_pos_nat
      have hx1 : x ≤ 1 := (by dsimp only [x]; rw [div_le_one hq_pos]; exact_mod_cast hpq)
      set y : ℝ := (a : ℝ) / b; have hy0 : 0 ≤ y := (by positivity)
      have ha_sub : (a : ℝ) = (q : ℝ) - p := (by dsimp only [a]; rw [Nat.cast_sub hpq])
      have hb_add : (b : ℝ) = (q : ℝ) + p := (by dsimp only [b]; push_cast; rfl)
      have hy_eq : (1 - x) / (1 + x) = y := by
        dsimp only [x, y]; rw [ha_sub, hb_add]
        have h1x : (1 : ℝ) + (p : ℝ) / q ≠ 0 := (by positivity)
        field_simp [hq_pos.ne', hb_pos.ne', h1x]
      have hceil_nat : 1000000000000 * p54 ≤ padeCeil * q54 := le_ceil_div_mul hq54_pos_nat
      have hceil_r : 1000000000000 * (p54 : ℝ) ≤ (padeCeil : ℝ) * q54 := by exact_mod_cast hceil_nat
      have hpade_ge : (p54 : ℝ) / q54 ≤ (padeCeil : ℝ) / 1000000000000 := by
        rw [div_le_div_iff₀ hq54_pos (by norm_num)]; linarith [hceil_r]
      have hrat : y * (945 + 735 * y ^ 2 + 64 * y ^ 4) / (945 + 1050 * y ^ 2 + 225 * y ^ 4) =
          (p54 : ℝ) / q54 := by
        have hden_y : 0 < 945 + 1050 * y ^ 2 + 225 * y ^ 4 := (by positivity)
        have hp_eq : (p54 : ℝ) = (a : ℝ) *
            (945 * (b : ℝ) ^ 4 + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4) := by
          dsimp only [p54]; push_cast; ring
        have hq_eq : (q54 : ℝ) = (b : ℝ) *
            (945 * (b : ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 225 * (a : ℝ) ^ 4) := by
          dsimp only [q54]; push_cast; ring
        rw [hp_eq, hq_eq]; dsimp only [y]; field_simp [hb_pos.ne', hden_y.ne']
      have hatan_y : Real.arctan y ≤ (padeCeil : ℝ) / 1000000000000 :=
        (arctan_le_pade54 hy0).trans (hrat.le.trans hpade_ge)
      have hpi_lo : (785398163397 : ℝ) / 1000000000000 ≤ π / 4 := (by linarith [Real.pi_gt_d20])
      have hoct := pi_div_four_sub_le_arctan hx0 hx1; rw [hy_eq] at hoct; rw [Nat.cast_sub hpade]
      push_cast; linarith [hoct, hpi_lo, hatan_y]
    · have hzero : 785398163397 - padeCeil = 0 := Nat.sub_eq_zero_of_le (by omega); rw [hzero]
      simp [Real.arctan_nonneg.2 hx0]
/-- Exact rational tangent difference formula for `arctan v - arctan u` when `0 ≤ u ≤ v`. -/
theorem arctan_sub_eq {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) :
    Real.arctan v - Real.arctan u = Real.arctan ((v - u) / (1 + v * u)) := by
  set φv : ℝ := Real.arctan v; set φu : ℝ := Real.arctan u
  have hφu_nn : 0 ≤ φu := Real.arctan_nonneg.2 hu0; have hφ_le : φu ≤ φv := Real.arctan_mono huv
  have hφv_lt : φv < π / 2 := Real.arctan_lt_pi_div_two v
  have hφu_lt : φu < π / 2 := lt_of_le_of_lt hφ_le hφv_lt
  have hdiff_gt : -(π / 2) < φv - φu := (by linarith [Real.pi_pos])
  have hdiff_lt : φv - φu < π / 2 := (by linarith)
  have hcv : 0 < Real.cos φv := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφv_lt⟩
  have hcu : 0 < Real.cos φu := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφu_lt⟩
  have hcd : 0 < Real.cos (φv - φu) := Real.cos_pos_of_mem_Ioo ⟨hdiff_gt, hdiff_lt⟩
  have htan_sub : Real.tan (φv - φu) = (v - u) / (1 + v * u) := by
    have h1 : Real.tan (φv - φu) =
        (Real.tan φv - Real.tan φu) / (1 + Real.tan φv * Real.tan φu) := by
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
        Real.sin_sub, Real.cos_sub]
      have hden_pos : 0 < Real.cos φv * Real.cos φu + Real.sin φv * Real.sin φu := by
        linarith [Real.cos_sub φv φu]
      field_simp [hcv.ne', hcu.ne', hcd.ne', hden_pos.ne']
    rw [h1, Real.tan_arctan, Real.tan_arctan]
  calc φv - φu = Real.arctan (Real.tan (φv - φu)) := (Real.arctan_tan hdiff_gt hdiff_lt).symm
    _ = Real.arctan ((v - u) / (1 + v * u)) := by rw [htan_sub]
/- ## 3. Multi-Click Product Difference, Inflation, & `[0, π / 4]` Concavity + AM-GM -/
theorem prod_nonneg_real {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf0 : ∀ j ∈ s, 0 ≤ f j) : 0 ≤ ∏ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
      rw [Finset.prod_insert hat]
      exact mul_nonneg (hf0 a (Finset.mem_insert_self a t))
        (ih fun j hj ↦ hf0 j (Finset.mem_insert_of_mem hj))
theorem prod_le_prod_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf0 : ∀ j ∈ s, 0 ≤ f j) (hfg : ∀ j ∈ s, f j ≤ g j) :
    (∏ j ∈ s, f j) ≤ ∏ j ∈ s, g j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
      have hf0_t : ∀ j ∈ t, 0 ≤ f j := fun j hj ↦ hf0 j (Finset.mem_insert_of_mem hj)
      have hfg_t : ∀ j ∈ t, f j ≤ g j := fun j hj ↦ hfg j (Finset.mem_insert_of_mem hj)
      have hfa0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a t)
      have hfga : f a ≤ g a := hfg a (Finset.mem_insert_self a t)
      rw [Finset.prod_insert hat, Finset.prod_insert hat]
      exact mul_le_mul hfga (ih hf0_t hfg_t) (prod_nonneg_real t f hf0_t) (hfa0.trans hfga)
theorem sin_two_mul_mono_quarter_pi :
    MonotoneOn (fun w : ℝ ↦ Real.sin (2 * w)) (Set.Icc 0 (π / 4)) := by
  have hd : ∀ w : ℝ, HasDerivAt (fun z : ℝ ↦ Real.sin (2 * z)) (2 * Real.cos (2 * w)) w :=
    fun w ↦ by
      have hlin : HasDerivAt (fun z : ℝ ↦ 2 * z) 2 w :=
        ((hasDerivAt_id' w).const_mul 2).congr_deriv (by ring)
      exact ((Real.hasDerivAt_sin (2 * w)).comp w hlin).congr_deriv (by ring)
  have hcont : ContinuousOn (fun z : ℝ ↦ Real.sin (2 * z)) (Set.Icc 0 (π / 4)) :=
    fun w _ ↦ (hd w).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun z : ℝ ↦ Real.sin (2 * z)) (interior (Set.Icc 0 (π / 4))) :=
    fun w _ ↦ (hd w).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 4)) hcont hdiff fun w hw ↦ ?_
  rw [(hd w).deriv]; rw [interior_Icc] at hw
  have hc : 0 < Real.cos (2 * w) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hw.1], by linarith [hw.2]⟩
  positivity
/-- Tangent upper bound witnessing concavity of `y ↦ 1 - (1 / 2) * sin² y` on `[0, π / 4]`. -/
theorem one_sub_half_sin_sq_le_tangent {a y : ℝ}
    (ha0 : 0 ≤ a) (ha_hi : a ≤ π / 4) (hy0 : 0 ≤ y) (hy_hi : y ≤ π / 4) :
    1 - (1 / 2) * Real.sin y ^ 2 ≤
      1 - (1 / 2) * Real.sin a ^ 2 - Real.sin a * Real.cos a * (y - a) := by
  let H : ℝ → ℝ := fun z ↦
    (1 - (1 / 2) * Real.sin a ^ 2 - Real.sin a * Real.cos a * (z - a)) -
      (1 - (1 / 2) * (Real.sin z * Real.sin z))
  have hd : ∀ z : ℝ, HasDerivAt H ((1 / 2) * (Real.sin (2 * z) - Real.sin (2 * a))) z := fun z ↦ by
    have hlin : HasDerivAt (fun w : ℝ ↦
        1 - (1 / 2) * Real.sin a ^ 2 - Real.sin a * Real.cos a * (w - a))
        (-(Real.sin a * Real.cos a)) z := by
      have hsub : HasDerivAt (fun w : ℝ ↦ w - a) 1 z := (hasDerivAt_id' z).sub_const a
      have hm := hsub.const_mul (Real.sin a * Real.cos a)
      exact (hm.const_sub (1 - (1 / 2) * Real.sin a ^ 2)).congr_deriv (by ring)
    have hquad : HasDerivAt (fun w : ℝ ↦ 1 - (1 / 2) * (Real.sin w * Real.sin w))
        (-(Real.sin z * Real.cos z)) z := by
      have hss := (Real.hasDerivAt_sin z).mul (Real.hasDerivAt_sin z)
      exact ((hss.const_mul (1 / 2)).const_sub 1).congr_deriv (by ring)
    refine (hlin.sub hquad).congr_deriv ?_; rw [Real.sin_two_mul, Real.sin_two_mul]; ring
  have hHa : H a = 0 := (by dsimp only [H]; ring)
  have hHy : 0 ≤ H y := by
    by_cases hay : a ≤ y
    · have hcont : ContinuousOn H (Set.Icc a y) :=
        fun z _ ↦ (hd z).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ H (interior (Set.Icc a y)) :=
        fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt
      have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a y) hcont hdiff fun z hz ↦ by
        rw [(hd z).deriv]; have hz_mem := interior_subset hz
        have hsin_le := sin_two_mul_mono_quarter_pi ⟨ha0, ha_hi⟩
          ⟨ha0.trans hz_mem.1, hz_mem.2.trans hy_hi⟩ hz_mem.1
        linarith
      have hle := hmono ⟨le_rfl, hay⟩ ⟨hay, le_rfl⟩ hay; linarith [hHa]
    · have hya : y ≤ a := le_of_not_ge hay
      have hd_neg : ∀ z : ℝ, HasDerivAt (fun w : ℝ ↦ -H w)
          (-((1 / 2) * (Real.sin (2 * z) - Real.sin (2 * a)))) z := fun z ↦ (hd z).neg
      have hcont : ContinuousOn (fun w : ℝ ↦ -H w) (Set.Icc y a) :=
        fun z _ ↦ (hd_neg z).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ (fun w : ℝ ↦ -H w) (interior (Set.Icc y a)) :=
        fun z _ ↦ (hd_neg z).differentiableAt.differentiableWithinAt
      have hmono := monotoneOn_of_deriv_nonneg (convex_Icc y a) hcont hdiff fun z hz ↦ by
        rw [(hd_neg z).deriv]; have hz_mem := interior_subset hz
        have hsin_le := sin_two_mul_mono_quarter_pi
          ⟨hy0.trans hz_mem.1, hz_mem.2.trans ha_hi⟩ ⟨ha0, ha_hi⟩ hz_mem.2
        linarith
      have hle := hmono ⟨le_rfl, hya⟩ ⟨hya, le_rfl⟩ hya; dsimp only at hle; linarith [hHa]
  dsimp only [H] at hHy; linarith [hHy, show Real.sin y * Real.sin y = Real.sin y ^ 2 by ring]
theorem prod_exp_eq_exp_sum {ι : Type*} (s : Finset ι) (h : ι → ℝ) :
    ∏ j ∈ s, Real.exp (h j) = Real.exp (∑ j ∈ s, h j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih => rw [Finset.prod_insert hat, Finset.sum_insert hat, Real.exp_add, ih]
theorem sum_div_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) (d : ℝ) :
    (∑ j ∈ s, f j / d) = (∑ j ∈ s, f j) / d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih => rw [Finset.sum_insert hat, Finset.sum_insert hat, add_div, ih]
/-- Joint AM-GM + `[0, π / 4]` Jensen inequality on `∏_{j ∈ s} (1 - (1 / 2) sin²(x_j))`. -/
theorem prod_one_sub_half_sin_sq_le_mean_pow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ j ∈ s, 0 ≤ x j) (hx_hi : ∀ j ∈ s, x j ≤ π / 4) :
    ∏ j ∈ s, (1 - (1 / 2) * Real.sin (x j) ^ 2) ≤
      (1 - (1 / 2) * Real.sin ((∑ j ∈ s, x j) / s.card) ^ 2) ^ s.card := by
  classical
  by_cases hs : s.Nonempty
  · set c : ℝ := (s.card : ℝ); have hc_pos : 0 < c := Nat.cast_pos.2 (Finset.Nonempty.card_pos hs)
    set xBar : ℝ := (∑ j ∈ s, x j) / c
    have hxBar0 : 0 ≤ xBar := div_nonneg (Finset.sum_nonneg fun j hj ↦ hx0 j hj) hc_pos.le
    have hxBar_hi : xBar ≤ π / 4 := by
      dsimp only [xBar]; rw [div_le_iff₀ hc_pos]
      have hsum : ∑ j ∈ s, x j ≤ ∑ _j ∈ s, (π / 4) := Finset.sum_le_sum fun j hj ↦ hx_hi j hj
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hsum; exact hsum
    let g : ℝ → ℝ := fun u ↦ 1 - (1 / 2) * Real.sin u ^ 2
    set μ : ℝ := g xBar
    have hμ_pos : 0 < μ := (by dsimp only [μ, g]; linarith [Real.sin_sq_le_one xBar])
    have hg_nn : ∀ j ∈ s, 0 ≤ g (x j) := fun j _ ↦ by
      dsimp only [g]; linarith [Real.sin_sq_le_one (x j)]
    have hterm_le : ∀ j ∈ s, g (x j) ≤ μ * Real.exp (g (x j) / μ - 1) := fun j _ ↦ by
      have hexp := Real.add_one_le_exp (g (x j) / μ - 1)
      have h1 : g (x j) / μ ≤ Real.exp (g (x j) / μ - 1) := (by linarith)
      exact (div_le_iff₀' hμ_pos).1 h1
    have hprod_le : ∏ j ∈ s, g (x j) ≤ ∏ j ∈ s, (μ * Real.exp (g (x j) / μ - 1)) :=
      prod_le_prod_real s (fun j ↦ g (x j)) (fun j ↦ μ * Real.exp (g (x j) / μ - 1)) hg_nn hterm_le
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_exp_eq_exp_sum] at hprod_le
    have hsum_g : ∑ j ∈ s, g (x j) ≤ c * μ := by
      have htan : ∑ j ∈ s, g (x j) ≤ ∑ j ∈ s, (μ - Real.sin xBar * Real.cos xBar * (x j - xBar)) :=
        Finset.sum_le_sum fun j hj ↦
          one_sub_half_sin_sq_le_tangent hxBar0 hxBar_hi (hx0 j hj) (hx_hi j hj)
      have hrhs : ∑ j ∈ s, (μ - Real.sin xBar * Real.cos xBar * (x j - xBar)) = c * μ := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
          Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hcx : (s.card : ℝ) * xBar = ∑ j ∈ s, x j := mul_div_cancel₀ _ hc_pos.ne'
        have hsub0 : (∑ j ∈ s, x j) - (s.card : ℝ) * xBar = 0 := (by linarith)
        rw [hsub0, mul_zero, sub_zero]
      exact htan.trans hrhs.le
    have hexp_arg : ∑ j ∈ s, (g (x j) / μ - 1) ≤ 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, sum_div_real]
      have hdiv : (∑ j ∈ s, g (x j)) / μ ≤ c := (div_le_iff₀ hμ_pos).2 (by linarith [hsum_g])
      dsimp only [c] at hdiv; linarith
    have hexp_le1 : Real.exp (∑ j ∈ s, (g (x j) / μ - 1)) ≤ 1 := Real.exp_le_one_iff.2 hexp_arg
    have hpow_nn : 0 ≤ μ ^ s.card := pow_nonneg hμ_pos.le _; exact hprod_le.trans (by nlinarith)
  · rw [Finset.not_nonempty_iff_eq_empty.1 hs]
    simp
/- ## 4. Soundness of `checkWarmR1Stage2` -/
theorem convex_pow_nonneg {u v lam : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (k : ℕ) :
    ((1 - lam) * u + lam * v) ^ k ≤ (1 - lam) * u ^ k + lam * v ^ k := by
  induction k with
  | zero => simp
  | succ j ih =>
      have h1l : 0 ≤ 1 - lam := (by linarith)
      have hw : 0 ≤ (1 - lam) * u + lam * v := (by positivity)
      have hm := mul_le_mul_of_nonneg_right ih hw
      have hmono : 0 ≤ (u ^ j - v ^ j) * (u - v) := by
        by_cases huv : u ≤ v
        · have hp : u ^ j ≤ v ^ j := pow_le_pow_left₀ hu huv j
          exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        · have hvu : v ≤ u := le_of_not_ge huv; have hp : v ^ j ≤ u ^ j := pow_le_pow_left₀ hv hvu j
          exact mul_nonneg (by linarith) (by linarith)
      have hdiff : 0 ≤ lam * (1 - lam) * ((u ^ j - v ^ j) * (u - v)) :=
        mul_nonneg (mul_nonneg hlam0 h1l) hmono
      rw [pow_succ, pow_succ, pow_succ]
      linarith [hm, hdiff, show ((1 - lam) * (u ^ j * u) + lam * (v ^ j * v)) -
            ((1 - lam) * u ^ j + lam * v ^ j) * ((1 - lam) * u + lam * v) =
          lam * (1 - lam) * ((u ^ j - v ^ j) * (u - v)) by ring]
theorem inv_two_theta2_ge {n : ℕ} {θ2 : ℝ} (hn : 100 ≤ n)
    (hθ2_hi : θ2 ≤ (√(2 : ℝ) / √((2 : ℝ) ^ n)) * (1 + 2 / (2 : ℝ) ^ n)) (hθ2_pos : 0 < θ2) :
    (353553390592 / 1000000000000 : ℝ) * √((2 : ℝ) ^ n) ≤ 1 / (2 * θ2) := by
  have h2_100 : ((2 * (10 : ℝ) ^ 20) : ℝ) ≤ (2 : ℝ) ^ n := by
    calc ((2 * (10 : ℝ) ^ 20) : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hN_pos : (0 : ℝ) < (2 : ℝ) ^ n := (by positivity)
  have hSN_pos : (0 : ℝ) < √((2 : ℝ) ^ n) := Real.sqrt_pos.2 hN_pos
  have hcorr : 1 + 2 / (2 : ℝ) ^ n ≤ ((10 : ℝ) ^ 20 + 1) / ((10 : ℝ) ^ 20) := by
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < (2 * (10 : ℝ) ^ 20)) h2_100
    linarith
  have hθ_ub : 2 * θ2 ≤
      (2 * √(2 : ℝ) * (((10 : ℝ) ^ 20 + 1) / ((10 : ℝ) ^ 20))) / √((2 : ℝ) ^ n) := by
    have hm := mul_le_mul_of_nonneg_left hcorr (by positivity : (0 : ℝ) ≤ √(2 : ℝ) / √((2 : ℝ) ^ n))
    have h2 : 2 * θ2 ≤ 2 * ((√(2 : ℝ) / √((2 : ℝ) ^ n)) *
        (((10 : ℝ) ^ 20 + 1) / ((10 : ℝ) ^ 20))) := by linarith [hθ2_hi, hm]
    exact h2.trans_eq (by ring)
  have hrec := one_div_le_one_div_of_le (by positivity : 0 < 2 * θ2) hθ_ub
  have hrew : 1 /
      ((2 * √(2 : ℝ) * (((10 : ℝ) ^ 20 + 1) / ((10 : ℝ) ^ 20))) / √((2 : ℝ) ^ n)) =
      (((10 : ℝ) ^ 20) / (2 * ((10 : ℝ) ^ 20 + 1) * √(2 : ℝ))) * √((2 : ℝ) ^ n) := by
    have hs2 : √(2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'; field_simp [hs2, hSN_pos.ne']
  rw [hrew] at hrec; refine (mul_le_mul_of_nonneg_right ?_ hSN_pos.le).trans hrec
  have hs2_pos : (0 : ℝ) < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  refine sq_le_imp_le (by positivity) (by norm_num) ?_
  have hsq : (353553390592 * (2 * ((10 : ℝ) ^ 20 + 1) * √(2 : ℝ))) ^ 2 =
      (353553390592 * 2 * ((10 : ℝ) ^ 20 + 1)) ^ 2 * 2 := by
    calc (353553390592 * (2 * ((10 : ℝ) ^ 20 + 1) * √(2 : ℝ))) ^ 2
        = (353553390592 * 2 * ((10 : ℝ) ^ 20 + 1)) ^ 2 * (√(2 : ℝ)) ^ 2 := by ring
      _ = (353553390592 * 2 * ((10 : ℝ) ^ 20 + 1)) ^ 2 * 2 := by rw [Real.sq_sqrt (by norm_num)]
  rw [hsq]; norm_num
theorem atan_sin_cos_identities {tau : ℕ} :
    let b := Real.arctan ((tau : ℝ) / 100000)
    1 - (1 / 2) * Real.sin b ^ 2 =
      (20000000000 + (tau : ℝ) ^ 2) / (2 * (10000000000 + (tau : ℝ) ^ 2)) ∧
      Real.sin b * Real.cos b =
        (100000 * (tau : ℝ)) / (10000000000 + (tau : ℝ) ^ 2) := by
  intro b; set u : ℝ := (tau : ℝ) / 100000
  have hb_nn : 0 ≤ b := Real.arctan_nonneg.2 (by positivity)
  have hb_lt : b < π / 2 := Real.arctan_lt_pi_div_two u
  have hc : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb_lt⟩
  have htan : Real.sin b / Real.cos b = u := by
    rw [← Real.tan_eq_sin_div_cos]; exact Real.tan_arctan u
  have hsin : Real.sin b = u * Real.cos b := (by rw [← htan]; field_simp [hc.ne'])
  have hcos_sq : (1 + u ^ 2) * Real.cos b ^ 2 = 1 := by
    have h1 := Real.sin_sq_add_cos_sq b; rw [hsin] at h1
    linarith [h1, show (u * Real.cos b) ^ 2 + Real.cos b ^ 2 = (1 + u ^ 2) * Real.cos b ^ 2 by ring]
  have hden_pos : (0 : ℝ) < 10000000000 + (tau : ℝ) ^ 2 := (by positivity)
  have h1u_pos : (0 : ℝ) < 1 + u ^ 2 := (by positivity); constructor
  · have hstep : 1 - (1 / 2) * Real.sin b ^ 2 = (2 + u ^ 2) / (2 * (1 + u ^ 2)) := by
      rw [eq_div_iff (by positivity : (2 * (1 + u ^ 2)) ≠ 0), hsin]
      linear_combination -(u ^ 2) * hcos_sq
    rw [hstep]; dsimp only [u]; field_simp [h1u_pos.ne', hden_pos.ne']; ring
  · have hstep : Real.sin b * Real.cos b = u / (1 + u ^ 2) := by
      rw [eq_div_iff h1u_pos.ne', hsin]; linear_combination u * hcos_sq
    rw [hstep]; dsimp only [u]; field_simp [h1u_pos.ne', hden_pos.ne']; ring
attribute [local irreducible]
  mulCeil12 powPredPow2Aux powPredPow2Ceil12 atanRatioLo12 cWarmHiNat
theorem warmR1Cred_le {d n t2 τ : ℕ} {θ2 : ℝ} (ht2 : t2 ≤ 100000) (hτ : τ ≤ t2) (hθ2_pos : 0 < θ2)
    (hinv_th : (353553390592 / 1000000000000 : ℝ) * √((2 : ℝ) ^ n) ≤ 1 / (2 * θ2)) :
    let m : ℕ := 2 ^ d
    ((((m - 1) * atanRatioLo12 ((t2 - τ) * 100000) (10000000000 + t2 * τ) *
      353553390592) / (m * 1000000000000) : ℕ) : ℝ) / 1000000000000 * √((2 : ℝ) ^ n) ≤
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) *
        (Real.arctan ((t2 : ℝ) / 100000) - Real.arctan ((τ : ℝ) / 100000)) / (2 * θ2) := by
  intro m; have hτ_r : (τ : ℝ) ≤ t2 := (by exact_mod_cast hτ)
  have hsub_atan := arctan_sub_eq (by positivity : (0 : ℝ) ≤ (τ : ℝ) / 100000)
    (by linarith : (τ : ℝ) / 100000 ≤ (t2 : ℝ) / 100000)
  have hrat_eq : ((t2 : ℝ) / 100000 - (τ : ℝ) / 100000) /
      (1 + ((t2 : ℝ) / 100000) * ((τ : ℝ) / 100000)) =
      (((t2 - τ) * 100000 : ℕ) : ℝ) / ((10000000000 + t2 * τ : ℕ) : ℝ) := by
    have hd1 : (0 : ℝ) < 1 + ((t2 : ℝ) / 100000) * ((τ : ℝ) / 100000) := (by positivity)
    have hns : (((t2 - τ) * 100000 : ℕ) : ℝ) = ((t2 : ℝ) - τ) * 100000 := by
      rw [Nat.cast_mul, Nat.cast_sub hτ]; norm_num
    have hds : ((10000000000 + t2 * τ : ℕ) : ℝ) = 10000000000 + (t2 : ℝ) * τ := (by push_cast; ring)
    rw [hns, hds]; field_simp [hd1.ne', (by positivity : (10000000000 + (t2 : ℝ) * τ) ≠ 0)]; ring
  have hpq_τ : (t2 - τ) * 100000 ≤ 10000000000 + t2 * τ :=
    (Nat.mul_le_mul_right 100000 (by omega : t2 - τ ≤ 100000)).trans (by omega)
  have hatan_lo := atanRatioLo12_le hpq_τ (by omega); rw [← hrat_eq, ← hsub_atan] at hatan_lo
  set aLo : ℕ := atanRatioLo12 ((t2 - τ) * 100000) (10000000000 + t2 * τ)
  set cr : ℕ := ((m - 1) * aLo * 353553390592) / (m * 1000000000000)
  have hm_pos_nat : 0 < m := Nat.two_pow_pos d
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm_pos_nat
  have hfl := Nat.div_mul_le_self ((m - 1) * aLo * 353553390592) (m * 1000000000000)
  have hfl_r : (cr : ℝ) * ((m : ℝ) * 1000000000000) ≤
      ((m - 1 : ℕ) : ℝ) * (aLo : ℝ) * 353553390592 := by exact_mod_cast hfl
  have hstep1 : (cr : ℝ) / 1000000000000 ≤
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((aLo : ℝ) / 1000000000000) *
        (353553390592 / 1000000000000) := by
    rw [show (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((aLo : ℝ) / 1000000000000) *
          (353553390592 / 1000000000000) =
        (((m - 1 : ℕ) : ℝ) * (aLo : ℝ) * 353553390592) /
          (((m : ℝ) * 1000000000000) * 1000000000000) by field_simp [hm_pos.ne']]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith [hfl_r]
  have hSN_nn : (0 : ℝ) ≤ √((2 : ℝ) ^ n) := Real.sqrt_nonneg _
  have hstep2 : (cr : ℝ) / 1000000000000 * √((2 : ℝ) ^ n) ≤
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((aLo : ℝ) / 1000000000000) * (1 / (2 * θ2)) := by
    calc (cr : ℝ) / 1000000000000 * √((2 : ℝ) ^ n)
        ≤ ((((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((aLo : ℝ) / 1000000000000)) *
            ((353553390592 / 1000000000000 : ℝ) * √((2 : ℝ) ^ n)) := by
          have hm1 := mul_le_mul_of_nonneg_right hstep1 hSN_nn; linarith [hm1]
      _ ≤ ((((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((aLo : ℝ) / 1000000000000)) * (1 / (2 * θ2)) :=
          mul_le_mul_of_nonneg_left hinv_th (by positivity)
  have hstep3 : (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((aLo : ℝ) / 1000000000000) * (1 / (2 * θ2)) ≤
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) *
        (Real.arctan ((t2 : ℝ) / 100000) - Real.arctan ((τ : ℝ) / 100000)) / (2 * θ2) := by
    rw [← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hatan_lo (by positivity)) (by positivity)
  exact hstep2.trans hstep3
theorem convex_endpoint_sub_bound {W C SN lam mc0 mc1 cr0 cr1 wn : ℝ}
    (hSN : 0 ≤ SN) (hlam0 : 0 ≤ lam) (h1lam : 0 ≤ 1 - lam)
    (hwarm : W ≤ ((1 - lam) * (mc0 / 1000000000000) + lam * (mc1 / 1000000000000)) * SN)
    (hcred : ((1 - lam) * (cr0 / 1000000000000) + lam * (cr1 / 1000000000000)) * SN ≤ C)
    (hend0 : mc0 ≤ wn + cr0) (hend1 : mc1 ≤ wn + cr1) :
    W - C ≤ (wn / 1000000000000) * SN := by
  have hc0 : (1 - lam) * ((mc0 - cr0) / 1000000000000) ≤ (1 - lam) * (wn / 1000000000000) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (by norm_num)) h1lam
  have hc1 : lam * ((mc1 - cr1) / 1000000000000) ≤ lam * (wn / 1000000000000) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hlam0
  have hcomb : (1 - lam) * ((mc0 - cr0) / 1000000000000) + lam * ((mc1 - cr1) / 1000000000000) ≤
        wn / 1000000000000 :=
    (add_le_add hc0 hc1).trans_eq (by ring)
  have hcomb_sn := mul_le_mul_of_nonneg_right hcomb hSN
  linarith [hwarm, hcred, hcomb_sn, show ((1 - lam) * ((mc0 - cr0) / 1000000000000) +
        lam * ((mc1 - cr1) / 1000000000000)) * SN =
      ((1 - lam) * (mc0 / 1000000000000) + lam * (mc1 / 1000000000000)) * SN -
        ((1 - lam) * (cr0 / 1000000000000) + lam * (cr1 / 1000000000000)) * SN by ring]
theorem warmR1Seg_sound {d n t2 warmNet s : ℕ} {θ2 xBar : ℝ}
    (hd : d < 11) (hn : 100 ≤ n) (ht2 : t2 ≤ 100000) (hs : s < 32)
    (hθ2_hi : θ2 ≤ (√(2 : ℝ) / √((2 : ℝ) ^ n)) * (1 + 2 / (2 : ℝ) ^ n)) (hθ2_pos : 0 < θ2)
    (hx_lo : Real.arctan ((((s * t2) / 32 : ℕ) : ℝ) / 100000) ≤ xBar)
    (hx_hi : xBar ≤ Real.arctan (((((s + 1) * t2) / 32 : ℕ) : ℝ) / 100000))
    (hseg : checkWarmR1Seg d t2 warmNet s = true) :
    let m : ℕ := 2 ^ d
    (100000004 / 100000000 : ℝ) *
        ((4091549431 / 5000000000 : ℝ) * (π / 4) * √(((2 : ℝ) ^ n) / (m : ℝ))) *
        (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) -
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * (Real.arctan ((t2 : ℝ) / 100000) - xBar) / (2 * θ2) ≤
      ((warmNet : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
  intro m; simp only [checkWarmR1Seg, withForcedNat_eq, Bool.and_eq_true] at hseg
  set tau0 : ℕ := (s * t2) / 32; set tau1 : ℕ := ((s + 1) * t2) / 32
  set den0 : ℕ := 10000000000 + tau0 * tau0
  set g0Hi : ℕ := ((20000000000 + tau0 * tau0) * 1000000000000 + 2 * den0 - 1) / (2 * den0)
  set dbLo : ℕ := atanRatioLo12 ((tau1 - tau0) * 100000) (10000000000 + tau1 * tau0)
  set dropLo : ℕ := (100000 * tau0 * dbLo) / den0; set g1Hi : ℕ := g0Hi - dropLo
  set p0 : ℕ := powPredPow2Ceil12 g0Hi d; set p1 : ℕ := powPredPow2Ceil12 g1Hi d
  set cred0 : ℕ := ((m - 1) * atanRatioLo12 ((t2 - tau0) * 100000) (10000000000 + t2 * tau0) *
      353553390592) / (m * 1000000000000)
  set cred1 : ℕ := ((m - 1) * atanRatioLo12 ((t2 - tau1) * 100000) (10000000000 + t2 * tau1) *
      353553390592) / (m * 1000000000000)
  set cWarm : ℕ := cWarmHiNat d; have hend0 := of_decide_eq_true hseg.1
  have hend1 := of_decide_eq_true hseg.2
  have htau01 : tau0 ≤ tau1 := Nat.div_le_div_right (Nat.mul_le_mul_right t2 (by omega : s ≤ s + 1))
  have htau1_le : tau1 ≤ t2 := by
    have hmul : (s + 1) * t2 ≤ 32 * t2 := Nat.mul_le_mul_right t2 (by omega : s + 1 ≤ 32)
    have h32 : (32 * t2) / 32 = t2 := (by omega); exact (Nat.div_le_div_right hmul).trans_eq h32
  have htau0_le : tau0 ≤ t2 := htau01.trans htau1_le
  set b0 : ℝ := Real.arctan ((tau0 : ℝ) / 100000); set b1 : ℝ := Real.arctan ((tau1 : ℝ) / 100000)
  set φ2 : ℝ := Real.arctan ((t2 : ℝ) / 100000)
  have hb0_nn : 0 ≤ b0 := Real.arctan_nonneg.2 (by positivity)
  have h1_pi4 : Real.arctan 1 = π / 4 := Real.arctan_one
  have hφ2_hi : φ2 ≤ π / 4 := by
    rw [← h1_pi4]; refine Real.arctan_mono ?_
    have ht2_r : (t2 : ℝ) ≤ 100000 := (by exact_mod_cast ht2); linarith
  have hb1_le_φ2 : b1 ≤ φ2 := Real.arctan_mono (by
    have h : (tau1 : ℝ) ≤ t2 := (by exact_mod_cast htau1_le); linarith)
  have hb0_hi : b0 ≤ π / 4 := (hx_lo.trans hx_hi).trans (hb1_le_φ2.trans hφ2_hi)
  have hb1_hi : b1 ≤ π / 4 := hb1_le_φ2.trans hφ2_hi
  have hx_pi4 : xBar ≤ π / 4 := hx_hi.trans hb1_hi; have hx0 : 0 ≤ xBar := hb0_nn.trans hx_lo
  obtain ⟨hg0_eq, hsc0_eq⟩ := atan_sin_cos_identities (tau := tau0)
  have hden0_pos_nat : 0 < den0 := (by dsimp only [den0]; omega)
  have hden0_pos : (0 : ℝ) < den0 := Nat.cast_pos.2 hden0_pos_nat
  have hden0_eq : (den0 : ℝ) = 10000000000 + (tau0 : ℝ) ^ 2 := by dsimp only [den0]; push_cast; ring
  have hg0_le : 1 - (1 / 2) * Real.sin b0 ^ 2 ≤ (g0Hi : ℝ) / 1000000000000 := by
    rw [hg0_eq, ← hden0_eq]
    have hceil := le_ceil_div_mul (a := (20000000000 + tau0 * tau0) * 1000000000000)
      (b := 2 * den0) (by omega)
    have hcast : ((20000000000 + (tau0 : ℝ) ^ 2) * 1000000000000) ≤ (g0Hi : ℝ) * (2 * den0) := by
      have hraw : ((20000000000 + (tau0 : ℝ) * tau0) * 1000000000000) ≤
          (g0Hi : ℝ) * (2 * den0) := by exact_mod_cast hceil
      linarith [hraw, show (tau0 : ℝ) ^ 2 = (tau0 : ℝ) * tau0 by ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hcast]
  have hinv_th : (353553390592 / 1000000000000 : ℝ) * √((2 : ℝ) ^ n) ≤ 1 / (2 * θ2) :=
    inv_two_theta2_ge hn hθ2_hi hθ2_pos
  have hcred0 := warmR1Cred_le (d := d) ht2 htau0_le hθ2_pos hinv_th
  have hcred1 := warmR1Cred_le (d := d) ht2 htau1_le hθ2_pos hinv_th
  have hm_eq : (m : ℝ) = (2 : ℝ) ^ d := (by dsimp only [m]; push_cast; rfl)
  have hSN_pos : (0 : ℝ) < √((2 : ℝ) ^ n) := Real.sqrt_pos.2 (by positivity)
  have hcWarm_le : (100000004 / 100000000 : ℝ) *
        ((4091549431 / 5000000000 : ℝ) * (π / 4) * √(((2 : ℝ) ^ n) / (m : ℝ))) ≤
        ((cWarm : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n), hm_eq]
    have hc := cWarmHiNat_sound hd; have hm := mul_le_mul_of_nonneg_right hc hSN_pos.le
    have hs2d : √((2 : ℝ) ^ d) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    refine (le_of_eq ?_).trans hm; field_simp [hs2d]
  have hg_nn : 0 ≤ 1 - (1 / 2) * Real.sin xBar ^ 2 := (by linarith [Real.sin_sq_le_one xBar])
  by_cases hb_eq : b0 = b1
  · have hx_eq : xBar = b0 := by linarith [hx_lo, hx_hi, hb_eq]
    rw [hx_eq]
    have hp0_le : (1 - (1 / 2) * Real.sin b0 ^ 2) ^ (m - 1) ≤ (p0 : ℝ) / 1000000000000 :=
      powPredPow2Ceil12_sound (by rw [← hx_eq]; exact hg_nn) hg0_le
    have hwarm0 : (100000004 / 100000000 : ℝ) *
          ((4091549431 / 5000000000 : ℝ) * (π / 4) * √(((2 : ℝ) ^ n) / (m : ℝ))) *
          (1 - (1 / 2) * Real.sin b0 ^ 2) ^ (m - 1) ≤
        ((mulCeil12 cWarm p0 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
      have hm1 := mul_le_mul hcWarm_le hp0_le (pow_nonneg (by rw [← hx_eq]; exact hg_nn) _)
        (by positivity)
      have hm2 := mul_le_mul_of_nonneg_right (le_mulCeil12 (x := cWarm) (y := p0)) hSN_pos.le
      linarith [hm1, hm2,
        show (((cWarm : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)) * ((p0 : ℝ) / 1000000000000) =
          (((cWarm : ℝ) / 1000000000000) * ((p0 : ℝ) / 1000000000000)) * √((2 : ℝ) ^ n) by ring]
    have hend0_r : (mulCeil12 cWarm p0 : ℝ) ≤ (warmNet : ℝ) + cred0 := (by exact_mod_cast hend0)
    have hdiff_r : ((mulCeil12 cWarm p0 : ℝ) - cred0) / 1000000000000 * √((2 : ℝ) ^ n) ≤
        ((warmNet : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hSN_pos.le
    linarith [hwarm0, hcred0, hdiff_r,
      show ((mulCeil12 cWarm p0 : ℝ) - cred0) / 1000000000000 * √((2 : ℝ) ^ n) =
        ((mulCeil12 cWarm p0 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) -
          (cred0 : ℝ) / 1000000000000 * √((2 : ℝ) ^ n) by ring]
  · have hb_lt : b0 < b1 := lt_of_le_of_ne (hx_lo.trans hx_hi) hb_eq
    have hb_diff_pos : 0 < b1 - b0 := sub_pos.2 hb_lt; set lam : ℝ := (xBar - b0) / (b1 - b0)
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hb_diff_pos.le
    have hlam1 : lam ≤ 1 := (div_le_one hb_diff_pos).2 (by linarith)
    have h1lam : 0 ≤ 1 - lam := (by linarith)
    have hx_sub : xBar - b0 = lam * (b1 - b0) := div_mul_cancel₀ _ hb_diff_pos.ne' |>.symm
    have hdb_lo : (dbLo : ℝ) / 1000000000000 ≤ b1 - b0 := by
      have htau01_r : (tau0 : ℝ) ≤ tau1 := (by exact_mod_cast htau01)
      have hsub_b := arctan_sub_eq (by positivity : (0 : ℝ) ≤ (tau0 : ℝ) / 100000)
        (by linarith : (tau0 : ℝ) / 100000 ≤ (tau1 : ℝ) / 100000)
      have hrat_b : ((tau1 : ℝ) / 100000 - (tau0 : ℝ) / 100000) /
          (1 + ((tau1 : ℝ) / 100000) * ((tau0 : ℝ) / 100000)) =
          (((tau1 - tau0) * 100000 : ℕ) : ℝ) / ((10000000000 + tau1 * tau0 : ℕ) : ℝ) := by
        have hd1 : (0 : ℝ) < 1 + ((tau1 : ℝ) / 100000) * ((tau0 : ℝ) / 100000) := (by positivity)
        have hns : (((tau1 - tau0) * 100000 : ℕ) : ℝ) = ((tau1 : ℝ) - tau0) * 100000 := by
          rw [Nat.cast_mul, Nat.cast_sub htau01]; norm_num
        have hds : ((10000000000 + tau1 * tau0 : ℕ) : ℝ) = 10000000000 + (tau1 : ℝ) * tau0 := by
          push_cast; ring
        rw [hns, hds]; field_simp [hd1.ne', (by positivity : (10000000000 + (tau1 : ℝ) * tau0) ≠ 0)]
        ring
      have hpq_b : (tau1 - tau0) * 100000 ≤ 10000000000 + tau1 * tau0 :=
        (Nat.mul_le_mul_right 100000 (by omega : tau1 - tau0 ≤ 100000)).trans (by omega)
      have hlo := atanRatioLo12_le hpq_b (by omega); dsimp only [b0, b1, dbLo] at hsub_b hlo ⊢
      rw [hsub_b, hrat_b]; exact hlo
    have hdrop_lo : (dropLo : ℝ) / 1000000000000 ≤ Real.sin b0 * Real.cos b0 * (b1 - b0) := by
      rw [hsc0_eq, ← hden0_eq]; have hfl := Nat.div_mul_le_self (100000 * tau0 * dbLo) den0
      have hfl_r : (dropLo : ℝ) * den0 ≤ 100000 * (tau0 : ℝ) * dbLo := (by exact_mod_cast hfl)
      have hstep1 : (dropLo : ℝ) / 1000000000000 ≤
          ((100000 * (tau0 : ℝ)) / den0) * ((dbLo : ℝ) / 1000000000000) := by
        rw [show ((100000 * (tau0 : ℝ)) / den0) * ((dbLo : ℝ) / 1000000000000) =
            (100000 * (tau0 : ℝ) * dbLo) / ((den0 : ℝ) * 1000000000000) by
              field_simp [hden0_pos.ne']]
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith [hfl_r]
      exact hstep1.trans (mul_le_mul_of_nonneg_left hdb_lo (by positivity))
    have hdrop_le_g0 : dropLo ≤ g0Hi := by
      have htan_b1 := one_sub_half_sin_sq_le_tangent hb0_nn hb0_hi (hb0_nn.trans hb_lt.le) hb1_hi
      have hb1_nn : 0 ≤ 1 - (1 / 2) * Real.sin b1 ^ 2 := (by linarith [Real.sin_sq_le_one b1])
      have hdiff_nn : (dropLo : ℝ) / 1000000000000 ≤ (g0Hi : ℝ) / 1000000000000 := by
        linarith [hb1_nn, htan_b1, hg0_le, hdrop_lo]
      have hr : (dropLo : ℝ) ≤ g0Hi := (by linarith); exact_mod_cast hr
    have hg1_cast : (g1Hi : ℝ) = (g0Hi : ℝ) - dropLo := by
      dsimp only [g1Hi]; rw [Nat.cast_sub hdrop_le_g0]
    have hgx_le : 1 - (1 / 2) * Real.sin xBar ^ 2 ≤
        (1 - lam) * ((g0Hi : ℝ) / 1000000000000) + lam * ((g1Hi : ℝ) / 1000000000000) := by
      have htan_x := one_sub_half_sin_sq_le_tangent hb0_nn hb0_hi hx0 hx_pi4; rw [hx_sub] at htan_x
      have hm_drop : lam * ((dropLo : ℝ) / 1000000000000) ≤
          Real.sin b0 * Real.cos b0 * (lam * (b1 - b0)) := by
        have hm := mul_le_mul_of_nonneg_left hdrop_lo hlam0; linarith [hm]
      rw [hg1_cast]
      linarith [htan_x, hg0_le, hm_drop,
        show (g0Hi : ℝ) / 1000000000000 - lam * ((dropLo : ℝ) / 1000000000000) =
          (1 - lam) * ((g0Hi : ℝ) / 1000000000000) +
            lam * (((g0Hi : ℝ) - dropLo) / 1000000000000) by ring]
    have hpow_conv : (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) ≤
          (1 - lam) * ((p0 : ℝ) / 1000000000000) + lam * ((p1 : ℝ) / 1000000000000) := by
      have hp_mono := pow_le_pow_left₀ hg_nn hgx_le (m - 1)
      have hp_cvx := convex_pow_nonneg (by positivity : 0 ≤ (g0Hi : ℝ) / 1000000000000)
        (by positivity : 0 ≤ (g1Hi : ℝ) / 1000000000000) hlam0 hlam1 (m - 1)
      have hp0_b : ((g0Hi : ℝ) / 1000000000000) ^ (m - 1) ≤ (p0 : ℝ) / 1000000000000 :=
        powPredPow2Ceil12_sound (by positivity) le_rfl
      have hp1_b : ((g1Hi : ℝ) / 1000000000000) ^ (m - 1) ≤ (p1 : ℝ) / 1000000000000 :=
        powPredPow2Ceil12_sound (by positivity) le_rfl
      exact hp_mono.trans (hp_cvx.trans (add_le_add
        (mul_le_mul_of_nonneg_left hp0_b h1lam) (mul_le_mul_of_nonneg_left hp1_b hlam0)))
    have hwarm_x : (100000004 / 100000000 : ℝ) *
          ((4091549431 / 5000000000 : ℝ) * (π / 4) * √(((2 : ℝ) ^ n) / (m : ℝ))) *
          (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) ≤
        ((1 - lam) * ((mulCeil12 cWarm p0 : ℝ) / 1000000000000) +
          lam * ((mulCeil12 cWarm p1 : ℝ) / 1000000000000)) * √((2 : ℝ) ^ n) := by
      have hm1 := mul_le_mul hcWarm_le hpow_conv (pow_nonneg hg_nn _) (by positivity)
      have hc0 := mul_le_mul_of_nonneg_left (le_mulCeil12 (x := cWarm) (y := p0)) h1lam
      have hc1 := mul_le_mul_of_nonneg_left (le_mulCeil12 (x := cWarm) (y := p1)) hlam0
      have hcs := mul_le_mul_of_nonneg_right (add_le_add hc0 hc1) hSN_pos.le
      linarith [hm1, hcs, show (((cWarm : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)) *
            ((1 - lam) * ((p0 : ℝ) / 1000000000000) + lam * ((p1 : ℝ) / 1000000000000)) =
          ((1 - lam) * (((cWarm : ℝ) / 1000000000000) * ((p0 : ℝ) / 1000000000000)) +
            lam * (((cWarm : ℝ) / 1000000000000) * ((p1 : ℝ) / 1000000000000))) *
            √((2 : ℝ) ^ n) by ring]
    have hcred_x : ((1 - lam) * ((cred0 : ℝ) / 1000000000000) +
          lam * ((cred1 : ℝ) / 1000000000000)) * √((2 : ℝ) ^ n) ≤
        (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * (φ2 - xBar) / (2 * θ2) := by
      have hphi_lin : φ2 - xBar = (1 - lam) * (φ2 - b0) + lam * (φ2 - b1) := (by linarith [hx_sub])
      have hm0 := mul_le_mul_of_nonneg_left hcred0 h1lam
      have hm1 := mul_le_mul_of_nonneg_left hcred1 hlam0; rw [hphi_lin]
      linarith [hm0, hm1, show (1 - lam) * ((((m - 1 : ℕ) : ℝ) / (m : ℝ)) * (φ2 - b0) / (2 * θ2)) +
            lam * ((((m - 1 : ℕ) : ℝ) / (m : ℝ)) * (φ2 - b1) / (2 * θ2)) =
          (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * ((1 - lam) * (φ2 - b0) + lam * (φ2 - b1)) /
            (2 * θ2) by ring,
        show ((1 - lam) * ((cred0 : ℝ) / 1000000000000) +
            lam * ((cred1 : ℝ) / 1000000000000)) * √((2 : ℝ) ^ n) =
          (1 - lam) * ((cred0 : ℝ) / 1000000000000 * √((2 : ℝ) ^ n)) +
            lam * ((cred1 : ℝ) / 1000000000000 * √((2 : ℝ) ^ n)) by ring]
    exact convex_endpoint_sub_bound hSN_pos.le hlam0 h1lam hwarm_x hcred_x
      (by exact_mod_cast hend0) (by exact_mod_cast hend1)
theorem exists_seg_of_le {t2 K : ℕ} {xBar : ℝ} (hx0 : 0 ≤ xBar)
    (hx_hi : xBar ≤ Real.arctan (((((K + 1) * t2) / 32 : ℕ) : ℝ) / 100000)) :
    ∃ s < K + 1, Real.arctan ((((s * t2) / 32 : ℕ) : ℝ) / 100000) ≤ xBar ∧
        xBar ≤ Real.arctan (((((s + 1) * t2) / 32 : ℕ) : ℝ) / 100000) := by
  induction K with
  | zero => refine ⟨0, by omega, ?_, hx_hi⟩; simpa using hx0
  | succ j ih =>
      by_cases hmid : xBar ≤ Real.arctan (((((j + 1) * t2) / 32 : ℕ) : ℝ) / 100000)
      · obtain ⟨s, hs, h0, h1⟩ := ih hmid; exact ⟨s, by omega, h0, h1⟩
      · exact ⟨j + 1, by omega, le_of_not_ge hmid, hx_hi⟩
/-- Master soundness theorem for `checkWarmR1Stage2`: bounds the `r = 2 → 1` stage
  transition
  cost at any mean locked angle `xBar ∈ [0, arctan(t2 / 10^5)]` for `n ≥ 100`. -/
theorem warmR1Stage2_sound {d n : ℕ} {rw2 : FuseStageRow} {θ2 xBar : ℝ} (hn : 100 ≤ n)
    (hθ2_hi : θ2 ≤ (√(2 : ℝ) / √((2 : ℝ) ^ n)) * (1 + 2 / (2 : ℝ) ^ n)) (hθ2_pos : 0 < θ2)
    (hx0 : 0 ≤ xBar) (hx_hi : xBar ≤ Real.arctan ((rw2.tNum : ℝ) / 100000))
    (hchk : checkWarmR1Stage2 d rw2 = true) :
    let m : ℕ := 2 ^ d
    1 / ((m : ℝ) * (4 * ((rw2.tNum : ℝ) / 100000) * (99999999 / 100000000) * √(2 : ℝ) /
          √((2 : ℝ) ^ n)) *
        (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) +
      1 + (100000004 / 100000000) *
        ((4091549431 / 5000000000 : ℝ) * (π / 4) * √(((2 : ℝ) ^ n) / (m : ℝ))) *
        (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) -
      (((m - 1 : ℕ) : ℝ) / (m : ℝ)) * (Real.arctan ((rw2.tNum : ℝ) / 100000) - xBar) / (2 * θ2) ≤
      ((rw2.v : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
  rcases rw2 with ⟨v2, t2, phiHi2, tBf2, td2, numU2, stepNum2, cNat2, uNat2⟩; dsimp only at hx_hi ⊢
  simp only [checkWarmR1Stage2, withForcedNat_eq, Bool.and_eq_true] at hchk
  have hd : d < 11 := of_decide_eq_true hchk.1.1.1.1.1.1
  have ht2_lo : 500 ≤ t2 := of_decide_eq_true hchk.1.1.1.1.1.2
  have ht2_hi : t2 ≤ 100000 := of_decide_eq_true hchk.1.1.1.1.2
  have hclick : checkClickRow (2 ^ d) 2 t2 stepNum2 = true := hchk.1.1.2
  have hv_ge : stepNum2 + 1 ≤ v2 := of_decide_eq_true hchk.1.2; have hall := hchk.2
  set m : ℕ := 2 ^ d
  have hclick_le : 1 / ((m : ℝ) * (4 * ((t2 : ℝ) / 100000) * (99999999 / 100000000) * √(2 : ℝ) /
          √((2 : ℝ) ^ n)) *
        (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) ≤
      ((stepNum2 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
    have hraw := clickRow_sound (n := n) Nat.one_le_two_pow (by omega : 1 ≤ 2) ht2_lo hclick
    simpa only [m, Nat.cast_ofNat] using hraw
  have h1_le : (1 : ℝ) ≤ (1 / 1000000000000) * √((2 : ℝ) ^ n) := by
    have hSN_ge : (1000000000000 : ℝ) ≤ √((2 : ℝ) ^ n) := by
      refine sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _) ?_; rw [Real.sq_sqrt (by positivity)]
      calc (1000000000000 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 100 := by norm_num
        _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    linarith
  have hx_32 : xBar ≤ Real.arctan (((((31 + 1) * t2) / 32 : ℕ) : ℝ) / 100000) := by
    simpa [Nat.mul_div_right t2 (by positivity : 0 < 32)] using hx_hi
  obtain ⟨s, hs, hx_s0, hx_s1⟩ := exists_seg_of_le hx0 hx_32; have hseg := of_allRange hall hs
  have hwarm_seg := warmR1Seg_sound hd hn ht2_hi hs hθ2_hi hθ2_pos hx_s0 hx_s1 hseg
  have hv_sum : (stepNum2 : ℝ) + 1 + ((v2 - stepNum2 - 1 : ℕ) : ℝ) = (v2 : ℝ) := by
    have hnat : stepNum2 + 1 + (v2 - stepNum2 - 1) = v2 := (by omega); exact_mod_cast hnat
  linarith [hclick_le, h1_le, hwarm_seg, show ((stepNum2 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) +
        (1 / 1000000000000) * √((2 : ℝ) ^ n) +
        (((v2 - stepNum2 - 1 : ℕ) : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) =
      (((stepNum2 : ℝ) + 1 + ((v2 - stepNum2 - 1 : ℕ) : ℝ)) / 1000000000000) *
        √((2 : ℝ) ^ n) by ring,
    congrArg (fun z : ℝ ↦ (z / 1000000000000) * √((2 : ℝ) ^ n)) hv_sum]
end QuantumComputation.Specs.GroverFindAll.PipeFuseWarmR1Cert
end Sec_PipelinedFuseWarmR1CertDefs
section Sec_PipelinedFusePot
namespace QuantumComputation.Specs.GroverFindAll

open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal NNRat ENNReal QHLExpectation
namespace PipeFuse
open PipeFuseCert
  (FuseStageRow checkFuseCellRow checkFuseStageIdx checkFuseDriftCert checkOctantAtan checkClickRow
   of_allRange octantAtan_sound fuseDriftCert_sound clickRow_sound
   harmSumPow2_le_sum sqrtMUpNat_bounds harmSumPow2 sqrtMUpNat)
/-- Map `2 ^ idx` (`idx ≤ 10`) to `idx`, or `11` if not a grid power of two. -/
def gridIdx (x : ℕ) : ℕ :=
  if x == 1 then 0
  else if x == 2 then 1
  else if x == 4 then 2
  else if x == 8 then 3
  else if x == 16 then 4
  else if x == 32 then 5
  else if x == 64 then 6
  else if x == 128 then 7
  else if x == 256 then 8
  else if x == 512 then 9
  else if x == 1024 then 10
  else 11
theorem gridIdx_pow_two {idx : ℕ} (h : idx < 11) : gridIdx (2 ^ idx) = idx := by
  have hcases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨
      idx = 6 ∨ idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
/-- Certified stage threshold function `phiFnOfFuseRow row r = arctan ((row r).tNum /
  100000)`. -/
noncomputable def phiFnOfFuseRow (row : ℕ → FuseStageRow) (r : ℕ) : ℝ :=
  Real.arctan (((row r).tNum : ℝ) / 100000)
/-- Certified stage base potential `vFnOfFuseRow row n r = ((row r).v / 10^12) * √(2 ^ n)`. -/
noncomputable def vFnOfFuseRow (row : ℕ → FuseStageRow) (n r : ℕ) : ℝ :=
  (((row r).v : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)
/-- Certified `(phiFn, Φ)` witness bundle for coherent peer-fusion cell `(d, kIdx)` at cost
  `rcNum / 10^10` for all `n ≥ 100`. -/
def CertifiedFuseCell (d kIdx rcNum : ℕ) (phiFn : ℕ → ℝ) : Prop :=
  ∀ n ≥ 100,
    ∃ Φ : ℕ → (Fin (2 ^ d) → ℝ) → ℝ,
      ValidPipelinedFusePotential (m := 2 ^ d) phiFn (fun _ ↦ π / 3) n (2 ^ kIdx) Φ ∧
      Φ (2 ^ kIdx) (fun _ : Fin (2 ^ d) ↦ halfAngleSet n (2 ^ kIdx)) ≤
        (((rcNum : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) *
            √((2 ^ n : ℝ) / (2 ^ d : ℕ)))
end PipeFuse
end QuantumComputation.Specs.GroverFindAll
end Sec_PipelinedFusePot
section Sec_PipelinedFuseWarmR1Pot
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal NNRat ENNReal QHLExpectation
namespace PipeFuse
/- ## 1. Multi-Click Product Difference & Zero-Penalty Locked-Slot Majorization -/
theorem prod_add_sub_prod_mono {ι : Type*} (s : Finset ι) (p g G c : ι → ℝ)
    (hp0 : ∀ j ∈ s, 0 ≤ p j) (hp1 : ∀ j ∈ s, p j ≤ 1)
    (hg0 : ∀ j ∈ s, 0 ≤ g j) (hgG : ∀ j ∈ s, g j ≤ G j)
    (hc0 : ∀ j ∈ s, 0 ≤ c j) (hc1 : ∀ j ∈ s, c j ≤ 1) :
    (∏ j ∈ s, ((1 - p j) * g j + p j * c j)) - (∏ j ∈ s, (1 - p j)) * (∏ j ∈ s, g j) ≤
      (∏ j ∈ s, ((1 - p j) * G j + p j)) - (∏ j ∈ s, (1 - p j)) * (∏ j ∈ s, G j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hp0a : 0 ≤ p a := hp0 a (Finset.mem_insert_self a s)
      have hp1a : p a ≤ 1 := hp1 a (Finset.mem_insert_self a s)
      have hg0a : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
      have hgGa : g a ≤ G a := hgG a (Finset.mem_insert_self a s)
      have hc0a : 0 ≤ c a := hc0 a (Finset.mem_insert_self a s)
      have hc1a : c a ≤ 1 := hc1 a (Finset.mem_insert_self a s)
      have hp0s : ∀ j ∈ s, 0 ≤ p j := fun j hj ↦ hp0 j (Finset.mem_insert_of_mem hj)
      have hp1s : ∀ j ∈ s, p j ≤ 1 := fun j hj ↦ hp1 j (Finset.mem_insert_of_mem hj)
      have hg0s : ∀ j ∈ s, 0 ≤ g j := fun j hj ↦ hg0 j (Finset.mem_insert_of_mem hj)
      have hgGs : ∀ j ∈ s, g j ≤ G j := fun j hj ↦ hgG j (Finset.mem_insert_of_mem hj)
      have hc0s : ∀ j ∈ s, 0 ≤ c j := fun j hj ↦ hc0 j (Finset.mem_insert_of_mem hj)
      have hc1s : ∀ j ∈ s, c j ≤ 1 := fun j hj ↦ hc1 j (Finset.mem_insert_of_mem hj)
      have hih := ih hp0s hp1s hg0s hgGs hc0s hc1s
      set Ag := ∏ j ∈ s, ((1 - p j) * g j + p j * c j); set AG := ∏ j ∈ s, ((1 - p j) * G j + p j)
      set Q := ∏ j ∈ s, (1 - p j); set Pg := ∏ j ∈ s, g j
      set PG := ∏ j ∈ s, G j
      have hAg_nn : 0 ≤ Ag := Finset.prod_nonneg fun j hj ↦
        add_nonneg (mul_nonneg (sub_nonneg.2 (hp1s j hj)) (hg0s j hj))
          (mul_nonneg (hp0s j hj) (hc0s j hj))
      have hAg_le_AG : Ag ≤ AG := PipeFuseWarmR1Cert.prod_le_prod_real s
        (fun j ↦ (1 - p j) * g j + p j * c j) (fun j ↦ (1 - p j) * G j + p j)
        (fun j hj ↦ add_nonneg (mul_nonneg (sub_nonneg.2 (hp1s j hj)) (hg0s j hj))
          (mul_nonneg (hp0s j hj) (hc0s j hj)))
        (fun j hj ↦ add_le_add
          (mul_le_mul_of_nonneg_left (hgGs j hj) (sub_nonneg.2 (hp1s j hj)))
          (by nlinarith [hp0s j hj, hc1s j hj]))
      have hDg_nn : 0 ≤ Ag - Q * Pg := by
        have hqp : Q * Pg = ∏ j ∈ s, ((1 - p j) * g j) := (Finset.prod_mul_distrib).symm
        rw [hqp]; exact sub_nonneg.2 (PipeFuseWarmR1Cert.prod_le_prod_real s
          (fun j ↦ (1 - p j) * g j) (fun j ↦ (1 - p j) * g j + p j * c j)
          (fun j hj ↦ mul_nonneg (sub_nonneg.2 (hp1s j hj)) (hg0s j hj))
          (fun j hj ↦ by linarith [mul_nonneg (hp0s j hj) (hc0s j hj)]))
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.prod_insert ha, Finset.prod_insert ha]
      have hid1 : ((1 - p a) * g a + p a * c a) * Ag - ((1 - p a) * Q) * (g a * Pg) =
          (1 - p a) * g a * (Ag - Q * Pg) + p a * c a * Ag := by ring
      have hid2 : ((1 - p a) * G a + p a) * AG - ((1 - p a) * Q) * (G a * PG) =
          (1 - p a) * G a * (AG - Q * PG) + p a * AG := by ring
      rw [hid1, hid2]
      have ht1 : (1 - p a) * g a * (Ag - Q * Pg) ≤ (1 - p a) * G a * (AG - Q * PG) := by
        have hm1 : (1 - p a) * g a ≤ (1 - p a) * G a :=
          mul_le_mul_of_nonneg_left hgGa (sub_nonneg.2 hp1a)
        exact mul_le_mul hm1 hih hDg_nn (mul_nonneg (sub_nonneg.2 hp1a) (hg0a.trans hgGa))
      have ht2 : p a * c a * Ag ≤ p a * AG := by
        have hm2 : p a * c a ≤ p a := by nlinarith
        exact mul_le_mul hm2 hAg_le_AG hAg_nn hp0a
      linarith
theorem prod_lock_mix_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) {G : ℝ}
    (hG_lo : 2 / 3 ≤ G) (hG_hi : G ≤ 1)
    (hp0 : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j ≤ 1) :
    ∏ j ∈ s, ((1 - p j) * G + p j) ≤ G ^ s.card * (1 + ∑ j ∈ s, p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hp0a : 0 ≤ p a := hp0 a (Finset.mem_insert_self a s)
      have hp0s : ∀ j ∈ s, 0 ≤ p j := fun j hj ↦ hp0 j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert ha] at hsum ⊢; set S := ∑ j ∈ s, p j
      have hS_nn : 0 ≤ S := Finset.sum_nonneg hp0s
      have hS_le1 : S ≤ 1 := by linarith
      have hpa_le1 : p a ≤ 1 := by linarith
      have hih := ih hp0s hS_le1
      have hG_nn : 0 ≤ G := by linarith
      have hmix_nn : 0 ≤ (1 - p a) * G + p a :=
        add_nonneg (mul_nonneg (sub_nonneg.2 hpa_le1) hG_nn) hp0a
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      have hstep1 : ((1 - p a) * G + p a) * (∏ j ∈ s, ((1 - p j) * G + p j)) ≤
          G ^ s.card * (((1 - p a) * G + p a) * (1 + S)) := by
        have hm := mul_le_mul_of_nonneg_left hih hmix_nn
        linarith [hm,
          show ((1 - p a) * G + p a) * (G ^ s.card * (1 + S)) =
            G ^ s.card * (((1 - p a) * G + p a) * (1 + S)) by ring]
      have hstep2 : ((1 - p a) * G + p a) * (1 + S) ≤ G * (1 + (p a + S)) := by
        have hdiff : G * (1 + (p a + S)) - ((1 - p a) * G + p a) * (1 + S) =
            p a * (3 * G - 2) + p a * ((1 - G) * (1 - S)) := by ring
        have h1 : 0 ≤ p a * (3 * G - 2) := mul_nonneg hp0a (by linarith)
        have h2 : 0 ≤ p a * ((1 - G) * (1 - S)) :=
          mul_nonneg hp0a (mul_nonneg (by linarith) (by linarith))
        linarith
      exact hstep1.trans (by
        have hm := mul_le_mul_of_nonneg_left hstep2 (pow_nonneg hG_nn s.card)
        linarith [hm, show G ^ s.card * (G * (1 + (p a + S))) =
          G * G ^ s.card * (1 + (p a + S)) by ring])
theorem mul_prod_lock_mix_sub_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) {G : ℝ}
    (hG_lo : 2 / 3 ≤ G) (hG_hi : G ≤ 1)
    (hp0 : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j ≤ 1) :
    G * ((∏ j ∈ s, ((1 - p j) * G + p j)) - (∏ j ∈ s, (1 - p j)) * G ^ s.card) ≤
      G ^ s.card * (∑ j ∈ s, p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hp0a : 0 ≤ p a := hp0 a (Finset.mem_insert_self a s)
      have hp0s : ∀ j ∈ s, 0 ≤ p j := fun j hj ↦ hp0 j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert ha] at hsum ⊢; set S := ∑ j ∈ s, p j
      have hS_nn : 0 ≤ S := Finset.sum_nonneg hp0s
      have hS_le1 : S ≤ 1 := by linarith
      have hpa_le1 : p a ≤ 1 := by linarith
      have hG_nn : 0 ≤ G := by linarith
      have hih := ih hp0s hS_le1
      have hA_le := prod_lock_mix_le s p hG_lo hG_hi hp0s hS_le1
      set A := ∏ j ∈ s, ((1 - p j) * G + p j); set Q := ∏ j ∈ s, (1 - p j)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      have hid : G * (((1 - p a) * G + p a) * A - ((1 - p a) * Q) * (G * G ^ s.card)) =
          (1 - p a) * G * (G * (A - Q * G ^ s.card)) + p a * G * A := by ring
      rw [hid]; have ht1 : (1 - p a) * G * (G * (A - Q * G ^ s.card)) ≤
          (1 - p a) * G * (G ^ s.card * S) :=
        mul_le_mul_of_nonneg_left hih (mul_nonneg (sub_nonneg.2 hpa_le1) hG_nn)
      have ht2 : p a * G * A ≤ p a * G * (G ^ s.card * (1 + S)) :=
        mul_le_mul_of_nonneg_left hA_le (mul_nonneg hp0a hG_nn)
      linarith [ht1, ht2,
        show (1 - p a) * G * (G ^ s.card * S) + p a * G * (G ^ s.card * (1 + S)) =
          G * G ^ s.card * (p a + S) by ring]
theorem prod_lock_mix_sub_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (p : ι → ℝ) {G : ℝ}
    (hG_lo : 2 / 3 ≤ G) (hG_hi : G ≤ 1)
    (hp0 : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j ≤ 1) :
    (∏ j ∈ s, ((1 - p j) * G + p j)) - (∏ j ∈ s, (1 - p j)) * G ^ s.card ≤
      G ^ (s.card - 1) * (∑ j ∈ s, p j) := by
  have hG_pos : 0 < G := by linarith
  have h1 : 1 ≤ s.card := Finset.one_le_card.2 hs
  have hm := mul_prod_lock_mix_sub_le s p hG_lo hG_hi hp0 hsum
  have hpow : G ^ s.card = G * G ^ (s.card - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1]
    rw [pow_succ']
  have hrhs : G ^ s.card * (∑ j ∈ s, p j) = G * (G ^ (s.card - 1) * (∑ j ∈ s, p j)) := by
    rw [hpow]; ring
  exact le_of_mul_le_mul_left (hm.trans_eq hrhs) hG_pos
/- ## 2. Zero-Slack Finite-`N` `r = 2` Envelope, `[0, π / 4]` Concavity & AM-GM -/
theorem cos_sq_fuseNextAngle_two_le {n : ℕ} (h4 : 2 * 2 ≤ 2 ^ n) {x β : ℝ}
    (hθ : halfAngleSet n 2 ≤ x) (hxβ : x ≤ β) (hβ : β < π / 2) :
    Real.cos (fuseNextAngle n 2 β) ^ 2 ≤ 1 - (1 / 2) * Real.sin x ^ 2 := by
  have hx_lt : x < π / 2 := lt_of_le_of_lt hxβ hβ
  have hx_nn : 0 ≤ x := (Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)).trans hθ
  have harc_le : Real.arcsin (√(((2 : ℝ) - 1) / 2) * Real.sin x) ≤ fuseNextAngle n 2 x :=
    arcsin_sqrt_ratio_le_fuseNextAngle le_rfl h4 hθ hx_lt
  have hmono : fuseNextAngle n 2 x ≤ fuseNextAngle n 2 β :=
    fuseNextAngle_mono le_rfl h4 hθ hxβ hβ.le
  have hlt_pi2 : fuseNextAngle n 2 β < π / 2 :=
    fuseNextAngle_lt_pi_div_two le_rfl h4 (hθ.trans hxβ) hβ
  set u : ℝ := √(((2 : ℝ) - 1) / 2) * Real.sin x
  have hsin_nn : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx_nn (by linarith [Real.pi_pos])
  have hu_nn : 0 ≤ u := mul_nonneg (Real.sqrt_nonneg _) hsin_nn
  have harc_nn : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.2 hu_nn
  have hu_sq : u ^ 2 = (1 / 2) * Real.sin x ^ 2 := by
    dsimp only [u]; rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hu_sq_le1 : u ^ 2 ≤ 1 := by linarith [hu_sq, Real.sin_sq_le_one x]
  have hcos_le : Real.cos (fuseNextAngle n 2 β) ≤ Real.cos (Real.arcsin u) :=
    Real.cos_le_cos_of_nonneg_of_le_pi harc_nn (by linarith [Real.pi_pos]) (harc_le.trans hmono)
  have hcos_nn : 0 ≤ Real.cos (fuseNextAngle n 2 β) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hlt_pi2.le⟩
  calc Real.cos (fuseNextAngle n 2 β) ^ 2
      ≤ Real.cos (Real.arcsin u) ^ 2 := pow_le_pow_left₀ hcos_nn hcos_le 2
    _ = √(1 - u ^ 2) ^ 2 := by rw [Real.cos_arcsin]
    _ = 1 - u ^ 2 := Real.sq_sqrt (by linarith)
    _ = 1 - (1 / 2) * Real.sin x ^ 2 := by rw [hu_sq]
/- ## 3. Exact `r = 2 → 1` Warm Projective Doob Step Reduction (`step_two_sepWarmR1_le`) -/
theorem mul_one_add_mul_comm_real (s p cb : ℝ) :
    s * (1 + p * cb) = s + cb * (s * p) := by ring
theorem one_add_mul_sub_add_mul_real (cb A q B : ℝ) :
    (1 + cb * A) - (q + cb * B) = (1 - q) + cb * (A - B) := by ring
theorem one_add_add_sub_one_real (v s : ℝ) :
    1 + (v + (s - 1)) = v + s := by ring
theorem mul_sub_mul_real (p m : ℝ) :
    p * (1 - m) = p - p * m := by ring
theorem mul_assoc_right_comm_real (l m p r : ℝ) :
    l * (m * p * r) = (l * p * r) * m := by ring
theorem prod_split_algebra_real (A R Q P : ℝ) :
    (A * R) - Q * (P * R) = R * (A - Q * P) := by ring
theorem mul_assoc_comm_three_real (r g p : ℝ) :
    r * (g * p) = p * (r * g) := by ring
theorem cb_div_mul_assoc_real (cb q r p : ℝ) :
    cb * ((q / r) * p) = q * ((1 / r) * cb * p) := by ring
theorem ramp_slot_step_algebra {φ b θ rem : ℝ} (hθ : (2 * θ) ≠ 0)
    (hceil : (φ - b) / (2 * θ) ≤ rem) :
    1 - rem ≤ -(φ - (b + 2 * θ)) / (2 * θ) := by
  have hsplit : 1 - (φ - b) / (2 * θ) = -(φ - (b + 2 * θ)) / (2 * θ) := by
    rw [eq_div_iff hθ, sub_mul, one_mul, div_mul_cancel₀ _ hθ]; ring
  linarith
theorem peers_ramp_sum_algebra (c xb φ d : ℝ) :
    (c * xb - c * φ) / d = -c * ((φ - xb) / d) := by ring
theorem ramp_sum_outer_algebra (m q c d : ℝ) :
    (1 / m) * (q * (-c * d)) = -q * ((c / m) * d) := by ring
theorem mul_div_assoc_symm_real (a b c : ℝ) :
    a * (b / c) = a * b / c := by ring
theorem sum_erase_zero_stepWeight_warmR1Cost1 {m : ℕ} (n : ℕ) (φ : ℝ) (betas : Fin m → ℝ) :
    ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ m)),
        stepWeight n 2 φ betas o *
          warmR1Cost1 n m (nextStageFuseBetas n 2 o (nextBetasRamp n 2 φ betas)) =
      (1 - stepWeight n 2 φ betas 0) +
        (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)) *
          ((∏ i : Fin m, ((1 - (1 - stepAlpha n 2 φ (betas i) ^ 2)) *
                Real.cos (fuseNextAngle n 2 (nextBetasRamp n 2 φ betas i)) ^ 2 +
              (1 - stepAlpha n 2 φ (betas i) ^ 2) * Real.cos (halfAngleSet n 1) ^ 2)) -
            (∏ i : Fin m, (1 - (1 - stepAlpha n 2 φ (betas i) ^ 2))) *
              (∏ i : Fin m,
                Real.cos (fuseNextAngle n 2 (nextBetasRamp n 2 φ betas i)) ^ 2)) := by
  let postB := nextBetasRamp n 2 φ betas
  let q0 := stepWeight n 2 φ betas 0
  let pSlot : Fin m → ℝ := fun i ↦ 1 - stepAlpha n 2 φ (betas i) ^ 2
  let gSlot : Fin m → ℝ := fun i ↦ Real.cos (fuseNextAngle n 2 (postB i)) ^ 2
  let c1 : ℝ := Real.cos (halfAngleSet n 1) ^ 2
  let CB : ℝ := ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)
  let pBool : Fin m → Bool → ℝ := fun i b ↦ if b then pSlot i else 1 - pSlot i
  have hpBool : ∀ i : Fin m, pBool i false + pBool i true = 1 := fun i ↦ by
    dsimp only [pBool]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact sub_add_cancel 1 (pSlot i)
  let qBool : Fin m → Bool → ℝ := fun i b ↦ if b then pSlot i * c1 else (1 - pSlot i) * gSlot i
  have hstep_eq : ∀ o : Fin (2 ^ m),
      stepWeight n 2 φ betas o = ∏ i : Fin m, pBool i (o.val.testBit i.val) := fun o ↦ by
    dsimp only [stepWeight, pBool, pSlot]; refine Finset.prod_congr rfl fun i _ ↦ ?_
    cases o.val.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte]
    exact (sub_sub_cancel 1 (stepAlpha n 2 φ (betas i) ^ 2)).symm
  have hprod_eq : ∀ o : Fin (2 ^ m),
      stepWeight n 2 φ betas o *
          (∏ i : Fin m, Real.cos (nextStageFuseBetas n 2 o postB i) ^ 2) =
        ∏ i : Fin m, qBool i (o.val.testBit i.val) := fun o ↦ by
    rw [hstep_eq o, ← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun i _ ↦ ?_
    dsimp only [pBool, qBool, nextStageFuseBetas, c1, gSlot]
    simp only [show (2 - 1 : ℕ) = 1 from rfl]
    cases o.val.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte]
  let f : Fin (2 ^ m) → ℝ := fun o ↦
    stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB)
  have herase : ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ m)), f o =
      (∑ o : Fin (2 ^ m), f o) - f 0 :=
    eq_sub_of_add_eq' (Finset.add_sum_erase Finset.univ f (Finset.mem_univ (0 : Fin (2 ^ m))))
  change ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ m)), f o =
    (1 - q0) + CB *
      ((∏ i : Fin m, ((1 - pSlot i) * gSlot i + pSlot i * c1)) -
        (∏ i : Fin m, (1 - pSlot i)) * (∏ i : Fin m, gSlot i))
  rw [herase]
  have hf_exp : ∀ o : Fin (2 ^ m),
      f o = (∏ i : Fin m, pBool i (o.val.testBit i.val)) +
        CB * (∏ i : Fin m, qBool i (o.val.testBit i.val)) := fun o ↦ by
    dsimp only [f, warmR1Cost1, CB]
    calc stepWeight n 2 φ betas o *
          (1 + (∏ i : Fin m, Real.cos (nextStageFuseBetas n 2 o postB i) ^ 2) *
            (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)))
        = stepWeight n 2 φ betas o +
          (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)) *
            (stepWeight n 2 φ betas o *
              ∏ i : Fin m, Real.cos (nextStageFuseBetas n 2 o postB i) ^ 2) :=
          mul_one_add_mul_comm_real _ _ _
      _ = (∏ i : Fin m, pBool i (o.val.testBit i.val)) +
          (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)) *
            (∏ i : Fin m, qBool i (o.val.testBit i.val)) := by rw [hprod_eq o, hstep_eq o]
  have hsum_q : ∑ o : Fin (2 ^ m), (∏ i : Fin m, qBool i (o.val.testBit i.val)) =
      ∏ i : Fin m, ((1 - pSlot i) * gSlot i + pSlot i * c1) := by
    have hrew : ∀ o : Fin (2 ^ m),
        (∏ i : Fin m, qBool i (o.val.testBit i.val)) =
          ∏ i : Fin m, qBool i (finPowTwoEquivBool m o i) := fun o ↦ by simp
    simp_rw [hrew]
    rw [(finPowTwoEquivBool m).sum_comp (fun h : Fin m → Bool ↦ ∏ i : Fin m, qBool i (h i)),
      ← Fintype.prod_sum]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Fintype.sum_bool]; dsimp only [qBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact add_comm _ _
  have hsum_f : ∑ o : Fin (2 ^ m), f o =
      1 + CB * (∏ i : Fin m, ((1 - pSlot i) * gSlot i + pSlot i * c1)) := by
    simp_rw [hf_exp]
    rw [Finset.sum_add_distrib, sum_prod_testBit_eq_one pBool hpBool, ← Finset.mul_sum, hsum_q]
  have hf0 : f 0 = q0 + CB * ((∏ i : Fin m, (1 - pSlot i)) * (∏ i : Fin m, gSlot i)) := by
    rw [hf_exp 0, ← hstep_eq 0]
    have h0b : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false :=
      fun i ↦ Nat.zero_testBit i.val
    have hq0_prod : (∏ i : Fin m, qBool i ((0 : Fin (2 ^ m)).val.testBit i.val)) =
        (∏ i : Fin m, (1 - pSlot i)) * (∏ i : Fin m, gSlot i) := by
      dsimp only [qBool]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, Finset.prod_mul_distrib]
    rw [hq0_prod]
  rw [hsum_f, hf0]
  exact one_add_mul_sub_add_mul_real CB _ q0 _
theorem base_diff_algebra {q0 V2 m_r l_r r_r SR : ℝ} (hm : m_r ≠ 0) (hcard : l_r + r_r = m_r) :
    1 + q0 * (V2 + 1 / m_r * (SR - r_r)) - (V2 + 1 / m_r * SR) =
      l_r / m_r - (1 - q0) * V2 + (1 / m_r) * ((1 - q0) * (r_r - SR)) := by
  have h1 : (1 : ℝ) = (l_r + r_r) * (1 / m_r) := by
    rw [hcard, mul_one_div_cancel hm]
  have h2 : l_r / m_r = l_r * (1 / m_r) := div_eq_mul_one_div l_r m_r
  rw [h2]
  linear_combination h1
theorem warm_step_combine_real
    {lhs rhs hit l_div q0 V2 ramp_sum m_p_ρ term_B term_R : ℝ}
    (hq0 : 0 ≤ 1 - q0)
    (hbase : lhs - rhs = l_div - (1 - q0) * V2 + ramp_sum)
    (hhit : hit ≤ (1 - q0) + (1 - q0) * term_B)
    (hl : l_div ≤ (1 - q0) / m_p_ρ)
    (hramp : ramp_sum ≤ -(1 - q0) * term_R)
    (hV2 : 1 / m_p_ρ + 1 + term_B - term_R ≤ V2) :
    lhs + hit ≤ rhs := by
  have hV2s := mul_le_mul_of_nonneg_left hV2 hq0
  have hid : (1 - q0) * (1 / m_p_ρ + 1 + term_B - term_R) =
      (1 - q0) / m_p_ρ + (1 - q0) + (1 - q0) * term_B - (1 - q0) * term_R := by ring
  linarith
theorem step_two_sepWarmR1_le {m n : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ 1024) (hn : 100 ≤ n)
    {tFn : ℕ → ℕ} {V : ℕ → ℝ}
    (ht2_lo : 500 ≤ tFn 2) (ht2_hi : tFn 2 ≤ 100000)
    (hwarm_1d : ∀ xBar : ℝ, 0 ≤ xBar → xBar ≤ Real.arctan ((tFn 2 : ℝ) / 100000) →
      1 / ((m : ℝ) *
          (4 * ((tFn 2 : ℝ) / 100000) * (99999999 / 100000000) * √(2 : ℝ) / √((2 : ℝ) ^ n)) *
          (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) +
        1 +
        (1 / (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) *
          (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)) *
          (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) -
        (((m - 1 : ℕ) : ℝ) / m) *
          ((Real.arctan ((tFn 2 : ℝ) / 100000) - xBar) / (2 * halfAngleSet n 2)) ≤ V 2)
    (betas : Fin m → ℝ) (hbetas : ValidStageBetas n 2 (π / 3) betas) :
    1 + stepWeight n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas 0 *
        sepPotential (fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)) V n 2
          (nextBetasRamp n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas) +
      (∑ o ∈ Finset.univ.erase 0,
        stepWeight n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas o *
          warmR1Cost1 n m
            (nextStageFuseBetas n 2 o
              (nextBetasRamp n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas))) ≤
      sepPotential (fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)) V n 2 betas := by
  let phiFn : ℕ → ℝ := fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)
  have hm1 : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
  set φ : ℝ := Real.arctan ((tFn 2 : ℝ) / 100000)
  set θ : ℝ := halfAngleSet n 2
  obtain ⟨h2θ_φ, hφ_2θ_ub, hpi3_lt, hlock⟩ :=
    phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn (by omega : 1 ≤ 2)
      (by omega : 2 ≤ 1024) ht2_lo ht2_hi
  change 2 * θ ≤ φ at h2θ_φ
  change φ + 2 * θ ≤ π / 3 at hφ_2θ_ub
  have h4_pow : 2 * 2 ≤ 2 ^ n := two_mul_le_pow_100 hn (by omega : 2 ≤ 1024)
  obtain ⟨hθ_lo, -⟩ := halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024)
  change √(2 : ℝ) / √((2 : ℝ) ^ n) ≤ θ at hθ_lo
  have hθ_pos : 0 < θ := lt_of_lt_of_le (by positivity) hθ_lo
  have hφ_le_pi4 : φ ≤ π / 4 := by
    dsimp only [φ]
    have ht_le1 : (tFn 2 : ℝ) / 100000 ≤ 1 := by
      have : (tFn 2 : ℝ) ≤ 100000 := by exact_mod_cast ht2_hi
      linarith
    simpa only [Real.arctan_one] using Real.arctan_mono ht_le1
  let L : Finset (Fin m) := Finset.univ.filter (fun i ↦ φ ≤ betas i)
  let R_set : Finset (Fin m) := Finset.univ.filter (fun i ↦ ¬ φ ≤ betas i)
  let postB : Fin m → ℝ := nextBetasRamp n 2 φ betas
  let pSlot : Fin m → ℝ := fun i ↦ 1 - stepAlpha n 2 φ (betas i) ^ 2
  have hpSlot_ramp : ∀ i ∈ R_set, pSlot i = 0 := fun i hi ↦ by
    have hlt : betas i < φ := not_le.1 (Finset.mem_filter.1 hi).2
    dsimp only [pSlot]; simp only [stepAlpha, hlt, ↓reduceIte, one_pow, sub_self]
  have hpSlot_lock : ∀ j ∈ L, pSlot j = 1 - lockedAlpha (betas j) θ ^ 2 := fun j hj ↦ by
    have hge : ¬ betas j < φ := not_lt.2 (Finset.mem_filter.1 hj).2
    dsimp only [pSlot, θ]; simp only [stepAlpha, hge, ↓reduceIte]
  have hpSlot_bds : ∀ i : Fin m, 0 ≤ pSlot i ∧ pSlot i ≤ 1 := fun i ↦ by
    have hβ_lt : betas i < π / 2 := lt_of_le_of_lt (hbetas i).2 hpi3_lt
    obtain ⟨_, hα_sq⟩ := stepAlpha_bounds (by omega : 1 ≤ 2) h2θ_φ hβ_lt
    exact ⟨by linarith, by nlinarith [sq_nonneg (stepAlpha n 2 φ (betas i))]⟩
  have hq0_eq : stepWeight n 2 φ betas 0 = ∏ j ∈ L, (1 - pSlot j) := by
    have h0b : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false :=
      fun i ↦ Nat.zero_testBit i.val
    dsimp only [stepWeight]; simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    have hrew : ∀ i : Fin m, stepAlpha n 2 φ (betas i) ^ 2 = 1 - pSlot i := fun i ↦ by
      dsimp only [pSlot]; exact (sub_sub_cancel 1 _).symm
    simp_rw [hrew]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin m ↦ φ ≤ betas i)]
    have hramp1 : ∏ i ∈ R_set, (1 - pSlot i) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by rw [hpSlot_ramp i hi, sub_zero]
    change (∏ j ∈ L, (1 - pSlot j)) * (∏ i ∈ R_set, (1 - pSlot i)) = _
    rw [hramp1, mul_one]
  have hrem_split : ∀ g : Fin m → ℝ, ∑ i : Fin m, g i = (∑ j ∈ L, g j) + (∑ i ∈ R_set, g i) :=
    fun g ↦ (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin m ↦ φ ≤ betas i) g).symm
  have hrem_lock : ∀ j ∈ L, (remStepsSlot n 2 φ (betas j) : ℝ) = 0 ∧
      (remStepsSlot n 2 φ (postB j) : ℝ) = 0 := fun j hj ↦ by
    have hge : φ ≤ betas j := (Finset.mem_filter.1 hj).2
    have hnot : ¬ betas j < φ := not_lt.2 hge
    refine ⟨by exact_mod_cast (remStepsSlot_eq_zero_iff (by omega : 1 ≤ 2) φ (betas j)).2 hge, ?_⟩
    dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [hnot, ↓reduceIte]
    exact_mod_cast (remStepsSlot_eq_zero_iff (by omega : 1 ≤ 2) φ (betas j)).2 hge
  have hrem_ramp : ∀ i ∈ R_set, 1 ≤ (remStepsSlot n 2 φ (betas i) : ℝ) ∧
      (remStepsSlot n 2 φ (postB i) : ℝ) = (remStepsSlot n 2 φ (betas i) : ℝ) - 1 :=
    fun i hi ↦ by
      have hlt : betas i < φ := not_le.1 (Finset.mem_filter.1 hi).2
      have hpos : 1 ≤ remStepsSlot n 2 φ (betas i) := by
        by_contra h0
        have hez : remStepsSlot n 2 φ (betas i) = 0 := by omega
        linarith [(remStepsSlot_eq_zero_iff (by omega : 1 ≤ 2) φ (betas i)).1 hez]
      refine ⟨by exact_mod_cast hpos, ?_⟩
      dsimp only [postB, nextBetasRamp]
      simp only [remStepsSlot_nextBetaSlot (by omega : 1 ≤ 2), hlt, ↓reduceIte]
      rw [Nat.cast_sub hpos, Nat.cast_one]
  have hcard_sum : (L.card : ℝ) + (R_set.card : ℝ) = m := by
    have hc := hrem_split (fun _ ↦ (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
    linarith
  by_cases hL_empty : L = ∅
  · have hq0_one : stepWeight n 2 φ betas 0 = 1 := by
      rw [hq0_eq, hL_empty, Finset.prod_empty]
    have hL_card : (L.card : ℝ) = 0 := by simp only [hL_empty, Finset.card_empty, Nat.cast_zero]
    have hR_card : (R_set.card : ℝ) = m := by linarith
    have hp_all0 : ∀ i : Fin m, pSlot i = 0 := fun i ↦ by
      have hiR : i ∈ R_set := by
        by_contra hnR
        have hiL : i ∈ L := by
          dsimp only [L, R_set] at hnR ⊢
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnR ⊢
          exact hnR
        rw [hL_empty] at hiL; exact Finset.notMem_empty i hiL
      exact hpSlot_ramp i hiR
    have hhit_zero : ∑ o ∈ Finset.univ.erase 0,
        stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB) = 0 := by
      have heq := sum_erase_zero_stepWeight_warmR1Cost1 n φ betas
      change ∑ o ∈ Finset.univ.erase 0,
          stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB) =
        (1 - stepWeight n 2 φ betas 0) +
          (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)) *
            ((∏ i : Fin m, ((1 - pSlot i) *
                Real.cos (fuseNextAngle n 2 (postB i)) ^ 2 +
                pSlot i * Real.cos (halfAngleSet n 1) ^ 2)) -
              (∏ i : Fin m, (1 - pSlot i)) *
                (∏ i : Fin m, Real.cos (fuseNextAngle n 2 (postB i)) ^ 2)) at heq
      rw [heq, hq0_one]; simp_rw [hp_all0]
      simp
    change 1 + stepWeight n 2 φ betas 0 * sepPotential phiFn V n 2 postB +
        (∑ o ∈ Finset.univ.erase 0,
          stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB)) ≤
      sepPotential phiFn V n 2 betas
    rw [hhit_zero, add_zero, hq0_one, one_mul]; dsimp only [sepPotential]
    change 1 + (V 2 + 1 / (m : ℝ) * ∑ i : Fin m, (remStepsSlot n 2 φ (postB i) : ℝ)) ≤
      V 2 + 1 / (m : ℝ) * ∑ i : Fin m, (remStepsSlot n 2 φ (betas i) : ℝ)
    rw [hrem_split (fun i ↦ (remStepsSlot n 2 φ (postB i) : ℝ)),
      hrem_split (fun i ↦ (remStepsSlot n 2 φ (betas i) : ℝ))]
    have h1 : ∑ j ∈ L, (remStepsSlot n 2 φ (postB j) : ℝ) = 0 := by
      simp only [hL_empty, Finset.sum_empty]
    have h2 : ∑ j ∈ L, (remStepsSlot n 2 φ (betas j) : ℝ) = 0 := by
      simp only [hL_empty, Finset.sum_empty]
    have h3 : ∑ i ∈ R_set, (remStepsSlot n 2 φ (postB i) : ℝ) =
        (∑ i ∈ R_set, (remStepsSlot n 2 φ (betas i) : ℝ)) - m := by
      rw [Finset.sum_congr rfl (fun i hi ↦ (hrem_ramp i hi).2), Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, mul_one, hR_card]
    rw [h1, h2, zero_add, zero_add, h3]
    have hdiv : 1 / (m : ℝ) * ((∑ i ∈ R_set, (remStepsSlot n 2 φ (betas i) : ℝ)) - m) =
        1 / (m : ℝ) * (∑ i ∈ R_set, (remStepsSlot n 2 φ (betas i) : ℝ)) - 1 := by
      rw [mul_sub, one_div_mul_cancel hm_pos.ne']
    rw [hdiv]; exact le_of_eq (one_add_add_sub_one_real _ _)
  · have hL_nonempty : L.Nonempty := Finset.nonempty_iff_ne_empty.2 hL_empty
    have hl_ge1 : (1 : ℝ) ≤ L.card := by exact_mod_cast Finset.one_le_card.2 hL_nonempty
    have hl_pos : (0 : ℝ) < L.card := by linarith
    have hl_lem : (L.card : ℝ) ≤ m := by linarith [show (0 : ℝ) ≤ R_set.card by positivity]
    set q0 : ℝ := stepWeight n 2 φ betas 0
    set p_min : ℝ := 4 * ((tFn 2 : ℝ) / 100000) * (99999999 / 100000000) * √(2 : ℝ) / √((2 : ℝ) ^ n)
    set p_max : ℝ := 1 / (100000000 * (m : ℝ)); set ρ : ℝ := 1 - (m : ℝ) * p_max
    have ht2_pos : (0 : ℝ) < (tFn 2 : ℝ) / 100000 := by
      have : (500 : ℝ) ≤ tFn 2 := by exact_mod_cast ht2_lo
      linarith
    have hp_min_pos : 0 < p_min := by dsimp only [p_min]; positivity
    have hp_max_nn : 0 ≤ p_max := by dsimp only [p_max]; positivity
    have hρ_eq : ρ = 99999999 / 100000000 := by
      dsimp only [ρ, p_max]; field_simp [hm_pos.ne']; norm_num
    have hρ_pos : 0 < ρ := by rw [hρ_eq]; norm_num
    have hL_p_bds : ∀ j ∈ L, p_min ≤ pSlot j ∧ pSlot j ≤ p_max := fun j hj ↦ by
      rw [hpSlot_lock j hj]; exact hlock (betas j) (Finset.mem_filter.1 hj).2 (hbetas j).2
    set P_L : ℝ := ∑ j ∈ L, pSlot j
    have hP_ge : (L.card : ℝ) * p_min ≤ P_L := by
      calc (L.card : ℝ) * p_min = ∑ _j ∈ L, p_min := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ L, pSlot j := Finset.sum_le_sum fun j hj ↦ (hL_p_bds j hj).1
    have hP_le : P_L ≤ (m : ℝ) * p_max := by
      calc ∑ j ∈ L, pSlot j ≤ ∑ _j ∈ L, p_max := Finset.sum_le_sum fun j hj ↦ (hL_p_bds j hj).2
        _ = (L.card : ℝ) * p_max := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (m : ℝ) * p_max := mul_le_mul_of_nonneg_right hl_lem hp_max_nn
    have hP_le1 : P_L ≤ 1 := by linarith [hP_le, hρ_pos]
    have hP_nn : 0 ≤ P_L := Finset.sum_nonneg fun j _ ↦ (hpSlot_bds j).1
    have h1q0_ge_Pρ : P_L * ρ ≤ 1 - q0 := by
      have hbonf := sum_sub_sq_le_one_sub_prod L pSlot
        (fun j _ ↦ (hpSlot_bds j).1) (fun j _ ↦ (hpSlot_bds j).2)
      rw [← hq0_eq] at hbonf
      have hsq : P_L ^ 2 ≤ P_L * ((m : ℝ) * p_max) := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hP_le hP_nn
      calc P_L * ρ = P_L - P_L * ((m : ℝ) * p_max) := mul_sub_mul_real P_L ((m : ℝ) * p_max)
        _ ≤ P_L - P_L ^ 2 := sub_le_sub_left hsq P_L
        _ ≤ 1 - q0 := hbonf
    have h1q0_ge_l : (L.card : ℝ) * p_min * ρ ≤ 1 - q0 :=
      (mul_le_mul_of_nonneg_right hP_ge hρ_pos.le).trans h1q0_ge_Pρ
    have h1q0_pos : 0 < 1 - q0 :=
      lt_of_lt_of_le (mul_pos (mul_pos hl_pos hp_min_pos) hρ_pos) h1q0_ge_l
    have hP_div_le : P_L ≤ (1 - q0) / ρ := (le_div_iff₀ hρ_pos).2 h1q0_ge_Pρ
    have hl_div_le : (L.card : ℝ) / m ≤ (1 - q0) / ((m : ℝ) * p_min * ρ) := by
      rw [div_le_div_iff₀ hm_pos (mul_pos (mul_pos hm_pos hp_min_pos) hρ_pos)]
      calc (L.card : ℝ) * ((m : ℝ) * p_min * ρ)
          = ((L.card : ℝ) * p_min * ρ) * m := mul_assoc_right_comm_real (L.card : ℝ) (m : ℝ) p_min ρ
        _ ≤ (1 - q0) * m := mul_le_mul_of_nonneg_right h1q0_ge_l hm_pos.le
    -- Base ramp difference at `r = 2`
    have hsum_L_b : ∑ j ∈ L, (remStepsSlot n 2 φ (betas j) : ℝ) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ (hrem_lock j hj).1
    have hsum_L_pb : ∑ j ∈ L, (remStepsSlot n 2 φ (postB j) : ℝ) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ (hrem_lock j hj).2
    have hsum_R_pb : ∑ i ∈ R_set, (remStepsSlot n 2 φ (postB i) : ℝ) =
        (∑ i ∈ R_set, (remStepsSlot n 2 φ (betas i) : ℝ)) - R_set.card := by
      rw [Finset.sum_congr rfl (fun i hi ↦ (hrem_ramp i hi).2), Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbase_diff :
        1 + q0 * sepPotential phiFn V n 2 postB - sepPotential phiFn V n 2 betas =
          (L.card : ℝ) / m - (1 - q0) * V 2 +
            (1 / (m : ℝ)) * ∑ i ∈ R_set,
              (1 - q0) * (1 - (remStepsSlot n 2 φ (betas i) : ℝ)) := by
      dsimp only [sepPotential]
      change 1 + q0 * (V 2 + 1 / (m : ℝ) * ∑ i : Fin m, (remStepsSlot n 2 φ (postB i) : ℝ)) -
          (V 2 + 1 / (m : ℝ) * ∑ i : Fin m, (remStepsSlot n 2 φ (betas i) : ℝ)) = _
      rw [hrem_split (fun i ↦ (remStepsSlot n 2 φ (postB i) : ℝ)),
        hrem_split (fun i ↦ (remStepsSlot n 2 φ (betas i) : ℝ)),
        hsum_L_pb, hsum_L_b, zero_add, zero_add, hsum_R_pb]
      have hR_sum_eq :
          ∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n 2 φ (betas i) : ℝ)) =
            (1 - q0) * ((R_set.card : ℝ) -
              ∑ i ∈ R_set, (remStepsSlot n 2 φ (betas i) : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hR_sum_eq]; exact base_diff_algebra hm_pos.ne' hcard_sum
    -- Clamped post-ramp angles `x i = min (postB i) φ ∈ [θ, φ]`
    let x : Fin m → ℝ := fun i ↦ min (postB i) φ
    have hx_lock : ∀ j ∈ L, x j = φ := fun j hj ↦ by
      have hge : φ ≤ betas j := (Finset.mem_filter.1 hj).2
      have hnot : ¬ betas j < φ := not_lt.2 hge
      dsimp only [x, postB, nextBetasRamp, nextBetaSlot]
      simp only [hnot, ↓reduceIte, min_eq_right hge]
    have hx_bds : ∀ i : Fin m, θ ≤ x i ∧ x i ≤ φ ∧ x i ≤ postB i ∧ postB i < π / 2 := fun i ↦ by
      have hβ_lo : θ ≤ betas i := (hbetas i).1
      have hβ_hi : betas i ≤ π / 3 := (hbetas i).2
      dsimp only [x, postB, nextBetasRamp, nextBetaSlot, θ]
      by_cases hlt : betas i < φ
      · simp only [hlt, ↓reduceIte]
        exact ⟨le_min (by linarith) (by linarith), min_le_right _ _, min_le_left _ _,
          by linarith⟩
      · simp only [hlt, ↓reduceIte]
        exact ⟨le_min hβ_lo (by linarith), min_le_right _ _, min_le_left _ _, by linarith⟩
    let gSlot : Fin m → ℝ := fun i ↦ Real.cos (fuseNextAngle n 2 (postB i)) ^ 2
    let fEnv : Fin m → ℝ := fun i ↦ 1 - (1 / 2) * Real.sin (x i) ^ 2
    set Gφ : ℝ := 1 - (1 / 2) * Real.sin φ ^ 2
    have hgSlot_nn : ∀ i : Fin m, 0 ≤ gSlot i := fun i ↦ sq_nonneg _
    have hgSlot_le_fEnv : ∀ i : Fin m, gSlot i ≤ fEnv i := fun i ↦ by
      obtain ⟨hx_θ, -, hx_pb, hpb_lt⟩ := hx_bds i
      exact cos_sq_fuseNextAngle_two_le h4_pow hx_θ hx_pb hpb_lt
    have hfEnv_lock : ∀ j ∈ L, fEnv j = Gφ := fun j hj ↦ by
      dsimp only [fEnv, Gφ]; rw [hx_lock j hj]
    have hGφ_bds : 2 / 3 ≤ Gφ ∧ Gφ ≤ 1 := by
      have hφ_nn : 0 ≤ φ := by linarith
      have hsin_le : Real.sin φ ≤ Real.sin (π / 4) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos]) hφ_le_pi4
      have hsin_nn : 0 ≤ Real.sin φ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hφ_nn (by linarith [Real.pi_pos])
      have hsin_sq : Real.sin φ ^ 2 ≤ 1 / 2 := by
        have h1 := pow_le_pow_left₀ hsin_nn hsin_le 2
        rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)] at h1; linarith
      dsimp only [Gφ]; exact ⟨by linarith, by nlinarith [sq_nonneg (Real.sin φ)]⟩
    -- Pick a representative locked slot `iStar ∈ L` and merge `(L.erase iStar) ∪ R_set`
    obtain ⟨iStar, hiStar⟩ := hL_nonempty
    let peers : Finset (Fin m) := Finset.univ.erase iStar
    have hpeers_card : peers.card = m - 1 := by
      dsimp only [peers]
      simp only [Finset.card_erase_of_mem (Finset.mem_univ iStar), Finset.card_univ,
        Fintype.card_fin]
    have hpeers_nonempty : peers.Nonempty := by
      rw [← Finset.card_pos, hpeers_card]; omega
    have hdisj_LR : Disjoint (L.erase iStar) R_set := by
      rw [Finset.disjoint_left]; intro y hyL hyR
      exact (Finset.mem_filter.1 hyR).2 (Finset.mem_filter.1 (Finset.mem_of_mem_erase hyL)).2
    have hunion_LR : L.erase iStar ∪ R_set = peers := by
      ext y
      dsimp only [peers, L, R_set]
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true]
      constructor
      · rintro (⟨hy_ne, _⟩ | hy_nle)
        · exact hy_ne
        · intro hy_eq
          subst hy_eq
          exact hy_nle (Finset.mem_filter.1 hiStar).2
      · intro hy_ne
        by_cases hle : φ ≤ betas y
        · exact Or.inl ⟨hy_ne, hle⟩
        · exact Or.inr hle
    -- Factorize & majorize the multi-click `r = 2 → 1` product difference
    set c1 : ℝ := Real.cos (halfAngleSet n 1) ^ 2
    set CB : ℝ := ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)
    have hCB_nn : 0 ≤ CB := by
      dsimp only [CB]; have hpi : 0 ≤ π / 4 := by linarith [Real.pi_pos]
      positivity
    have hprod_split :
        (∏ i : Fin m, ((1 - pSlot i) * gSlot i + pSlot i * c1)) -
          (∏ i : Fin m, (1 - pSlot i)) * (∏ i : Fin m, gSlot i) =
        (∏ i ∈ R_set, gSlot i) *
          ((∏ j ∈ L, ((1 - pSlot j) * gSlot j + pSlot j * c1)) -
            (∏ j ∈ L, (1 - pSlot j)) * (∏ j ∈ L, gSlot j)) := by
      have h1 : (∏ i : Fin m, ((1 - pSlot i) * gSlot i + pSlot i * c1)) =
          (∏ j ∈ L, ((1 - pSlot j) * gSlot j + pSlot j * c1)) * (∏ i ∈ R_set, gSlot i) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin m ↦ φ ≤ betas i)]
        congr 1
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        rw [hpSlot_ramp i hi, sub_zero, one_mul, zero_mul, add_zero]
      have h2 : (∏ i : Fin m, (1 - pSlot i)) = ∏ j ∈ L, (1 - pSlot j) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin m ↦ φ ≤ betas i)]
        have hr1 : ∏ i ∈ R_set, (1 - pSlot i) = 1 :=
          Finset.prod_eq_one fun i hi ↦ by rw [hpSlot_ramp i hi, sub_zero]
        change (∏ j ∈ L, (1 - pSlot j)) * (∏ i ∈ R_set, (1 - pSlot i)) = _
        rw [hr1, mul_one]
      have h3 : (∏ i : Fin m, gSlot i) = (∏ j ∈ L, gSlot j) * (∏ i ∈ R_set, gSlot i) :=
        (Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun i : Fin m ↦ φ ≤ betas i) gSlot).symm
      rw [h1, h2, h3]; exact prod_split_algebra_real _ _ _ _
    have hL_diff_le :
        (∏ j ∈ L, ((1 - pSlot j) * gSlot j + pSlot j * c1)) -
          (∏ j ∈ L, (1 - pSlot j)) * (∏ j ∈ L, gSlot j) ≤
        Gφ ^ (L.card - 1) * P_L := by
      have hmono := prod_add_sub_prod_mono L pSlot gSlot (fun _ ↦ Gφ) (fun _ ↦ c1)
        (fun j _ ↦ (hpSlot_bds j).1) (fun j _ ↦ (hpSlot_bds j).2)
        (fun j _ ↦ hgSlot_nn j)
        (fun j hj ↦ (hgSlot_le_fEnv j).trans_eq (hfEnv_lock j hj))
        (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ Real.cos_sq_le_one _)
      rw [Finset.prod_const] at hmono
      exact hmono.trans (prod_lock_mix_sub_le (Finset.nonempty_iff_ne_empty.2 hL_empty) pSlot
        hGφ_bds.1 hGφ_bds.2 (fun j _ ↦ (hpSlot_bds j).1) hP_le1)
    set xBar : ℝ := (∑ j ∈ peers, x j) / peers.card
    have hxBar_bds : 0 ≤ xBar ∧ xBar ≤ φ := by
      have hcard_pos : (0 : ℝ) < peers.card := Nat.cast_pos.2 (Finset.card_pos.2 hpeers_nonempty)
      refine ⟨div_nonneg (Finset.sum_nonneg fun j _ ↦ hθ_pos.le.trans (hx_bds j).1) hcard_pos.le,
        ?_⟩
      dsimp only [xBar]; rw [div_le_iff₀ hcard_pos]
      calc ∑ j ∈ peers, x j ≤ ∑ _j ∈ peers, φ := Finset.sum_le_sum fun j _ ↦ (hx_bds j).2.1
        _ = (peers.card : ℝ) * φ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = φ * peers.card := mul_comm _ _
    have hprod_peers_le :
        (∏ i ∈ R_set, gSlot i) * (Gφ ^ (L.card - 1) * P_L) ≤
          ((1 - q0) / ρ) * (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) := by
      have hG_pow : Gφ ^ (L.card - 1) = ∏ j ∈ L.erase iStar, fEnv j := by
        have hcongr : ∏ j ∈ L.erase iStar, fEnv j = ∏ _j ∈ L.erase iStar, Gφ :=
          Finset.prod_congr rfl fun j hj ↦ hfEnv_lock j (Finset.mem_of_mem_erase hj)
        rw [hcongr, Finset.prod_const, Finset.card_erase_of_mem hiStar]
      have hR_prod : ∏ i ∈ R_set, gSlot i ≤ ∏ i ∈ R_set, fEnv i :=
        PipeFuseWarmR1Cert.prod_le_prod_real R_set gSlot fEnv
          (fun i _ ↦ hgSlot_nn i) (fun i _ ↦ hgSlot_le_fEnv i)
      have hG_pow_nn : 0 ≤ Gφ ^ (L.card - 1) :=
        pow_nonneg ((by norm_num : (0 : ℝ) ≤ 2 / 3).trans hGφ_bds.1) _
      have hmerge : (∏ i ∈ R_set, gSlot i) * Gφ ^ (L.card - 1) ≤ ∏ j ∈ peers, fEnv j := by
        calc (∏ i ∈ R_set, gSlot i) * Gφ ^ (L.card - 1)
            ≤ (∏ i ∈ R_set, fEnv i) * Gφ ^ (L.card - 1) :=
              mul_le_mul_of_nonneg_right hR_prod hG_pow_nn
          _ = (∏ j ∈ L.erase iStar, fEnv j) * (∏ i ∈ R_set, fEnv i) := by rw [hG_pow, mul_comm]
          _ = ∏ j ∈ L.erase iStar ∪ R_set, fEnv j := (Finset.prod_union hdisj_LR).symm
          _ = ∏ j ∈ peers, fEnv j := by rw [hunion_LR]
      have hamgm : ∏ j ∈ peers, fEnv j ≤ (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) := by
        have h1 := PipeFuseWarmR1Cert.prod_one_sub_half_sin_sq_le_mean_pow peers x
          (fun j _ ↦ hθ_pos.le.trans (hx_bds j).1)
          (fun j _ ↦ (hx_bds j).2.1.trans hφ_le_pi4)
        dsimp only [fEnv, xBar]; rw [← hpeers_card]
        exact h1
      have hprod_R_nn : 0 ≤ ∏ i ∈ R_set, gSlot i := Finset.prod_nonneg fun i _ ↦ hgSlot_nn i
      calc (∏ i ∈ R_set, gSlot i) * (Gφ ^ (L.card - 1) * P_L)
          = P_L * ((∏ i ∈ R_set, gSlot i) * Gφ ^ (L.card - 1)) := mul_assoc_comm_three_real _ _ _
        _ ≤ ((1 - q0) / ρ) * (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1) :=
          mul_le_mul hP_div_le (hmerge.trans hamgm) (mul_nonneg hprod_R_nn hG_pow_nn)
            (div_nonneg h1q0_pos.le hρ_pos.le)
    have hhit_le :
        ∑ o ∈ Finset.univ.erase 0,
            stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB) ≤
          (1 - q0) + (1 - q0) * ((1 / ρ) * CB * (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1)) := by
      have heq := sum_erase_zero_stepWeight_warmR1Cost1 n φ betas
      change ∑ o ∈ Finset.univ.erase 0,
          stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB) =
        (1 - q0) + CB *
          ((∏ i : Fin m, ((1 - pSlot i) * gSlot i + pSlot i * c1)) -
            (∏ i : Fin m, (1 - pSlot i)) * (∏ i : Fin m, gSlot i)) at heq
      rw [heq, hprod_split]
      have hprod_R_nn : 0 ≤ ∏ i ∈ R_set, gSlot i := Finset.prod_nonneg fun i _ ↦ hgSlot_nn i
      have hm1 := mul_le_mul_of_nonneg_left hL_diff_le hprod_R_nn
      have hm2 : CB * ((∏ i ∈ R_set, gSlot i) *
          ((∏ j ∈ L, ((1 - pSlot j) * gSlot j + pSlot j * c1)) -
            (∏ j ∈ L, (1 - pSlot j)) * (∏ j ∈ L, gSlot j))) ≤
          (1 - q0) * ((1 / ρ) * CB * (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1)) :=
        (mul_le_mul_of_nonneg_left (hm1.trans hprod_peers_le) hCB_nn).trans_eq
          (cb_div_mul_assoc_real CB (1 - q0) ρ ((1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1)))
      exact add_le_add le_rfl hm2
    -- Zero-rounding ramp credit on `R_set`
    have hramp_slot_le : ∀ i ∈ R_set,
        1 - (remStepsSlot n 2 φ (betas i) : ℝ) ≤ -(φ - x i) / (2 * θ) := fun i hi ↦ by
      have hlt : betas i < φ := not_le.1 (Finset.mem_filter.1 hi).2
      have h1_le : (1 : ℝ) ≤ (remStepsSlot n 2 φ (betas i) : ℝ) := (hrem_ramp i hi).1
      dsimp only [x, postB, nextBetasRamp, nextBetaSlot]; simp only [hlt, ↓reduceIte]
      change 1 - (remStepsSlot n 2 φ (betas i) : ℝ) ≤ -(φ - min (betas i + 2 * θ) φ) / (2 * θ)
      by_cases hstep : φ ≤ betas i + 2 * θ
      · rw [min_eq_right hstep, sub_self, neg_zero, zero_div]
        exact sub_nonpos.2 h1_le
      · have hstep_lt : betas i + 2 * θ < φ := not_le.1 hstep
        rw [min_eq_left hstep_lt.le]
        have hceil : (φ - betas i) / (2 * θ) ≤ (remStepsSlot n 2 φ (betas i) : ℝ) := by
          dsimp only [remStepsSlot, θ]; exact Nat.le_ceil _
        exact ramp_slot_step_algebra (by positivity) hceil
    have hramp_sum_le :
        (1 / (m : ℝ)) * ∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n 2 φ (betas i) : ℝ)) ≤
          -(1 - q0) * ((((m - 1 : ℕ) : ℝ) / m) * ((φ - xBar) / (2 * θ))) := by
      have hsum_R : ∑ i ∈ R_set, (1 - (remStepsSlot n 2 φ (betas i) : ℝ)) ≤
          ∑ j ∈ peers, (-(φ - x j) / (2 * θ)) := by
        have hL_zero : ∑ j ∈ L.erase iStar, (-(φ - x j) / (2 * θ)) = 0 :=
          Finset.sum_eq_zero fun j hj ↦ by
            rw [hx_lock j (Finset.mem_of_mem_erase hj), sub_self, neg_zero, zero_div]
        rw [← hunion_LR, Finset.sum_union hdisj_LR, hL_zero, zero_add]
        exact Finset.sum_le_sum hramp_slot_le
      have hpeers_eq : ∑ j ∈ peers, (-(φ - x j) / (2 * θ)) =
          -((m - 1 : ℕ) : ℝ) * ((φ - xBar) / (2 * θ)) := by
        have hcard_pos : (0 : ℝ) < peers.card := Nat.cast_pos.2 (Finset.card_pos.2 hpeers_nonempty)
        have hsum_x : ∑ j ∈ peers, x j = (peers.card : ℝ) * xBar :=
          (mul_div_cancel₀ (∑ j ∈ peers, x j) hcard_pos.ne').symm
        have hrew : ∀ j : Fin m, -(φ - x j) / (2 * θ) = (x j - φ) / (2 * θ) :=
          fun j ↦ by rw [neg_sub]
        simp_rw [hrew]
        rw [PipeFuseWarmR1Cert.sum_div_real, Finset.sum_sub_distrib, Finset.sum_const,
          nsmul_eq_mul, hsum_x, hpeers_card]
        exact peers_ramp_sum_algebra ((m - 1 : ℕ) : ℝ) xBar φ (2 * θ)
      rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hsum_R.trans_eq hpeers_eq) h1q0_pos.le)
        (by positivity : 0 ≤ 1 / (m : ℝ))).trans_eq
        (ramp_sum_outer_algebra (m : ℝ) (1 - q0) ((m - 1 : ℕ) : ℝ) ((φ - xBar) / (2 * θ)))
    -- Combine all pieces via pure-ℝ `warm_step_combine_real` (zero let-unfolding)
    have hV2 :
        1 / ((m : ℝ) * p_min * ρ) + 1 +
          ((1 / ρ) * CB * (1 - (1 / 2) * Real.sin xBar ^ 2) ^ (m - 1)) -
          ((((m - 1 : ℕ) : ℝ) / m) * ((φ - xBar) / (2 * θ))) ≤ V 2 :=
      hwarm_1d xBar hxBar_bds.1 hxBar_bds.2
    change (1 + q0 * sepPotential phiFn V n 2 postB) +
        (∑ o ∈ Finset.univ.erase 0,
          stepWeight n 2 φ betas o * warmR1Cost1 n m (nextStageFuseBetas n 2 o postB)) ≤
      sepPotential phiFn V n 2 betas
    exact warm_step_combine_real h1q0_pos.le hbase_diff hhit_le hl_div_le hramp_sum_le hV2
section CertBridge
open PipeFuseCert
  (FuseStageRow checkFuseStageIdx checkFuseDriftCert checkOctantAtan checkClickRow
   of_allRange octantAtan_sound fuseDriftCert_sound clickRow_sound
   harmSumPow2_le_sum sqrtMUpNat_bounds harmSumPow2 sqrtMUpNat)
open PipeFuseWarmR1Cert
  (checkWarmR1Stage2 checkWarmR1StageIdx checkWarmR1CellRow warmR1Stage2_sound)
end CertBridge
end PipeFuse
end QuantumComputation.Specs.GroverFindAll
end Sec_PipelinedFuseWarmR1Pot
section Sec_PipelinedFuseM2MultiStage
section Sec_PipelinedFuseM2CertDefs
namespace QuantumComputation.Specs.GroverFindAll.PipeFuseM2Cert
open Real
open PipeFuseCert
  (FuseStageRow withForcedNat withForcedNat_eq allRange of_allRange
   checkOctantAtan checkClickRow checkFuseDriftCert checkFuseStageIdx
   harmSumPow2 sqrtMUpNat sq_le_imp_le arctan_le_pade54 pade56_le_arctan)
/-- Certified integer parameters for one bin `j < B` at stage `r ≥ 2` (`m = 2`). -/
structure M2BinCert where
  /-- Scaled lower-bound tangent `tcLo` (`0` or `1 ≤ tcLo ≤ 100000`). -/
  tcLo : ℕ
  /-- Certified upper bound `bLoHi / 10^12 ≥ arctan (tcLo / 100000)`. -/
  bLoHi : ℕ
  /-- Certified upper bound `dropHi / 10^12 ≥ 2 * (d - 1) * halfAngleSet n r`. -/
  dropHi : ℕ
  /-- Certified lower bound `tBfLo / 10^12` for `checkFuseDriftCert`. -/
  tBfLo : ℕ
  /-- Certified upper bound `tdHi / 10^8` for `checkFuseDriftCert`. -/
  tdHi : ℕ
  /-- Certified drift numerator `numU / 10^12` for `checkFuseDriftCert`. -/
  numU : ℕ
  /-- Certified unclicked-peer step bound `uNat`. -/
  uNat : ℕ
  /-- Certified upper bound `psiHi / 10^12` on `psiPiecewise` at `cNat - uNat`. -/
  psiHi : ℕ
  /-- Certified hit-potential upper bound `hHi ≥ uNat + psiHi`. -/
  hHi : ℕ
/-- Certified lock-drift parameters at `s_0 = s_1 = 0` for stage `r ≥ 2` (`m = 2`). -/
structure M2LockDrift where
  /-- Certified lower bound `tBfLo` for `checkFuseDriftCert` at `tNum`. -/
  tBfLo : ℕ
  /-- Certified upper bound `tdHi` for `checkFuseDriftCert` at `tNum`. -/
  tdHi : ℕ
  /-- Certified drift numerator `numU` for `checkFuseDriftCert` at `tNum`. -/
  numU : ℕ
  /-- Certified unclicked-locked-peer step bound `uLock`. -/
  uLock : ℕ
  /-- Certified upper bound `psiLock` at `cNat - uLock`. -/
  psiLock : ℕ
  /-- Certified single-click hit bound `hLock ≥ uLock + psiLock`. -/
  hLock : ℕ
  /-- Certified double-click hit bound `hBoth ≥ cNat + wPrev 0`. -/
  hBoth : ℕ
/-- Certified stage-`r` scalar parameters (`1 ≤ r ≤ min k rcap`) for `m = 2`. -/
structure M2StageScalar where
  /-- Scaled tangent `tNum` (`500 ≤ tNum ≤ 100000`). -/
  tNum : ℕ
  /-- Certified upper bound `phiHi / 10^12 ≥ arctan (tNum / 100000)`. -/
  phiHi : ℕ
  /-- Certified lower bound `phiLo / 10^12 ≤ arctan (tNum / 100000)`. -/
  phiLo : ℕ
  /-- Certified current-stage ramp cap `cSelf`. -/
  cSelf : ℕ
  /-- Bin width `dNat` at scale `10^12` (`1000 ≤ dNat`, `cSelf ≤ B * dNat`). -/
  dNat : ℕ
  /-- Certified click-term numerator `stepNum`. -/
  stepNum : ℕ
  /-- Certified reset-slot step bound `cNat` (`r ≥ 2`). -/
  cNat : ℕ
  /-- Certified lock-drift certificate at `s_0 = s_1 = 0` (`r ≥ 2`). -/
  lockDrift : M2LockDrift
/- ## Pure-Integer Certificate Checkers -/
/-- Octant-folded `[5/6]` / `[5/4]` Padé lower bound check `phiLo / 10^12 ≤ arctan (tn /
  10^5)`. -/
def checkOctantAtanLo (tn phiLo : ℕ) : Bool :=
  decide (tn ≤ 100000) &&
  if 12 * tn ≤ 500000 then
    withForcedNat (tn * tn) fun tt ↦
    decide (phiLo * (1155 * 1000000000000000000000000000000 +
        1575 * tt * 100000000000000000000 +
        525 * tt * tt * 10000000000 + 25 * tt * tt * tt) ≤
      tn * (1155 * 100000000000000000000 + 1190 * tt * 10000000000 +
        231 * tt * tt) * 100000000000000000)
  else
    withForcedNat (100000 - tn) fun a ↦
    withForcedNat (100000 + tn) fun b ↦
    withForcedNat (a * a) fun aa ↦
    withForcedNat (b * b) fun bb ↦
    withForcedNat (a * (945 * bb * bb + 735 * aa * bb + 64 * aa * aa)) fun p54 ↦
    withForcedNat (b * (945 * bb * bb + 1050 * aa * bb + 225 * aa * aa)) fun q54 ↦
    decide (phiLo * q54 + 1000000000000 * p54 ≤ 785398163397 * q54)
/-- Exact integer upper bound check `psiPiecewise B dNat w (y / 10^12) ≤ psiHi / 10^12`. -/
def checkPsiHi (B dNat : ℕ) (w : ℕ → ℕ) (y psiHi : ℕ) : Bool :=
  withForcedNat (y / dNat) fun q ↦
  withForcedNat (y % dNat) fun rem ↦
  if q < B then
    withForcedNat (w q) fun wq ↦
    withForcedNat (w (q + 1)) fun wq1 ↦
    decide (wq * dNat + (wq1 - wq) * rem ≤ psiHi * dNat)
  else
    decide (w B + (y - B * dNat) ≤ psiHi)
/-- Minimum adjacent knot difference across bin `j` and (when `j + 1 < B`) bin `j + 1`. -/
def minDiffNat (B : ℕ) (w : ℕ → ℕ) (j : ℕ) : ℕ :=
  withForcedNat (w (j + 1) - w j) fun dwCur ↦
  if j + 1 == B then dwCur else min dwCur (w (j + 2) - w (j + 1))
/-- Knot slope check `w j ≤ w (j + 1) ≤ w j + dNat` on bin `j < B`. -/
def checkM2KnotSlope (dNat : ℕ) (w : ℕ → ℕ) (j : ℕ) : Bool :=
  withForcedNat (w j) fun wj ↦
  withForcedNat (w (j + 1)) fun wj1 ↦
  decide (wj ≤ wj1) && decide (wj1 ≤ wj + dNat)
/-- Stage-`1` single-locked drift check on bin `j < B`. -/
def checkM2Stage1Bin (B dNat tn : ℕ) (w : ℕ → ℕ) (j : ℕ) : Bool :=
  withForcedNat (minDiffNat B w j) fun minDiff ↦
  withForcedNat (w j) fun wj ↦
  decide ((dNat - minDiff) * 100000 * 100000000 * 1000000000000 ≤
    dNat * 4 * tn * 99999999 * wj)
/-- Stage-`r` (`r ≥ 2`) single-locked drift check on bin `j < B`. -/
def checkM2StageGe2Bin (B r tn phiLo dNat tp phiHiP dNatP cNat : ℕ)
    (w wP : ℕ → ℕ) (bc : M2BinCert) (j : ℕ) : Bool :=
  match bc with
  | ⟨tcLo, bLoHi, dropHi, tBfLo, tdHi, numU, uNat, psiHi, hHi⟩ =>
    (if tcLo == 0 then
      uNat == cNat
    else
      decide (1 ≤ tcLo) && decide (tcLo ≤ 100000) &&
      checkOctantAtan tcLo bLoHi &&
      withForcedNat ((j + 1) * dNat * 1000000000001) fun dropRoot ↦
      decide (4 * r * dropRoot * dropRoot ≤
        (dropHi * 1000000000000) * (dropHi * 1000000000000)) &&
      decide (bLoHi + dropHi ≤ phiLo) &&
      checkFuseDriftCert r tcLo tp phiHiP tBfLo tdHi numU cNat uNat) &&
    checkPsiHi B dNatP wP (cNat - uNat) psiHi &&
    decide (uNat + psiHi ≤ hHi) &&
    withForcedNat (w j) fun wj ↦
    decide (hHi ≤ wj) &&
    withForcedNat (minDiffNat B w j) fun minDiff ↦
    withForcedNat ((dNat - minDiff) * 100000 * 100000000 * 1000000000000) fun lhsR ↦
    withForcedNat (dNat * 4 * tn * 99999999 * (wj - hHi)) fun rhsR ↦
    decide (lhsR * lhsR ≤ r * rhsR * rhsR)
/-- Full integer certificate check for stage `r = idx + 1 ≤ min k rcap`. -/
def checkM2StageIdx (B : ℕ) (stFn : ℕ → M2StageScalar) (wFn : ℕ → ℕ → ℕ)
    (binFn : ℕ → ℕ → M2BinCert) (idx : ℕ) : Bool :=
  let r := idx + 1
  let w := wFn r
  match stFn r with
  | ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, cNat,
      ⟨tBfLo, tdHi, numU, uLock, psiLock, hLock, hBoth⟩⟩ =>
    decide (500 ≤ tn) && decide (tn ≤ 100000) &&
    checkOctantAtan tn phiHi &&
    checkOctantAtanLo tn phiLo &&
    decide (1 ≤ cSelf) &&
    decide (phiHi * phiHi ≤ 4 * r * (cSelf - 1) * (cSelf - 1)) &&
    decide (1000 ≤ dNat) && decide (cSelf ≤ B * dNat) &&
    checkClickRow 2 r tn stepNum &&
    allRange (checkM2KnotSlope dNat w) B &&
    if r == 1 then
      decide (stepNum ≤ w 0) &&
      allRange (checkM2Stage1Bin B dNat tn w) B
    else
      let wP := wFn idx
      match stFn idx with
      | ⟨tp, phiHiP, _, _, dNatP, _, _, _⟩ =>
        checkFuseDriftCert r tn tp phiHiP tBfLo tdHi numU cNat uLock &&
        checkPsiHi B dNatP wP (cNat - uLock) psiLock &&
        decide (uLock + psiLock ≤ hLock) &&
        decide (cNat + wP 0 ≤ hBoth) &&
        withForcedNat (if hLock ≤ hBoth then hBoth - hLock else 0) fun extra ↦
        withForcedNat (w 0) fun w0 ↦
        decide (stepNum ≤ w0) &&
        decide (200000000 * hLock + extra ≤ 200000000 * (w0 - stepNum)) &&
        allRange (fun j ↦
          checkM2StageGe2Bin B r tn phiLo dNat tp phiHiP dNatP cNat w wP (binFn r j) j) B
/-- Knot dominance check `2 * w j ≤ 2 * vBridge + j * dNat` at the bridge stage `rcap`. -/
def checkM2BridgeKnot (dNat vBridge : ℕ) (w : ℕ → ℕ) (j : ℕ) : Bool :=
  decide (2 * w j ≤ 2 * vBridge + j * dNat)
/-- Effective `FuseStageRow` schedule stitching `stFn` (`r ≤ rcapCap`) to `tailFn` (`r >
  rcapCap`),
  placing `(vBridge, tNum, phiHi)` at `r = rcapCap` for stage `rcapCap + 1`. -/
def effSepRow (rcapCap vBridge : ℕ) (stFn : ℕ → M2StageScalar) (tailFn : ℕ → FuseStageRow)
    (r : ℕ) : FuseStageRow :=
  if r == 0 then
    ⟨0, 500, 0, 0, 0, 0, 0, 0, 0⟩
  else if r < rcapCap then
    ⟨0, (stFn r).tNum, (stFn r).phiHi, 0, 0, 0, 0, 0, 0⟩
  else if r == rcapCap then
    ⟨vBridge, (stFn rcapCap).tNum, (stFn rcapCap).phiHi, 0, 0, 0, 0, 0, 0⟩
  else
    tailFn r
/-- Full cell certificate check for `(m = 2, k = 2 ^ kIdx)` with piecewise-linear stages
  `1..min k rcapCap` and separable `FuseStageRow` tail `rcapCap + 1..k`. -/
def checkM2CellCert (B rcapCap : ℕ) (stFn : ℕ → M2StageScalar) (wFn : ℕ → ℕ → ℕ)
    (binFn : ℕ → ℕ → M2BinCert) (tailFn : ℕ → FuseStageRow)
    (kIdx topR vBridge rcNum : ℕ) : Bool :=
  let k := 2 ^ kIdx
  let rcap := min k rcapCap
  decide (1 ≤ B) &&
  decide (1 ≤ rcapCap) &&
  decide (1 ≤ kIdx) && decide (kIdx < 11) &&
  allRange (checkM2StageIdx B stFn wFn binFn) rcap &&
  decide (1 ≤ topR) &&
  if k ≤ rcapCap then
    match stFn k with
    | ⟨_, phiHiK, _, _, _, _, _, _⟩ =>
      decide (phiHiK * phiHiK ≤ 4 * k * (topR - 1) * (topR - 1)) &&
      decide ((wFn k 0 + topR) * 10000000000 * sqrtMUpNat 1 ≤
        rcNum * 785398163397 * harmSumPow2 kIdx)
  else
    match stFn rcapCap, tailFn k with
    | ⟨_, _, _, _, dNatCap, _, _, _⟩, ⟨vK, tK, phiHiK, _, _, _, _, _, _⟩ =>
      allRange (checkM2BridgeKnot dNatCap vBridge (wFn rcapCap)) (B + 1) &&
      allRange (fun idxT ↦
        checkFuseStageIdx (effSepRow rcapCap vBridge stFn tailFn) 1 (rcapCap + idxT))
        (k - rcapCap) &&
      decide (500 ≤ tK) && decide (tK ≤ 100000) &&
      checkOctantAtan tK phiHiK &&
      decide (phiHiK * phiHiK ≤ 4 * k * (topR - 1) * (topR - 1)) &&
      decide ((vK + topR) * 10000000000 * sqrtMUpNat 1 ≤
        rcNum * 785398163397 * harmSumPow2 kIdx)
/- ## Real-Analytic Soundness of `checkOctantAtanLo` -/
/-- Octant reflection lower bound `π / 4 - arctan ((1 - x) / (1 + x)) ≤ arctan x` (`0 ≤ x ≤
  1`). -/
theorem pi_div_four_sub_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : π / 4 - Real.arctan ((1 - x)
  / (1 + x)) ≤ Real.arctan x := by
  let G : ℝ → ℝ := fun z ↦ -(Real.arctan z + Real.arctan ((1 + (-1 : ℝ) * z) / (1 + z)))
  have hd : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt G 0 z := fun z hz ↦ by
    have hz0 : 0 ≤ z := hz; have h1z : 0 < 1 + z := (by linarith)
    have hnum : HasDerivAt (fun w : ℝ ↦ 1 + (-1 : ℝ) * w) (-1) z :=
      ((hasDerivAt_id' z).const_mul (-1)).const_add 1 |>.congr_deriv (by ring)
    have hden : HasDerivAt (fun w : ℝ ↦ 1 + w) 1 z := (hasDerivAt_id' z).const_add 1; have hq :=
      hnum.div hden h1z.ne'; have hcomp := (Real.hasDerivAt_arctan ((1 + (-1 : ℝ) * z) / (1 +
      z))).comp z hq; refine (((Real.hasDerivAt_arctan z).add hcomp).neg).congr_deriv ?_
    have hden2 : 0 < 1 + ((1 + (-1 : ℝ) * z) / (1 + z)) ^ 2 := (by positivity); have h1z2 : 0 < 1 +
      z ^ 2 := (by positivity); field_simp [h1z.ne', hden2.ne', h1z2.ne']; ring
  have hcont : ContinuousOn G (Set.Ici 0) := fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Set.Ici (0 : ℝ))) := fun z hz ↦ by
    rw [interior_Ici] at hz; exact (hd z hz.le).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff fun z hz ↦ by
    rw [interior_Ici] at hz; rw [(hd z hz.le).deriv]
  have hle := hmono hx0 (by norm_num : (0 : ℝ) ≤ 1) hx1; have hG1 : G 1 = -(π / 4) :=
    (by dsimp only [G]; norm_num [Real.arctan_one]); rw [hG1] at hle; dsimp only [G] at hle
  have hrew : (1 + (-1 : ℝ) * x) / (1 + x) = (1 - x) / (1 + x) := (by ring); rw [hrew] at hle;
    linarith
theorem octantAtanLo_sound {tn phiLo : ℕ} (h : checkOctantAtanLo tn phiLo = true) : (phiLo : ℝ) /
  1000000000000 ≤ Real.arctan ((tn : ℝ) / 100000) := by
  simp only [checkOctantAtanLo, Bool.and_eq_true] at h; have htn_le := of_decide_eq_true h.1
  have hbody := h.2; set x : ℝ := (tn : ℝ) / 100000; have hx0 : 0 ≤ x := (by positivity)
  split_ifs at hbody with h12
  · simp only [withForcedNat_eq] at hbody; have hnat := of_decide_eq_true hbody
    refine le_trans ?_ (pade56_le_arctan hx0)
    have hden_pos : 0 < 1155 + 1575 * x ^ 2 + 525 * x ^ 4 + 25 * x ^ 6 := by positivity
    rw [div_le_div_iff₀ (by norm_num) hden_pos]; have hcast : (phiLo : ℝ) * (1155 *
      1000000000000000000000000000000 + 1575 * (tn * tn : ℝ) * 100000000000000000000 + 525 * (tn *
      tn : ℝ) * (tn * tn) * 10000000000 + 25 * (tn * tn : ℝ) * (tn * tn) * (tn * tn)) ≤ (tn : ℝ) *
      (1155 * 100000000000000000000 + 1190 * (tn * tn : ℝ) * 10000000000 + 231 * (tn * tn : ℝ) * (tn
      * tn)) * 100000000000000000 := (by exact_mod_cast hnat); dsimp only [x]
    linear_combination hcast / 1000000000000000000000000000000
  · simp only [withForcedNat_eq] at hbody
    have hnat := of_decide_eq_true hbody; set a : ℕ := 100000 - tn
    set b : ℕ := 100000 + tn; set y : ℝ := (a : ℝ) / b; have hx1 : x ≤ 1 :=
      (by dsimp only [x]; have : (tn : ℝ) ≤ 100000 := (by exact_mod_cast htn_le); linarith)
    have hb_pos : (0 : ℝ) < b := (by exact_mod_cast (show 0 < b by omega)); have ha_sub : (a : ℝ) =
      100000 - tn := (by dsimp only [a]; rw [Nat.cast_sub htn_le]; push_cast; rfl); have hb_add : (b
      : ℝ) = 100000 + tn := (by dsimp only [b]; push_cast; rfl)
    have hy_eq : (1 - x) / (1 + x) = y := by
      dsimp only [x, y]; rw [ha_sub, hb_add]
      field_simp [(by positivity : (1 : ℝ) + (tn : ℝ) / 100000 ≠ 0),
        (by positivity : (100000 : ℝ) + tn ≠ 0)]
    have hy0 : 0 ≤ y := (by positivity); have hp54 := arctan_le_pade54 hy0; have hoct :=
      pi_div_four_sub_le_arctan hx0 hx1; rw [hy_eq] at hoct; have hpi : (785398163397 : ℝ) /
      1000000000000 ≤ π / 4 := (by linarith [Real.pi_gt_d20]); set p54R : ℝ := (a : ℝ) * (945 * (b :
      ℝ) ^ 4 + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4); set q54R : ℝ := (b : ℝ) * (945 *
      (b : ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 225 * (a : ℝ) ^ 4); have hq_pos : 0 < q54R :=
      (by dsimp only [q54R]; positivity)
    have hrat_eq : y * (945 + 735 * y ^ 2 + 64 * y ^ 4) / (945 + 1050 * y ^ 2 + 225 * y ^ 4) = p54R
      / q54R := by
      dsimp only [y, p54R, q54R]; have hden_y : 0 < 945 + 1050 * ((a : ℝ) / b) ^ 2 + 225 * ((a : ℝ)
        / b) ^ 4 := (by positivity); field_simp [hb_pos.ne', hden_y.ne', hq_pos.ne']
    have hcast : (phiLo : ℝ) * q54R + 1000000000000 * p54R ≤ 785398163397 * q54R := by
      have hraw : (phiLo : ℝ) * ((b : ℝ) * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b * b) + 225
        * (a * a) * (a * a))) + 1000000000000 * ((a : ℝ) * (945 * (b * b) * (b * b) + 735 * (a * a)
        * (b * b) + 64 * (a * a) * (a * a))) ≤ 785398163397 * ((b : ℝ) * (945 * (b * b) * (b * b) +
        1050 * (a * a) * (b * b) + 225 * (a * a) * (a * a))) := (by exact_mod_cast hnat)
      dsimp only [p54R, q54R]
      linarith [hraw, show (b : ℝ) * (945 * (b : ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 +
            225 * (a : ℝ) ^ 4) =
          (b : ℝ) * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b * b) +
            225 * (a * a) * (a * a)) by ring,
        show (a : ℝ) * (945 * (b : ℝ) ^ 4 + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4) =
          (a : ℝ) * (945 * (b * b) * (b * b) + 735 * (a * a) * (b * b) +
            64 * (a * a) * (a * a)) by ring]
    have hdiv : (phiLo : ℝ) / 1000000000000 ≤ (785398163397 : ℝ) / 1000000000000 - p54R / q54R := by
      have h1 : (phiLo : ℝ) / 1000000000000 = ((phiLo : ℝ) * q54R) / (1000000000000 * q54R) :=
        (by field_simp [hq_pos.ne']); have h2 : (785398163397 : ℝ) / 1000000000000 - p54R / q54R =
        (785398163397 * q54R - 1000000000000 * p54R) / (1000000000000 * q54R) :=
        (by field_simp [hq_pos.ne']); rw [h1, h2]
      exact div_le_div_of_nonneg_right (by linarith [hcast]) (by positivity)
    rw [hrat_eq] at hp54; linarith [hoct, hpi, hp54, hdiv]
/- ## Piecewise-Linear Clamped-Segment Profile `psiPiecewise` -/
/-- Clamped bin segment `min ((j + 1) * δ) (max 0 x) - min (j * δ) (max 0 x)`. -/
noncomputable def clampSeg (δ : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  min (((j + 1 : ℕ) : ℝ) * δ) (max 0 x) - min ((j : ℝ) * δ) (max 0 x)
/-- `B`-bin piecewise-linear potential profile with bin width `δ = dNat / 10^12`, knot
  values
  `w j / 10^12` at `j * δ` (`0 ≤ j ≤ B`), and unit-slope tail above `B * δ`. -/
noncomputable def psiPiecewise (B dNat : ℕ) (w : ℕ → ℕ) (x : ℝ) : ℝ :=
  let δ : ℝ := (dNat : ℝ) / 1000000000000
  ((w 0 : ℝ) / 1000000000000) +
    (∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j x)) +
    (max 0 x - min ((B : ℝ) * δ) (max 0 x))
theorem sum_range_clampSeg (δ : ℝ) (K : ℕ) (x : ℝ) : ∑ j ∈ Finset.range K, clampSeg δ j x = min ((K
  : ℝ) * δ) (max 0 x) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul]; exact (min_eq_left
      (le_max_left 0 x)).symm
  | succ k ih => rw [Finset.sum_range_succ, ih, clampSeg]; ring
theorem clampSeg_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) (x : ℝ) : 0 ≤ clampSeg δ j x := by
  dsimp only [clampSeg]; have hle : (j : ℝ) * δ ≤ ((j + 1 : ℕ) : ℝ) * δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hδ; linarith [min_le_min_right (max
    0 x) hle]
theorem clampSeg_mono {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) : clampSeg δ j x₁ ≤
  clampSeg δ j x₂ := by
  dsimp only [clampSeg]; set a : ℝ := (j : ℝ) * δ; set b : ℝ := ((j + 1 : ℕ) : ℝ) * δ; set u₁ : ℝ :=
    max 0 x₁; set u₂ : ℝ := max 0 x₂
  have hab : a ≤ b := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hδ
  have hu : u₁ ≤ u₂ := max_le_max le_rfl hx; by_cases hb1 : b ≤ u₁
  · rw [min_eq_left hb1, min_eq_left (hb1.trans hu), min_eq_left (hab.trans hb1), min_eq_left
      (hab.trans (hb1.trans hu))]
  · by_cases ha2 : u₂ ≤ a
    · rw [min_eq_right (hu.trans (ha2.trans hab)), min_eq_right (hu.trans ha2), min_eq_right
        (ha2.trans hab), min_eq_right ha2]; linarith
    · have hb1' : u₁ < b := not_le.1 hb1; have ha2' : a < u₂ := not_le.1 ha2; rw [min_eq_right
        hb1'.le, min_eq_left ha2'.le]; by_cases ha1 : a ≤ u₁
      · rw [min_eq_left ha1]; linarith [le_min hb1'.le hu]
      · have ha1' : u₁ < a := not_le.1 ha1; rw [min_eq_right ha1'.le]; linarith [le_min hab ha2'.le]
theorem tailSeg_mono (c : ℝ) {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) : max 0 x₁ - min c (max 0 x₁) ≤ max 0 x₂ -
  min c (max 0 x₂) := by
  set u₁ : ℝ := max 0 x₁; set u₂ : ℝ := max 0 x₂; have hu : u₁ ≤ u₂ := max_le_max le_rfl hx
  by_cases hc1 : c ≤ u₁
  · rw [min_eq_left hc1, min_eq_left (hc1.trans hu)]; linarith
  · have hc1' : u₁ < c := not_le.1 hc1; rw [min_eq_right hc1'.le]; linarith [min_le_right c u₂]
theorem psiPiecewise_nonneg (B dNat : ℕ) (w : ℕ → ℕ) (x : ℝ) : 0 ≤ psiPiecewise B dNat w x := by
  dsimp only [psiPiecewise]; have h1 : 0 ≤ (w 0 : ℝ) / 1000000000000 := (by positivity)
  have h2 : 0 ≤ ∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg ((dNat
    : ℝ) / 1000000000000) j x) := Finset.sum_nonneg fun j _ ↦ mul_nonneg (by positivity)
    (clampSeg_nonneg (by positivity) j x)
  have h3 : 0 ≤ max 0 x - min ((B : ℝ) * ((dNat : ℝ) / 1000000000000)) (max 0 x) :=
    (by linarith [min_le_right ((B : ℝ) * ((dNat : ℝ) / 1000000000000)) (max 0 x)]); linarith
theorem psiPiecewise_mono {B dNat : ℕ} {w : ℕ → ℕ} {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) : psiPiecewise B dNat
  w x₁ ≤ psiPiecewise B dNat w x₂ := by
  dsimp only [psiPiecewise]
  have hsum : ∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg ((dNat :
    ℝ) / 1000000000000) j x₁) ≤ ∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) *
    clampSeg ((dNat : ℝ) / 1000000000000) j x₂) := Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (clampSeg_mono (by positivity) j hx) (by positivity); have htail :=
    tailSeg_mono ((B : ℝ) * ((dNat : ℝ) / 1000000000000)) hx; linarith
theorem psiPiecewise_sub_le {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ j < B, w j ≤ w (j + 1)
  ∧ w (j + 1) ≤ w j + dNat) {x₁ x₂ : ℝ} (hx₁ : 0 ≤ x₁) (hx : x₁ ≤ x₂) : psiPiecewise B dNat w x₂ -
  psiPiecewise B dNat w x₁ ≤ x₂ - x₁ := by
  dsimp only [psiPiecewise]; set δ : ℝ := (dNat : ℝ) / 1000000000000
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd; have hδ_nn : 0 ≤ δ := (by positivity)
  have hdiff_sum : (∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j
    x₂)) - (∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j x₁)) ≤
    (∑ j ∈ Finset.range B, clampSeg δ j x₂) - (∑ j ∈ Finset.range B, clampSeg δ j x₁) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]; refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [Finset.mem_range] at hj; have hinc_nn : 0 ≤ clampSeg δ j x₂ - clampSeg δ j x₁ :=
      sub_nonneg.2 (clampSeg_mono hδ_nn j hx)
    have hslope_le1 : ((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ) ≤ 1 := by
      rw [div_le_one hd_pos]; have hsub_le : w (j + 1) - w j ≤ dNat :=
        (by have h2 := (hw j hj).2; omega); exact_mod_cast hsub_le
    calc (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j x₂ -
          (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j x₁
        = (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (clampSeg δ j x₂ - clampSeg δ j x₁) := by
          ring
      _ ≤ 1 * (clampSeg δ j x₂ - clampSeg δ j x₁) := mul_le_mul_of_nonneg_right hslope_le1 hinc_nn
      _ = clampSeg δ j x₂ - clampSeg δ j x₁ := one_mul _
  rw [sum_range_clampSeg, sum_range_clampSeg] at hdiff_sum
  have hm1 : max 0 x₁ = x₁ := max_eq_right hx₁; have hm2 : max 0 x₂ = x₂ := max_eq_right (hx₁.trans
    hx); rw [hm1, hm2] at hdiff_sum ⊢; linarith [hdiff_sum]
/-- Affine evaluation of `psiPiecewise B dNat w x` on bin `q < B` (`q * δ ≤ x ≤ (q + 1) *
  δ`). -/
theorem psiPiecewise_on_bin {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ j < B, w j ≤ w (j + 1)
  ∧ w (j + 1) ≤ w j + dNat) {q : ℕ} (hq : q < B) {x : ℝ} (hx_lo : (q : ℝ) * ((dNat : ℝ) /
  1000000000000) ≤ x) (hx_hi : x ≤ ((q + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000)) : psiPiecewise
  B dNat w x = ((w q : ℝ) / 1000000000000) + (((w (q + 1) - w q : ℕ) : ℝ) / (dNat : ℝ)) * (x - (q :
  ℝ) * ((dNat : ℝ) / 1000000000000)) := by
  dsimp only [psiPiecewise]; set δ : ℝ := (dNat : ℝ) / 1000000000000
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd; have hδ_nn : 0 ≤ δ := (by positivity)
  have hx0 : 0 ≤ x := le_trans (by positivity) hx_lo; have hmx : max 0 x = x := max_eq_right hx0
  have hx_le_B : x ≤ (B : ℝ) * δ := hx_hi.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.succ_le_of_lt hq) hδ_nn); have htail : max 0 x - min ((B : ℝ) * δ) (max 0
    x) = 0 := (by rw [hmx, min_eq_right hx_le_B, sub_self]); rw [htail, add_zero]
  have hsplit : Finset.range B = Finset.range q ∪ (insert q (Finset.Ico (q + 1) B)) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_Ico]; omega
  have hdisj1 : Disjoint (Finset.range q) (insert q (Finset.Ico (q + 1) B)) := by
    rw [Finset.disjoint_left]; intro j hj1 hj2; simp only [Finset.mem_range, Finset.mem_insert,
      Finset.mem_Ico] at hj1 hj2; omega
  have hnotmem : q ∉ Finset.Ico (q + 1) B := (by simp); rw [hsplit, Finset.sum_union hdisj1,
    Finset.sum_insert hnotmem]
  have hprefix : ∑ j ∈ Finset.range q, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j x)
    = ((w q : ℝ) - w 0) / 1000000000000 := by
    have hcongr : ∑ j ∈ Finset.range q, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j
      x) = ∑ j ∈ Finset.range q, (((w (j + 1) : ℝ) - w j) / 1000000000000) := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_; rw [Finset.mem_range] at hj; have hj1_le : ((j + 1
        : ℕ) : ℝ) * δ ≤ x := (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj)
        hδ_nn).trans hx_lo; have hj_le : (j : ℝ) * δ ≤ x := (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hj.le) hδ_nn).trans hx_lo; have hseg : clampSeg δ j x = δ :=
        (by dsimp only [clampSeg]; rw [hmx, min_eq_left hj1_le, min_eq_left hj_le]; push_cast; ring)
      rw [hseg, Nat.cast_sub (hw j (hj.trans hq)).1]; dsimp only [δ]; field_simp [hd_pos.ne']
    rw [hcongr]; clear hcongr hsplit hdisj1 hnotmem hx_lo hx_hi hq
    induction q with
    | zero => simp [sub_self]
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have hmid : clampSeg δ q x = x - (q : ℝ) * δ :=
    (by dsimp only [clampSeg]; rw [hmx, min_eq_right hx_hi, min_eq_left hx_lo])
  have hsuffix : ∑ j ∈ Finset.Ico (q + 1) B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg
    δ j x) = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_; rw [Finset.mem_Ico] at hj
    have hj_ge : x ≤ (j : ℝ) * δ := hx_hi.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj.1)
      hδ_nn); have hj1_ge : x ≤ ((j + 1 : ℕ) : ℝ) * δ := hj_ge.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_succ j) hδ_nn); have hseg : clampSeg δ j x = 0 :=
      (by dsimp only [clampSeg]; rw [hmx, min_eq_right hj1_ge, min_eq_right hj_ge, sub_self])
    rw [hseg, mul_zero]
  rw [hprefix, hmid, hsuffix, add_zero]; ring
/-- Tail evaluation of `psiPiecewise B dNat w x` above `B * δ` (`B * δ ≤ x`). -/
theorem psiPiecewise_above_cap {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ j < B, w j ≤ w (j +
  1) ∧ w (j + 1) ≤ w j + dNat) {x : ℝ} (hx_ge : (B : ℝ) * ((dNat : ℝ) / 1000000000000) ≤ x) :
  psiPiecewise B dNat w x = ((w B : ℝ) / 1000000000000) + (x - (B : ℝ) * ((dNat : ℝ) /
  1000000000000)) := by
  dsimp only [psiPiecewise]; set δ : ℝ := (dNat : ℝ) / 1000000000000
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd; have hδ_nn : 0 ≤ δ := (by positivity)
  have hx0 : 0 ≤ x := le_trans (by positivity) hx_ge; have hmx : max 0 x = x := max_eq_right hx0
  have htail : max 0 x - min ((B : ℝ) * δ) (max 0 x) = x - (B : ℝ) * δ :=
    (by rw [hmx, min_eq_left hx_ge])
  have hsum : ∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j x) =
    ((w B : ℝ) - w 0) / 1000000000000 := by
    have hcongr : ∑ j ∈ Finset.range B, ((((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * clampSeg δ j
      x) = ∑ j ∈ Finset.range B, (((w (j + 1) : ℝ) - w j) / 1000000000000) := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_; rw [Finset.mem_range] at hj; have hj1_le : ((j + 1
        : ℕ) : ℝ) * δ ≤ x := (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj)
        hδ_nn).trans hx_ge; have hj_le : (j : ℝ) * δ ≤ x := (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hj.le) hδ_nn).trans hx_ge; have hseg : clampSeg δ j x = δ :=
        (by dsimp only [clampSeg]; rw [hmx, min_eq_left hj1_le, min_eq_left hj_le]; push_cast; ring)
      rw [hseg, Nat.cast_sub (hw j hj).1]; dsimp only [δ]; field_simp [hd_pos.ne']
    rw [hcongr]; clear hcongr hw hx_ge htail
    induction B with
    | zero => simp [sub_self]
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  rw [hsum, htail]; ring
/-- Exact knot evaluation `psiPiecewise B dNat w (k * δ) = w k / 10^12` (`k ≤ B`). -/
theorem psiPiecewise_knot {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ j < B, w j ≤ w (j + 1) ∧
  w (j + 1) ≤ w j + dNat) {k : ℕ} (hk : k ≤ B) : psiPiecewise B dNat w ((k : ℝ) * ((dNat : ℝ) /
  1000000000000)) = (w k : ℝ) / 1000000000000 := by
  set δ : ℝ := (dNat : ℝ) / 1000000000000; have hδ_nn : 0 ≤ δ := (by positivity)
  rcases hk.eq_or_lt with rfl | hlt
  · rw [psiPiecewise_above_cap hd hw le_rfl]; ring
  · rw [psiPiecewise_on_bin hd hw hlt le_rfl (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_succ k) hδ_nn)]; ring
/-- Soundness of `checkPsiHi`: `psiPiecewise B dNat w (y / 10^12) ≤ psiHi / 10^12`. -/
theorem checkPsiHi_sound {B dNat : ℕ} {w : ℕ → ℕ} {y psiHi : ℕ} (hd : 1 ≤ dNat) (hw : ∀ j < B, w j ≤
  w (j + 1) ∧ w (j + 1) ≤ w j + dNat) (hchk : checkPsiHi B dNat w y psiHi = true) : psiPiecewise B
  dNat w ((y : ℝ) / 1000000000000) ≤ (psiHi : ℝ) / 1000000000000 := by
  simp only [checkPsiHi, withForcedNat_eq] at hchk; set q : ℕ := y / dNat; set rem : ℕ := y % dNat
  have hdiv_mod : q * dNat + rem = y :=
    (by dsimp only [q, rem]; rw [mul_comm]; exact Nat.div_add_mod y dNat)
  have hrem_lt : rem < dNat := Nat.mod_lt y hd; have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd
  set δ : ℝ := (dNat : ℝ) / 1000000000000
  split_ifs at hchk with hq
  · have hnat := of_decide_eq_true hchk
    have hy_lo : (q : ℝ) * δ ≤ (y : ℝ) / 1000000000000 := by
      dsimp only [δ]; have h1 : (q * dNat : ℕ) ≤ y := (by omega); have h2 : (q : ℝ) * dNat ≤ y :=
        (by exact_mod_cast h1); linarith
    have hy_hi : (y : ℝ) / 1000000000000 ≤ ((q + 1 : ℕ) : ℝ) * δ := by
      dsimp only [δ]; have h1 : y ≤ (q + 1) * dNat := (by rw [add_mul, one_mul]; omega)
      have h2 : (y : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * dNat := (by exact_mod_cast h1); linarith
    rw [psiPiecewise_on_bin hd hw hq hy_lo hy_hi]
    have hrem_eq : (y : ℝ) / 1000000000000 - (q : ℝ) * δ = (rem : ℝ) / 1000000000000 := by
      dsimp only [δ]; have hy_r : (y : ℝ) = (q : ℝ) * dNat + rem :=
        (by exact_mod_cast hdiv_mod.symm); rw [hy_r]; ring
    rw [hrem_eq]; have hcast : (w q : ℝ) * dNat + ((w (q + 1) - w q : ℕ) : ℝ) * rem ≤ (psiHi : ℝ) *
      dNat := (by exact_mod_cast hnat); have hrew : ((w q : ℝ) / 1000000000000) + (((w (q + 1) - w q
      : ℕ) : ℝ) / (dNat : ℝ)) * ((rem : ℝ) / 1000000000000) = ((w q : ℝ) * dNat + ((w (q + 1) - w q
      : ℕ) : ℝ) * rem) / ((dNat : ℝ) * 1000000000000) := (by field_simp [hd_pos.ne'])
    have hrhs : (psiHi : ℝ) / 1000000000000 = ((psiHi : ℝ) * dNat) / ((dNat : ℝ) * 1000000000000) :=
      (by field_simp [hd_pos.ne']); rw [hrew, hrhs]
    exact div_le_div_of_nonneg_right hcast (by positivity)
  · have hnat := of_decide_eq_true hchk; have hB_le_q : B ≤ q := not_lt.1 hq
    have hBd_le_y : B * dNat ≤ y := by
      calc B * dNat ≤ q * dNat := Nat.mul_le_mul_right dNat hB_le_q
        _ ≤ y := by omega
    have hy_ge : (B : ℝ) * δ ≤ (y : ℝ) / 1000000000000 :=
      (by dsimp only [δ]; have h1 : (B : ℝ) * dNat ≤ y := (by exact_mod_cast hBd_le_y); linarith)
    rw [psiPiecewise_above_cap hd hw hy_ge]; have hcast : (w B : ℝ) + ((y - B * dNat : ℕ) : ℝ) ≤
      psiHi := (by exact_mod_cast hnat); rw [Nat.cast_sub hBd_le_y, Nat.cast_mul] at hcast
    linarith [div_le_div_of_nonneg_right hcast (by norm_num : (0 : ℝ) ≤ 1000000000000)]
/-- Bin location without `Nat.floor`: any `x ∈ [0, K * δ]` (`1 ≤ K`, `0 < δ`) lies in some
  `[j * δ, (j + 1) * δ]` with `j < K`. -/
theorem exists_bin_of_le {K : ℕ} (hK : 1 ≤ K) {δ x : ℝ} (_hδ : 0 < δ) (hx0 : 0 ≤ x) (hxK : x ≤ (K :
  ℝ) * δ) : ∃ j < K, (j : ℝ) * δ ≤ x ∧ x ≤ ((j + 1 : ℕ) : ℝ) * δ := by
  induction K with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · refine ⟨0, by omega, by simp [hx0], ?_⟩; simpa using hxK
    · by_cases hle : x ≤ (k : ℝ) * δ
      · obtain ⟨j, hj, hlo, hhi⟩ := ih hk_pos hle; exact ⟨j, by omega, hlo, hhi⟩
      · have hlt : (k : ℝ) * δ < x := not_le.1 hle; exact ⟨k, by omega, hlt.le, hxK⟩
/-- Lower bound on `psiPiecewise B dNat w (x' + h) - psiPiecewise B dNat w x'` when
  `x' ∈ [j * δ, (j + 1) * δ]` (`j < B`) and `0 ≤ h ≤ δ`. -/
theorem psiPiecewise_step_ge_minDiff {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ i < B, w i ≤ w
  (i + 1) ∧ w (i + 1) ≤ w i + dNat) {j : ℕ} (hj : j < B) {x' h : ℝ} (hx_lo : (j : ℝ) * ((dNat : ℝ) /
  1000000000000) ≤ x') (hx_hi : x' ≤ ((j + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000)) (hh0 : 0 ≤ h)
  (hh_hi : h ≤ (dNat : ℝ) / 1000000000000) : ((minDiffNat B w j : ℝ) / (dNat : ℝ)) * h ≤
  psiPiecewise B dNat w (x' + h) - psiPiecewise B dNat w x' := by
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd
  have hmd_le_cur : (minDiffNat B w j : ℝ) ≤ (w (j + 1) - w j : ℕ) := by
    dsimp only [minDiffNat]; rw [withForcedNat_eq]
    split_ifs
    · exact le_rfl
    · exact_mod_cast Nat.min_le_left _ _
  have hs_cur : (minDiffNat B w j : ℝ) / dNat ≤ ((w (j + 1) - w j : ℕ) : ℝ) / dNat :=
    div_le_div_of_nonneg_right hmd_le_cur hd_pos.le; rw [psiPiecewise_on_bin hd hw hj hx_lo hx_hi]
  by_cases hstay : x' + h ≤ ((j + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000)
  · rw [psiPiecewise_on_bin hd hw hj (by linarith) hstay]; have hdiff : (((w j : ℝ) / 1000000000000)
      + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * ((x' + h) - (j : ℝ) * ((dNat : ℝ) /
      1000000000000))) - (((w j : ℝ) / 1000000000000) + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) *
      (x' - (j : ℝ) * ((dNat : ℝ) / 1000000000000))) = (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) *
      h := (by ring); rw [hdiff]; exact mul_le_mul_of_nonneg_right hs_cur hh0
  · have hstay' : ((j + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000) < x' + h := not_le.1 hstay
    set xMid : ℝ := ((j + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000); have hh1_nn : 0 ≤ xMid - x' :=
      sub_nonneg.2 hx_hi; have hh2_nn : 0 ≤ (x' + h) - xMid := sub_nonneg.2 hstay'.le
    have hmid_val : ((w j : ℝ) / 1000000000000) + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (xMid
      - (j : ℝ) * ((dNat : ℝ) / 1000000000000)) = (w (j + 1) : ℝ) / 1000000000000 := by
      have h1 : xMid - (j : ℝ) * ((dNat : ℝ) / 1000000000000) = (dNat : ℝ) / 1000000000000 :=
        (by dsimp only [xMid]; push_cast; ring)
      rw [h1, Nat.cast_sub (hw j hj).1]; field_simp [hd_pos.ne']; ring
    have hpart1 : ((minDiffNat B w j : ℝ) / dNat) * (xMid - x') ≤ (w (j + 1) : ℝ) / 1000000000000 -
      (((w j : ℝ) / 1000000000000) + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (x' - (j : ℝ) *
      ((dNat : ℝ) / 1000000000000))) := by
      rw [← hmid_val]; have heq : (((w j : ℝ) / 1000000000000) + (((w (j + 1) - w j : ℕ) : ℝ) /
        (dNat : ℝ)) * (xMid - (j : ℝ) * ((dNat : ℝ) / 1000000000000))) - (((w j : ℝ) /
        1000000000000) + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (x' - (j : ℝ) * ((dNat : ℝ) /
        1000000000000))) = (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (xMid - x') := (by ring)
      rw [heq]; exact mul_le_mul_of_nonneg_right hs_cur hh1_nn
    by_cases hj1_lt : j + 1 < B
    · have hx2_hi : x' + h ≤ ((j + 1 + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000) := by
        have h1 : ((j + 1 + 1 : ℕ) : ℝ) * ((dNat : ℝ) / 1000000000000) = xMid + (dNat : ℝ) /
          1000000000000 := (by dsimp only [xMid]; push_cast; ring)
        rw [h1]; exact add_le_add hx_hi hh_hi
      rw [psiPiecewise_on_bin hd hw hj1_lt hstay'.le hx2_hi]; have hne : (j + 1 == B) = false :=
        beq_false_of_ne (by omega)
      have hmd_le_nxt : (minDiffNat B w j : ℝ) ≤ (w (j + 1 + 1) - w (j + 1) : ℕ) := by
        dsimp only [minDiffNat]; rw [withForcedNat_eq, hne]; simp only [Bool.false_eq_true,
          ↓reduceIte]; exact_mod_cast Nat.min_le_right _ _
      have hs_nxt : (minDiffNat B w j : ℝ) / dNat ≤ ((w (j + 1 + 1) - w (j + 1) : ℕ) : ℝ) / dNat :=
        div_le_div_of_nonneg_right hmd_le_nxt hd_pos.le
      have hpart2 : ((minDiffNat B w j : ℝ) / dNat) * ((x' + h) - xMid) ≤ (((w (j + 1) : ℝ) /
        1000000000000) + (((w (j + 1 + 1) - w (j + 1) : ℕ) : ℝ) / (dNat : ℝ)) * ((x' + h) - xMid)) -
        ((w (j + 1) : ℝ) / 1000000000000) := by
        have heq : (((w (j + 1) : ℝ) / 1000000000000) + (((w (j + 1 + 1) - w (j + 1) : ℕ) : ℝ) /
          (dNat : ℝ)) * ((x' + h) - xMid)) - ((w (j + 1) : ℝ) / 1000000000000) = (((w (j + 1 + 1) -
          w (j + 1) : ℕ) : ℝ) / (dNat : ℝ)) * ((x' + h) - xMid) := (by ring)
        rw [heq]; exact mul_le_mul_of_nonneg_right hs_nxt hh2_nn
      have hh_split : ((minDiffNat B w j : ℝ) / dNat) * h = ((minDiffNat B w j : ℝ) / dNat) * (xMid
        - x') + ((minDiffNat B w j : ℝ) / dNat) * ((x' + h) - xMid) := (by ring)
      change ((minDiffNat B w j : ℝ) / (dNat : ℝ)) * h ≤ ((w (j + 1) : ℝ) / 1000000000000 + (((w (j
        + 1 + 1) - w (j + 1) : ℕ) : ℝ) / (dNat : ℝ)) * ((x' + h) - xMid)) - ((w j : ℝ) /
        1000000000000 + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (x' - (j : ℝ) * ((dNat : ℝ) /
        1000000000000))); linarith [hpart1, hpart2, hh_split]
    · have hj1_eq : j + 1 = B := (by omega); have hx2_ge : (B : ℝ) * ((dNat : ℝ) / 1000000000000) ≤
        x' + h := (by rw [← hj1_eq]; exact hstay'.le); rw [psiPiecewise_above_cap hd hw hx2_ge]
      have hwB : w B = w (j + 1) := (by rw [hj1_eq]); have hB_mid : (B : ℝ) * ((dNat : ℝ) /
        1000000000000) = xMid := (by dsimp only [xMid]; rw [hj1_eq]); rw [hwB, hB_mid]
      have hmd_le1 : (minDiffNat B w j : ℝ) / dNat ≤ 1 := by
        rw [div_le_one hd_pos]; have hsub_le : w (j + 1) - w j ≤ dNat :=
          (by have h2 := (hw j hj).2; omega); exact hmd_le_cur.trans (by exact_mod_cast hsub_le)
      have hpart2 : ((minDiffNat B w j : ℝ) / dNat) * ((x' + h) - xMid) ≤ (x' + h) - xMid :=
        mul_le_of_le_one_left hh2_nn hmd_le1; have hh_split : ((minDiffNat B w j : ℝ) / dNat) * h =
        ((minDiffNat B w j : ℝ) / dNat) * (xMid - x') + ((minDiffNat B w j : ℝ) / dNat) * ((x' + h)
        - xMid) := (by ring); linarith [hpart1, hpart2, hh_split]
/-- Pointwise dominance `psiPiecewise B dNat w x ≤ vBridge / 10^12 + x / 2` across `[0, B *
  δ]`
  from knot inequalities `2 * w j ≤ 2 * vBridge + j * dNat` (`0 ≤ j ≤ B`). -/
theorem psiPiecewise_le_bridge {B dNat vBridge : ℕ} {w : ℕ → ℕ} (hB : 1 ≤ B) (hd : 1 ≤ dNat) (hw : ∀
  i < B, w i ≤ w (i + 1) ∧ w (i + 1) ≤ w i + dNat) (hbr : allRange (checkM2BridgeKnot dNat vBridge
  w) (B + 1) = true) {x : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ (B : ℝ) * ((dNat : ℝ) / 1000000000000)) :
  psiPiecewise B dNat w x ≤ ((vBridge : ℝ) / 1000000000000) + x / 2 := by
  set δ : ℝ := (dNat : ℝ) / 1000000000000; have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨j, hj, hlo, hhi⟩ := exists_bin_of_le hB hδ_pos hx0 hxB; rw [psiPiecewise_on_bin hd hw hj
    hlo hhi]; have hkj_b := of_allRange hbr (by omega : j < B + 1)
  have hkj1_b := of_allRange hbr (by omega : j + 1 < B + 1)
  simp only [checkM2BridgeKnot] at hkj_b hkj1_b; have hkj : (2 : ℝ) * w j ≤ 2 * vBridge + (j : ℝ) *
    dNat := (by exact_mod_cast of_decide_eq_true hkj_b); have hkj1 : (2 : ℝ) * w (j + 1) ≤ 2 *
    vBridge + ((j + 1 : ℕ) : ℝ) * dNat := (by exact_mod_cast of_decide_eq_true hkj1_b); set t : ℝ :=
    (x - (j : ℝ) * δ) / δ; have ht0 : 0 ≤ t := div_nonneg (by linarith) hδ_pos.le
  have ht1 : t ≤ 1 := by
    rw [div_le_one hδ_pos]; have : ((j + 1 : ℕ) : ℝ) * δ = (j : ℝ) * δ + δ := (by push_cast; ring)
    linarith
  have hx_eq : x = (j : ℝ) * δ + t * δ := by dsimp only [t]; field_simp [hδ_pos.ne']; ring
  have hlhs_eq : ((w j : ℝ) / 1000000000000) + (((w (j + 1) - w j : ℕ) : ℝ) / (dNat : ℝ)) * (x - (j
    : ℝ) * δ) = (1 - t) * ((w j : ℝ) / 1000000000000) + t * ((w (j + 1) : ℝ) / 1000000000000) :=
    (by rw [hx_eq, Nat.cast_sub (hw j hj).1]; dsimp only [δ]; field_simp [hd_pos.ne']; ring)
  have hrhs_eq : ((vBridge : ℝ) / 1000000000000) + x / 2 = (1 - t) * (((vBridge : ℝ) + (j : ℝ) *
    dNat / 2) / 1000000000000) + t * (((vBridge : ℝ) + ((j + 1 : ℕ) : ℝ) * dNat / 2) /
    1000000000000) := (by rw [hx_eq]; dsimp only [δ]; push_cast; ring); rw [hlhs_eq, hrhs_eq]
  have he0 : (w j : ℝ) / 1000000000000 ≤ ((vBridge : ℝ) + (j : ℝ) * dNat / 2) / 1000000000000 :=
    div_le_div_of_nonneg_right (by linarith [hkj]) (by norm_num)
  have he1 : (w (j + 1) : ℝ) / 1000000000000 ≤ ((vBridge : ℝ) + ((j + 1 : ℕ) : ℝ) * dNat / 2) /
    1000000000000 := div_le_div_of_nonneg_right
    (by linarith [hkj1, (by push_cast; rfl : ((j + 1 : ℕ) : ℝ) = j + 1)]) (by norm_num)
  exact add_le_add (mul_le_mul_of_nonneg_left he0 (by linarith)) (mul_le_mul_of_nonneg_left he1 ht0)
end QuantumComputation.Specs.GroverFindAll.PipeFuseM2Cert
end Sec_PipelinedFuseM2CertDefs
section Sec_PipelinedFuseM2MultiStage
namespace QuantumComputation.Specs.GroverFindAll.PipeFuseM2
open Real
open scoped NNReal NNRat ENNReal
open PipeFuseCert
  (FuseStageRow withForcedNat_eq allRange of_allRange
   checkOctantAtan checkClickRow checkFuseDriftCert checkFuseStageIdx
   harmSumPow2 sqrtMUpNat sq_le_imp_le pade56_le_arctan
   octantAtan_sound fuseDriftCert_sound clickRow_sound
   harmSumPow2_le_sum sqrtMUpNat_bounds)
open PipeFuseM2Cert
  (M2BinCert M2StageScalar checkOctantAtanLo checkPsiHi minDiffNat
   checkM2KnotSlope checkM2Stage1Bin checkM2StageGe2Bin checkM2StageIdx
   checkM2BridgeKnot effSepRow checkM2CellCert
   octantAtanLo_sound psiPiecewise psiPiecewise_nonneg psiPiecewise_mono
   psiPiecewise_sub_le psiPiecewise_knot checkPsiHi_sound
   exists_bin_of_le psiPiecewise_step_ge_minDiff psiPiecewise_le_bridge)
open PipeFuse
  (CertifiedFuseCell sepPotential phiFnOfFuseRow vFnOfFuseRow unclickedFuseRem
   pow_two_bounds_100 halfAngleSet_bounds_100 two_mul_le_pow_100
   phi_and_lockedAlpha_bounds_pi_div_three_100 unclicked_fuse_branch_le_100
   sum_erase_zero_stepWeight_expOnHitFuse_one
   sum_erase_zero_stepWeight_expOnHitFuse_sepPotential)
/- ## 1. Threshold Schedule & `Fin (2 ^ 1)` Outcome Helpers -/
theorem sum_erase_zero_fin_four {M : Type*} [AddCommMonoid M] (g : Fin (2 ^ (2 ^ 1)) → M) :
    (∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ (2 ^ 1))), g o) =
      g ⟨1, by decide⟩ + g ⟨2, by decide⟩ + g ⟨3, by decide⟩ := by
  have herase : Finset.univ.erase (0 : Fin (2 ^ (2 ^ 1))) = {⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3,
    by omega⟩} := by
    ext ⟨x, hx⟩; have hx4 : x < 4 := hx; simp only [Finset.mem_erase, ne_eq, Finset.mem_univ,
      and_true, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    change x ≠ 0 ↔ x = 1 ∨ x = 2 ∨ x = 3; omega
  rw [herase, Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_pair (by simp [Fin.ext_iff]), ←
    add_assoc]
theorem remStepsSlot_mono_beta {n r : ℕ} (hr1 : 1 ≤ r) (φ : ℝ) {β₁ β₂ : ℝ} (hβ : β₁ ≤ β₂) :
  remStepsSlot n r φ β₂ ≤ remStepsSlot n r φ β₁ := by
  dsimp only [remStepsSlot]; have hθ : 0 < halfAngleSet n r := Real.arcsin_pos.2 (Real.sqrt_pos.2
    (div_pos (Nat.cast_pos.2 hr1) (by positivity))); exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (by linarith) (by positivity))
theorem remStepsSlot_le_of_three_add_max {n rp : ℕ} (hrp1 : 1 ≤ rp) {φp y U : ℝ} (hU_nn : 0 ≤ U) (hb
  : 3 + max 0 ((φp - y) / (2 * halfAngleSet n rp)) ≤ U) : (remStepsSlot n rp φp y : ℝ) ≤ U := by
  have hθp : 0 < halfAngleSet n rp := Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos (Nat.cast_pos.2
    hrp1) (by positivity))); by_cases hge : φp ≤ y
  · rw [(remStepsSlot_eq_zero_iff hrp1 φp y).2 hge]; simpa using hU_nn
  · have hlt : y < φp := not_le.1 hge; dsimp only [remStepsSlot]; have hq_nn : 0 ≤ (φp - y) / (2 *
      halfAngleSet n rp) := div_nonneg (by linarith) (by positivity); have hq_le : (φp - y) / (2 *
      halfAngleSet n rp) ≤ max 0 ((φp - y) / (2 * halfAngleSet n rp)) := le_max_right _ _
    linarith [Nat.ceil_lt_add_one hq_nn]
theorem knotSlope_of_allRange {B dNat : ℕ} {w : ℕ → ℕ}
    (hall : allRange (checkM2KnotSlope dNat w) B = true) :
    ∀ j < B, w j ≤ w (j + 1) ∧ w (j + 1) ≤ w j + dNat := fun j hj ↦ by
  have hj_chk := of_allRange hall hj
  simp only [checkM2KnotSlope, withForcedNat_eq, Bool.and_eq_true] at hj_chk
  exact ⟨of_decide_eq_true hj_chk.1, of_decide_eq_true hj_chk.2⟩
/- ## 4. Two-Slot Locked Click Algebra (`m = 2`) -/
theorem two_locked_one_sub_q0_bounds {p0 p1 p_min : ℝ} (hp_min : 0 < p_min) (hp0_lo : p_min ≤ p0)
  (hp1_lo : p_min ≤ p1) (hp0_hi : p0 ≤ 1 / (100000000 * (2 : ℝ))) (hp1_hi : p1 ≤ 1 / (100000000 * (2
  : ℝ))) :
    let q0 := (1 - p0) * (1 - p1); let p_max : ℝ := 1 / (100000000 * (2 : ℝ))
    0 < 1 - q0 ∧ 2 * p_min * (1 - 2 * p_max) ≤ 1 - q0 ∧ (p0 + p1) * (1 - 2 * p_max) ≤ 1 - q0 ∧ p0 ≤
      1 - q0 ∧ p1 ≤ 1 - q0 ∧ p0 * p1 ≤ (1 / 200000000) * (1 - q0) := by
  intro q0 p_max; have hp0_pm : p0 ≤ p_max := hp0_hi
  have hp1_pm : p1 ≤ p_max := hp1_hi; have hp0_nn : 0 ≤ p0 := le_trans hp_min.le hp0_lo
  have hp1_nn : 0 ≤ p1 := le_trans hp_min.le hp1_lo; have hpmax_val : p_max = 1 / 200000000 :=
    (by dsimp only [p_max]; norm_num); have hident : (1 - q0) - (p0 + p1) * (1 - 2 * p_max) = p0 *
    (2 * p_max - p1) + 2 * p_max * p1 := (by dsimp only [q0]; ring)
  have hsum_rho : (p0 + p1) * (1 - 2 * p_max) ≤ 1 - q0 := by
    have hnn : 0 ≤ p0 * (2 * p_max - p1) + 2 * p_max * p1 := add_nonneg (mul_nonneg hp0_nn
      (by linarith [hp1_pm, hp1_nn])) (mul_nonneg (by rw [hpmax_val]; positivity) hp1_nn)
    linarith [hident]
  have hrho_pos : 0 < 1 - 2 * p_max := (by rw [hpmax_val]; norm_num); have h2p_rho : 2 * p_min * (1
    - 2 * p_max) ≤ 1 - q0 := (mul_le_mul_of_nonneg_right (by linarith [hp0_lo, hp1_lo])
    hrho_pos.le).trans hsum_rho
  have h1q0_pos : 0 < 1 - q0 := lt_of_lt_of_le (by positivity) h2p_rho
  have hp0_le : p0 ≤ 1 - q0 := by
    have : (1 - q0) - p0 = p1 * (1 - p0) := (by dsimp only [q0]; ring); linarith [mul_nonneg hp1_nn
      (by linarith [hp0_pm, hpmax_val] : 0 ≤ 1 - p0)]
  have hp1_le : p1 ≤ 1 - q0 := by
    have : (1 - q0) - p1 = p0 * (1 - p1) := (by dsimp only [q0]; ring); linarith [mul_nonneg hp0_nn
      (by linarith [hp1_pm, hpmax_val] : 0 ≤ 1 - p1)]
  have hprod_le : p0 * p1 ≤ (1 / 200000000) * (1 - q0) := by
    calc p0 * p1 ≤ (1 / 200000000) * p1 :=
          mul_le_mul_of_nonneg_right (by linarith [hp0_pm, hpmax_val]) hp1_nn
      _ ≤ (1 / 200000000) * (1 - q0) := mul_le_mul_of_nonneg_left hp1_le (by positivity)
  exact ⟨h1q0_pos, h2p_rho, hsum_rho, hp0_le, hp1_le, hprod_le⟩
/- ## 5. Single-Locked Bin-Conditional Step Soundness (`1 ≤ r ≤ min k rcapCap`) -/
end QuantumComputation.Specs.GroverFindAll.PipeFuseM2
end Sec_PipelinedFuseM2MultiStage
end Sec_PipelinedFuseM2MultiStage
section Sec_Warm2M2WarmCertDefs
namespace QuantumComputation.Specs.GroverFindAll.Warm2
open Real
open PipeFuseCert
  (withForcedNat withForcedNat_eq allRange of_allRange
   checkOctantAtan octantAtan_sound checkClickRow checkFuseDriftCert
   harmSumPow2 sqrtMUpNat sq_le_imp_le arctan_le_pade54 pade56_le_arctan
   arctan_le_pi_div_four_sub)
open PipeFuseM2Cert
  (M2BinCert M2LockDrift M2StageScalar
   checkOctantAtanLo octantAtanLo_sound checkPsiHi minDiffNat checkM2KnotSlope)
/- ## 1. Pure-Integer Certificate Checkers (`tn ≤ 200000` & CSWAP Stage-`1` Hit Bounds) -/
/-- Extended octant-folded `[5/4]` / `[5/6]` Padé upper bound check
  `arctan (tn / 10^5) ≤ phiHi / 10^12` for `tn ≤ 200000`. -/
def checkAtan200Hi (tn phiHi : ℕ) : Bool :=
  decide (tn ≤ 200000) &&
  if tn ≤ 100000 then
    checkOctantAtan tn phiHi
  else
    withForcedNat (tn - 100000) fun a ↦
    withForcedNat (100000 + tn) fun b ↦
    withForcedNat (a * a) fun aa ↦
    withForcedNat (b * b) fun bb ↦
    withForcedNat (a * (945 * bb * bb + 735 * aa * bb + 64 * aa * aa)) fun p54 ↦
    withForcedNat (b * (945 * bb * bb + 1050 * aa * bb + 225 * aa * aa)) fun q54 ↦
    decide (785398163398 * q54 + 1000000000000 * p54 ≤ phiHi * q54)
/-- Extended octant-folded `[5/6]` / `[5/4]` Padé lower bound check
  `phiLo / 10^12 ≤ arctan (tn / 10^5)` for `tn ≤ 200000`. -/
def checkAtan200Lo (tn phiLo : ℕ) : Bool :=
  decide (tn ≤ 200000) &&
  if tn ≤ 100000 then
    checkOctantAtanLo tn phiLo
  else
    withForcedNat (tn - 100000) fun a ↦
    withForcedNat (100000 + tn) fun b ↦
    withForcedNat (a * a) fun aa ↦
    withForcedNat (b * b) fun bb ↦
    withForcedNat (a * b * (1155 * bb * bb + 1190 * aa * bb + 231 * aa * aa)) fun pHom ↦
    withForcedNat (1155 * bb * bb * bb + 1575 * aa * bb * bb +
      525 * aa * aa * bb + 25 * aa * aa * aa) fun qHom ↦
    decide (phiLo * qHom ≤ 785398163397 * qHom + 1000000000000 * pHom)
/-- Octant-folded `[5/6]` / `[5/4]` Padé lower bound check at scale `10^8`:
  `atanLo / 10^12 ≤ arctan (t8 / 10^8)` for `t8 ≤ 100000000`. -/
def checkAtanScale8Lo (t8 atanLo : ℕ) : Bool :=
  decide (t8 ≤ 100000000) &&
  if 12 * t8 ≤ 500000000 then
    withForcedNat (t8 * t8) fun tt ↦
    withForcedNat 10000000000000000 fun e16 ↦
    decide (atanLo * (1155 * e16 * e16 * e16 + 1575 * tt * e16 * e16 +
        525 * tt * tt * e16 + 25 * tt * tt * tt) ≤
      t8 * (1155 * e16 * e16 + 1190 * tt * e16 + 231 * tt * tt) * 10000 * e16)
  else
    withForcedNat (100000000 - t8) fun a ↦
    withForcedNat (100000000 + t8) fun b ↦
    withForcedNat (a * a) fun aa ↦
    withForcedNat (b * b) fun bb ↦
    withForcedNat (a * (945 * bb * bb + 735 * aa * bb + 64 * aa * aa)) fun p54 ↦
    withForcedNat (b * (945 * bb * bb + 1050 * aa * bb + 225 * aa * aa)) fun q54 ↦
    decide (atanLo * q54 + 1000000000000 * p54 ≤ 785398163397 * q54)
/-- Elementary `√N`-normalized stage-`1` CSWAP warm-readout cost coefficient. -/
noncomputable def cswapCoeffUpper (γ_lo : ℝ) : ℝ :=
  (1 - Real.sin γ_lo ^ 2 / 2) *
      ((π / 4 - Real.arctan (Real.tan γ_lo / √2)) / (2 * √2) + 1 / (4 * √2)) +
    1 / 1000000000000
/-- Certified scale-`10^12` upper bound on `cswapCoeffUpper 0`. -/
abbrev cswapZeroHitNat : ℕ := 454456896438
/-- Tight `m = 2, r = 2` click-row check (`999999999997 / 10^12` factor, valid at `100 ≤
  n`). -/
def checkClickRowM2R2Tight (tn stepNum : ℕ) : Bool :=
  decide ((1000000000000 * 100000 * 1000000000000) *
      (1000000000000 * 100000 * 1000000000000) ≤
    2 * (4 * 2 * 999999999997 * tn * stepNum) *
      (4 * 2 * 999999999997 * tn * stepNum))
/-- Certified scale-`10^12` upper bound `cswapCoeffUpper γ₀ ≤ hHi / 10^12` at
  `γ₀ = arcsin (√(1 / 2) * sin (arctan (tc / 10^5)))` (`1 ≤ tc ≤ 200000`). -/
def checkCswapHitSingle (tc tSymLo8 symAtanLo hHi : ℕ) : Bool :=
  decide (1 ≤ tc) && decide (tc ≤ 200000) &&
  withForcedNat (tc * tc) fun t2 ↦
  decide ((40000000000 + 2 * t2) * tSymLo8 * tSymLo8 ≤
    t2 * 10000000000000000) &&
  checkAtanScale8Lo tSymLo8 symAtanLo &&
  decide (symAtanLo ≤ 1285398163398) &&
  decide (1 ≤ hHi) &&
  decide ((40000000000 + 3 * t2) * (1285398163398 - symAtanLo) * 1000000000000 ≤
    (hHi - 1) * 8 * (10000000000 + t2) * 1414213562373)
/-- Scale-`10^12` `[5/6]` Padé lower bound `atanLo / 10^12 ≤ 2 * arctan (y12 / 10^12)`
  for `12 * y12 ≤ 5 * 10^12`. -/
def checkAtanHalf12Lo (y12 atanLo : ℕ) : Bool :=
  decide (12 * y12 ≤ 5000000000000) &&
  withForcedNat (y12 * y12) fun yy ↦
  withForcedNat 1000000000000000000000000 fun e24 ↦
  withForcedNat (e24 * e24) fun e48 ↦
  decide (atanLo * (1155 * e48 * e24 + 1575 * yy * e48 +
      525 * yy * yy * e24 + 25 * yy * yy * yy) ≤
    2 * y12 * (1155 * e48 + 1190 * yy * e24 + 231 * yy * yy) * e24)
/-- Half-angle scale-`10^12` upper bound `cswapCoeffUpper γ₀ ≤ hHi / 10^12` at
  `γ₀ = arcsin (√(1 / 2) * sin (arctan (tc / 10^5)))` (`1 ≤ tc ≤ 200000`). -/
def checkCswapHalf12 (tc y12 symAtanLo hHi : ℕ) : Bool :=
  decide (1 ≤ tc) && decide (tc ≤ 200000) &&
  withForcedNat (tc * tc) fun t2 ↦
  withForcedNat (y12 * y12) fun y2 ↦
  withForcedNat 1000000000000000000000000 fun e24 ↦
  decide (y2 + 1 ≤ e24) &&
  decide (4 * y2 * (40000000000 + 2 * t2) * e24 ≤
    t2 * (e24 - y2) * (e24 - y2)) &&
  checkAtanHalf12Lo y12 symAtanLo &&
  decide (symAtanLo ≤ 1285398163398) &&
  decide (1 ≤ hHi) &&
  decide ((40000000000 + 3 * t2) * (1285398163398 - symAtanLo) * 1000000000000 ≤
    (hHi - 1) * 8 * (10000000000 + t2) * 1414213562373)
/-- Stage-`2` locked CSWAP hit bound dispatching scale-`10^8` (`tSym ≤ 10^8`) or
  half-angle scale-`10^12` (`10^8 < tSym`). -/
def checkCswapHitLock (tc tSym symAtanLo hHi : ℕ) : Bool :=
  if tSym ≤ 100000000 then
    checkCswapHitSingle tc tSym symAtanLo hHi
  else
    checkCswapHalf12 tc tSym symAtanLo hHi
/-- Stage-`2` (`r = 2 → r = 1` CSWAP warm readout) single-locked drift check on bin `j < B`,
  storing `(tSymLo8, symAtanLo, hHi)` in `(tBfLo, tdHi, hHi)` of `M2BinCert`. -/
def checkWarm2Stage2Bin (B tn phiLo dNat : ℕ) (w : ℕ → ℕ) (bc : M2BinCert) (j : ℕ) : Bool :=
  match bc with
  | ⟨tcLo, bLoHi, dropHi, tSymLo8, symAtanLo, _, _, _, hHi⟩ =>
    (if tcLo == 0 then
      decide (cswapZeroHitNat ≤ hHi)
    else
      decide (1 ≤ tcLo) && decide (tcLo ≤ 200000) &&
      checkAtan200Hi tcLo bLoHi &&
      withForcedNat ((j + 1) * dNat * 1000000000001) fun dropRoot ↦
      decide (4 * 2 * dropRoot * dropRoot ≤
        (dropHi * 1000000000000) * (dropHi * 1000000000000)) &&
      decide (bLoHi + dropHi ≤ phiLo) &&
      checkCswapHitSingle tcLo tSymLo8 symAtanLo hHi) &&
    withForcedNat (w j) fun wj ↦
    decide (hHi ≤ wj) &&
    withForcedNat (minDiffNat B w j) fun minDiff ↦
    withForcedNat ((dNat - minDiff) * 100000 * 100000000 * 1000000000000) fun lhsR ↦
    withForcedNat (dNat * 4 * tn * 99999999 * (wj - hHi)) fun rhsR ↦
    decide (lhsR * lhsR ≤ 2 * rhsR * rhsR)
/-- Stage-`r` (`r ≥ 3`) single-locked drift check on bin `j < B` (`tn, tp, tcLo ≤ 200000`). -/
def checkWarm2StageGe3Bin (B r tn phiLo dNat tp phiHiP dNatP cNat : ℕ)
    (w wP : ℕ → ℕ) (bc : M2BinCert) (j : ℕ) : Bool :=
  match bc with
  | ⟨tcLo, bLoHi, dropHi, tBfLo, tdHi, numU, uNat, psiHi, hHi⟩ =>
    (if tcLo == 0 then
      uNat == cNat
    else
      decide (1 ≤ tcLo) && decide (tcLo ≤ 200000) &&
      checkAtan200Hi tcLo bLoHi &&
      withForcedNat ((j + 1) * dNat * 1000000000001) fun dropRoot ↦
      decide (4 * r * dropRoot * dropRoot ≤
        (dropHi * 1000000000000) * (dropHi * 1000000000000)) &&
      decide (bLoHi + dropHi ≤ phiLo) &&
      checkFuseDriftCert r tcLo tp phiHiP tBfLo tdHi numU cNat uNat) &&
    checkPsiHi B dNatP wP (cNat - uNat) psiHi &&
    decide (uNat + psiHi ≤ hHi) &&
    withForcedNat (w j) fun wj ↦
    decide (hHi ≤ wj) &&
    withForcedNat (minDiffNat B w j) fun minDiff ↦
    withForcedNat ((dNat - minDiff) * 100000 * 100000000 * 1000000000000) fun lhsR ↦
    withForcedNat (dNat * 4 * tn * 99999999 * (wj - hHi)) fun rhsR ↦
    decide (lhsR * lhsR ≤ r * rhsR * rhsR)
/-- Full integer certificate check for stage `r = idx + 2 ≥ 2` (`idx < k - 1`). -/
def checkWarm2StageIdx (B : ℕ) (stFn : ℕ → M2StageScalar) (wFn : ℕ → ℕ → ℕ)
    (binFn : ℕ → ℕ → M2BinCert) (idx : ℕ) : Bool :=
  let r := idx + 2
  let w := wFn r
  match stFn r with
  | ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, cNat,
      ⟨tBfLo, tdHi, numU, uLock, psiLock, hLock, hBoth⟩⟩ =>
    decide (500 ≤ tn) && decide (tn ≤ 200000) &&
    checkAtan200Hi tn phiHi &&
    checkAtan200Lo tn phiLo &&
    decide (1 ≤ cSelf) &&
    decide (phiHi * phiHi ≤ 4 * r * (cSelf - 1) * (cSelf - 1)) &&
    decide (1000 ≤ dNat) && decide (cSelf ≤ B * dNat) &&
    (if idx == 0 then checkClickRowM2R2Tight tn stepNum else checkClickRow 2 r tn stepNum) &&
    allRange (checkM2KnotSlope dNat w) B &&
    if idx == 0 then
      checkCswapHitLock tn tBfLo tdHi hLock &&
      decide (cswapZeroHitNat ≤ hBoth) &&
      withForcedNat (if hLock ≤ hBoth then hBoth - hLock else 0) fun extra ↦
      withForcedNat (w 0) fun w0 ↦
      decide (stepNum ≤ w0) &&
      decide (4000000000000 * hLock + extra ≤ 4000000000000 * (w0 - stepNum)) &&
      allRange (fun j ↦ checkWarm2Stage2Bin B tn phiLo dNat w (binFn 2 j) j) B
    else
      let rPrev := idx + 1
      let wP := wFn rPrev
      match stFn rPrev with
      | ⟨tp, phiHiP, _, _, dNatP, _, _, _⟩ =>
        checkFuseDriftCert r tn tp phiHiP tBfLo tdHi numU cNat uLock &&
        checkPsiHi B dNatP wP (cNat - uLock) psiLock &&
        decide (uLock + psiLock ≤ hLock) &&
        decide (cNat + wP 0 ≤ hBoth) &&
        withForcedNat (if hLock ≤ hBoth then hBoth - hLock else 0) fun extra ↦
        withForcedNat (w 0) fun w0 ↦
        decide (stepNum ≤ w0) &&
        decide (200000000 * hLock + extra ≤ 200000000 * (w0 - stepNum)) &&
        allRange (fun j ↦
          checkWarm2StageGe3Bin B r tn phiLo dNat tp phiHiP dNatP cNat w wP (binFn r j) j) B
/-- Full cell certificate check for `(m = 2, k = 2 ^ kIdx)` (`1 ≤ kIdx < 11`) with
  piecewise-linear
  potentials at all stages `r = 2..k` and terminal CSWAP warm `r = 1` readout. -/
def checkWarm2CellCert (B : ℕ) (stFn : ℕ → M2StageScalar) (wFn : ℕ → ℕ → ℕ)
    (binFn : ℕ → ℕ → M2BinCert) (kIdx topR rcNum : ℕ) : Bool :=
  let k := 2 ^ kIdx
  decide (1 ≤ B) &&
  decide (1 ≤ kIdx) && decide (kIdx < 11) &&
  allRange (checkWarm2StageIdx B stFn wFn binFn) (k - 1) &&
  decide (1 ≤ topR) &&
  match stFn k with
  | ⟨_, phiHiK, _, _, _, _, _, _⟩ =>
    decide (phiHiK * phiHiK ≤ 4 * k * (topR - 1) * (topR - 1)) &&
    decide ((wFn k 0 + topR) * 10000000000 * sqrtMUpNat 1 ≤
      rcNum * 785398163397 * harmSumPow2 kIdx)
/- ## 2. Real-Analytic Soundness of Extended Padé & CSWAP Hit Bounds -/
/-- Exact octant identity `arctan x = π / 4 + arctan ((x - 1) / (1 + x))` for `1 ≤ x`. -/
theorem arctan_eq_pi_div_four_add {x : ℝ} (hx1 : 1 ≤ x) : Real.arctan x = π / 4 + Real.arctan ((x -
  1) / (1 + x)) := by
  let F : ℝ → ℝ := fun z ↦ Real.arctan z - Real.arctan ((z - 1) / (1 + z))
  have hd : ∀ z ∈ Set.Ici (0 : ℝ), HasDerivAt F 0 z := fun z hz ↦ by
    have hz0 : 0 ≤ z := hz; have h1z : 0 < 1 + z := (by linarith); have hnum : HasDerivAt (fun w : ℝ
      ↦ w - 1) 1 z := (hasDerivAt_id' z).sub_const 1
    have hden : HasDerivAt (fun w : ℝ ↦ 1 + w) 1 z := (hasDerivAt_id' z).const_add 1; have hq :=
      hnum.div hden h1z.ne'; have hcomp := (Real.hasDerivAt_arctan ((z - 1) / (1 + z))).comp z hq
    refine ((Real.hasDerivAt_arctan z).sub hcomp).congr_deriv ?_; have hden2 : 0 < 1 + ((z - 1) / (1
      + z)) ^ 2 := (by positivity); have h1z2 : 0 < 1 + z ^ 2 := (by positivity)
    field_simp [h1z.ne', hden2.ne', h1z2.ne']; ring
  have hcont : ContinuousOn F (Set.Ici 0) := fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Ici (0 : ℝ))) := fun z hz ↦ by
    rw [interior_Ici] at hz; exact (hd z hz.le).differentiableAt.differentiableWithinAt
  have hge := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff (fun z hz ↦ by
    rw [interior_Ici] at hz
    rw [(hd z hz.le).deriv]) (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : (0 : ℝ) ≤ x) hx1
  have hcontN : ContinuousOn (-F) (Set.Ici 0) := hcont.neg
  have hdiffN : DifferentiableOn ℝ (-F) (interior (Set.Ici (0 : ℝ))) := hdiff.neg
  have hle := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcontN hdiffN (fun z hz ↦ by
    rw [interior_Ici] at hz; rw [((hd z hz.le).neg).deriv]
    norm_num) (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ x) hx1
  have hF1 : F 1 = π / 4 := by dsimp only [F]; norm_num [Real.arctan_one]
  change (-F) 1 ≤ (-F) x at hle; simp only [Pi.neg_apply] at hle
  rw [hF1] at hge hle; dsimp only [F] at hge hle; linarith
theorem atan200Hi_sound {tn phiHi : ℕ} (h : checkAtan200Hi tn phiHi = true) : Real.arctan ((tn : ℝ)
  / 100000) ≤ (phiHi : ℝ) / 1000000000000 := by
  simp only [checkAtan200Hi, Bool.and_eq_true] at h; have hbody := h.2
  split_ifs at hbody with h100
  · exact octantAtan_sound hbody
  · simp only [withForcedNat_eq] at hbody; have hnat := of_decide_eq_true hbody
    have htn_ge : 100000 ≤ tn := (by omega); have ha_sub : ((tn - 100000 : ℕ) : ℝ) = (tn : ℝ) -
      100000 := (by rw [Nat.cast_sub htn_ge]; push_cast; rfl)
    generalize tn - 100000 = a at hnat ha_sub; set b : ℕ := 100000 + tn; set x : ℝ := (tn : ℝ) /
      100000; set y : ℝ := (a : ℝ) / b; have hx1 : 1 ≤ x :=
      (by dsimp only [x]; have : (100000 : ℝ) ≤ tn := (by exact_mod_cast htn_ge); linarith)
    have hb_pos : (0 : ℝ) < b := (by exact_mod_cast (show 0 < b by omega)); have hb_add : (b : ℝ) =
      100000 + tn := (by dsimp only [b]; push_cast; rfl)
    have hy_eq : (x - 1) / (1 + x) = y := by
      dsimp only [x, y]; rw [ha_sub, hb_add]
      field_simp [(by positivity : (1 : ℝ) + (tn : ℝ) / 100000 ≠ 0),
        (by positivity : (100000 : ℝ) + tn ≠ 0)]
    have hy0 : 0 ≤ y := (by positivity); have hp54 := arctan_le_pade54 hy0; have hoct :=
      arctan_eq_pi_div_four_add hx1; rw [hy_eq] at hoct; have hpi : π / 4 ≤ (785398163398 : ℝ) /
      1000000000000 := (by linarith [Real.pi_lt_d20]); set p54R : ℝ := (a : ℝ) * (945 * (b : ℝ) ^ 4
      + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4); set q54R : ℝ := (b : ℝ) * (945 * (b :
      ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 225 * (a : ℝ) ^ 4); have hq_pos : 0 < q54R :=
      (by dsimp only [q54R]; positivity)
    have hrat_eq : y * (945 + 735 * y ^ 2 + 64 * y ^ 4) / (945 + 1050 * y ^ 2 + 225 * y ^ 4) = p54R
      / q54R := by
      dsimp only [y, p54R, q54R]; have hden_y : 0 < 945 + 1050 * ((a : ℝ) / b) ^ 2 + 225 * ((a : ℝ)
        / b) ^ 4 := (by positivity); field_simp [hb_pos.ne', hden_y.ne', hq_pos.ne']
    have hcast : 785398163398 * q54R + 1000000000000 * p54R ≤ (phiHi : ℝ) * q54R := by
      have hraw : (785398163398 : ℝ) * ((b : ℝ) * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b *
        b) + 225 * (a * a) * (a * a))) + 1000000000000 * ((a : ℝ) * (945 * (b * b) * (b * b) + 735 *
        (a * a) * (b * b) + 64 * (a * a) * (a * a))) ≤ (phiHi : ℝ) * ((b : ℝ) * (945 * (b * b) * (b
        * b) + 1050 * (a * a) * (b * b) + 225 * (a * a) * (a * a))) := (by exact_mod_cast hnat)
      dsimp only [p54R, q54R]
      linarith [hraw, show (b : ℝ) * (945 * (b : ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 +
            225 * (a : ℝ) ^ 4) =
          (b : ℝ) * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b * b) +
            225 * (a * a) * (a * a)) by ring,
        show (a : ℝ) * (945 * (b : ℝ) ^ 4 + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4) =
          (a : ℝ) * (945 * (b * b) * (b * b) + 735 * (a * a) * (b * b) +
            64 * (a * a) * (a * a)) by ring]
    have hdiv : (785398163398 : ℝ) / 1000000000000 + p54R / q54R ≤ (phiHi : ℝ) / 1000000000000 := by
      have h1 : (785398163398 : ℝ) / 1000000000000 + p54R / q54R = (785398163398 * q54R +
        1000000000000 * p54R) / (1000000000000 * q54R) := (by field_simp [hq_pos.ne'])
      have h2 : (phiHi : ℝ) / 1000000000000 = ((phiHi : ℝ) * q54R) / (1000000000000 * q54R) :=
        (by field_simp [hq_pos.ne']); rw [h1, h2]
      exact div_le_div_of_nonneg_right hcast (by positivity)
    rw [hrat_eq] at hp54; linarith [hoct, hpi, hp54, hdiv]
theorem atan200Lo_sound {tn phiLo : ℕ} (h : checkAtan200Lo tn phiLo = true) : (phiLo : ℝ) /
  1000000000000 ≤ Real.arctan ((tn : ℝ) / 100000) := by
  simp only [checkAtan200Lo, Bool.and_eq_true] at h; have hbody := h.2
  split_ifs at hbody with h100
  · exact octantAtanLo_sound hbody
  · simp only [withForcedNat_eq] at hbody; have hnat := of_decide_eq_true hbody
    have htn_ge : 100000 ≤ tn := (by omega); have ha_sub : ((tn - 100000 : ℕ) : ℝ) = (tn : ℝ) -
      100000 := (by rw [Nat.cast_sub htn_ge]; push_cast; rfl)
    generalize tn - 100000 = a at hnat ha_sub; set b : ℕ := 100000 + tn; set x : ℝ := (tn : ℝ) /
      100000; set y : ℝ := (a : ℝ) / b; have hx1 : 1 ≤ x :=
      (by dsimp only [x]; have : (100000 : ℝ) ≤ tn := (by exact_mod_cast htn_ge); linarith)
    have hb_pos : (0 : ℝ) < b := (by exact_mod_cast (show 0 < b by omega)); have hb_add : (b : ℝ) =
      100000 + tn := (by dsimp only [b]; push_cast; rfl)
    have hy_eq : (x - 1) / (1 + x) = y := by
      dsimp only [x, y]; rw [ha_sub, hb_add]
      field_simp [(by positivity : (1 : ℝ) + (tn : ℝ) / 100000 ≠ 0),
        (by positivity : (100000 : ℝ) + tn ≠ 0)]
    have hy0 : 0 ≤ y := (by positivity); have hp56 := pade56_le_arctan hy0; have hoct :=
      arctan_eq_pi_div_four_add hx1; rw [hy_eq] at hoct; have hpi : (785398163397 : ℝ) /
      1000000000000 ≤ π / 4 := (by linarith [Real.pi_gt_d20]); set pHomR : ℝ := (a : ℝ) * b * (1155
      * (b : ℝ) ^ 4 + 1190 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 231 * (a : ℝ) ^ 4); set qHomR : ℝ := 1155 *
      (b : ℝ) ^ 6 + 1575 * (a : ℝ) ^ 2 * (b : ℝ) ^ 4 + 525 * (a : ℝ) ^ 4 * (b : ℝ) ^ 2 + 25 * (a :
      ℝ) ^ 6; have hq_pos : 0 < qHomR := (by dsimp only [qHomR]; positivity)
    have hrat_eq : y * (1155 + 1190 * y ^ 2 + 231 * y ^ 4) / (1155 + 1575 * y ^ 2 + 525 * y ^ 4 + 25
      * y ^ 6) = pHomR / qHomR := by
      dsimp only [y, pHomR, qHomR]; have hden_y : 0 < 1155 + 1575 * ((a : ℝ) / b) ^ 2 + 525 * ((a :
        ℝ) / b) ^ 4 + 25 * ((a : ℝ) / b) ^ 6 := (by positivity); field_simp [hb_pos.ne', hden_y.ne',
        hq_pos.ne']
    have hcast : (phiLo : ℝ) * qHomR ≤ 785398163397 * qHomR + 1000000000000 * pHomR := by
      have hraw : (phiLo : ℝ) * (1155 * (b * b : ℝ) * (b * b) * (b * b) + 1575 * (a * a) * (b * b) *
        (b * b) + 525 * (a * a) * (a * a) * (b * b) + 25 * (a * a) * (a * a) * (a * a)) ≤
        (785398163397 : ℝ) * (1155 * (b * b : ℝ) * (b * b) * (b * b) + 1575 * (a * a) * (b * b) * (b
        * b) + 525 * (a * a) * (a * a) * (b * b) + 25 * (a * a) * (a * a) * (a * a)) + 1000000000000
        * ((a : ℝ) * b * (1155 * (b * b) * (b * b) + 1190 * (a * a) * (b * b) + 231 * (a * a) * (a *
        a))) := (by exact_mod_cast hnat); dsimp only [pHomR, qHomR]
      linarith [hraw, show 1155 * (b : ℝ) ^ 6 + 1575 * (a : ℝ) ^ 2 * (b : ℝ) ^ 4 +
            525 * (a : ℝ) ^ 4 * (b : ℝ) ^ 2 + 25 * (a : ℝ) ^ 6 =
          1155 * (b * b : ℝ) * (b * b) * (b * b) + 1575 * (a * a) * (b * b) * (b * b) +
            525 * (a * a) * (a * a) * (b * b) + 25 * (a * a) * (a * a) * (a * a) by ring,
        show (a : ℝ) * b * (1155 * (b : ℝ) ^ 4 + 1190 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 +
            231 * (a : ℝ) ^ 4) =
          (a : ℝ) * b * (1155 * (b * b) * (b * b) + 1190 * (a * a) * (b * b) +
            231 * (a * a) * (a * a)) by ring]
    have hdiv : (phiLo : ℝ) / 1000000000000 ≤ (785398163397 : ℝ) / 1000000000000 + pHomR / qHomR
      := by
      have h1 : (phiLo : ℝ) / 1000000000000 = ((phiLo : ℝ) * qHomR) / (1000000000000 * qHomR) :=
        (by field_simp [hq_pos.ne']); have h2 : (785398163397 : ℝ) / 1000000000000 + pHomR / qHomR =
        (785398163397 * qHomR + 1000000000000 * pHomR) / (1000000000000 * qHomR) :=
        (by field_simp [hq_pos.ne']); rw [h1, h2]
      exact div_le_div_of_nonneg_right hcast (by positivity)
    rw [hrat_eq] at hp56; linarith [hoct, hpi, hp56, hdiv]
theorem atanScale8Lo_sound {t8 atanLo : ℕ} (h : checkAtanScale8Lo t8 atanLo = true) : (atanLo : ℝ) /
  1000000000000 ≤ Real.arctan ((t8 : ℝ) / 100000000) := by
  simp only [checkAtanScale8Lo, Bool.and_eq_true] at h; have ht8_le := of_decide_eq_true h.1
  have hbody := h.2; set x : ℝ := (t8 : ℝ) / 100000000; have hx0 : 0 ≤ x := (by positivity)
  split_ifs at hbody with h12
  · simp only [withForcedNat_eq] at hbody; have hnat := of_decide_eq_true hbody
    refine le_trans ?_ (pade56_le_arctan hx0)
    have hden_pos : 0 < 1155 + 1575 * x ^ 2 + 525 * x ^ 4 + 25 * x ^ 6 := by positivity
    rw [div_le_div_iff₀ (by norm_num) hden_pos]; set e16 : ℝ := 10000000000000000
    have hcast : (atanLo : ℝ) * (1155 * e16 * e16 * e16 + 1575 * (t8 * t8 : ℝ) * e16 * e16 + 525 *
      (t8 * t8 : ℝ) * (t8 * t8) * e16 + 25 * (t8 * t8 : ℝ) * (t8 * t8) * (t8 * t8)) ≤ (t8 : ℝ) *
      (1155 * e16 * e16 + 1190 * (t8 * t8 : ℝ) * e16 + 231 * (t8 * t8 : ℝ) * (t8 * t8)) * 10000 *
      e16 := (by dsimp only [e16]; exact_mod_cast hnat); dsimp only [x, e16] at hcast ⊢
    linear_combination hcast / (10000000000000000 * 10000000000000000 * 10000000000000000)
  · simp only [withForcedNat_eq] at hbody; have hnat := of_decide_eq_true hbody; set a : ℕ :=
      100000000 - t8; set b : ℕ := 100000000 + t8; set y : ℝ := (a : ℝ) / b; have hx1 : x ≤ 1 :=
      (by dsimp only [x]; have : (t8 : ℝ) ≤ 100000000 := (by exact_mod_cast ht8_le); linarith)
    have hb_pos : (0 : ℝ) < b := (by exact_mod_cast (show 0 < b by omega)); have ha_sub : (a : ℝ) =
      100000000 - t8 := (by dsimp only [a]; rw [Nat.cast_sub ht8_le]; push_cast; rfl)
    have hb_add : (b : ℝ) = 100000000 + t8 := by dsimp only [b]; push_cast; rfl
    have hy_eq : (1 - x) / (1 + x) = y := by
      dsimp only [x, y]; rw [ha_sub, hb_add]
      field_simp [(by positivity : (1 : ℝ) + (t8 : ℝ) / 100000000 ≠ 0),
        (by positivity : (100000000 : ℝ) + t8 ≠ 0)]
    have hy0 : 0 ≤ y := (by positivity); have hp54 := arctan_le_pade54 hy0; have hoct :=
      PipeFuseM2Cert.pi_div_four_sub_le_arctan hx0 hx1; rw [hy_eq] at hoct; have hpi : (785398163397
      : ℝ) / 1000000000000 ≤ π / 4 := (by linarith [Real.pi_gt_d20]); set p54R : ℝ := (a : ℝ) * (945
      * (b : ℝ) ^ 4 + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4); set q54R : ℝ := (b : ℝ) *
      (945 * (b : ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 225 * (a : ℝ) ^ 4); have hq_pos : 0 <
      q54R := (by dsimp only [q54R]; positivity)
    have hrat_eq : y * (945 + 735 * y ^ 2 + 64 * y ^ 4) / (945 + 1050 * y ^ 2 + 225 * y ^ 4) = p54R
      / q54R := by
      dsimp only [y, p54R, q54R]; have hden_y : 0 < 945 + 1050 * ((a : ℝ) / b) ^ 2 + 225 * ((a : ℝ)
        / b) ^ 4 := (by positivity); field_simp [hb_pos.ne', hden_y.ne', hq_pos.ne']
    have hcast : (atanLo : ℝ) * q54R + 1000000000000 * p54R ≤ 785398163397 * q54R := by
      have hraw : (atanLo : ℝ) * ((b : ℝ) * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b * b) +
        225 * (a * a) * (a * a))) + 1000000000000 * ((a : ℝ) * (945 * (b * b) * (b * b) + 735 * (a *
        a) * (b * b) + 64 * (a * a) * (a * a))) ≤ 785398163397 * ((b : ℝ) * (945 * (b * b) * (b * b)
        + 1050 * (a * a) * (b * b) + 225 * (a * a) * (a * a))) := (by exact_mod_cast hnat)
      dsimp only [p54R, q54R]
      linarith [hraw, show (b : ℝ) * (945 * (b : ℝ) ^ 4 + 1050 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 +
            225 * (a : ℝ) ^ 4) =
          (b : ℝ) * (945 * (b * b) * (b * b) + 1050 * (a * a) * (b * b) +
            225 * (a * a) * (a * a)) by ring,
        show (a : ℝ) * (945 * (b : ℝ) ^ 4 + 735 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 + 64 * (a : ℝ) ^ 4) =
          (a : ℝ) * (945 * (b * b) * (b * b) + 735 * (a * a) * (b * b) +
            64 * (a * a) * (a * a)) by ring]
    have hdiv : (atanLo : ℝ) / 1000000000000 ≤ (785398163397 : ℝ) / 1000000000000 - p54R / q54R
      := by
      have h1 : (atanLo : ℝ) / 1000000000000 = ((atanLo : ℝ) * q54R) / (1000000000000 * q54R) :=
        (by field_simp [hq_pos.ne']); have h2 : (785398163397 : ℝ) / 1000000000000 - p54R / q54R =
        (785398163397 * q54R - 1000000000000 * p54R) / (1000000000000 * q54R) :=
        (by field_simp [hq_pos.ne']); rw [h1, h2]
      exact div_le_div_of_nonneg_right (by linarith [hcast]) (by positivity)
    rw [hrat_eq] at hp54; linarith [hoct, hpi, hp54, hdiv]
theorem sqrt_two_ge_d12 : (1414213562373 : ℝ) / 1000000000000 ≤ √2 := by
  refine sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _) ?_; rw [Real.sq_sqrt (by norm_num)]
  norm_num
theorem cswapZeroHit_sound : cswapCoeffUpper 0 ≤ (cswapZeroHitNat : ℝ) / 1000000000000 := by
  dsimp only [cswapCoeffUpper, cswapZeroHitNat]; rw [Real.sin_zero, Real.tan_zero, zero_div,
    Real.arctan_zero, sub_zero, zero_pow (by omega), zero_div, sub_zero, one_mul]
  have hnum : (π / 4) / (2 * √2) + 1 / (4 * √2) = (π / 4 + 1 / 2) / (2 * √2) :=
    (by have hs2 : √2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'; field_simp [hs2]; ring)
  rw [hnum]; have hpi : π / 4 + 1 / 2 ≤ (1285398163398 : ℝ) / 1000000000000 :=
    (by linarith [Real.pi_lt_d20]); have hs2 := sqrt_two_ge_d12; have hd1 : (π / 4 + 1 / 2) / (2 *
    √2) ≤ ((1285398163398 : ℝ) / 1000000000000) / (2 * ((1414213562373 : ℝ) / 1000000000000)) :=
    (div_le_div_of_nonneg_right hpi (by positivity)).trans (div_le_div_of_nonneg_left (by norm_num)
    (by norm_num) (by linarith [hs2])); linarith [hd1, show ((1285398163398 : ℝ) / 1000000000000) /
    (2 * ((1414213562373 : ℝ) / 1000000000000)) + 1 / 1000000000000 ≤ (454456896438 : ℝ) /
    1000000000000 by norm_num]
theorem atanHalf12Lo_sound {y12 atanLo : ℕ} (h : checkAtanHalf12Lo y12 atanLo = true) : (atanLo : ℝ)
  / 1000000000000 ≤ 2 * Real.arctan ((y12 : ℝ) / 1000000000000) := by
  simp only [checkAtanHalf12Lo, withForcedNat_eq, Bool.and_eq_true] at h; have hnat :=
    of_decide_eq_true h.2; set y : ℝ := (y12 : ℝ) / 1000000000000; have hy0 : 0 ≤ y :=
    (by positivity); refine le_trans ?_ (mul_le_mul_of_nonneg_left (pade56_le_arctan hy0)
    (by norm_num)); have hmul : 2 * (y * (1155 + 1190 * y ^ 2 + 231 * y ^ 4) / (1155 + 1575 * y ^ 2
    + 525 * y ^ 4 + 25 * y ^ 6)) = (2 * y * (1155 + 1190 * y ^ 2 + 231 * y ^ 4)) / (1155 + 1575 * y
    ^ 2 + 525 * y ^ 4 + 25 * y ^ 6) := (by ring); rw [hmul]
  have hden_pos : 0 < 1155 + 1575 * y ^ 2 + 525 * y ^ 4 + 25 * y ^ 6 := by positivity
  rw [div_le_div_iff₀ (by norm_num) hden_pos]
  set e24 : ℝ := 1000000000000000000000000; set e48 : ℝ := e24 * e24
  have hcast : (atanLo : ℝ) * (1155 * e48 * e24 + 1575 * (y12 * y12 : ℝ) * e48 + 525 * (y12 * y12 :
    ℝ) * (y12 * y12) * e24 + 25 * (y12 * y12 : ℝ) * (y12 * y12) * (y12 * y12)) ≤ 2 * (y12 : ℝ) *
    (1155 * e48 + 1190 * (y12 * y12 : ℝ) * e24 + 231 * (y12 * y12 : ℝ) * (y12 * y12)) * e24 :=
    (by dsimp only [e48, e24]; exact_mod_cast hnat); dsimp only [y, e48, e24] at hcast ⊢
  linear_combination hcast /
    (1000000000000000000000000 * 1000000000000000000000000 * 1000000000000000000000000)
theorem cswapHit_sound_of_tan_sq {tc symAtanLo hHi : ℕ} {z : ℝ} (htc_hi : tc ≤ 200000) (hsym_cap :
  symAtanLo ≤ 1285398163398) (hh4000 : 1 ≤ hHi) (hfin : (40000000000 + 3 * (tc * tc)) *
  (1285398163398 - symAtanLo) * 1000000000000 ≤ (hHi - 1) * 8 * (10000000000 + tc * tc) *
  1414213562373) (hz_nn : 0 ≤ z) (hz_sq : z ^ 2 ≤ (tc : ℝ) ^ 2 / (40000000000 + 2 * (tc : ℝ) ^ 2))
  (hatan_z : (symAtanLo : ℝ) / 1000000000000 ≤ Real.arctan z) :
    let γ₀ := Real.arcsin (√((1 : ℝ) / 2) * Real.sin (Real.arctan ((tc : ℝ) / 100000)))
    0 ≤ γ₀ ∧ cswapCoeffUpper γ₀ ≤ (hHi : ℝ) / 1000000000000 := by
  intro γ₀; have hhSub_r : ((hHi - 1 : ℕ) : ℝ) = (hHi : ℝ) - 1 :=
    (by rw [Nat.cast_sub hh4000]; push_cast; rfl); have hsymDiff_r : ((1285398163398 - symAtanLo :
    ℕ) : ℝ) = 1285398163398 - symAtanLo := (by rw [Nat.cast_sub hsym_cap]; push_cast; rfl)
  generalize hHi - 1 = hSub at hfin hhSub_r
  generalize 1285398163398 - symAtanLo = symDiff at hfin hsymDiff_r; set t : ℝ := (tc : ℝ) / 100000;
    set s : ℝ := √((1 : ℝ) / 2) * Real.sin (Real.arctan t); have hsin_atan : Real.sin (Real.arctan
    t) = t / √(1 + t ^ 2) := Real.sin_arctan t; have hs_nn : 0 ≤ s :=
    (by dsimp only [s, t]; rw [hsin_atan]; positivity)
  have hs_sq : s ^ 2 = (tc : ℝ) ^ 2 / (2 * (10000000000 + (tc : ℝ) ^ 2)) := by
    dsimp only [s, t]; rw [hsin_atan, mul_pow, Real.sq_sqrt (by norm_num), div_pow, Real.sq_sqrt
      (by positivity)]; have hden1 : (0 : ℝ) < 1 + ((tc : ℝ) / 100000) ^ 2 := (by positivity)
    have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity); field_simp [hden1.ne',
      hden2.ne']; ring
  have h1_sub_s2 : 1 - s ^ 2 = (20000000000 + (tc : ℝ) ^ 2) / (2 * (10000000000 + (tc : ℝ) ^ 2))
    := by
    rw [hs_sq]; have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity)
    field_simp [hden2.ne']; ring
  have h1s2_pos : 0 < 1 - s ^ 2 := (by rw [h1_sub_s2]; positivity); have hs_lt1 : s < 1 :=
    (by nlinarith only [h1s2_pos, sq_nonneg s, hs_nn])
  have hγ_nn : 0 ≤ γ₀ := Real.arcsin_nonneg.2 hs_nn; refine ⟨hγ_nn, ?_⟩; have hsin_γ : Real.sin γ₀ =
    s := Real.sin_arcsin (by linarith only [hs_nn]) hs_lt1.le; have hcos_γ : Real.cos γ₀ = √(1 - s ^
    2) := Real.cos_arcsin s; have hcos_pos : 0 < Real.cos γ₀ :=
    (by rw [hcos_γ]; exact Real.sqrt_pos.2 h1s2_pos); have hcos_sq : Real.cos γ₀ ^ 2 = 1 - s ^ 2 :=
    (by rw [hcos_γ, Real.sq_sqrt h1s2_pos.le])
  have htan_nn : 0 ≤ Real.tan γ₀ / √2 := by
    rw [Real.tan_eq_sin_div_cos, hsin_γ]
    exact div_nonneg (div_nonneg hs_nn hcos_pos.le) (Real.sqrt_nonneg _)
  have htan_div_sq : (Real.tan γ₀ / √2) ^ 2 = (tc : ℝ) ^ 2 / (40000000000 + 2 * (tc : ℝ) ^ 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num), Real.tan_eq_sin_div_cos, div_pow, hsin_γ, hcos_sq,
      h1_sub_s2, hs_sq]; have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity)
    have hden3 : (0 : ℝ) < 40000000000 + 2 * (tc : ℝ) ^ 2 := (by positivity); field_simp [hden2.ne',
      hden3.ne']; ring
  have hz_le : z ≤ Real.tan γ₀ / √2 := sq_le_imp_le hz_nn htan_nn (by rwa [htan_div_sq])
  have hatan_ge : (symAtanLo : ℝ) / 1000000000000 ≤ Real.arctan (Real.tan γ₀ / √2) := hatan_z.trans
    (Real.arctan_mono hz_le)
  have htan_div_le1 : Real.tan γ₀ / √2 ≤ 1 := by
    refine sq_le_imp_le htan_nn zero_le_one ?_; rw [htan_div_sq, one_pow, div_le_one
      (by positivity)]; have htc_r : (tc : ℝ) ≤ 200000 := (by exact_mod_cast htc_hi)
    have htc_nn : (0 : ℝ) ≤ tc := Nat.cast_nonneg tc; nlinarith only [htc_r, htc_nn]
  have harc_le_pi4 : Real.arctan (Real.tan γ₀ / √2) ≤ π / 4 :=
    (by simpa [Real.arctan_one] using Real.arctan_mono htan_div_le1)
  have hcomb_eq : (π / 4 - Real.arctan (Real.tan γ₀ / √2)) / (2 * √2) + 1 / (4 * √2) = (π / 4 + 1 /
    2 - Real.arctan (Real.tan γ₀ / √2)) / (2 * √2) :=
    (by have hs2 : √2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'; field_simp [hs2]; ring)
  have hcomb_nn : 0 ≤ (π / 4 + 1 / 2 - Real.arctan (Real.tan γ₀ / √2)) / (2 * √2) := div_nonneg
    (by linarith only [harc_le_pi4]) (by positivity)
  have hpi : π / 4 + 1 / 2 ≤ (1285398163398 : ℝ) / 1000000000000 :=
    (by linarith only [Real.pi_lt_d20]); have hnum_le : π / 4 + 1 / 2 - Real.arctan (Real.tan γ₀ /
    √2) ≤ (symDiff : ℝ) / 1000000000000 := (by rw [hsymDiff_r]; linarith only [hpi, hatan_ge])
  have hcomb_le : (π / 4 + 1 / 2 - Real.arctan (Real.tan γ₀ / √2)) / (2 * √2) ≤ (symDiff : ℝ) / (2 *
    1414213562373) := by
    have hs2 := sqrt_two_ge_d12
    calc (π / 4 + 1 / 2 - Real.arctan (Real.tan γ₀ / √2)) / (2 * √2)
        ≤ ((symDiff : ℝ) / 1000000000000) / (2 * √2) :=
          div_le_div_of_nonneg_right hnum_le (by positivity)
      _ ≤ ((symDiff : ℝ) / 1000000000000) / (2 * ((1414213562373 : ℝ) / 1000000000000)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hs2])
      _ = (symDiff : ℝ) / (2 * 1414213562373) := by ring
  have hw_eq : 1 - Real.sin γ₀ ^ 2 / 2 = (40000000000 + 3 * (tc : ℝ) ^ 2) / (4 * (10000000000 + (tc
    : ℝ) ^ 2)) := by
    rw [hsin_γ, hs_sq]; have hden2 : (0 : ℝ) < 10000000000 + (tc : ℝ) ^ 2 := (by positivity)
    field_simp [hden2.ne']; ring
  dsimp only [cswapCoeffUpper]; rw [hcomb_eq]
  have hprod_le : (1 - Real.sin γ₀ ^ 2 / 2) * ((π / 4 + 1 / 2 - Real.arctan (Real.tan γ₀ / √2)) / (2
    * √2)) ≤ (hSub : ℝ) / 1000000000000 := by
    have hm := mul_le_mul (le_of_eq hw_eq) hcomb_le hcomb_nn (by positivity); refine hm.trans ?_
    have hlhs : ((40000000000 + 3 * (tc : ℝ) ^ 2) / (4 * (10000000000 + (tc : ℝ) ^ 2))) * ((symDiff
      : ℝ) / (2 * 1414213562373)) = ((40000000000 + 3 * (tc : ℝ) ^ 2) * (symDiff : ℝ)) / (8 *
      (10000000000 + (tc : ℝ) ^ 2) * 1414213562373) := (by rw [div_mul_div_comm]; congr 1; ring)
    rw [hlhs, div_le_div_iff₀ (by positivity) (by positivity)]; have hcast : (40000000000 + 3 * ((tc
      : ℝ) * tc)) * (symDiff : ℝ) * 1000000000000 ≤ (hSub : ℝ) * 8 * (10000000000 + (tc : ℝ) * tc) *
      1414213562373 := (by exact_mod_cast hfin); have hident : (40000000000 + 3 * (tc : ℝ) ^ 2) *
      (symDiff : ℝ) * 1000000000000 - (hSub : ℝ) * (8 * (10000000000 + (tc : ℝ) ^ 2) *
      1414213562373) = (40000000000 + 3 * ((tc : ℝ) * tc)) * (symDiff : ℝ) * 1000000000000 - (hSub :
      ℝ) * 8 * (10000000000 + (tc : ℝ) * tc) * 1414213562373 := (by ring); linarith only [hcast,
      hident]
  rw [hhSub_r] at hprod_le; linarith only [hprod_le]
theorem cswapHitSingle_sound {tc tSymLo8 symAtanLo hHi : ℕ} (h : checkCswapHitSingle tc tSymLo8
  symAtanLo hHi = true) :
    let γ₀ := Real.arcsin (√((1 : ℝ) / 2) * Real.sin (Real.arctan ((tc : ℝ) / 100000)))
    0 ≤ γ₀ ∧ cswapCoeffUpper γ₀ ≤ (hHi : ℝ) / 1000000000000 := by
  simp only [checkCswapHitSingle, withForcedNat_eq, Bool.and_eq_true, and_assoc] at h; rcases h with
    ⟨_, htc_hi_d, htsym_sq_d, hatan_chk, hsym_cap_d, hh1_d, hfin_d⟩; have htsym_sq :=
    of_decide_eq_true htsym_sq_d
  refine cswapHit_sound_of_tan_sq (z := (tSymLo8 : ℝ) / 100000000) (of_decide_eq_true htc_hi_d)
    (of_decide_eq_true hsym_cap_d) (of_decide_eq_true hh1_d) (of_decide_eq_true hfin_d)
    (by positivity) ?_ (atanScale8Lo_sound hatan_chk); rw [div_pow, div_le_div_iff₀ (by positivity)
    (by positivity)]; have hcast : (40000000000 + 2 * ((tc : ℝ) * tc)) * tSymLo8 * tSymLo8 ≤ ((tc :
    ℝ) * tc) * 10000000000000000 := (by exact_mod_cast htsym_sq); have hident : (tSymLo8 : ℝ) ^ 2 *
    (40000000000 + 2 * (tc : ℝ) ^ 2) - (tc : ℝ) ^ 2 * (100000000 : ℝ) ^ 2 = (40000000000 + 2 * ((tc
    : ℝ) * tc)) * tSymLo8 * tSymLo8 - ((tc : ℝ) * tc) * 10000000000000000 := (by ring)
  linarith only [hcast, hident]
theorem cswapHalf12_sound {tc y12 symAtanLo hHi : ℕ} (h : checkCswapHalf12 tc y12 symAtanLo hHi =
  true) :
    let γ₀ := Real.arcsin (√((1 : ℝ) / 2) * Real.sin (Real.arctan ((tc : ℝ) / 100000)))
    0 ≤ γ₀ ∧ cswapCoeffUpper γ₀ ≤ (hHi : ℝ) / 1000000000000 := by
  simp only [checkCswapHalf12, withForcedNat_eq, Bool.and_eq_true, and_assoc] at h; rcases h with
    ⟨_, htc_hi_d, hy2_lt_d, hy_sq_d, hatan_chk, hsym_cap_d, hh1_d, hfin_d⟩; have hy2_lt :=
    of_decide_eq_true hy2_lt_d; have hy_sq := of_decide_eq_true hy_sq_d; set y : ℝ := (y12 : ℝ) /
    1000000000000; have hy0 : 0 ≤ y := (by positivity); have hy2_lt_r : (y12 : ℝ) * y12 + 1 ≤
    1000000000000000000000000 := (by exact_mod_cast hy2_lt)
  have hy12_lt : y12 < 1000000000000 := by
    by_contra hge
    have h1 : 1000000000000 ≤ y12 := Nat.le_of_not_lt hge; have h2 : 1000000000000 * 1000000000000 ≤
      y12 * y12 := Nat.mul_le_mul h1 h1; omega
  have hy1 : y < 1 := by
    dsimp only [y]; have hy12_r : (y12 : ℝ) < 1000000000000 := (by exact_mod_cast hy12_lt)
    linarith only [hy12_r]
  have h1sub : 0 < 1 - y ^ 2 := by
    have hy_sq_lt : y ^ 2 < 1 := by
      calc y ^ 2 = y * y := sq y
        _ ≤ 1 * y := mul_le_mul_of_nonneg_right hy1.le hy0
        _ < 1 := by linarith only [hy1]
    linarith only [hy_sq_lt]
  have hy_neg1 : -1 < y := lt_of_lt_of_le (by norm_num) hy0; set z : ℝ := 2 * y / (1 - y ^ 2)
  refine cswapHit_sound_of_tan_sq (z := z) (of_decide_eq_true htc_hi_d) (of_decide_eq_true
    hsym_cap_d) (of_decide_eq_true hh1_d) (of_decide_eq_true hfin_d) (by dsimp only [z]; positivity)
    ?_ ((atanHalf12Lo_sound hatan_chk).trans (le_of_eq (Real.two_mul_arctan hy_neg1 hy1)))
  have hsub_nat : ((1000000000000000000000000 - y12 * y12 : ℕ) : ℝ) = 1000000000000000000000000 -
    (y12 : ℝ) * y12 :=
    (by rw [Nat.cast_sub (by omega : y12 * y12 ≤ 1000000000000000000000000)]; push_cast; rfl)
  have hden_pos : (0 : ℝ) < 1000000000000000000000000 - (y12 : ℝ) * y12 :=
    (by linarith only [hy2_lt_r])
  have hz_eq : z = (2 * (y12 : ℝ) * 1000000000000) / (1000000000000000000000000 - (y12 : ℝ) * y12)
    := (by dsimp only [z, y]; field_simp [h1sub.ne', hden_pos.ne']; ring); rw [hz_eq, div_pow,
    div_le_div_iff₀ (pow_pos hden_pos 2) (by positivity)]
  have hcast : 4 * ((y12 : ℝ) * y12) * (40000000000 + 2 * ((tc : ℝ) * tc)) *
    1000000000000000000000000 ≤ ((tc : ℝ) * tc) * (1000000000000000000000000 - (y12 : ℝ) * y12) *
    (1000000000000000000000000 - (y12 : ℝ) * y12) := by
    have hraw : (4 : ℝ) * ((y12 : ℝ) * y12) * (40000000000 + 2 * ((tc : ℝ) * tc)) *
      1000000000000000000000000 ≤ ((tc : ℝ) * tc) * ((1000000000000000000000000 - y12 * y12 : ℕ) :
      ℝ) * ((1000000000000000000000000 - y12 * y12 : ℕ) : ℝ) := (by exact_mod_cast hy_sq)
    rwa [hsub_nat] at hraw
  linarith only [hcast, show (2 * (y12 : ℝ) * 1000000000000) ^ 2 * (40000000000 + 2 * (tc : ℝ) ^ 2)
    - (tc : ℝ) ^ 2 * (1000000000000000000000000 - (y12 : ℝ) * y12) ^ 2 = 4 * ((y12 : ℝ) * y12) *
    (40000000000 + 2 * ((tc : ℝ) * tc)) * 1000000000000000000000000 - ((tc : ℝ) * tc) *
    (1000000000000000000000000 - (y12 : ℝ) * y12) * (1000000000000000000000000 - (y12 : ℝ) * y12)
    by ring]
theorem cswapHitLock_sound {tc tSym symAtanLo hHi : ℕ} (h : checkCswapHitLock tc tSym symAtanLo hHi
  = true) :
    let γ₀ := Real.arcsin (√((1 : ℝ) / 2) * Real.sin (Real.arctan ((tc : ℝ) / 100000)))
    0 ≤ γ₀ ∧ cswapCoeffUpper γ₀ ≤ (hHi : ℝ) / 1000000000000 := by
  dsimp only [checkCswapHitLock] at h
  split_ifs at h
  · exact cswapHitSingle_sound h
  · exact cswapHalf12_sound h
end QuantumComputation.Specs.GroverFindAll.Warm2
end Sec_Warm2M2WarmCertDefs
end
