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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SevenGearBondDeferA

/-!
# Seven-Gear Bond-Deferred Dihedral Engine — Part B
Universal recursive peel-from-bottom coarse schedule identities (`32 ≤ nStd ≤ 46`, covering both
`M = 46,719` and commutator-SOS `M ≈ 36,600..44,200`), concrete `M = 46,719` `SevenGear` /
`SixGear` / `FiveGear` coarse identities, parametric `1`-bit Möttönen window step cascades
(`cWinPrefixAt`, `cWinStepAt`), and the zero-ancilla assertion lift `rExtZeroDefer0_wp_lift`
across `m1 ≤ m2 ≤ 14`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution Solution.BlockEncodingCore
open Solution.BlockEncodingCircuit Solution.TopIntegrationBridge
open Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open Solution.WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open Solution.Cat11CompactPhase2Bridge
open Solution.DihedralWalkQPE BlockReflection ApproxIqft16 SineWindowFlexM
open Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16 CleanWalkRefl2 WalkRefl2ErrLe)
open Solution.TwoGearBox hiding m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open Solution.TailShiftBox Solution.TwoGearQPEPhase5
open Solution.TwoGearBondDefer
open Solution.TailShiftWindow46847
open Solution.TailShiftThreeGear
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 3: Universal Recursive Peel-From-Bottom Algebra (`32 ≤ nStd ≤ 46`) -/

/-- Closed-form target walk-power exponent at coarse peel level `top = nStd + 1`. -/
def tailTargetVal (top : ℕ) (K t : ℤ) (x : ℕ) : ℤ :=
  if x ≤ top - 1 then -t + K * (2 * (x : ℤ) - ((top - 1 : ℕ) : ℤ))
  else t + K * ((top - 1 : ℕ) : ℤ)

theorem tailFusedScheduleFiber_eq_tailTarget {b nStd kStd kTail d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (hb2 : 2 ≤ b)
    (hnLo : 2 ^ (b - 1) ≤ nStd) (hnLt : nStd < 2 ^ b)
    (hFoldStd : ∀ q : Fin (2 ^ b), q.val ≤ nStd →
      (qpeAffinePerm b b nStd q).val < 2 ^ b - 1)
    (hFoldTop : ∀ q : Fin (2 ^ b), q.val = nStd + 1 →
      (qpeAffinePerm b b nStd q).val = 2 ^ b - 1)
    (x : Fin (2 ^ b)) (hx : x.val ≤ nStd + 1) :
    let W := R₁ * R₂
    tailFusedScheduleFiber nStd (R₁ * W ^ kStd) (R₁ * W ^ kTail) R₁ x =
      W ^ tailTargetVal (nStd + 1) (kStd : ℤ) (kTail : ℤ) x.val := by
  intro W
  have hW_pow (k : ℕ) : R₁ * (R₁ * W ^ k) = W ^ k := by
    rw [← mul_assoc, hR₁, one_mul]
  by_cases hxs : x.val ≤ nStd
  · unfold tailFusedScheduleFiber tailFusedBodyFiber tailTargetVal
    rw [Nat.add_sub_cancel, ite_eq_left hxs, ite_eq_right (ne_of_lt (hFoldStd x hxs))]
    change ((R₁ * W ^ kTail) * R₁) *
      affineScheduleFiber b nStd (R₁ * (R₁ * W ^ kStd)) R₁ x = _
    rw [affineScheduleFiber_ideal_eq_zpow (m := x) hR₁ (superRefl_involutive hR₁ hR₂ kStd)
      (by omega) le_rfl hnLo hnLt hxs, hW_pow, refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kTail,
      ← _root_.zpow_natCast W kStd, ← _root_.zpow_mul, ← _root_.zpow_add]
  · have hxt : x.val = nStd + 1 := by omega
    unfold tailFusedScheduleFiber tailTargetVal
    rw [Nat.add_sub_cancel, ite_eq_right hxs,
      tailFusedBodyFiber_allOnes_eq hb2 hnLo (R₁ * W ^ kStd) (R₁ * W ^ kTail) R₁ hR₁ _
        (hFoldTop x hxt), hW_pow, hW_pow, ← pow_mul, ← pow_add, ← _root_.zpow_natCast]
    congr 1

theorem topG0_eq_tailTarget {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (kA kB : ℕ)
    (x : Fin (2 ^ 2)) (hx : x.val ≤ 2) :
    let W := R₁ * R₂
    topG0Fiber (R₁ * W ^ kA) (R₁ * W ^ kB) R₁ x =
      W ^ tailTargetVal 2 (kA : ℤ) (kB : ℤ) x.val := by
  intro W
  have hnegA : (R₁ * W ^ kA) * R₁ = W ^ (-(kA : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kA
  have hnegB : (R₁ * W ^ kB) * R₁ = W ^ (-(kB : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kB
  have hpos (k : ℕ) : R₁ * (R₁ * W ^ k) = W ^ (k : ℤ) := by
    rw [← mul_assoc, hR₁, one_mul, ← _root_.zpow_natCast]
  rcases (by omega : x.val = 0 ∨ x.val = 1 ∨ x.val = 2) with hxv | hxv | hxv
  · have hx0 : x = ⟨0, by decide⟩ := Fin.ext hxv
    have hb1 : ((⟨0, by decide⟩ : Fin 4).val.testBit 1 == true) = false := rfl
    have hb0 : ((⟨0, by decide⟩ : Fin 4).val.testBit 0 == false) = true := rfl
    have hdec : decide ((⟨0, by decide⟩ : Fin 4) = ⟨0, by decide⟩) = true := rfl
    have htv : tailTargetVal 2 (kA : ℤ) (kB : ℤ) 0 = -(kB : ℤ) + -(kA : ℤ) := by
      dsimp [tailTargetVal]
      ring
    rw [hx0, topG0Fiber, hb1, hb0, hdec]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    change _ = W ^ tailTargetVal 2 (kA : ℤ) (kB : ℤ) 0
    rw [← mul_assoc (R₁ * W ^ kB) R₁, hnegB, hnegA, ← _root_.zpow_add, htv]
  · have hx1 : x = ⟨1, by decide⟩ := Fin.ext hxv
    have hb1 : ((⟨1, by decide⟩ : Fin 4).val.testBit 1 == true) = false := rfl
    have hb0 : ((⟨1, by decide⟩ : Fin 4).val.testBit 0 == false) = false := rfl
    have hdec : decide ((⟨1, by decide⟩ : Fin 4) = ⟨0, by decide⟩) = false := rfl
    have htv : tailTargetVal 2 (kA : ℤ) (kB : ℤ) 1 = -(kB : ℤ) + (kA : ℤ) := by
      dsimp [tailTargetVal]
      ring
    rw [hx1, topG0Fiber, hb1, hb0, hdec]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
    change _ = W ^ tailTargetVal 2 (kA : ℤ) (kB : ℤ) 1
    rw [← mul_assoc (R₁ * W ^ kB) R₁, hnegB, ← _root_.zpow_natCast W kA, ← _root_.zpow_add, htv]
  · have hx2 : x = ⟨2, by decide⟩ := Fin.ext hxv
    have hb1 : ((⟨2, by decide⟩ : Fin 4).val.testBit 1 == true) = true := rfl
    have hb0 : ((⟨2, by decide⟩ : Fin 4).val.testBit 0 == false) = true := rfl
    have hdec : decide ((⟨2, by decide⟩ : Fin 4) = ⟨0, by decide⟩) = false := rfl
    have htv : tailTargetVal 2 (kA : ℤ) (kB : ℤ) 2 = (kB : ℤ) + (kA : ℤ) := by
      dsimp [tailTargetVal]
      ring
    rw [hx2, topG0Fiber, hb1, hb0, hdec]
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    change _ = W ^ tailTargetVal 2 (kA : ℤ) (kB : ℤ) 2
    rw [← mul_assoc R₁ (R₁ * W ^ kB), hpos kB, hpos kA, ← _root_.zpow_add, htv]

theorem peel_odd {bGear q d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (hq1 : 1 ≤ q)
    (hpat : 2 * q < 2 ^ bGear) (kA kB : ℕ) (x : Fin (2 ^ bGear)) (hx : x.val ≤ 2 * q + 1) :
    let W := R₁ * R₂
    patFlipTwoStepFiber (R₁ * W ^ kA) (R₁ * W ^ kB) R₁ ⟨2 * q, hpat⟩ x *
      W ^ tailTargetVal q (2 * ((kA : ℤ) + (kB : ℤ)))
        ((kB : ℤ) + ((kA : ℤ) + (kB : ℤ))) (x.val / 2) =
      W ^ tailTargetVal (2 * q + 1) ((kA : ℤ) + (kB : ℤ)) (kB : ℤ) x.val := by
  intro W
  have hEven : (⟨2 * q, hpat⟩ : Fin (2 ^ bGear)).val.testBit 0 = false := by
    simp [Nat.testBit_zero]
  rw [patFlipTwoStep_ideal_eq_zpow hR₁ hR₂ kA kB ⟨2 * q, hpat⟩ hEven x, ← _root_.zpow_add]
  congr 1
  have hqCast : (((q - 1 : ℕ) : ℤ)) = (q : ℤ) - 1 := by omega
  have htopCast : (((2 * q + 1 - 1 : ℕ) : ℤ)) = 2 * (q : ℤ) := by omega
  by_cases hxp : x = ⟨2 * q, hpat⟩
  · have hxv : x.val = 2 * q := congrArg Fin.val hxp
    have hdiv : (2 * q) / 2 = q := by omega
    have hnle : ¬ (q ≤ q - 1) := by omega
    have hle : 2 * q ≤ 2 * q + 1 - 1 := by omega
    dsimp only [tailTargetVal]
    rw [ite_eq_left hxp, hxv, hdiv, ite_eq_right hnle, ite_eq_left hle, hqCast, htopCast]
    push_cast
    ring
  · have hxne : x.val ≠ 2 * q := fun h ↦ hxp (Fin.ext h)
    rw [ite_eq_right hxp]
    by_cases hlt : x.val < 2 * q
    · have hle1 : x.val / 2 ≤ q - 1 := by omega
      have hle2 : x.val ≤ 2 * q + 1 - 1 := by omega
      have hdiv : (x.val : ℤ) = 2 * ((x.val / 2 : ℕ) : ℤ) + ((x.val % 2 : ℕ) : ℤ) := by omega
      rw [tailTargetVal, ite_eq_left hle1, tailTargetVal, ite_eq_left hle2, hqCast, htopCast]
      cases hb0 : x.val.testBit 0
      · simp only [Nat.testBit_zero, decide_eq_false_iff_not] at hb0
        have hmod : ((x.val % 2 : ℕ) : ℤ) = 0 := by omega
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hdiv, hmod]
        ring
      · simp only [Nat.testBit_zero, decide_eq_true_eq] at hb0
        have hmod : ((x.val % 2 : ℕ) : ℤ) = 1 := by omega
        simp only [↓reduceIte]
        rw [hdiv, hmod]
        ring
    · have hxv : x.val = 2 * q + 1 := by omega
      have hdiv : (2 * q + 1) / 2 = q := by omega
      have hb0 : x.val.testBit 0 = true := by
        simp only [hxv, Nat.testBit_zero, decide_eq_true_eq]
        omega
      have hnle1 : ¬ (q ≤ q - 1) := by omega
      have hnle2 : ¬ (2 * q + 1 ≤ 2 * q + 1 - 1) := by omega
      rw [hb0, ite_eq_left rfl, hxv, hdiv, tailTargetVal, ite_eq_right hnle1, tailTargetVal,
        ite_eq_right hnle2, hqCast, htopCast]
      ring

theorem peel_even {bGear q d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (hq1 : 1 ≤ q)
    (hpat : 2 * q < 2 ^ bGear) (K : ℕ) (t : ℤ) (x : Fin (2 ^ bGear)) (hx : x.val ≤ 2 * q) :
    let W := R₁ * R₂
    singleSignedFiber (R₁ * W ^ K) R₁ ⟨2 * q, hpat⟩ x *
      W ^ tailTargetVal q (2 * (K : ℤ)) t (x.val / 2) =
      W ^ tailTargetVal (2 * q) (K : ℤ) t x.val := by
  intro W
  have hEven : (⟨2 * q, hpat⟩ : Fin (2 ^ bGear)).val.testBit 0 = false := by
    simp [Nat.testBit_zero]
  rw [singleSigned_ideal_eq_zpow hR₁ hR₂ K ⟨2 * q, hpat⟩ hEven x, ← _root_.zpow_add]
  congr 1
  have hqCast : (((q - 1 : ℕ) : ℤ)) = (q : ℤ) - 1 := by omega
  have htopCast : (((2 * q - 1 : ℕ) : ℤ)) = 2 * (q : ℤ) - 1 := by omega
  by_cases hxp : x = ⟨2 * q, hpat⟩
  · have hxv : x.val = 2 * q := congrArg Fin.val hxp
    have hdiv : (2 * q) / 2 = q := by omega
    have hnle1 : ¬ (q ≤ q - 1) := by omega
    have hnle2 : ¬ (2 * q ≤ 2 * q - 1) := by omega
    rw [ite_eq_left hxp, hxv, hdiv, tailTargetVal, ite_eq_right hnle1, tailTargetVal,
      ite_eq_right hnle2, hqCast, htopCast]
    ring
  · have hxne : x.val ≠ 2 * q := fun h ↦ hxp (Fin.ext h)
    have hlt : x.val < 2 * q := by omega
    have hle1 : x.val / 2 ≤ q - 1 := by omega
    have hle2 : x.val ≤ 2 * q - 1 := by omega
    have hdiv : (x.val : ℤ) = 2 * ((x.val / 2 : ℕ) : ℤ) + ((x.val % 2 : ℕ) : ℤ) := by omega
    rw [ite_eq_right hxp, tailTargetVal, ite_eq_left hle1, tailTargetVal, ite_eq_left hle2,
      hqCast, htopCast]
    cases hb0 : x.val.testBit 0
    · simp only [Nat.testBit_zero, decide_eq_false_iff_not] at hb0
      have hmod : ((x.val % 2 : ℕ) : ℤ) = 0 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hdiv, hmod]
      ring
    · simp only [Nat.testBit_zero, decide_eq_true_eq] at hb0
      have hmod : ((x.val % 2 : ℕ) : ℤ) = 1 := by omega
      simp only [↓reduceIte]
      rw [hdiv, hmod]
      ring

/-- Active top index `(nStd + 1) / 2 ^ g` at symbolic peel level `g` (`0` at `G4`..`4` at `G0`). -/
def peelTop (nStd g : ℕ) : ℕ := (nStd + 1) / 2 ^ g

/-- Standard coarse step size `1024 * 2 ^ g` at symbolic peel level `g`. -/
def peelK (g : ℕ) : ℕ := 1024 * 2 ^ g

/-- Accumulated tail offset `t` at symbolic peel level `g`. -/
def peelTail (nStd kTail : ℕ) : ℕ → ℕ
  | 0 => kTail
  | g + 1 =>
      if peelTop nStd g % 2 = 1 then peelTail nStd kTail g + peelK g
      else peelTail nStd kTail g

/-- First walk-step count `kA` at symbolic peel level `g` (`K - t` if odd, `K` if even). -/
def peelStepA (nStd kTail g : ℕ) : ℕ :=
  if peelTop nStd g % 2 = 1 then peelK g - peelTail nStd kTail g else peelK g

/-- Second walk-step count `kB` at symbolic peel level `g` (`t` if odd, `0` if even). -/
def peelStepB (nStd kTail g : ℕ) : ℕ :=
  if peelTop nStd g % 2 = 1 then peelTail nStd kTail g else 0

theorem peelTail_pos {nStd kTail : ℕ} (hk : 1 ≤ kTail) :
    ∀ g, 1 ≤ peelTail nStd kTail g
  | 0 => hk
  | g + 1 => by
      have ih := peelTail_pos (nStd := nStd) hk g
      dsimp only [peelTail]
      split_ifs
      · omega
      · omega

theorem peelTail_lt {nStd kTail : ℕ} (hk : kTail < 1024) :
    ∀ g, peelTail nStd kTail g < peelK g
  | 0 => hk
  | g + 1 => by
      have ih := peelTail_lt (nStd := nStd) hk g
      have hK : peelK (g + 1) = 2 * peelK g := by
        dsimp only [peelK]
        rw [pow_succ]
        ring
      dsimp only [peelTail]
      split_ifs
      · omega
      · omega

theorem peelStepA_pos {nStd kTail : ℕ} (hk : kTail < 1024) (g : ℕ) :
    1 ≤ peelStepA nStd kTail g := by
  have hlt := peelTail_lt (nStd := nStd) hk g
  have hK : 1024 ≤ peelK g := by
    dsimp only [peelK]
    have hp := Nat.one_le_two_pow (n := g)
    omega
  dsimp only [peelStepA]
  split_ifs
  · omega
  · omega

theorem peelGear_ideal_step {bGear nStd kTail g d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (hkLt : kTail < 1024)
    (hq1 : 1 ≤ peelTop nStd (g + 1)) (htop_lt : peelTop nStd g < 2 ^ bGear)
    (x : Fin (2 ^ bGear)) (hx : x.val ≤ peelTop nStd g) :
    let W := R₁ * R₂
    peelGearFiber (peelTop nStd g) htop_lt
        (R₁ * W ^ peelStepA nStd kTail g) (R₁ * W ^ peelStepB nStd kTail g) R₁ x *
      W ^ tailTargetVal (peelTop nStd (g + 1)) (peelK (g + 1) : ℤ)
        (peelTail nStd kTail (g + 1) : ℤ) (x.val / 2) =
      W ^ tailTargetVal (peelTop nStd g) (peelK g : ℤ)
        (peelTail nStd kTail g : ℤ) x.val := by
  intro W
  have htop_div : peelTop nStd (g + 1) = peelTop nStd g / 2 := by
    dsimp only [peelTop]
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have hK_next : (peelK (g + 1) : ℤ) = 2 * (peelK g : ℤ) := by
    dsimp only [peelK]
    rw [pow_succ]
    push_cast
    ring
  have htLt := peelTail_lt (nStd := nStd) hkLt g
  dsimp only [peelGearFiber, peelStepA, peelStepB, peelTail]
  by_cases hOdd : peelTop nStd g % 2 = 1
  · simp only [hOdd, ↓reduceIte]
    have hq_eq : peelTop nStd g = 2 * peelTop nStd (g + 1) + 1 := by omega
    have hpat_eq : (⟨peelTop nStd g - 1, by omega⟩ : Fin (2 ^ bGear)) =
        ⟨2 * peelTop nStd (g + 1), by omega⟩ := Fin.ext (by
      dsimp
      omega)
    have hsum : ((peelK g - peelTail nStd kTail g : ℕ) : ℤ) +
        (peelTail nStd kTail g : ℤ) = (peelK g : ℤ) := by omega
    have htNext : (((peelTail nStd kTail g + peelK g : ℕ) : ℤ)) =
        (peelTail nStd kTail g : ℤ) + (peelK g : ℤ) := Nat.cast_add _ _
    rw [hpat_eq, hK_next, htNext, ← hsum]
    simpa only [hq_eq] using peel_odd hR₁ hR₂ hq1 (by omega)
      (peelK g - peelTail nStd kTail g) (peelTail nStd kTail g) x (by omega)
  · simp only [hOdd, ↓reduceIte]
    have hq_eq : peelTop nStd g = 2 * peelTop nStd (g + 1) := by omega
    have hpat_eq : (⟨peelTop nStd g, htop_lt⟩ : Fin (2 ^ bGear)) =
        ⟨2 * peelTop nStd (g + 1), by omega⟩ := Fin.ext (by
      dsimp
      omega)
    rw [hpat_eq, hK_next]
    simpa only [hq_eq] using peel_even hR₁ hR₂ hq1 (by omega) (peelK g)
      (peelTail nStd kTail g : ℤ) x (by omega)

theorem qpeBlockHi_extract_val (b bSub s : ℕ) (hs : s + bSub ≤ b)
    (heq : s + bSub = b := by omega) (x : Fin (2 ^ b)) :
    ((QRegister.block s bSub hs : QRegister bSub b).extractIndex x).val = x.val / 2 ^ s := by
  rw [block_extractIndex_val_tg]
  refine Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul ?_)
  rw [← pow_add, heq]
  exact x.isLt

theorem symbolicSevenGear_ideal_coarse_mul_eq {nStd kTail d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1)
    (hnLo : 32 ≤ nStd) (hnHi : nStd ≤ 46) (hkLt : kTail < 1024)
    (hFoldStd : ∀ q : Fin (2 ^ 6), q.val ≤ nStd → (qpeAffinePerm 6 6 nStd q).val < 63)
    (hFoldTop : ∀ q : Fin (2 ^ 6), q.val = nStd + 1 → (qpeAffinePerm 6 6 nStd q).val = 63)
    (xc : Fin (2 ^ 6)) (hxc : xc.val ≤ nStd + 1) :
    let W := R₁ * R₂
    let x5 := (QRegister.block 1 5 (by decide) : QRegister 5 6).extractIndex xc
    let x4 := (QRegister.block 2 4 (by decide) : QRegister 4 6).extractIndex xc
    let x3 := (QRegister.block 3 3 (by decide) : QRegister 3 6).extractIndex xc
    let x2 := (QRegister.block 4 2 (by decide) : QRegister 2 6).extractIndex xc
    peelGearFiber (peelTop nStd 0) (by
        dsimp [peelTop]
        omega)
        (R₁ * W ^ peelStepA nStd kTail 0) (R₁ * W ^ peelStepB nStd kTail 0) R₁ xc *
      peelGearFiber (peelTop nStd 1) (by
        dsimp [peelTop]
        omega)
        (R₁ * W ^ peelStepA nStd kTail 1) (R₁ * W ^ peelStepB nStd kTail 1) R₁ x5 *
      peelGearFiber (peelTop nStd 2) (by
        dsimp [peelTop]
        omega)
        (R₁ * W ^ peelStepA nStd kTail 2) (R₁ * W ^ peelStepB nStd kTail 2) R₁ x4 *
      peelGearFiber (peelTop nStd 3) (by
        dsimp [peelTop]
        omega)
        (R₁ * W ^ peelStepA nStd kTail 3) (R₁ * W ^ peelStepB nStd kTail 3) R₁ x3 *
      topG0Fiber (R₁ * W ^ peelK 4) (R₁ * W ^ peelTail nStd kTail 4) R₁ x2 =
      tailFusedScheduleFiber nStd (R₁ * W ^ 1024) (R₁ * W ^ kTail) R₁ xc := by
  intro W x5 x4 x3 x2
  have hx5 : x5.val = xc.val / 2 := qpeBlockHi_extract_val 6 5 1 (by decide) rfl xc
  have hx4 : x4.val = xc.val / 4 := qpeBlockHi_extract_val 6 4 2 (by decide) rfl xc
  have hx3 : x3.val = xc.val / 8 := qpeBlockHi_extract_val 6 3 3 (by decide) rfl xc
  have hx2 : x2.val = xc.val / 16 := qpeBlockHi_extract_val 6 2 4 (by decide) rfl xc
  have hx4_div : x4.val = x5.val / 2 := by omega
  have hx3_div : x3.val = x4.val / 2 := by omega
  have hx2_div : x2.val = x3.val / 2 := by omega
  have htop4 : peelTop nStd 4 = 2 := by
    dsimp [peelTop]
    omega
  have hg0 : topG0Fiber (R₁ * W ^ peelK 4) (R₁ * W ^ peelTail nStd kTail 4) R₁ x2 =
      W ^ tailTargetVal (peelTop nStd 4) (peelK 4 : ℤ) (peelTail nStd kTail 4 : ℤ)
        (x3.val / 2) := by
    rw [htop4, ← hx2_div]
    exact topG0_eq_tailTarget hR₁ hR₂ (peelK 4) (peelTail nStd kTail 4) x2 (by omega)
  have hg1 := peelGear_ideal_step (bGear := 3) (nStd := nStd) (kTail := kTail) (g := 3)
    hR₁ hR₂ hkLt (by
      dsimp [peelTop]
      omega) (by
      dsimp [peelTop]
      omega) x3 (by
      dsimp [peelTop]
      omega)
  have hg2 := peelGear_ideal_step (bGear := 4) (nStd := nStd) (kTail := kTail) (g := 2)
    hR₁ hR₂ hkLt (by
      dsimp [peelTop]
      omega) (by
      dsimp [peelTop]
      omega) x4 (by
      dsimp [peelTop]
      omega)
  have hg3 := peelGear_ideal_step (bGear := 5) (nStd := nStd) (kTail := kTail) (g := 1)
    hR₁ hR₂ hkLt (by
      dsimp [peelTop]
      omega) (by
      dsimp [peelTop]
      omega) x5 (by
      dsimp [peelTop]
      omega)
  have hg4 := peelGear_ideal_step (bGear := 6) (nStd := nStd) (kTail := kTail) (g := 0)
    hR₁ hR₂ hkLt (by
      dsimp [peelTop]
      omega) (by
      dsimp [peelTop]
      omega) xc (by
      dsimp [peelTop]
      omega)
  dsimp only at hg1 hg2 hg3 hg4
  rw [← hx3_div] at hg2
  rw [← hx4_div] at hg3
  rw [← hx5] at hg4
  have hFin := tailFusedScheduleFiber_eq_tailTarget (b := 6) (nStd := nStd)
    (kStd := 1024) (kTail := kTail) hR₁ hR₂ (by decide) (by omega) (by omega)
    hFoldStd hFoldTop xc hxc
  dsimp only at hFin
  have htop0 : peelTop nStd 0 = nStd + 1 := by
    dsimp [peelTop]
    omega
  simp only [hg0, mul_assoc]
  rw [hg1, hg2, hg3, hg4, htop0, hFin]
  rfl

theorem oddPairG1_ideal_eq_zpow {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (kA kB : ℕ)
    (x : Fin (2 ^ 3)) (hx : x.val ≤ 5) :
    let W := R₁ * R₂
    oddPairG1Fiber (R₁ * W ^ kA) (R₁ * W ^ kB) R₁ x =
      W ^ (if x = ⟨4, by decide⟩ then (kA : ℤ) - (kB : ℤ)
           else if x = ⟨5, by decide⟩ then (kA : ℤ) + (kB : ℤ)
           else if x.val.testBit 0 then (kA : ℤ) - (kB : ℤ)
           else -((kA : ℤ) + (kB : ℤ))) := by
  intro W
  have hnA : (R₁ * W ^ kA) * R₁ = W ^ (-(kA : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kA
  have hnB : (R₁ * W ^ kB) * R₁ = W ^ (-(kB : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kB
  have hp (k : ℕ) : R₁ * (R₁ * W ^ k) = W ^ (k : ℤ) := by
    rw [← mul_assoc, hR₁, one_mul, ← _root_.zpow_natCast]
  have ⟨hft, hff, htt, htf⟩ :
      (false == true) = false ∧ (false == false) = true ∧
      (true == true) = true ∧ (true == false) = false := ⟨rfl, rfl, rfl, rfl⟩
  by_cases hx4 : x = ⟨4, by decide⟩
  · have hb0 : ((⟨4, by decide⟩ : Fin 8).val.testBit 0 == false) = true := rfl
    have hb2 : ((⟨4, by decide⟩ : Fin 8).val.testBit 2 == true) = true := rfl
    have hd4 : decide ((⟨4, by decide⟩ : Fin 8) = ⟨4, by decide⟩) = true := rfl
    have hd5 : decide ((⟨4, by decide⟩ : Fin 8) = ⟨5, by decide⟩) = false := rfl
    rw [ite_eq_left hx4, hx4, oddPairG1Fiber, hd4, hd5, hb0, hb2]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hR₁, mul_one]
    rw [← mul_assoc (R₁ * W ^ kB) R₁, hnB, hp kA, ← _root_.zpow_add]
    congr 1
    ring
  · rw [ite_eq_right hx4]
    by_cases hx5 : x = ⟨5, by decide⟩
    · have hb0 : ((⟨5, by decide⟩ : Fin 8).val.testBit 0 == false) = false := rfl
      have hb2 : ((⟨5, by decide⟩ : Fin 8).val.testBit 2 == true) = true := rfl
      have hd4 : decide ((⟨5, by decide⟩ : Fin 8) = ⟨4, by decide⟩) = false := rfl
      have hd5 : decide ((⟨5, by decide⟩ : Fin 8) = ⟨5, by decide⟩) = true := rfl
      rw [ite_eq_left hx5, hx5, oddPairG1Fiber, hd4, hd5, hb0, hb2]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
      rw [← mul_assoc R₁ (R₁ * W ^ kB), hp kB, hp kA, ← _root_.zpow_add]
      congr 1
      ring
    · have hxne4 : x.val ≠ 4 := fun h ↦ hx4 (Fin.ext h)
      have hxne5 : x.val ≠ 5 := fun h ↦ hx5 (Fin.ext h)
      have hb2 : x.val.testBit 2 = false := by
        rcases (by omega : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3) with h | h | h | h
        · rw [h]
          rfl
        · rw [h]
          rfl
        · rw [h]
          rfl
        · rw [h]
          rfl
      rw [ite_eq_right hx5, oddPairG1Fiber, decide_eq_false hx4, decide_eq_false hx5, hb2, hft]
      cases hb0 : x.val.testBit 0
      · rw [hff]
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
        rw [← mul_assoc (R₁ * W ^ kB) R₁, hnB, hnA, ← _root_.zpow_add]
        congr 1
        ring
      · rw [htf]
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
        rw [← mul_assoc (R₁ * W ^ kB) R₁, hnB, ← _root_.zpow_natCast W kA, ← _root_.zpow_add]
        congr 1
        ring

theorem oddPairG2_ideal_eq_zpow {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (kA kB : ℕ) (x : Fin (2 ^ 4)) :
    let W := R₁ * R₂
    oddPairG2Fiber (R₁ * W ^ kA) (R₁ * W ^ kB) R₁ x =
      W ^ (if x = ⟨10, by decide⟩ then (kA : ℤ) - (kB : ℤ)
           else if x = ⟨11, by decide⟩ then (kA : ℤ) + (kB : ℤ)
           else if x.val.testBit 0 then (kA : ℤ) - (kB : ℤ)
           else -((kA : ℤ) + (kB : ℤ))) := by
  intro W
  have hnA : (R₁ * W ^ kA) * R₁ = W ^ (-(kA : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kA
  have hnB : (R₁ * W ^ kB) * R₁ = W ^ (-(kB : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kB
  have hp (k : ℕ) : R₁ * (R₁ * W ^ k) = W ^ (k : ℤ) := by
    rw [← mul_assoc, hR₁, one_mul, ← _root_.zpow_natCast]
  have ⟨hff, htf⟩ : (false == false) = true ∧ (true == false) = false := ⟨rfl, rfl⟩
  by_cases hx10 : x = ⟨10, by decide⟩
  · have hb0 : ((⟨10, by decide⟩ : Fin 16).val.testBit 0 == false) = true := rfl
    have hd10 : decide ((⟨10, by decide⟩ : Fin 16) = ⟨10, by decide⟩) = true := rfl
    have hd11 : decide ((⟨10, by decide⟩ : Fin 16) = ⟨11, by decide⟩) = false := rfl
    rw [ite_eq_left hx10, hx10, oddPairG2Fiber, hd10, hd11, hb0]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hR₁, mul_one]
    rw [← mul_assoc (R₁ * W ^ kB) R₁, hnB, hp kA, ← _root_.zpow_add]
    congr 1
    ring
  · rw [ite_eq_right hx10]
    by_cases hx11 : x = ⟨11, by decide⟩
    · have hb0 : ((⟨11, by decide⟩ : Fin 16).val.testBit 0 == false) = false := rfl
      have hd10 : decide ((⟨11, by decide⟩ : Fin 16) = ⟨10, by decide⟩) = false := rfl
      have hd11 : decide ((⟨11, by decide⟩ : Fin 16) = ⟨11, by decide⟩) = true := rfl
      rw [ite_eq_left hx11, hx11, oddPairG2Fiber, hd10, hd11, hb0]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
      rw [← mul_assoc R₁ (R₁ * W ^ kB), hp kB, hp kA, ← _root_.zpow_add]
      congr 1
      ring
    · rw [ite_eq_right hx11, oddPairG2Fiber, decide_eq_false hx10, decide_eq_false hx11]
      cases hb0 : x.val.testBit 0
      · rw [hff]
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
        rw [← mul_assoc (R₁ * W ^ kB) R₁, hnB, hnA, ← _root_.zpow_add]
        congr 1
        ring
      · rw [htf]
        simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
        rw [← mul_assoc (R₁ * W ^ kB) R₁, hnB, ← _root_.zpow_natCast W kA, ← _root_.zpow_add]
        congr 1
        ring

theorem sevenGear_g2g1g0_eq_tailTarget11 {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (x4 : Fin (2 ^ 4)) (hx4 : x4.val ≤ 11) :
    let W := R₁ * R₂
    let x3 : Fin (2 ^ 3) := ⟨x4.val / 2, by omega⟩
    let x2 : Fin (2 ^ 2) := ⟨x4.val / 4, by omega⟩
    oddPairG2Fiber (R₁ * W ^ 4096) (R₁ * W ^ 1664) R₁ x4 *
      (oddPairG1Fiber (R₁ * W ^ 8192) (R₁ * W ^ 4096) R₁ x3 *
        topG0Fiber (R₁ * W ^ 16384) (R₁ * W ^ 8192) R₁ x2) =
      W ^ tailTargetVal 11 4096 1664 x4.val := by
  intro W x3 x2
  rw [oddPairG2_ideal_eq_zpow hR₁ hR₂ 4096 1664 x4,
    oddPairG1_ideal_eq_zpow hR₁ hR₂ 8192 4096 x3 (by
      dsimp [x3]
      omega),
    topG0_eq_tailTarget hR₁ hR₂ 16384 8192 x2 (by
      dsimp [x2]
      omega),
    ← _root_.zpow_add, ← _root_.zpow_add]
  congr 1
  dsimp only [x3, x2]
  revert hx4
  revert x4
  decide

theorem qpeAffinePerm_self_val {b : ℕ} (hb1 : 1 ≤ b) (nStd : ℕ) (q : Fin (2 ^ b)) :
    (qpeAffinePerm b b nStd q).val = affineFoldVal (b - 1) (nStd + 1 - 2 ^ (b - 1)) q.val := by
  dsimp only [qpeAffinePerm]
  rw [dite_eq_left ⟨hb1, le_rfl⟩]
  rfl

theorem sevenGear_ideal_coarse_mul_eq {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (xc : Fin (2 ^ 6)) (hxc : xc.val ≤ 45) :
    let W := R₁ * R₂
    let x5 := (QRegister.block 1 5 (by decide) : QRegister 5 6).extractIndex xc
    let x4 := (QRegister.block 2 4 (by decide) : QRegister 4 6).extractIndex xc
    let x3 := (QRegister.block 3 3 (by decide) : QRegister 3 6).extractIndex xc
    let x2 := (QRegister.block 4 2 (by decide) : QRegister 2 6).extractIndex xc
    patFlipTwoStepFiber (R₁ * W ^ 384) (R₁ * W ^ 640) R₁ ⟨44, by decide⟩ xc *
      (singleSignedFiber (R₁ * W ^ 2048) R₁ ⟨22, by decide⟩ x5 *
        (oddPairG2Fiber (R₁ * W ^ 4096) (R₁ * W ^ 1664) R₁ x4 *
          (oddPairG1Fiber (R₁ * W ^ 8192) (R₁ * W ^ 4096) R₁ x3 *
            topG0Fiber (R₁ * W ^ 16384) (R₁ * W ^ 8192) R₁ x2))) =
      tailFusedScheduleFiber 44 (R₁ * W ^ 1024) (R₁ * W ^ 640) R₁ xc := by
  intro W x5 x4 x3 x2
  let ts := tailShiftParams_46719_10 7
  have hx5 : x5.val = xc.val / 2 := qpeBlockHi_extract_val 6 5 1 (by decide) rfl xc
  have hx4 : x4.val = xc.val / 4 := qpeBlockHi_extract_val 6 4 2 (by decide) rfl xc
  have hx3 : x3.val = xc.val / 8 := qpeBlockHi_extract_val 6 3 3 (by decide) rfl xc
  have hx2 : x2.val = xc.val / 16 := qpeBlockHi_extract_val 6 2 4 (by decide) rfl xc
  have hx4_div : x4.val = x5.val / 2 := by omega
  have hx3_eq : x3 = ⟨x4.val / 2, by omega⟩ := Fin.ext (by
    dsimp
    omega)
  have hx2_eq : x2 = ⟨x4.val / 4, by omega⟩ := Fin.ext (by
    dsimp
    omega)
  have hBase := sevenGear_g2g1g0_eq_tailTarget11 hR₁ hR₂ x4 (by omega)
  dsimp only at hBase
  rw [← hx3_eq, ← hx2_eq, hx4_div] at hBase
  have hg3 := peel_even (bGear := 5) (q := 11) hR₁ hR₂ (by decide) (by decide) 2048 1664 x5
    (by omega)
  have hg4 := peel_odd (bGear := 6) (q := 22) hR₁ hR₂ (by decide) (by decide)
    384 640 xc (by omega)
  dsimp only at hg3 hg4
  simp only [Nat.cast_ofNat] at hg3 hg4
  rw [show (2 : ℤ) * 2048 = 4096 by norm_num] at hg3
  rw [show (384 : ℤ) + 640 = 1024 by norm_num, show (2 : ℤ) * 1024 = 2048 by norm_num,
    show (640 : ℤ) + 1024 = 1664 by norm_num, ← hx5] at hg4
  have hFin := tailFusedScheduleFiber_eq_tailTarget (b := 6) (nStd := 44)
    (kStd := 1024) (kTail := 640) hR₁ hR₂ (by decide) (by decide) (by decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      exact ts.hFoldStd q hq)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide), hq]
      exact ts.hFoldTop) xc hxc
  dsimp only at hFin
  simp only [Nat.cast_ofNat] at hFin
  rw [hBase, hg3, hg4, hFin]

theorem sixGear_ideal_coarse_mul_eq {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (xc : Fin (2 ^ 6)) (hxc : xc.val ≤ 45) :
    let W := R₁ * R₂
    let x5 := (QRegister.block 1 5 (by decide) : QRegister 5 6).extractIndex xc
    let x4 := (QRegister.block 2 4 (by decide) : QRegister 4 6).extractIndex xc
    let x3 := (QRegister.block 3 3 (by decide) : QRegister 3 6).extractIndex xc
    patFlipTwoStepFiber (R₁ * W ^ 384) (R₁ * W ^ 640) R₁ ⟨44, by decide⟩ xc *
      (singleSignedFiber (R₁ * W ^ 2048) R₁ ⟨22, by decide⟩ x5 *
        (patFlipTwoStepFiber (R₁ * W ^ 2432) (R₁ * W ^ 1664) R₁ ⟨10, by decide⟩ x4 *
          (tailFusedScheduleFiber 4 (R₁ * W ^ 8192) (R₁ * W ^ 5760) R₁ x3 * 1))) =
      tailFusedScheduleFiber 44 (R₁ * W ^ 1024) (R₁ * W ^ 640) R₁ xc := by
  intro W x5 x4 x3
  let ts := tailShiftParams_46719_10 7
  have hx5 : x5.val = xc.val / 2 := qpeBlockHi_extract_val 6 5 1 (by decide) rfl xc
  have hx4 : x4.val = xc.val / 4 := qpeBlockHi_extract_val 6 4 2 (by decide) rfl xc
  have hx3 : x3.val = xc.val / 8 := qpeBlockHi_extract_val 6 3 3 (by decide) rfl xc
  have hx4_div : x4.val = x5.val / 2 := by omega
  have hx3_div : x3.val = x4.val / 2 := by omega
  have hg1 := tailFusedScheduleFiber_eq_tailTarget (b := 3) (nStd := 4)
    (kStd := 8192) (kTail := 5760) hR₁ hR₂ (by decide) (by decide) (by decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      revert hq
      revert q
      decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      revert hq
      revert q
      decide) x3 (by omega)
  have hg2 := peel_odd (bGear := 4) (q := 5) hR₁ hR₂ (by decide) (by decide)
    2432 1664 x4 (by omega)
  have hg3 := peel_even (bGear := 5) (q := 11) hR₁ hR₂ (by decide) (by decide) 2048 1664 x5
    (by omega)
  have hg4 := peel_odd (bGear := 6) (q := 22) hR₁ hR₂ (by decide) (by decide)
    384 640 xc (by omega)
  dsimp only at hg1 hg2 hg3 hg4
  simp only [Nat.cast_ofNat] at hg1 hg2 hg3 hg4
  rw [hx3_div] at hg1
  rw [show (2432 : ℤ) + 1664 = 4096 by norm_num, show (2 : ℤ) * 4096 = 8192 by norm_num,
    show (1664 : ℤ) + 4096 = 5760 by norm_num] at hg2
  rw [show (2 : ℤ) * 2048 = 4096 by norm_num, ← hx4_div] at hg3
  rw [show (384 : ℤ) + 640 = 1024 by norm_num, show (2 : ℤ) * 1024 = 2048 by norm_num,
    show (640 : ℤ) + 1024 = 1664 by norm_num, ← hx5] at hg4
  have hFin := tailFusedScheduleFiber_eq_tailTarget (b := 6) (nStd := 44)
    (kStd := 1024) (kTail := 640) hR₁ hR₂ (by decide) (by decide) (by decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      exact ts.hFoldStd q hq)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide), hq]
      exact ts.hFoldTop) xc hxc
  dsimp only at hFin
  simp only [Nat.cast_ofNat] at hFin
  rw [mul_one, hg1, hg2, hg3, hg4, hFin]

theorem fiveGear_ideal_coarse_mul_eq {d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (xc : Fin (2 ^ 6)) (hxc : xc.val ≤ 45) :
    let W := R₁ * R₂
    let x5 := (QRegister.block 1 5 (by decide) : QRegister 5 6).extractIndex xc
    let x4 := (QRegister.block 2 4 (by decide) : QRegister 4 6).extractIndex xc
    patFlipTwoStepFiber (R₁ * W ^ 384) (R₁ * W ^ 640) R₁ ⟨44, by decide⟩ xc *
      (singleSignedFiber (R₁ * W ^ 2048) R₁ ⟨22, by decide⟩ x5 *
        (tailFusedScheduleFiber 10 (R₁ * W ^ 4096) (R₁ * W ^ 1664) R₁ x4 * (1 * 1))) =
      tailFusedScheduleFiber 44 (R₁ * W ^ 1024) (R₁ * W ^ 640) R₁ xc := by
  intro W x5 x4
  let ts := tailShiftParams_46719_10 7
  have hx5 : x5.val = xc.val / 2 := qpeBlockHi_extract_val 6 5 1 (by decide) rfl xc
  have hx4 : x4.val = xc.val / 4 := qpeBlockHi_extract_val 6 4 2 (by decide) rfl xc
  have hx4_div : x4.val = x5.val / 2 := by omega
  have hg2 := tailFusedScheduleFiber_eq_tailTarget (b := 4) (nStd := 10)
    (kStd := 4096) (kTail := 1664) hR₁ hR₂ (by decide) (by decide) (by decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      revert hq
      revert q
      decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      revert hq
      revert q
      decide) x4 (by omega)
  have hg3 := peel_even (bGear := 5) (q := 11) hR₁ hR₂ (by decide) (by decide) 2048 1664 x5
    (by omega)
  have hg4 := peel_odd (bGear := 6) (q := 22) hR₁ hR₂ (by decide) (by decide)
    384 640 xc (by omega)
  dsimp only at hg2 hg3 hg4
  simp only [Nat.cast_ofNat] at hg2 hg3 hg4
  rw [hx4_div] at hg2
  rw [show (2 : ℤ) * 2048 = 4096 by norm_num] at hg3
  rw [show (384 : ℤ) + 640 = 1024 by norm_num, show (2 : ℤ) * 1024 = 2048 by norm_num,
    show (640 : ℤ) + 1024 = 1664 by norm_num, ← hx5] at hg4
  have hFin := tailFusedScheduleFiber_eq_tailTarget (b := 6) (nStd := 44)
    (kStd := 1024) (kTail := 640) hR₁ hR₂ (by decide) (by decide) (by decide)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide)]
      exact ts.hFoldStd q hq)
    (fun q hq ↦ by
      rw [qpeAffinePerm_self_val (by decide), hq]
      exact ts.hFoldTop) xc hxc
  dsimp only at hFin
  simp only [Nat.cast_ofNat] at hFin
  rw [mul_one, mul_one, hg2, hg3, hg4, hFin]

/-! ## Section 4: Parametric Single-Bit Möttönen Window Step Cascades (`m ∈ 10..14`) -/

/-- Prefix of `16 - m` coarse Walsh trees from `d : TwoGearRegimeData`. -/
abbrev treesPrefix (d : TwoGearRegimeData) (m : ℕ) : List WordPairTree :=
  (d.hiTrees.take (16 - d.mLow)).take (16 - m)

theorem treesPrefix_take (d : TwoGearRegimeData) (m : ℕ) :
    (treesPrefix d m).take (16 - (m + 1)) = treesPrefix d (m + 1) := by
  dsimp only [treesPrefix]
  rw [List.take_take, Nat.min_eq_left (by omega)]

/-- Prefix Möttönen window preparation circuit on QPE bits `m..15` (`m ≤ 15`). -/
def cWinPrefixAt (d : TwoGearRegimeData) (m : ℕ) : Circuit (0 + (16 - m)) :=
  (mottonenCascade (16 - m) (16 - m) le_rfl (treesPrefix d m)).onRegister
    (QRegister.block 0 (16 - m) le_rfl)

/-- Single-bit Möttönen window transition circuit on QPE bits `m..15` (`m < 16`). -/
def cWinStepAt (d : TwoGearRegimeData) (m : ℕ) (hm16 : m < 16 := by decide) :
    Circuit (0 + (16 - m)) :=
  (mottonenCascade (16 - m) 1 (by omega)
    ((treesPrefix d m).drop (16 - (m + 1)))).onRegister
    (QRegister.block 0 (16 - m) le_rfl)

theorem cWinStepAt_add_count {dg : ℕ} (d : TwoGearRegimeData) {m : ℕ}
    (hm15 : m < 15) (g : PrimitiveGate dg) :
    (cWinPrefixAt d (m + 1)).count g + (cWinStepAt d m (by omega)).count g =
      (cWinPrefixAt d m).count g := by
  have hSplit := mottonenCascade_split_of_eq (16 - m) 1 (16 - (m + 1)) (16 - (m + 1)) (16 - m)
    (by omega) (by omega) (by omega) (treesPrefix d m)
  dsimp only [cWinPrefixAt, cWinStepAt]
  rw [Circuit.count_onRegister, Circuit.count_onRegister, Circuit.count_onRegister,
    ← treesPrefix_take d m]
  exact hSplit.1 g

theorem cWinStepAt_mul_prefix_eval (d : TwoGearRegimeData) {m : ℕ} (hm15 : m < 15) :
    (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _)).embedUnitary
        (cWinStepAt d m (by omega)).eval *
      (rWinHiDeferInQPE (m + 1) 0 (by omega) (Nat.zero_le _)).embedUnitary
        (cWinPrefixAt d (m + 1)).eval =
    (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _)).embedUnitary (cWinPrefixAt d m).eval := by
  have hSplit := mottonenCascade_split_of_eq (16 - m) 1 (16 - (m + 1)) (16 - (m + 1)) (16 - m)
    (by omega) (by omega) (by omega) (treesPrefix d m)
  let rCm : QRegister (16 - m) 16 := QRegister.block m (16 - m) (by omega)
  have hrm : (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _)).compose
      (QRegister.block 0 (16 - m) le_rfl) = rCm := concat_zero_compose_drop0 _ _ _
  have hrm1 : (rWinHiDeferInQPE (m + 1) 0 (by omega) (Nat.zero_le _)).compose
      (QRegister.block 0 (16 - (m + 1)) le_rfl) =
      rCm.compose (QRegister.block 1 (16 - (m + 1)) (by omega)) := by
    dsimp only [rWinHiDeferInQPE, rHiInQPE16]
    rw [concat_zero_compose_drop0]
    apply BlockEncodingCircuit.qreg_ext
    intro i
    apply Fin.ext
    dsimp only [rCm, rHiInQPE16]
    have hi := i.isLt
    simp only [QRegister.compose_apply, QRegister.block_apply_val]
    omega
  dsimp only [cWinStepAt, cWinPrefixAt]
  rw [Circuit.eval_onRegister, Circuit.eval_onRegister, Circuit.eval_onRegister,
    ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    ← QRegister.embedUnitary_compose, hrm, hrm1, QRegister.embedUnitary_compose,
    ← QRegister.embedUnitary_mul, ← treesPrefix_take d m]
  exact congrArg rCm.embedUnitary hSplit.2

theorem comm_cWinStepAt_mux (d : TwoGearRegimeData) {m : ℕ} (hm15 : m < 15)
    (mOut mMid : ℕ) (F : Fin (2 ^ (16 - (m + 1))) → FGWalkU mOut mMid) :
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rWC := rWalkCatInAct 16 11 mOut mMid
    let rHiPrev := rHiInQPE16 (m + 1) (by omega)
    have hDisj : (rQPE.compose rHiPrev).DisjointWires rWC :=
      QubitisedWalk.disjointWires_compose_left (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    (rQPE.compose (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _))).embedUnitary
        (cWinStepAt d m (by omega)).eval *
      ((rQPE.compose rHiPrev).concat rWC hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) =
    ((rQPE.compose rHiPrev).concat rWC hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) *
      (rQPE.compose (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _))).embedUnitary
        (cWinStepAt d m (by omega)).eval := by
  intro rQPE rWC rHiPrev hDisj
  let rCm : QRegister (16 - m) 16 := QRegister.block m (16 - m) (by omega)
  have hrm : (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _)).compose
      (QRegister.block 0 (16 - m) le_rfl) = rCm := concat_zero_compose_drop0 _ _ _
  dsimp only [cWinStepAt]
  rw [Circuit.eval_onRegister, ← QRegister.embedUnitary_compose, QRegister.compose_assoc, hrm]
  refine mottonenCascade_comm_qpeMuxUnitary (rQPE.compose rHiPrev) rWC hDisj F
    (rQPE.compose rCm)
    (QubitisedWalk.disjointWires_compose_left (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid))
    1 (by omega) (fun j hj hm' ↦ ?_) _
  obtain ⟨ic, hic⟩ := (QRegister.mem_image _ _).mp hm'
  have hv := congrArg Fin.val (rQPE.wires.injective hic)
  simp only [rHiPrev, rHiInQPE16, rCm, QRegister.block_apply_val] at hv
  omega

/-! ## Section 5: Zero-Ancilla `wp` Lift Across Borrowed QPE Cuts (`m1 ≤ m2 ≤ 14`) -/

theorem rExtZeroDefer0_wp_lift {Var : Type} [Finite Var] {n : ℕ}
    (wOuter wInner2 ko km m1 m2 sRem : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hm12 : m1 ≤ m2) (hm2_14 : m2 ≤ 14) (rSys : FGSysReg n)
    (rAnc : FGAncReg wOuter wInner2 ko km sRem n) (hdisj : rSys.DisjointWires rAnc)
    {Θ₁ Θ₂ : Store Var → Observable (Fin (2 ^ n))}
    (hEq : restrictAssertionToZeroAncilla Θ₁
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m1 0 sRem hkOut hkMid (le_trans hm12 hm2_14)
            (Nat.zero_le _))) =
      restrictAssertionToZeroAncilla Θ₂
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m1 0 sRem hkOut hkMid (le_trans hm12 hm2_14)
            (Nat.zero_le _)))) :
    restrictAssertionToZeroAncilla Θ₁
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m2 0 sRem hkOut hkMid hm2_14 (Nat.zero_le _))) =
      restrictAssertionToZeroAncilla Θ₂
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m2 0 sRem hkOut hkMid hm2_14
              (Nat.zero_le _))) := by
  cases nonempty_fintype Var
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  let combined := rSys.concat rAnc hdisj
  let rExt2 := rExtZeroDeferLocB wOuter wInner2 ko km m2 0 sRem hkOut hkMid hm2_14 (Nat.zero_le _)
  let rExt1 := rExtZeroDeferLocB wOuter wInner2 ko km m1 0 sRem hkOut hkMid (le_trans hm12 hm2_14)
    (Nat.zero_le _)
  let rBor2 :=
    rBorrowLocB wOuter wInner2 ko km (m2 + 1) 0 sRem (by omega) (by omega) (Nat.zero_le _)
  let rBor1 :=
    rBorrowLocB wOuter wInner2 ko km (m1 + 1) 0 sRem (by omega) (by omega) (Nat.zero_le _)
  let rBorMid := (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose
    (.block m1 (m2 - m1) (by omega))
  let rExt2_emb := combined.compose rExt2
  let rExt1_emb := combined.compose rExt1
  let rBorMid_emb := combined.compose rBorMid
  have hdisj_e1_mid : rExt1_emb.DisjointWires rBorMid_emb :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by
      have hloc := combined.wires.injective hij
      rcases finSumFinEquiv.surjective i with ⟨ifull | ibor, rfl⟩
      · simp only [finSumFinEquiv_apply_left, rExt1, rExtZeroDeferLocB, rExtZeroLocB,
          QRegister.concat_apply_left] at hloc
        have hd :=
          rFullZeroLocB_disjoint_rBorrowLocB wOuter wInner2 ko km (m2 + 1) 0 sRem hkOut hkMid
          (by omega) (by omega) (Nat.zero_le _)
        let jb : Fin ((m2 + 1) - 1 - 0) := ⟨m1 + j.val, by omega⟩
        have hjb : rBor2 jb = rBorMid j :=
          congrArg (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem) (Fin.ext (by
            simp only [rBorrowInQPE16, QRegister.block_apply_val, jb]
            omega))
        exact hd.ne ifull jb (hloc.trans hjb.symm)
      · simp only [finSumFinEquiv_apply_right, rExt1, rExtZeroDeferLocB, rExtZeroLocB,
          QRegister.concat_apply_right, rBorrowLocB, rBorMid, QRegister.compose_apply] at hloc
        have hv := congrArg Fin.val ((rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).wires.injective
          hloc)
        have hib := ibor.isLt
        simp only [rBorrowInQPE16, QRegister.block_apply_val] at hv
        omega
  have hExt2_cast (Θ : Store Var → Observable (Fin (2 ^ n))) :
      restrictAssertionToZeroAncilla Θ rExt2_emb =
        restrictAssertionToZeroAncilla Θ (rExt1_emb.concat rBorMid_emb hdisj_e1_mid) := by
    let kF := scrAncillas 16 0 aRem mRem sRem + (ko + km)
    have hk_len : kF + (m2 + 1 - 1 - 0) = kF + (m1 + 1 - 1 - 0) + (m2 - m1) := by omega
    refine restrictZero_castLen hk_len Θ rExt2_emb (rExt1_emb.concat rBorMid_emb hdisj_e1_mid)
      fun idx ↦ ?_
    have hlt : idx.val < kF + ((m2 + 1) - 1 - 0) := idx.isLt
    by_cases h1lt : idx.val < kF
    · let i0 : Fin kF := ⟨idx.val, h1lt⟩
      have hiL : idx = Fin.castAdd _ i0 := Fin.ext rfl
      have hiR : idx.cast hk_len = Fin.castAdd (m2 - m1) (Fin.castAdd ((m1 + 1) - 1 - 0) i0) :=
        Fin.ext rfl
      conv_lhs => rw [hiL]
      conv_rhs => rw [hiR]
      simp only [rExt2_emb, rExt1_emb, rExt2, rExt1, rExtZeroDeferLocB, rExtZeroLocB,
        QRegister.compose_apply, QRegister.concat_apply_left]
    · let j2 : Fin ((m2 + 1) - 1 - 0) := ⟨idx.val - kF, by omega⟩
      have hiL : idx = Fin.natAdd kF j2 := Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp h1lt)).symm
      by_cases h2lt : idx.val < kF + ((m1 + 1) - 1 - 0)
      · let j1 : Fin ((m1 + 1) - 1 - 0) := ⟨idx.val - kF, by omega⟩
        have hiR : idx.cast hk_len = Fin.castAdd (m2 - m1) (Fin.natAdd kF j1) :=
          Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp h1lt)).symm
        conv_lhs => rw [hiL]
        conv_rhs => rw [hiR]
        simp only [kF, aRem, mRem, rExt2_emb, rExt1_emb, rExt2, rExt1, rExtZeroDeferLocB,
          rExtZeroLocB, QRegister.compose_apply, QRegister.concat_apply_left,
          QRegister.concat_apply_right]
        exact congrArg combined (show rBor2 j2 = rBor1 j1 from
          congrArg (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem) (Fin.ext rfl))
      · let jM : Fin (m2 - m1) := ⟨idx.val - (kF + ((m1 + 1) - 1 - 0)), by omega⟩
        have hiR : idx.cast hk_len = Fin.natAdd (kF + ((m1 + 1) - 1 - 0)) jM :=
          Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp h2lt)).symm
        conv_lhs => rw [hiL]
        conv_rhs => rw [hiR]
        simp only [kF, aRem, mRem, rExt2_emb, rBorMid_emb, rExt2, rExtZeroDeferLocB,
          rExtZeroLocB, QRegister.compose_apply, QRegister.concat_apply_right]
        exact congrArg combined (show rBor2 j2 = rBorMid jM from
          congrArg (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem) (Fin.ext (by
            simp only [rBorrowInQPE16, QRegister.block_apply_val, j2, jM]
            omega)))
  exact (hExt2_cast Θ₁).trans ((restrictAssertionToZeroAncilla_concat Θ₁ rExt1_emb rBorMid_emb
    hdisj_e1_mid).trans ((congrArg (restrictAssertionToZeroAncilla · rBorMid_emb) hEq).trans
      ((restrictAssertionToZeroAncilla_concat Θ₂ rExt1_emb rBorMid_emb hdisj_e1_mid).symm.trans
        (hExt2_cast Θ₂).symm)))

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer

end
