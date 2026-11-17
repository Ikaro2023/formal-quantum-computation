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

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SineWindowFlex
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ChunkedPulledMaster11
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SineWindowPrep
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Cat11MidReflBridge

/-!
# Clamped Dihedral Walk QPE, `Ray1036` Catalyst & Midpoint Closure (`DihedralWalkQPE46687`)

Consolidates the clamped QPE closure, `Ray1036` projective `11`-qubit phase gradient, SWAR
sine windows (`M = 46,687` at `2,026 T` and `2,030 T`), `FastPhasedAQFT16`, affine-folded
dihedral walk schedule, and `61` µHa `ℓ₂` midpoint DF-THC perturbation certificates.

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564–4570 (1996), DOI: 10.1103/PhysRevA.54.4564.
- R. Babbush *et al.*, *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- D. W. Berry *et al.*, *Quantum* **3**, 208 (2019), DOI: 10.22331/q-2019-12-02-208.
- J. Lee *et al.*, *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
- J. J. Goings *et al.*, *Proc. Natl. Acad. Sci. U.S.A.* **119**(38), e2203533119 (2022),
  DOI: 10.1073/pnas.2203533119.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

scoped instance (priority := 1000000) instNeZeroTwoPowP450Compact (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

namespace DihedralWalkQPE

namespace SineWindowFlexM

open Operator QProg Matrix Real
open scoped Matrix Matrix.Norms.L2Operator BigOperators

/-! ## Section 1: Pure-`ℕ` Arbitrary-`bWin` Base-Angle, `RzBundleSC`, Grover & Tree Verifiers -/

/-- Base-angle ulp tolerance `5 * 10^6` (`5 * 10^-18` at `scale24 = 10^24`). -/
def e0SC : ℕ := 5000000

/-- Pure-`ℕ` base-angle certificate check for `x₀ = π / (2 * L)` covering all `L ≥ 16,384`. -/
def checkBaseTrigNatSC (L c0Mid s0Mid : ℕ) : Bool :=
  let twoL := 2 * L
  let xLo := OuterWeights.SineWindowPrep.piLoNat / twoL
  let xHi := OuterWeights.SineWindowPrep.piHiNat / twoL + 1
  let S := OuterWeights.SineWindowPrep.scale24
  decide (16384 ≤ L ∧ c0Mid ≤ S ∧ s0Mid ≤ S ∧ e0SC ≤ c0Mid ∧ e0SC ≤ s0Mid ∧
    xHi * 10000 ≤ S ∧
    2 * S * (c0Mid - e0SC) + xHi * xHi ≤ 2 * S * S ∧
    2 * S * S + 8340000 * S ≤ 2 * S * (c0Mid + e0SC) + xLo * xLo ∧
    6 * S * S * (s0Mid - e0SC) + xHi * xHi * xHi ≤ 6 * S * S * xLo ∧
    6 * S * S * (xHi + 84) ≤ 6 * S * S * (s0Mid + e0SC) + xLo * xLo * xLo)

theorem checkBaseTrigNatSC_valid {L c0Mid s0Mid : ℕ}
    (h : checkBaseTrigNatSC L c0Mid s0Mid = true) :
    16384 ≤ L ∧
      (⟨.ofNat c0Mid, .ofNat s0Mid, e0SC⟩ : OuterWeights.SineWindowPrep.TrigCert).Valid
        (π / (2 * (L : ℝ))) := by
  dsimp only [checkBaseTrigNatSC] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hL, _hc0_le, _hs0_le, hc0_ge, hs0_ge, hxHi_cap,
    hcos_lo, hcos_hi, hsin_lo, hsin_hi⟩ := h
  refine ⟨hL, ?_⟩
  dsimp only [OuterWeights.SineWindowPrep.TrigCert.Valid]
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  have hS_val : S = (10 : ℝ) ^ 24 := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; norm_num
  have hS_pos : 0 < S := by rw [hS_val]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have h2L_pos_nat : 0 < 2 * L := by omega
  have h2L_pos : 0 < (2 * (L : ℝ)) := by positivity
  let xLo := OuterWeights.SineWindowPrep.piLoNat / (2 * L)
  let xHi := OuterWeights.SineWindowPrep.piHiNat / (2 * L) + 1
  let x0 : ℝ := π / (2 * (L : ℝ))
  obtain ⟨hpi_lo, hpi_hi⟩ := OuterWeights.SineWindowPrep.pi_scaled_bounds
  have hxLo_nat : xLo * (2 * L) ≤ OuterWeights.SineWindowPrep.piLoNat :=
    Nat.div_mul_le_self OuterWeights.SineWindowPrep.piLoNat (2 * L)
  have hxHi_nat : OuterWeights.SineWindowPrep.piHiNat ≤ xHi * (2 * L) := by
    have hdiv := Nat.div_add_mod OuterWeights.SineWindowPrep.piHiNat (2 * L)
    have hmod := Nat.mod_lt OuterWeights.SineWindowPrep.piHiNat h2L_pos_nat
    dsimp only [xHi]
    rw [Nat.add_one_mul, Nat.mul_comm _ (2 * L)]
    omega
  have hxLo_le : (xLo : ℝ) / S ≤ x0 := by
    have h1 : (xLo : ℝ) * (2 * (L : ℝ)) ≤ (OuterWeights.SineWindowPrep.piLoNat : ℝ) := by
      exact_mod_cast hxLo_nat
    have h2 : (xLo : ℝ) / S ≤ ((OuterWeights.SineWindowPrep.piLoNat : ℝ) / S) / (2 * (L : ℝ)) := by
      rw [div_div, div_le_div_iff₀ hS_pos (mul_pos hS_pos h2L_pos)]
      calc (xLo : ℝ) * (S * (2 * (L : ℝ)))
          = ((xLo : ℝ) * (2 * (L : ℝ))) * S := by ring
        _ ≤ (OuterWeights.SineWindowPrep.piLoNat : ℝ) * S := mul_le_mul_of_nonneg_right h1 hS_pos.le
    exact h2.trans (div_le_div_of_nonneg_right hpi_lo.le h2L_pos.le)
  have hx0_le : x0 ≤ (xHi : ℝ) / S := by
    have h1 : (OuterWeights.SineWindowPrep.piHiNat : ℝ) ≤ (xHi : ℝ) * (2 * (L : ℝ)) := by
      exact_mod_cast hxHi_nat
    have h2 : π / (2 * (L : ℝ)) ≤ ((OuterWeights.SineWindowPrep.piHiNat : ℝ) / S) / (2 * (L : ℝ)) :=
      div_le_div_of_nonneg_right hpi_hi.le h2L_pos.le
    have h3 : ((OuterWeights.SineWindowPrep.piHiNat : ℝ) / S) / (2 * (L : ℝ)) ≤ (xHi : ℝ) / S := by
      rw [div_div, div_le_div_iff₀ (mul_pos hS_pos h2L_pos) hS_pos]
      calc (OuterWeights.SineWindowPrep.piHiNat : ℝ) * S
          ≤ ((xHi : ℝ) * (2 * (L : ℝ))) * S := mul_le_mul_of_nonneg_right h1 hS_pos.le
        _ = (xHi : ℝ) * (S * (2 * (L : ℝ))) := by ring
    exact h2.trans h3
  have hxLo0 : 0 ≤ (xLo : ℝ) / S := by positivity
  have hx0_nonneg : 0 ≤ x0 := le_trans hxLo0 hxLo_le
  have hxHi_small : (xHi : ℝ) / S ≤ 1 / 10000 := by
    rw [div_le_div_iff₀ hS_pos (by norm_num)]
    have hc : ((xHi * 10000 : ℕ) : ℝ) ≤ (OuterWeights.SineWindowPrep.scale24 : ℝ) := by
      exact_mod_cast hxHi_cap
    push_cast at hc
    change (xHi : ℝ) * 10000 ≤ S at hc
    linarith
  have hx0_small : x0 ≤ 1 / 10000 := hx0_le.trans hxHi_small
  have hx0_pow4 : x0 ^ 4 / 24 ≤ 4170000 / S := by
    have hp : x0 ^ 4 ≤ (1 / 10000 : ℝ) ^ 4 := pow_le_pow_left₀ hx0_nonneg hx0_small 4
    have hnum : (1 / 10000 : ℝ) ^ 4 / 24 ≤ 4170000 / S := by rw [hS_val]; norm_num
    linarith
  have hx0_pow5 : x0 ^ 5 / 120 ≤ 84 / S := by
    have hp : x0 ^ 5 ≤ (1 / 10000 : ℝ) ^ 5 := pow_le_pow_left₀ hx0_nonneg hx0_small 5
    have hnum : (1 / 10000 : ℝ) ^ 5 / 120 ≤ 84 / S := by rw [hS_val]; norm_num
    linarith
  have hx_sq_lo : ((xLo : ℝ) / S) ^ 2 ≤ x0 ^ 2 := pow_le_pow_left₀ hxLo0 hxLo_le 2
  have hx_sq_hi : x0 ^ 2 ≤ ((xHi : ℝ) / S) ^ 2 := pow_le_pow_left₀ hx0_nonneg hx0_le 2
  have hx_cu_lo : ((xLo : ℝ) / S) ^ 3 ≤ x0 ^ 3 := pow_le_pow_left₀ hxLo0 hxLo_le 3
  have hx_cu_hi : x0 ^ 3 ≤ ((xHi : ℝ) / S) ^ 3 := pow_le_pow_left₀ hx0_nonneg hx0_le 3
  have hS3_pos : (0 : ℝ) ≤ 6 * S ^ 3 := by positivity
  have hS2_pos : (0 : ℝ) ≤ 2 * S ^ 2 := by positivity
  change |Real.cos x0 - (OuterWeights.SineWindowPrep.SInt.ofNat c0Mid).toReal / S| ≤ (e0SC : ℝ) / S
    ∧
    |Real.sin x0 - (OuterWeights.SineWindowPrep.SInt.ofNat s0Mid).toReal / S| ≤ (e0SC : ℝ) / S
  constructor
  · rw [OuterWeights.SineWindowPrep.SInt.toReal_ofNat, abs_le]
    constructor
    · have hR : 2 * S * ((c0Mid : ℝ) - (e0SC : ℝ)) + (xHi : ℝ) ^ 2 ≤ 2 * S ^ 2 := by
        have hc : ((2 * OuterWeights.SineWindowPrep.scale24 * (c0Mid - e0SC) + xHi * xHi : ℕ) : ℝ) ≤
            ((2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24 : ℕ) :
              ℝ) := by
          exact_mod_cast hcos_lo
        push_cast [Nat.cast_sub hc0_ge] at hc
        simpa [S, sq, mul_assoc] using hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS2_pos
      have hl : (2 * S * ((c0Mid : ℝ) - (e0SC : ℝ)) + (xHi : ℝ) ^ 2) / (2 * S ^ 2) =
          (c0Mid : ℝ) / S - (e0SC : ℝ) / S + ((xHi : ℝ) / S) ^ 2 / 2 := by
        field_simp [hS_ne]
      have hr : (2 * S ^ 2) / (2 * S ^ 2) = (1 : ℝ) := by field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      linarith [Real.one_sub_sq_div_two_le_cos (x := x0)]
    · have hR : 2 * S ^ 2 + 8340000 * S ≤
          2 * S * ((c0Mid : ℝ) + (e0SC : ℝ)) + (xLo : ℝ) ^ 2 := by
        have hc : ((2 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24 +
              8340000 * OuterWeights.SineWindowPrep.scale24 : ℕ) : ℝ) ≤
            ((2 * OuterWeights.SineWindowPrep.scale24 * (c0Mid + e0SC) + xLo * xLo : ℕ) : ℝ) := by
          exact_mod_cast hcos_hi
        push_cast at hc
        simpa [S, sq, mul_assoc] using hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS2_pos
      have hl : (2 * S ^ 2 + 8340000 * S) / (2 * S ^ 2) = 1 + 4170000 / S := by
        field_simp [hS_ne]; ring
      have hr : (2 * S * ((c0Mid : ℝ) + (e0SC : ℝ)) + (xLo : ℝ) ^ 2) / (2 * S ^ 2) =
          (c0Mid : ℝ) / S + (e0SC : ℝ) / S + ((xLo : ℝ) / S) ^ 2 / 2 := by
        field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      linarith [OuterWeights.SineWindowPrep.cos_le_one_sub_sq_div_two_add_fourth_div_24 hx0_nonneg]
  · rw [OuterWeights.SineWindowPrep.SInt.toReal_ofNat, abs_le]
    constructor
    · have hR : 6 * S ^ 2 * ((s0Mid : ℝ) - (e0SC : ℝ)) + (xHi : ℝ) ^ 3 ≤
          6 * S ^ 2 * (xLo : ℝ) := by
        have hc : ((6 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24 *
          (s0Mid - e0SC) +
              xHi * xHi * xHi : ℕ) : ℝ) ≤
            ((6 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24 *
              xLo : ℕ) : ℝ) := by
          exact_mod_cast hsin_lo
        push_cast [Nat.cast_sub hs0_ge] at hc
        simpa [sq, pow_three, mul_assoc] using hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS3_pos
      have hl : (6 * S ^ 2 * ((s0Mid : ℝ) - (e0SC : ℝ)) + (xHi : ℝ) ^ 3) / (6 * S ^ 3) =
          (s0Mid : ℝ) / S - (e0SC : ℝ) / S + ((xHi : ℝ) / S) ^ 3 / 6 := by
        field_simp [hS_ne]
      have hr : (6 * S ^ 2 * (xLo : ℝ)) / (6 * S ^ 3) = (xLo : ℝ) / S := by
        field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      linarith [Real.sin_ge_sub_cube hx0_nonneg]
    · have hR : 6 * S ^ 2 * ((xHi : ℝ) + 84) ≤
          6 * S ^ 2 * ((s0Mid : ℝ) + (e0SC : ℝ)) + (xLo : ℝ) ^ 3 := by
        have hc : ((6 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24 *
          (xHi + 84) :
              ℕ) : ℝ) ≤
            ((6 * OuterWeights.SineWindowPrep.scale24 * OuterWeights.SineWindowPrep.scale24 *
              (s0Mid + e0SC) +
              xLo * xLo * xLo : ℕ) : ℝ) := by
          exact_mod_cast hsin_hi
        push_cast at hc
        simpa [sq, pow_three, mul_assoc] using hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS3_pos
      have hl : (6 * S ^ 2 * ((xHi : ℝ) + 84)) / (6 * S ^ 3) = (xHi : ℝ) / S + 84 / S := by
        field_simp [hS_ne]
      have hr : (6 * S ^ 2 * ((s0Mid : ℝ) + (e0SC : ℝ)) + (xLo : ℝ) ^ 3) / (6 * S ^ 3) =
          (s0Mid : ℝ) / S + (e0SC : ℝ) / S + ((xLo : ℝ) / S) ^ 3 / 6 := by
        field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      linarith [OuterWeights.SineWindowPrep.sin_le_sub_cube_add_fifth_div_120 hx0_nonneg]

end SineWindowFlexM

namespace BlockReflection

open Operator QProg Matrix Real HermitianMat
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open TopIntegrationBridge
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: `O(log m)` Binary-Tree Iteration `iterBinDyn` & Arithmetic Helpers -/

/-- `O(log m)` DAG-shared binary-tree sequential repetition of a `DynamicCircuit`. -/
def iterBinDyn {Var : Type} {N : ℕ} (m : ℕ) (P : DynamicCircuit Var N) : DynamicCircuit Var N :=
  if _ : m = 0 then .identity
  else if _ : m = 1 then P
  else
    let q := iterBinDyn (m / 2) P
    if m % 2 = 0 then .seq q q else .seq q (.seq q P)
termination_by m
decreasing_by omega

@[simp]
theorem count_iterBinDyn {Var : Type} {N k : ℕ} (m : ℕ) (P : DynamicCircuit Var N)
    (g : PrimitiveGate k) : (iterBinDyn m P).count g = m * P.count g := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    unfold iterBinDyn
    split_ifs with h0 h1 heven
    · subst h0; simp
    · subst h1; simp
    · simp only [DynamicCircuit.count, ih (m / 2) (by omega)]
      have hm : m / 2 + m / 2 = m := by omega
      rw [← Nat.add_mul, hm]
    · simp only [DynamicCircuit.count, ih (m / 2) (by omega)]
      have hm : m / 2 + (m / 2 + 1) = m := by omega
      calc (m / 2) * P.count g + ((m / 2) * P.count g + P.count g)
          = (m / 2 + (m / 2 + 1)) * P.count g := by ring
        _ = m * P.count g := by rw [hm]

/-- `CleanRealizes` for `iterBinDyn m P` realizing `U ^ m` in `O(log m)` recursion depth. -/
theorem cleanRealizes_iterBinDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hP : XMeasCircuit.CleanRealizes v rAct rScr U P) (m : ℕ) :
    XMeasCircuit.CleanRealizes v rAct rScr (U ^ m) (iterBinDyn m P) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    unfold iterBinDyn
    split_ifs with h0 h1 heven
    · subst h0
      rw [_root_.pow_zero]
      exact XMeasCircuit.CleanRealizes.identity v rAct rScr
    · subst h1
      simpa [_root_.pow_one] using hP
    · have hq := ih (m / 2) (by omega)
      have hm : m / 2 + m / 2 = m := by omega
      refine (hq.seq hq).congrUnitary ?_
      congr 2
      rw [← pow_add, hm]
    · have hq := ih (m / 2) (by omega)
      have hm : (m / 2 + m / 2) + 1 = m := by omega
      refine (hq.seq (hq.seq hP)).congrUnitary ?_
      congr 2
      rw [mul_assoc, ← pow_add, ← pow_succ', hm]

section ClassicalAdderAndAffineFold

open Comparators

/-- Exact `T`-gate count of `ctrlAddConstModDyn` on a `w`-qubit target with constant `C`. -/
def ctrlAddConstModTCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | w' + 1, C =>
    if C % 2 = 0 then ctrlAddConstModTCount w' (C / 2)
    else 4 * w'

@[simp]
private theorem bitNat_zero : bitNat 0 = 0 := rfl

@[simp]
private theorem bitNat_one : bitNat 1 = 1 := rfl

private theorem count_cnot_toff {N : ℕ} (c t : Wire N) (h : c ≠ t) :
    (Circuit.CNOT c t h).count .TOFF = 0 := by
  simp [Circuit.CNOT]

private theorem count_cnot_t {N : ℕ} (c t : Wire N) (h : c ≠ t) :
    (Circuit.CNOT c t h).count .T = 0 := by
  simp [Circuit.CNOT]

/-- Cuccaro-style `andSandwich` 1-control ripple-carry modular constant adder on `m' + 1` target
wires with incoming carry wire `wCin`, realizing
`|ctrl, cin, z⟩ ↦ |ctrl, cin, (z + cin + ctrl * K) mod 2 ^ (m' + 1)⟩` in `4 * m'` `T` gates and
`0` `TOFF` gates using `m'` clean scratch wires. -/
def ctrlAddCarryModDyn {Var : Type} {N : ℕ} (v : Var) (wCtrl wCin : Wire N) :
    {m' : ℕ} → (rTgt : QRegister (m' + 1) N) → (K : ℕ) → (rScr : QRegister m' N) →
    (hCC : wCtrl ≠ wCin) →
    (hCT : ∀ i, wCtrl ≠ rTgt i) →
    (hCinT : ∀ i, wCin ≠ rTgt i) →
    (hCS : ∀ j, wCtrl ≠ rScr j) →
    (hCinS : ∀ j, wCin ≠ rScr j) →
    (hTS : rTgt.DisjointWires rScr) →
    DynamicCircuit Var N
  | 0, rTgt, K, _, _, hCT, hCinT, _, _, _ =>
    let w0 := rTgt ⟨0, by omega⟩
    if K % 2 = 0 then
      .circuit (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩))
    else
      .seq (.circuit (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩)))
        (.circuit (Circuit.CNOT wCtrl w0 (hCT ⟨0, by omega⟩)))
  | d + 1, rTgt, K, rScr, hCC, hCT, hCinT, hCS, hCinS, hTS =>
    let w0 := rTgt ⟨0, by omega⟩
    let rTail := rTgt.slice 1 (d + 1) (by omega)
    let wAnc := rScr 0
    let rScrTail := rScr.slice 1 d (by omega)
    have hCAnc : wCtrl ≠ wAnc := hCS 0
    have hCinAnc : wCin ≠ wAnc := hCinS 0
    have h0Anc : w0 ≠ wAnc := hTS.ne ⟨0, by omega⟩ 0
    have h0Ctrl : w0 ≠ wCtrl := (hCT ⟨0, by omega⟩).symm
    have hAncTail : ∀ i, wAnc ≠ rTail i := fun i ↦ (hTS.ne _ 0).symm
    have hAncScrTail : ∀ j, wAnc ≠ rScrTail j := fun j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      change 0 = 1 + j.val at hv
      omega
    have hTailScr : rTail.DisjointWires rScrTail :=
      QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS)
    let recCall := ctrlAddCarryModDyn v wCtrl wAnc rTail (K / 2) rScrTail
      hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr
    if K % 2 = 0 then
      .seq (andSandwich v wCin w0 wAnc (hCinT ⟨0, by omega⟩) hCinAnc h0Anc recCall)
        (.circuit (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩)))
    else
      .seq (.circuit (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩)))
        (.seq (.circuit (Circuit.CNOT wCin wCtrl hCC.symm))
          (.seq
            (andSandwich v w0 wCtrl wAnc h0Ctrl h0Anc hCAnc
              (.seq (.circuit (Circuit.CNOT wCin wCtrl hCC.symm))
                (.seq (.circuit (Circuit.CNOT wCin wAnc hCinAnc))
                  (.seq recCall
                    (.seq (.circuit (Circuit.CNOT wCin wAnc hCinAnc))
                      (.circuit (Circuit.CNOT wCin wCtrl hCC.symm)))))))
            (.seq (.circuit (Circuit.CNOT wCin wCtrl hCC.symm))
              (.circuit (Circuit.CNOT wCtrl w0 (hCT ⟨0, by omega⟩))))))

@[simp]
theorem count_ctrlAddCarryModDyn_toff {Var : Type} {N m' : ℕ} (v : Var)
    (wCtrl wCin : Wire N) (rTgt : QRegister (m' + 1) N) (K : ℕ) (rScr : QRegister m' N)
    (hCC : wCtrl ≠ wCin) (hCT : ∀ i, wCtrl ≠ rTgt i) (hCinT : ∀ i, wCin ≠ rTgt i)
    (hCS : ∀ j, wCtrl ≠ rScr j) (hCinS : ∀ j, wCin ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    (ctrlAddCarryModDyn v wCtrl wCin rTgt K rScr hCC hCT hCinT hCS hCinS hTS).count .TOFF = 0 := by
  induction m' generalizing wCin K with
  | zero =>
    unfold ctrlAddCarryModDyn
    dsimp only
    split_ifs <;> simp
  | succ d ih =>
    unfold ctrlAddCarryModDyn
    dsimp only
    have hrec := ih (rScr 0) (rTgt.slice 1 (d + 1) (by omega)) (K / 2)
      (rScr.slice 1 d (by omega)) (hCS 0) (fun i ↦ hCT _)
      (fun i ↦ (hTS.ne _ 0).symm) (fun j ↦ hCS _)
      (fun j h ↦ by
        have hv := congrArg Fin.val (rScr.wires.injective h)
        change 0 = 1 + j.val at hv; omega)
      (QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS))
    split_ifs <;> simp [hrec]

@[simp]
theorem count_ctrlAddCarryModDyn_t {Var : Type} {N m' : ℕ} (v : Var)
    (wCtrl wCin : Wire N) (rTgt : QRegister (m' + 1) N) (K : ℕ) (rScr : QRegister m' N)
    (hCC : wCtrl ≠ wCin) (hCT : ∀ i, wCtrl ≠ rTgt i) (hCinT : ∀ i, wCin ≠ rTgt i)
    (hCS : ∀ j, wCtrl ≠ rScr j) (hCinS : ∀ j, wCin ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    (ctrlAddCarryModDyn v wCtrl wCin rTgt K rScr hCC hCT hCinT hCS hCinS hTS).count .T =
      4 * m' := by
  induction m' generalizing wCin K with
  | zero =>
    unfold ctrlAddCarryModDyn
    dsimp only
    split_ifs <;> simp
  | succ d ih =>
    unfold ctrlAddCarryModDyn
    dsimp only
    have hrec := ih (rScr 0) (rTgt.slice 1 (d + 1) (by omega)) (K / 2)
      (rScr.slice 1 d (by omega)) (hCS 0) (fun i ↦ hCT _)
      (fun i ↦ (hTS.ne _ 0).symm) (fun j ↦ hCS _)
      (fun j h ↦ by
        have hv := congrArg Fin.val (rScr.wires.injective h)
        change 0 = 1 + j.val at hv; omega)
      (QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS))
    split_ifs <;>
      (simp only [DynamicCircuit.count, count_andSandwich_t, count_cnot_t, hrec]
       omega)

/-- Single-wire-controlled modular constant adder `|ctrl, z⟩ ↦ |ctrl, (z + ctrl * C) mod 2 ^ w⟩`
skipping trailing zero bits of `C` (`ctrlAddConstModTCount w C ≤ 4 * (w - 1)` `T` gates, `0`
`TOFF` gates, `w - 1` clean scratch wires). -/
def ctrlAddConstModDyn {Var : Type} {N : ℕ} (v : Var) (wCtrl : Wire N) :
    {w : ℕ} → (rTgt : QRegister w N) → (C : ℕ) → (rScr : QRegister (w - 1) N) →
    (hCT : ∀ i, wCtrl ≠ rTgt i) →
    (hCS : ∀ j, wCtrl ≠ rScr j) →
    (hTS : rTgt.DisjointWires rScr) →
    DynamicCircuit Var N
  | 0, _, _, _, _, _, _ => .identity
  | w' + 1, rTgt, C, rScr, hCT, hCS, hTS =>
    if C % 2 = 0 then
      ctrlAddConstModDyn v wCtrl (rTgt.slice 1 w' (by omega)) (C / 2)
        (rScr.slice 0 (w' - 1) (by omega))
        (fun i ↦ hCT _) (fun j ↦ hCS _)
        (QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS))
    else
      match w', rTgt, rScr, hCT, hCS, hTS with
      | 0, rTgt, _, hCT, _, _ =>
        .circuit (Circuit.CNOT wCtrl (rTgt ⟨0, by omega⟩) (hCT ⟨0, by omega⟩))
      | d + 1, rTgt, rScr, hCT, hCS, hTS =>
        let w0 := rTgt ⟨0, by omega⟩
        let rTail := rTgt.slice 1 (d + 1) (by omega)
        let wAnc := rScr ⟨0, by omega⟩
        let rScrTail := rScr.slice 1 d (by omega)
        have hCAnc : wCtrl ≠ wAnc := hCS ⟨0, by omega⟩
        have h0Anc : w0 ≠ wAnc := hTS.ne ⟨0, by omega⟩ ⟨0, by omega⟩
        have hAncTail : ∀ i, wAnc ≠ rTail i := fun i ↦ (hTS.ne _ ⟨0, by omega⟩).symm
        have hAncScrTail : ∀ j, wAnc ≠ rScrTail j := fun j h ↦ by
          have hv := congrArg Fin.val (rScr.wires.injective h)
          change 0 = 1 + j.val at hv
          omega
        have hTailScr : rTail.DisjointWires rScrTail :=
          QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS)
        .seq
          (andSandwich v wCtrl w0 wAnc (hCT ⟨0, by omega⟩) hCAnc h0Anc
            (ctrlAddCarryModDyn v wCtrl wAnc rTail (C / 2) rScrTail
              hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr))
          (.circuit (Circuit.CNOT wCtrl w0 (hCT ⟨0, by omega⟩)))

@[simp]
theorem count_ctrlAddConstModDyn_toff {Var : Type} {N w : ℕ} (v : Var)
    (wCtrl : Wire N) (rTgt : QRegister w N) (C : ℕ) (rScr : QRegister (w - 1) N)
    (hCT : ∀ i, wCtrl ≠ rTgt i) (hCS : ∀ j, wCtrl ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    (ctrlAddConstModDyn v wCtrl rTgt C rScr hCT hCS hTS).count .TOFF = 0 := by
  induction w generalizing C with
  | zero => rfl
  | succ w' ih =>
    unfold ctrlAddConstModDyn
    split_ifs
    · exact ih _ (C / 2) _ _ _ _
    · rcases w' with _ | d
      · simp
      · have hc := count_ctrlAddCarryModDyn_toff v wCtrl (rScr ⟨0, by omega⟩)
          (rTgt.slice 1 (d + 1) (by omega)) (C / 2) (rScr.slice 1 d (by omega))
          (hCS ⟨0, by omega⟩) (fun i ↦ hCT _) (fun i ↦ (hTS.ne _ ⟨0, by omega⟩).symm)
          (fun j ↦ hCS _)
          (fun j h ↦ by
            have hv := congrArg Fin.val (rScr.wires.injective h)
            change 0 = 1 + j.val at hv; omega)
          (QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS))
        dsimp only
        simp only [DynamicCircuit.count, count_andSandwich_toff, count_cnot_toff, hc]

@[simp]
theorem count_ctrlAddConstModDyn_t {Var : Type} {N w : ℕ} (v : Var)
    (wCtrl : Wire N) (rTgt : QRegister w N) (C : ℕ) (rScr : QRegister (w - 1) N)
    (hCT : ∀ i, wCtrl ≠ rTgt i) (hCS : ∀ j, wCtrl ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    (ctrlAddConstModDyn v wCtrl rTgt C rScr hCT hCS hTS).count .T =
      ctrlAddConstModTCount w C := by
  induction w generalizing C with
  | zero => rfl
  | succ w' ih =>
    unfold ctrlAddConstModDyn ctrlAddConstModTCount
    split_ifs with heven
    · exact ih _ (C / 2) _ _ _ _
    · rcases w' with _ | d
      · simp
      · have hc := count_ctrlAddCarryModDyn_t v wCtrl (rScr ⟨0, by omega⟩)
          (rTgt.slice 1 (d + 1) (by omega)) (C / 2) (rScr.slice 1 d (by omega))
          (hCS ⟨0, by omega⟩) (fun i ↦ hCT _) (fun i ↦ (hTS.ne _ ⟨0, by omega⟩).symm)
          (fun j ↦ hCS _)
          (fun j h ↦ by
            have hv := congrArg Fin.val (rScr.wires.injective h)
            change 0 = 1 + j.val at hv; omega)
          (QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS))
        dsimp only
        simp only [DynamicCircuit.count, count_andSandwich_t, count_cnot_t, hc]
        omega

/-- Whole-system permutation unitary induced by a bit-assignment permutation `σ`. -/
private noncomputable def bitPermUnitary {N : ℕ} (σ : Equiv.Perm (BitAssignment N)) :
    Unitary (2 ^ N) :=
  permutationUnitary ((basisBits N).trans (σ.trans (basisBits N).symm))

private theorem bitPermUnitary_mulVec_ket {N : ℕ} (σ : Equiv.Perm (BitAssignment N))
    (β : BitAssignment N) :
    (bitPermUnitary σ).1.mulVec (ket β) = ket (σ β) := by
  have hwhole := (QRegister.whole_embedUnitary (bitPermUnitary σ)).symm
  rw [hwhole, bitPermUnitary, embedUnitary_permutationUnitary_mulVec_ket]
  have hwrite (δ : BitAssignment N) : writeReg β (QRegister.whole N) δ = δ := by
    funext p; exact writeReg_apply_reg β (QRegister.whole N) δ p
  rw [hwrite]
  simp [localIdx]

private theorem bitPermUnitary_comm_zeroProjOn {N : ℕ} (σ : Equiv.Perm (BitAssignment N))
    (S : Finset (Wire N)) (hpres : ∀ β, ∀ q ∈ S, σ β q = β q) :
    (bitPermUnitary σ).1 * zeroProjOn S = zeroProjOn S * (bitPermUnitary σ).1 := by
  apply matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket,
    bitPermUnitary_mulVec_ket, zeroProjOn_mulVec_ket]
  have hiff : (∀ q ∈ S, σ β q = 0) ↔ (∀ q ∈ S, β q = 0) :=
    forall₂_congr fun q hq ↦ by rw [hpres β q hq]
  by_cases hS : ∀ q ∈ S, β q = 0
  · rw [ite_eq_left hS, bitPermUnitary_mulVec_ket, ite_eq_left (hiff.mpr hS)]
  · rw [ite_eq_right hS, Matrix.mulVec_zero, ite_eq_right (mt hiff.mp hS)]

private theorem writeReg_idem {N m : ℕ} (β : BitAssignment N) (r : QRegister m N)
    (γ₁ γ₂ : BitAssignment m) :
    writeReg (writeReg β r γ₁) r γ₂ = writeReg β r γ₂ := by
  funext q
  by_cases hq : q ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hq
    simp
  · rw [writeReg_apply_of_not_mem _ _ _ _ hq, writeReg_apply_of_not_mem _ _ _ _ hq,
      writeReg_apply_of_not_mem _ _ _ _ hq]

private theorem writeReg_self {N m : ℕ} (β : BitAssignment N) (r : QRegister m N) :
    writeReg β r (basisBits m (localIdx r β)) = β := by
  funext q
  by_cases hq : q ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hq
    rw [writeReg_apply_reg, basisBits_basisBitsEquiv_symm]
  · exact writeReg_apply_of_not_mem _ _ _ _ hq

private theorem regVal_writeReg_basisBits {N m : ℕ} (β : BitAssignment N) (r : QRegister m N)
    (x : Fin (2 ^ m)) :
    regVal r (writeReg β r (basisBits m x)) = x.val := by
  have hloc : localIdx r (writeReg β r (basisBits m x)) = x := by
    unfold localIdx
    simp
  exact congrArg Fin.val hloc

private theorem regVal_update_of_not_mem {N m : ℕ} (r : QRegister m N) (β : BitAssignment N)
    (q : Wire N) (hq : ∀ i, q ≠ r i) (val : ZMod 2) :
    regVal r (Function.update β q val) = regVal r β := by
  refine congrArg Fin.val ?_
  unfold localIdx
  congr 1; funext i
  rw [Function.update_of_ne (fun h ↦ hq i h.symm)]

/-- Reversible bit-assignment permutation adding `delta β` modulo `2 ^ m` into `rTgt` whenever
`delta` does not depend on `rTgt`. -/
private noncomputable def regAddPerm {N m : ℕ} (rTgt : QRegister m N)
    (delta : BitAssignment N → ℕ)
    (hdelta : ∀ β γ, delta (writeReg β rTgt γ) = delta β) : Equiv.Perm (BitAssignment N) where
  toFun β := writeReg β rTgt
    (basisBits m ⟨(regVal rTgt β + delta β) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)
  invFun β := writeReg β rTgt
    (basisBits m
      ⟨(regVal rTgt β + (2 ^ m - delta β % 2 ^ m)) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)
  left_inv β := by
    have hd := hdelta β
      (basisBits m ⟨(regVal rTgt β + delta β) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)
    dsimp only
    rw [writeReg_idem]
    conv_rhs => rw [← writeReg_self β rTgt]
    congr 2
    apply Fin.ext
    dsimp only
    rw [regVal_writeReg_basisBits, hd]
    have hz : regVal rTgt β < 2 ^ m := regVal_lt rTgt β
    have hm : delta β % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
    have h1 :
        ((regVal rTgt β + delta β) % 2 ^ m + (2 ^ m - delta β % 2 ^ m)) % 2 ^ m =
          (regVal rTgt β + (delta β % 2 ^ m + (2 ^ m - delta β % 2 ^ m))) % 2 ^ m := by
      rw [Nat.mod_add_mod]
      have hdecomp : regVal rTgt β + delta β + (2 ^ m - delta β % 2 ^ m) =
          (regVal rTgt β + (delta β % 2 ^ m + (2 ^ m - delta β % 2 ^ m))) +
            (delta β / 2 ^ m) * 2 ^ m := by
        calc regVal rTgt β + delta β + (2 ^ m - delta β % 2 ^ m)
          _ = regVal rTgt β + (delta β % 2 ^ m + 2 ^ m * (delta β / 2 ^ m)) +
                (2 ^ m - delta β % 2 ^ m) := by
              congr 2; exact (Nat.mod_add_div (delta β) (2 ^ m)).symm
          _ = (regVal rTgt β + (delta β % 2 ^ m + (2 ^ m - delta β % 2 ^ m))) +
                (delta β / 2 ^ m) * 2 ^ m := by ring
      rw [hdecomp, Nat.add_mul_mod_self_right]
    have h2 : delta β % 2 ^ m + (2 ^ m - delta β % 2 ^ m) = 2 ^ m := by omega
    rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hz]
  right_inv β := by
    have hd := hdelta β
      (basisBits m
        ⟨(regVal rTgt β + (2 ^ m - delta β % 2 ^ m)) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)
    dsimp only
    rw [writeReg_idem]
    conv_rhs => rw [← writeReg_self β rTgt]
    congr 2
    apply Fin.ext
    dsimp only
    rw [regVal_writeReg_basisBits, hd]
    have hz : regVal rTgt β < 2 ^ m := regVal_lt rTgt β
    have hm : delta β % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
    have h1 :
        ((regVal rTgt β + (2 ^ m - delta β % 2 ^ m)) % 2 ^ m + delta β) % 2 ^ m =
          (regVal rTgt β + ((2 ^ m - delta β % 2 ^ m) + delta β % 2 ^ m)) % 2 ^ m := by
      rw [Nat.mod_add_mod]
      have hdecomp : regVal rTgt β + (2 ^ m - delta β % 2 ^ m) + delta β =
          (regVal rTgt β + ((2 ^ m - delta β % 2 ^ m) + delta β % 2 ^ m)) +
            (delta β / 2 ^ m) * 2 ^ m := by
        calc regVal rTgt β + (2 ^ m - delta β % 2 ^ m) + delta β
          _ = regVal rTgt β + (2 ^ m - delta β % 2 ^ m) +
                (delta β % 2 ^ m + 2 ^ m * (delta β / 2 ^ m)) := by
              congr 1; exact (Nat.mod_add_div (delta β) (2 ^ m)).symm
          _ = (regVal rTgt β + ((2 ^ m - delta β % 2 ^ m) + delta β % 2 ^ m)) +
                (delta β / 2 ^ m) * 2 ^ m := by ring
      rw [hdecomp, Nat.add_mul_mod_self_right]
    have h2 : (2 ^ m - delta β % 2 ^ m) + delta β % 2 ^ m = 2 ^ m := by omega
    rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hz]

/-- Whole-system unitary adding `delta β` modulo `2 ^ m` into `rTgt`. -/
private noncomputable def regAddUnitary {N m : ℕ} (rTgt : QRegister m N)
    (delta : BitAssignment N → ℕ)
    (hdelta : ∀ β γ, delta (writeReg β rTgt γ) = delta β) : Unitary (2 ^ N) :=
  bitPermUnitary (regAddPerm rTgt delta hdelta)

private theorem regAddUnitary_mulVec_ket {N m : ℕ} (rTgt : QRegister m N)
    (delta : BitAssignment N → ℕ)
    (hdelta : ∀ β γ, delta (writeReg β rTgt γ) = delta β) (β : BitAssignment N) :
    (regAddUnitary rTgt delta hdelta).1.mulVec (ket β) =
      ket (writeReg β rTgt
        (basisBits m ⟨(regVal rTgt β + delta β) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩)) :=
  bitPermUnitary_mulVec_ket (regAddPerm rTgt delta hdelta) β

private theorem regAddUnitary_comm_zeroProjOn {N m : ℕ} (rTgt : QRegister m N)
    (delta : BitAssignment N → ℕ)
    (hdelta : ∀ β γ, delta (writeReg β rTgt γ) = delta β)
    (S : Finset (Wire N)) (hdisj : Disjoint rTgt.image S) :
    (regAddUnitary rTgt delta hdelta).1 * zeroProjOn S =
      zeroProjOn S * (regAddUnitary rTgt delta hdelta).1 := by
  refine bitPermUnitary_comm_zeroProjOn (regAddPerm rTgt delta hdelta) S fun β q hq ↦ ?_
  exact ComparatorProofs.writeReg_apply_of_not_mem_image β rTgt _ q
    (fun hmem ↦ Finset.disjoint_left.mp hdisj hmem hq)

private theorem regVal_slice_tail {N d : ℕ} (rTgt : QRegister (d + 1) N) (β : BitAssignment N) :
    regVal (rTgt.slice 1 d (by omega)) β = regVal rTgt β / 2 := by
  have heq : (basisBits d).symm (fun j : Fin d ↦ β ((rTgt.slice 1 d (by omega)) j)) =
      ⟨regVal rTgt β / 2, Nat.div_lt_of_lt_mul (by
        have h := regVal_lt rTgt β; rw [pow_succ'] at h; exact h)⟩ := by
    apply (basisBits d).injective
    rw [basisBits_basisBitsEquiv_symm]
    funext j
    rw [basisBits_eq_div_mod]
    have hj : (rTgt.slice 1 d (by omega)) j = rTgt ⟨j.val + 1, by omega⟩ := by
      rw [QRegister.slice_apply]; exact congrArg rTgt.wires (Fin.ext (by dsimp; omega))
    have hb1 : β (rTgt ⟨j.val + 1, by omega⟩) =
        basisBits (d + 1) (localIdx rTgt β) ⟨j.val + 1, by omega⟩ :=
      (congrFun (basisBits_basisBitsEquiv_symm (fun i ↦ β (rTgt i))) ⟨j.val + 1, by omega⟩).symm
    rw [hj, hb1, basisBits_eq_div_mod]
    apply congrArg (Nat.cast : ℕ → ZMod 2)
    change regVal rTgt β / 2 ^ (j.val + 1) % 2 = (regVal rTgt β / 2) / 2 ^ j.val % 2
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
  exact congrArg Fin.val heq

private theorem regVal_cons_slice {N d : ℕ} (rTgt : QRegister (d + 1) N) (β : BitAssignment N) :
    regVal rTgt β = bitNat (β (rTgt ⟨0, by omega⟩)) + 2 * regVal (rTgt.slice 1 d (by omega)) β := by
  have h1 := (Nat.mod_add_div (regVal rTgt β) 2).symm
  have h0 := regVal_div_pow_mod_two rTgt β (by omega : 0 < d + 1)
  simp only [_root_.pow_zero, Nat.div_one] at h0
  rw [regVal_slice_tail, ← h0]
  exact h1

private theorem basisBits_bitNat_eq {k : ℕ} (x : Fin (2 ^ k)) (i : Fin k) :
    bitNat (basisBits k x i) = (x.val / 2 ^ i.val) % 2 := by
  have hb := basisBits_eq_div_mod k x i
  have hmod : (x.val / 2 ^ i.val) % 2 < 2 := Nat.mod_lt _ (by omega)
  rcases (by omega : (x.val / 2 ^ i.val) % 2 = 0 ∨ (x.val / 2 ^ i.val) % 2 = 1) with h0 | h1
  · simp [hb, h0, bitNat]
  · simp [hb, h1, bitNat]

private theorem bit_eq_of_bitNat_eq {a b : ZMod 2} (h : bitNat a = bitNat b) : a = b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp_all [bitNat]

private theorem writeReg_cons_slice_eq {N d : ℕ} (β : BitAssignment N)
    (rTgt : QRegister (d + 1) N) (b0 : ZMod 2) (yTail : Fin (2 ^ d)) :
    Function.update
        (writeReg β (rTgt.slice 1 d (by omega)) (basisBits d yTail))
        (rTgt ⟨0, by omega⟩) b0 =
      writeReg β rTgt
        (basisBits (d + 1)
          ⟨bitNat b0 + 2 * yTail.val, by
            have := bitNat_lt_two b0; have := yTail.isLt; rw [pow_succ']; omega⟩) := by
  let yFull : Fin (2 ^ (d + 1)) :=
    ⟨bitNat b0 + 2 * yTail.val, by
      have := bitNat_lt_two b0; have := yTail.isLt; rw [pow_succ']; omega⟩
  funext q
  by_cases hq : q ∈ Set.range rTgt.wires
  · obtain ⟨i, rfl⟩ := hq
    rw [writeReg_apply_reg]
    by_cases hi0 : i.val = 0
    · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hi, Function.update_self]
      apply bit_eq_of_bitNat_eq
      rw [basisBits_bitNat_eq]
      dsimp [yFull]
      simp only [Nat.div_one]
      have hb0 := bitNat_lt_two b0
      omega
    · have hne : rTgt i ≠ rTgt ⟨0, by omega⟩ :=
        rTgt.wires.injective.ne (fun h ↦ hi0 (congrArg Fin.val h))
      rw [Function.update_of_ne hne]
      let j : Fin d := ⟨i.val - 1, by omega⟩
      have hj : (rTgt.slice 1 d (by omega)) j = rTgt i := by
        rw [QRegister.slice_apply]; congr 1; ext; dsimp [j]; omega
      rw [← hj, writeReg_apply_reg]
      apply bit_eq_of_bitNat_eq
      rw [basisBits_bitNat_eq, basisBits_bitNat_eq]
      dsimp [yFull, j]
      have hb0 := bitNat_lt_two b0
      have hij : i.val = (i.val - 1) + 1 := by omega
      conv_rhs => rw [hij, pow_succ', ← Nat.div_div_eq_div_mul]
      have hdiv2 : (bitNat b0 + 2 * yTail.val) / 2 = yTail.val := by omega
      rw [hdiv2]
  · have hq0 : q ≠ rTgt ⟨0, by omega⟩ := fun h ↦ hq ⟨⟨0, by omega⟩, h.symm⟩
    have hqTail : q ∉ Set.range (rTgt.slice 1 d (by omega)).wires := by
      rintro ⟨j, rfl⟩
      exact hq ⟨_, rfl⟩
    rw [Function.update_of_ne hq0, writeReg_apply_of_not_mem _ _ _ _ hqTail,
      writeReg_apply_of_not_mem _ _ _ _ hq]

private theorem add_mod_two_mul_pow {s0 cout rem M : ℕ} (hs0 : s0 < 2) :
    (s0 + 2 * (cout + rem)) % (2 * M) = s0 + 2 * ((cout + rem) % M) := by
  by_cases hM : M = 0
  · subst hM; simp
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    let q := (cout + rem) / M
    let r := (cout + rem) % M
    have hr : r < M := Nat.mod_lt _ hMpos
    have hdiv : cout + rem = r + M * q := (Nat.mod_add_div (cout + rem) M).symm
    have hlhs : s0 + 2 * (cout + rem) = (s0 + 2 * r) + (2 * M) * q := by rw [hdiv]; ring
    rw [hlhs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem cleanRealizesWires_ctrlAddCarryModDyn
    {Var : Type} [Fintype Var] [DecidableEq Var] {N m' : ℕ} (v : Var)
    (wCtrl wCin : Wire N) (rTgt : QRegister (m' + 1) N) (K : ℕ) (rScr : QRegister m' N)
    (hCC : wCtrl ≠ wCin) (hCT : ∀ i, wCtrl ≠ rTgt i) (hCinT : ∀ i, wCin ≠ rTgt i)
    (hCS : ∀ j, wCtrl ≠ rScr j) (hCinS : ∀ j, wCin ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    let hdelta : ∀ β γ,
        bitNat (writeReg β rTgt γ wCin) + bitNat (writeReg β rTgt γ wCtrl) * K =
          bitNat (β wCin) + bitNat (β wCtrl) * K := fun β γ ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (by rintro ⟨i, hi⟩; exact hCinT i hi.symm),
        writeReg_apply_of_not_mem _ _ _ _ (by rintro ⟨i, hi⟩; exact hCT i hi.symm)]
    CleanRealizesWires v rScr.image
      (regAddUnitary rTgt (fun β ↦ bitNat (β wCin) + bitNat (β wCtrl) * K) hdelta)
      (ctrlAddCarryModDyn v wCtrl wCin rTgt K rScr hCC hCT hCinT hCS hCinS hTS) := by
  induction m' generalizing wCin K with
  | zero =>
    intro hdelta
    have himg : rScr.image = ∅ := by
      ext q; simp only [QRegister.mem_image, Finset.notMem_empty, iff_false]
      rintro ⟨j, _⟩; exact Fin.elim0 j
    rw [himg]
    let w0 := rTgt ⟨0, by omega⟩
    unfold ctrlAddCarryModDyn
    dsimp only
    split_ifs with heven
    · have hcnot := CleanRealizesWires.circuit v ∅ (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩))
        (by simp) (Finset.disjoint_empty_right _)
      refine hcnot.congr_unitary ?_ (by simp)
      simp only [zeroProjOn_empty, Matrix.mul_one]
      apply matrix_ext_ket; intro β
      rw [ket_CNOT, regAddUnitary_mulVec_ket]
      have hval := regVal_cons_slice rTgt β
      have h0 : regVal (rTgt.slice 1 0 (by omega)) β = 0 := by
        have := regVal_lt (rTgt.slice 1 0 (by omega)) β; omega
      rw [h0, mul_zero, add_zero] at hval
      have hupd := writeReg_cons_slice_eq β rTgt (β w0 + β wCin) 0
      have hslice0 : writeReg β (rTgt.slice 1 0 (by omega)) (basisBits 0 0) = β := by
        funext q; apply writeReg_apply_of_not_mem; rintro ⟨j, _⟩; exact Fin.elim0 j
      rw [hslice0] at hupd
      rw [hupd]; congr 3; apply Fin.ext
      dsimp only [Fin.val_zero, mul_zero, add_zero]
      dsimp only [w0] at *
      have hbit_add : ∀ a b : ZMod 2, bitNat (a + b) = (bitNat a + bitNat b) % 2 := by
        intro a b
        rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide
      change bitNat (β (rTgt ⟨0, by omega⟩) + β wCin) =
        (regVal rTgt β + (bitNat (β wCin) + bitNat (β wCtrl) * K)) % 2
      rw [hval, hbit_add]
      rcases bit_cases (β wCtrl) with hbk | hbk
      · rw [hbk, bitNat_zero, zero_mul]; omega
      · rw [hbk, bitNat_one, one_mul]; omega
    · have hc1 := CleanRealizesWires.circuit v ∅ (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩))
        (by simp) (Finset.disjoint_empty_right _)
      have hc2 := CleanRealizesWires.circuit v ∅ (Circuit.CNOT wCtrl w0 (hCT ⟨0, by omega⟩))
        (by simp) (Finset.disjoint_empty_right _)
      refine (hc1.seq hc2).congr_unitary ?_ (by simp)
      simp only [zeroProjOn_empty, Matrix.mul_one]
      apply matrix_ext_ket; intro β
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_CNOT]
      rw [Function.update_of_ne (hCT ⟨0, by omega⟩), Function.update_self, Function.update_idem,
        regAddUnitary_mulVec_ket]
      have hval := regVal_cons_slice rTgt β
      have h0 : regVal (rTgt.slice 1 0 (by omega)) β = 0 := by
        have := regVal_lt (rTgt.slice 1 0 (by omega)) β; omega
      rw [h0, mul_zero, add_zero] at hval
      have hupd := writeReg_cons_slice_eq β rTgt (β w0 + β wCin + β wCtrl) 0
      have hslice0 : writeReg β (rTgt.slice 1 0 (by omega)) (basisBits 0 0) = β := by
        funext q; apply writeReg_apply_of_not_mem; rintro ⟨j, _⟩; exact Fin.elim0 j
      rw [hslice0] at hupd
      rw [hupd]; congr 3; apply Fin.ext
      dsimp only [Fin.val_zero, mul_zero, add_zero]
      dsimp only [w0] at *
      have hbit_add : ∀ a b : ZMod 2, bitNat (a + b) = (bitNat a + bitNat b) % 2 := by
        intro a b
        rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide
      change bitNat (β (rTgt ⟨0, by omega⟩) + β wCin + β wCtrl) =
        (regVal rTgt β + (bitNat (β wCin) + bitNat (β wCtrl) * K)) % 2
      rw [hval, hbit_add, hbit_add]
      rcases bit_cases (β wCtrl) with hbk | hbk
      · rw [hbk, bitNat_zero, zero_mul]; omega
      · rw [hbk, bitNat_one, one_mul]; omega
  | succ d ih =>
    intro hdelta
    let w0 := rTgt ⟨0, by omega⟩
    let rTail := rTgt.slice 1 (d + 1) (by omega)
    let wAnc := rScr 0
    let rScrTail := rScr.slice 1 d (by omega)
    have hCAnc : wCtrl ≠ wAnc := hCS 0
    have hCinAnc : wCin ≠ wAnc := hCinS 0
    have h0Anc : w0 ≠ wAnc := hTS.ne ⟨0, by omega⟩ 0
    have h0Ctrl : w0 ≠ wCtrl := (hCT ⟨0, by omega⟩).symm
    have hAncTail : ∀ i, wAnc ≠ rTail i := fun i ↦ (hTS.ne _ 0).symm
    have hAncScrTail : ∀ j, wAnc ≠ rScrTail j := fun j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      change 0 = 1 + j.val at hv; omega
    have hTailScr : rTail.DisjointWires rScrTail :=
      QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS)
    have hScrImg : insert wAnc rScrTail.image = rScr.image :=
      ReflectionProofs.insert_zero_slice_one_image rScr
    have hRec := ih wAnc rTail (K / 2) rScrTail hCAnc (fun i ↦ hCT _) hAncTail
      (fun j ↦ hCS _) hAncScrTail hTailScr
    have hwCtrlNotS : wCtrl ∉ rScrTail.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hCS _ hj.symm
    have hwCinNotS : wCin ∉ rScrTail.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hCinS _ hj.symm
    have hw0NotS : w0 ∉ rScrTail.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hTS.ne ⟨0, by omega⟩ _ hj.symm
    have hwAncNotS : wAnc ∉ rScrTail.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hAncScrTail j hj.symm
    have hwCtrlNotR : wCtrl ∉ rScr.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hCS j hj.symm
    have hwCinNotR : wCin ∉ rScr.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hCinS j hj.symm
    have hw0NotR : w0 ∉ rScr.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hTS.ne ⟨0, by omega⟩ j hj.symm
    have hTgtDisjR : Disjoint rTgt.image rScr.image := by
      rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
      obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2; exact hTS.ne i j hj.symm
    have hTailDisjS : Disjoint rTail.image rScrTail.image := by
      rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
      obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2; exact hTailScr.ne i j hj.symm
    have hTailDisjAnc : Disjoint rTail.image {wAnc} := by
      rw [Finset.disjoint_singleton_right, QRegister.mem_image]
      rintro ⟨i, hi⟩; exact hAncTail i hi.symm
    have hw0NotTail : w0 ∉ Set.range rTail.wires := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val (rTgt.wires.injective hi)
      change 1 + i.val = 0 at hv; omega
    have hwCinNotTail : wCin ∉ Set.range rTail.wires := by
      rintro ⟨i, hi⟩; exact hCinT _ hi.symm
    have hwCtrlNotTail : wCtrl ∉ Set.range rTail.wires := by
      rintro ⟨i, hi⟩; exact hCT _ hi.symm
    have hwAncNotTail : wAnc ∉ Set.range rTail.wires := by
      rintro ⟨i, hi⟩; exact hAncTail i hi.symm
    have hwAncNotTailImg : wAnc ∉ rTail.image := by
      rw [QRegister.mem_image]; rintro ⟨i, hi⟩; exact hAncTail i hi.symm
    have hwCtrlNotTailImg : wCtrl ∉ rTail.image := by
      rw [QRegister.mem_image]; rintro ⟨i, hi⟩; exact hCT _ hi.symm
    have hw0NotTailImg : w0 ∉ rTail.image := by
      rw [QRegister.mem_image]; rintro ⟨i, hi⟩; exact hw0NotTail ⟨i, hi⟩
    unfold ctrlAddCarryModDyn
    dsimp only
    split_ifs with heven
    · have hdeltaMid : ∀ β γ,
          bitNat (writeReg β rTail γ wCin * writeReg β rTail γ w0) +
              bitNat (writeReg β rTail γ wCtrl) * (K / 2) =
            bitNat (β wCin * β w0) + bitNat (β wCtrl) * (K / 2) := fun β γ ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
          writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail]
      let Wmid := regAddUnitary rTail
        (fun β ↦ bitNat (β wCin * β w0) + bitNat (β wCtrl) * (K / 2)) hdeltaMid
      have hSand : CleanRealizesWires v rScr.image Wmid
          (andSandwich v wCin w0 wAnc (hCinT ⟨0, by omega⟩) hCinAnc h0Anc
            (ctrlAddCarryModDyn v wCtrl wAnc rTail (K / 2) rScrTail
              hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr)) := by
        rw [← hScrImg]
        refine CleanRealizesWires.andSandwich wCin w0 wAnc (hCinT ⟨0, by omega⟩)
          hCinAnc h0Anc hwCinNotS hw0NotS hwAncNotS hRec ?_ ?_ ?_
        · apply matrix_ext_ket; intro β
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            singleton_basisOutcomeProjector_zero_eq, zeroProjOn_mulVec_ket]
          by_cases h0 : ∀ q ∈ ({wAnc} : Finset (Wire N)), β q = 0
          · have hanc0 : β wAnc = 0 := h0 wAnc (Finset.mem_singleton_self _)
            rw [ite_eq_left h0]
            simp only [Wmid, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_TOFF,
              regAddUnitary_mulVec_ket]
            rw [hanc0, zero_add, Function.update_self,
              Function.update_of_ne hCAnc,
              regVal_update_of_not_mem rTail β wAnc hAncTail,
              writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail,
              writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
              writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
              Function.update_self, Function.update_of_ne hCinAnc,
              Function.update_of_ne h0Anc, CharTwo.add_self_eq_zero,
              ← ComparatorProofs.update_writeReg_comm β rTail _ wAnc hwAncNotTailImg,
              Function.update_idem]
            have hanc_wr : writeReg β rTail
                (basisBits (d + 1)
                  ⟨(regVal rTail β + (bitNat (β wCin * β w0) + bitNat (β wCtrl) * (K / 2))) %
                    2 ^ (d + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
                wAnc = 0 := by
              rw [writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail, hanc0]
            rw [← hanc_wr, Function.update_eq_self]
          · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
        · rw [singleton_basisOutcomeProjector_zero_eq]
          exact regAddUnitary_comm_zeroProjOn rTail _ hdeltaMid {wAnc} hTailDisjAnc
        · exact regAddUnitary_comm_zeroProjOn rTail _ hdeltaMid rScrTail.image hTailDisjS
      have hcnot := CleanRealizesWires.circuit v rScr.image
        (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩)) (by simp)
        (by
          rw [Circuit.support_cnot, Finset.disjoint_left]
          intro q hq hqR; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact hwCinNotR hqR
          · exact hw0NotR hqR)
      refine (hSand.seq hcnot).congr_unitary ?_
        (regAddUnitary_comm_zeroProjOn rTgt _ hdelta rScr.image hTgtDisjR)
      apply congrArg (· * zeroProjOn rScr.image)
      apply matrix_ext_ket; intro β
      simp only [Wmid, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, regAddUnitary_mulVec_ket,
        ket_CNOT]
      rw [writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
        writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
        writeReg_cons_slice_eq]
      congr 3; apply Fin.ext
      dsimp only
      have hval := regVal_cons_slice rTgt β
      have hK : K = 2 * (K / 2) := by omega
      have hpow : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := pow_succ' 2 (d + 1)
      have hb0_s0 : bitNat (β w0 + β wCin) = (bitNat (β w0) + bitNat (β wCin)) % 2 := by
        rcases bit_cases (β w0) with h1 | h1 <;> rcases bit_cases (β wCin) with h2 | h2 <;>
          (rw [h1, h2]; decide)
      have hcout : bitNat (β wCin * β w0) = (bitNat (β w0) + bitNat (β wCin)) / 2 := by
        rcases bit_cases (β w0) with h1 | h1 <;> rcases bit_cases (β wCin) with h2 | h2 <;>
          (rw [h1, h2]; decide)
      have hsplit : regVal rTgt β + (bitNat (β wCin) + bitNat (β wCtrl) * K) =
          bitNat (β w0 + β wCin) + 2 * (bitNat (β wCin * β w0) +
            (regVal rTail β + bitNat (β wCtrl) * (K / 2))) := by
        dsimp only [w0, rTail] at hval hb0_s0 hcout ⊢
        rw [hval, hb0_s0, hcout]
        conv_lhs => rw [hK]
        rcases bit_cases (β wCtrl) with hk | hk
        · rw [hk, bitNat_zero, zero_mul]; omega
        · rw [hk, bitNat_one, one_mul]; omega
      rw [hpow, hsplit, add_mod_two_mul_pow (bitNat_lt_two _)]
      ring_nf
    · have hcCtrlS : CleanRealizesWires v rScrTail.image
          (Circuit.CNOT wCin wCtrl hCC.symm).eval
          (.circuit (Circuit.CNOT wCin wCtrl hCC.symm)) :=
        CleanRealizesWires.circuit v rScrTail.image (Circuit.CNOT wCin wCtrl hCC.symm)
          (by simp)
          (by
            rw [Circuit.support_cnot, Finset.disjoint_left]
            intro q hq hqS; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact hwCinNotS hqS
            · exact hwCtrlNotS hqS)
      have hcAncS : CleanRealizesWires v rScrTail.image
          (Circuit.CNOT wCin wAnc hCinAnc).eval
          (.circuit (Circuit.CNOT wCin wAnc hCinAnc)) :=
        CleanRealizesWires.circuit v rScrTail.image (Circuit.CNOT wCin wAnc hCinAnc)
          (by simp)
          (by
            rw [Circuit.support_cnot, Finset.disjoint_left]
            intro q hq hqS; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact hwCinNotS hqS
            · exact hwAncNotS hqS)
      have hInnerSeq := hcCtrlS.seq (hcAncS.seq (hRec.seq (hcAncS.seq hcCtrlS)))
      have hdeltaInner : ∀ δ γ,
          bitNat (writeReg δ rTail γ wAnc + writeReg δ rTail γ wCin) +
              bitNat (writeReg δ rTail γ wCtrl + writeReg δ rTail γ wCin) * (K / 2) =
            bitNat (δ wAnc + δ wCin) + bitNat (δ wCtrl + δ wCin) * (K / 2) := fun δ γ ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail]
      let Umid := regAddUnitary rTail
        (fun δ ↦ bitNat (δ wAnc + δ wCin) + bitNat (δ wCtrl + δ wCin) * (K / 2)) hdeltaInner
      have hInner : CleanRealizesWires v rScrTail.image Umid
          (.seq (.circuit (Circuit.CNOT wCin wCtrl hCC.symm))
            (.seq (.circuit (Circuit.CNOT wCin wAnc hCinAnc))
              (.seq
                (ctrlAddCarryModDyn v wCtrl wAnc rTail (K / 2) rScrTail
                  hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr)
                (.seq (.circuit (Circuit.CNOT wCin wAnc hCinAnc))
                  (.circuit (Circuit.CNOT wCin wCtrl hCC.symm)))))) := by
        refine hInnerSeq.congr_unitary ?_
          (regAddUnitary_comm_zeroProjOn rTail _ hdeltaInner rScrTail.image hTailDisjS)
        apply congrArg (· * zeroProjOn rScrTail.image)
        apply matrix_ext_ket; intro δ
        simp only [Umid, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_CNOT,
          regAddUnitary_mulVec_ket]
        set δ₁ := Function.update δ wCtrl (δ wCtrl + δ wCin)
        have hδ₁_anc : δ₁ wAnc = δ wAnc := by
          dsimp only [δ₁]; rw [Function.update_of_ne hCAnc.symm]
        have hδ₁_cin : δ₁ wCin = δ wCin := by
          dsimp only [δ₁]; rw [Function.update_of_ne hCC.symm]
        set δ₂ := Function.update δ₁ wAnc (δ₁ wAnc + δ₁ wCin)
        have hδ₂_anc : δ₂ wAnc = δ wAnc + δ wCin := by
          dsimp only [δ₂]; rw [Function.update_self, hδ₁_anc, hδ₁_cin]
        have hδ₂_ctrl : δ₂ wCtrl = δ wCtrl + δ wCin := by
          dsimp only [δ₂, δ₁]; rw [Function.update_of_ne hCAnc, Function.update_self]
        have hδ₂_cin : δ₂ wCin = δ wCin := by
          dsimp only [δ₂]; rw [Function.update_of_ne hCinAnc, hδ₁_cin]
        have hδ₂_reg : regVal rTail δ₂ = regVal rTail δ := by
          dsimp only [δ₂, δ₁]
          rw [regVal_update_of_not_mem rTail _ wAnc hAncTail,
            regVal_update_of_not_mem rTail _ wCtrl (fun i ↦ hCT _)]
        have hidx_eq :
            (⟨(regVal rTail δ₂ + (bitNat (δ₂ wAnc) + bitNat (δ₂ wCtrl) * (K / 2))) %
                2 ^ (d + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (d + 1))) =
              ⟨(regVal rTail δ +
                (bitNat (δ wAnc + δ wCin) + bitNat (δ wCtrl + δ wCin) * (K / 2))) %
                2 ^ (d + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
          Fin.ext (by dsimp only; rw [hδ₂_anc, hδ₂_ctrl, hδ₂_reg])
        rw [hidx_eq,
          writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
          hδ₂_anc, hδ₂_cin,
          ComparatorProofs.update_writeReg_comm δ₂ rTail _ wAnc hwAncNotTailImg]
        have hrestore_δ₁ : Function.update δ₂ wAnc (δ wAnc + δ wCin + δ wCin) = δ₁ := by
          dsimp only [δ₂]
          rw [Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero,
            ← hδ₁_anc, Function.update_eq_self]
        rw [hrestore_δ₁,
          writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
          hδ₁_cin,
          ComparatorProofs.update_writeReg_comm δ₁ rTail _ wCtrl hwCtrlNotTailImg]
        have hrestore_δ : Function.update δ₁ wCtrl (δ₁ wCtrl + δ wCin) = δ := by
          dsimp only [δ₁]
          rw [Function.update_self, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero,
            add_zero, Function.update_eq_self]
        rw [hrestore_δ]
      have hdeltaSand : ∀ δ γ,
          bitNat (writeReg δ rTail γ w0 * writeReg δ rTail γ wCtrl + writeReg δ rTail γ wCin) +
              bitNat (writeReg δ rTail γ wCtrl + writeReg δ rTail γ wCin) * (K / 2) =
            bitNat (δ w0 * δ wCtrl + δ wCin) + bitNat (δ wCtrl + δ wCin) * (K / 2) := fun δ γ ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail]
      let Wsand := regAddUnitary rTail
        (fun δ ↦ bitNat (δ w0 * δ wCtrl + δ wCin) + bitNat (δ wCtrl + δ wCin) * (K / 2))
        hdeltaSand
      have hSand : CleanRealizesWires v rScr.image Wsand
          (andSandwich v w0 wCtrl wAnc h0Ctrl h0Anc hCAnc
            (.seq (.circuit (Circuit.CNOT wCin wCtrl hCC.symm))
              (.seq (.circuit (Circuit.CNOT wCin wAnc hCinAnc))
                (.seq
                  (ctrlAddCarryModDyn v wCtrl wAnc rTail (K / 2) rScrTail
                    hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr)
                  (.seq (.circuit (Circuit.CNOT wCin wAnc hCinAnc))
                    (.circuit (Circuit.CNOT wCin wCtrl hCC.symm))))))) := by
        rw [← hScrImg]
        refine CleanRealizesWires.andSandwich w0 wCtrl wAnc h0Ctrl h0Anc hCAnc
          hw0NotS hwCtrlNotS hwAncNotS hInner ?_ ?_ ?_
        · apply matrix_ext_ket; intro δ
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            singleton_basisOutcomeProjector_zero_eq, zeroProjOn_mulVec_ket]
          by_cases h0 : ∀ q ∈ ({wAnc} : Finset (Wire N)), δ q = 0
          · have hanc0 : δ wAnc = 0 := h0 wAnc (Finset.mem_singleton_self _)
            rw [ite_eq_left h0]
            simp only [Umid, Wsand, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_TOFF,
              regAddUnitary_mulVec_ket]
            rw [hanc0, zero_add, Function.update_self,
              Function.update_of_ne hCinAnc, Function.update_of_ne hCAnc,
              regVal_update_of_not_mem rTail δ wAnc hAncTail,
              writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail,
              writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
              writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
              Function.update_self, Function.update_of_ne h0Anc,
              Function.update_of_ne hCAnc, CharTwo.add_self_eq_zero,
              ← ComparatorProofs.update_writeReg_comm δ rTail _ wAnc hwAncNotTailImg,
              Function.update_idem]
            have hanc_wr : writeReg δ rTail
                (basisBits (d + 1)
                  ⟨(regVal rTail δ +
                    (bitNat (δ w0 * δ wCtrl + δ wCin) + bitNat (δ wCtrl + δ wCin) * (K / 2))) %
                    2 ^ (d + 1), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
                wAnc = 0 := by
              rw [writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail, hanc0]
            rw [← hanc_wr, Function.update_eq_self]
          · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
        · rw [singleton_basisOutcomeProjector_zero_eq]
          exact regAddUnitary_comm_zeroProjOn rTail _ hdeltaSand {wAnc} hTailDisjAnc
        · exact regAddUnitary_comm_zeroProjOn rTail _ hdeltaSand rScrTail.image hTailDisjS
      have hcCin0R := CleanRealizesWires.circuit v rScr.image
        (Circuit.CNOT wCin w0 (hCinT ⟨0, by omega⟩)) (by simp)
        (by
          rw [Circuit.support_cnot, Finset.disjoint_left]
          intro q hq hqR; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact hwCinNotR hqR
          · exact hw0NotR hqR)
      have hcCinCtrlR := CleanRealizesWires.circuit v rScr.image
        (Circuit.CNOT wCin wCtrl hCC.symm) (by simp)
        (by
          rw [Circuit.support_cnot, Finset.disjoint_left]
          intro q hq hqR; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact hwCinNotR hqR
          · exact hwCtrlNotR hqR)
      have hcCtrl0R := CleanRealizesWires.circuit v rScr.image
        (Circuit.CNOT wCtrl w0 (hCT ⟨0, by omega⟩)) (by simp)
        (by
          rw [Circuit.support_cnot, Finset.disjoint_left]
          intro q hq hqR; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact hwCtrlNotR hqR
          · exact hw0NotR hqR)
      refine (hcCin0R.seq (hcCinCtrlR.seq (hSand.seq (hcCinCtrlR.seq hcCtrl0R)))).congr_unitary ?_
        (regAddUnitary_comm_zeroProjOn rTgt _ hdelta rScr.image hTgtDisjR)
      apply congrArg (· * zeroProjOn rScr.image)
      apply matrix_ext_ket; intro β
      simp only [Wsand, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_CNOT,
        regAddUnitary_mulVec_ket]
      have hCin0 : wCin ≠ w0 := hCinT ⟨0, by omega⟩
      set β₁ := Function.update β w0 (β w0 + β wCin)
      have hβ₁_ctrl : β₁ wCtrl = β wCtrl := by
        dsimp only [β₁]; rw [Function.update_of_ne (hCT ⟨0, by omega⟩)]
      have hβ₁_cin : β₁ wCin = β wCin := by
        dsimp only [β₁]; rw [Function.update_of_ne hCin0]
      set β₂ := Function.update β₁ wCtrl (β₁ wCtrl + β₁ wCin)
      have hβ₂_0 : β₂ w0 = β w0 + β wCin := by
        dsimp only [β₂, β₁]; rw [Function.update_of_ne h0Ctrl, Function.update_self]
      have hβ₂_ctrl : β₂ wCtrl = β wCtrl + β wCin := by
        dsimp only [β₂]; rw [Function.update_self, hβ₁_ctrl, hβ₁_cin]
      have hβ₂_cin : β₂ wCin = β wCin := by
        dsimp only [β₂]; rw [Function.update_of_ne hCC.symm, hβ₁_cin]
      have hβ₂_reg : regVal rTail β₂ = regVal rTail β := by
        dsimp only [β₂, β₁]
        rw [regVal_update_of_not_mem rTail _ wCtrl (fun i ↦ hCT _),
          regVal_update_of_not_mem rTail _ w0 (fun i h ↦ hw0NotTail ⟨i, h.symm⟩)]
      have hidx_eq :
          (⟨(regVal rTail β₂ +
              (bitNat (β₂ w0 * β₂ wCtrl + β₂ wCin) + bitNat (β₂ wCtrl + β₂ wCin) * (K / 2))) %
              2 ^ (d + 1),
            Nat.mod_lt _ (Nat.two_pow_pos (d + 1))⟩ : Fin (2 ^ (d + 1))) =
          ⟨(regVal rTail β +
              (bitNat ((β w0 + β wCin) * (β wCtrl + β wCin) + β wCin) +
                bitNat (β wCtrl) * (K / 2))) % 2 ^ (d + 1),
            Nat.mod_lt _ (Nat.two_pow_pos (d + 1))⟩ := by
        apply Fin.ext; dsimp only
        rw [hβ₂_0, hβ₂_ctrl, hβ₂_cin, hβ₂_reg, add_assoc (β wCtrl), CharTwo.add_self_eq_zero,
          add_zero]
      rw [hidx_eq,
        writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
        writeReg_apply_of_not_mem _ _ _ _ hwCinNotTail,
        hβ₂_ctrl, hβ₂_cin,
        ComparatorProofs.update_writeReg_comm β₂ rTail _ wCtrl hwCtrlNotTailImg]
      have hrestore_β₁ : Function.update β₂ wCtrl (β wCtrl + β wCin + β wCin) = β₁ := by
        dsimp only [β₂]
        rw [Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero,
          ← hβ₁_ctrl, Function.update_eq_self]
      have hβ₁_0 : β₁ w0 = β w0 + β wCin := by
        dsimp only [β₁]; rw [Function.update_self]
      rw [hrestore_β₁,
        writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
        writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
        hβ₁_0, hβ₁_ctrl]
      dsimp only [β₁]
      rw [← ComparatorProofs.update_writeReg_comm β rTail _ w0 hw0NotTailImg,
        Function.update_idem, writeReg_cons_slice_eq]
      congr 3; apply Fin.ext
      dsimp only
      have hval := regVal_cons_slice rTgt β
      have hK : K = 1 + 2 * (K / 2) := by omega
      have hpow : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := pow_succ' 2 (d + 1)
      have hb0_s0 : bitNat (β w0 + β wCin + β wCtrl) =
          (bitNat (β w0) + bitNat (β wCin) + bitNat (β wCtrl)) % 2 := by
        rcases bit_cases (β w0) with h1 | h1 <;>
          rcases bit_cases (β wCin) with h2 | h2 <;>
          rcases bit_cases (β wCtrl) with h3 | h3 <;>
          (rw [h1, h2, h3]; decide)
      have hcout : bitNat ((β w0 + β wCin) * (β wCtrl + β wCin) + β wCin) =
          (bitNat (β w0) + bitNat (β wCin) + bitNat (β wCtrl)) / 2 := by
        rcases bit_cases (β w0) with h1 | h1 <;>
          rcases bit_cases (β wCin) with h2 | h2 <;>
          rcases bit_cases (β wCtrl) with h3 | h3 <;>
          (rw [h1, h2, h3]; decide)
      have hsplit : regVal rTgt β + (bitNat (β wCin) + bitNat (β wCtrl) * K) =
          bitNat (β w0 + β wCin + β wCtrl) +
            2 * (bitNat ((β w0 + β wCin) * (β wCtrl + β wCin) + β wCin) +
              (regVal rTail β + bitNat (β wCtrl) * (K / 2))) := by
        dsimp only [w0, rTail] at hval hb0_s0 hcout ⊢
        rw [hval, hb0_s0, hcout]
        conv_lhs => rw [hK]
        rcases bit_cases (β wCtrl) with hk | hk
        · rw [hk, bitNat_zero, zero_mul]; omega
        · rw [hk, bitNat_one, one_mul]; omega
      rw [hpow, hsplit, add_mod_two_mul_pow (bitNat_lt_two _)]
      ring_nf

private theorem support_ctrlAddCarryModDyn_subset {Var : Type} {N m' : ℕ} (v : Var)
    (wCtrl wCin : Wire N) (rTgt : QRegister (m' + 1) N) (K : ℕ) (rScr : QRegister m' N)
    (hCC : wCtrl ≠ wCin) (hCT : ∀ i, wCtrl ≠ rTgt i) (hCinT : ∀ i, wCin ≠ rTgt i)
    (hCS : ∀ j, wCtrl ≠ rScr j) (hCinS : ∀ j, wCin ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    (ctrlAddCarryModDyn v wCtrl wCin rTgt K rScr hCC hCT hCinT hCS hCinS hTS).support ⊆
      {wCtrl, wCin} ∪ rTgt.image ∪ rScr.image := by
  induction m' generalizing wCin K with
  | zero =>
    unfold ctrlAddCarryModDyn
    intro q hq
    dsimp only at hq
    have hw0 : rTgt ⟨0, by omega⟩ ∈ rTgt.image :=
      (QRegister.mem_image _ _).mpr ⟨⟨0, by omega⟩, rfl⟩
    by_cases he : K % 2 = 0
    · rw [ite_eq_left he] at hq
      simp only [DynamicCircuit.support_circuit, Circuit.support_cnot, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      rcases hq with rfl | rfl <;> tauto
    · rw [ite_eq_right he] at hq
      simp only [DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Circuit.support_cnot, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      rcases hq with (rfl | rfl) | (rfl | rfl) <;> tauto
  | succ d ih =>
    unfold ctrlAddCarryModDyn
    dsimp only
    let w0 := rTgt ⟨0, by omega⟩
    let rTail := rTgt.slice 1 (d + 1) (by omega)
    let wAnc := rScr 0
    let rScrTail := rScr.slice 1 d (by omega)
    have hw0Mem : w0 ∈ rTgt.image := (QRegister.mem_image _ _).mpr ⟨⟨0, by omega⟩, rfl⟩
    have hwAncMem : wAnc ∈ rScr.image := (QRegister.mem_image _ _).mpr ⟨0, rfl⟩
    have hTailSub : rTail.image ⊆ rTgt.image := by
      intro q hq; obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hq
      exact (QRegister.mem_image _ _).mpr ⟨_, rfl⟩
    have hScrTailSub : rScrTail.image ⊆ rScr.image := by
      intro q hq; obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hq
      exact (QRegister.mem_image _ _).mpr ⟨_, rfl⟩
    have hAncScrTail : ∀ j, wAnc ≠ rScrTail j := fun j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      change 0 = 1 + j.val at hv; omega
    have hTailScr : rTail.DisjointWires rScrTail :=
      QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS)
    have hRecSub := ih wAnc rTail (K / 2) rScrTail (hCS 0) (fun i ↦ hCT _)
      (fun i ↦ (hTS.ne _ 0).symm) (fun j ↦ hCS _) hAncScrTail hTailScr
    intro q hq
    split_ifs at hq
    · simp only [DynamicCircuit.support_seq, support_andSandwich, DynamicCircuit.support_circuit,
        Circuit.support_cnot, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      rcases hq with ((rfl | rfl | rfl) | hrec) | (rfl | rfl)
      · tauto
      · exact Or.inl (Or.inr hw0Mem)
      · exact Or.inr hwAncMem
      · have hq' := hRecSub hrec
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq'
        rcases hq' with ((rfl | rfl) | h1) | h2
        · tauto
        · exact Or.inr hwAncMem
        · exact Or.inl (Or.inr (hTailSub h1))
        · exact Or.inr (hScrTailSub h2)
      · tauto
      · exact Or.inl (Or.inr hw0Mem)
    · simp only [DynamicCircuit.support_seq, support_andSandwich, DynamicCircuit.support_circuit,
        Circuit.support_cnot, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
      have hrec_mem : ∀ x,
          x ∈ (ctrlAddCarryModDyn v wCtrl wAnc rTail (K / 2) rScrTail
            (hCS 0) (fun i ↦ hCT _) (fun i ↦ (hTS.ne _ 0).symm)
            (fun j ↦ hCS _) hAncScrTail hTailScr).support →
          (x = wCtrl ∨ x = wCin) ∨ x ∈ rTgt.image ∨ x ∈ rScr.image := fun x hx ↦ by
        have hx' := hRecSub hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with ((rfl | rfl) | h1) | h2
        · tauto
        · exact Or.inr (Or.inr hwAncMem)
        · exact Or.inr (Or.inl (hTailSub h1))
        · exact Or.inr (Or.inr (hScrTailSub h2))
      rcases hq with (rfl | rfl) | (rfl | rfl) |
          (((rfl | rfl | rfl) | ((rfl | rfl) | (rfl | rfl) | hrec | (rfl | rfl) | (rfl | rfl))) |
            ((rfl | rfl) | (rfl | rfl)))
      all_goals try tauto
      · obtain h1 | h2 | h3 := hrec_mem q hrec
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h3

private theorem support_ctrlAddConstModDyn_subset {Var : Type} {N w : ℕ} (v : Var)
    (wCtrl : Wire N) (rTgt : QRegister w N) (C : ℕ) (rScr : QRegister (w - 1) N)
    (hCT : ∀ i, wCtrl ≠ rTgt i) (hCS : ∀ j, wCtrl ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    (ctrlAddConstModDyn v wCtrl rTgt C rScr hCT hCS hTS).support ⊆
      insert wCtrl rTgt.image ∪ rScr.image := by
  induction w generalizing C with
  | zero => simp [ctrlAddConstModDyn]
  | succ w' ih =>
    unfold ctrlAddConstModDyn
    split_ifs
    · refine (ih _ (C / 2) _ _ _ _).trans ?_
      intro q hq
      simp only [Finset.mem_union, Finset.mem_insert, QRegister.mem_image] at hq ⊢
      rcases hq with (rfl | ⟨i, rfl⟩) | ⟨j, rfl⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr ⟨_, rfl⟩)
      · exact Or.inr ⟨_, rfl⟩
    · rcases w' with _ | d
      · intro q hq
        simp only [DynamicCircuit.support_circuit, Circuit.support_cnot, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, QRegister.mem_image] at hq ⊢
        rcases hq with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ⟨⟨0, by omega⟩, rfl⟩)
      · intro q hq
        dsimp only at hq
        simp only [DynamicCircuit.support_seq, support_andSandwich, DynamicCircuit.support_circuit,
          Circuit.support_cnot, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq with ((rfl | rfl | rfl) | hrec) | (rfl | rfl)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ((QRegister.mem_image _ _).mpr ⟨⟨0, by omega⟩, rfl⟩))
        · exact Or.inr ((QRegister.mem_image _ _).mpr ⟨⟨0, by omega⟩, rfl⟩)
        · have hq' := support_ctrlAddCarryModDyn_subset v wCtrl (rScr ⟨0, by omega⟩)
            (rTgt.slice 1 (d + 1) (by omega)) (C / 2) (rScr.slice 1 d (by omega)) _ _ _ _ _ _ hrec
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            QRegister.mem_image] at hq' ⊢
          rcases hq' with ((rfl | rfl) | ⟨i, rfl⟩) | ⟨j, rfl⟩
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨⟨0, by omega⟩, rfl⟩
          · exact Or.inl (Or.inr ⟨_, rfl⟩)
          · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ((QRegister.mem_image _ _).mpr ⟨⟨0, by omega⟩, rfl⟩))

private theorem cleanRealizesWires_ctrlAddConstModDyn
    {Var : Type} [Fintype Var] [DecidableEq Var] {N w : ℕ} (v : Var)
    (wCtrl : Wire N) (rTgt : QRegister w N) (C : ℕ) (rScr : QRegister (w - 1) N)
    (hCT : ∀ i, wCtrl ≠ rTgt i) (hCS : ∀ j, wCtrl ≠ rScr j) (hTS : rTgt.DisjointWires rScr) :
    let hdelta : ∀ β γ,
        bitNat (writeReg β rTgt γ wCtrl) * C = bitNat (β wCtrl) * C := fun β γ ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (by rintro ⟨i, hi⟩; exact hCT i hi.symm)]
    CleanRealizesWires v rScr.image
      (regAddUnitary rTgt (fun β ↦ bitNat (β wCtrl) * C) hdelta)
      (ctrlAddConstModDyn v wCtrl rTgt C rScr hCT hCS hTS) := by
  induction w generalizing C with
  | zero =>
    intro hdelta
    have himg : rScr.image = ∅ := by
      ext q; simp only [QRegister.mem_image, Finset.notMem_empty, iff_false]
      rintro ⟨j, _⟩; exact Fin.elim0 j
    rw [himg]
    refine (CleanRealizesWires.identity v ∅).congr_unitary ?_ (by simp)
    simp only [zeroProjOn_empty, Matrix.mul_one]
    apply matrix_ext_ket; intro β
    rw [Submonoid.coe_one, Matrix.one_mulVec, regAddUnitary_mulVec_ket]
    have hslice0 : writeReg β rTgt (basisBits 0 ⟨(regVal rTgt β + bitNat (β wCtrl) * C) % 2 ^ 0,
        Nat.mod_lt _ (Nat.two_pow_pos 0)⟩) = β := by
      funext q; apply writeReg_apply_of_not_mem; rintro ⟨j, _⟩; exact Fin.elim0 j
    rw [hslice0]
  | succ w' ih =>
    intro hdelta
    have hTgtDisjR : Disjoint rTgt.image rScr.image := by
      rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
      obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2; exact hTS.ne i j hj.symm
    have hwCtrlNotR : wCtrl ∉ rScr.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hCS j hj.symm
    unfold ctrlAddConstModDyn
    split_ifs with heven
    · let rTail := rTgt.slice 1 w' (by omega)
      let rScrSub := rScr.slice 0 (w' - 1) (by omega)
      have hCT' : ∀ i, wCtrl ≠ rTail i := fun i ↦ hCT _
      have hCS' : ∀ j, wCtrl ≠ rScrSub j := fun j ↦ hCS _
      have hTS' : rTail.DisjointWires rScrSub :=
        QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS)
      have hSub := ih rTail (C / 2) rScrSub hCT' hCS' hTS'
      have hSubImg : rScrSub.image ⊆ rScr.image := by
        intro q hq; obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hq
        exact (QRegister.mem_image _ _).mpr ⟨_, rfl⟩
      have hUnion : rScrSub.image ∪ (rScr.image \ rScrSub.image) = rScr.image :=
        Finset.union_sdiff_of_subset hSubImg
      have hSuppDisj : Disjoint
          (ctrlAddConstModDyn v wCtrl rTail (C / 2) rScrSub hCT' hCS' hTS').support
          (rScr.image \ rScrSub.image) := by
        refine Finset.disjoint_of_subset_left
          (support_ctrlAddConstModDyn_subset v wCtrl rTail (C / 2) rScrSub hCT' hCS' hTS') ?_
        rw [Finset.disjoint_left]
        intro q hq hdiff
        have hqR : q ∈ rScr.image := (Finset.mem_sdiff.mp hdiff).1
        have hqNotSub : q ∉ rScrSub.image := (Finset.mem_sdiff.mp hdiff).2
        simp only [Finset.mem_union, Finset.mem_insert] at hq
        rcases hq with (rfl | hTail) | hSubM
        · exact hwCtrlNotR hqR
        · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hTail
          exact Finset.disjoint_left.mp hTgtDisjR ((QRegister.mem_image _ _).mpr ⟨_, rfl⟩) hqR
        · exact hqNotSub hSubM
      have hTailDisjDiff : Disjoint rTail.image (rScr.image \ rScrSub.image) := by
        refine Finset.disjoint_of_subset_right Finset.sdiff_subset ?_
        refine Finset.disjoint_of_subset_left ?_ hTgtDisjR
        intro q hq; obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hq
        exact (QRegister.mem_image _ _).mpr ⟨_, rfl⟩
      have hExt := hUnion ▸ hSub.extend_wires (rScr.image \ rScrSub.image) hSuppDisj
        (regAddUnitary_comm_zeroProjOn rTail _ _ _ hTailDisjDiff)
      refine hExt.congr_unitary ?_
        (regAddUnitary_comm_zeroProjOn rTgt _ hdelta rScr.image hTgtDisjR)
      apply congrArg (· * zeroProjOn rScr.image)
      apply matrix_ext_ket; intro β
      rw [regAddUnitary_mulVec_ket, regAddUnitary_mulVec_ket]
      have hw0_unch :
          writeReg β rTail
            (basisBits w' ⟨(regVal rTail β + bitNat (β wCtrl) * (C / 2)) % 2 ^ w',
              Nat.mod_lt _ (Nat.two_pow_pos w')⟩)
            (rTgt ⟨0, by omega⟩) = β (rTgt ⟨0, by omega⟩) := by
        apply writeReg_apply_of_not_mem
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val (rTgt.wires.injective hi)
        change 1 + i.val = 0 at hv; omega
      have hupd := writeReg_cons_slice_eq β rTgt (β (rTgt ⟨0, by omega⟩))
        ⟨(regVal rTail β + bitNat (β wCtrl) * (C / 2)) % 2 ^ w',
          Nat.mod_lt _ (Nat.two_pow_pos w')⟩
      have hself : Function.update
          (writeReg β rTail
            (basisBits w' ⟨(regVal rTail β + bitNat (β wCtrl) * (C / 2)) % 2 ^ w',
              Nat.mod_lt _ (Nat.two_pow_pos w')⟩))
          (rTgt ⟨0, by omega⟩) (β (rTgt ⟨0, by omega⟩)) =
          writeReg β rTail
            (basisBits w' ⟨(regVal rTail β + bitNat (β wCtrl) * (C / 2)) % 2 ^ w',
              Nat.mod_lt _ (Nat.two_pow_pos w')⟩) := by
        rw [← hw0_unch, Function.update_eq_self]
      rw [← hself, hupd]
      congr 3; apply Fin.ext
      dsimp only
      have hval := regVal_cons_slice rTgt β
      have hC : C = 2 * (C / 2) := by omega
      have hpow : 2 ^ (w' + 1) = 2 * 2 ^ w' := pow_succ' 2 w'
      have hsplit : regVal rTgt β + bitNat (β wCtrl) * C =
          bitNat (β (rTgt ⟨0, by omega⟩)) +
            2 * (0 + (regVal rTail β + bitNat (β wCtrl) * (C / 2))) := by
        dsimp only [rTail] at hval ⊢
        rw [hval]
        conv_lhs => rw [hC]
        ring
      rw [hpow, hsplit, add_mod_two_mul_pow (bitNat_lt_two _), zero_add]
    · rcases w' with _ | d
      · have himg : rScr.image = ∅ := by
          ext q; simp only [QRegister.mem_image, Finset.notMem_empty, iff_false]
          rintro ⟨j, _⟩; exact Fin.elim0 j
        rw [himg]
        have hcnot := CleanRealizesWires.circuit v ∅
          (Circuit.CNOT wCtrl (rTgt ⟨0, by omega⟩) (hCT ⟨0, by omega⟩))
          (by simp) (Finset.disjoint_empty_right _)
        refine hcnot.congr_unitary ?_ (by simp)
        simp only [zeroProjOn_empty, Matrix.mul_one]
        apply matrix_ext_ket; intro β
        rw [ket_CNOT, regAddUnitary_mulVec_ket]
        have hval := regVal_cons_slice rTgt β
        have h0 : regVal (rTgt.slice 1 0 (by omega)) β = 0 := by
          have := regVal_lt (rTgt.slice 1 0 (by omega)) β; omega
        rw [h0, mul_zero, add_zero] at hval
        have hupd := writeReg_cons_slice_eq β rTgt (β (rTgt ⟨0, by omega⟩) + β wCtrl) 0
        have hslice0 : writeReg β (rTgt.slice 1 0 (by omega)) (basisBits 0 0) = β := by
          funext q; apply writeReg_apply_of_not_mem; rintro ⟨j, _⟩; exact Fin.elim0 j
        rw [hslice0] at hupd
        rw [hupd]; congr 3; apply Fin.ext
        dsimp only [Fin.val_zero, mul_zero, add_zero]
        have hbit_add : ∀ a b : ZMod 2, bitNat (a + b) = (bitNat a + bitNat b) % 2 := by
          intro a b; rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
            decide
        change bitNat (β (rTgt ⟨0, by omega⟩) + β wCtrl) =
          (regVal rTgt β + bitNat (β wCtrl) * C) % 2
        rw [hval, hbit_add]
        rcases bit_cases (β wCtrl) with hbk | hbk
        · rw [hbk, bitNat_zero, zero_mul]
        · rw [hbk, bitNat_one, one_mul]; omega
      · dsimp only
        let w0 := rTgt ⟨0, by omega⟩
        let rTail := rTgt.slice 1 (d + 1) (by omega)
        let wAnc := rScr ⟨0, by omega⟩
        let rScrTail := rScr.slice 1 d (by omega)
        have hCAnc : wCtrl ≠ wAnc := hCS ⟨0, by omega⟩
        have h0Anc : w0 ≠ wAnc := hTS.ne ⟨0, by omega⟩ ⟨0, by omega⟩
        have hAncTail : ∀ i, wAnc ≠ rTail i := fun i ↦ (hTS.ne _ ⟨0, by omega⟩).symm
        have hAncScrTail : ∀ j, wAnc ≠ rScrTail j := fun j h ↦ by
          have hv := congrArg Fin.val (rScr.wires.injective h)
          change 0 = 1 + j.val at hv; omega
        have hTailScr : rTail.DisjointWires rScrTail :=
          QubitisedWalk.disjointWires_compose_right (QubitisedWalk.disjointWires_compose_left hTS)
        have hScrImg : insert wAnc rScrTail.image = rScr.image :=
          ReflectionProofs.insert_zero_slice_one_image rScr
        have hwCtrlNotS : wCtrl ∉ rScrTail.image := by
          rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hCS _ hj.symm
        have hw0NotS : w0 ∉ rScrTail.image := by
          rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hTS.ne ⟨0, by omega⟩ _ hj.symm
        have hwAncNotS : wAnc ∉ rScrTail.image := by
          rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hAncScrTail j hj.symm
        have hw0NotR : w0 ∉ rScr.image := by
          rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hTS.ne ⟨0, by omega⟩ j hj.symm
        have hw0NotTail : w0 ∉ Set.range rTail.wires := by
          rintro ⟨i, hi⟩
          have hv := congrArg Fin.val (rTgt.wires.injective hi)
          change 1 + i.val = 0 at hv; omega
        have hwCtrlNotTail : wCtrl ∉ Set.range rTail.wires := by
          rintro ⟨i, hi⟩; exact hCT _ hi.symm
        have hwAncNotTail : wAnc ∉ Set.range rTail.wires := by
          rintro ⟨i, hi⟩; exact hAncTail i hi.symm
        have hwAncNotTailImg : wAnc ∉ rTail.image := by
          rw [QRegister.mem_image]; rintro ⟨i, hi⟩; exact hAncTail i hi.symm
        have hTailDisjS : Disjoint rTail.image rScrTail.image := by
          rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
          obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2; exact hTailScr.ne i j hj.symm
        have hTailDisjAnc : Disjoint rTail.image {wAnc} := by
          rw [Finset.disjoint_singleton_right]; exact hwAncNotTailImg
        have hCarry := cleanRealizesWires_ctrlAddCarryModDyn v wCtrl wAnc rTail (C / 2) rScrTail
          hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr
        have hdeltaMid : ∀ β γ,
            bitNat (writeReg β rTail γ wCtrl * writeReg β rTail γ w0) +
                bitNat (writeReg β rTail γ wCtrl) * (C / 2) =
              bitNat (β wCtrl * β w0) + bitNat (β wCtrl) * (C / 2) := fun β γ ↦ by
          rw [writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
            writeReg_apply_of_not_mem _ _ _ _ hw0NotTail]
        let Wmid := regAddUnitary rTail
          (fun β ↦ bitNat (β wCtrl * β w0) + bitNat (β wCtrl) * (C / 2)) hdeltaMid
        have hSand : CleanRealizesWires v rScr.image Wmid
            (andSandwich v wCtrl w0 wAnc (hCT ⟨0, by omega⟩) hCAnc h0Anc
              (ctrlAddCarryModDyn v wCtrl wAnc rTail (C / 2) rScrTail
                hCAnc (fun i ↦ hCT _) hAncTail (fun j ↦ hCS _) hAncScrTail hTailScr)) := by
          rw [← hScrImg]
          refine CleanRealizesWires.andSandwich wCtrl w0 wAnc (hCT ⟨0, by omega⟩) hCAnc h0Anc
            hwCtrlNotS hw0NotS hwAncNotS hCarry ?_ ?_ ?_
          · apply matrix_ext_ket; intro β
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
              singleton_basisOutcomeProjector_zero_eq, zeroProjOn_mulVec_ket]
            by_cases h0 : ∀ q ∈ ({wAnc} : Finset (Wire N)), β q = 0
            · have hanc0 : β wAnc = 0 := h0 wAnc (Finset.mem_singleton_self _)
              rw [ite_eq_left h0]
              simp only [Wmid, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_TOFF,
                regAddUnitary_mulVec_ket]
              rw [hanc0, zero_add, Function.update_self, Function.update_of_ne hCAnc,
                regVal_update_of_not_mem rTail β wAnc hAncTail,
                writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail,
                writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
                writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
                Function.update_self, Function.update_of_ne hCAnc,
                Function.update_of_ne h0Anc, CharTwo.add_self_eq_zero,
                ← ComparatorProofs.update_writeReg_comm β rTail _ wAnc hwAncNotTailImg,
                Function.update_idem]
              have hanc_wr :
                  writeReg β rTail
                    (basisBits (d + 1)
                      ⟨(regVal rTail β + (bitNat (β wCtrl * β w0) + bitNat (β wCtrl) * (C / 2))) %
                        2 ^ (d + 1),
                      Nat.mod_lt _ (Nat.two_pow_pos (d + 1))⟩)
                    wAnc = 0 := by
                rw [writeReg_apply_of_not_mem _ _ _ _ hwAncNotTail, hanc0]
              rw [← hanc_wr, Function.update_eq_self]
            · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
          · rw [singleton_basisOutcomeProjector_zero_eq]
            exact regAddUnitary_comm_zeroProjOn rTail _ hdeltaMid {wAnc} hTailDisjAnc
          · exact regAddUnitary_comm_zeroProjOn rTail _ hdeltaMid rScrTail.image hTailDisjS
        have hcnot := CleanRealizesWires.circuit v rScr.image
          (Circuit.CNOT wCtrl w0 (hCT ⟨0, by omega⟩)) (by simp)
          (by
            rw [Circuit.support_cnot, Finset.disjoint_left]
            intro q hq hqR; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact hwCtrlNotR hqR
            · exact hw0NotR hqR)
        refine (hSand.seq hcnot).congr_unitary ?_
          (regAddUnitary_comm_zeroProjOn rTgt _ hdelta rScr.image hTgtDisjR)
        apply congrArg (· * zeroProjOn rScr.image)
        apply matrix_ext_ket; intro β
        simp only [Wmid, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, regAddUnitary_mulVec_ket,
          ket_CNOT]
        rw [writeReg_apply_of_not_mem _ _ _ _ hw0NotTail,
          writeReg_apply_of_not_mem _ _ _ _ hwCtrlNotTail,
          writeReg_cons_slice_eq]
        congr 3; apply Fin.ext
        dsimp only
        have hval := regVal_cons_slice rTgt β
        have hC : C = 1 + 2 * (C / 2) := by omega
        have hpow : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := pow_succ' 2 (d + 1)
        have hb0_s0 : bitNat (β w0 + β wCtrl) = (bitNat (β w0) + bitNat (β wCtrl)) % 2 := by
          rcases bit_cases (β w0) with h1 | h1 <;> rcases bit_cases (β wCtrl) with h2 | h2 <;>
            (rw [h1, h2]; decide)
        have hcout : bitNat (β wCtrl * β w0) = (bitNat (β w0) + bitNat (β wCtrl)) / 2 := by
          rcases bit_cases (β w0) with h1 | h1 <;> rcases bit_cases (β wCtrl) with h2 | h2 <;>
            (rw [h1, h2]; decide)
        have hsplit : regVal rTgt β + bitNat (β wCtrl) * C =
            bitNat (β w0 + β wCtrl) +
              2 * (bitNat (β wCtrl * β w0) + (regVal rTail β + bitNat (β wCtrl) * (C / 2))) := by
          dsimp only [w0, rTail] at hval hb0_s0 hcout ⊢
          rw [hval, hb0_s0, hcout]
          conv_lhs => rw [hC]
          rcases bit_cases (β wCtrl) with hk | hk
          · rw [hk, bitNat_zero, zero_mul]; omega
          · rw [hk, bitNat_one, one_mul]; omega
        rw [hpow, hsplit, add_mod_two_mul_pow (bitNat_lt_two _)]
        ring_nf

/-! ### Involutive Affine Clock Permutation & Dihedral Exponent Identity -/

/-- Natural-number `(w + 1)`-bit affine clock fold map leaving upper bits `≥ w + 1` unchanged:
maps `x_lo = x % 2 ^ w` to `2 ^ w - 1 - x_lo` when bit `w` is `0`, and to
`((2 ^ w - 1 - x_lo) + C) % 2 ^ w` when bit `w` is `1`. -/
def affineFoldVal (w C x : ℕ) : ℕ :=
  let x_lo := x % 2 ^ w
  let x_hi := (x / 2 ^ w) % 2
  let x_top := x / 2 ^ (w + 1)
  let y_lo := if x_hi = 0 then 2 ^ w - 1 - x_lo else ((2 ^ w - 1 - x_lo) + C) % 2 ^ w
  y_lo + 2 ^ w * x_hi + 2 ^ (w + 1) * x_top

private theorem affineFoldVal_lo_lt (w C x : ℕ) :
    (if (x / 2 ^ w) % 2 = 0 then 2 ^ w - 1 - x % 2 ^ w
      else ((2 ^ w - 1 - x % 2 ^ w) + C) % 2 ^ w) < 2 ^ w := by
  have hx := Nat.mod_lt x (Nat.two_pow_pos w)
  have hm := Nat.mod_lt ((2 ^ w - 1 - x % 2 ^ w) + C) (Nat.two_pow_pos w)
  split_ifs <;> omega

private theorem affineFoldVal_decomp (w C x : ℕ) :
    affineFoldVal w C x % 2 ^ w =
        (if (x / 2 ^ w) % 2 = 0 then 2 ^ w - 1 - x % 2 ^ w
          else ((2 ^ w - 1 - x % 2 ^ w) + C) % 2 ^ w) ∧
      (affineFoldVal w C x / 2 ^ w) % 2 = (x / 2 ^ w) % 2 ∧
      affineFoldVal w C x / 2 ^ (w + 1) = x / 2 ^ (w + 1) := by
  let y_lo := if (x / 2 ^ w) % 2 = 0 then 2 ^ w - 1 - x % 2 ^ w
    else ((2 ^ w - 1 - x % 2 ^ w) + C) % 2 ^ w
  have hy_lt : y_lo < 2 ^ w := affineFoldVal_lo_lt w C x
  have hhi_lt : (x / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by omega)
  have heq : affineFoldVal w C x = y_lo + 2 ^ w * ((x / 2 ^ w) % 2 + 2 * (x / 2 ^ (w + 1))) := by
    dsimp [affineFoldVal, y_lo]
    rw [pow_succ]
    ring
  have hmod1 : affineFoldVal w C x % 2 ^ w = y_lo := by
    rw [heq, mul_comm (2 ^ w), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy_lt]
  have hdiv1 : affineFoldVal w C x / 2 ^ w = (x / 2 ^ w) % 2 + 2 * (x / 2 ^ (w + 1)) := by
    rw [heq, mul_comm (2 ^ w), Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
      Nat.div_eq_zero_iff.mpr (Or.inr hy_lt), zero_add]
  refine ⟨hmod1, ?_, ?_⟩
  · rw [hdiv1]; omega
  · conv_lhs => rw [pow_succ, ← Nat.div_div_eq_div_mul, hdiv1]
    omega

/-- `affineFoldVal w C` is an exact involution on ALL `x : ℕ`. -/
theorem affineFoldVal_involutive (w C x : ℕ) :
    affineFoldVal w C (affineFoldVal w C x) = x := by
  obtain ⟨hlo, hhi, htop⟩ := affineFoldVal_decomp w C x
  let y := affineFoldVal w C x
  change affineFoldVal w C y = x
  unfold affineFoldVal
  dsimp only [y]
  rw [hlo, hhi, htop]
  have hx_lo : x % 2 ^ w < 2 ^ w := Nat.mod_lt x (Nat.two_pow_pos w)
  have hx_reconstruct :
      x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) + 2 ^ (w + 1) * (x / 2 ^ (w + 1)) = x := by
    have h1 := Nat.mod_add_div x (2 ^ w)
    have h2 := Nat.mod_add_div (x / 2 ^ w) 2
    have h3 : x / 2 ^ (w + 1) = (x / 2 ^ w) / 2 := by rw [pow_succ, ← Nat.div_div_eq_div_mul]
    rw [h3, pow_succ]
    calc x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) + 2 ^ w * 2 * (x / 2 ^ w / 2)
      _ = x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2 + 2 * (x / 2 ^ w / 2)) := by ring
      _ = x % 2 ^ w + 2 ^ w * (x / 2 ^ w) := by rw [h2]
      _ = x := h1
  by_cases h0 : (x / 2 ^ w) % 2 = 0
  · simp only [h0, ↓reduceIte]
    have hinv : 2 ^ w - 1 - (2 ^ w - 1 - x % 2 ^ w) = x % 2 ^ w := by omega
    rw [hinv, ← h0, hx_reconstruct]
  · simp only [h0, ↓reduceIte]
    let A := (2 ^ w - 1 - x % 2 ^ w) + C
    let q := A / 2 ^ w
    let r := A % 2 ^ w
    have hr : r < 2 ^ w := Nat.mod_lt A (Nat.two_pow_pos w)
    have hA : A = r + 2 ^ w * q := (Nat.mod_add_div A (2 ^ w)).symm
    have hsum : (2 ^ w - 1 - r) + C = x % 2 ^ w + 2 ^ w * q := by
      dsimp [A] at hA; omega
    have hinv : ((2 ^ w - 1 - r) + C) % 2 ^ w = x % 2 ^ w := by
      rw [hsum, mul_comm (2 ^ w) q, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx_lo]
    change ((2 ^ w - 1 - r) + C) % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) +
        2 ^ (w + 1) * (x / 2 ^ (w + 1)) = x
    rw [hinv, hx_reconstruct]

/-- Bound `< 2 ^ bQPE` preserved by `affineFoldVal w C` whenever `w + 1 ≤ bQPE`. -/
theorem affineFoldVal_lt {w bQPE C x : ℕ} (hw : w + 1 ≤ bQPE) (hx : x < 2 ^ bQPE) :
    affineFoldVal w C x < 2 ^ bQPE := by
  have hy_lo := affineFoldVal_lo_lt w C x
  have hhi : (x / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hpow : 2 ^ bQPE = 2 ^ (w + 1) * 2 ^ (bQPE - (w + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le hw]
  have htop : x / 2 ^ (w + 1) < 2 ^ (bQPE - (w + 1)) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hx)
  let a := if (x / 2 ^ w) % 2 = 0 then 2 ^ w - 1 - x % 2 ^ w
    else ((2 ^ w - 1 - x % 2 ^ w) + C) % 2 ^ w
  have ha : a < 2 ^ w := hy_lo
  have hmid : a + 2 ^ w * ((x / 2 ^ w) % 2) < 2 ^ (w + 1) := by
    rw [pow_succ]
    rcases (by omega : (x / 2 ^ w) % 2 = 0 ∨ (x / 2 ^ w) % 2 = 1) with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega
  dsimp [affineFoldVal]
  rw [hpow]
  calc a + 2 ^ w * ((x / 2 ^ w) % 2) + 2 ^ (w + 1) * (x / 2 ^ (w + 1))
      < 2 ^ (w + 1) + 2 ^ (w + 1) * (x / 2 ^ (w + 1)) := Nat.add_lt_add_right hmid _
    _ = 2 ^ (w + 1) * (x / 2 ^ (w + 1) + 1) := by ring
    _ ≤ 2 ^ (w + 1) * 2 ^ (bQPE - (w + 1)) := Nat.mul_le_mul_left _ (by omega)

/-- Involutive affine permutation on `Fin (2 ^ bQPE)` folding `[0, M]` onto single-wire chunk
predicates across the low `bAct` clock qubits (`identity` outside `1 ≤ bAct ≤ bQPE`). -/
def qpeAffinePerm (bAct bQPE M : ℕ) : Equiv.Perm (Fin (2 ^ bQPE)) :=
  if h : 1 ≤ bAct ∧ bAct ≤ bQPE then
    let w := bAct - 1
    let C := M + 1 - 2 ^ w
    have hw : w + 1 ≤ bQPE := by omega
    { toFun := fun x ↦ ⟨affineFoldVal w C x.val, affineFoldVal_lt hw x.isLt⟩
      invFun := fun x ↦ ⟨affineFoldVal w C x.val, affineFoldVal_lt hw x.isLt⟩
      left_inv := fun x ↦ Fin.ext (affineFoldVal_involutive w C x.val)
      right_inv := fun x ↦ Fin.ext (affineFoldVal_involutive w C x.val) }
  else
    Equiv.refl _

/-- `qpeAffinePerm bAct bQPE M` is an exact involution on `Fin (2 ^ bQPE)`. -/
@[simp]
theorem qpeAffinePerm_involutive (bAct bQPE M : ℕ) (x : Fin (2 ^ bQPE)) :
    qpeAffinePerm bAct bQPE M (qpeAffinePerm bAct bQPE M x) = x := by
  unfold qpeAffinePerm
  split_ifs with h
  · exact Fin.ext (affineFoldVal_involutive (bAct - 1) (M + 1 - 2 ^ (bAct - 1)) x.val)
  · rfl

/-- Chunk sizes for the `bAct`-chunk affine-folded dihedral schedule: `2 ^ j` for `j < bAct - 1`
and `M + 1 - 2 ^ (bAct - 1)` for the top chunk `j = bAct - 1`. -/
def chunkSize2 (w M : ℕ) (j : ℕ) : ℕ :=
  if j < w then 2 ^ j else M + 1 - 2 ^ w

/-- Single-wire chunk predicates on the folded clock state `y`: `y.testBit j` for `j < w` and
`!(y.testBit w)` for the top chunk `j = w`. -/
def chunkPred {bQPE : ℕ} (w : ℕ) (j : ℕ) (y : Fin (2 ^ bQPE)) : Bool :=
  if j < w then y.val.testBit j else !(y.val.testBit w)

private theorem sum_signed_bits_eq (w u : ℕ) (hu : u < 2 ^ w) :
    (∑ j : Fin w, (if u.testBit j.val then (-1 : ℤ) else 1) * (2 ^ j.val : ℤ)) =
      (2 ^ w : ℤ) - 1 - 2 * (u : ℤ) := by
  induction w generalizing u with
  | zero =>
    have hu0 : u = 0 := by omega
    subst hu0; simp
  | succ w' ih =>
    rw [Fin.sum_univ_castSucc]
    have hlow_lt : u % 2 ^ w' < 2 ^ w' := Nat.mod_lt u (Nat.two_pow_pos w')
    have hcongr :
        (∑ i : Fin w', (if u.testBit (Fin.castSucc i).val then (-1 : ℤ) else 1) *
            (2 ^ (Fin.castSucc i).val : ℤ)) =
          ∑ i : Fin w', (if (u % 2 ^ w').testBit i.val then (-1 : ℤ) else 1) * (2 ^ i.val : ℤ) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have ht : (u % 2 ^ w').testBit i.val = u.testBit i.val := by
        rw [Nat.testBit_mod_two_pow]; simp [i.isLt]
      rw [Fin.val_castSucc, ht]
    rw [hcongr, ih (u % 2 ^ w') hlow_lt, Fin.val_last]
    by_cases hlt : u < 2 ^ w'
    · have hmod : u % 2 ^ w' = u := Nat.mod_eq_of_lt hlt
      have htb : u.testBit w' = false := Nat.testBit_lt_two_pow hlt
      rw [hmod, htb, pow_succ]
      simp; ring
    · have hge : 2 ^ w' ≤ u := by omega
      have hlt2 : u - 2 ^ w' < 2 ^ w' := by rw [pow_succ] at hu; omega
      have hdiv : u / 2 ^ w' = 1 := by
        have h1 : u = (u - 2 ^ w') + 2 ^ w' * 1 := by omega
        rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w'),
          Nat.div_eq_zero_iff.mpr (Or.inr hlt2), zero_add]
      have hmod : u % 2 ^ w' = u - 2 ^ w' := by
        have h1 : u = (u - 2 ^ w') + 2 ^ w' * 1 := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
      have htb : u.testBit w' = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]; decide
      rw [hmod, htb, pow_succ]
      simp only [↓reduceIte]
      push_cast [Nat.cast_sub hge]
      ring

/-- Exact dihedral exponent identity: for ANY `1 ≤ bAct ≤ bQPE`, `2 ^ (bAct - 1) ≤ M < 2 ^ bAct`,
and ANY `x : Fin (2 ^ bQPE)` with `x.val ≤ M`, the signed chunk sum at
`y = qpeAffinePerm bAct bQPE M x` equals `2 * x - M`! -/
theorem affine_folded_dihedral_exponent_eq {bAct bQPE M : ℕ}
    (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hMlo : 2 ^ (bAct - 1) ≤ M) (hMhi : M < 2 ^ bAct)
    {x : Fin (2 ^ bQPE)} (hx : x.val ≤ M) :
    let w := bAct - 1
    let y := qpeAffinePerm bAct bQPE M x
    (∑ j : Fin bAct,
      (if ¬ chunkPred w j.val y then (1 : ℤ) else -1) * (chunkSize2 w M j.val : ℤ)) =
      2 * (x.val : ℤ) - (M : ℤ) := by
  obtain ⟨w, rfl⟩ : ∃ w, bAct = w + 1 := ⟨bAct - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hMlo
  change (∑ j : Fin (w + 1),
    (if ¬ chunkPred w j.val (qpeAffinePerm (w + 1) bQPE M x) then (1 : ℤ) else -1) *
      (chunkSize2 w M j.val : ℤ)) = 2 * (x.val : ℤ) - (M : ℤ)
  set y := qpeAffinePerm (w + 1) bQPE M x
  let C := M + 1 - 2 ^ w
  have hy_val : y.val = affineFoldVal w C x.val := by
    dsimp only [y, qpeAffinePerm, Nat.add_sub_cancel]
    split_ifs with h
    · rfl
    · exfalso; exact h ⟨hbAct, hbQPE⟩
  obtain ⟨hylo, hyhi, _⟩ := affineFoldVal_decomp w C x.val
  have hx_lt_top : x.val < 2 ^ (w + 1) := lt_of_le_of_lt hx hMhi
  rw [Fin.sum_univ_castSucc]
  have hprefix :
      (∑ i : Fin w,
        (if ¬ chunkPred w (Fin.castSucc i).val y then (1 : ℤ) else -1) *
          (chunkSize2 w M (Fin.castSucc i).val : ℤ)) =
        (2 ^ w : ℤ) - 1 - 2 * ((y.val % 2 ^ w : ℕ) : ℤ) := by
    have hcongr :
        (∑ i : Fin w,
          (if ¬ chunkPred w (Fin.castSucc i).val y then (1 : ℤ) else -1) *
            (chunkSize2 w M (Fin.castSucc i).val : ℤ)) =
        ∑ i : Fin w,
          (if (y.val % 2 ^ w).testBit i.val then (-1 : ℤ) else 1) * (2 ^ i.val : ℤ) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have ht : (y.val % 2 ^ w).testBit i.val = y.val.testBit i.val := by
        rw [Nat.testBit_mod_two_pow]; simp [i.isLt]
      simp only [Fin.val_castSucc, chunkPred, chunkSize2, i.isLt, ↓reduceIte, ← ht]
      cases (y.val % 2 ^ w).testBit i.val <;> simp
    rw [hcongr]
    exact sum_signed_bits_eq w (y.val % 2 ^ w) (Nat.mod_lt _ (Nat.two_pow_pos w))
  rw [hprefix, Fin.val_last]
  have hlast_pred : chunkPred w w y = !(y.val.testBit w) := by simp [chunkPred]
  have hlast_size : chunkSize2 w M w = M + 1 - 2 ^ w := by simp [chunkSize2]
  rw [hlast_pred, hlast_size, hy_val, hylo]
  have htb_w : (affineFoldVal w C x.val).testBit w = decide ((x.val / 2 ^ w) % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, hyhi]
  rw [htb_w]
  have hle3 : 2 ^ w ≤ M + 1 := by omega
  by_cases hlt : x.val < 2 ^ w
  · have hdiv0 : x.val / 2 ^ w = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hlt)
    have hmod : x.val % 2 ^ w = x.val := Nat.mod_eq_of_lt hlt
    rw [hdiv0, hmod]
    simp only [Nat.zero_mod, zero_ne_one, decide_false, Bool.not_false, not_true_eq_false,
      ↓reduceIte]
    have hle1 : x.val ≤ 2 ^ w - 1 := by omega
    have hle2 : 1 ≤ 2 ^ w := by omega
    push_cast [Nat.cast_sub hle1, Nat.cast_sub hle2, Nat.cast_sub hle3]
    ring
  · have hge : 2 ^ w ≤ x.val := by omega
    have hsub_lt : x.val - 2 ^ w < 2 ^ w := by rw [pow_succ] at hx_lt_top; omega
    have hdiv1 : x.val / 2 ^ w = 1 := by
      have h1 : x.val = (x.val - 2 ^ w) + 2 ^ w * 1 := by omega
      rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
        Nat.div_eq_zero_iff.mpr (Or.inr hsub_lt), zero_add]
    have hmod : x.val % 2 ^ w = x.val - 2 ^ w := by
      have h1 : x.val = (x.val - 2 ^ w) + 2 ^ w * 1 := by omega
      conv_lhs => rw [h1]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub_lt]
    have hMsub_lt : M - x.val < 2 ^ w := by rw [pow_succ] at hMhi; omega
    have hfold_val : ((2 ^ w - 1 - (x.val - 2 ^ w)) + C) % 2 ^ w = M - x.val := by
      have hsum : (2 ^ w - 1 - (x.val - 2 ^ w)) + C = (M - x.val) + 2 ^ w * 1 := by
        dsimp [C]; omega
      rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hMsub_lt]
    rw [hdiv1, hmod, hfold_val]
    simp only [Nat.one_mod, decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
      ↓reduceIte]
    push_cast [Nat.cast_sub hx, Nat.cast_sub hle3]
    ring

/-- Sum of `chunkSize2 (bAct - 1) M j` across `j : Fin bAct` equals `M`. -/
theorem sumChunkSize_eq {bAct M : ℕ} (hbAct : 1 ≤ bAct) (hMlo : 2 ^ (bAct - 1) ≤ M) :
    (∑ j : Fin bAct, chunkSize2 (bAct - 1) M j.val) = M := by
  obtain ⟨w, rfl⟩ : ∃ w, bAct = w + 1 := ⟨bAct - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hMlo ⊢
  rw [Fin.sum_univ_castSucc]
  have hgeom : ∀ k : ℕ, (∑ i : Fin k, 2 ^ i.val) = 2 ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k' ih =>
      rw [Fin.sum_univ_castSucc, Fin.val_last]
      have h1 : (∑ i : Fin k', 2 ^ (Fin.castSucc i).val) = ∑ i : Fin k', 2 ^ i.val := rfl
      rw [h1, ih, pow_succ]
      have := @Nat.one_le_two_pow k'
      omega
  have hpref : (∑ i : Fin w, chunkSize2 w M (Fin.castSucc i).val) = 2 ^ w - 1 := by
    rw [← hgeom w]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [chunkSize2, i.isLt]
  rw [hpref, Fin.val_last]
  simp only [chunkSize2, lt_irrefl, ↓reduceIte]
  have := @Nat.one_le_two_pow w
  omega

/-- Involutive affine clock-folding circuit on `rQPELoc`, flipping the low `bAct - 1` clock wires
and adding `M + 1 - 2 ^ (bAct - 1)` modulo `2 ^ (bAct - 1)` controlled by wire `bAct - 1`. -/
def qpeAffineFoldDyn {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  let w := bAct - 1
  let C := M + 1 - 2 ^ w
  let rClock := rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rScr := rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rLow := rClock.slice 0 w (by omega)
  let wCtrl := rClock ⟨w, by omega⟩
  let rAddScr := rScr.slice 0 (w - 1) (by omega)
  have hCT : ∀ i : Fin w, wCtrl ≠ rLow i := fun i h ↦ by
    have hv := congrArg Fin.val (rClock.wires.injective h)
    change w = 0 + i.val at hv
    omega
  have hCS : ∀ j : Fin (w - 1), wCtrl ≠ rAddScr j := fun j ↦
    (QubitisedWalk.disjointWires_compose_right
      (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)).ne ⟨w, by omega⟩ j
  have hTS : rLow.DisjointWires rAddScr :=
    QubitisedWalk.disjointWires_compose_right
      (QubitisedWalk.disjointWires_compose_left
        (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
  .seq (.circuit (xRegCirc rLow)) (ctrlAddConstModDyn v wCtrl rLow C rAddScr hCT hCS hTS)

@[simp]
theorem qpeAffineFoldDyn_count_toff {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb) :
    (qpeAffineFoldDyn bQPE bCat mOut mMid mLow sUb v (aRem := aRem) (mRem := mRem)
      bAct M hbAct hbQPE hbScr).count .TOFF = 0 := by
  simp [qpeAffineFoldDyn, count_xRegCirc_toff]

@[simp]
theorem qpeAffineFoldDyn_count_t {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb) :
    (qpeAffineFoldDyn bQPE bCat mOut mMid mLow sUb v (aRem := aRem) (mRem := mRem)
      bAct M hbAct hbQPE hbScr).count .T =
      ctrlAddConstModTCount (bAct - 1) (M + 1 - 2 ^ (bAct - 1)) := by
  simp [qpeAffineFoldDyn, count_xRegCirc_t]

private theorem regVal_flipRegBits {N w : ℕ} (r : QRegister w N) (β : BitAssignment N) :
    regVal r (ReflectionProofs.flipRegBits r β) = 2 ^ w - 1 - regVal r β := by
  induction w with
  | zero =>
    have h1 := regVal_lt r (ReflectionProofs.flipRegBits r β)
    have h2 := regVal_lt r β
    omega
  | succ d ih =>
    rw [regVal_cons_slice r (ReflectionProofs.flipRegBits r β), regVal_cons_slice r β]
    have h0 : ReflectionProofs.flipRegBits r β (r ⟨0, by omega⟩) = β (r ⟨0, by omega⟩) + 1 :=
      ReflectionProofs.flipRegBits_apply_reg r β ⟨0, by omega⟩
    let rTail := r.slice 1 d (by omega)
    have htail_eq : regVal rTail (ReflectionProofs.flipRegBits r β) =
        regVal rTail (ReflectionProofs.flipRegBits rTail β) := by
      refine congrArg Fin.val ?_
      unfold localIdx; congr 1; funext j
      rw [ReflectionProofs.flipRegBits_apply_reg]
      change ReflectionProofs.flipRegBits r β (r ⟨1 + j.val, by omega⟩) = _
      rw [ReflectionProofs.flipRegBits_apply_reg]; rfl
    have hlt := regVal_lt rTail β
    dsimp only [rTail] at htail_eq hlt ⊢
    rw [h0, htail_eq, ih (r.slice 1 d (by omega)), pow_succ']
    rcases bit_cases (β (r ⟨0, by omega⟩)) with hb | hb
    · rw [hb, zero_add, bitNat_zero, bitNat_one]; omega
    · rw [hb, one_add_one_zmod2, bitNat_one, bitNat_zero]; omega

private theorem mod_two_pow_div_mod_two (a w i : ℕ) (hi : i < w) :
    ((a % 2 ^ w) / 2 ^ i) % 2 = (a / 2 ^ i) % 2 := by
  have ht : (a % 2 ^ w).testBit i = a.testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at ht
  have h1 : ((a % 2 ^ w) / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
  have h2 : (a / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
  rcases (by omega : ((a % 2 ^ w) / 2 ^ i) % 2 = 0 ∨
      ((a % 2 ^ w) / 2 ^ i) % 2 = 1) with ha0 | ha1 <;>
    rcases (by omega : (a / 2 ^ i) % 2 = 0 ∨ (a / 2 ^ i) % 2 = 1) with hb0 | hb1 <;>
    simp_all

private theorem regVal_slice_zero_eq_mod {N b w : ℕ} (r : QRegister b N) (hw : w ≤ b)
    (β : BitAssignment N) :
    regVal (r.slice 0 w (by omega)) β = regVal r β % 2 ^ w := by
  have heq : localIdx (r.slice 0 w (by omega)) β =
      ⟨regVal r β % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩ := by
    apply (basisBits w).injective
    funext i
    rw [basisBits_basisBitsEquiv_symm]
    apply bit_eq_of_bitNat_eq
    rw [basisBits_bitNat_eq]
    dsimp only
    rw [mod_two_pow_div_mod_two (regVal r β) w i.val i.isLt,
      regVal_div_pow_mod_two r β (by omega : i.val < b)]
    have hi : (r.slice 0 w (by omega)) i = r ⟨i.val, by omega⟩ := by
      rw [QRegister.slice_apply]
      exact congrArg _ (Fin.ext (by simp))
    rw [hi]
  exact congrArg Fin.val heq

/-- `CleanRealizes` theorem for `qpeAffineFoldDyn` on `(rQPELoc, rFullZeroLoc)`. -/
theorem qpeAffineFoldDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid))
    (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb) :
    XMeasCircuit.CleanRealizes v
      (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (permutationUnitary (qpeAffinePerm bAct bQPE M))
      (qpeAffineFoldDyn bQPE bCat mOut mMid mLow sUb v (aRem := aRem) (mRem := mRem)
        bAct M hbAct hbQPE hbScr) := by
  let w := bAct - 1
  let C := M + 1 - 2 ^ w
  let rClock := rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rScr := rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
  let rLow := rClock.slice 0 w (by omega)
  let wCtrl := rClock ⟨w, by omega⟩
  let rAddScr := rScr.slice 0 (w - 1) (by omega)
  have hClockFullImg : Disjoint rClock.image rFull.image := by
    rw [image_rFullZeroLoc, Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
      obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2
      exact (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).ne i j hj.symm
    · rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
      obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2
      exact (QubitisedWalk.disjointWires_compose_right
        (QubitisedWalk.disjointWires_compose_right
          (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))).ne i j hj.symm
  have hAddScrSub : rAddScr.image ⊆ rFull.image := by
    intro q hq
    obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hq
    rw [image_rFullZeroLoc]
    exact Finset.mem_union_left _ ((QRegister.mem_image rScr _).mpr ⟨_, rfl⟩)
  have hx : CleanRealizesWires v rFull.image (xRegCirc rLow).eval (.circuit (xRegCirc rLow)) :=
    CleanRealizesWires.circuit v rFull.image (xRegCirc rLow) (count_xRegCirc_toff rLow)
      (by
        refine Finset.disjoint_of_subset_left
          ((support_xRegCirc_subset rLow).trans ?_) hClockFullImg
        intro q hq; obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hq
        exact (QRegister.mem_image rClock _).mpr ⟨_, rfl⟩)
  have hCT : ∀ i : Fin w, wCtrl ≠ rLow i := fun i h ↦ by
    have hv := congrArg Fin.val (rClock.wires.injective h)
    change w = 0 + i.val at hv; omega
  have hCS : ∀ j : Fin (w - 1), wCtrl ≠ rAddScr j := fun j ↦
    (QubitisedWalk.disjointWires_compose_right
      (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)).ne ⟨w, by omega⟩ j
  have hTS : rLow.DisjointWires rAddScr :=
    QubitisedWalk.disjointWires_compose_right
      (QubitisedWalk.disjointWires_compose_left
        (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
  have hAddSub := cleanRealizesWires_ctrlAddConstModDyn v wCtrl rLow C rAddScr hCT hCS hTS
  have hAddSuppDisj : Disjoint
      (ctrlAddConstModDyn v wCtrl rLow C rAddScr hCT hCS hTS).support
      (rFull.image \ rAddScr.image) := by
    refine Finset.disjoint_of_subset_left
      (support_ctrlAddConstModDyn_subset v wCtrl rLow C rAddScr hCT hCS hTS) ?_
    rw [Finset.disjoint_left]
    intro q hq hdiff
    have hqF : q ∈ rFull.image := (Finset.mem_sdiff.mp hdiff).1
    have hqNotAdd : q ∉ rAddScr.image := (Finset.mem_sdiff.mp hdiff).2
    simp only [Finset.mem_union, Finset.mem_insert] at hq
    rcases hq with (rfl | hLow) | hAdd
    · exact Finset.disjoint_left.mp hClockFullImg
        ((QRegister.mem_image rClock _).mpr ⟨⟨w, by omega⟩, rfl⟩) hqF
    · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hLow
      exact Finset.disjoint_left.mp hClockFullImg
        ((QRegister.mem_image rClock _).mpr ⟨_, rfl⟩) hqF
    · exact hqNotAdd hAdd
  have hLowDisjDiff : Disjoint rLow.image (rFull.image \ rAddScr.image) := by
    refine Finset.disjoint_of_subset_right Finset.sdiff_subset ?_
    refine Finset.disjoint_of_subset_left ?_ hClockFullImg
    intro q hq; obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hq
    exact (QRegister.mem_image rClock _).mpr ⟨_, rfl⟩
  have hAddFull : CleanRealizesWires v rFull.image _
      (ctrlAddConstModDyn v wCtrl rLow C rAddScr hCT hCS hTS) :=
    (Finset.union_sdiff_of_subset hAddScrSub) ▸
      hAddSub.extend_wires (rFull.image \ rAddScr.image) hAddSuppDisj
        (regAddUnitary_comm_zeroProjOn rLow _ _ _ hLowDisjDiff)
  apply CleanRealizesWires.toCleanRealizes
  refine (hx.seq hAddFull).congr_unitary ?_
    (embedMatrix_comm_zeroProjOn_of_disjoint rClock rFull.image hClockFullImg _)
  apply congrArg (· * zeroProjOn rFull.image)
  apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ReflectionProofs.xRegCirc_mulVec_ket,
    regAddUnitary_mulVec_ket, embedUnitary_permutationUnitary_mulVec_ket]
  congr 1
  have hCtrlFlip : ReflectionProofs.flipRegBits rLow β wCtrl = β wCtrl := by
    apply ReflectionProofs.flipRegBits_apply_of_not_mem
    rw [QRegister.mem_image]; rintro ⟨i, hi⟩; exact hCT i hi.symm
  rw [hCtrlFlip, regVal_flipRegBits rLow β, regVal_slice_zero_eq_mod rClock (by omega : w ≤ bQPE) β]
  have hy_eq : (qpeAffinePerm bAct bQPE M (localIdx rClock β)).val =
      affineFoldVal w C (regVal rClock β) := by
    dsimp only [qpeAffinePerm]
    split_ifs with h
    · rfl
    · exfalso; exact h ⟨hbAct, hbQPE⟩
  obtain ⟨hylo, hyhi, hytop⟩ := affineFoldVal_decomp w C (regVal rClock β)
  have hctrl_val : bitNat (β wCtrl) = (regVal rClock β / 2 ^ w) % 2 :=
    (regVal_div_pow_mod_two rClock β (by omega : w < bQPE)).symm
  have hlow_target :
      ((2 ^ w - 1 - regVal rClock β % 2 ^ w) + bitNat (β wCtrl) * C) % 2 ^ w =
        (qpeAffinePerm bAct bQPE M (localIdx rClock β)).val % 2 ^ w := by
    rw [hy_eq, hylo, hctrl_val]
    have hlt2 : (regVal rClock β / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by omega)
    rcases (by omega : (regVal rClock β / 2 ^ w) % 2 = 0 ∨
        (regVal rClock β / 2 ^ w) % 2 = 1) with h0 | h1
    · simp only [h0, zero_mul, add_zero, ↓reduceIte]
      exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (regVal rClock β) (Nat.two_pow_pos w); omega)
    · rw [h1, one_mul, ite_eq_right Nat.one_ne_zero]
  funext q
  by_cases hqC : q ∈ Set.range rClock.wires
  · obtain ⟨k, rfl⟩ := hqC
    rw [writeReg_apply_reg]
    by_cases hk : k.val < w
    · have hkLow : rClock k = rLow ⟨k.val, hk⟩ := by
        rw [QRegister.slice_apply]
        exact congrArg _ (Fin.ext (by simp))
      rw [hkLow, writeReg_apply_reg]
      apply bit_eq_of_bitNat_eq
      rw [basisBits_bitNat_eq, basisBits_bitNat_eq]
      dsimp only
      rw [hlow_target, mod_two_pow_div_mod_two _ w k.val hk]
    · have hnotLow : rClock k ∉ Set.range rLow.wires := by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val (rClock.wires.injective hi)
        change 0 + i.val = k.val at hv; omega
      have hnotLowImg : rClock k ∉ rLow.image := by
        rw [QRegister.mem_image]; rintro ⟨i, hi⟩; exact hnotLow ⟨i, hi⟩
      rw [writeReg_apply_of_not_mem _ _ _ _ hnotLow,
        ReflectionProofs.flipRegBits_apply_of_not_mem _ _ _ hnotLowImg]
      apply bit_eq_of_bitNat_eq
      rw [basisBits_bitNat_eq, ← regVal_div_pow_mod_two rClock β k.isLt, hy_eq]
      by_cases hkw : k.val = w
      · rw [hkw, hyhi]
      · have hk_ge : w + 1 ≤ k.val := by omega
        have hsplit_k : k.val = (w + 1) + (k.val - (w + 1)) := by omega
        conv_lhs => rw [hsplit_k, pow_add, ← Nat.div_div_eq_div_mul]
        conv_rhs => rw [hsplit_k, pow_add, ← Nat.div_div_eq_div_mul, hytop]
  · have hnotLow : q ∉ Set.range rLow.wires := by
      rintro ⟨i, rfl⟩; exact hqC ⟨_, rfl⟩
    have hnotLowImg : q ∉ rLow.image := by
      rw [QRegister.mem_image]; rintro ⟨i, rfl⟩; exact hqC ⟨_, rfl⟩
    rw [writeReg_apply_of_not_mem _ _ _ _ hnotLow,
      ReflectionProofs.flipRegBits_apply_of_not_mem _ _ _ hnotLowImg,
      writeReg_apply_of_not_mem _ _ _ _ hqC]

end ClassicalAdderAndAffineFold

/-! ## Section 3: Boundary-Fused & Endpoint-Absorbed Dihedral Walk `affineDihedralRefl2Dyn` -/

section BoundaryFusedDihedralWalk

open Comparators Comparators.ComparatorProofs

/-- Every chunk size `chunkSize2 (bAct - 1) M j` is strictly positive whenever
`2 ^ (bAct - 1) ≤ M`. -/
theorem chunkSize_pos {bAct M : ℕ} (hMlo : 2 ^ (bAct - 1) ≤ M) (j : ℕ) :
    1 ≤ chunkSize2 (bAct - 1) M j := by
  unfold chunkSize2
  split_ifs
  · exact Nat.one_le_two_pow
  · omega

private theorem basisOutcomeProjector_comm_3 {N k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ N) (x : Fin (2 ^ k₁)) (r₂ : QRegister k₂ N) (y : Fin (2 ^ k₂)) :
    r₁.basisOutcomeProjector x * r₂.basisOutcomeProjector y =
      r₂.basisOutcomeProjector y * r₁.basisOutcomeProjector x := by
  rw [r₁.basisOutcomeProjector_eq_diagonal, r₂.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)

private theorem basisOutcomeProjector_mul_of_union_eq2 {N k₁ k₂ s : ℕ}
    {r₁ : QRegister k₁ N} {r₂ : QRegister k₂ N} {rFull : QRegister s N}
    (h : r₁.image ∪ rFull.image = r₂.image ∪ rFull.image) :
    r₁.basisOutcomeProjector 0 * rFull.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * rFull.basisOutcomeProjector 0 := by
  rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    SelectSwapQROM.zeroProjOn_mul_union, SelectSwapQROM.zeroProjOn_mul_union, h]

private theorem absorbCleanActive_of_comm_3 {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₁ s₂ : ℕ} {v : Var} {rAct : QRegister k N}
    {rScr : QRegister s₁ N} {rFull : QRegister s₂ N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hbase : CleanDyn.CleanRealizes v rAct rScr U P)
    (hsub : rScr.image ⊆ rFull.image)
    (hcomm : (rAct.embedUnitary U).1 * rFull.basisOutcomeProjector 0 =
      rFull.basisOutcomeProjector 0 * (rAct.embedUnitary U).1) :
    XMeasCircuit.CleanRealizes v rAct rFull U P := by
  refine XMeasCircuit.CleanRealizes.absorbCleanActive hbase hsub rfl ?_
  change rFull.basisOutcomeProjector 0 *
      ((rAct.embedUnitary U).1 * rFull.basisOutcomeProjector 0) = _
  rw [hcomm, ← Matrix.mul_assoc, rFull.basisOutcomeProjector_mul_self 0]

private theorem embed_reflInUnitary_comm2 {N k w s : ℕ}
    (rWalk : QRegister k N) (inAll : QRegister w k) (rScr : QRegister s N) :
    (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1 * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * (rWalk.embedUnitary (QubitisedWalk.reflInUnitary
        inAll)).1 := by
  have hemb : (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1 =
      (2 : ℂ) • (rWalk.compose inAll).basisOutcomeProjector 0 - 1 := by
    change rWalk.embedMatrix ((2 : ℂ) • inAll.basisOutcomeProjector 0 - 1) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
      CleanDyn.compose_basisOutcomeProjector]
  rw [hemb, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
    mul_smul_comm, basisOutcomeProjector_comm_3]

private theorem embed_reflInUnitary_mul_rFullZero2
    {bQPE bCat mOut mMid mLow sUb aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero) :
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).embedUnitary
        (QubitisedWalk.reflInUnitary refl.inAll)).1 *
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).basisOutcomeProjector 0 =
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).embedUnitary
        (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid))).1 *
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).basisOutcomeProjector 0 := by
  let rW := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  have hemb {w : ℕ} (sub : QRegister w (walkCatWidth bCat mOut mMid)) :
      (rW.embedUnitary (QubitisedWalk.reflInUnitary sub)).1 =
        (2 : ℂ) • (rW.compose sub).basisOutcomeProjector 0 - 1 := by
    change rW.embedMatrix ((2 : ℂ) • sub.basisOutcomeProjector 0 - 1) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
      CleanDyn.compose_basisOutcomeProjector]
  rw [hemb, hemb, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, smul_mul_assoc, smul_mul_assoc,
    basisOutcomeProjector_mul_of_union_eq2 hCov.2]

private theorem embed_qpeMux_reflIn_comm {N b k w s : ℕ}
    (rQPE : QRegister b N) (rWalk : QRegister k N) (hQW : rQPE.DisjointWires rWalk)
    (inAll : QRegister w k) (rScr : QRegister s N) (pred : Fin (2 ^ b) → Bool) :
    ((rQPE.concat rWalk hQW).embedUnitary
        (QubitisedWalk.qpeMuxUnitary fun m ↦ if pred m then QubitisedWalk.reflInUnitary inAll else
          1)).1 *
        rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 *
        ((rQPE.concat rWalk hQW).embedUnitary
          (QubitisedWalk.qpeMuxUnitary fun m ↦ if pred m then QubitisedWalk.reflInUnitary inAll else
            1)).1 := by
  rw [QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
    QubitisedWalk.embedMatrix_qpeMuxMatrix,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  cases pred m
  · simp [basisOutcomeProjector_comm_3]
  · change (rQPE.basisOutcomeProjector m *
        (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1) * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * (rQPE.basisOutcomeProjector m *
        (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1)
    rw [Matrix.mul_assoc, embed_reflInUnitary_comm2, ← Matrix.mul_assoc,
      basisOutcomeProjector_comm_3 rQPE m, Matrix.mul_assoc]

private theorem embed_qpeMux_reflIn_mul_rFullZero2
    {bQPE bCat mOut mMid mLow sUb aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    (pred : Fin (2 ^ bQPE) → Bool) :
    let rC := (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
      (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    let rF := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
    (rC.embedUnitary (QubitisedWalk.qpeMuxUnitary fun m ↦
        if pred m then QubitisedWalk.reflInUnitary refl.inAll else 1)).1 * rF.basisOutcomeProjector
          0 =
      (rC.embedUnitary (QubitisedWalk.qpeMuxUnitary fun m ↦
        if pred m then QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) else 1)).1 *
        rF.basisOutcomeProjector 0 := by
  intro rC rF
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
    QubitisedWalk.qpeMuxUnitary_val, QubitisedWalk.embedMatrix_qpeMuxMatrix,
      QubitisedWalk.embedMatrix_qpeMuxMatrix,
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  cases pred m
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte, Matrix.mul_assoc]
    apply congrArg
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).basisOutcomeProjector m * ·)
    rw [← QRegister.embedUnitary_val, ← QRegister.embedUnitary_val]
    exact embed_reflInUnitary_mul_rFullZero2 hCov

private theorem singleton_rClock_extractIndex_eq_zero_iff {bQPE N : ℕ}
    (rClock : QRegister bQPE N) (idx : Fin bQPE) (g : Fin (2 ^ N)) :
    (QRegister.singleton (rClock idx)).extractIndex g = 0 ↔
      ¬ (rClock.extractIndex g).val.testBit idx.val := by
  rw [Fin.ext_iff, Fin.val_zero, extractIndex_val_eq_regVal,
    regVal_width_one, QRegister.singleton_apply,
    Nat.testBit_eq_decide_div_mod_eq, extractIndex_val_eq_regVal,
    regVal_div_pow_mod_two rClock (basisBits N g) idx.isLt]
  rcases bit_cases (basisBits N g (rClock idx)) with hb | hb <;>
    simp [hb, bitNat]

private theorem lowBitCtrlR0Dyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero) (idx : Fin bQPE) :
    XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary fun x : Fin (2 ^ bQPE) ↦
        if !x.val.testBit idx.val then
          QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
        else 1)
      (lowBitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl idx) := by
  let rClock := rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rWalk := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rScr := rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
  let hCW := rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  have hSW : (QRegister.singleton (rClock idx)).DisjointWires rWalk :=
    QRegister.disjoint_iff.mpr fun _ j ↦ hCW.ne idx j
  have hraw := QubitisedWalk.reflInOnlyAtZeroDyn_cleanRealizes v
    (QRegister.singleton (rClock idx)) rWalk hSW refl.inAll rScr
    (by decide) refl.haPos (scr_ge_lowCtrl bQPE mLow aRem mRem sUb)
    (QRegister.disjoint_iff.mpr fun _ j ↦
      (QubitisedWalk.disjointWires_compose_right hCW).ne idx j)
    (QRegister.disjoint_iff.mpr fun _ j ↦
      (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).ne idx j)
    (QubitisedWalk.disjointWires_compose_left
      (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
  have hSWS : ((QRegister.singleton (rClock idx)).concat rWalk hSW).DisjointWires rScr := by
    rw [QRegister.disjoint_iff]; intro p j
    rcases fin_eq_castAdd_or_natAdd p with ⟨a, rfl⟩ | ⟨i, rfl⟩
    · fin_cases a
      rw [QRegister.concat_apply_left]
      exact (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).ne idx j
    · rw [QRegister.concat_apply_right]
      exact (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).ne i j
  have hemb :
      ((QRegister.singleton (rClock idx)).concat rWalk hSW).embedUnitary
        (QubitisedWalk.qpeMuxUnitary fun b : Fin (2 ^ 1) ↦
          if b.val = 0 then QubitisedWalk.reflInUnitary refl.inAll else 1) =
      (rClock.concat rWalk hCW).embedUnitary
        (QubitisedWalk.qpeMuxUnitary fun x : Fin (2 ^ bQPE) ↦
          if !x.val.testBit idx.val then
            QubitisedWalk.reflInUnitary refl.inAll
          else 1) := by
    apply Subtype.ext
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
      QubitisedWalk.qpeMuxUnitary_val, QubitisedWalk.embedMatrix_qpeMuxMatrix,
        QubitisedWalk.embedMatrix_qpeMuxMatrix]
    have hsplit (f : Fin (2 ^ bQPE) → Bool) (U : Unitary (2 ^ walkCatWidth bCat mOut mMid)) :
        (∑ x : Fin (2 ^ bQPE), rClock.basisOutcomeProjector x *
            rWalk.embedMatrix (if f x then U else 1).1) =
          (Matrix.diagonal fun g ↦ if f (rClock.extractIndex g) then (1 : ℂ) else 0) *
            rWalk.embedMatrix U.1 +
          (Matrix.diagonal fun g ↦ if f (rClock.extractIndex g) then 0 else (1 : ℂ)) := by
      have h1 : (∑ x : Fin (2 ^ bQPE), rClock.basisOutcomeProjector x *
            rWalk.embedMatrix (if f x then U else 1).1) =
          (∑ x : Fin (2 ^ bQPE), if f x then rClock.basisOutcomeProjector x else 0) *
            rWalk.embedMatrix U.1 +
          ∑ x : Fin (2 ^ bQPE), if f x then 0 else rClock.basisOutcomeProjector x := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        cases f x <;> simp [QRegister.embedMatrix_one]
      rw [h1]
      refine congrArg₂ (· + ·) (congrArg₂ (· * ·) ?_ rfl) ?_
      · ext i j
        rw [Matrix.sum_apply]
        by_cases hij : i = j
        · subst hij
          rw [Finset.sum_eq_single (rClock.extractIndex i)]
          · cases hf : f (rClock.extractIndex i) <;> simp [hf]
          · intro x _ hxi
            cases f x
            · simp
            · simp [hxi.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp only [Matrix.diagonal_apply_ne _ hij]
          refine Finset.sum_eq_zero fun x _ ↦ ?_
          cases f x
          · simp
          · simp [hij]
      · ext i j
        rw [Matrix.sum_apply]
        by_cases hij : i = j
        · subst hij
          rw [Finset.sum_eq_single (rClock.extractIndex i)]
          · cases hf : f (rClock.extractIndex i) <;> simp [hf]
          · intro x _ hxi
            cases f x
            · simp [hxi.symm]
            · simp
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp only [Matrix.diagonal_apply_ne _ hij]
          refine Finset.sum_eq_zero fun x _ ↦ ?_
          cases f x
          · simp [hij]
          · simp
    have hsum2 :
        (∑ m : Fin (2 ^ 1),
          (QRegister.singleton (rClock idx)).basisOutcomeProjector m *
            rWalk.embedMatrix (if m.val = 0 then QubitisedWalk.reflInUnitary refl.inAll else 1).1) =
        (QRegister.singleton (rClock idx)).basisOutcomeProjector 0 *
            rWalk.embedMatrix (QubitisedWalk.reflInUnitary refl.inAll).1 +
          (QRegister.singleton (rClock idx)).basisOutcomeProjector 1 *
            rWalk.embedMatrix (1 : Unitary _).1 :=
      Fin.sum_univ_two _
    rw [hsplit (fun x ↦ !x.val.testBit idx.val), hsum2,
      OneMemClass.coe_one, QRegister.embedMatrix_one, Matrix.mul_one]
    refine congrArg₂ (· + ·) (congrArg₂ (· * ·) ?_ rfl) ?_
    · rw [QRegister.basisOutcomeProjector_eq_diagonal]
      apply congrArg Matrix.diagonal; funext g
      by_cases h : (QRegister.singleton (rClock idx)).extractIndex g = 0
      · have hnot := (singleton_rClock_extractIndex_eq_zero_iff rClock idx g).mp h
        have ht : (!(rClock.extractIndex g).val.testBit idx.val) = true := by
          cases htb : (rClock.extractIndex g).val.testBit idx.val
          · rfl
          · exact absurd htb hnot
        simp only [ht, h, ↓reduceIte]
      · have hf : (!(rClock.extractIndex g).val.testBit idx.val) = false := by
          cases htb : (rClock.extractIndex g).val.testBit idx.val
          · exfalso
            exact h
              ((singleton_rClock_extractIndex_eq_zero_iff rClock idx g).mpr
                (by rw [htb]; decide))
          · rfl
        simp only [hf, h, Bool.false_eq_true, ↓reduceIte]
    · rw [QRegister.basisOutcomeProjector_eq_diagonal]
      apply congrArg Matrix.diagonal; funext g
      by_cases h0 : (QRegister.singleton (rClock idx)).extractIndex g = 0
      · have hnot := (singleton_rClock_extractIndex_eq_zero_iff rClock idx g).mp h0
        have ht : (!(rClock.extractIndex g).val.testBit idx.val) = true := by
          cases htb : (rClock.extractIndex g).val.testBit idx.val
          · rfl
          · exact absurd htb hnot
        have hne1 : (QRegister.singleton (rClock idx)).extractIndex g ≠ 1 := by
          rw [h0]; decide
        simp only [ht, hne1, ↓reduceIte]
      · have hf : (!(rClock.extractIndex g).val.testBit idx.val) = false := by
          cases htb : (rClock.extractIndex g).val.testBit idx.val
          · exfalso
            exact h0
              ((singleton_rClock_extractIndex_eq_zero_iff rClock idx g).mpr
                (by rw [htb]; decide))
          · rfl
        have h1 : (QRegister.singleton (rClock idx)).extractIndex g = 1 := by
          have hlt := ((QRegister.singleton (rClock idx)).extractIndex g).isLt
          have hne0 : ((QRegister.singleton (rClock idx)).extractIndex g).val ≠ 0 :=
            fun hv ↦ h0 (Fin.ext hv)
          exact Fin.ext (by
            change ((QRegister.singleton (rClock idx)).extractIndex g).val = 1; omega)
        simp only [hf, h1, Bool.false_eq_true, ↓reduceIte]
  have hScrLift : CleanDyn.CleanRealizes v (rClock.concat rWalk hCW) rScr
      (QubitisedWalk.qpeMuxUnitary fun x : Fin (2 ^ bQPE) ↦
        if !x.val.testBit idx.val then QubitisedWalk.reflInUnitary refl.inAll else 1)
      (lowBitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl idx) :=
    CleanRealizesWires.toCleanRealizes
      (hemb ▸ CleanRealizesWires.ofCleanRealizes hSWS hraw)
  have hsub : rScr.image ⊆ rFull.image := by
    rw [image_rFullZeroLoc]; exact Finset.subset_union_left
  exact (absorbCleanActive_of_comm_3 hScrLift hsub
    (embed_qpeMux_reflIn_comm rClock rWalk hCW refl.inAll rFull _)).congrUnitary
    (embed_qpeMux_reflIn_mul_rFullZero2 hCov _)

private theorem cleanRealizes_of_eq2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} {v : Var} {rAct : QRegister k N} {rFull : QRegister s N}
    {U₁ U₂ : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : XMeasCircuit.CleanRealizes v rAct rFull U₁ P) (heq : U₁ = U₂) :
    XMeasCircuit.CleanRealizes v rAct rFull U₂ P :=
  heq ▸ h

private theorem basisOutcomeProjector_mulVec_ket {N m : ℕ} (r : QRegister m N)
    (x : Fin (2 ^ m)) (β : BitAssignment N) :
    (r.basisOutcomeProjector x).mulVec (ket β) = if localIdx r β = x then ket β else 0 := by
  funext g
  rw [QRegister.basisOutcomeProjector_mulVec]
  by_cases hg : g = (basisBits N).symm β
  · subst hg
    have hex : r.extractIndex ((basisBits N).symm β) = localIdx r β := by
      apply (basisBits m).injective
      funext i
      rw [QRegister.basisBits_extractIndex, basisBits_basisBitsEquiv_symm]
      exact (congrFun (basisBits_basisBitsEquiv_symm (fun j ↦ β (r j))) i).symm
    rw [hex]
    by_cases hx : localIdx r β = x <;> simp [hx]
  · have hk0 : ket β g = 0 := by
      dsimp [ket, basisState]; exact Pi.single_eq_of_ne hg _
    split_ifs <;> simp [hk0]

/-- Conjugating `QubitisedWalk.qpeMuxUnitary F` by an involutive clock permutation `σ` reindexes
the multiplexer fiber to `fun x ↦ F (σ x)`. -/
theorem qpeMuxUnitary_conj_perm {b k : ℕ} (σ : Equiv.Perm (Fin (2 ^ b)))
    (hinv : ∀ x, σ (σ x) = x) (F : Fin (2 ^ b) → Unitary (2 ^ k)) :
    (QubitisedWalk.qpeInCombined b k).embedUnitary (permutationUnitary σ) *
        QubitisedWalk.qpeMuxUnitary F *
        (QubitisedWalk.qpeInCombined b k).embedUnitary (permutationUnitary σ) =
      QubitisedWalk.qpeMuxUnitary (fun x ↦ F (σ x)) := by
  let rQ := QubitisedWalk.qpeInCombined b k
  let rW := QubitisedWalk.walkInCombined b k
  let Pσ := (rQ.embedUnitary (permutationUnitary σ)).1
  have hdisj : rQ.DisjointWires rW := QubitisedWalk.qpeInCombined_disjoint_walkInCombined b k
  have hproj (m : Fin (2 ^ b)) :
      Pσ * rQ.basisOutcomeProjector m * Pσ = rQ.basisOutcomeProjector (σ m) := by
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [Pσ]
    rw [embedUnitary_permutationUnitary_mulVec_ket, basisOutcomeProjector_mulVec_ket,
      basisOutcomeProjector_mulVec_ket]
    have hloc : localIdx rQ (writeReg β rQ (basisBits b (σ (localIdx rQ β)))) =
        σ (localIdx rQ β) := by
      apply (basisBits b).injective
      funext i
      rw [basisBits_basisBitsEquiv_symm, writeReg_apply_reg]
    rw [hloc]
    have hiff : σ (localIdx rQ β) = m ↔ localIdx rQ β = σ m :=
      ⟨fun h ↦ by rw [← h, hinv], fun h ↦ by rw [h, hinv]⟩
    by_cases hm : localIdx rQ β = σ m
    · rw [ite_eq_left (hiff.mpr hm), ite_eq_left hm, embedUnitary_permutationUnitary_mulVec_ket,
        hloc, writeReg_idem, hinv, writeReg_self]
    · rw [ite_eq_right (mt hiff.mp hm), ite_eq_right hm, Matrix.mulVec_zero]
  apply Subtype.ext
  change Pσ * (QubitisedWalk.qpeMuxUnitary F).1 * Pσ = (QubitisedWalk.qpeMuxUnitary (fun x ↦
    F (σ x))).1
  rw [QubitisedWalk.qpeMuxUnitary_val, QubitisedWalk.qpeMuxUnitary_val]
  dsimp only [QubitisedWalk.qpeMuxMatrix]
  rw [Finset.mul_sum, Finset.sum_mul]
  let g : Fin (2 ^ b) → Operator (2 ^ (b + k)) := fun x ↦
    rQ.basisOutcomeProjector x * rW.embedMatrix (F (σ x)).1
  have hterm (m : Fin (2 ^ b)) :
      Pσ * (rQ.basisOutcomeProjector m * rW.embedMatrix (F m).1) * Pσ = g (σ m) := by
    have hcomm : rW.embedMatrix (F m).1 * Pσ = Pσ * rW.embedMatrix (F m).1 :=
      (rQ.embedMatrix_comm_of_disjoint rW hdisj (permutationUnitary σ).1 (F m).1).symm
    calc Pσ * (rQ.basisOutcomeProjector m * rW.embedMatrix (F m).1) * Pσ
        = Pσ * rQ.basisOutcomeProjector m * (rW.embedMatrix (F m).1 * Pσ) := by
          simp only [Matrix.mul_assoc]
      _ = (Pσ * rQ.basisOutcomeProjector m * Pσ) * rW.embedMatrix (F m).1 := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = rQ.basisOutcomeProjector (σ m) * rW.embedMatrix (F m).1 := by rw [hproj m]
      _ = g (σ m) := by dsimp only [g]; rw [hinv m]
  exact (Finset.sum_congr rfl fun m _ ↦ hterm m).trans (Equiv.sum_comp σ g)

/-- Conjugating a `CleanRealizes` multiplexer on `rClock.concat rWalk` by an involutive
`CleanRealizes` clock permutation on `rClock` reindexes the multiplexer fiber by `σ`. -/
theorem cleanRealizes_conj_clockPerm {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b k s : ℕ} {v : Var}
    {rClock : QRegister b N} {rWalk : QRegister k N} (hCW : rClock.DisjointWires rWalk)
    {rFull : QRegister s N}
    {σ : Equiv.Perm (Fin (2 ^ b))} (hinv : ∀ x, σ (σ x) = x)
    {F : Fin (2 ^ b) → Unitary (2 ^ k)}
    {pPerm pMid : DynamicCircuit Var N}
    (hPerm : XMeasCircuit.CleanRealizes v rClock rFull (permutationUnitary σ) pPerm)
    (hMid : XMeasCircuit.CleanRealizes v (rClock.concat rWalk hCW) rFull
      (QubitisedWalk.qpeMuxUnitary F) pMid) :
    XMeasCircuit.CleanRealizes v (rClock.concat rWalk hCW) rFull
      (QubitisedWalk.qpeMuxUnitary (fun x ↦ F (σ x)))
      (.seq pPerm (.seq pMid pPerm)) := by
  have hP := XMeasCircuit.CleanRealizes.liftActiveOfEq
    (QubitisedWalk.concat_compose_qpeInCombined rClock rWalk hCW).symm hPerm
  exact cleanRealizes_of_eq2 (hP.seq (hMid.seq hP)) (qpeMuxUnitary_conj_perm σ hinv F)

/-- Clock-index permutation flipping bit `idx` of a `b`-qubit register. -/
noncomputable def xClockPerm {b : ℕ} (idx : Fin b) : Equiv.Perm (Fin (2 ^ b)) where
  toFun x :=
    ⟨x.val ^^^ 2 ^ idx.val,
      Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by omega) idx.isLt)⟩
  invFun x :=
    ⟨x.val ^^^ 2 ^ idx.val,
      Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by omega) idx.isLt)⟩
  left_inv x := by
    apply Fin.ext; dsimp only
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  right_inv x := by
    apply Fin.ext; dsimp only
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

@[simp]
theorem xClockPerm_involutive {b : ℕ} (idx : Fin b) (x : Fin (2 ^ b)) :
    xClockPerm idx (xClockPerm idx x) = x :=
  (xClockPerm idx).left_inv x

@[simp]
theorem xClockPerm_testBit_self {b : ℕ} (idx : Fin b) (x : Fin (2 ^ b)) :
    (xClockPerm idx x).val.testBit idx.val = !x.val.testBit idx.val := by
  dsimp [xClockPerm]
  cases h : x.val.testBit idx.val <;> simp [Nat.testBit_xor, h]

/-- Clock-index permutation applying `CNOT i j` (`target := j`, `control := i`, `i ≠ j`). -/
noncomputable def cnotClockPerm {b : ℕ} (i j : Fin b) (hne : i ≠ j) :
    Equiv.Perm (Fin (2 ^ b)) where
  toFun x :=
    ⟨if x.val.testBit i.val then x.val ^^^ 2 ^ j.val else x.val, by
      split_ifs
      · exact Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by omega) j.isLt)
      · exact x.isLt⟩
  invFun x :=
    ⟨if x.val.testBit i.val then x.val ^^^ 2 ^ j.val else x.val, by
      split_ifs
      · exact Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by omega) j.isLt)
      · exact x.isLt⟩
  left_inv x := by
    have hij : j.val ≠ i.val := fun h ↦ hne (Fin.ext h.symm)
    apply Fin.ext; dsimp only
    by_cases hb : x.val.testBit i.val
    · have hb' : (x.val ^^^ 2 ^ j.val).testBit i.val = true := by
        simp [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hij, hb]
      simp [hb, hb', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · simp [hb]
  right_inv x := by
    have hij : j.val ≠ i.val := fun h ↦ hne (Fin.ext h.symm)
    apply Fin.ext; dsimp only
    by_cases hb : x.val.testBit i.val
    · have hb' : (x.val ^^^ 2 ^ j.val).testBit i.val = true := by
        simp [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hij, hb]
      simp [hb, hb', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · simp [hb]

@[simp]
theorem cnotClockPerm_involutive {b : ℕ} (i j : Fin b) (hne : i ≠ j) (x : Fin (2 ^ b)) :
    cnotClockPerm i j hne (cnotClockPerm i j hne x) = x :=
  (cnotClockPerm i j hne).left_inv x

@[simp]
theorem cnotClockPerm_testBit_tgt {b : ℕ} (i j : Fin b) (hne : i ≠ j) (x : Fin (2 ^ b)) :
    (cnotClockPerm i j hne x).val.testBit j.val =
      (x.val.testBit j.val != x.val.testBit i.val) := by
  dsimp [cnotClockPerm]
  by_cases hb : x.val.testBit i.val
  · simp [hb, Nat.testBit_xor]
  · simp [hb]

private theorem testBit_eq_bitNat_eq_one {k : ℕ} (x : Fin (2 ^ k)) (i : Fin k) :
    x.val.testBit i.val = decide (bitNat (basisBits k x i) = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, basisBits_bitNat_eq]

private theorem cleanRealizes_xClock {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b s : ℕ} (v : Var) (rClock : QRegister b N) (rFull : QRegister s N)
    (hCF : Disjoint rClock.image rFull.image) (idx : Fin b) :
    XMeasCircuit.CleanRealizes v rClock rFull (permutationUnitary (xClockPerm idx))
      (.circuit (xRegCirc (QRegister.singleton (rClock idx)))) := by
  let rIdx := QRegister.singleton (rClock idx)
  have hc := CleanRealizesWires.circuit v rFull.image (xRegCirc rIdx) (count_xRegCirc_toff rIdx)
    (by
      refine Finset.disjoint_of_subset_left
        ((support_xRegCirc_subset rIdx).trans ?_) hCF
      intro q hq; obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hq
      fin_cases i
      exact (QRegister.mem_image rClock _).mpr ⟨idx, rfl⟩)
  apply CleanRealizesWires.toCleanRealizes
  refine hc.congr_unitary ?_
    (embedMatrix_comm_zeroProjOn_of_disjoint rClock rFull.image hCF _)
  apply congrArg (· * zeroProjOn rFull.image)
  apply matrix_ext_ket; intro β
  rw [ReflectionProofs.xRegCirc_mulVec_ket, embedUnitary_permutationUnitary_mulVec_ket]
  congr 1; funext q
  by_cases hqC : q ∈ Set.range rClock.wires
  · obtain ⟨k, rfl⟩ := hqC
    rw [writeReg_apply_reg]
    by_cases hki : k = idx
    · subst hki
      change ReflectionProofs.flipRegBits rIdx β (rIdx 0) = _
      rw [ReflectionProofs.flipRegBits_apply_reg rIdx β 0,
        show rIdx.wires 0 = rClock.wires k from rfl]
      have hloc_bit : basisBits b (localIdx rClock β) k = β (rClock k) :=
        congrFun (basisBits_basisBitsEquiv_symm (fun i ↦ β (rClock i))) k
      apply bit_eq_of_bitNat_eq
      have htb := xClockPerm_testBit_self k (localIdx rClock β)
      rw [testBit_eq_bitNat_eq_one, testBit_eq_bitNat_eq_one, hloc_bit] at htb
      rcases bit_cases (β (rClock k)) with hb | hb <;>
        rcases bit_cases (basisBits b (xClockPerm k (localIdx rClock β)) k) with hb' | hb' <;>
        simp_all [bitNat]
    · have hnot : rClock k ∉ rIdx.image := by
        rw [QRegister.mem_image]; rintro ⟨a, ha⟩; fin_cases a
        exact hki (rClock.wires.injective ha).symm
      rw [ReflectionProofs.flipRegBits_apply_of_not_mem _ _ _ hnot]
      have hloc_bit : basisBits b (localIdx rClock β) k = β (rClock k) :=
        congrFun (basisBits_basisBitsEquiv_symm (fun i ↦ β (rClock i))) k
      apply bit_eq_of_bitNat_eq
      have hne_val : k.val ≠ idx.val := fun hv ↦ hki (Fin.ext hv)
      have htb : (xClockPerm idx (localIdx rClock β)).val.testBit k.val =
          (localIdx rClock β).val.testBit k.val := by
        dsimp [xClockPerm]
        simp [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm hne_val)]
      rw [testBit_eq_bitNat_eq_one, testBit_eq_bitNat_eq_one, hloc_bit] at htb
      rcases bit_cases (β (rClock k)) with hb | hb <;>
        rcases bit_cases (basisBits b (xClockPerm idx (localIdx rClock β)) k) with hb' | hb' <;>
        simp_all [bitNat]
  · have hnot : q ∉ rIdx.image := by
      rw [QRegister.mem_image]; rintro ⟨a, rfl⟩; fin_cases a; exact hqC ⟨idx, rfl⟩
    rw [ReflectionProofs.flipRegBits_apply_of_not_mem _ _ _ hnot,
      writeReg_apply_of_not_mem _ _ _ _ hqC]

private theorem cleanRealizes_cnotClock {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b s : ℕ} (v : Var) (rClock : QRegister b N) (rFull : QRegister s N)
    (hCF : Disjoint rClock.image rFull.image) (i j : Fin b) (hne : i ≠ j) :
    XMeasCircuit.CleanRealizes v rClock rFull (permutationUnitary (cnotClockPerm i j hne))
      (.circuit (Circuit.CNOT (rClock i) (rClock j) (rClock.wires.injective.ne hne))) := by
  have hc := CleanRealizesWires.circuit v rFull.image
    (Circuit.CNOT (rClock i) (rClock j) (rClock.wires.injective.ne hne)) (by simp)
    (by
      rw [Circuit.support_cnot, Finset.disjoint_left]
      intro q hq hqF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.disjoint_left.mp hCF ((QRegister.mem_image rClock _).mpr ⟨i, rfl⟩) hqF
      · exact Finset.disjoint_left.mp hCF ((QRegister.mem_image rClock _).mpr ⟨j, rfl⟩) hqF)
  apply CleanRealizesWires.toCleanRealizes
  refine hc.congr_unitary ?_
    (embedMatrix_comm_zeroProjOn_of_disjoint rClock rFull.image hCF _)
  apply congrArg (· * zeroProjOn rFull.image)
  apply matrix_ext_ket; intro β
  rw [ket_CNOT, embedUnitary_permutationUnitary_mulVec_ket]
  congr 1; funext q
  by_cases hqC : q ∈ Set.range rClock.wires
  · obtain ⟨k, rfl⟩ := hqC
    rw [writeReg_apply_reg]
    have hloc_k : basisBits b (localIdx rClock β) k = β (rClock k) :=
      congrFun (basisBits_basisBitsEquiv_symm (fun a ↦ β (rClock a))) k
    have hloc_i : basisBits b (localIdx rClock β) i = β (rClock i) :=
      congrFun (basisBits_basisBitsEquiv_symm (fun a ↦ β (rClock a))) i
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self]
      apply bit_eq_of_bitNat_eq
      have htb := cnotClockPerm_testBit_tgt i k hne (localIdx rClock β)
      rw [testBit_eq_bitNat_eq_one, testBit_eq_bitNat_eq_one, testBit_eq_bitNat_eq_one,
        hloc_k, hloc_i] at htb
      rcases bit_cases (β (rClock k)) with hbk | hbk <;>
        rcases bit_cases (β (rClock i)) with hbi | hbi <;>
        rcases bit_cases (basisBits b (cnotClockPerm i k hne (localIdx rClock β)) k)
          with hbc | hbc <;>
        simp_all [bitNat]
    · rw [Function.update_of_ne (rClock.wires.injective.ne hkj)]
      apply bit_eq_of_bitNat_eq
      have hne_val : k.val ≠ j.val := fun hv ↦ hkj (Fin.ext hv)
      have htb : (cnotClockPerm i j hne (localIdx rClock β)).val.testBit k.val =
          (localIdx rClock β).val.testBit k.val := by
        dsimp [cnotClockPerm]
        split_ifs
        · simp [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm hne_val)]
        · rfl
      rw [testBit_eq_bitNat_eq_one, testBit_eq_bitNat_eq_one, hloc_k] at htb
      rcases bit_cases (β (rClock k)) with hbk | hbk <;>
        rcases bit_cases (basisBits b (cnotClockPerm i j hne (localIdx rClock β)) k)
          with hbc | hbc <;>
        simp_all [bitNat]
  · have hnej : q ≠ rClock j := fun h ↦ hqC ⟨j, h.symm⟩
    rw [Function.update_of_ne hnej, writeReg_apply_of_not_mem _ _ _ _ hqC]

/-- Polarity-parametric single-clock-wire controlled reflection `R₀`:
applies `refl.inAll` when `testBit idx = pol` using `4 * (aRem - 1)` `T` gates and `0` `.TOFF`. -/
def bitCtrlR0Dyn {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pol : Bool) (idx : Fin bQPE) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  if pol then
    let cX := xRegCirc
      (QRegister.singleton (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb idx))
    .seq (.circuit cX)
      (.seq (lowBitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl idx)
        (.circuit cX))
  else
    lowBitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl idx

@[simp]
theorem bitCtrlR0Dyn_count_toff {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pol : Bool) (idx : Fin bQPE) :
    (bitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl pol idx).count .TOFF = 0 := by
  unfold bitCtrlR0Dyn
  cases pol <;> simp [count_xRegCirc_toff]

@[simp]
theorem bitCtrlR0Dyn_count_t {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pol : Bool) (idx : Fin bQPE) :
    (bitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl pol idx).count .T = 4 * (aRem - 1) := by
  unfold bitCtrlR0Dyn
  cases pol <;> simp [count_xRegCirc_t]

private theorem rClock_disjoint_rFullZeroLoc
    (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    Disjoint (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).image
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image := by
  rw [image_rFullZeroLoc, Finset.disjoint_union_right]
  refine ⟨Finset.disjoint_left.mpr fun q hqC hqS ↦ ?_,
    Finset.disjoint_left.mpr fun q hqC hqA ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hqC
    obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hqS
    exact (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).ne i j hj.symm
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hqC
    obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hqA
    exact (QubitisedWalk.disjointWires_compose_right
      (QubitisedWalk.disjointWires_compose_right
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))).ne i j hj.symm

/-- `CleanRealizes` for `bitCtrlR0Dyn`: applies `R₀` on `inAllWalkCat` iff
`x.val.testBit idx.val == pol`. -/
theorem bitCtrlR0Dyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    (pol : Bool) (idx : Fin bQPE) :
    XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary fun x : Fin (2 ^ bQPE) ↦
        if x.val.testBit idx.val == pol then
          QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
        else 1)
      (bitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl pol idx) := by
  have hlow := lowBitCtrlR0Dyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov idx
  unfold bitCtrlR0Dyn
  cases pol
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    refine cleanRealizes_of_eq2 hlow (congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ ?_))
    cases x.val.testBit idx.val <;> rfl
  · dsimp only [↓reduceIte]
    have hx := cleanRealizes_xClock v
      (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (rClock_disjoint_rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) idx
    have hconj := cleanRealizes_conj_clockPerm
      (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (xClockPerm_involutive idx) hx hlow
    refine cleanRealizes_of_eq2 hconj (congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ ?_))
    rw [xClockPerm_testBit_self, Bool.not_not]
    cases x.val.testBit idx.val <;> rfl

/-- Fused boundary reflection between chunk `k - 1` and chunk `k` (`1 ≤ k ≤ bAct - 1`):
conjugates `bitCtrlR0Dyn` by a temporary `CNOT` on clock wires `k - 1` and `k`, realizing `R₀`
iff `chunkPred (bAct - 1) k y == chunkPred (bAct - 1) (k - 1) y` at cost `4 * (aRem - 1)` `T`
gates (`0` `.TOFF` gates). -/
def boundaryCtrlR0Dyn {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct k : ℕ) (hk1 : 1 ≤ k) (hkw : k ≤ bAct - 1) (hbQPE : bAct ≤ bQPE) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  let rClock := rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let i : Fin bQPE := ⟨k - 1, by omega⟩
  let j : Fin bQPE := ⟨k, by omega⟩
  have hne : i ≠ j := fun h ↦ by have hv := congrArg Fin.val h; dsimp [i, j] at hv; omega
  let cnotClk := Circuit.CNOT (rClock i) (rClock j) (rClock.wires.injective.ne hne)
  .seq (.circuit cnotClk)
    (.seq (bitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl (decide (k = bAct - 1)) j)
      (.circuit cnotClk))

@[simp]
theorem boundaryCtrlR0Dyn_count_toff {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct k : ℕ) (hk1 : 1 ≤ k) (hkw : k ≤ bAct - 1) (hbQPE : bAct ≤ bQPE) :
    (boundaryCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl bAct k hk1 hkw hbQPE).count .TOFF =
      0 := by
  unfold boundaryCtrlR0Dyn
  simp

@[simp]
theorem boundaryCtrlR0Dyn_count_t {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct k : ℕ) (hk1 : 1 ≤ k) (hkw : k ≤ bAct - 1) (hbQPE : bAct ≤ bQPE) :
    (boundaryCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl bAct k hk1 hkw hbQPE).count .T =
      4 * (aRem - 1) := by
  unfold boundaryCtrlR0Dyn
  simp

/-- `CleanRealizes` for `boundaryCtrlR0Dyn`: applies `R₀` iff
`chunkPred (bAct - 1) k y == chunkPred (bAct - 1) (k - 1) y` (equivalently, iff
`!(chunkPred (bAct - 1) k y != chunkPred (bAct - 1) (k - 1) y)`). -/
theorem boundaryCtrlR0Dyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    (bAct k : ℕ) (hk1 : 1 ≤ k) (hkw : k ≤ bAct - 1) (hbQPE : bAct ≤ bQPE) :
    XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary fun y : Fin (2 ^ bQPE) ↦
        if chunkPred (bAct - 1) k y == chunkPred (bAct - 1) (k - 1) y then
          QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
        else 1)
      (boundaryCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl bAct k hk1 hkw hbQPE) := by
  let i : Fin bQPE := ⟨k - 1, by omega⟩
  let j : Fin bQPE := ⟨k, by omega⟩
  have hne : i ≠ j := fun h ↦ by have hv := congrArg Fin.val h; dsimp [i, j] at hv; omega
  have hcnot := cleanRealizes_cnotClock v
    (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
    (rClock_disjoint_rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) i j hne
  have hmid := bitCtrlR0Dyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov
    (decide (k = bAct - 1)) j
  have hconj := cleanRealizes_conj_clockPerm
    (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    (cnotClockPerm_involutive i j hne) hcnot hmid
  unfold boundaryCtrlR0Dyn
  refine cleanRealizes_of_eq2 hconj (congrArg QubitisedWalk.qpeMuxUnitary (funext fun y ↦ ?_))
  rw [cnotClockPerm_testBit_tgt]
  have hprev_lt : k - 1 < bAct - 1 := by omega
  by_cases hkeq : k = bAct - 1
  · subst hkeq
    simp only [i, j, chunkPred, Nat.lt_irrefl, hprev_lt, ↓reduceIte, decide_true]
    cases y.val.testBit (bAct - 1) <;> cases y.val.testBit (bAct - 1 - 1) <;> rfl
  · have hk_lt : k < bAct - 1 := by omega
    simp only [i, j, chunkPred, hkeq, hk_lt, hprev_lt, ↓reduceIte, decide_false]
    cases y.val.testBit k <;> cases y.val.testBit (k - 1) <;> rfl

/-- Endpoint-absorbed `L`-step chunk core (`L - 1` calls to `wStepProg`, followed by `1` call to
`pRefl2`, omitting the trailing unconditional `reflInDyn` so it merges with the next boundary). -/
def chunkCoreDyn {Var : Type} {N : ℕ} (L : ℕ)
    (wStepProg pRefl2 : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (iterBinDyn (L - 1) wStepProg) pRefl2

@[simp]
theorem chunkCoreDyn_count {Var : Type} {N d : ℕ} (L : ℕ)
    (wStepProg pRefl2 : DynamicCircuit Var N) (g : PrimitiveGate d) :
    (chunkCoreDyn L wStepProg pRefl2).count g =
      (L - 1) * wStepProg.count g + pRefl2.count g := by
  simp [chunkCoreDyn]

/-- Open-prefix dihedral loop over chunks `0 .. idx` (`idx < bAct`), leaving an unclosed trailing
factor `(if !(chunkPred (bAct - 1) idx y) then R₀ else 1)` that merges into the next boundary. -/
def prefixOpenDyn {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbQPE : bAct ≤ bQPE)
    (wStepProg pRefl2 :
      DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    (idx : ℕ) → idx < bAct →
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)
  | 0, h0 =>
      .seq
        (bitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl
          (decide (0 < bAct - 1)) ⟨0, by omega⟩)
        (chunkCoreDyn (chunkSize2 (bAct - 1) M 0) wStepProg pRefl2)
  | k' + 1, hk =>
      .seq
        (prefixOpenDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbQPE
          wStepProg pRefl2 k' (by omega))
        (.seq
          (boundaryCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl
            bAct (k' + 1) (by omega) (by omega) hbQPE)
          (chunkCoreDyn (chunkSize2 (bAct - 1) M (k' + 1)) wStepProg pRefl2))

/-- Boundary-fused and endpoint-absorbed dihedral walk body over all `bAct` chunks
(`0 .. bAct - 1`), closed by a single wire-`(bAct - 1)` `pol = true` reflection. -/
def fusedWalkBodyDyn {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  let wStepProg := wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2
  .seq
    (prefixOpenDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbQPE
      wStepProg pRefl2 (bAct - 1) (by omega))
    (bitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl true ⟨bAct - 1, by omega⟩)

/-- **Arbitrary-`M` Affine-Folded & Boundary-Fused Dihedral QPE Walk (`affineDihedralRefl2Dyn`):**
Conjugates `fusedWalkBodyDyn` by the involutive affine clock folding `qpeAffineFoldDyn`,
supporting **every** integer `M` (`2 ^ (bAct - 1) ≤ M < 2 ^ bAct`) with `0` `.TOFF` gates and
at most `≤ 308 T` QPE control + boundary reflection excess for all `M < 2^16` at `aRem = 34`
(`244 T` at `M = 48,895` and `M = 47,871`). -/
def affineDihedralRefl2Dyn {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  let pFold := qpeAffineFoldDyn bQPE bCat mOut mMid mLow sUb v
    (aRem := aRem) (mRem := mRem) bAct M hbAct hbQPE hbScr
  .seq pFold
    (.seq (fusedWalkBodyDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbAct hbQPE pRefl2)
      pFold)

/-- Exact closed-form `T`-gate count of `affineDihedralRefl2Dyn` for `2 ^ (bAct - 1) ≤ M`:
`2 * ctrlAddConstModTCount (bAct - 1) (M + 1 - 2 ^ (bAct - 1))` (affine clock folding/unfolding)
`+ M * tRefl2` (`M` inner reflections)
`+ (M - bAct) * (4 * (aRem - 2))` (`M - bAct` unconditional `reflInDyn` calls)
`+ (bAct + 1) * (4 * (aRem - 1))` (`bAct + 1` single-wire controlled `R₀` boundaries). -/
abbrev walkCtrlTCount (bAct M aRem tRefl2 : ℕ) : ℕ :=
  2 * ctrlAddConstModTCount (bAct - 1) (M + 1 - 2 ^ (bAct - 1)) +
    M * tRefl2 + (M - bAct) * (4 * (aRem - 2)) + (bAct + 1) * (4 * (aRem - 1))

private theorem prefixOpenDyn_count_toff {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbQPE : bAct ≤ bQPE)
    (wStepProg pRefl2 :
      DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb))
    (hw : wStepProg.count .TOFF = 0) (hp : pRefl2.count .TOFF = 0)
    (idx : ℕ) (hidx : idx < bAct) :
    (prefixOpenDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbQPE
      wStepProg pRefl2 idx hidx).count .TOFF = 0 := by
  induction idx with
  | zero =>
    unfold prefixOpenDyn
    simp [hw, hp]
  | succ k' ih =>
    unfold prefixOpenDyn
    simp [ih (by omega), hw, hp]

private theorem chunk_core_t_eq (L tR aRem : ℕ) (hL : 1 ≤ L) :
    (L - 1) * (tR + 4 * (aRem - 2)) + tR = L * tR + (L - 1) * (4 * (aRem - 2)) := by
  obtain ⟨d, rfl⟩ : ∃ d, L = d + 1 := ⟨L - 1, by omega⟩
  set c2 := 4 * (aRem - 2)
  simp only [Nat.add_sub_cancel]
  ring

private theorem prefixOpenDyn_count_t {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbQPE : bAct ≤ bQPE) (hMlo : 2 ^ (bAct - 1) ≤ M)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb))
    (idx : ℕ) (hidx : idx < bAct) :
    let wStepProg := wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2
    (prefixOpenDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbQPE
      wStepProg pRefl2 idx hidx).count .T =
      (∑ j ∈ Finset.range (idx + 1), chunkSize2 (bAct - 1) M j) * pRefl2.count .T +
      ((∑ j ∈ Finset.range (idx + 1), chunkSize2 (bAct - 1) M j) - (idx + 1)) *
        (4 * (aRem - 2)) +
      (idx + 1) * (4 * (aRem - 1)) := by
  intro wStepProg
  have hsum_ge : ∀ m : ℕ, m ≤ ∑ j ∈ Finset.range m, chunkSize2 (bAct - 1) M j := by
    intro m
    induction m with
    | zero => simp
    | succ m' ihm =>
      rw [Finset.sum_range_succ]
      have := chunkSize_pos hMlo m'
      omega
  induction idx with
  | zero =>
    unfold prefixOpenDyn
    rw [Nat.zero_add, Finset.sum_range_one]
    simp only [DynamicCircuit.count, bitCtrlR0Dyn_count_t, chunkCoreDyn_count,
      wStepProg, wStepRefl2Dyn_count_t]
    have hL0 := chunkSize_pos hMlo 0
    rw [chunk_core_t_eq _ _ _ hL0]
    set P0 := chunkSize2 (bAct - 1) M 0 * pRefl2.count .T
    set D0 := (chunkSize2 (bAct - 1) M 0 - 1) * (4 * (aRem - 2))
    omega
  | succ k' ih =>
    unfold prefixOpenDyn
    simp only [DynamicCircuit.count, ih (by omega), boundaryCtrlR0Dyn_count_t,
      chunkCoreDyn_count, wStepProg, wStepRefl2Dyn_count_t]
    rw [Finset.sum_range_succ _ (k' + 1)]
    set S := ∑ j ∈ Finset.range (k' + 1), chunkSize2 (bAct - 1) M j
    set L := chunkSize2 (bAct - 1) M (k' + 1)
    have hS : k' + 1 ≤ S := hsum_ge (k' + 1)
    have hL : 1 ≤ L := chunkSize_pos hMlo (k' + 1)
    have hLmul := chunk_core_t_eq L (pRefl2.count .T) aRem hL
    have hsub1 : (S - (k' + 1)) + (L - 1) = (S + L) - (k' + 1 + 1) := by omega
    rw [hLmul, ← hsub1]
    set D := S - (k' + 1)
    set E := L - 1
    set c2 := 4 * (aRem - 2)
    set c1 := 4 * (aRem - 1)
    ring

/-- `.TOFF = 0` for `affineDihedralRefl2Dyn` whenever `pRefl2.count .TOFF = 0`. -/
@[simp]
theorem affineDihedralRefl2Dyn_count_toff {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb))
    (hRefl2 : pRefl2.count .TOFF = 0) :
    (affineDihedralRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl bAct M
      hbAct hbQPE hbScr pRefl2).count .TOFF = 0 := by
  unfold affineDihedralRefl2Dyn fusedWalkBodyDyn
  have hw : (wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2).count .TOFF = 0 :=
    (wStepRefl2Dyn_count_toff bQPE bCat mOut mMid mLow sUb v refl pRefl2).trans hRefl2
  simp [prefixOpenDyn_count_toff bQPE bCat mOut mMid mLow sUb v refl bAct M hbQPE _ _
    hw hRefl2 (bAct - 1) (by omega)]

/-- Exact `T`-count of `affineDihedralRefl2Dyn` for every `M ≥ 2 ^ (bAct - 1)`. -/
theorem affineDihedralRefl2Dyn_count_t {Var : Type}
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE) (hMlo : 2 ^ (bAct - 1) ≤ M)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    (affineDihedralRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl bAct M
      hbAct hbQPE hbScr pRefl2).count .T =
      walkCtrlTCount bAct M aRem (pRefl2.count .T) := by
  unfold affineDihedralRefl2Dyn fusedWalkBodyDyn walkCtrlTCount
  have hp := prefixOpenDyn_count_t bQPE bCat mOut mMid mLow sUb v refl bAct M
    hbQPE hMlo pRefl2 (bAct - 1) (by omega)
  have h1 : bAct - 1 + 1 = bAct := by omega
  have hsum : ∑ j ∈ Finset.range bAct, chunkSize2 (bAct - 1) M j = M :=
    (Fin.sum_univ_eq_sum_range (fun j ↦ chunkSize2 (bAct - 1) M j) bAct).symm.trans
      (sumChunkSize_eq hbAct hMlo)
  simp only [DynamicCircuit.count, qpeAffineFoldDyn_count_t, bitCtrlR0Dyn_count_t]
  dsimp only at hp
  rw [hp, h1, hsum]
  set C := ctrlAddConstModTCount (bAct - 1) (M + 1 - 2 ^ (bAct - 1))
  set D := M - bAct
  set c2 := 4 * (aRem - 2)
  set c1 := 4 * (aRem - 1)
  ring

/-- Multiplexed chunk-product fiber over chunks `0 .. n - 1` (`0 ≤ n ≤ bAct`) in the folded clock
basis `y`. -/
noncomputable def chunksFiber {bQPE d : ℕ} (w M : ℕ) (W R : Unitary d) :
    ℕ → Fin (2 ^ bQPE) → Unitary d
  | 0, _ => 1
  | k + 1, y =>
      chunkFiberStep (chunkPred w k) (chunkSize2 w M k) W R y * chunksFiber w M W R k y

/-- Full affine-folded dihedral multiplexer fiber `y = qpeAffinePerm bAct bQPE M m`:
applies `chunksFiber (bAct - 1) M W R bAct (qpeAffinePerm bAct bQPE M m)`. -/
noncomputable def affineScheduleFiber {bQPE d : ℕ}
    (bAct M : ℕ) (W R : Unitary d) (m : Fin (2 ^ bQPE)) : Unitary d :=
  chunksFiber (bAct - 1) M W R bAct (qpeAffinePerm bAct bQPE M m)

private theorem embedUnitary_pow {k N : ℕ} (r : QRegister k N) (U : Unitary (2 ^ k)) (m : ℕ) :
    r.embedUnitary (U ^ m) = r.embedUnitary U ^ m := by
  induction m with
  | zero => simp [_root_.pow_zero]
  | succ m' ih => rw [pow_succ, pow_succ, QRegister.embedUnitary_mul, ih]

theorem embedUnitaryChunksFiber {bQPE k N : ℕ} (r : QRegister k N)
    (w M : ℕ) (W R : Unitary (2 ^ k)) (n : ℕ) (y : Fin (2 ^ bQPE)) :
    r.embedUnitary (chunksFiber w M W R n y) =
      chunksFiber w M (r.embedUnitary W) (r.embedUnitary R) n y := by
  induction n with
  | zero => simp [chunksFiber]
  | succ k' ih =>
    simp only [chunksFiber, QRegister.embedUnitary_mul, ih]
    dsimp [chunkFiberStep]
    split_ifs <;> simp [embedUnitary_pow]

theorem embedUnitaryAffineScheduleFiber {bQPE k N : ℕ} (r : QRegister k N)
    (bAct M : ℕ) (W R : Unitary (2 ^ k)) (m : Fin (2 ^ bQPE)) :
    r.embedUnitary (affineScheduleFiber bAct M W R m) =
      affineScheduleFiber bAct M (r.embedUnitary W) (r.embedUnitary R) m :=
  embedUnitaryChunksFiber r (bAct - 1) M W R bAct (qpeAffinePerm bAct bQPE M m)

/-- Endpoint-absorption algebraic identity in any monoid with `R * R = 1` (requiring **no**
involution assumption on `V`!):
`(R * V) ^ (L - 1)` followed by `V` (i.e. `V * (R * V) ^ (L - 1)`) equals `R * (R * V) ^ L`, so
pre-multiplying an incoming `(if pred y then R else 1)` produces
`(if !pred y then R else 1) * chunkFiberStep pred L (R * V) R y`. -/
theorem chunk_core_endpoint_absorb {G : Type*} [Monoid G] {R V : G}
    (hR : R * R = 1) {L : ℕ} (hL : 1 ≤ L) (b : Bool) :
    (V * (R * V) ^ (L - 1)) * (if b then R else 1) =
      (if !b then R else 1) * (if b then R * (R * V) ^ L * R else (R * V) ^ L) := by
  have hpow : (R * V) ^ L = (R * V) * (R * V) ^ (L - 1) := by
    conv_lhs => rw [show L = (L - 1) + 1 by omega, pow_succ']
  have hcore : V * (R * V) ^ (L - 1) = R * (R * V) ^ L := by
    rw [hpow, ← mul_assoc, ← mul_assoc, hR, one_mul]
  rw [hcore]
  cases b
  · simp [mul_one]
  · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, one_mul, mul_assoc]

private theorem cleanRealizes_walkOnCombined {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b k s : ℕ} {v : Var}
    {rClock : QRegister b N} {rWalk : QRegister k N} (hCW : rClock.DisjointWires rWalk)
    {rFull : QRegister s N} {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hP : XMeasCircuit.CleanRealizes v rWalk rFull U P) :
    XMeasCircuit.CleanRealizes v (rClock.concat rWalk hCW) rFull
      (QubitisedWalk.qpeMuxUnitary (fun _ : Fin (2 ^ b) ↦ U)) P := by
  refine cleanRealizes_of_eq2 (XMeasCircuit.CleanRealizes.liftActiveOfEq
    (QubitisedWalk.concat_compose_walkInCombined rClock rWalk hCW).symm hP) ?_
  apply Subtype.ext
  rw [QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val]
  dsimp only [QubitisedWalk.qpeMuxMatrix]
  rw [← Finset.sum_mul, (QubitisedWalk.qpeInCombined b k).sum_basisOutcomeProjector, Matrix.one_mul]

private theorem chunkCoreDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    {uRefl2 : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (hRefl2 : XMeasCircuit.CleanRealizes v (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) uRefl2 pRefl2)
    (L : ℕ) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    let wStepProg := wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2
    XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (fun _ : Fin (2 ^ bQPE) ↦ uRefl2 * (R₀ * uRefl2) ^ (L - 1)))
      (chunkCoreDyn L wStepProg pRefl2) := by
  intro R₀ wStepProg
  have hW := wStepRefl2Dyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov hRefl2
  have hIter := cleanRealizes_iterBinDyn hW (L - 1)
  have hCoreWalk : XMeasCircuit.CleanRealizes v
      (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (uRefl2 * (R₀ * uRefl2) ^ (L - 1))
      (chunkCoreDyn L wStepProg pRefl2) :=
    hIter.seq hRefl2
  exact cleanRealizes_walkOnCombined
    (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb) hCoreWalk

private theorem prefixOpenDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    (bAct M : ℕ) (hbQPE : bAct ≤ bQPE) (hMlo : 2 ^ (bAct - 1) ≤ M)
    {uRefl2 : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (hRefl2 : XMeasCircuit.CleanRealizes v (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) uRefl2 pRefl2)
    (idx : ℕ) (hidx : idx < bAct) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    let wStepProg := wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2
    XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary fun y : Fin (2 ^ bQPE) ↦
        (if !(chunkPred (bAct - 1) idx y) then R₀ else 1) *
          chunksFiber (bAct - 1) M (R₀ * uRefl2) R₀ (idx + 1) y)
      (prefixOpenDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbQPE
        wStepProg pRefl2 idx hidx) := by
  intro R₀ wStepProg
  have hR₀ : R₀ * R₀ = 1 := QubitisedWalk.reflInUnitary_mul_self (inAllWalkCat bCat mOut mMid)
  induction idx with
  | zero =>
    unfold prefixOpenDyn
    have h0 := bitCtrlR0Dyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov
      (decide (0 < bAct - 1)) ⟨0, by omega⟩
    have hc := chunkCoreDyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov hRefl2
      (chunkSize2 (bAct - 1) M 0)
    refine cleanRealizes_of_eq2 (h0.seq hc) ?_
    rw [← QubitisedWalk.qpeMuxUnitary_mul]
    apply congrArg QubitisedWalk.qpeMuxUnitary; funext y
    have hp0 : (y.val.testBit 0 == decide (0 < bAct - 1)) = chunkPred (bAct - 1) 0 y := by
      dsimp [chunkPred]
      by_cases hw : 0 < bAct - 1
      · simp [hw]
      · have hw0 : bAct - 1 = 0 := by omega
        simp [hw0]
    simp only [hp0, chunksFiber, mul_one, chunkFiberStep]
    exact chunk_core_endpoint_absorb hR₀ (chunkSize_pos hMlo 0) (chunkPred (bAct - 1) 0 y)
  | succ k' ih =>
    unfold prefixOpenDyn
    have hprev := ih (by omega)
    have hbnd := boundaryCtrlR0Dyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov
      bAct (k' + 1) (by omega) (by omega) hbQPE
    have hc := chunkCoreDyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov hRefl2
      (chunkSize2 (bAct - 1) M (k' + 1))
    refine cleanRealizes_of_eq2 (hprev.seq (hbnd.seq hc)) ?_
    rw [← QubitisedWalk.qpeMuxUnitary_mul, ← QubitisedWalk.qpeMuxUnitary_mul]
    apply congrArg QubitisedWalk.qpeMuxUnitary; funext y
    have hmerge :
        (if chunkPred (bAct - 1) (k' + 1) y == chunkPred (bAct - 1) k' y then R₀ else 1) *
          (if !(chunkPred (bAct - 1) k' y) then R₀ else 1) =
        if chunkPred (bAct - 1) (k' + 1) y then R₀ else 1 := by
      cases chunkPred (bAct - 1) (k' + 1) y <;>
        cases chunkPred (bAct - 1) k' y <;>
        simp [hR₀]
    have habs := chunk_core_endpoint_absorb (V := uRefl2) hR₀
      (chunkSize_pos hMlo (k' + 1)) (chunkPred (bAct - 1) (k' + 1) y)
    simp only [Nat.add_sub_cancel, chunksFiber, chunkFiberStep]
    calc (uRefl2 * (R₀ * uRefl2) ^ (chunkSize2 (bAct - 1) M (k' + 1) - 1) *
            (if chunkPred (bAct - 1) (k' + 1) y == chunkPred (bAct - 1) k' y then
              R₀ else 1)) *
          ((if !(chunkPred (bAct - 1) k' y) then R₀ else 1) *
            chunksFiber (bAct - 1) M (R₀ * uRefl2) R₀ (k' + 1) y)
        = ((uRefl2 * (R₀ * uRefl2) ^ (chunkSize2 (bAct - 1) M (k' + 1) - 1)) *
            ((if chunkPred (bAct - 1) (k' + 1) y == chunkPred (bAct - 1) k' y then
                R₀ else 1) *
              (if !(chunkPred (bAct - 1) k' y) then R₀ else 1))) *
          chunksFiber (bAct - 1) M (R₀ * uRefl2) R₀ (k' + 1) y := by
          simp only [mul_assoc]
      _ = ((uRefl2 * (R₀ * uRefl2) ^ (chunkSize2 (bAct - 1) M (k' + 1) - 1)) *
            (if chunkPred (bAct - 1) (k' + 1) y then R₀ else 1)) *
          chunksFiber (bAct - 1) M (R₀ * uRefl2) R₀ (k' + 1) y := by rw [hmerge]
      _ = (if !(chunkPred (bAct - 1) (k' + 1) y) then R₀ else 1) *
            ((if chunkPred (bAct - 1) (k' + 1) y then
                R₀ * (R₀ * uRefl2) ^ chunkSize2 (bAct - 1) M (k' + 1) * R₀
              else (R₀ * uRefl2) ^ chunkSize2 (bAct - 1) M (k' + 1)) *
            chunksFiber (bAct - 1) M (R₀ * uRefl2) R₀ (k' + 1) y) := by
          rw [habs, mul_assoc]

/-- **`CleanRealizes` for `affineDihedralRefl2Dyn`:**
Realizes `QubitisedWalk.qpeMuxUnitary (affineScheduleFiber bAct M (R₀ * uRefl2) R₀)` on
`(rQPELoc.concat rWalkCatLoc, rFullZeroLoc)` for any `uRefl2` (not assumed involutive!). -/
theorem affineDihedralRefl2Dyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    (bAct M : ℕ) (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE) (hMlo : 2 ^ (bAct - 1) ≤ M)
    (hbScr : bAct - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb)
    {uRefl2 : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (hRefl2 : XMeasCircuit.CleanRealizes v (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) uRefl2 pRefl2) :
    XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary
        (affineScheduleFiber bAct M
          (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) * uRefl2)
          (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid))))
      (affineDihedralRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl bAct M
        hbAct hbQPE hbScr pRefl2) := by
  let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
  have hBody : XMeasCircuit.CleanRealizes v
      ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
        (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (chunksFiber (bAct - 1) M (R₀ * uRefl2) R₀ bAct))
      (fusedWalkBodyDyn bQPE bCat mOut mMid mLow sUb v refl bAct M hbAct hbQPE pRefl2) := by
    unfold fusedWalkBodyDyn
    have hopen := prefixOpenDyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov
      bAct M hbQPE hMlo hRefl2 (bAct - 1) (by omega)
    have hclose := bitCtrlR0Dyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v hCov
      true ⟨bAct - 1, by omega⟩
    refine cleanRealizes_of_eq2 (hopen.seq hclose) ?_
    rw [← QubitisedWalk.qpeMuxUnitary_mul]
    apply congrArg QubitisedWalk.qpeMuxUnitary; funext y
    have h1 : bAct - 1 + 1 = bAct := by omega
    have hpred_top : (!chunkPred (bAct - 1) (bAct - 1) y) = y.val.testBit (bAct - 1) := by
      dsimp [chunkPred]
      rw [ite_eq_right (Nat.lt_irrefl _), Bool.not_not]
    have hbeq : (y.val.testBit (bAct - 1) == true) = y.val.testBit (bAct - 1) := by
      cases y.val.testBit (bAct - 1) <;> rfl
    dsimp only [R₀] at hopen ⊢
    simp only [hbeq, hpred_top, h1]
    cases y.val.testBit (bAct - 1)
    · simp
    · simp only [↓reduceIte, ← mul_assoc, QubitisedWalk.reflInUnitary_mul_self, one_mul]
  have hFold := qpeAffineFoldDyn_cleanRealizes bQPE bCat mOut mMid mLow sUb v
    (aRem := aRem) (mRem := mRem) rAncZero bAct M hbAct hbQPE hbScr
  exact cleanRealizes_conj_clockPerm
    (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    (qpeAffinePerm_involutive bAct bQPE M) hFold hBody

private theorem chunkFiberStep_eq_zpow {bQPE d : ℕ}
    {R₁ R₂ : Unitary d} (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1)
    (pred : Fin (2 ^ bQPE) → Bool) (L : ℕ) (y : Fin (2 ^ bQPE)) :
    chunkFiberStep pred L (R₁ * R₂) R₁ y =
      (R₁ * R₂) ^ ((if pred y then -(1 : ℤ) else 1) * (L : ℤ)) := by
  dsimp [chunkFiberStep]
  cases hp : pred y with
  | false => simp [one_mul, _root_.zpow_natCast]
  | true =>
    have hR₁_mul (X : Unitary d) : R₁ * (R₁ * X) = X := by
      rw [← mul_assoc, hR₁, one_mul]
    have hconj : R₁ * (R₁ * R₂) ^ L * R₁ = (R₁ * (R₁ * R₂) * R₁) ^ L := by
      induction L with
      | zero => simp [hR₁]
      | succ n ih =>
        rw [pow_succ, pow_succ, ← ih]
        simp only [mul_assoc, hR₁_mul]
    simp only [↓reduceIte, hconj, QubitisedWalk.conj_walk_eq_inv hR₁ hR₂,
      neg_one_mul, _root_.zpow_neg, _root_.zpow_natCast, inv_pow]

private theorem chunksFiber_eq_zpow {bQPE d : ℕ}
    {R₁ R₂ : Unitary d} (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1)
    (w M n : ℕ) (y : Fin (2 ^ bQPE)) :
    chunksFiber w M (R₁ * R₂) R₁ n y =
      (R₁ * R₂) ^
        (∑ j ∈ Finset.range n,
          (if chunkPred w j y then -(1 : ℤ) else 1) * (chunkSize2 w M j : ℤ)) := by
  induction n with
  | zero => simp [chunksFiber]
  | succ k ih =>
    rw [chunksFiber, chunkFiberStep_eq_zpow hR₁ hR₂, ih, ← _root_.zpow_add,
      Finset.sum_range_succ, add_comm]

/-- **Ideal Arbitrary-`M` Dihedral Exponent Identity:**
For every `m : Fin (2 ^ bQPE)` with `m.val ≤ M`
(`1 ≤ bAct ≤ bQPE`, `2 ^ (bAct - 1) ≤ M < 2 ^ bAct`),
`affineScheduleFiber bAct M (R₁ * R₂) R₁ m = (R₁ * R₂) ^ (2 * m.val - M)`. -/
theorem affineScheduleFiber_ideal_eq_zpow {bQPE d : ℕ}
    {R₁ R₂ : Unitary d} (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1)
    {bAct M : ℕ} (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE)
    (hMlo : 2 ^ (bAct - 1) ≤ M) (hMhi : M < 2 ^ bAct)
    {m : Fin (2 ^ bQPE)} (hm : m.val ≤ M) :
    affineScheduleFiber bAct M (R₁ * R₂) R₁ m =
      (R₁ * R₂) ^ (2 * (m.val : ℤ) - (M : ℤ)) := by
  unfold affineScheduleFiber
  rw [chunksFiber_eq_zpow hR₁ hR₂, ← Fin.sum_univ_eq_sum_range]
  have hsign (j : Fin bAct) :
      (if chunkPred (bAct - 1) j.val (qpeAffinePerm bAct bQPE M m) then -(1 : ℤ) else 1) =
        if ¬ chunkPred (bAct - 1) j.val (qpeAffinePerm bAct bQPE M m) then
          (1 : ℤ) else -1 := by
    cases chunkPred (bAct - 1) j.val (qpeAffinePerm bAct bQPE M m) <;> simp
  simp_rw [hsign]
  exact congrArg ((R₁ * R₂) ^ ·)
    (affine_folded_dihedral_exponent_eq hbAct hbQPE hMlo hMhi hm)

private theorem embedUnitary_rWalkInWalkCat_reflIn2 (bCat mOut mMid : ℕ) :
    QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)) := by
  apply Subtype.ext
  change (2 : ℂ) • (inAllWalkCat bCat mOut mMid).basisOutcomeProjector 0 - 1 =
    (rWalkInWalkCat bCat mOut mMid).embedMatrix
      ((2 : ℂ) • (rAllInWalk mOut mMid).basisOutcomeProjector 0 - 1)
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    inAllWalkCat, CleanDyn.compose_basisOutcomeProjector]

private theorem embedUnitary_rWalkInWalkCat_reflMid2 (bCat mOut mMid : ℕ) :
    QubitisedWalk.reflMidUnitary (inMidWalkCat bCat mOut mMid) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflMidUnitary (rMidInWalk mOut mMid)) := by
  apply Subtype.ext
  change 1 - (2 : ℂ) • (inMidWalkCat bCat mOut mMid).basisOutcomeProjector 0 =
    (rWalkInWalkCat bCat mOut mMid).embedMatrix
      (1 - (2 : ℂ) • (rMidInWalk mOut mMid).basisOutcomeProjector 0)
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    inMidWalkCat, CleanDyn.compose_basisOutcomeProjector]

private theorem embedUnitary_rWalkInWalkCat_reflPulled2 (bCat mOut mMid : ℕ)
    (uB : Unitary (2 ^ walkWidth mOut mMid)) :
    QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid)
        ((rWalkInWalkCat bCat mOut mMid).embedUnitary uB) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB) := by
  dsimp [QubitisedWalk.reflPulledUnitary, QubitisedWalk.reflPulledPair]
  rw [embedUnitary_rWalkInWalkCat_reflMid2, ← QRegister.embedUnitary_inv,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]

end BoundaryFusedDihedralWalk

/-! ## Section 4: Parametric Master Programs, Gate Counts & Turnkey Correctness Theorems -/

section MasterIntegration

open WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge

/-- Ideal 4-stage blocked-basis active unitary for the two-reflection walk schedule. -/
noncomputable def blockedIdealUnitary (bQPE bCat mOut mMid bAct M : ℕ)
    (uCatIdeal : Unitary (2 ^ bCat))
    (uB : Unitary (2 ^ walkWidth mOut mMid))
    (uWinIdeal uIqftIdeal : Unitary (2 ^ bQPE)) :
    Unitary (2 ^ actWidth bQPE bCat mOut mMid) :=
  (rQPEInAct bQPE bCat mOut mMid).embedUnitary uIqftIdeal *
    ((rQPEInAct bQPE bCat mOut mMid).concat (rWalkCatInAct bQPE bCat mOut mMid)
      (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary
        (affineScheduleFiber bAct M
          (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) *
            QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid)
              ((rWalkInWalkCat bCat mOut mMid).embedUnitary uB))
          (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)))) *
    (rQPEInAct bQPE bCat mOut mMid).embedUnitary uWinIdeal *
    (rCatInAct bQPE bCat mOut mMid).embedUnitary uCatIdeal

private theorem inner_tensorWalkCat2 {bCat mOut mMid : ℕ}
    (u₁ u₂ : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    (∑ x : Fin (2 ^ walkCatWidth bCat mOut mMid),
      star (tensorWalkCat u₁ cat x) * tensorWalkCat u₂ cat x) =
      QubitisedWalk.vecInner u₁ u₂ * ∑ c : Fin (2 ^ bCat), star (cat c) * cat c := by
  let f : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ := fun x ↦
    star (tensorWalkCat u₁ cat x) * tensorWalkCat u₂ cat x
  rw [show (∑ x, star (tensorWalkCat u₁ cat x) * tensorWalkCat u₂ cat x) = ∑ x, f x from rfl,
    ← (BlockEncodingCore.splitBlockEquiv (walkWidth mOut mMid) bCat).symm.sum_comp f,
    Fintype.sum_prod_type]
  dsimp [QubitisedWalk.vecInner, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  let x := (BlockEncodingCore.splitBlockEquiv (walkWidth mOut mMid) bCat).symm (a, c)
  have hfst : (rWalkInWalkCat bCat mOut mMid).extractIndex x = a := by
    rw [← BlockEncodingCore.splitBlockEquiv_fst, Equiv.apply_symm_apply]
  have hsnd : (rCatInWalkCat bCat mOut mMid).extractIndex x = c := by
    rw [← BlockEncodingCore.splitBlockEquiv_snd, Equiv.apply_symm_apply]
  dsimp [f, tensorWalkCat]
  change star (u₁ ((rWalkInWalkCat bCat mOut mMid).extractIndex x) *
      cat ((rCatInWalkCat bCat mOut mMid).extractIndex x)) *
    (u₂ ((rWalkInWalkCat bCat mOut mMid).extractIndex x) *
      cat ((rCatInWalkCat bCat mOut mMid).extractIndex x)) = _
  rw [hfst, hsnd]
  simp only [star_mul, Complex.star_def]
  ring

private def actSplitEquiv2 (bQPE bCat mOut mMid : ℕ) :
    Fin (2 ^ actWidth bQPE bCat mOut mMid) ≃
      Fin (2 ^ walkCatWidth bCat mOut mMid) × Fin (2 ^ bQPE) :=
  (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid))).trans
    (BlockEncodingCore.splitBlockEquiv (walkCatWidth bCat mOut mMid) bQPE)

private theorem actSplitEquiv_fst2 (bQPE bCat mOut mMid : ℕ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    (actSplitEquiv2 bQPE bCat mOut mMid g).1 =
      (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g := by
  apply (basisBits (walkCatWidth bCat mOut mMid)).injective
  funext i
  have h1 := congrFun (congrArg (basisBits (walkCatWidth bCat mOut mMid))
    (BlockEncodingCore.splitBlockEquiv_fst (walkCatWidth bCat mOut mMid) bQPE
      (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid)) g))) i
  dsimp only [actSplitEquiv2, Equiv.trans_apply]
  rw [h1]
  change basisBits _ _ i = basisBits _ _ i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]
  simp [finCongr, TopIntegrationBridge.rWalkCatInAct]

private theorem actSplitEquiv_snd2 (bQPE bCat mOut mMid : ℕ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    (actSplitEquiv2 bQPE bCat mOut mMid g).2 =
      (rQPEInAct bQPE bCat mOut mMid).extractIndex g := by
  apply (basisBits bQPE).injective
  funext j
  have h2 := congrFun (congrArg (basisBits bQPE)
    (BlockEncodingCore.splitBlockEquiv_snd (walkCatWidth bCat mOut mMid) bQPE
      (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid)) g))) j
  dsimp only [actSplitEquiv2, Equiv.trans_apply]
  rw [h2]
  change basisBits _ _ j = basisBits _ _ j
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]
  dsimp only [TopIntegrationBridge.rQPEInAct, QRegister.block]
  by_cases hb : g.val.testBit (walkCatWidth bCat mOut mMid + j.val) <;> simp [finCongr, hb]

private noncomputable def tensorWCQPE2 {bQPE bCat mOut mMid : ℕ}
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    Fin (2 ^ actWidth bQPE bCat mOut mMid) → ℂ :=
  fun g ↦ wc ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
    q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)

private theorem embedMatrix_mulVec_apply_replaceIndex_4 {k n : ℕ} (r : QRegister k n)
    (A : Operator (2 ^ k)) (state : Fin (2 ^ n) → ℂ) (output : Fin (2 ^ n)) :
    (r.embedMatrix A *ᵥ state) output =
      ∑ a : Fin (2 ^ k), A (r.extractIndex output) a * state (r.replaceIndex output a) :=
  r.embedMatrix_mulVec_apply A state output

private theorem embedMatrix_rWalkCatInAct_mulVec2 {bQPE bCat mOut mMid : ℕ}
    (A : Operator (2 ^ walkCatWidth bCat mOut mMid))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ((rWalkCatInAct bQPE bCat mOut mMid).embedMatrix A) *ᵥ tensorWCQPE2 wc q =
      tensorWCQPE2 (A *ᵥ wc) q := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex_4]
  have hstep :
      (∑ u : Fin (2 ^ walkCatWidth bCat mOut mMid),
        A ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) u *
          tensorWCQPE2 wc q ((rWalkCatInAct bQPE bCat mOut mMid).replaceIndex g u)) =
      ∑ u : Fin (2 ^ walkCatWidth bCat mOut mMid),
        (A ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) u * wc u) *
          q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tensorWCQPE2]
    have hq :
        (rQPEInAct bQPE bCat mOut mMid).extractIndex
            ((rWalkCatInAct bQPE bCat mOut mMid).replaceIndex g u) =
          (rQPEInAct bQPE bCat mOut mMid).extractIndex g :=
      (rQPEInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
        (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid) g u
    rw [hq, QRegister.extractIndex_replaceIndex, mul_assoc]
  rw [hstep, ← Finset.sum_mul]
  rfl

private theorem embedMatrix_rQPEInAct_mulVec2 {bQPE bCat mOut mMid : ℕ}
    (B : Operator (2 ^ bQPE))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ((rQPEInAct bQPE bCat mOut mMid).embedMatrix B) *ᵥ tensorWCQPE2 wc q =
      tensorWCQPE2 wc (B *ᵥ q) := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex_4]
  have hstep :
      (∑ u : Fin (2 ^ bQPE),
        B ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) u *
          tensorWCQPE2 wc q ((rQPEInAct bQPE bCat mOut mMid).replaceIndex g u)) =
      wc ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
        ∑ u : Fin (2 ^ bQPE), B ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) u * q u := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tensorWCQPE2]
    have hwc :
        (rWalkCatInAct bQPE bCat mOut mMid).extractIndex
            ((rQPEInAct bQPE bCat mOut mMid).replaceIndex g u) =
          (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g :=
      (rWalkCatInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
        (QRegister.disjoint_comm.mp (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)) g u
    rw [hwc, QRegister.extractIndex_replaceIndex]
    ring
  rw [hstep]
  rfl

private theorem embed_qpeMuxUnitary_mulVec_3 {bQPE bCat mOut mMid : ℕ}
    (F : Fin (2 ^ bQPE) → Unitary (2 ^ walkCatWidth bCat mOut mMid))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    ((((rQPEInAct bQPE bCat mOut mMid).concat (rWalkCatInAct bQPE bCat mOut mMid)
        (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)).embedUnitary
          (QubitisedWalk.qpeMuxUnitary F)).1 *ᵥ tensorWCQPE2 wc q) g =
      ((F ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)).1 *ᵥ wc)
          ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
        q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) := by
  rw [QubitisedWalk.embed_qpeMuxUnitary_mulVec, Finset.sum_apply,
    Finset.sum_eq_single ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)]
  · rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_left rfl, QRegister.embedUnitary_val,
      embedMatrix_rWalkCatInAct_mulVec2]
    rfl
  · intro m _ hm
    rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_right (Ne.symm hm)]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem sysAct_tensorState_zero_eq2 {bQPE bCat mOut mMid : ℕ}
    (ψ : Fin (2 ^ systemQubits_local) → ℂ) :
    let sys : QRegister systemQubits_local (actWidth bQPE bCat mOut mMid) :=
      .block 0 systemQubits_local (by dsimp [actWidth]; omega)
    let e₁ := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
    sys.tensorState ψ (Pi.single 0 1) =
      tensorWCQPE2 (tensorWalkCat e₁ (basisState (0 : Fin (2 ^ bCat))))
        (basisState 0) := by
  intro sys e₁
  funext g
  let xwc := (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g
  let xw := (rWalkInWalkCat bCat mOut mMid).extractIndex xwc
  have hsys_eq : sys.extractIndex g = (rSysInWalk mOut mMid).extractIndex xw := by
    dsimp only [xw, xwc]
    rw [← QRegister.extractIndex_compose, ← QRegister.extractIndex_compose]
    congr 1; ext i; simp [sys, TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat, rSysInWalk]
  have hbits_iff :
      ((sys.basisSplitEquiv g).2 = 0) ↔
        (((rSysInWalk mOut mMid).basisSplitEquiv xw).2 = 0 ∧
          (rCatInWalkCat bCat mOut mMid).extractIndex xwc = 0 ∧
          (rQPEInAct bQPE bCat mOut mMid).extractIndex g = 0) := by
    rw [CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
      CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
    constructor
    · intro h
      have hzero (w : Wire (actWidth bQPE bCat mOut mMid)) (hw : systemQubits_local ≤ w.val) :
          basisBits (actWidth bQPE bCat mOut mMid) g w = 0 := by
        have hnot : w ∉ Set.range sys.wires := by
          rintro ⟨i, rfl⟩; simp [sys] at hw; omega
        exact congrFun h ⟨w, hnot⟩
      refine ⟨?_, fun i ↦ ?_, fun j ↦ hzero _ (by
        simp [TopIntegrationBridge.rQPEInAct, walkCatWidth, walkWidth, systemQubits_local]; omega)⟩
      · funext ⟨w, hw⟩
        have hge : systemQubits_local ≤ w.val := by
          by_contra hlt; push Not at hlt
          exact hw ⟨⟨w.val, hlt⟩, by ext; simp [rSysInWalk]⟩
        simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply, xw, xwc,
          QRegister.basisBits_extractIndex]
        exact hzero _ (by simp [TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat]; omega)
      · simp only [xwc, QRegister.basisBits_extractIndex]
        exact hzero _ (by
          simp [TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat, walkWidth]; omega)
    · rintro ⟨h1, h2, h3⟩
      funext ⟨w, hw⟩
      have hge : systemQubits_local ≤ w.val := by
        by_contra hlt; push Not at hlt
        exact hw ⟨⟨w.val, hlt⟩, by ext; simp [sys]⟩
      simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply]
      by_cases h_w : w.val < walkWidth mOut mMid
      · let w' : Wire (walkWidth mOut mMid) := ⟨w.val, h_w⟩
        have hw' : w' ∉ Set.range (rSysInWalk mOut mMid).wires := by
          rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi
          simp [rSysInWalk, w', systemQubits_local] at hv hge; omega
        have hb := congrFun h1 ⟨w', hw'⟩
        simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply, xw, xwc,
          QRegister.basisBits_extractIndex] at hb
        rw [← hb]; refine congrArg (basisBits _ _) ?_
        ext; simp [TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat, w']
      · by_cases h_wc : w.val < walkCatWidth bCat mOut mMid
        · let i : Fin bCat := ⟨w.val - walkWidth mOut mMid, by
            dsimp [walkCatWidth] at h_wc; omega⟩
          have hb := h2 i
          simp only [xwc, QRegister.basisBits_extractIndex] at hb
          rw [← hb]; refine congrArg (basisBits _ _) ?_
          ext; simp [TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat, i]; omega
        · let j : Fin bQPE := ⟨w.val - walkCatWidth bCat mOut mMid, by
            have hw_lt : w.val < walkCatWidth bCat mOut mMid + bQPE :=
              actWidth_eq bQPE bCat mOut mMid ▸ w.isLt
            omega⟩
          have hb := h3 j
          rw [← hb]; refine congrArg (basisBits _ _) ?_
          ext; simp [TopIntegrationBridge.rQPEInAct, j]; omega
  dsimp only [QRegister.tensorState, tensorWCQPE2, tensorWalkCat, basisState]
  change _ =
    (e₁ xw *
      (Pi.single 0 (1 : ℂ) : Fin (2 ^ bCat) → ℂ)
        ((rCatInWalkCat bCat mOut mMid).extractIndex xwc)) *
    (Pi.single 0 (1 : ℂ) : Fin (2 ^ bQPE) → ℂ) ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)
  dsimp only [e₁, QRegister.tensorState]
  rw [hsys_eq]
  by_cases h : (sys.basisSplitEquiv g).2 = 0
  · obtain ⟨h1, h2, h3⟩ := hbits_iff.mp h
    simp [h, h1, h2, h3]
  · have hnot := mt hbits_iff.mpr h
    by_cases h1 : ((rSysInWalk mOut mMid).basisSplitEquiv xw).2 = 0
    · by_cases h2 : (rCatInWalkCat bCat mOut mMid).extractIndex xwc = 0
      · have h3 : (rQPEInAct bQPE bCat mOut mMid).extractIndex g ≠ 0 :=
          fun hc ↦ hnot ⟨h1, h2, hc⟩
        simp [Pi.single_apply, h, h3]
      · simp [Pi.single_apply, h, h2]
    · simp [Pi.single_apply, h, h1]

private theorem rCatInAct_eq_compose2 (bQPE bCat mOut mMid : ℕ) :
    rCatInAct bQPE bCat mOut mMid =
      (rWalkCatInAct bQPE bCat mOut mMid).compose (rCatInWalkCat bCat mOut mMid) := by
  ext i; simp [TopIntegrationBridge.rCatInAct, TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat]

private theorem ancAct_compose_rQPEInAnc2 (bQPE bCat mOut mMid : ℕ) :
    (QRegister.block systemQubits_local (actAncillas bQPE bCat mOut mMid) le_rfl).compose
        (rQPEInAnc bQPE bCat mOut mMid) =
      rQPEInAct bQPE bCat mOut mMid := by
  ext i
  simp [TopIntegrationBridge.rQPEInAnc, TopIntegrationBridge.rQPEInAct, walkCatWidth, walkWidth,
    systemQubits_local]
  omega

section Proofs

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked

private theorem unitary_conjTranspose_mul_self {d : ℕ} (V : Unitary d) :
    V.1ᴴ * V.1 = 1 := by
  rw [← Matrix.star_eq_conjTranspose]; exact Matrix.UnitaryGroup.star_mul_self V

private theorem dotProduct_star_tensorState_zero {k n : ℕ} (r : QRegister k n)
    (ψ₁ ψ₂ : Fin (2 ^ k) → ℂ) (horth : star ψ₁ ⬝ᵥ ψ₂ = 0) :
    star (r.tensorState ψ₁ (Pi.single 0 1)) ⬝ᵥ r.tensorState ψ₂ (Pi.single 0 1) = 0 := by
  let f : Fin (2 ^ n) → ℂ := fun g ↦
    star (r.tensorState ψ₁ (Pi.single 0 1) g) * r.tensorState ψ₂ (Pi.single 0 1) g
  change ∑ g, f g = 0
  rw [← r.basisSplitEquiv.symm.sum_comp f, Fintype.sum_prod_type]
  have hrow (s : Fin (2 ^ k)) :
      (∑ env, f (r.basisSplitEquiv.symm (s, env))) = star (ψ₁ s) * ψ₂ s := by
    rw [Finset.sum_eq_single 0]
    · have h1 : r.extractIndex (r.basisSplitEquiv.symm (s, 0)) = s :=
        congrArg Prod.fst (r.basisSplitEquiv.apply_symm_apply (s, 0))
      simp [f, QRegister.tensorState, h1]
    · intro env _ henv
      simp [f, QRegister.tensorState, Pi.single_apply, henv]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hrow]
  exact horth

/-- Cross-eigenstate QPE-outcome orthogonality (`horth`) for `blockedIdealUnitary` under any
`PulledSOSBlockEncoding`, proved via 2D Jordan-subspace invariance and
`PerturbedQPEClosure.jordan_span_cross_ortho`. -/
theorem blocked_ideal_qpe_horth (bQPE bCat mOut mMid bAct M : ℕ)
    {H_tilde_blk : Operator (2 ^ (2 * 58))} {eLB lam : ℝ}
    {uB : Unitary (2 ^ walkWidth mOut mMid)}
    (hSOS : PulledSOSBlockEncoding mOut mMid H_tilde_blk eLB lam uB)
    (uCatIdeal : Unitary (2 ^ bCat))
    (uWinIdeal uIqftIdeal : Unitary (2 ^ bQPE))
    (η : ℕ)
    (E₁ : ℝ) (ψ₁ : Fin (2 ^ (2 * 58)) → ℂ)
    (E₂ : ℝ) (ψ₂ : Fin (2 ^ (2 * 58)) → ℂ)
    (hEig₁ : IsEigenSector H_tilde_blk η E₁ ψ₁)
    (hnorm₁ : ∑ i, Complex.normSq (ψ₁ i) = 1)
    (hEig₂ : IsEigenSector H_tilde_blk η E₂ ψ₂)
    (hnorm₂ : ∑ i, Complex.normSq (ψ₂ i) = 1)
    (horth : star ψ₁ ⬝ᵥ ψ₂ = 0)
    (y : Fin (2 ^ bQPE)) :
    let sys : QRegister (2 * 58) (2 * 58 + actAncillas bQPE bCat mOut mMid) :=
      .block 0 (2 * 58) (by omega)
    let anc : QRegister (actAncillas bQPE bCat mOut mMid)
      (2 * 58 + actAncillas bQPE bCat mOut mMid) :=
      .block (2 * 58) (actAncillas bQPE bCat mOut mMid) le_rfl
    let Py := (anc.compose (rQPEInAnc bQPE bCat mOut mMid)).basisOutcomeProjector y
    let wIdBlk := blockedIdealUnitary bQPE bCat mOut mMid bAct M
      uCatIdeal uB uWinIdeal uIqftIdeal
    star (Py *ᵥ (wIdBlk.1 *ᵥ sys.tensorState ψ₁ (Pi.single 0 1))) ⬝ᵥ
      (Py *ᵥ (wIdBlk.1 *ᵥ sys.tensorState ψ₂ (Pi.single 0 1))) = 0 := by
  intro sys anc Py wIdBlk
  let P₁ := QubitisedWalk.projIn (rAllInWalk mOut mMid)
  let P₂ := QubitisedWalk.pulledProjMid (rMidInWalk mOut mMid) uB
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  let F := affineScheduleFiber (bQPE := bQPE) bAct M (R₁ * R₂) R₁
  let cat := uCatIdeal.1 *ᵥ basisState (0 : Fin (2 ^ bCat))
  let window0 := uWinIdeal.1 *ᵥ basisState (0 : Fin (2 ^ bQPE))
  have hP₂_idem : P₂ * P₂ = P₂ := QubitisedWalk.pulledProjMid_mul_self (rMidInWalk mOut mMid) uB
  have hR₁_eq : R₁.1 = (2 : ℂ) • P₁ - 1 := rfl
  have hR₂_eq : R₂.1 = 1 - (2 : ℂ) • P₂ := by
    dsimp [R₂, P₂, QubitisedWalk.reflPulledUnitary, QubitisedWalk.reflPulledPair,
      QubitisedWalk.reflMidUnitary, QubitisedWalk.pulledProjMid, QubitisedWalk.projMid]
    have hu : uB.1ᴴ * uB.1 = 1 := unitary_conjTranspose_mul_self uB
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      mul_smul_comm, smul_mul_assoc, hu]
  have hspan_closed : ∀ (e : Fin (2 ^ walkWidth mOut mMid) → ℂ) (c : ℂ),
      P₁ *ᵥ e = e → P₁ *ᵥ (P₂ *ᵥ e) = c • e →
      ∃ a b : ℂ,
        (∑ m : Fin (2 ^ bQPE), (uIqftIdeal.1 y m * window0 m) • ((F m).1 *ᵥ e)) =
          a • e + b • (P₂ *ᵥ e) := by
    intro e c he hproj
    let inSpan (v : Fin (2 ^ walkWidth mOut mMid) → ℂ) : Prop :=
      ∃ a b : ℂ, v = a • e + b • (P₂ *ᵥ e)
    have hR₁_span {v} : inSpan v → inSpan (R₁.1 *ᵥ v) := by
      rintro ⟨a, b, rfl⟩
      refine ⟨2 * (a + b * c) - a, -b, ?_⟩
      rw [hR₁_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, he, hproj]
      ext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hR₂_span {v} : inSpan v → inSpan (R₂.1 *ᵥ v) := by
      rintro ⟨a, b, rfl⟩
      refine ⟨a, b - 2 * (a + b), ?_⟩
      have hP₂P₂ : P₂ *ᵥ (P₂ *ᵥ e) = P₂ *ᵥ e := by rw [Matrix.mulVec_mulVec, hP₂_idem]
      rw [hR₂_eq, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hP₂P₂]
      ext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hW_pow : ∀ (k : ℕ) {v}, inSpan v → inSpan (((R₁ * R₂) ^ k).1 *ᵥ v) := by
      intro k
      induction k with
      | zero => intro v hv; simpa [_root_.pow_zero] using hv
      | succ k' ih =>
        intro v hv
        rw [pow_succ, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        exact ih (hR₁_span (hR₂_span hv))
    have hChunk (pred : Fin (2 ^ bQPE) → Bool) (k : ℕ) (x : Fin (2 ^ bQPE)) {v}
        (hv : inSpan v) : inSpan ((chunkFiberStep pred k (R₁ * R₂) R₁ x).1 *ᵥ v) := by
      dsimp only [chunkFiberStep]
      split_ifs
      · simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        exact hR₁_span (hW_pow k (hR₁_span hv))
      · exact hW_pow k hv
    have hChunks : ∀ (n : ℕ) (x : Fin (2 ^ bQPE)) {v}, inSpan v →
        inSpan ((chunksFiber (bAct - 1) M (R₁ * R₂) R₁ n x).1 *ᵥ v) := by
      intro n
      induction n with
      | zero => intro x v hv; simpa [chunksFiber] using hv
      | succ n' ih =>
        intro x v hv
        rw [chunksFiber, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        exact hChunk _ _ x (ih x hv)
    have hF (m : Fin (2 ^ bQPE)) : inSpan ((F m).1 *ᵥ e) :=
      hChunks bAct (qpeAffinePerm bAct bQPE M m) ⟨1, 0, by simp⟩
    choose fa fb hfab using hF
    refine ⟨∑ m, (uIqftIdeal.1 y m * window0 m) * fa m,
      ∑ m, (uIqftIdeal.1 y m * window0 m) * fb m, ?_⟩
    ext x
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    have hm := congrFun (hfab m) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hm
    rw [hm]; ring
  have hProjEval (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
      let e := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
      let vy := ∑ m : Fin (2 ^ bQPE), (uIqftIdeal.1 y m * window0 m) • ((F m).1 *ᵥ e)
      ∀ g : Fin (2 ^ actWidth bQPE bCat mOut mMid),
        (Py *ᵥ (wIdBlk.1 *ᵥ sys.tensorState ψ (Pi.single 0 1))) g =
          if (rQPEInAct bQPE bCat mOut mMid).extractIndex g = y then
            tensorWalkCat vy cat ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g)
          else 0 := by
    intro e vy g
    have hPy : Py = (rQPEInAct bQPE bCat mOut mMid).basisOutcomeProjector y := by
      dsimp only [Py, anc]; rw [ancAct_compose_rQPEInAnc2]
    let u1Id := (rCatInAct bQPE bCat mOut mMid).embedUnitary uCatIdeal
    let u2Id := (rQPEInAct bQPE bCat mOut mMid).embedUnitary uWinIdeal
    let rComb := (rQPEInAct bQPE bCat mOut mMid).concat (rWalkCatInAct bQPE bCat mOut mMid)
      (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)
    let Fc := affineScheduleFiber (bQPE := bQPE) bAct M
      (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) *
        QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid)
          ((rWalkInWalkCat bCat mOut mMid).embedUnitary uB))
      (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid))
    let u3Id := rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary Fc)
    let u4Id := (rQPEInAct bQPE bCat mOut mMid).embedUnitary uIqftIdeal
    have hs1 : u1Id.1 *ᵥ sys.tensorState ψ (Pi.single 0 1) =
        tensorWCQPE2 (tensorWalkCat e cat) (basisState 0) := by
      rw [sysAct_tensorState_zero_eq2 ψ]
      dsimp only [u1Id, cat]
      rw [rCatInAct_eq_compose2, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
        embedMatrix_rWalkCatInAct_mulVec2, QRegister.embedUnitary_val,
        embedMatrix_rCatInWalkCat_mulVec]
    have hs2 : u2Id.1 *ᵥ (u1Id.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)) =
        tensorWCQPE2 (tensorWalkCat e cat) window0 := by
      rw [hs1, QRegister.embedUnitary_val, embedMatrix_rQPEInAct_mulVec2]
    have hFc (m : Fin (2 ^ bQPE)) :
        Fc m = (rWalkInWalkCat bCat mOut mMid).embedUnitary (F m) := by
      dsimp only [Fc, F, R₁, R₂]
      rw [embedUnitary_rWalkInWalkCat_reflIn2, embedUnitary_rWalkInWalkCat_reflPulled2,
        ← QRegister.embedUnitary_mul, ← embedUnitaryAffineScheduleFiber]
    have hstep : wIdBlk.1 *ᵥ sys.tensorState ψ (Pi.single 0 1) =
        u4Id.1 *ᵥ (u3Id.1 *ᵥ tensorWCQPE2 (tensorWalkCat e cat) window0) := by
      dsimp only [wIdBlk, blockedIdealUnitary, u4Id, u3Id, u2Id, u1Id, rComb, Fc]
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hs2]
    rw [hPy, QRegister.basisOutcomeProjector_mulVec]
    split_ifs with hgy
    · rw [hstep]
      dsimp only [u4Id]
      rw [QRegister.embedUnitary_val, embedMatrix_mulVec_apply_replaceIndex_4, hgy]
      dsimp only [tensorWalkCat, vy]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      dsimp only [u3Id]
      rw [embed_qpeMuxUnitary_mulVec_3, QRegister.extractIndex_replaceIndex]
      have hwc : (rWalkCatInAct bQPE bCat mOut mMid).extractIndex
          ((rQPEInAct bQPE bCat mOut mMid).replaceIndex g m) =
          (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g :=
        (rWalkCatInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
          (QRegister.disjoint_comm.mp (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)) g m
      rw [hwc, hFc m, QRegister.embedUnitary_val, embedMatrix_rWalkInWalkCat_mulVec]
      dsimp only [tensorWalkCat]
      ring
    · rfl
  let e₁ := (rSysInWalk mOut mMid).tensorState ψ₁ (Pi.single 0 1)
  let e₂ := (rSysInWalk mOut mMid).tensorState ψ₂ (Pi.single 0 1)
  obtain ⟨hPin₁, _, _, _, hProj₁⟩ := hSOS.jordanRelation ψ₁ E₁ hEig₁.1 hnorm₁
  obtain ⟨hPin₂, _, _, _, hProj₂⟩ := hSOS.jordanRelation ψ₂ E₂ hEig₂.1 hnorm₂
  obtain ⟨a₁, b₁, hv₁⟩ := hspan_closed e₁ _ hPin₁ hProj₁
  obtain ⟨a₂, b₂, hv₂⟩ := hspan_closed e₂ _ hPin₂ hProj₂
  let v₁y := a₁ • e₁ + b₁ • (P₂ *ᵥ e₁)
  let v₂y := a₂ • e₂ + b₂ • (P₂ *ᵥ e₂)
  let term : Fin (2 ^ actWidth bQPE bCat mOut mMid) → ℂ := fun g ↦
    star ((Py *ᵥ (wIdBlk.1 *ᵥ sys.tensorState ψ₁ (Pi.single 0 1))) g) *
      (Py *ᵥ (wIdBlk.1 *ᵥ sys.tensorState ψ₂ (Pi.single 0 1))) g
  change ∑ g, term g = 0
  rw [← (actSplitEquiv2 bQPE bCat mOut mMid).symm.sum_comp term, Fintype.sum_prod_type_right,
    Fintype.sum_eq_single y]
  · have hpt : ∑ x : Fin (2 ^ walkCatWidth bCat mOut mMid),
        term ((actSplitEquiv2 bQPE bCat mOut mMid).symm (x, y)) =
        ∑ x, star (tensorWalkCat v₁y cat x) * tensorWalkCat v₂y cat x := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      let g := (actSplitEquiv2 bQPE bCat mOut mMid).symm (x, y)
      have hfst : (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g = x := by
        rw [← actSplitEquiv_fst2, Equiv.apply_symm_apply]
      have hsnd : (rQPEInAct bQPE bCat mOut mMid).extractIndex g = y := by
        rw [← actSplitEquiv_snd2, Equiv.apply_symm_apply]
      dsimp only [term]
      rw [hProjEval ψ₁ g, hProjEval ψ₂ g, ite_eq_left hsnd, ite_eq_left hsnd, hfst, hv₁, hv₂]
    rw [hpt, inner_tensorWalkCat2]
    have horth_e : star e₁ ⬝ᵥ e₂ = 0 :=
      dotProduct_star_tensorState_zero (rSysInWalk mOut mMid) ψ₁ ψ₂ horth
    have hjord : QubitisedWalk.vecInner v₁y v₂y = 0 :=
      PerturbedQPEClosure.jordan_span_cross_ortho
        (QubitisedWalk.projIn_conjTranspose (rAllInWalk mOut mMid))
        (QubitisedWalk.pulledProjMid_conjTranspose (rMidInWalk mOut mMid) uB)
        hP₂_idem hPin₁ hProj₂ horth_e a₁ b₁ a₂ b₂
    rw [hjord, zero_mul]
  · intro y' hy'
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    let g := (actSplitEquiv2 bQPE bCat mOut mMid).symm (x, y')
    have hsnd : (rQPEInAct bQPE bCat mOut mMid).extractIndex g = y' := by
      rw [← actSplitEquiv_snd2, Equiv.apply_symm_apply]
    dsimp only [term]
    rw [hProjEval ψ₁ g, ite_eq_right (hsnd ▸ hy'), star_zero, zero_mul]

end Proofs
end MasterIntegration

end BlockReflection

namespace ApproxIqft16

open Operator QProg Matrix Real
open scoped Matrix Matrix.Norms.L2Operator BigOperators

/-! ## Section 1: Diagonal Phase Algebra & ZZ Phase-Telescoping Identities -/

theorem diagPhaseUnitary_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    diagPhaseUnitary (0 : ι → ℝ) = 1 := by
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst hij; simp [diagPhaseMatrix]
  · simp [diagPhaseMatrix, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem diagPhaseUnitary_add {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) :
    diagPhaseUnitary (f + g) = diagPhaseUnitary f * diagPhaseUnitary g := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, diagPhaseUnitary_coe, diagPhaseUnitary_coe, diagPhaseUnitary_coe,
    diagPhaseMatrix, diagPhaseMatrix, diagPhaseMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem diagPhaseUnitary_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    diagPhaseUnitary (-f) = (diagPhaseUnitary f)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← diagPhaseUnitary_add, neg_add_cancel, diagPhaseUnitary_zero]

theorem diagPhaseUnitary_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) :
    diagPhaseUnitary f * diagPhaseUnitary g = diagPhaseUnitary g * diagPhaseUnitary f := by
  rw [← diagPhaseUnitary_add, add_comm, diagPhaseUnitary_add]

theorem diagPhaseUnitary_comm_hadamardAt (b : ℕ) (ℓ : Fin b) (f : Fin (2 ^ b) → ℝ)
    (hind : ∀ i j : Fin (2 ^ b),
      (∀ m ≠ ℓ, basisBits b i m = basisBits b j m) → f i = f j) :
    diagPhaseUnitary f * hadamardAt b ℓ = hadamardAt b ℓ * diagPhaseUnitary f := by
  apply Subtype.ext
  ext i j
  rw [Submonoid.coe_mul, Submonoid.coe_mul, diagPhaseUnitary_coe, diagPhaseMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, hadamardAt_apply]
  by_cases h : ∀ m ≠ ℓ, basisBits b i m = basisBits b j m
  · rw [ite_eq_left h, hind i j h, mul_comm]
  · rw [ite_eq_right h, mul_zero, zero_mul]

theorem zmod2_xor_sub_eq_neg_two_mul (x y : ZMod 2) :
    ((x + y).val : ℝ) - (x.val : ℝ) - (y.val : ℝ) = -2 * ((x.val : ℝ) * (y.val : ℝ)) := by
  have hnat : (x + y).val + 2 * (x.val * y.val) = x.val + y.val := by
    fin_cases x <;> fin_cases y <;> decide
  have hreal : (((x + y).val + 2 * (x.val * y.val) : ℕ) : ℝ) = ((x.val + y.val : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal
  linarith

theorem neg_crPhase_eq_zz_add (b : ℕ) (idx ℓ : Fin b) (r : ℕ) (j : Fin (2 ^ b)) :
    -QFT.crPhase b idx ℓ r j =
      ((basisBits b j idx + basisBits b j ℓ).val : ℝ) / (2 : ℝ) ^ (r + 1) +
        (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (r + 1)) +
        (-((basisBits b j ℓ).val : ℝ) / (2 : ℝ) ^ (r + 1)) := by
  unfold QFT.crPhase
  have hxor := zmod2_xor_sub_eq_neg_two_mul (basisBits b j idx) (basisBits b j ℓ)
  have h2ne : (2 : ℝ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  rw [pow_succ]
  field_simp [h2ne]
  linarith

theorem sum_fin_lt_sub {m : ℕ} (c : ℕ) (hc : c ≤ m) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ i.val < c), (g (i.val + 1) - g i.val)) =
      g c - g 0 := by
  induction c with
  | zero =>
    have hempty : Finset.univ.filter (fun i : Fin m ↦ i.val < 0) = ∅ := by ext i; simp
    rw [hempty, Finset.sum_empty, sub_self]
  | succ c ih =>
    have hlt : c < m := by omega
    let ic : Fin m := ⟨c, hlt⟩
    have hsplit : Finset.univ.filter (fun i : Fin m ↦ i.val < c + 1) =
        insert ic (Finset.univ.filter (fun i : Fin m ↦ i.val < c)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, ic]
      omega
    have hnot : ic ∉ Finset.univ.filter (fun i : Fin m ↦ i.val < c) := by simp [ic]
    rw [hsplit, Finset.sum_insert hnot, ih (by omega)]
    dsimp [ic]
    ring

theorem sum_fin_ge_sub {m : ℕ} (a : ℕ) (ha : a ≤ m) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ a ≤ i.val), (g i.val - g (i.val + 1))) =
      g a - g m := by
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin m ↦ i.val < a))
      (Finset.univ.filter (fun i : Fin m ↦ a ≤ i.val)) :=
    Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ by omega
  have hunion : Finset.univ.filter (fun i : Fin m ↦ i.val < a) ∪
      Finset.univ.filter (fun i : Fin m ↦ a ≤ i.val) =
      Finset.univ.filter (fun i : Fin m ↦ i.val < m) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, i.isLt, iff_true]
    exact lt_or_ge i.val a
  have hall := sum_fin_lt_sub m le_rfl g
  rw [← hunion, Finset.sum_union hdisj, sum_fin_lt_sub a ha g] at hall
  have hneg :
      (∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ a ≤ i.val), (g i.val - g (i.val + 1))) =
        -(∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ a ≤ i.val), (g (i.val + 1) - g i.val)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  linarith

/-! ## Section 2: Parametric ZZ-Telescoped `QFT†` Circuit & Exact Gate Counts -/

/-- Diagonal parity-phase core `CNOT(0, 1) · Rz(π / 2^k)_1 · CNOT(0, 1)` (`T` for `k = 2`). -/
def zzCoreCircuit (k : ℕ) (cRz : ℕ → Circuit 1) : Circuit 2 :=
  if k = 2 then
    SineQPE.cnotRzCnotCircuit (Circuit.T 0)
  else
    SineQPE.cnotRzCnotCircuit (cRz k)

/-- Telescoped single-wire phase shift realizing `diag(1, exp(2πi(-1/4 + 1/2^(M+1))))` up to
global phase (`T†` for `M = 2`; `S† · cRz M` for `M ≥ 3`). -/
def phaseShiftCircuit (M : ℕ) (cRz : ℕ → Circuit 1) : Circuit 1 :=
  if M = 2 then
    (Circuit.T (0 : Fin 1)).inverse
  else
    .seq (cRz M) (Circuit.S (0 : Fin 1)).inverse

/-- Inner diagonal parity-phase loop for stage `ℓ` (`idx = b - 1` down to `ℓ + 1`). -/
def zzInnerCircuit (b : ℕ) (cRz : ℕ → Circuit 1) (ℓ : Fin b) : Circuit b :=
  SineQPE.revLoopCircuit b
    (fun idx ↦
      if h : ℓ.val < idx.val then
        (zzCoreCircuit (idx.val - ℓ.val + 1) cRz).onRegister
          (QRegister.pair idx ℓ (by intro heq; subst heq; omega))
      else
        .identity)
    (ℓ.val + 1)

/-- Stage `ℓ` of ZZ-telescoped `QFT†`: parity cores, telescoped target phase (if `ℓ + 1 < b`),
and `H ℓ`. -/
def zzOuterStep (b : ℕ) (cRz : ℕ → Circuit 1) (ℓ : Fin b) : Circuit b :=
  let preH : Circuit b :=
    if ℓ.val + 1 < b then
      .seq (zzInnerCircuit b cRz ℓ)
        ((phaseShiftCircuit (b - ℓ.val) cRz).onRegister (QRegister.singleton ℓ))
    else
      zzInnerCircuit b cRz ℓ
  .seq preH (Circuit.H ℓ)

/-- Post-Hadamard parallel control-wire phase layer on wires `idx = 1 .. b - 1`. -/
def zzPostCtrlLayer (b : ℕ) (cRz : ℕ → Circuit 1) : Circuit b :=
  SineQPE.revLoopCircuit b
    (fun idx ↦
      if 1 ≤ idx.val then
        (phaseShiftCircuit (idx.val + 1) cRz).onRegister (QRegister.singleton idx)
      else
        .identity)
    1

/-- Parametric ancilla-free `b`-qubit ZZ-telescoped `QFT†` circuit. -/
def zzIqftFromRzCircuit (b : ℕ) (cRz : ℕ → Circuit 1) : Circuit b :=
  .seq (.seq (SineQPE.revLoopCircuit b (zzOuterStep b cRz) 0) (zzPostCtrlLayer b cRz))
    (SineQPE.swapAllCircuit b)

theorem zzCoreCircuit_count_toff (k : ℕ) (cRz : ℕ → Circuit 1)
    (htoff : ∀ m, (cRz m).count PrimitiveGate.TOFF = 0) :
    (zzCoreCircuit k cRz).count PrimitiveGate.TOFF = 0 := by
  unfold zzCoreCircuit
  split_ifs <;> simp [htoff]

theorem phaseShiftCircuit_count_toff (M : ℕ) (cRz : ℕ → Circuit 1)
    (htoff : ∀ m, (cRz m).count PrimitiveGate.TOFF = 0) :
    (phaseShiftCircuit M cRz).count PrimitiveGate.TOFF = 0 := by
  unfold phaseShiftCircuit
  split_ifs
  · rfl
  · simp [htoff]; rfl

theorem zzIqftFromRzCircuit_count_toff (b : ℕ) (cRz : ℕ → Circuit 1)
    (htoff : ∀ m, (cRz m).count PrimitiveGate.TOFF = 0) :
    (zzIqftFromRzCircuit b cRz).count PrimitiveGate.TOFF = 0 := by
  simp only [zzIqftFromRzCircuit, zzPostCtrlLayer, Circuit.count_seq,
    SineQPE.swapAllCircuit_count_toff, add_zero, SineQPE.revLoopCircuit_count]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro idx _
    split_ifs <;> simp [phaseShiftCircuit_count_toff _ _ htoff]
  · intro ℓ _
    dsimp only [zzOuterStep, zzInnerCircuit]
    have hH : (Circuit.H ℓ).count PrimitiveGate.TOFF = 0 := rfl
    rw [Circuit.count_seq, hH, add_zero]
    by_cases hlt : ℓ.val + 1 < b
    · rw [ite_eq_left hlt, Circuit.count_seq, Circuit.count_onRegister,
        phaseShiftCircuit_count_toff _ _ htoff, add_zero, SineQPE.revLoopCircuit_count]
      apply Finset.sum_eq_zero
      intro idx _
      split_ifs <;> simp [zzCoreCircuit_count_toff _ _ htoff]
    · rw [ite_eq_right hlt, SineQPE.revLoopCircuit_count]
      apply Finset.sum_eq_zero
      intro idx _
      split_ifs <;> simp [zzCoreCircuit_count_toff _ _ htoff]

theorem zzCoreCircuit_count_t (k : ℕ) (cRz : ℕ → Circuit 1) :
    (zzCoreCircuit k cRz).count PrimitiveGate.T =
      if k = 2 then 1 else (cRz k).count PrimitiveGate.T := by
  unfold zzCoreCircuit
  by_cases hk : k = 2
  · rw [ite_eq_left hk, ite_eq_left hk]; simp
  · rw [ite_eq_right hk, ite_eq_right hk]; simp

theorem phaseShiftCircuit_count_t (M : ℕ) (cRz : ℕ → Circuit 1) :
    (phaseShiftCircuit M cRz).count PrimitiveGate.T =
      if M = 2 then 1 else (cRz M).count PrimitiveGate.T := by
  unfold phaseShiftCircuit
  by_cases hM : M = 2
  · rw [ite_eq_left hM, ite_eq_left hM]; rfl
  · rw [ite_eq_right hM, ite_eq_right hM, Circuit.count_seq]
    have hS : ((Circuit.S (0 : Fin 1)).inverse).count PrimitiveGate.T = 0 := rfl
    rw [hS, add_zero]

theorem zzIqftFromRzCircuit_count_t (b : ℕ) (cRz : ℕ → Circuit 1) :
    (zzIqftFromRzCircuit b cRz).count PrimitiveGate.T =
      (∑ ℓ : Fin b,
        ((∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
            if ℓ.val < idx.val then
              if idx.val - ℓ.val + 1 = 2 then 1
              else (cRz (idx.val - ℓ.val + 1)).count PrimitiveGate.T
            else 0) +
          if ℓ.val + 1 < b then
            if b - ℓ.val = 2 then 1 else (cRz (b - ℓ.val)).count PrimitiveGate.T
          else 0)) +
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ 1 ≤ idx.val),
        if 1 ≤ idx.val then
          if idx.val + 1 = 2 then 1 else (cRz (idx.val + 1)).count PrimitiveGate.T
        else 0) := by
  simp only [zzIqftFromRzCircuit, zzPostCtrlLayer, Circuit.count_seq,
    SineQPE.swapAllCircuit_count_t, add_zero, SineQPE.revLoopCircuit_count]
  have huniv : Finset.univ.filter (fun i : Fin b ↦ 0 ≤ i.val) = Finset.univ := by
    ext i; simp
  rw [huniv]
  congr 1
  · refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
    dsimp only [zzOuterStep, zzInnerCircuit]
    have hH : (Circuit.H ℓ).count PrimitiveGate.T = 0 := rfl
    rw [Circuit.count_seq, hH, add_zero]
    by_cases hlt : ℓ.val + 1 < b
    · rw [ite_eq_left hlt, ite_eq_left hlt, Circuit.count_seq, Circuit.count_onRegister,
        phaseShiftCircuit_count_t, SineQPE.revLoopCircuit_count]
      congr 1
      refine Finset.sum_congr rfl fun idx _ ↦ ?_
      by_cases h : ℓ.val < idx.val
      · rw [dite_eq_left h, ite_eq_left h, Circuit.count_onRegister, zzCoreCircuit_count_t]
      · rw [dite_eq_right h, ite_eq_right h]; rfl
    · rw [ite_eq_right hlt, ite_eq_right hlt, add_zero, SineQPE.revLoopCircuit_count]
      refine Finset.sum_congr rfl fun idx _ ↦ ?_
      by_cases h : ℓ.val < idx.val
      · rw [dite_eq_left h, ite_eq_left h, Circuit.count_onRegister, zzCoreCircuit_count_t]
      · rw [dite_eq_right h, ite_eq_right h]; rfl
  · refine Finset.sum_congr rfl fun idx _ ↦ ?_
    by_cases h1 : 1 ≤ idx.val
    · rw [ite_eq_left h1, ite_eq_left h1, Circuit.count_onRegister, phaseShiftCircuit_count_t]
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

/-! ## Section 3: Ideal Diagonal Targets & Primitive Operator-Norm Bounds -/

/-- Parity diagonal phase `((b_idx ⊕ b_ℓ) : ℝ) / 2^(k + 1)` on `b` qubits. -/
noncomputable def zzParityPhase (b : ℕ) (idx ℓ : Fin b) (k : ℕ) (j : Fin (2 ^ b)) : ℝ :=
  ((basisBits b j idx + basisBits b j ℓ).val : ℝ) / (2 : ℝ) ^ (k + 1)

/-- Two-qubit ideal parity-phase unitary `diagPhaseUnitary (zzParityPhase 2 0 1 k)`. -/
noncomputable def zzCoreUnitary2 (k : ℕ) : Unitary (2 ^ 2) :=
  diagPhaseUnitary (zzParityPhase 2 0 1 k)

/-- Telescoped single-wire diagonal phase `b_w * (-1 / 4 + 1 / 2^(M + 1))` on `b` qubits. -/
noncomputable def wireShiftPhase (b : ℕ) (w : Fin b) (M : ℕ) (j : Fin (2 ^ b)) : ℝ :=
  ((basisBits b j w).val : ℝ) * (-1 / 4 + 1 / (2 : ℝ) ^ (M + 1))

/-- Single-qubit ideal telescoped phase-shift unitary `diagPhaseUnitary (wireShiftPhase 1 0 M)`. -/
noncomputable def phaseShiftUnitary1 (M : ℕ) : Unitary (2 ^ 1) :=
  diagPhaseUnitary (wireShiftPhase 1 0 M)

/-- Global unit scalar `exp(-i π / 2^(k + 1))` from `Rz(π / 2^k)`. -/
noncomputable def rzGlobalPhase (k : ℕ) : ℂ :=
  Complex.exp (-Complex.I * ((π / (2 : ℝ) ^ (k + 1) : ℝ) : ℂ))

theorem norm_rzGlobalPhase (k : ℕ) : ‖rzGlobalPhase k‖ = 1 := by
  unfold rzGlobalPhase
  rw [show -Complex.I * ((π / (2 : ℝ) ^ (k + 1) : ℝ) : ℂ) =
      ((-(π / (2 : ℝ) ^ (k + 1)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem pair_embedUnitary_zzCoreUnitary2 (b : ℕ) (idx ℓ : Fin b) (hne : idx ≠ ℓ) (k : ℕ) :
    (QRegister.pair idx ℓ hne).embedUnitary (zzCoreUnitary2 k) =
      diagPhaseUnitary (zzParityPhase b idx ℓ k) := by
  apply Subtype.ext
  rw [QRegister.embedUnitary_val, zzCoreUnitary2, diagPhaseUnitary_coe, diagPhaseUnitary_coe,
    diagPhaseMatrix, diagPhaseMatrix, QRegister.embedMatrix_diagonal]
  congr 1
  funext g
  simp only [zzParityPhase, QRegister.basisBits_extractIndex]
  rfl

theorem singleton_embedUnitary_phaseShiftUnitary1 (b : ℕ) (w : Fin b) (M : ℕ) :
    (QRegister.singleton w).embedUnitary (phaseShiftUnitary1 M) =
      diagPhaseUnitary (wireShiftPhase b w M) := by
  apply Subtype.ext
  rw [QRegister.embedUnitary_val, phaseShiftUnitary1, diagPhaseUnitary_coe, diagPhaseUnitary_coe,
    diagPhaseMatrix, diagPhaseMatrix, QRegister.embedMatrix_diagonal]
  congr 1
  funext g
  simp only [wireShiftPhase, QRegister.basisBits_extractIndex]
  rfl

theorem parityRzUnitary_eq_smul_zzCoreUnitary2 (k : ℕ) :
    (SineQPE.parityRzUnitary (π / (2 : ℝ) ^ k)).1 =
      rzGlobalPhase k • (zzCoreUnitary2 k).1 := by
  rw [SineQPE.parityRzUnitary_eq_diagonal, zzCoreUnitary2, diagPhaseUnitary_coe, diagPhaseMatrix,
    ← Matrix.diagonal_smul]
  congr 1
  funext i
  have hb (m : Fin 4) :
      (2 * ((basisBits 2 m 1).val : ℝ) - 1) * (1 - 2 * ((basisBits 2 m 0).val : ℝ)) =
        2 * ((basisBits 2 m 0 + basisBits 2 m 1).val : ℝ) - 1 := by
    linear_combination -2 * zmod2_xor_sub_eq_neg_two_mul (basisBits 2 m 0) (basisBits 2 m 1)
  simp only [Pi.smul_apply, smul_eq_mul, rzGlobalPhase, zzParityPhase, hb i, ← Complex.exp_add]
  congr 1
  rw [pow_succ (2 : ℝ)]
  push_cast
  ring

theorem zzCoreCircuit_two_eval (cRz : ℕ → Circuit 1) :
    (zzCoreCircuit 2 cRz).eval.1 = (zzCoreUnitary2 2).1 := by
  have hT_rz :
      (Circuit.T (0 : Fin 1)).eval.1 =
        Complex.exp (Complex.I * ((π / 8 : ℝ) : ℂ)) • SineQPE.rzMatrix (π / (2 : ℝ) ^ 2) := by
    have hT : (Circuit.T (0 : Fin 1)).eval.1 =
        Matrix.diagonal (fun i : Fin 2 ↦ if i = 0 then 1 else SineQPE.omega8) := by
      have hT0 : (Circuit.T (0 : Fin 1)).eval.1 = !![1, 0; 0, SineQPE.omega8] := by
        simpa [SineQPE.Gate1.toCircuit, SineQPE.Gate1.evalCyc, SineQPE.CyclotomicMat2.toMatrix,
          SineQPE.CyclotomicEight.toComplex] using SineQPE.Gate1.eval_toCircuit .T
      rw [hT0]
      ext a b; fin_cases a <;> fin_cases b <;> simp
    have hw : Complex.exp (Complex.I * ((π / 4 : ℝ) : ℂ)) = SineQPE.omega8 := by
      rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_four, Real.sin_pi_div_four, SineQPE.omega8]
      have hs2_sq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hs2_ne : (√2 : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
      field_simp [hs2_ne]
      push_cast
      ring_nf
      rw [hs2_sq]
      ring
    rw [hT, SineQPE.rzMatrix, ← Matrix.diagonal_smul]
    congr 1
    funext a
    fin_cases a
    · dsimp
      rw [← Complex.exp_add]
      convert Complex.exp_zero.symm; push_cast; ring
    · dsimp
      rw [← hw, ← Complex.exp_add]
      congr 1; push_cast; ring
  have hcnot :
      (SineQPE.cnotRzCnotCircuit (Circuit.T 0)).eval.1 =
        Complex.exp (Complex.I * ((π / 8 : ℝ) : ℂ)) •
          (SineQPE.parityRzUnitary (π / (2 : ℝ) ^ 2)).1 := by
    simp only [SineQPE.cnotRzCnotCircuit, SineQPE.parityRzUnitary, Circuit.sequence,
      Circuit.eval_seq, Circuit.eval_identity, one_mul, Submonoid.coe_mul, Circuit.eval_onRegister,
      QRegister.embedUnitary_val, SineQPE.rzUnitary, hT_rz]
    rw [(QRegister.singleton 1).embedMatrix_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [zzCoreCircuit, ite_eq_left rfl, hcnot, parityRzUnitary_eq_smul_zzCoreUnitary2, smul_smul,
    rzGlobalPhase, ← Complex.exp_add]
  have hzero : Complex.I * ((π / 8 : ℝ) : ℂ) +
      -Complex.I * ((π / (2 : ℝ) ^ (2 + 1) : ℝ) : ℂ) = 0 := by push_cast; ring
  rw [hzero, Complex.exp_zero, one_smul]

theorem norm_zzCoreCircuit_sub_le (k : ℕ) (hk : k ≠ 2) (cRz : ℕ → Circuit 1) :
    ‖(zzCoreCircuit k cRz).eval.1 - rzGlobalPhase k • (zzCoreUnitary2 k).1‖ ≤
      ‖(cRz k).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ k)‖ := by
  rw [zzCoreCircuit, ite_eq_right hk, ← parityRzUnitary_eq_smul_zzCoreUnitary2]
  exact SineQPE.norm_cnotRzCnotCircuit_sub_le (cRz k) (π / (2 : ℝ) ^ k)

theorem phaseShiftCircuit_two_eval (cRz : ℕ → Circuit 1) :
    (phaseShiftCircuit 2 cRz).eval.1 = (phaseShiftUnitary1 2).1 := by
  have hT : (Circuit.T (0 : Fin 1)).eval.1 = !![1, 0; 0, SineQPE.omega8] := by
    simpa [SineQPE.Gate1.toCircuit, SineQPE.Gate1.evalCyc, SineQPE.CyclotomicMat2.toMatrix,
      SineQPE.CyclotomicEight.toComplex] using SineQPE.Gate1.eval_toCircuit .T
  have hTinv : (Circuit.T (0 : Fin 1)).inverse.eval.1 = !![1, 0; 0, star SineQPE.omega8] := by
    rw [Circuit.eval_inverse, SineQPE.unitary_inv_val, hT]
    ext a b; fin_cases a <;> fin_cases b <;> simp [RCLike.star_def]
  have hw_inv : Complex.exp (2 * ↑π * Complex.I * ((-1 / 8 : ℝ) : ℂ)) = star SineQPE.omega8 := by
    have harg : 2 * (π : ℂ) * Complex.I * ((-1 / 8 : ℝ) : ℂ) =
        ((-(π / 4) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, SineQPE.omega8]
    simp only [RCLike.star_def, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal]
    have hs2_sq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs2_ne : (√2 : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    field_simp [hs2_ne]
    push_cast
    ring_nf
    rw [hs2_sq]
    ring
  rw [phaseShiftCircuit, ite_eq_left rfl, hTinv, phaseShiftUnitary1, diagPhaseUnitary_coe,
    diagPhaseMatrix]
  have hb0 : (basisBits 1 (0 : Fin (2 ^ 1)) 0).val = 0 := by decide
  have hb1 : (basisBits 1 (1 : Fin (2 ^ 1)) 0).val = 1 := by decide
  ext a b
  fin_cases a <;> fin_cases b
  · change (1 : ℂ) = Complex.exp (2 * ↑π * Complex.I * ↑(wireShiftPhase 1 0 2 0))
    rw [wireShiftPhase, hb0]
    simp
  · simp
  · simp
  · change star SineQPE.omega8 = Complex.exp (2 * ↑π * Complex.I * ↑(wireShiftPhase 1 0 2 1))
    rw [← hw_inv, wireShiftPhase, hb1]
    congr 1; push_cast; ring

theorem norm_phaseShiftCircuit_sub_le (M : ℕ) (hM : M ≠ 2) (cRz : ℕ → Circuit 1) :
    ‖(phaseShiftCircuit M cRz).eval.1 - rzGlobalPhase M • (phaseShiftUnitary1 M).1‖ ≤
      ‖(cRz M).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ M)‖ := by
  let uSinv := ((Circuit.S (0 : Fin 1)).inverse).eval
  have hS : (Circuit.S (0 : Fin 1)).eval.1 =
      Matrix.diagonal (fun i : Fin 2 ↦ if i = 0 then 1 else Complex.I) := by
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Circuit.S, PrimitiveGate.eval, Qubit.S]
  have hSinv : uSinv.1 = Matrix.diagonal (fun i : Fin 2 ↦ if i = 0 then 1 else -Complex.I) := by
    have hev : uSinv = ((Circuit.S (0 : Fin 1)).eval)⁻¹ :=
      Circuit.eval_inverse (Circuit.S (0 : Fin 1))
    rw [hev, SineQPE.unitary_inv_val, hS]
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have hideal :
      uSinv.1 * SineQPE.rzMatrix (π / (2 : ℝ) ^ M) =
        rzGlobalPhase M • (phaseShiftUnitary1 M).1 := by
    have hnegI : (-Complex.I : ℂ) = Complex.exp (2 * ↑π * Complex.I * ((-1 / 4 : ℝ) : ℂ)) := by
      have harg : 2 * (π : ℂ) * Complex.I * ((-1 / 4 : ℝ) : ℂ) =
          ((-(π / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    have hb0 : (basisBits 1 (0 : Fin (2 ^ 1)) 0).val = 0 := by decide
    have hb1 : (basisBits 1 (1 : Fin (2 ^ 1)) 0).val = 1 := by decide
    change uSinv.1 * SineQPE.rzMatrix (π / (2 : ℝ) ^ M) =
      rzGlobalPhase M • diagPhaseMatrix (wireShiftPhase 1 0 M)
    rw [hSinv, SineQPE.rzMatrix, diagPhaseMatrix, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_smul]
    congr 1
    funext a
    fin_cases a
    · change (1 : ℂ) * Complex.exp (-Complex.I * ↑(π / (2 : ℝ) ^ M / 2)) =
        rzGlobalPhase M * Complex.exp (2 * ↑π * Complex.I * ↑(wireShiftPhase 1 0 M 0))
      rw [one_mul, wireShiftPhase, hb0]
      simp only [Nat.cast_zero, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
        mul_one, rzGlobalPhase]
      congr 1; rw [pow_succ (2 : ℝ)]; push_cast; ring
    · change (-Complex.I) * Complex.exp (Complex.I * ↑(π / (2 : ℝ) ^ M / 2)) =
        rzGlobalPhase M * Complex.exp (2 * ↑π * Complex.I * ↑(wireShiftPhase 1 0 M 1))
      rw [hnegI, ← Complex.exp_add, wireShiftPhase, hb1, rzGlobalPhase, ← Complex.exp_add]
      congr 1; rw [pow_succ (2 : ℝ)]; push_cast; ring
  have hsub :
      (phaseShiftCircuit M cRz).eval.1 - rzGlobalPhase M • (phaseShiftUnitary1 M).1 =
        uSinv.1 * ((cRz M).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ M)) := by
    rw [phaseShiftCircuit, ite_eq_right hM, Circuit.eval_seq, Submonoid.coe_mul, ← hideal,
      Matrix.mul_sub]
  rw [hsub]
  calc ‖uSinv.1 * ((cRz M).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ M))‖
      ≤ ‖uSinv.1‖ * ‖(cRz M).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ M)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ‖(cRz M).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ M)‖ := by
        gcongr; exact SineQPE.unitary_opNorm_le_one uSinv
    _ = ‖(cRz M).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ M)‖ := one_mul _

/-! ## Section 4: `Unitary (2 ^ b)` ZZ Phase-Telescoping Equivalence -/

theorem diagPhaseUnitary_loopUnitary_inv {d : ℕ}
    (m : ℕ) (f : Fin m → Fin d → ℝ) (k : ℕ) :
    (QFT.loopUnitary m (fun i ↦ diagPhaseUnitary (f i)) k)⁻¹ =
      diagPhaseUnitary (fun j ↦
        ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), -f i j) := by
  have haux : ∀ rem k : ℕ, m - k = rem →
      (QFT.loopUnitary m (fun i ↦ diagPhaseUnitary (f i)) k)⁻¹ =
        diagPhaseUnitary (fun j ↦
          ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val), -f i j) := by
    intro rem
    induction rem with
    | zero =>
      intro k hrem
      have hempty : Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val) = ∅ := by ext i; simp; omega
      rw [QFT.loopUnitary_of_ge m _ (by omega), inv_one, hempty]
      simp only [Finset.sum_empty]
      exact diagPhaseUnitary_zero.symm
    | succ r ih =>
      intro k hrem
      have hk : k < m := by omega
      let ik : Fin m := ⟨k, hk⟩
      have hmem : ik ∈ Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val) := by simp [ik]
      have herase : (Finset.univ.filter (fun i : Fin m ↦ k ≤ i.val)).erase ik =
          Finset.univ.filter (fun i : Fin m ↦ k + 1 ≤ i.val) := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hne, hle⟩
          have hne_val : i.val ≠ k := fun hv ↦ hne (Fin.ext hv)
          omega
        · intro hle
          exact ⟨fun heq ↦ by have hv : i.val = k := congrArg Fin.val heq; omega, by omega⟩
      rw [QFT.loopUnitary_step m _ hk, _root_.mul_inv_rev, ih (k + 1) (by omega),
        ← diagPhaseUnitary_neg, ← diagPhaseUnitary_add]
      congr 1
      funext j
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [← Finset.add_sum_erase _ _ hmem, herase]
  exact haux (m - k) k rfl

/-- Sum of parity phases across `idx > ℓ` at stage `ℓ`. -/
noncomputable def zzInnerPhase (b : ℕ) (ℓ : Fin b) (j : Fin (2 ^ b)) : ℝ :=
  ∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
    zzParityPhase b idx ℓ (idx.val - ℓ.val + 1) j

/-- Total pre-Hadamard diagonal phase at stage `ℓ` (parity sum + telescoped target shift). -/
noncomputable def zzPreHPhase (b : ℕ) (ℓ : Fin b) (j : Fin (2 ^ b)) : ℝ :=
  zzInnerPhase b ℓ j + if ℓ.val + 1 < b then wireShiftPhase b ℓ (b - ℓ.val) j else 0

/-- Forward stage unitary whose inverse is `hadamardAt b ℓ * diagPhaseUnitary (zzPreHPhase b ℓ)`. -/
noncomputable def zzPhaseFwd (b : ℕ) (ℓ : Fin b) : Unitary (2 ^ b) :=
  diagPhaseUnitary (-zzPreHPhase b ℓ) * hadamardAt b ℓ

/-- Sum of post-Hadamard control-wire phases across `idx = 1 .. b - 1`. -/
noncomputable def zzPostCtrlPhase (b : ℕ) (j : Fin (2 ^ b)) : ℝ :=
  ∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ 1 ≤ idx.val),
    wireShiftPhase b idx (idx.val + 1) j

/-- Control-wire phases accumulated from stages `ℓ ≥ k`. -/
noncomputable def accCtrlPhase (b k : ℕ) (j : Fin (2 ^ b)) : ℝ :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin b ↦ k ≤ ℓ.val),
    ∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
      (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (idx.val - ℓ.val + 2))

theorem targSum_eq_wireShiftPhase (b : ℕ) (ℓ : Fin b) (j : Fin (2 ^ b)) :
    (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
        (-((basisBits b j ℓ).val : ℝ) / (2 : ℝ) ^ (idx.val - ℓ.val + 2))) =
      if ℓ.val + 1 < b then wireShiftPhase b ℓ (b - ℓ.val) j else 0 := by
  by_cases hlt : ℓ.val + 1 < b
  · rw [ite_eq_left hlt]
    let g (x : ℕ) : ℝ := 1 / (2 : ℝ) ^ (x - ℓ.val + 1)
    have hterm : ∀ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
        (-((basisBits b j ℓ).val : ℝ) / (2 : ℝ) ^ (idx.val - ℓ.val + 2)) =
          -((basisBits b j ℓ).val : ℝ) * (g idx.val - g (idx.val + 1)) := by
      intro idx hmem
      have hge : ℓ.val + 1 ≤ idx.val := (Finset.mem_filter.mp hmem).2
      have hstep : idx.val + 1 - ℓ.val + 1 = (idx.val - ℓ.val + 1) + 1 := by omega
      dsimp only [g]
      rw [hstep, show idx.val - ℓ.val + 2 = (idx.val - ℓ.val + 1) + 1 by omega, pow_succ]
      have h2ne : (2 : ℝ) ^ (idx.val - ℓ.val + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [h2ne]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_fin_ge_sub (ℓ.val + 1) (by omega) g]
    dsimp only [g, wireShiftPhase]
    rw [show ℓ.val + 1 - ℓ.val + 1 = 2 by omega]
    norm_num
    ring
  · rw [ite_eq_right hlt]
    have hempty : Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val) = ∅ := by
      ext idx; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]; have := idx.isLt; omega
    rw [hempty, Finset.sum_empty]

theorem accCtrlPhase_zero_eq (b : ℕ) : accCtrlPhase b 0 = zzPostCtrlPhase b := by
  funext j
  unfold accCtrlPhase zzPostCtrlPhase
  have huniv : Finset.univ.filter (fun ℓ : Fin b ↦ 0 ≤ ℓ.val) = Finset.univ := by ext ℓ; simp
  rw [huniv]
  have hinner (ℓ : Fin b) :
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
        (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (idx.val - ℓ.val + 2))) =
      ∑ idx : Fin b,
        if ℓ.val < idx.val then
          (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (idx.val - ℓ.val + 2))
        else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext idx; simp
  simp_rw [hinner]
  rw [Finset.sum_comm,
    ← Finset.sum_subset (Finset.filter_subset (fun idx : Fin b ↦ 1 ≤ idx.val) Finset.univ)]
  · refine Finset.sum_congr rfl fun idx hmem ↦ ?_
    have h1 : 1 ≤ idx.val := (Finset.mem_filter.mp hmem).2
    rw [← Finset.sum_filter]
    let g (x : ℕ) : ℝ := 1 / (2 : ℝ) ^ (idx.val + 2 - x)
    have hterm : ∀ ℓ ∈ Finset.univ.filter (fun ℓ : Fin b ↦ ℓ.val < idx.val),
        (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (idx.val - ℓ.val + 2)) =
          -((basisBits b j idx).val : ℝ) * (g (ℓ.val + 1) - g ℓ.val) := by
      intro ℓ hℓ
      have hlt : ℓ.val < idx.val := (Finset.mem_filter.mp hℓ).2
      dsimp only [g]
      rw [show idx.val + 2 - (ℓ.val + 1) = idx.val - ℓ.val + 1 by omega,
        show idx.val + 2 - ℓ.val = (idx.val - ℓ.val + 1) + 1 by omega,
        show idx.val - ℓ.val + 2 = (idx.val - ℓ.val + 1) + 1 by omega, pow_succ]
      have h2ne : (2 : ℝ) ^ (idx.val - ℓ.val + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [h2ne]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_fin_lt_sub idx.val (by omega) g]
    dsimp only [g, wireShiftPhase]
    rw [show idx.val + 2 - idx.val = 2 by omega, show idx.val + 2 - 0 = (idx.val + 1) + 1 by omega]
    norm_num
    ring
  · intro idx _ hnot
    have hz : idx.val = 0 := by simp at hnot; omega
    apply Finset.sum_eq_zero
    intro ℓ _
    simp [hz]

theorem outerLoopInv_eq_zzIdeal (b : ℕ) :
    (QFT.outerLoopUnitary b 0)⁻¹ =
      diagPhaseUnitary (zzPostCtrlPhase b) * (QFT.loopUnitary b (zzPhaseFwd b) 0)⁻¹ := by
  have haux : ∀ rem k : ℕ, b - k = rem →
      (QFT.outerLoopUnitary b k)⁻¹ =
        diagPhaseUnitary (accCtrlPhase b k) * (QFT.loopUnitary b (zzPhaseFwd b) k)⁻¹ := by
    intro rem
    induction rem with
    | zero =>
      intro k hrem
      have hge : b ≤ k := by omega
      have hzero : accCtrlPhase b k = (0 : Fin (2 ^ b) → ℝ) := by
        funext j
        unfold accCtrlPhase
        have hempty : Finset.univ.filter (fun ℓ : Fin b ↦ k ≤ ℓ.val) = ∅ := by
          ext ℓ; simp; have := ℓ.isLt; omega
        rw [hempty, Finset.sum_empty]
        rfl
      rw [QFT.outerLoopUnitary, QFT.outerLoopUnitaryGen, QFT.loopUnitary_of_ge b _ hge,
        QFT.loopUnitary_of_ge b _ hge, hzero, diagPhaseUnitary_zero, inv_one, one_mul]
    | succ r ih =>
      intro k hrem
      have hk : k < b := by omega
      let ℓ : Fin b := ⟨k, hk⟩
      let ctrlStep (j : Fin (2 ^ b)) : ℝ :=
        ∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ k + 1 ≤ idx.val),
          (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (idx.val - k + 2))
      have hinner_eq :
          (QFT.innerLoopUnitary b ℓ (k + 1))⁻¹ =
            diagPhaseUnitary ctrlStep * diagPhaseUnitary (zzPreHPhase b ℓ) := by
        change (QFT.loopUnitary b
          (fun idx ↦ diagPhaseUnitary (QFT.crPhase b idx ℓ (idx.val - k + 1))) (k + 1))⁻¹ = _
        rw [diagPhaseUnitary_loopUnitary_inv, ← diagPhaseUnitary_add]
        congr 1
        funext j
        simp only [Pi.add_apply, ctrlStep, zzPreHPhase, zzInnerPhase]
        have hsum :
            (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ k + 1 ≤ idx.val),
              -QFT.crPhase b idx ℓ (idx.val - k + 1) j) =
            (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ k + 1 ≤ idx.val),
              zzParityPhase b idx ℓ (idx.val - k + 1) j) +
            (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ k + 1 ≤ idx.val),
              (-((basisBits b j idx).val : ℝ) / (2 : ℝ) ^ (idx.val - k + 2))) +
            (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ k + 1 ≤ idx.val),
              (-((basisBits b j ℓ).val : ℝ) / (2 : ℝ) ^ (idx.val - k + 2))) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun idx _ ↦ ?_
          simpa [zzParityPhase, add_assoc] using neg_crPhase_eq_zz_add b idx ℓ (idx.val - k + 1) j
        rw [hsum]
        have htarg := targSum_eq_wireShiftPhase b ℓ j
        dsimp only [ℓ] at htarg ⊢
        rw [htarg]
        ring
      have hcomm_ctrl :
          hadamardAt b ℓ * diagPhaseUnitary ctrlStep =
            diagPhaseUnitary ctrlStep * hadamardAt b ℓ := by
        symm
        apply diagPhaseUnitary_comm_hadamardAt
        intro x y hxy
        dsimp only [ctrlStep]
        refine Finset.sum_congr rfl fun idx hmem ↦ ?_
        have hge : k + 1 ≤ idx.val := (Finset.mem_filter.mp hmem).2
        have hne : idx ≠ ℓ := fun heq ↦ by have hv : idx.val = k := congrArg Fin.val heq; omega
        rw [hxy idx hne]
      have hcomm_acc :
          hadamardAt b ℓ * diagPhaseUnitary (accCtrlPhase b (k + 1)) =
            diagPhaseUnitary (accCtrlPhase b (k + 1)) * hadamardAt b ℓ := by
        symm
        apply diagPhaseUnitary_comm_hadamardAt
        intro x y hxy
        unfold accCtrlPhase
        refine Finset.sum_congr rfl fun m hm ↦ Finset.sum_congr rfl fun idx hidx ↦ ?_
        have hmge : k + 1 ≤ m.val := (Finset.mem_filter.mp hm).2
        have hidge : m.val + 1 ≤ idx.val := (Finset.mem_filter.mp hidx).2
        have hne : idx ≠ ℓ := fun heq ↦ by have hv : idx.val = k := congrArg Fin.val heq; omega
        rw [hxy idx hne]
      have hphase_inv2 :
          (zzPhaseFwd b ℓ)⁻¹ = hadamardAt b ℓ * diagPhaseUnitary (zzPreHPhase b ℓ) := by
        rw [zzPhaseFwd, _root_.mul_inv_rev, SineQPE.hadamardAt_inv, ← diagPhaseUnitary_neg,
          neg_neg]
      have hacc_step :
          diagPhaseUnitary ctrlStep * diagPhaseUnitary (accCtrlPhase b (k + 1)) =
            diagPhaseUnitary (accCtrlPhase b k) := by
        rw [← diagPhaseUnitary_add]
        congr 1
        funext j
        simp only [Pi.add_apply, ctrlStep, accCtrlPhase]
        have hmem : ℓ ∈ Finset.univ.filter (fun m : Fin b ↦ k ≤ m.val) := by simp [ℓ]
        have herase : (Finset.univ.filter (fun m : Fin b ↦ k ≤ m.val)).erase ℓ =
            Finset.univ.filter (fun m : Fin b ↦ k + 1 ≤ m.val) := by
          ext m
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hne, hle⟩
            have hne_val : m.val ≠ k := fun hv ↦ hne (Fin.ext hv)
            omega
          · intro hle
            exact ⟨fun heq ↦ by have hv : m.val = k := congrArg Fin.val heq; omega, by omega⟩
        rw [← Finset.add_sum_erase _ _ hmem, herase]
      have hstep_lhs :
          (QFT.outerLoopUnitary b k)⁻¹ =
            (hadamardAt b ℓ * (QFT.innerLoopUnitary b ℓ (k + 1))⁻¹) *
              (QFT.outerLoopUnitary b (k + 1))⁻¹ := by
        rw [QFT.outerLoopUnitary, QFT.outerLoopUnitaryGen, QFT.loopUnitary_step b _ hk,
          _root_.mul_inv_rev, _root_.mul_inv_rev, SineQPE.hadamardAt_inv]
        rfl
      have hstep_rhs :
          (QFT.loopUnitary b (zzPhaseFwd b) k)⁻¹ =
            (zzPhaseFwd b ℓ)⁻¹ * (QFT.loopUnitary b (zzPhaseFwd b) (k + 1))⁻¹ := by
        rw [QFT.loopUnitary_step b _ hk, _root_.mul_inv_rev]
      rw [hstep_lhs, ih (k + 1) (by omega), hinner_eq, hstep_rhs, hphase_inv2]
      calc (hadamardAt b ℓ * (diagPhaseUnitary ctrlStep * diagPhaseUnitary (zzPreHPhase b ℓ))) *
              (diagPhaseUnitary (accCtrlPhase b (k + 1)) *
                (QFT.loopUnitary b (zzPhaseFwd b) (k + 1))⁻¹)
          = diagPhaseUnitary ctrlStep * hadamardAt b ℓ *
              (diagPhaseUnitary (zzPreHPhase b ℓ) * diagPhaseUnitary (accCtrlPhase b (k + 1))) *
              (QFT.loopUnitary b (zzPhaseFwd b) (k + 1))⁻¹ := by
            rw [← mul_assoc (hadamardAt b ℓ), hcomm_ctrl]
            simp only [mul_assoc]
        _ = diagPhaseUnitary ctrlStep *
              (hadamardAt b ℓ * diagPhaseUnitary (accCtrlPhase b (k + 1))) *
              diagPhaseUnitary (zzPreHPhase b ℓ) *
              (QFT.loopUnitary b (zzPhaseFwd b) (k + 1))⁻¹ := by
            rw [diagPhaseUnitary_comm (zzPreHPhase b ℓ) (accCtrlPhase b (k + 1))]
            simp only [mul_assoc]
        _ = (diagPhaseUnitary ctrlStep * diagPhaseUnitary (accCtrlPhase b (k + 1))) *
              (hadamardAt b ℓ * diagPhaseUnitary (zzPreHPhase b ℓ) *
                (QFT.loopUnitary b (zzPhaseFwd b) (k + 1))⁻¹) := by
            rw [hcomm_acc]
            simp only [mul_assoc]
        _ = diagPhaseUnitary (accCtrlPhase b k) *
              (hadamardAt b ℓ * diagPhaseUnitary (zzPreHPhase b ℓ) *
                (QFT.loopUnitary b (zzPhaseFwd b) (k + 1))⁻¹) := by
            rw [hacc_step]
  rw [← accCtrlPhase_zero_eq]
  exact haux b 0 rfl

/-! ## Section 5: Master ZZ-Telescoped Error Theorem & `fastIqft16HiCircuit` (`14,247 T`) -/

theorem norm_zzIqftFromRzCircuit_sub_le (b : ℕ) (cRz : ℕ → Circuit 1) (εRz : ℕ → ℝ)
    (hRz : ∀ k, 3 ≤ k → k ≤ b → ‖(cRz k).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ k)‖ ≤ εRz k) :
    ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1),
      ‖(zzIqftFromRzCircuit b cRz).eval.1 - (phasedIqftUnitary b ζ hζ).1‖ ≤
        (∑ ℓ : Fin b,
          ((∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val),
              if ℓ.val < idx.val then
                if idx.val - ℓ.val + 1 = 2 then 0 else εRz (idx.val - ℓ.val + 1)
              else 0) +
            if ℓ.val + 1 < b then
              if b - ℓ.val = 2 then 0 else εRz (b - ℓ.val)
            else 0)) +
        (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ 1 ≤ idx.val),
          if 1 ≤ idx.val then
            if idx.val + 1 = 2 then 0 else εRz (idx.val + 1)
          else 0) := by
  let ζCore (k : ℕ) : ℂ := if k = 2 then 1 else rzGlobalPhase k
  let εCore (k : ℕ) : ℝ := if k = 2 then 0 else εRz k
  have hζCore (k : ℕ) : ‖ζCore k‖ = 1 := by
    dsimp only [ζCore]
    split_ifs
    · exact norm_one
    · exact norm_rzGlobalPhase k
  have hShift (w : Fin b) (M : ℕ) (hM2 : 2 ≤ M) (hMb : M ≤ b) :
      ‖((phaseShiftCircuit M cRz).onRegister (QRegister.singleton w)).eval.1 -
          ζCore M • (diagPhaseUnitary (wireShiftPhase b w M)).1‖ ≤ εCore M := by
    let reg := QRegister.singleton w
    have hemb : reg.embedMatrix (ζCore M • (phaseShiftUnitary1 M).1) =
        ζCore M • (diagPhaseUnitary (wireShiftPhase b w M)).1 := by
      rw [reg.embedMatrix_smul, ← QRegister.embedUnitary_val,
        singleton_embedUnitary_phaseShiftUnitary1]
    rw [← hemb]
    refine (SineQPE.norm_onRegister_sub_le reg (phaseShiftCircuit M cRz) _).trans ?_
    dsimp only [ζCore, εCore]
    by_cases h2 : M = 2
    · rw [ite_eq_left h2, ite_eq_left h2, h2, one_smul, phaseShiftCircuit_two_eval, sub_self,
        norm_zero]
    · rw [ite_eq_right h2, ite_eq_right h2]
      exact (norm_phaseShiftCircuit_sub_le M h2 cRz).trans (hRz M (by omega) hMb)
  let ζInStep (ℓ idx : Fin b) : ℂ := if ℓ.val < idx.val then ζCore (idx.val - ℓ.val + 1) else 1
  let εInStep (ℓ idx : Fin b) : ℝ := if ℓ.val < idx.val then εCore (idx.val - ℓ.val + 1) else 0
  let ζIn (ℓ : Fin b) : ℂ :=
    ∏ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val), ζInStep ℓ idx
  let εIn (ℓ : Fin b) : ℝ :=
    ∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ ℓ.val + 1 ≤ idx.val), εInStep ℓ idx
  have hInner (ℓ : Fin b) :
      ‖ζIn ℓ‖ = 1 ∧
      ‖(zzInnerCircuit b cRz ℓ).eval.1 - ζIn ℓ • (diagPhaseUnitary (zzInnerPhase b ℓ)).1‖ ≤
        εIn ℓ := by
    let fIn (idx : Fin b) : Unitary (2 ^ b) :=
      diagPhaseUnitary (-zzParityPhase b idx ℓ (idx.val - ℓ.val + 1))
    have hloop := SineQPE.norm_revLoopCircuit_sub_le b
      (fun idx ↦
        if h : ℓ.val < idx.val then
          (zzCoreCircuit (idx.val - ℓ.val + 1) cRz).onRegister
            (QRegister.pair idx ℓ (by intro heq; subst heq; omega))
        else .identity)
      fIn (ζInStep ℓ) (εInStep ℓ) (ℓ.val + 1)
      (fun idx hle ↦ by
        have hlt : ℓ.val < idx.val := by omega
        dsimp only [ζInStep]; rw [ite_eq_left hlt]; exact hζCore _)
      (fun idx hle ↦ by
        have hlt : ℓ.val < idx.val := by omega
        have hne : idx ≠ ℓ := by intro heq; subst heq; omega
        let reg := QRegister.pair idx ℓ hne
        let k := idx.val - ℓ.val + 1
        dsimp only [ζInStep, εInStep]
        rw [dite_eq_left hlt, ite_eq_left hlt, ite_eq_left hlt]
        have hfinv : (fIn idx)⁻¹ = diagPhaseUnitary (zzParityPhase b idx ℓ k) := by
          dsimp only [fIn, k]; rw [← diagPhaseUnitary_neg, neg_neg]
        have hemb : reg.embedMatrix (ζCore k • (zzCoreUnitary2 k).1) =
            ζCore k • ((fIn idx)⁻¹).1 := by
          rw [hfinv, reg.embedMatrix_smul, ← QRegister.embedUnitary_val,
            pair_embedUnitary_zzCoreUnitary2]
        rw [← hemb]
        refine (SineQPE.norm_onRegister_sub_le reg (zzCoreCircuit k cRz) _).trans ?_
        dsimp only [ζCore, εCore]
        by_cases hk2 : k = 2
        · rw [ite_eq_left hk2, ite_eq_left hk2, hk2, one_smul, zzCoreCircuit_two_eval, sub_self,
            norm_zero]
        · rw [ite_eq_right hk2, ite_eq_right hk2]
          exact (norm_zzCoreCircuit_sub_le k hk2 cRz).trans
            (hRz k (by omega) (by have := idx.isLt; omega)))
    have hinv_eq : (QFT.loopUnitary b fIn (ℓ.val + 1))⁻¹ =
        diagPhaseUnitary (zzInnerPhase b ℓ) := by
      dsimp only [fIn]
      rw [diagPhaseUnitary_loopUnitary_inv]
      congr 1; funext j; refine Finset.sum_congr rfl fun idx _ ↦ ?_; simp
    rw [hinv_eq] at hloop
    exact hloop
  let ζStage (ℓ : Fin b) : ℂ := (if ℓ.val + 1 < b then ζCore (b - ℓ.val) else 1) * ζIn ℓ
  let εStage (ℓ : Fin b) : ℝ := εIn ℓ + if ℓ.val + 1 < b then εCore (b - ℓ.val) else 0
  have hPhase (ℓ : Fin b) :
      ‖ζStage ℓ‖ = 1 ∧
      ‖(zzOuterStep b cRz ℓ).eval.1 - ζStage ℓ • ((zzPhaseFwd b ℓ)⁻¹).1‖ ≤ εStage ℓ := by
    have hζS : ‖ζStage ℓ‖ = 1 := by
      dsimp only [ζStage]
      rw [norm_mul, (hInner ℓ).1, mul_one]
      split_ifs
      · exact hζCore _
      · exact norm_one
    refine ⟨hζS, ?_⟩
    let preH : Circuit b :=
      if ℓ.val + 1 < b then
        .seq (zzInnerCircuit b cRz ℓ)
          ((phaseShiftCircuit (b - ℓ.val) cRz).onRegister (QRegister.singleton ℓ))
      else zzInnerCircuit b cRz ℓ
    have hpre : ‖preH.eval.1 - ζStage ℓ • (diagPhaseUnitary (zzPreHPhase b ℓ)).1‖ ≤ εStage ℓ := by
      dsimp only [preH, ζStage, εStage]
      by_cases hlt : ℓ.val + 1 < b
      · rw [ite_eq_left hlt, ite_eq_left hlt, ite_eq_left hlt, Circuit.eval_seq, Submonoid.coe_mul]
        have hph : diagPhaseUnitary (zzPreHPhase b ℓ) =
            diagPhaseUnitary (wireShiftPhase b ℓ (b - ℓ.val)) *
              diagPhaseUnitary (zzInnerPhase b ℓ) := by
          rw [← diagPhaseUnitary_add]
          congr 1; funext j; simp [zzPreHPhase, hlt, add_comm]
        have hsmul :
            (ζCore (b - ℓ.val) * ζIn ℓ) • (diagPhaseUnitary (zzPreHPhase b ℓ)).1 =
              (ζCore (b - ℓ.val) • (diagPhaseUnitary (wireShiftPhase b ℓ (b - ℓ.val))).1) *
                (ζIn ℓ • (diagPhaseUnitary (zzInnerPhase b ℓ)).1) := by
          rw [hph, Submonoid.coe_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [hsmul, add_comm (εIn ℓ)]
        have hV₂ : ‖ζCore (b - ℓ.val) • (diagPhaseUnitary (wireShiftPhase b ℓ (b - ℓ.val))).1‖ ≤
            1 := by
          rw [norm_smul, hζCore, one_mul]; exact SineQPE.unitary_opNorm_le_one _
        exact (SineQPE.norm_mul_sub_mul_of_le_one (SineQPE.unitary_opNorm_le_one _) hV₂).trans
          (add_le_add (hShift ℓ (b - ℓ.val) (by omega) (by omega)) (hInner ℓ).2)
      · rw [ite_eq_right hlt, ite_eq_right hlt, ite_eq_right hlt, one_mul, add_zero]
        have hph : zzPreHPhase b ℓ = zzInnerPhase b ℓ := by funext j; simp [zzPreHPhase, hlt]
        rw [hph]
        exact (hInner ℓ).2
    have hphase_inv2 : (zzPhaseFwd b ℓ)⁻¹ = hadamardAt b ℓ * diagPhaseUnitary (zzPreHPhase b
      ℓ) := by
      rw [zzPhaseFwd, _root_.mul_inv_rev, SineQPE.hadamardAt_inv, ← diagPhaseUnitary_neg, neg_neg]
    have hsub : (zzOuterStep b cRz ℓ).eval.1 - ζStage ℓ • ((zzPhaseFwd b ℓ)⁻¹).1 =
        (hadamardAt b ℓ).1 *
          (preH.eval.1 - ζStage ℓ • (diagPhaseUnitary (zzPreHPhase b ℓ)).1) := by
      change (Circuit.H ℓ).eval.1 * preH.eval.1 - ζStage ℓ • ((zzPhaseFwd b ℓ)⁻¹).1 = _
      rw [SineQPE.eval_H_eq_hadamardAt, hphase_inv2, Submonoid.coe_mul, ← Matrix.mul_smul,
        ← Matrix.mul_sub]
    rw [hsub]
    calc ‖(hadamardAt b ℓ).1 * (preH.eval.1 - ζStage ℓ • (diagPhaseUnitary (zzPreHPhase b ℓ)).1)‖
        ≤ ‖(hadamardAt b ℓ).1‖ *
            ‖preH.eval.1 - ζStage ℓ • (diagPhaseUnitary (zzPreHPhase b ℓ)).1‖ :=
          Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * εStage ℓ :=
          mul_le_mul (SineQPE.unitary_opNorm_le_one _) hpre (norm_nonneg _) zero_le_one
      _ = εStage ℓ := one_mul _
  obtain ⟨hζOut, hOut⟩ := SineQPE.norm_revLoopCircuit_sub_le b (zzOuterStep b cRz) (zzPhaseFwd b)
    ζStage εStage 0 (fun ℓ _ ↦ (hPhase ℓ).1) (fun ℓ _ ↦ (hPhase ℓ).2)
  have huniv : Finset.univ.filter (fun ℓ : Fin b ↦ 0 ≤ ℓ.val) = Finset.univ := by ext ℓ; simp
  rw [huniv] at hζOut hOut
  let ζOut : ℂ := ∏ ℓ : Fin b, ζStage ℓ
  let fPost (idx : Fin b) : Unitary (2 ^ b) :=
    diagPhaseUnitary (-wireShiftPhase b idx (idx.val + 1))
  let ζPostStep (idx : Fin b) : ℂ := if 1 ≤ idx.val then ζCore (idx.val + 1) else 1
  let εPostStep (idx : Fin b) : ℝ := if 1 ≤ idx.val then εCore (idx.val + 1) else 0
  obtain ⟨hζPost, hPost⟩ := SineQPE.norm_revLoopCircuit_sub_le b
    (fun idx ↦
      if 1 ≤ idx.val then
        (phaseShiftCircuit (idx.val + 1) cRz).onRegister (QRegister.singleton idx)
      else .identity)
    fPost ζPostStep εPostStep 1
    (fun idx h1 ↦ by dsimp only [ζPostStep]; rw [ite_eq_left h1]; exact hζCore _)
    (fun idx h1 ↦ by
      dsimp only [ζPostStep, εPostStep]
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
      have hfinv : (fPost idx)⁻¹ = diagPhaseUnitary (wireShiftPhase b idx (idx.val + 1)) := by
        dsimp only [fPost]; rw [← diagPhaseUnitary_neg, neg_neg]
      rw [hfinv]
      exact hShift idx (idx.val + 1) (by omega) (by have := idx.isLt; omega))
  have hpost_inv : (QFT.loopUnitary b fPost 1)⁻¹ = diagPhaseUnitary (zzPostCtrlPhase b) := by
    dsimp only [fPost]
    rw [diagPhaseUnitary_loopUnitary_inv]
    congr 1; funext j; refine Finset.sum_congr rfl fun idx _ ↦ ?_; simp
  rw [hpost_inv] at hPost
  let ζPost : ℂ := ∏ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ 1 ≤ idx.val), ζPostStep idx
  let ζTot : ℂ := ζPost * ζOut
  have hζTot : ‖ζTot‖ = 1 := by rw [norm_mul, hζPost, hζOut, mul_one]
  refine ⟨ζTot, hζTot, ?_⟩
  let cPreSwap : Circuit b :=
    .seq (SineQPE.revLoopCircuit b (zzOuterStep b cRz) 0) (zzPostCtrlLayer b cRz)
  have hpreSwap :
      ‖cPreSwap.eval.1 - ζTot • ((QFT.outerLoopUnitary b 0)⁻¹).1‖ ≤
        (∑ ℓ : Fin b, εStage ℓ) +
          (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ 1 ≤ idx.val), εPostStep idx) := by
    dsimp only [cPreSwap, ζTot]
    rw [Circuit.eval_seq, Submonoid.coe_mul, outerLoopInv_eq_zzIdeal b, Submonoid.coe_mul]
    have hsmul :
        (ζPost * ζOut) • ((diagPhaseUnitary (zzPostCtrlPhase b)).1 *
            ((QFT.loopUnitary b (zzPhaseFwd b) 0)⁻¹).1) =
          (ζPost • (diagPhaseUnitary (zzPostCtrlPhase b)).1) *
            (ζOut • ((QFT.loopUnitary b (zzPhaseFwd b) 0)⁻¹).1) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hsmul, add_comm (∑ ℓ : Fin b, εStage ℓ)]
    have hV₂ : ‖ζPost • (diagPhaseUnitary (zzPostCtrlPhase b)).1‖ ≤ 1 := by
      rw [norm_smul, hζPost, one_mul]; exact SineQPE.unitary_opNorm_le_one _
    exact (SineQPE.norm_mul_sub_mul_of_le_one (SineQPE.unitary_opNorm_le_one _) hV₂).trans
      (add_le_add hPost hOut)
  have hfinal_sub :
      (zzIqftFromRzCircuit b cRz).eval.1 - (phasedIqftUnitary b ζTot hζTot).1 =
        (QFT.swapAllUnitary b).1 *
          (cPreSwap.eval.1 - ζTot • ((QFT.outerLoopUnitary b 0)⁻¹).1) := by
    change (SineQPE.swapAllCircuit b).eval.1 * cPreSwap.eval.1 - ζTot • (QFT.qftMatrix b)ᴴ = _
    rw [SineQPE.swapAllCircuit_eval, ← swapAll_mul_outerLoopInv_eq_iqftMatrix,
      Submonoid.coe_mul, ← Matrix.mul_smul, ← Matrix.mul_sub]
  rw [hfinal_sub]
  calc ‖(QFT.swapAllUnitary b).1 * (cPreSwap.eval.1 - ζTot • ((QFT.outerLoopUnitary b 0)⁻¹).1)‖
      ≤ ‖(QFT.swapAllUnitary b).1‖ *
          ‖cPreSwap.eval.1 - ζTot • ((QFT.outerLoopUnitary b 0)⁻¹).1‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ((∑ ℓ : Fin b, εStage ℓ) +
          (∑ idx ∈ Finset.univ.filter (fun idx : Fin b ↦ 1 ≤ idx.val), εPostStep idx)) :=
        mul_le_mul (SineQPE.unitary_opNorm_le_one _) hpreSwap (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Weighted sum across all `133` non-`k = 2` `Rz(π / 2^k)` calls in `16`-qubit ZZ `QFT†`. -/
def zzWeightedSum16 (w : ℕ → ℕ) : ℕ :=
  (∑ ℓ : Fin 16,
    ((∑ idx ∈ Finset.univ.filter (fun idx : Fin 16 ↦ ℓ.val + 1 ≤ idx.val),
        if ℓ.val < idx.val then
          if idx.val - ℓ.val + 1 = 2 then 0 else w (idx.val - ℓ.val + 1)
        else 0) +
      if ℓ.val + 1 < 16 then
        if 16 - ℓ.val = 2 then 0 else w (16 - ℓ.val)
      else 0)) +
  (∑ idx ∈ Finset.univ.filter (fun idx : Fin 16 ↦ 1 ≤ idx.val),
    if 1 ≤ idx.val then
      if idx.val + 1 = 2 then 0 else w (idx.val + 1)
    else 0)

private theorem zzRealSum16_eq (w : ℕ → ℕ) (s : ℝ) :
    (∑ ℓ : Fin 16,
      ((∑ idx ∈ Finset.univ.filter (fun idx : Fin 16 ↦ ℓ.val + 1 ≤ idx.val),
          if ℓ.val < idx.val then
            if idx.val - ℓ.val + 1 = 2 then (0 : ℝ) else (w (idx.val - ℓ.val + 1) : ℝ) * s
          else 0) +
        if ℓ.val + 1 < 16 then
          if 16 - ℓ.val = 2 then (0 : ℝ) else (w (16 - ℓ.val) : ℝ) * s
        else 0)) +
    (∑ idx ∈ Finset.univ.filter (fun idx : Fin 16 ↦ 1 ≤ idx.val),
      if 1 ≤ idx.val then
        if idx.val + 1 = 2 then (0 : ℝ) else (w (idx.val + 1) : ℝ) * s
      else 0) = (zzWeightedSum16 w : ℝ) * s := by
  unfold zzWeightedSum16
  rw [Nat.cast_add, add_mul, Nat.cast_sum, Finset.sum_mul, Nat.cast_sum, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
    rw [Nat.cast_add, add_mul, Nat.cast_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun idx _ ↦ ?_
      by_cases h1 : ℓ.val < idx.val
      · by_cases h2 : idx.val - ℓ.val + 1 = 2 <;>
          simp only [h1, h2, ↓reduceIte, Nat.cast_zero, zero_mul]
      · simp only [h1, ↓reduceIte, Nat.cast_zero, zero_mul]
    · by_cases h1 : ℓ.val + 1 < 16
      · by_cases h2 : 16 - ℓ.val = 2 <;>
          simp only [h1, h2, ↓reduceIte, Nat.cast_zero, zero_mul]
      · simp only [h1, ↓reduceIte, Nat.cast_zero, zero_mul]
  · refine Finset.sum_congr rfl fun idx _ ↦ ?_
    by_cases h1 : 1 ≤ idx.val
    · by_cases h2 : idx.val + 1 = 2 <;>
        simp only [h1, h2, ↓reduceIte, Nat.cast_zero, zero_mul]
    · simp only [h1, ↓reduceIte, Nat.cast_zero, zero_mul]

private theorem cycMat2_eq_su2Matrix_of_eqVal {M : OuterWeights.SineWindowPrep.CycMat2}
    (hda : M.d.eqVal M.a.conj = true) (hbc : M.b.eqVal M.c.conj.opp = true) :
    M.toMatrix = SineQPE.su2Matrix (M.toMatrix 0 0) (M.toMatrix 1 0) := by
  have hdaC := OuterWeights.SineWindowPrep.Cyc8.toComplex_eq_of_eqVal hda
  have hbcC := OuterWeights.SineWindowPrep.Cyc8.toComplex_eq_of_eqVal hbc
  rw [OuterWeights.SineWindowPrep.Cyc8.toComplex_conj] at hdaC
  rw [OuterWeights.SineWindowPrep.Cyc8.toComplex_opp,
    OuterWeights.SineWindowPrep.Cyc8.toComplex_conj] at hbcC
  have hpow_star : (starRingEnd ℂ) (((√2 : ℂ) ^ M.k)⁻¹) = ((√2 : ℂ) ^ M.k)⁻¹ := by
    have hr : ((√2 : ℂ) ^ M.k)⁻¹ = ((((√2 : ℝ) ^ M.k)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hr, Complex.conj_ofReal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OuterWeights.SineWindowPrep.CycMat2.toMatrix, SineQPE.su2Matrix, smul_eq_mul, one_div,
      inv_pow,
      hdaC, hbcC, RCLike.star_def, mul_neg]

/-- Pure-`ℕ` verifier certifying that single-qubit Clifford+`T` word `w` approximates `Rz(θ)`
within operator-norm error `epsNum / 10^24` given trig certificate `(cMid, sMid, eUlps)`. -/
def checkRzWordNatLe (w : List OuterWeights.SineWindowPrep.Gate1)
    (cMid sMid : OuterWeights.SineWindowPrep.SInt) (eUlps epsNum : ℕ) : Bool :=
  OuterWeights.SineWindowPrep.withForcedCycMat2 (OuterWeights.SineWindowPrep.evalWordCyc w) fun M ↦
    M.d.eqVal M.a.conj && M.b.eqVal M.c.conj.opp &&
      OuterWeights.SineWindowPrep.withForcedNat (M.k / 2 + 1) fun q ↦
      OuterWeights.SineWindowPrep.withForcedNat (2 ^ q) fun pow2q ↦
      OuterWeights.SineWindowPrep.withForcedNat
        (OuterWeights.SineWindowPrep.coordNumBound pow2q
          (OuterWeights.SineWindowPrep.cycReAB M.k M.a) cMid eUlps) fun n1 ↦
      OuterWeights.SineWindowPrep.withForcedNat
        (OuterWeights.SineWindowPrep.coordNumBound pow2q
          (OuterWeights.SineWindowPrep.cycImAB M.k M.a) sMid.opp eUlps) fun n2 ↦
      OuterWeights.SineWindowPrep.withForcedNat
        (OuterWeights.SineWindowPrep.coordNumBound pow2q
          (OuterWeights.SineWindowPrep.cycReAB M.k M.c) (.ofNat 0) 0) fun n3 ↦
      OuterWeights.SineWindowPrep.withForcedNat
        (OuterWeights.SineWindowPrep.coordNumBound pow2q
          (OuterWeights.SineWindowPrep.cycImAB M.k M.c) (.ofNat 0) 0) fun n4 ↦
        decide (n1 * n1 + n2 * n2 + n3 * n3 + n4 * n4 ≤ (epsNum * pow2q) ^ 2)

theorem checkRzWordNatLe_sound {w : List OuterWeights.SineWindowPrep.Gate1}
    {t : OuterWeights.SineWindowPrep.TrigCert} {θ : ℝ} {epsNum : ℕ}
    (ht : t.Valid (θ / 2))
    (hok : checkRzWordNatLe w t.cMid t.sMid t.eUlps epsNum = true) :
    ‖(OuterWeights.SineWindowPrep.wordToCircuit1 w).eval.1 - SineQPE.rzMatrix θ‖ ≤
      (epsNum : ℝ) * (1 / (OuterWeights.SineWindowPrep.scale24 : ℝ)) := by
  unfold checkRzWordNatLe at hok
  simp only [OuterWeights.SineWindowPrep.withForcedCycMat2_eq,
    OuterWeights.SineWindowPrep.withForcedNat_eq,
    Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hda, hbc⟩, hsum_nat⟩ := hok
  let S : ℝ := (OuterWeights.SineWindowPrep.scale24 : ℝ)
  let M := OuterWeights.SineWindowPrep.evalWordCyc w
  let U := (OuterWeights.SineWindowPrep.wordToCircuit1 w).eval
  have hUM : U.1 = M.toMatrix := (OuterWeights.SineWindowPrep.evalWordCyc_toMatrix w).symm
  have hM_su2 : M.toMatrix = SineQPE.su2Matrix (M.toMatrix 0 0) (M.toMatrix 1 0) :=
    cycMat2_eq_su2Matrix_of_eqVal hda hbc
  have hU_su2 : U.1 = SineQPE.su2Matrix (U.1 0 0) (U.1 1 0) := by
    have h00 : U.1 0 0 = M.toMatrix 0 0 := congrFun (congrFun hUM 0) 0
    have h10 : U.1 1 0 = M.toMatrix 1 0 := congrFun (congrFun hUM 1) 0
    rw [h00, h10, ← hM_su2, hUM]
  let q := M.k / 2 + 1
  let pow2q := 2 ^ q
  let SP : ℝ := S * (pow2q : ℝ)
  have hSP_pos : 0 < SP := by dsimp [SP, S, pow2q, OuterWeights.SineWindowPrep.scale24]; positivity
  have hcos : |Real.cos (θ / 2) - t.cMid.toReal / S| ≤ (t.eUlps : ℝ) / S := ht.1
  have hsin : |-Real.sin (θ / 2) - t.sMid.opp.toReal / S| ≤ (t.eUlps : ℝ) / S := by
    rw [OuterWeights.SineWindowPrep.SInt.toReal_opp,
      show -Real.sin (θ / 2) - -t.sMid.toReal / S = -(Real.sin (θ / 2) - t.sMid.toReal / S) by
        ring,
      abs_neg]
    exact ht.2
  have h0_bound :
      |(0 : ℝ) - (OuterWeights.SineWindowPrep.SInt.ofNat 0).toReal / S| ≤ ((0 : ℕ) : ℝ) / S := by
    simp [OuterWeights.SineWindowPrep.SInt.toReal_ofNat]
  have hb1 := OuterWeights.SineWindowPrep.coordNumBound_spec
    (OuterWeights.SineWindowPrep.cycReAB_spec M.k M.a) hcos
  have hb2 := OuterWeights.SineWindowPrep.coordNumBound_spec
    (OuterWeights.SineWindowPrep.cycImAB_spec M.k M.a) hsin
  have hb3 := OuterWeights.SineWindowPrep.coordNumBound_spec
    (OuterWeights.SineWindowPrep.cycReAB_spec M.k M.c) h0_bound
  have hb4 := OuterWeights.SineWindowPrep.coordNumBound_spec
    (OuterWeights.SineWindowPrep.cycImAB_spec M.k M.c) h0_bound
  have h00_val : U.1 0 0 = (1 / (√2 : ℂ)) ^ M.k * M.a.toComplex := by rw [hUM]; rfl
  have h10_val : U.1 1 0 = (1 / (√2 : ℂ)) ^ M.k * M.c.toComplex := by rw [hUM]; rfl
  have hre00 : (U.1 0 0).re - Real.cos (θ / 2) =
      ((1 / (√2 : ℂ)) ^ M.k * M.a.toComplex).re - Real.cos (θ / 2) := by rw [h00_val]
  have him00 : (U.1 0 0).im - (-Real.sin (θ / 2)) =
      ((1 / (√2 : ℂ)) ^ M.k * M.a.toComplex).im - (-Real.sin (θ / 2)) := by rw [h00_val]
  have hre10 : (U.1 1 0).re - 0 = ((1 / (√2 : ℂ)) ^ M.k * M.c.toComplex).re - 0 := by rw [h10_val]
  have him10 : (U.1 1 0).im - 0 = ((1 / (√2 : ℂ)) ^ M.k * M.c.toComplex).im - 0 := by rw [h10_val]
  let n1 := OuterWeights.SineWindowPrep.coordNumBound pow2q
    (OuterWeights.SineWindowPrep.cycReAB M.k M.a) t.cMid t.eUlps
  let n2 := OuterWeights.SineWindowPrep.coordNumBound pow2q
    (OuterWeights.SineWindowPrep.cycImAB M.k M.a) t.sMid.opp t.eUlps
  let n3 := OuterWeights.SineWindowPrep.coordNumBound pow2q
    (OuterWeights.SineWindowPrep.cycReAB M.k M.c) (.ofNat 0) 0
  let n4 := OuterWeights.SineWindowPrep.coordNumBound pow2q
    (OuterWeights.SineWindowPrep.cycImAB M.k M.c) (.ofNat 0) 0
  have hsq1 : SP ^ 2 * ((U.1 0 0).re - Real.cos (θ / 2)) ^ 2 ≤ (n1 : ℝ) ^ 2 := by
    rw [← mul_pow, hre00, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
  have hsq2 : SP ^ 2 * ((U.1 0 0).im - (-Real.sin (θ / 2))) ^ 2 ≤ (n2 : ℝ) ^ 2 := by
    rw [← mul_pow, him00, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb2 2
  have hsq3 : SP ^ 2 * ((U.1 1 0).re - 0) ^ 2 ≤ (n3 : ℝ) ^ 2 := by
    rw [← mul_pow, hre10, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb3 2
  have hsq4 : SP ^ 2 * ((U.1 1 0).im - 0) ^ 2 ≤ (n4 : ℝ) ^ 2 := by
    rw [← mul_pow, him10, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb4 2
  have hsumR :
      (n1 : ℝ) ^ 2 + (n2 : ℝ) ^ 2 + (n3 : ℝ) ^ 2 + (n4 : ℝ) ^ 2 ≤
        ((epsNum : ℝ) * (pow2q : ℝ)) ^ 2 := by
    have hc : (n1 * n1 + n2 * n2 + n3 * n3 + n4 * n4 : ℝ) ≤
        (((epsNum * pow2q) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsum_nat
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, sq] using hc
  let eps : ℝ := (epsNum : ℝ) * (1 / S)
  have heps_nonneg : 0 ≤ eps := by dsimp [eps, S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hS_ne : S ≠ 0 := by dsimp [S, OuterWeights.SineWindowPrep.scale24]; positivity
  have hdel : (epsNum : ℝ) * (pow2q : ℝ) = SP * eps := by
    dsimp [SP, eps]
    calc (epsNum : ℝ) * (pow2q : ℝ)
        = (epsNum : ℝ) * (pow2q : ℝ) * (S * S⁻¹) := by rw [mul_inv_cancel₀ hS_ne, mul_one]
      _ = S * (pow2q : ℝ) * ((epsNum : ℝ) * (1 / S)) := by rw [one_div]; ring
  rw [hdel, mul_pow] at hsumR
  have hscaled :
      SP ^ 2 * (((U.1 0 0).re - Real.cos (θ / 2)) ^ 2 +
        ((U.1 0 0).im - (-Real.sin (θ / 2))) ^ 2 +
        ((U.1 1 0).re - 0) ^ 2 + ((U.1 1 0).im - 0) ^ 2) ≤
      SP ^ 2 * eps ^ 2 := by linarith
  have hsum_err := le_of_mul_le_mul_left hscaled (sq_pos_of_pos hSP_pos)
  rw [hU_su2, SineQPE.rzMatrix_eq_su2Matrix]
  apply SineQPE.norm_su2Matrix_sub_le heps_nonneg
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im, zero_mul,
    one_mul, zero_add, sub_zero]
  linarith

/-- Scaled `cos(π / 131072)` midpoint at `10^24` (`L = 65536 = 2^16`). -/
def fastC0Mid : ℕ := 999999999712756706849414

/-- Scaled `sin(π / 131072)` midpoint at `10^24` (`L = 65536 = 2^16`). -/
def fastS0Mid : ℕ := 23968449808418218729

private theorem fastBaseTrig_ok :
    OuterWeights.SineWindowPrep.checkBaseTrigNat 65536 fastC0Mid fastS0Mid = true := by
  decide +kernel

/-- `T`-gate count per synthesized `Rz(π / 2^k)` word (`k = 3 .. 16`). -/
def fastRz16CountT : ℕ → ℕ
  | 3 => 92 | 4 => 96 | 5 => 96 | 6 => 92 | 7 => 94 | 8 => 96 | 9 => 96
  | 10 => 98 | 11 => 94 | 12 => 94 | 13 => 94 | 14 => 94 | 15 => 94 | 16 => 96
  | _ => 0

/-- Error numerator at `10^24` per synthesized `Rz(π / 2^k)` word (`k = 3 .. 16`). -/
def fastRz16EpsNum : ℕ → ℕ
  | 3 => 167927641877721
  | 4 => 111644748718690
  | 5 => 286277131607326
  | 6 => 386937305421085
  | 7 => 269459167388534
  | 8 => 318438090054180
  | 9 => 484277318870706
  | 10 => 254332419803808
  | 11 => 203006859746028
  | 12 => 136645707485174
  | 13 => 250594561926979
  | 14 => 492964889247127
  | 15 => 357930523797411
  | 16 => 247890884777829
  | _ => 0

/-- Pure-`ℕ` verifier certifying the `k`-th synthesized `Rz(π / 2^k)` word (`3 ≤ k ≤ 16`). -/
def checkFastQft16Word (k : ℕ) (w : List OuterWeights.SineWindowPrep.Gate1) : Bool :=
  let t0 : OuterWeights.SineWindowPrep.TrigCert := ⟨.ofNat fastC0Mid, .ofNat fastS0Mid, 1000000⟩
  OuterWeights.SineWindowPrep.withForcedTrigRes
    (OuterWeights.SineWindowPrep.iterDoubleTrig (16 - k) t0) fun tr okr ↦
    okr &&
      checkRzWordNatLe w tr.cMid tr.sMid tr.eUlps (fastRz16EpsNum k) &&
      (OuterWeights.SineWindowPrep.wordCountT w == fastRz16CountT k)

theorem checkFastQft16Word_sound {k : ℕ} {w : List OuterWeights.SineWindowPrep.Gate1}
    (hk3 : 3 ≤ k) (hk16 : k ≤ 16) (h : checkFastQft16Word k w = true) :
    ‖(OuterWeights.SineWindowPrep.wordToCircuit1 w).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ k)‖ ≤
      (fastRz16EpsNum k : ℝ) * (1 / (OuterWeights.SineWindowPrep.scale24 : ℝ)) ∧
    OuterWeights.SineWindowPrep.wordCountT w = fastRz16CountT k := by
  unfold checkFastQft16Word at h
  simp only [OuterWeights.SineWindowPrep.withForcedTrigRes_eq, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at h
  obtain ⟨hokr, hwr, hwt⟩ := h
  refine ⟨?_, hwt⟩
  obtain ⟨_hL, ht0⟩ := OuterWeights.SineWindowPrep.checkBaseTrigNat_valid fastBaseTrig_ok
  have htr := OuterWeights.SineWindowPrep.iterDoubleTrig_valid (16 - k) ht0 hokr
  have hk_add : (16 - k) + k = 16 := by omega
  have hpow : (2 : ℝ) ^ (16 - k) * (2 : ℝ) ^ k = (65536 : ℝ) := by
    rw [← pow_add, hk_add]; norm_num
  have h2k_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hang : (2 ^ (16 - k) : ℝ) * (π / (2 * (65536 : ℝ))) = (π / (2 : ℝ) ^ k) / 2 := by
    apply mul_right_cancel₀ (by positivity : (2 : ℝ) * (2 : ℝ) ^ k ≠ 0)
    calc (2 ^ (16 - k) : ℝ) * (π / (2 * (65536 : ℝ))) * (2 * (2 : ℝ) ^ k)
        = ((2 : ℝ) ^ (16 - k) * (2 : ℝ) ^ k) * (π / 65536) := by ring
      _ = (65536 : ℝ) * (π / 65536) := by rw [hpow]
      _ = π := by ring
      _ = π / (2 : ℝ) ^ k * (2 : ℝ) ^ k := (div_mul_cancel₀ π h2k_ne).symm
      _ = (π / (2 : ℝ) ^ k) / 2 * (2 * (2 : ℝ) ^ k) := by ring
  have hc65 : ((65536 : ℕ) : ℝ) = (65536 : ℝ) := by norm_num
  rw [hc65, hang] at htr
  exact checkRzWordNatLe_sound htr hwr

/-! ## Section 7: Synthesized `fastIqft16Circuit` (`12,603 T`, `≤ 36 / 10 ^ 9`) -/

/-- Decodes `fuel` base-`8` digits (`1=H, 2=T, 3=S, 4=X, 5=Z`, `0=stop`) into `List Gate1`. -/
def decodeGate1Nat : ℕ → ℕ → List OuterWeights.SineWindowPrep.Gate1
  | 0, _ => []
  | fuel + 1, code =>
    let d := code % 8
    if d == 0 then []
    else
      let g : OuterWeights.SineWindowPrep.Gate1 :=
        if d == 1 then .H
        else if d == 2 then .T
        else if d == 3 then .S
        else if d == 4 then .X
        else .Z
      g :: decodeGate1Nat fuel (code / 8)

/-- Synthesized `Gate1` word for `Rz(π / 2^16)`. -/
def fastWord16 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 253
    (0x45a2d168b45a28b45a28b45168a2d145a2d168a28b45a2d145a28a2d14514 * 2 ^ 512 +
     0x5168b45168a2d168a2d168b45a28b45168a2d168b45145a28a2d145a28a28b45 * 2 ^ 256 +
     0xa2d145a28b45a2d145a2d168a2d168a2d145a2d168b45168a2d168a28a855959)

/-- Synthesized `Gate1` word for `Rz(π / 2^15)`. -/
def fastWord15 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 240
    (0xd145a28a2d145145168a2d145a2d145168a2d145145a2d145a2 * 2 ^ 512 +
     0x8b45a28b45145a2d168a2d168b45a2d168a2d145168a2d145a28a28a2d168a28 * 2 ^ 256 +
     0xb45a28b45a2d145168a2d145145145a28b45168a2d168a2d168a2d168b45a959)

/-- Synthesized `Gate1` word for `Rz(π / 2^14)`. -/
def fastWord14 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 245
    (0x45145a28a2d145a2d168a2d168a28a28b45145a28a2d168b45168a2 * 2 ^ 512 +
     0x8a2d145a28a2d168b45a28a28b45168b45a2d145168b45168a2d145145a28b45 * 2 ^ 256 +
     0x145145a2d145a2d168b45168b45a2d168b45a28a28b45a2d168b4516a152c2cb)

/-- Synthesized `Gate1` word for `Rz(π / 2^13)`. -/
def fastWord13 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 238
    (0x22d168a2d145168a2d168b45a28b45a28a28a28b45145a2d16 * 2 ^ 512 +
     0x8a28a2d168b45145168b45168a28b45168b45168b45a28b45a28b45168a28b45 * 2 ^ 256 +
     0x168a28b45168b45a28a2d145a28b45a28a28b45a28b45a28a2d168a2d168a28b)

/-- Synthesized `Gate1` word for `Rz(π / 2^12)`. -/
def fastWord12 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 249
    (0x2d168b45a2d168b45a2d168a2d145145a28a2d168a2d168a28b45a28a2 * 2 ^ 512 +
     0x8b45a28a28b45a28b45145168a28b45145a2d168a28a2d168a2d145168b45168 * 2 ^ 256 +
     0xb45a28b45a2d168a2d168a2d145a2d168b45a28b45145a28a2d168b4516a9729)

/-- Synthesized `Gate1` word for `Rz(π / 2^11)`. -/
def fastWord11 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 252
    (0xd168b45a2d145145a2d168a2d145168a2d168b45a2d145a28a28b45a2d14 * 2 ^ 512 +
     0x5a2d145a2d168b45a2d168a2d145a2d168b45168b45168a2d168a2d168b45168 * 2 ^ 256 +
     0xb45a28a2d145168b45a2d145168a2d168b45a28a2d168a2d145145a28b45a8e1)

/-- Synthesized `Gate1` word for `Rz(π / 2^10)`. -/
def fastWord10 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 249
    (0x68a2d168a28b45a28a28b45a2d145a2d145145a28b45a2d168a28a2d16 * 2 ^ 512 +
     0x8a2d168a28b45168a2d145a28b45168b45a2d168a28a2d145145145145145a2d * 2 ^ 256 +
     0x145168a28b45a28a2d145145a2d168b45a28a2d168a2d145a2d14516a155ca5a)

/-- Synthesized `Gate1` word for `Rz(π / 2^9)`. -/
def fastWord9 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 242
    (0x145145145a2d168a2d145a2d168a28b45a28a2d145a28a28b4516 * 2 ^ 512 +
     0x8b45145a28b45a28a2d145145145168a28b45a28b45a2d145145a28a2d145145 * 2 ^ 256 +
     0x145a2d168a2d145a2d168b45a2d145a28a2d168b45a28a2d168a28a2d145aa59)

/-- Synthesized `Gate1` word for `Rz(π / 2^8)`. -/
def fastWord8 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 245
    (0x65168a28b45a28b45168b45145168b45a28a28a28a28a2d145168b4 * 2 ^ 512 +
     0x5145145168b45145145a28b45145a2d145a28b45a28a28b45a2d145168b45a28 * 2 ^ 256 +
     0xa28a2d145a2d145a2d168a2d145a2d168a2d168a2d168b45a28a2d14516acacb)

/-- Synthesized `Gate1` word for `Rz(π / 2^7)`. -/
def fastWord7 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 244
    (0x5a2d145168a2d168a28b45a2d168a28a2d168a2d145a28b45168a2 * 2 ^ 512 +
     0xd145145145a2d168b45145168b45a28a28a28b45a28a2d168b45168a28a28b45 * 2 ^ 256 +
     0xa2d145a2d168b45a28b45168a28a28b45168a28b45a2d145a28a2d16a150b94b)

/-- Synthesized `Gate1` word for `Rz(π / 2^6)`. -/
def fastWord6 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 238
    (0x32d145a28b45168b45168a28b45a2d145a28b45168a28a28a2 * 2 ^ 512 +
     0xd168b45145168b45a2d145a28b45a28a28a28a28a28a28b45a2d168b45145168 * 2 ^ 256 +
     0xb45a2d168a28a2d168a28b45145a2d145a28a2d168b45a2d145a2d145a855859)

/-- Synthesized `Gate1` word for `Rz(π / 2^5)`. -/
def fastWord5 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 242
    (0x328a28b45168a2d145145168a28b45168a28a28b45145168b4516 * 2 ^ 512 +
     0x8a28b45a2d145168a2d145168b45a28a2d168a28a2d145a2d145a2d168a28b45 * 2 ^ 256 +
     0xa28a28b45a2d168b45a28a2d145a2d145a2d145145a28a2d145a28a2d168b561)

/-- Synthesized `Gate1` word for `Rz(π / 2^4)`. -/
def fastWord4 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 249
    (0x45a28a2d168a2d168b45a2d145a28b45145145168a28b45a2d145145a2 * 2 ^ 512 +
     0x8a2d145145a28a2d168b45a28b45145a28a2d145a2d168a28b45a2d145168b45 * 2 ^ 256 +
     0x168a2d145145a2d168b45a2d168a28b45a2d168b45168a2d145a2d145a851729)

/-- Synthesized `Gate1` word for `Rz(π / 2^3)`. -/
def fastWord3 : List OuterWeights.SineWindowPrep.Gate1 :=
  decodeGate1Nat 234
    (0x22d145145a28b45168b45145a2d145a28a28a2d168a2d14 * 2 ^ 512 +
     0x5145168b45168b45145a28b45a2d145a2d168a2d145168b45145a28b45168b45 * 2 ^ 256 +
     0x168a2d168a2d145145a2d168b45145145168b45a28b45168a28a28b4542aca59)

private theorem fastWord3_ok : checkFastQft16Word 3 fastWord3 = true := by
  decide +kernel
private theorem fastWord4_ok : checkFastQft16Word 4 fastWord4 = true := by
  decide +kernel
private theorem fastWord5_ok : checkFastQft16Word 5 fastWord5 = true := by
  decide +kernel
private theorem fastWord6_ok : checkFastQft16Word 6 fastWord6 = true := by
  decide +kernel
private theorem fastWord7_ok : checkFastQft16Word 7 fastWord7 = true := by
  decide +kernel
private theorem fastWord8_ok : checkFastQft16Word 8 fastWord8 = true := by
  decide +kernel
private theorem fastWord9_ok : checkFastQft16Word 9 fastWord9 = true := by
  decide +kernel
private theorem fastWord10_ok : checkFastQft16Word 10 fastWord10 = true := by
  decide +kernel
private theorem fastWord11_ok : checkFastQft16Word 11 fastWord11 = true := by
  decide +kernel
private theorem fastWord12_ok : checkFastQft16Word 12 fastWord12 = true := by
  decide +kernel
private theorem fastWord13_ok : checkFastQft16Word 13 fastWord13 = true := by
  decide +kernel
private theorem fastWord14_ok : checkFastQft16Word 14 fastWord14 = true := by
  decide +kernel
private theorem fastWord15_ok : checkFastQft16Word 15 fastWord15 = true := by
  decide +kernel
private theorem fastWord16_ok : checkFastQft16Word 16 fastWord16 = true := by
  decide +kernel

attribute [irreducible] fastWord3 fastWord4 fastWord5 fastWord6 fastWord7 fastWord8 fastWord9
attribute [irreducible] fastWord10 fastWord11 fastWord12 fastWord13 fastWord14 fastWord15
attribute [irreducible] fastWord16

/-- Synthesized single-qubit `Rz(π / 2^k)` circuit (`k = 3 .. 16`) for `16`-qubit ZZ `QFT†`. -/
def fastRz16Circuit : ℕ → Circuit 1
  | 3 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord3
  | 4 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord4
  | 5 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord5
  | 6 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord6
  | 7 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord7
  | 8 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord8
  | 9 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord9
  | 10 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord10
  | 11 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord11
  | 12 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord12
  | 13 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord13
  | 14 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord14
  | 15 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord15
  | 16 => OuterWeights.SineWindowPrep.wordToCircuit1 fastWord16
  | _ => .identity

@[simp]
theorem fastRz16Circuit_count_toff (k : ℕ) :
    (fastRz16Circuit k).count PrimitiveGate.TOFF = 0 := by
  match k with
  | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 =>
      dsimp [fastRz16Circuit]; exact OuterWeights.SineWindowPrep.count_wordToCircuit1_toff _
  | 0 | 1 | 2 => rfl
  | _ + 17 => rfl

@[simp]
theorem fastRz16Circuit_count_t (k : ℕ) :
    (fastRz16Circuit k).count PrimitiveGate.T = fastRz16CountT k := by
  match k with
  | 3 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord3_ok).2
  | 4 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord4_ok).2
  | 5 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord5_ok).2
  | 6 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord6_ok).2
  | 7 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord7_ok).2
  | 8 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord8_ok).2
  | 9 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord9_ok).2
  | 10 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord10_ok).2
  | 11 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord11_ok).2
  | 12 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord12_ok).2
  | 13 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord13_ok).2
  | 14 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord14_ok).2
  | 15 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord15_ok).2
  | 16 =>
      rw [fastRz16Circuit, OuterWeights.SineWindowPrep.count_wordToCircuit1_t]
      exact (checkFastQft16Word_sound (by decide) (by decide) fastWord16_ok).2
  | 0 | 1 | 2 => rfl
  | _ + 17 => rfl

theorem norm_fastRz16Circuit_sub_le (k : ℕ) (hk3 : 3 ≤ k) (hk16 : k ≤ 16) :
    ‖(fastRz16Circuit k).eval.1 - SineQPE.rzMatrix (π / (2 : ℝ) ^ k)‖ ≤
      (fastRz16EpsNum k : ℝ) * (1 / (OuterWeights.SineWindowPrep.scale24 : ℝ)) := by
  interval_cases k
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord3_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord4_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord5_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord6_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord7_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord8_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord9_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord10_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord11_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord12_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord13_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord14_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord15_ok).1
  · rw [fastRz16Circuit]; exact (checkFastQft16Word_sound hk3 hk16 fastWord16_ok).1

/-- Ancilla-free `16`-qubit ZZ-telescoped `QFT†` (`TOFF = 0`, `T = 12,603`,
operator-norm error `≤ 36 / 10 ^ 9`). -/
def fastIqft16Circuit : Circuit 16 :=
  zzIqftFromRzCircuit 16 fastRz16Circuit

@[simp]
theorem fastIqft16Circuit_count_toff :
    fastIqft16Circuit.count PrimitiveGate.TOFF = 0 :=
  zzIqftFromRzCircuit_count_toff 16 fastRz16Circuit fastRz16Circuit_count_toff

@[simp]
theorem fastIqft16Circuit_count_t :
    fastIqft16Circuit.count PrimitiveGate.T = 12603 := by
  rw [fastIqft16Circuit, zzIqftFromRzCircuit_count_t]
  simp_rw [fastRz16Circuit_count_t]
  decide +kernel

theorem norm_fastIqft16Circuit_sub_le :
    ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1),
      ‖fastIqft16Circuit.eval.1 - (phasedIqftUnitary 16 ζ hζ).1‖ ≤ 36 / 10 ^ 9 := by
  obtain ⟨ζ, hζ, hbound⟩ := norm_zzIqftFromRzCircuit_sub_le 16 fastRz16Circuit
    (fun k ↦ (fastRz16EpsNum k : ℝ) * (1 / (OuterWeights.SineWindowPrep.scale24 : ℝ)))
    norm_fastRz16Circuit_sub_le
  refine ⟨ζ, hζ, hbound.trans ?_⟩
  rw [zzRealSum16_eq fastRz16EpsNum (1 / (OuterWeights.SineWindowPrep.scale24 : ℝ))]
  have hsum : zzWeightedSum16 fastRz16EpsNum = 35992033677685357 := by decide +kernel
  rw [hsum]
  norm_num [OuterWeights.SineWindowPrep.scale24]

end ApproxIqft16

namespace PhaseSwar

open Operator QProg Matrix Real
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open OuterWeights.SineWindowPrep
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNe2 (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 1: Pure-`ℕ` Unitary, `FastSU2`, and `4 × 128`-Bit SWAR Verifiers -/
/-- Packed `2 × 2` Clifford+`T` unitary state `(1 / √2) ^ k` with determinant `ω₈ ^ p`. -/
structure FastSU2 where
  /-- Denominator exponent `(1 / √2) ^ k`. -/
  k : ℕ
  /-- Determinant phase exponent `p` modulo `8` (`det = ω₈ ^ p`). -/
  p : ℕ
  /-- `(0, 0)` cyclotomic numerator. -/
  a : OuterWeights.SineWindowPrep.Cyc8
  /-- `(1, 0)` cyclotomic numerator. -/
  c : OuterWeights.SineWindowPrep.Cyc8
  /-- Accumulated `.T` gate count. -/
  tCnt : ℕ

/-- Identity state in `FastSU2`. -/
def FastSU2.init : FastSU2 :=
  ⟨0, 0, OuterWeights.SineWindowPrep.Cyc8.one, OuterWeights.SineWindowPrep.Cyc8.zero, 0⟩

/-- Single-gate left-multiplication step on `FastSU2`. -/
def stepGateSU2 (g : OuterWeights.SineWindowPrep.Gate1) (st : FastSU2) : FastSU2 :=
  FastSU2.casesOn st fun k p a c t ↦
    match g with
    | .X =>
      OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 4) 8) fun p' ↦
        ⟨k, p', c, a, t⟩
    | .Z =>
      OuterWeights.SineWindowPrep.Cyc8.casesOn c.oppStrict fun c0 c1 c2 c3 ↦
      OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 4) 8) fun p' ↦
        ⟨k, p', a, ⟨c0, c1, c2, c3⟩, t⟩
    | .S =>
      OuterWeights.SineWindowPrep.Cyc8.casesOn c.mulIStrict fun c0 c1 c2 c3 ↦
      OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 2) 8) fun p' ↦
        ⟨k, p', a, ⟨c0, c1, c2, c3⟩, t⟩
    | .T =>
      OuterWeights.SineWindowPrep.Cyc8.casesOn c.mulOmegaStrict fun c0 c1 c2 c3 ↦
      OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 1) 8) fun p' ↦
      OuterWeights.SineWindowPrep.withForcedNat (Nat.add t 1) fun t' ↦
        ⟨k, p', a, ⟨c0, c1, c2, c3⟩, t'⟩
    | .H =>
      OuterWeights.SineWindowPrep.Cyc8.casesOn (a.addStrict c) fun a0 a1 a2 a3 ↦
      OuterWeights.SineWindowPrep.Cyc8.casesOn (a.subStrict c) fun c0 c1 c2 c3 ↦
      OuterWeights.SineWindowPrep.withForcedNat (Nat.add k 1) fun k' ↦
      OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 4) 8) fun p' ↦
        ⟨k', p', ⟨a0, a1, a2, a3⟩, ⟨c0, c1, c2, c3⟩, t⟩

/-- Fused `5`-gate `[.Z, .S, .T, .Z, .H]` Clifford+`T` syllable step on `FastSU2`. -/
def stepZSTZH (st : FastSU2) : FastSU2 :=
  FastSU2.casesOn st fun k p a c t ↦
    OuterWeights.SineWindowPrep.Cyc8.casesOn c.mulOmegaStrict fun w0 w1 w2 w3 ↦
    OuterWeights.SineWindowPrep.Cyc8.casesOn (OuterWeights.SineWindowPrep.Cyc8.mk w0 w1 w2
      w3).mulIStrict
      fun m0 m1 m2 m3 ↦
    let cw : OuterWeights.SineWindowPrep.Cyc8 := ⟨m0, m1, m2, m3⟩
    OuterWeights.SineWindowPrep.Cyc8.casesOn (a.addStrict cw) fun a0 a1 a2 a3 ↦
    OuterWeights.SineWindowPrep.Cyc8.casesOn (a.subStrict cw) fun c0 c1 c2 c3 ↦
    OuterWeights.SineWindowPrep.withForcedNat (Nat.add k 1) fun k' ↦
    OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 7) 8) fun p' ↦
    OuterWeights.SineWindowPrep.withForcedNat (Nat.add t 1) fun t' ↦
      ⟨k', p', ⟨a0, a1, a2, a3⟩, ⟨c0, c1, c2, c3⟩, t'⟩

/-- Fused `5`-gate `[.Z, .S, .T, .S, .H]` Clifford+`T` syllable step on `FastSU2`. -/
def stepZSTSH (st : FastSU2) : FastSU2 :=
  FastSU2.casesOn st fun k p a c t ↦
    OuterWeights.SineWindowPrep.Cyc8.casesOn c.mulOmegaStrict fun m0 m1 m2 m3 ↦
    let cw : OuterWeights.SineWindowPrep.Cyc8 := ⟨m0, m1, m2, m3⟩
    OuterWeights.SineWindowPrep.Cyc8.casesOn (a.addStrict cw) fun a0 a1 a2 a3 ↦
    OuterWeights.SineWindowPrep.Cyc8.casesOn (a.subStrict cw) fun c0 c1 c2 c3 ↦
    OuterWeights.SineWindowPrep.withForcedNat (Nat.add k 1) fun k' ↦
    OuterWeights.SineWindowPrep.withForcedNat (Nat.mod (Nat.add p 5) 8) fun p' ↦
    OuterWeights.SineWindowPrep.withForcedNat (Nat.add t 1) fun t' ↦
      ⟨k', p', ⟨a0, a1, a2, a3⟩, ⟨c0, c1, c2, c3⟩, t'⟩

/-- Decode one `3`-bit syllable (`1 = ZSTZH`, `2 = ZSTSH`, `3..7 = H,S,T,X,Z`) to `Gate1` list. -/
def decodeSyl1 : ℕ → List OuterWeights.SineWindowPrep.Gate1
  | 1 => [.Z, .S, .T, .Z, .H]
  | 2 => [.Z, .S, .T, .S, .H]
  | 3 => [.H]
  | 4 => [.S]
  | 5 => [.T]
  | 6 => [.X]
  | 7 => [.Z]
  | _ => []

/-- `3`-bit syllable step matching `decodeSyl1`. -/
def stepCodeSU2 : ℕ → FastSU2 → FastSU2
  | 1, st => stepZSTZH st
  | 2, st => stepZSTSH st
  | 3, st => stepGateSU2 .H st
  | 4, st => stepGateSU2 .S st
  | 5, st => stepGateSU2 .T st
  | 6, st => stepGateSU2 .X st
  | 7, st => stepGateSU2 .Z st
  | _, st => st

/-- Decode up to `n` base-`8` syllables packed little-endian into `code : ℕ`. -/
def decodeChunkAux : ℕ → ℕ → List OuterWeights.SineWindowPrep.Gate1
  | 0, _ => []
  | n + 1, code =>
    let d := Nat.mod code 8
    if Nat.beq d 0 then []
    else decodeSyl1 d ++ decodeChunkAux n (Nat.div code 8)

/-- Evaluate up to `n` base-`8` syllables packed little-endian into `code : ℕ`. -/
def evalChunkAux : ℕ → ℕ → FastSU2 → FastSU2
  | 0, _, st => st
  | n + 1, code, st =>
    let d := Nat.mod code 8
    if Nat.beq d 0 then st
    else evalChunkAux n (Nat.div code 8) (stepCodeSU2 d st)

/-- Decode a list of `20`-syllable base-`8` chunks into a `Gate1` word. -/
def decodeChunks : List ℕ → List OuterWeights.SineWindowPrep.Gate1
  | [] => []
  | ch :: chs => decodeChunkAux (4 * 5) ch ++ decodeChunks chs

/-- Evaluate a list of `20`-syllable base-`8` chunks on `FastSU2`. -/
def evalChunksSU2 : List ℕ → FastSU2 → FastSU2
  | [], st => st
  | ch :: chs, st => evalChunksSU2 chs (evalChunkAux (4 * 5) ch st)

/-- Predicate testing whether syllable `d` is in `{1, 2}`. -/
@[inline] def is12SWAR (d : ℕ) : Bool := Nat.ble 1 d && Nat.ble d 2

/-- Branch-free natural absolute difference `|x - y|`. -/
@[inline] def absDiffNat (x y : ℕ) : ℕ :=
  Bool.casesOn (Nat.ble y x) (Nat.sub y x) (Nat.sub x y)

/-- Scaled cyclotomic coordinate error bound from positive/negative split parts. -/
def coordBoundPosNeg (pow2q p1 n1 p2 n2 tPos tNeg eUlps : ℕ) : ℕ :=
  let pos := Nat.add (Nat.add (Nat.mul p1 scale24) (Nat.mul p2 s2Nat)) (Nat.mul tNeg pow2q)
  let neg := Nat.add (Nat.add (Nat.mul n1 scale24) (Nat.mul n2 s2Nat)) (Nat.mul tPos pow2q)
  Nat.add (Nat.add (absDiffNat pos neg) (absDiffNat p2 n2)) (Nat.mul pow2q eUlps)

/-- Nonnegative part of `SInt` as `ℕ`. -/
def sintPos (x : SInt) : ℕ := Bool.casesOn x.neg x.mag 0
/-- Negated part of `SInt` as `ℕ`. -/
def sintNeg (x : SInt) : ℕ := Bool.casesOn x.neg 0 x.mag

section SWARProofs
end SWARProofs
/-- Binary decision tree over LSB-first `ℕ` bitmasks (`const` short-circuits `and`/`xor`). -/
inductive BTree where
  /-- Constant Boolean leaf. -/
  | const (b : Bool) : BTree
  /-- Branch on `y % 2 = 0` (`lo`) vs `y % 2 = 1` (`hi`), continuing on `y / 2`. -/
  | branch (lo hi : BTree) : BTree

/-- Evaluate `t : BTree` at integer bitmask `y : ℕ`. -/
def BTree.eval : BTree → ℕ → Bool
  | .const b, _ => b
  | .branch lo hi, y =>
    if Nat.beq (y % 2) 0 then lo.eval (y / 2) else hi.eval (y / 2)

end PhaseSwar

namespace MultiGearQPE

open Operator QProg Matrix HermitianMat Real WalkQPEBridge WalkQPEBridgeXMeas
open WalkQPEFlexBridge QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open SineWindowFlexM
open BlockReflection
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ChunkedPulledMaster11
open PhaseSwar
open OuterWeights.SineWindowPrep SineWindowFlex OuterWeights.GroverUniform
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowInlinePhase5 (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ### Self-Contained `M = 46687` SWAR Sine Windows (`2030 T` and `2026 T`) -/

@[simp] theorem tensorWalkCat_smul_right {bCat mOut mMid : ℕ}
    (v : Fin (2 ^ walkWidth mOut mMid) → ℂ) (α : ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    tensorWalkCat v (α • cat) = α • tensorWalkCat v cat := by
  funext g; simp only [tensorWalkCat, Pi.smul_apply, smul_eq_mul]; ring
/-- Active `out` width. -/ abbrev outRemWidth (a ko : ℕ) : ℕ := blockRemWidth (mOutUB a) 8 ko
/-- Clean-zero outer prefix. -/ abbrev outZeroPrefixReg (a ko : ℕ) (ho : ko ≤ a) :
    QRegister ko (mOutUB a) := blockZeroReg (mOutUB a) 8 ko (by dsimp [mOutUB]; omega)
/-- Active outer complement. -/ abbrev outRemComplementReg (a ko : ℕ) (ho : ko ≤ a) :
    QRegister (outRemWidth a ko) (mOutUB a) :=
  blockComplementReg (mOutUB a) 8 ko (by dsimp [mOutUB]; omega)
/-- Combined width. -/ abbrev combARem (a b ko km : ℕ) : ℕ := outRemWidth a ko + midRemWidth b km
/-- Combined `(ko, km)` reduced-reflection bundle on `(mOutUB a, mMidUB b)`. -/
def combWalkReflRegs (bCat a b ko km : ℕ) (ho : ko ≤ a) (hm : km ≤ b) :
    WalkReflRegs bCat (mOutUB a) (mMidUB b) (combARem a b ko km) (midRemWidth b km) :=
  reducedOutMidWalkReflRegs bCat (mOutUB a) (mMidUB b)
    (outRemComplementReg a ko ho) (midRemComplementReg b km hm)
    (by dsimp [combARem, outRemWidth, midRemWidth, blockRemWidth, mOutUB, mMidUB]; omega)
    (by dsimp [midRemWidth, blockRemWidth, mMidUB]; omega)
theorem combWalkReflCovers (bQPE bCat a b mLow s ko km : ℕ) (ho : ko ≤ a) (hm : km ≤ b) :
    WalkReflCovers bQPE bCat (mOutUB a) (mMidUB b) mLow s
      (combWalkReflRegs bCat a b ko km ho hm)
      (liftOutMidZeroToAnc (mOutUB a) (mMidUB b)
        (outZeroPrefixReg a ko ho) (midZeroPrefixReg b km hm)) :=
  reducedOutMidWalkReflCovers bQPE bCat (mOutUB a) (mMidUB b) mLow s
    (outRemComplementReg a ko ho) (midRemComplementReg b km hm) _ _
    (outZeroPrefixReg a ko ho) (midZeroPrefixReg b km hm)
    (blockComplementReg_cover (mOutUB a) 8 ko _) (blockComplementReg_cover (mMidUB b) 5 km _)
/-- Total ancilla count (`bCat = 11`). -/ abbrev combAncillas (a b ko km mLow s : ℕ) : ℕ :=
  cat11TotalAncillas 16 (mOutUB a) (mMidUB b) mLow (combARem a b ko km) (midRemWidth b km) s
/-- Total local qubit count. -/ abbrev combQubits (a b ko km mLow s : ℕ) : ℕ :=
  cat11TotalQubits 16 (mOutUB a) (mMidUB b) mLow (combARem a b ko km) (midRemWidth b km) s
/-- Local `(nUB a b + 11)`-wire `(walk, cat)` register inside `combQubits`. -/
abbrev combWalkCatReg (a b ko km mLow s : ℕ) :
    QRegister (nUB a b + 11) (combQubits a b ko km mLow s) :=
  rWalkCatLoc 16 11 (mOutUB a) (mMidUB b) mLow (combARem a b ko km) (midRemWidth b km) s
theorem comb_hbScr16 (a b ko km mLow s : ℕ) (ho : ko ≤ a) (hm : km ≤ b) :
    16 - 2 ≤ scrAncillas 16 mLow (combARem a b ko km) (midRemWidth b km) s := by
  have h1 : 15 ≤ combARem a b ko km := by
    dsimp [combARem, outRemWidth, midRemWidth, blockRemWidth, mOutUB, mMidUB]; omega
  have h2 := scr_ge_lowCtrl 16 mLow (combARem a b ko km) (midRemWidth b km) s; omega
/-- Clean two-reflection realization hypothesis on `(combWalkCatReg, rFullZeroLoc)`. -/
abbrev CleanWalkRefl2 {Var : Type} [Fintype Var] [DecidableEq Var] (a b ko km mLow s : ℕ)
    (ho : ko ≤ a) (hm : km ≤ b) (v : Var) (uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB a)
      (mMidUB b))) (pRefl2 : DynamicCircuit Var (combQubits a b ko km mLow s)) : Prop :=
  QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.CleanRealizes v
    (combWalkCatReg a b ko km mLow s)
    (rFullZeroLoc 16 11 (mOutUB a) (mMidUB b) mLow (combARem a b ko km) (midRemWidth b km) s
      (liftOutMidZeroToAnc (mOutUB a) (mMidUB b) (outZeroPrefixReg a ko ho)
        (midZeroPrefixReg b km hm))) uRefl2 pRefl2
/-- Catalytic `L²` double-reflection error bound against `QubitisedWalk.reflPulledUnitary` on
`uB`. -/
noncomputable abbrev WalkRefl2ErrLe (a b : ℕ) (uB : Unitary (2 ^ nUB a b))
    (uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB a) (mMidUB b))) (δStep : ℝ) : Prop :=
  ∀ x : Fin (2 ^ nUB a b) → ℂ,
    ‖WithLp.toLp 2 (uRefl2.1 *ᵥ tensorWalkCat x
      (CircuitModular.phaseGradientLowFactor
      11 3) -
        tensorWalkCat ((QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB a) (mMidUB b)) uB).1 *ᵥ
          x)
          (CircuitModular.phaseGradientLowFactor
            11 3))‖ ≤
      δStep * ‖WithLp.toLp 2 (tensorWalkCat x
        (CircuitModular.phaseGradientLowFactor
        11 3))‖
/-- Variational upper-bound hypothesis `E₀(63e) ≤ eRef` on `thcHamiltonian P450.dfthc`. -/
noncomputable abbrev P450RefVarBound (eRef : ℝ) : Prop :=
  ∀ (T : ℝ), (∀ (E' : ℝ) (φ : Fin (2 ^ (2 * 58)) → ℂ),
    (thcHamiltonian P450.dfthc *ᵥ φ = (E' : ℂ) • φ ∧
      electronSectorProjector (2 * 58) 63 *ᵥ φ = φ ∧ φ ≠ 0) → T ≤ E' + 0.1) → T ≤ eRef + 0.1
/-- Bundled `PulledSOSBlockEncoding` + clean `2`-reflection + `L²` step-error + variational. -/
noncomputable abbrev ReordSosHyp {Var : Type} [Fintype Var] [DecidableEq Var]
    (a b ko km mLow s : ℕ) (ho : ko ≤ a) (hm : km ≤ b) (v : Var) (uB : Unitary (2 ^ nUB a b))
    (uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB a) (mMidUB b)))
    (pRefl2 : DynamicCircuit Var (combQubits a b ko km mLow s)) (δStep eRef : ℝ) : Prop :=
  PulledSOSBlockEncoding (mOutUB a) (mMidUB b) p450HBlocked dfthcLowerBound 97.3864 uB ∧
    CleanWalkRefl2 a b ko km mLow s ho hm v uRefl2 pRefl2 ∧
    0 ≤ δStep ∧ WalkRefl2ErrLe a b uB uRefl2 δStep ∧ P450RefVarBound eRef
/-- Target `MeasuresLowEnergies_local` + clean zero-workspace realization predicate for `P450`. -/
noncomputable abbrev RealizesP450GroundQPE {Var : Type} [Fintype Var] [DecidableEq Var]
    {n m : ℕ} [NeZero (2 ^ n)] (rSys : QRegister systemQubits_local n) (rAnc : QRegister m n)
    (hdisj : rSys.DisjointWires rAnc) (prog : DynamicCircuit Var n) : Prop :=
  ∃ W : Unitary (2 ^ (systemQubits_local + m)),
    MeasuresLowEnergies_local (thcHamiltonian P450.dfthc) p450Eta p450Delta p450Eps W ∧
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W prog.compile
private theorem exp_two_pi_I_nat2 (q : ℕ) :
    Complex.exp (2 * π * Complex.I * (q : ℂ)) = 1 := by
  rw [show (2 : ℂ) * π * Complex.I * (q : ℂ) =
      (q : ℂ) * (π * Complex.I + π * Complex.I) by ring,
    Complex.exp_nat_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring_nf

private theorem iqft16_apply (y m : Fin (2 ^ 16)) : (QFT.qftMatrix 16)ᴴ y m =
    (1 / 256 : ℂ) * Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ)) := by
  change star (QFT.qftMatrix 16 m y) = _
  simp only [QFT.qftMatrix, qpeAngle, star_mul', Complex.star_def, ← Complex.exp_conj]
  rw [show √(2 ^ 16 : ℝ) = 256 by
      rw [show (2 ^ 16 : ℝ) = (256 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    show (starRingEnd ℂ) (1 / (256 : ℝ) : ℂ) = (1 / 256 : ℂ) by simp [map_ofNat]]
  congr 2; simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_div₀]
  push_cast; ring

private noncomputable def gPoleSum (u : ℝ) : ℝ :=
  (24 / 15625) / (u + 8 / 10000) ^ 2 + (6 / 625) / (u + 5 / 1000) ^ 2 +
    (3 / 50) / (u + 3125 / 100000) ^ 2 + (48 / 125) / (u + 2 / 10) ^ 2
private noncomputable def fPoleSum (x : ℝ) : ℝ :=
  (2967 / 1953125) / (x + 8 / 10000) + (14991 / 1562500) / (x + 5 / 1000) +
    (29997 / 500000) / (x + 3125 / 100000) + (29997 / 78125) / (x + 2 / 10)
private noncomputable def fPoleTan0 (a : ℝ) : ℝ :=
  (2967 / 1953125) * (2 / (a + 8 / 10000) - (8 / 10000) / (a + 8 / 10000) ^ 2 -
      1 / (69 / 100 + 8 / 10000)) +
    (14991 / 1562500) * (2 / (a + 5 / 1000) - (5 / 1000) / (a + 5 / 1000) ^ 2 -
      1 / (69 / 100 + 5 / 1000)) +
    (29997 / 500000) * (2 / (a + 3125 / 100000) - (3125 / 100000) / (a + 3125 / 100000) ^ 2 -
      1 / (69 / 100 + 3125 / 100000)) +
    (29997 / 78125) * (2 / (a + 2 / 10) - (2 / 10) / (a + 2 / 10) ^ 2 - 1 / (69 / 100 + 2 / 10))
private noncomputable def fPoleTan1 (a : ℝ) : ℝ :=
  (2967 / 1953125) / (a + 8 / 10000) ^ 2 + (14991 / 1562500) / (a + 5 / 1000) ^ 2 +
    (29997 / 500000) / (a + 3125 / 100000) ^ 2 + (29997 / 78125) / (a + 2 / 10) ^ 2

private theorem fPoleSum_sub_ge_tan {a uEnd a0 : ℝ} (ha : 0 < a) (ha0 : 0 < a0)
    (hu : 69 / 100 ≤ uEnd) : fPoleTan0 a0 - fPoleTan1 a0 * a ≤ fPoleSum a - fPoleSum uEnd := by
  have ht {s : ℝ} (hs : 0 < s) : 2 / (a0 + s) - s / (a0 + s) ^ 2 - 1 / (69 / 100 + s) -
      a / (a0 + s) ^ 2 ≤ 1 / (a + s) - 1 / (uEnd + s) := by
    have h1 : 0 ≤ 1 / (a + s) - (2 / (a0 + s) - s / (a0 + s) ^ 2 - a / (a0 + s) ^ 2) := by
      have : 1 / (a + s) - (2 / (a0 + s) - s / (a0 + s) ^ 2 - a / (a0 + s) ^ 2) =
          (a - a0) ^ 2 / ((a + s) * (a0 + s) ^ 2) := by field_simp; ring
      rw [this]; positivity
    have h2 : 1 / (uEnd + s) ≤ 1 / (69 / 100 + s) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have h1 := ht (show (0 : ℝ) < 8 / 10000 by norm_num)
  have h2 := ht (show (0 : ℝ) < 5 / 1000 by norm_num)
  have h3 := ht (show (0 : ℝ) < 3125 / 100000 by norm_num)
  have h4 := ht (show (0 : ℝ) < 2 / 10 by norm_num)
  have hrew : fPoleTan1 a0 * a = (2967 / 1953125) * (a / (a0 + 8 / 10000) ^ 2) +
      (14991 / 1562500) * (a / (a0 + 5 / 1000) ^ 2) +
      (29997 / 500000) * (a / (a0 + 3125 / 100000) ^ 2) +
      (29997 / 78125) * (a / (a0 + 2 / 10) ^ 2) := by unfold fPoleTan1; ring
  have hfP (x : ℝ) : fPoleSum x = (2967 / 1953125) * (1 / (x + 8 / 10000)) +
      (14991 / 1562500) * (1 / (x + 5 / 1000)) +
      (29997 / 500000) * (1 / (x + 3125 / 100000)) +
      (29997 / 78125) * (1 / (x + 2 / 10)) := by unfold fPoleSum; ring
  rw [hrew, hfP a, hfP uEnd]; unfold fPoleTan0
  linarith only [h1, h2, h3, h4]

private theorem fPoleSum_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    fPoleSum y ≤ fPoleSum x := by
  have hs {s : ℝ} (hs0 : 0 < s) : 1 / (y + s) ≤ 1 / (x + s) :=
    one_div_le_one_div_of_le (by linarith only [hx, hs0]) (by linarith only [hxy])
  have h1 := hs (by norm_num : (0 : ℝ) < 8 / 10000)
  have h2 := hs (by norm_num : (0 : ℝ) < 5 / 1000)
  have h3 := hs (by norm_num : (0 : ℝ) < 3125 / 100000)
  have h4 := hs (by norm_num : (0 : ℝ) < 2 / 10)
  have hfP (z : ℝ) : fPoleSum z = (2967 / 1953125) * (1 / (z + 8 / 10000)) +
      (14991 / 1562500) * (1 / (z + 5 / 1000)) +
      (29997 / 500000) * (1 / (z + 3125 / 100000)) +
      (29997 / 78125) * (1 / (z + 2 / 10)) := by unfold fPoleSum; ring
  rw [hfP y, hfP x]; linarith only [h1, h2, h3, h4]

private theorem fPoleSum_conv_ge {a x1 x2 mu : ℝ}
    (hjen : ∀ {s : ℝ}, 0 ≤ s → 1 / (a + s) ≤ mu / (x1 + s) + (1 - mu) / (x2 + s)) :
    fPoleSum a ≤ mu * fPoleSum x1 + (1 - mu) * fPoleSum x2 := by
  have hj1 := hjen (s := 8 / 10000) (by norm_num)
  have hj2 := hjen (s := 5 / 1000) (by norm_num)
  have hj3 := hjen (s := 3125 / 100000) (by norm_num)
  have hj4 := hjen (s := 2 / 10) (by norm_num)
  have hfP (z : ℝ) : fPoleSum z = (2967 / 1953125) * (1 / (z + 8 / 10000)) +
      (14991 / 1562500) * (1 / (z + 5 / 1000)) +
      (29997 / 500000) * (1 / (z + 3125 / 100000)) +
      (29997 / 78125) * (1 / (z + 2 / 10)) := by unfold fPoleSum; ring
  have hrw (s : ℝ) : mu * (1 / (x1 + s)) + (1 - mu) * (1 / (x2 + s)) =
      mu / (x1 + s) + (1 - mu) / (x2 + s) := by ring
  rw [hfP a, hfP x1, hfP x2]
  linarith only [hj1, hj2, hj3, hj4, hrw (8 / 10000), hrw (5 / 1000),
    hrw (3125 / 100000), hrw (2 / 10),
    show mu * ((2967 / 1953125) * (1 / (x1 + 8 / 10000)) +
          (14991 / 1562500) * (1 / (x1 + 5 / 1000)) +
          (29997 / 500000) * (1 / (x1 + 3125 / 100000)) +
          (29997 / 78125) * (1 / (x1 + 2 / 10))) +
        (1 - mu) * ((2967 / 1953125) * (1 / (x2 + 8 / 10000)) +
          (14991 / 1562500) * (1 / (x2 + 5 / 1000)) +
          (29997 / 500000) * (1 / (x2 + 3125 / 100000)) +
          (29997 / 78125) * (1 / (x2 + 2 / 10))) =
      (2967 / 1953125) * (mu * (1 / (x1 + 8 / 10000)) + (1 - mu) * (1 / (x2 + 8 / 10000))) +
      (14991 / 1562500) * (mu * (1 / (x1 + 5 / 1000)) + (1 - mu) * (1 / (x2 + 5 / 1000))) +
      (29997 / 500000) * (mu * (1 / (x1 + 3125 / 100000)) +
        (1 - mu) * (1 / (x2 + 3125 / 100000))) +
      (29997 / 78125) * (mu * (1 / (x1 + 2 / 10)) + (1 - mu) * (1 / (x2 + 2 / 10))) by ring]

private theorem pu_odd_pole_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 7 / 10) :
  gPoleSum u ≤ (1 - u ^ 2 / 2) ^ 3 / u := by
  let num : ℝ := (1 - u ^ 2 / 2) ^ 3 * ((u + 8 / 10000) ^ 2 * (u + 5 / 1000) ^ 2 *
      (u + 3125 / 100000) ^ 2 * (u + 2 / 10) ^ 2) -
    u * ((24 / 15625) * ((u + 5 / 1000) ^ 2 * (u + 3125 / 100000) ^ 2 * (u + 2 / 10) ^ 2) +
      (6 / 625) * ((u + 8 / 10000) ^ 2 * (u + 3125 / 100000) ^ 2 * (u + 2 / 10) ^ 2) +
      (3 / 50) * ((u + 8 / 10000) ^ 2 * (u + 5 / 1000) ^ 2 * (u + 2 / 10) ^ 2) +
      (48 / 125) * ((u + 8 / 10000) ^ 2 * (u + 5 / 1000) ^ 2 * (u + 3125 / 100000) ^ 2))
  have hden : 0 < u * ((u + 8 / 10000) ^ 2 * (u + 5 / 1000) ^ 2 *
      (u + 3125 / 100000) ^ 2 * (u + 2 / 10) ^ 2) := by positivity
  rw [← sub_nonneg]; unfold gPoleSum
  suffices hnum : 0 ≤ num by
    refine (div_nonneg hnum hden.le).trans_eq ?_; dsimp [num]; field_simp
  rcases le_total u (1 / 100) with hmid | hmid
  · let x := u - 0; let y := 1 / 100 - u
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : num = 6250000000000 * y ^ 14 + 94935000000000 * x * y ^ 13 +
        968859187500000 * x ^ 2 * y ^ 12 + 5816704103750000 * x ^ 3 * y ^ 11 +
        21625511191078125 * x ^ 4 * y ^ 10 + (107389039875838125 / 2) * x ^ 5 * y ^ 9 +
        (3002097169595778325 / 32) * x ^ 6 * y ^ 8 + (7612795198737376533 / 64) * x ^ 7 * y ^ 7 +
        (1421168458094174992011 / 12800) * x ^ 8 * y ^ 6 +
        (4887294297344272694583 / 64000) * x ^ 9 * y ^ 5 +
        (48959218305787026181959 / 1280000) * x ^ 10 * y ^ 4 +
        (1087545102126273293247 / 80000) * x ^ 11 * y ^ 3 +
        (2094635097288658765539 / 640000) * x ^ 12 * y ^ 2 +
        (156274694977022314209 / 320000) * x ^ 13 * y +
        (45478730704870426311 / 1280000) * x ^ 14 := by dsimp [num, x, y]; ring
    rw [hEq]; positivity
  · let x := u - 1 / 100; let y := 7 / 10 - u
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : num = (20795030043379253 / 32452522293460794665322240000) * y ^ 14 +
        (27384169278975367 / 1352188428894199777721760000) * x * y ^ 13 +
        (222708968279699913307 / 16226261146730397332661120000) * x ^ 2 * y ^ 12 +
        (824237510271372573307 / 253535330417662458322830000) * x ^ 3 * y ^ 11 +
        (9309613504592174705846117 / 32452522293460794665322240000) * x ^ 4 * y ^ 10 +
        (11997362095743499915729027 / 811313057336519866633056000) * x ^ 5 * y ^ 9 +
        (35560307232566712500598653 / 81131305733651986663305600) * x ^ 6 * y ^ 8 +
        (6670476357524508489380363 / 1622626114673039733266112) * x ^ 7 * y ^ 7 +
        (41070857021342639971973671 / 1622626114673039733266112) * x ^ 8 * y ^ 6 +
        (11203015668282958684204925 / 135218842889419977772176) * x ^ 9 * y ^ 5 +
        (29085947860219262776249475 / 202828264334129966658264) * x ^ 10 * y ^ 4 +
        (4466597721960126216218375 / 33804710722354994443044) * x ^ 11 * y ^ 3 +
        (12358570064337805759553125 / 202828264334129966658264) * x ^ 12 * y ^ 2 +
        (94510545073278640318750 / 8451177680588748610761) * x ^ 13 * y +
        (228957213000286625000 / 2817059226862916203587) * x ^ 14 := by dsimp [num, x, y]; ring
    rw [hEq]; positivity

private noncomputable def qDeg5Poly (kapQ Ctot pref qMin F0 F1 t : ℝ) : ℝ :=
  let a := t + 2 * (4794 / 10 ^ 8)
  ((kapQ - Ctot + pref * (-100 / 69 + qMin * (F0 - F1 * (2 * (4794 / 10 ^ 8))))) +
      (2 * kapQ * qMin - pref * qMin * F1) * t - kapQ * t ^ 2) * (3 * a ^ 3) +
    3 * pref * a ^ 2 - (5001 / 5000) * pref * (276 / 10 ^ 10 + t ^ 2)

private theorem exists_qDeg5_cert_low {t : ℝ}
    (ht0 : 6 * (4794 / 10 ^ 8) ≤ t) (ht1 : t ≤ 83 / 20000) :
    ∃ a0 F0 F1 : ℝ, 0 < a0 ∧ F0 ≤ fPoleTan0 a0 ∧ fPoleTan1 a0 ≤ F1 ∧
      0 ≤ qDeg5Poly ((1 / 4) * (3979 / 4000) ^ 2) (1250013 / 5000000)
        (5319 / 3125000000) (3091 / 1000) F0 F1 t := by
  rcases le_total t (3 / 5000) with h1 | h1
  · refine ⟨11 / 20000, (67921 / 10000), (12138773 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (7191 / 25000000); let y := (3 / 5000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (3979 / 4000) ^ 2) (1250013 / 5000000)
          (5319 / 3125000000) (3091 / 1000) (67921 / 10000) (12138773 / 10000) t =
        (345528380244413482689722171873231 / 5153472330607171104375000000) * y ^ 5 +
        (7665982383242475372921888425043973 / 20613889322428684417500000000) * x * y ^ 4 +
        (61955891672327535088915775265572957 / 82455557289714737670000000000) * x ^ 2 * y ^ 3 +
        (74879205882512914050187219941520781 / 109940743052952983560000000000) * x ^ 3 * y ^ 2 +
        (944595555127688747554928749526603 / 3435648220404780736250000000) * x ^ 4 * y +
        (138801830850547046710151506514359 / 3435648220404780736250000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (3 / 4000) with h2 | h2
  · refine ⟨3 / 4000, (16621 / 2500), (9906017 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 5000); let y := (3 / 4000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (3979 / 4000) ^ 2) (1250013 / 5000000)
          (5319 / 3125000000) (3091 / 1000) (16621 / 2500) (9906017 / 10000) t =
        (138873563737489553846936115504211 / 87738037109375000000000000) * y ^ 5 +
        (114856926698386729717676850618211 / 17547607421875000000000000) * x * y ^ 4 +
        (1435081621498373230121418155856001 / 140380859375000000000000000) * x ^ 2 * y ^ 3 +
        (3126860293097707966741270594602503 / 421142578125000000000000000) * x ^ 3 * y ^ 2 +
        (1044115870446656228133750587810689 / 421142578125000000000000000) * x ^ 4 * y +
        (662634972367973496249903329921689 / 2105712890625000000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (9 / 10000) with h3 | h3
  · refine ⟨19 / 20000, (13033 / 2000), (4172047 / 5000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 4000); let y := (9 / 10000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (3979 / 4000) ^ 2) (1250013 / 5000000)
          (5319 / 3125000000) (3091 / 1000) (13033 / 2000) (4172047 / 5000) t =
        (662693233505294426087934643852273 / 2105712890625000000000000000) * y ^ 5 +
        (282459758497036010639328578179273 / 421142578125000000000000000) * x * y ^ 4 +
        (80780741570844192595541773215671 / 421142578125000000000000000) * x ^ 2 * y ^ 3 +
        (391219003067975846140047282377 / 18310546875000000000000000) * x ^ 3 * y ^ 2 +
        (31954431627174688572826689549331 / 52642822265625000000000000) * x ^ 4 * y +
        (221870916465699416934237272914787 / 526428222656250000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (3 / 2500) with h4 | h4
  · refine ⟨23 / 20000, (63967 / 10000), (7198061 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (9 / 10000); let y := (3 / 2500) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (3979 / 4000) ^ 2) (1250013 / 5000000)
          (5319 / 3125000000) (3091 / 1000) (63967 / 10000) (7198061 / 10000) t =
        (221258283602370003042238628301653 / 16845703125000000000000000000) * y ^ 5 +
        (537814768870758950795242186601903 / 3369140625000000000000000000) * x * y ^ 4 +
        (2470804273458920121888025190038681 / 3369140625000000000000000000) * x ^ 2 * y ^ 3 +
        (5002975694398907944131451855545431 / 3369140625000000000000000000) * x ^ 3 * y ^ 2 +
        (2287448317866378166415898270165389 / 1684570312500000000000000000) * x ^ 4 * y +
        (3872899005623376946047883847206139 / 8422851562500000000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  · refine ⟨1 / 400, (58129 / 10000), (232558 / 625), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 2500); let y := (83 / 20000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (3979 / 4000) ^ 2) (1250013 / 5000000)
          (5319 / 3125000000) (3091 / 1000) (58129 / 10000) (232558 / 625) t =
        (2440783287243096176142515198237769 / 490047302156686782836914062500000) * y ^ 5 +
        (1575455559134454685432076730451122807 / 12545210935211181640625000000000000) *
          x * y ^ 4 +
        (114258678581921801930059654812575525787 / 100361687481689453125000000000000000) *
          x ^ 2 * y ^ 3 +
        (19615603134414189395661151929789960969 / 4363551629638671875000000000000000) *
          x ^ 3 * y ^ 2 +
        (763184423082438365239949927566903644081 / 100361687481689453125000000000000000) *
          x ^ 4 * y +
        (2070529872624994762436354534099704026081 / 501808437408447265625000000000000000) *
          x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity

private theorem exists_qDeg5_cert_mid {t : ℝ}
    (ht0 : 6 * (4794 / 10 ^ 8) ≤ t) (ht1 : t ≤ 83 / 20000) :
    ∃ a0 F0 F1 : ℝ, 0 < a0 ∧ F0 ≤ fPoleTan0 a0 ∧ fPoleTan1 a0 ≤ F1 ∧
      0 ≤ qDeg5Poly ((1 / 4) * (49739 / 50000) ^ 2) (1250013 / 5000000)
        (169281 / 100000000000) (77 / 25) F0 F1 t := by
  rcases le_total t (3 / 5000) with h1 | h1
  · refine ⟨11 / 20000, (67921 / 10000), (12138773 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (7191 / 25000000); let y := (3 / 5000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (49739 / 50000) ^ 2) (1250013 / 5000000)
          (169281 / 100000000000) (77 / 25) (67921 / 10000) (12138773 / 10000) t =
        (28671116738327740871550401814221 / 429456027550597592031250000) * y ^ 5 +
        (636453715933469063157069511723063 / 1717824110202390368125000000) * x * y ^ 4 +
        (5149039750473529491996318859099183 / 6871296440809561472500000000) * x ^ 2 * y ^ 3 +
        (56123835011531497355640778887959143 / 82455557289714737670000000000) * x ^ 3 * y ^ 2 +
        (2275860042528728682240516134562227 / 8245555728971473767000000000) * x ^ 4 * y +
        (337825727066451437349189551513131 / 8245555728971473767000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (3 / 4000) with h2 | h2
  · refine ⟨3 / 4000, (16621 / 2500), (9906017 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 5000); let y := (3 / 4000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (49739 / 50000) ^ 2) (1250013 / 5000000)
          (169281 / 100000000000) (77 / 25) (16621 / 2500) (9906017 / 10000) t =
        (337996339041332867288501146675999 / 210571289062500000000000000) * y ^ 5 +
        (281764845532906827591890853226999 / 42114257812500000000000000) * x * y ^ 4 +
        (111483078242931086154911195412437 / 10528564453125000000000000) * x ^ 2 * y ^ 3 +
        (82915458489690546528359784031687 / 10528564453125000000000000) * x ^ 3 * y ^ 2 +
        (115868349300460773797152677911249 / 42114257812500000000000000) * x ^ 4 * y +
        (79866096659916489295545528962249 / 210571289062500000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (9 / 10000) with h3 | h3
  · refine ⟨19 / 20000, (13033 / 2000), (4172047 / 5000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 4000); let y := (9 / 10000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (49739 / 50000) ^ 2) (1250013 / 5000000)
          (169281 / 100000000000) (77 / 25) (13033 / 2000) (4172047 / 5000) t =
        (19967967605609012097173243900267 / 52642822265625000000000000) * y ^ 5 +
        (10998309800660119342546072845767 / 10528564453125000000000000) * x * y ^ 4 +
        (22107696785927035513178366180693 / 21057128906250000000000000) * x ^ 2 * y ^ 3 +
        (304473793034761519581269599097 / 305175781250000000000000) * x ^ 3 * y ^ 2 +
        (8128129900110371104162126928803 / 7019042968750000000000000) * x ^ 4 * y +
        (19123244298972133288841666038303 / 35095214843750000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (3 / 2500) with h4 | h4
  · refine ⟨23 / 20000, (63967 / 10000), (7198061 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (9 / 10000); let y := (3 / 2500) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (49739 / 50000) ^ 2) (1250013 / 5000000)
          (169281 / 100000000000) (77 / 25) (63967 / 10000) (7198061 / 10000) t =
        (38165538200539400966727558596489 / 2246093750000000000000000000) * y ^ 5 +
        (82229555333734293951415877468489 / 449218750000000000000000000) * x * y ^ 4 +
        (177283202333395813326174108152989 / 224609375000000000000000000) * x ^ 2 * y ^ 3 +
        (1044830918471132909835784720699967 / 673828125000000000000000000) * x ^ 3 * y ^ 2 +
        (1880955342933267211888031539878467 / 1347656250000000000000000000) * x ^ 4 * y +
        (3156011883464584304887103250744467 / 6738281250000000000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  · refine ⟨1 / 400, (58129 / 10000), (232558 / 625), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 2500); let y := (83 / 20000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (49739 / 50000) ^ 2) (1250013 / 5000000)
          (169281 / 100000000000) (77 / 25) (58129 / 10000) (232558 / 625) t =
        (7956829676542486947723327726768303 / 1568151366901397705078125000000000) * y ^ 5 +
        (19849664619834803237871030775359339 / 156815136690139770507812500000000) * x * y ^ 4 +
        (5727737099420305217923809354741019071 / 5018084374084472656250000000000000) *
          x ^ 2 * y ^ 3 +
        (980670483704245290886149240238336677 / 218177581481933593750000000000000) *
          x ^ 3 * y ^ 2 +
        (38100238720832014853037412835678444973 / 5018084374084472656250000000000000) *
          x ^ 4 * y +
        (103295514539769543340134168607150025973 / 25090421870422363281250000000000000) *
          x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity

private theorem exists_qDeg5_cert_univ {t : ℝ}
    (ht0 : 6 * (4794 / 10 ^ 8) ≤ t) (ht1 : t ≤ 83 / 20000) :
    ∃ a0 F0 F1 : ℝ, 0 < a0 ∧ F0 ≤ fPoleTan0 a0 ∧ fPoleTan1 a0 ≤ F1 ∧
      0 ≤ qDeg5Poly ((1 / 4) * (99487 / 100000) ^ 2) (2500027 / 10000000)
        (16757 / 10000000000) (376 / 125) F0 F1 t := by
  rcases le_total t (3 / 5000) with h1 | h1
  · refine ⟨11 / 20000, (67921 / 10000), (12138773 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (7191 / 25000000); let y := (3 / 5000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (99487 / 100000) ^ 2) (2500027 / 10000000)
          (16757 / 10000000000) (376 / 125) (67921 / 10000) (12138773 / 10000) t =
        (3096401510529801367846053670212703 / 46381250975464539939375000000) * y ^ 5 +
        (68906399153242107232212831387003509 / 185525003901858159757500000000) * x * y ^ 4 +
        (559662605766508291006689636211079629 / 742100015607432639030000000000) * x ^ 2 * y ^ 3 +
        (2046301054837724581934588537747999863 / 2968400062429730556120000000000) *
          x ^ 3 * y ^ 2 +
        (10475808088897731510285240408702223 / 37105000780371631951500000000) * x ^ 4 * y +
        (393997256391759428557416186822461 / 9276250195092907987875000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (3 / 4000) with h2 | h2
  · refine ⟨3 / 4000, (16621 / 2500), (9906017 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 5000); let y := (3 / 4000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (99487 / 100000) ^ 2) (2500027 / 10000000)
          (16757 / 10000000000) (376 / 125) (16621 / 2500) (9906017 / 10000) t =
        (394182813331639883286083779370069 / 236892700195312500000000000) * y ^ 5 +
        (663969309468642486883345113624013 / 94757080078125000000000000) * x * y ^ 4 +
        (8530195832984789028875113891860583 / 758056640625000000000000000) * x ^ 2 * y ^ 3 +
        (6481058451667368653128241126315083 / 758056640625000000000000000) * x ^ 3 * y ^ 2 +
        (2334103250738085205451239250908229 / 758056640625000000000000000) * x ^ 4 * y +
        (1664352981217082089509730772854229 / 3790283203125000000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (9 / 10000) with h3 | h3
  · refine ⟨19 / 20000, (13033 / 2000), (4172047 / 5000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 4000); let y := (9 / 10000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (99487 / 100000) ^ 2) (2500027 / 10000000)
          (16757 / 10000000000) (376 / 125) (13033 / 2000) (4172047 / 5000) t =
        (1664453453574239473128033928392053 / 3790283203125000000000000000) * y ^ 5 +
        (996854387102494506277742893314053 / 758056640625000000000000000) * x * y ^ 4 +
        (1133002680339805924353154804862731 / 758056640625000000000000000) * x ^ 2 * y ^ 3 +
        (42785071702372287550667845166597 / 32958984375000000000000000) * x ^ 3 * y ^ 2 +
        (28579982229757918691042168168029 / 23689270019531250000000000) * x ^ 4 * y +
        (499426504282066503005168241121607 / 947570800781250000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  rcases le_total t (3 / 2500) with h4 | h4
  · refine ⟨23 / 20000, (63967 / 10000), (7198061 / 10000), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (9 / 10000); let y := (3 / 2500) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (99487 / 100000) ^ 2) (2500027 / 10000000)
          (16757 / 10000000000) (376 / 125) (63967 / 10000) (7198061 / 10000) t =
        (498370008122169686772360038001983 / 30322265625000000000000000000) * y ^ 5 +
        (1041033849464333975682384547204733 / 6064453125000000000000000000) * x * y ^ 4 +
        (4489726941331510226190941775111841 / 6064453125000000000000000000) * x ^ 2 * y ^ 3 +
        (8874506268831306375996890422798591 / 6064453125000000000000000000) * x ^ 3 * y ^ 2 +
        (251111912426877167651712307104019 / 189514160156250000000000000) * x ^ 4 * y +
        (1693398450329248761726217665648451 / 3790283203125000000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
  · refine ⟨1 / 400, (58129 / 10000), (232558 / 625), by norm_num,
      by unfold fPoleTan0; norm_num, by unfold fPoleTan1; norm_num, ?_⟩
    let x := t - (3 / 2500); let y := (83 / 20000) - t
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hEq : qDeg5Poly ((1 / 4) * (99487 / 100000) ^ 2) (2500027 / 10000000)
          (16757 / 10000000000) (376 / 125) (58129 / 10000) (232558 / 625) t =
        (128636029621088524246151403098649 / 26578836727142333984375000000000) * y ^ 5 +
        (2581759977161827751517601008809721 / 21263069381713867187500000000000) * x * y ^ 4 +
        (374781330998827725292653873414898197 / 340209110107421875000000000000000) *
          x ^ 2 * y ^ 3 +
        (64450619802476036272746367481635639 / 14791700439453125000000000000000) * x ^ 3 * y ^ 2 +
        (2511219169715301164776224307699490911 / 340209110107421875000000000000000) * x ^ 4 * y +
        (6818610405816628038736754596074257911 / 1701045550537109375000000000000000) * x ^ 5 := by
      unfold qDeg5Poly; dsimp [x, y]; ring
    rw [hEq]; positivity
private noncomputable def shiftPhaseVec (L : ℕ) (θ : ℝ) (k : ℕ) : Fin (2 ^ 16) → ℂ := fun m ↦
  if k ≤ m.val ∧ m.val < L + k then
    (sineWindowCoeff L (m.val - k) : ℂ) * Complex.exp (Complex.I * (m.val : ℂ) * (θ : ℂ)) else 0

private theorem shiftPhaseVec_zero (M : ℕ) (θ : ℝ) :
    shiftPhaseVec (M + 1) θ 0 = windowPhaseVec 16 M (sineWindowCoeff (M + 1)) θ := by
  funext m; simp [shiftPhaseVec, windowPhaseVec]

private theorem iqft16_mulVec_shiftPhaseVec {L k : ℕ} (hLk : L + k ≤ 2 ^ 16) (θ : ℝ)
    (y : Fin (2 ^ 16)) : ((QFT.qftMatrix 16)ᴴ *ᵥ shiftPhaseVec L θ k) y =
      Complex.exp (-2 * Complex.I * (k : ℂ) * (((qpeAngle 16 y - θ) / 2 : ℝ) : ℂ)) *
        ((QFT.qftMatrix 16)ᴴ *ᵥ shiftPhaseVec L θ 0) y := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  let S1 : Finset (Fin (2 ^ 16)) := Finset.univ.filter fun m ↦ k ≤ m.val ∧ m.val < L + k
  let S0 : Finset (Fin (2 ^ 16)) := Finset.univ.filter fun m ↦ m.val < L
  rw [← Finset.sum_subset (Finset.subset_univ S1) (fun m _ hm ↦ by
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hm; simp [shiftPhaseVec, hm]),
    ← Finset.sum_subset (Finset.subset_univ S0) (fun m _ hm ↦ by
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hm; simp [shiftPhaseVec, hm])]
  refine Finset.sum_bij (fun m hm ↦ ⟨m.val - k, by
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hm; omega⟩)
    (fun m hm ↦ by simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢; omega)
    (fun m₁ hm₁ m₂ hm₂ h ↦ by
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
      exact Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    (fun j hj ↦ by
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact ⟨⟨j.val + k, by omega⟩,
        by simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]; omega,
        Fin.ext (Nat.add_sub_cancel j.val k)⟩) fun m hm ↦ ?_
  simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  rw [iqft16_apply, iqft16_apply]
  have hc1 : k ≤ m.val ∧ m.val < L + k := ⟨hm.1, hm.2⟩
  have hc0 : 0 ≤ m.val - k ∧ m.val - k < L + 0 := ⟨Nat.zero_le _, by omega⟩
  dsimp only [shiftPhaseVec]; rw [ite_eq_left hc1, ite_eq_left hc0]; simp only [Nat.sub_zero]
  have hm_eq : (m.val : ℂ) = ((m.val - k : ℕ) : ℂ) + (k : ℂ) := by
    exact_mod_cast (by omega : m.val = m.val - k + k)
  have hexp : Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ)) *
        Complex.exp (Complex.I * (m.val : ℂ) * (θ : ℂ)) =
      Complex.exp (-2 * Complex.I * (k : ℂ) * (((qpeAngle 16 y - θ) / 2 : ℝ) : ℂ)) *
        (Complex.exp (-Complex.I * ((m.val - k : ℕ) : ℂ) * (qpeAngle 16 y : ℂ)) *
          Complex.exp (Complex.I * ((m.val - k : ℕ) : ℂ) * (θ : ℂ))) := by
    set αy : ℝ := (qpeAngle 16 y - θ) / 2
    have harg : -Complex.I * (((m.val - k : ℕ) : ℂ) + (k : ℂ)) * (qpeAngle 16 y : ℂ) +
        Complex.I * (((m.val - k : ℕ) : ℂ) + (k : ℂ)) * (θ : ℂ) =
        -2 * Complex.I * (k : ℂ) * (αy : ℂ) +
          (-Complex.I * ((m.val - k : ℕ) : ℂ) * (qpeAngle 16 y : ℂ) +
            Complex.I * ((m.val - k : ℕ) : ℂ) * (θ : ℂ)) := by
      have hαy : (αy : ℂ) = ((qpeAngle 16 y : ℂ) - (θ : ℂ)) / 2 := by
        dsimp only [αy]; rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]
      rw [hαy]; ring
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hm_eq, harg]
  linear_combination (sineWindowCoeff L (m.val - k) : ℂ) * (1 / 256 : ℂ) * hexp

private theorem sineWindow_shift_dot {M k : ℕ} (hk : M + 1 + k ≤ 2 ^ 16) (θ : ℝ) :
    let q := (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) θ
    (∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
        Real.sin (2 * (k : ℝ) * ((qpeAngle 16 y - θ) / 2)) = 0) ∧
      (∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
        Real.cos (2 * (k : ℝ) * ((qpeAngle 16 y - θ) / 2)) =
        ∑ j ∈ Finset.range (M + 1 - k),
          sineWindowCoeff (M + 1) (j + k) * sineWindowCoeff (M + 1) j) := by
  intro q; let L := M + 1; let w0 := shiftPhaseVec L θ 0; let wk := shiftPhaseVec L θ k
  have hiso : star ((QFT.qftMatrix 16)ᴴ *ᵥ w0) ⬝ᵥ ((QFT.qftMatrix 16)ᴴ *ᵥ wk) = star w0 ⬝ᵥ wk := by
    have hU : (QFT.qftMatrix 16)ᴴᴴ * (QFT.qftMatrix 16)ᴴ = 1 := by
      have h := (iqftMatrixUnitary 16).2.1
      rwa [iqftMatrixUnitary_coe, Matrix.star_eq_conjTranspose] at h
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]
  have hlhs : star ((QFT.qftMatrix 16)ᴴ *ᵥ w0) ⬝ᵥ ((QFT.qftMatrix 16)ᴴ *ᵥ wk) =
      ∑ y : Fin (2 ^ 16), (Complex.normSq (q y) : ℂ) *
        Complex.exp (((-(2 * (k : ℝ) * ((qpeAngle 16 y - θ) / 2)) : ℝ) : ℂ) * Complex.I) := by
    simp only [dotProduct, Pi.star_apply]; refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [iqft16_mulVec_shiftPhaseVec hk θ y]
    have hq0 : ((QFT.qftMatrix 16)ᴴ *ᵥ w0) y = q y := by
      dsimp only [w0, L, q]; rw [shiftPhaseVec_zero]
    rw [hq0, mul_left_comm, Complex.star_def, mul_comm _ (q y), Complex.mul_conj, mul_comm]
    set αy : ℝ := (qpeAngle 16 y - θ) / 2
    exact congrArg (fun z ↦ (Complex.normSq (q y) : ℂ) * Complex.exp z) (by
      rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_natCast]
      ring)
  have hrhs : star w0 ⬝ᵥ wk = ((∑ j ∈ Finset.range (L - k),
      sineWindowCoeff L (j + k) * sineWindowCoeff L j : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply]
    let S : Finset (Fin (2 ^ 16)) := Finset.univ.filter fun m ↦ k ≤ m.val ∧ m.val < L
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun m _ hm ↦ by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      dsimp [w0, wk, shiftPhaseVec]; split_ifs with h1 h2 <;> [omega; simp; simp; simp])]
    rw [Complex.ofReal_sum]
    refine Finset.sum_bij (fun m hm ↦ m.val - k)
      (fun m hm ↦ by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm
                     exact Finset.mem_range.mpr (by omega))
      (fun m₁ hm₁ m₂ hm₂ h ↦ by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
        exact Fin.ext (by dsimp at h; omega))
      (fun j hj ↦ ⟨⟨j + k, by have := Finset.mem_range.mp hj; omega⟩,
        by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
           have := Finset.mem_range.mp hj; omega, Nat.add_sub_cancel j k⟩) fun m hm ↦ ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    have hc0 : 0 ≤ m.val ∧ m.val < L + 0 := ⟨Nat.zero_le _, by omega⟩
    have hck : k ≤ m.val ∧ m.val < L + k := ⟨hm.1, by omega⟩
    dsimp only [w0, wk, shiftPhaseVec]
    rw [ite_eq_left hc0, ite_eq_left hck]; simp only [Nat.sub_zero, Nat.sub_add_cancel hm.1]
    rw [Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
      mul_mul_mul_comm, ← Complex.exp_add, show (starRingEnd ℂ)
        (Complex.I * (m.val : ℂ) * (θ : ℂ)) + Complex.I * (m.val : ℂ) * (θ : ℂ) = 0 by
        simp [Complex.conj_ofReal, Complex.conj_I], Complex.exp_zero, mul_one,
      Complex.ofReal_mul]
  rw [hlhs, hrhs] at hiso
  have him := congrArg Complex.im hiso; have hre := congrArg Complex.re hiso
  simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    add_zero, Complex.exp_ofReal_mul_I_im, Real.sin_neg, mul_neg, Finset.sum_neg_distrib] at him
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
    sub_zero, Complex.exp_ofReal_mul_I_re, Real.cos_neg] at hre
  dsimp only [L] at hre
  exact ⟨neg_eq_zero.mp him, hre⟩

private theorem sineWindow_moments {M : ℕ} (hMlo : 46368 ≤ M) (hMhi : M ≤ 47488) (θ : ℝ) :
    let q := (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) θ
    (∑ y : Fin (2 ^ 16), Complex.normSq (q y) = 1) ∧
    (∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
      (Real.sin ((qpeAngle 16 y - θ) / 2) ^ 3 * Real.cos ((qpeAngle 16 y - θ) / 2)) = 0) ∧
    (∑ y : Fin (2 ^ 16), Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 2 ≤
      ((M : ℝ) / ((M : ℝ) + 1)) * (π / ((M : ℝ) + 1)) ^ 2 / 4) ∧
    (∑ y : Fin (2 ^ 16), Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 4 ≤
      (1 / (8 * ((M : ℝ) + 1)) + (π / ((M : ℝ) + 1)) ^ 2 / 16) * (π / ((M : ℝ) + 1)) ^ 2) := by
  intro q; let L := M + 1; let α := π / (2 * (L : ℝ))
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hα0 : 0 < α := by dsimp [α]; positivity
  have h2α_lt : 2 * α < π := by
    dsimp [α, L]; rw [show 2 * (π / (2 * ((M + 1 : ℕ) : ℝ))) = π / ((M + 1 : ℕ) : ℝ) by ring]
    exact div_lt_self pi_pos (by exact_mod_cast (by omega : 1 < M + 1))
  have hsin2α : 0 < Real.sin (2 * α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2α_lt
  have hsinα : Real.sin α ≤ (π / (L : ℝ)) / 2 := by
    exact (Real.sin_le hα0.le).trans_eq (by dsimp [α]; rw [div_mul_eq_div_div]; ring)
  have hsinα0 : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0.le (by linarith [pi_pos])
  have hd0 := sineWindow_shift_dot (M := M) (k := 0) (by omega) θ
  have hd1 := sineWindow_shift_dot (M := M) (k := 1) (by omega) θ
  have hd2 := sineWindow_shift_dot (M := M) (k := 2) (by omega) θ
  dsimp only at hd0 hd1 hd2
  change (∑ y, Complex.normSq (q y) * Real.sin (2 * (0 : ℕ) * ((qpeAngle 16 y - θ) / 2)) = 0) ∧
    (∑ y, Complex.normSq (q y) * Real.cos (2 * (0 : ℕ) * ((qpeAngle 16 y - θ) / 2)) = _) at hd0
  change (∑ y, Complex.normSq (q y) * Real.sin (2 * (1 : ℕ) * ((qpeAngle 16 y - θ) / 2)) = 0) ∧
    (∑ y, Complex.normSq (q y) * Real.cos (2 * (1 : ℕ) * ((qpeAngle 16 y - θ) / 2)) = _) at hd1
  change (∑ y, Complex.normSq (q y) * Real.sin (2 * (2 : ℕ) * ((qpeAngle 16 y - θ) / 2)) = 0) ∧
    (∑ y, Complex.normSq (q y) * Real.cos (2 * (2 : ℕ) * ((qpeAngle 16 y - θ) / 2)) = _) at hd2
  have htel (k : ℕ) (hk : k ≤ 2) :
      ∑ j ∈ Finset.range (L - k), sineWindowCoeff L (j + k) * sineWindowCoeff L j =
        (((L - k : ℕ) : ℝ) * Real.cos (2 * (k : ℝ) * α) +
          Real.sin (2 * (k : ℝ) * α) / Real.sin (2 * α)) / (L : ℝ) := by
    have hterm (j : ℕ) (hj : j ∈ Finset.range (L - k)) :
        sineWindowCoeff L (j + k) * sineWindowCoeff L j = (1 / (L : ℝ)) *
          (Real.cos (2 * (k : ℝ) * α) - Real.cos ((4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α)) := by
      have hjl := Finset.mem_range.mp hj
      simp only [sineWindowCoeff, show j + k < L by omega, show j < L by omega, ↓reduceIte]
      have hsq : √(2 / (L : ℝ)) * √(2 / (L : ℝ)) = 2 / (L : ℝ) := Real.mul_self_sqrt (by positivity)
      set s1 := Real.sin (π * (((j + k : ℕ) : ℝ) + 1 / 2) / (L : ℝ))
      set s2 := Real.sin (π * ((j : ℝ) + 1 / 2) / (L : ℝ))
      have hsc : 2 * s1 * s2 =
          Real.cos (2 * (k : ℝ) * α) - Real.cos ((4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α) := by
        dsimp only [s1, s2]; push_cast
        rw [show π * ((j : ℝ) + (k : ℝ) + 1 / 2) / (L : ℝ) =
            (2 * (j : ℝ) + (k : ℝ) + 1) * α + (k : ℝ) * α by dsimp [α]; field_simp; ring,
          show π * ((j : ℝ) + 1 / 2) / (L : ℝ) =
            (2 * (j : ℝ) + (k : ℝ) + 1) * α - (k : ℝ) * α by dsimp [α]; field_simp; ring,
          show 2 * (k : ℝ) * α = 2 * ((k : ℝ) * α) by ring,
          show (4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α = 2 * ((2 * (j : ℝ) + (k : ℝ) + 1) * α) by ring]
        rw [Real.sin_add, Real.sin_sub, Real.cos_two_mul, Real.cos_two_mul]
        linear_combination 2 * Real.cos ((k : ℝ) * α) ^ 2 *
            Real.sin_sq_add_cos_sq ((2 * (j : ℝ) + (k : ℝ) + 1) * α) -
          2 * Real.cos ((2 * (j : ℝ) + (k : ℝ) + 1) * α) ^ 2 * Real.sin_sq_add_cos_sq ((k : ℝ) * α)
      calc √(2 / (L : ℝ)) * s1 * (√(2 / (L : ℝ)) * s2)
          = (1 / (L : ℝ)) * (2 * s1 * s2) := by linear_combination s1 * s2 * hsq
        _ = _ := by rw [hsc]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have hsum_cos : 2 * Real.sin (2 * α) *
        ∑ j ∈ Finset.range (L - k), Real.cos ((4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α) =
        -2 * Real.sin (2 * (k : ℝ) * α) := by
      have hstep (j : ℕ) : 2 * Real.sin (2 * α) * Real.cos ((4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α) =
          Real.sin ((4 * ((j + 1 : ℕ) : ℝ) + 2 * (k : ℝ)) * α) -
            Real.sin ((4 * (j : ℝ) + 2 * (k : ℝ)) * α) := by
        push_cast
        rw [show (4 * ((j : ℝ) + 1) + 2 * (k : ℝ)) * α =
            (4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α + 2 * α by ring,
          show (4 * (j : ℝ) + 2 * (k : ℝ)) * α =
            (4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α - 2 * α by ring, Real.sin_add, Real.sin_sub]; ring
      rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ ↦ hstep j,
        Finset.sum_range_sub (fun j ↦ Real.sin ((4 * (j : ℝ) + 2 * (k : ℝ)) * α))]
      simp only [Nat.cast_zero, mul_zero, zero_add]
      rw [Nat.cast_sub (by omega : k ≤ L),
        show (4 * ((L : ℝ) - (k : ℝ)) + 2 * (k : ℝ)) * α = 2 * π - 2 * (k : ℝ) * α by
          dsimp [α]; field_simp; ring,
        show 2 * π - 2 * (k : ℝ) * α = -(2 * (k : ℝ) * α) + 2 * π by ring,
        Real.sin_add_two_pi, Real.sin_neg]; ring
    have hcos_eq : ∑ j ∈ Finset.range (L - k), Real.cos ((4 * (j : ℝ) + 2 * (k : ℝ) + 2) * α) =
        -(Real.sin (2 * (k : ℝ) * α) / Real.sin (2 * α)) := by
      apply mul_left_cancel₀ (ne_of_gt (mul_pos zero_lt_two hsin2α))
      rw [hsum_cos]; field_simp [ne_of_gt hsin2α]
    rw [hcos_eq]; field_simp; ring
  have hs0 : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) = 1 := by
    have h0 : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
        Real.cos (2 * ((0 : ℕ) : ℝ) * ((qpeAngle 16 y - θ) / 2)) = _ := hd0.2
    simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one] at h0
    rw [h0, htel 0 (by omega)]; simp [ne_of_gt hLpos]
  have hodd : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
      (Real.sin ((qpeAngle 16 y - θ) / 2) ^ 3 * Real.cos ((qpeAngle 16 y - θ) / 2)) = 0 := by
    have htrig (y : Fin (2 ^ 16)) :
        Real.sin ((qpeAngle 16 y - θ) / 2) ^ 3 * Real.cos ((qpeAngle 16 y - θ) / 2) =
          (2 * Real.sin (2 * ((1 : ℕ) : ℝ) * ((qpeAngle 16 y - θ) / 2)) -
            Real.sin (2 * ((2 : ℕ) : ℝ) * ((qpeAngle 16 y - θ) / 2))) / 8 := by
      set u := (qpeAngle 16 y - θ) / 2
      rw [Nat.cast_one, Nat.cast_ofNat, show 2 * (1 : ℝ) * u = 2 * u by ring,
        show 2 * (2 : ℝ) * u = 2 * (2 * u) by ring,
        Real.sin_two_mul (2 * u), Real.sin_two_mul u, Real.cos_two_mul u,
        show Real.cos u ^ 2 = 1 - Real.sin u ^ 2 by linarith [Real.sin_sq_add_cos_sq u]]
      ring
    have hsum_rew : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
          (Real.sin ((qpeAngle 16 y - θ) / 2) ^ 3 * Real.cos ((qpeAngle 16 y - θ) / 2)) =
        (2 * ∑ y, Complex.normSq (q y) * Real.sin (2 * ((1 : ℕ) : ℝ) * ((qpeAngle 16 y - θ) / 2)) -
          ∑ y, Complex.normSq (q y) * Real.sin (2 * ((2 : ℕ) : ℝ) * ((qpeAngle 16 y - θ) / 2))) /
          8 := by
      simp_rw [htrig, ← mul_div_assoc]
      rw [← Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact congrArg (· / 8) (Finset.sum_congr rfl fun _ _ ↦ by ring)
    rw [hsum_rew, hd1.1, hd2.1]; norm_num
  have hs1_eq : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 2 =
      ((M : ℝ) / ((M : ℝ) + 1)) * Real.sin α ^ 2 := by
    have hpt (y : Fin (2 ^ 16)) : Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 2 =
        (Complex.normSq (q y) - Complex.normSq (q y) *
          Real.cos (2 * ((qpeAngle 16 y - θ) / 2))) / 2 := by
      rw [Real.cos_two_mul, show Real.cos ((qpeAngle 16 y - θ) / 2) ^ 2 =
        1 - Real.sin ((qpeAngle 16 y - θ) / 2) ^ 2 by
        linarith [Real.sin_sq_add_cos_sq ((qpeAngle 16 y - θ) / 2)]]
      ring
    simp_rw [hpt]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hs0]
    have h1cos : (∑ x : Fin (2 ^ 16),
          Complex.normSq (q x) * Real.cos (2 * ((qpeAngle 16 x - θ) / 2))) =
        ∑ x : Fin (2 ^ 16),
          Complex.normSq (q x) * Real.cos (2 * ((1 : ℕ) : ℝ) * ((qpeAngle 16 x - θ) / 2)) :=
      Finset.sum_congr rfl fun _ _ ↦ by rw [Nat.cast_one, mul_one]
    rw [h1cos, hd1.2, htel 1 (by omega)]
    simp only [Nat.cast_one, mul_one, show L - 1 = M by omega, div_self (ne_of_gt hsin2α)]
    rw [Real.cos_two_mul, show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by
      linarith [Real.sin_sq_add_cos_sq α]]
    dsimp [L]; push_cast; field_simp; ring
  have hs2_eq : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 4 =
      (1 / (2 * (L : ℝ))) * Real.sin α ^ 2 + (((L : ℝ) - 2) / (L : ℝ)) * Real.sin α ^ 4 := by
    have hpt (y : Fin (2 ^ 16)) : Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 4 =
        (8 * (Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - θ) / 2) ^ 2) -
          Complex.normSq (q y) +
          Complex.normSq (q y) * Real.cos (2 * ((2 : ℕ) : ℝ) * ((qpeAngle 16 y - θ) / 2))) / 8 := by
      set u := (qpeAngle 16 y - θ) / 2
      rw [Nat.cast_ofNat, show 2 * (2 : ℝ) * u = 2 * (2 * u) by ring, Real.cos_two_mul (2 * u),
        Real.cos_two_mul u,
        show Real.cos u ^ 2 = 1 - Real.sin u ^ 2 by linarith [Real.sin_sq_add_cos_sq u]]
      ring
    simp_rw [hpt]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hs1_eq, hs0, hd2.2, htel 2 (by omega)]
    rw [Nat.cast_sub (by omega : 2 ≤ L), Nat.cast_ofNat, show 2 * (2 : ℝ) * α = 2 * (2 * α) by ring,
      show Real.sin (2 * (2 * α)) / Real.sin (2 * α) = 2 * Real.cos (2 * α) by
        rw [Real.sin_two_mul (2 * α), mul_assoc, mul_comm (Real.sin (2 * α)), ← mul_assoc,
          mul_div_cancel_right₀ _ (ne_of_gt hsin2α)],
      Real.cos_two_mul (2 * α), Real.cos_two_mul α]
    have hc2 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by linarith [Real.sin_sq_add_cos_sq α]
    rw [hc2]; dsimp [L]; push_cast; field_simp; ring
  refine ⟨hs0, hodd, ?_, ?_⟩
  · rw [hs1_eq]
    have h2 : Real.sin α ^ 2 ≤ (π / (L : ℝ)) ^ 2 / 4 :=
      (pow_le_pow_left₀ hsinα0 hsinα 2).trans_eq (by ring)
    have hM_nn : (0 : ℝ) ≤ (M : ℝ) / ((M : ℝ) + 1) := by positivity
    refine (mul_le_mul_of_nonneg_left h2 hM_nn).trans_eq ?_
    dsimp [L]; push_cast; ring
  · rw [hs2_eq]
    have h2 : Real.sin α ^ 2 ≤ (π / (L : ℝ)) ^ 2 / 4 :=
      (pow_le_pow_left₀ hsinα0 hsinα 2).trans_eq (by ring)
    have h4 : Real.sin α ^ 4 ≤ (π / (L : ℝ)) ^ 4 / 16 := by
      have := pow_le_pow_left₀ (sq_nonneg _) h2 2; linarith [show (Real.sin α ^ 2) ^ 2 =
        Real.sin α ^ 4 by ring, show ((π / (L : ℝ)) ^ 2 / 4) ^ 2 = (π / (L : ℝ)) ^ 4 / 16 by ring]
    have h2L : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 2 ≤ L)
    have hL2 : 0 ≤ ((L : ℝ) - 2) / (L : ℝ) := div_nonneg (by linarith) hLpos.le
    have hL2_le : ((L : ℝ) - 2) / (L : ℝ) ≤ 1 := (div_le_one hLpos).mpr (by linarith)
    have hterm1 : (1 / (2 * (L : ℝ))) * Real.sin α ^ 2 ≤
        (1 / (2 * (L : ℝ))) * ((π / (L : ℝ)) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg zero_le_one (mul_nonneg zero_le_two hLpos.le))
    have hterm2 : (((L : ℝ) - 2) / (L : ℝ)) * Real.sin α ^ 4 ≤ 1 * ((π / (L : ℝ)) ^ 4 / 16) :=
      mul_le_mul hL2_le h4 (pow_nonneg hsinα0 4) zero_le_one
    refine (add_le_add hterm1 hterm2).trans_eq ?_
    dsimp [L]; push_cast; have : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    field_simp; ring

private theorem sineWindow_sidelobe_eq {M : ℕ} (hMhi : M ≤ 47488) (θ : ℝ) (y : Fin (2 ^ 16)) :
    let L := M + 1; let u := (qpeAngle 16 y - θ) / 2
    let q := (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff L) θ
    (Real.sin u ^ 2 - Real.sin (π / (2 * (L : ℝ))) ^ 2) ^ 2 * Complex.normSq (q y) =
      (1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 * Real.cos u ^ 2 *
        Real.cos ((L : ℝ) * u) ^ 2 := by
  intro L u q; let α := π / (2 * (L : ℝ)); have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  let z : ℂ := Complex.exp (((-2 * u : ℝ) : ℂ) * Complex.I)
  let f : ℕ → ℂ := fun m ↦ (Real.sin ((2 * (m : ℝ) + 1) * α) : ℂ)
  let c : ℂ := (Real.cos (2 * α) : ℂ)
  have hqy : q y = ((1 / 256 : ℂ) * (√(2 / (L : ℝ)) : ℂ)) *
      ∑ m ∈ Finset.range L, f m * z ^ m := by
    dsimp only [q]; simp only [Matrix.mulVec, dotProduct]
    let S : Finset (Fin (2 ^ 16)) := Finset.univ.filter fun m ↦ m.val ≤ M
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun m _ hm ↦ by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hm; simp [windowPhaseVec, hm])]
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun m _ ↦ m.val)
      (fun m hm ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hm).2))
      (fun _ _ _ _ h ↦ Fin.ext h)
      (fun m hm ↦ ⟨⟨m, (Finset.mem_range.mp hm).trans (by omega)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_lt_succ (Finset.mem_range.mp hm)⟩, rfl⟩)
      fun m hm ↦ ?_
    have hml := (Finset.mem_filter.mp hm).2
    have hlt : m.val < L := by omega
    rw [iqft16_apply]; simp only [windowPhaseVec, hml, sineWindowCoeff, hlt, ↓reduceIte]
    have harg : π * ((m.val : ℝ) + 1 / 2) / (L : ℝ) = (2 * (m.val : ℝ) + 1) * α := by
      dsimp [α]; field_simp
    have hexp : Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ)) *
        Complex.exp (Complex.I * (m.val : ℂ) * (θ : ℂ)) = z ^ m.val := by
      dsimp [z]; rw [← Complex.exp_add, ← Complex.exp_nat_mul]
      set uy : ℝ := (qpeAngle 16 y - θ) / 2
      have harg2 : -Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ) +
          Complex.I * (m.val : ℂ) * (θ : ℂ) =
          (m.val : ℂ) * (((-2 * uy : ℝ) : ℂ) * Complex.I) := by
        have huy : ((-2 * uy : ℝ) : ℂ) = -((qpeAngle 16 y : ℂ) - (θ : ℂ)) := by
          dsimp only [uy, u]; rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub]
          norm_num; ring
        rw [huy]; ring
      exact congrArg Complex.exp harg2
    rw [harg, Complex.ofReal_mul]
    dsimp only [f]
    linear_combination (1 / 256 : ℂ) * (√(2 / (L : ℝ)) : ℂ) *
      (Real.sin ((2 * (m.val : ℝ) + 1) * α) : ℂ) * hexp
  have hrec (m : ℕ) : f (m + 2) + f m = 2 * c * f (m + 1) := by
    dsimp only [f, c]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_add, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    rw [show (2 * ((m + 2 : ℕ) : ℝ) + 1) * α = (2 * ((m + 1 : ℕ) : ℝ) + 1) * α + 2 * α by
        push_cast; ring,
      show (2 * (m : ℝ) + 1) * α = (2 * ((m + 1 : ℕ) : ℝ) + 1) * α - 2 * α by push_cast; ring,
      Real.sin_add, Real.sin_sub]
    ring
  have hind (k : ℕ) : (1 - 2 * c * z + z ^ 2) * ∑ m ∈ Finset.range (k + 1), f m * z ^ m =
      f 0 + (f 1 - 2 * c * f 0) * z - f (k + 1) * z ^ (k + 1) + f k * z ^ (k + 2) := by
    induction k with
    | zero => simp [Finset.range_one]; ring
    | succ k ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        linear_combination (z ^ (k + 2)) * hrec k
  have hpoly : (1 - 2 * c * z + z ^ 2) * ∑ m ∈ Finset.range L, f m * z ^ m =
      (Real.sin α : ℂ) * (1 + z) * (1 + z ^ L) := by
    rw [hind M]
    have hf0 : f 0 = (Real.sin α : ℂ) := by dsimp [f]; norm_num
    have hf1 : f 1 - 2 * c * f 0 = (Real.sin α : ℂ) := by
      dsimp only [f, c]
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Nat.cast_one, Nat.cast_zero,
        ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
      apply congrArg Complex.ofReal
      rw [show (2 * (1 : ℝ) + 1) * α = 2 * α + α by ring,
        show (2 * (0 : ℝ) + 1) * α = α by ring, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
      ring
    have hfL : f L = -(Real.sin α : ℂ) := by
      dsimp [f]; rw [show (2 * (L : ℝ) + 1) * α = α + π by dsimp [α]; field_simp; ring,
        Real.sin_add_pi, Complex.ofReal_neg]
    have hfM : f M = (Real.sin α : ℂ) := by
      dsimp [f]
      rw [show (2 * (M : ℝ) + 1) * α = π - α by dsimp [α, L]; push_cast; field_simp; ring,
        Real.sin_pi_sub]
    rw [hf1, hf0, show M + 1 = L from rfl, hfL, hfM]; ring
  have hz1 : Complex.normSq (1 + z) = 4 * Real.cos u ^ 2 := by
    dsimp [z]; rw [Complex.exp_ofReal_mul_I]
    have : (1 : ℂ) + (↑(Real.cos (-2 * u)) + ↑(Real.sin (-2 * u)) * Complex.I) =
        ((1 + Real.cos (2 * u) : ℝ) : ℂ) + ((-Real.sin (2 * u) : ℝ) : ℂ) * Complex.I := by
      rw [show -2 * u = -(2 * u) by ring, Real.cos_neg, Real.sin_neg]; push_cast; ring
    rw [this, Complex.normSq_add_mul_I, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination 4 * Real.cos u ^ 2 * Real.sin_sq_add_cos_sq u
  have hzL : Complex.normSq (1 + z ^ L) = 4 * Real.cos ((L : ℝ) * u) ^ 2 := by
    have : z ^ L = Complex.exp (((-2 * ((L : ℝ) * u) : ℝ) : ℂ) * Complex.I) := by
      dsimp [z]; rw [← Complex.exp_nat_mul]; exact congrArg Complex.exp (by push_cast; ring)
    rw [this, Complex.exp_ofReal_mul_I]
    have h2 : (1 : ℂ) + (↑(Real.cos (-2 * ((L : ℝ) * u))) +
        ↑(Real.sin (-2 * ((L : ℝ) * u))) * Complex.I) =
        ((1 + Real.cos (2 * ((L : ℝ) * u)) : ℝ) : ℂ) +
          ((-Real.sin (2 * ((L : ℝ) * u)) : ℝ) : ℂ) * Complex.I := by
      rw [show -2 * ((L : ℝ) * u) = -(2 * ((L : ℝ) * u)) by ring, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [h2, Complex.normSq_add_mul_I, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination 4 * Real.cos ((L : ℝ) * u) ^ 2 * Real.sin_sq_add_cos_sq ((L : ℝ) * u)
  have hzq : Complex.normSq (1 - 2 * c * z + z ^ 2) =
      16 * (Real.sin u ^ 2 - Real.sin α ^ 2) ^ 2 := by
    have hfac : 1 - 2 * c * z + z ^ 2 =
        z * (((2 * Real.cos (2 * u) - 2 * Real.cos (2 * α) : ℝ) : ℂ)) := by
      dsimp [z, c]; rw [Complex.exp_ofReal_mul_I]
      have hz2 : Complex.exp (((-2 * u : ℝ) : ℂ) * Complex.I) ^ 2 =
          Complex.exp (((-4 * u : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_nat_mul]; exact congrArg Complex.exp (by push_cast; ring)
      rw [← Complex.exp_ofReal_mul_I, hz2, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
        show -2 * u = -(2 * u) by ring, show -4 * u = -(2 * (2 * u)) by ring, Real.cos_neg,
        Real.sin_neg, Real.cos_neg, Real.sin_neg, Real.cos_two_mul (2 * u),
        Real.sin_two_mul (2 * u)]
      push_cast; ring
    rw [hfac, map_mul, show Complex.normSq z = 1 by
      dsimp [z]; rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, _root_.one_pow],
      one_mul, Complex.normSq_ofReal, Real.cos_two_mul u, Real.cos_two_mul α,
      show Real.cos u ^ 2 = 1 - Real.sin u ^ 2 by linarith [Real.sin_sq_add_cos_sq u],
      show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by linarith [Real.sin_sq_add_cos_sq α]]
    ring
  have hns := congrArg Complex.normSq hpoly
  simp only [map_mul, Complex.normSq_ofReal, hzq, hz1, hzL] at hns
  rw [hqy, map_mul, map_mul, show Complex.normSq (1 / 256 : ℂ) = 1 / 65536 by norm_num,
    Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 / L)]
  dsimp [α] at hns; linear_combination (1 / 524288 : ℝ) * (1 / (L : ℝ)) * hns

private theorem quartet_weights {M : ℕ} (hMlo : 46368 ≤ M) (hMhi : M ≤ 47488) :
    let L := M + 1; let du := π / 65536; let w0 := 1 / (8 * Real.sin ((L : ℝ) * du) ^ 2)
    let w1 := 1 / 2 - w0
    (185 / 1000 ≤ w0 ∧ w0 ≤ 219 / 1000) ∧ ∀ u : ℝ,
      w0 * Real.cos ((L : ℝ) * u) ^ 2 + w1 * Real.cos ((L : ℝ) * (u + du)) ^ 2 +
        w1 * Real.cos ((L : ℝ) * (u + 2 * du)) ^ 2 +
        w0 * Real.cos ((L : ℝ) * (u + 3 * du)) ^ 2 = 1 / 2 := by
  intro L du w0 w1; let θs := (L : ℝ) * du; let z := π - θs
  have hpi_lo := Real.pi_gt_d20; have hpi_hi := Real.pi_lt_d20
  have hL_lo : (46369 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.succ_le_succ hMlo
  have hL_hi : (L : ℝ) ≤ 47489 := by exact_mod_cast Nat.succ_le_succ hMhi
  have hz_lo : 865 / 1000 ≤ z := by dsimp [z, θs, du]; nlinarith only [hpi_lo, hpi_hi, hL_hi]
  have hz_hi : z ≤ 919 / 1000 := by dsimp [z, θs, du]; nlinarith only [hpi_lo, hpi_hi, hL_lo]
  have hsin_eq : Real.sin θs = Real.sin z := by dsimp [z]; rw [Real.sin_pi_sub]
  have hsin_lo : 757 / 1000 ≤ Real.sin θs := by
    rw [hsin_eq]; have h := Real.sin_gt_sub_cube (by linarith only [hz_lo] : 0 < z)
    nlinarith only [h, hz_lo, hz_hi, sq_nonneg (z - 865 / 1000)]
  have hcos_z : 1 - (919 / 1000) ^ 2 / 2 ≤ Real.cos z := by
    have h1 := Real.sin_le (by linarith only [hz_lo] : 0 ≤ z / 2)
    have hc2 := Real.cos_two_mul (z / 2)
    rw [show 2 * (z / 2) = z by ring] at hc2
    have hpy := Real.sin_sq_add_cos_sq (z / 2)
    have hs0 : 0 ≤ Real.sin (z / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith only [hz_lo])
        (by linarith only [hz_hi, hpi_lo])
    have hs2 : Real.sin (z / 2) ^ 2 ≤ (919 / 2000) ^ 2 :=
      pow_le_pow_left₀ hs0 (by linarith only [h1, hz_hi]) 2
    linarith only [hc2, hpy, hs2]
  have hsin_sq_hi : Real.sin θs ^ 2 ≤ 1 - (1 - (919 / 1000) ^ 2 / 2) ^ 2 := by
    rw [hsin_eq]
    have hc2 : (1 - (919 / 1000) ^ 2 / 2) ^ 2 ≤ Real.cos z ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hcos_z 2
    linarith only [hc2, Real.sin_sq_add_cos_sq z]
  have hsin_sq_pos : 0 < Real.sin θs ^ 2 := by positivity
  refine ⟨⟨?_, ?_⟩, fun u ↦ ?_⟩
  · dsimp [w0]; rw [le_div_iff₀ (by positivity)]
    have : Real.sin ((L : ℝ) * du) ^ 2 ≤ 1 - (1 - (919 / 1000) ^ 2 / 2) ^ 2 := hsin_sq_hi
    linarith only [this]
  · dsimp [w0]; rw [div_le_iff₀ (by positivity)]
    have : (757 / 1000) ^ 2 ≤ Real.sin ((L : ℝ) * du) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hsin_lo 2
    linarith only [this]
  · have hcsq (x : ℝ) : Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
      rw [Real.cos_two_mul]; ring
    have hcos_sum (a b : ℝ) : Real.cos (a - b) + Real.cos (a + b) = 2 * Real.cos a * Real.cos b :=
      by rw [Real.cos_sub, Real.cos_add]; ring
    rw [hcsq, hcsq, hcsq, hcsq]
    let β := 2 * (L : ℝ) * u + 3 * θs
    have hp03 : Real.cos (2 * ((L : ℝ) * u)) + Real.cos (2 * ((L : ℝ) * (u + 3 * du))) =
        2 * Real.cos β * Real.cos (3 * θs) := by
      rw [show 2 * ((L : ℝ) * u) = β - 3 * θs by dsimp [β, θs]; ring,
        show 2 * ((L : ℝ) * (u + 3 * du)) = β + 3 * θs by dsimp [β, θs]; ring,
        hcos_sum]
    have hp12 : Real.cos (2 * ((L : ℝ) * (u + du))) + Real.cos (2 * ((L : ℝ) * (u + 2 * du))) =
        2 * Real.cos β * Real.cos θs := by
      rw [show 2 * ((L : ℝ) * (u + du)) = β - θs by dsimp [β, θs]; ring,
        show 2 * ((L : ℝ) * (u + 2 * du)) = β + θs by dsimp [β, θs]; ring,
        hcos_sum]
    have hc3 : Real.cos (3 * θs) = 4 * Real.cos θs ^ 3 - 3 * Real.cos θs := by
      rw [show 3 * θs = 2 * θs + θs by ring, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
      linear_combination -2 * Real.cos θs * Real.sin_sq_add_cos_sq θs
    have hw0_sin : w0 * (8 * Real.sin θs ^ 2) = 1 := by
      dsimp [w0, θs] at hsin_sq_pos ⊢; exact div_mul_cancel₀ 1 (ne_of_gt (by positivity))
    have hcos_id : 4 * Real.cos θs ^ 2 - 4 = -4 * Real.sin θs ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θs]
    have hw1_eq : w1 = 1 / 2 - w0 := rfl
    calc w0 * ((1 + Real.cos (2 * ((L : ℝ) * u))) / 2) +
          w1 * ((1 + Real.cos (2 * ((L : ℝ) * (u + du)))) / 2) +
          w1 * ((1 + Real.cos (2 * ((L : ℝ) * (u + 2 * du)))) / 2) +
          w0 * ((1 + Real.cos (2 * ((L : ℝ) * (u + 3 * du)))) / 2)
        = (w0 + w1) + (w0 / 2) * (Real.cos (2 * ((L : ℝ) * u)) +
            Real.cos (2 * ((L : ℝ) * (u + 3 * du)))) +
            (w1 / 2) * (Real.cos (2 * ((L : ℝ) * (u + du))) +
              Real.cos (2 * ((L : ℝ) * (u + 2 * du)))) := by ring
      _ = (w0 + w1) + Real.cos β * (w0 * Real.cos (3 * θs) + w1 * Real.cos θs) := by
          rw [hp03, hp12]; ring
      _ = 1 / 2 := by
          rw [hc3, hw1_eq]
          linear_combination Real.cos β * Real.cos θs * w0 * hcos_id -
            (1 / 2) * Real.cos β * Real.cos θs * hw0_sin

private theorem chordal_midpoint_sos {γ a b sx sy D : ℝ} (hγlo : 949 / 1000 ≤ γ)
    (hγhi : γ ≤ 9555 / 10000) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hsx : a ^ 2 + sx ^ 2 = 1) (hsy : b ^ 2 + sy ^ 2 = 1) (hsx0 : 0 ≤ sx) (hsy0 : 0 ≤ sy)
    (hs_mid : γ + 6 / 10000 ≤ (a + b) / 2) (hD0 : 0 ≤ D) (hD_le : D ≤ |b - a|) :
    D ^ 2 ≤ (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) * (a * sy - b * sx) ^ 2 := by
  let K := (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2)
  have hK0 : 0 < K := by dsimp [K]; nlinarith only [hγlo, hγhi]
  let P := a ^ 2 + b ^ 2 - 2 * a ^ 2 * b ^ 2; let Q := 2 * a * b * sx * sy
  have hPQ_eq : (a * sy - b * sx) ^ 2 = P - Q := by
    dsimp [P, Q]; linear_combination a ^ 2 * hsy + b ^ 2 * hsx
  have hPQ_id : P ^ 2 - Q ^ 2 = (a ^ 2 - b ^ 2) ^ 2 := by
    dsimp [P, Q]
    linear_combination -4 * a ^ 2 * b ^ 2 * (1 - b ^ 2) * hsx - 4 * a ^ 2 * b ^ 2 * sx ^ 2 * hsy
  rw [hPQ_eq]; suffices h : D ^ 2 ≤ K * (P - Q) from h
  suffices hab : (b - a) ^ 2 ≤ K * (P - Q) by
    have hD2 : D ^ 2 ≤ (b - a) ^ 2 := by rw [← sq_abs (b - a)]; exact pow_le_pow_left₀ hD0 hD_le 2
    linarith only [hD2, hab]
  let s := (a + b) / 2; let d := (b - a) / 2
  have hs_lo : γ + 6 / 10000 ≤ s := hs_mid
  have hs_hi : s ≤ 1 := by dsimp [s]; linarith only [ha1, hb1]
  have hs_nn : 0 ≤ s := by linarith only [hs_lo, hγlo]
  have hKs : 1 - s ^ 2 ≤ K := by
    have hs2 : (γ + 6 / 10000) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith only [hγlo]) hs_lo 2
    have hγ2 : (949 / 1000) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (by norm_num) hγlo 2
    dsimp [K]; linarith only [hs2, hγ2, hγlo]
  have hK3 : K ≤ 1 / 10 := by
    have hγ2 : (949 / 1000) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (by norm_num) hγlo 2
    dsimp [K]; linarith only [hγ2]
  have hP_ub : P ≤ 2 * s ^ 2 * (1 - s ^ 2) + 2 * d ^ 2 * (1 + 2 * s ^ 2) := by
    have hid : P = 2 * s ^ 2 * (1 - s ^ 2) + 2 * d ^ 2 * (1 + 2 * s ^ 2) - 2 * d ^ 4 := by
      dsimp [P, s, d]; ring
    linarith only [hid, show 0 ≤ 2 * d ^ 4 by positivity]
  have h1 : 4 * d ^ 2 ≤ K * P := by
    have hs1p : 1 - s ≤ (1 - s ^ 2) / (19 / 10) := by nlinarith only [hs_hi, hs_lo, hγlo]
    have hP_nn : 0 ≤ P := by
      have hid : P = a ^ 2 * sy ^ 2 + b ^ 2 * sx ^ 2 := by
        dsimp [P]; linear_combination -a ^ 2 * hsy - b ^ 2 * hsx
      rw [hid]; positivity
    have hP_ge : 4 * s * |d| ≤ P := by
      have hsq : (4 * s * |d|) ^ 2 ≤ P ^ 2 := by
        rw [mul_pow, sq_abs]
        have hid : (4 * s) ^ 2 * d ^ 2 = (a ^ 2 - b ^ 2) ^ 2 := by dsimp [s, d]; ring
        rw [hid]; linarith only [hPQ_id, sq_nonneg Q]
      have h4sd : 0 ≤ 4 * s * |d| := by positivity
      nlinarith only [hsq, hP_nn, h4sd]
    have hd_abs : |d| ≤ 1 - s := abs_le.mpr
      ⟨by dsimp [s, d]; linarith only [ha1, hb0], by dsimp [s, d]; linarith only [hb1, ha0]⟩
    have hK_d : (19 / 10) * |d| ≤ K := by linarith only [hd_abs, hs1p, hKs]
    have hs_d : (37 / 10) * |d| ≤ P :=
      (mul_le_mul_of_nonneg_right (by linarith only [hs_lo, hγlo] : (37 / 10 : ℝ) ≤ 4 * s)
        (abs_nonneg d)).trans hP_ge
    have hmul := mul_le_mul hK_d hs_d (by positivity) hK0.le
    have hrew : (19 / 10) * |d| * ((37 / 10) * |d|) = (703 / 100) * d ^ 2 := by
      calc (19 / 10) * |d| * ((37 / 10) * |d|) = (703 / 100) * |d| ^ 2 := by ring
        _ = (703 / 100) * d ^ 2 := by rw [sq_abs]
    linarith only [hmul, hrew, sq_nonneg d]
  have h2 : (K * Q) ^ 2 ≤ (K * P - 4 * d ^ 2) ^ 2 := by
    have hid : (K * P - 4 * d ^ 2) ^ 2 - (K * Q) ^ 2 =
        K ^ 2 * (P ^ 2 - Q ^ 2) - 8 * K * P * d ^ 2 + 16 * d ^ 4 := by ring
    rw [← sub_nonneg, hid, hPQ_id,
      show (a ^ 2 - b ^ 2) ^ 2 = 16 * s ^ 2 * d ^ 2 by dsimp [s, d]; ring]
    have hmul := mul_le_mul_of_nonneg_left hP_ub
      (mul_nonneg (by positivity : 0 ≤ 8 * K) (sq_nonneg d))
    have hs2_le : s ^ 2 ≤ 1 := by
      have := pow_le_pow_left₀ hs_nn hs_hi 2; linarith only [this]
    have h1mK : 0 ≤ 1 - K * (1 + 2 * s ^ 2) := by nlinarith only [hK0, hK3, hs2_le, sq_nonneg s]
    have hcore : 0 ≤ 16 * K * s ^ 2 * (K - (1 - s ^ 2)) * d ^ 2 +
        16 * d ^ 4 * (1 - K * (1 + 2 * s ^ 2)) := by
      have hsub : 0 ≤ K - (1 - s ^ 2) := by linarith only [hKs]
      positivity
    linarith only [hmul, hcore,
      show K ^ 2 * (16 * s ^ 2 * d ^ 2) -
          8 * K * d ^ 2 * (2 * s ^ 2 * (1 - s ^ 2) + 2 * d ^ 2 * (1 + 2 * s ^ 2)) + 16 * d ^ 4 =
        16 * K * s ^ 2 * (K - (1 - s ^ 2)) * d ^ 2 +
          16 * d ^ 4 * (1 - K * (1 + 2 * s ^ 2)) by ring]
  have hQ0 : 0 ≤ K * Q := by dsimp [Q]; positivity
  have hKP_nn : 0 ≤ K * P - 4 * d ^ 2 := by linarith only [h1]
  have hKQ_le : K * Q ≤ K * P - 4 * d ^ 2 := by nlinarith only [h2, hQ0, hKP_nn]
  have hba : (b - a) ^ 2 = 4 * d ^ 2 := by dsimp [d]; ring
  linarith only [hKQ_le, hba, show K * (P - Q) = K * P - K * Q by ring]

private theorem clamped_regime1_3a_le {γ x y : ℝ} (hγlo : 949 / 1000 ≤ γ)
    (hγhi : γ ≤ 9555 / 10000)
    (hreg : γ + 3 / 2500 ≤ |Real.cos y| ∨ |Real.cos y| ≤ γ - 1 / 20000) :
    (max |Real.cos x| γ - max |Real.cos y| γ) ^ 2 ≤
      (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) * Real.sin (x - y) ^ 2 := by
  let a := |Real.cos x|; let b := |Real.cos y|
  let sx := |Real.sin x|; let sy := |Real.sin y|
  have ha0 : 0 ≤ a := abs_nonneg _; have hb0 : 0 ≤ b := abs_nonneg _
  have ha1 : a ≤ 1 := Real.abs_cos_le_one x; have hb1 : b ≤ 1 := Real.abs_cos_le_one y
  have hsx : a ^ 2 + sx ^ 2 = 1 := by
    dsimp [a, sx]; rw [sq_abs, sq_abs]; exact Real.cos_sq_add_sin_sq x
  have hsy : b ^ 2 + sy ^ 2 = 1 := by
    dsimp [b, sy]; rw [sq_abs, sq_abs]; exact Real.cos_sq_add_sin_sq y
  have hK_nn : 0 ≤ (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) := by nlinarith only [hγlo, hγhi]
  have hrev : (a * sy - b * sx) ^ 2 ≤ Real.sin (x - y) ^ 2 := by
    have h1 : |a * sy - b * sx| ≤ |Real.sin (x - y)| := by
      rw [Real.sin_sub, abs_sub_comm]
      have := abs_abs_sub_abs_le_abs_sub (Real.sin x * Real.cos y) (Real.cos x * Real.sin y)
      simpa only [abs_mul, a, b, sx, sy, mul_comm b sx] using this
    rw [← sq_abs, ← sq_abs (Real.sin (x - y))]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  change (max a γ - max b γ) ^ 2 ≤ _
  rcases hreg with hR1 | hR3a
  · rcases le_total γ a with ha_ge | ha_le
    · have h1 := chordal_midpoint_sos hγlo hγhi ha0 ha1 hb0 hb1 hsx hsy (abs_nonneg _)
        (abs_nonneg _) (by dsimp [b] at *; linarith only [hR1, ha_ge]) (abs_nonneg (b - a)) le_rfl
      rw [sq_abs] at h1
      rw [max_eq_left ha_ge, max_eq_left (by dsimp [b] at *; linarith only [hR1] : γ ≤ b)]
      exact (le_of_eq (by ring : (a - b) ^ 2 = (b - a) ^ 2)).trans
        (h1.trans (mul_le_mul_of_nonneg_left hrev hK_nn))
    · let sγ := √(1 - γ ^ 2)
      have hsγ0 : 0 ≤ sγ := Real.sqrt_nonneg _
      have hsγ2 : γ ^ 2 + sγ ^ 2 = 1 := by
        dsimp [sγ]; rw [Real.sq_sqrt (by nlinarith only [hγlo, hγhi])]; ring
      have h1 := chordal_midpoint_sos hγlo hγhi (by linarith only [hγlo]) (by linarith only [hγhi])
        hb0 hb1 hsγ2 hsy hsγ0 (abs_nonneg _)
        (by dsimp [b] at *; linarith only [hR1])
        (by dsimp [b] at *; linarith only [hR1] : 0 ≤ b - γ) (le_abs_self (b - γ))
      have hmono : (γ * sy - b * sγ) ^ 2 ≤ (a * sy - b * sx) ^ 2 := by
        have hsx_ge : sγ ≤ sx := by
          dsimp only [sx]; rw [← Real.sqrt_sq (abs_nonneg (Real.sin x))]
          have ha2 : a ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ ha0 ha_le 2
          exact Real.sqrt_le_sqrt (by linarith only [hsx, ha2])
        have hsy_le : sy ≤ sγ := by
          dsimp only [sy]; rw [← Real.sqrt_sq (abs_nonneg (Real.sin y))]
          have hb2 : γ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith only [hγlo])
            (by dsimp [b] at *; linarith only [hR1]) 2
          exact Real.sqrt_le_sqrt (by linarith only [hsy, hb2])
        have hm1 : γ * sy ≤ b * sγ := mul_le_mul (by dsimp [b] at *; linarith only [hR1]) hsy_le
          (abs_nonneg _) (by dsimp [b] at *; linarith only [hR1, hγlo])
        have hm2 : b * sγ ≤ b * sx := mul_le_mul_of_nonneg_left hsx_ge hb0
        have hm3 : a * sy ≤ γ * sy := mul_le_mul_of_nonneg_right ha_le (abs_nonneg _)
        have hpos : 0 ≤ b * sγ - γ * sy := by linarith only [hm1]
        have hle : b * sγ - γ * sy ≤ b * sx - a * sy := by linarith only [hm2, hm3]
        exact (le_of_eq (by ring : (γ * sy - b * sγ) ^ 2 = (b * sγ - γ * sy) ^ 2)).trans
          ((pow_le_pow_left₀ hpos hle 2).trans_eq (by ring))
      rw [max_eq_right ha_le, max_eq_left (by dsimp [b] at *; linarith only [hR1] : γ ≤ b)]
      exact (le_of_eq (by ring : (γ - b) ^ 2 = (b - γ) ^ 2)).trans
        (h1.trans ((mul_le_mul_of_nonneg_left hmono hK_nn).trans
          (mul_le_mul_of_nonneg_left hrev hK_nn)))
  · rcases le_total a γ with ha_le | ha_ge
    · rw [max_eq_right ha_le, max_eq_right (by dsimp [b] at *; linarith only [hR3a] : b ≤ γ),
        sub_self, zero_pow two_ne_zero]
      exact mul_nonneg hK_nn (sq_nonneg _)
    · let γ' := γ - 1 / 20000
      have hγ'0 : 0 ≤ γ' := by dsimp [γ']; linarith only [hγlo]
      have hγ'1 : γ' ≤ 1 := by dsimp [γ']; linarith only [hγhi]
      rw [max_eq_left ha_ge, max_eq_right (by dsimp [b] at *; linarith only [hR3a] : b ≤ γ)]
      rcases le_total a (γ + 13 / 10000) with ha_mid | ha_hi
      · have hratio : a - γ ≤ (26 / 27) * (a - γ') := by dsimp [γ']; linarith only [ha_mid]
        have hlip := abs_max_abs_cos_sub_le hγ'0 hγ'1 x y
        change |max a γ' - max b γ'| ≤ _ at hlip
        rw [max_eq_left (by dsimp [γ']; linarith only [ha_ge] : γ' ≤ a), max_eq_right hR3a,
          abs_of_nonneg (by dsimp [γ']; linarith only [ha_ge] : 0 ≤ a - γ')] at hlip
        have hsq : (a - γ) ^ 2 ≤ (26 / 27) ^ 2 * (1 - γ' ^ 2) * Real.sin (x - y) ^ 2 := by
          have h2 : a - γ ≤ (26 / 27) * (√(1 - γ' ^ 2) * |Real.sin (x - y)|) :=
            hratio.trans (mul_le_mul_of_nonneg_left hlip (by norm_num))
          have h3 := pow_le_pow_left₀ (by linarith only [ha_ge]) h2 2
          rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith only [hγ'0, hγ'1]), sq_abs] at h3
          linarith only [h3, show (26 / 27) ^ 2 * ((1 - γ' ^ 2) * Real.sin (x - y) ^ 2) =
            (26 / 27) ^ 2 * (1 - γ' ^ 2) * Real.sin (x - y) ^ 2 by ring]
        have hcoef : (26 / 27) ^ 2 * (1 - γ' ^ 2) ≤ (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) := by
          dsimp [γ']; nlinarith only [hγlo, hγhi, sq_nonneg (9555 / 10000 - γ)]
        exact hsq.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      · let s' := √(1 - γ' ^ 2)
        have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
        have hs'2 : γ' ^ 2 + s' ^ 2 = 1 := by
          dsimp [s']; rw [Real.sq_sqrt (by nlinarith only [hγ'0, hγ'1])]; ring
        have h1 := chordal_midpoint_sos hγlo hγhi ha0 ha1 hγ'0 hγ'1 hsx hs'2 (abs_nonneg _) hs'0
          (by dsimp [γ']; linarith only [ha_hi]) (by linarith only [ha_ge] : 0 ≤ a - γ)
          (by rw [abs_sub_comm, abs_of_nonneg (by dsimp [γ']; linarith only [ha_ge])]
              dsimp [γ']; linarith only)
        have hmono : (a * s' - γ' * sx) ^ 2 ≤ (a * sy - b * sx) ^ 2 := by
          have hsx_le : sx ≤ s' := by
            dsimp only [sx]; rw [← Real.sqrt_sq (abs_nonneg (Real.sin x))]
            have ha2 : γ' ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hγ'0
              (by dsimp [γ']; linarith only [ha_hi]) 2
            exact Real.sqrt_le_sqrt (by linarith only [hsx, ha2])
          have hsy_ge : s' ≤ sy := by
            dsimp only [sy]; rw [← Real.sqrt_sq (abs_nonneg (Real.sin y))]
            have hb2 : b ^ 2 ≤ γ' ^ 2 := pow_le_pow_left₀ hb0 hR3a 2
            exact Real.sqrt_le_sqrt (by linarith only [hsy, hb2])
          have hm1 : γ' * sx ≤ a * s' := mul_le_mul (by dsimp [γ']; linarith only [ha_hi]) hsx_le
            (abs_nonneg _) ha0
          have hm2 : a * s' ≤ a * sy := mul_le_mul_of_nonneg_left hsy_ge ha0
          have hm3 : b * sx ≤ γ' * sx := mul_le_mul_of_nonneg_right hR3a (abs_nonneg _)
          have hpos : 0 ≤ a * s' - γ' * sx := by linarith only [hm1]
          have hle : a * s' - γ' * sx ≤ a * sy - b * sx := by linarith only [hm2, hm3]
          exact (pow_le_pow_left₀ hpos hle 2)
        exact h1.trans ((mul_le_mul_of_nonneg_left hmono hK_nn).trans
          (mul_le_mul_of_nonneg_left hrev hK_nn))

private theorem clamped_majorant_le {γ φ' : ℝ} (hγlo : 949 / 1000 ≤ γ) (hγhi : γ ≤ 9555 / 10000)
    (hc0lo : γ - 1 / 20000 ≤ Real.cos φ') (hc0hi : Real.cos φ' ≤ γ + 3 / 2500)
    (hs0_nn : 0 ≤ Real.sin φ') (u : ℝ) :
    let c0 := Real.cos φ'; let s0 := Real.sin φ'
    (max |Real.cos (φ' + u)| γ - max c0 γ) ^ 2 ≤
      s0 ^ 2 * Real.sin u ^ 2 + (247 / 1000) * Real.sin u ^ 4 +
        s0 * c0 * (Real.sin u ^ 3 * Real.cos u) := by
  intro c0 s0
  suffices hpos : ∀ v : ℝ, 0 ≤ Real.cos v → (max |Real.cos (φ' + v)| γ - max c0 γ) ^ 2 ≤
      s0 ^ 2 * Real.sin v ^ 2 + (247 / 1000) * Real.sin v ^ 4 +
        s0 * c0 * (Real.sin v ^ 3 * Real.cos v) by
    rcases le_total 0 (Real.cos u) with hc | hc
    · exact hpos u hc
    · have h := hpos (u + π) (by rw [Real.cos_add_pi]; linarith only [hc])
      have h1 : |Real.cos (φ' + (u + π))| = |Real.cos (φ' + u)| := by
        rw [show φ' + (u + π) = (φ' + u) + π by ring, Real.cos_add_pi, abs_neg]
      rw [h1, Real.sin_add_pi, Real.cos_add_pi] at h
      linarith only [h, show (-Real.sin u) ^ 2 = Real.sin u ^ 2 by ring,
        show (-Real.sin u) ^ 4 = Real.sin u ^ 4 by ring,
        show (-Real.sin u) ^ 3 * (-Real.cos u) = Real.sin u ^ 3 * Real.cos u by ring]
  intro v hv; let x := Real.sin v; let y := Real.cos v
  have hxy : x ^ 2 + y ^ 2 = 1 := Real.sin_sq_add_cos_sq v
  have hc0s0 : c0 ^ 2 + s0 ^ 2 = 1 := Real.cos_sq_add_sin_sq φ'
  have hc0_lo : 18979 / 20000 ≤ c0 := by dsimp [c0] at *; linarith only [hγlo, hc0lo]
  have hc0_hi : c0 ≤ 9567 / 10000 := by dsimp [c0] at *; linarith only [hγhi, hc0hi]
  have hs0_lo : 29 / 100 ≤ s0 := by
    have : (29 / 100) ^ 2 ≤ s0 ^ 2 := by nlinarith only [hc0s0, hc0_lo, hc0_hi]
    nlinarith only [this, hs0_nn]
  have hs0_hi : s0 ≤ 31543 / 100000 := by
    have hc2 : (18979 / 20000) ^ 2 ≤ c0 ^ 2 := pow_le_pow_left₀ (by norm_num) hc0_lo 2
    have hs2 : s0 ^ 2 ≤ (31543 / 100000) ^ 2 := by linarith only [hc0s0, hc2]
    nlinarith only [hs2, hs0_nn]
  have hy1 : y ≤ 1 := by nlinarith only [hxy, sq_nonneg x, hv]
  have hx1 : -1 ≤ x ∧ x ≤ 1 :=
    ⟨by nlinarith only [hxy, sq_nonneg y], by nlinarith only [hxy, sq_nonneg y]⟩
  have hcos_add : Real.cos (φ' + v) = c0 * y - s0 * x := Real.cos_add φ' v
  by_cases hRegA : 3 / 4 ≤ y ∧ s0 * x ≤ 1 / 200
  · obtain ⟨hy34, hsx⟩ := hRegA
    have hpos_add : 0 ≤ c0 * y - s0 * x := by nlinarith only [hc0_lo, hy34, hsx]
    have hlip : |max (c0 * y - s0 * x) γ - max c0 γ| ≤ |(c0 * y - s0 * x) - c0| := by
      rcases le_total (c0 * y - s0 * x) γ with h1 | h1 <;> rcases le_total c0 γ with h2 | h2
      · rw [max_eq_right h1, max_eq_right h2, sub_self, abs_zero]; exact abs_nonneg _
      · rw [max_eq_right h1, max_eq_left h2, abs_le]
        exact ⟨by linarith only [h1, h2, neg_le_abs (c0 * y - s0 * x - c0)],
          by linarith only [h1, h2, abs_nonneg (c0 * y - s0 * x - c0)]⟩
      · rw [max_eq_left h1, max_eq_right h2, abs_le]
        exact ⟨by linarith only [h1, h2, abs_nonneg (c0 * y - s0 * x - c0)],
          by linarith only [h1, h2, le_abs_self (c0 * y - s0 * x - c0)]⟩
      · rw [max_eq_left h1, max_eq_left h2]
    have hsq_le : (max |Real.cos (φ' + v)| γ - max c0 γ) ^ 2 ≤ ((c0 * y - s0 * x) - c0) ^ 2 := by
      rw [hcos_add, abs_of_nonneg hpos_add, ← sq_abs, ← sq_abs ((c0 * y - s0 * x) - c0)]
      exact pow_le_pow_left₀ (abs_nonneg _) hlip 2
    suffices hA : ((c0 * y - s0 * x) - c0) ^ 2 * (1 + y) ^ 2 ≤
        (s0 ^ 2 * x ^ 2 + (247 / 1000) * x ^ 4 + s0 * c0 * (x ^ 3 * y)) * (1 + y) ^ 2 by
      exact hsq_le.trans (le_of_mul_le_mul_right hA (by positivity))
    have hid : ((c0 * y - s0 * x) - c0) ^ 2 * (1 + y) ^ 2 -
        (s0 ^ 2 * x ^ 2 + s0 * c0 * (x ^ 3 * y)) * (1 + y) ^ 2 =
        x ^ 4 * (c0 ^ 2 + c0 * s0 * x * (2 + y)) := by
      have hx2 : x ^ 2 = 1 - y ^ 2 := by linarith only [hxy]
      calc ((c0 * y - s0 * x) - c0) ^ 2 * (1 + y) ^ 2 -
            (s0 ^ 2 * x ^ 2 + s0 * c0 * (x ^ 3 * y)) * (1 + y) ^ 2
          = c0 ^ 2 * (1 - y ^ 2) ^ 2 +
              c0 * s0 * x * (2 * (1 - y ^ 2) * (1 + y) - x ^ 2 * y * (1 + y) ^ 2) := by ring
        _ = (1 - y ^ 2) ^ 2 * (c0 ^ 2 + c0 * s0 * x * (2 + y)) := by rw [hx2]; ring
        _ = x ^ 4 * (c0 ^ 2 + c0 * s0 * x * (2 + y)) := by rw [← hx2]; ring
    have hcoef : c0 ^ 2 + c0 * s0 * x * (2 + y) ≤ (247 / 1000) * (1 + y) ^ 2 := by
      rcases le_total 0 x with hx0 | hx0
      · have hx_ub : x ≤ 1 / 58 := by nlinarith only [hs0_lo, hsx, hx0]
        have hy_lb : 999 / 1000 ≤ y := by
          have hx2 : x ^ 2 ≤ (1 / 58) ^ 2 := pow_le_pow_left₀ hx0 hx_ub 2
          nlinarith only [hxy, hx2, hv]
        have hc2 : c0 ^ 2 ≤ (9567 / 10000) ^ 2 := pow_le_pow_left₀ (by linarith only [hc0_lo])
          hc0_hi 2
        have hterm2 : c0 * s0 * x * (2 + y) ≤ 1 * (1 / 200) * 3 := by
          have hcsx : 0 ≤ s0 * x := mul_nonneg (by linarith only [hs0_lo]) hx0
          have h1 : c0 * (s0 * x) ≤ 1 * (1 / 200) :=
            mul_le_mul (by linarith only [hc0_hi]) hsx hcsx zero_le_one
          have h2 := mul_le_mul h1 (by linarith only [hy1] : 2 + y ≤ 3)
            (by linarith only [hy34]) (by norm_num)
          linarith only [h2]
        have hrhs : (247 / 1000) * (1999 / 1000) ^ 2 ≤ (247 / 1000) * (1 + y) ^ 2 := by
          have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1999 / 1000)
            (by linarith only [hy_lb] : 1999 / 1000 ≤ 1 + y) 2
          linarith only [this]
        linarith only [hc2, hterm2, hrhs]
      · have hnx : 1 - y ^ 2 ≤ -x := by
          nlinarith only [hxy, mul_nonneg (sub_nonneg.mpr hx1.1) (neg_nonneg.mpr hx0)]
        have hcs : (9489 / 10000) * (29 / 100) ≤ c0 * s0 :=
          mul_le_mul (by linarith only [hc0_lo]) hs0_lo (by norm_num) (by linarith only [hc0_lo])
        have hc2 : c0 ^ 2 ≤ (9567 / 10000) ^ 2 :=
          pow_le_pow_left₀ (by linarith only [hc0_lo]) hc0_hi 2
        have hcsx : c0 * s0 * (-x) * (2 + y) ≥
            (9489 / 10000) * (29 / 100) * (1 - y ^ 2) * (2 + y) := by
          have h1 : (9489 / 10000) * (29 / 100) * (1 - y ^ 2) ≤ (c0 * s0) * (-x) :=
            mul_le_mul hcs hnx (by nlinarith only [hy1, hy34]) (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (by linarith only [hy34])
        have hpoly : (9567 / 10000) ^ 2 - (9489 / 10000) * (29 / 100) * (1 - y ^ 2) * (2 + y) ≤
            (247 / 1000) * (1 + y) ^ 2 := by
          let uA := y - 3 / 4; let vA := 1 - y
          have huA : 0 ≤ uA := by dsimp [uA]; linarith only [hy34]
          have hvA : 0 ≤ vA := by dsimp [vA]; linarith only [hy1]
          have hbA : (247 / 1000) * (1 + y) ^ 2 -
              ((9567 / 10000) ^ 2 - (9489 / 10000) * (29 / 100) * (1 - y ^ 2) * (2 + y)) =
              (275583601 / 25000000) * vA ^ 3 + (191664707 / 6250000) * uA * vA ^ 2 +
              (38394683 / 1562500) * uA ^ 2 * vA + (7272511 / 1562500) * uA ^ 3 := by
            dsimp [uA, vA]; ring
          have hnnA : 0 ≤ (247 / 1000) * (1 + y) ^ 2 -
              ((9567 / 10000) ^ 2 - (9489 / 10000) * (29 / 100) * (1 - y ^ 2) * (2 + y)) := by
            rw [hbA]; positivity
          linarith only [hnnA]
        linarith only [hc2, hcsx, hpoly]
    have hmul := mul_le_mul_of_nonneg_left hcoef (pow_nonneg (sq_nonneg x) 2)
    linarith only [hid, hmul]
  · have hB : 1 / 200 ≤ s0 * x ∨ y ≤ 3 / 4 := by
      rcases not_and_or.mp hRegA with hy | hsx
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    have habs_le : |c0 * y - s0 * x| ≤ γ := by
      rw [abs_le]; refine ⟨?_, ?_⟩
      · have hcy : 0 ≤ c0 * y := mul_nonneg (by linarith only [hc0_lo]) hv
        have hsx_ub : s0 * x ≤ 32 / 100 := by
          by_cases hx0 : 0 ≤ x
          · exact (mul_le_mul (by linarith only [hs0_hi] : s0 ≤ 32 / 100) hx1.2 hx0
              (by norm_num)).trans_eq (mul_one _)
          · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hs0_nn (le_of_not_ge hx0)) (by norm_num)
        linarith only [hcy, hsx_ub, hγlo]
      · rcases hB with hsx | hy34
        · have hcy : c0 * y ≤ c0 := mul_le_of_le_one_right (by linarith only [hc0_lo]) hy1
          dsimp [c0] at hcy ⊢; linarith only [hcy, hsx, hc0hi]
        · have ham : (4 / 3) * (-x) ≤ 13 / 9 - y ^ 2 := by
            nlinarith only [hxy, sq_nonneg (x + 2 / 3)]
          have hcy : c0 * y ≤ (9567 / 10000) * y :=
            mul_le_mul_of_nonneg_right hc0_hi hv
          have hsx : -s0 * x ≤ (31543 / 100000) * ((3 / 4) * (13 / 9 - y ^ 2)) := by
            by_cases hx0 : 0 ≤ -x
            · have h1 : s0 * (-x) ≤ (31543 / 100000) * (-x) :=
                mul_le_mul_of_nonneg_right hs0_hi hx0
              linarith only [h1, ham]
            · have h1 : -s0 * x ≤ 0 := by nlinarith only [hs0_nn, hx0]
              have h2 : 0 ≤ 13 / 9 - y ^ 2 := by nlinarith only [hy34, hv]
              linarith only [h1, h2]
          let uB := y; let vB := 3 / 4 - y
          have hvB : 0 ≤ vB := by dsimp [vB]; linarith only [hy34]
          have hbB : 949 / 1000 - ((9567 / 10000) * y +
              (31543 / 100000) * ((3 / 4) * (13 / 9 - y ^ 2))) =
              (728741 / 675000) * vB ^ 2 + (149113 / 168750) * uB * vB +
              (438359 / 10800000) * uB ^ 2 := by dsimp [uB, vB]; ring
          have hnnB : 0 ≤ 949 / 1000 - ((9567 / 10000) * y +
              (31543 / 100000) * ((3 / 4) * (13 / 9 - y ^ 2))) := by
            rw [hbB]; dsimp [uB]; positivity
          linarith only [hcy, hsx, hγlo, hnnB]
    rw [hcos_add, max_eq_right habs_le]
    have hlhs : (γ - max c0 γ) ^ 2 ≤ (3 / 2500) ^ 2 := by
      rcases le_total c0 γ with h | h
      · rw [max_eq_right h, sub_self]; norm_num
      · rw [max_eq_left h]
        have h1 : 0 ≤ c0 - γ := by linarith only [h]
        have h2 : c0 - γ ≤ 3 / 2500 := by dsimp [c0] at *; linarith only [hc0hi]
        nlinarith only [h1, h2]
    refine hlhs.trans ?_
    rcases hB with hsx | hy34
    · have hx0 : 0 ≤ x := by nlinarith only [hsx, hs0_lo]
      have hpos3 : 0 ≤ s0 * c0 * (x ^ 3 * y) :=
        mul_nonneg (mul_nonneg hs0_nn (by linarith only [hc0_lo])) (mul_nonneg (by positivity) hv)
      have hsx2 : (1 / 200) ^ 2 ≤ (s0 * x) ^ 2 := pow_le_pow_left₀ (by norm_num) hsx 2
      have hx4 : 0 ≤ (247 / 1000) * x ^ 4 := by positivity
      linarith only [hpos3, hsx2, hx4, show (s0 * x) ^ 2 = s0 ^ 2 * x ^ 2 by ring]
    · have hx2 : 7 / 16 ≤ x ^ 2 := by nlinarith only [hxy, hv, hy34]
      have hx4 : (7 / 16) * x ^ 2 ≤ x ^ 4 := by
        have := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
        linarith only [this, show x ^ 2 * x ^ 2 = x ^ 4 by ring]
      have hxy_lb : -(1 / 2) ≤ x * y := by nlinarith only [hxy, sq_nonneg (x + y)]
      have hcubic : -(1 / 2) * x ^ 2 ≤ x ^ 3 * y := by
        have := mul_le_mul_of_nonneg_left hxy_lb (sq_nonneg x)
        linarith only [this, show x ^ 2 * (-(1 / 2)) = -(1 / 2) * x ^ 2 by ring,
          show x ^ 2 * (x * y) = x ^ 3 * y by ring]
      have hsc : s0 * c0 ≤ (32 / 100) * (96 / 100) :=
        mul_le_mul (by linarith only [hs0_hi]) (by linarith only [hc0_hi])
          (by linarith only [hc0_lo]) (by norm_num)
      have hsc_nn : 0 ≤ s0 * c0 := mul_nonneg hs0_nn (by linarith only [hc0_lo])
      have h3term : -((32 / 100) * (96 / 100) * (1 / 2)) * x ^ 2 ≤ s0 * c0 * (x ^ 3 * y) := by
        have h1 := mul_le_mul_of_nonneg_left hcubic hsc_nn
        have h2 := mul_le_mul_of_nonneg_right hsc
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg x))
        linarith only [h1, h2,
          show s0 * c0 * (-(1 / 2) * x ^ 2) = -(s0 * c0 * ((1 / 2) * x ^ 2)) by ring,
          show (32 / 100) * (96 / 100) * ((1 / 2) * x ^ 2) =
            ((32 / 100) * (96 / 100) * (1 / 2)) * x ^ 2 by ring]
      have hs02 : (29 / 100) ^ 2 * x ^ 2 ≤ s0 ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hs0_lo 2) (sq_nonneg x)
      linarith only [hx2, hx4, h3term, hs02]

private theorem D_to_G_le {M : ℕ} (hMlo : 46368 ≤ M) {s0 c0 d u : ℝ} (hs0 : 29 / 100 ≤ s0)
    (hs0_hi : s0 ^ 2 ≤ 995 / 10000) (hc0 : 0 ≤ c0) (hd0 : 0 ≤ d) (hdu : d ≤ s0 * u)
    (hu_lo : 6 * (4794 / 10 ^ 8) ≤ u) (hu_hi : u ≤ 7 / 10) :
    let α := π / (2 * ((M + 1 : ℕ) : ℝ)); let t := d / s0
    0 < Real.sin u ^ 2 - Real.sin α ^ 2 ∧ 0 < Real.cos u ^ 2 ∧
      ((Real.sin u ^ 2 - Real.sin α ^ 2) ^ 2 / Real.cos u ^ 2) *
          (s0 ^ 2 * (1 / u ^ 2 - t ^ 2 / u ^ 4) + s0 * c0 * gPoleSum u) ≤
        s0 ^ 2 * Real.sin u ^ 2 + (247 / 1000) * Real.sin u ^ 4 +
          s0 * c0 * (Real.sin u ^ 3 * Real.cos u) - d ^ 2 := by
  intro α t; have hu0 : 0 < u := by linarith only [hu_lo]
  have hpi := Real.pi_lt_d20
  have hα_hi : α ≤ 5 / 10 ^ 5 := by
    dsimp [α]; rw [div_le_iff₀ (by positivity)]
    have hM1 : (46369 : ℝ) ≤ (M + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hMlo
    linarith only [hpi, hM1]
  have hs_lo : u * (1 - u ^ 2 / 6) ≤ Real.sin u := by
    linarith [Real.sin_gt_sub_cube hu0]
  have hs_hi : Real.sin u ≤ u := Real.sin_le hu0.le
  have hs_pos : 0 < Real.sin u := by
    have : (11 / 12) * u ≤ u * (1 - u ^ 2 / 6) := by nlinarith only [hu0, hu_hi]
    linarith only [this, hs_lo, hu0]
  have hα_sin : 0 ≤ Real.sin α ∧ Real.sin α ≤ α :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by dsimp [α]; positivity)
      (by linarith only [hα_hi, Real.pi_gt_d20]), Real.sin_le (by dsimp [α]; positivity)⟩
  have hdiff_pos : 0 < Real.sin u ^ 2 - Real.sin α ^ 2 := by
    have hu_sin_lo : 2 / 10 ^ 4 ≤ Real.sin u := by
      have : (11 / 12) * u ≤ u * (1 - u ^ 2 / 6) := by nlinarith only [hu0, hu_hi]
      linarith only [this, hs_lo, hu_lo]
    have h1 : (2 / 10 ^ 4) ^ 2 ≤ Real.sin u ^ 2 := pow_le_pow_left₀ (by norm_num) hu_sin_lo 2
    have h2 : Real.sin α ^ 2 ≤ (5 / 10 ^ 5) ^ 2 :=
      pow_le_pow_left₀ hα_sin.1 (hα_sin.2.trans hα_hi) 2
    linarith only [h1, h2]
  have hcos_lo : 1 - u ^ 2 / 2 ≤ Real.cos u := by
    have h1 := Real.sin_le (by linarith only [hu0] : 0 ≤ u / 2)
    have hc2 := Real.cos_two_mul (u / 2); rw [show 2 * (u / 2) = u by ring] at hc2
    have hs20 : 0 ≤ Real.sin (u / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith only [hu0])
        (by linarith only [hu_hi, Real.pi_gt_d20])
    have hs2 : Real.sin (u / 2) ^ 2 ≤ (u / 2) ^ 2 := pow_le_pow_left₀ hs20 h1 2
    linarith only [hc2, hs2, Real.sin_sq_add_cos_sq (u / 2)]
  have hcos_pos : 0 < Real.cos u := by nlinarith only [hcos_lo, hu0, hu_hi]
  refine ⟨hdiff_pos, sq_pos_of_pos hcos_pos, ?_⟩
  have hsq_le : (Real.sin u ^ 2 - Real.sin α ^ 2) ^ 2 ≤ Real.sin u ^ 4 := by
    have hnn : 0 ≤ Real.sin α ^ 2 := sq_nonneg _
    nlinarith only [hdiff_pos, hnn]
  have ht_le : 0 ≤ t ∧ t ≤ u := ⟨by dsimp [t]; positivity, by
    dsimp [t]; rw [div_le_iff₀ (by linarith only [hs0])]; linarith only [hdu]⟩
  have hGe_nn : 0 ≤ 1 / u ^ 2 - t ^ 2 / u ^ 4 := by
    rw [show 1 / u ^ 2 - t ^ 2 / u ^ 4 = (u ^ 2 - t ^ 2) / u ^ 4 by field_simp]
    exact div_nonneg (by nlinarith only [ht_le.1, ht_le.2]) (by positivity)
  have hGp_nn : 0 ≤ gPoleSum u := by unfold gPoleSum; positivity
  have h59 : (247 / 100) * s0 ^ 2 ≤ 247 / 1000 := by linarith only [hs0_hi]
  have heven : Real.sin u ^ 4 * (1 / u ^ 2 - t ^ 2 / u ^ 4) ≤
      (Real.sin u ^ 2 - t ^ 2 + (247 / 100) * Real.sin u ^ 4) * Real.cos u ^ 2 := by
    rw [show Real.cos u ^ 2 = 1 - Real.sin u ^ 2 by linarith [Real.sin_sq_add_cos_sq u]]
    suffices hmul : Real.sin u ^ 4 * (u ^ 2 - t ^ 2) ≤
        (Real.sin u ^ 2 - t ^ 2 + (247 / 100) * Real.sin u ^ 4) * (1 - Real.sin u ^ 2) * u ^ 4 by
      have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ u ^ 4)
      rw [mul_div_cancel_right₀ _ (ne_of_gt (pow_pos hu0 4))] at hdiv
      refine le_trans (le_of_eq ?_) hdiv; field_simp
    let S := t ^ 2; have hS0 : 0 ≤ S := sq_nonneg t
    have hSu : S ≤ u ^ 2 := pow_le_pow_left₀ ht_le.1 ht_le.2 2
    have h0 : 0 ≤ (Real.sin u ^ 2 + (247 / 100) * Real.sin u ^ 4) *
        (1 - Real.sin u ^ 2) * u ^ 4 - Real.sin u ^ 4 * u ^ 2 := by
      have hs2_le : Real.sin u ^ 2 ≤ 49 / 100 :=
        (pow_le_pow_left₀ hs_pos.le (hs_hi.trans hu_hi) 2).trans_eq (by norm_num)
      have hfac : 1 ≤ (1 + (247 / 100) * Real.sin u ^ 2) * (1 - Real.sin u ^ 2) := by
        nlinarith only [hs2_le, sq_nonneg (Real.sin u)]
      have hu2s2 : Real.sin u ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hs_pos.le hs_hi 2
      have h1 := mul_le_mul hfac hu2s2 (sq_nonneg _) (by linarith only [hfac])
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg (Real.sin u)) (sq_nonneg u))
      linarith only [h2, show Real.sin u ^ 2 * u ^ 2 * (1 * Real.sin u ^ 2) =
        Real.sin u ^ 4 * u ^ 2 by ring,
        show Real.sin u ^ 2 * u ^ 2 *
          ((1 + (247 / 100) * Real.sin u ^ 2) * (1 - Real.sin u ^ 2) * u ^ 2) =
          (Real.sin u ^ 2 + (247 / 100) * Real.sin u ^ 4) * (1 - Real.sin u ^ 2) * u ^ 4 by ring]
    have h1 : 0 ≤ (Real.sin u ^ 2 - u ^ 2 + (247 / 100) * Real.sin u ^ 4) *
        (1 - Real.sin u ^ 2) * u ^ 4 := by
      have hcub : 1 ≤ (247 / 100) * 3 * (1 - u ^ 2 / 6) ^ 4 := by
        have h11 : 11 / 12 ≤ 1 - u ^ 2 / 6 := by nlinarith only [hu0, hu_hi]
        have hp4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11 / 12) h11 4
        linarith only [hp4]
      have hcore : 0 ≤ Real.sin u ^ 2 - u ^ 2 + (247 / 100) * Real.sin u ^ 4 := by
        have hs2 : u ^ 2 * (1 - u ^ 2 / 6) ^ 2 ≤ Real.sin u ^ 2 := by
          calc u ^ 2 * (1 - u ^ 2 / 6) ^ 2 = (u * (1 - u ^ 2 / 6)) ^ 2 := by ring
            _ ≤ Real.sin u ^ 2 := pow_le_pow_left₀ (by nlinarith only [hu0, hu_hi]) hs_lo 2
        have hs4 : u ^ 4 * (1 - u ^ 2 / 6) ^ 4 ≤ Real.sin u ^ 4 := by
          calc u ^ 4 * (1 - u ^ 2 / 6) ^ 4 = (u ^ 2 * (1 - u ^ 2 / 6) ^ 2) ^ 2 := by ring
            _ ≤ (Real.sin u ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hs2 2
            _ = Real.sin u ^ 4 := by ring
        have hmul_c := mul_le_mul_of_nonneg_right hcub (pow_nonneg hu0.le 4)
        have hsub : -(u ^ 4 / 3) ≤ u ^ 2 * (1 - u ^ 2 / 6) ^ 2 - u ^ 2 := by
          nlinarith only [sq_nonneg (u ^ 2)]
        linarith only [hs2, hs4, hmul_c, hsub]
      have h1m : 0 ≤ 1 - Real.sin u ^ 2 := by
        linarith only [Real.sin_sq_add_cos_sq u, sq_nonneg (Real.cos u)]
      exact mul_nonneg (mul_nonneg hcore h1m) (by positivity)
    have hid : (Real.sin u ^ 2 - S + (247 / 100) * Real.sin u ^ 4) * (1 - Real.sin u ^ 2) * u ^ 4 -
        Real.sin u ^ 4 * (u ^ 2 - S) =
        ((u ^ 2 - S) * ((Real.sin u ^ 2 + (247 / 100) * Real.sin u ^ 4) *
            (1 - Real.sin u ^ 2) * u ^ 4 - Real.sin u ^ 4 * u ^ 2) +
          S * ((Real.sin u ^ 2 - u ^ 2 + (247 / 100) * Real.sin u ^ 4) *
            (1 - Real.sin u ^ 2) * u ^ 4)) / u ^ 2 := by field_simp; ring
    have hnn : 0 ≤ (Real.sin u ^ 2 - S + (247 / 100) * Real.sin u ^ 4) *
        (1 - Real.sin u ^ 2) * u ^ 4 - Real.sin u ^ 4 * (u ^ 2 - S) := by
      rw [hid]
      exact div_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hSu) h0) (mul_nonneg hS0 h1))
        (sq_nonneg u)
    linarith only [hnn]
  have hodd : Real.sin u ^ 4 * gPoleSum u ≤ Real.sin u ^ 3 * Real.cos u ^ 3 := by
    have hpu := pu_odd_pole_le hu0 hu_hi
    have hcos3 : (1 - u ^ 2 / 2) ^ 3 ≤ Real.cos u ^ 3 :=
      pow_le_pow_left₀ (by nlinarith only [hu0, hu_hi]) hcos_lo 3
    have hdiv : (1 - u ^ 2 / 2) ^ 3 / u ≤ Real.cos u ^ 3 / Real.sin u := by
      calc (1 - u ^ 2 / 2) ^ 3 / u ≤ Real.cos u ^ 3 / u := div_le_div_of_nonneg_right hcos3 hu0.le
        _ ≤ Real.cos u ^ 3 / Real.sin u :=
            div_le_div_of_nonneg_left (by positivity) hs_pos hs_hi
    have := mul_le_mul_of_nonneg_left (hpu.trans hdiv) (pow_nonneg hs_pos.le 4)
    refine this.trans_eq ?_; field_simp
  have hd_eq : d ^ 2 = s0 ^ 2 * t ^ 2 := by
    dsimp [t]; have : s0 ≠ 0 := ne_of_gt (by linarith only [hs0]); field_simp
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hcos_pos)]
  have hs0_nn : 0 ≤ s0 := by linarith only [hs0]
  calc (Real.sin u ^ 2 - Real.sin α ^ 2) ^ 2 *
        (s0 ^ 2 * (1 / u ^ 2 - t ^ 2 / u ^ 4) + s0 * c0 * gPoleSum u)
      ≤ Real.sin u ^ 4 * (s0 ^ 2 * (1 / u ^ 2 - t ^ 2 / u ^ 4) + s0 * c0 * gPoleSum u) :=
        mul_le_mul_of_nonneg_right hsq_le (by positivity)
    _ = s0 ^ 2 * (Real.sin u ^ 4 * (1 / u ^ 2 - t ^ 2 / u ^ 4)) +
        s0 * c0 * (Real.sin u ^ 4 * gPoleSum u) := by ring
    _ ≤ s0 ^ 2 * ((Real.sin u ^ 2 - t ^ 2 + (247 / 100) * Real.sin u ^ 4) * Real.cos u ^ 2) +
        s0 * c0 * (Real.sin u ^ 3 * Real.cos u ^ 3) := by gcongr
    _ ≤ (s0 ^ 2 * Real.sin u ^ 2 + (247 / 1000) * Real.sin u ^ 4 +
        s0 * c0 * (Real.sin u ^ 3 * Real.cos u) - d ^ 2) * Real.cos u ^ 2 := by
        rw [hd_eq]
        have hmul59 := mul_le_mul_of_nonneg_right h59
          (mul_nonneg (pow_nonneg (sq_nonneg (Real.sin u)) 2) (sq_nonneg (Real.cos u)))
        linarith only [hmul59]

private theorem even_k2_m2_poly_nonneg {y d : ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) :
    (6 * (y + 12 * d) * d - (109 / 5) * d ^ 2) * (y + 16 * d) ^ 4 ≤
      (6 * (y + 12 * d) * d + 9 * d ^ 2) * (y + 15 * d) ^ 4 := by
  have hid : (6 * (y + 12 * d) * d + 9 * d ^ 2) * (y + 15 * d) ^ 4 -
      (6 * (y + 12 * d) * d - (109 / 5) * d ^ 2) * (y + 16 * d) ^ 4 =
      (4053589 / 5) * d ^ 6 + (907786 / 5) * y * d ^ 5 + (74694 / 5) * y ^ 2 * d ^ 4 +
        (2656 / 5) * y ^ 3 * d ^ 3 + (34 / 5) * y ^ 4 * d ^ 2 := by ring
  linarith [show 0 ≤ (6 * (y + 12 * d) * d + 9 * d ^ 2) * (y + 15 * d) ^ 4 -
    (6 * (y + 12 * d) * d - (109 / 5) * d ^ 2) * (y + 16 * d) ^ 4 by rw [hid]; positivity]

private theorem even_stencil_tail_le {uk du t w0 : ℝ} (hdu0 : 0 < du)
    (hw0_lo : 185 / 1000 ≤ w0) (hw0_hi : w0 ≤ 219 / 1000) (huk : 9 * du ≤ uk) :
    let w1 := 1 / 2 - w0
    let He : ℝ → ℝ := fun m ↦ (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4
    w0 * He (uk + (3 / 2 - 0) * du) + w1 * He (uk + (3 / 2 - 1) * du) +
      w1 * He (uk + (3 / 2 - 2) * du) + w0 * He (uk + (3 / 2 - 3) * du) ≤
      1 / uk ^ 2 - t ^ 2 / uk ^ 4 := by
  intro w1 He
  let d := du / 2
  have hd_pos : 0 < d := by dsimp [d]; linarith
  have huk_lo : 18 * d ≤ uk := by dsimp [d]; linarith
  have huk_pos : 0 < uk := by linarith only [huk_lo, hd_pos]
  have hrew0 : uk + (3 / 2 - 0) * du = uk + 3 * d := by dsimp [d]; ring
  have hrew1 : uk + (3 / 2 - 1) * du = uk + d := by dsimp [d]; ring
  have hrew2 : uk + (3 / 2 - 2) * du = uk - d := by dsimp [d]; ring
  have hrew3 : uk + (3 / 2 - 3) * du = uk - 3 * d := by dsimp [d]; ring
  rw [hrew0, hrew1, hrew2, hrew3]; dsimp [He]
  have hjen {a : ℝ} (ha : 0 ≤ a) (huk_a : a < uk) :
      2 / uk ^ 4 ≤ 1 / (uk - a) ^ 4 + 1 / (uk + a) ^ 4 := by
    have hp1 : 0 < uk - a := by linarith
    have hp2 : 0 < uk + a := by linarith
    have hsub : (1 / (uk - a) ^ 4 + 1 / (uk + a) ^ 4) - 2 / uk ^ 4 =
        2 * a ^ 2 * (5 * uk ^ 4 * (uk ^ 2 - a ^ 2) + 5 * uk ^ 6 +
          a ^ 4 * (4 * uk ^ 2 - a ^ 2)) / (uk ^ 4 * (uk - a) ^ 4 * (uk + a) ^ 4) := by
      field_simp; ring
    have ha2 : a ^ 2 ≤ uk ^ 2 := pow_le_pow_left₀ ha huk_a.le 2
    have h1 : 0 ≤ uk ^ 2 - a ^ 2 := by linarith only [ha2]
    have h2 : 0 ≤ 4 * uk ^ 2 - a ^ 2 := by linarith only [ha2, sq_nonneg uk]
    have : 0 ≤ (1 / (uk - a) ^ 4 + 1 / (uk + a) ^ 4) - 2 / uk ^ 4 := by rw [hsub]; positivity
    linarith
  have hj3 := hjen (a := 3 * d) (by positivity) (by linarith only [huk_lo, hd_pos])
  have hj1 := hjen (a := d) (by positivity) (by linarith only [huk_lo, hd_pos])
  have hsplit {m : ℝ} (hm : 0 < m) : (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4 =
      1 / m ^ 2 - (t ^ 2 + (77 / 10) * du ^ 2) * (1 / m ^ 4) := by field_simp; ring
  rw [hsplit (by linarith), hsplit (by linarith), hsplit (by linarith), hsplit (by linarith)]
  have hC0 : 0 ≤ t ^ 2 + (77 / 10) * du ^ 2 := by positivity
  have hw1_pos : 0 ≤ w1 := by dsimp [w1]; linarith only [hw0_hi]
  have hpair4 : (t ^ 2 + (77 / 10) * du ^ 2) / uk ^ 4 ≤
      w0 * ((t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk + 3 * d) ^ 4 + 1 / (uk - 3 * d) ^ 4)) +
        w1 * ((t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk + d) ^ 4 + 1 / (uk - d) ^ 4)) := by
    have hw_sum : 2 * w0 + 2 * w1 = 1 := by dsimp [w1]; ring
    have ha := mul_le_mul_of_nonneg_left hj3 (mul_nonneg (by linarith only [hw0_lo]) hC0)
    have hb := mul_le_mul_of_nonneg_left hj1 (mul_nonneg hw1_pos hC0)
    have hsum := add_le_add ha hb
    refine (le_of_eq ?_).trans (hsum.trans_eq (by ring))
    linear_combination -((t ^ 2 + (77 / 10) * du ^ 2) / uk ^ 4) * hw_sum
  suffices hp2 : w0 * (1 / (uk + 3 * d) ^ 2 + 1 / (uk - 3 * d) ^ 2) +
      w1 * (1 / (uk + d) ^ 2 + 1 / (uk - d) ^ 2) ≤
      1 / uk ^ 2 + (77 / 10) * du ^ 2 / uk ^ 4 by
    have hlin := sub_le_sub hp2 hpair4
    linarith only [hlin, show w0 * (1 / (uk + 3 * d) ^ 2 + 1 / (uk - 3 * d) ^ 2) +
        w1 * (1 / (uk + d) ^ 2 + 1 / (uk - d) ^ 2) -
        (w0 * ((t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk + 3 * d) ^ 4 + 1 / (uk - 3 * d) ^ 4)) +
          w1 * ((t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk + d) ^ 4 + 1 / (uk - d) ^ 4))) =
        w0 * (1 / (uk + 3 * d) ^ 2 - (t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk + 3 * d) ^ 4)) +
        w1 * (1 / (uk + d) ^ 2 - (t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk + d) ^ 4)) +
        w1 * (1 / (uk - d) ^ 2 - (t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk - d) ^ 4)) +
        w0 * (1 / (uk - 3 * d) ^ 2 - (t ^ 2 + (77 / 10) * du ^ 2) * (1 / (uk - 3 * d) ^ 4)) by
      ring,
      show 1 / uk ^ 2 + (77 / 10) * du ^ 2 / uk ^ 4 -
        (t ^ 2 + (77 / 10) * du ^ 2) / uk ^ 4 = 1 / uk ^ 2 - t ^ 2 / uk ^ 4 by ring]
  have hp3_id : 1 / (uk + 3 * d) ^ 2 + 1 / (uk - 3 * d) ^ 2 =
      (2 * uk ^ 2 + 18 * d ^ 2) / (uk ^ 2 - 9 * d ^ 2) ^ 2 := by
    have h1 : uk + 3 * d ≠ 0 := ne_of_gt (by linarith only [huk_lo, hd_pos])
    have h2 : uk - 3 * d ≠ 0 := ne_of_gt (by linarith only [huk_lo, hd_pos])
    have h3 : uk ^ 2 - 9 * d ^ 2 = (uk - 3 * d) * (uk + 3 * d) := by ring
    rw [h3]; field_simp; ring
  have hp1_id : 1 / (uk + d) ^ 2 + 1 / (uk - d) ^ 2 =
      (2 * uk ^ 2 + 2 * d ^ 2) / (uk ^ 2 - d ^ 2) ^ 2 := by
    have h1 : uk + d ≠ 0 := ne_of_gt (by linarith only [huk_lo, hd_pos])
    have h2 : uk - d ≠ 0 := ne_of_gt (by linarith only [huk_lo, hd_pos])
    have h3 : uk ^ 2 - d ^ 2 = (uk - d) * (uk + d) := by ring
    rw [h3]; field_simp; ring
  rw [hp3_id, hp1_id]
  have hd2_pos : 0 < d ^ 2 := sq_pos_of_pos hd_pos
  have huk2_324 : 324 * d ^ 2 ≤ uk ^ 2 := by
    calc 324 * d ^ 2 = (18 * d) ^ 2 := by ring
      _ ≤ uk ^ 2 := pow_le_pow_left₀ (by positivity) huk_lo 2
  have hb3 : (2 * uk ^ 2 + 18 * d ^ 2) / (uk ^ 2 - 9 * d ^ 2) ^ 2 ≤
      2 / uk ^ 2 + 60 * d ^ 2 / uk ^ 4 := by
    rw [show 2 / uk ^ 2 + 60 * d ^ 2 / uk ^ 4 = (2 * uk ^ 2 + 60 * d ^ 2) / uk ^ 4 by
      field_simp, div_le_div_iff₀ (sq_pos_of_pos (by linarith only [huk2_324, hd2_pos]))
      (by positivity)]
    let y := uk ^ 2 - 324 * d ^ 2; have hy : 0 ≤ y := by dsimp [y]; linarith only [huk2_324]
    have hid : (2 * uk ^ 2 + 60 * d ^ 2) * (uk ^ 2 - 9 * d ^ 2) ^ 2 -
        (2 * uk ^ 2 + 18 * d ^ 2) * uk ^ 4 =
        6 * d ^ 2 * y ^ 2 + 2970 * d ^ 4 * y + 337284 * d ^ 6 := by dsimp [y]; ring
    have : 0 ≤ (2 * uk ^ 2 + 60 * d ^ 2) * (uk ^ 2 - 9 * d ^ 2) ^ 2 -
        (2 * uk ^ 2 + 18 * d ^ 2) * uk ^ 4 := by rw [hid]; positivity
    linarith
  have hb1 : (2 * uk ^ 2 + 2 * d ^ 2) / (uk ^ 2 - d ^ 2) ^ 2 ≤
      2 / uk ^ 2 + 7 * d ^ 2 / uk ^ 4 := by
    rw [show 2 / uk ^ 2 + 7 * d ^ 2 / uk ^ 4 = (2 * uk ^ 2 + 7 * d ^ 2) / uk ^ 4 by
      field_simp, div_le_div_iff₀ (sq_pos_of_pos (by linarith only [huk2_324, hd2_pos]))
      (by positivity)]
    let y := uk ^ 2 - 324 * d ^ 2; have hy : 0 ≤ y := by dsimp [y]; linarith only [huk2_324]
    have hid : (2 * uk ^ 2 + 7 * d ^ 2) * (uk ^ 2 - d ^ 2) ^ 2 -
        (2 * uk ^ 2 + 2 * d ^ 2) * uk ^ 4 =
        d ^ 2 * y ^ 2 + 636 * d ^ 4 * y + 101095 * d ^ 6 := by dsimp [y]; ring
    have : 0 ≤ (2 * uk ^ 2 + 7 * d ^ 2) * (uk ^ 2 - d ^ 2) ^ 2 -
        (2 * uk ^ 2 + 2 * d ^ 2) * uk ^ 4 := by rw [hid]; positivity
    linarith
  have hdu_d : du ^ 2 = 4 * d ^ 2 := by dsimp [d]; ring
  rw [hdu_d]; dsimp [w1] at hw1_pos ⊢
  have hcoef : w0 * 60 + (1 / 2 - w0) * 7 ≤ (77 / 10) * 4 := by linarith only [hw0_hi]
  have hd4 : 0 ≤ d ^ 2 / uk ^ 4 := by positivity
  have hw3 := mul_le_mul_of_nonneg_left hb3 (by linarith only [hw0_lo] : 0 ≤ w0)
  have hw1 := mul_le_mul_of_nonneg_left hb1 hw1_pos
  have hc4 := mul_le_mul_of_nonneg_right hcoef hd4
  linarith only [hw3, hw1, hc4, show w0 * (2 / uk ^ 2 + 60 * d ^ 2 / uk ^ 4) +
      (1 / 2 - w0) * (2 / uk ^ 2 + 7 * d ^ 2 / uk ^ 4) =
      1 / uk ^ 2 + (w0 * 60 + (1 / 2 - w0) * 7) * (d ^ 2 / uk ^ 4) by ring,
    show (77 / 10) * 4 * (d ^ 2 / uk ^ 4) = (77 / 10) * (4 * d ^ 2) / uk ^ 4 by ring]

private theorem even_dfe_le_he {u0 du t x : ℝ} (hdu0 : 0 < du) (hdu_hi : du ≤ 4794 / 10 ^ 8)
    (ht0 : 0 ≤ t) (htu0' : t ≤ u0) (hu0 : 6 * du ≤ u0) (hx : u0 + du ≤ x) :
    let C3 := t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2
    let dFe := ((1 / x - C3 / (3 * x ^ 3)) - (1 / (x + du) - C3 / (3 * (x + du) ^ 3))) / du
    let He : ℝ → ℝ := fun m ↦ (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4
    dFe ≤ He (x + du / 2) ∧ 0 ≤ (x + du / 2) ^ 2 - t ^ 2 - (77 / 10) * du ^ 2 := by
  intro C3 dFe He
  have hu0_pos : 0 < u0 := by linarith
  let m := x + du / 2; let d := du / 2
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hm : 15 * d ≤ m := by dsimp [m, d]; linarith
  have hmd_pos : 0 < m ^ 2 - d ^ 2 := by nlinarith only [hm, hd0]
  have hm_pos : 0 < m := by linarith only [hm, hd0]
  have hd1 : (1 / x - 1 / (x + du)) / du ≤ 1 / m ^ 2 + (3 / 10) * du ^ 2 / m ^ 4 := by
    have heq : (1 / x - 1 / (x + du)) / du - 1 / m ^ 2 = d ^ 2 / (m ^ 2 * (m ^ 2 - d ^ 2)) := by
      have hx1 : x = m - d := by dsimp [m, d]; ring
      have hx2 : x + du = m + d := by dsimp [m, d]; ring
      have hdu2 : du = 2 * d := by dsimp [d]; ring
      have hp1 : m - d ≠ 0 := ne_of_gt (by linarith only [hm, hd0])
      have hp2 : m + d ≠ 0 := ne_of_gt (by linarith only [hm, hd0])
      rw [hx2, hx1, hdu2]; field_simp; ring
    rw [← sub_le_iff_le_add', heq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hdu2 : du = 2 * d := by dsimp [d]; ring
    rw [hdu2]
    have hm2 : 225 * d ^ 2 ≤ m ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hm 2; linarith only [this]
    have h1 : d ^ 2 * m ^ 2 ≤ (6 / 5) * d ^ 2 * (m ^ 2 - d ^ 2) := by
      nlinarith only [hm2, sq_nonneg d]
    calc d ^ 2 * m ^ 4 = (d ^ 2 * m ^ 2) * m ^ 2 := by ring
      _ ≤ ((6 / 5) * d ^ 2 * (m ^ 2 - d ^ 2)) * m ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg m)
      _ = (3 / 10) * (2 * d) ^ 2 * (m ^ 2 * (m ^ 2 - d ^ 2)) := by ring
  have hd2 : (t ^ 2 + 8 * du ^ 2) / m ^ 4 ≤
      C3 * (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) / du := by
    have hC3 : t ^ 2 + 8 * du ^ 2 ≤ C3 := by dsimp [C3]; nlinarith only [hdu0, hdu_hi]
    have h3 : 1 / m ^ 4 ≤ (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) / du := by
      have hx1 : x = m - d := by dsimp [m, d]; ring
      have hx2 : x + du = m + d := by dsimp [m, d]; ring
      have hpos1 : 0 < m - d := by linarith only [hm, hd0]
      have hpos2 : 0 < m + d := by linarith only [hm, hd0]
      rw [hx2, hx1, le_div_iff₀ hdu0]
      have hsub : (1 / (3 * (m - d) ^ 3) - 1 / (3 * (m + d) ^ 3)) - du / m ^ 4 =
          du * d ^ 2 * (10 * m ^ 4 - 9 * m ^ 2 * d ^ 2 + 3 * d ^ 4) /
            (3 * m ^ 4 * (m - d) ^ 3 * (m + d) ^ 3) := by
        have hdu2 : du = 2 * d := by dsimp [d]; ring
        rw [hdu2]; field_simp; ring
      have hnum : 0 ≤ 10 * m ^ 4 - 9 * m ^ 2 * d ^ 2 + 3 * d ^ 4 := by
        have hid : 10 * m ^ 4 - 9 * m ^ 2 * d ^ 2 + 3 * d ^ 4 =
            (3 * m ^ 2 - (3 / 2) * d ^ 2) ^ 2 + m ^ 4 + (3 / 4) * d ^ 4 := by ring
        rw [hid]; positivity
      have hpos_sub : 0 ≤ (1 / (3 * (m - d) ^ 3) - 1 / (3 * (m + d) ^ 3)) - du / m ^ 4 := by
        rw [hsub]; positivity
      linarith only [hpos_sub, show (1 / m ^ 4) * du = du / m ^ 4 by ring]
    calc (t ^ 2 + 8 * du ^ 2) / m ^ 4 = (t ^ 2 + 8 * du ^ 2) * (1 / m ^ 4) := by ring
      _ ≤ C3 * ((1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) / du) :=
          mul_le_mul hC3 h3 (by positivity) (by dsimp [C3]; positivity)
      _ = _ := by ring
  have hdFe_eq : dFe = (1 / x - 1 / (x + du)) / du -
      C3 * (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) / du := by dsimp [dFe]; ring
  have hHe_eq : He m = 1 / m ^ 2 + (3 / 10) * du ^ 2 / m ^ 4 -
      (t ^ 2 + 8 * du ^ 2) / m ^ 4 := by dsimp [He]; field_simp; ring
  have hm_gt : 0 ≤ (x + du / 2) ^ 2 - t ^ 2 - (77 / 10) * du ^ 2 := by
    have hu0_du : 3 * (6 * du) * du ≤ 3 * u0 * du := by nlinarith only [hu0, hdu0]
    have hx_u0 : u0 + (3 / 2) * du ≤ x + du / 2 := by linarith only [hx]
    have htu2 : t ^ 2 ≤ u0 ^ 2 := pow_le_pow_left₀ ht0 htu0' 2
    have hxu2 : (u0 + (3 / 2) * du) ^ 2 ≤ (x + du / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hx_u0 2
    nlinarith only [htu2, hxu2, hu0_du, sq_nonneg du]
  exact ⟨by dsimp [m] at hHe_eq hd1 hd2; linarith only [hdFe_eq, hHe_eq, hd1, hd2], hm_gt⟩

private theorem even_stencil_he_one_le {u0 du t w0 : ℝ} (hdu0 : 0 < du) (ht0 : 0 ≤ t)
    (htu0' : t ≤ u0) (hu0_pos : 0 < u0) (hw0_lo : 185 / 1000 ≤ w0) (hw0_hi : w0 ≤ 219 / 1000) :
    let w1 := 1 / 2 - w0
    let He : ℝ → ℝ := fun m ↦ (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4
    w0 * He (u0 + 1 * du + (3 / 2 - 0) * du) + w1 * He (u0 + 1 * du + (3 / 2 - 1) * du) ≤
      1 / (u0 + 1 * du) ^ 2 - t ^ 2 / (u0 + 1 * du) ^ 4 := by
  intro w1 He
  let d := du / 2; let m0 := u0 + 5 * d; let m1 := u0 + 3 * d
  have hd_pos : 0 < d := by dsimp [d]; linarith
  have hrew0 : u0 + 1 * du + (3 / 2 - 0) * du = m0 := by dsimp [m0, d]; ring
  have hrew1 : u0 + 1 * du + (3 / 2 - 1) * du = m1 := by dsimp [m1, d]; ring
  have huk1 : u0 + 1 * du = u0 + 2 * d := by dsimp [d]; ring
  rw [hrew0, hrew1, huk1]; dsimp [He]
  let f (S : ℝ) : ℝ := w0 * ((m0 ^ 2 - S - (77 / 10) * du ^ 2) / m0 ^ 4) +
    w1 * ((m1 ^ 2 - S - (77 / 10) * du ^ 2) / m1 ^ 4) -
    (1 / (u0 + 2 * d) ^ 2 - S / (u0 + 2 * d) ^ 4)
  have hf_aff : f (t ^ 2) = (1 - t ^ 2 / u0 ^ 2) * f 0 + (t ^ 2 / u0 ^ 2) * f (u0 ^ 2) := by
    dsimp [f]; have : u0 ≠ 0 := ne_of_gt hu0_pos; field_simp; ring
  have hf0 : f 0 ≤ 0 := by
    dsimp [f, w1]; simp only [sub_zero, zero_div]
    have h0 : (m0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤ 1 / (u0 + 2 * d) ^ 2 := by
      have : (m0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤ 1 / m0 ^ 2 := by
        rw [div_le_div_iff₀ (by dsimp [m0]; positivity) (by dsimp [m0]; positivity)]
        nlinarith only [sq_nonneg m0, sq_nonneg du]
      exact this.trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) (by dsimp [m0]; linarith) 2))
    have h1 : (m1 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤ 1 / (u0 + 2 * d) ^ 2 := by
      have : (m1 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤ 1 / m1 ^ 2 := by
        rw [div_le_div_iff₀ (by dsimp [m1]; positivity) (by dsimp [m1]; positivity)]
        nlinarith only [sq_nonneg m1, sq_nonneg du]
      exact this.trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) (by dsimp [m1]; linarith) 2))
    have hw0' := mul_le_mul_of_nonneg_left h0 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hw1' := mul_le_mul_of_nonneg_left h1 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hpos_inv : 0 ≤ 1 / (u0 + 2 * d) ^ 2 := by positivity
    linarith only [hw0', hw1', hpos_inv,
      show w0 * (1 / (u0 + 2 * d) ^ 2) + (1 / 2 - w0) * (1 / (u0 + 2 * d) ^ 2) =
        (1 / 2) * (1 / (u0 + 2 * d) ^ 2) by ring]
  have hfu : f (u0 ^ 2) ≤ 0 := by
    dsimp [f, w1]
    have h0 : (m0 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤
        (10 * u0 * d) / (u0 + 2 * d) ^ 4 := by
      have hnum : m0 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2 ≤ 10 * u0 * d := by
        dsimp [m0, d]; nlinarith only [sq_nonneg du]
      have hpos : 0 ≤ 10 * u0 * d := by positivity
      calc (m0 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤ (10 * u0 * d) / m0 ^ 4 :=
            div_le_div_of_nonneg_right hnum (by dsimp [m0]; positivity)
        _ ≤ (10 * u0 * d) / (u0 + 2 * d) ^ 4 := div_le_div_of_nonneg_left hpos
            (by positivity) (pow_le_pow_left₀ (by positivity) (by dsimp [m0]; linarith) 4)
    have h1 : (m1 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤
        (6 * u0 * d) / (u0 + 2 * d) ^ 4 := by
      have hnum : m1 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2 ≤ 6 * u0 * d := by
        dsimp [m1, d]; nlinarith only [sq_nonneg du]
      have hpos : 0 ≤ 6 * u0 * d := by positivity
      calc (m1 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤ (6 * u0 * d) / m1 ^ 4 :=
            div_le_div_of_nonneg_right hnum (by dsimp [m1]; positivity)
        _ ≤ (6 * u0 * d) / (u0 + 2 * d) ^ 4 := div_le_div_of_nonneg_left hpos
            (by positivity) (pow_le_pow_left₀ (by positivity) (by dsimp [m1]; linarith) 4)
    have hge : 1 / (u0 + 2 * d) ^ 2 - u0 ^ 2 / (u0 + 2 * d) ^ 4 =
        (4 * u0 * d + 4 * d ^ 2) / (u0 + 2 * d) ^ 4 := by
      have : u0 + 2 * d ≠ 0 := ne_of_gt (by positivity); field_simp; ring
    rw [hge]; have hden : 0 < (u0 + 2 * d) ^ 4 := by positivity
    have hcomb : w0 * (10 * u0 * d) + (1 / 2 - w0) * (6 * u0 * d) ≤ 4 * u0 * d + 4 * d ^ 2 := by
      have hud : 0 ≤ u0 * d := by positivity
      nlinarith only [hw0_hi, hud, sq_nonneg d]
    have hw0' := mul_le_mul_of_nonneg_left h0 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hw1' := mul_le_mul_of_nonneg_left h1 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    linarith only [hw0', hw1', div_le_div_of_nonneg_right hcomb hden.le,
      show w0 * ((10 * u0 * d) / (u0 + 2 * d) ^ 4) +
          (1 / 2 - w0) * ((6 * u0 * d) / (u0 + 2 * d) ^ 4) =
        (w0 * (10 * u0 * d) + (1 / 2 - w0) * (6 * u0 * d)) / (u0 + 2 * d) ^ 4 by ring]
  have hS1 : 0 ≤ 1 - t ^ 2 / u0 ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact pow_le_pow_left₀ ht0 htu0' 2
  have hS0 : 0 ≤ t ^ 2 / u0 ^ 2 := by positivity
  have hf_le : f (t ^ 2) ≤ 0 := by
    rw [hf_aff]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hS1 hf0)
      (mul_nonpos_of_nonneg_of_nonpos hS0 hfu)
  dsimp [f] at hf_le; linarith only [hf_le]

private theorem even_stencil_he_two_le {u0 du t w0 : ℝ} (hdu0 : 0 < du) (ht0 : 0 ≤ t)
    (htu0' : t ≤ u0) (hu0 : 6 * du ≤ u0) (hw0_lo : 185 / 1000 ≤ w0) (hw0_hi : w0 ≤ 219 / 1000) :
    let w1 := 1 / 2 - w0
    let He : ℝ → ℝ := fun m ↦ (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4
    w0 * He (u0 + 2 * du + (3 / 2 - 0) * du) + w1 * He (u0 + 2 * du + (3 / 2 - 1) * du) +
      w1 * He (u0 + 2 * du + (3 / 2 - 2) * du) ≤
      1 / (u0 + 2 * du) ^ 2 - t ^ 2 / (u0 + 2 * du) ^ 4 := by
  intro w1 He
  have hu0_pos : 0 < u0 := by linarith
  let d := du / 2; let m0 := u0 + 7 * d; let m1 := u0 + 5 * d; let m2 := u0 + 3 * d
  have hrew0 : u0 + 2 * du + (3 / 2 - 0) * du = m0 := by dsimp [m0, d]; ring
  have hrew1 : u0 + 2 * du + (3 / 2 - 1) * du = m1 := by dsimp [m1, d]; ring
  have hrew2 : u0 + 2 * du + (3 / 2 - 2) * du = m2 := by dsimp [m2, d]; ring
  have huk2 : u0 + 2 * du = u0 + 4 * d := by dsimp [d]; ring
  rw [hrew0, hrew1, hrew2, huk2]; dsimp [He]
  let f (S : ℝ) : ℝ := w0 * ((m0 ^ 2 - S - (77 / 10) * du ^ 2) / m0 ^ 4) +
    w1 * ((m1 ^ 2 - S - (77 / 10) * du ^ 2) / m1 ^ 4) +
    w1 * ((m2 ^ 2 - S - (77 / 10) * du ^ 2) / m2 ^ 4) -
    (1 / (u0 + 4 * d) ^ 2 - S / (u0 + 4 * d) ^ 4)
  have hf_aff : f (t ^ 2) = (1 - t ^ 2 / u0 ^ 2) * f 0 + (t ^ 2 / u0 ^ 2) * f (u0 ^ 2) := by
    dsimp [f]; have : u0 ≠ 0 := ne_of_gt hu0_pos; field_simp; ring
  have hd_pos : 0 < d := by dsimp [d]; linarith
  have hu0d : 12 * d ≤ u0 := by dsimp [d]; linarith
  have hf0 : f 0 ≤ 0 := by
    dsimp [f, w1]; simp only [sub_zero, zero_div]
    have h0 : (m0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤ 1 / (u0 + 4 * d) ^ 2 := by
      have : (m0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤ 1 / m0 ^ 2 := by
        rw [div_le_div_iff₀ (by dsimp [m0]; positivity) (by dsimp [m0]; positivity)]
        nlinarith only [sq_nonneg m0, sq_nonneg du]
      exact this.trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) (by dsimp [m0]; linarith) 2))
    have h1 : (m1 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤ 1 / (u0 + 4 * d) ^ 2 := by
      have : (m1 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤ 1 / m1 ^ 2 := by
        rw [div_le_div_iff₀ (by dsimp [m1]; positivity) (by dsimp [m1]; positivity)]
        nlinarith only [sq_nonneg m1, sq_nonneg du]
      exact this.trans (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by positivity) (by dsimp [m1]; linarith) 2))
    have h2 : (m2 ^ 2 - (77 / 10) * du ^ 2) / m2 ^ 4 ≤ (4 / 3) / (u0 + 4 * d) ^ 2 := by
      have : (m2 ^ 2 - (77 / 10) * du ^ 2) / m2 ^ 4 ≤ 1 / m2 ^ 2 := by
        rw [div_le_div_iff₀ (by dsimp [m2]; positivity) (by dsimp [m2]; positivity)]
        nlinarith only [sq_nonneg m2, sq_nonneg du]
      refine this.trans ?_; rw [div_le_div_iff₀ (by dsimp [m2]; positivity) (by positivity)]
      dsimp [m2]; nlinarith only [hu0d, hd_pos]
    have hw0' := mul_le_mul_of_nonneg_left h0 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hw1' := mul_le_mul_of_nonneg_left h1 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hw2' := mul_le_mul_of_nonneg_left h2 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hinv : 0 ≤ 1 / (u0 + 4 * d) ^ 2 := by positivity
    have h43 : (4 / 3) / (u0 + 4 * d) ^ 2 = (4 / 3) * (1 / (u0 + 4 * d) ^ 2) := by ring
    rw [h43] at hw2'
    have hc : (w0 + (1 / 2 - w0) + (1 / 2 - w0) * (4 / 3) - 1) *
        (1 / (u0 + 4 * d) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hw0_lo]) hinv
    linarith only [hw0', hw1', hw2', hc,
      show w0 * (1 / (u0 + 4 * d) ^ 2) + (1 / 2 - w0) * (1 / (u0 + 4 * d) ^ 2) +
          (1 / 2 - w0) * ((4 / 3) * (1 / (u0 + 4 * d) ^ 2)) - 1 / (u0 + 4 * d) ^ 2 =
        (w0 + (1 / 2 - w0) + (1 / 2 - w0) * (4 / 3) - 1) * (1 / (u0 + 4 * d) ^ 2) by ring]
  have hfu : f (u0 ^ 2) ≤ 0 := by
    dsimp [f, w1]
    have h0 : (m0 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m0 ^ 4 ≤
        (14 * u0 * d + (91 / 5) * d ^ 2) / (u0 + 4 * d) ^ 4 := by
      have hnum : m0 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2 = 14 * u0 * d + (91 / 5) * d ^ 2 := by
        dsimp [m0, d]; ring
      rw [hnum]; exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by dsimp [m0]; linarith) 4)
    have h1 : (m1 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m1 ^ 4 ≤
        (10 * u0 * d) / (u0 + 4 * d) ^ 4 := by
      have hnum : m1 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2 ≤ 10 * u0 * d := by
        dsimp [m1, d]; nlinarith only [sq_nonneg d]
      exact (div_le_div_of_nonneg_right hnum (by dsimp [m1]; positivity)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) (by dsimp [m1]; linarith) 4))
    have h2 : (m2 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2) / m2 ^ 4 ≤
        (6 * u0 * d + 9 * d ^ 2) / (u0 + 4 * d) ^ 4 := by
      rw [div_le_div_iff₀ (by dsimp [m2]; positivity) (by positivity)]
      have hnum : m2 ^ 2 - u0 ^ 2 - (77 / 10) * du ^ 2 = 6 * u0 * d - (109 / 5) * d ^ 2 := by
        dsimp [m2, d]; ring
      rw [hnum]; dsimp [m2]
      have hp := even_k2_m2_poly_nonneg (y := u0 - 12 * d) (d := d) (by linarith) hd_pos.le
      have hrw1 : u0 - 12 * d + 12 * d = u0 := by ring
      have hrw2 : u0 - 12 * d + 16 * d = u0 + 4 * d := by ring
      have hrw3 : u0 - 12 * d + 15 * d = u0 + 3 * d := by ring
      rw [hrw1, hrw2, hrw3] at hp
      exact hp
    have hge : 1 / (u0 + 4 * d) ^ 2 - u0 ^ 2 / (u0 + 4 * d) ^ 4 =
        (8 * u0 * d + 16 * d ^ 2) / (u0 + 4 * d) ^ 4 := by
      have : u0 + 4 * d ≠ 0 := ne_of_gt (by positivity); field_simp; ring
    rw [hge]; have hden : 0 < (u0 + 4 * d) ^ 4 := by positivity
    have hcomb : w0 * (14 * u0 * d + (91 / 5) * d ^ 2) + (1 / 2 - w0) * (10 * u0 * d) +
        (1 / 2 - w0) * (6 * u0 * d + 9 * d ^ 2) ≤ 8 * u0 * d + 16 * d ^ 2 := by
      have hid : 8 * u0 * d + 16 * d ^ 2 - (w0 * (14 * u0 * d + (91 / 5) * d ^ 2) +
          (1 / 2 - w0) * (10 * u0 * d) + (1 / 2 - w0) * (6 * u0 * d + 9 * d ^ 2)) =
          2 * w0 * (u0 * d) + (23 / 2 - (46 / 5) * w0) * d ^ 2 := by ring
      have hw_pos : 0 ≤ 2 * w0 := by linarith only [hw0_lo]
      have hw_ub : 0 ≤ 23 / 2 - (46 / 5) * w0 := by linarith only [hw0_hi]
      have hnn : 0 ≤ 8 * u0 * d + 16 * d ^ 2 - (w0 * (14 * u0 * d + (91 / 5) * d ^ 2) +
          (1 / 2 - w0) * (10 * u0 * d) + (1 / 2 - w0) * (6 * u0 * d + 9 * d ^ 2)) := by
        rw [hid]; positivity
      linarith only [hnn]
    have hw0' := mul_le_mul_of_nonneg_left h0 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hw1' := mul_le_mul_of_nonneg_left h1 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hw2' := mul_le_mul_of_nonneg_left h2 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    linarith only [hw0', hw1', hw2', div_le_div_of_nonneg_right hcomb hden.le,
      show w0 * ((14 * u0 * d + (91 / 5) * d ^ 2) / (u0 + 4 * d) ^ 4) +
        (1 / 2 - w0) * ((10 * u0 * d) / (u0 + 4 * d) ^ 4) +
        (1 / 2 - w0) * ((6 * u0 * d + 9 * d ^ 2) / (u0 + 4 * d) ^ 4) =
        (w0 * (14 * u0 * d + (91 / 5) * d ^ 2) + (1 / 2 - w0) * (10 * u0 * d) +
          (1 / 2 - w0) * (6 * u0 * d + 9 * d ^ 2)) / (u0 + 4 * d) ^ 4 by ring]
  have hS1 : 0 ≤ 1 - t ^ 2 / u0 ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact pow_le_pow_left₀ ht0 htu0' 2
  have hS0 : 0 ≤ t ^ 2 / u0 ^ 2 := by positivity
  have hf_le : f (t ^ 2) ≤ 0 := by
    rw [hf_aff]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hS1 hf0)
      (mul_nonpos_of_nonneg_of_nonpos hS0 hfu)
  dsimp [f] at hf_le; linarith only [hf_le]

private theorem even_stencil_le {u0 du t w0 mu : ℝ} (hdu0 : 0 < du) (hdu_hi : du ≤ 4794 / 10 ^ 8)
    (ht0 : 0 ≤ t) (htu0 : t + mu * du ≤ u0) (hu0 : 6 * du ≤ u0) (hw0_lo : 185 / 1000 ≤ w0)
    (hw0_hi : w0 ≤ 219 / 1000) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) (k : ℕ) :
    let w1 := 1 / 2 - w0; let W : ℕ → ℝ := fun r ↦ if r = 0 ∨ r = 3 then w0 else w1
    let C3 := t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2
    let dFe : ℝ → ℝ := fun x ↦ ((1 / x - C3 / (3 * x ^ 3)) -
      (1 / (x + du) - C3 / (3 * (x + du) ^ 3))) / du
    let ce : ℕ → ℝ := fun j ↦ if j = 0 then mu * dFe (u0 + du) else dFe (u0 + ((j : ℝ) + 1) * du)
    let uk := u0 + (k : ℝ) * du
    (∑ r ∈ Finset.range 4, if r ≤ k then W r * ce (k - r) else 0) ≤
      1 / uk ^ 2 - t ^ 2 / uk ^ 4 := by
  intro w1 W C3 dFe ce uk
  have hu0_pos : 0 < u0 := by linarith
  have htu0' : t ≤ u0 := by nlinarith only [htu0, hmu0, hdu0]
  let He : ℝ → ℝ := fun m ↦ (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4
  have hce_le (j : ℕ) : ce j ≤ He (u0 + ((j : ℝ) + 3 / 2) * du) := by
    have hj0 : (0 : ℝ) ≤ (j : ℝ) * du := mul_nonneg (Nat.cast_nonneg j) hdu0.le
    have ⟨h1, h2_num⟩ := even_dfe_le_he hdu0 hdu_hi ht0 htu0' hu0
      (x := u0 + ((j : ℝ) + 1) * du) (by linarith only [hj0])
    have h2 : 0 ≤ He (u0 + ((j : ℝ) + 1) * du + du / 2) :=
      div_nonneg h2_num (by positivity)
    rw [show u0 + ((j : ℝ) + 1) * du + du / 2 = u0 + ((j : ℝ) + 3 / 2) * du by ring] at h1 h2
    dsimp [ce]; split_ifs with hj
    · subst hj; simp only [Nat.cast_zero, zero_add, one_mul] at h1 h2 ⊢
      exact (mul_le_mul_of_nonneg_left h1 hmu0).trans (mul_le_of_le_one_left h2 hmu1)
    · exact h1
  have hW0 (r : ℕ) : 0 ≤ W r := by dsimp [W, w1]; split_ifs <;> linarith
  by_cases hk0 : k = 0
  · subst hk0; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      le_refl, ↓reduceIte, Nat.sub_zero, show ¬(1 ≤ 0) by omega, show ¬(2 ≤ 0) by omega,
      show ¬(3 ≤ 0) by omega, W, true_or, ce, Nat.cast_zero, zero_mul, add_zero, uk]
    have ⟨h1, h0⟩ := even_dfe_le_he hdu0 hdu_hi ht0 htu0' hu0 (x := u0 + du) le_rfl
    set m := u0 + (3 / 2) * du
    rw [show u0 + du + du / 2 = m by dsimp [m]; ring] at h1 h0
    have hstep1 : w0 * (mu * dFe (u0 + du)) ≤ w0 * (mu * He m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hmu0) (by linarith only [hw0_lo])
    have hm_pos : 0 < m := by dsimp [m]; linarith
    have hm_ge : u0 ^ 4 ≤ m ^ 4 := pow_le_pow_left₀ hu0_pos.le (by dsimp [m]; linarith) 4
    have hnum_le : w0 * mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) ≤ u0 ^ 2 - t ^ 2 := by
      have hmudu : u0 * (mu * du) ≤ u0 ^ 2 - t ^ 2 := by
        nlinarith only [htu0, ht0, hu0_pos, mul_nonneg ht0 (sub_nonneg.mpr htu0')]
      have hm2 : m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2 ≤ (u0 ^ 2 - t ^ 2) + 3 * u0 * du := by
        dsimp [m]; nlinarith only [sq_nonneg du]
      have hmu_step : mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) ≤ 4 * (u0 ^ 2 - t ^ 2) := by
        have ha := mul_le_mul_of_nonneg_left hm2 hmu0
        have hb : mu * (u0 ^ 2 - t ^ 2) ≤ 1 * (u0 ^ 2 - t ^ 2) :=
          mul_le_mul_of_nonneg_right hmu1 (by nlinarith only [ht0, htu0'])
        linarith only [ha, hb, hmudu, show mu * ((u0 ^ 2 - t ^ 2) + 3 * u0 * du) =
          mu * (u0 ^ 2 - t ^ 2) + 3 * (u0 * (mu * du)) by ring]
      have hw_step := mul_le_mul (by linarith only [hw0_hi] : w0 ≤ 1 / 4) hmu_step
        (mul_nonneg hmu0 h0) (by norm_num)
      linarith only [hw_step, show w0 * (mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2)) =
        w0 * mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) by ring]
    have hnum_nn : 0 ≤ w0 * mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith only [hw0_lo]) hmu0) h0
    calc w0 * (mu * dFe (u0 + du)) ≤ (w0 * mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2)) / m ^ 4 := by
          dsimp [He] at hstep1
          linarith only [hstep1, show w0 * (mu * ((m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2) / m ^ 4)) =
            (w0 * mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2)) / m ^ 4 by ring]
      _ ≤ (w0 * mu * (m ^ 2 - t ^ 2 - (77 / 10) * du ^ 2)) / u0 ^ 4 :=
          div_le_div_of_nonneg_left hnum_nn (by positivity) hm_ge
      _ ≤ (u0 ^ 2 - t ^ 2) / u0 ^ 4 := div_le_div_of_nonneg_right hnum_le (by positivity)
      _ = 1 / u0 ^ 2 - t ^ 2 / u0 ^ 4 := by field_simp
  have hsum_He : (∑ r ∈ Finset.range 4, if r ≤ k then W r * ce (k - r) else 0) ≤
      ∑ r ∈ Finset.range 4, if r ≤ k then W r * He (uk + (3 / 2 - (r : ℝ)) * du) else 0 := by
    refine Finset.sum_le_sum fun r _ ↦ ?_
    split_ifs with hr
    · rw [show uk + (3 / 2 - (r : ℝ)) * du = u0 + (((k - r : ℕ) : ℝ) + 3 / 2) * du by
        dsimp [uk]; rw [Nat.cast_sub hr]; ring]
      exact mul_le_mul_of_nonneg_left (hce_le (k - r)) (hW0 r)
    · rfl
  refine hsum_He.trans ?_
  by_cases hk1 : k = 1
  · subst hk1; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      show 0 ≤ 1 by omega, le_refl, show ¬(2 ≤ 1) by omega, show ¬(3 ≤ 1) by omega, ↓reduceIte,
      add_zero, W, true_or, show ¬(1 = 0 ∨ 1 = 3) by omega, Nat.cast_zero, Nat.cast_one, uk]
    exact even_stencil_he_one_le hdu0 ht0 htu0' hu0_pos hw0_lo hw0_hi
  by_cases hk2 : k = 2
  · subst hk2; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      show 0 ≤ 2 by omega, show 1 ≤ 2 by omega, le_refl, show ¬(3 ≤ 2) by omega, ↓reduceIte,
      add_zero, W, true_or, show ¬(1 = 0 ∨ 1 = 3) by omega, show ¬(2 = 0 ∨ 2 = 3) by omega,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, uk]
    exact even_stencil_he_two_le hdu0 ht0 htu0' hu0 hw0_lo hw0_hi
  have hk3 : 3 ≤ k := by omega
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.zero_le, show 1 ≤ k by omega, show 2 ≤ k by omega, hk3, ↓reduceIte, W, true_or,
    show ¬(1 = 0 ∨ 1 = 3) by omega, show ¬(2 = 0 ∨ 2 = 3) by omega, or_true,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  exact even_stencil_tail_le hdu0 hw0_lo hw0_hi (by
    dsimp [uk]; have hk3r : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    nlinarith only [hu0, hk3r, hdu0])

private theorem pole_single_stencil_le {u0 du w0 mu s r Z : ℝ} (hdu0 : 0 < du)
    (hdu_hi : du ≤ 4794 / 10 ^ 8) (hu0 : 6 * du ≤ u0) (hw0_lo : 185 / 1000 ≤ w0)
    (hw0_hi : w0 ≤ 219 / 1000) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) (hs : 8 / 10000 ≤ s)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hZ : 25 ≤ Z) (hZv : Z * du ≤ u0 + 3 * du + s)
    (hcert : r * ((219 / 1000) * (2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4)) +
      (281 / 1000) * 2 / (Z ^ 2 - 1)) * Z ^ 2 ≤ 1) (k : ℕ) :
    let w1 := 1 / 2 - w0; let W : ℕ → ℝ := fun r ↦ if r = 0 ∨ r = 3 then w0 else w1
    let df1 : ℝ → ℝ := fun x ↦ r / ((x + s) * (x + du + s))
    let c1 : ℕ → ℝ := fun j ↦ if j = 0 then mu * df1 (u0 + du) else df1 (u0 + ((j : ℝ) + 1) * du)
    (∑ q ∈ Finset.range 4, if q ≤ k then W q * c1 (k - q) else 0) ≤
      1 / (u0 + (k : ℝ) * du + s) ^ 2 := by
  intro w1 W df1 c1
  let uk := u0 + (k : ℝ) * du
  change _ ≤ 1 / (uk + s) ^ 2
  have hu0_pos : 0 < u0 := by linarith
  have hdf1_nn (x : ℝ) (hx : 0 < x) : 0 ≤ df1 x := div_nonneg hr0 (by positivity)
  have hc1_le (j : ℕ) : c1 j ≤ df1 (u0 + ((j : ℝ) + 1) * du) := by
    dsimp [c1]; split_ifs with hj
    · subst hj; simp only [Nat.cast_zero, zero_add, one_mul]
      refine (le_abs_self _).trans ?_
      rw [abs_of_nonneg (mul_nonneg hmu0 (hdf1_nn (u0 + du) (by positivity)))]
      exact mul_le_of_le_one_left (hdf1_nn (u0 + du) (by positivity)) hmu1
    · rfl
  have hW0 (q : ℕ) : 0 ≤ W q := by dsimp [W, w1]; split_ifs <;> linarith
  have hstep : (∑ q ∈ Finset.range 4, if q ≤ k then W q * c1 (k - q) else 0) ≤
      ∑ q ∈ Finset.range 4,
        if q ≤ k then W q * df1 (u0 + (((k - q : ℕ) : ℝ) + 1) * du) else 0 := by
    refine Finset.sum_le_sum fun q _ ↦ ?_
    split_ifs with hq
    · exact mul_le_mul_of_nonneg_left (hc1_le (k - q)) (hW0 q)
    · rfl
  refine hstep.trans ?_
  by_cases hk0 : k = 0
  · subst hk0; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      le_refl, ↓reduceIte, Nat.sub_zero, show ¬(1 ≤ 0) by omega, show ¬(2 ≤ 0) by omega,
      show ¬(3 ≤ 0) by omega, add_zero, one_mul, W, true_or, Nat.cast_zero, df1, uk]
    have h1 : r / ((u0 + du + s) * (u0 + du + du + s)) ≤ 1 / (u0 + 0 * du + s) ^ 2 :=
      (div_le_div_of_nonneg_right hr1 (by positivity)).trans
        (one_div_le_one_div_of_le (by positivity) (by nlinarith only [hu0_pos, hdu0, hs]))
    have hw0' := mul_le_mul_of_nonneg_left h1 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hinv : 0 ≤ 1 / (u0 + 0 * du + s) ^ 2 := by positivity
    exact hw0'.trans (mul_le_of_le_one_left hinv (by linarith only [hw0_hi]))
  by_cases hk1 : k = 1
  · subst hk1; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      show 0 ≤ 1 by omega, le_refl, show ¬(2 ≤ 1) by omega, show ¬(3 ≤ 1) by omega, ↓reduceIte,
      add_zero, W, true_or, show ¬(1 = 0 ∨ 1 = 3) by omega, Nat.cast_one, df1, uk]
    have hb (x : ℝ) (hx : u0 + 1 * du ≤ x) : r / ((x + s) * (x + du + s)) ≤
        1 / (u0 + 1 * du + s) ^ 2 := by
      have hx0 : 0 < x := by linarith only [hx, hu0_pos, hdu0]
      exact (div_le_div_of_nonneg_right hr1 (by positivity)).trans
        (one_div_le_one_div_of_le (by positivity) (by nlinarith only [hx, hu0_pos, hdu0, hs]))
    have hb0 := hb (u0 + (1 + 1) * du) (by linarith only [hdu0])
    have hb1 := hb (u0 + (0 + 1) * du) (by linarith only [hdu0])
    dsimp [w1]
    have hw0' := mul_le_mul_of_nonneg_left hb0 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hw1' := mul_le_mul_of_nonneg_left hb1 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hinv : 0 ≤ 1 / (u0 + 1 * du + s) ^ 2 := by positivity
    nlinarith only [hw0', hw1', hinv, hw0_hi]
  by_cases hk2 : k = 2
  · subst hk2; simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      show 0 ≤ 2 by omega, show 1 ≤ 2 by omega, le_refl, show ¬(3 ≤ 2) by omega, ↓reduceIte,
      add_zero, W, true_or, show ¬(1 = 0 ∨ 1 = 3) by omega, show ¬(2 = 0 ∨ 2 = 3) by omega,
      Nat.cast_ofNat, df1, uk]
    let v := u0 + 2 * du + s
    have hv_du : 18 * du ≤ v := by dsimp [v]; linarith only [hu0, hs, hdu_hi]
    have hb0 : r / ((u0 + (2 + 1) * du + s) * (u0 + (2 + 1) * du + du + s)) ≤ 1 / v ^ 2 :=
      (div_le_div_of_nonneg_right hr1 (by positivity)).trans
        (one_div_le_one_div_of_le (by dsimp [v]; positivity)
          (by dsimp [v]; nlinarith only [hu0_pos, hdu0, hs]))
    have hb1 : r / ((u0 + (1 + 1) * du + s) * (u0 + (1 + 1) * du + du + s)) ≤ 1 / v ^ 2 :=
      (div_le_div_of_nonneg_right hr1 (by positivity)).trans
        (one_div_le_one_div_of_le (by dsimp [v]; positivity)
          (by dsimp [v]; nlinarith only [hu0_pos, hdu0, hs]))
    have hb2 : r / ((u0 + (0 + 1) * du + s) * (u0 + (0 + 1) * du + du + s)) ≤
        (18 / 17) / v ^ 2 := by
      refine (div_le_div_of_nonneg_right hr1 (by positivity)).trans ?_
      rw [div_le_div_iff₀ (by positivity) (by dsimp [v]; positivity)]
      have h1 : u0 + (0 + 1) * du + s = v - du := by dsimp [v]; ring
      have h2 : u0 + (0 + 1) * du + du + s = v := by dsimp [v]; ring
      rw [h1, h2]; nlinarith only [hv_du, hdu0]
    dsimp [w1]
    have hw0' := mul_le_mul_of_nonneg_left hb0 (by linarith only [hw0_lo] : 0 ≤ w0)
    have hw1' := mul_le_mul_of_nonneg_left hb1 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hw2' := mul_le_mul_of_nonneg_left hb2 (by linarith only [hw0_hi] : 0 ≤ 1 / 2 - w0)
    have hinv : 0 ≤ 1 / v ^ 2 := div_nonneg zero_le_one (sq_nonneg v)
    rw [show (18 / 17) / v ^ 2 = (18 / 17) * (1 / v ^ 2) by ring] at hw2'
    nlinarith only [hw0', hw1', hw2', hinv, hw0_lo]
  have hk3 : 3 ≤ k := by omega
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.zero_le, show 1 ≤ k by omega, show 2 ≤ k by omega, hk3, ↓reduceIte, W, true_or,
    show ¬(1 = 0 ∨ 1 = 3) by omega, show ¬(2 = 0 ∨ 2 = 3) by omega, or_true]
  let v := uk + s
  have hvZ : Z * du ≤ v := by
    dsimp [v, uk]; have hk3r : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    nlinarith only [hZv, hk3r, hdu0]
  have hv_pos : 0 < v := by nlinarith only [hvZ, hZ, hdu0]
  have hp03 : df1 (u0 + (((k - 0 : ℕ) : ℝ) + 1) * du) +
      df1 (u0 + (((k - 3 : ℕ) : ℝ) + 1) * du) =
      r * (2 * v ^ 2 + 4 * du ^ 2) / ((v ^ 2 - du ^ 2) * (v ^ 2 - 4 * du ^ 2)) := by
    dsimp [df1]; rw [Nat.cast_sub hk3]; push_cast
    have h1 : u0 + ((k : ℝ) + 1) * du + s = v + du := by dsimp [v, uk]; ring
    have h2 : u0 + ((k : ℝ) + 1) * du + du + s = v + 2 * du := by dsimp [v, uk]; ring
    have h3 : u0 + ((k : ℝ) - 3 + 1) * du + s = v - 2 * du := by dsimp [v, uk]; ring
    have h4 : u0 + ((k : ℝ) - 3 + 1) * du + du + s = v - du := by dsimp [v, uk]; ring
    rw [h1, h2, h3, h4]
    have hd1 : 0 < (v + du) * (v + 2 * du) :=
      mul_pos (by linarith only [hv_pos, hdu0]) (by linarith only [hv_pos, hdu0])
    have hd2 : 0 < (v - 2 * du) * (v - du) :=
      mul_pos (by nlinarith only [hvZ, hZ, hdu0]) (by nlinarith only [hvZ, hZ, hdu0])
    rw [div_add_div _ _ hd1.ne' hd2.ne']
    exact congrArg₂ (· / ·) (by ring) (by ring)
  have hp12 : df1 (u0 + (((k - 1 : ℕ) : ℝ) + 1) * du) +
      df1 (u0 + (((k - 2 : ℕ) : ℝ) + 1) * du) = r * 2 / (v ^ 2 - du ^ 2) := by
    dsimp [df1]; rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]; push_cast
    have h1 : u0 + ((k : ℝ) - 1 + 1) * du + s = v := by dsimp [v, uk]; ring
    have h2 : u0 + ((k : ℝ) - 1 + 1) * du + du + s = v + du := by dsimp [v, uk]; ring
    have h3 : u0 + ((k : ℝ) - 2 + 1) * du + s = v - du := by dsimp [v, uk]; ring
    have h4 : u0 + ((k : ℝ) - 2 + 1) * du + du + s = v := by dsimp [v, uk]; ring
    rw [h1, h2, h3, h4]
    have hp1 : v + du ≠ 0 := ne_of_gt (by linarith only [hv_pos, hdu0])
    have hp2 : v - du ≠ 0 := ne_of_gt (by nlinarith only [hvZ, hZ, hdu0])
    have hd1 : v ^ 2 - du ^ 2 = (v - du) * (v + du) := by ring
    rw [hd1]; field_simp [ne_of_gt hv_pos]; ring
  have hsum_rew : w0 * df1 (u0 + (((k - 0 : ℕ) : ℝ) + 1) * du) +
      w1 * df1 (u0 + (((k - 1 : ℕ) : ℝ) + 1) * du) +
      w1 * df1 (u0 + (((k - 2 : ℕ) : ℝ) + 1) * du) +
      w0 * df1 (u0 + (((k - 3 : ℕ) : ℝ) + 1) * du) =
      w0 * (df1 (u0 + (((k - 0 : ℕ) : ℝ) + 1) * du) +
        df1 (u0 + (((k - 3 : ℕ) : ℝ) + 1) * du)) +
      w1 * (df1 (u0 + (((k - 1 : ℕ) : ℝ) + 1) * du) +
        df1 (u0 + (((k - 2 : ℕ) : ℝ) + 1) * du)) := by ring
  rw [hsum_rew, hp03, hp12]
  have hv2Z : Z ^ 2 * du ^ 2 ≤ v ^ 2 :=
    (le_of_eq (by ring)).trans (pow_le_pow_left₀ (by nlinarith only [hZ, hdu0]) hvZ 2)
  have hdu2_pos : 0 < du ^ 2 := sq_pos_of_pos hdu0
  have hZ2 : 625 ≤ Z ^ 2 := by nlinarith only [hZ]
  have hv2_625 : 625 * du ^ 2 ≤ v ^ 2 :=
    (mul_le_mul_of_nonneg_right hZ2 hdu2_pos.le).trans hv2Z
  have hv1 : 0 < v ^ 2 - du ^ 2 := by linarith only [hv2_625, hdu2_pos]
  have hv4 : 0 < v ^ 2 - 4 * du ^ 2 := by linarith only [hv2_625, hdu2_pos]
  have hZ1 : 0 < Z ^ 2 - 1 := by linarith only [hZ2]
  have hZ4 : 0 < Z ^ 2 - 4 := by linarith only [hZ2]
  have hb_in : 2 / (v ^ 2 - du ^ 2) ≤ (2 / (Z ^ 2 - 1)) * (Z ^ 2 / v ^ 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ hv1 (mul_pos hZ1 (sq_pos_of_pos hv_pos))]
    linarith only [hv2Z, show 2 * ((Z ^ 2 - 1) * v ^ 2) = 2 * (Z ^ 2 * v ^ 2) - 2 * v ^ 2 by ring,
      show 2 * Z ^ 2 * (v ^ 2 - du ^ 2) = 2 * (Z ^ 2 * v ^ 2) - 2 * (Z ^ 2 * du ^ 2) by ring]
  have hb_out : (2 * v ^ 2 + 4 * du ^ 2) / ((v ^ 2 - du ^ 2) * (v ^ 2 - 4 * du ^ 2)) ≤
      ((2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4))) * (Z ^ 2 / v ^ 2) := by
    rw [div_mul_div_comm,
      div_le_div_iff₀ (mul_pos hv1 hv4) (mul_pos (mul_pos hZ1 hZ4) (sq_pos_of_pos hv_pos))]
    let w := Z ^ 2 - 625; let x := v ^ 2 - Z ^ 2 * du ^ 2
    have hw : 0 ≤ w := by dsimp [w]; linarith only [hZ2]
    have hx : 0 ≤ x := by dsimp [x]; linarith only [hv2Z]
    have hid : (2 * Z ^ 2 + 4) * Z ^ 2 * ((v ^ 2 - du ^ 2) * (v ^ 2 - 4 * du ^ 2)) -
        (2 * v ^ 2 + 4 * du ^ 2) * ((Z ^ 2 - 1) * (Z ^ 2 - 4)) * v ^ 2 =
        5458734 * x * du ^ 2 + 8742 * x ^ 2 + 17484 * w * x * du ^ 2 +
          14 * w * x ^ 2 + 14 * w ^ 2 * x * du ^ 2 := by dsimp [w, x]; ring
    have : 0 ≤ (2 * Z ^ 2 + 4) * Z ^ 2 * ((v ^ 2 - du ^ 2) * (v ^ 2 - 4 * du ^ 2)) -
        (2 * v ^ 2 + 4 * du ^ 2) * ((Z ^ 2 - 1) * (Z ^ 2 - 4)) * v ^ 2 := by
      rw [hid]; positivity
    linarith
  have hw_mono : w0 * ((2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4))) +
      w1 * (2 / (Z ^ 2 - 1)) ≤
      (219 / 1000) * (2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4)) +
        (281 / 1000) * 2 / (Z ^ 2 - 1) := by
    dsimp [w1]
    have hdiff : 0 ≤ (2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4)) - 2 / (Z ^ 2 - 1) := by
      rw [sub_nonneg, div_le_div_iff₀ hZ1 (mul_pos hZ1 hZ4)]; linarith only [hZ2]
    have hprod := mul_nonneg (by linarith only [hw0_hi] : 0 ≤ 219 / 1000 - w0) hdiff
    linarith only [hprod,
      show (219 / 1000 - w0) *
          ((2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4)) - 2 / (Z ^ 2 - 1)) =
        ((219 / 1000) * (2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4)) +
          (281 / 1000) * 2 / (Z ^ 2 - 1)) -
        (w0 * ((2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4))) +
          (1 / 2 - w0) * (2 / (Z ^ 2 - 1))) by ring]
  have hw1_pos : 0 ≤ w1 := by dsimp [w1]; linarith only [hw0_hi]
  calc w0 * (r * (2 * v ^ 2 + 4 * du ^ 2) / ((v ^ 2 - du ^ 2) * (v ^ 2 - 4 * du ^ 2))) +
        w1 * (r * 2 / (v ^ 2 - du ^ 2))
      = r * (w0 * ((2 * v ^ 2 + 4 * du ^ 2) / ((v ^ 2 - du ^ 2) * (v ^ 2 - 4 * du ^ 2))) +
          w1 * (2 / (v ^ 2 - du ^ 2))) := by ring
    _ ≤ r * (w0 * (((2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4))) * (Z ^ 2 / v ^ 2)) +
          w1 * ((2 / (Z ^ 2 - 1)) * (Z ^ 2 / v ^ 2))) := by gcongr
    _ = (r * (w0 * ((2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4))) +
          w1 * (2 / (Z ^ 2 - 1))) * Z ^ 2) * (1 / v ^ 2) := by ring
    _ ≤ (r * ((219 / 1000) * (2 * Z ^ 2 + 4) / ((Z ^ 2 - 1) * (Z ^ 2 - 4)) +
          (281 / 1000) * 2 / (Z ^ 2 - 1)) * Z ^ 2) * (1 / v ^ 2) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw_mono hr0) (sq_nonneg Z)
        exact mul_le_mul_of_nonneg_right (this.trans_eq (by ring)) (by positivity)
    _ ≤ 1 * (1 / v ^ 2) := mul_le_mul_of_nonneg_right hcert (by positivity)
    _ = 1 / (uk + s) ^ 2 := by dsimp [v]; ring

private theorem pole_stencil_le {u0 du w0 mu : ℝ} (hdu0 : 0 < du) (hdu_hi : du ≤ 4794 / 10 ^ 8)
    (hu0 : 6 * du ≤ u0) (hw0_lo : 185 / 1000 ≤ w0) (hw0_hi : w0 ≤ 219 / 1000)
    (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) (k : ℕ) :
    let w1 := 1 / 2 - w0; let W : ℕ → ℝ := fun r ↦ if r = 0 ∨ r = 3 then w0 else w1
    let dFp : ℝ → ℝ := fun x ↦ (fPoleSum x - fPoleSum (x + du)) / du
    let cp : ℕ → ℝ := fun j ↦ if j = 0 then mu * dFp (u0 + du) else dFp (u0 + ((j : ℝ) + 1) * du)
    (∑ r ∈ Finset.range 4, if r ≤ k then W r * cp (k - r) else 0) ≤
      gPoleSum (u0 + (k : ℝ) * du) := by
  intro w1 W dFp cp
  have hu0_pos : 0 < u0 := by linarith
  have hdFp_eq (x : ℝ) (hx : 0 < x) : dFp x =
      (24 / 15625) * ((989 / 1000) / ((x + 8 / 10000) * (x + du + 8 / 10000))) +
      (6 / 625) * ((9994 / 10000) / ((x + 5 / 1000) * (x + du + 5 / 1000))) +
      (3 / 50) * ((9999 / 10000) / ((x + 3125 / 100000) * (x + du + 3125 / 100000))) +
      (48 / 125) * ((9999 / 10000) / ((x + 2 / 10) * (x + du + 2 / 10))) := by
    dsimp [dFp]; unfold fPoleSum
    have hd {s : ℝ} (hs : 0 < s) : (1 / (x + s) - 1 / (x + du + s)) / du =
        1 / ((x + s) * (x + du + s)) := by
      have : x + s ≠ 0 := ne_of_gt (by linarith)
      have : x + du + s ≠ 0 := ne_of_gt (by linarith)
      have : du ≠ 0 := ne_of_gt hdu0
      field_simp; ring
    have h1 := hd (show (0 : ℝ) < 8 / 10000 by norm_num)
    have h2 := hd (show (0 : ℝ) < 5 / 1000 by norm_num)
    have h3 := hd (show (0 : ℝ) < 3125 / 100000 by norm_num)
    have h4 := hd (show (0 : ℝ) < 2 / 10 by norm_num)
    linear_combination (2967 / 1953125) * h1 + (14991 / 1562500) * h2 +
      (29997 / 500000) * h3 + (29997 / 78125) * h4
  have hp0 := pole_single_stencil_le hdu0 hdu_hi hu0 hw0_lo hw0_hi hmu0 hmu1
    (s := 8 / 10000) (r := 989 / 1000) (Z := 25) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith only [hu0, hdu_hi, hdu0]) (by norm_num) k
  have hp1 := pole_single_stencil_le hdu0 hdu_hi hu0 hw0_lo hw0_hi hmu0 hmu1
    (s := 5 / 1000) (r := 9994 / 10000) (Z := 113) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith only [hu0, hdu_hi, hdu0]) (by norm_num) k
  have hp2 := pole_single_stencil_le hdu0 hdu_hi hu0 hw0_lo hw0_hi hmu0 hmu1
    (s := 3125 / 100000) (r := 9999 / 10000) (Z := 660) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith only [hu0, hdu_hi, hdu0]) (by norm_num) k
  have hp3 := pole_single_stencil_le hdu0 hdu_hi hu0 hw0_lo hw0_hi hmu0 hmu1
    (s := 2 / 10) (r := 9999 / 10000) (Z := 4180) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith only [hu0, hdu_hi, hdu0]) (by norm_num) k
  have hlin : (∑ q ∈ Finset.range 4, if q ≤ k then W q * cp (k - q) else 0) =
      (24 / 15625) * (∑ q ∈ Finset.range 4, if q ≤ k then W q *
        (if k - q = 0 then mu * ((989 / 1000) /
            ((u0 + du + 8 / 10000) * (u0 + du + du + 8 / 10000)))
          else (989 / 1000) / ((u0 + (((k - q : ℕ) : ℝ) + 1) * du + 8 / 10000) *
            (u0 + (((k - q : ℕ) : ℝ) + 1) * du + du + 8 / 10000))) else 0) +
      (6 / 625) * (∑ q ∈ Finset.range 4, if q ≤ k then W q *
        (if k - q = 0 then mu * ((9994 / 10000) /
            ((u0 + du + 5 / 1000) * (u0 + du + du + 5 / 1000)))
          else (9994 / 10000) / ((u0 + (((k - q : ℕ) : ℝ) + 1) * du + 5 / 1000) *
            (u0 + (((k - q : ℕ) : ℝ) + 1) * du + du + 5 / 1000))) else 0) +
      (3 / 50) * (∑ q ∈ Finset.range 4, if q ≤ k then W q *
        (if k - q = 0 then mu * ((9999 / 10000) / ((u0 + du + 3125 / 100000) *
            (u0 + du + du + 3125 / 100000)))
          else (9999 / 10000) / ((u0 + (((k - q : ℕ) : ℝ) + 1) * du + 3125 / 100000) *
            (u0 + (((k - q : ℕ) : ℝ) + 1) * du + du + 3125 / 100000))) else 0) +
      (48 / 125) * (∑ q ∈ Finset.range 4, if q ≤ k then W q *
        (if k - q = 0 then mu * ((9999 / 10000) / ((u0 + du + 2 / 10) * (u0 + du + du + 2 / 10)))
          else (9999 / 10000) / ((u0 + (((k - q : ℕ) : ℝ) + 1) * du + 2 / 10) *
            (u0 + (((k - q : ℕ) : ℝ) + 1) * du + du + 2 / 10))) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    split_ifs with hq h0
    · simp only [cp, h0, ↓reduceIte, hdFp_eq (u0 + du) (by positivity)]; ring
    · simp only [cp, h0, ↓reduceIte,
        hdFp_eq (u0 + (((k - q : ℕ) : ℝ) + 1) * du) (by positivity)]; ring
    · simp
  rw [hlin]
  have hgP : gPoleSum (u0 + (k : ℝ) * du) =
      (24 / 15625) * (1 / (u0 + (k : ℝ) * du + 8 / 10000) ^ 2) +
      (6 / 625) * (1 / (u0 + (k : ℝ) * du + 5 / 1000) ^ 2) +
      (3 / 50) * (1 / (u0 + (k : ℝ) * du + 3125 / 100000) ^ 2) +
      (48 / 125) * (1 / (u0 + (k : ℝ) * du + 2 / 10) ^ 2) := by unfold gPoleSum; ring
  rw [hgP]
  exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp0 (by norm_num))
      (mul_le_mul_of_nonneg_left hp1 (by norm_num)))
      (mul_le_mul_of_nonneg_left hp2 (by norm_num)))
    (mul_le_mul_of_nonneg_left hp3 (by norm_num))

private theorem cubic_conv_le {tau du t mu : ℝ} (hdu_lo : 4793 / 10 ^ 8 ≤ du)
    (hdu_hi : du ≤ 4794 / 10 ^ 8) (ht0 : 0 ≤ t) (htau_t : t ≤ tau)
    (htau_lo : 6 * (4794 / 10 ^ 8) ≤ tau) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    let x1 := tau + (1 + mu) * du; let x2 := tau + (2 + mu) * du
    let a := tau + 2 * (4794 / 10 ^ 8)
    (t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2) * (mu / x1 ^ 3 + (1 - mu) / x2 ^ 3) ≤
      (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / a ^ 3 := by
  intro x1 x2 a; let x0 := tau + 2 * du
  have hx0_pos : 0 < x0 := by dsimp [x0]; linarith
  have h8du : 8 * du ≤ x0 := by dsimp [x0]; linarith
  have hquad {x : ℝ} (hx : (7 / 8) * x0 ≤ x) :
      1 / x ^ 3 ≤ 1 / x0 ^ 3 - 3 * (x - x0) / x0 ^ 4 + 8 * (x - x0) ^ 2 / x0 ^ 5 := by
    have hx_pos : 0 < x := by linarith
    have hsub : (1 / x0 ^ 3 - 3 * (x - x0) / x0 ^ 4 + 8 * (x - x0) ^ 2 / x0 ^ 5) - 1 / x ^ 3 =
        (x - x0) ^ 2 * ((5 / 16) * x0 ^ 3 + (89 / 8) * x0 ^ 2 * (x - (7 / 8) * x0) +
          18 * x0 * (x - (7 / 8) * x0) ^ 2 + 8 * (x - (7 / 8) * x0) ^ 3) /
          (x ^ 3 * x0 ^ 5) := by field_simp; ring
    have hnum : 0 ≤ (5 / 16) * x0 ^ 3 + (89 / 8) * x0 ^ 2 * (x - (7 / 8) * x0) +
        18 * x0 * (x - (7 / 8) * x0) ^ 2 + 8 * (x - (7 / 8) * x0) ^ 3 := by
      have : 0 ≤ x - (7 / 8) * x0 := by linarith
      positivity
    have : 0 ≤ (1 / x0 ^ 3 - 3 * (x - x0) / x0 ^ 4 + 8 * (x - x0) ^ 2 / x0 ^ 5) - 1 / x ^ 3 := by
      rw [hsub]; positivity
    linarith
  have hq1 := hquad (x := x1) (by dsimp [x1, x0]; nlinarith only [h8du, hmu0, hdu_lo])
  have hq2 := hquad (x := x2) (by dsimp [x2, x0]; nlinarith only [h8du, hmu0, hdu_lo])
  have hcomb : mu / x1 ^ 3 + (1 - mu) / x2 ^ 3 ≤ 1 / x0 ^ 3 + 2 * du ^ 2 / x0 ^ 5 := by
    have hlin : mu * (x1 - x0) + (1 - mu) * (x2 - x0) = 0 := by dsimp [x1, x2, x0]; ring
    have hsq : mu * (x1 - x0) ^ 2 + (1 - mu) * (x2 - x0) ^ 2 = mu * (1 - mu) * du ^ 2 := by
      dsimp [x1, x2, x0]; ring
    have hmu_prod : mu * (1 - mu) ≤ 1 / 4 := by nlinarith only [sq_nonneg (mu - 1 / 2)]
    have h1 := add_le_add (mul_le_mul_of_nonneg_left hq1 hmu0)
      (mul_le_mul_of_nonneg_left hq2 (sub_nonneg.mpr hmu1))
    calc mu / x1 ^ 3 + (1 - mu) / x2 ^ 3
        = mu * (1 / x1 ^ 3) + (1 - mu) * (1 / x2 ^ 3) := by ring
      _ ≤ mu * (1 / x0 ^ 3 - 3 * (x1 - x0) / x0 ^ 4 + 8 * (x1 - x0) ^ 2 / x0 ^ 5) +
          (1 - mu) * (1 / x0 ^ 3 - 3 * (x2 - x0) / x0 ^ 4 + 8 * (x2 - x0) ^ 2 / x0 ^ 5) := h1
      _ = 1 / x0 ^ 3 - 3 * (mu * (x1 - x0) + (1 - mu) * (x2 - x0)) / x0 ^ 4 +
          8 * (mu * (x1 - x0) ^ 2 + (1 - mu) * (x2 - x0) ^ 2) / x0 ^ 5 := by ring
      _ = 1 / x0 ^ 3 + 8 * (mu * (1 - mu) * du ^ 2) / x0 ^ 5 := by rw [hlin, hsq]; ring
      _ ≤ 1 / x0 ^ 3 + 2 * du ^ 2 / x0 ^ 5 := by
          have hnum : 8 * (mu * (1 - mu) * du ^ 2) ≤ 2 * du ^ 2 := by
            nlinarith only [hmu_prod, sq_nonneg du]
          exact add_le_add_right (div_le_div_of_nonneg_right hnum (by positivity)) _
  have hstep2 : (t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2) * (1 / x0 ^ 3 + 2 * du ^ 2 / x0 ^ 5) ≤
      (t ^ 2 + 276 / 10 ^ 10) / x0 ^ 3 := by
    rw [show 1 / x0 ^ 3 + 2 * du ^ 2 / x0 ^ 5 = (x0 ^ 2 + 2 * du ^ 2) / x0 ^ 5 by field_simp,
      mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have ht_x0 : t ^ 2 ≤ x0 ^ 2 := pow_le_pow_left₀ ht0 (by dsimp [x0]; linarith) 2
    have hdu_x0 : 63 * (4794 / 10 ^ 8) ^ 2 ≤ x0 ^ 2 := by
      have : (6 * (4794 / 10 ^ 8) + 2 * (4793 / 10 ^ 8)) ^ 2 ≤ x0 ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by dsimp [x0]; linarith) 2
      linarith
    have hdu2 : du ^ 2 ≤ (4794 / 10 ^ 8) ^ 2 := pow_le_pow_left₀ (by linarith) hdu_hi 2
    have hcore : (t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2) * (x0 ^ 2 + 2 * du ^ 2) ≤
        (t ^ 2 + 276 / 10 ^ 10) * x0 ^ 2 := by
      nlinarith only [ht_x0, hdu_x0, hdu2, sq_nonneg du]
    exact (mul_le_mul_of_nonneg_right hcore (pow_nonneg hx0_pos.le 3)).trans_eq (by ring)
  have ha_rat : a ^ 3 ≤ (5001 / 5000) * x0 ^ 3 := by
    have ha_x0 : (6 * (4794 / 10 ^ 8) + 2 * (4793 / 10 ^ 8)) * a ≤
        (8 * (4794 / 10 ^ 8)) * x0 := by dsimp [a, x0]; linarith
    have hp := pow_le_pow_left₀ (by dsimp [a]; positivity) ha_x0 3
    rw [mul_pow, mul_pow] at hp
    have hx03 : 0 ≤ x0 ^ 3 := by positivity
    linarith only [hp, hx03]
  have hstep3 : (t ^ 2 + 276 / 10 ^ 10) / x0 ^ 3 ≤
      (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / a ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by dsimp [a]; positivity)]
    exact (mul_le_mul_of_nonneg_left ha_rat (by positivity)).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hcomb (by positivity)).trans (hstep2.trans hstep3)

/-- Quartic trigonometric majorant of `(max |cos(φ' + u)| γ - max (cos φ') γ)^2`. -/
private noncomputable def clampedMajorant (s0 c0 u : ℝ) : ℝ :=
  s0 ^ 2 * Real.sin u ^ 2 + (247 / 1000) * Real.sin u ^ 4 +
    s0 * c0 * (Real.sin u ^ 3 * Real.cos u)

/-- Antiderivative primitive `F(x)` for the quartet telescoping sum. -/
private noncomputable def stencilPrim (s0 c0 t x : ℝ) : ℝ :=
  s0 ^ 2 * (1 / x - (t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2) / (3 * x ^ 3)) + s0 * c0 * fPoleSum x

private theorem clamped_tot_sum_le {M mHi : ℕ} {Ctot : ℝ} (hMlo : 46368 ≤ M) (hMhi : M ≤ mHi)
    (hmHi_ub : mHi ≤ 47488)
    {γ φ' : ℝ} (hγlo : 949 / 1000 ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hφ0 : 0 ≤ φ')
    (hφ_hi : φ' ≤ 35 / 100) (hc0lo : γ - 1 / 20000 ≤ Real.cos φ')
    (hc0hi : Real.cos φ' ≤ γ + 3 / 2500) (hs0_nn : 0 ≤ Real.sin φ')
    (hs0_lo : 29 / 100 ≤ Real.sin φ') (hs0_hi : Real.sin φ' ≤ 31543 / 100000)
    (hs0_sq_lo : 1 - (9567 / 10000) ^ 2 ≤ Real.sin φ' ^ 2)
    (hc0_lo : 18979 / 20000 ≤ Real.cos φ') (hc0_hi : Real.cos φ' ≤ 9567 / 10000)
    (hCtot_ge : (mHi : ℝ) / (4 * ((mHi : ℝ) + 1)) ≤ Ctot)
    (hCtot : (1 - (9567 / 10000) ^ 2) * ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) +
      (247 / 1000) * (1 / (8 * 46369) + 16 / (16 * 46369 ^ 2)) ≤
      (1 - (9567 / 10000) ^ 2) * Ctot)
    {j0 K : ℕ} {tau : ℝ} (htau_lo : 6 * (4794 / 10 ^ 8) ≤ tau)
    (ht_tau : max (Real.cos φ' - γ) 0 / Real.sin φ' ≤ tau)
    (hu0_lo : tau ≤ (j0 : ℝ) * (π / 65536) - φ')
    (huK_hi : ((j0 : ℝ) * (π / 65536) - φ') + (K : ℝ) * (π / 65536) ≤ 7 / 10)
    {q : Fin (2 ^ 16) → ℂ}
    (hq : q = (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) :
    let c0 := Real.cos φ'; let s0 := Real.sin φ'; let d := max (c0 - γ) 0
    let Ibin : Finset (Fin (2 ^ 16)) := Finset.univ.filter fun y ↦ j0 ≤ y.val ∧ y.val ≤ j0 + K
    ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
          (max |Real.cos (qpeAngle 16 y / 2)| γ - max c0 γ) ^ 2 +
        ∑ y ∈ Ibin, Complex.normSq (q y) *
          (clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2) ≤
      s0 ^ 2 * Ctot * (π / ((M : ℝ) + 1)) ^ 2 := by
  intro c0 s0 d Ibin
  let du := π / 65536; let u0 := (j0 : ℝ) * du - φ'; let t := d / s0
  change tau ≤ u0 at hu0_lo
  change u0 + (K : ℝ) * du ≤ 7 / 10 at huK_hi
  have hpi_lo := Real.pi_gt_d20; have hpi_hi := Real.pi_lt_d20
  have hdu0 : 0 < du := by dsimp [du]; positivity
  have hd_eq : max c0 γ - γ = d := by
    dsimp [d]; rcases le_total c0 γ with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
  have hpt_all (y : Fin (2 ^ 16)) :
      let uy := (qpeAngle 16 y - 2 * φ') / 2
      (max |Real.cos (qpeAngle 16 y / 2)| γ - max c0 γ) ^ 2 +
        (if y ∈ Ibin then clampedMajorant s0 c0 uy - d ^ 2 else 0) ≤
        clampedMajorant s0 c0 uy := by
    intro uy
    have hmaj : (max |Real.cos (φ' + uy)| γ - max c0 γ) ^ 2 ≤ clampedMajorant s0 c0 uy :=
      clamped_majorant_le hγlo hγhi hc0lo hc0hi hs0_nn uy
    rw [show φ' + uy = qpeAngle 16 y / 2 by dsimp [uy]; ring] at hmaj
    split_ifs with hy
    · obtain ⟨hy1, hy2⟩ := (Finset.mem_filter.mp hy).2
      have huy_eq : uy = u0 + ((y.val - j0 : ℕ) : ℝ) * du := by
        dsimp [uy, qpeAngle, u0, du]; rw [Nat.cast_sub hy1]; field_simp; ring
      have huy_lo : tau ≤ uy := by
        rw [huy_eq]
        have := mul_nonneg (Nat.cast_nonneg (y.val - j0)) hdu0.le
        linarith only [hu0_lo, this]
      have huy_hi : uy ≤ 7 / 10 := by
        rw [huy_eq]
        have hleK : ((y.val - j0 : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : y.val - j0 ≤ K)
        have := mul_le_mul_of_nonneg_right hleK hdu0.le
        linarith only [huK_hi, this]
      have huy_pos : 0 < uy := by linarith only [htau_lo, huy_lo]
      have hcos_pos : 0 ≤ Real.cos (qpeAngle 16 y / 2) := by
        rw [show qpeAngle 16 y / 2 = φ' + uy by dsimp [uy]; ring]
        exact Real.cos_nonneg_of_mem_Icc
          ⟨by linarith only [hφ0, huy_pos, hpi_lo], by linarith only [hφ_hi, huy_hi, hpi_lo]⟩
      have hcos_le : Real.cos (qpeAngle 16 y / 2) ≤ γ := by
        rw [show qpeAngle 16 y / 2 = φ' + uy by dsimp [uy]; ring, Real.cos_add]
        have hs_lo := Real.sin_gt_sub_cube huy_pos
        by_cases huy_small : uy ≤ 1 / 50
        · have huy2_le : uy ^ 2 ≤ (1 / 50) ^ 2 := pow_le_pow_left₀ huy_pos.le huy_small 2
          have hcy : Real.cos uy ≤ 1 - uy ^ 2 / 2 + uy ^ 4 / 24 := by
            have hh := Real.sin_gt_sub_cube (by linarith only [huy_pos] : 0 < uy / 2)
            have hc2 := Real.cos_two_mul (uy / 2)
            rw [show 2 * (uy / 2) = uy by ring] at hc2
            have hs2 : 0 ≤ uy / 2 - (uy / 2) ^ 3 / 6 := by
              rw [show uy / 2 - (uy / 2) ^ 3 / 6 = (uy / 48) * (24 - uy ^ 2) by ring]
              exact mul_nonneg (by linarith only [huy_pos]) (by linarith only [huy2_le])
            have hsq := pow_le_pow_left₀ hs2 hh.le 2
            have hsc := Real.sin_sq_add_cos_sq (uy / 2)
            have hge : uy ^ 2 / 4 - uy ^ 4 / 48 ≤ (uy / 2 - (uy / 2) ^ 3 / 6) ^ 2 := by
              have hid : (uy / 2 - (uy / 2) ^ 3 / 6) ^ 2 - (uy ^ 2 / 4 - uy ^ 4 / 48) =
                  uy ^ 6 / 2304 := by ring
              linarith only [hid, show 0 ≤ uy ^ 6 / 2304 by positivity]
            linarith only [hc2, hsc, hsq, hge]
          have hsy : uy - uy ^ 3 / 6 ≤ Real.sin uy := hs_lo.le
          have htd : t * s0 = d := div_mul_cancel₀ d (ne_of_gt (by linarith only [hs0_lo]))
          have h1 : c0 * Real.cos uy - s0 * Real.sin uy ≤
              c0 * (1 - uy ^ 2 / 2 + uy ^ 4 / 24) - s0 * (uy - uy ^ 3 / 6) := by
            have hc1 := mul_le_mul_of_nonneg_left hcy (by linarith only [hc0_lo] : 0 ≤ c0)
            have hs1 := mul_le_mul_of_nonneg_left hsy hs0_nn
            linarith only [hc1, hs1]
          have h2 : c0 * (1 - uy ^ 2 / 2 + uy ^ 4 / 24) - s0 * (uy - uy ^ 3 / 6) ≤ c0 - d := by
            have ht_uy : t ≤ uy := ht_tau.trans huy_lo
            have hdt : d ≤ s0 * uy := by
              rw [← htd]; have := mul_le_mul_of_nonneg_right ht_uy hs0_nn
              linarith only [this, show t * s0 = s0 * t by ring]
            have hrem : 0 ≤ uy ^ 2 * (c0 / 2 - c0 * uy ^ 2 / 24 - s0 * uy / 6) := by
              refine mul_nonneg (sq_nonneg uy) ?_
              nlinarith only [hc0_lo, hc0_hi, hs0_hi, huy_pos, huy_small, huy2_le]
            linarith only [hdt, hrem,
              show c0 - d - (c0 * (1 - uy ^ 2 / 2 + uy ^ 4 / 24) - s0 * (uy - uy ^ 3 / 6)) =
                (s0 * uy - d) + uy ^ 2 * (c0 / 2 - c0 * uy ^ 2 / 24 - s0 * uy / 6) by ring]
          have hcd : c0 - d ≤ γ := by dsimp [d]; linarith only [le_max_left (c0 - γ) 0]
          dsimp [c0, s0] at h1 h2 hcd; linarith only [h1, h2, hcd]
        · push Not at huy_small
          have hsy : 18 / 1000 ≤ Real.sin uy := by
            have huy2 : uy ^ 2 ≤ (7 / 10) ^ 2 := pow_le_pow_left₀ huy_pos.le huy_hi 2
            have h1 : uy * (1 - (7 / 10) ^ 2 / 6) ≤ uy - uy ^ 3 / 6 := by
              rw [← sub_nonneg, show uy - uy ^ 3 / 6 - uy * (1 - (7 / 10) ^ 2 / 6) =
                (uy / 6) * ((7 / 10) ^ 2 - uy ^ 2) by ring]
              exact mul_nonneg (by positivity) (sub_nonneg.mpr huy2)
            linarith only [hs_lo, h1, huy_small]
          have hcy : Real.cos uy ≤ 1 := Real.cos_le_one uy
          have hc1 : c0 * Real.cos uy ≤ c0 :=
            (mul_le_mul_of_nonneg_left hcy (by linarith only [hc0_lo])).trans_eq (mul_one c0)
          have hs1 : (29 / 100) * (18 / 1000) ≤ s0 * Real.sin uy :=
            mul_le_mul hs0_lo hsy (by norm_num) hs0_nn
          dsimp [c0, s0] at hc1 hs1 hc0hi ⊢
          linarith only [hc1, hs1, hc0hi]
      rw [abs_of_nonneg hcos_pos, max_eq_right hcos_le,
        show (γ - max c0 γ) ^ 2 = (max c0 γ - γ) ^ 2 by ring, hd_eq]
      linarith only
    · linarith only [hmaj]
  have htot_sum : ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
        (max |Real.cos (qpeAngle 16 y / 2)| γ - max c0 γ) ^ 2 +
      ∑ y ∈ Ibin, Complex.normSq (q y) *
        (clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2) ≤
      ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
        clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) := by
    have hrew : ∑ y ∈ Ibin, Complex.normSq (q y) *
          (clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2) =
        ∑ y : Fin (2 ^ 16), Complex.normSq (q y) *
          (if y ∈ Ibin then clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2
            else 0) := by
      rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun y _ ↦ ?_
      simp only [Ibin, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> ring
    rw [hrew, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hpt_all y) (Complex.normSq_nonneg _)
  refine htot_sum.trans ?_
  have hmom := sineWindow_moments hMlo (hMhi.trans hmHi_ub) (2 * φ')
  dsimp only at hmom; rw [← hq] at hmom
  have hsplit : ∑ y : Fin (2 ^ 16),
        Complex.normSq (q y) * clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) =
      s0 ^ 2 * (∑ y, Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - 2 * φ') / 2) ^ 2) +
      (247 / 1000) * (∑ y, Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - 2 * φ') / 2) ^ 4) +
      s0 * c0 * (∑ y, Complex.normSq (q y) *
        (Real.sin ((qpeAngle 16 y - 2 * φ') / 2) ^ 3 *
          Real.cos ((qpeAngle 16 y - 2 * φ') / 2))) := by
    simp only [clampedMajorant, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hsplit, hmom.2.1, mul_zero, add_zero]
  let P2 := (π / ((M : ℝ) + 1)) ^ 2
  have hL_ge : (46369 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (46368 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMlo
    linarith only [this]
  have hm1 : (M : ℝ) / ((M : ℝ) + 1) ≤ (mHi : ℝ) / ((mHi : ℝ) + 1) := by
    rw [div_le_div_iff₀ (Nat.cast_add_one_pos M) (Nat.cast_add_one_pos mHi)]
    have hMle : (M : ℝ) ≤ mHi := by exact_mod_cast hMhi
    linarith only [hMle,
      show (M : ℝ) * ((mHi : ℝ) + 1) - (mHi : ℝ) * ((M : ℝ) + 1) = (M : ℝ) - mHi by ring]
  have hs2_ub : ∑ y, Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - 2 * φ') / 2) ^ 2 ≤
      ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) * P2 := by
    refine hmom.2.2.1.trans ?_
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm1 (sq_nonneg _))
      (by norm_num)).trans_eq
      (by rw [mul_comm _ P2, mul_div_assoc, div_div, mul_comm ((mHi : ℝ) + 1) 4, mul_comm P2])
  have hs4_ub : ∑ y, Complex.normSq (q y) * Real.sin ((qpeAngle 16 y - 2 * φ') / 2) ^ 4 ≤
      (1 / (8 * 46369) + 16 / (16 * 46369 ^ 2)) * P2 := by
    refine hmom.2.2.2.trans ?_
    have hpL : P2 ≤ 16 / 46369 ^ 2 := by
      have hdiv : π / ((M : ℝ) + 1) ≤ 4 / 46369 :=
        div_le_div₀ (by norm_num) (by linarith only [hpi_hi]) (by norm_num) hL_ge
      have hsq := pow_le_pow_left₀ (by positivity) hdiv 2
      dsimp only [P2]; linarith only [hsq, show (4 / 46369 : ℝ) ^ 2 = 16 / 46369 ^ 2 by norm_num]
    have h1L : 1 / (8 * ((M : ℝ) + 1)) ≤ 1 / (8 * 46369) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hL_ge])
    exact mul_le_mul_of_nonneg_right (by dsimp only [P2] at hpL; linarith only [h1L, hpL])
      (sq_nonneg _)
  have hcomb : s0 ^ 2 * ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) +
      (247 / 1000) * (1 / (8 * 46369) + 16 / (16 * 46369 ^ 2)) ≤ s0 ^ 2 * Ctot := by
    have hmul_s0 := mul_le_mul_of_nonneg_right hs0_sq_lo (sub_nonneg.mpr hCtot_ge)
    linarith only [hmul_s0, hCtot,
      show (1 - (9567 / 10000) ^ 2) * (Ctot - (mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) =
        (1 - (9567 / 10000) ^ 2) * Ctot -
          (1 - (9567 / 10000) ^ 2) * ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) by ring,
      show s0 ^ 2 * (Ctot - (mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) =
        s0 ^ 2 * Ctot - s0 ^ 2 * ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) by ring]
  have hsum1 := mul_le_mul_of_nonneg_left hs2_ub (sq_nonneg s0)
  have hsum2 := mul_le_mul_of_nonneg_left hs4_ub (by norm_num : (0 : ℝ) ≤ 247 / 1000)
  have hsum3 := mul_le_mul_of_nonneg_right hcomb (by dsimp only [P2]; positivity : 0 ≤ P2)
  dsimp only [P2] at hsum1 hsum2 hsum3
  linarith only [hsum1, hsum2, hsum3,
    show s0 ^ 2 * (((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) * (π / ((M : ℝ) + 1)) ^ 2) +
        (247 / 1000) * ((1 / (8 * 46369) + 16 / (16 * 46369 ^ 2)) * (π / ((M : ℝ) + 1)) ^ 2) =
      (s0 ^ 2 * ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) +
        (247 / 1000) * (1 / (8 * 46369) + 16 / (16 * 46369 ^ 2))) *
        (π / ((M : ℝ) + 1)) ^ 2 by ring,
    show (s0 ^ 2 * Ctot) * (π / ((M : ℝ) + 1)) ^ 2 =
      s0 ^ 2 * Ctot * (π / ((M : ℝ) + 1)) ^ 2 by ring]

private theorem quartet_ibin_sum_ge {M mHi : ℕ} {pref : ℝ} (hMlo : 46368 ≤ M) (hMhi : M ≤ mHi)
    (hmHi_ub : mHi ≤ 47488) (hpref0 : 0 ≤ pref)
    (hpref_rat : pref * (4 * (314159265358979323847 / 10 ^ 20) * ((mHi : ℝ) + 1)) ≤
      (1 - (2 / 46369) ^ 2 / 6) ^ 2)
    {φ' d tau : ℝ} (hs0_nn : 0 ≤ Real.sin φ') (hs0_lo : 29 / 100 ≤ Real.sin φ')
    (hs0_sq_hi : Real.sin φ' ^ 2 ≤ 995 / 10000) (hc0_nn : 0 ≤ Real.cos φ')
    (hd0 : 0 ≤ d) (htau_lo : 6 * (4794 / 10 ^ 8) ≤ tau) (ht_tau : d / Real.sin φ' ≤ tau)
    {j0 K : ℕ} (hK_ge : 4 ≤ K) (hj0K_lt : j0 + K < 2 ^ 16)
    (hu0_lo : tau ≤ (j0 : ℝ) * (π / 65536) - φ')
    (hu0_hi : (j0 : ℝ) * (π / 65536) - φ' ≤ tau + π / 65536)
    (huK_hi : ((j0 : ℝ) * (π / 65536) - φ') + (K : ℝ) * (π / 65536) ≤ 7 / 10)
    {q : Fin (2 ^ 16) → ℂ}
    (hq : q = (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) :
    let c0 := Real.cos φ'; let s0 := Real.sin φ'; let t := d / s0
    let du := π / 65536; let u0 := (j0 : ℝ) * du - φ'; let mu := (u0 - tau) / du
    let Ibin : Finset (Fin (2 ^ 16)) := Finset.univ.filter fun y ↦ j0 ≤ y.val ∧ y.val ≤ j0 + K
    pref * (π / ((M + 1 : ℕ) : ℝ)) ^ 2 *
        (mu * stencilPrim s0 c0 t (u0 + du) + (1 - mu) * stencilPrim s0 c0 t (u0 + 2 * du) -
          stencilPrim s0 c0 t (u0 + ((K - 1 : ℕ) : ℝ) * du)) ≤
      ∑ y ∈ Ibin, Complex.normSq (q y) *
        (clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2) := by
  intro c0 s0 t du u0 mu Ibin
  change tau ≤ u0 at hu0_lo
  change u0 ≤ tau + du at hu0_hi
  change u0 + (K : ℝ) * du ≤ 7 / 10 at huK_hi
  let L := M + 1
  have hpi_lo := Real.pi_gt_d20; have hpi_hi := Real.pi_lt_d20
  have hdu_lo : 4793 / 10 ^ 8 ≤ du := by dsimp [du]; linarith only [hpi_lo]
  have hdu_le : du ≤ 4794 / 10 ^ 8 := by dsimp [du]; linarith only [hpi_hi]
  have hdu0 : 0 < du := by linarith only [hdu_lo]
  have hs0_pos : 0 < s0 := by linarith only [hs0_lo]
  have ht0 : 0 ≤ t := div_nonneg hd0 hs0_nn
  have hmu0 : 0 ≤ mu := div_nonneg (by linarith only [hu0_lo]) hdu0.le
  have hmu1 : mu ≤ 1 := (div_le_one hdu0).mpr (by linarith only [hu0_hi])
  have hu0_eq : u0 = tau + mu * du := by
    dsimp [mu]; rw [div_mul_cancel₀ _ hdu0.ne']; ring
  let w0 := 1 / (8 * Real.sin ((L : ℝ) * du) ^ 2); let w1 := 1 / 2 - w0
  obtain ⟨⟨hw0_lo, hw0_hi⟩, hquart⟩ := quartet_weights hMlo (hMhi.trans hmHi_ub)
  let W : ℕ → ℝ := fun r ↦ if r = 0 ∨ r = 3 then w0 else w1
  let G (u : ℝ) : ℝ := s0 ^ 2 * (1 / u ^ 2 - t ^ 2 / u ^ 4) + s0 * c0 * gPoleSum u
  let C3 := t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2
  let Fe (x : ℝ) : ℝ := 1 / x - C3 / (3 * x ^ 3)
  let dF (x : ℝ) : ℝ := (stencilPrim s0 c0 t x - stencilPrim s0 c0 t (x + du)) / du
  let cseq (j : ℕ) : ℝ := if j = 0 then mu * dF (u0 + du) else dF (u0 + ((j : ℝ) + 1) * du)
  let yOf (k : ℕ) : Fin (2 ^ 16) := ⟨(j0 + k) % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩
  have hbin_k (k : ℕ) (hk : k ≤ K) :
      let uk := u0 + (k : ℝ) * du
      (1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 * Real.cos ((L : ℝ) * uk) ^ 2 *
        (∑ r ∈ Finset.range 4, if r ≤ k then W r * cseq (k - r) else 0) ≤
        Complex.normSq (q (yOf k)) *
          (clampedMajorant s0 c0 ((qpeAngle 16 (yOf k) - 2 * φ') / 2) - d ^ 2) := by
    intro uk
    have hyval : (yOf k).val = j0 + k := Nat.mod_eq_of_lt (by omega)
    have huy : (qpeAngle 16 (yOf k) - 2 * φ') / 2 = uk := by
      dsimp [qpeAngle, uk, u0, du]; rw [hyval]; push_cast; field_simp; ring
    rw [huy]
    have huk_lo : tau ≤ uk := by
      dsimp [uk]; have := mul_nonneg (Nat.cast_nonneg k) hdu0.le; linarith only [hu0_lo, this]
    have huk_hi : uk ≤ 7 / 10 := by
      dsimp [uk]
      have hleK : (k : ℝ) ≤ K := by exact_mod_cast hk
      have := mul_le_mul_of_nonneg_right hleK hdu0.le
      linarith only [huK_hi, this]
    have hd_uk : d ≤ s0 * uk := by
      have hdt : d = s0 * t := (mul_div_cancel₀ d hs0_pos.ne').symm
      rw [hdt]; exact mul_le_mul_of_nonneg_left (ht_tau.trans huk_lo) hs0_nn
    have hDG_raw := D_to_G_le hMlo hs0_lo hs0_sq_hi hc0_nn hd0 hd_uk
      (htau_lo.trans huk_lo) huk_hi
    dsimp only at hDG_raw
    obtain ⟨_, hcos_pos, hDG⟩ := hDG_raw
    have hside := sineWindow_sidelobe_eq (hMhi.trans hmHi_ub) (2 * φ') (yOf k)
    dsimp only at hside; rw [← hq, huy] at hside
    have hDG_q : (1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 *
        Real.cos ((L : ℝ) * uk) ^ 2 * G uk ≤
        Complex.normSq (q (yOf k)) * (clampedMajorant s0 c0 uk - d ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hDG (Complex.normSq_nonneg (q (yOf k)))
      have hlhs_eq : Complex.normSq (q (yOf k)) *
          (((Real.sin uk ^ 2 - Real.sin (π / (2 * (L : ℝ))) ^ 2) ^ 2 / Real.cos uk ^ 2) * G uk) =
          (1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 *
            Real.cos ((L : ℝ) * uk) ^ 2 * G uk := by
        calc Complex.normSq (q (yOf k)) *
              (((Real.sin uk ^ 2 - Real.sin (π / (2 * (L : ℝ))) ^ 2) ^ 2 / Real.cos uk ^ 2) * G uk)
            = ((Real.sin uk ^ 2 - Real.sin (π / (2 * (L : ℝ))) ^ 2) ^ 2 *
                Complex.normSq (q (yOf k))) / Real.cos uk ^ 2 * G uk := by ring
          _ = (((1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 *
                Real.cos ((L : ℝ) * uk) ^ 2) * Real.cos uk ^ 2) / Real.cos uk ^ 2 * G uk := by
              rw [hside]; ring
          _ = _ := by rw [mul_div_cancel_right₀ _ hcos_pos.ne']
      dsimp only [clampedMajorant]; dsimp only [G, L] at hlhs_eq ⊢
      rw [hlhs_eq] at hmul; exact hmul
    have hsten : (∑ r ∈ Finset.range 4, if r ≤ k then W r * cseq (k - r) else 0) ≤ G uk := by
      have hu0_6du : 6 * du ≤ u0 := by linarith only [hdu_le, htau_lo, hu0_lo]
      have he := even_stencil_le hdu0 hdu_le ht0 (by rw [hu0_eq]; linarith only [ht_tau])
        hu0_6du hw0_lo hw0_hi hmu0 hmu1 k
      have hp := pole_stencil_le hdu0 hdu_le hu0_6du hw0_lo hw0_hi hmu0 hmu1 k
      dsimp only at he hp
      let dFe (x : ℝ) : ℝ := (Fe x - Fe (x + du)) / du
      let ce (j : ℕ) : ℝ := if j = 0 then mu * dFe (u0 + du) else dFe (u0 + ((j : ℝ) + 1) * du)
      let dFp (x : ℝ) : ℝ := (fPoleSum x - fPoleSum (x + du)) / du
      let cp (j : ℕ) : ℝ := if j = 0 then mu * dFp (u0 + du) else dFp (u0 + ((j : ℝ) + 1) * du)
      have hcseq_eq (j : ℕ) : cseq j = s0 ^ 2 * ce j + s0 * c0 * cp j := by
        dsimp [cseq, ce, cp, dF, dFe, dFp, stencilPrim, Fe, C3]; split_ifs <;> ring
      have hsplit_c : (∑ r ∈ Finset.range 4, if r ≤ k then W r * cseq (k - r) else 0) =
          s0 ^ 2 * (∑ r ∈ Finset.range 4, if r ≤ k then W r * ce (k - r) else 0) +
          s0 * c0 * (∑ r ∈ Finset.range 4, if r ≤ k then W r * cp (k - r) else 0) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        split_ifs
        · rw [hcseq_eq]; ring
        · ring
      rw [hsplit_c]; dsimp [G, ce, cp, dFe, dFp, Fe, C3, uk] at he hp ⊢
      exact add_le_add (mul_le_mul_of_nonneg_left he (sq_nonneg s0))
        (mul_le_mul_of_nonneg_left hp (mul_nonneg hs0_nn hc0_nn))
    exact (mul_le_mul_of_nonneg_left hsten (by positivity)).trans hDG_q
  have hcseq_nn (j : ℕ) : 0 ≤ cseq j := by
    have hdF_nn {x : ℝ} (hx : u0 + du ≤ x) : 0 ≤ dF x := by
      have hx0 : 0 < x := by linarith only [htau_lo, hu0_lo, hdu0, hx]
      have hCx : C3 ≤ x ^ 2 := by
        dsimp only [C3]
        rcases le_total t (4 * (4794 / 10 ^ 8)) with ht_sm | ht_lg
        · have ht2 : t ^ 2 ≤ (4 * (4794 / 10 ^ 8)) ^ 2 := pow_le_pow_left₀ ht0 ht_sm 2
          have hx2 : (6 * (4794 / 10 ^ 8)) ^ 2 ≤ x ^ 2 :=
            pow_le_pow_left₀ (by norm_num) (by linarith only [htau_lo, hu0_lo, hdu0, hx]) 2
          linarith only [ht2, hx2]
        · have hx_lo : t + 4793 / 10 ^ 8 ≤ x := by
            have ht_u0 : t ≤ u0 := ht_tau.trans hu0_lo
            linarith only [ht_u0, hdu_lo, hx]
          have hx2 : (t + 4793 / 10 ^ 8) ^ 2 ≤ x ^ 2 :=
            pow_le_pow_left₀ (by linarith only [ht0]) hx_lo 2
          linarith only [hx2, ht_lg,
            show (t + 4793 / 10 ^ 8) ^ 2 =
              t ^ 2 + 2 * (4793 / 10 ^ 8) * t + (4793 / 10 ^ 8) ^ 2 by ring]
      have hdFe_nn : 0 ≤ (Fe x - Fe (x + du)) / du := by
        dsimp [Fe]; apply div_nonneg _ hdu0.le
        have hsub : (1 / x - 1 / (x + du)) - x ^ 2 * (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) =
            x ^ 2 * du ^ 2 * (3 * x + 2 * du) / (3 * x ^ 3 * (x + du) ^ 3) := by
          field_simp; ring
        have hpos1 : 0 ≤ 1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0.le (by linarith only [hdu0]) 3)
              (by norm_num)))
        have hpos2 : 0 ≤ (1 / x - 1 / (x + du)) -
            x ^ 2 * (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) := by rw [hsub]; positivity
        have hmul := mul_le_mul_of_nonneg_right hCx hpos1
        linarith only [hpos2, hmul,
          show (1 / x - C3 / (3 * x ^ 3)) - (1 / (x + du) - C3 / (3 * (x + du) ^ 3)) =
            ((1 / x - 1 / (x + du)) - x ^ 2 * (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3))) +
              (x ^ 2 - C3) * (1 / (3 * x ^ 3) - 1 / (3 * (x + du) ^ 3)) by ring]
      have hdFp_nn : 0 ≤ (fPoleSum x - fPoleSum (x + du)) / du :=
        div_nonneg (sub_nonneg.mpr (fPoleSum_antitone hx0 (by linarith only [hdu0]))) hdu0.le
      have hrew : dF x = s0 ^ 2 * ((Fe x - Fe (x + du)) / du) +
          s0 * c0 * ((fPoleSum x - fPoleSum (x + du)) / du) := by
        dsimp [dF, stencilPrim, Fe, C3]; ring
      rw [hrew]
      exact add_nonneg (mul_nonneg (sq_nonneg s0) hdFe_nn)
        (mul_nonneg (mul_nonneg hs0_nn hc0_nn) hdFp_nn)
    dsimp [cseq]; split_ifs with hj
    · exact mul_nonneg hmu0 (hdF_nn le_rfl)
    · exact hdF_nn (by have := mul_nonneg (Nat.cast_nonneg j) hdu0.le; linarith only [this])
  have hW_nn (r : ℕ) : 0 ≤ W r := by dsimp [W, w1]; split_ifs <;> linarith only [hw0_lo, hw0_hi]
  have hquart_r (u : ℝ) :
      ∑ r ∈ Finset.range 4, W r * Real.cos ((L : ℝ) * (u + (r : ℝ) * du)) ^ 2 = 1 / 2 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, W, true_or,
      show ¬(1 = 0 ∨ 1 = 3) by omega, show ¬(2 = 0 ∨ 2 = 3) by omega, or_true, ↓reduceIte,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, add_zero, one_mul]
    exact hquart u
  have hswap : (1 / 2) * ∑ j ∈ Finset.range (K - 2), cseq j ≤
      ∑ k ∈ Finset.range (K + 1), Real.cos ((L : ℝ) * (u0 + (k : ℝ) * du)) ^ 2 *
        (∑ r ∈ Finset.range 4, if r ≤ k then W r * cseq (k - r) else 0) := by
    have h1 : (1 / 2) * ∑ j ∈ Finset.range (K - 2), cseq j =
        ∑ j ∈ Finset.range (K - 2), ∑ r ∈ Finset.range 4,
          cseq j * W r * Real.cos ((L : ℝ) * (u0 + ((j + r : ℕ) : ℝ) * du)) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hq4 := hquart_r (u0 + (j : ℝ) * du)
      calc (1 / 2) * cseq j = cseq j * (∑ r ∈ Finset.range 4,
              W r * Real.cos ((L : ℝ) * (u0 + (j : ℝ) * du + (r : ℝ) * du)) ^ 2) := by
            rw [hq4]; ring
        _ = _ := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [show u0 + ((j + r : ℕ) : ℝ) * du = u0 + (j : ℝ) * du + (r : ℝ) * du by
            push_cast; ring]
          ring
    rw [h1]
    have h2 : ∑ j ∈ Finset.range (K - 2), ∑ r ∈ Finset.range 4,
          cseq j * W r * Real.cos ((L : ℝ) * (u0 + ((j + r : ℕ) : ℝ) * du)) ^ 2 =
        ∑ k ∈ Finset.range (K + 1), ∑ r ∈ Finset.range 4,
          if r ≤ k ∧ k - r < K - 2 then
            Real.cos ((L : ℝ) * (u0 + (k : ℝ) * du)) ^ 2 * (W r * cseq (k - r)) else 0 := by
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hr4 := Finset.mem_range.mp hr
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun j _ ↦ j + r)
        (fun j hj ↦ by
          have := Finset.mem_range.mp hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega,
            by rw [Nat.add_sub_cancel]; omega⟩)
        (fun _ _ _ _ h ↦ by omega)
        (fun k hk ↦ by
          obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hk
          exact ⟨k - r, Finset.mem_range.mpr h2, Nat.sub_add_cancel h1⟩)
        fun j _ ↦ ?_
      rw [Nat.add_sub_cancel]; ring
    rw [h2]; refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [Finset.mul_sum]; refine Finset.sum_le_sum fun r _ ↦ ?_
    split_ifs with h1 h2
    · exact le_rfl
    · omega
    · exact mul_nonneg (sq_nonneg _) (mul_nonneg (hW_nn r) (hcseq_nn (k - r)))
    · simp
  have htel_c : ∑ j ∈ Finset.range (K - 2), cseq j =
      (mu * stencilPrim s0 c0 t (u0 + du) + (1 - mu) * stencilPrim s0 c0 t (u0 + 2 * du) -
        stencilPrim s0 c0 t (u0 + ((K - 1 : ℕ) : ℝ) * du)) / du := by
    obtain ⟨m, hm⟩ : ∃ m, K - 2 = m + 1 := ⟨K - 3, by omega⟩
    rw [hm, Finset.sum_range_succ']
    let S (i : ℕ) : ℝ := stencilPrim s0 c0 t (u0 + ((i : ℝ) + 2) * du)
    have hshift : ∑ i ∈ Finset.range m, cseq (i + 1) =
        (stencilPrim s0 c0 t (u0 + 2 * du) -
          stencilPrim s0 c0 t (u0 + ((K - 1 : ℕ) : ℝ) * du)) / du := by
      have hterm (i : ℕ) : cseq (i + 1) = (S i - S (i + 1)) / du := by
        simp only [cseq, dF, S, Nat.succ_ne_zero, ↓reduceIte]
        have h1 : u0 + (((i + 1 : ℕ) : ℝ) + 1) * du = u0 + ((i : ℝ) + 2) * du := by
          push_cast; ring
        have h2 : u0 + ((i : ℝ) + 2) * du + du = u0 + (((i + 1 : ℕ) : ℝ) + 2) * du := by
          push_cast; ring
        rw [h1, h2]
      simp_rw [hterm, ← Finset.sum_div, Finset.sum_range_sub']
      have hS0 : S 0 = stencilPrim s0 c0 t (u0 + 2 * du) := by
        dsimp only [S]; rw [Nat.cast_zero, zero_add]
      have hSm : S m = stencilPrim s0 c0 t (u0 + ((K - 1 : ℕ) : ℝ) * du) := by
        dsimp only [S]
        have hmK : (m : ℝ) + 2 = ((K - 1 : ℕ) : ℝ) := by
          have : m + 2 = K - 1 := by omega
          rw [← this]; push_cast; ring
        rw [hmK]
      rw [hS0, hSm]
    rw [hshift]; simp only [cseq, dF, ↓reduceIte]
    rw [show u0 + du + du = u0 + 2 * du by ring]; ring
  have hIbin_sum : (1 / ((π : ℝ) * L)) * Real.sin (π / (2 * (L : ℝ))) ^ 2 *
      (mu * stencilPrim s0 c0 t (u0 + du) + (1 - mu) * stencilPrim s0 c0 t (u0 + 2 * du) -
        stencilPrim s0 c0 t (u0 + ((K - 1 : ℕ) : ℝ) * du)) ≤
      ∑ y ∈ Ibin, Complex.normSq (q y) *
        (clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2) := by
    have hbij : ∑ k ∈ Finset.range (K + 1), Complex.normSq (q (yOf k)) *
          (clampedMajorant s0 c0 ((qpeAngle 16 (yOf k) - 2 * φ') / 2) - d ^ 2) =
        ∑ y ∈ Ibin, Complex.normSq (q y) *
          (clampedMajorant s0 c0 ((qpeAngle 16 y - 2 * φ') / 2) - d ^ 2) := by
      refine Finset.sum_bij (fun k _ ↦ yOf k)
        (fun k hk ↦ by
          have hk' := Finset.mem_range.mp hk
          have hv : (yOf k).val = j0 + k := Nat.mod_eq_of_lt (by omega)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by omega⟩)
        (fun k1 hk1 k2 hk2 h ↦ by
          have h1 := Finset.mem_range.mp hk1; have h2 := Finset.mem_range.mp hk2
          have hv := congrArg Fin.val h; dsimp [yOf] at hv
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega)
        (fun y hy ↦ by
          obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hy).2
          refine ⟨y.val - j0, Finset.mem_range.mpr (by omega), Fin.ext ?_⟩
          dsimp [yOf]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        fun _ _ ↦ rfl
    rw [← hbij]
    have hsum_k : (1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 *
          ∑ k ∈ Finset.range (K + 1), Real.cos ((L : ℝ) * (u0 + (k : ℝ) * du)) ^ 2 *
            (∑ r ∈ Finset.range 4, if r ≤ k then W r * cseq (k - r) else 0) ≤
        ∑ k ∈ Finset.range (K + 1), Complex.normSq (q (yOf k)) *
          (clampedMajorant s0 c0 ((qpeAngle 16 (yOf k) - 2 * φ') / 2) - d ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      simpa only [mul_assoc] using hbin_k k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have hc_nn : 0 ≤ (1 / (32768 * (L : ℝ))) * Real.sin (π / (2 * (L : ℝ))) ^ 2 :=
      mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by norm_num) (Nat.cast_nonneg L)))
        (sq_nonneg _)
    have hcomb := (mul_le_mul_of_nonneg_left hswap hc_nn).trans hsum_k
    have hpre_eq : (1 / ((π : ℝ) * L)) = (1 / (32768 * (L : ℝ))) * (1 / 2) * du⁻¹ := by
      dsimp only [du]; simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]; ring
    rw [htel_c] at hcomb
    refine le_trans (le_of_eq ?_) hcomb
    rw [hpre_eq, div_eq_mul_inv (_ - _)]; ring
  have hpref : pref * (π / (L : ℝ)) ^ 2 ≤
      (1 / ((π : ℝ) * L)) * Real.sin (π / (2 * (L : ℝ))) ^ 2 := by
    have hL_lo : (46369 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.succ_le_succ hMlo
    have hL_hi : (L : ℝ) ≤ (mHi : ℝ) + 1 := by
      have hMle : (M : ℝ) ≤ mHi := by exact_mod_cast hMhi
      dsimp [L]; push_cast; linarith only [hMle]
    let α := π / (2 * (L : ℝ))
    have hα_pos : 0 < α := by dsimp [α]; positivity
    have hα_hi : α ≤ 2 / 46369 := by
      dsimp [α]; rw [div_le_iff₀ (by positivity)]; linarith only [hpi_hi, hL_lo]
    have hs_lo : α * (1 - (2 / 46369) ^ 2 / 6) ≤ Real.sin α := by
      have hh := Real.sin_gt_sub_cube hα_pos
      have hα2 : α ^ 2 ≤ (2 / 46369) ^ 2 := pow_le_pow_left₀ hα_pos.le hα_hi 2
      have hsub : α * (1 - (2 / 46369) ^ 2 / 6) ≤ α - α ^ 3 / 6 := by
        rw [← sub_nonneg, show α - α ^ 3 / 6 - α * (1 - (2 / 46369) ^ 2 / 6) =
          (α / 6) * ((2 / 46369) ^ 2 - α ^ 2) by ring]
        exact mul_nonneg (by positivity) (sub_nonneg.mpr hα2)
      linarith only [hh, hsub]
    have hs2 : α ^ 2 * (1 - (2 / 46369) ^ 2 / 6) ^ 2 ≤ Real.sin α ^ 2 := by
      have := pow_le_pow_left₀ (mul_nonneg hα_pos.le (by norm_num)) hs_lo 2
      linarith only [this, show (α * (1 - (2 / 46369) ^ 2 / 6)) ^ 2 =
        α ^ 2 * (1 - (2 / 46369) ^ 2 / 6) ^ 2 by ring]
    have hpiL : (π : ℝ) * L ≤ (314159265358979323847 / 10 ^ 20) * ((mHi : ℝ) + 1) :=
      mul_le_mul (by linarith only [hpi_hi]) hL_hi (by positivity) (by norm_num)
    have h4piL := mul_le_mul_of_nonneg_left hpiL (mul_nonneg hpref0 (by norm_num : (0 : ℝ) ≤ 4))
    have h1 : pref * (4 * ((π : ℝ) * L)) ≤ (1 - (2 / 46369) ^ 2 / 6) ^ 2 := by
      linarith only [hpref_rat, h4piL,
        show pref * 4 * ((π : ℝ) * L) = pref * (4 * ((π : ℝ) * L)) by ring,
        show pref * 4 * ((314159265358979323847 / 10 ^ 20) * ((mHi : ℝ) + 1)) =
          pref * (4 * (314159265358979323847 / 10 ^ 20) * ((mHi : ℝ) + 1)) by ring]
    have h2 : α ^ 2 * (pref * (4 * ((π : ℝ) * L))) ≤ Real.sin α ^ 2 :=
      (mul_le_mul_of_nonneg_left h1 (sq_nonneg α)).trans hs2
    have h3 : α ^ 2 * (pref * (4 * ((π : ℝ) * L))) =
        pref * (π / (L : ℝ)) ^ 2 * ((π : ℝ) * L) := by
      dsimp only [α]; rw [← div_div]; ring
    rw [h3] at h2
    have hpiL_pos : (0 : ℝ) < (π : ℝ) * L := by positivity
    exact ((le_div_iff₀ hpiL_pos).mpr h2).trans_eq (by dsimp only [α]; ring)
  have hD_nn : 0 ≤ mu * stencilPrim s0 c0 t (u0 + du) +
      (1 - mu) * stencilPrim s0 c0 t (u0 + 2 * du) -
      stencilPrim s0 c0 t (u0 + ((K - 1 : ℕ) : ℝ) * du) := by
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (K - 2), cseq j :=
      Finset.sum_nonneg fun j _ ↦ hcseq_nn j
    rw [htel_c] at hsum_nn
    have := (le_div_iff₀ hdu0).mp hsum_nn
    linarith only [this]
  exact (mul_le_mul_of_nonneg_right hpref hD_nn).trans hIbin_sum

private theorem stencilPrim_conv_sub_ge {qMin s0 c0 t tau du mu uEnd : ℝ}
    (hs0_nn : 0 ≤ s0) (hc0_nn : 0 ≤ c0) (hq_min : qMin * s0 ≤ c0)
    (hdu_lo : 4793 / 10 ^ 8 ≤ du) (hdu_le : du ≤ 4794 / 10 ^ 8)
    (ht0 : 0 ≤ t) (ht_tau : t ≤ tau) (htau_lo : 6 * (4794 / 10 ^ 8) ≤ tau)
    (htau_hi : tau ≤ 83 / 20000) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (huEnd_lo : 69 / 100 ≤ uEnd) :
    let a_t := tau + 2 * (4794 / 10 ^ 8)
    s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
        100 / 69 + qMin * (fPoleSum a_t - fPoleSum uEnd)) ≤
      mu * stencilPrim s0 c0 t (tau + (1 + mu) * du) +
        (1 - mu) * stencilPrim s0 c0 t (tau + (2 + mu) * du) -
        stencilPrim s0 c0 t uEnd := by
  intro a_t
  let x1 := tau + (1 + mu) * du; let x2 := tau + (2 + mu) * du
  let C3 := t ^ 2 + 8 * (4794 / 10 ^ 8) ^ 2
  let Fe (x : ℝ) : ℝ := 1 / x - C3 / (3 * x ^ 3)
  have hdu0 : 0 < du := by linarith only [hdu_lo]
  have htau0 : 0 ≤ tau := by linarith only [htau_lo]
  have hx0_conv : mu * x1 + (1 - mu) * x2 = tau + 2 * du := by dsimp [x1, x2]; ring
  have hx0_le_at : tau + 2 * du ≤ a_t := by dsimp [a_t]; linarith only [hdu_le]
  have hat_pos : 0 < a_t := by dsimp [a_t]; linarith only [htau_lo]
  have hjen_inv {s : ℝ} (hs : 0 ≤ s) :
      1 / (a_t + s) ≤ mu / (x1 + s) + (1 - mu) / (x2 + s) := by
    have hp1 : 0 < x1 + s := by
      dsimp [x1]; have := mul_pos (by linarith only [hmu0] : 0 < 1 + mu) hdu0
      linarith only [htau0, this, hs]
    have hp2 : 0 < x2 + s := by
      dsimp [x2]; have := mul_pos (by linarith only [hmu0] : 0 < 2 + mu) hdu0
      linarith only [htau0, this, hs]
    have hp0 : 0 < tau + 2 * du + s := by linarith only [htau0, hdu0, hs]
    have h1 : 1 / (a_t + s) ≤ 1 / (tau + 2 * du + s) :=
      one_div_le_one_div_of_le hp0 (by linarith only [hx0_le_at])
    have h2 : 0 ≤ (mu / (x1 + s) + (1 - mu) / (x2 + s)) - 1 / (tau + 2 * du + s) := by
      have hid : (mu / (x1 + s) + (1 - mu) / (x2 + s)) - 1 / (tau + 2 * du + s) =
          mu * (1 - mu) * (x2 - x1) ^ 2 / ((x1 + s) * (x2 + s) * (tau + 2 * du + s)) := by
        have hconv : tau + 2 * du + s = mu * (x1 + s) + (1 - mu) * (x2 + s) := by
          linarith only [hx0_conv]
        have hp0' : mu * (x1 + s) + (1 - mu) * (x2 + s) ≠ 0 := by linarith only [hp0, hconv]
        rw [hconv]; field_simp [hp1.ne', hp2.ne', hp0']; ring
      rw [hid]; have : 0 ≤ 1 - mu := by linarith only [hmu1]
      positivity
    linarith only [h1, h2]
  have hFe_lb : 1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) - 100 / 69 ≤
      mu * Fe x1 + (1 - mu) * Fe x2 - Fe uEnd := by
    have hc3 := cubic_conv_le hdu_lo hdu_le ht0 ht_tau htau_lo hmu0 hmu1
    dsimp only at hc3
    have h1 := hjen_inv (s := 0) le_rfl
    simp only [add_zero] at h1
    have huEnd_ub : Fe uEnd ≤ 100 / 69 := by
      dsimp [Fe]
      have huEnd_pos : 0 < uEnd := by linarith only [huEnd_lo]
      have hpos : 0 ≤ C3 / (3 * uEnd ^ 3) := by dsimp [C3]; positivity
      have hinv : 1 / uEnd ≤ 100 / 69 := by
        rw [div_le_div_iff₀ huEnd_pos (by norm_num)]; linarith only [huEnd_lo]
      linarith only [hpos, hinv]
    change C3 * (mu / x1 ^ 3 + (1 - mu) / x2 ^ 3) ≤
      (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / a_t ^ 3 at hc3
    change 1 / a_t ≤ mu / x1 + (1 - mu) / x2 at h1
    dsimp only [Fe] at huEnd_ub ⊢
    have hr1 : mu * (1 / x1 - C3 / (3 * x1 ^ 3)) + (1 - mu) * (1 / x2 - C3 / (3 * x2 ^ 3)) =
        (mu / x1 + (1 - mu) / x2) - (1 / 3) * (C3 * (mu / x1 ^ 3 + (1 - mu) / x2 ^ 3)) := by
      rw [← div_div C3 3 (x1 ^ 3), ← div_div C3 3 (x2 ^ 3)]; ring
    have hr2 : (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) =
        (1 / 3) * ((5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / a_t ^ 3) := by
      rw [← div_div _ 3 (a_t ^ 3)]; ring
    linarith only [hc3, h1, huEnd_ub, hr1, hr2]
  have hfP_lb : fPoleSum a_t - fPoleSum uEnd ≤
      mu * fPoleSum x1 + (1 - mu) * fPoleSum x2 - fPoleSum uEnd :=
    sub_le_sub_right (fPoleSum_conv_ge hjen_inv) _
  have hpole_nn : 0 ≤ fPoleSum a_t - fPoleSum uEnd :=
    sub_nonneg.mpr (fPoleSum_antitone hat_pos (by dsimp [a_t]; linarith only [htau_hi, huEnd_lo]))
  have hc0_s0 : s0 ^ 2 * qMin ≤ s0 * c0 := by
    have := mul_le_mul_of_nonneg_left hq_min hs0_nn
    linarith only [this, show s0 * (qMin * s0) = s0 ^ 2 * qMin by ring]
  have hm1 := mul_le_mul_of_nonneg_left hFe_lb (sq_nonneg s0)
  have hm2 := mul_le_mul hc0_s0 hfP_lb hpole_nn (mul_nonneg hs0_nn hc0_nn)
  dsimp only [stencilPrim]; change _ ≤ mu * (s0 ^ 2 * Fe x1 + s0 * c0 * fPoleSum x1) +
    (1 - mu) * (s0 ^ 2 * Fe x2 + s0 * c0 * fPoleSum x2) -
    (s0 ^ 2 * Fe uEnd + s0 * c0 * fPoleSum uEnd)
  linarith only [hm1, hm2,
    show s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
        100 / 69 + qMin * (fPoleSum a_t - fPoleSum uEnd)) =
      s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) - 100 / 69) +
        (s0 ^ 2 * qMin) * (fPoleSum a_t - fPoleSum uEnd) by ring,
    show mu * (s0 ^ 2 * Fe x1 + s0 * c0 * fPoleSum x1) +
        (1 - mu) * (s0 ^ 2 * Fe x2 + s0 * c0 * fPoleSum x2) -
        (s0 ^ 2 * Fe uEnd + s0 * c0 * fPoleSum uEnd) =
      s0 ^ 2 * (mu * Fe x1 + (1 - mu) * Fe x2 - Fe uEnd) +
        (s0 * c0) * (mu * fPoleSum x1 + (1 - mu) * fPoleSum x2 - fPoleSum uEnd) by ring]

private theorem regime2_3b_algebraic_closure {qMin Ctot pref kap γ c0 s0 uEnd mse ibinSum p2 : ℝ}
    (hq_nn : 0 ≤ qMin) (hpref0 : 0 ≤ pref) (_hkap0 : 0 ≤ kap)
    (hγlo : 949 / 1000 ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hc0lo : γ - 1 / 20000 ≤ c0)
    (hs0_pos : 0 < s0) (hc0s0 : c0 ^ 2 + s0 ^ 2 = 1) (hq_min : qMin * s0 ≤ c0)
    (ht_hi : max (c0 - γ) 0 / s0 ≤ 83 / 20000) (huEnd_lo : 69 / 100 ≤ uEnd) (hp2 : 0 ≤ p2)
    (h3A_0 :
      let a3A : ℝ := 8 * (4794 / 10 ^ 8)
      let B0 := 1 / a3A - (5001 / 5000) * (276 / 10 ^ 10) / (3 * a3A ^ 3) - 100 / 69 +
        qMin * (67921 / 10000 - (12138773 / 10000) * a3A)
      0 ≤ Ctot - pref * B0 ∧ (1002 / 1000) * (Ctot - pref * B0) ≤ (1 / 4) * kap ^ 2)
    (h3A_hi :
      let a3A : ℝ := 8 * (4794 / 10 ^ 8)
      let Bhi := 1 / a3A - (5001 / 5000) * ((6 * (4794 / 10 ^ 8)) ^ 2 + 276 / 10 ^ 10) /
          (3 * a3A ^ 3) - 100 / 69 + qMin * (67921 / 10000 - (12138773 / 10000) * a3A)
      Ctot - pref * Bhi ≤ (1 / 4) * kap ^ 2)
    (hQ5_cert : ∀ {t : ℝ}, 6 * (4794 / 10 ^ 8) ≤ t → t ≤ 83 / 20000 →
      ∃ a0 F0 F1 : ℝ, 0 < a0 ∧ F0 ≤ fPoleTan0 a0 ∧ fPoleTan1 a0 ≤ F1 ∧
        0 ≤ qDeg5Poly ((1 / 4) * kap ^ 2) Ctot pref qMin F0 F1 t)
    (htot : mse + ibinSum ≤ s0 ^ 2 * Ctot * p2)
    (hibin_lb :
      let t := max (c0 - γ) 0 / s0
      let a_t := max t (6 * (4794 / 10 ^ 8)) + 2 * (4794 / 10 ^ 8)
      pref * p2 *
          (s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
            100 / 69 + qMin * (fPoleSum a_t - fPoleSum uEnd))) ≤ ibinSum) :
    mse ≤ (1 / 4) * kap ^ 2 * (1 - γ ^ 2) * p2 := by
  dsimp only at hibin_lb h3A_0 h3A_hi
  let d := max (c0 - γ) 0; let t := d / s0; let du_hi : ℝ := 4794 / 10 ^ 8
  let tau := max t (6 * du_hi); let a_t := tau + 2 * du_hi
  have ht0 : 0 ≤ t := div_nonneg (le_max_right _ _) hs0_pos.le
  have hat_pos : 0 < a_t := by
    have : 6 * du_hi ≤ tau := le_max_right _ _
    dsimp [a_t, du_hi] at *; linarith only [this]
  have hγ2 : γ ^ 2 ≤ (9555 / 10000) ^ 2 := pow_le_pow_left₀ (by linarith only [hγlo]) hγhi 2
  have hgam_nn : 0 ≤ 1 - γ ^ 2 := by linarith only [hγ2]
  have hkapQ_nn : 0 ≤ (1 / 4) * kap ^ 2 := by positivity
  change pref * p2 *
      (s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
        100 / 69 + qMin * (fPoleSum a_t - fPoleSum uEnd))) ≤ ibinSum at hibin_lb
  rcases le_total t (6 * du_hi) with ht3A | ht3B
  · have htau_eq : tau = 6 * du_hi := max_eq_right ht3A
    have hat_eq : a_t = 8 * (4794 / 10 ^ 8) := by dsimp [a_t, du_hi]; rw [htau_eq]; ring
    have htan := fPoleSum_sub_ge_tan (a := a_t) (uEnd := uEnd) (a0 := 11 / 20000) hat_pos
      (by norm_num) huEnd_lo
    have hF0 : (67921 / 10000 : ℝ) ≤ fPoleTan0 (11 / 20000) := by unfold fPoleTan0; norm_num
    have hF1 : fPoleTan1 (11 / 20000) ≤ 12138773 / 10000 := by unfold fPoleTan1; norm_num
    let B3A := 1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
      100 / 69 + qMin * (67921 / 10000 - (12138773 / 10000) * a_t)
    have hsav : pref * p2 * (s0 ^ 2 * B3A) ≤ ibinSum := by
      have htan' : 67921 / 10000 - (12138773 / 10000) * a_t ≤ fPoleSum a_t - fPoleSum uEnd := by
        have := mul_le_mul_of_nonneg_right hF1 hat_pos.le
        linarith only [htan, hF0, this]
      have h1 : s0 ^ 2 * B3A ≤
          s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
            100 / 69 + qMin * (fPoleSum a_t - fPoleSum uEnd)) := by
        dsimp only [B3A]
        exact mul_le_mul_of_nonneg_left
          (by linarith only [mul_le_mul_of_nonneg_left htan' hq_nn]) (sq_nonneg s0)
      exact (mul_le_mul_of_nonneg_left h1 (mul_nonneg hpref0 hp2)).trans hibin_lb
    have hmse_le : mse ≤ s0 ^ 2 * (Ctot - pref * B3A) * p2 := by
      linarith only [htot, hsav,
        show s0 ^ 2 * (Ctot - pref * B3A) * p2 =
          s0 ^ 2 * Ctot * p2 - pref * p2 * (s0 ^ 2 * B3A) by ring]
    refine hmse_le.trans ?_
    rcases le_total c0 γ with hc0_lt | hc0_ge
    · have hd_zero : d = 0 := max_eq_right (by linarith only [hc0_lt])
      have ht_zero : t = 0 := by dsimp [t]; rw [hd_zero, zero_div]
      have hs0_gam : s0 ^ 2 ≤ (1002 / 1000) * (1 - γ ^ 2) := by
        have hc0_sq : (γ - 1 / 20000) ^ 2 ≤ c0 ^ 2 :=
          pow_le_pow_left₀ (by linarith only [hγlo]) hc0lo 2
        linarith only [hc0s0, hc0_sq, hγhi, hγ2,
          show (γ - 1 / 20000) ^ 2 = γ ^ 2 - γ / 10000 + 1 / 400000000 by ring]
      have hB_eq : B3A = 1 / (8 * (4794 / 10 ^ 8)) -
          (5001 / 5000) * (276 / 10 ^ 10) / (3 * (8 * (4794 / 10 ^ 8)) ^ 3) - 100 / 69 +
          qMin * (67921 / 10000 - (12138773 / 10000) * (8 * (4794 / 10 ^ 8))) := by
        dsimp [B3A]; rw [hat_eq, ht_zero]; ring
      have hpos_m : 0 ≤ Ctot - pref * B3A := by rw [hB_eq]; exact h3A_0.1
      have hcoef : (1002 / 1000) * (Ctot - pref * B3A) ≤ (1 / 4) * kap ^ 2 := by
        rw [hB_eq]; exact h3A_0.2
      have h1 := mul_le_mul_of_nonneg_right hs0_gam hpos_m
      have h2 := mul_le_mul_of_nonneg_right hcoef hgam_nn
      have h3 : s0 ^ 2 * (Ctot - pref * B3A) ≤ (1 / 4) * kap ^ 2 * (1 - γ ^ 2) := by
        linarith only [h1, h2,
          show (1002 / 1000) * (1 - γ ^ 2) * (Ctot - pref * B3A) =
            (1002 / 1000) * (Ctot - pref * B3A) * (1 - γ ^ 2) by ring]
      exact mul_le_mul_of_nonneg_right h3 hp2
    · have hs0_gam : s0 ^ 2 ≤ 1 - γ ^ 2 := by
        have := pow_le_pow_left₀ (by linarith only [hγlo]) hc0_ge 2
        linarith only [hc0s0, this]
      have ht2_le : t ^ 2 ≤ (6 * (4794 / 10 ^ 8)) ^ 2 := pow_le_pow_left₀ ht0 ht3A 2
      have hB_ge : 1 / (8 * (4794 / 10 ^ 8)) -
          (5001 / 5000) * ((6 * (4794 / 10 ^ 8)) ^ 2 + 276 / 10 ^ 10) /
            (3 * (8 * (4794 / 10 ^ 8)) ^ 3) - 100 / 69 +
          qMin * (67921 / 10000 - (12138773 / 10000) * (8 * (4794 / 10 ^ 8))) ≤ B3A := by
        dsimp [B3A]; rw [hat_eq]
        have hdiv : (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * (8 * (4794 / 10 ^ 8)) ^ 3) ≤
            (5001 / 5000) * ((6 * (4794 / 10 ^ 8)) ^ 2 + 276 / 10 ^ 10) /
              (3 * (8 * (4794 / 10 ^ 8)) ^ 3) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [ht2_le])
            (by norm_num)) (by positivity)
        linarith only [hdiv]
      have hcoef : Ctot - pref * B3A ≤ (1 / 4) * kap ^ 2 := by
        linarith only [h3A_hi, mul_le_mul_of_nonneg_left hB_ge hpref0]
      have h3 : s0 ^ 2 * (Ctot - pref * B3A) ≤ (1 / 4) * kap ^ 2 * (1 - γ ^ 2) := by
        by_cases hp : 0 ≤ Ctot - pref * B3A
        · exact (mul_le_mul hs0_gam hcoef hp hgam_nn).trans_eq (by ring)
        · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith only [hp])).trans
            (mul_nonneg hkapQ_nn hgam_nn)
      exact mul_le_mul_of_nonneg_right h3 hp2
  · have htau_eq : tau = t := max_eq_left ht3B
    have hat_eq : a_t = t + 2 * (4794 / 10 ^ 8) := by dsimp [a_t, du_hi]; rw [htau_eq]
    obtain ⟨a0, F0, F1, ha0, hF0, hF1, hQ5⟩ := hQ5_cert ht3B ht_hi
    have htan := fPoleSum_sub_ge_tan hat_pos ha0 huEnd_lo
    let B3B := 1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
      100 / 69 + qMin * (F0 - F1 * a_t)
    have hsav : pref * p2 * (s0 ^ 2 * B3B) ≤ ibinSum := by
      have htan' : F0 - F1 * a_t ≤ fPoleSum a_t - fPoleSum uEnd := by
        have := mul_le_mul_of_nonneg_right hF1 hat_pos.le
        linarith only [htan, hF0, this]
      have h1 : s0 ^ 2 * B3B ≤
          s0 ^ 2 * (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) -
            100 / 69 + qMin * (fPoleSum a_t - fPoleSum uEnd)) := by
        dsimp only [B3B]
        exact mul_le_mul_of_nonneg_left
          (by linarith only [mul_le_mul_of_nonneg_left htan' hq_nn]) (sq_nonneg s0)
      exact (mul_le_mul_of_nonneg_left h1 (mul_nonneg hpref0 hp2)).trans hibin_lb
    have hmse_le : mse ≤ s0 ^ 2 * (Ctot - pref * B3B) * p2 := by
      linarith only [htot, hsav,
        show s0 ^ 2 * (Ctot - pref * B3B) * p2 =
          s0 ^ 2 * Ctot * p2 - pref * p2 * (s0 ^ 2 * B3B) by ring]
    refine hmse_le.trans ?_
    have hc0_gt : γ < c0 := by
      by_contra hle; push Not at hle
      have hd0' : d = 0 := max_eq_right (by linarith only [hle])
      have ht0' : t = 0 := by dsimp [t]; rw [hd0', zero_div]
      dsimp [du_hi] at ht3B; linarith only [ht3B, ht0']
    have hd_val : d = c0 - γ := max_eq_left (by linarith only [hc0_gt])
    have hgam_lb : 1 - c0 ^ 2 + 2 * c0 * d - d ^ 2 = 1 - γ ^ 2 := by rw [hd_val]; ring
    have h1_gam : s0 ^ 2 * (1 + 2 * qMin * t - t ^ 2) ≤ 1 - γ ^ 2 := by
      have hdt : d = s0 * t := (mul_div_cancel₀ d hs0_pos.ne').symm
      rw [← hgam_lb, show 1 - c0 ^ 2 = s0 ^ 2 by linarith only [hc0s0], hdt]
      have hm := mul_le_mul_of_nonneg_right hq_min (mul_nonneg hs0_pos.le ht0)
      linarith only [hm,
        show s0 ^ 2 + 2 * c0 * (s0 * t) - (s0 * t) ^ 2 -
            s0 ^ 2 * (1 + 2 * qMin * t - t ^ 2) =
          2 * (c0 * (s0 * t) - (qMin * s0) * (s0 * t)) by ring]
    have hB_q : Ctot - pref * B3B ≤ (1 / 4) * kap ^ 2 * (1 + 2 * qMin * t - t ^ 2) := by
      have h3a3 : 0 < 3 * a_t ^ 3 := by positivity
      have hB_mul : B3B * (3 * a_t ^ 3) = 3 * a_t ^ 2 -
          (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) +
          (-100 / 69 + qMin * (F0 - F1 * a_t)) * (3 * a_t ^ 3) := by
        have ha1 : (1 / a_t) * (3 * a_t ^ 3) = 3 * a_t ^ 2 := by
          rw [show 3 * a_t ^ 3 = 3 * a_t ^ 2 * a_t by ring, one_div_mul_eq_div,
            mul_div_cancel_right₀ _ hat_pos.ne']
        have ha3 : ((5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3)) * (3 * a_t ^ 3) =
            (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) := div_mul_cancel₀ _ h3a3.ne'
        dsimp only [B3B]; linarith only [ha1, ha3,
          show (1 / a_t - (5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3) - 100 / 69 +
              qMin * (F0 - F1 * a_t)) * (3 * a_t ^ 3) =
            (1 / a_t) * (3 * a_t ^ 3) -
              ((5001 / 5000) * (t ^ 2 + 276 / 10 ^ 10) / (3 * a_t ^ 3)) * (3 * a_t ^ 3) +
              (-100 / 69 + qMin * (F0 - F1 * a_t)) * (3 * a_t ^ 3) by ring]
      have hid : ((1 / 4) * kap ^ 2 * (1 + 2 * qMin * t - t ^ 2) -
          (Ctot - pref * B3B)) * (3 * a_t ^ 3) =
          qDeg5Poly ((1 / 4) * kap ^ 2) Ctot pref qMin F0 F1 t := by
        rw [show ((1 / 4) * kap ^ 2 * (1 + 2 * qMin * t - t ^ 2) -
            (Ctot - pref * B3B)) * (3 * a_t ^ 3) =
          ((1 / 4) * kap ^ 2 * (1 + 2 * qMin * t - t ^ 2) - Ctot) * (3 * a_t ^ 3) +
            pref * (B3B * (3 * a_t ^ 3)) by ring,
          hB_mul, hat_eq]
        unfold qDeg5Poly; ring
      have hprod_nn : 0 ≤ ((1 / 4) * kap ^ 2 * (1 + 2 * qMin * t - t ^ 2) -
          (Ctot - pref * B3B)) * (3 * a_t ^ 3) := by
        rw [hid]; exact hQ5
      have hsub_nn := (mul_nonneg_iff_of_pos_right h3a3).mp hprod_nn
      linarith only [hsub_nn]
    have hfinal : s0 ^ 2 * (Ctot - pref * B3B) ≤ (1 / 4) * kap ^ 2 * (1 - γ ^ 2) := by
      calc s0 ^ 2 * (Ctot - pref * B3B)
          ≤ s0 ^ 2 * ((1 / 4) * kap ^ 2 * (1 + 2 * qMin * t - t ^ 2)) :=
            mul_le_mul_of_nonneg_left hB_q (sq_nonneg s0)
        _ = (1 / 4) * kap ^ 2 * (s0 ^ 2 * (1 + 2 * qMin * t - t ^ 2)) := by ring
        _ ≤ (1 / 4) * kap ^ 2 * (1 - γ ^ 2) := mul_le_mul_of_nonneg_left h1_gam hkapQ_nn
    exact mul_le_mul_of_nonneg_right hfinal hp2

private theorem clamped_regime2_3b_le_band {M mHi : ℕ} {gamLo s0Hi qMin Ctot pref kap : ℝ}
    (hMlo : 46368 ≤ M) (hMhi : M ≤ mHi) (hmHi_ub : mHi ≤ 47488)
    (hgam_ge : 949 / 1000 ≤ gamLo) (hs0Hi_nn : 0 ≤ s0Hi) (hs0Hi_ub : s0Hi ≤ 31543 / 100000)
    (hs0_band : 1 - (gamLo - 1 / 20000) ^ 2 ≤ s0Hi ^ 2)
    (hq_nn : 0 ≤ qMin) (hq_band : qMin * s0Hi ≤ gamLo - 1 / 20000)
    (hCtot_ge : (mHi : ℝ) / (4 * ((mHi : ℝ) + 1)) ≤ Ctot)
    (hCtot : (1 - (9567 / 10000) ^ 2) * ((mHi : ℝ) / (4 * ((mHi : ℝ) + 1))) +
      (247 / 1000) * (1 / (8 * 46369) + 16 / (16 * 46369 ^ 2)) ≤
      (1 - (9567 / 10000) ^ 2) * Ctot)
    (hpref0 : 0 ≤ pref) (hkap0 : 0 ≤ kap)
    (hpref_rat : pref * (4 * (314159265358979323847 / 10 ^ 20) * ((mHi : ℝ) + 1)) ≤
      (1 - (2 / 46369) ^ 2 / 6) ^ 2)
    (h3A_0 :
      let a3A : ℝ := 8 * (4794 / 10 ^ 8)
      let B0 := 1 / a3A - (5001 / 5000) * (276 / 10 ^ 10) / (3 * a3A ^ 3) - 100 / 69 +
        qMin * (67921 / 10000 - (12138773 / 10000) * a3A)
      0 ≤ Ctot - pref * B0 ∧ (1002 / 1000) * (Ctot - pref * B0) ≤ (1 / 4) * kap ^ 2)
    (h3A_hi :
      let a3A : ℝ := 8 * (4794 / 10 ^ 8)
      let Bhi := 1 / a3A - (5001 / 5000) * ((6 * (4794 / 10 ^ 8)) ^ 2 + 276 / 10 ^ 10) /
          (3 * a3A ^ 3) - 100 / 69 + qMin * (67921 / 10000 - (12138773 / 10000) * a3A)
      Ctot - pref * Bhi ≤ (1 / 4) * kap ^ 2)
    (hQ5_cert : ∀ {t : ℝ}, 6 * (4794 / 10 ^ 8) ≤ t → t ≤ 83 / 20000 →
      ∃ a0 F0 F1 : ℝ, 0 < a0 ∧ F0 ≤ fPoleTan0 a0 ∧ fPoleTan1 a0 ≤ F1 ∧
        0 ≤ qDeg5Poly ((1 / 4) * kap ^ 2) Ctot pref qMin F0 F1 t)
    {γ φ' : ℝ} (hγlo_b : gamLo ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hφ0 : 0 ≤ φ')
    (hφpi : φ' ≤ π / 2) (hc0lo : γ - 1 / 20000 ≤ Real.cos φ')
    (hc0hi : Real.cos φ' ≤ γ + 3 / 2500) :
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) y) *
        (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 ≤
      (1 / 4) * kap ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 := by
  let q := (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')
  let c0 := Real.cos φ'; let s0 := Real.sin φ'
  have hγlo : 949 / 1000 ≤ γ := hgam_ge.trans hγlo_b
  have hpi_lo := Real.pi_gt_d20; have hpi_hi := Real.pi_lt_d20
  have hs0_nn : 0 ≤ s0 := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith only [hφpi, hpi_lo])
  have hc0s0 : c0 ^ 2 + s0 ^ 2 = 1 := Real.cos_sq_add_sin_sq φ'
  have hc0_lo_b : gamLo - 1 / 20000 ≤ c0 := by dsimp [c0] at *; linarith only [hγlo_b, hc0lo]
  have hc0_lo : 18979 / 20000 ≤ c0 := by linarith only [hgam_ge, hc0_lo_b]
  have hc0_hi : c0 ≤ 9567 / 10000 := by dsimp [c0] at *; linarith only [hγhi, hc0hi]
  have hs0_sq_lo : 1 - (9567 / 10000) ^ 2 ≤ s0 ^ 2 := by
    have := pow_le_pow_left₀ (by linarith only [hc0_lo]) hc0_hi 2
    linarith only [hc0s0, this]
  have hs0_sq_exact : s0 ^ 2 ≤ 1 - (gamLo - 1 / 20000) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith only [hgam_ge]) hc0_lo_b 2
    linarith only [hc0s0, this]
  have hs0_sq_hi : s0 ^ 2 ≤ 995 / 10000 := by
    have hc2 : (18979 / 20000) ^ 2 ≤ c0 ^ 2 := pow_le_pow_left₀ (by norm_num) hc0_lo 2
    linarith only [hc0s0, hc2]
  have hs0_lo : 29 / 100 ≤ s0 := by nlinarith only [hs0_sq_lo, hs0_nn]
  have hs0_hi_b : s0 ≤ s0Hi := by nlinarith only [hs0_sq_exact, hs0_band, hs0_nn, hs0Hi_nn]
  have hs0_hi : s0 ≤ 31543 / 100000 := hs0_hi_b.trans hs0Hi_ub
  have hq_min : qMin * s0 ≤ c0 :=
    (mul_le_mul_of_nonneg_left hs0_hi_b hq_nn).trans (hq_band.trans hc0_lo_b)
  let d := max (c0 - γ) 0; let t := d / s0
  have hd0 : 0 ≤ d := le_max_right _ _
  have ht0 : 0 ≤ t := div_nonneg hd0 hs0_nn
  have ht_hi : t ≤ 83 / 20000 := by
    dsimp [t, d]; rw [div_le_iff₀ (by linarith only [hs0_lo])]
    rcases le_total (c0 - γ) 0 with h | h <;>
      [rw [max_eq_right h]; rw [max_eq_left h]] <;>
      (dsimp [c0] at *; linarith only [hc0hi, hs0_lo])
  let du := π / 65536; let du_hi : ℝ := 4794 / 10 ^ 8; let tau := max t (6 * du_hi)
  have hdu_lo : 4793 / 10 ^ 8 ≤ du := by dsimp [du]; linarith only [hpi_lo]
  have hdu_le : du ≤ du_hi := by dsimp [du, du_hi]; linarith only [hpi_hi]
  have hdu0 : 0 < du := by linarith only [hdu_lo]
  have hφ_hi : φ' ≤ 35 / 100 := by
    by_contra hlt; push Not at hlt
    have hs35 : 34 / 100 < Real.sin (35 / 100) := by
      linarith only [Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 35 / 100)]
    have hmono : Real.sin (35 / 100) ≤ s0 :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith only [hpi_lo]) hφpi hlt.le
    linarith only [hs35, hmono, hs0_hi]
  let j0 := ⌊(φ' + tau) / du⌋₊ + 1; let jEnd := ⌊(φ' + 7 / 10) / du⌋₊; let K := jEnd - j0
  have htau_lo : 6 * du_hi ≤ tau := le_max_right _ _
  have htau_hi : tau ≤ 83 / 20000 := max_le ht_hi (by dsimp [du_hi]; norm_num)
  have htau0 : 0 ≤ tau := by dsimp [du_hi] at htau_lo; linarith only [htau_lo]
  have hjEnd_lt : jEnd < 2 ^ 16 := by
    dsimp [jEnd]; rw [Nat.floor_lt (by positivity)]
    calc (φ' + 7 / 10) / du ≤ (35 / 100 + 7 / 10) / (4793 / 10 ^ 8) :=
          div_le_div₀ (by norm_num) (by linarith only [hφ_hi]) (by norm_num) hdu_lo
      _ < ((2 ^ 16 : ℕ) : ℝ) := by norm_num
  have hK_ge : 4 ≤ K := by
    have h1 : (j0 : ℝ) ≤ (φ' + tau) / du + 1 := by
      dsimp [j0]; push_cast; linarith only [Nat.floor_le (by positivity : 0 ≤ (φ' + tau) / du)]
    have h2 : (φ' + 7 / 10) / du - 1 < (jEnd : ℝ) := by
      dsimp [jEnd]; linarith only [Nat.lt_floor_add_one ((φ' + 7 / 10) / du)]
    have hdiff : 1000 < (jEnd : ℝ) - (j0 : ℝ) := by
      have h3 : (7 / 10 - tau) / du_hi ≤ (φ' + 7 / 10) / du - (φ' + tau) / du := by
        rw [← sub_div, show (φ' + 7 / 10) - (φ' + tau) = 7 / 10 - tau by ring]
        exact div_le_div_of_nonneg_left (by linarith only [htau_hi]) hdu0 hdu_le
      dsimp [du_hi] at h3; linarith only [h1, h2, h3, htau_hi]
    have hjle : j0 ≤ jEnd := by exact_mod_cast (by linarith only [hdiff] : (j0 : ℝ) ≤ jEnd)
    have h4 : (4 : ℝ) ≤ ((jEnd - j0 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hjle]; linarith only [hdiff]
    exact_mod_cast h4
  have hj0_le_end : j0 ≤ jEnd := by omega
  have hj0K_lt : j0 + K < 2 ^ 16 := by omega
  let u0 := (j0 : ℝ) * du - φ'; let mu := (u0 - tau) / du
  have hu0_lo : tau ≤ u0 := by
    dsimp [u0, j0]; push_cast
    have := (div_lt_iff₀ hdu0).mp (Nat.lt_floor_add_one ((φ' + tau) / du))
    linarith only [this]
  have hu0_hi : u0 ≤ tau + du := by
    dsimp [u0, j0]; push_cast
    have := (le_div_iff₀ hdu0).mp (Nat.floor_le (by positivity : 0 ≤ (φ' + tau) / du))
    linarith only [this]
  have hmu0 : 0 ≤ mu := div_nonneg (by linarith only [hu0_lo]) hdu0.le
  have hmu1 : mu ≤ 1 := (div_le_one hdu0).mpr (by linarith only [hu0_hi])
  have hu0_eq : u0 = tau + mu * du := by dsimp [mu]; rw [div_mul_cancel₀ _ hdu0.ne']; ring
  have huK_hi : u0 + (K : ℝ) * du ≤ 7 / 10 := by
    have h1 : u0 + (K : ℝ) * du = (jEnd : ℝ) * du - φ' := by
      dsimp [u0, K]; rw [Nat.cast_sub hj0_le_end]; ring
    rw [h1]
    have h2 := (le_div_iff₀ hdu0).mp (Nat.floor_le (by positivity : 0 ≤ (φ' + 7 / 10) / du))
    linarith only [h2]
  have huKm1_lo : 69 / 100 ≤ u0 + ((K - 1 : ℕ) : ℝ) * du := by
    have h1 : u0 + ((K - 1 : ℕ) : ℝ) * du = ((jEnd : ℝ) - 1) * du - φ' := by
      dsimp [u0, K]; rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_sub hj0_le_end]; push_cast; ring
    rw [h1]
    have h2 := (div_lt_iff₀ hdu0).mp (Nat.lt_floor_add_one ((φ' + 7 / 10) / du))
    dsimp [du_hi] at hdu_le; linarith only [h2, hdu_le]
  have ht_tau : t ≤ tau := le_max_left _ _
  have htot := clamped_tot_sum_le hMlo hMhi hmHi_ub hγlo hγhi hφ0 hφ_hi hc0lo hc0hi hs0_nn hs0_lo
    hs0_hi hs0_sq_lo hc0_lo hc0_hi hCtot_ge hCtot htau_lo ht_tau hu0_lo huK_hi (q := q) rfl
  dsimp only at htot
  have hibin_prim := quartet_ibin_sum_ge hMlo hMhi hmHi_ub hpref0 hpref_rat hs0_nn hs0_lo hs0_sq_hi
    (by linarith only [hc0_lo]) hd0 htau_lo ht_tau hK_ge hj0K_lt hu0_lo hu0_hi huK_hi (q := q) rfl
  dsimp only at hibin_prim
  rw [Nat.cast_add_one] at hibin_prim
  have hconv := stencilPrim_conv_sub_ge hs0_nn (by linarith only [hc0_lo]) hq_min hdu_lo hdu_le
    ht0 ht_tau htau_lo htau_hi hmu0 hmu1 huKm1_lo
  dsimp only at hconv
  rw [show tau + (1 + mu) * du = u0 + du by rw [hu0_eq]; ring,
    show tau + (2 + mu) * du = u0 + 2 * du by rw [hu0_eq]; ring] at hconv
  have hibin_lb := (mul_le_mul_of_nonneg_left hconv
    (mul_nonneg hpref0 (sq_nonneg (π / ((M : ℝ) + 1))))).trans hibin_prim
  exact regime2_3b_algebraic_closure hq_nn hpref0 hkap0 hγlo hγhi hc0lo (by linarith only [hs0_lo])
    hc0s0 hq_min ht_hi huKm1_lo (sq_nonneg _) h3A_0 h3A_hi hQ5_cert htot hibin_lb

private theorem clamped_regime2_3b_le_low {M : ℕ} (hMlo : 46368 ≤ M) (hMhi : M ≤ 46752)
    {γ φ' : ℝ} (hγlo : 1903 / 2000 ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hφ0 : 0 ≤ φ')
    (hφpi : φ' ≤ π / 2) (hc0lo : γ - 1 / 20000 ≤ Real.cos φ')
    (hc0hi : Real.cos φ' ≤ γ + 3 / 2500) :
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) y) *
        (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 ≤
      (1 / 4) * (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 :=
  (clamped_regime2_3b_le_band (s0Hi := 30781 / 100000) hMlo hMhi (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    (by norm_num) exists_qDeg5_cert_low hγlo hγhi hφ0 hφpi hc0lo hc0hi).trans_eq
    (by congr 3; norm_num)

private theorem clamped_regime2_3b_le_mid {M : ℕ} (hMlo : 46368 ≤ M) (hMhi : M ≤ 47008)
    {γ φ' : ℝ} (hγlo : 1189 / 1250 ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hφ0 : 0 ≤ φ')
    (hφpi : φ' ≤ π / 2) (hc0lo : γ - 1 / 20000 ≤ Real.cos φ')
    (hc0hi : Real.cos φ' ≤ γ + 3 / 2500) :
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) y) *
        (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 ≤
      (1 / 4) * (99478 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 :=
  (clamped_regime2_3b_le_band (s0Hi := 30873 / 100000) hMlo hMhi (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    (by norm_num) exists_qDeg5_cert_mid hγlo hγhi hφ0 hφpi hc0lo hc0hi).trans_eq
    (by congr 3; norm_num)

private theorem clamped_regime2_3b_le_univ {M : ℕ} (hMlo : 46368 ≤ M) (hMhi : M ≤ 47488)
    {γ φ' : ℝ} (hγlo : 949 / 1000 ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hφ0 : 0 ≤ φ')
    (hφpi : φ' ≤ π / 2) (hc0lo : γ - 1 / 20000 ≤ Real.cos φ')
    (hc0hi : Real.cos φ' ≤ γ + 3 / 2500) :
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) y) *
        (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 ≤
      (1 / 4) * (99487 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 :=
  (clamped_regime2_3b_le_band (s0Hi := 31543 / 100000) hMlo hMhi (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    (by norm_num) exists_qDeg5_cert_univ hγlo hγhi hφ0 hφpi hc0lo hc0hi).trans_eq
    (by congr 3; norm_num)

private def negMod16 : Equiv.Perm (Fin (2 ^ 16)) where
  toFun y := ⟨(2 ^ 16 - y.val) % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩
  invFun y := ⟨(2 ^ 16 - y.val) % 2 ^ 16, Nat.mod_lt _ (by positivity)⟩
  left_inv y := by apply Fin.ext; dsimp; have hyLt : y.val < 65536 := y.isLt; omega
  right_inv y := by apply Fin.ext; dsimp; have hyLt : y.val < 65536 := y.isLt; omega

private theorem qpeDecodeEnergy_negMod16 (eLB lam : ℝ) (y : Fin (2 ^ 16)) :
    qpeDecodeEnergy eLB lam 16 (negMod16 y) = qpeDecodeEnergy eLB lam 16 y := by
  unfold qpeDecodeEnergy qpeHalfPhase
  rw [cos_foldAngle_div_two (qpeAngle_nonneg 16 (negMod16 y)) (qpeAngle_le_two_pi 16 (negMod16 y)),
    cos_foldAngle_div_two (qpeAngle_nonneg 16 y) (qpeAngle_le_two_pi 16 y)]
  suffices h : |Real.cos (qpeAngle 16 (negMod16 y) / 2)| = |Real.cos (qpeAngle 16 y / 2)| by rw [h]
  by_cases hy : y.val = 0
  · have heq : negMod16 y = y := by apply Fin.ext; simp [negMod16, hy]
    rw [heq]
  · have hval : (negMod16 y).val = 2 ^ 16 - y.val :=
      Nat.mod_eq_of_lt (by have := y.isLt; omega)
    have hang : qpeAngle 16 (negMod16 y) / 2 = π - qpeAngle 16 y / 2 := by
      dsimp [qpeAngle]; rw [hval, Nat.cast_sub (le_of_lt y.isLt)]; push_cast; field_simp; ring
    rw [hang, Real.cos_pi_sub, abs_neg]

private theorem windowPhaseVec_two_pi_sub (M : ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    windowPhaseVec 16 M c (2 * π - θ) = windowPhaseVec 16 M c (-θ) := by
  funext m; dsimp [windowPhaseVec]; split_ifs with hm
  · congr 1
    have hsplit : Complex.I * (m.val : ℂ) * ((2 * π - θ : ℝ) : ℂ) =
        2 * π * Complex.I * (m.val : ℂ) +
          Complex.I * (m.val : ℂ) * ((-θ : ℝ) : ℂ) := by push_cast; ring
    rw [hsplit, Complex.exp_add, exp_two_pi_I_nat2, one_mul]
  · rfl

private theorem normSq_iqft16_windowPhaseVec_neg (M : ℕ) (c : ℕ → ℝ) (θ : ℝ)
    (y : Fin (2 ^ 16)) :
    Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) (negMod16 y)) =
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c θ) y) := by
  suffices h : ((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c (-θ)) (negMod16 y) =
      star (((QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M c θ) y) by
    rw [h, Complex.star_def, Complex.normSq_conj]
  simp only [Matrix.mulVec, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [iqft16_apply, iqft16_apply, star_mul', star_mul']
  have h1 : star (1 / 256 : ℂ) = (1 / 256 : ℂ) := by simp
  have hexp_y : Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 (negMod16 y) : ℂ)) =
      star (Complex.exp (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) (-Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ)) =
        Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ) := by
      simp [Complex.conj_ofReal, Complex.conj_I]
    rw [hconj]
    by_cases hy : y.val = 0
    · have h0 : (negMod16 y).val = 0 := by simp [negMod16, hy]
      simp [qpeAngle, hy, h0]
    · have hval : (negMod16 y).val = 2 ^ 16 - y.val :=
        Nat.mod_eq_of_lt (by have := y.isLt; omega)
      have hang : (qpeAngle 16 (negMod16 y) : ℂ) = 2 * π - (qpeAngle 16 y : ℂ) := by
        dsimp [qpeAngle]; rw [hval, Nat.cast_sub (le_of_lt y.isLt)]; push_cast; field_simp; ring
      have hsplit : -Complex.I * (m.val : ℂ) * (2 * π - (qpeAngle 16 y : ℂ)) =
          -(2 * π * Complex.I * (m.val : ℂ)) +
            Complex.I * (m.val : ℂ) * (qpeAngle 16 y : ℂ) := by ring
      rw [hang, hsplit, Complex.exp_add, Complex.exp_neg, exp_two_pi_I_nat2, inv_one, one_mul]
  have hw : windowPhaseVec 16 M c (-θ) m = star (windowPhaseVec 16 M c θ m) := by
    unfold windowPhaseVec; split_ifs with hm
    · rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2; simp [Complex.conj_ofReal, Complex.conj_I]
    · simp
  rw [h1, hexp_y, hw]

private theorem sum_normSq_iqft16_windowPhaseVec_cos_clamped_neg (M : ℕ) (γ φ' : ℝ) :
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (-(2 * φ'))) y) *
          (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 =
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) y) *
          (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 := by
  let f : Fin (2 ^ 16) → ℝ := fun z ↦
    Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
      windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (-(2 * φ'))) z) *
        (max |Real.cos (qpeAngle 16 z / 2)| γ - max (Real.cos φ') γ) ^ 2
  rw [show (∑ y, f y) = ∑ z, f z from rfl, ← Equiv.sum_comp negMod16 f]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  dsimp only [f]; rw [normSq_iqft16_windowPhaseVec_neg]
  have hdec := qpeDecodeEnergy_negMod16 0 1 y
  unfold qpeDecodeEnergy qpeHalfPhase at hdec
  rw [cos_foldAngle_div_two (qpeAngle_nonneg 16 (negMod16 y))
      (qpeAngle_le_two_pi 16 (negMod16 y)),
    cos_foldAngle_div_two (qpeAngle_nonneg 16 y) (qpeAngle_le_two_pi 16 y)] at hdec
  have habs : |Real.cos (qpeAngle 16 (negMod16 y) / 2)| =
      |Real.cos (qpeAngle 16 y / 2)| := by linarith
  rw [habs]

/-- Certified 3-band parameter box `(M, eGapUb, κ)` for `T`-clamped doubled-phase sine-window QPE:
- **Low (`M ≤ 46752`, `eGapUb ≤ 4.715`):** `κ ≥ 99475 / 10 ^ 5`
- **Mid (`M ≤ 47008`, `eGapUb ≤ 4.75`):** `κ ≥ 99478 / 10 ^ 5`
- **Universal (`M ≤ 47488`, `eGapUb ≤ 4.96`):** `κ ≥ 99487 / 10 ^ 5`. -/
def ValidClampedBox (M : ℕ) (eGapUb κ : ℝ) : Prop :=
  46368 ≤ M ∧ M ≤ 47488 ∧ 440 / 100 ≤ eGapUb ∧ eGapUb ≤ 496 / 100 ∧
    ((M ≤ 46752 ∧ eGapUb ≤ 4715 / 1000 ∧ 99475 / 10 ^ 5 ≤ κ) ∨
      (M ≤ 47008 ∧ eGapUb ≤ 475 / 100 ∧ 99478 / 10 ^ 5 ≤ κ) ∨
      99487 / 10 ^ 5 ≤ κ)

theorem validClampedBox_kap_ge {M : ℕ} {eGapUb κ : ℝ} (hbox : ValidClampedBox M eGapUb κ) :
    99475 / 10 ^ 5 ≤ κ := by
  rcases hbox.2.2.2.2 with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h <;> linarith

private theorem clamped_cos_mse_le_box {M : ℕ} {eGapUb κ g γ φ : ℝ}
    (hbox : ValidClampedBox M eGapUb κ) (hg_hi : g ≤ eGapUb) (hγ_def : γ = 1 - g / 97.3864)
    (hγlo : 949 / 1000 ≤ γ) (hγhi : γ ≤ 9555 / 10000) (hφ0 : 0 ≤ φ) (hφ_pi : φ ≤ π) :
    ∑ y : Fin (2 ^ 16),
      Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
        windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ)) y) *
        (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2 ≤
      (1 / 4) * κ ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 := by
  have hkap_lo : 99475 / 10 ^ 5 ≤ κ := validClampedBox_kap_ge hbox
  obtain ⟨hMlo, hMhi, _, _, hband⟩ := hbox
  have hkap2 : (99475 / 10 ^ 5) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by norm_num) hkap_lo 2
  have h1mg_nn : 0 ≤ 1 - γ ^ 2 := by nlinarith only [hγlo, hγhi]
  let q0 := (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ)
  by_cases hreg : γ + 3 / 2500 ≤ |Real.cos φ| ∨ |Real.cos φ| ≤ γ - 1 / 20000
  · have hmom : ∑ y : Fin (2 ^ 16),
          Complex.normSq (q0 y) * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2 ≤
        ((M : ℝ) / ((M : ℝ) + 1)) * (π / ((M : ℝ) + 1)) ^ 2 / 4 :=
      (sineWindow_moments hMlo hMhi (2 * φ)).2.2.1
    have hm1 : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have h994 : ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
          (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2 ≤
        (1 / 4) * (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 := by
      calc ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
              (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2
          ≤ ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
              ((99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) *
                Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2) := by
            refine Finset.sum_le_sum fun y _ ↦
              mul_le_mul_of_nonneg_left ?_ (Complex.normSq_nonneg _)
            have hp := clamped_regime1_3a_le hγlo hγhi hreg (x := qpeAngle 16 y / 2)
            rwa [show qpeAngle 16 y / 2 - φ = (qpeAngle 16 y - 2 * φ) / 2 by ring] at hp
        _ = (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) *
              ∑ y : Fin (2 ^ 16),
                Complex.normSq (q0 y) * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ ≤ _ := by
            have hs_le : ∑ y : Fin (2 ^ 16),
                  Complex.normSq (q0 y) * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2 ≤
                (1 / 4) * (π / ((M : ℝ) + 1)) ^ 2 := by
              nlinarith [sq_nonneg (π / ((M : ℝ) + 1))]
            have hpos : 0 ≤ (99475 / 10 ^ 5) ^ 2 * (1 - γ ^ 2) := by positivity
            exact (mul_le_mul_of_nonneg_left hs_le hpos).trans_eq (by ring)
    exact h994.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkap2 (by norm_num)) h1mg_nn) (sq_nonneg _))
  · push Not at hreg
    obtain ⟨hhi, hlo⟩ := hreg
    have hdispatch : ∀ {φ' : ℝ}, 0 ≤ φ' → φ' ≤ π / 2 →
        γ - 1 / 20000 ≤ Real.cos φ' → Real.cos φ' ≤ γ + 3 / 2500 →
        ∑ y : Fin (2 ^ 16),
          Complex.normSq (((QFT.qftMatrix 16)ᴴ *ᵥ
            windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ')) y) *
            (max |Real.cos (qpeAngle 16 y / 2)| γ - max (Real.cos φ') γ) ^ 2 ≤
          (1 / 4) * κ ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 := by
      intro φ' hφ'0 hφ'h hc_lo hc_hi
      rcases hband with ⟨hMb, hgb, hkb⟩ | ⟨hMb, hgb, hkb⟩ | hkb
      · have hγb : 1903 / 2000 ≤ γ := by rw [hγ_def]; norm_num at hg_hi hgb ⊢; linarith
        have hb := clamped_regime2_3b_le_low hMlo hMb hγb hγhi hφ'0 hφ'h hc_lo hc_hi
        have hk2 : (99475 / 10 ^ 5) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by norm_num) hkb 2
        exact hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hk2 (by norm_num)) h1mg_nn) (sq_nonneg _))
      · have hγb : 1189 / 1250 ≤ γ := by rw [hγ_def]; norm_num at hg_hi hgb ⊢; linarith
        have hb := clamped_regime2_3b_le_mid hMlo hMb hγb hγhi hφ'0 hφ'h hc_lo hc_hi
        have hk2 : (99478 / 10 ^ 5) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by norm_num) hkb 2
        exact hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hk2 (by norm_num)) h1mg_nn) (sq_nonneg _))
      · have hb := clamped_regime2_3b_le_univ hMlo hMhi hγlo hγhi hφ'0 hφ'h hc_lo hc_hi
        have hk2 : (99487 / 10 ^ 5) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by norm_num) hkb 2
        exact hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hk2 (by norm_num)) h1mg_nn) (sq_nonneg _))
    by_cases hc_nn : 0 ≤ Real.cos φ
    · have hφ_half : φ ≤ π / 2 := by
        by_contra hgt; push Not at hgt
        have hsin_pos : 0 < Real.sin (φ - π / 2) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
        have hcos_eq : Real.cos φ = -Real.sin (φ - π / 2) := by
          conv_lhs => rw [show φ = (φ - π / 2) + π / 2 by ring, Real.cos_add_pi_div_two]
        linarith
      rw [abs_of_nonneg hc_nn] at hlo hhi ⊢
      exact hdispatch hφ0 hφ_half hlo.le hhi.le
    · push Not at hc_nn
      let φ' := π - φ
      have hφ'0 : 0 ≤ φ' := by dsimp [φ']; linarith
      have hφ'_half : φ' ≤ π / 2 := by
        by_contra hgt; push Not at hgt
        have : 0 ≤ Real.cos φ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by dsimp [φ'] at hgt; linarith⟩
        linarith
      have hc' : Real.cos φ' = |Real.cos φ| := by
        dsimp [φ']; rw [Real.cos_pi_sub, abs_of_neg hc_nn]
      have hvec : windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ) =
          windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (-(2 * φ')) := by
        rw [show 2 * φ = 2 * π - 2 * φ' by dsimp [φ']; ring]
        exact windowPhaseVec_two_pi_sub M (sineWindowCoeff (M + 1)) (2 * φ')
      rw [hvec, ← hc', sum_normSq_iqft16_windowPhaseVec_cos_clamped_neg]
      rw [← hc'] at hlo hhi
      exact hdispatch hφ'0 hφ'_half hlo.le hhi.le

theorem clamped_sineWindow_energy_mse_le_box {M : ℕ} {eLB eGapUb κ T E : ℝ}
    (hbox : ValidClampedBox M eGapUb κ)
    (hT : T ≤ eLB + eGapUb) (hElo : eLB ≤ E) (hEhi : E ≤ eLB + 2 * 97.3864 - eGapUb) :
    let φ := QubitisedWalk.spectralPhase eLB 97.3864 E
    let q0 := (QFT.qftMatrix 16)ᴴ *ᵥ windowPhaseVec 16 M (sineWindowCoeff (M + 1)) (2 * φ)
    ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
        (min (qpeDecodeEnergy eLB 97.3864 16 y) T - min E T) ^ 2 ≤
      (κ * (spectralAmpEffNorm 97.3864 eGapUb / 2) * (π / ((M : ℝ) + 1))) ^ 2 := by
  intro φ q0
  have hkap_lo : 99475 / 10 ^ 5 ≤ κ := validClampedBox_kap_ge hbox
  have ⟨hMlo, hMhi, heGapLo, heGapHi, _⟩ := hbox
  have hkap2 : (99475 / 10 ^ 5) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by norm_num) hkap_lo 2
  have hφ_eq : E = eLB + 97.3864 * (1 - Real.cos φ) :=
    (QubitisedWalk.energy_eq_of_spectralPhase (by norm_num) hElo (by linarith)).symm
  have hφ0 : 0 ≤ φ := QubitisedWalk.spectralPhase_nonneg
  have hφ_pi : φ ≤ π := QubitisedWalk.spectralPhase_le_pi eLB 97.3864 E
  have heff_sq : spectralAmpEffNorm 97.3864 eGapUb ^ 2 = eGapUb * (2 * 97.3864 - eGapUb) := by
    unfold spectralAmpEffNorm; exact sq_sqrt (by nlinarith)
  rcases le_total (T - eLB) ((988 / 1000) * eGapUb) with hT_low | hT_high
  · let g' := max (T - eLB) 0
    have hg'0 : 0 ≤ g' := le_max_right _ _
    have hg'_le : g' ≤ (988 / 1000) * eGapUb := max_le hT_low (by positivity)
    have hT_g' : T ≤ eLB + g' := by dsimp [g']; linarith [le_max_left (T - eLB) 0]
    have hpt (y : Fin (2 ^ 16)) :
        (min (qpeDecodeEnergy eLB 97.3864 16 y) T - min E T) ^ 2 ≤
          (spectralAmpEffNorm 97.3864 g' / 2) ^ 2 *
            (4 * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2) :=
      sq_min_qpeDecodeEnergy_sub_min_le_pos y (by norm_num) hg'0 (by linarith) hT_g' hφ_eq
        (by linarith)
    have hmom : ∑ y : Fin (2 ^ 16),
          Complex.normSq (q0 y) * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2 ≤
        ((M : ℝ) / ((M : ℝ) + 1)) * (π / ((M : ℝ) + 1)) ^ 2 / 4 :=
      (sineWindow_moments hMlo hMhi (2 * φ)).2.2.1
    have hvar : ∑ y : Fin (2 ^ 16),
          Complex.normSq (q0 y) * (4 * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2) ≤
        (π / ((M : ℝ) + 1)) ^ 2 := by
      have hrew : ∑ y : Fin (2 ^ 16),
            Complex.normSq (q0 y) * (4 * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2) =
          4 * ∑ y : Fin (2 ^ 16),
            Complex.normSq (q0 y) * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      have hm1 : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      rw [hrew]; nlinarith [sq_nonneg (π / ((M : ℝ) + 1))]
    have hsum : ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
          (min (qpeDecodeEnergy eLB 97.3864 16 y) T - min E T) ^ 2 ≤
        (spectralAmpEffNorm 97.3864 g' / 2) ^ 2 * (π / ((M : ℝ) + 1)) ^ 2 := by
      calc ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
              (min (qpeDecodeEnergy eLB 97.3864 16 y) T - min E T) ^ 2
          ≤ ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
              ((spectralAmpEffNorm 97.3864 g' / 2) ^ 2 *
                (4 * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2)) :=
            Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hpt y) (Complex.normSq_nonneg _)
        _ = (spectralAmpEffNorm 97.3864 g' / 2) ^ 2 *
              ∑ y : Fin (2 ^ 16),
                Complex.normSq (q0 y) * (4 * Real.sin ((qpeAngle 16 y - 2 * φ) / 2) ^ 2) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    refine hsum.trans ?_
    have heff_g' : (spectralAmpEffNorm 97.3864 g' / 2) ^ 2 ≤
        (κ * (spectralAmpEffNorm 97.3864 eGapUb / 2)) ^ 2 := by
      have hg'sq : spectralAmpEffNorm 97.3864 g' ^ 2 = g' * (2 * 97.3864 - g') := by
        unfold spectralAmpEffNorm; exact sq_sqrt (by nlinarith)
      have hmono1 : g' * (2 * 97.3864 - g') ≤
          ((988 / 1000) * eGapUb) * (2 * 97.3864 - (988 / 1000) * eGapUb) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hg'_le)
          (by linarith : 0 ≤ 2 * 97.3864 - (988 / 1000) * eGapUb - g')]
      have h994 : (spectralAmpEffNorm 97.3864 g' / 2) ^ 2 ≤
          ((99475 / 10 ^ 5) * (spectralAmpEffNorm 97.3864 eGapUb / 2)) ^ 2 := by
        rw [div_pow, mul_pow, div_pow, div_pow, hg'sq, heff_sq]
        norm_num at hmono1 heGapLo heGapHi ⊢; nlinarith
      refine h994.trans ?_
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right hkap2 (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right heff_g'
      (sq_nonneg (π / ((M : ℝ) + 1)))).trans_eq (mul_pow _ _ 2).symm
  · let g := T - eLB; let γ := 1 - g / 97.3864
    have hg_lo : (988 / 1000) * (440 / 100) ≤ g := by dsimp [g]; linarith
    have hg_hi : g ≤ eGapUb := by dsimp [g]; linarith
    have hγlo : 949 / 1000 ≤ γ := by dsimp only [γ]; norm_num at hg_hi heGapHi ⊢; linarith
    have hγhi : γ ≤ 9555 / 10000 := by dsimp only [γ]; norm_num at hg_lo ⊢; linarith
    have hminE : min E T = min (eLB + 97.3864 * (1 - |Real.cos φ|)) T := by
      by_cases hc : 0 ≤ Real.cos φ
      · rw [abs_of_nonneg hc, ← hφ_eq]
      · push Not at hc
        rw [abs_of_neg hc, min_eq_right (by dsimp [g] at hg_hi; linarith),
          min_eq_right (by dsimp [g] at hg_hi; linarith)]
    have hmin_c (c : ℝ) : min (eLB + 97.3864 * (1 - c)) T = eLB + 97.3864 * (1 - max c γ) := by
      have hTeq : T = eLB + 97.3864 * (1 - γ) := by dsimp [γ, g]; field_simp; ring
      rw [hTeq]
      by_cases hc : c ≤ γ
      · rw [max_eq_right hc, min_eq_right (by linarith)]
      · push Not at hc; rw [max_eq_left hc.le, min_eq_left (by linarith)]
    have hpt_eq (y : Fin (2 ^ 16)) :
        (min (qpeDecodeEnergy eLB 97.3864 16 y) T - min E T) ^ 2 =
          97.3864 ^ 2 * (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2 := by
      have hdec : qpeDecodeEnergy eLB 97.3864 16 y =
          eLB + 97.3864 * (1 - |Real.cos (qpeAngle 16 y / 2)|) := by
        unfold qpeDecodeEnergy qpeHalfPhase
        rw [cos_foldAngle_div_two (qpeAngle_nonneg 16 y) (qpeAngle_le_two_pi 16 y)]
      rw [hdec, hminE, hmin_c, hmin_c]; ring
    have hscale : 97.3864 ^ 2 * (1 - γ ^ 2) ≤ spectralAmpEffNorm 97.3864 eGapUb ^ 2 := by
      rw [heff_sq]
      have h1 : 97.3864 ^ 2 * (1 - γ ^ 2) = g * (2 * 97.3864 - g) := by
        dsimp [γ]; field_simp; ring
      rw [h1]; nlinarith [mul_nonneg (sub_nonneg.mpr hg_hi)
        (by linarith : 0 ≤ 2 * 97.3864 - eGapUb - g)]
    suffices hcos_mse : ∑ y : Fin (2 ^ 16), Complex.normSq (q0 y) *
          (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2 ≤
        (1 / 4) * κ ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2 by
      simp_rw [hpt_eq, ← mul_assoc]
      have hrew : ∑ y : Fin (2 ^ 16),
            Complex.normSq (q0 y) * 97.3864 ^ 2 *
              (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2 =
          97.3864 ^ 2 * ∑ y : Fin (2 ^ 16),
            Complex.normSq (q0 y) *
              (max |Real.cos (qpeAngle 16 y / 2)| γ - max |Real.cos φ| γ) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hrew]
      have h2 := mul_le_mul_of_nonneg_left hcos_mse (by norm_num : (0 : ℝ) ≤ 97.3864 ^ 2)
      refine h2.trans ?_
      calc 97.3864 ^ 2 * ((1 / 4) * κ ^ 2 * (1 - γ ^ 2) * (π / ((M : ℝ) + 1)) ^ 2)
          = (1 / 4) * κ ^ 2 * (97.3864 ^ 2 * (1 - γ ^ 2)) * (π / ((M : ℝ) + 1)) ^ 2 := by ring
        _ ≤ (1 / 4) * κ ^ 2 * spectralAmpEffNorm 97.3864 eGapUb ^ 2 *
              (π / ((M : ℝ) + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hscale (by positivity))
              (sq_nonneg _)
        _ = (κ * (spectralAmpEffNorm 97.3864 eGapUb / 2) * (π / ((M : ℝ) + 1))) ^ 2 := by ring
    exact clamped_cos_mse_le_box hbox hg_hi rfl hγlo hγhi hφ0 hφ_pi

private theorem embedUnitary_rWalkInWalkCat_reflIn (bCat mOut mMid : ℕ) :
    QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)) := by
  apply Subtype.ext
  change (2 : ℂ) • (inAllWalkCat bCat mOut mMid).basisOutcomeProjector 0 - 1 =
    (rWalkInWalkCat bCat mOut mMid).embedMatrix
      ((2 : ℂ) • (rAllInWalk mOut mMid).basisOutcomeProjector 0 - 1)
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    inAllWalkCat,
      CleanDyn.compose_basisOutcomeProjector]

private theorem embedUnitary_rWalkInWalkCat_reflMid (bCat mOut mMid : ℕ) :
    QubitisedWalk.reflMidUnitary (inMidWalkCat bCat mOut mMid) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflMidUnitary (rMidInWalk mOut mMid)) := by
  apply Subtype.ext
  change 1 - (2 : ℂ) • (inMidWalkCat bCat mOut mMid).basisOutcomeProjector 0 =
    (rWalkInWalkCat bCat mOut mMid).embedMatrix
      (1 - (2 : ℂ) • (rMidInWalk mOut mMid).basisOutcomeProjector 0)
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    inMidWalkCat,
      CleanDyn.compose_basisOutcomeProjector]

private theorem embedUnitary_rWalkInWalkCat_reflPulled (bCat mOut mMid : ℕ)
    (uB : Unitary (2 ^ walkWidth mOut mMid)) :
    QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid)
        ((rWalkInWalkCat bCat mOut mMid).embedUnitary uB) =
      (rWalkInWalkCat bCat mOut mMid).embedUnitary
        (QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB) := by
  dsimp [QubitisedWalk.reflPulledUnitary, QubitisedWalk.reflPulledPair]
  rw [embedUnitary_rWalkInWalkCat_reflMid, ← QRegister.embedUnitary_inv,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]

private theorem inner_tensorWalkCat {bCat mOut mMid : ℕ}
    (u₁ u₂ : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    (∑ x : Fin (2 ^ walkCatWidth bCat mOut mMid),
      star (tensorWalkCat u₁ cat x) * tensorWalkCat u₂ cat x) =
      QubitisedWalk.vecInner u₁ u₂ * ∑ c : Fin (2 ^ bCat), star (cat c) * cat c := by
  let f : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ := fun x ↦
    star (tensorWalkCat u₁ cat x) * tensorWalkCat u₂ cat x
  rw [show (∑ x, star (tensorWalkCat u₁ cat x) * tensorWalkCat u₂ cat x) = ∑ x, f x from rfl,
    ← (BlockEncodingCore.splitBlockEquiv (walkWidth mOut mMid) bCat).symm.sum_comp f,
    Fintype.sum_prod_type]
  dsimp [QubitisedWalk.vecInner, dotProduct]; rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ ↦ ?_
  let x := (BlockEncodingCore.splitBlockEquiv (walkWidth mOut mMid) bCat).symm (a, c)
  have hfst : (rWalkInWalkCat bCat mOut mMid).extractIndex x = a := by
    rw [← BlockEncodingCore.splitBlockEquiv_fst, Equiv.apply_symm_apply]
  have hsnd : (rCatInWalkCat bCat mOut mMid).extractIndex x = c := by
    rw [← BlockEncodingCore.splitBlockEquiv_snd, Equiv.apply_symm_apply]
  dsimp [f, tensorWalkCat]
  change star (u₁ ((rWalkInWalkCat bCat mOut mMid).extractIndex x) *
      cat ((rCatInWalkCat bCat mOut mMid).extractIndex x)) *
    (u₂ ((rWalkInWalkCat bCat mOut mMid).extractIndex x) *
      cat ((rCatInWalkCat bCat mOut mMid).extractIndex x)) = _
  rw [hfst, hsnd]; simp only [star_mul, Complex.star_def]; ring

private def actSplitEquiv (bQPE bCat mOut mMid : ℕ) :
    Fin (2 ^ actWidth bQPE bCat mOut mMid) ≃
      Fin (2 ^ walkCatWidth bCat mOut mMid) × Fin (2 ^ bQPE) :=
  (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid))).trans
    (BlockEncodingCore.splitBlockEquiv (walkCatWidth bCat mOut mMid) bQPE)

private theorem actSplitEquiv_fst (bQPE bCat mOut mMid : ℕ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    (actSplitEquiv bQPE bCat mOut mMid g).1 =
      (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g := by
  apply (basisBits (walkCatWidth bCat mOut mMid)).injective; funext i
  have h1 := congrFun (congrArg (basisBits (walkCatWidth bCat mOut mMid))
    (BlockEncodingCore.splitBlockEquiv_fst (walkCatWidth bCat mOut mMid) bQPE
      (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid)) g))) i
  dsimp only [actSplitEquiv, Equiv.trans_apply]; rw [h1]
  change basisBits _ _ i = basisBits _ _ i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]
  simp [finCongr, TopIntegrationBridge.rWalkCatInAct]

private theorem actSplitEquiv_snd (bQPE bCat mOut mMid : ℕ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    (actSplitEquiv bQPE bCat mOut mMid g).2 =
      (rQPEInAct bQPE bCat mOut mMid).extractIndex g := by
  apply (basisBits bQPE).injective; funext j
  have h2 := congrFun (congrArg (basisBits bQPE)
    (BlockEncodingCore.splitBlockEquiv_snd (walkCatWidth bCat mOut mMid) bQPE
      (finCongr (congrArg (2 ^ ·) (actWidth_eq bQPE bCat mOut mMid)) g))) j
  dsimp only [actSplitEquiv, Equiv.trans_apply]; rw [h2]
  change basisBits _ _ j = basisBits _ _ j
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
    basisBits_eq_testBit, basisBits_eq_testBit]
  dsimp only [TopIntegrationBridge.rQPEInAct, QRegister.block]
  by_cases hb : g.val.testBit (walkCatWidth bCat mOut mMid + j.val) <;> simp [finCongr, hb]

private noncomputable def tensorWCQPE {bQPE bCat mOut mMid : ℕ}
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    Fin (2 ^ actWidth bQPE bCat mOut mMid) → ℂ :=
  fun g ↦ wc ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
    q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)

private theorem embedMatrix_mulVec_apply_replaceIndex2 {k n : ℕ} (r : QRegister k n)
    (A : Operator (2 ^ k)) (state : Fin (2 ^ n) → ℂ) (output : Fin (2 ^ n)) :
    (r.embedMatrix A *ᵥ state) output =
      ∑ a : Fin (2 ^ k), A (r.extractIndex output) a * state (r.replaceIndex output a) :=
  r.embedMatrix_mulVec_apply A state output

private theorem embedMatrix_rWalkCatInAct_mulVec {bQPE bCat mOut mMid : ℕ}
    (A : Operator (2 ^ walkCatWidth bCat mOut mMid))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ((rWalkCatInAct bQPE bCat mOut mMid).embedMatrix A) *ᵥ tensorWCQPE wc q =
      tensorWCQPE (A *ᵥ wc) q := by
  funext g; rw [embedMatrix_mulVec_apply_replaceIndex2]
  have hstep : (∑ u : Fin (2 ^ walkCatWidth bCat mOut mMid),
        A ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) u *
          tensorWCQPE wc q ((rWalkCatInAct bQPE bCat mOut mMid).replaceIndex g u)) =
      ∑ u : Fin (2 ^ walkCatWidth bCat mOut mMid),
        (A ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) u * wc u) *
          q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tensorWCQPE]
    have hq := (rQPEInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
      (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid) g u
    rw [hq, QRegister.extractIndex_replaceIndex, mul_assoc]
  rw [hstep, ← Finset.sum_mul]; rfl

private theorem embedMatrix_rQPEInAct_mulVec {bQPE bCat mOut mMid : ℕ}
    (B : Operator (2 ^ bQPE))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ) :
    ((rQPEInAct bQPE bCat mOut mMid).embedMatrix B) *ᵥ tensorWCQPE wc q =
      tensorWCQPE wc (B *ᵥ q) := by
  funext g; rw [embedMatrix_mulVec_apply_replaceIndex2]
  have hstep : (∑ u : Fin (2 ^ bQPE),
        B ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) u *
          tensorWCQPE wc q ((rQPEInAct bQPE bCat mOut mMid).replaceIndex g u)) =
      wc ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
        ∑ u : Fin (2 ^ bQPE), B ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) u * q u := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ ↦ ?_
    dsimp only [tensorWCQPE]
    have hwc := (rWalkCatInAct bQPE bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
      (QRegister.disjoint_comm.mp (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)) g u
    rw [hwc, QRegister.extractIndex_replaceIndex]; ring
  rw [hstep]; rfl

private theorem embed_qpeMuxUnitary_mulVec2 {bQPE bCat mOut mMid : ℕ}
    (F : Fin (2 ^ bQPE) → Unitary (2 ^ walkCatWidth bCat mOut mMid))
    (wc : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ) (q : Fin (2 ^ bQPE) → ℂ)
    (g : Fin (2 ^ actWidth bQPE bCat mOut mMid)) :
    ((((rQPEInAct bQPE bCat mOut mMid).concat (rWalkCatInAct bQPE bCat mOut mMid)
        (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)).embedUnitary
          (QubitisedWalk.qpeMuxUnitary F)).1 *ᵥ tensorWCQPE wc q) g =
      ((F ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)).1 *ᵥ wc)
          ((rWalkCatInAct bQPE bCat mOut mMid).extractIndex g) *
        q ((rQPEInAct bQPE bCat mOut mMid).extractIndex g) := by
  rw [QubitisedWalk.embed_qpeMuxUnitary_mulVec, Finset.sum_apply,
    Finset.sum_eq_single ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)]
  · rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_left rfl, QRegister.embedUnitary_val,
      embedMatrix_rWalkCatInAct_mulVec]
    rfl
  · intro m _ hm; rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_right (Ne.symm hm)]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem sysAct_tensorState_zero_eq {bQPE bCat mOut mMid : ℕ}
    (ψ : Fin (2 ^ systemQubits_local) → ℂ) :
    let sys : QRegister systemQubits_local (actWidth bQPE bCat mOut mMid) :=
      .block 0 systemQubits_local (by dsimp [actWidth]; omega)
    let e₁ := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
    sys.tensorState ψ (Pi.single 0 1) =
      tensorWCQPE (tensorWalkCat e₁ (basisState (0 : Fin (2 ^ bCat)))) (basisState 0) := by
  intro sys e₁; funext g
  let xwc := (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g
  let xw := (rWalkInWalkCat bCat mOut mMid).extractIndex xwc
  have hsys_eq : sys.extractIndex g = (rSysInWalk mOut mMid).extractIndex xw := by
    dsimp only [xw, xwc]
    rw [← QRegister.extractIndex_compose, ← QRegister.extractIndex_compose]
    congr 1; ext i; simp [sys, TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat, rSysInWalk]
  have hbits_iff : ((sys.basisSplitEquiv g).2 = 0) ↔
      (((rSysInWalk mOut mMid).basisSplitEquiv xw).2 = 0 ∧
        (rCatInWalkCat bCat mOut mMid).extractIndex xwc = 0 ∧
        (rQPEInAct bQPE bCat mOut mMid).extractIndex g = 0) := by
    rw
      [CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero,
      CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
    constructor
    · intro h
      have hzero (w : Wire (actWidth bQPE bCat mOut mMid)) (hw : systemQubits_local ≤ w.val) :
          basisBits (actWidth bQPE bCat mOut mMid) g w = 0 := by
        have hnot : w ∉ Set.range sys.wires := by
          rintro ⟨i, rfl⟩; simp [sys] at hw; omega
        exact congrFun h ⟨w, hnot⟩
      refine ⟨?_, fun _ ↦ ?_, fun _ ↦ hzero _ (by
        simp [TopIntegrationBridge.rQPEInAct, walkCatWidth, walkWidth, systemQubits_local]; omega)⟩
      · funext ⟨w, hw⟩
        have hge : systemQubits_local ≤ w.val := by
          by_contra hlt; push Not at hlt
          exact hw ⟨⟨w.val, hlt⟩, by ext; simp [rSysInWalk]⟩
        simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply, xw, xwc,
          QRegister.basisBits_extractIndex]
        exact hzero _ (by simp [TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat]; omega)
      · simp only [xwc, QRegister.basisBits_extractIndex]
        exact hzero _ (by
          simp [TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat, walkWidth]; omega)
    · rintro ⟨h1, h2, h3⟩; funext ⟨w, hw⟩
      have hge : systemQubits_local ≤ w.val := by
        by_contra hlt; push Not at hlt
        exact hw ⟨⟨w.val, hlt⟩, by ext; simp [sys]⟩
      simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply]
      by_cases h_w : w.val < walkWidth mOut mMid
      · let w' : Wire (walkWidth mOut mMid) := ⟨w.val, h_w⟩
        have hw' : w' ∉ Set.range (rSysInWalk mOut mMid).wires := by
          rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi
          simp [rSysInWalk, w', systemQubits_local] at hv hge; omega
        have hb := congrFun h1 ⟨w', hw'⟩
        simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply, xw, xwc,
          QRegister.basisBits_extractIndex] at hb
        rw [← hb]; refine congrArg (basisBits _ _) ?_
        ext; simp [TopIntegrationBridge.rWalkCatInAct, rWalkInWalkCat, w']
      · by_cases h_wc : w.val < walkCatWidth bCat mOut mMid
        · let i : Fin bCat := ⟨w.val - walkWidth mOut mMid, by
            dsimp [walkCatWidth] at h_wc; omega⟩
          have hb := h2 i
          simp only [xwc, QRegister.basisBits_extractIndex] at hb
          rw [← hb]; refine congrArg (basisBits _ _) ?_
          ext; simp [TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat, i]; omega
        · let j : Fin bQPE := ⟨w.val - walkCatWidth bCat mOut mMid, by
            have hw_lt : w.val < walkCatWidth bCat mOut mMid + bQPE :=
              actWidth_eq bQPE bCat mOut mMid ▸ w.isLt
            omega⟩
          have hb := h3 j
          rw [← hb]; refine congrArg (basisBits _ _) ?_
          ext; simp [TopIntegrationBridge.rQPEInAct, j]; omega
  dsimp only [QRegister.tensorState, tensorWCQPE, tensorWalkCat, basisState]
  change _ =
    (e₁ xw *
      (Pi.single 0 (1 : ℂ) : Fin (2 ^ bCat) → ℂ)
        ((rCatInWalkCat bCat mOut mMid).extractIndex xwc)) *
    (Pi.single 0 (1 : ℂ) : Fin (2 ^ bQPE) → ℂ) ((rQPEInAct bQPE bCat mOut mMid).extractIndex g)
  dsimp only [e₁, QRegister.tensorState]; rw [hsys_eq]
  by_cases h : (sys.basisSplitEquiv g).2 = 0
  · obtain ⟨h1, h2, h3⟩ := hbits_iff.mp h; simp [h, h1, h2, h3]
  · have hnot := mt hbits_iff.mpr h
    by_cases h1 : ((rSysInWalk mOut mMid).basisSplitEquiv xw).2 = 0
    · by_cases h2 : (rCatInWalkCat bCat mOut mMid).extractIndex xwc = 0
      · have h3 : (rQPEInAct bQPE bCat mOut mMid).extractIndex g ≠ 0 :=
          fun hc ↦ hnot ⟨h1, h2, hc⟩
        simp [Pi.single_apply, h, h3]
      · simp [Pi.single_apply, h, h2]
    · simp [Pi.single_apply, h, h1]

private theorem rCatInAct_eq_compose (bQPE bCat mOut mMid : ℕ) :
    rCatInAct bQPE bCat mOut mMid =
      (rWalkCatInAct bQPE bCat mOut mMid).compose (rCatInWalkCat bCat mOut mMid) := by
  ext i; simp [TopIntegrationBridge.rCatInAct, TopIntegrationBridge.rWalkCatInAct, rCatInWalkCat]

private theorem ancAct_compose_rQPEInAnc (bQPE bCat mOut mMid : ℕ) :
    (QRegister.block systemQubits_local (actAncillas bQPE bCat mOut mMid) le_rfl).compose
        (rQPEInAnc bQPE bCat mOut mMid) =
      rQPEInAct bQPE bCat mOut mMid := by
  ext i
  simp [TopIntegrationBridge.rQPEInAnc, TopIntegrationBridge.rQPEInAct, walkCatWidth, walkWidth,
    systemQubits_local]
  omega

private theorem sum_filter_basisOutcomeProbability_eq {k m n : ℕ}
    (rAnc : QRegister k n) (rSub : QRegister m k) (u : Fin (2 ^ n) → ℂ) (y : Fin (2 ^ m)) :
    (∑ a ∈ Finset.univ.filter (fun a ↦ rSub.extractIndex a = y),
      rAnc.basisOutcomeProbability a u) =
      (rAnc.compose rSub).basisOutcomeProbability y u := by
  calc ∑ a ∈ Finset.univ.filter (fun a ↦ rSub.extractIndex a = y),
        rAnc.basisOutcomeProbability a u
      = ∑ a, rAnc.basisOutcomeProbability a u *
          (if rSub.extractIndex a = y then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring
    _ = ∑ y', (rAnc.compose rSub).basisOutcomeProbability y' u *
          (if y' = y then (1 : ℝ) else 0) :=
        sum_basisOutcomeProbability_mul_comp rAnc rSub u (fun y' ↦ if y' = y then (1 : ℝ) else 0)
    _ = (rAnc.compose rSub).basisOutcomeProbability y u := by
        rw [Fintype.sum_eq_single y (fun y' hy' ↦ by simp [hy'])]; simp

private theorem basisOutcomeProbability_rQPEInAct_ortho_branches {bQPE bCat mOut mMid : ℕ}
    (wcPos wcNeg : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ)
    (qPos qNeg : Fin (2 ^ bQPE) → ℂ) (hwcOrtho : ∑ x, star (wcPos x) * wcNeg x = 0)
    (y : Fin (2 ^ bQPE)) :
    (rQPEInAct bQPE bCat mOut mMid).basisOutcomeProbability y
        (tensorWCQPE wcPos qPos + tensorWCQPE wcNeg qNeg) =
      (∑ x, Complex.normSq (wcPos x)) * Complex.normSq (qPos y) +
        (∑ x, Complex.normSq (wcNeg x)) * Complex.normSq (qNeg y) := by
  unfold QRegister.basisOutcomeProbability
  let term : Fin (2 ^ actWidth bQPE bCat mOut mMid) → ℝ := fun g ↦
    Complex.normSq (((rQPEInAct bQPE bCat mOut mMid).basisOutcomeProjector y *ᵥ
      (tensorWCQPE wcPos qPos + tensorWCQPE wcNeg qNeg)) g)
  rw [show (∑ g, Complex.normSq (((rQPEInAct bQPE bCat mOut mMid).basisOutcomeProjector y *ᵥ
      (tensorWCQPE wcPos qPos + tensorWCQPE wcNeg qNeg)) g)) = ∑ g, term g from rfl,
    ← (actSplitEquiv bQPE bCat mOut mMid).symm.sum_comp term, Fintype.sum_prod_type_right]
  rw [Fintype.sum_eq_single y]
  · have hpt : ∑ x : Fin (2 ^ walkCatWidth bCat mOut mMid),
        term ((actSplitEquiv bQPE bCat mOut mMid).symm (x, y)) =
        ∑ x, Complex.normSq (wcPos x * qPos y + wcNeg x * qNeg y) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      let g := (actSplitEquiv bQPE bCat mOut mMid).symm (x, y)
      have hfst : (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g = x := by
        rw [← actSplitEquiv_fst, Equiv.apply_symm_apply]
      have hsnd : (rQPEInAct bQPE bCat mOut mMid).extractIndex g = y := by
        rw [← actSplitEquiv_snd, Equiv.apply_symm_apply]
      dsimp [term]
      change Complex.normSq (((rQPEInAct bQPE bCat mOut mMid).basisOutcomeProjector y *ᵥ
        (tensorWCQPE wcPos qPos + tensorWCQPE wcNeg qNeg)) g) = _
      rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_left hsnd]
      simp [tensorWCQPE, hfst, hsnd]
    rw [hpt]
    simp only [Complex.normSq_add, Complex.normSq_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Complex.star_def]
    have hcross : ∑ x, wcPos x * qPos y * star (wcNeg x * qNeg y) = 0 := by
      have hfac (x : Fin (2 ^ walkCatWidth bCat mOut mMid)) :
          wcPos x * qPos y * star (wcNeg x * qNeg y) =
            (qPos y * star (qNeg y)) * star (star (wcPos x) * wcNeg x) := by
        simp only [star_mul, star_star]; ring
      simp_rw [hfac]; rw [← Finset.mul_sum, ← star_sum, hwcOrtho, star_zero, mul_zero]
    rw [← Finset.mul_sum, ← Complex.re_sum, hcross, Complex.zero_re, mul_zero, add_zero]
  · intro y' hy'; refine Finset.sum_eq_zero fun x _ ↦ ?_
    let g := (actSplitEquiv bQPE bCat mOut mMid).symm (x, y')
    have hsnd : (rQPEInAct bQPE bCat mOut mMid).extractIndex g = y' := by
      rw [← actSplitEquiv_snd, Equiv.apply_symm_apply]
    dsimp [term]
    change Complex.normSq (((rQPEInAct bQPE bCat mOut mMid).basisOutcomeProjector y *ᵥ
      (tensorWCQPE wcPos qPos + tensorWCQPE wcNeg qNeg)) g) = 0
    rw [QRegister.basisOutcomeProjector_mulVec, ite_eq_right (hsnd ▸ hy'), map_zero]

theorem blocked_ideal_qpe_exact (bQPE bCat mOut mMid bAct M : ℕ)
    (hbAct : 1 ≤ bAct) (hbQPE : bAct ≤ bQPE) (hMlo : 2 ^ (bAct - 1) ≤ M) (hMhi : M < 2 ^ bAct)
    {H_tilde_blk : Operator (2 ^ (2 * 58))} {eLB lam : ℝ}
    {uB : Unitary (2 ^ walkWidth mOut mMid)}
    (hSOS : PulledSOSBlockEncoding mOut mMid H_tilde_blk eLB lam uB)
    (uCatIdeal : Unitary (2 ^ bCat)) (uWinIdeal uIqftIdeal : Unitary (2 ^ bQPE))
    (winCoeff : ℕ → ℝ) (hWinZero : uWinIdeal.1 *ᵥ basisState 0 = windowVec bQPE M winCoeff)
    (η : ℕ) (E_t : ℝ) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (hEig : IsEigenSector H_tilde_blk η E_t ψ) (hnorm : ∑ i, Complex.normSq (ψ i) = 1) :
    let sys : QRegister (2 * 58) (2 * 58 + actAncillas bQPE bCat mOut mMid) :=
      .block 0 (2 * 58) (by omega)
    let anc : QRegister (actAncillas bQPE bCat mOut mMid)
      (2 * 58 + actAncillas bQPE bCat mOut mMid) :=
      .block (2 * 58) (actAncillas bQPE bCat mOut mMid) le_rfl
    let wIdBlk := blockedIdealUnitary bQPE bCat mOut mMid bAct M
      uCatIdeal uB uWinIdeal uIqftIdeal
    let uIdeal := wIdBlk.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
    let φ := QubitisedWalk.spectralPhase eLB lam E_t
    let qPos := uIqftIdeal.1 *ᵥ windowPhaseVec bQPE M winCoeff (2 * φ)
    let qNeg := uIqftIdeal.1 *ᵥ windowPhaseVec bQPE M winCoeff (-(2 * φ))
    ∃ w_pos w_neg : ℝ,
      0 ≤ w_pos ∧ 0 ≤ w_neg ∧ w_pos + w_neg ≤ 1 ∧
      ∀ y : Fin (2 ^ bQPE),
        (∑ a ∈ Finset.univ.filter (fun a ↦ (rQPEInAnc bQPE bCat mOut mMid).extractIndex a = y),
          anc.basisOutcomeProbability a uIdeal) =
        w_pos * Complex.normSq (qPos y) + w_neg * Complex.normSq (qNeg y) := by
  intro sys anc wIdBlk uIdeal φ qPos qNeg
  let cat := uCatIdeal.1 *ᵥ basisState (0 : Fin (2 ^ bCat))
  have hCatNorm : ∑ c, Complex.normSq (cat c) = 1 := by
    refine (sum_normSq_unitary_mulVec uCatIdeal (basisState 0)).trans ?_
    rw [Fintype.sum_eq_single 0 (fun c hc ↦ by simp [basisState, hc])]; simp [basisState]
  let rW := rWalkInWalkCat bCat mOut mMid
  let rComb := (rQPEInAct bQPE bCat mOut mMid).concat (rWalkCatInAct bQPE bCat mOut mMid)
    (rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid)
  let u1Id := (rCatInAct bQPE bCat mOut mMid).embedUnitary uCatIdeal
  let u2Id := (rQPEInAct bQPE bCat mOut mMid).embedUnitary uWinIdeal
  let u3Id := rComb.embedUnitary
    (QubitisedWalk.qpeMuxUnitary
      (affineScheduleFiber bAct M
        (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) *
          QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid) (rW.embedUnitary uB))
        (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid))))
  let u4Id := (rQPEInAct bQPE bCat mOut mMid).embedUnitary uIqftIdeal
  let e₁ := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
  let window0 := windowVec bQPE M winCoeff
  obtain ⟨hPin, he₁Norm, hElo, hEhi, hProj⟩ := hSOS.jordanRelation ψ E_t hEig.1 hnorm
  obtain ⟨vPlus, vMinus, _, hOrtho, hNormSum, _, _, _, hzPow⟩ :=
    QubitisedWalk.walkStepUnitary_eigen_of_energy (rAllInWalk mOut mMid) (rMidInWalk mOut mMid)
      uB e₁ hPin he₁Norm hSOS.hLamPos hElo hEhi hProj
  let cPos : ℂ := Complex.exp (-Complex.I * (M : ℂ) * (φ : ℂ))
  let cNeg : ℂ := Complex.exp (Complex.I * (M : ℂ) * (φ : ℂ))
  let wcPos := tensorWalkCat (cPos • vPlus) cat
  let wcNeg := tensorWalkCat (cNeg • vMinus) cat
  have hs1 : u1Id.1 *ᵥ sys.tensorState ψ (Pi.single 0 1) =
      tensorWCQPE (tensorWalkCat e₁ cat) (basisState 0) := by
    rw [sysAct_tensorState_zero_eq ψ]; dsimp only [u1Id, cat]
    rw [rCatInAct_eq_compose, QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      embedMatrix_rWalkCatInAct_mulVec, QRegister.embedUnitary_val,
      embedMatrix_rCatInWalkCat_mulVec]
  have hs2 : u2Id.1 *ᵥ (u1Id.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)) =
      tensorWCQPE (tensorWalkCat e₁ cat) window0 := by
    rw [hs1, QRegister.embedUnitary_val, embedMatrix_rQPEInAct_mulVec]
    dsimp only [window0]; rw [hWinZero]
  have hs3 : u3Id.1 *ᵥ tensorWCQPE (tensorWalkCat e₁ cat) window0 =
      tensorWCQPE wcPos (windowPhaseVec bQPE M winCoeff (2 * φ)) +
      tensorWCQPE wcNeg (windowPhaseVec bQPE M winCoeff (-(2 * φ))) := by
    funext g; dsimp only [u3Id]; rw [embed_qpeMuxUnitary_mulVec2]
    let m := (rQPEInAct bQPE bCat mOut mMid).extractIndex g
    let x := (rWalkCatInAct bQPE bCat mOut mMid).extractIndex g
    change ((affineScheduleFiber bAct M _ _ m).1 *ᵥ tensorWalkCat e₁ cat) x * window0 m =
      wcPos x * windowPhaseVec bQPE M winCoeff (2 * φ) m +
        wcNeg x * windowPhaseVec bQPE M winCoeff (-(2 * φ)) m
    by_cases hm : m.val ≤ M
    · have hEmb : affineScheduleFiber bAct M
          (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) *
            QubitisedWalk.reflPulledUnitary (inMidWalkCat bCat mOut mMid) (rW.embedUnitary uB))
          (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)) m =
          rW.embedUnitary (QubitisedWalk.walkStepUnitary (rAllInWalk mOut mMid)
            (rMidInWalk mOut mMid) uB ^ (2 * (m.val : ℤ) - (M : ℤ))) := by
        rw [embedUnitary_rWalkInWalkCat_reflIn, embedUnitary_rWalkInWalkCat_reflPulled,
          ← QRegister.embedUnitary_mul, ← embedUnitaryAffineScheduleFiber,
          affineScheduleFiber_ideal_eq_zpow
            (QubitisedWalk.reflInUnitary_mul_self _) (QubitisedWalk.reflPulledUnitary_mul_self _ _)
            hbAct hbQPE hMlo hMhi hm]
        rfl
      rw [hEmb, QRegister.embedUnitary_val, embedMatrix_rWalkInWalkCat_mulVec, hzPow]
      have hexp1 : Complex.exp (Complex.I * ((2 * (m.val : ℤ) - (M : ℤ) : ℤ) : ℂ) * (φ : ℂ)) =
          cPos * Complex.exp (Complex.I * (m.val : ℂ) * ((2 * φ : ℝ) : ℂ)) := by
        dsimp only [cPos]; rw [← Complex.exp_add]; exact congrArg Complex.exp (by push_cast; ring)
      have hexp2 : Complex.exp (-Complex.I * ((2 * (m.val : ℤ) - (M : ℤ) : ℤ) : ℂ) * (φ : ℂ)) =
          cNeg * Complex.exp (Complex.I * (m.val : ℂ) * ((-(2 * φ) : ℝ) : ℂ)) := by
        dsimp only [cNeg]; rw [← Complex.exp_add]; exact congrArg Complex.exp (by push_cast; ring)
      dsimp only [window0, windowVec, windowPhaseVec, wcPos, wcNeg, tensorWalkCat]
      simp only [hm, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hexp1, hexp2]; ring
    · have hw0 : window0 m = 0 := by dsimp only [window0, windowVec]; exact ite_eq_right hm
      have hp1 : windowPhaseVec bQPE M winCoeff (2 * φ) m = 0 := by
        dsimp only [windowPhaseVec]; exact ite_eq_right hm
      have hp2 : windowPhaseVec bQPE M winCoeff (-(2 * φ)) m = 0 := by
        dsimp only [windowPhaseVec]; exact ite_eq_right hm
      rw [hw0, hp1, hp2]; ring
  have huId : uIdeal = tensorWCQPE wcPos qPos + tensorWCQPE wcNeg qNeg := by
    have hstep : uIdeal =
        u4Id.1 *ᵥ (u3Id.1 *ᵥ (u2Id.1 *ᵥ (u1Id.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)))) := by
      dsimp only [uIdeal, wIdBlk, blockedIdealUnitary, u4Id, u3Id, u2Id, u1Id, rComb, rW]
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [hstep, hs2, hs3, Matrix.mulVec_add, QRegister.embedUnitary_val,
      embedMatrix_rQPEInAct_mulVec, embedMatrix_rQPEInAct_mulVec]
  have hwcOrtho : ∑ x, star (wcPos x) * wcNeg x = 0 := by
    dsimp only [wcPos, wcNeg]
    rw [inner_tensorWalkCat, QubitisedWalk.vecInner_smul_left, QubitisedWalk.vecInner_smul_right,
      hOrtho, mul_zero, mul_zero, zero_mul]
  have hcPosSq : Complex.normSq cPos = 1 := by
    dsimp only [cPos]
    rw [Complex.normSq_eq_norm_sq, show -Complex.I * (M : ℂ) * (φ : ℂ) =
        ((-(M * φ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, _root_.one_pow]
  have hcNegSq : Complex.normSq cNeg = 1 := by
    dsimp only [cNeg]
    rw [Complex.normSq_eq_norm_sq, show Complex.I * (M : ℂ) * (φ : ℂ) =
        ((M * φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, _root_.one_pow]
  have hwcSum : (∑ x, Complex.normSq (wcPos x)) + (∑ x, Complex.normSq (wcNeg x)) ≤ 1 := by
    dsimp only [wcPos, wcNeg]
    rw [sum_normSq_tensorWalkCat, sum_normSq_tensorWalkCat, hCatNorm, mul_one, mul_one]
    change QubitisedWalk.vecNormSq (cPos • vPlus) + QubitisedWalk.vecNormSq (cNeg • vMinus) ≤ 1
    rw [QubitisedWalk.vecNormSq_smul, QubitisedWalk.vecNormSq_smul, hcPosSq, hcNegSq, one_mul,
      one_mul,
      hNormSum]
  refine ⟨∑ x, Complex.normSq (wcPos x), ∑ x, Complex.normSq (wcNeg x),
    Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _,
    Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _, hwcSum, fun y ↦ ?_⟩
  rw [sum_filter_basisOutcomeProbability_eq anc (rQPEInAnc bQPE bCat mOut mMid) uIdeal y]
  dsimp only [anc]
  rw [ancAct_compose_rQPEInAnc bQPE bCat mOut mMid, huId,
    basisOutcomeProbability_rQPEInAct_ortho_branches wcPos wcNeg qPos qNeg hwcOrtho y]

/-- Statewise `L²` synthesis perturbation predicate on the eigen-sector. -/
noncomputable abbrev ImplQPEPertHyp (wOuter wInner2 M : ℕ)
    (uCatIdeal : Unitary (2 ^ 11)) (uB : Unitary (2 ^ nUB wOuter wInner2))
    (uWinIdeal uIqftIdeal : Unitary (2 ^ 16))
    (wImplBlk : Unitary (2 ^ (2 * 58 + actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2))))
    (δW : ℝ) : Prop :=
  ∀ (E_t : ℝ) (ψ : Fin (2 ^ (2 * 58)) → ℂ),
    IsEigenSector p450HBlocked 63 E_t ψ → (∑ i, Complex.normSq (ψ i) = 1) →
    let sys : QRegister (2 * 58) (2 * 58 + actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)) :=
      .block 0 (2 * 58) (by omega)
    let wIdBlk := BlockReflection.blockedIdealUnitary 16 11 (mOutUB wOuter) (mMidUB wInner2) 16 M
      uCatIdeal uB uWinIdeal uIqftIdeal
    let init := sys.tensorState ψ (Pi.single 0 1)
    ‖WithLp.toLp 2 (wImplBlk.1 *ᵥ init - wIdBlk.1 *ᵥ init)‖ ≤ δW

@[simp] theorem combARem_11_20_7_16 : combARem 11 20 7 16 = 23 := rfl

private theorem cos_sin_pi_pow_step_half (k : ℕ) {cPrev cMid sMid εPrev : ℝ}
    (hcPrev : |cos (π / 2 ^ k) - cPrev| ≤ εPrev)
    (hclo : (cMid - 1 / 10 ^ 25) ^ 2 ≤ (1 + cPrev) / 2 - εPrev / 2)
    (hchi : (1 + cPrev) / 2 + εPrev / 2 ≤ (cMid + 1 / 10 ^ 25) ^ 2)
    (hcm : 1 / 10 ^ 25 ≤ cMid)
    (hslo : (sMid - 1 / 10 ^ 20) ^ 2 ≤ (1 - cPrev) / 2 - εPrev / 2)
    (hshi : (1 - cPrev) / 2 + εPrev / 2 ≤ (sMid + 1 / 10 ^ 20) ^ 2)
    (hsm : 1 / 10 ^ 20 ≤ sMid) :
    |cos (π / 2 ^ (k + 1)) - cMid| ≤ 1 / 10 ^ 25 ∧
      |sin (π / 2 ^ (k + 1)) - sMid| ≤ 1 / 10 ^ 20 := by
  have hpi : 0 ≤ π := pi_pos.le
  have hθ0 : 0 ≤ π / 2 ^ k := by positivity
  have hθpi : π / 2 ^ k ≤ π :=
    div_le_self hpi (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hdiv : (π / 2 ^ k) / 2 = π / 2 ^ (k + 1) := by
    rw [div_div, ← pow_succ]
  rw [← hdiv]
  exact CliffordT.cos_sin_half_approx hθ0 hθpi hcPrev (by norm_num) hcm hclo hchi
    (by norm_num) hsm hslo hshi

private theorem cos_sin_pi_pow_bounds_4_to_8 :
    (|cos (π / 2 ^ 4) - 98078528040323044912618224 / 10 ^ 26| ≤ 1 / 10 ^ 25 ∧
      |sin (π / 2 ^ 4) - 19509032201612826784828487 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 5) - 99518472667219688624483695 / 10 ^ 26| ≤ 1 / 10 ^ 25 ∧
      |sin (π / 2 ^ 5) - 9801714032956060199419556 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 6) - 99879545620517239271477160 / 10 ^ 26| ≤ 1 / 10 ^ 25 ∧
      |sin (π / 2 ^ 6) - 4906767432741801425495498 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 7) - 99969881869620422011576565 / 10 ^ 26| ≤ 1 / 10 ^ 25 ∧
      |sin (π / 2 ^ 7) - 2454122852291228803173453 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 8) - 99992470183914454092164649 / 10 ^ 26| ≤ 1 / 10 ^ 25 ∧
      |sin (π / 2 ^ 8) - 1227153828571992607940826 / 10 ^ 26| ≤ 1 / 10 ^ 20) := by
  have h1 : |cos (π / 2 ^ 1) - 0| ≤ (0 : ℝ) := by
    rw [pow_one, cos_pi_div_two, sub_zero, abs_zero]
  have h2 := cos_sin_pi_pow_step_half 1 (cMid := 70710678118654752440084436 / 10 ^ 26)
    (sMid := 70710678118654752440084436 / 10 ^ 26) h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := cos_sin_pi_pow_step_half 2 (cMid := 92387953251128675612818319 / 10 ^ 26)
    (sMid := 38268343236508977172845998 / 10 ^ 26) h2.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := cos_sin_pi_pow_step_half 3 (cMid := 98078528040323044912618224 / 10 ^ 26)
    (sMid := 19509032201612826784828487 / 10 ^ 26) h3.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := cos_sin_pi_pow_step_half 4 (cMid := 99518472667219688624483695 / 10 ^ 26)
    (sMid := 9801714032956060199419556 / 10 ^ 26) h4.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 := cos_sin_pi_pow_step_half 5 (cMid := 99879545620517239271477160 / 10 ^ 26)
    (sMid := 4906767432741801425495498 / 10 ^ 26) h5.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 := cos_sin_pi_pow_step_half 6 (cMid := 99969881869620422011576565 / 10 ^ 26)
    (sMid := 2454122852291228803173453 / 10 ^ 26) h6.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 := cos_sin_pi_pow_step_half 7 (cMid := 99992470183914454092164649 / 10 ^ 26)
    (sMid := 1227153828571992607940826 / 10 ^ 26) h7.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h4, h5, h6, h7, h8⟩

private theorem cos_sin_pi_pow_bounds :
    (|cos (π / 2 ^ 4) - 98078528040323044912618224 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 4) - 19509032201612826784828487 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 5) - 99518472667219688624483695 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 5) - 9801714032956060199419556 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 6) - 99879545620517239271477160 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 6) - 4906767432741801425495498 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 7) - 99969881869620422011576565 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 7) - 2454122852291228803173453 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 8) - 99992470183914454092164649 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 8) - 1227153828571992607940826 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 9) - 99998117528260114265699044 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 9) - 613588464915447535964023 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 10) - 99999529380957617151158013 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 10) - 306795676296597627014537 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 11) - 99999882345170190992902571 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 11) - 153398018628476561230370 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 12) - 99999970586288221916022822 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 12) - 76699031874270452693857 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 13) - 99999992646571785114473148 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 13) - 38349518757139558907246 / 10 ^ 26| ≤ 1 / 10 ^ 20) ∧
    (|cos (π / 2 ^ 14) - 99999998161642929380834692 / 10 ^ 26| ≤ 1 / 10 ^ 20 ∧
      |sin (π / 2 ^ 14) - 19174759731070330743991 / 10 ^ 26| ≤ 1 / 10 ^ 20) := by
  obtain ⟨h4, h5, h6, h7, h8⟩ := cos_sin_pi_pow_bounds_4_to_8
  have h9 := cos_sin_pi_pow_step_half 8 (cMid := 99998117528260114265699044 / 10 ^ 26)
    (sMid := 613588464915447535964023 / 10 ^ 26) h8.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 := cos_sin_pi_pow_step_half 9 (cMid := 99999529380957617151158013 / 10 ^ 26)
    (sMid := 306795676296597627014537 / 10 ^ 26) h9.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 := cos_sin_pi_pow_step_half 10 (cMid := 99999882345170190992902571 / 10 ^ 26)
    (sMid := 153398018628476561230370 / 10 ^ 26) h10.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 := cos_sin_pi_pow_step_half 11 (cMid := 99999970586288221916022822 / 10 ^ 26)
    (sMid := 76699031874270452693857 / 10 ^ 26) h11.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := cos_sin_pi_pow_step_half 12 (cMid := 99999992646571785114473148 / 10 ^ 26)
    (sMid := 38349518757139558907246 / 10 ^ 26) h12.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h14 := cos_sin_pi_pow_step_half 13 (cMid := 99999998161642929380834692 / 10 ^ 26)
    (sMid := 19174759731070330743991 / 10 ^ 26) h13.1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have widen : ∀ {x : ℝ}, x ≤ 1 / 10 ^ 25 → x ≤ 1 / 10 ^ 20 := fun h ↦ h.trans (by norm_num)
  exact ⟨⟨widen h4.1, h4.2⟩, ⟨widen h5.1, h5.2⟩, ⟨widen h6.1, h6.2⟩, ⟨widen h7.1, h7.2⟩,
    ⟨widen h8.1, h8.2⟩, ⟨widen h9.1, h9.2⟩, ⟨widen h10.1, h10.2⟩, ⟨widen h11.1, h11.2⟩,
    ⟨widen h12.1, h12.2⟩, ⟨widen h13.1, h13.2⟩, ⟨widen h14.1, h14.2⟩⟩

private theorem trace_approx_rz_pi_pow (tr : CliffordT.GateTrace) (m : CliffordT.CyclotomicMat2)
    (k : ℕ) (cMid sMid : ℝ) (hm : tr.checkFrom .one = some m)
    (hd : m.d = m.a.conj) (hb : m.b = m.c.conj.neg)
    (hc : |cos (π / 2 ^ (k + 1)) - cMid| ≤ 1 / 10 ^ 20)
    (hs : |sin (π / 2 ^ (k + 1)) - sMid| ≤ 1 / 10 ^ 20)
    (hbound :
      CliffordT.cycCoordErrBound (CliffordT.cycReAB m.k m.a) m.k cMid (1 / 10 ^ 20) ^ 2 +
      CliffordT.cycCoordErrBound (CliffordT.cycImAB m.k m.a) m.k (-sMid) (1 / 10 ^ 20) ^ 2 +
      CliffordT.cycCoordErrBound (CliffordT.cycReAB m.k m.c) m.k 0 (1 / 10 ^ 20) ^ 2 +
      CliffordT.cycCoordErrBound (CliffordT.cycImAB m.k m.c) m.k 0 (1 / 10 ^ 20) ^ 2 ≤
        (78 / 10 ^ 11) ^ 2) :
    ‖tr.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ (k + 1))‖ ≤ 78 / 10 ^ 11 := by
  set θ : ℝ := π / 2 ^ (k + 1)
  have htheta : (2 * π / (2 : ℝ) ^ (k + 1)) / 2 = θ := by dsimp only [θ]; ring
  have hmat : CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ (k + 1)) =
      CliffordT.su2Matrix ((cos θ : ℂ) - Complex.I * (sin θ : ℂ)) 0 := by
    rw [CliffordT.rzMatrix_eq_su2Matrix, htheta]
  rw [hmat]
  refine CliffordT.traceCircuit_approx_su2Matrix tr m
    ((cos θ : ℂ) - Complex.I * (sin θ : ℂ)) 0 cMid (-sMid) 0 0 (1 / 10 ^ 20) (78 / 10 ^ 11)
    hm hd hb ?_ ?_ (by norm_num) (by norm_num) (by norm_num) hbound
  · have hre : ((cos θ : ℂ) - Complex.I * (sin θ : ℂ)).re = cos θ := by
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]; ring
    rw [hre]; exact hc
  · have him : ((cos θ : ℂ) - Complex.I * (sin θ : ℂ)).im - (-sMid) = -(sin θ - sMid) := by
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re]; ring
    rw [him, abs_neg]; exact hs

private theorem norm_rzPg4Word_sub_le :
    ‖CliffordT.rzPg4Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 4)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg4Word
    ⟨46, ⟨5217351, 2576456, -2270123, -1680429⟩, ⟨-25989, -2652354, 3776984, -2689108⟩,
      ⟨25989, -2689108, 3776984, -2652354⟩, ⟨5217351, 1680429, 2270123, -2576456⟩⟩
    3 (98078528040323044912618224 / 10 ^ 26) (19509032201612826784828487 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.1.1 cos_sin_pi_pow_bounds.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg5Word_sub_le :
    ‖CliffordT.rzPg5Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 5)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg5Word
    ⟨48, ⟨7139864, 11711573, -8650555, -1803451⟩, ⟨1698124, -2740608, 2177681, -339098⟩,
      ⟨-1698124, -339098, 2177681, -2740608⟩, ⟨7139864, 1803451, 8650555, -11711573⟩⟩
    4 (99518472667219688624483695 / 10 ^ 26) (9801714032956060199419556 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.1.1 cos_sin_pi_pow_bounds.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg6Word_sub_le :
    ‖CliffordT.rzPg6Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 6)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg6Word
    ⟨48, ⟨12508484, -2067945, 6349820, -8076264⟩, ⟨-2741185, 1737087, 284573, -2139534⟩,
      ⟨2741185, -2139534, 284573, 1737087⟩, ⟨12508484, 8076264, -6349820, 2067945⟩⟩
    5 (99879545620517239271477160 / 10 ^ 26) (4906767432741801425495498 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.1.1 cos_sin_pi_pow_bounds.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg7Word_sub_le :
    ‖CliffordT.rzPg7Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 7)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg7Word
    ⟨48, ⟨5572059, 6961642, 943122, -8877697⟩, ⟨-1092253, 6246681, -7741888, 4702002⟩,
      ⟨1092253, 4702002, -7741888, 6246681⟩, ⟨5572059, 8877697, -943122, -6961642⟩⟩
    6 (99969881869620422011576565 / 10 ^ 26) (2454122852291228803173453 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.1.1 cos_sin_pi_pow_bounds.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg8Word_sub_le :
    ‖CliffordT.rzPg8Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 8)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg8Word
    ⟨48, ⟨11989636, 700799, 3589355, -6068075⟩, ⟨2807938, 2250006, -5989927, 6221030⟩,
      ⟨-2807938, 6221030, -5989927, 2250006⟩, ⟨11989636, 6068075, -3589355, -700799⟩⟩
    7 (99992470183914454092164649 / 10 ^ 26) (1227153828571992607940826 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.1.1 cos_sin_pi_pow_bounds.2.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg9Word_sub_le :
    ‖CliffordT.rzPg9Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 9)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg9Word
    ⟨48, ⟨6162154, 9629994, -3107065, -5381524⟩, ⟨-5327573, 7488229, -5262382, -46097⟩,
      ⟨5327573, -46097, -5262382, 7488229⟩, ⟨6162154, 5381524, 3107065, -9629994⟩⟩
    8 (99998117528260114265699044 / 10 ^ 26) (613588464915447535964023 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.2.1.1 cos_sin_pi_pow_bounds.2.2.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg10Word_sub_le :
    ‖CliffordT.rzPg10Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 10)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg10Word
    ⟨48, ⟨6678547, 5700420, 1985507, -8581143⟩, ⟨-7777768, 4294350, 1704640, -6705075⟩,
      ⟨7777768, -6705075, 1704640, 4294350⟩, ⟨6678547, 8581143, -1985507, -5700420⟩⟩
    9 (99999529380957617151158013 / 10 ^ 26) (306795676296597627014537 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.2.2.1.1 cos_sin_pi_pow_bounds.2.2.2.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg11Word_sub_le :
    ‖CliffordT.rzPg11Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 11)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg11Word
    ⟨49, ⟨8190158, 8097365, 4048581, -13874395⟩, ⟨-10388093, 8527560, -1671698, -6163422⟩,
      ⟨10388093, -6163422, -1671698, 8527560⟩, ⟨8190158, 13874395, -4048581, -8097365⟩⟩
    10 (99999882345170190992902571 / 10 ^ 26) (153398018628476561230370 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.1.1 cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg12Word_sub_le :
    ‖CliffordT.rzPg12Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 12)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg12Word
    ⟨48, ⟨7998025, 11939252, -8118334, -476392⟩, ⟨-1026427, -570300, 1832953, -2021887⟩,
      ⟨1026427, -2021887, 1832953, -570300⟩, ⟨7998025, 476392, 8118334, -11939252⟩⟩
    11 (99999970586288221916022822 / 10 ^ 26) (76699031874270452693857 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.2.1.1
    cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg13Word_sub_le :
    ‖CliffordT.rzPg13Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 13)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg13Word
    ⟨48, ⟨10145005, 10045390, -7580551, 666029⟩, ⟨3025490, -2736936, 845122, 1541753⟩,
      ⟨-3025490, 1541753, 845122, -2736936⟩, ⟨10145005, -666029, 7580551, -10045390⟩⟩
    12 (99999992646571785114473148 / 10 ^ 26) (38349518757139558907246 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.2.2.1.1
    cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.2.2.1.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

private theorem norm_rzPg14Word_sub_le :
    ‖CliffordT.rzPg14Word.toCircuit.eval.1 - CliffordT.rzMatrix (2 * π / (2 : ℝ) ^ 14)‖ ≤
      78 / 10 ^ 11 :=
  trace_approx_rz_pi_pow CliffordT.rzPg14Word
    ⟨47, ⟨11437097, -947501, 1763880, -1550219⟩, ⟨-875010, -86045, 996696, -1323496⟩,
      ⟨875010, -1323496, 996696, -86045⟩, ⟨11437097, 1550219, -1763880, 947501⟩⟩
    13 (99999998161642929380834692 / 10 ^ 26) (19174759731070330743991 / 10 ^ 26)
    rfl rfl rfl cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.2.2.2.1
    cos_sin_pi_pow_bounds.2.2.2.2.2.2.2.2.2.2.2 (by
      unfold CliffordT.cycCoordErrBound CliffordT.cycReAB CliffordT.cycImAB CliffordT.s2Mid
      norm_num)

/-- Local single-qubit circuit for wire `r` of the ray-valid `11`-qubit phase-gradient catalyst,
omitting `rzPgCancel14Word` on wire `0`. -/
def pgWireRay11LocalCircuit (r : Fin 11) : Circuit 1 :=
  if r.val = 0 then
    Circuit.sequence [Circuit.H 0, CliffordT.rzPg14Word.toCircuit.inverse]
  else
    CliffordT.pgWireLocalCircuit (Fin.castAdd 3 r)

/-- Exact single-qubit unitary for wire `r` of the ray-valid `11`-qubit phase-gradient catalyst. -/
noncomputable def pgWireRay11LocalExact (r : Fin 11) : Unitary 2 :=
  if r.val = 0 then
    (CliffordT.rzUnitary (2 * π / (2 : ℝ) ^ 14))⁻¹ * Qubit.H
  else
    CliffordT.pgWireLocalExact (Fin.castAdd 3 r)

/-- Approximate `11`-qubit phase-gradient catalyst circuit omitting `rzPgCancel14Word`
(`1,036 T`, `0 TOFF`). -/
def approxPhaseGrad11Ray : Circuit 11 :=
  Circuit.sequence ((List.finRange 11).map fun r =>
    (pgWireRay11LocalCircuit r).onRegister (QRegister.singleton r))

/-- Exact `11`-qubit unitary realized by `approxPhaseGrad11Ray` up to `858 / 10 ^ 11`. -/
noncomputable def exactPhaseGrad11RayUnitary : Unitary (2 ^ 11) :=
  CliffordT.seqUnitary ((List.finRange 11).map fun r =>
    (QRegister.singleton r).embedUnitary (pgWireRay11LocalExact r))

/-- Unit-modulus global phase relating `exactPhaseGrad11RayUnitary *ᵥ |0⟩` to
`CircuitModular.phaseGradientLowFactor 11 3`. -/
noncomputable def phaseGrad11RayScalar : ℂ :=
  Complex.exp (Complex.I * (CliffordT.pgCancelBeta : ℂ))

theorem norm_phaseGrad11RayScalar : ‖phaseGrad11RayScalar‖ = 1 := by
  unfold phaseGrad11RayScalar
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I CliffordT.pgCancelBeta

theorem phaseGrad11RayScalar_ne_zero : phaseGrad11RayScalar ≠ 0 :=
  norm_ne_zero_iff.mp (norm_phaseGrad11RayScalar ▸ one_ne_zero)

@[simp] theorem approxPhaseGrad11Ray_count_toff :
    approxPhaseGrad11Ray.count PrimitiveGate.TOFF = 0 := by
  have hfr : List.finRange 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  simp [approxPhaseGrad11Ray, hfr, pgWireRay11LocalCircuit, CliffordT.pgWireLocalCircuit,
    Circuit.inverseGate]

@[simp] theorem approxPhaseGrad11Ray_count_t :
    approxPhaseGrad11Ray.count PrimitiveGate.T = 1036 := by
  have hfr : List.finRange 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  simp [approxPhaseGrad11Ray, hfr, pgWireRay11LocalCircuit, CliffordT.pgWireLocalCircuit,
    Circuit.inverseGate]

private theorem norm_inv_mul_H_sub_le_ray (c : Circuit 1) (θ δ : ℝ)
    (h : ‖c.eval.1 - CliffordT.rzMatrix θ‖ ≤ δ) :
    ‖(Circuit.sequence [Circuit.H 0, c.inverse]).eval.1 -
        ((CliffordT.rzUnitary θ)⁻¹ * Qubit.H).1‖ ≤ δ := by
  have hreg : ∀ U : Unitary 2, ((QRegister.singleton (0 : Fin 1)).embedUnitary U).1 = U.1 := by
    intro U
    have hs : QRegister.singleton (0 : Fin 1) = QRegister.whole 1 :=
      CoherentAlias.qreg_ext fun _ ↦ congrArg Fin.val (Subsingleton.elim _ _)
    rw [hs, QRegister.whole_embedUnitary]
  have hsub_eq :
      (Circuit.sequence [Circuit.H 0, c.inverse]).eval.1 -
          ((CliffordT.rzUnitary θ)⁻¹ * Qubit.H).1 =
        (c.inverse.eval.1 - (CliffordT.rzMatrix θ)ᴴ) * Qubit.H.1 := by
    simp only [Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity, Circuit.eval_single,
      one_mul, Submonoid.coe_mul, hreg, PrimitiveGate.eval, CliffordT.unitary_inv_val,
      CliffordT.rzUnitary]
    exact (sub_mul _ _ _).symm
  refine le_trans (le_of_eq (congrArg norm hsub_eq)) ?_
  calc ‖(c.inverse.eval.1 - (CliffordT.rzMatrix θ)ᴴ) * Qubit.H.1‖
      ≤ ‖c.inverse.eval.1 - (CliffordT.rzMatrix θ)ᴴ‖ * ‖Qubit.H.1‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖c.eval.1 - CliffordT.rzMatrix θ‖ * 1 := by
        rw [CliffordT.norm_inverse_sub_eq]
        gcongr
        exact CliffordT.unitary_opNorm_le_one Qubit.H
    _ ≤ δ := by rw [mul_one]; exact h

private theorem norm_pgWireRay11LocalCircuit_sub_le (r : Fin 11) :
    ‖(pgWireRay11LocalCircuit r).eval.1 - (pgWireRay11LocalExact r).1‖ ≤ 78 / 10 ^ 11 := by
  fin_cases r <;> dsimp only [pgWireRay11LocalCircuit, pgWireRay11LocalExact, Fin.val_zero,
      Fin.castAdd_mk, CliffordT.pgWireLocalCircuit, CliffordT.pgWireLocalExact, ↓reduceIte]
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg14Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg13Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg12Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg11Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg10Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg9Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg8Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg7Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg6Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg5Word_sub_le
  · exact norm_inv_mul_H_sub_le_ray _ _ _ norm_rzPg4Word_sub_le

/-- Tightened `L2Operator` norm bound `≤ 858 / 10 ^ 11` (`8.58e-9`) for `approxPhaseGrad11Ray`. -/
theorem norm_approxPhaseGrad11Ray_sub_le :
    ‖approxPhaseGrad11Ray.eval.1 - exactPhaseGrad11RayUnitary.1‖ ≤ 858 / 10 ^ 11 := by
  let cs := (List.finRange 11).map fun r =>
    (pgWireRay11LocalCircuit r).onRegister (QRegister.singleton r)
  let us := (List.finRange 11).map fun r =>
    (QRegister.singleton r).embedUnitary (pgWireRay11LocalExact r)
  have hseq : ‖(Circuit.sequence cs).eval.1 - (CliffordT.seqUnitary us).1‖ ≤
      ((List.finRange 11).map fun _ => (78 / 10 ^ 11 : ℝ)).sum := by
    have hlen : cs.length = us.length := by simp [cs, us]
    have hzip : ((cs.zip us).map fun p => ‖p.1.eval.1 - p.2.1‖).sum ≤
        ((List.finRange 11).map fun _ => (78 / 10 ^ 11 : ℝ)).sum := by
      have hfr : List.finRange 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
      have hr (r : Fin 11) :
          ‖((pgWireRay11LocalCircuit r).onRegister (QRegister.singleton r)).eval.1 -
              ((QRegister.singleton r).embedUnitary (pgWireRay11LocalExact r)).1‖ ≤
            78 / 10 ^ 11 :=
        le_trans (CliffordT.norm_onRegister_sub_le (QRegister.singleton r) _ _)
          (norm_pgWireRay11LocalCircuit_sub_le r)
      dsimp only [cs, us]; rw [hfr]
      simp only [List.map, List.zip_cons_cons, List.zip_nil_right, List.sum_cons, List.sum_nil]
      linarith [hr 0, hr 1, hr 2, hr 3, hr 4, hr 5, hr 6, hr 7, hr 8, hr 9, hr 10]
    have hseq_eq : CliffordT.seqUnitary us = us.reverse.prod := by
      clear hzip hlen cs
      induction us with
      | nil => rfl
      | cons u rest ih => simp [CliffordT.seqUnitary, ih, List.reverse_cons, List.prod_append]
    rw [hseq_eq]
    exact le_trans (Catalyst.l2_opNorm_circuit_sequence_sub_le cs us hlen) hzip
  refine le_trans hseq ?_
  have hfr : List.finRange 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  rw [hfr]; norm_num

private theorem exactPhaseGrad11Unitary_eq_ray_mul_cancel :
    WalkQPECat11ReducedRefl.exactPhaseGrad11Unitary =
      exactPhaseGrad11RayUnitary *
        (QRegister.singleton (0 : Fin 11)).embedUnitary
          (CliffordT.rzUnitary (2 * CliffordT.pgCancelBeta)) := by
  have hfr : List.finRange 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
  have h0 :
      (QRegister.singleton (0 : Fin 11)).embedUnitary
        (CliffordT.pgWireLocalExact (Fin.castAdd 3 (0 : Fin 11))) =
      (QRegister.singleton (0 : Fin 11)).embedUnitary (pgWireRay11LocalExact 0) *
        (QRegister.singleton (0 : Fin 11)).embedUnitary
          (CliffordT.rzUnitary (2 * CliffordT.pgCancelBeta)) := by
    rw [← QRegister.embedUnitary_mul]; rfl
  have htail (r : Fin 11) (hr : r.val ≠ 0) :
      CliffordT.pgWireLocalExact (Fin.castAdd 3 r) = pgWireRay11LocalExact r := by
    simp [pgWireRay11LocalExact, hr]
  unfold WalkQPECat11ReducedRefl.exactPhaseGrad11Unitary exactPhaseGrad11RayUnitary
  rw [hfr]; simp only [List.map, CliffordT.seqUnitary]
  rw [h0, htail 1 (by decide), htail 2 (by decide), htail 3 (by decide), htail 4 (by decide),
    htail 5 (by decide), htail 6 (by decide), htail 7 (by decide), htail 8 (by decide),
    htail 9 (by decide), htail 10 (by decide)]
  simp only [mul_assoc]

/-- Exact action of `exactPhaseGrad11RayUnitary` on `|0^11⟩`: prepares
`phaseGrad11RayScalar • CircuitModular.phaseGradientLowFactor 11 3`. -/
theorem exactPhaseGrad11RayUnitary_mulVec_zero :
    exactPhaseGrad11RayUnitary.1 *ᵥ basisState 0 =
      phaseGrad11RayScalar •
        CircuitModular.phaseGradientLowFactor
        11 3 := by
  have hcancel_zero :
      ((QRegister.singleton (0 : Fin 11)).embedUnitary
          (CliffordT.rzUnitary (2 * CliffordT.pgCancelBeta))).1 *ᵥ basisState 0 =
        phaseGrad11RayScalar⁻¹ • basisState 0 := by
    let r0 := QRegister.singleton (0 : Fin 11)
    have hex : r0.extractIndex (0 : Fin (2 ^ 11)) = 0 :=
      (QRegister.extractIndex_eq_zero_iff _ _).mpr fun _ => basisBits_zero_at _ _
    have hr0 : r0.replaceIndex (0 : Fin (2 ^ 11)) 0 = 0 := by
      rw [← hex, r0.replaceIndex_extractIndex]
    have hloc :
        (CliffordT.rzUnitary (2 * CliffordT.pgCancelBeta)).1 *ᵥ (Pi.single (0 : Fin 2) 1) =
          phaseGrad11RayScalar⁻¹ • Pi.single (0 : Fin 2) 1 := by
      funext i
      have hhalf : (2 * CliffordT.pgCancelBeta) / 2 = CliffordT.pgCancelBeta := by ring
      rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
      · simp [CliffordT.rzUnitary, CliffordT.rzMatrix, hhalf, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, phaseGrad11RayScalar, ← Complex.exp_neg, neg_mul]
      · simp [CliffordT.rzUnitary, CliffordT.rzMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [QRegister.embedUnitary_val, basisState, r0.embedMatrix_mulVec_single_factors, hex, hloc,
      r0.tensorState_smul_left, r0.tensorState_single_replaceIndex, hr0]
  have h11 :
      WalkQPECat11ReducedRefl.exactPhaseGrad11Unitary.1 *ᵥ basisState 0 =
        phaseGrad11RayScalar⁻¹ • (exactPhaseGrad11RayUnitary.1 *ᵥ basisState 0) := by
    rw [exactPhaseGrad11Unitary_eq_ray_mul_cancel, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      hcancel_zero, Matrix.mulVec_smul]
  rw [WalkQPECat11ReducedRefl.exactPhaseGrad11Unitary_mulVec_zero] at h11
  calc exactPhaseGrad11RayUnitary.1 *ᵥ basisState 0
      = (phaseGrad11RayScalar * phaseGrad11RayScalar⁻¹) •
          (exactPhaseGrad11RayUnitary.1 *ᵥ basisState 0) := by
          rw [mul_inv_cancel₀ phaseGrad11RayScalar_ne_zero, one_smul]
    _ = phaseGrad11RayScalar •
          (phaseGrad11RayScalar⁻¹ • (exactPhaseGrad11RayUnitary.1 *ᵥ basisState 0)) :=
          mul_smul _ _ _
    _ = phaseGrad11RayScalar •
      CircuitModular.phaseGradientLowFactor
      11 3 := by rw [← h11]

attribute [irreducible] pgWireRay11LocalCircuit approxPhaseGrad11Ray

/-! ### Turnkey `Ray1036` + `Hi14247` / `Fast12603` End-to-End QPE Wrappers -/

end MultiGearQPE

namespace TrigCert2

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DataArrays Real
open scoped BigOperators

attribute [local irreducible] leafAngleTableArr oneBodyAngleTableArr

end TrigCert2

namespace MidpointCert

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DataArrays Operator Matrix Real
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RefEnergy
open TrigCert2
open scoped Matrix

/-! ## Section 1: Kernel-Certified `319`-Row `ℓ₂` Midpoint Rounding Bounds -/

end MidpointCert

/-! ## Consolidated Public Exports under `DihedralWalkQPE` -/

export ApproxIqft16 (
  fastIqft16Circuit fastIqft16Circuit_count_toff fastIqft16Circuit_count_t
  norm_fastIqft16Circuit_sub_le
)

export MultiGearQPE (
  outRemWidth combARem combAncillas combQubits combWalkReflRegs CleanWalkRefl2
  WalkRefl2ErrLe P450RefVarBound ReordSosHyp RealizesP450GroundQPE ValidClampedBox
  combARem_11_20_7_16 pgWireRay11LocalCircuit pgWireRay11LocalExact approxPhaseGrad11Ray
  exactPhaseGrad11RayUnitary phaseGrad11RayScalar norm_phaseGrad11RayScalar
  phaseGrad11RayScalar_ne_zero approxPhaseGrad11Ray_count_toff approxPhaseGrad11Ray_count_t
  norm_approxPhaseGrad11Ray_sub_le exactPhaseGrad11RayUnitary_mulVec_zero
)

end DihedralWalkQPE

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
