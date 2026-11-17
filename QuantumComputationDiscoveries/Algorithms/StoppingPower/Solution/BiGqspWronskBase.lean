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
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ApexOffsetHoist

set_option linter.style.longLine false
@[expose] public section
set_option exponentiation.threshold 2048

namespace QuantumComputation.Specs.StoppingPowerSolution
noncomputable section Gqsp0_SwarUnpack
section
set_option compiler.extract_closed false
namespace GqspWronskian62592
section FastKernelHelpers
set_option maxRecDepth 600000
open List (length sum)
local instance (priority :=
  1000000) instLoc_TwoAngleStage2Cert_gqsp_Common_1InstNeZeroTw (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Real Operator Matrix Circuit SpecsAux
open SpecsAux.SpecMirror PhaseGradSignalRot
open TFreeLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open CatalyzedLaurentGQSPBridge
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open BidirectionalIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
open TwoAngleBiGqspVerifierBridge
open scoped Matrix Matrix.Norms.L2Operator BigOperators
noncomputable def gqsp_tramp {α : Type} (x : α) : α := x
noncomputable def gqsp_applyNat0Bool (f : ℕ → Bool) (x : ℕ) : Bool :=
  @Nat.casesOn (fun _ => Bool) (Nat.add 1 x) false f
theorem gqsp_applyNat0Bool_eq (f : ℕ → Bool) (x : ℕ) : gqsp_applyNat0Bool f x = f x :=
  congrArg (@Nat.casesOn (fun _ => Bool) · false f) (Nat.one_add x)
noncomputable def gqsp_applyNat1Bool (f : ℕ → ℕ → Bool) (x : ℕ) : ℕ → Bool :=
  @Nat.casesOn (fun _ => ℕ → Bool) (Nat.add 1 x) (fun _ => false) f
theorem gqsp_applyNat1Bool_eq (f : ℕ → ℕ → Bool) (x : ℕ) : gqsp_applyNat1Bool f x = f x :=
  congrArg (@Nat.casesOn (fun _ => ℕ → Bool) · (fun _ => false) f) (Nat.one_add x)
noncomputable def gqsp_applyNat2Bool (f : ℕ → ℕ → ℕ → Bool) (x : ℕ) : ℕ → ℕ → Bool :=
  @Nat.casesOn (fun _ => ℕ → ℕ → Bool) (Nat.add 1 x) (fun _ _ => false) f
theorem gqsp_applyNat2Bool_eq (f : ℕ → ℕ → ℕ → Bool) (x : ℕ) : gqsp_applyNat2Bool f x = f x :=
  congrArg (@Nat.casesOn (fun _ => ℕ → ℕ → Bool) · (fun _ _ => false) f) (Nat.one_add x)
private theorem gqsp_tzAux_succ (n x : ℕ) : PhaseGradSignalRot.trailingZeros42Aux (n + 1) x =
    if x = 0 then n + 1 else if x % 2 = 0 then 1 + PhaseGradSignalRot.trailingZeros42Aux n (x / 2)
    else 0 := rfl
private theorem gqsp_tzAux_zero : ∀ a : ℕ, PhaseGradSignalRot.trailingZeros42Aux a 0 = a
  | 0 => rfl
  | a + 1 => by rw [gqsp_tzAux_succ a 0, ite_eq_left rfl]
private theorem gqsp_tzAux_add : ∀ (a b c : ℕ),
    PhaseGradSignalRot.trailingZeros42Aux (a + b) c =
      if c % 2 ^ a = 0 then a + PhaseGradSignalRot.trailingZeros42Aux b (c / 2 ^ a)
      else PhaseGradSignalRot.trailingZeros42Aux a (c % 2 ^ a)
  | 0, b, c => by
      rw [Nat.zero_add, Nat.pow_zero, Nat.mod_one, ite_eq_left rfl, Nat.zero_add, Nat.div_one]
  | a + 1, b, c => by
      rw [show a + 1 + b = (a + b) + 1 by omega, gqsp_tzAux_succ (a + b) c]
      by_cases hc0 : c = 0
      · rw [hc0, ite_eq_left rfl, Nat.zero_mod, ite_eq_left rfl, Nat.zero_div, gqsp_tzAux_zero]
        omega
      · rw [ite_eq_right hc0]
        have hmod2 : (c % 2 ^ (a + 1)) % 2 = c % 2 :=
          Nat.mod_mod_of_dvd c ⟨2 ^ a, by rw [Nat.pow_succ, Nat.mul_comm]⟩
        by_cases hpar : c % 2 = 0
        · rw [ite_eq_left hpar, gqsp_tzAux_add a b (c / 2)]
          have hr : (c % 2 ^ (a + 1)) / 2 = (c / 2) % 2 ^ a := by
            rw [Nat.pow_succ, Nat.mod_mul_left_div_self]
          have hrem_div := Nat.div_add_mod (c % 2 ^ (a + 1)) 2
          by_cases hdiv0 : (c / 2) % 2 ^ a = 0
          · rw [ite_eq_left hdiv0, ite_eq_left (by omega), Nat.div_div_eq_div_mul,
              Nat.mul_comm 2 (2 ^ a), ← Nat.pow_succ, Nat.succ_eq_add_one]
            omega
          · have hm_ne0 : ¬ c % 2 ^ (a + 1) = 0 := by omega
            rw [ite_eq_right hdiv0, ite_eq_right hm_ne0, gqsp_tzAux_succ a, ite_eq_right hm_ne0,
              ite_eq_left (hmod2.trans hpar), hr]
        · have hm_ne0 : ¬ c % 2 ^ (a + 1) = 0 := fun hm0 ↦ hpar (by rw [← hmod2, hm0])
          rw [ite_eq_right hpar, ite_eq_right hm_ne0, gqsp_tzAux_succ a, ite_eq_right hm_ne0,
            hmod2, ite_eq_right hpar]
private theorem gqsp_ctz_split (a b c m : ℕ) (hm : m = 2 ^ a - 1) (fa fb : ℕ → ℕ)
    (hfa : ∀ x, fa x = PhaseGradSignalRot.trailingZeros42Aux a x)
    (hfb : ∀ x, fb x = PhaseGradSignalRot.trailingZeros42Aux b x) :
    (@Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c m) 0) (fa (Nat.land c m))
      (Nat.add a (fb (Nat.shiftRight c a)))) = PhaseGradSignalRot.trailingZeros42Aux (a + b) c := by
  rw [show Nat.land c m = c % 2 ^ a by rw [hm, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod],
    show Nat.shiftRight c a = c / 2 ^ a from Nat.shiftRight_eq_div_pow c a, gqsp_tzAux_add a b c]
  cases hb : Nat.beq (c % 2 ^ a) 0
  · rw [ite_eq_right (fun h ↦ Bool.noConfusion (hb.symm.trans (Nat.beq_eq.mpr h))), hfa]
  · rw [ite_eq_left (Nat.beq_eq.mp hb), Nat.add_eq, hfb]
noncomputable def gqsp_ctz1 (c : ℕ) : ℕ :=
  @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c 1) 0) 0 1
noncomputable def gqsp_ctz2 (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c 1) 0)
  (gqsp_ctz1 (Nat.land c 1)) (Nat.add 1 (gqsp_ctz1 (Nat.shiftRight c 1)))
noncomputable def gqsp_ctz4 (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c 3) 0)
  (gqsp_ctz2 (Nat.land c 3)) (Nat.add 2 (gqsp_ctz2 (Nat.shiftRight c 2)))
noncomputable def gqsp_ctz8 (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c 15) 0)
  (gqsp_ctz4 (Nat.land c 15)) (Nat.add 4 (gqsp_ctz4 (Nat.shiftRight c 4)))
noncomputable def gqsp_ctz16 (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c 255) 0)
  (gqsp_ctz8 (Nat.land c 255)) (Nat.add 8 (gqsp_ctz8 (Nat.shiftRight c 8)))
noncomputable def gqsp_ctz32 (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ)
  (Nat.beq (Nat.land c 65535) 0) (gqsp_ctz16 (Nat.land c 65535))
  (Nat.add 16 (gqsp_ctz16 (Nat.shiftRight c 16)))
noncomputable def gqsp_ctz10 (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ) (Nat.beq (Nat.land c 255) 0)
  (gqsp_ctz8 (Nat.land c 255)) (Nat.add 8 (gqsp_ctz2 (Nat.shiftRight c 8)))
noncomputable def gqsp_ctz42Bin (c : ℕ) : ℕ := @Bool.casesOn (fun _ => ℕ)
  (Nat.beq (Nat.land c 4294967295) 0) (gqsp_ctz32 (Nat.land c 4294967295))
  (Nat.add 32 (gqsp_ctz10 (Nat.shiftRight c 32)))
private theorem gqsp_ctz42Bin_eq (c : ℕ) :
    gqsp_ctz42Bin c = PhaseGradSignalRot.trailingZeros42 c := by
  have h1 (x : ℕ) : gqsp_ctz1 x = PhaseGradSignalRot.trailingZeros42Aux 1 x := by
    unfold gqsp_ctz1
    rw [gqsp_tzAux_succ 0 x, show PhaseGradSignalRot.trailingZeros42Aux 0 (x / 2) = 0 from rfl,
      show Nat.land x 1 = x % 2 by rw [Nat.land_eq, Nat.and_one_is_mod]]
    by_cases hx0 : x = 0
    · subst hx0
      rfl
    · rw [ite_eq_right hx0]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · rw [h]
        rfl
      · rw [h]
        rfl
  have h2 (x) : gqsp_ctz2 x = _ := gqsp_ctz_split 1 1 x 1 rfl _ _ h1 h1
  have h4 (x) : gqsp_ctz4 x = _ := gqsp_ctz_split 2 2 x 3 rfl _ _ h2 h2
  have h8 (x) : gqsp_ctz8 x = _ := gqsp_ctz_split 4 4 x 15 rfl _ _ h4 h4
  have h16 (x) : gqsp_ctz16 x = _ := gqsp_ctz_split 8 8 x 255 rfl _ _ h8 h8
  have h32 (x) : gqsp_ctz32 x = _ := gqsp_ctz_split 16 16 x 65535 rfl _ _ h16 h16
  exact gqsp_ctz_split 32 10 c 4294967295 rfl _ _ h32
    (fun x ↦ gqsp_ctz_split 8 2 x 255 rfl _ _ h8 h2)
noncomputable def gqsp_forceLitCat (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  @Nat.casesOn (fun _ => ℕ) (Nat.add 1 x) 0 f
theorem gqsp_forceLitCat_eq (x : ℕ) (f : ℕ → ℕ) : gqsp_forceLitCat x f = f x :=
  congrArg (@Nat.casesOn (fun _ => ℕ) · 0 f) (Nat.one_add x)
noncomputable def gqsp_applyNatCat (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  @Nat.casesOn (fun _ => ℕ) (Nat.add 1 x) 0 f
theorem gqsp_applyNatCat_eq (f : ℕ → ℕ) (x : ℕ) : gqsp_applyNatCat f x = f x :=
  congrArg (@Nat.casesOn (fun _ => ℕ) · 0 f) (Nat.one_add x)
noncomputable def gqsp_applyNatPairCat (f : ℕ → List ℕ × ℕ) (x : ℕ) : List ℕ × ℕ :=
  @Nat.casesOn (fun _ => List ℕ × ℕ) (Nat.add 1 x) ([], 0) f
theorem gqsp_applyNatPairCat_eq (f : ℕ → List ℕ × ℕ) (x : ℕ) :
    gqsp_applyNatPairCat f x = f x :=
  congrArg (@Nat.casesOn (fun _ => List ℕ × ℕ) · ([], 0) f) (Nat.one_add x)
noncomputable def gqsp_pLo_0 (_ : ℕ) : ℕ := 0x1000000000000000000000000
noncomputable def gqsp_pLo_1 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_0 nx) nx) 52
noncomputable def gqsp_pLo_2 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_1 nx) nx) 52
noncomputable def gqsp_pLo_3 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_2 nx) nx) 52
noncomputable def gqsp_pLo_4 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_3 nx) nx) 52
noncomputable def gqsp_pLo_5 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_4 nx) nx) 52
noncomputable def gqsp_pLo_6 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_5 nx) nx) 52
noncomputable def gqsp_pLo_7 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_6 nx) nx) 52
noncomputable def gqsp_pLo_8 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_7 nx) nx) 52
noncomputable def gqsp_pLo_9 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_8 nx) nx) 52
noncomputable def gqsp_pLo_10 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_9 nx) nx) 52
noncomputable def gqsp_pLo_11 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_10 nx) nx) 52
noncomputable def gqsp_pLo_12 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_11 nx) nx) 52
noncomputable def gqsp_pLo_13 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_12 nx) nx) 52
noncomputable def gqsp_pLo_14 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_13 nx) nx) 52
noncomputable def gqsp_pLo_15 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_14 nx) nx) 52
noncomputable def gqsp_pLo_16 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_15 nx) nx) 52
noncomputable def gqsp_pLo_17 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_16 nx) nx) 52
noncomputable def gqsp_pLo_18 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_17 nx) nx) 52
noncomputable def gqsp_pLo_19 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_18 nx) nx) 52
noncomputable def gqsp_pLo_20 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_19 nx) nx) 52
noncomputable def gqsp_pLo_21 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_20 nx) nx) 52
noncomputable def gqsp_pLo_22 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_21 nx) nx) 52
noncomputable def gqsp_pLo_23 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_22 nx) nx) 52
noncomputable def gqsp_pLo_24 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_23 nx) nx) 52
noncomputable def gqsp_pLo_25 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_24 nx) nx) 52
noncomputable def gqsp_pLo_26 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_25 nx) nx) 52
noncomputable def gqsp_pLo_27 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_26 nx) nx) 52
noncomputable def gqsp_pLo_28 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_27 nx) nx) 52
noncomputable def gqsp_pLo_29 (nx : ℕ) : ℕ := Nat.shiftRight (Nat.mul (gqsp_pLo_28 nx) nx) 52
noncomputable def gqsp_cosP15 (nx : ℕ) : ℕ :=
  Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add (Nat.add (0) (Nat.mul 0x6f99461a1e9e1432dcb6000000 (gqsp_pLo_0 nx)))
  (Nat.mul 0x4a662ebc146962cc932400000 (gqsp_pLo_4 nx)))
  (Nat.mul 0xb5646830f4d02dd5840000 (gqsp_pLo_8 nx)))
  (Nat.mul 0x3e8a65c6c052cf28000 (gqsp_pLo_12 nx))) (Nat.mul 0x5dd576018094400 (gqsp_pLo_16 nx)))
  (Nat.mul 0x34e29e21380 (gqsp_pLo_20 nx))) (Nat.mul 0xd97268 (gqsp_pLo_24 nx)))
  (Nat.mul 0x1d (gqsp_pLo_28 nx))
noncomputable def gqsp_cosN15 (nx : ℕ) : ℕ :=
  Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add (Nat.add (0) (Nat.mul 0x37cca30d0f4f0a196e5b000000 (gqsp_pLo_2 nx)))
  (Nat.mul 0x27adf6cab58d8a06b4e00000 (gqsp_pLo_6 nx)))
  (Nat.mul 0x203f5c7a7b2ab2d0a0000 (gqsp_pLo_10 nx)))
  (Nat.mul 0x57f81ea1688afc000 (gqsp_pLo_14 nx))) (Nat.mul 0x4e8062b94f200 (gqsp_pLo_18 nx)))
  (Nat.mul 0x1d4deb040 (gqsp_pLo_22 nx))) (Nat.mul 0x55a4 (gqsp_pLo_26 nx))
noncomputable def gqsp_sinP15 (nx : ℕ) : ℕ :=
  Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add (Nat.add (0) (Nat.mul 0x6f99461a1e9e1432dcb6000000 (gqsp_pLo_1 nx)))
  (Nat.mul 0xee13c8c041513c283d400000 (gqsp_pLo_5 nx)))
  (Nat.mul 0x142799cc8cfaafc2640000 (gqsp_pLo_9 nx)))
  (Nat.mul 0x4cf91acd3b799c8000 (gqsp_pLo_13 nx))) (Nat.mul 0x58506f10790400 (gqsp_pLo_17 nx)))
  (Nat.mul 0x284b232580 (gqsp_pLo_21 nx))) (Nat.mul 0x8b2a8 (gqsp_pLo_25 nx)))
  (Nat.mul 0x1 (gqsp_pLo_29 nx))
noncomputable def gqsp_sinN15 (nx : ℕ) : ℕ :=
  Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add
  (Nat.add (Nat.add (0) (Nat.mul 0x12998baf051a58b324c9000000 (gqsp_pLo_3 nx)))
  (Nat.mul 0x5ab234187a6816eac200000 (gqsp_pLo_7 nx)))
  (Nat.mul 0x2ee7cc55103e1b5e0000 (gqsp_pLo_11 nx))) (Nat.mul 0x5dd5760180944000 (gqsp_pLo_15 nx)))
  (Nat.mul 0x421b45a98600 (gqsp_pLo_19 nx))) (Nat.mul 0x1462b9c0 (gqsp_pLo_23 nx)))
  (Nat.mul 0x32c (gqsp_pLo_27 nx))
private noncomputable def gqsp_pLo (nx : ℕ) : ℕ → ℕ
  | 0 => 0x1000000000000000000000000
  | k + 1 => Nat.shiftRight (Nat.mul (gqsp_pLo nx k) nx) 52
private noncomputable def gqsp_pHi (nx : ℕ) : ℕ → ℕ
  | 0 => 0x1000000000000000000000000
  | k + 1 => Nat.add (Nat.shiftRight (Nat.mul (gqsp_pHi nx k) nx) 52) 1
private noncomputable def gqsp_delta4 : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * gqsp_delta4 k + 1
private theorem gqsp_pLo_pHi_bounds (nx : ℕ) : ∀ k ≤ 29,
    2 ^ 1412 * gqsp_pLo nx k ≤ nx ^ k * 2 ^ (52 * (29 - k)) ∧
      nx ^ k * 2 ^ (52 * (29 - k)) ≤ 2 ^ 1412 * gqsp_pHi nx k
  | 0, _ => by
      simp only [gqsp_pLo, gqsp_pHi, Nat.pow_zero, Nat.sub_zero,
        (by rw [show (0x1000000000000000000000000 : ℕ) = 2 ^ 96 from rfl, ← Nat.pow_add, one_mul] :
          2 ^ 1412 * (0x1000000000000000000000000 : ℕ) = 1 * 2 ^ (52 * 29)), le_refl, and_self]
  | k + 1, hk => by
      rcases gqsp_pLo_pHi_bounds nx k (by omega) with ⟨hlo, hhi⟩
      have hexact : nx ^ k * 2 ^ (52 * (29 - k)) * nx =
          2 ^ 52 * (nx ^ (k + 1) * 2 ^ (52 * (29 - (k + 1)))) := by
        rw [show 2 ^ (52 * (29 - k)) = 2 ^ 52 * 2 ^ (52 * (29 - (k + 1))) by
          rw [← Nat.pow_add, show 52 + 52 * (29 - (k + 1)) = 52 * (29 - k) by omega], Nat.pow_succ]
        ring
      have hp52 : 0 < 2 ^ 52 := Nat.two_pow_pos 52
      simp only [gqsp_pLo, gqsp_pHi,
        show ∀ a b : ℕ, Nat.shiftRight a b = a / 2 ^ b from Nat.shiftRight_eq_div_pow,
        Nat.mul_eq, Nat.add_eq]
      refine ⟨Nat.le_of_mul_le_mul_left ?_ hp52, Nat.le_of_mul_le_mul_left ?_ hp52⟩
      · have hdiv1 := Nat.div_add_mod (gqsp_pLo nx k * nx) (2 ^ 52)
        rw [← hexact, show 2 ^ 52 * (2 ^ 1412 * (gqsp_pLo nx k * nx / 2 ^ 52)) =
            2 ^ 1412 * (2 ^ 52 * (gqsp_pLo nx k * nx / 2 ^ 52)) by ring]
        exact (Nat.mul_le_mul_left _ (by omega : 2 ^ 52 * (gqsp_pLo nx k * nx / 2 ^ 52) ≤
          gqsp_pLo nx k * nx)).trans
          ((Nat.mul_assoc _ _ _).symm.le.trans (Nat.mul_le_mul_right nx hlo))
      · have hdiv2 := Nat.div_add_mod (gqsp_pHi nx k * nx) (2 ^ 52)
        have hmod2 := Nat.mod_lt (gqsp_pHi nx k * nx) hp52
        rw [← hexact, show 2 ^ 52 * (2 ^ 1412 * (gqsp_pHi nx k * nx / 2 ^ 52 + 1)) =
            2 ^ 1412 * (2 ^ 52 * (gqsp_pHi nx k * nx / 2 ^ 52 + 1)) by ring]
        exact (Nat.mul_le_mul_right nx hhi).trans
          ((Nat.mul_assoc _ _ _).le.trans (Nat.mul_le_mul_left _ (by
            rw [Nat.mul_add, Nat.mul_one]
            omega)))
private theorem gqsp_pHi_le_pLo_add_delta4 (nx : ℕ) (hnx : nx ≤ 4 * 2 ^ 52) :
    ∀ k, gqsp_pHi nx k ≤ gqsp_pLo nx k + gqsp_delta4 k
  | 0 => by simp [gqsp_pHi, gqsp_pLo, gqsp_delta4]
  | k + 1 => by
      have hmul : gqsp_pHi nx k * nx ≤ gqsp_pLo nx k * nx + (4 * gqsp_delta4 k) * 2 ^ 52 :=
        (Nat.mul_le_mul_right nx (gqsp_pHi_le_pLo_add_delta4 nx hnx k)).trans (by
          rw [Nat.add_mul, show (4 * gqsp_delta4 k) * 2 ^ 52 = gqsp_delta4 k * (4 * 2 ^ 52) by ring]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hnx) _)
      simp only [gqsp_pHi, gqsp_pLo, gqsp_delta4,
        show ∀ a b : ℕ, Nat.shiftRight a b = a / 2 ^ b from Nat.shiftRight_eq_div_pow,
        Nat.mul_eq, Nat.add_eq]
      exact Nat.add_le_add_right
        ((Nat.div_le_div_right hmul).trans_eq (Nat.add_mul_div_right _ _ (Nat.two_pow_pos 52))) 1
private noncomputable def tayCoeff (k : ℕ) : ℕ := Nat.div (Nat.factorial 29) (Nat.factorial k)
private noncomputable def tayPSum (odd : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if oddSign m then tayPSum odd f m
      else Nat.add (tayPSum odd f m) (Nat.mul (tayCoeff (2 * m + odd)) (f (2 * m + odd)))
private noncomputable def tayNSum (odd : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if oddSign m then
      Nat.add (tayNSum odd f m) (Nat.mul (tayCoeff (2 * m + odd)) (f (2 * m + odd)))
      else tayNSum odd f m
private theorem taySum_bounds (nx odd : ℕ) (hnx : nx ≤ 4 * 2 ^ 52) (hodd : odd ≤ 1)
    (taySM : ℕ → Bool × ℕ) (h0 : taySM 0 = (false, 0))
    (hstep : ∀ m, smToInt (taySM (m + 1)).1 (taySM (m + 1)).2 =
      smToInt (taySM m).1 (taySM m).2 + smToInt (oddSign m)
        (tayCoeff (2 * m + odd) * nx ^ (2 * m + odd) * 2 ^ (52 * (29 - (2 * m + odd))))) :
    ∀ m ≤ 15,
      (2 ^ 1412 : ℤ) * ((tayPSum odd (gqsp_pLo nx) m : ℤ) -
        ((tayNSum odd (gqsp_pLo nx) m + tayNSum odd gqsp_delta4 m : ℕ) : ℤ)) ≤
        smToInt (taySM m).1 (taySM m).2 ∧
      smToInt (taySM m).1 (taySM m).2 ≤
        (2 ^ 1412 : ℤ) * (((tayPSum odd (gqsp_pLo nx) m +
          tayPSum odd gqsp_delta4 m : ℕ) : ℤ) - (tayNSum odd (gqsp_pLo nx) m : ℤ))
  | 0, _ => by simp [tayPSum, tayNSum, h0]
  | m + 1, hm => by
      let k := 2 * m + odd
      rcases taySum_bounds nx odd hnx hodd taySM h0 hstep m (by omega) with ⟨hLo, hHi⟩
      rcases gqsp_pLo_pHi_bounds nx k (by omega) with ⟨hplo, hphi⟩
      have hd := gqsp_pHi_le_pLo_add_delta4 nx hnx k
      have ht_lo : (2 ^ 1412 : ℤ) * ((tayCoeff k * gqsp_pLo nx k : ℕ) : ℤ) ≤
          ((tayCoeff k * nx ^ k * 2 ^ (52 * (29 - k)) : ℕ) : ℤ) := by
        exact_mod_cast (by
          rw [show 2 ^ 1412 * (tayCoeff k * gqsp_pLo nx k) =
              tayCoeff k * (2 ^ 1412 * gqsp_pLo nx k) by ring,
            Nat.mul_assoc (tayCoeff k)]
          exact Nat.mul_le_mul_left _ hplo : 2 ^ 1412 * (tayCoeff k * gqsp_pLo nx k) ≤ _)
      have ht_hi : ((tayCoeff k * nx ^ k * 2 ^ (52 * (29 - k)) : ℕ) : ℤ) ≤
          (2 ^ 1412 : ℤ) *
            ((tayCoeff k * gqsp_pLo nx k + tayCoeff k * gqsp_delta4 k : ℕ) : ℤ) := by
        exact_mod_cast (by
          rw [Nat.mul_assoc (tayCoeff k),
            show 2 ^ 1412 * (tayCoeff k * gqsp_pLo nx k + tayCoeff k * gqsp_delta4 k) =
              tayCoeff k * (2 ^ 1412 * (gqsp_pLo nx k + gqsp_delta4 k)) by ring]
          exact Nat.mul_le_mul_left _ (hphi.trans (Nat.mul_le_mul_left _ hd)) : _ ≤ 2 ^ 1412 * _)
      simp only [Nat.cast_add] at hLo hHi ht_hi
      rw [hstep m]
      cases hsign : oddSign m
      · simp only [tayPSum, tayNSum, hsign, Bool.false_eq_true, ↓reduceIte,
          smToInt_false, Nat.add_eq, Nat.mul_eq, Nat.cast_add]
        exact ⟨by linear_combination hLo + ht_lo, by linear_combination hHi + ht_hi⟩
      · simp only [tayPSum, tayNSum, hsign, ↓reduceIte,
          smToInt_true, Nat.add_eq, Nat.mul_eq, Nat.cast_add]
        exact ⟨by linear_combination hLo + ht_hi, by linear_combination hHi + ht_lo⟩
noncomputable def gqsp_catRatNx (c_val : ℕ) : ℕ :=
  let mag := if Nat.ble c_val 0x20000000000 then c_val else Nat.sub 0x40000000000 c_val
  Nat.shiftRight (Nat.mul 0x3243f6a8885a308d3 mag) 53
private theorem gqsp_catRatNx_eq (c_val : ℕ) : gqsp_catRatNx c_val = catRatNx c_val := by
  dsimp only [gqsp_catRatNx, catRatNx, catSymMag, piApproxNat]
  rw [show ∀ x n : ℕ, Nat.shiftRight x n = x / 2 ^ n from Nat.shiftRight_eq_div_pow]
  rfl
private theorem gqsp_catRatNx_le (c_val : ℕ) : gqsp_catRatNx c_val ≤ 4 * 2 ^ 52 := by
  dsimp only [gqsp_catRatNx]
  rw [show ∀ x n : ℕ, Nat.shiftRight x n = x / 2 ^ n from Nat.shiftRight_eq_div_pow,
    show (2 ^ 53 : ℕ) = 0x20000000000000 from rfl]
  have hmag : (if Nat.ble c_val 0x20000000000 then c_val else Nat.sub 0x40000000000 c_val) ≤
      0x20000000000 := by
    split_ifs with h
    · exact Nat.ble_eq.mp h
    · have := mt Nat.ble_eq.mpr h
      rw [Nat.sub_eq]
      omega
  exact (Nat.div_le_div_right (Nat.mul_le_mul_left _ hmag)).trans (Nat.ble_eq.mp (rfl :
    Nat.ble (Nat.div (Nat.mul 0x3243f6a8885a308d3 0x20000000000) 0x20000000000000) (4 * 2 ^ 52) =
      true))
@[inline] noncomputable def gqsp_natMax (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)
noncomputable def gqsp_ivlAbsMax (pLo pHi nLo nHi : ℕ) (g_neg : Bool) (g_u : ℕ) : ℕ :=
  match g_neg with
  | false => gqsp_natMax (Nat.sub (Nat.add g_u nHi) pLo) (Nat.sub pHi (Nat.add nLo g_u))
  | true  => gqsp_natMax (Nat.sub nHi (Nat.add pLo g_u)) (Nat.sub (Nat.add pHi g_u) nLo)
private theorem gqsp_ivlAbsMax_spec (pLo pHi nLo nHi : ℕ) (s1 : Bool) (m1 : ℕ) (g_neg : Bool)
    (g_comp G_unit gate_scale : ℕ) (hscale : gate_scale = 2 ^ 1412 * G_unit)
    (hlo : (2 ^ 1412 : ℤ) * ((pLo : ℤ) - (nHi : ℤ)) ≤ smToInt s1 m1)
    (hhi : smToInt s1 m1 ≤ (2 ^ 1412 : ℤ) * ((pHi : ℤ) - (nLo : ℤ))) : smAbsDiff s1 m1 g_neg
    (Nat.mul g_comp gate_scale) ≤ 2 ^ 1412 * gqsp_ivlAbsMax pLo pHi nLo nHi g_neg
    (Nat.mul g_comp G_unit) := by
  have hsm : smToInt g_neg (Nat.mul g_comp gate_scale) =
      (2 ^ 1412 : ℤ) * smToInt g_neg (Nat.mul g_comp G_unit) := by
    cases g_neg
    · simp only [smToInt_false, Nat.mul_eq, hscale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    · simp only [smToInt_true, Nat.mul_eq, hscale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
  let g_u := Nat.mul g_comp G_unit
  let M := gqsp_ivlAbsMax pLo pHi nLo nHi g_neg g_u
  have hM : -((M : ℤ)) ≤ ((pLo : ℤ) - (nHi : ℤ)) - smToInt g_neg g_u ∧
      ((pHi : ℤ) - (nLo : ℤ)) - smToInt g_neg g_u ≤ (M : ℤ) := by
    cases g_neg
    · simp only [M, gqsp_ivlAbsMax, gqsp_natMax, smToInt_false, Nat.add_eq, Nat.sub_eq]
      omega
    · simp only [M, gqsp_ivlAbsMax, gqsp_natMax, smToInt_true, Nat.add_eq, Nat.sub_eq]
      omega
  have hp : (0 : ℤ) ≤ (2 ^ 1412 : ℤ) := by exact_mod_cast Nat.zero_le (2 ^ 1412)
  exact Int.ofNat_le.mp (by
    rw [smAbsDiff_cast_eq, hsm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact abs_le.mpr ⟨by linear_combination mul_le_mul_of_nonneg_left hM.1 hp + hlo,
      by linear_combination hhi + mul_le_mul_of_nonneg_left hM.2 hp⟩)
@[inline] noncomputable def gqsp_pickSinIvl (is_le : Bool) (sPLo sPHi sNLo sNHi : ℕ) (neg_s' : Bool)
    (gs_u : ℕ) : ℕ :=
  match is_le with
  | true  => gqsp_ivlAbsMax sNLo sNHi sPLo sPHi neg_s' gs_u
  | false => gqsp_ivlAbsMax sPLo sPHi sNLo sNHi neg_s' gs_u
noncomputable def gqsp_tayFinishEval (c_val gc_u gs_u : ℕ) (neg_c neg_s : Bool)
    (cP_15 cN_15 sP_15 sN_15 : ℕ) : ℕ :=
  let cPHi_15 := Nat.add cP_15 0x1c904eb8afd9b17db2e982c3ca9
  let cNHi_15 := Nat.add cN_15 0x1f56ef9e3c3afc44231a350c2b4
  let sPHi_15 := Nat.add sP_15 0x1c80028f50f8489257ac45e369d
  let sNHi_15 := Nat.add sN_15 0x20374aa0ae5949e9f9946f5d45c
  let dc := gqsp_ivlAbsMax cP_15 cPHi_15 cN_15 cNHi_15 neg_c gc_u
  let ds := gqsp_pickSinIvl (Nat.ble c_val 0x20000000000)
    sP_15 sPHi_15 sN_15 sNHi_15 (xor neg_c neg_s) gs_u
  Nat.add dc ds
noncomputable def gqsp_tayRun15 (c_val gc_u gs_u : ℕ) (neg_c neg_s : Bool) (nx : ℕ) : ℕ :=
  gqsp_tayFinishEval c_val gc_u gs_u neg_c neg_s
    (gqsp_cosP15 nx) (gqsp_cosN15 nx) (gqsp_sinP15 nx) (gqsp_sinN15 nx)
noncomputable def gqsp_gateUpperAux (t0 t1 : ℕ) (neg_c neg_s : Bool) (c_val : ℕ) : ℕ :=
  gqsp_applyNatCat
    (gqsp_tayRun15 c_val (Nat.mul t0 0x6f99461a1e9e1432dcb6000000000000000000)
    (Nat.mul (Nat.sub t1 t0) 0x6f99461a1e9e1432dcb6000000000000000000) neg_c neg_s)
    (gqsp_catRatNx c_val)
noncomputable def gqsp_gateUpper (c_raw : ℕ) (g : DyadicRyGate) : ℕ :=
  match g with
  | ⟨t0, t1, neg_c, neg_s⟩ =>
      gqsp_applyNatCat (gqsp_gateUpperAux t0 t1 neg_c neg_s) (Nat.land c_raw 0x3ffffffffff)
private theorem gqsp_gateUpper_spec (c_raw : ℕ) (g : DyadicRyGate) :
    gateBridgeDiffNat (Nat.factorial 29) (Nat.factorial 29 * 2 ^ 1460) c_raw g ≤
      2 ^ 1412 * gqsp_gateUpper c_raw g := by
  rcases g with ⟨t0, t1, neg_c, neg_s⟩
  have hcmod : Nat.land c_raw 0x3ffffffffff = Nat.mod c_raw (Nat.pow 2 42) :=
    Nat.and_two_pow_sub_one_eq_mod c_raw 42
  have hgu : Nat.factorial 29 * 2 ^ 1460 =
      2 ^ 1412 * (0x6f99461a1e9e1432dcb6000000000000000000 : ℕ) := by
    rw [← show Nat.factorial 29 * 2 ^ 48 = 0x6f99461a1e9e1432dcb6000000000000000000 from rfl,
      show (1460 : ℕ) = 48 + 1412 from rfl, Nat.pow_add]
    ring
  unfold gqsp_gateUpper gqsp_gateUpperAux gqsp_tayRun15 gateBridgeDiffNat
  simp only [gqsp_applyNatCat_eq, FastRecurrenceVerifier.forceNatFast_eq, hcmod, gqsp_catRatNx_eq]
  let c_val := Nat.mod c_raw (Nat.pow 2 42)
  let nx := catRatNx c_val
  have hnx : nx ≤ 4 * 2 ^ 52 := Eq.mp (congrArg (· ≤ 4 * 2 ^ 52) (gqsp_catRatNx_eq c_val))
    (gqsp_catRatNx_le c_val)
  rcases taySum_bounds nx 0 hnx (Nat.zero_le 1) (cosTaylorSM (Nat.factorial 29) nx) rfl
    (fun m ↦ by
      let cterm := (Nat.factorial 29 / (2 * m).factorial) * nx ^ (2 * m) * 2 ^ (52 * (29 - 2 * m))
      rw [cosTaylorSM, FastRecurrenceVerifier.forceNatFast_eq]
      exact (FastRecurrenceVerifier.smAdd_eq_pair _ _ (oddSign m) cterm
        FastRecurrenceVerifier.smToInt).symm.trans
        (FastRecurrenceVerifier.smToInt_smAdd _ _ (oddSign m) cterm)) 15 (le_refl 15) with
    ⟨hcLo, hcHi⟩
  rcases taySum_bounds nx 1 hnx (le_refl 1) (sinTaylorSM (Nat.factorial 29) nx) rfl
    (fun m ↦ by
      let sterm := (Nat.factorial 29 / (2 * m + 1).factorial) * nx ^ (2 * m + 1) *
        2 ^ (52 * (29 - (2 * m + 1)))
      rw [sinTaylorSM, FastRecurrenceVerifier.forceNatFast_eq]
      exact (FastRecurrenceVerifier.smAdd_eq_pair _ _ (oddSign m) sterm
        FastRecurrenceVerifier.smToInt).symm.trans
        (FastRecurrenceVerifier.smToInt_smAdd _ _ (oddSign m) sterm)) 15 (le_refl 15) with
    ⟨hsLo, hsHi⟩
  rw [show tayPSum 0 (gqsp_pLo nx) 15 = gqsp_cosP15 nx from rfl,
    show tayNSum 0 (gqsp_pLo nx) 15 = gqsp_cosN15 nx from rfl] at hcLo hcHi
  rw [show tayPSum 1 (gqsp_pLo nx) 15 = gqsp_sinP15 nx from rfl,
    show tayNSum 1 (gqsp_pLo nx) 15 = gqsp_sinN15 nx from rfl] at hsLo hsHi
  rw [show tayNSum 0 gqsp_delta4 15 = 0x1f56ef9e3c3afc44231a350c2b4 from rfl] at hcLo
  rw [show tayPSum 0 gqsp_delta4 15 = 0x1c904eb8afd9b17db2e982c3ca9 from rfl] at hcHi
  rw [show tayNSum 1 gqsp_delta4 15 = 0x20374aa0ae5949e9f9946f5d45c from rfl] at hsLo
  rw [show tayPSum 1 gqsp_delta4 15 = 0x1c80028f50f8489257ac45e369d from rfl] at hsHi
  have hdc := gqsp_ivlAbsMax_spec (gqsp_cosP15 nx) (gqsp_cosP15 nx + 0x1c904eb8afd9b17db2e982c3ca9)
    (gqsp_cosN15 nx) (gqsp_cosN15 nx + 0x1f56ef9e3c3afc44231a350c2b4)
    (cosTaylorSM (Nat.factorial 29) nx 15).1 (cosTaylorSM (Nat.factorial 29) nx 15).2
    neg_c t0 0x6f99461a1e9e1432dcb6000000000000000000 (Nat.factorial 29 * 2 ^ 1460) hgu hcLo hcHi
  rw [show catSymNeg c_val = Nat.ble c_val 0x20000000000 from rfl]
  dsimp only [gqsp_tayFinishEval]
  change Nat.add _ (smAbsDiff (if Nat.ble c_val 0x20000000000 then _ else _) _ _ _) ≤
    2 ^ 1412 * Nat.add _ (gqsp_pickSinIvl (Nat.ble c_val 0x20000000000) _ _ _ _ _ _)
  cases Nat.ble c_val 0x20000000000
  · simp only [Bool.false_eq_true, ↓reduceIte, gateSM, Nat.add_eq, gqsp_pickSinIvl, Nat.mul_add]
    exact Nat.add_le_add hdc (gqsp_ivlAbsMax_spec (gqsp_sinP15 nx)
      (gqsp_sinP15 nx + 0x1c80028f50f8489257ac45e369d) (gqsp_sinN15 nx)
      (gqsp_sinN15 nx + 0x20374aa0ae5949e9f9946f5d45c) (sinTaylorSM (Nat.factorial 29) nx 15).1
      (sinTaylorSM (Nat.factorial 29) nx 15).2 (xor neg_c neg_s) (Nat.sub t1 t0)
      0x6f99461a1e9e1432dcb6000000000000000000 (Nat.factorial 29 * 2 ^ 1460) hgu hsLo hsHi)
  · simp only [↓reduceIte, gateSM, Nat.add_eq, gqsp_pickSinIvl, Nat.mul_add]
    exact Nat.add_le_add hdc (gqsp_ivlAbsMax_spec (gqsp_sinN15 nx)
      (gqsp_sinN15 nx + 0x20374aa0ae5949e9f9946f5d45c) (gqsp_sinP15 nx)
      (gqsp_sinP15 nx + 0x1c80028f50f8489257ac45e369d)
      (Bool.not (sinTaylorSM (Nat.factorial 29) nx 15).1) (sinTaylorSM (Nat.factorial 29) nx 15).2
      (xor neg_c neg_s) (Nat.sub t1 t0) 0x6f99461a1e9e1432dcb6000000000000000000
      (Nat.factorial 29 * 2 ^ 1460) hgu
      (by
        rw [smToInt_neg]
        linear_combination hsHi)
      (by
        rw [smToInt_neg]
        linear_combination hsLo))
noncomputable def gqsp_catUpperList : List ℕ → List DyadicRyGate → ℕ → ℕ
  | [], _, acc => acc
  | _, [], acc => acc
  | c_raw :: cs, g :: gs, acc =>
      gqsp_forceLitCat (Nat.add acc (gqsp_gateUpper c_raw g)) fun acc' =>
        gqsp_catUpperList cs gs acc'
theorem gqsp_catUpperList_spec (K29_fact gate_scale : ℕ) (hK : K29_fact = Nat.factorial 29)
    (hgs : gate_scale = K29_fact * 2 ^ 1460) :
    ∀ (cs : List ℕ) (gs : List DyadicRyGate) (acc_exact acc_up : ℕ),
      acc_exact ≤ 2 ^ 1412 * acc_up →
      catPolyDiffListNat K29_fact gate_scale cs gs acc_exact ≤
        2 ^ 1412 * gqsp_catUpperList cs gs acc_up
  | [], _, _, _, hacc => hacc
  | _ :: _, [], _, _, hacc => hacc
  | c_raw :: cs, g :: gs, acc_exact, acc_up, hacc => by
      subst hK hgs
      simp only [catPolyDiffListNat, gqsp_catUpperList, FastRecurrenceVerifier.forceNatFast_eq,
        gqsp_forceLitCat_eq, Nat.add_eq]
      exact gqsp_catUpperList_spec _ _ rfl rfl cs gs _ _
        ((Nat.add_le_add hacc (gqsp_gateUpper_spec c_raw g)).trans_eq (Nat.mul_add _ _ _).symm)
noncomputable def gqsp_natDistFast (a b : ℕ) : ℕ := Nat.add (Nat.sub a b) (Nat.sub b a)
private theorem gqsp_getD_land_zero (tz_mask : ℕ) : ∀ (xs : List ℕ) (idx : ℕ),
    xs.all (fun x => Nat.beq (Nat.land x tz_mask) 0) = true →
      Nat.beq (Nat.land (xs.getD idx 0) tz_mask) 0 = true
  | [], _, _ => by simp [List.getD]
  | _ :: _, 0, hall => by simpa [List.getD] using (Bool.and_eq_true _ _).mp hall |>.1
  | _ :: xt, k + 1, hall => by
      simpa [List.getD] using gqsp_getD_land_zero tz_mask xt k ((Bool.and_eq_true _ _).mp hall).2
set_option exponentiation.threshold 256 in
theorem gqsp_fin42_dvd_of_land (M s s_cert tz_mask : ℕ) (hs_le : s ≤ s_cert) (hs42 : s_cert ≤ 42)
    (hmask : tz_mask = 2 ^ s_cert - 1) (x0 : ℕ) (xs : List ℕ) (F_opt : Fin (M + 1) → Fin (2 ^ 42))
    (hF_opt : ∀ i : Fin (M + 1), F_opt i = Fin.ofNat (2 ^ 42) ((x0 :: xs).getD i.val 0))
    (hx0 : Nat.beq (Nat.land x0 tz_mask) 0 = true)
    (hxs : xs.all (fun x => Nat.beq (Nat.land x tz_mask) 0) = true) (t : Fin (M + 1)) :
    2 ^ s ∣ (F_opt t).val := by
  have hget := gqsp_getD_land_zero tz_mask (x0 :: xs) t.val
    ((Bool.and_eq_true _ _).mpr ⟨hx0, hxs⟩)
  have h0 : ((x0 :: xs).getD t.val 0) &&& (2 ^ s_cert - 1) = 0 := Nat.beq_eq.mp (hmask ▸ hget)
  rw [Nat.and_two_pow_sub_one_eq_mod] at h0
  rw [hF_opt t]
  change 2 ^ s ∣ ((x0 :: xs).getD t.val 0) % 2 ^ 42
  exact (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (hs_le.trans hs42))).mpr
    (dvd_trans (Nat.pow_dvd_pow 2 hs_le) (Nat.dvd_of_mod_eq_zero h0))
noncomputable def gqsp_ryLenContrLoop (n_exp D2 : ℕ) (gs0 : List DyadicRyGate) (cnt0 : ℕ) : Bool :=
  @List.rec DyadicRyGate (fun _ => ℕ → Bool) (fun cnt => Nat.beq cnt n_exp)
    (fun g _ ih cnt =>
      let gsm := gateSM g
      match Nat.ble (Nat.add (Nat.mul gsm.1.2 gsm.1.2) (Nat.mul gsm.2.2 gsm.2.2)) D2 with
      | true => gqsp_applyNat0Bool ih (Nat.add 1 cnt)
      | false => false) gs0 cnt0
theorem gqsp_ryLenContrLoop_spec (n_exp D2 : ℕ) : ∀ (gs : List DyadicRyGate) (cnt : ℕ),
    gqsp_ryLenContrLoop n_exp D2 gs cnt = true →
      cnt + gs.length = n_exp ∧ gatesContractionBleAux D2 gs = true
  | [], cnt, h => ⟨by simp [Nat.beq_eq.mp h], rfl⟩
  | g :: gs, cnt, h => by
      dsimp only [gqsp_ryLenContrLoop] at h
      unfold gatesContractionBleAux
      dsimp only
      cases hb : Nat.ble (Nat.add (Nat.mul (gateSM g).1.2 (gateSM g).1.2)
        (Nat.mul (gateSM g).2.2 (gateSM g).2.2)) D2
      · rw [hb] at h
        cases h
      · rw [hb, gqsp_applyNat0Bool_eq] at h
        rcases gqsp_ryLenContrLoop_spec n_exp D2 gs (Nat.add 1 cnt) h with ⟨hl, hc⟩
        simp only [List.length_cons, Nat.add_eq] at hl ⊢
        exact ⟨by omega, hc⟩
noncomputable def gqsp_mask768 : ℕ :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
theorem gqsp_land_mask768_pack (x : ℕ) (xt : List ℕ) (hx : x < 2 ^ 768) :
    Nat.land (pack768 (x :: xt)) gqsp_mask768 = x ∧
      Nat.shiftRight (pack768 (x :: xt)) 768 = pack768 xt := by
  rcases sched_mod_div_768_mul_add 1 x (pack768 xt)
    (by rwa [Nat.mul_one, Nat.one_shiftLeft]) with ⟨hlo, hhi⟩
  rw [Nat.mul_one] at hlo hhi
  refine ⟨by
    unfold gqsp_mask768
    rw [sched_mask768_eq_mod]
    change Nat.mod (x + (pack768 xt <<< 768)) sched_pow768 = x
    rw [sched_pow768_eq_pow]
    exact hlo, by
    change (x + (pack768 xt <<< 768)) >>> 768 = pack768 xt
    rw [Nat.shiftRight_eq_div_pow]
    exact hhi⟩
theorem gqsp_shr_add (w a b : ℕ) :
    Nat.shiftRight w (a + b) = Nat.shiftRight (Nat.shiftRight w a) b := by
  simp only [show ∀ x n : ℕ, Nat.shiftRight x n = x / 2 ^ n from Nat.shiftRight_eq_div_pow,
    Nat.pow_add, Nat.div_div_eq_div_mul]
noncomputable def gqsp_rev1Acc (w acc : ℕ) : ℕ :=
  Nat.add (Nat.land w gqsp_mask768) (Nat.shiftLeft acc 768)
noncomputable def gqsp_rev2Acc (w acc : ℕ) : ℕ :=
  gqsp_rev1Acc (Nat.shiftRight w 768) (gqsp_rev1Acc w acc)
noncomputable def gqsp_rev4Acc (w acc : ℕ) : ℕ :=
  gqsp_rev2Acc (Nat.shiftRight w 1536) (gqsp_rev2Acc w acc)
private theorem gqsp_rev1Acc_pack (xs rest ys : List ℕ) (hlen : xs.length = 1)
    (hxs : ∀ x ∈ xs, x < 2 ^ 768) :
    gqsp_rev1Acc (pack768 (xs ++ rest)) (pack768 ys) = pack768 (xs.reverse ++ ys) ∧
      Nat.shiftRight (pack768 (xs ++ rest)) 768 = pack768 rest := by
  rcases xs with _ | ⟨x0, _ | ⟨_, _⟩⟩
  · cases hlen
  · rcases gqsp_land_mask768_pack x0 rest (hxs x0 List.mem_cons_self) with ⟨hlo, hhi⟩
    simp only [List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil]
    exact ⟨congrArg (Nat.add · (Nat.shiftLeft (pack768 ys) 768)) hlo, hhi⟩
  · cases Nat.succ.inj hlen
private theorem gqsp_double_rev_pack (fn : ℕ → ℕ → ℕ) (k sh : ℕ) (hfn : ∀ (xs rest ys : List ℕ),
    xs.length = k → (∀ x ∈ xs, x < 2 ^ 768) → fn (pack768 (xs ++ rest)) (pack768 ys) = pack768
    (xs.reverse ++ ys) ∧ Nat.shiftRight (pack768 (xs ++ rest)) sh = pack768 rest)
    (xs rest ys : List ℕ) (hlen : xs.length = k + k) (hxs : ∀ x ∈ xs, x < 2 ^ 768) : fn
    (Nat.shiftRight (pack768 (xs ++ rest)) sh) (fn (pack768 (xs ++ rest)) (pack768 ys)) =
      pack768 (xs.reverse ++ ys) ∧
      Nat.shiftRight (pack768 (xs ++ rest)) (sh + sh) = pack768 rest := by
  have hsp : xs.take k ++ xs.drop k = xs := List.take_append_drop k xs
  have happ : xs ++ rest = xs.take k ++ (xs.drop k ++ rest) := by rw [← List.append_assoc, hsp]
  rcases hfn (xs.take k) (xs.drop k ++ rest) ys (by rw [List.length_take]; omega)
    (fun a ha ↦ hxs a (List.mem_of_mem_take ha)) with ⟨hr1, hs1⟩
  rcases hfn (xs.drop k) rest ((xs.take k).reverse ++ ys) (by rw [List.length_drop]; omega)
    (fun a ha ↦ hxs a (List.mem_of_mem_drop ha)) with ⟨hr2, hs2⟩
  exact ⟨by rw [happ, hs1, hr1, hr2, ← List.append_assoc, ← List.reverse_append, hsp],
    by rw [gqsp_shr_add, happ, hs1, hs2]⟩
theorem gqsp_rev4Acc_pack (xs rest ys : List ℕ) (hlen : xs.length = 4)
    (hxs : ∀ x ∈ xs, x < 2 ^ 768) : gqsp_rev4Acc (pack768 (xs ++ rest)) (pack768 ys) =
    pack768 (xs.reverse ++ ys) ∧ Nat.shiftRight (pack768 (xs ++ rest)) 3072 = pack768 rest :=
  gqsp_double_rev_pack gqsp_rev2Acc 2 1536
    (gqsp_double_rev_pack gqsp_rev1Acc 1 768 gqsp_rev1Acc_pack) xs rest ys hlen hxs
noncomputable def gqsp_consForceNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  @Nat.casesOn (fun _ => List ℕ) (Nat.add 1 x) xs (fun v => v :: xs)
noncomputable def gqsp_peel1Shr256 (w : ℕ) (racc : List ℕ) : List ℕ :=
  gqsp_consForceNat (Nat.shiftRight (Nat.land w gqsp_mask768) 256) racc
noncomputable def gqsp_peel4Shr256 (w : ℕ) (racc : List ℕ) : List ℕ :=
  let r1 := gqsp_peel1Shr256 w racc; let w1 := Nat.shiftRight w 768
  let r2 := gqsp_peel1Shr256 w1 r1; let w2 := Nat.shiftRight w1 768
  let r3 := gqsp_peel1Shr256 w2 r2; let w3 := Nat.shiftRight w2 768
  gqsp_peel1Shr256 w3 r3
theorem gqsp_peel4Shr256_pack (z0 z1 z2 z3 : ℕ) (zt racc : List ℕ) (h0 : z0 < 2 ^ 768)
    (h1 : z1 < 2 ^ 768) (h2 : z2 < 2 ^ 768) (h3 : z3 < 2 ^ 768) : gqsp_peel4Shr256
    (pack768 (z0 :: z1 :: z2 :: z3 :: zt)) racc = Nat.shiftRight z3 256 :: Nat.shiftRight z2
    256 :: Nat.shiftRight z1 256 :: Nat.shiftRight z0 256 :: racc ∧ Nat.shiftRight
    (pack768 (z0 :: z1 :: z2 :: z3 :: zt)) 3072 = pack768 zt := by
  have hp1 {z : ℕ} (zt r : List ℕ) (hz : z < 2 ^ 768) :
      gqsp_peel1Shr256 (pack768 (z :: zt)) r = Nat.shiftRight z 256 :: r := by
    unfold gqsp_peel1Shr256
    rw [show ∀ x xs, gqsp_consForceNat x xs = x :: xs from fun x xs ↦
      congrArg (@Nat.casesOn (fun _ => List ℕ) · xs (fun v => v :: xs)) (Nat.one_add x),
      (gqsp_land_mask768_pack z zt hz).1]
  rcases gqsp_land_mask768_pack z0 (z1 :: z2 :: z3 :: zt) h0 with ⟨_, hs0⟩
  rcases gqsp_land_mask768_pack z1 (z2 :: z3 :: zt) h1 with ⟨_, hs1⟩
  rcases gqsp_land_mask768_pack z2 (z3 :: zt) h2 with ⟨_, hs2⟩
  rcases gqsp_land_mask768_pack z3 zt h3 with ⟨_, hs3⟩
  refine ⟨?_, by rw [show (3072 : ℕ) = 768 + (768 + (768 + 768)) from rfl, gqsp_shr_add, hs0,
    gqsp_shr_add, hs1, gqsp_shr_add, hs2, hs3]⟩
  dsimp only [gqsp_peel4Shr256]
  rw [hp1 _ _ h0, hs0, hp1 _ _ h1, hs1, hp1 _ _ h2, hs2, hp1 _ _ h3]
noncomputable def gqsp_peelCode42One (s w : ℕ) (acc : List ℕ) : List ℕ :=
  @Nat.casesOn (fun _ => List ℕ) (Nat.add 1 (Nat.land w 0x3ffffffffff)) []
    (fun v => sched_idSalt s v :: acc)
noncomputable def gqsp_peelCode42OneStep (ih : ℕ → ℕ → List ℕ →
    List ℕ) (s w : ℕ) (acc : List ℕ) : List ℕ :=
  let a1 := gqsp_peelCode42One s w acc
  sched_stfList (Nat.add 1 s) (fun w1 => ih (Nat.add 2 s) w1 a1) (Nat.shiftRight w 42)
noncomputable def gqsp_fast1_unpackCodeWord (rem : ℕ) : ℕ → ℕ → List ℕ → List ℕ := @Nat.rec
    (fun _ => ℕ → ℕ → List ℕ → List ℕ) (fun _ _ acc => acc)
    (fun _ ih => gqsp_peelCode42OneStep ih) rem
noncomputable def gqsp_peelCode42EightStep (ih : ℕ → ℕ → List ℕ →
    List ℕ) (s w : ℕ) (acc : List ℕ) : List ℕ :=
  let a1 := gqsp_peelCode42One s w acc
  let a2 := gqsp_peelCode42One (Nat.add 1 s) (Nat.shiftRight w 42) a1
  let a3 := gqsp_peelCode42One (Nat.add 2 s) (Nat.shiftRight w 84) a2
  let a4 := gqsp_peelCode42One (Nat.add 3 s) (Nat.shiftRight w 126) a3
  let a5 := gqsp_peelCode42One (Nat.add 4 s) (Nat.shiftRight w 168) a4
  let a6 := gqsp_peelCode42One (Nat.add 5 s) (Nat.shiftRight w 210) a5
  let a7 := gqsp_peelCode42One (Nat.add 6 s) (Nat.shiftRight w 252) a6
  let a8 := gqsp_peelCode42One (Nat.add 7 s) (Nat.shiftRight w 294) a7
  sched_stfList (Nat.add 8 s) (fun w8 => ih (Nat.add 16 s) w8 a8) (Nat.shiftRight w 336)
noncomputable def gqsp_fast8_unpackCodeWord (q8 rem : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
    @Nat.rec (fun _ => ℕ → ℕ → List ℕ → List ℕ) (gqsp_fast1_unpackCodeWord rem)
    (fun _ ih => gqsp_peelCode42EightStep ih) q8
noncomputable def gqsp_decCodes42Fast8WordsAcc (ws0 : List (ℕ × ℕ)) (s0 : ℕ) (rest0 : List ℕ)
    : List ℕ := @List.rec (ℕ × ℕ) (fun _ => ℕ → List ℕ) (fun _ => rest0) (fun p _ ih s =>
    sched_stfList s (fun s' => gqsp_fast8_unpackCodeWord (Nat.div p.1 8) (Nat.mod p.1 8)
    (Nat.add 8 s) p.2 (ih s')) (Nat.add 512 s)) ws0 s0
noncomputable def gqsp_decCodes42Fast8Blocks (baseSalt : ℕ) (bss0 : List (List (ℕ × ℕ))) :
    List ℕ := @List.rec (List (ℕ × ℕ)) (fun _ => ℕ → List ℕ) (fun _ => []) (fun ws _ ih s =>
    sched_stfList s (fun s' => gqsp_decCodes42Fast8WordsAcc ws (Nat.add 16 s) (ih s'))
    (Nat.add 131072 s)) bss0 baseSalt
noncomputable def gqsp_mask100 : ℕ := 0xfffffffffffffffffffffffff
noncomputable def gqsp_stfListRy (s : ℕ) (f : ℕ → List DyadicRyGate) (x : ℕ) : List DyadicRyGate :=
  @Nat.casesOn (fun _ => List DyadicRyGate) (Nat.add 1 (sched_idSalt s x)) [] f
noncomputable def gqsp_mkRyCons2 (s t0 t1 : ℕ) (acc : List DyadicRyGate) (nc ns : Bool) : List
    DyadicRyGate :=
  @Bool.casesOn (fun _ => List DyadicRyGate) ns
    ({ T0 := sched_idSalt s t0, T1 := t1, neg_c := nc, neg_s := false } :: acc)
    ({ T0 := sched_idSalt s t0, T1 := t1, neg_c := nc, neg_s := true } :: acc)
noncomputable def gqsp_mkRyCons1 (s t0 t1 : ℕ) (acc : List DyadicRyGate) (nc ns : Bool) :
    List DyadicRyGate := @Bool.casesOn (fun _ => List DyadicRyGate) nc
    (gqsp_mkRyCons2 s t0 t1 acc false ns) (gqsp_mkRyCons2 s t0 t1 acc true ns)
noncomputable def gqsp_peelRyGateOneGo (s : ℕ) (acc : List DyadicRyGate) (gw : ℕ) : List
    DyadicRyGate := @Nat.casesOn (fun _ => List DyadicRyGate)
    (Nat.add 1 (Nat.land gw 0x1ffffffffffff)) [] (fun t0 => @Nat.casesOn (fun _ => List
    DyadicRyGate) (Nat.add 1 (Nat.land (Nat.shiftRight gw 49) 0x1ffffffffffff)) [] (fun t1 =>
    gqsp_mkRyCons1 s t0 t1 acc (Nat.beq (Nat.land (Nat.shiftRight gw 98) 1) 1) (Nat.beq
    (Nat.land (Nat.shiftRight gw 99) 1) 1)))
noncomputable def gqsp_peelRyGateOne (s w : ℕ) (acc : List DyadicRyGate) : List DyadicRyGate :=
  @Nat.casesOn (fun _ => List DyadicRyGate) (Nat.add 1 (Nat.land w gqsp_mask100)) []
    (gqsp_peelRyGateOneGo s acc)
noncomputable def gqsp_peelRyGateOneStep (ih : ℕ → ℕ → List DyadicRyGate → List DyadicRyGate)
    (s w : ℕ) (acc : List DyadicRyGate) : List DyadicRyGate :=
  let a1 := gqsp_peelRyGateOne s w acc
  gqsp_stfListRy (Nat.add 1 s) (fun w1 => ih (Nat.add 2 s) w1 a1) (Nat.shiftRight w 100)
noncomputable def gqsp_fast1_unpackGateChunk (rem : ℕ) : ℕ → ℕ → List DyadicRyGate → List
    DyadicRyGate := @Nat.rec (fun _ => ℕ → ℕ → List DyadicRyGate → List DyadicRyGate)
    (fun _ _ acc => acc) (fun _ ih => gqsp_peelRyGateOneStep ih) rem
noncomputable def gqsp_peelRyGateEightStep (ih : ℕ → ℕ → List DyadicRyGate → List DyadicRyGate)
    (s w : ℕ) (acc : List DyadicRyGate) : List DyadicRyGate :=
  let a1 := gqsp_peelRyGateOne s w acc
  let a2 := gqsp_peelRyGateOne (Nat.add 1 s) (Nat.shiftRight w 100) a1
  let a3 := gqsp_peelRyGateOne (Nat.add 2 s) (Nat.shiftRight w 200) a2
  let a4 := gqsp_peelRyGateOne (Nat.add 3 s) (Nat.shiftRight w 300) a3
  let a5 := gqsp_peelRyGateOne (Nat.add 4 s) (Nat.shiftRight w 400) a4
  let a6 := gqsp_peelRyGateOne (Nat.add 5 s) (Nat.shiftRight w 500) a5
  let a7 := gqsp_peelRyGateOne (Nat.add 6 s) (Nat.shiftRight w 600) a6
  let a8 := gqsp_peelRyGateOne (Nat.add 7 s) (Nat.shiftRight w 700) a7
  gqsp_stfListRy (Nat.add 8 s) (fun w8 => ih (Nat.add 16 s) w8 a8) (Nat.shiftRight w 800)
noncomputable def gqsp_fast8_unpackGateChunk (q8 rem : ℕ) : ℕ → ℕ → List DyadicRyGate → List
    DyadicRyGate := @Nat.rec (fun _ => ℕ → ℕ → List DyadicRyGate → List DyadicRyGate)
    (gqsp_fast1_unpackGateChunk rem) (fun _ ih => gqsp_peelRyGateEightStep ih) q8
noncomputable def gqsp_decRyGatesFast8WordsAcc (ws0 : List (ℕ × ℕ)) (s0 : ℕ)
    (rest0 : List DyadicRyGate) : List DyadicRyGate := @List.rec (ℕ × ℕ)
    (fun _ => ℕ → List DyadicRyGate) (fun _ => rest0) (fun p _ ih s => gqsp_stfListRy s (fun
    s' => gqsp_fast8_unpackGateChunk (Nat.div p.1 8) (Nat.mod p.1 8) (Nat.add 8 s) p.2 (ih
    s')) (Nat.add 512 s)) ws0 s0
noncomputable def gqsp_tayMemo15 (c_val gc_u gs_u : ℕ) (neg_c neg_s : Bool) (nx : ℕ) : ℕ :=
  gqsp_tayRun15 c_val gc_u gs_u neg_c neg_s nx
noncomputable def gqsp_gateUpperMemoAux (t0 t1 : ℕ) (neg_c neg_s : Bool) (c_val : ℕ) : ℕ :=
  gqsp_applyNatCat
    (gqsp_tayMemo15 c_val (Nat.mul t0 0x6f99461a1e9e1432dcb6000000000000000000)
    (Nat.mul (Nat.sub t1 t0) 0x6f99461a1e9e1432dcb6000000000000000000) neg_c neg_s)
    (gqsp_catRatNx c_val)
noncomputable def gqsp_gateUpperMemo (c_raw : ℕ) (g : DyadicRyGate) : ℕ :=
  match g with
  | ⟨t0, t1, neg_c, neg_s⟩ =>
      gqsp_applyNatCat (gqsp_gateUpperMemoAux t0 t1 neg_c neg_s) (Nat.land c_raw 0x3ffffffffff)
noncomputable def gqsp_catUpperMemoStep (cs0 : List ℕ) (gs0 : List DyadicRyGate) (acc0 : ℕ) : List ℕ
    × ℕ :=
  @List.rec DyadicRyGate (fun _ => List ℕ → ℕ → List ℕ × ℕ)
    (fun cs acc => (cs, acc))
    (fun g _ ih cs acc =>
      match cs with
      | [] => ([], acc)
      | c_raw :: cs' =>
          gqsp_applyNatPairCat (ih cs') (Nat.add acc (gqsp_gateUpperMemo c_raw g)))
    gs0 cs0 acc0
private theorem gqsp_catUpperMemoStep_list_eq :
    ∀ (cs : List ℕ) (gs gs_rest : List DyadicRyGate) (acc : ℕ),
      (let r := gqsp_catUpperMemoStep cs gs acc; gqsp_catUpperList r.1 gs_rest r.2) =
        gqsp_catUpperList cs (gs ++ gs_rest) acc
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | c_raw :: cs, g :: gs, gs_rest, acc => by
      have hgm : gqsp_gateUpperMemo c_raw g = gqsp_gateUpper c_raw g := by
        cases g
        unfold gqsp_gateUpperMemo gqsp_gateUpper gqsp_gateUpperMemoAux gqsp_gateUpperAux
          gqsp_tayMemo15
        simp only [gqsp_applyNatCat_eq]
      change (let r := gqsp_applyNatPairCat (gqsp_catUpperMemoStep cs gs)
                (Nat.add acc (gqsp_gateUpperMemo c_raw g))
              gqsp_catUpperList r.1 gs_rest r.2) =
        gqsp_catUpperList (c_raw :: cs) ((g :: gs) ++ gs_rest) acc
      dsimp only
      rw [hgm, gqsp_applyNatPairCat_eq, List.cons_append, gqsp_catUpperList, gqsp_forceLitCat_eq]
      exact gqsp_catUpperMemoStep_list_eq cs gs gs_rest (Nat.add acc (gqsp_gateUpper c_raw g))
noncomputable def gqsp_catUpperMemoChunks (cs0 : List ℕ) (chs0 : List (List DyadicRyGate))
    (acc0 : ℕ) : ℕ := @List.rec (List DyadicRyGate) (fun _ => List ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun ch _ ih cs acc => match gqsp_catUpperMemoStep cs ch acc with
      | (cs', acc') => gqsp_applyNatCat (ih cs') acc') chs0 cs0 acc0
theorem gqsp_catUpperMemoChunks_eq :
    ∀ (chs : List (List DyadicRyGate)) (cs : List ℕ) (acc : ℕ),
      gqsp_catUpperMemoChunks cs chs acc = gqsp_catUpperList cs chs.flatten acc
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | ch :: chs, cs, acc => by
      change (match gqsp_catUpperMemoStep cs ch acc with
        | (cs', acc') => gqsp_applyNatCat (gqsp_catUpperMemoChunks cs' chs) acc') =
        gqsp_catUpperList cs (ch :: chs).flatten acc
      rw [List.flatten_cons, ← gqsp_catUpperMemoStep_list_eq cs ch chs.flatten acc]
      rcases gqsp_catUpperMemoStep cs ch acc with ⟨cs', acc'⟩
      simp only [gqsp_applyNatCat_eq]
      exact gqsp_catUpperMemoChunks_eq chs cs' acc'
/-- Fast binary-tree 1-angle Gidney rotation Toffoli-equivalent cost `2 * ((42 - ctz42Bin c) -
  2)`. -/
noncomputable def gqsp_gidneyRotFast (c : ℕ) : ℕ :=
  Nat.mul 2 (Nat.sub (Nat.sub 42 (gqsp_ctz42Bin c)) 2)
/-- `O(1)`-stack base code-list validator checking `cs.length = n_exp` and `∀ c ∈ cs, c < 2 ^
  42`. -/
noncomputable def gqsp_codeOrigLoop (n_exp : ℕ) (cs0 : List ℕ) (cnt0 : ℕ) : Bool :=
  @List.rec ℕ (fun _ => ℕ → Bool) (fun cnt => Nat.beq cnt n_exp)
    (fun c _ ih cnt => match Nat.blt c 4398046511104 with
      | true => gqsp_applyNat0Bool ih (Nat.add 1 cnt)
      | false => false) cs0 cnt0
theorem gqsp_codeOrigLoop_spec (n_exp : ℕ) : ∀ (cs : List ℕ) (cnt : ℕ),
    gqsp_codeOrigLoop n_exp cs cnt = true →
      cnt + cs.length = n_exp ∧ cs.all (· < 4398046511104) = true
  | [], cnt, h => ⟨by simp [Nat.beq_eq.mp h], rfl⟩
  | c :: cs, cnt, h => by
      dsimp only [gqsp_codeOrigLoop] at h
      cases hb : Nat.blt c 4398046511104
      · rw [hb] at h
        cases h
      · rw [hb, gqsp_applyNat0Bool_eq] at h
        rcases gqsp_codeOrigLoop_spec n_exp cs (Nat.add 1 cnt) h with ⟨hl, ha⟩
        simp only [List.length_cons, List.all_cons, Bool.and_eq_true, Nat.add_eq] at hl ⊢
        exact ⟨by omega, ⟨by simpa [Nat.blt_eq] using hb, ha⟩⟩
/-- Pack `(cnt, dist_sum, rot_sum)` into three 64-bit limbs `cnt + (dist <<< 64) + (rot <<<
  128)`. -/
def gqsp_packTriple (cnt dist rot : ℕ) : ℕ :=
  cnt + 0x10000000000000000 * (dist + 0x10000000000000000 * rot)
private theorem gqsp_div_mod_base (B r q : ℕ) (hr : r < B) :
    (r + B * q) % B = r ∧ (r + B * q) / B = q :=
  ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr],
   by rw [Nat.add_mul_div_left r q (Nat.zero_lt_of_lt hr), Nat.div_eq_of_lt hr, Nat.zero_add]⟩
theorem gqsp_packTriple_limbs (cnt dist rot : ℕ)
    (hc : cnt < 0x10000000000000000) (hd : dist < 0x10000000000000000) :
    let p := gqsp_packTriple cnt dist rot
    Nat.land p 0xffffffffffffffff = cnt ∧
      Nat.land (Nat.shiftRight p 64) 0xffffffffffffffff = dist ∧ Nat.shiftRight p 128 = rot := by
  have hland (x : ℕ) : Nat.land x 0xffffffffffffffff = x % 0x10000000000000000 :=
    Nat.and_two_pow_sub_one_eq_mod x 64
  have hshr (x : ℕ) : Nat.shiftRight x 64 = x / 0x10000000000000000 :=
    Nat.shiftRight_eq_div_pow x 64
  rcases gqsp_div_mod_base 0x10000000000000000 cnt (dist + 0x10000000000000000 * rot) hc with
    ⟨m0, d0⟩
  rcases gqsp_div_mod_base 0x10000000000000000 dist rot hd with ⟨m1, d1⟩
  have s1 : Nat.shiftRight (gqsp_packTriple cnt dist rot) 64 = dist + 0x10000000000000000 * rot :=
    (hshr _).trans d0
  refine ⟨(hland _).trans m0, by rw [s1, hland]; exact m1, ?_⟩
  rw [show (128 : ℕ) = 64 + 64 from rfl, gqsp_shr_add, s1, hshr]
  exact d1
theorem gqsp_packTriple_step (cnt dist rot d_add r_add : ℕ) :
    Nat.add (gqsp_packTriple cnt dist rot)
      (Nat.add 1 (Nat.add (Nat.shiftLeft d_add 64) (Nat.shiftLeft r_add 128))) =
      gqsp_packTriple (Nat.add 1 cnt) (Nat.add dist d_add) (Nat.add rot r_add) := by
  rw [show Nat.shiftLeft d_add 64 = d_add * 0x10000000000000000 from Nat.shiftLeft_eq d_add 64,
      show Nat.shiftLeft r_add 128 = r_add * (0x10000000000000000 * 0x10000000000000000) from
        Nat.shiftLeft_eq r_add 128]
  unfold gqsp_packTriple
  simp only [Nat.add_eq]
  generalize (0x10000000000000000 : ℕ) = B
  ring
/-- Clean 3-accumulator reference loop for 1-angle rounded tier verification. -/
noncomputable def gqsp_codeTierTzLoop (tz_mask n_exp d_exp rot_exp : ℕ) :
    List ℕ → List ℕ → ℕ → ℕ → ℕ → Bool
  | [], [], cnt, dist, rot =>
      Bool.and (Nat.beq cnt n_exp) (Bool.and (Nat.beq dist d_exp) (Nat.beq rot rot_exp))
  | cr :: crt, co :: cot, cnt, dist, rot =>
      match Bool.and (Bool.and (Nat.blt cr 4398046511104) (Nat.blt co 4398046511104))
              (Nat.beq (Nat.land cr tz_mask) 0) with
      | true => gqsp_applyNat0Bool (gqsp_applyNat1Bool (gqsp_applyNat2Bool
          (gqsp_codeTierTzLoop tz_mask n_exp d_exp rot_exp crt cot) (Nat.add 1 cnt))
          (Nat.add dist (gqsp_natDistFast cr co))) (Nat.add rot (gqsp_gidneyRotFast cr))
      | false => false
  | _, _, _, _, _ => false
theorem gqsp_codeTierTzLoop_spec (tz_mask n_exp d_exp rot_exp : ℕ) :
    ∀ (cr co : List ℕ) (cnt dist rot : ℕ),
      gqsp_codeTierTzLoop tz_mask n_exp d_exp rot_exp cr co cnt dist rot = true →
      cnt + cr.length = n_exp ∧ cnt + co.length = n_exp ∧ cr.all (· < 4398046511104) = true ∧
      cr.all (fun x => Nat.beq (Nat.land x tz_mask) 0) = true ∧
      dist + (List.zipWith natDist cr co).sum = d_exp ∧
      rot + (cr.map GidneySignalRotPart1.gidneyRotToffEquiv).sum = rot_exp
  | [], [], cnt, dist, rot, h => by
      unfold gqsp_codeTierTzLoop at h
      rcases (by simpa only [Bool.and_eq_true, Nat.beq_eq] using h :
        cnt = n_exp ∧ dist = d_exp ∧ rot = rot_exp) with ⟨rfl, rfl, rfl⟩
      simp
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | cr :: crt, co :: cot, cnt, dist, rot, h => by
      unfold gqsp_codeTierTzLoop at h
      cases hg : Bool.and (Bool.and (Nat.blt cr 4398046511104) (Nat.blt co 4398046511104))
        (Nat.beq (Nat.land cr tz_mask) 0)
      · rw [hg] at h
        cases h
      · rw [hg] at h
        dsimp only at h
        rw [gqsp_applyNat0Bool_eq, gqsp_applyNat1Bool_eq, gqsp_applyNat2Bool_eq] at h
        rcases gqsp_codeTierTzLoop_spec tz_mask n_exp d_exp rot_exp crt cot (Nat.add 1 cnt)
          (Nat.add dist (gqsp_natDistFast cr co)) (Nat.add rot (gqsp_gidneyRotFast cr)) h with
          ⟨l1, l2, a1, tz1, s1, s2⟩
        rcases (by simpa only [Bool.and_eq_true, Nat.blt_eq] using hg :
          (cr < 4398046511104 ∧ co < 4398046511104) ∧ Nat.beq (Nat.land cr tz_mask) 0 = true) with
          ⟨⟨hcr_lt, _⟩, hcr_tz⟩
        rw [show gqsp_natDistFast cr co = natDist cr co from rfl] at s1
        rw [show gqsp_gidneyRotFast cr =
            GidneySignalRotPart1.gidneyRotToffEquiv cr by
          unfold gqsp_gidneyRotFast
            GidneySignalRotPart1.gidneyRotToffEquiv
            PhaseGradSignalRot.activeMsbWidth42
          rw [gqsp_ctz42Bin_eq]
          rfl] at s2
        simp only [List.length_cons, List.all_cons, List.zipWith_cons_cons, List.map_cons,
          List.sum_cons, Bool.and_eq_true, Nat.add_eq] at l1 l2 s1 s2 ⊢
        exact ⟨by omega, by omega, ⟨by simpa [Nat.blt_eq] using hcr_lt, a1⟩, ⟨hcr_tz, tz1⟩,
          by omega, by omega⟩
end FastKernelHelpers
section GenericWronskianHelpers
set_option maxRecDepth 600000
open TFreeLaurentGQSP
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChebWeightCertS4805
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
open TwoAngleBiGqspVerifierBridge (ta_revNatTR ta_revNatTR_eq)
def powBinDepth : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | d + 1, b, e => if e = 0 then 1 else
      forceNatFast (powBinDepth d b (e / 2)) fun half ↦
      forceNatFast (Nat.mul half half) fun sq ↦ if e % 2 = 0 then sq else Nat.mul b sq
theorem powBinDepth_eq : ∀ (d b e : ℕ), e < 2 ^ d → powBinDepth d b e = b ^ e
  | 0, _, e, he => by
      obtain rfl : e = 0 := by omega
      rfl
  | d + 1, b, e, he => by
      unfold powBinDepth
      simp only [forceNatFast_eq]
      split_ifs with h0 hpar
      · subst h0
        simp
      · rw [Nat.mul_eq, powBinDepth_eq d b (e / 2) (by omega), ← pow_add]
        exact congrArg (b ^ ·) (by omega)
      · rw [Nat.mul_eq, Nat.mul_eq, powBinDepth_eq d b (e / 2) (by omega), ← pow_add, ← pow_succ']
        exact congrArg (b ^ ·) (by omega)
/-- Strict `ℕ` accumulator for `evenTailBiasedLoop` avoiding lazy `ℤ` thunks. -/
def evenTailPosNegLoop (Bw : ℕ) : List ℕ → ℕ → ℕ → ℕ × ℕ
  | [], p, n => (p, n)
  | [_], p, n => (p, n)
  | _ :: u_even :: rest, p, n =>
      if Nat.blt u_even Bw then
        forceNatFast (Nat.add n (Nat.mul 2 (Nat.sub Bw u_even))) fun n' ↦
          evenTailPosNegLoop Bw rest p n'
      else
        forceNatFast (Nat.add p (Nat.mul 2 (Nat.sub u_even Bw))) fun p' ↦
          evenTailPosNegLoop Bw rest p' n
theorem evenTailPosNegLoop_spec (Bw : ℕ) : ∀ (xs : List ℕ) (p n : ℕ),
    ((evenTailPosNegLoop Bw xs p n).1 : ℤ) - ((evenTailPosNegLoop Bw xs p n).2 : ℤ) =
      evenTailBiasedLoop Bw xs ((p : ℤ) - (n : ℤ))
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: u_even :: rest, p, n => by
      unfold evenTailPosNegLoop evenTailBiasedLoop
      cases hlt : Nat.blt u_even Bw
      · have : Bw ≤ u_even :=
          Nat.not_lt.mp (fun h ↦ Bool.noConfusion (hlt.symm.trans (Nat.blt_eq.mpr h)))
        simp only [Bool.false_eq_true, ↓reduceIte, forceNatFast_eq,
          evenTailPosNegLoop_spec Bw rest, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
        exact congrArg (evenTailBiasedLoop Bw rest) (by omega)
      · have : u_even ≤ Bw := (Nat.blt_eq.mp hlt).le
        simp only [↓reduceIte, forceNatFast_eq,
          evenTailPosNegLoop_spec Bw rest, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
        exact congrArg (evenTailBiasedLoop Bw rest) (by omega)
def StrictListBind {α : Type*} (xs : List ℕ) (f : List ℕ → α) : α :=
  match xs with | [] => f [] | h :: t => f (h :: t)
theorem StrictListBind_eq {α : Type*} (xs : List ℕ) (f : List ℕ → α) :
    StrictListBind xs f = f xs := by cases xs <;> rfl
private theorem doubleBiasedTail_length (Bw : ℕ) :
    ∀ xs : List ℕ, (doubleBiasedTail Bw xs).length = xs.length
  | [] => rfl
  | _ :: ut => by simp [doubleBiasedTail, forceNatFast_eq, doubleBiasedTail_length Bw ut]
theorem buildChebWsFromBiasedU_length (Bw pad : ℕ) (us : List ℕ) (hne : 0 < us.length) :
    (buildChebWsFromBiasedU Bw pad us).length = us.length + pad := by
  rcases us with _ | ⟨_, ut⟩
  · cases hne
  · simp only [buildChebWsFromBiasedU, List.length_cons, List.length_append,
      doubleBiasedTail_length, List.length_replicate]
    omega
noncomputable def gqsp_doubleBiasedRevTR (Bw : ℕ) (xs0 acc0 : List ℕ) : List ℕ := @List.rec ℕ
    (fun _ ↦ List ℕ → List ℕ) (fun acc ↦ acc) (fun u _ ih acc ↦ @Nat.casesOn (fun _ ↦ List ℕ)
    (Nat.add 1 (Nat.sub (Nat.mul 2 u) Bw)) [] (fun w ↦ gqsp_tramp (ih (w :: acc)))) xs0 acc0
private theorem gqsp_doubleBiasedRevTR_eq (Bw : ℕ) :
    ∀ (xs acc : List ℕ), gqsp_doubleBiasedRevTR Bw xs acc = (doubleBiasedTail Bw xs).reverse ++ acc
  | [], _ => rfl
  | u :: ut, acc => by
      dsimp only [gqsp_doubleBiasedRevTR]
      change @Nat.casesOn (fun _ ↦ List ℕ) (1 + Nat.sub (Nat.mul 2 u) Bw) []
        (fun w ↦ gqsp_tramp (gqsp_doubleBiasedRevTR Bw ut (w :: acc))) =
        (doubleBiasedTail Bw (u :: ut)).reverse ++ acc
      rw [Nat.one_add]
      dsimp only [gqsp_tramp]
      unfold doubleBiasedTail
      rw [forceNatFast_eq, gqsp_doubleBiasedRevTR_eq Bw ut, List.reverse_cons,
        List.append_assoc, List.singleton_append]
/-- `O(1)`-stack, `O(1)`-WHNF-cache unpadded Chebyshev weight builder matching
  `buildChebWsFromBiasedU Bw 0 us`. -/
noncomputable def gqsp_buildChebWsUnpadFast (Bw : ℕ) (us : List ℕ) : List ℕ :=
  match us with
  | [] => [Bw]
  | u0 :: ut => u0 :: ta_revNatTR (gqsp_doubleBiasedRevTR Bw ut []) []
theorem gqsp_buildChebWsUnpadFast_append_eq (Bw pad : ℕ) (us : List ℕ) (hne : 0 < us.length) :
    gqsp_buildChebWsUnpadFast Bw us ++ List.replicate pad Bw =
      buildChebWsFromBiasedU Bw pad us := by
  rcases us with _ | ⟨u0, ut⟩
  · cases hne
  · simp only [gqsp_buildChebWsUnpadFast, buildChebWsFromBiasedU, ta_revNatTR_eq,
      gqsp_doubleBiasedRevTR_eq, List.append_nil, List.reverse_reverse, List.cons_append]
end GenericWronskianHelpers
end GqspWronskian62592
end
end Gqsp0_SwarUnpack
end QuantumComputation.Specs.StoppingPowerSolution
end
