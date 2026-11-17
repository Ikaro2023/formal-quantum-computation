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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspRealTourn

set_option linter.style.longLine false

@[expose] public section
set_option allowUnsafeReducibility true
set_option compiler.extract_closed false

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp0d_PostRootLowMem
open Operator Matrix Circuit

section
namespace GqspWronskian62592
section ZeroCacheKernelPrimitives
set_option exponentiation.threshold 2048
open Real
open scoped BigOperators
open TFreeLaurentGQSP
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChebWeightCertS4805
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
open TwoAngleBiGqspVerifierBridge
theorem gqsp_zwForce_eq {α : Type} (dflt : α) (f : ℕ → α) (x : ℕ) :
    @Nat.rec (fun _ ↦ α) dflt (fun v _ ↦ f v) (Nat.add 1 x) = f x := by
  change @Nat.rec (fun _ ↦ α) dflt (fun v _ ↦ f v) (1 + x) = f x
  rw [Nat.one_add]
theorem gqsp_zwBlt_eq (a b : ℕ) : Nat.ble (Nat.add a 1) b = Nat.blt a b :=
  congrArg (Nat.ble · b) (Nat.succ_eq_add_one a).symm
theorem gqsp_zwBoolRec_eq_casesOn {α : Type} :
    ∀ (b : Bool) (vf vt : α), @Bool.rec (fun _ ↦ α) vf vt b = @Bool.casesOn (fun _ ↦ α) b vf vt
  | false, _, _ => rfl
  | true, _, _ => rfl
theorem gqsp_zwBoolNot_eq : ∀ b : Bool, @Bool.rec (fun _ ↦ Bool) true false b = Bool.not b
  | false => rfl
  | true => rfl
theorem gqsp_zwParFlip_eq :
    ∀ (par : Bool) (B2 u : ℕ), @Bool.rec (fun _ ↦ ℕ) u (Nat.sub B2 u) par = ta_parFlip par B2 u
  | false, _, _ => rfl
  | true, _, _ => rfl
theorem gqsp_zwHeadD_eq (dflt : ℕ) :
    ∀ xs : List ℕ, @List.rec ℕ (fun _ ↦ ℕ) dflt (fun h _ _ ↦ h) xs = xs.headD dflt
  | [] => rfl
  | _ :: _ => rfl
theorem gqsp_zwTail_eq :
    ∀ xs : List ℕ, @List.rec ℕ (fun _ ↦ List ℕ) [] (fun _ t _ ↦ t) xs = xs.tail
  | [] => rfl
  | _ :: _ => rfl
theorem gqsp_zwAbsDiff_eq (a b : ℕ) :
    Nat.add (Nat.sub a b) (Nat.sub b a) = natAbsDiff a b := by
  refine Nat.cast_injective (R := ℝ) ?_
  rw [natAbsDiff_cast_real]
  rcases le_total a b with h | h
  · simp [Nat.add_eq, Nat.sub_eq, Nat.sub_eq_zero_of_le h, Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h))]
  · simp [Nat.add_eq, Nat.sub_eq, Nat.sub_eq_zero_of_le h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
theorem gqsp_zwAbsDiff_eq_int_natAbs (a b : ℕ) :
    Nat.add (Nat.sub a b) (Nat.sub b a) = Int.natAbs ((a : ℤ) - (b : ℤ)) :=
  (gqsp_zwAbsDiff_eq a b).trans <| Nat.cast_injective (R := ℝ) <| by
    rw [natAbsDiff_cast_real, natAbs_cast_real]
    push_cast
    rfl
/-- Zero-cache tail-recursive `List ℕ` reversal (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwRevNatTR (xs0 acc0 : List ℕ) : List ℕ := @List.rec ℕ
    (fun _ ↦ List ℕ → List ℕ) (fun acc ↦ acc) (fun x _ ih acc ↦ ih (x :: acc)) xs0 acc0
theorem gqsp_zwRevNatTR_eq : ∀ (xs acc : List ℕ), gqsp_zwRevNatTR xs acc = ta_revNatTR xs acc
  | [], _ => rfl
  | x :: xs, acc => (gqsp_zwRevNatTR_eq xs (x :: acc)).trans (ta_revNatTR_cons x xs acc).symm
/-- Zero-cache strict-element `List ℕ` reversal (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwStrictRevNatTR (xs0 acc0 : List ℕ) : List ℕ := @List.rec ℕ
    (fun _ ↦ List ℕ → List ℕ) (fun acc ↦ acc) (fun x _ ih acc ↦ @Nat.rec (fun _ ↦ List ℕ) []
    (fun x' _ ↦ ih (x' :: acc)) (Nat.add 1 x)) xs0 acc0
theorem gqsp_zwStrictRevNatTR_eq :
    ∀ (xs acc : List ℕ), gqsp_zwStrictRevNatTR xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
      dsimp only [gqsp_zwStrictRevNatTR]
      rw [gqsp_zwForce_eq]
      exact (gqsp_zwStrictRevNatTR_eq xs (x :: acc)).trans (by simp)
/-- Zero-cache strict `List ℕ` normalizer (`0` `DefinitionVal`s inside loops). -/
noncomputable def gqsp_zwStrictNatList (xs : List ℕ) : List ℕ :=
  gqsp_zwRevNatTR (gqsp_zwStrictRevNatTR xs []) []
theorem gqsp_zwStrictNatList_eq (xs : List ℕ) : gqsp_zwStrictNatList xs = xs := by
  simp [gqsp_zwStrictNatList, gqsp_zwRevNatTR_eq, ta_revNatTR_eq, gqsp_zwStrictRevNatTR_eq]
/-- Zero-cache tail-recursive `List PQPair` reversal (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwRevPQTR (xs0 acc0 : List PQPair) : List PQPair := @List.rec PQPair
    (fun _ ↦ List PQPair → List PQPair) (fun acc ↦ acc) (fun h _ ih acc ↦ ih (h :: acc)) xs0 acc0
theorem gqsp_zwRevPQTR_eq : ∀ (xs acc : List PQPair), gqsp_zwRevPQTR xs acc = ta_revPQTR xs acc
  | [], _ => rfl
  | ⟨ph, qh⟩ :: xs, acc => by
      rw [ta_revPQTR_cons]
      exact gqsp_zwRevPQTR_eq xs (⟨ph, qh⟩ :: acc)
/-! ## Zero-Cache Chebyshev Weights & Wronskian Recurrence Verifiers -/
/-- Zero-cache `2 * u - Bw` reversed list builder (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwDoubleBiasedRevTR (Bw : ℕ) (xs0 acc0 : List ℕ) : List ℕ := @List.rec
    ℕ (fun _ ↦ List ℕ → List ℕ) (fun acc ↦ acc) (fun u _ ih acc ↦ @Nat.rec (fun _ ↦ List ℕ) []
    (fun w _ ↦ ih (w :: acc)) (Nat.add 1 (Nat.sub (Nat.mul 2 u) Bw))) xs0 acc0
theorem gqsp_zwDoubleBiasedRevTR_eq_fast (Bw : ℕ) :
    ∀ (xs acc : List ℕ), gqsp_zwDoubleBiasedRevTR Bw xs acc = gqsp_doubleBiasedRevTR Bw xs acc
  | [], _ => rfl
  | u :: ut, acc => by
      dsimp only [gqsp_zwDoubleBiasedRevTR, gqsp_doubleBiasedRevTR]
      rw [gqsp_zwForce_eq]
      change gqsp_zwDoubleBiasedRevTR Bw ut (Nat.sub (Nat.mul 2 u) Bw :: acc) =
        @Nat.casesOn (fun _ ↦ List ℕ) (1 + Nat.sub (Nat.mul 2 u) Bw) []
          (fun w ↦ gqsp_tramp (gqsp_doubleBiasedRevTR Bw ut (w :: acc)))
      rw [Nat.one_add]
      exact gqsp_zwDoubleBiasedRevTR_eq_fast Bw ut _
/-- Zero-cache unpadded Chebyshev weight builder matching `gqsp_buildChebWsUnpadFast`. -/
noncomputable def gqsp_buildChebWsUnpadLowMem (Bw : ℕ) (us : List ℕ) : List ℕ := @List.rec ℕ
    (fun _ ↦ List ℕ) [Bw] (fun u0 ut _ ↦ u0 :: gqsp_zwRevNatTR (gqsp_zwDoubleBiasedRevTR Bw
    ut []) []) us
theorem gqsp_buildChebWsUnpadLowMem_eq (Bw : ℕ) :
    ∀ us : List ℕ, gqsp_buildChebWsUnpadLowMem Bw us = gqsp_buildChebWsUnpadFast Bw us
  | [] => rfl
  | u0 :: ut => by
      dsimp only [gqsp_buildChebWsUnpadLowMem, gqsp_buildChebWsUnpadFast]
      rw [gqsp_zwRevNatTR_eq, gqsp_zwDoubleBiasedRevTR_eq_fast]
theorem gqsp_buildChebWsUnpadLowMem_append_eq (Bw pad : ℕ) (us : List ℕ) (hne : 0 < us.length) :
    gqsp_buildChebWsUnpadLowMem Bw us ++ List.replicate pad Bw =
      buildChebWsFromBiasedU Bw pad us :=
  gqsp_buildChebWsUnpadLowMem_eq Bw us ▸ gqsp_buildChebWsUnpadFast_append_eq Bw pad us hne
/-- Zero-cache downward Miller recurrence + `shr 144` rescaler (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwMillerDownU (β_nat Bw_hi Bw2_hi Bw steps : ℕ) :
    ℕ → ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ)
    (fun j0 _ acc ↦
      let u0 := @Bool.rec (fun _ ↦ ℕ) (Nat.add Bw (Nat.shiftRight (Nat.sub j0 Bw_hi) 144))
        (Nat.sub Bw (Nat.shiftRight (Nat.sub Bw_hi j0) 144)) (Nat.ble (Nat.add j0 1) Bw_hi)
      @Nat.rec (fun _ ↦ List ℕ) [] (fun u0' _ ↦ u0' :: acc) (Nat.add 1 u0))
    (fun d ih jd jd1 acc ↦
      let jprev0 := @Bool.rec (fun _ ↦ ℕ)
        (Nat.sub (Nat.add Bw2_hi (Nat.div (Nat.mul (Nat.mul 2 (Nat.add d 1))
          (Nat.sub jd Bw_hi)) β_nat)) jd1)
        (Nat.sub (Nat.sub Bw2_hi (Nat.div (Nat.mul (Nat.mul 2 (Nat.add d 1))
          (Nat.sub Bw_hi jd)) β_nat)) jd1) (Nat.ble (Nat.add jd 1) Bw_hi)
      let ud0 := @Bool.rec (fun _ ↦ ℕ) (Nat.add Bw (Nat.shiftRight (Nat.sub jd Bw_hi) 144))
        (Nat.sub Bw (Nat.shiftRight (Nat.sub Bw_hi jd) 144)) (Nat.ble (Nat.add jd 1) Bw_hi)
      @Nat.rec (fun _ ↦ List ℕ) [] (fun jprev _ ↦ @Nat.rec (fun _ ↦ List ℕ) []
        (fun ud _ ↦ ih jprev jd (ud :: acc)) (Nat.add 1 ud0)) (Nat.add 1 jprev0)) steps
/-- Zero-cache downward homogeneous Bessel solution `v` recurrence (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwMillerDownV (β_nat Bw Bw2 steps : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → List ℕ → List ℕ)
    (fun j0 _ acc ↦ @Nat.rec (fun _ ↦ List ℕ) [] (fun v0 _ ↦ v0 :: acc) (Nat.add 1 j0))
    (fun d ih jd jd1 acc ↦
      let jprev0 := @Bool.rec (fun _ ↦ ℕ) (Nat.sub (Nat.add Bw2 (Nat.div (Nat.mul (Nat.mul 2
          (Nat.add d 1)) (Nat.sub jd Bw)) β_nat)) jd1) (Nat.sub (Nat.sub Bw2 (Nat.div (Nat.mul
          (Nat.mul 2 (Nat.add d 1)) (Nat.sub Bw jd)) β_nat)) jd1) (Nat.ble (Nat.add jd 1) Bw)
      @Nat.rec (fun _ ↦ List ℕ) [] (fun jprev _ ↦ @Nat.rec (fun _ ↦ List ℕ) []
        (fun vd _ ↦ ih jprev jd (vd :: acc)) (Nat.add 1 jd)) (Nat.add 1 jprev0)) steps
/-- Zero-cache list length equality check `cnt0 + xs0.length == n_exp` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwLenEq (n_exp : ℕ) (xs0 : List ℕ) (cnt0 : ℕ) : Bool := @List.rec ℕ
    (fun _ ↦ ℕ → Bool) (fun cnt ↦ Nat.beq cnt n_exp) (fun _ _ ih cnt ↦ @Nat.rec (fun _ ↦ Bool)
    false (fun cnt' _ ↦ ih cnt') (Nat.add 1 (Nat.add 1 cnt))) xs0 cnt0
theorem gqsp_zwLenEq_spec (n_exp : ℕ) :
    ∀ (xs : List ℕ) (cnt : ℕ), gqsp_zwLenEq n_exp xs cnt = true → cnt + xs.length = n_exp
  | [], cnt, h => by simpa using Nat.beq_eq.mp h
  | _ :: xs, cnt, h => by
      dsimp only [gqsp_zwLenEq] at h
      rw [gqsp_zwForce_eq] at h
      have ih := gqsp_zwLenEq_spec n_exp xs (Nat.add 1 cnt) h
      simp only [List.length_cons, Nat.add_eq] at ih ⊢
      omega
/-- Zero-cache indexed `List.getD` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwGetD (dflt n0 : ℕ) : List ℕ → ℕ := @Nat.rec (fun _ ↦ List ℕ → ℕ)
    (fun xs ↦ @List.rec ℕ (fun _ ↦ ℕ) dflt (fun h _ _ ↦ h) xs)
    (fun _ ih xs ↦ @List.rec ℕ (fun _ ↦ ℕ) dflt (fun _ t _ ↦ ih t) xs) n0
theorem gqsp_zwGetD_eq (dflt : ℕ) :
    ∀ (n : ℕ) (xs : List ℕ), gqsp_zwGetD dflt n xs = xs.getD n dflt
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: t => by
      rw [getD_cons_succ_nat]
      exact gqsp_zwGetD_eq dflt n t
/-- Zero-cache `List.drop` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwDrop (n0 : ℕ) : List ℕ → List ℕ := @Nat.rec
    (fun _ ↦ List ℕ → List ℕ) (fun xs ↦ xs) (fun _ ih xs ↦ @List.rec ℕ (fun _ ↦ List ℕ) []
    (fun _ t _ ↦ ih t) xs) n0
theorem gqsp_zwDrop_eq : ∀ (n : ℕ) (xs : List ℕ), gqsp_zwDrop n xs = xs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: t => gqsp_zwDrop_eq n t
/-- Zero-cache maximum `|w - Bw|` loop matching `wsMaxMagLoop` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwMaxMagLoop (Bw : ℕ) (xs0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ → ℕ) (fun acc ↦ acc)
    (fun w _ ih acc ↦
      let diff := Nat.add (Nat.sub w Bw) (Nat.sub Bw w)
      let mx := @Bool.rec (fun _ ↦ ℕ) acc diff (Nat.ble acc diff)
      @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih acc') (Nat.add 1 mx)) xs0 acc0
theorem gqsp_zwMaxMagLoop_eq (Bw : ℕ) :
    ∀ (xs : List ℕ) (acc : ℕ), gqsp_zwMaxMagLoop Bw xs acc = wsMaxMagLoop Bw xs acc
  | [], _ => rfl
  | w :: wt, acc => by
      dsimp only [gqsp_zwMaxMagLoop]
      rw [gqsp_zwForce_eq, gqsp_zwAbsDiff_eq]
      have hmax : @Bool.rec (fun _ ↦ ℕ) acc (natAbsDiff w Bw) (Nat.ble acc (natAbsDiff w Bw)) =
          Nat.max acc (natAbsDiff w Bw) := by
        by_cases h : acc ≤ natAbsDiff w Bw
        · simp [Nat.ble_eq.mpr h, Nat.max_eq_right h]
        · simp [Bool.eq_false_iff.mpr (fun ht ↦ h (Nat.ble_eq.mp ht)),
            Nat.max_eq_left (Nat.le_of_not_le h)]
      change gqsp_zwMaxMagLoop Bw wt (@Bool.rec (fun _ ↦ ℕ) acc (natAbsDiff w Bw)
        (Nat.ble acc (natAbsDiff w Bw))) = wsMaxMagLoop Bw (w :: wt) acc
      simp only [hmax, gqsp_zwMaxMagLoop_eq Bw wt, wsMaxMagLoop, forceNatFast_eq]
/-- Zero-cache Miller three-term recurrence residual accumulator (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwMillerResLoop (β_nat Bw m0 : ℕ) : ℕ → List ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ ℕ → List ℕ → ℕ → ℕ) (fun _ _ acc ↦ acc) (fun _ ih d js acc ↦
    @List.rec ℕ (fun _ ↦ ℕ) acc (fun j0 rest _ ↦
      let j1 := @List.rec ℕ (fun _ ↦ ℕ) Bw (fun x _ _ ↦ x) rest
      let j2 := @List.rec ℕ (fun _ ↦ ℕ) Bw
        (fun _ r2 _ ↦ @List.rec ℕ (fun _ ↦ ℕ) Bw (fun y _ _ ↦ y) r2) rest
      let lhs := Nat.add (Nat.mul β_nat (Nat.add j0 j2)) (Nat.mul (Nat.mul 2 d) Bw)
      let rhs := Nat.add (Nat.mul (Nat.mul 2 β_nat) Bw) (Nat.mul (Nat.mul 2 d) j1)
      let rstep := Nat.add (Nat.sub lhs rhs) (Nat.sub rhs lhs)
      @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦
        @Nat.rec (fun _ ↦ ℕ) 0 (fun d' _ ↦ ih d' rest acc') (Nat.add 1 (Nat.add d 1)))
        (Nat.add 1 (Nat.add acc rstep))) js) m0
theorem gqsp_zwMillerResLoop_eq (β_nat Bw : ℕ) :
    ∀ (m d : ℕ) (js : List ℕ) (acc : ℕ),
      gqsp_zwMillerResLoop β_nat Bw m d js acc = millerResCountLoop β_nat Bw Bw m d js acc
  | 0, _, _, _ => rfl
  | _ + 1, _, [], _ => rfl
  | m + 1, d, j0 :: rest, acc => by
      dsimp only [gqsp_zwMillerResLoop]
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq]
      have hj1 : @List.rec ℕ (fun _ ↦ ℕ) Bw (fun x _ _ ↦ x) rest = rest.getD 0 Bw := by
        cases rest
        all_goals rfl
      have hj2 : @List.rec ℕ (fun _ ↦ ℕ) Bw
          (fun _ r2 _ ↦ @List.rec ℕ (fun _ ↦ ℕ) Bw (fun y _ _ ↦ y) r2) rest = rest.getD 1 Bw := by
        rcases rest with _ | ⟨_, _ | ⟨_, _⟩⟩
        all_goals rfl
      rw [hj1, hj2]
      have hstep : Nat.add (Nat.sub (Nat.add (Nat.mul β_nat (Nat.add j0 (rest.getD 1 Bw)))
          (Nat.mul (Nat.mul 2 d) Bw)) (Nat.add (Nat.mul (Nat.mul 2 β_nat) Bw) (Nat.mul
          (Nat.mul 2 d) (rest.getD 0 Bw)))) (Nat.sub (Nat.add (Nat.mul (Nat.mul 2 β_nat) Bw)
          (Nat.mul (Nat.mul 2 d) (rest.getD 0 Bw))) (Nat.add (Nat.mul β_nat (Nat.add j0
          (rest.getD 1 Bw))) (Nat.mul (Nat.mul 2 d) Bw))) = millerStepResidualNat β_nat Bw d
          j0 (rest.getD 0 Bw) (rest.getD 1 Bw) := by
        unfold millerStepResidualNat
        dsimp only
        rw [gqsp_zwAbsDiff_eq_int_natAbs]
        simp only [Nat.add_eq, Nat.mul_eq]
        congr 1
        push_cast
        ring
      rw [hstep]
      change gqsp_zwMillerResLoop β_nat Bw m (Nat.add d 1) rest
        (Nat.add acc (millerStepResidualNat β_nat Bw d j0 (rest.getD 0 Bw) (rest.getD 1 Bw))) =
        millerResCountLoop β_nat Bw Bw (m + 1) d (j0 :: rest) acc
      rw [gqsp_zwMillerResLoop_eq β_nat Bw m]
      simp only [millerResCountLoop, forceNatFast_eq, Nat.add_eq]
/-- Zero-cache Wronskian minimum check matching `wronskianMinCheckBle` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwWronskianMinBle (Bw W_min m0 : ℕ) : List ℕ → List ℕ → Bool :=
  @Nat.rec (fun _ ↦ List ℕ → List ℕ → Bool) (fun _ _ ↦ true) (fun _ ih us vs ↦
    @List.rec ℕ (fun _ ↦ Bool) false (fun u0 ur0 _ ↦
      @List.rec ℕ (fun _ ↦ Bool) false (fun u1 ur _ ↦
        @List.rec ℕ (fun _ ↦ Bool) false (fun v0 vr0 _ ↦
          @List.rec ℕ (fun _ ↦ Bool) false (fun v1 vr _ ↦
            let lhs := Nat.add (Nat.mul u0 v1) (Nat.mul Bw (Nat.add u1 v0))
            let rhs := Nat.add (Nat.mul u1 v0) (Nat.mul Bw (Nat.add u0 v1))
            let wstep := Nat.add (Nat.sub lhs rhs) (Nat.sub rhs lhs)
            @Bool.rec (fun _ ↦ Bool) false (ih (u1 :: ur) (v1 :: vr))
              (Nat.ble W_min wstep)) vr0) vs) ur0) us) m0
theorem gqsp_zwWronskianMinBle_eq (Bw W_min : ℕ) :
    ∀ (m : ℕ) (us vs : List ℕ),
      gqsp_zwWronskianMinBle Bw W_min m us vs = wronskianMinCheckBle Bw W_min us vs m
  | 0, us, vs => by
      rcases us with _ | ⟨_, _ | ⟨_, _⟩⟩
      all_goals rcases vs with _ | ⟨_, _ | ⟨_, _⟩⟩
      all_goals rfl
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl
  | _ + 1, _ :: _ :: _, [] => rfl
  | _ + 1, _ :: _ :: _, [_] => rfl
  | m + 1, u0 :: u1 :: ur, v0 :: v1 :: vr => by
      dsimp only [gqsp_zwWronskianMinBle]
      have hw : Nat.add (Nat.sub (Nat.add (Nat.mul u0 v1) (Nat.mul Bw (Nat.add u1 v0)))
          (Nat.add (Nat.mul u1 v0) (Nat.mul Bw (Nat.add u0 v1)))) (Nat.sub (Nat.add (Nat.mul
          u1 v0) (Nat.mul Bw (Nat.add u0 v1))) (Nat.add (Nat.mul u0 v1) (Nat.mul Bw (Nat.add
          u1 v0)))) = wronskianStepNat Bw u0 u1 v0 v1 := by
        unfold wronskianStepNat
        rw [gqsp_zwAbsDiff_eq_int_natAbs]
        simp only [Nat.add_eq, Nat.mul_eq]
        congr 1
        push_cast
        ring
      rw [hw]
      unfold wronskianMinCheckBle
      cases Nat.ble W_min (wronskianStepNat Bw u0 u1 v0 v1)
      · rfl
      · exact gqsp_zwWronskianMinBle_eq Bw W_min m (u1 :: ur) (v1 :: vr)
/-- Zero-cache Neumann sum `u_0 + 2 * ∑ u_{2m}` accumulator (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwEvenTailPosNeg (Bw fuel : ℕ) : List ℕ → ℕ → ℕ → ℕ × ℕ :=
  @Nat.rec (fun _ ↦ List ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ p n ↦ (p, n)) (fun _ ih xs p n ↦
    @List.rec ℕ (fun _ ↦ ℕ × ℕ) (p, n) (fun _ r1 _ ↦
      @List.rec ℕ (fun _ ↦ ℕ × ℕ) (p, n) (fun u_even rest _ ↦
        let cond := Nat.ble (Nat.add u_even 1) Bw
        let p0 := @Bool.rec (fun _ ↦ ℕ) (Nat.add p (Nat.mul 2 (Nat.sub u_even Bw))) p cond
        let n0 := @Bool.rec (fun _ ↦ ℕ) n (Nat.add n (Nat.mul 2 (Nat.sub Bw u_even))) cond
        @Nat.rec (fun _ ↦ ℕ × ℕ) (0, 0) (fun p' _ ↦
          @Nat.rec (fun _ ↦ ℕ × ℕ) (0, 0) (fun n' _ ↦ ih rest p' n')
            (Nat.add 1 n0)) (Nat.add 1 p0)) r1) xs) fuel
theorem gqsp_zwEvenTailPosNeg_eq (Bw : ℕ) :
    ∀ (fuel : ℕ) (xs : List ℕ) (p n : ℕ), xs.length ≤ 2 * fuel →
      gqsp_zwEvenTailPosNeg Bw fuel xs p n = evenTailPosNegLoop Bw xs p n
  | 0, xs, _, _, hlen => by
      cases xs with
      | nil => rfl
      | cons _ _ => simp at hlen
  | _ + 1, [], _, _, _ => rfl
  | _ + 1, [_], _, _, _ => rfl
  | fuel + 1, _ :: u_even :: rest, p, n, hlen => by
      have hlen' : rest.length ≤ 2 * fuel := by
        simp only [List.length_cons] at hlen
        omega
      dsimp only [gqsp_zwEvenTailPosNeg]
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwBlt_eq]
      unfold evenTailPosNegLoop
      cases Nat.blt u_even Bw
      all_goals simp only [Bool.false_eq_true, ↓reduceIte, forceNatFast_eq]
      all_goals exact gqsp_zwEvenTailPosNeg_eq Bw fuel rest _ _ hlen'
/-- Zero-cache check `∀ u ∈ xs, Bw ≤ 2 * u` matching `doubleBiasedAllGeBle` (`0`
  `DefinitionVal`s). -/
noncomputable def gqsp_zwDoubleGeBle (Bw : ℕ) (xs0 : List ℕ) : Bool := @List.rec ℕ
    (fun _ ↦ Bool) true (fun u _ ih ↦ @Bool.rec (fun _ ↦ Bool) false ih (Nat.ble Bw (Nat.mul 2
    u))) xs0
theorem gqsp_zwDoubleGeBle_eq (Bw : ℕ) :
    ∀ xs : List ℕ, gqsp_zwDoubleGeBle Bw xs = doubleBiasedAllGeBle Bw xs
  | [] => rfl
  | u :: ut => by
      dsimp only [gqsp_zwDoubleGeBle]
      unfold doubleBiasedAllGeBle
      cases Nat.ble Bw (Nat.mul 2 u)
      · rfl
      · exact gqsp_zwDoubleGeBle_eq Bw ut
/-! ## Zero-Cache `pack768` Chunk Unpacker & 1-Angle Post-Root Pipeline -/
theorem gqsp_zwMask768_eq :
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff =
      gqsp_mask768 :=
  rfl
/-- Zero-cache `n0`-lane `pack768` peeler (`0` `DefinitionVal`s inside loop). -/
noncomputable def gqsp_zwPeel1Shr256Aux (n0 : ℕ) : ℕ → List ℕ → List ℕ :=
  @Nat.rec (fun _ ↦ ℕ → List ℕ → List ℕ)
    (fun _ racc ↦ racc)
    (fun _ ih w racc ↦
      let v0 := Nat.shiftRight (Nat.land w 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) 256
      let w0 := Nat.shiftRight w 768
      @Nat.rec (fun _ ↦ List ℕ) [] (fun v _ ↦
        @Nat.rec (fun _ ↦ List ℕ) [] (fun w' _ ↦ ih w' (v :: racc)) (Nat.add 1 w0))
        (Nat.add 1 v0))
    n0
theorem gqsp_zwPeel1Shr256Aux_succ (r w : ℕ) (racc : List ℕ) : gqsp_zwPeel1Shr256Aux (r + 1)
    w racc = gqsp_zwPeel1Shr256Aux r (Nat.shiftRight w 768)
    (Nat.shiftRight (Nat.land w gqsp_mask768) 256 :: racc) := by
  dsimp only [gqsp_zwPeel1Shr256Aux]
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq]
  rfl
theorem gqsp_unpackPow2LeafAux_eq_zw :
    ∀ (r s w : ℕ) (racc : List ℕ),
      gqsp_unpackPow2LeafAux r s w racc = gqsp_zwPeel1Shr256Aux r w racc
  | 0, _, _, _ => rfl
  | r + 1, s, w, racc => by
      change gqsp_speel1Step (gqsp_unpackPow2LeafAux r) s w racc = _
      unfold gqsp_speel1Step gqsp_speel1StepHi gqsp_speel1StepGo
      simp only [sched_stfList_eq, sched_idSalt_eq]
      rw [gqsp_zwPeel1Shr256Aux_succ, gqsp_unpackPow2LeafAux_eq_zw r]
theorem gqsp_unpackPow2Leaf4SaltAux_eq_zw (rem : ℕ) :
    ∀ (q s w : ℕ) (racc : List ℕ),
      gqsp_unpackPow2Leaf4SaltAux q rem s w racc = gqsp_zwPeel1Shr256Aux (4 * q + rem) w racc
  | 0, s, w, racc => by
      rw [Nat.mul_zero, Nat.zero_add]
      exact gqsp_unpackPow2LeafAux_eq_zw rem s w racc
  | q + 1, s, w, racc => by
      change gqsp_speel4Step (gqsp_unpackPow2Leaf4SaltAux q rem) s w racc = _
      unfold gqsp_speel4Step gqsp_speel4StepGo gqsp_speel4Op gqsp_speel4Op1
        gqsp_speel4Op2 gqsp_speel4Op3 gqsp_speel1Op gqsp_speelConsFlip
      simp only [sched_stfList_eq, sched_idSalt_eq]
      have h4 : 4 * (q + 1) + rem = (((4 * q + rem) + 1) + 1) + 1 + 1 := by omega
      have h3072 : (3072 : ℕ) = 768 + (768 + (768 + 768)) := rfl
      rw[h4, gqsp_zwPeel1Shr256Aux_succ, gqsp_zwPeel1Shr256Aux_succ,
          gqsp_zwPeel1Shr256Aux_succ, gqsp_zwPeel1Shr256Aux_succ, h3072, gqsp_shr_add,
          gqsp_shr_add, gqsp_shr_add, gqsp_unpackPow2Leaf4SaltAux_eq_zw rem q]
/-- Zero-cache chunk list peeler unconditionally equal to `gqsp_peelWords64RevTR`. -/
noncomputable def gqsp_zwPeelWords64RevTR (chunks0 : List (ℕ × ℕ)) (racc0 : List ℕ) : List ℕ
    := @List.rec (ℕ × ℕ) (fun _ ↦ List ℕ → List ℕ) (fun racc ↦ racc) (fun p _ ih racc ↦
    @Prod.rec ℕ ℕ (fun _ ↦ List ℕ) (fun n w ↦ ih (gqsp_zwPeel1Shr256Aux n w racc)) p) chunks0
    racc0
theorem gqsp_zwPeelWords64RevTR_eq :
    ∀ (chunks : List (ℕ × ℕ)) (s : ℕ) (racc : List ℕ),
      gqsp_zwPeelWords64RevTR chunks racc = gqsp_peelWords64RevTR chunks s racc
  | [], _, _ => rfl
  | (n, w) :: chunks, s, racc => by
      dsimp only [gqsp_zwPeelWords64RevTR]
      rw [gqsp_peelWords64RevTR_cons, gqsp_unpackPow2Leaf4SaltAux_eq_zw]
      have hdiv : 4 * (Nat.div n 4) + Nat.mod n 4 = n := Nat.div_add_mod n 4
      rw [hdiv]
      exact gqsp_zwPeelWords64RevTR_eq chunks (Nat.add 512 s) _
/-- Zero-cache `64`-lane chunked `pack768` unpacker unconditionally equal to
  `gqsp_sunpackShr256Chunked`. -/
noncomputable def gqsp_zwSunpackShr256Chunked (d n w : ℕ) : List ℕ :=
  @Nat.rec (fun _ ↦ List ℕ) [] (fun w0 _ ↦
    let s0 := Nat.add 0x10000000000 (Nat.land (Nat.xor (Nat.mul 0x9e3779b9 n) (Nat.xor
        (Nat.xor (Nat.xor (Nat.shiftRight w0 256) (Nat.shiftRight w0 1024)) (Nat.xor
        (Nat.shiftRight w0 4096) (Nat.shiftRight w0 16384))) (Nat.xor (Nat.xor (Nat.shiftRight
        w0 65536) (Nat.shiftRight w0 524288)) (Nat.xor (Nat.shiftRight w0 4194304)
        (Nat.shiftRight w0 33554432))))) 0xfffffffff)
    @Nat.rec (fun _ ↦ List ℕ) [] (fun s _ ↦
      gqsp_zwRevNatTR (gqsp_zwPeelWords64RevTR (gqsp_splitWords64Aux (Nat.sub d 6) s n w0 []) [])
        [])
      (Nat.add 1 s0))
    (Nat.add 1 w)
theorem gqsp_zwSunpackShr256Chunked_eq (d n w : ℕ) :
    gqsp_zwSunpackShr256Chunked d n w = gqsp_sunpackShr256Chunked d n w := by
  unfold gqsp_zwSunpackShr256Chunked gqsp_sunpackShr256Chunked
    gqsp_sunpackShr256ChunkedSalt gqsp_sunpackShr256ChunkedGo
  rw [gqsp_zwForce_eq, gqsp_zwForce_eq, ta_tfList_eq, sched_tfList_eq,
    gqsp_zwRevNatTR_eq, gqsp_srevNatTR_eq]
  congr 1
  exact gqsp_zwPeelWords64RevTR_eq _ _ []
/-- Zero-cache 1-angle `(ep, eq, op, oq)` reversed interleaver (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwInterleave1AngleRevTR (B2 BIAS : ℕ)
    (uP0 uQ0 ruP0 ruQ0 : List ℕ) (acc0 : List PQPair) : List PQPair :=
  @List.rec ℕ (fun _ ↦ List ℕ → List ℕ → List ℕ → List PQPair → List PQPair) (fun _ _ _ a ↦ a)
    (fun up _ ih luq lrup lruq a ↦
      @List.rec ℕ (fun _ ↦ List PQPair) a (fun uq uqt _ ↦
        @List.rec ℕ (fun _ ↦ List PQPair) a (fun rup rupt _ ↦
          @List.rec ℕ (fun _ ↦ List PQPair) a (fun ruq ruqt _ ↦
            let ep0 := Nat.add up BIAS
            let eq0 := Nat.add uq BIAS
            let op0 := Nat.sub B2 (Nat.add ruq BIAS)
            let oq0 := Nat.add rup BIAS
            @Nat.rec (fun _ ↦ List PQPair) [] (fun ep _ ↦ @Nat.rec (fun _ ↦ List PQPair) []
              (fun eq _ ↦ @Nat.rec (fun _ ↦ List PQPair) [] (fun op _ ↦
                @Nat.rec (fun _ ↦ List PQPair) [] (fun oq _ ↦
                  ih uqt rupt ruqt (PQPair.mk op oq :: PQPair.mk ep eq :: a))
                (Nat.add 1 oq0)) (Nat.add 1 op0)) (Nat.add 1 eq0)) (Nat.add 1 ep0))
          lruq) lrup) luq) uP0 uQ0 ruP0 ruQ0 acc0
theorem gqsp_zwInterleave1AngleRevTR_eq (B2 BIAS : ℕ) :
    ∀ (uP : List ℕ) (s : ℕ) (uQ ruP ruQ : List ℕ) (acc : List PQPair),
      gqsp_zwInterleave1AngleRevTR B2 BIAS uP uQ ruP ruQ acc =
        gqsp_interleave1AngleRevTR B2 BIAS s uP uQ ruP ruQ acc
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, [], _, _, _ => rfl
  | _ :: _, _, _ :: _, [], _, _ => rfl
  | _ :: _, _, _ :: _, _ :: _, [], _ => rfl
  | up :: upt, s, uq :: uqt, rup :: rupt, ruq :: ruqt, acc => by
      dsimp only [gqsp_zwInterleave1AngleRevTR]
      rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwForce_eq,
        gqsp_interleave1AngleRevTR_cons]
      exact gqsp_zwInterleave1AngleRevTR_eq B2 BIAS upt (Nat.add 4 s) uqt rupt ruqt _
/-- Zero-cache `.p`-only reversed outer Hadamard pass (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwHadamardRevPOnly (B : ℕ) (pq0 : List PQPair) (q0 : ℕ)
    (acc0 : List ℕ) : List ℕ := @List.rec PQPair (fun _ ↦ ℕ → List ℕ → List ℕ) (fun q_prev acc
    ↦ @Nat.rec (fun _ ↦ List ℕ) [] (fun np _ ↦ np :: acc) (Nat.add 1 (Nat.shiftRight (Nat.add
    B q_prev) 1))) (fun h _ ih q_prev acc ↦ @PQPair.rec (fun _ ↦ List ℕ) (fun ph qh ↦ @Nat.rec
    (fun _ ↦ List ℕ) [] (fun np _ ↦ ih qh (np :: acc)) (Nat.add 1 (Nat.shiftRight (Nat.add ph
    q_prev) 1))) h) pq0 q0 acc0
theorem gqsp_zwHadamardRevPOnly_eq (B : ℕ) :
    ∀ (pq : List PQPair) (s q_prev : ℕ) (acc : List ℕ),
      gqsp_zwHadamardRevPOnly B pq q_prev acc = ta_hadamardRevPOnlyFast B pq s q_prev acc
  | [], s, q_prev, acc => by
      dsimp only [gqsp_zwHadamardRevPOnly, ta_hadamardRevPOnlyFast]
      rw [gqsp_zwForce_eq]
      simp only [ta_stfList_eq, ta_hadamardNilGo, ta_idSalt]
  | ⟨ph, qh⟩ :: t, s, q_prev, acc => by
      dsimp only [gqsp_zwHadamardRevPOnly]
      rw [gqsp_zwForce_eq, ta_hadamardRevPOnlyFast_cons]
      exact gqsp_zwHadamardRevPOnly_eq B t (Nat.add 2 s) qh _
/-- Zero-cache `.p`-only splitter into `(neg_rev, p_center, pos_tail_p)` (`0` `DefinitionVal`s in
  loop). -/
noncomputable def gqsp_zwSplitPRevNil (B m0 : ℕ) (neg0 : List ℕ) : List ℕ × ℕ × List ℕ :=
    @Nat.rec (fun _ ↦ List ℕ → List ℕ × ℕ × List ℕ) (fun neg_acc ↦ (neg_acc, B, []))
    (fun _ ih neg_acc ↦ ih (B :: neg_acc)) m0 neg0
theorem gqsp_zwSplitPRevNil_eq (B : ℕ) :
    ∀ (m : ℕ) (neg_acc : List ℕ), gqsp_zwSplitPRevNil B m neg_acc = ta_splitPRevNil B m neg_acc
  | 0, _ => rfl
  | m + 1, neg_acc => gqsp_zwSplitPRevNil_eq B m (B :: neg_acc)
noncomputable def gqsp_zwSplitPRev (B m0 : ℕ) (ps0 neg0 : List ℕ) : List ℕ × ℕ × List ℕ :=
    @List.rec ℕ (fun _ ↦ ℕ → List ℕ → List ℕ × ℕ × List ℕ)
    (fun m neg_acc ↦ gqsp_zwSplitPRevNil B m neg_acc) (fun p ps ih m neg_acc ↦ @Nat.rec (fun
    _ ↦ List ℕ × ℕ × List ℕ) (neg_acc, p, ps) (fun m' _ ↦ ih m' (p :: neg_acc)) m) ps0 m0 neg0
theorem gqsp_zwSplitPRev_eq (B : ℕ) :
    ∀ (ps : List ℕ) (m : ℕ) (neg_acc : List ℕ),
      gqsp_zwSplitPRev B m ps neg_acc = gqsp_ssplitPRevFast B m ps neg_acc
  | [], m, neg_acc => by
      dsimp only [gqsp_zwSplitPRev, gqsp_ssplitPRevFast]
      exact gqsp_zwSplitPRevNil_eq B m neg_acc
  | _ :: _, 0, _ => rfl
  | p :: ps, m + 1, neg_acc => by
      rw [gqsp_ssplitPRevFast_eq]
      dsimp only [gqsp_zwSplitPRev]
      change gqsp_zwSplitPRev B m ps (p :: neg_acc) = ta_splitPRevFast B (m + 1) (p :: ps) neg_acc
      rw [gqsp_zwSplitPRev_eq B ps m (p :: neg_acc), gqsp_ssplitPRevFast_eq]
      rfl
/-- Zero-cache tail accumulator for `d > M1` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwChebTail (Bw W_err_dpos pad : ℕ) (ws0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ → ℕ) (fun acc ↦ Nat.add acc (Nat.mul pad W_err_dpos))
    (fun w _ ih acc ↦
      let diff := Nat.add (Nat.sub w Bw) (Nat.sub Bw w)
      @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih acc')
        (Nat.add 1 (Nat.add acc (Nat.add diff W_err_dpos)))) ws0 acc0
theorem gqsp_zwChebTail_eq (Bw W_err_dpos pad : ℕ) :
    ∀ (ws : List ℕ) (acc : ℕ),
      gqsp_zwChebTail Bw W_err_dpos pad ws acc = ta_chebTailFast Bw W_err_dpos pad ws acc
  | [], _ => rfl
  | w :: wt, acc => by
      dsimp only [gqsp_zwChebTail]
      rw [gqsp_zwForce_eq, gqsp_zwAbsDiff_eq, ta_chebTailFast_cons]
      exact gqsp_zwChebTail_eq Bw W_err_dpos pad wt _
/-- Zero-cache `.p`-only positive-index Chebyshev L1 loop (`0` `DefinitionVal`s inside `rem > 0`
  loop). -/
noncomputable def gqsp_zwChebL1Pos (B B2 Bw W_err_dpos err_d_in pad : ℕ)
    (ws0 : List ℕ) (rem0 : ℕ) (par0 : Bool) (neg0 pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ → Bool → List ℕ → List ℕ → ℕ → ℕ)
    (fun _ _ _ _ acc ↦ Nat.add acc (Nat.mul pad W_err_dpos))
    (fun w wt ih rem par neg_cur pos_cur acc ↦ @Nat.rec (fun _ ↦ ℕ)
      (let diff0 := Nat.add (Nat.sub w Bw) (Nat.sub Bw w)
       @Nat.rec (fun _ ↦ ℕ) 0 (fun acc1 _ ↦ gqsp_zwChebTail Bw W_err_dpos pad wt acc1)
         (Nat.add 1 (Nat.add acc (Nat.add diff0 W_err_dpos))))
      (fun rem' _ ↦
        let p_neg := @List.rec ℕ (fun _ ↦ ℕ) B (fun h _ _ ↦ h) neg_cur
        let nt := @List.rec ℕ (fun _ ↦ List ℕ) [] (fun _ t _ ↦ t) neg_cur
        let p_pos_raw := @List.rec ℕ (fun _ ↦ ℕ) B (fun h _ _ ↦ h) pos_cur
        let pt := @List.rec ℕ (fun _ ↦ List ℕ) [] (fun _ t _ ↦ t) pos_cur
        let p_pos := @Bool.rec (fun _ ↦ ℕ) p_pos_raw (Nat.sub B2 p_pos_raw) par
        let par' := @Bool.rec (fun _ ↦ Bool) true false par
        let a := Nat.add (Nat.add p_pos p_neg) Bw
        let b := Nat.add w B2
        let diff := Nat.add (Nat.sub a b) (Nat.sub b a)
        @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih rem' par' nt pt acc')
          (Nat.add 1 (Nat.add acc (Nat.add diff err_d_in)))) rem) ws0 rem0 par0 neg0 pos0 acc0
theorem gqsp_zwChebL1Pos_eq (B B2 Bw W_err_dpos err_d_in pad : ℕ) :
    ∀ (ws : List ℕ) (rem : ℕ) (par : Bool) (neg_cur pos_cur : List ℕ) (acc : ℕ),
      gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad ws rem par neg_cur pos_cur acc =
        gqsp_chebL1PosBoolPar B B2 Bw W_err_dpos err_d_in pad ws rem par neg_cur pos_cur acc
  | [], _, _, _, _, _ => rfl
  | w :: wt, Nat.zero, _, _, _, acc => by
      dsimp only [gqsp_zwChebL1Pos, gqsp_chebL1PosBoolPar]
      rw [gqsp_zwForce_eq, ta_tfNat_eq, gqsp_zwAbsDiff_eq, gqsp_zwChebTail_eq]
  | w :: wt, rem' + 1, par, neg_cur, pos_cur, acc => by
      dsimp only [gqsp_zwChebL1Pos]
      rw [gqsp_zwForce_eq, gqsp_zwHeadD_eq, gqsp_zwTail_eq, gqsp_zwHeadD_eq, gqsp_zwTail_eq,
        gqsp_zwParFlip_eq, gqsp_zwBoolNot_eq, gqsp_zwAbsDiff_eq,
        gqsp_chebL1PosBoolPar_cons_succ]
      exact gqsp_zwChebL1Pos_eq B B2 Bw W_err_dpos err_d_in pad wt rem'
        (Bool.not par) neg_cur.tail pos_cur.tail _
/-- Zero-cache `.p`-only Chebyshev L1 sum matching `gqsp_chebL1POnlyFast`. -/
noncomputable def gqsp_zwChebL1POnly (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail ws_unpad : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ) 0 (fun w0 wt _ ↦
    let a0 := Nat.add p_center Bw
    let b0 := Nat.add w0 B
    let diff0 := Nat.add (Nat.sub a0 b0) (Nat.sub b0 a0)
    let term0_raw := Nat.add diff0 (Nat.add R_final W_err_d0)
    let err_d_raw := Nat.add (Nat.mul 2 R_final) W_err_dpos
    @Nat.rec (fun _ ↦ ℕ) 0 (fun term0 _ ↦ @Nat.rec (fun _ ↦ ℕ) 0 (fun err_d_in _ ↦
      gqsp_zwChebL1Pos B B2 Bw W_err_dpos err_d_in pad wt M1 true neg_rev pos_tail term0)
      (Nat.add 1 err_d_raw)) (Nat.add 1 term0_raw)) ws_unpad
theorem gqsp_zwChebL1POnly_eq (M1 B B2 Bw R_final W_err_d0 W_err_dpos pad : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail ws_unpad : List ℕ) :
    gqsp_zwChebL1POnly M1 B B2 Bw R_final W_err_d0 W_err_dpos pad neg_rev p_center pos_tail ws_unpad
      =
      gqsp_chebL1POnlyFast M1 B B2 Bw R_final W_err_d0 W_err_dpos pad neg_rev p_center pos_tail
        ws_unpad := by
  rcases ws_unpad with _ | ⟨w0, wt⟩
  · rfl
  · unfold gqsp_zwChebL1POnly gqsp_chebL1POnlyFast
    dsimp only
    rw [gqsp_zwForce_eq, gqsp_zwForce_eq, gqsp_zwAbsDiff_eq]
    simp only [ta_tfNat_eq, ta_tfNatFn_eq, gqsp_chebL1StartGo, gqsp_zwChebL1Pos_eq]
/-- Zero-cache empty-`neg_cur` fallback for asymmetry defect (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwAsymDefectEmpty (B B2 two_Rf k0 : ℕ)
    (par0 : Bool) (pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @Nat.rec (fun _ ↦ Bool → List ℕ → ℕ → ℕ) (fun _ _ acc ↦ acc) (fun _ ih par pos_cur acc ↦
    let p_pos_raw := @List.rec ℕ (fun _ ↦ ℕ) B (fun h _ _ ↦ h) pos_cur
    let pt := @List.rec ℕ (fun _ ↦ List ℕ) [] (fun _ t _ ↦ t) pos_cur
    let p_pos := @Bool.rec (fun _ ↦ ℕ) p_pos_raw (Nat.sub B2 p_pos_raw) par
    let par' := @Bool.rec (fun _ ↦ Bool) true false par
    let diff := Nat.add (Nat.sub p_pos B) (Nat.sub B p_pos)
    @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih par' pt acc')
      (Nat.add 1 (Nat.add acc (Nat.add diff two_Rf)))) k0 par0 pos0 acc0
theorem gqsp_zwAsymDefectEmpty_eq (B B2 two_Rf : ℕ) :
    ∀ (k : ℕ) (par : Bool) (pos_cur : List ℕ) (acc : ℕ),
      gqsp_zwAsymDefectEmpty B B2 two_Rf k par pos_cur acc =
        ta_asymDefectEmptyPOnly B B2 two_Rf k par pos_cur acc
  | 0, _, _, _ => rfl
  | k + 1, par, pos_cur, acc => by
      cases pos_cur
      all_goals dsimp only [gqsp_zwAsymDefectEmpty, ta_asymDefectEmptyPOnly]
      all_goals rw [gqsp_zwForce_eq, ta_tfNat_eq, gqsp_zwParFlip_eq, gqsp_zwBoolNot_eq,
        gqsp_zwAbsDiff_eq]
      all_goals exact gqsp_zwAsymDefectEmpty_eq B B2 two_Rf k (Bool.not par) _ _
/-- Zero-cache `.p`-only asymmetry defect loop (`0` `DefinitionVal`s inside loop). -/
noncomputable def gqsp_zwAsymDefectLoop (B B2 two_Rf k0 : ℕ)
    (par0 : Bool) (neg0 pos0 : List ℕ) (acc0 : ℕ) : ℕ :=
  @List.rec ℕ (fun _ ↦ ℕ → Bool → List ℕ → ℕ → ℕ)
    (fun k par pos_cur acc ↦ gqsp_zwAsymDefectEmpty B B2 two_Rf k par pos_cur acc)
    (fun p_neg _ ih k par pos_cur acc ↦ @Nat.rec (fun _ ↦ ℕ) acc (fun k' _ ↦
      let p_pos_raw := @List.rec ℕ (fun _ ↦ ℕ) B (fun h _ _ ↦ h) pos_cur
      let pt := @List.rec ℕ (fun _ ↦ List ℕ) [] (fun _ t _ ↦ t) pos_cur
      let p_pos := @Bool.rec (fun _ ↦ ℕ) p_pos_raw (Nat.sub B2 p_pos_raw) par
      let par' := @Bool.rec (fun _ ↦ Bool) true false par
      let diff := Nat.add (Nat.sub p_pos p_neg) (Nat.sub p_neg p_pos)
      @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih k' par' pt acc')
        (Nat.add 1 (Nat.add acc (Nat.add diff two_Rf)))) k) neg0 k0 par0 pos0 acc0
theorem gqsp_zwAsymDefectLoop_eq (B B2 two_Rf : ℕ) :
    ∀ (neg_cur : List ℕ) (k : ℕ) (par : Bool) (pos_cur : List ℕ) (acc : ℕ),
      gqsp_zwAsymDefectLoop B B2 two_Rf k par neg_cur pos_cur acc =
        gqsp_asymDefectLoopPOnlyFast B B2 two_Rf k par neg_cur pos_cur acc
  | [], k, par, pos_cur, acc => by
      dsimp only [gqsp_zwAsymDefectLoop, gqsp_asymDefectLoopPOnlyFast]
      exact gqsp_zwAsymDefectEmpty_eq B B2 two_Rf k par pos_cur acc
  | _ :: _, 0, _, _, _ => rfl
  | p_neg :: nt, k' + 1, par, pos_cur, acc => by
      dsimp only [gqsp_zwAsymDefectLoop]
      rw [gqsp_zwForce_eq, gqsp_zwHeadD_eq, gqsp_zwTail_eq, gqsp_zwParFlip_eq,
        gqsp_zwBoolNot_eq, gqsp_zwAbsDiff_eq, gqsp_asymDefectLoopPOnlyFast_cons]
      exact gqsp_zwAsymDefectLoop_eq B B2 two_Rf nt k' (Bool.not par) pos_cur.tail _
noncomputable def gqsp_zwAsymDefectPOnly (M1 B B2 R_final : ℕ) (neg_rev pos_tail : List ℕ) :
    ℕ := @Nat.rec (fun _ ↦ ℕ) 0 (fun two_Rf _ ↦ gqsp_zwAsymDefectLoop B B2 two_Rf M1 true
    neg_rev pos_tail 0) (Nat.add 1 (Nat.mul 2 R_final))
theorem gqsp_zwAsymDefectPOnly_eq (M1 B B2 R_final : ℕ) (neg_rev pos_tail : List ℕ) :
    gqsp_zwAsymDefectPOnly M1 B B2 R_final neg_rev pos_tail =
      gqsp_asymDefectPOnlyFast M1 B B2 R_final neg_rev pos_tail := by
  unfold gqsp_zwAsymDefectPOnly gqsp_asymDefectPOnlyFast
  rw [gqsp_zwForce_eq, ta_tfNat_eq]
  dsimp only [gqsp_asymDefectStartGo]
  exact gqsp_zwAsymDefectLoop_eq B B2 (Nat.mul 2 R_final) neg_rev M1 true pos_tail 0
/-- Zero-cache `.q`-residual sum directly over `pqM` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwQResidHadamard
    (B B2 R_final : ℕ) (pq0 : List PQPair) (q_prev0 acc0 : ℕ) : ℕ :=
  @List.rec PQPair (fun _ ↦ ℕ → ℕ → ℕ)
    (fun q_prev acc ↦
      let q_last := Nat.shiftRight (Nat.add B (Nat.sub B2 q_prev)) 1
      Nat.add acc (Nat.add (Nat.add (Nat.sub q_last B) (Nat.sub B q_last)) R_final))
    (fun h _ ih q_prev acc ↦ @PQPair.rec (fun _ ↦ ℕ) (fun ph qh ↦
      let q_cur := Nat.shiftRight (Nat.add ph (Nat.sub B2 q_prev)) 1
      let diff := Nat.add (Nat.sub q_cur B) (Nat.sub B q_cur)
      @Nat.rec (fun _ ↦ ℕ) 0 (fun acc' _ ↦ ih qh acc')
        (Nat.add 1 (Nat.add acc (Nat.add diff R_final)))) h) pq0 q_prev0 acc0
theorem gqsp_zwQResidHadamard_eq (B B2 R_final : ℕ) :
    ∀ (pq : List PQPair) (q_prev acc : ℕ),
      gqsp_zwQResidHadamard B B2 R_final pq q_prev acc =
        gqsp_qResidHadamardFast B B2 R_final pq q_prev acc
  | [], q_prev, acc => by
      dsimp only [gqsp_zwQResidHadamard, gqsp_qResidHadamardFast]
      rw [gqsp_zwAbsDiff_eq]
  | ⟨ph, qh⟩ :: t, q_prev, acc => by
      dsimp only [gqsp_zwQResidHadamard]
      rw [gqsp_zwForce_eq, gqsp_zwAbsDiff_eq, gqsp_qResidHadamardFast_cons]
      exact gqsp_zwQResidHadamard_eq B B2 R_final t qh _
/-- CPS wrapper sharing the forced 1-angle root unpack + outer Hadamard + split setup across
full and split (`T1` / `T23`) low-memory post-root checks (`14` outer calls total, `0` `O(M)`
cache). -/
noncomputable def gqsp_withRootSplit1AngleLowMem
    (d M : ℕ) (g0 : DyadicSu2Gate) (root : TreeNodeC)
    (cont : List PQPair → List ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : Bool :=
  @TreeNodeC.casesOn (fun _ => Bool) root
    (fun rdeg rsalt rrep1 rprp rprn _ _ rqrp rqrn _ _ rerr =>
      ta_tfBool (fun n_lanes =>
        ta_tfBool (fun rep_bcomb =>
          let c_ar := smToPolyPN g0.sar g0.mar
          let c_br := smToPolyPN g0.sbr g0.mbr
          let nc_br := negPolyPN c_br
          ta_tfBool (fun rqrp_rev =>
            ta_tfBool (fun rqrn_rev =>
              gqsp_forceListBool
                (gqsp_finishRootVec2RealFast gqsp_zwSunpackShr256Chunked 0x410001
                  d n_lanes rep_bcomb c_ar ⟨rprp, rprn⟩ nc_br ⟨rqrp_rev, rqrn_rev⟩)
                (fun uPre =>
                  gqsp_forceListBool (gqsp_zwRevNatTR uPre []) (fun ruP =>
                    ta_tfBool (fun rprp_rev =>
                      ta_tfBool (fun rprn_rev =>
                        gqsp_forceListBool
                          (gqsp_finishRootVec2RealFast gqsp_zwSunpackShr256Chunked 0x420001
                            d n_lanes rep_bcomb c_ar ⟨rqrp, rqrn⟩ c_br ⟨rprp_rev, rprn_rev⟩)
                          (fun uQre =>
                            gqsp_forceListBool (gqsp_zwRevNatTR uQre []) (fun ruQ =>
                              let pqM := gqsp_zwRevPQTR
                                (gqsp_zwInterleave1AngleRevTR ta_B2 ta_BIAS_OUT uPre uQre ruP ruQ
                                  []) []
                              ta_tfBool (fun R_final => ta_tfBool (fun M1 =>
                                ta_tfBool (fun B => ta_tfBool (fun B2 =>
                                  ta_tfBool (fun Bw => ta_tfBool (fun shift0 =>
                                    let p_fin := gqsp_zwRevNatTR
                                      (gqsp_zwHadamardRevPOnly B pqM B []) []
                                    @Prod.casesOn _ _ (fun _ => Bool)
                                      (gqsp_zwSplitPRev B M1 p_fin []) fun neg_re p2_re =>
                                      @Prod.casesOn _ _ (fun _ => Bool) p2_re fun pc_re pos_re =>
                                        cont pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0)
                                    ta_shift0) ta_Bw) ta_B2) ta_B) (Nat.add M 1))
                                (Nat.add (Nat.add (Nat.shiftRight rerr 206) 2) 1))))
                      (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rprn))
                    (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rprp))))
            (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rqrn))
          (gqsp_fastRevSwarSalt 8 rsalt d n_lanes rqrp))
        (Nat.mul rrep1 ta_B_COMB)) (Nat.add 1 rdeg))
/-- Zero-cache 1-angle post-root verifier unconditionally equal to
  `gqsp_oneAnglePostRootRealFastBle`. -/
noncomputable def gqsp_oneAnglePostRootRealLowMemBle (d M N_rec W_err_d0 W_err_dpos pad : ℕ)
    (g0 : DyadicSu2Gate) (root : TreeNodeC) (ws_unpad : List ℕ) : Bool :=
  gqsp_withRootSplit1AngleLowMem d M g0 root
    (fun pqM neg_re pc_re pos_re R_final M1 B B2 Bw shift0 =>
      let t1 := gqsp_zwChebL1POnly M1 B B2 Bw R_final W_err_d0 W_err_dpos pad
        neg_re pc_re pos_re ws_unpad
      let t2 := gqsp_zwAsymDefectPOnly M1 B B2 R_final neg_re pos_re
      let t3 := gqsp_zwQResidHadamard B B2 R_final pqM B 0
      Nat.ble (Nat.add (Nat.add t1 t2) t3) (Nat.mul N_rec shift0))
theorem gqsp_zwSunpackShr256Chunked_fun_eq :
    gqsp_zwSunpackShr256Chunked = gqsp_sunpackShr256Chunked :=
  funext fun d ↦ funext fun n ↦ funext (gqsp_zwSunpackShr256Chunked_eq d n)
private theorem ta_tfBool_congr {f1 f2 : ℕ → Bool} {x1 x2 : ℕ} (hx : x1 = x2)
    (hf : ∀ v, f1 v = f2 v) : ta_tfBool f1 x1 = ta_tfBool f2 x2 :=
  hx ▸ congrArg (ta_tfBool · x1) (funext hf)
private theorem forceListBool_congr {xs1 xs2 : List ℕ} {f1 f2 : List ℕ → Bool}
    (hxs : xs1 = xs2) (hf : ∀ ys, f1 ys = f2 ys) :
    gqsp_forceListBool xs1 f1 = gqsp_forceListBool xs2 f2 :=
  hxs ▸ congrArg (gqsp_forceListBool xs1) (funext hf)
theorem gqsp_oneAnglePostRootRealLowMemBle_eq (d M N_rec W_err_d0 W_err_dpos pad : ℕ)
    (g0 : DyadicSu2Gate) (root : TreeNodeC) (ws_unpad : List ℕ) :
    gqsp_oneAnglePostRootRealLowMemBle d M N_rec W_err_d0 W_err_dpos pad g0 root ws_unpad =
    gqsp_oneAnglePostRootRealFastBle d M N_rec W_err_d0 W_err_dpos pad g0 root ws_unpad := by
  rcases root with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
  unfold gqsp_oneAnglePostRootRealLowMemBle gqsp_withRootSplit1AngleLowMem
    gqsp_oneAnglePostRootRealFastBle
  dsimp only
  refine ta_tfBool_congr rfl fun n_lanes ↦ ta_tfBool_congr rfl fun rep_bcomb ↦
    ta_tfBool_congr rfl fun rqrp_rev ↦ ta_tfBool_congr rfl fun rqrn_rev ↦
    forceListBool_congr (by rw [gqsp_zwSunpackShr256Chunked_fun_eq]) fun uPre ↦
    forceListBool_congr (by rw [gqsp_zwRevNatTR_eq, gqsp_srevNatTR_eq]) fun ruP ↦
    ta_tfBool_congr rfl fun rprp_rev ↦ ta_tfBool_congr rfl fun rprn_rev ↦
    forceListBool_congr (by rw [gqsp_zwSunpackShr256Chunked_fun_eq]) fun uQre ↦
    forceListBool_congr (by rw [gqsp_zwRevNatTR_eq, gqsp_srevNatTR_eq]) fun ruQ ↦
    ta_tfBool_congr rfl fun R_final ↦ ta_tfBool_congr rfl fun M1 ↦
    ta_tfBool_congr rfl fun B ↦ ta_tfBool_congr rfl fun B2 ↦
    ta_tfBool_congr rfl fun Bw ↦ ta_tfBool_congr rfl fun shift0 ↦ ?_
  rw [show gqsp_zwRevPQTR
      (gqsp_zwInterleave1AngleRevTR ta_B2 ta_BIAS_OUT uPre uQre ruP ruQ []) [] =
      gqsp_srevPQTR (gqsp_interleave1AngleRevTR ta_B2 ta_BIAS_OUT 1 uPre uQre ruP ruQ [])
        1 [] by
    rw [gqsp_zwRevPQTR_eq, gqsp_srevPQTR_eq,
      gqsp_zwInterleave1AngleRevTR_eq ta_B2 ta_BIAS_OUT uPre 1]]
  generalize gqsp_srevPQTR
    (gqsp_interleave1AngleRevTR ta_B2 ta_BIAS_OUT 1 uPre uQre ruP ruQ []) 1 [] = pqM
  rw [show gqsp_zwRevNatTR (gqsp_zwHadamardRevPOnly B pqM B []) [] =
      gqsp_srevNatTR (ta_hadamardRevPOnlyFast B pqM 1 B []) 1 [] by
    rw [gqsp_zwRevNatTR_eq, gqsp_srevNatTR_eq, gqsp_zwHadamardRevPOnly_eq B pqM 1 B []],
    gqsp_zwSplitPRev_eq]
  rcases gqsp_ssplitPRevFast B M1
    (gqsp_srevNatTR (ta_hadamardRevPOnlyFast B pqM 1 B []) 1 []) [] with ⟨neg_re, pc_re, pos_re⟩
  dsimp only
  rw [gqsp_zwChebL1POnly_eq, gqsp_zwAsymDefectPOnly_eq, gqsp_zwQResidHadamard_eq]
/-- Zero-cache reversal of `List BiGqspUnpackSeg226` (`0` `DefinitionVal`s). -/
noncomputable def gqsp_zwRevSegs226 (xs0 acc0 : List BiGqspUnpackSeg226) : List
    BiGqspUnpackSeg226 := @List.rec BiGqspUnpackSeg226
    (fun _ ↦ List BiGqspUnpackSeg226 → List BiGqspUnpackSeg226) (fun acc ↦ acc)
    (fun x _ ih acc ↦ ih (x :: acc)) xs0 acc0
/-- Zero-cache pairwise merge pass on `List BiGqspUnpackSeg226` (`0` `DefinitionVal`s in loop). -/
noncomputable def gqsp_zwPairUnpackSegs226
    (xs0 : List BiGqspUnpackSeg226) : List BiGqspUnpackSeg226 :=
  gqsp_zwRevSegs226 (@List.rec BiGqspUnpackSeg226
    (fun _ ↦ Option BiGqspUnpackSeg226 → List BiGqspUnpackSeg226 → List BiGqspUnpackSeg226)
    (fun pend racc ↦ @Option.rec BiGqspUnpackSeg226 (fun _ ↦ List BiGqspUnpackSeg226)
      racc (fun a ↦ a :: racc) pend)
    (fun b _ ih pend racc ↦ @Option.rec BiGqspUnpackSeg226 (fun _ ↦ List BiGqspUnpackSeg226)
      (ih (some b) racc) (fun a ↦
        let m := @BiGqspUnpackSeg226.rec (fun _ ↦ BiGqspUnpackSeg226) (fun al ap an ↦
          @BiGqspUnpackSeg226.rec (fun _ ↦ BiGqspUnpackSeg226) (fun bl bp bn ↦
            let sh := Nat.mul 768 al
            let len0 := Nat.add al bl
            let pos0 := Nat.add ap (Nat.shiftLeft bp sh)
            let neg0 := Nat.add an (Nat.shiftLeft bn sh)
            @Nat.rec (fun _ ↦ BiGqspUnpackSeg226) (BiGqspUnpackSeg226.mk 0 0 0) (fun len' _ ↦
              @Nat.rec (fun _ ↦ BiGqspUnpackSeg226) (BiGqspUnpackSeg226.mk 0 0 0) (fun pos' _ ↦
                @Nat.rec (fun _ ↦ BiGqspUnpackSeg226) (BiGqspUnpackSeg226.mk 0 0 0) (fun neg' _ ↦
                  BiGqspUnpackSeg226.mk len' pos' neg') (Nat.add 1 neg0))
              (Nat.add 1 pos0)) (Nat.add 1 len0)) b) a
        ih none (m :: racc)) pend) xs0 none []) []
/-- Zero-cache binary-tournament unpacker reducing `List BiGqspUnpackSeg226` to `PolyPN`. -/
noncomputable def gqsp_zwTournamentUnpack226 (fuel : ℕ) (xs0 : List BiGqspUnpackSeg226) :
    PolyPN := @Nat.rec (fun _ ↦ List BiGqspUnpackSeg226 → PolyPN) (fun _ ↦ ⟨0, 0⟩) (fun _ ih xs
    ↦ @List.rec BiGqspUnpackSeg226 (fun _ ↦ PolyPN) ⟨0, 0⟩ (fun x xt _ ↦ @List.rec
    BiGqspUnpackSeg226 (fun _ ↦ PolyPN) (@BiGqspUnpackSeg226.rec (fun _ ↦ PolyPN) (fun _ p n ↦
    ⟨p, n⟩) x) (fun _ _ _ ↦ ih (gqsp_zwPairUnpackSegs226 xs)) xt) xs) fuel xs0
/-- Zero-list-closure-cache packed single-accumulator tier verifier. -/
noncomputable def gqsp_zwCodeTierTzFast (tz_mask n_exp d_exp rot_exp : ℕ) (cr0 : List ℕ) : ℕ
    → List ℕ → Bool := @List.rec ℕ (fun _ ↦ ℕ → List ℕ → Bool) (fun acc co ↦ @List.rec ℕ (fun
    _ ↦ Bool) (Bool.and (Nat.beq (Nat.land acc 0xffffffffffffffff) n_exp) (Bool.and (Nat.beq
    (Nat.land (Nat.shiftRight acc 64) 0xffffffffffffffff) d_exp) (Nat.beq (Nat.shiftRight acc
    128) rot_exp))) (fun _ _ _ ↦ false) co) (fun cr _ ih acc co ↦ @List.rec ℕ (fun _ ↦ Bool)
    false (fun coh cot _ ↦ @Bool.rec (fun _ ↦ Bool) false (@Nat.rec (fun _ ↦ Bool) false (fun
    acc' _ ↦ ih acc' cot) (Nat.add 1 (Nat.add acc (Nat.add 1 (Nat.add (Nat.shiftLeft
    (gqsp_natDistFast cr coh) 64) (Nat.shiftLeft (gqsp_gidneyRotFast cr) 128)))))) (Bool.and
    (Bool.and (Bool.and (Nat.blt cr 4398046511104) (Nat.blt coh 4398046511104)) (Nat.beq
    (Nat.land cr tz_mask) 0)) (Nat.blt (Nat.land acc 0xffffffffffffffff) 0x100000))) co) cr0
theorem gqsp_zwCodeTierTzFast_go (tz_mask n_exp d_exp rot_exp : ℕ) :
    ∀ (cr co : List ℕ) (cnt dist rot : ℕ), cnt ≤ 0x100000 → dist ≤ cnt * 4398046511104 →
      gqsp_zwCodeTierTzFast tz_mask n_exp d_exp rot_exp cr
        (gqsp_packTriple cnt dist rot) co = true →
      gqsp_codeTierTzLoop tz_mask n_exp d_exp rot_exp cr co cnt dist rot = true
  | [], [], cnt, dist, rot, hcnt, hdist, h => by
      rcases gqsp_packTriple_limbs cnt dist rot (Nat.lt_of_le_of_lt hcnt (by decide))
        (Nat.lt_of_le_of_lt (Nat.le_trans hdist (Nat.mul_le_mul_right _ hcnt)) (by decide)) with
        ⟨e0, e1, e2⟩
      dsimp only [gqsp_zwCodeTierTzFast, gqsp_codeTierTzLoop] at h ⊢
      rwa [e0, e1, e2] at h
  | [], _ :: _, _, _, _, _, _, h => Bool.noConfusion h
  | _ :: _, [], _, _, _, _, _, h => Bool.noConfusion h
  | cr :: crt, coh :: cot, cnt, dist, rot, hcnt, hdist, h => by
      have hcnt_limb : Nat.land (gqsp_packTriple cnt dist rot) 0xffffffffffffffff = cnt :=
        (gqsp_packTriple_limbs cnt dist rot (Nat.lt_of_le_of_lt hcnt (by decide))
          (Nat.lt_of_le_of_lt (Nat.le_trans hdist (Nat.mul_le_mul_right _ hcnt)) (by decide))).1
      dsimp only [gqsp_zwCodeTierTzFast] at h
      rw [hcnt_limb] at h
      unfold gqsp_codeTierTzLoop
      revert h
      cases hg1 : Bool.and (Bool.and (Nat.blt cr 4398046511104) (Nat.blt coh 4398046511104))
        (Nat.beq (Nat.land cr tz_mask) 0)
      · exact Bool.noConfusion
      · cases hg2 : Nat.blt cnt 0x100000
        · exact Bool.noConfusion
        · intro h
          dsimp only [Bool.true_and] at h ⊢
          rw [gqsp_zwForce_eq, gqsp_packTriple_step] at h
          have hcnt_lt : cnt < 0x100000 := Nat.blt_eq.mp hg2
          have hd_le : gqsp_natDistFast cr coh ≤ 4398046511104 := by
            simp only [Bool.and_eq_true, Nat.blt_eq] at hg1
            unfold gqsp_natDistFast
            simp only [Nat.add_eq, Nat.sub_eq]
            omega
          rw [gqsp_applyNat0Bool_eq, gqsp_applyNat1Bool_eq, gqsp_applyNat2Bool_eq]
          exact gqsp_zwCodeTierTzFast_go tz_mask n_exp d_exp rot_exp crt cot
            (Nat.add 1 cnt) (Nat.add dist (gqsp_natDistFast cr coh))
            (Nat.add rot (gqsp_gidneyRotFast cr))
            (by simp only [Nat.add_eq]; omega) (by simp only [Nat.add_eq]; omega) h
end ZeroCacheKernelPrimitives
end GqspWronskian62592
end
end Gqsp0d_PostRootLowMem

end QuantumComputation.Specs.StoppingPowerSolution
end
