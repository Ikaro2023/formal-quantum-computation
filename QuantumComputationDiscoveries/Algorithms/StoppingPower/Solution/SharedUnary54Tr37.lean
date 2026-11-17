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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot2StreamInit42

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSharedUnary54Trunc37
@[expose] public section
namespace SharedUnary54Trunc37
section ConfigSharedUnary54Trunc37
set_option maxRecDepth 32768
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm
open NuclearTwistAndXor654Concrete (dXor32All654)
open NuclearTwistRealizes
  (embedUnitary_idReg_eq)
open InterWalkRSum42Hoist
local instance (priority := 1000000) instNeZeroTwoPowSharedUnary54 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
section RevTempPermLoadFromHdr
open RevTempPerm
theorem selectSwapXorBit_eval_any {M : ℕ} (uBase L : ℕ) (hM : uBase + L + 2 = M)
    (lsb target : Wire M) (hlsb : lsb.val < uBase) (ht : target.val < uBase)
    (hlt : lsb ≠ target) (table : Fin (2 * L) → ℕ) (j : ℕ) :
    let hM' : uBase + L + 2 ≤ M := by omega
    let p := selectSwapXorBit uBase L hM' lsb target hlsb ht table j
    RevTempPerm.ValidCleanRem M 2 p ∧
    ∀ (β : BitAssignment M), CleanRem M 2 β →
      p.evalBits β = Function.update β target
        (β target +
          (∑ k : Fin L,
            if (table ⟨2 * k.val, by omega⟩).testBit j then β ⟨uBase + k.val, by omega⟩ else 0) +
          β lsb * (∑ k : Fin L,
            if xor ((table ⟨2 * k.val, by omega⟩).testBit j)
                ((table ⟨2 * k.val + 1, by omega⟩).testBit j)
            then β ⟨uBase + k.val, by omega⟩ else 0)) := by
  subst hM
  intro hM' p
  obtain ⟨hvAll, hPresNe⟩ := selectSwapXorBit_pres_ne uBase L rfl lsb target hlsb ht hlt table j
  refine ⟨hvAll, fun β hβ ↦ ?_⟩
  let scrD : Wire (uBase + L + 2) := ⟨uBase + L, by omega⟩
  let ancOut : Wire (uBase + L + 2) := ⟨uBase + L + 1, by omega⟩
  let predD : ℕ → Bool := fun a ↦
    if ha : a < L then
      xor ((table ⟨2 * a, by omega⟩).testBit j) ((table ⟨2 * a + 1, by omega⟩).testBit j)
    else false
  let predB0 : ℕ → Bool := fun a ↦
    if ha : a < L then (table ⟨2 * a, by omega⟩).testBit j else false
  let cFanD := fanoutUnaryToTarget uBase L scrD (Or.inr (by dsimp [scrD]; omega))
    (by omega) predD L le_rfl
  let cFanB0 := fanoutUnaryToTarget uBase L target (Or.inl ht) (by omega) predB0 L le_rfl
  have hsuppD : cFanD.SupportsRange uBase (uBase + L + 1) :=
    fanoutUnaryToTarget_supportsRange uBase L (uBase + L + 1) scrD
      (Or.inr (by dsimp [scrD]; omega)) (by omega) (by dsimp [scrD]; omega)
      (by dsimp [scrD]; omega) (by omega) predD L le_rfl
  have hAnd := andXor_spec (M := uBase + L + 2) (rem := 1) lsb scrD target ancOut
    (wire_ne_of_lt (by dsimp [scrD]; omega)) hlt (wire_ne_of_gt (by dsimp [scrD]; omega))
    (by dsimp [ancOut]; omega) (by dsimp [scrD, ancOut]; omega) (by dsimp [ancOut]; omega)
    (by dsimp [ancOut]; omega)
  have hscr0 : β scrD = 0 := hβ scrD (by dsimp [scrD]; omega)
  let sumD : ZMod 2 := ∑ k : Fin L, if predD k.val then β ⟨uBase + k.val, by omega⟩ else 0
  let sumB0 : ZMod 2 := ∑ k : Fin L, if predB0 k.val then β ⟨uBase + k.val, by omega⟩ else 0
  let β₁ := cFanD.eval β
  have hβ₁_eq : β₁ = Function.update β scrD sumD := by
    dsimp [β₁, cFanD, sumD]
    rw [fanoutUnaryToTarget_eval, hscr0, zero_add]
  have hβ₁_clean1 : CleanRem (uBase + L + 2) 1 β₁ := fun w hw ↦ by
    rw [hβ₁_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp [scrD]; omega))]
    exact hβ w (by omega)
  let β₂ := (RevTempPerm.andXor lsb scrD target ancOut
    (wire_ne_of_lt (by dsimp [scrD]; omega))
    (wire_ne_of_lt (by dsimp [ancOut]; omega))
    (wire_ne_of_lt (by dsimp [scrD, ancOut]; omega))
    (wire_ne_of_gt (by dsimp [ancOut]; omega))).evalBits β₁
  have hβ₂_eq : β₂ = Function.update β₁ target (β target + β lsb * sumD) := by
    dsimp only [β₂]
    rw [hAnd.2 β₁ hβ₁_clean1, hβ₁_eq,
      Function.update_of_ne (wire_ne_of_lt (by dsimp [scrD]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [scrD]; omega)),
      Function.update_self]
  let β₃ := cFanB0.eval β₂
  have hβ₃_eq : β₃ = Function.update β₁ target (β target + sumB0 + β lsb * sumD) := by
    have hu_same : ∀ k : Fin L, β₂ ⟨uBase + k.val, by omega⟩ = β ⟨uBase + k.val, by omega⟩ :=
      fun k ↦ by
        rw [hβ₂_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp; omega)), hβ₁_eq,
          Function.update_of_ne (wire_ne_of_lt (by dsimp [scrD]; omega))]
    have hsum_congr :
        (∑ k : Fin L, if predB0 k.val then β₂ ⟨uBase + k.val, by omega⟩ else 0) = sumB0 :=
      Finset.sum_congr rfl fun k _ ↦ by rw [hu_same k]
    dsimp [β₃, cFanB0]
    rw [fanoutUnaryToTarget_eval, hsum_congr, hβ₂_eq, Function.update_idem, Function.update_self]
    congr 1; ring
  have hsumB0_eq : sumB0 =
      ∑ k : Fin L,
        if (table ⟨2 * k.val, by omega⟩).testBit j then β ⟨uBase + k.val, by omega⟩ else 0 :=
    Finset.sum_congr rfl fun k _ ↦ by simp [predB0, k.isLt]
  have hsumD_eq : sumD =
      ∑ k : Fin L,
        if xor ((table ⟨2 * k.val, by omega⟩).testBit j)
            ((table ⟨2 * k.val + 1, by omega⟩).testBit j)
        then β ⟨uBase + k.val, by omega⟩ else 0 :=
    Finset.sum_congr rfl fun k _ ↦ by simp [predD, k.isLt]
  funext w
  by_cases hwt : w = target
  · subst w
    have hinv_t : cFanD.inv.eval β₃ target = β₃ target :=
      cFanD.inv.eval_outside (cFanD.inv_supportsRange hsuppD) β₃ target (Or.inl ht)
    change cFanD.inv.eval β₃ target = _
    rw [hinv_t, hβ₃_eq, Function.update_self, Function.update_self, hsumB0_eq, hsumD_eq]
  · rw [hPresNe β hβ w hwt, Function.update_of_ne hwt]
attribute [local irreducible] selectSwapXorBit
theorem selectSwapXorBitLoop_eval_any {M : ℕ} (uBase L W : ℕ) (hW_le : W ≤ uBase)
    (hM : uBase + L + 2 = M) (hM' : uBase + L + 2 ≤ M)
    (lsb : Wire M) (hlsb_lo : W ≤ lsb.val) (hlsb_hi : lsb.val < uBase)
    (table : Fin (2 * L) → ℕ) :
    ∀ (remW : ℕ) (hW : remW ≤ W),
      let p := selectSwapXorBitLoop uBase L W hW_le hM' lsb hlsb_lo hlsb_hi table remW hW
      RevTempPerm.ValidCleanRem M 2 p ∧
      ∀ (β : BitAssignment M), CleanRem M 2 β →
        (∀ w : Wire M, W ≤ w.val → p.evalBits β w = β w) ∧
        (∀ w : Wire M, w.val < W - remW → p.evalBits β w = β w) ∧
        (∀ w : Wire M, W - remW ≤ w.val → w.val < W →
          p.evalBits β w = β w +
            (∑ k : Fin L,
              if (table ⟨2 * k.val, by omega⟩).testBit w.val then
                β ⟨uBase + k.val, by omega⟩
              else 0) +
            β lsb * (∑ k : Fin L,
              if xor ((table ⟨2 * k.val, by omega⟩).testBit w.val)
                  ((table ⟨2 * k.val + 1, by omega⟩).testBit w.val)
              then β ⟨uBase + k.val, by omega⟩ else 0)) := by
  subst hM
  intro remW
  induction remW with
  | zero =>
      intro _
      exact ⟨trivial, fun _ _ ↦ ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl,
        fun _ hlo hhi ↦ absurd (lt_of_le_of_lt hlo hhi) (by omega)⟩⟩
  | succ remW ih =>
      intro hW
      let j := W - (remW + 1)
      have hj_lt : j < uBase + L + 2 := by dsimp [j]; omega
      have hStep := selectSwapXorBit_eval_any uBase L rfl lsb ⟨j, hj_lt⟩ hlsb_hi
        (by dsimp [j]; omega) (wire_ne_of_gt (by dsimp [j]; omega)) table j
      obtain ⟨hvHigh, _⟩ := selectSwapXorBitLoop_high uBase L W hW_le rfl lsb hlsb_lo hlsb_hi
        table (remW + 1) hW
      obtain ⟨_, hSpecRec⟩ := ih (by omega)
      refine ⟨hvHigh, fun β hβ ↦ ?_⟩
      let β' := (selectSwapXorBit uBase L hM' lsb ⟨j, hj_lt⟩ hlsb_hi (by dsimp [j]; omega)
        table j).evalBits β
      have hβ'_eq : β' = _ := hStep.2 β hβ
      have hβ'_cl : CleanRem (uBase + L + 2) 2 β' := fun w hw ↦ by
        rw [hβ'_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp [j]; omega))]
        exact hβ w hw
      have hβ'_un : ∀ k : Fin L, β' ⟨uBase + k.val, by omega⟩ = β ⟨uBase + k.val, by omega⟩ :=
        fun k ↦ by rw [hβ'_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp [j]; omega))]
      have hβ'_lsb : β' lsb = β lsb := by
        rw [hβ'_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp [j]; omega))]
      obtain ⟨hge, hlt, hmid⟩ := hSpecRec β' hβ'_cl
      refine ⟨fun w hw ↦ (hge w hw).trans (by
          rw [hβ'_eq, Function.update_of_ne (wire_ne_of_gt (by dsimp [j]; omega))]),
        fun w hw ↦ (hlt w (by omega)).trans (by
          rw [hβ'_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [j]; omega))]),
        fun w hwlo hwhi ↦ ?_⟩
      dsimp only [selectSwapXorBitLoop, RevTempProg.evalBits]
      by_cases hwj : w.val = j
      · have hweq : w = ⟨j, hj_lt⟩ := Fin.ext hwj
        rw [hweq, hlt ⟨j, hj_lt⟩ (by dsimp [j]; omega), hβ'_eq, Function.update_self]
      · have hwgt : W - remW ≤ w.val := by dsimp [j] at hwlo hwj; omega
        have hsum (p : Fin L → Bool) :
            (∑ k : Fin L, if p k then β' ⟨uBase + k.val, by omega⟩ else 0) =
              ∑ k : Fin L, if p k then β ⟨uBase + k.val, by omega⟩ else 0 :=
          Finset.sum_congr rfl fun k _ ↦ by rw [hβ'_un k]
        rw [hmid w hwgt hwhi, hsum (fun k ↦ (table ⟨2 * k.val, by omega⟩).testBit w.val),
          hsum (fun k ↦ xor ((table ⟨2 * k.val, by omega⟩).testBit w.val)
            ((table ⟨2 * k.val + 1, by omega⟩).testBit w.val)),
          hβ'_lsb, hβ'_eq,
          Function.update_of_ne (fun h : w = ⟨j, hj_lt⟩ ↦ hwj (congrArg Fin.val h))]
end RevTempPermLoadFromHdr
section TempPhaseProgXUncomputeFromHdr
theorem embedUnitary_diagSignUnitary_eq {kSub kAmb : ℕ} (rSub : QRegister kSub kAmb)
    (phaseSub : Fin (2 ^ kSub) → Bool) : rSub.embedUnitary (diagSignUnitary phaseSub) =
    diagSignUnitary (fun x : Fin (2 ^ kAmb) ↦ phaseSub (rSub.extractIndex x)) := by
  apply Subtype.ext
  ext i g
  have h1 := congrFun (embedUnitary_diagSignUnitary_mulVec_single rSub phaseSub g) i
  have h2 := congrFun (embedUnitary_diagSignUnitary_mulVec_single (QRegExt.idReg kAmb)
    (fun x : Fin (2 ^ kAmb) ↦ phaseSub (rSub.extractIndex x)) g) i
  rw [embedUnitary_idReg_eq] at h2
  have hexId : (QRegExt.idReg kAmb).extractIndex g = g := by
    apply (basisBitsEquiv kAmb).injective
    funext q
    change basisBits kAmb ((QRegExt.idReg kAmb).extractIndex g) q = basisBits kAmb g q
    rw [QRegister.basisBits_extractIndex, QRegExt.idReg_apply]
  rw [hexId] at h2
  rw [Matrix.mulVec_single_one] at h1 h2
  exact h1.trans h2.symm
end TempPhaseProgXUncomputeFromHdr
theorem bitsVal8_decomp (bits : BitAssignment 8) :
    bitsVal bits =
      4 * bitsVal (fun j : Fin 6 ↦ bits ⟨2 + j.val, by omega⟩) +
        2 * (bits ⟨1, by decide⟩).val + (bits ⟨0, by decide⟩).val := by
  rw [RevTempPerm.bitsVal_cons_eq bits,
    RevTempPerm.bitsVal_cons_eq (fun j : Fin 7 ↦ bits j.succ)]
  have h0 : bits 0 = bits ⟨0, by decide⟩ := rfl
  have h1 : bits (Fin.succ 0) = bits ⟨1, by decide⟩ := rfl
  have htl : (fun j : Fin 6 ↦ bits j.succ.succ) =
      (fun j : Fin 6 ↦ bits ⟨2 + j.val, by omega⟩) :=
    funext fun j ↦ congrArg bits (Fin.ext (by dsimp; omega))
  rw [h0, h1, htl]
  ring
section ReorderedHoistedTwist37
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
open HoistInitStream1300And164 (IsSlot2StreamUnitary)
attribute [local irreducible]
  dXor32All654
theorem isSlot2StreamUnitary_base : IsSlot2StreamUnitary uHybridStream220 :=
  fun w β₀ hz ↦
    uHybridStream220_compute_ket w rCoreFull (rSum14Full w) (hCoreFull_disj_Sum14 w) β₀ hz
end ReorderedHoistedTwist37
end ConfigSharedUnary54Trunc37
end SharedUnary54Trunc37
end
end ModSharedUnary54Trunc37

end QuantumComputation.Specs.StoppingPowerSolution
