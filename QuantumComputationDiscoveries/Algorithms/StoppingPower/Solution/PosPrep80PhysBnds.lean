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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80VepCert

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPosPostPrep80L1Bounds
@[expose] public section
namespace PosPostPrep80L1Bounds
section Opts
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 262144
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowPosPostL1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open ZeroAncillaUSP PosPostPrep80MergedVep
theorem pos80IdealDist_eq_physics : PosPostPrep80MergedVep.pos80IdealDist =
    PosSlots24Semantic80Physics.pos80IdealDist := rfl
theorem ite_pos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) {a b : α} :
    (if P then a else b) = a := by simp [hp]
theorem ite_neg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) {a b : α} :
    (if P then a else b) = b := by simp [hp]
theorem zmod2_add_self_cancel (a b : ZMod 2) : a + b + b = a := by
  revert a b; decide
theorem zmod2_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide
theorem z2BitOfNat_val (x i : ℕ) : (z2BitOfNat x i).val = (x / 2 ^ i) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [z2BitOfNat, h]
theorem bitsVal_z2BitOfNat (m x : ℕ) (hx : x < 2 ^ m) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ z2BitOfNat x j.val) = x := by
  induction m generalizing x with
  | zero => exact (Nat.lt_one_iff.mp hx).symm
  | succ m ih =>
    have hstep : ∀ i : Fin m, (z2BitOfNat x i.succ.val).val * 2 ^ i.succ.val =
        2 * ((z2BitOfNat (x / 2) i.val).val * 2 ^ i.val) := fun i ↦ by
      rw [z2BitOfNat_val, z2BitOfNat_val, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
      ring
    have hx2 : x / 2 < 2 ^ m := by
      rw [pow_succ'] at hx
      omega
    rw [Pos24HeadCoordXor80.bitsVal, Fin.sum_univ_succ]
    simp_rw [hstep, ← Finset.mul_sum]
    change (z2BitOfNat x 0).val * 2 ^ (0 : ℕ) +
      2 * Pos24HeadCoordXor80.bitsVal (fun i : Fin m ↦ z2BitOfNat (x / 2) i.val) = x
    rw [z2BitOfNat_val, ih (x / 2) hx2]
    omega
theorem z2BitOfNat_bitsVal {m : ℕ} (γ : BitAssignment m) (i : Fin m) :
    z2BitOfNat (Pos24HeadCoordXor80.bitsVal γ) i.val = γ i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    have hSplit : Pos24HeadCoordXor80.bitsVal γ =
        (γ 0).val + 2 * Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ γ j.succ) := by
      have hs : ∀ j : Fin m, (γ j.succ).val * 2 ^ j.succ.val =
          2 * ((γ j.succ).val * 2 ^ j.val) := fun j ↦ by
        rw [Fin.val_succ, pow_succ']
        ring
      rw [Pos24HeadCoordXor80.bitsVal, Fin.sum_univ_succ,
        show (γ 0).val * 2 ^ (0 : Fin (m + 1)).val = (γ 0).val by simp]
      simp_rw [hs, ← Finset.mul_sum]
    have _hb0 : (γ 0).val < 2 := ZMod.val_lt (γ 0)
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [hSplit]
      rcases zmod2_zero_or_one (γ 0) with h | h <;> simp [z2BitOfNat, h]
    · have hdiv : ((γ 0).val + 2 * Pos24HeadCoordXor80.bitsVal (fun k : Fin m ↦ γ k.succ)) /
          2 ^ j.succ.val =
          Pos24HeadCoordXor80.bitsVal (fun k : Fin m ↦ γ k.succ) / 2 ^ j.val := by
        rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      change z2BitOfNat (Pos24HeadCoordXor80.bitsVal γ) j.succ.val = γ j.succ
      unfold z2BitOfNat
      rw [hSplit, hdiv]
      exact ih (fun k : Fin m ↦ γ k.succ) j
theorem flipTailDpScratch80_preserve (p : BitAssignment 80) (q : Fin 80)
    (hq : q.val ≠ 75 ∧ q.val ≠ 76 ∧ q.val ≠ 77) : flipTailDpScratch80 p q = p q := by
  unfold flipTailDpScratch80
  by_cases h30 : (p 30 == 1) = true
  · simp [h30]
  · simp [h30, beq_false_of_ne hq.1, beq_false_of_ne hq.2.1, beq_false_of_ne hq.2.2]
theorem flipTailDpScratch80_eq_outside_scratch16 (p : BitAssignment 80) (j : Fin 80)
    (hj : ¬(63 ≤ j.val ∧ j.val < 79)) : flipTailDpScratch80 p j = p j :=
  flipTailDpScratch80_preserve p j ⟨by omega, by omega, by omega⟩
theorem flipTailDpScratch80_involutive : Function.Involutive flipTailDpScratch80 := fun p ↦ by
  set fp := flipTailDpScratch80 p with hfp_def
  have hpr : ∀ q : Fin 80, q.val ≠ 75 ∧ q.val ≠ 76 ∧ q.val ≠ 77 → fp q = p q :=
    flipTailDpScratch80_preserve p
  funext q
  unfold flipTailDpScratch80
  rw [hpr 30 (by decide)]
  by_cases h30 : (p 30 == 1) = true
  · simp [h30, hfp_def, flipTailDpScratch80]
  · have hfp : ∀ r : Fin 80, fp r = if r.val == 75 then p 75 + p 0
        else if r.val == 76 then p 76 + p 1 else if r.val == 77 then p 77 + p 2 else p r :=
      fun r ↦ by simp [hfp_def, flipTailDpScratch80, h30]
    simp only [h30, Bool.false_eq_true, ↓reduceIte, hpr 0 (by decide), hpr 1 (by decide),
      hpr 2 (by decide)]
    split_ifs with h75 h76 h77
    · simpa [hfp 75, zmod2_add_self_cancel] using congrArg p (Fin.ext (beq_iff_eq.mp h75)).symm
    · simpa [hfp 76, zmod2_add_self_cancel] using congrArg p (Fin.ext (beq_iff_eq.mp h76)).symm
    · simpa [hfp 77, zmod2_add_self_cancel] using congrArg p (Fin.ext (beq_iff_eq.mp h77)).symm
    · simp [hfp q, h75, h76, h77]
theorem coherentSysOp80_muSlot2Ideal216_eq
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : SpecsAux.SpecMirror.Configuration) :
    PosSlots24SemanticOracleConcrete80.coherentSysOp80 qft cfg false
      PosPostPrep80MergedVep.muSlot2Ideal216 =
    PosSlots24SemanticOracleConcrete80.coherentSysOp80 qft cfg false
      (PosSlots24Semantic80Physics.pos80IdealDist false) := by
  unfold PosSlots24SemanticOracleConcrete80.coherentSysOp80
  let e : BitAssignment 80 ≃ BitAssignment 80 := flipTailDpScratch80_involutive.toPerm
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [show e p = flipTailDpScratch80 p from rfl, ← pos80IdealDist_eq_physics,
    PosSlots24Semantic80Physics.blk_eq_of_eq_outside_scratch16 qft cfg false _ p
      (flipTailDpScratch80_eq_outside_scratch16 p), muSlot2Ideal216, flipTailDpScratch80_involutive]
theorem p80NucVal_eq_bitsVal (p : BitAssignment 80) : MergedVepTopCoinCollapse.p80NucVal p =
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j)) := rfl
theorem p80NucVal_flipTailDpScratch80 (p : BitAssignment 80) :
    MergedVepTopCoinCollapse.p80NucVal (flipTailDpScratch80 p) =
      MergedVepTopCoinCollapse.p80NucVal p := by
  rw [p80NucVal_eq_bitsVal, p80NucVal_eq_bitsVal]
  congr 1; funext j
  exact flipTailDpScratch80_preserve p (pos80SubIdx 6 8 (by decide) j)
    ⟨by dsimp [pos80SubIdx]; omega, by dsimp [pos80SubIdx]; omega, by dsimp [pos80SubIdx]; omega⟩
theorem muSlot2Ideal216_eq_zero_of_nuc_ge_216 (p : BitAssignment 80)
    (hge : 216 ≤ MergedVepTopCoinCollapse.p80NucVal p) : muSlot2Ideal216 p = 0 := by
  have hnuc : ¬(Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ flipTailDpScratch80 p (pos80SubIdx 6 8 (by decide) j)) < 216) := by
    rw [← p80NucVal_eq_bitsVal, p80NucVal_flipTailDpScratch80]
    omega
  unfold muSlot2Ideal216 pos80IdealDist
  by_cases h62 : (flipTailDpScratch80 p 62 != 0) = true
  · simp [h62]
  · simp only [h62, Bool.false_eq_true, ↓reduceIte]
    by_cases h30 : (flipTailDpScratch80 p 30 == 1) = true
    · simp only [h30, ↓reduceIte, hnuc, decide_false, Bool.false_eq_true, Bool.and_false,
        Bool.false_and]
      split_ifs <;> rfl
    · simp only [h30, Bool.false_eq_true, ↓reduceIte, hnuc, decide_false, Bool.and_false,
        Bool.false_and]
theorem muSlot2Ideal216_eq_zero_of_b0_ne_zero (p : BitAssignment 80)
    (hb0 : MergedVepTopCoinCollapse.p80CosetP3 p ≠ 0) : muSlot2Ideal216 p = 0 := by
  have hbVal : Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ flipTailDpScratch80 p (pos80SubIdx 3 3 (by decide) j)) ≠ 0 := fun hZero ↦
    hb0 <| funext fun w ↦ by
      have hwEq : flipTailDpScratch80 p (pos80SubIdx 3 3 (by decide) w) = p ⟨3 + w.val, by omega⟩ :=
        flipTailDpScratch80_preserve p (pos80SubIdx 3 3 (by decide) w)
          ((show ∀ u : Fin 3, (pos80SubIdx 3 3 (by decide) u).val ≠ 75 ∧
            (pos80SubIdx 3 3 (by decide) u).val ≠ 76 ∧
            (pos80SubIdx 3 3 (by decide) u).val ≠ 77 by decide) w)
      have hz := z2BitOfNat_bitsVal
        (fun j : Fin 3 ↦ flipTailDpScratch80 p (pos80SubIdx 3 3 (by decide) j)) w
      rw [hZero, hwEq] at hz
      have hv : (p ⟨3 + w.val, by omega⟩).val = 0 := by
        rw [← hz, z2BitOfNat_val]
        simp
      exact Fin.ext hv
  have hbFalse := beq_false_of_ne hbVal
  unfold muSlot2Ideal216 pos80IdealDist
  by_cases h62 : (flipTailDpScratch80 p 62 != 0) = true
  · simp [h62]
  · simp only [h62, Bool.false_eq_true, ↓reduceIte]
    by_cases h30 : (flipTailDpScratch80 p 30 == 1) = true
    · simp only [h30, ↓reduceIte, hbFalse, Bool.false_eq_true, decide_false, Bool.and_false,
        Bool.false_and]
      split_ifs <;> rfl
    · simp only [h30, Bool.false_eq_true, ↓reduceIte, hbFalse, Bool.false_and, Bool.and_false]
theorem flip_setCosetAndNuc_comm (l : Fin 256) (p : BitAssignment 80) :
    flipTailDpScratch80 (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l p) =
      MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l (flipTailDpScratch80 p) := by
  set s := MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l with hs_def
  have hOut : ∀ (r : BitAssignment 80) (j : Fin 80), (j.val < 3 ∨ 14 ≤ j.val) → s r j = r j :=
    fun r j hj ↦ by
      simp [hs_def, MergedVepTopCoinCollapse.p80SetCosetAndNuc,
        show ¬(3 ≤ j.val ∧ j.val < 6) by omega, show ¬(6 ≤ j.val ∧ j.val < 14) by omega]
  funext q
  by_cases hq30 : (p 30 == 1) = true
  · unfold flipTailDpScratch80
    rw [hOut p 30 (by decide)]
    simp [hq30]
  · by_cases hIn : 3 ≤ q.val ∧ q.val < 14
    · rw [flipTailDpScratch80_preserve _ q ⟨by omega, by omega, by omega⟩, hs_def]
      unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
      by_cases h36 : 3 ≤ q.val ∧ q.val < 6
      · simp [h36]
      · simp [h36, show 6 ≤ q.val ∧ q.val < 14 from ⟨by omega, hIn.2⟩]
    · have hOutQ : q.val < 3 ∨ 14 ≤ q.val := by omega
      change flipTailDpScratch80 (s p) q = s (flipTailDpScratch80 p) q
      rw [hOut (flipTailDpScratch80 p) q hOutQ]
      unfold flipTailDpScratch80
      rw [hOut p 30 (by decide)]
      simp only [hq30, Bool.false_eq_true, ↓reduceIte, hOut p q hOutQ, hOut p 75 (by decide),
        hOut p 76 (by decide), hOut p 77 (by decide), hOut p 0 (by decide),
        hOut p 1 (by decide), hOut p 2 (by decide)]
theorem p80ClearCosetAndNucLocal_eq_set0 (p : BitAssignment 80) :
    p80ClearCosetAndNucLocal p = MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 0 p := by
  funext q
  unfold p80ClearCosetAndNucLocal MergedVepTopCoinCollapse.p80SetCosetAndNuc
  by_cases h36 : 3 ≤ q.val ∧ q.val < 6
  · simp [h36, show 3 ≤ q.val ∧ q.val < 14 from ⟨h36.1, by omega⟩]
  · by_cases h614 : 6 ≤ q.val ∧ q.val < 14
    · simp [h614, show 3 ≤ q.val ∧ q.val < 14 from ⟨by omega, h614.2⟩]
    · simp [h36, h614, show ¬(3 ≤ q.val ∧ q.val < 14) by omega]
theorem natModTwoCast_eq_z2BitOfNat (x i : ℕ) :
    (((x / 2 ^ i) % 2 : ℕ) : ZMod 2) = z2BitOfNat x i := by
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [z2BitOfNat, h]
theorem pos80IdealDist_false_setCosetAndNuc_eq (l : Fin 256) (hl : l.val < 216)
    (q : BitAssignment 80) :
    pos80IdealDist false (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 l q) =
      pos80IdealDist false (MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 0 q) := by
  let qM (m : Fin 256) : BitAssignment 80 := MergedVepTopCoinCollapse.p80SetCosetAndNuc 0 m q
  have hOutGen : ∀ (m : Fin 256) (j : Fin 80), (j.val < 3 ∨ 14 ≤ j.val) → qM m j = q j :=
    fun m j hj ↦ by
      simp [qM, MergedVepTopCoinCollapse.p80SetCosetAndNuc,
        show ¬(3 ≤ j.val ∧ j.val < 6) by omega, show ¬(6 ≤ j.val ∧ j.val < 14) by omega]
  have hAt : ∀ j : Fin 80, (j.val < 3 ∨ 14 ≤ j.val) → qM l j = qM 0 j := fun j hj ↦
    (hOutGen l j hj).trans (hOutGen 0 j hj).symm
  have hB0Gen : ∀ m : Fin 256, Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ qM m (pos80SubIdx 3 3 (by decide) j)) = 0 := fun m ↦ by
    have hfn : (fun j : Fin 3 ↦ qM m (pos80SubIdx 3 3 (by decide) j)) =
        fun j : Fin 3 ↦ z2BitOfNat 0 j.val := funext fun j ↦ by
      simp [qM, MergedVepTopCoinCollapse.p80SetCosetAndNuc, pos80SubIdx, z2BitOfNat,
        show 3 ≤ 3 + j.val ∧ 3 + j.val < 6 by omega]
    rw [hfn]
    exact bitsVal_z2BitOfNat 3 0 (by decide)
  have hNucGen : ∀ m : Fin 256, Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 8 ↦ qM m (pos80SubIdx 6 8 (by decide) j)) = m.val := fun m ↦ by
    have hfn : (fun j : Fin 8 ↦ qM m (pos80SubIdx 6 8 (by decide) j)) =
        fun j : Fin 8 ↦ z2BitOfNat m.val j.val := funext fun j ↦ by
      dsimp only [qM]
      unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc pos80SubIdx
      simp only [show ¬(3 ≤ 6 + j.val ∧ 6 + j.val < 6) by omega, ↓reduceDIte,
        show 6 ≤ 6 + j.val ∧ 6 + j.val < 14 by omega, natModTwoCast_eq_z2BitOfNat]
      exact congrArg (z2BitOfNat m.val) (by omega)
    rw [hfn]
    exact bitsVal_z2BitOfNat 8 m.val m.isLt
  have hEqSlice : ∀ (off a : ℕ) (h : off + a ≤ 80), 14 ≤ off →
      (fun j : Fin a ↦ qM l (pos80SubIdx off a h j)) =
      (fun j : Fin a ↦ qM 0 (pos80SubIdx off a h j)) := fun off a h hoff ↦
    funext fun j ↦ hAt _ (Or.inr (Nat.le_trans hoff (Nat.le_add_right off j.val)))
  have hPayloadEq : ∀ (W : ℕ → BitAssignment 80),
      (∀ j : Fin 80, (j.val < 3 ∨ 14 ≤ j.val) → W l.val j = W 0 j) →
      (∀ (m : ℕ) (j : Fin 80), 3 ≤ j.val → j.val < 6 → W m j = z2BitOfNat 0 (j.val - 3)) →
      (∀ (m : ℕ) (j : Fin 80), 6 ≤ j.val → j.val < 14 → W m j = z2BitOfNat m (j.val - 6)) →
      (qM l == W l.val) = (qM 0 == W 0) := fun W hWOut hWB0 hWNuc ↦ by
    have hImp : ∀ (m₁ m₂ : Fin 256),
        (∀ j : Fin 80, (j.val < 3 ∨ 14 ≤ j.val) → W m₁.val j = W m₂.val j) →
        qM m₁ = W m₁.val → qM m₂ = W m₂.val := fun m₁ m₂ hW12 hEq ↦ funext fun j ↦ by
      by_cases hj3 : j.val < 3
      · exact (hOutGen m₂ j (Or.inl hj3)).trans ((hOutGen m₁ j (Or.inl hj3)).symm.trans
          ((congrFun hEq j).trans (hW12 j (Or.inl hj3))))
      · by_cases hj6 : j.val < 6
        · rw [hWB0 m₂.val j (by omega) hj6]
          simp [qM, MergedVepTopCoinCollapse.p80SetCosetAndNuc, z2BitOfNat,
            show 3 ≤ j.val ∧ j.val < 6 by omega]
        · by_cases hj14 : j.val < 14
          · rw [hWNuc m₂.val j (by omega) hj14]
            dsimp only [qM]
            unfold MergedVepTopCoinCollapse.p80SetCosetAndNuc
            rw [dite_eq_right (by omega : ¬(3 ≤ j.val ∧ j.val < 6)),
              dite_eq_left (by omega : 6 ≤ j.val ∧ j.val < 14)]
            exact natModTwoCast_eq_z2BitOfNat m₂.val (j.val - 6)
          · have ho : j.val < 3 ∨ 14 ≤ j.val := Or.inr (by omega)
            exact (hOutGen m₂ j ho).trans
              ((hOutGen m₁ j ho).symm.trans ((congrFun hEq j).trans (hW12 j ho)))
    simpa only [beq_iff_eq] using Bool.eq_iff_iff.mpr
      ⟨by simpa only [beq_iff_eq, Fin.val_zero] using hImp l 0 hWOut,
        by simpa only [beq_iff_eq, Fin.val_zero] using hImp 0 l fun j hj ↦ (hWOut j hj).symm⟩
  have hHeadEq : ∀ (anc : ℕ) (k : Fin 56) (pid : Fin 6) (sm : Fin 8) (t r : Bool),
      (qM l == headWitnessPayload80 0 l.val anc k pid sm t r) =
      (qM 0 == headWitnessPayload80 0 0 anc k pid sm t r) := fun anc k pid sm t r ↦
    hPayloadEq (fun m ↦ headWitnessPayload80 0 m anc k pid sm t r)
      (fun j hj ↦ by
        rcases hj with hj3 | hj14
        · simp [headWitnessPayload80, hj3]
        · simp [headWitnessPayload80, show ¬j.val < 3 by omega, show ¬j.val < 6 by omega,
            show ¬j.val < 14 by omega])
      (fun _ j _ hj6 ↦ by simp [headWitnessPayload80, show ¬j.val < 3 by omega, hj6])
      (fun _ j _ hj14 ↦ by
        simp [headWitnessPayload80, show ¬j.val < 3 by omega, show ¬j.val < 6 by omega, hj14])
  have hTailEq : ∀ (anc part : ℕ) (dp : Fin 8) (keep : ℕ) (t r : Bool),
      (qM l == tailWitnessPayload80 0 l.val anc part dp keep t r) =
      (qM 0 == tailWitnessPayload80 0 0 anc part dp keep t r) := fun anc part dp keep t r ↦
    hPayloadEq (fun m ↦ tailWitnessPayload80 0 m anc part dp keep t r)
      (fun j hj ↦ by
        rcases hj with hj3 | hj14
        · simp [tailWitnessPayload80, hj3]
        · simp [tailWitnessPayload80, show ¬j.val < 3 by omega, show ¬j.val < 6 by omega,
            show ¬j.val < 14 by omega])
      (fun _ j _ hj6 ↦ by simp [tailWitnessPayload80, show ¬j.val < 3 by omega, hj6])
      (fun _ j _ hj14 ↦ by
        simp [tailWitnessPayload80, show ¬j.val < 3 by omega, show ¬j.val < 6 by omega, hj14])
  have hScrEq : (∀ j : Fin 12, qM l (pos80SubIdx 63 12 (by decide) j) = 0) ↔
      (∀ j : Fin 12, qM 0 (pos80SubIdx 63 12 (by decide) j) = 0) :=
    forall_congr' fun j ↦ by rw [congrFun (hEqSlice 63 12 (by decide) (by decide)) j]
  change pos80IdealDist false (qM l) = pos80IdealDist false (qM 0)
  unfold pos80IdealDist
  dsimp only
  rw [hB0Gen l, hB0Gen 0, hNucGen l, hNucGen 0,
    congrArg Pos24HeadCoordXor80.bitsVal (hEqSlice 14 8 (by decide) (by decide)),
    congrArg Pos24HeadCoordXor80.bitsVal (hEqSlice 22 8 (by decide) (by decide)),
    congrArg Pos24HeadCoordXor80.bitsVal (hEqSlice 32 30 (by decide) (by decide)),
    hAt 62 (by decide), hAt 30 (by decide), hAt 31 (by decide), hAt 75 (by decide),
    hAt 76 (by decide), hAt 77 (by decide), hAt 78 (by decide), hAt 79 (by decide)]
  have hl0 : (0 : ℕ) < 216 := by decide
  by_cases hc62 : (qM 0 62 != 0) = true
  · rw [ite_pos hc62, ite_pos hc62]
  · rw [ite_neg hc62, ite_neg hc62]
    by_cases hc30 : (qM 0 30 == 1) = true
    · simp only [hc30, ↓reduceIte, Bool.false_eq_true, Fin.val_zero, hl, hl0, decide_true,
        hEqSlice 63 6 (by decide) (by decide), hEqSlice 69 3 (by decide) (by decide),
        hEqSlice 72 3 (by decide) (by decide)]
      by_cases hk :
          Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ qM 0 (pos80SubIdx 63 6 (by decide) j)) < 56
      · by_cases hp :
            Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ qM 0 (pos80SubIdx 69 3 (by decide) j)) < 6
        · simp only [hk, hp, ↓reduceDIte, hHeadEq]
        · simp only [hk, hp, ↓reduceDIte]
      · simp only [hk, ↓reduceDIte]
    · simp only [hc30, Bool.false_eq_true, ↓reduceIte, Fin.val_zero, hl, hl0, decide_true,
        hScrEq, hEqSlice 75 3 (by decide) (by decide), hTailEq]
theorem mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen (qRatio : ℝ) (b2 :
    SpecsAux.SpecMirror.Configuration → Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (cfg : SpecsAux.SpecMirror.Configuration) : MergedVepTopCoinCollapse.mMergedBUnitTwosGen qRatio
    b2 cfg = Pos24MergedVepPrepAndStitch.mergedPosSlot2BUnitTwosGen qRatio b2 cfg := by
  have hr : MergedVepTopCoinCollapse.mProj24_sp = PosSlots24MergedVepBound.rProj24_sp := rfl
  have hg : MergedVepTopCoinCollapse.mProjGridEquiv24 = PosSlots24MergedVepBound.projGridEquiv24 :=
    by
    ext x w; rfl
  have hc : ProjZ512QftAndTwist288.cfgProjZ512 = PosSlots24MergedVepBound.cfgProjZ512 := rfl
  have hpg : ProjZ512QftAndTwist288.projGridEquiv24 = PosSlots24MergedVepBound.projGridEquiv24 := by
    ext x w; rfl
  have hpt : ProjZ512QftAndTwist288.projTwosMom3D = PosSlots24MergedVepBound.projTwosMom3D := by
    funext uIdx w
    simp only [ProjZ512QftAndTwist288.projTwosMom3D, PosSlots24MergedVepBound.projTwosMom3D, hpg]
  have hu : ProjZ512QftAndTwist288.uProjPlus512_3D = PosSlots24MergedVepBound.uProjPlus512_3D := by
    funext b; apply Subtype.ext
    rw [ProjZ512QftAndTwist288.uProjPlus512_3D_val]
    change ProjZ512QftAndTwist288.uProjPlus512TwosMat3D b =
      PosSlots24MergedVepBound.uProjPlus512TwosMat3D b
    ext yIdx uIdx
    simp only[ProjZ512QftAndTwist288.uProjPlus512TwosMat3D,
        PosSlots24MergedVepBound.uProjPlus512TwosMat3D, Matrix.of_apply, hpg, hpt]
  have hp : ∀ yIdx,
    MergedVepTopCoinCollapse.mProjBasisGen PosSlots24MergedVepBound.rProj24_sp yIdx =
      PosSlots24MergedVepBound.projBasisGen PosSlots24MergedVepBound.rProj24_sp yIdx := fun _ ↦ rfl
  unfold MergedVepTopCoinCollapse.mMergedBUnitTwosGen MergedVepTopCoinCollapse.mVepFromSlot2TwosOp
    MergedVepTopCoinCollapse.mVepGen Pos24MergedVepPrepAndStitch.mergedPosSlot2BUnitTwosGen
    PosSlots24MergedVepBound.vepFromSlot2TwosOp PosSlots24MergedVepBound.vepGen
  rw [hr, hg, hc, hu]
  simp_rw [hp]
theorem mergedCoherentOp80_muSlot2Ideal218_eq
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : SpecsAux.SpecMirror.Configuration) :
    MergedVepTopCoinCollapse.mergedCoherentOp80 qft cfg PosPostPrep80MergedVep.muSlot2Ideal218 =
    Pos24MergedVepPrepAndStitch.mergedPosSlot2BUnitTwosGen (108 / 109 : ℝ) (fun c ↦
      PosSlots24SemanticOracleConcrete80.coherentSysOp80 qft c false
        (PosSlots24Semantic80Physics.pos80IdealDist false)) cfg := by
  refine (MergedVepTopCoinCollapse.mergedCoherentOpGen_eq_mergedBUnitTwosGen_of_b0Zero
    (fun c' p' ↦ MergedVepTopCoinCollapse.sysBlock80 qft c' false p')
    (108 / 109 : ℝ) muSlot2Ideal216 muSlot2Ideal218
    (MergedVepTopCoinCollapse.sysBlock80_projIndep qft)
    muSlot2Ideal216_eq_zero_of_nuc_ge_216 muSlot2Ideal216_eq_zero_of_b0_ne_zero
    (fun p hp ↦ by simp [muSlot2Ideal218, ← p80NucVal_eq_bitsVal, hp])
    (fun p hp ↦ by
      simp [muSlot2Ideal218, ← p80NucVal_eq_bitsVal,
        show ¬MergedVepTopCoinCollapse.p80NucVal p < 216 by omega,
        show ¬MergedVepTopCoinCollapse.p80NucVal p < 218 by omega])
    (fun p l hge hlt hl ↦ by
      unfold muSlot2Ideal218
      rw [← p80NucVal_eq_bitsVal]
      simp only [show ¬MergedVepTopCoinCollapse.p80NucVal p < 216 by omega, ↓reduceIte, hlt]
      rw [show (27 / 218 : ℝ) = (108 / 109 : ℝ) / 8 by norm_num]
      congr 1
      unfold muSlot2Ideal216
      rw [p80ClearCosetAndNucLocal_eq_set0, flip_setCosetAndNuc_comm,
        flip_setCosetAndNuc_comm, pos80IdealDist_false_setCosetAndNuc_eq l hl])
    cfg).trans ?_
  have hBase : (fun c ↦ ∑ p : BitAssignment 80,
      (muSlot2Ideal216 p : ℂ) • MergedVepTopCoinCollapse.sysBlock80 qft c false p) =
      (fun c ↦ PosSlots24SemanticOracleConcrete80.coherentSysOp80 qft c false
        (PosSlots24Semantic80Physics.pos80IdealDist false)) :=
    funext (coherentSysOp80_muSlot2Ideal216_eq qft)
  rw [hBase]
  exact mMergedBUnitTwosGen_eq_mergedPosSlot2BUnitTwosGen (108 / 109 : ℝ) _ cfg
theorem castUnitaryPow2_sa {a b : ℕ} (h : a = b) (V : Unitary (2 ^ a)) (hV : V.1ᴴ = V.1) :
    (PosSlots24SemanticBridge.castUnitaryPow2 h V).1ᴴ =
      (PosSlots24SemanticBridge.castUnitaryPow2 h V).1 := by
  subst h; exact hV
theorem conj_sa_of_sa {D : ℕ} (U M : Operator D) (hM : Mᴴ = M) :
    (Uᴴ * M * U)ᴴ = Uᴴ * M * U := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hM, Matrix.mul_assoc]
theorem pos24ConjCore80_conjTranspose (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) :
    (PosSlots24SemanticBridge.pos24ConjCore80 qft cfg).1ᴴ =
    (PosSlots24SemanticBridge.pos24ConjCore80 qft cfg).1 := by
  unfold PosSlots24SemanticBridge.pos24ConjCore80
  rw [PosMomSelectDynamic.unitaryConj_val]
  exact conj_sa_of_sa _ _ (castUnitaryPow2_sa _ _ (PosSlots24TopWrapper.uPosPhase_sa_core true
    PosSlots24SemanticBridge.pos24TailSign PosSlots24SemanticBridge.pos24TailMag30))
theorem sysBlock80_conjTranspose (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (p : BitAssignment 80) :
    (MergedVepTopCoinCollapse.sysBlock80 qft cfg s0 p)ᴴ = MergedVepTopCoinCollapse.sysBlock80
    qft cfg s0 p := by
  unfold MergedVepTopCoinCollapse.sysBlock80
  rw [PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_conjTranspose,
    pos24ConjCore80_conjTranspose]
theorem coherentSysOp80_conjTranspose (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (mu : BitAssignment 80 → ℝ) :
    (PosSlots24SemanticOracleConcrete80.coherentSysOp80 qft cfg s0 mu)ᴴ =
    PosSlots24SemanticOracleConcrete80.coherentSysOp80 qft cfg s0 mu := by
  unfold PosSlots24SemanticOracleConcrete80.coherentSysOp80
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    PosSlots24SemanticOracleConcrete80.sysBlockAtPayloadGen_conjTranspose,
    pos24ConjCore80_conjTranspose]
theorem basisOutcomeProjector_comm_of_projDiag {S m : ℕ}
    (r : QRegister m S) (A : Operator (2 ^ S)) (y : Fin (2 ^ m))
    (hDiag : ∀ x' x, r.extractIndex x' ≠ r.extractIndex x → A x' x = 0) :
    r.basisOutcomeProjector y * A = A * r.basisOutcomeProjector y := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  ext x' x
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases h : r.extractIndex x' = r.extractIndex x
  · rw [h, mul_comm]
  · simp [hDiag x' x h]
theorem mergedSliceGen_sysBlock80_conjTranspose
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : SpecsAux.SpecMirror.Configuration)
    (p : BitAssignment 80) : (MergedVepTopCoinCollapse.mergedSliceGen (fun c' p' ↦
    MergedVepTopCoinCollapse.sysBlock80 qft c' false p') cfg p)ᴴ =
    MergedVepTopCoinCollapse.mergedSliceGen
    (fun c' p' ↦ MergedVepTopCoinCollapse.sysBlock80 qft c' false p') cfg p := by
  unfold MergedVepTopCoinCollapse.mergedSliceGen
  by_cases h : MergedVepTopCoinCollapse.p80NucVal p < 216
  · rw [MergedVepTopCoinCollapse.ite_eq_of_pos h]
    exact sysBlock80_conjTranspose qft cfg false p
  · rw [MergedVepTopCoinCollapse.ite_eq_of_neg h]
    dsimp only
    refine conj_sa_of_sa _ _ ?_
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
    rw [MergedVepTopCoinCollapse.mProjBasisGen_eq_basisOutcomeProjector,
      Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
      sysBlock80_conjTranspose]
    exact (basisOutcomeProjector_comm_of_projDiag _ _ yIdx
      fun x' x hne ↦ MergedVepTopCoinCollapse.sysBlock80_projDiag qft _ false
        (MergedVepTopCoinCollapse.p80SetNucZero p) x' x hne).symm
theorem mergedCoherentOp80_conjTranspose (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (mu : BitAssignment 80 → ℝ) :
    (MergedVepTopCoinCollapse.mergedCoherentOp80 qft cfg mu)ᴴ =
    MergedVepTopCoinCollapse.mergedCoherentOp80 qft cfg mu := by
  unfold MergedVepTopCoinCollapse.mergedCoherentOp80 MergedVepTopCoinCollapse.mergedCoherentOpGen
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    mergedSliceGen_sysBlock80_conjTranspose]
end Opts
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
end PosPostPrep80L1Bounds
end
end ModPosPostPrep80L1Bounds

section ModPosSlots24Semantic80PhysicsExt
@[expose] public section
namespace PosSlots24Semantic80Physics
section ConfigPosSlots24Semantic80PhysicsExt
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowSem80Sec4 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit hiding norm_projector_le_one
open PosMomSelectDynamic
open FullSysMomSlots0135Concrete
open NuclearTwistRealizes
open FullSysCatSegmentBridge
open HoistedSwapSelectBridge hiding unitaryConj unitaryConj_val
open OraAndPrepBundle
open FullSysHoistedSelectStitch
open GeneralBetaAndAlphaTopEndpoint
open SingleCatClosure
open PosSlots24TopWrapper
open PosSlots24SemanticBridge
open PosSlots24SemanticOracleConcrete80
open PosSlots24BranchConcrete (uPosPhase)
lemma ite_true_branch_sem80 {α : Type*} {P : Prop} [Decidable P] (hp : P)
    {a b : α} : (if P then a else b) = a := ite_eq_left hp
lemma ite_false_branch_sem80 {α : Type*} {P : Prop} [Decidable P] (hp : ¬P)
    {a b : α} : (if P then a else b) = b := ite_eq_right hp
lemma dite_true_branch_sem80_s4 {α : Type*} {P : Prop} [Decidable P] (hp : P)
    {a : P → α} {b : ¬P → α} : (if h : P then a h else b h) = a hp := dite_eq_left hp
lemma dite_false_branch_sem80_s4 {α : Type*} {P : Prop} [Decidable P] (hp : ¬P)
    {a : P → α} {b : ¬P → α} : (if h : P then a h else b h) = b hp := dite_eq_right hp
theorem eq_of_bitsVal_eq {m x : ℕ} (f : BitAssignment m) (hx : x < 2 ^ m)
    (hf : ∀ j : Fin m, f j = z2BitOfNat x j.val) : Pos24HeadCoordXor80.bitsVal f = x := by
  rw [bitsVal_congr hf, bitsVal_z2BitOfNat, Nat.mod_eq_of_lt hx]
theorem castCore80_uPosPhase_conjTranspose : (castUnitaryPow2 pos24_coreWires80_eq.symm
    (uPosPhase true pos24TailSign pos24TailMag30)).1ᴴ = (castUnitaryPow2
    pos24_coreWires80_eq.symm (uPosPhase true pos24TailSign pos24TailMag30)).1 :=
  PosPostPrep80L1Bounds.castUnitaryPow2_sa
    pos24_coreWires80_eq.symm _ (uPosPhase_sa_core true pos24TailSign pos24TailMag30)
theorem pos24ConjCore80_conjTranspose (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) : (pos24ConjCore80 qft cfg).1ᴴ =
    (pos24ConjCore80 qft cfg).1 := PosMomSelectDynamic.unitaryConj_conjTranspose
    castCore80_uPosPhase_conjTranspose
theorem sysBlockAtPayloadGen_pos24ConjCore80_isHermitian
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg : SpecsAux.SpecMirror.Configuration)
    (s0 : Bool) (p80 : BitAssignment 80) : (sysBlockAtPayloadGen pos24_coreWires80_eq.symm
    (pos24ConjCore80 qft cfg).1 s0 p80).IsHermitian := by
  rw [Matrix.IsHermitian, sysBlockAtPayloadGen_conjTranspose, pos24ConjCore80_conjTranspose]
theorem coherentSysOp80_isHermitian (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (α : BitAssignment 80 → ℝ) :
    (coherentSysOp80 qft cfg s0 α).IsHermitian := by
  rw [Matrix.IsHermitian, coherentSysOp80, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun p80 _ ↦ ?_
  rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    (sysBlockAtPayloadGen_pos24ConjCore80_isHermitian qft cfg s0 p80).eq]
abbrev HeadSupportIdx (s0 : Bool) : Type :=
  Fin (if s0 then 8 else 1) × Fin (if s0 then 1 else 216) × Fin (if s0 then 218 else 1) ×
    Fin 56 × Fin 6 × Fin 8 × Bool × Bool
abbrev TailSupportIdx (s0 : Bool) : Type :=
  Fin (if s0 then 8 else 1) × Fin (if s0 then 1 else 216) × Fin 218 × Fin (if s0 then 217 else 1) ×
    (Σ dp : Fin 8, Fin (pos24TailSpan8 dp)) × Bool × Bool
abbrev Pos80SupportIdx (s0 : Bool) : Type := HeadSupportIdx s0 ⊕ TailSupportIdx s0
def pos80WitnessOf (s0 : Bool) : Pos80SupportIdx s0 → BitAssignment 80
  | Sum.inl ⟨b0, nuc, anc, k, pid, sm, th, rj⟩ =>
      headWitnessPayload80 b0.val nuc.val anc.val k pid sm th rj
  | Sum.inr ⟨b0, nuc, anc, part, ⟨dp, keep⟩, th, rj⟩ =>
      tailWitnessPayload80 b0.val nuc.val anc.val part.val dp keep.val th rj
def decodeHeadIdx (p : BitAssignment 80) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Bool × Bool :=
  (Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 14 8 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ p (pos80SubIdx 63 6 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 69 3 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 72 3 (by decide) j)),
   p 31 == 1, p 79 == 1)
def decodeTailIdx (p : BitAssignment 80) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Bool × Bool :=
  (Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 14 8 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 22 8 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 75 3 (by decide) j)),
   Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ p (pos80SubIdx 32 30 (by decide) j)),
   p 31 == 1, p 79 == 1)
private theorem lemHex428 {A B C D E F G H : Type*} {x₁ y₁ : A} {x₂ y₂ : B} {x₃ y₃ : C}
    {x₄ y₄ : D} {x₅ y₅ : E} {x₆ y₆ : F} {x₇ y₇ : G} {x₈ y₈ : H} (h₁ : x₁ = y₁) (h₂ : x₂ = y₂)
    (h₃ : x₃ = y₃) (h₄ : x₄ = y₄) (h₅ : x₅ = y₅) (h₆ : x₆ = y₆) (h₇ : x₇ = y₇) (h₈ : x₈ = y₈)
    : (x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈) = (y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈) := by
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈; rfl
theorem decodeHeadIdx_headWitnessPayload80 {b0Val nuc anc : ℕ} (hb0 : b0Val < 8)
    (hnuc : nuc < 256) (hanc : anc < 256) (k : Fin 56) (pid : Fin 6) (sm : Fin 8)
    (th rj : Bool) : decodeHeadIdx (headWitnessPayload80 b0Val nuc anc k pid sm th rj) =
    (b0Val, nuc, anc, k.val, pid.val, sm.val, th, rj) :=
  lemHex428
    (eq_of_bitsVal_eq _ hb0 fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ hnuc fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ hanc fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ (lt_trans k.isLt (by decide)) fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ (lt_trans pid.isLt (by decide)) fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ sm.isLt fun j ↦ by fin_cases j <;> rfl)
    (by cases th <;> rfl) (by cases rj <;> rfl)
private lemma lemHex429 (b0Val nuc anc part : ℕ) (dp : Fin 8) {keep : ℕ}
    (hkeep : keep < pos24TailSpan8 dp) (th rj : Bool) : Pos24HeadCoordXor80.bitsVal
    (fun j : Fin 30 ↦ tailWitnessPayload80 b0Val nuc anc part dp keep th rj
      (pos80SubIdx 32 30 (by decide) j)) = keep := by
  rw [bitsVal_congr (g := fun j : Fin 30 ↦ z2BitOfNat keep j.val)]
  · exact bitsVal_z2BitOfNat_of_lt (lt_of_lt_of_le hkeep (tailSpan8_lt_two_pow_30 dp))
  · intro j
    fin_cases j <;> rfl
theorem decodeTailIdx_tailWitnessPayload80 {b0Val nuc anc part : ℕ} (hb0 : b0Val < 8)
    (hnuc : nuc < 256) (hanc : anc < 256) (hpart : part < 256) (dp : Fin 8) {keep : ℕ}
    (hkeep : keep < pos24TailSpan8 dp) (th rj : Bool) :
    decodeTailIdx (tailWitnessPayload80 b0Val nuc anc part dp keep th rj) =
      (b0Val, nuc, anc, part, dp.val, keep, th, rj) :=
  lemHex428
    (eq_of_bitsVal_eq _ hb0 fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ hnuc fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ hanc fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ hpart fun j ↦ by fin_cases j <;> rfl)
    (eq_of_bitsVal_eq _ dp.isLt fun j ↦ by fin_cases j <;> rfl)
    (lemHex429 b0Val nuc anc part dp hkeep th rj)
    (by cases th <;> rfl) (by cases rj <;> rfl)
theorem pos80WitnessOf_injective (s0 : Bool) : Function.Injective (pos80WitnessOf s0) := by
  have hb8 : ∀ b : Fin (if s0 then 8 else 1), b.val < 8 := fun b ↦ by
    cases s0 <;> exact lt_of_lt_of_le b.isLt (by decide)
  have hn256 : ∀ n : Fin (if s0 then 1 else 216), n.val < 256 := fun n ↦ by
    cases s0 <;> exact lt_of_lt_of_le n.isLt (by decide)
  have ha256 : ∀ a : Fin (if s0 then 218 else 1), a.val < 256 := fun a ↦ by
    cases s0 <;> exact lt_of_lt_of_le a.isLt (by decide)
  have hp256 : ∀ p : Fin (if s0 then 217 else 1), p.val < 256 := fun p ↦ by
    cases s0 <;> exact lt_of_lt_of_le p.isLt (by decide)
  rintro (⟨b₁, n₁, a₁, k₁, p₁, s₁, th₁, rj₁⟩ | ⟨b₁, n₁, a₁, pt₁, ⟨dp₁, kp₁⟩, th₁, rj₁⟩)
    (⟨b₂, n₂, a₂, k₂, p₂, s₂, th₂, rj₂⟩ | ⟨b₂, n₂, a₂, pt₂, ⟨dp₂, kp₂⟩, th₂, rj₂⟩) heq
  · have hd := congrArg decodeHeadIdx heq
    dsimp only [pos80WitnessOf] at hd
    rw [decodeHeadIdx_headWitnessPayload80 (hb8 b₁) (hn256 n₁) (ha256 a₁),
      decodeHeadIdx_headWitnessPayload80 (hb8 b₂) (hn256 n₂) (ha256 a₂)] at hd
    simp only [Prod.mk.injEq] at hd
    rcases hd with ⟨eb, en, ea, ek, ep, es, eth, erj⟩
    exact congrArg Sum.inl (Prod.ext (Fin.ext eb) (Prod.ext (Fin.ext en) (Prod.ext (Fin.ext ea)
      (Prod.ext (Fin.ext ek) (Prod.ext (Fin.ext ep) (Prod.ext (Fin.ext es) (Prod.ext eth erj)))))))
  · have h30 := congrFun heq 30
    dsimp only [pos80WitnessOf] at h30
    exact nomatch (h30 : (1 : ZMod 2) = 0)
  · have h30 := congrFun heq 30
    dsimp only [pos80WitnessOf] at h30
    exact nomatch (h30 : (0 : ZMod 2) = 1)
  · have hd := congrArg decodeTailIdx heq
    dsimp only [pos80WitnessOf] at hd
    rw [decodeTailIdx_tailWitnessPayload80 (hb8 b₁) (hn256 n₁) (lt_trans a₁.isLt (by decide))
        (hp256 pt₁) dp₁ kp₁.isLt,
      decodeTailIdx_tailWitnessPayload80 (hb8 b₂) (hn256 n₂) (lt_trans a₂.isLt (by decide))
        (hp256 pt₂) dp₂ kp₂.isLt] at hd
    simp only [Prod.mk.injEq] at hd
    rcases hd with ⟨eb, en, ea, ept, edp, ekp, eth, erj⟩
    cases Fin.ext edp
    exact congrArg Sum.inr (Prod.ext (Fin.ext eb) (Prod.ext (Fin.ext en) (Prod.ext (Fin.ext ea)
      (Prod.ext (Fin.ext ept) (Prod.ext (Sigma.ext rfl (heq_of_eq (Fin.ext ekp)))
        (Prod.ext eth erj))))))
theorem pos80IdealDist_eq_zero_of_not_mem (s0 : Bool) {p80 : BitAssignment 80}
    (hnot : ¬ ∃ w : Pos80SupportIdx s0, pos80WitnessOf s0 w = p80) :
    pos80IdealDist s0 p80 = 0 := by
  unfold pos80IdealDist
  by_cases h62 : (p80 62 != 0) = true
  · rw [ite_true_branch_sem80 h62]
  · rw [ite_false_branch_sem80 h62]
    by_cases h30 : (p80 30 == 1) = true
    · rw [ite_true_branch_sem80 h30]
      set b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 3 3 (by decide) j))
      set nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 6 8 (by decide) j))
      set anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j))
      set kVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ p80 (pos80SubIdx 63 6 (by decide) j))
      set pidVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
        p80 (pos80SubIdx 69 3 (by decide) j))
      set smVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
        p80 (pos80SubIdx 72 3 (by decide) j))
      by_cases hk : kVal < 56
      · rw [dite_true_branch_sem80_s4 hk]
        by_cases hp : pidVal < 6
        · rw [dite_true_branch_sem80_s4 hp]
          refine ite_false_branch_sem80 fun hcond ↦ hnot ?_
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          rcases hcond with ⟨⟨⟨_, hmeta⟩, _⟩, hpeq⟩
          have hb8 : b0Val < 8 := Pos24HeadCoordXor80.bitsVal3_lt8 _
          cases s0
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
              decide_eq_true_eq] at hmeta
            rcases hmeta with ⟨⟨hb0, hnuc⟩, hanc⟩
            exact ⟨Sum.inl ⟨⟨b0Val, by rw [hb0]; decide⟩,⟨nuc, hnuc⟩,⟨anc, by rw [hanc]; decide⟩,
              ⟨kVal, hk⟩,⟨pidVal, hp⟩,⟨smVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩,
              p80 31 == 1, p80 79 == 1⟩, hpeq.symm⟩
          · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmeta
            rcases hmeta with ⟨hnuc, hanc⟩
            exact ⟨Sum.inl ⟨⟨b0Val, hb8⟩,⟨nuc, by rw [hnuc]; decide⟩,⟨anc, hanc⟩,
              ⟨kVal, hk⟩,⟨pidVal, hp⟩,⟨smVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩,
              p80 31 == 1, p80 79 == 1⟩, hpeq.symm⟩
        · rw [dite_false_branch_sem80_s4 hp]
      · rw [dite_false_branch_sem80_s4 hk]
    · rw [ite_false_branch_sem80 h30]
      set b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 3 3 (by decide) j))
      set nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 6 8 (by decide) j))
      set anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j))
      set part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j))
      set fine30 := Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦
        p80 (pos80SubIdx 32 30 (by decide) j))
      set dpVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
        p80 (pos80SubIdx 75 3 (by decide) j))
      refine ite_false_branch_sem80 fun hcond ↦ hnot ?_
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨⟨_, hmeta⟩, hfine⟩, hpeq⟩
      have hb8 : b0Val < 8 := Pos24HeadCoordXor80.bitsVal3_lt8 _
      cases s0
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at hmeta
        rcases hmeta with ⟨⟨⟨hb0, hnuc⟩, hanc⟩, hpart⟩
        exact ⟨Sum.inr ⟨⟨b0Val, by rw [hb0]; decide⟩,⟨nuc, hnuc⟩,⟨anc, hanc⟩,⟨part, by
          rw [hpart]; decide⟩,
          ⟨⟨dpVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩,⟨fine30, hfine⟩⟩,
          p80 31 == 1, p80 79 == 1⟩, hpeq.symm⟩
      · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmeta
        rcases hmeta with ⟨⟨hnuc, hanc⟩, hpart⟩
        exact ⟨Sum.inr ⟨⟨b0Val, hb8⟩,⟨nuc, by rw [hnuc]; decide⟩,⟨anc, hanc⟩,⟨part, hpart⟩,
          ⟨⟨dpVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩,⟨fine30, hfine⟩⟩,
          p80 31 == 1, p80 79 == 1⟩, hpeq.symm⟩
theorem sum_over_pos80IdealDist_support {M : Type*} [AddCommMonoid M] (s0 : Bool)
    (F : BitAssignment 80 → ℝ → M) (hZero : ∀ p80, F p80 0 = 0) :
    (∑ p80 : BitAssignment 80, F p80 (pos80IdealDist s0 p80)) = ∑ w : Pos80SupportIdx s0, F
    (pos80WitnessOf s0 w) (pos80IdealDist s0 (pos80WitnessOf s0 w)) := by
  let g : Pos80SupportIdx s0 → M := fun w ↦
    F (pos80WitnessOf s0 w) (pos80IdealDist s0 (pos80WitnessOf s0 w))
  have hpt : ∀ p80 : BitAssignment 80,
      F p80 (pos80IdealDist s0 p80) =
        PosSlots24SemanticOracleConcrete80.extendZero (pos80WitnessOf s0) g p80 := fun p80 ↦ by
    by_cases hw : ∃ w, pos80WitnessOf s0 w = p80
    · obtain ⟨w, rfl⟩ := hw
      rw [PosSlots24SemanticOracleConcrete80.extendZero_apply (pos80WitnessOf_injective s0) g w]
    · rw [pos80IdealDist_eq_zero_of_not_mem s0 hw, hZero p80,
        PosSlots24SemanticOracleConcrete80.extendZero_of_not_exists _ g hw]
  exact (Finset.sum_congr rfl fun p80 _ ↦ hpt p80).trans
    (PosSlots24SemanticOracleConcrete80.sum_extendZero (pos80WitnessOf_injective s0) g)
theorem pos80WitnessOf_eval_head (s0 : Bool) (b0 : Fin (if s0 then 8 else 1))
    (nuc : Fin (if s0 then 1 else 216)) (anc : Fin (if s0 then 218 else 1)) (k : Fin 56)
    (pid : Fin 6) (sm : Fin 8) (th rj : Bool) : pos80IdealDist s0
    (pos80WitnessOf s0 (Sum.inl (b0, nuc, anc, k, pid, sm, th, rj))) = if s0 then
    (pos24HeadWeight56 k : ℝ) / (8 * 218 * 48 * 2 * 2 * pos80Slot4TotNat) else
    (pos24HeadWeight56 k : ℝ) / (216 * 48 * 2 * 2 * pos80Slot2TotNat) := by
  refine headWitnessPayload80_eval_pos80IdealDist s0 b0.val nuc.val anc.val k pid sm th rj
    (by cases s0 <;> exact lt_of_lt_of_le b0.isLt (by decide))
    (by cases s0 <;> exact lt_of_lt_of_le nuc.isLt (by decide))
    (by cases s0 <;> exact lt_of_lt_of_le anc.isLt (by decide)) ?_
  cases s0
  · simp
  · simp
theorem pos80WitnessOf_eval_tail (s0 : Bool) (b0 : Fin (if s0 then 8 else 1))
    (nuc : Fin (if s0 then 1 else 216)) (anc : Fin 218) (part : Fin (if s0 then 217 else 1))
    (dp : Fin 8) (keep : Fin (pos24TailSpan8 dp)) (th rj : Bool) : pos80IdealDist s0
    (pos80WitnessOf s0 (Sum.inr (b0, nuc, anc, part, ⟨dp, keep⟩, th, rj))) = if s0 then
    (1 : ℝ) / (8 * 218 * 2 * 2 * pos80Slot4TotNat) else (1 : ℝ) /
    (216 * 2 * 2 * pos80Slot2TotNat) := by
  refine tailWitnessPayload80_eval_pos80IdealDist s0 b0.val nuc.val anc.val part.val dp keep.val
    th rj (by cases s0 <;> exact lt_of_lt_of_le b0.isLt (by decide))
    (by cases s0 <;> exact lt_of_lt_of_le nuc.isLt (by decide)) (lt_trans anc.isLt (by decide))
    (by cases s0 <;> exact lt_of_lt_of_le part.isLt (by decide)) keep.isLt ?_
  cases s0
  · simp [anc.isLt]
  · simp [anc.isLt]
theorem pos24HeadWeight56_sum_eq :
    (∑ k : Fin 56, pos24HeadWeight56 k) = pos24HeadSumNat := by decide
theorem pos24TailSpan8_sum_eq :
    (∑ dp : Fin 8, pos24TailSpan8 dp) = pos24TailSpanSumNat := by decide
theorem sum_pos80IdealDist_eq_one (s0 : Bool) :
    (∑ p80 : BitAssignment 80, pos80IdealDist s0 p80) = 1 := by
  rw [sum_over_pos80IdealDist_support s0 (fun _ r ↦ r) (fun _ ↦ rfl), Fintype.sum_sum_type]
  have hsumR : (∑ k : Fin 56, (pos24HeadWeight56 k : ℝ)) = (pos24HeadSumNat : ℝ) := by
    exact_mod_cast pos24HeadWeight56_sum_eq
  have hsumT : (∑ dp : Fin 8, (pos24TailSpan8 dp : ℝ)) = (pos24TailSpanSumNat : ℝ) := by
    exact_mod_cast pos24TailSpan8_sum_eq
  cases s0 <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, pos80WitnessOf_eval_head,
      pos80WitnessOf_eval_tail, Bool.false_eq_true, ↓reduceIte, Finset.sum_const, Fintype.card_fin,
      Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, div_eq_mul_inv, ← Finset.mul_sum,
      ← Finset.sum_mul, hsumR, hsumT] <;>
    norm_num [pos80Slot2TotNat, pos80Slot4TotNat, pos80HeadWeightNat, pos80TailWeightNat,
      pos24HeadSumNat, pos24TailSpanSumNat]
end ConfigPosSlots24Semantic80PhysicsExt
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
end PosSlots24Semantic80Physics
end
end ModPosSlots24Semantic80PhysicsExt

section ModWindowedSlot2MulKick288
@[expose] public section
namespace WindowedSlot2MulKick288Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end WindowedSlot2MulKick288Alt
namespace WindowedSlot2MulKick288
section ConfigWindowedSlot2MulKick288
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64WalkCircuit
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
instance (priority := 1000000) instNeZeroTwoPowWin (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
def StoreClosed {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (d : DynamicCircuit Var n) : Prop :=
      ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = fun _ ↦ M'
def PreservesVarIndep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (d : DynamicCircuit Var n) : Prop := ∀ Θ : CQAssertionCompat Var (2 ^ n),
    (∀ σ val, Θ (Function.update σ v val) = Θ σ) → ∀ σ val, (wp d.compile Θ)
    (Function.update σ v val) = (wp d.compile Θ) σ
theorem storeClosed_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (c : Circuit n) : StoreClosed (Var := Var) (.circuit c) := by
  intro M
  refine ⟨qAssignObsMap c.eval M, ?_⟩
  funext σ
  simp [compile, wpQAssignCompat]
theorem storeClosed_seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {d₁ d₂ : DynamicCircuit Var n} (h₁ : StoreClosed d₁) (h₂ : StoreClosed d₂) :
    StoreClosed (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hM₂⟩ := h₂ M
  obtain ⟨M₁, hM₁⟩ := h₁ M₂
  refine ⟨M₁, ?_⟩
  simp only [compile, wp_qSeq, hM₂, hM₁]
theorem storeClosed_wrapDynamic {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (st : TempAndStep n) {d : DynamicCircuit Var n}
    (hd : StoreClosed d) : StoreClosed (st.wrapDynamic v d) := fun M ↦
    TempAndStep.wp_wrapDynamic_const v st d hd M
theorem preservesVarIndep_identity {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) : PreservesVarIndep v (.identity : DynamicCircuit Var n) := fun
    _ hΘ σ val ↦ hΘ σ val
theorem preservesVarIndep_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (c : Circuit n) :
    PreservesVarIndep v (.circuit c : DynamicCircuit Var n) := by
  intro Θ hΘ σ val
  simp only [compile, DynCircuitExt.wp_circuit_compile_compat, wpQAssignCompat]
  exact congrArg (qAssignObsMap c.eval) (hΘ σ val)
theorem preservesVarIndep_seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {d₁ d₂ : DynamicCircuit Var n} (h₁ : PreservesVarIndep v d₁)
    (h₂ : PreservesVarIndep v d₂) : PreservesVarIndep v (.seq d₁ d₂) := by
  intro Θ hΘ σ val
  simp only [compile, wp_qSeq]
  exact h₁ (wp d₂.compile Θ) (h₂ Θ hΘ) σ val
theorem preservesVarIndep_wrapDynamic {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (st : TempAndStep n) {d : DynamicCircuit Var n}
    (hd : PreservesVarIndep v d) : PreservesVarIndep v (st.wrapDynamic v d) := by
  intro Θ hΘ σ val
  let Θ₁ := wpQAssignCompat st.post.eval Θ
  let Ψ := wpQAssignCompat st.midPost.eval
    (wp (DynamicCircuit.andUncompute v st.c₁ st.c₂ st.anc st.h₁₂).compile Θ₁)
  have hΨ : ∀ σ' val', Ψ (Function.update σ' v val') = Ψ σ' := by
    intro σ' val'
    dsimp only [Ψ, wpQAssignCompat]
    rw [DynamicCircuit.wp_andUncompute_update_self]
  have hexp : wp (st.wrapDynamic v d).compile Θ = wpQAssignCompat st.pre.eval (wpQAssignCompat
      (Circuit.andCompute st.c₁ st.c₂ st.anc st.h₁a st.h₂a).eval (wpQAssignCompat
      st.midPre.eval (wp d.compile Ψ))) := by
    simp [TempAndStep.wrapDynamic, DynamicCircuit.andCompute, Θ₁, Ψ]
  rw [hexp]
  dsimp only [wpQAssignCompat]
  rw [hd Ψ hΨ σ val]
attribute [local irreducible] gidneyAdderAuxDyn gidneyAdderDyn gidneyAdderCircuit
structure CleanPermEquiv {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAnc : QRegister m n) (M_set : Finset (Wire n))
    (d : DynamicCircuit Var n) (c : Circuit n)
    (f : BitAssignment n → BitAssignment n) : Prop where
  varIndep : PreservesVarIndep v d
  storeClosed : StoreClosed d
  perm : ClassicalPerm c f
  outside : ∀ β w, w ∉ M_set → f β w = β w
  wp_eq : ∀ Θ : CQAssertionCompat Var (2 ^ n),
    (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      CQAssertion.restrictToZeroAncilla (wp d.compile Θ) rAnc =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ) rAnc
theorem CleanPermEquiv.widenAnc {Var : Type} [Fintype Var] [DecidableEq Var] {m m' n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {rAnc' : QRegister m' n}
    {M_set : Finset (Wire n)} {d : DynamicCircuit Var n} {c : Circuit n}
    {f : BitAssignment n → BitAssignment n} (hSub : rAnc.image ⊆ rAnc'.image)
    (h : CleanPermEquiv v rAnc M_set d c f) : CleanPermEquiv v rAnc' M_set d c f :=
  { varIndep := h.varIndep
    storeClosed := h.storeClosed
    perm := h.perm
    outside := h.outside
    wp_eq := fun Θ hΘ ↦ restrictAssertionToZeroAncilla_eq_of_subset hSub (h.wp_eq Θ hΘ) }
theorem classicalPerm_comm_zero_proj {m n : ℕ} [NeZero (2 ^ n)] {c : Circuit n}
    {f : BitAssignment n → BitAssignment n} (hPerm : ClassicalPerm c f)
    {M_set : Finset (Wire n)} (hOut : ∀ β w, w ∉ M_set → f β w = β w) (rAnc : QRegister m n)
    (hDisj : Disjoint M_set rAnc.image) : c.eval.1 * rAnc.basisOutcomeProjector 0 =
    rAnc.basisOutcomeProjector 0 * c.eval.1 := by
  apply matrix_ext_basisKet
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    register_basisOutcomeProjector_zero_mulVec_basisKet, hPerm β,
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  have hIff : (∀ i : Fin m, f β (rAnc i) = 0) ↔ (∀ i : Fin m, β (rAnc i) = 0) :=
    forall_congr' fun i ↦ by
      rw [hOut β (rAnc i)
        (Finset.disjoint_right.mp hDisj ((QRegister.mem_image rAnc _).mpr ⟨i, rfl⟩))]
  simp only [hIff]
  split_ifs
  · exact hPerm β
  · exact Matrix.mulVec_zero _
theorem restrict_wp_qAssign_comm_of_perm {Var : Type} [Fintype Var] {m n : ℕ} [NeZero (2 ^ n)]
    {c : Circuit n} {f : BitAssignment n → BitAssignment n} (hPerm : ClassicalPerm c f)
    {M_set : Finset (Wire n)} (hOut : ∀ β w, w ∉ M_set → f β w = β w) (rAnc : QRegister m n)
    (hDisj : Disjoint M_set rAnc.image) (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ) rAnc = wpQAssignCompat c.eval
    (CQAssertion.restrictToZeroAncilla Θ rAnc) := by
  have hCommAdj : c.eval.1ᴴ * rAnc.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 * c.eval.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      (congrArg Matrix.conjTranspose (classicalPerm_comm_zero_proj hPerm hOut rAnc hDisj)).symm
  funext σ
  apply Subtype.ext
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, HermitianMat.conj_conj,
    hCommAdj]
theorem CleanPermEquiv.identity {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rAnc : QRegister m n) (M_set : Finset (Wire n)) :
    CleanPermEquiv v rAnc M_set (.identity : DynamicCircuit Var n) .identity id :=
  { varIndep := preservesVarIndep_identity v, storeClosed := fun M ↦ ⟨M, rfl⟩
    perm := ClassicalPerm.identity, outside := fun _ _ _ ↦ rfl
    wp_eq := fun Θ _ ↦ by
      simp only [compile, DynCircuitExt.wp_circuit_compile_compat,
        show wpQAssignCompat (.identity : Circuit n).eval Θ = Θ from
          funext fun _ ↦ by simp [wpQAssignCompat, Circuit.eval_identity]] }
theorem CleanPermEquiv.seq {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {M_set : Finset (Wire n)}
    {d₁ d₂ : DynamicCircuit Var n} {c₁ c₂ : Circuit n}
    {f₁ f₂ : BitAssignment n → BitAssignment n}
    (hDisj : Disjoint M_set rAnc.image)
    (h₁ : CleanPermEquiv v rAnc M_set d₁ c₁ f₁)
    (h₂ : CleanPermEquiv v rAnc M_set d₂ c₂ f₂) :
    CleanPermEquiv v rAnc M_set (.seq d₁ d₂) (c₁ ;;ᶜ c₂) (fun β ↦ f₂ (f₁ β)) :=
  { varIndep := preservesVarIndep_seq h₁.varIndep h₂.varIndep
    storeClosed := storeClosed_seq h₁.storeClosed h₂.storeClosed
    perm := h₁.perm.seq h₂.perm
    outside := fun β w hw ↦ (h₂.outside (f₁ β) w hw).trans (h₁.outside β w hw)
    wp_eq := fun Θ hΘ ↦ by
      simp only [compile, wp_qSeq, Circuit.eval_seq]
      rw [h₁.wp_eq (wp d₂.compile Θ) (h₂.varIndep Θ hΘ),
        restrict_wp_qAssign_comm_of_perm h₁.perm h₁.outside rAnc hDisj,
        h₂.wp_eq Θ hΘ,
        ← restrict_wp_qAssign_comm_of_perm h₁.perm h₁.outside rAnc hDisj,
        wpQAssignCompat_comp] }
theorem CleanPermEquiv.conjLocalPerm {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {M_set S_p : Finset (Wire n)}
    {cPrep cUnprep : Circuit n} {fPrep fUnprep : BitAssignment n → BitAssignment n}
    {d : DynamicCircuit Var n} {c : Circuit n} {f : BitAssignment n → BitAssignment n}
    (hpPrep : LocalClassicalPerm S_p cPrep fPrep)
    (hpUnprep : LocalClassicalPerm S_p cUnprep fUnprep)
    (hInv : ∀ γ, fUnprep (fPrep γ) = γ)
    (hDisjPM : Disjoint S_p M_set)
    (hDisjPA : Disjoint S_p rAnc.image)
    (hInner : CleanPermEquiv v rAnc M_set d c f) :
    CleanPermEquiv v rAnc M_set
      (.seq (.circuit cPrep) (.seq d (.circuit cUnprep)))
      (cPrep ;;ᶜ (c ;;ᶜ cUnprep))
      (fun β w ↦ if w ∈ M_set then f (fPrep β) w else β w) := by
  have hComb : (fUnprep ∘ (f ∘ fPrep)) =
      (fun β w ↦ if w ∈ M_set then f (fPrep β) w else β w) := by
    funext β w
    dsimp only [Function.comp_apply]
    by_cases hwM : w ∈ M_set
    · simp only [hwM, ↓reduceIte]
      exact hpUnprep.preserves_outside (f (fPrep β)) w (Finset.disjoint_right.mp hDisjPM hwM)
    · simp only [hwM, ↓reduceIte]
      by_cases hwP : w ∈ S_p
      · have hAgree : ∀ u ∈ S_p, f (fPrep β) u = fPrep β u := fun u hu ↦
          hInner.outside (fPrep β) u (Finset.disjoint_left.mp hDisjPM hu)
        rw [hpUnprep.depends_on (f (fPrep β)) (fPrep β) hAgree w hwP, hInv β]
      · rw [hpUnprep.preserves_outside _ w hwP, hInner.outside _ w hwM,
          hpPrep.preserves_outside _ w hwP]
  exact
    { varIndep := preservesVarIndep_seq (preservesVarIndep_circuit v cPrep)
        (preservesVarIndep_seq hInner.varIndep (preservesVarIndep_circuit v cUnprep))
      storeClosed := storeClosed_seq (storeClosed_circuit cPrep)
        (storeClosed_seq hInner.storeClosed (storeClosed_circuit cUnprep))
      perm := by
        rw [← hComb]
        exact hpPrep.perm.seq (hInner.perm.seq hpUnprep.perm)
      outside := fun β w hw ↦ by simp [hw]
      wp_eq := fun Θ hΘ ↦ by
        have hΘ' : ∀ σ val, (wpQAssignCompat cUnprep.eval Θ) (Function.update σ v val) =
            (wpQAssignCompat cUnprep.eval Θ) σ := fun σ val ↦ congrArg
            (qAssignObsMap cUnprep.eval) (hΘ σ val)
        simp only [compile, wp_qSeq, DynCircuitExt.wp_circuit_compile_compat, Circuit.eval_seq]
        rw [restrict_wp_qAssign_comm_of_perm hpPrep.perm hpPrep.preserves_outside rAnc hDisjPA,
          hInner.wp_eq (wpQAssignCompat cUnprep.eval Θ) hΘ',
          ← restrict_wp_qAssign_comm_of_perm hpPrep.perm hpPrep.preserves_outside rAnc hDisjPA]
        simp only [wpQAssignCompat_comp, mul_assoc] }
theorem realizesClean_of_cleanPermEquiv {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct m n : ℕ} [NeZero (2 ^ n)] {v : Var} {rAct : QRegister kAct n} {rAnc : QRegister m n}
    {M_set : Finset (Wire n)} {u : Unitary (2 ^ kAct)} {d : DynamicCircuit Var n}
    {c : Circuit n} {f : BitAssignment n → BitAssignment n}
    (hEquiv : CleanPermEquiv v rAnc M_set d c f) (hAction : ∀ β : BitAssignment n, (∀ i : Fin
    m, β (rAnc i) = 0) → basisKet (f β) = (rAct.embedUnitary u).1.mulVec (basisKet β)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rAnc u d := by
  let P₀ := rAnc.basisOutcomeProjector 0
  have hProjMul : c.eval.1 * P₀ = (rAct.embedUnitary u).1 * P₀ := by
    apply matrix_ext_basisKet
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with hz
    · rw [hEquiv.perm β, hAction β hz]
    · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hProjConj : P₀ * c.eval.1ᴴ = P₀ * (rAct.embedUnitary u).1ᴴ := by
    have h1 := congrArg Matrix.conjTranspose hProjMul
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      QRegister.basisOutcomeProjector_conjTranspose] at h1
    exact h1
  intro M
  obtain ⟨M', hM'⟩ := hEquiv.storeClosed M
  refine ⟨M', hM', ?_⟩
  have hEq0 := congrArg (fun X ↦ (X (fun _ ↦ 0)).1) (hEquiv.wp_eq (fun _ ↦ M) (fun _ _ ↦ rfl))
  rw [hM'] at hEq0
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      HermitianMat.conj_conj] at hEq0
  rw [hProjConj] at hEq0
  have hHerm : (HermitianMat.conj (rAnc.basisOutcomeProjector 0)) M'.1 =
      (HermitianMat.conj (rAnc.basisOutcomeProjector 0))
      ((HermitianMat.conj (rAct.embedUnitary u).1ᴴ) M.1) := by
    rw [hEq0, HermitianMat.conj_conj]
  have hMat := congrArg
    (fun H : HermitianMat (Fin (2 ^ n)) ℂ ↦ (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) hHerm
  simpa [HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.mul_assoc] using hMat
theorem localClassicalPerm_X {n : ℕ} {S : Finset (Wire n)} (w : Wire n) (hwS : w ∈ S) :
    LocalClassicalPerm S (Circuit.X w) (fun β ↦ Function.update β w (β w + 1)) :=
  { perm := fun β ↦ evolve_X_basisKet w β
    support_sub := support_X_sub hwS
    preserves_outside := fun β z hz ↦
      Function.update_of_ne (fun h ↦ hz (by rw [h]; exact hwS)) _ _
    depends_on := fun _ _ hβ z hz ↦ by
      by_cases hzw : z = w
      · subst hzw; simp [hβ z hz]
      · simp [Function.update_of_ne hzw, hβ z hz] }
theorem zmod2_x_self_cancel {n : ℕ} (w : Wire n) (β : BitAssignment n) :
    let f := fun γ : BitAssignment n ↦ Function.update γ w (γ w + 1)
    f (f β) = β := by
  intro f; funext z; dsimp only [f]
  by_cases h : z = w
  · subst h
    have h1 : ∀ a : ZMod 2, a + 1 + 1 = a := by decide
    simp [h1]
  · simp [Function.update_of_ne h]
def carrySymStep {n : ℕ} (x y c anc : Wire n) (hxy : x ≠ y) (hxc : x ≠ c) (hxa : x ≠ anc)
    (hyc : y ≠ c) (hya : y ≠ anc) (hca : c ≠ anc) : SymTempAndStep n :=
  let S : Finset (Wire n) := {x, y, c, anc}
  let hxS : x ∈ S := by simp [S]
  let hyS : y ∈ S := by simp [S]
  let hcS : c ∈ S := by simp [S]
  let haS : anc ∈ S := by simp [S]
  let hc_x := LocalClassicalPerm.CNOT (S := S) c x hxc.symm hcS hxS
  let hc_y := LocalClassicalPerm.CNOT (S := S) c y hyc.symm hcS hyS
  let hc_a := LocalClassicalPerm.CNOT (S := S) c anc hca hcS haS
  { pre := Circuit.CNOT c x hxc.symm ;;ᶜ Circuit.CNOT c y hyc.symm
    c₁ := x, c₂ := y, anc := anc, h₁₂ := hxy, h₁a := hxa, h₂a := hya
    midPre := Circuit.CNOT c y hyc.symm ;;ᶜ (Circuit.CNOT c x hxc.symm ;;ᶜ Circuit.CNOT c anc hca)
    midPost := Circuit.CNOT c anc hca ;;ᶜ (Circuit.CNOT c x hxc.symm ;;ᶜ Circuit.CNOT c y hyc.symm)
    post := Circuit.CNOT c y hyc.symm ;;ᶜ Circuit.CNOT c x hxc.symm
    S := S, f_pre := _, f_midPre := _, f_midPost := _, f_post := _
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := hc_x.seq hc_y, local_post := hc_y.seq hc_x
    local_midPre := hc_y.seq (hc_x.seq hc_a), local_midPost := hc_a.seq (hc_x.seq hc_y)
    post_pre_id := LocalClassicalPerm.comp_self_inv₂ _ _
      (LocalClassicalPerm.cnot_self_cancel c x hxc.symm)
      (LocalClassicalPerm.cnot_self_cancel c y hyc.symm)
    midPost_midPre_id := LocalClassicalPerm.comp_self_inv₃ _ _ _
      (LocalClassicalPerm.cnot_self_cancel c y hyc.symm)
      (LocalClassicalPerm.cnot_self_cancel c x hxc.symm)
      (LocalClassicalPerm.cnot_self_cancel c anc hca)
    c₁_mem := hxS, c₂_mem := hyS, anc_mem := haS
    anc_not_mem_pre := by
      simp [Circuit.support_seq, Circuit.support_gate, QRegister.image_pair,
        hxa.symm, hya.symm, hca.symm] }
theorem carrySymStep_stepFwd {n : ℕ} (x y c anc : Wire n) (hxy : x ≠ y) (hxc : x ≠ c)
    (hxa : x ≠ anc) (hyc : y ≠ c) (hya : y ≠ anc) (hca : c ≠ anc) (β : BitAssignment n)
    (hβ_anc : β anc = 0) : (carrySymStep x y c anc hxy hxc hxa hyc hya hca).stepFwd β =
    Function.update β anc (β c + (β x + β c) * (β y + β c)) := by
  have hcancel : ∀ (a d : ZMod 2), a + d + d = a := by decide
  funext w
  unfold SymTempAndStep.stepFwd carrySymStep
  dsimp only [Function.comp_apply]
  by_cases hwa : w = anc
  · subst hwa
    simp only [Function.update_self, Function.update_of_ne hxy, Function.update_of_ne hxy.symm,
      Function.update_of_ne hxc.symm, Function.update_of_ne hxa, Function.update_of_ne hxa.symm,
      Function.update_of_ne hyc.symm, Function.update_of_ne hya, Function.update_of_ne hya.symm,
      Function.update_of_ne hca, hβ_anc]
    ring
  · by_cases hwxy : w = x ∨ w = y
    · rcases hwxy with rfl | rfl <;>
        simp only [Function.update_self, Function.update_of_ne hxy, Function.update_of_ne hxy.symm,
          Function.update_of_ne hxc.symm, Function.update_of_ne hxa, Function.update_of_ne hxa.symm,
          Function.update_of_ne hyc.symm, Function.update_of_ne hya, Function.update_of_ne hya.symm,
          Function.update_of_ne hca, hcancel]
    · simp only [Function.update_of_ne hwa, Function.update_of_ne (not_or.mp hwxy).1,
        Function.update_of_ne (not_or.mp hwxy).2]
def withSymBank {Var : Type} {n : ℕ} (v : Var) :
    (m : ℕ) → (Fin m → SymTempAndStep n) → DynamicCircuit Var n → DynamicCircuit Var n
  | 0, _, dInner => dInner
  | m + 1, steps, dInner =>
      (steps 0).toTempAndStep.wrapDynamic v
        (withSymBank v m (fun i ↦ steps i.succ) dInner)
def withSymBankCircuit {n : ℕ} :
    (m : ℕ) → (Fin m → SymTempAndStep n) → Circuit n → Circuit n
  | 0, _, cInner => cInner
  | m + 1, steps, cInner =>
      (steps 0).toTempAndStep.wrapCircuit
        (withSymBankCircuit m (fun i ↦ steps i.succ) cInner)
def bankFwd {n : ℕ} :
    (m : ℕ) → (Fin m → SymTempAndStep n) → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, steps, β => bankFwd m (fun i ↦ steps i.succ) ((steps 0).stepFwd β)
@[simp] theorem count_withSymBank_toff {Var : Type} {n : ℕ} (v : Var) :
    ∀ (m : ℕ) (steps : Fin m → SymTempAndStep n) (dInner : DynamicCircuit Var n),
      (∀ i, (steps i).toTempAndStep.IsCliffordWrapper) →
      (withSymBank v m steps dInner).count .TOFF = dInner.count .TOFF
  | 0, _, _, _ => rfl
  | m + 1, steps, dInner, hcl => by
      unfold withSymBank
      rw [TempAndStep.count_wrapDynamic_toff v _ _ (hcl 0),
        count_withSymBank_toff v m _ dInner (fun i ↦ hcl i.succ)]
@[simp] theorem count_withSymBank_t {Var : Type} {n : ℕ} (v : Var) :
    ∀ (m : ℕ) (steps : Fin m → SymTempAndStep n) (dInner : DynamicCircuit Var n),
      (∀ i, (steps i).toTempAndStep.IsCliffordWrapper) →
      (withSymBank v m steps dInner).count .T = 4 * m + dInner.count .T
  | 0, _, _, _ => by simp [withSymBank]
  | m + 1, steps, dInner, hcl => by
      unfold withSymBank
      rw [TempAndStep.count_wrapDynamic_t v _ _ (hcl 0),
        count_withSymBank_t v m _ dInner (fun i ↦ hcl i.succ)]
      ring
theorem CleanPermEquiv.withSymBank {Var : Type} [Fintype Var] [DecidableEq Var] {mc n : ℕ}
    [NeZero (2 ^ n)] (v : Var) : ∀ (m : ℕ) (steps : Fin m → SymTempAndStep n)
    (rAnc : QRegister m n) (rC : QRegister mc n) (hDisjAC : rAnc.DisjointWires rC)
    {M_set : Finset (Wire n)} {dInner : DynamicCircuit Var n} {cInner : Circuit n}
    {fInner : BitAssignment n → BitAssignment n}, (∀ i, (steps i).anc = rAnc i) →
    (∀ i, Disjoint (steps i).S M_set) → (∀ i, Disjoint (steps i).S rC.image) →
    (∀ i j : Fin m, i.val < j.val → rAnc j ∉ (steps i).S) → CleanPermEquiv v rC M_set dInner
    cInner fInner → CleanPermEquiv v (rAnc.concat rC hDisjAC) M_set
    (_root_.QuantumComputation.Specs.StoppingPowerSolution.WindowedSlot2MulKick288.withSymBank v m
      steps dInner)
    (withSymBankCircuit m steps cInner)
    (fun β w ↦ if w ∈ M_set then fInner (bankFwd m steps β) w else β w) := by
  intro m
  induction m with
  | zero =>
      intro steps rAnc rC hDisjAC M_set dInner cInner fInner _ _ _ _ hInner
      have hImgEq : (rAnc.concat rC hDisjAC).image = rC.image := by
        ext w
        simp only [QRegExt.image_concat, Finset.mem_union, QRegister.mem_image]
        exact ⟨fun h ↦ h.elim (fun ⟨i, _⟩ ↦ Fin.elim0 i) id, Or.inr⟩
      have hF : (fun β w ↦ if w ∈ M_set then fInner β w else β w) = fInner := by
        funext β w
        split_ifs with hhw
        · rfl
        · exact (hInner.outside β w hhw).symm
      unfold
        _root_.QuantumComputation.Specs.StoppingPowerSolution.WindowedSlot2MulKick288.withSymBank
        withSymBankCircuit bankFwd
      rw [hF]
      exact { varIndep := hInner.varIndep, storeClosed := hInner.storeClosed, perm := hInner.perm
              outside := hInner.outside
              wp_eq := fun Θ hΘ ↦
                restrictAssertionToZeroAncilla_eq_of_image_eq hImgEq.symm (hInner.wp_eq Θ hΘ) }
  | succ m ih =>
      intro steps rAnc rC hDisjAC M_set dInner cInner fInner hAnc hDisjM hDisjC hOrder hInner
      let rAncTail : QRegister m n := rAnc.slice 1 m (by omega)
      have hDisjTailC : rAncTail.DisjointWires rC :=
        QRegExt.disjointWires_mono_left hDisjAC (QRegister.image_compose_subset rAnc _)
      have hTailApply : ∀ j : Fin m, rAncTail j = rAnc j.succ := fun j ↦
        (rAnc.slice_apply 1 m _ j).trans (congrArg rAnc (Fin.ext (Nat.add_comm 1 j.val)))
      have hIH := ih (fun i ↦ steps i.succ) rAncTail rC hDisjTailC
        (fun i ↦ (hAnc i.succ).trans (hTailApply i).symm) (fun i ↦ hDisjM i.succ)
        (fun i ↦ hDisjC i.succ)
        (fun i j hij ↦ hTailApply j ▸ hOrder i.succ j.succ (Nat.succ_lt_succ hij)) hInner
      let rTotRaw := rAnc.concat rC hDisjAC
      let eCongr : Fin ((m + mc) + 1) ≃ Fin (m + 1 + mc) := finCongr (by omega)
      let rTot : QRegister ((m + mc) + 1) n := ⟨⟨fun idx ↦ rTotRaw (eCongr idx), fun a b hab ↦
        eCongr.injective (rTotRaw.wires.injective hab)⟩⟩
      let rRest := rTot.slice 1 (m + mc) (by omega)
      have hTotImg : rTot.image = rTotRaw.image := by
        ext w
        simp only [QRegister.mem_image]
        exact eCongr.exists_congr_left
      have hHead : (steps 0).anc = rTot 0 :=
        (hAnc 0).trans ((QRegister.concat_apply_left rAnc rC hDisjAC 0).symm.trans
          (congrArg rTotRaw (Fin.ext rfl)))
      have hrRestEq : rRest = rAncTail.concat rC hDisjTailC :=
        QRegister.ext (Function.Embedding.ext fun q ↦ by
          have hrA : rRest q = rTotRaw ⟨1 + q.val, by omega⟩ :=
            (rTot.slice_apply 1 (m + mc) _ q).trans (congrArg rTotRaw (Fin.ext rfl))
          rw [hrA]
          by_cases hqm : q.val < m
          · conv_lhs =>
              rw [show (⟨1 + q.val, by omega⟩ : Fin (m + 1 + mc)) =
                Fin.castAdd mc ⟨1 + q.val, by omega⟩ from Fin.ext rfl, QRegister.concat_apply_left]
            conv_rhs =>
              rw [show q = Fin.castAdd mc ⟨q.val, hqm⟩ from Fin.ext rfl,
                QRegister.concat_apply_left, hTailApply]
            exact congrArg rAnc (Fin.ext (Nat.add_comm 1 q.val))
          · conv_lhs =>
              rw [show (⟨1 + q.val, by omega⟩ : Fin (m + 1 + mc)) = Fin.natAdd (m + 1)
                ⟨q.val - m, by omega⟩ from Fin.ext (by
                  change 1 + q.val = (m + 1) + (q.val - m)
                  omega), QRegister.concat_apply_right]
            conv_rhs =>
              rw [show q = Fin.natAdd m ⟨q.val - m, by omega⟩ from Fin.ext (by
                change q.val = m + (q.val - m)
                omega), QRegister.concat_apply_right])
      have hImgRest : rRest.image = (rAncTail.concat rC hDisjTailC).image :=
        congrArg QRegister.image hrRestEq
      have hDisjRest : Disjoint (steps 0).S rRest.image := by
        rw [hImgRest, QRegExt.image_concat, Finset.disjoint_union_right]
        refine ⟨Finset.disjoint_right.mpr fun w hw ↦ ?_, hDisjC 0⟩
        obtain ⟨j, rfl⟩ := (QRegister.mem_image rAncTail w).mp hw
        exact hTailApply j ▸ hOrder 0 j.succ (Nat.succ_pos j.val)
      obtain ⟨hWrapPerm, hWrapOut, hWrapWp⟩ := SymTempAndStep.wrap_correct
        v (steps 0) (hDisjM 0) _ _ _ rTot hHead hDisjRest hIH.perm hIH.outside
        (fun Ψ hΨ ↦ restrictAssertionToZeroAncilla_eq_of_image_eq hImgRest.symm (hIH.wp_eq Ψ hΨ))
      have hFunEq : (fun β w ↦ if w ∈ M_set then (if w ∈ M_set then fInner (bankFwd m (fun i ↦
          steps i.succ) ((steps 0).stepFwd β)) w else (steps 0).stepFwd β w) else β w) =
          (fun β w ↦ if w ∈ M_set then fInner (bankFwd (m + 1) steps β) w else β w) :=
        funext fun β ↦ funext fun w ↦ by by_cases hw : w ∈ M_set <;> simp [hw, bankFwd]
      unfold
        _root_.QuantumComputation.Specs.StoppingPowerSolution.WindowedSlot2MulKick288.withSymBank
        withSymBankCircuit
      rw [hFunEq] at hWrapPerm hWrapOut
      exact { varIndep := preservesVarIndep_wrapDynamic v _ hIH.varIndep
              storeClosed := storeClosed_wrapDynamic v _ hIH.storeClosed
              perm := hWrapPerm, outside := hWrapOut
              wp_eq := fun Θ hΘ ↦
                restrictAssertionToZeroAncilla_eq_of_image_eq hTotImg (hWrapWp Θ hΘ) }
attribute [local irreducible] withSymBank withSymBankCircuit
def cnotFanoutCircuit {n : ℕ} :
    (m : ℕ) → (wNeg : Wire n) → (rT : QRegister m n) → (wNeg ∉ rT.image) → Circuit n
  | 0, _, _, _ => .identity
  | m + 1, wNeg, rT, hwNeg =>
      Circuit.CNOT wNeg (rT 0) (fun h ↦ hwNeg ((QRegister.mem_image rT wNeg).mpr ⟨0, h.symm⟩)) ;;ᶜ
        cnotFanoutCircuit m wNeg (rT.slice 1 m (by omega))
          (fun hm_in ↦ hwNeg (QRegister.image_compose_subset rT _ hm_in))
@[simp] theorem count_cnotFanoutCircuit_toff {n : ℕ} :
    ∀ (m : ℕ) (wNeg : Wire n) (rT : QRegister m n) (hwNeg : wNeg ∉ rT.image),
      (cnotFanoutCircuit m wNeg rT hwNeg).count .TOFF = 0
  | 0, _, _, _ => rfl
  | m + 1, wNeg, rT, hwNeg => by
      simp [cnotFanoutCircuit, count_cnotFanoutCircuit_toff m]
@[simp] theorem count_cnotFanoutCircuit_t {n : ℕ} :
    ∀ (m : ℕ) (wNeg : Wire n) (rT : QRegister m n) (hwNeg : wNeg ∉ rT.image),
      (cnotFanoutCircuit m wNeg rT hwNeg).count .T = 0
  | 0, _, _, _ => rfl
  | m + 1, wNeg, rT, hwNeg => by
      simp [cnotFanoutCircuit, count_cnotFanoutCircuit_t m]
def fanoutToggleFn {m n : ℕ} (wNeg : Wire n) (rT : QRegister m n) (β : BitAssignment n) :
    BitAssignment n := fun w ↦ if w ∈ rT.image then β w + β wNeg else β w
theorem fanoutToggleFn_of_mem {m n : ℕ} (wNeg : Wire n) (rT : QRegister m n)
    (β : BitAssignment n) {w : Wire n} (hw : w ∈ rT.image) :
    fanoutToggleFn wNeg rT β w = β w + β wNeg := by
  simp [fanoutToggleFn, hw]
theorem fanoutToggleFn_of_not_mem {m n : ℕ} (wNeg : Wire n) (rT : QRegister m n)
    (β : BitAssignment n) {w : Wire n} (hw : w ∉ rT.image) :
    fanoutToggleFn wNeg rT β w = β w := by
  simp [fanoutToggleFn, hw]
theorem localClassicalPerm_cnotFanout {n : ℕ} : ∀ (m : ℕ) (wNeg : Wire n) (rT : QRegister m n)
    (hwNeg : wNeg ∉ rT.image), LocalClassicalPerm (insert wNeg rT.image)
    (cnotFanoutCircuit m wNeg rT hwNeg) (fanoutToggleFn wNeg rT)
  | 0, wNeg, rT, _ => by
      have hEq : fanoutToggleFn wNeg rT = id := funext fun β ↦ funext fun w ↦
        fanoutToggleFn_of_not_mem wNeg rT β fun hm ↦
          Fin.elim0 ((QRegister.mem_image rT w).mp hm).choose
      simpa only [cnotFanoutCircuit, hEq] using LocalClassicalPerm.identity (insert wNeg rT.image)
  | m + 1, wNeg, rT, hwNeg => by
      let rTail := rT.slice 1 m (by omega)
      have hwNegNe0 : wNeg ≠ rT 0 := fun h ↦ hwNeg ((QRegister.mem_image rT wNeg).mpr ⟨0, h.symm⟩)
      have hHead := LocalClassicalPerm.CNOT (S := insert wNeg rT.image) wNeg (rT 0) hwNegNe0
        (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem ((QRegister.mem_image rT _).mpr ⟨0, rfl⟩))
      have hTail := (localClassicalPerm_cnotFanout m wNeg rTail
        (fun hm_in ↦ hwNeg (QRegister.image_compose_subset rT _ hm_in))).mono
        (Finset.insert_subset_insert wNeg (QRegister.image_compose_subset rT _))
      have hComp := hHead.seq hTail
      have hTailEq : ∀ j : Fin m, rTail j = rT j.succ := fun j ↦
        (rT.slice_apply 1 m _ j).trans (congrArg rT (Fin.ext (Nat.add_comm 1 j.val)))
      have h0NotTail : rT 0 ∉ rTail.image := fun hm_in ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rTail _).mp hm_in
        exact Fin.succ_ne_zero j (rT.wires.injective ((hTailEq j).symm.trans hj))
      have hFunEq : (fanoutToggleFn wNeg rTail ∘ fun β ↦ Function.update β (rT 0) (β (rT 0) +
          β wNeg)) = fanoutToggleFn wNeg rT := funext fun β ↦ funext fun w ↦ by
        dsimp only [Function.comp_apply]
        by_cases hwTail : w ∈ rTail.image
        · rw [fanoutToggleFn_of_mem wNeg rTail _ hwTail,
            fanoutToggleFn_of_mem wNeg rT β (QRegister.image_compose_subset rT _ hwTail),
            Function.update_of_ne (fun h : w = rT 0 ↦ h0NotTail (h ▸ hwTail)),
            Function.update_of_ne hwNegNe0]
        · rw [fanoutToggleFn_of_not_mem wNeg rTail _ hwTail]
          rcases eq_or_ne w (rT 0) with rfl | hw0
          · rw [Function.update_self,
              fanoutToggleFn_of_mem wNeg rT β ((QRegister.mem_image rT _).mpr ⟨0, rfl⟩)]
          · rw [Function.update_of_ne hw0, fanoutToggleFn_of_not_mem wNeg rT β fun hm_in ↦ by
              obtain ⟨i, rfl⟩ := (QRegister.mem_image rT _).mp hm_in
              rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
              · exact hw0 rfl
              · exact hwTail ((QRegister.mem_image rTail _).mpr ⟨j, hTailEq j⟩)]
      unfold cnotFanoutCircuit
      rwa [hFunEq] at hComp
attribute [local irreducible] cnotFanoutCircuit
theorem onesComplement_bitsVal {L : ℕ} (γ : BitAssignment L) :
    bitsVal (fun j : Fin L ↦ γ j + 1) + bitsVal γ = 2 ^ L - 1 := by
  induction L with
  | zero => simp [bitsVal]
  | succ L ih =>
    have h0 : (γ 0 + 1).val + (γ 0).val = 1 :=
      (show ∀ z : ZMod 2, (z + 1).val + z.val = 1 by decide) (γ 0)
    have hsh : ∀ δ : BitAssignment L, (∑ i : Fin L, (δ i).val * 2 ^ i.succ.val) =
        2 * bitsVal δ := fun δ ↦ by
      rw [bitsVal, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Fin.val_succ, pow_succ]
      ring
    have hih := ih (fun i ↦ γ i.succ)
    have hpos : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by decide)
    unfold bitsVal
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hsh (fun i ↦ γ i.succ + 1), hsh (fun i ↦ γ i.succ),
      pow_succ]
    simp only [Fin.val_zero, _root_.pow_zero, mul_one]
    omega
theorem regVal_split_at_shift {s L B n : ℕ} (hs : s + L = B)
    (rPG : QRegister B n) (β : BitAssignment n) :
    regVal rPG β = bitsVal (fun i : Fin s ↦ β (rPG ⟨i.val, by omega⟩)) +
      2 ^ s * regVal (rPG.slice s L (by omega)) β := by
  subst hs
  unfold regVal bitsVal
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  have hr : (rPG.slice s L (by omega)) j = rPG (Fin.natAdd s j) :=
    congrArg rPG (Fin.ext (by
      dsimp [QRegister.slice, QRegister.slice_apply,
        WindowedSlot2MulKick288Alt.qreg_slice_wires,
        WindowedSlot2MulKick288Alt.qreg_whole_wires,
        WindowedSlot2MulKick288Alt.emb_trans_apply,
        WindowedSlot2MulKick288Alt.emb_refl_apply,
        WindowedSlot2MulKick288Alt.emb_mk_apply, QRegister.compose,
        QRegister.compose_apply, WindowedSlot2MulKick288Alt.qreg_compose_wires,
        WindowedSlot2MulKick288Alt.qreg_block_apply,
        WindowedSlot2MulKick288Alt.qreg_block_wires_apply]))
  rw [hr, Fin.val_natAdd, pow_add]
  ring
theorem classicalPerm_seq {n : ℕ} [NeZero (2 ^ n)]
    {c₁ c₂ : Circuit n} {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : ClassicalPerm c₁ f₁) (h₂ : ClassicalPerm c₂ f₂) :
    ClassicalPerm (c₁ ;;ᶜ c₂) (f₂ ∘ f₁) :=
  fun β ↦ by
    rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁ β, Function.comp_apply,
      h₂ (f₁ β)]
set_option maxRecDepth 512
end ConfigWindowedSlot2MulKick288
end WindowedSlot2MulKick288
end
end ModWindowedSlot2MulKick288

section ModUltraLeanProjPlus512Vep
@[expose] public section
namespace UltraLeanProjPlus512Vep
section ConfigUltraLeanProjPlus512Vep
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open DyadicQft64WalkCircuit hiding wSlot2
open FullSysCatSegmentBridge
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288
open WindowedSlot2MulKick288
local instance (priority := 1000000) instNeZeroTwoPowUltraVep (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
@[simp] theorem count_withSymBank_toff_fast {Var : Type} {n : ℕ} (v : Var) (m : ℕ)
    (steps : Fin m → SymTempAndStep n) (dInner : DynamicCircuit Var n) :
    (withSymBank v m steps dInner).count .TOFF = dInner.count .TOFF :=
  count_withSymBank_toff v m steps dInner (fun i ↦ (steps i).clifford)
@[simp] theorem count_withSymBank_t_fast {Var : Type} {n : ℕ} (v : Var) (m : ℕ)
    (steps : Fin m → SymTempAndStep n) (dInner : DynamicCircuit Var n) :
    (withSymBank v m steps dInner).count .T = 4 * m + dInner.count .T :=
  count_withSymBank_t v m steps dInner (fun i ↦ (steps i).clifford)
def optX {n : ℕ} (b : Bool) (w : Wire n) : Circuit n :=
  if b then Circuit.X w else Circuit.identity
def optXFn {n : ℕ} (b : Bool) (w : Wire n) (β : BitAssignment n) : BitAssignment n :=
  Function.update β w (β w + if b then 1 else 0)
theorem localClassicalPerm_optX {n : ℕ} {S : Finset (Wire n)} (b : Bool) (w : Wire n)
    (hw : w ∈ S) : LocalClassicalPerm S (optX b w) (optXFn b w) := by
  cases b
  · have hid : optXFn false w = id := funext fun β ↦ by
      simp only [optXFn, Bool.false_eq_true, ↓reduceIte, add_zero, Function.update_eq_self, id_eq]
    simp only [optX, Bool.false_eq_true, ↓reduceIte]
    rw [hid]
    exact LocalClassicalPerm.identity S
  · have hid : optXFn true w = fun β ↦ Function.update β w (β w + 1) := funext fun β ↦ by
      simp only [optXFn, ↓reduceIte]
    simp only [optX, ↓reduceIte]
    rw [hid]
    exact WindowedSlot2MulKick288.localClassicalPerm_X w hw
theorem optXFn_self_cancel {n : ℕ} (b : Bool) (w : Wire n) (β : BitAssignment n) :
    optXFn b w (optXFn b w β) = β := by
  cases b
  · simp only [optXFn, Bool.false_eq_true, ↓reduceIte, add_zero, Function.update_eq_self]
  · change Function.update (Function.update β w (β w + 1)) w
        (Function.update β w (β w + 1) w + 1) = β
    exact zmod2_x_self_cancel w β
theorem optX_not_mem_support {n : ℕ} (b : Bool) {w u : Wire n} (hne : u ≠ w) :
    u ∉ (optX b w).support := by
  cases b
  · simp only [optX, Bool.false_eq_true, ↓reduceIte, Circuit.support_identity,
      Finset.notMem_empty, not_false_eq_true]
  · intro hm
    simp only [optX, ↓reduceIte] at hm
    exact hne (Finset.mem_singleton.mp (support_X_sub (Finset.mem_singleton_self w) hm))
def genBoolSymStep {n : ℕ} (neg1 neg2 negOut : Bool) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : SymTempAndStep n :=
  let S : Finset (Wire n) := {c₁, c₂, anc}
  let h1S : c₁ ∈ S := by simp [S]
  let h2S : c₂ ∈ S := by simp [S]
  let haS : anc ∈ S := by simp [S]
  let lp1 := localClassicalPerm_optX neg1 c₁ h1S
  let lp2 := localClassicalPerm_optX neg2 c₂ h2S
  let lpa := localClassicalPerm_optX negOut anc haS
  { pre := optX neg1 c₁ ;;ᶜ optX neg2 c₂
    c₁ := c₁, c₂ := c₂, anc := anc, h₁₂ := h₁₂, h₁a := h₁a, h₂a := h₂a
    midPre := optX neg2 c₂ ;;ᶜ (optX neg1 c₁ ;;ᶜ optX negOut anc)
    midPost := optX negOut anc ;;ᶜ (optX neg1 c₁ ;;ᶜ optX neg2 c₂)
    post := optX neg2 c₂ ;;ᶜ optX neg1 c₁
    S := S, f_pre := _, f_midPre := _, f_midPost := _, f_post := _
    clifford := by
      cases neg1 <;> cases neg2 <;> cases negOut <;>
        simp [optX, TempAndStep.IsCliffordWrapper, Circuit.X]
    local_pre := lp1.seq lp2, local_post := lp2.seq lp1
    local_midPre := lp2.seq (lp1.seq lpa), local_midPost := lpa.seq (lp1.seq lp2)
    post_pre_id := LocalClassicalPerm.comp_self_inv₂ _ _
      (optXFn_self_cancel neg1 c₁) (optXFn_self_cancel neg2 c₂)
    midPost_midPre_id := LocalClassicalPerm.comp_self_inv₃ _ _ _
      (optXFn_self_cancel neg2 c₂) (optXFn_self_cancel neg1 c₁) (optXFn_self_cancel negOut anc)
    c₁_mem := h1S, c₂_mem := h2S, anc_mem := haS
    anc_not_mem_pre := fun hm ↦
      (Finset.mem_union.mp (Circuit.support_seq _ _ ▸ hm)).elim
        (optX_not_mem_support neg1 h₁a.symm) (optX_not_mem_support neg2 h₂a.symm) }
theorem genBoolSymStep_stepFwd {n : ℕ} (neg1 neg2 negOut : Bool) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (β : BitAssignment n)
    (hβ_anc : β anc = 0) : (genBoolSymStep neg1 neg2 negOut c₁ c₂ anc h₁₂ h₁a h₂a).stepFwd β =
    Function.update β anc ((if negOut then 1 else 0) + (β c₁ + if neg1 then 1 else 0) * (β c₂
    + if neg2 then 1 else 0)) := by
  have hcancel : ∀ (a d : ZMod 2), a + d + d = a := by decide
  funext w
  unfold SymTempAndStep.stepFwd genBoolSymStep
  dsimp only [Function.comp_apply, optXFn]
  by_cases hwa : w = anc
  · subst hwa
    simp only [Function.update_self, Function.update_of_ne h₁a.symm, Function.update_of_ne h₂a.symm,
      Function.update_of_ne h₁₂, Function.update_of_ne h₁₂.symm, hβ_anc]
    ring
  · by_cases hw12 : w = c₁ ∨ w = c₂
    · rcases hw12 with rfl | rfl <;>
        simp only [Function.update_of_ne hwa, Function.update_of_ne h₁₂,
          Function.update_of_ne h₁₂.symm, Function.update_self, hcancel]
    · simp only [Function.update_of_ne hwa, Function.update_of_ne (not_or.mp hw12).1,
        Function.update_of_ne (not_or.mp hw12).2]
def andSymStep {n : ℕ} (x y anc : Wire n) (hxy : x ≠ y) (hxa : x ≠ anc) (hya : y ≠ anc) :
    SymTempAndStep n := genBoolSymStep false false false x y anc hxy hxa hya
theorem andSymStep_stepFwd {n : ℕ} (x y anc : Wire n) (hxy : x ≠ y) (hxa : x ≠ anc)
    (hya : y ≠ anc) (β : BitAssignment n) (hβ_anc : β anc = 0) :
    (andSymStep x y anc hxy hxa hya).stepFwd β = Function.update β anc (β x * β y) := by
  simpa [andSymStep] using
    genBoolSymStep_stepFwd false false false x y anc hxy hxa hya β hβ_anc
theorem bankFwd_apply_eq {n : ℕ} :
    ∀ (m : ℕ) (steps : Fin m → SymTempAndStep n) (rAnc : QRegister m n)
      (β : BitAssignment n) (target : Fin m → ZMod 2),
      (∀ i : Fin m, β (rAnc i) = 0) →
      (∀ (i : Fin m) (γ : BitAssignment n),
        (∀ w, w ∉ rAnc.image → γ w = β w) →
        (∀ k : Fin m, k.val < i.val → γ (rAnc k) = target k) →
        γ (rAnc i) = 0 →
        (steps i).stepFwd γ = Function.update γ (rAnc i) (target i)) →
      (∀ w, w ∉ rAnc.image → bankFwd m steps β w = β w) ∧
      (∀ i : Fin m, bankFwd m steps β (rAnc i) = target i)
  | 0, _, _, _, _, _, _ => ⟨fun _ _ ↦ rfl, fun i ↦ Fin.elim0 i⟩
  | m + 1, steps, rAnc, β, target, hZero, hStep => by
      let β₁ := (steps 0).stepFwd β
      have hβ₁ : β₁ = Function.update β (rAnc 0) (target 0) :=
        hStep 0 β (fun _ _ ↦ rfl) (fun _ hk ↦ absurd hk (Nat.not_lt_zero _)) (hZero 0)
      let rTail := rAnc.slice 1 m (by omega)
      have hTailEq : ∀ j : Fin m, rTail j = rAnc j.succ := fun j ↦
        (rAnc.slice_apply 1 m _ j).trans (congrArg rAnc (Fin.ext (Nat.add_comm 1 j.val)))
      have h0NotTail : rAnc 0 ∉ rTail.image := by
        intro hm_in
        obtain ⟨j, hj⟩ := (QRegister.mem_image rTail _).mp hm_in
        rw [hTailEq j] at hj
        exact Fin.succ_ne_zero j (rAnc.wires.injective hj)
      have hZero₁ : ∀ j : Fin m, β₁ (rTail j) = 0 := fun j ↦ by
        rw [hTailEq j, hβ₁,
          Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (rAnc.wires.injective h))]
        exact hZero j.succ
      have hStep₁ : ∀ (j : Fin m) (γ : BitAssignment n), (∀ w, w ∉ rTail.image → γ w = β₁ w) →
          (∀ k : Fin m, k.val < j.val → γ (rTail k) = target k.succ) → γ (rTail j) = 0 →
          (steps j.succ).stepFwd γ = Function.update γ (rTail j) (target j.succ) := by
        intro j γ hOutγ hPrevγ hZγ
        rw [hTailEq j] at hZγ ⊢
        refine hStep j.succ γ (fun w hw ↦ ?_) (fun k hk ↦ ?_) hZγ
        · have hwTail : w ∉ rTail.image :=
            fun hm_in ↦ hw (QRegister.image_compose_subset rAnc _ hm_in)
          have hwNe0 : w ≠ rAnc 0 :=
            fun h ↦ hw (h ▸ (QRegister.mem_image rAnc _).mpr ⟨0, rfl⟩)
          rw [hOutγ w hwTail, hβ₁, Function.update_of_ne hwNe0]
        · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
          · rw [hOutγ (rAnc 0) h0NotTail, hβ₁, Function.update_self]
          · rw [← hTailEq k']
            exact hPrevγ k' (Nat.lt_of_succ_lt_succ hk)
      obtain ⟨hIHOut, hIHTarget⟩ :=
        bankFwd_apply_eq m (fun j ↦ steps j.succ) rTail β₁ (fun j ↦ target j.succ) hZero₁ hStep₁
      unfold bankFwd
      refine ⟨fun w hw ↦ ?_, fun i ↦ ?_⟩
      · have hwTail : w ∉ rTail.image :=
          fun hm_in ↦ hw (QRegister.image_compose_subset rAnc _ hm_in)
        have hwNe0 : w ≠ rAnc 0 := fun h ↦ hw (h ▸ (QRegister.mem_image rAnc _).mpr ⟨0, rfl⟩)
        rw [hIHOut w hwTail, hβ₁, Function.update_of_ne hwNe0]
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · rw [hIHOut (rAnc 0) h0NotTail, hβ₁, Function.update_self]
        · rw [← hTailEq j]
          exact hIHTarget j
def cnotPairCircuit {n : ℕ} :
    (m : ℕ) → (rSrc rDst : QRegister m n) → (rSrc.DisjointWires rDst) → Circuit n
  | 0, _, _, _ => .identity
  | m + 1, rSrc, rDst, hSD =>
      Circuit.CNOT (rSrc 0) (rDst 0) (QRegister.DisjointWires.ne hSD 0 0) ;;ᶜ
        cnotPairCircuit m (rSrc.slice 1 m (by omega)) (rDst.slice 1 m (by omega))
          (QRegExt.disjointWires_mono_left
            (QRegExt.disjointWires_mono_right hSD (rDst.image_compose_subset _))
            (rSrc.image_compose_subset _))
@[simp] theorem count_cnotPairCircuit_toff {n : ℕ} :
    ∀ (m : ℕ) (rSrc rDst : QRegister m n) (hSD : rSrc.DisjointWires rDst),
      (cnotPairCircuit m rSrc rDst hSD).count .TOFF = 0
  | 0, _, _, _ => rfl
  | m + 1, _, _, _ => by simp [cnotPairCircuit, count_cnotPairCircuit_toff m]
@[simp] theorem count_cnotPairCircuit_t {n : ℕ} :
    ∀ (m : ℕ) (rSrc rDst : QRegister m n) (hSD : rSrc.DisjointWires rDst),
      (cnotPairCircuit m rSrc rDst hSD).count .T = 0
  | 0, _, _, _ => rfl
  | m + 1, _, _, _ => by simp [cnotPairCircuit, count_cnotPairCircuit_t m]
noncomputable def cnotPairFn {m n : ℕ} (rSrc rDst : QRegister m n) (β : BitAssignment n) :
    BitAssignment n :=
  fun u ↦
    if hu : u ∈ rDst.image then
      let j := Classical.choose ((QRegister.mem_image rDst u).mp hu)
      β (rDst j) + β (rSrc j)
    else β u
theorem classicalPerm_cnotPairCircuit {n : ℕ} [NeZero (2 ^ n)] :
    ∀ (m : ℕ) (rSrc rDst : QRegister m n) (hSD : rSrc.DisjointWires rDst),
      ClassicalPerm (cnotPairCircuit m rSrc rDst hSD) (cnotPairFn rSrc rDst)
  | 0, rSrc, rDst, _ => fun β ↦ by
      have hid : cnotPairFn rSrc rDst β = β := funext fun u ↦ by
        have hn : u ∉ rDst.image := fun hm_in ↦ by
          obtain ⟨j, _⟩ := (QRegister.mem_image rDst u).mp hm_in
          exact Fin.elim0 j
        simp only [cnotPairFn, hn, ↓reduceDIte]
      have hId := (LocalClassicalPerm.identity (n := n) ∅).perm β
      simpa only [cnotPairCircuit, hid, id_eq] using hId
  | m + 1, rSrc, rDst, hSD => fun β ↦ by
      let rS' := rSrc.slice 1 m (by omega)
      let rD' := rDst.slice 1 m (by omega)
      have hSD' : rS'.DisjointWires rD' := QRegExt.disjointWires_mono_left
        (QRegExt.disjointWires_mono_right hSD (rDst.image_compose_subset _))
        (rSrc.image_compose_subset _)
      have hHead := (LocalClassicalPerm.CNOT (S := Finset.univ) (rSrc 0) (rDst 0)
        (QRegister.DisjointWires.ne hSD 0 0) (Finset.mem_univ _) (Finset.mem_univ _)).perm
      have hTail := classicalPerm_cnotPairCircuit m rS' rD' hSD'
      rw [cnotPairCircuit, classicalPerm_seq hHead hTail β]
      congr 1; funext u
      dsimp only [Function.comp_apply]
      have hkD_eq : ∀ k : Fin m, rD' k = rDst k.succ := fun k ↦
        (rDst.slice_apply 1 m _ k).trans (congrArg rDst (Fin.ext (Nat.add_comm 1 k.val)))
      have hkS_eq : ∀ k : Fin m, rS' k = rSrc k.succ := fun k ↦
        (rSrc.slice_apply 1 m _ k).trans (congrArg rSrc (Fin.ext (Nat.add_comm 1 k.val)))
      by_cases hu' : u ∈ rD'.image
      · obtain ⟨k, rfl⟩ := (QRegister.mem_image rD' u).mp hu'
        have huD : rD' k ∈ rDst.image := QRegister.image_compose_subset rDst _ hu'
        have hch' : Classical.choose ((QRegister.mem_image rD' _).mp hu') = k :=
          rD'.wires.injective (Classical.choose_spec ((QRegister.mem_image rD' _).mp hu'))
        have hchD : Classical.choose ((QRegister.mem_image rDst _).mp huD) = k.succ :=
          rDst.wires.injective ((Classical.choose_spec ((QRegister.mem_image rDst _).mp huD)).trans
            (hkD_eq k))
        rw [cnotPairFn, dite_pos_8 hu', cnotPairFn, dite_pos_8 huD]
        dsimp only
        rw [hch', hchD,
          Function.update_of_ne (fun e ↦
            Fin.succ_ne_zero k (rDst.wires.injective ((hkD_eq k).symm.trans e))),
          Function.update_of_ne (QRegister.DisjointWires.ne hSD k.succ 0 ∘ ((hkS_eq k).symm.trans
            ·)),
          hkD_eq k, hkS_eq k]
      · by_cases hu0 : u = rDst 0
        · subst hu0
          have huD : rDst 0 ∈ rDst.image := (QRegister.mem_image rDst _).mpr ⟨0, rfl⟩
          have hchD : Classical.choose ((QRegister.mem_image rDst _).mp huD) = 0 :=
            rDst.wires.injective (Classical.choose_spec ((QRegister.mem_image rDst _).mp huD))
          simp only [cnotPairFn, hu', huD, ↓reduceDIte, hchD, Function.update_self]
        · have huNotD : u ∉ rDst.image := fun hm_in ↦ by
            obtain ⟨j, rfl⟩ := (QRegister.mem_image rDst u).mp hm_in
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
            · exact hu0 rfl
            · exact hu' ((QRegister.mem_image rD' _).mpr ⟨k, hkD_eq k⟩)
          simp only [cnotPairFn, hu', huNotD, ↓reduceDIte, Function.update_of_ne hu0]
noncomputable def dFlagXor9 {Var : Type} {n : ℕ} (v : Var) (wf : Wire n)
    (uSrc9 : Fin 9 → Wire n) (rTemp9 rDst9 : QRegister 9 n) (hfu : ∀ j, wf ≠ uSrc9 j)
    (hfT : ∀ j, wf ≠ rTemp9 j) (huT : ∀ j, uSrc9 j ≠ rTemp9 j)
    (hTD : rTemp9.DisjointWires rDst9) : DynamicCircuit Var n := withSymBank v 9
    (fun j ↦ andSymStep wf (uSrc9 j) (rTemp9 j) (hfu j) (hfT j) (huT j))
    (.circuit (cnotPairCircuit 9 rTemp9 rDst9 hTD))
theorem dFlagXor9_cleanPermEquiv {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (wf : Wire n) (uSrc9 : Fin 9 → Wire n)
    (rTemp9 rDst9 : QRegister 9 n) (hfu : ∀ j, wf ≠ uSrc9 j) (hfT : ∀ j, wf ≠ rTemp9 j)
    (huT : ∀ j, uSrc9 j ≠ rTemp9 j) (huT_cross : ∀ i j, uSrc9 i ≠ rTemp9 j)
    (hfD : wf ∉ rDst9.image) (huD : ∀ j, uSrc9 j ∉ rDst9.image)
    (hTD : rTemp9.DisjointWires rDst9) :
    ∃ cOut fOut,
      CleanPermEquiv v rTemp9 rDst9.image
        (dFlagXor9 v wf uSrc9 rTemp9 rDst9 hfu hfT huT hTD) cOut fOut ∧
      (∀ β, (∀ j : Fin 9, β (rTemp9 j) = 0) → ∀ u, fOut β u =
        if hu : u ∈ rDst9.image then
          let j := Classical.choose ((QRegister.mem_image rDst9 u).mp hu)
          β (rDst9 j) + β wf * β (uSrc9 j)
        else β u) := by
  let steps : Fin 9 → SymTempAndStep n :=
    fun j ↦ andSymStep wf (uSrc9 j) (rTemp9 j) (hfu j) (hfT j) (huT j)
  let rEmp : QRegister 0 n := rTemp9.slice 0 0 (by decide)
  have hEmpImg : rEmp.image = ∅ := Finset.eq_empty_of_forall_notMem fun w hw ↦
    Fin.elim0 ((QRegister.mem_image rEmp w).mp hw).choose
  have hInner : CleanPermEquiv v rEmp rDst9.image
      (.circuit (cnotPairCircuit 9 rTemp9 rDst9 hTD)) (cnotPairCircuit 9 rTemp9 rDst9 hTD)
      (cnotPairFn rTemp9 rDst9) :=
    { varIndep := preservesVarIndep_circuit v _, storeClosed := storeClosed_circuit _
      perm := classicalPerm_cnotPairCircuit 9 rTemp9 rDst9 hTD
      outside := fun β u hu ↦ by simp only [cnotPairFn, hu, ↓reduceDIte]
      wp_eq := fun Θ _ ↦ congrArg (fun X ↦ CQAssertion.restrictToZeroAncilla X rEmp)
        (DynCircuitExt.wp_circuit_compile_compat (cnotPairCircuit 9 rTemp9 rDst9 hTD) Θ) }
  have hDisjTC : rTemp9.DisjointWires rEmp :=
    QRegExt.disjointWires_of_finset (by simp [hEmpImg])
  have hEq0 := CleanPermEquiv.withSymBank v 9 steps rTemp9 rEmp hDisjTC (fun _ ↦ rfl)
    (fun i ↦ Finset.disjoint_left.mpr fun u huS huIn ↦ by
      simp only [steps, andSymStep, genBoolSymStep, Finset.mem_insert, Finset.mem_singleton] at huS
      rcases huS with rfl | rfl | rfl
      · exact hfD huIn
      · exact huD i huIn
      · exact Finset.disjoint_left.mp
          ((QRegExt.disjointWires_iff_disjoint_image rTemp9 rDst9).mp hTD)
          ((QRegister.mem_image rTemp9 _).mpr ⟨i, rfl⟩) huIn)
    (fun _ ↦ hEmpImg ▸ Finset.disjoint_empty_right _)
    (fun i k hik hm ↦ by
      simp only [steps, andSymStep, genBoolSymStep, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · exact hfT k h.symm
      · exact huT_cross i k h.symm
      · exact (by omega : i.val ≠ k.val) (congrArg Fin.val (rTemp9.wires.injective h.symm)))
    hInner
  have hImg : (rTemp9.concat rEmp hDisjTC).image = rTemp9.image := by
    rw [QRegExt.image_concat, hEmpImg, Finset.union_empty]
  let fOut := fun β u ↦
    if u ∈ rDst9.image then cnotPairFn rTemp9 rDst9 (bankFwd 9 steps β) u else β u
  refine ⟨_, fOut,
    { varIndep := hEq0.varIndep, storeClosed := hEq0.storeClosed
      perm := hEq0.perm, outside := hEq0.outside
      wp_eq := fun Θ hΘ ↦
        NuclearTwistMulKickAndBridge288.restrictAssertionToZeroAncilla_eq_of_image_eq
          hImg (hEq0.wp_eq Θ hΘ) }, fun β hz u ↦ ?_⟩
  have ⟨hBOut, hBVal⟩ := bankFwd_apply_eq 9 steps rTemp9 β (fun j ↦ β wf * β (uSrc9 j)) hz
    fun j γ hOutγ _ hZγ ↦ by
      rw [andSymStep_stepFwd _ _ _ _ _ _ γ hZγ,
        hOutγ wf fun hm ↦ by
          obtain ⟨k, hk⟩ := (QRegister.mem_image rTemp9 _).mp hm
          exact hfT k hk.symm,
        hOutγ _ fun hm ↦ by
          obtain ⟨k, hk⟩ := (QRegister.mem_image rTemp9 _).mp hm
          exact huT_cross j k hk.symm]
  by_cases hu : u ∈ rDst9.image
  · have hDjNot : rDst9 (Classical.choose ((QRegister.mem_image rDst9 u).mp hu)) ∉ rTemp9.image :=
      Finset.disjoint_right.mp ((QRegExt.disjointWires_iff_disjoint_image rTemp9 rDst9).mp hTD)
        ((QRegister.mem_image rDst9 _).mpr ⟨_, rfl⟩)
    simp only [fOut, cnotPairFn, hu, ↓reduceIte, ↓reduceDIte,
      hBOut _ hDjNot, hBVal (Classical.choose ((QRegister.mem_image rDst9 u).mp hu))]
  · simp only [fOut, hu, ↓reduceIte, ↓reduceDIte]
def vepFlagSteps {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rS7 : QRegister 7 n)
    (hCS7 : rCore.DisjointWires rS7) : Fin 7 → SymTempAndStep n :=
  let c2 : Fin (fullSysCoreWires mPayload) := ⟨3950, by rw [fcw_eq_add]; omega⟩
  let c1 : Fin (fullSysCoreWires mPayload) := ⟨3949, by rw [fcw_eq_add]; omega⟩
  let c0 : Fin (fullSysCoreWires mPayload) := ⟨3948, by rw [fcw_eq_add]; omega⟩
  let b3 : Fin (fullSysCoreWires mPayload) := ⟨3963, by rw [fcw_eq_add]; omega⟩
  let b4 : Fin (fullSysCoreWires mPayload) := ⟨3964, by rw [fcw_eq_add]; omega⟩
  let b5 : Fin (fullSysCoreWires mPayload) := ⟨3965, by rw [fcw_eq_add]; omega⟩
  let b6 : Fin (fullSysCoreWires mPayload) := rNucIdx hm (QRegExt.idReg _) 6
  let b7 : Fin (fullSysCoreWires mPayload) := ⟨3967, by rw [fcw_eq_add]; omega⟩
  let hcs : ∀ q i, rCore q ≠ rS7 i := fun q i ↦ QRegister.DisjointWires.ne hCS7 q i
  let hsne : ∀ {i j : Fin 7}, i ≠ j → rS7 i ≠ rS7 j := fun hij h ↦ hij (rS7.wires.injective h)
  fun i ↦
    match i with
    | ⟨0, _⟩ => genBoolSymStep true true false (rCore c2) (rCore c1) (rS7 0)
        (core_wire_ne rCore (by dsimp [c2, c1]; omega)) (hcs _ _) (hcs _ _)
    | ⟨1, _⟩ => genBoolSymStep false true false (rS7 0) (rCore c0) (rS7 1)
        (hcs _ _).symm (hsne (by decide)) (hcs _ _)
    | ⟨2, _⟩ => genBoolSymStep false false false (rCore b4) (rCore b3) (rS7 2)
        (core_wire_ne rCore (by dsimp [b4, b3]; omega)) (hcs _ _) (hcs _ _)
    | ⟨3, _⟩ => genBoolSymStep true true true (rCore b5) (rS7 2) (rS7 3)
        (hcs _ _) (hcs _ _) (hsne (by decide))
    | ⟨4, _⟩ => genBoolSymStep false false false (rCore b7) (rS7 3) (rS7 4)
        (hcs _ _) (hcs _ _) (hsne (by decide))
    | ⟨5, _⟩ => genBoolSymStep false false false (rS7 1) (rS7 4) (rS7 5)
        (hsne (by decide)) (hsne (by decide)) (hsne (by decide))
    | ⟨6, _⟩ => genBoolSymStep false false false (rS7 5) (rCore b6) (rS7 6)
        (hcs _ _).symm (hsne (by decide)) (hcs _ _)
end ConfigUltraLeanProjPlus512Vep
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
end UltraLeanProjPlus512Vep
end
end ModUltraLeanProjPlus512Vep

section ModWindowedSlot2FusedTwist288
@[expose] public section
namespace WindowedSlot2FusedTwist288Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end WindowedSlot2FusedTwist288Alt
namespace WindowedSlot2FusedTwist288
section ConfigWindowedSlot2FusedTwist288
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64WalkCircuit
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
local instance (priority := 1000000) instNeZeroTwoPowSlot2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open WindowedSlot2MulKick288
noncomputable def lockVal {α : Sort _} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem lockVal_eq {α : Sort _} (x : α) : lockVal x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem bit_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide
@[simp] theorem count_withSymBank_toff' {Var : Type} {n : ℕ} (v : Var) (m : ℕ)
    (steps : Fin m → SymTempAndStep n) (dInner : DynamicCircuit Var n) :
    (withSymBank v m steps dInner).count .TOFF = dInner.count .TOFF :=
  count_withSymBank_toff v m steps dInner (fun i ↦ (steps i).clifford)
@[simp] theorem count_withSymBank_t' {Var : Type} {n : ℕ} (v : Var) (m : ℕ)
    (steps : Fin m → SymTempAndStep n) (dInner : DynamicCircuit Var n) :
    (withSymBank v m steps dInner).count .T = 4 * m + dInner.count .T :=
  count_withSymBank_t v m steps dInner (fun i ↦ (steps i).clifford)
def andSymStep {n : ℕ} (x y anc : Wire n)
    (hxy : x ≠ y) (hxa : x ≠ anc) (hya : y ≠ anc) : SymTempAndStep n :=
  let sWires : Finset (Wire n) := {x, y, anc}
  { pre := Circuit.identity, c₁ := x, c₂ := y, anc := anc, h₁₂ := hxy, h₁a := hxa, h₂a := hya
    midPre := Circuit.identity, midPost := Circuit.identity, post := Circuit.identity
    S := sWires, f_pre := _, f_midPre := _, f_midPost := _, f_post := _
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := LocalClassicalPerm.identity sWires
    local_post := LocalClassicalPerm.identity sWires
    local_midPre := LocalClassicalPerm.identity sWires
    local_midPost := LocalClassicalPerm.identity sWires
    post_pre_id := fun _ ↦ rfl, midPost_midPre_id := fun _ ↦ rfl
    c₁_mem := by simp [sWires], c₂_mem := by simp [sWires], anc_mem := by simp [sWires]
    anc_not_mem_pre := by simp }
theorem andSymStep_stepFwd {n : ℕ} (x y anc : Wire n) (hxy : x ≠ y) (hxa : x ≠ anc)
    (hya : y ≠ anc) (β : BitAssignment n) (hβ_anc : β anc = 0) :
    (andSymStep x y anc hxy hxa hya).stepFwd β = Function.update β anc (β x * β y) := by
  funext w
  unfold SymTempAndStep.stepFwd andSymStep
  dsimp only [id_eq]
  by_cases hwa : w = anc
  · subst hwa
    simp [hβ_anc]
  · simp [Function.update_of_ne hwa]
theorem slice_disj_of_le {K m₁ m₂ n : ℕ} (r : QRegister K n) (s₁ : ℕ) (h₁ : s₁ + m₁ ≤ K)
    (s₂ : ℕ) (h₂ : s₂ + m₂ ≤ K) (hle : s₁ + m₁ ≤ s₂) : (r.slice s₁ m₁ h₁).DisjointWires
    (r.slice s₂ m₂ h₂) := by
  refine QRegExt.disjointWires_of_finset (Finset.disjoint_left.mpr fun w hw1 hw2 ↦ ?_)
  obtain ⟨i, rfl⟩ := (QRegister.mem_image _ w).mp hw1
  obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hw2
  have hv := congrArg Fin.val (r.wires.injective hj)
  have hi := i.isLt
  have hj' := j.isLt
  dsimp [QRegister.slice, QRegister.slice_apply,
    WindowedSlot2FusedTwist288Alt.qreg_slice_wires,
    WindowedSlot2FusedTwist288Alt.qreg_whole_wires,
    WindowedSlot2FusedTwist288Alt.emb_trans_apply,
    WindowedSlot2FusedTwist288Alt.emb_refl_apply,
    WindowedSlot2FusedTwist288Alt.emb_mk_apply, QRegister.compose, QRegister.compose_apply,
    WindowedSlot2FusedTwist288Alt.qreg_compose_wires,
    WindowedSlot2FusedTwist288Alt.qreg_block_apply,
    WindowedSlot2FusedTwist288Alt.qreg_block_wires_apply] at hv
  omega
attribute [local irreducible] withSymBank
end ConfigWindowedSlot2FusedTwist288
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
end WindowedSlot2FusedTwist288
end
end ModWindowedSlot2FusedTwist288

end QuantumComputation.Specs.StoppingPowerSolution
