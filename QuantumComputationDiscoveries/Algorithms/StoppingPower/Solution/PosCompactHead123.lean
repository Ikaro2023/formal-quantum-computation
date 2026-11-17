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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.NucTwistRealizes
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModPosSlots24CompactHead123
@[expose] public section
namespace PosSlots24CompactHead123Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ) (h : offset +
    width ≤ k) (i : Fin width) : (r.slice offset width h).wires i = r.wires ⟨offset + i.val,
    by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) : (f.trans g) x = g (f x) :=
  rfl
end PosSlots24CompactHead123Alt
namespace PosSlots24CompactHead123
open Operator QProg Matrix HermitianMat LocalClassicalPerm
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open OctahedralOrbit Dyadic128CoulombMath
open CanonRank7Circuit
open StreamingBchComparator
open GridGuard654ReflAux (localPermX xPerm_self_cancel)
instance (priority := 100000) instNeZeroTwoPowHead123 (n : ℕ) : NeZero (2 ^ n) :=
  ⟨(Nat.two_pow_pos n).ne'⟩
noncomputable section Main
section CleanDiagCombinators
variable {Var : Type} {n : ℕ}
def carryOnlySymStep (y q cin cout : Wire n) (hyq : y ≠ q) (hyci : y ≠ cin) (hqci : q ≠ cin) (hyco :
    y ≠ cout) (hqco : q ≠ cout) (hcico : cin ≠ cout) : SymTempAndStep n :=
  let S : Finset (Wire n) := {y, q, cin, cout}
  let hy : y ∈ S := by simp [S]
  let hq : q ∈ S := by simp [S]
  let hci : cin ∈ S := by simp [S]
  let hco : cout ∈ S := by simp [S]
  let f1 := fun β : BitAssignment n ↦ Function.update β y (β y + β cin)
  let f2 := fun β : BitAssignment n ↦ Function.update β q (β q + 1)
  let f3 := fun β : BitAssignment n ↦ Function.update β q (β q + β cin)
  let f4 := fun β : BitAssignment n ↦ Function.update β cout (β cout + β cin)
  have hf1 := cnot_self_cancel cin y hyci.symm
  have hf2 := xPerm_self_cancel q
  have hf3 := cnot_self_cancel cin q hqci.symm
  have hf4 := cnot_self_cancel cin cout hcico
  { pre := Circuit.CNOT cin y hyci.symm ;;ᶜ (Circuit.X q ;;ᶜ Circuit.CNOT cin q hqci.symm)
    c₁ := y
    c₂ := q
    anc := cout
    h₁₂ := hyq
    h₁a := hyco
    h₂a := hqco
    midPre := Circuit.CNOT cin q hqci.symm ;;ᶜ
      (Circuit.X q ;;ᶜ (Circuit.CNOT cin y hyci.symm ;;ᶜ Circuit.CNOT cin cout hcico))
    midPost := Circuit.CNOT cin cout hcico ;;ᶜ
      (Circuit.CNOT cin y hyci.symm ;;ᶜ (Circuit.X q ;;ᶜ Circuit.CNOT cin q hqci.symm))
    post := Circuit.CNOT cin q hqci.symm ;;ᶜ (Circuit.X q ;;ᶜ Circuit.CNOT cin y hyci.symm)
    S := S
    f_pre := (f3 ∘ f2) ∘ f1
    f_midPre := ((f4 ∘ f1) ∘ f2) ∘ f3
    f_midPost := ((f3 ∘ f2) ∘ f1) ∘ f4
    f_post := (f1 ∘ f2) ∘ f3
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := (LocalClassicalPerm.CNOT cin y hyci.symm hci hy).seq
      ((localPermX q hq).seq (LocalClassicalPerm.CNOT cin q hqci.symm hci hq))
    local_post := (LocalClassicalPerm.CNOT cin q hqci.symm hci hq).seq
      ((localPermX q hq).seq (LocalClassicalPerm.CNOT cin y hyci.symm hci hy))
    local_midPre := (LocalClassicalPerm.CNOT cin q hqci.symm hci hq).seq
      ((localPermX q hq).seq
        ((LocalClassicalPerm.CNOT cin y hyci.symm hci hy).seq
          (LocalClassicalPerm.CNOT cin cout hcico hci hco)))
    local_midPost := (LocalClassicalPerm.CNOT cin cout hcico hci hco).seq
      ((LocalClassicalPerm.CNOT cin y hyci.symm hci hy).seq
        ((localPermX q hq).seq (LocalClassicalPerm.CNOT cin q hqci.symm hci hq)))
    post_pre_id := fun β ↦ by simp only [Function.comp_apply, f1, f2, f3, hf3, hf2, hf1]
    midPost_midPre_id := fun β ↦ by
      simp only [Function.comp_apply, f1, f2, f3, f4, hf4, hf1, hf2, hf3]
    c₁_mem := hy
    c₂_mem := hq
    anc_mem := hco
    anc_not_mem_pre := by
      simp [Circuit.support_seq, Circuit.support_gate, QRegister.image_pair,
        hyco.symm, hqco.symm, hcico.symm] }
theorem carryOnlySymStep_stepFwd (y q cin cout : Wire n) (hyq : y ≠ q) (hyci : y ≠ cin) (hqci : q ≠
    cin) (hyco : y ≠ cout) (hqco : q ≠ cout) (hcico : cin ≠ cout)
    (β : BitAssignment n) (hco0 : β cout = 0) : (carryOnlySymStep y q cin cout hyq hyci hqci hyco
      hqco hcico).stepFwd β = Function.update β cout (β cin + (β y + β cin) * (β q + 1 + β cin)) :=
      by
  let stp := carryOnlySymStep y q cin cout hyq hyci hqci hyco hqco hcico
  let β₁ := stp.f_pre β
  have hp_y : β₁ y = β y + β cin := by
    simp [β₁, stp, carryOnlySymStep, Function.update_of_ne hyq]
  have hp_q : β₁ q = β q + 1 + β cin := by
    simp [β₁, stp, carryOnlySymStep, Function.update_of_ne hqci.symm,
      Function.update_of_ne hyq.symm, Function.update_of_ne hyci.symm]
  have hp_ci : β₁ cin = β cin := by
    simp [β₁, stp, carryOnlySymStep, Function.update_of_ne hqci.symm,
      Function.update_of_ne hyci.symm]
  have hp_co : β₁ cout = 0 := by
    simp [β₁, stp, carryOnlySymStep, Function.update_of_ne hqco.symm,
      Function.update_of_ne hyco.symm, hco0]
  funext w
  change stp.f_midPre (Function.update β₁ cout (β₁ cout + β₁ y * β₁ q)) w = _
  rw [hp_co, hp_y, hp_q, zero_add]
  dsimp only [stp, carryOnlySymStep, Function.comp_apply]
  rcases eq_or_ne w cout with rfl | hwco
  · simp only [Function.update_self, Function.update_of_ne hyco.symm,
      Function.update_of_ne hqco.symm, Function.update_of_ne hyci.symm,
      Function.update_of_ne hqci.symm, Function.update_of_ne hcico, hp_ci]
    exact add_comm _ _
  · rcases eq_or_ne w y with rfl | hwy
    · simp only [Function.update_of_ne hwco, Function.update_self, Function.update_of_ne hyq,
        Function.update_of_ne hqci.symm, Function.update_of_ne hcico,
        hp_y, hp_ci, zmod2_add_cancel_right]
    · rcases eq_or_ne w q with rfl | hwq
      · simp only [Function.update_of_ne hwco, Function.update_of_ne hwy, Function.update_self,
          Function.update_of_ne hqci.symm, Function.update_of_ne hcico,
          hp_q, hp_ci, zmod2_add_cancel_right]
      · simp only [β₁, stp, carryOnlySymStep, Function.comp_apply, Function.update_of_ne hwco,
          Function.update_of_ne hwy, Function.update_of_ne hwq]
def muxDiffSymStep (s0 y c m : Wire n) (hsy : s0 ≠ y) (_hsc : s0 ≠ c) (hsm : s0 ≠ m) (hyc : y ≠ c)
    (hym : y ≠ m) (hcm : c ≠ m) : SymTempAndStep n :=
  let S : Finset (Wire n) := {s0, y, c, m}
  let hs : s0 ∈ S := by simp [S]
  let hy : y ∈ S := by simp [S]
  let hc : c ∈ S := by simp [S]
  let hm : m ∈ S := by simp [S]
  let f1 := fun β : BitAssignment n ↦ Function.update β y (β y + β c)
  let f2 := fun β : BitAssignment n ↦ Function.update β y (β y + 1)
  { pre := Circuit.CNOT c y hyc.symm ;;ᶜ Circuit.X y
    c₁ := s0
    c₂ := y
    anc := m
    h₁₂ := hsy
    h₁a := hsm
    h₂a := hym
    midPre := Circuit.X y ;;ᶜ Circuit.CNOT c y hyc.symm
    midPost := Circuit.CNOT c y hyc.symm ;;ᶜ Circuit.X y
    post := Circuit.X y ;;ᶜ Circuit.CNOT c y hyc.symm
    S := S
    f_pre := f2 ∘ f1
    f_midPre := f1 ∘ f2
    f_midPost := f2 ∘ f1
    f_post := f1 ∘ f2
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := (LocalClassicalPerm.CNOT c y hyc.symm hc hy).seq (localPermX y hy)
    local_post := (localPermX y hy).seq (LocalClassicalPerm.CNOT c y hyc.symm hc hy)
    local_midPre := (localPermX y hy).seq (LocalClassicalPerm.CNOT c y hyc.symm hc hy)
    local_midPost := (LocalClassicalPerm.CNOT c y hyc.symm hc hy).seq (localPermX y hy)
    post_pre_id := fun β ↦ by
      simp only [Function.comp_apply, f1, f2, xPerm_self_cancel y, cnot_self_cancel c y hyc.symm]
    midPost_midPre_id := fun β ↦ by
      simp only [Function.comp_apply, f1, f2, cnot_self_cancel c y hyc.symm, xPerm_self_cancel y]
    c₁_mem := hs
    c₂_mem := hy
    anc_mem := hm
    anc_not_mem_pre := by
      simp [Circuit.support_seq, Circuit.support_gate, QRegister.image_pair, hym.symm, hcm.symm] }
theorem muxDiffSymStep_stepFwd (s0 y c m : Wire n) (hsy : s0 ≠ y) (hsc : s0 ≠ c) (hsm : s0 ≠ m)
    (hyc : y ≠ c) (hym : y ≠ m) (hcm : c ≠ m) (β : BitAssignment n)
    (hm0 : β m = 0) : (muxDiffSymStep s0 y c m hsy hsc hsm hyc hym hcm).stepFwd β = Function.update
      β m (β s0 * (β y + β c + 1)) := by
  let stp := muxDiffSymStep s0 y c m hsy hsc hsm hyc hym hcm
  funext w
  change stp.f_midPre (Function.update (stp.f_pre β) m
    (stp.f_pre β m + stp.f_pre β s0 * stp.f_pre β y)) w = _
  dsimp only [stp, muxDiffSymStep, Function.comp_apply]
  simp only [Function.update_of_ne hym.symm, Function.update_of_ne hsy, Function.update_self, hm0,
    zero_add]
  rcases eq_or_ne w m with rfl | hwm
  · simp only [Function.update_self, Function.update_of_ne hym.symm]
  · rcases eq_or_ne w y with rfl | hwy
    · simp only [Function.update_of_ne hwm, Function.update_self, Function.update_of_ne hcm,
        Function.update_of_ne hyc.symm, zmod2_add_cancel_right]
    · simp only [Function.update_of_ne hwm, Function.update_of_ne hwy]
end CleanDiagCombinators
section ArithmeticLemmas
theorem regVal8_expand {n : ℕ} (r : QRegister 8 n) (β : BitAssignment n) : regVal r β =
    (β (r 0)).val * 1 + (β (r 1)).val * 2 + (β (r 2)).val * 4 + (β (r 3)).val * 8 +
    (β (r 4)).val * 16 + (β (r 5)).val * 32 + (β (r 6)).val * 64 + (β (r 7)).val * 128 := by
  unfold regVal bitsVal
  rw [Fin.sum_univ_eight]
  rfl
theorem full_adder_step_val (y q c : ZMod 2) : y.val + (q + 1).val + c.val = (y + (q + 1) + c).val +
    2 * (c + (y + c) * (q + 1 + c)).val := by
  revert y q c
  decide
def carrySeq6 (y q : Fin 6 → ZMod 2) (c0 : ZMod 2) : ℕ → ZMod 2
  | 0 => c0
  | j + 1 =>
      if hj : j < 6 then
        let cj := carrySeq6 y q c0 j
        cj + (y ⟨j, hj⟩ + cj) * (q ⟨j, hj⟩ + 1 + cj)
      else 0
private theorem carrySeq6_sum_mod64 (y q : Fin 6 → ZMod 2) (c0 : ZMod 2) : bitsVal (fun j : Fin 6 ↦
    y j + (q j + 1) + carrySeq6 y q c0 j.val) =
    (bitsVal y + bitsVal (fun j : Fin 6 ↦ q j + 1) + c0.val) % 64 := by
  have hprefix : ∀ (k : ℕ) (hk : k ≤ 6), (∑ j : Fin k, (y ⟨j.val, by omega⟩).val * 2 ^ j.val) +
    (∑ j : Fin k, (q ⟨j.val, by omega⟩ + 1).val * 2 ^ j.val) + c0.val =
      (∑ j : Fin k, (y ⟨j.val, by omega⟩ + (q ⟨j.val, by omega⟩ + 1) + carrySeq6 y q c0 j.val).val *
        2 ^ j.val) + (carrySeq6 y q c0 k).val * 2 ^ k := by
    intro k hk
    induction k with
    | zero => simp [carrySeq6]
    | succ k ih =>
        have hklt : k < 6 := by omega
        have hih := ih (by omega)
        have hstep := full_adder_step_val (y ⟨k, hklt⟩) (q ⟨k, hklt⟩) (carrySeq6 y q c0 k)
        simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, carrySeq6, hklt,
          ↓reduceDIte, pow_succ]
        linear_combination hih + hstep * 2 ^ k
  have hlt : bitsVal (fun i : Fin 6 ↦ y i + (q i + 1) + carrySeq6 y q c0 i.val) < 64 :=
    bitsVal_lt_two_pow _
  unfold bitsVal at hlt ⊢
  rw [show (∑ i : Fin 6, (y i).val * 2 ^ i.val) + (∑ i : Fin 6, (q i + 1).val * 2 ^ i.val) +
    c0.val = (∑ j : Fin 6, (y j + (q j + 1) + carrySeq6 y q c0 j.val).val * 2 ^ j.val) +
    (carrySeq6 y q c0 6).val * 64 from hprefix 6 le_rfl]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
theorem mux_target_bitsVal_eq (s0 b0 d0 : ZMod 2) (y q : Fin 6 → ZMod 2) :
    let c0 : ZMod 2 := 1 + (b0 + 1) * d0
    bitsVal (fun j : Fin 6 ↦ s0 * (y j + carrySeq6 y q c0 j.val + 1) + q j) =
      if Bool.not (s0 == 1) then bitsVal q
      else (bitsVal y + (((if b0 = 1 then 1 else 0) + 128 - (d0.val + 2 * bitsVal q)) % 128) / 2) %
        64 := by
  intro c0
  rcases zmod2_eq_zero_or_one s0 with rfl | rfl
  · simp only [zero_mul, zero_add]
    rfl
  · rw [show Bool.not ((1 : ZMod 2) == 1) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h1 : ∀ a b c : ZMod 2, (1 : ZMod 2) * (a + c + 1) + b = a + (b + 1) + c := by decide
    rw [show (fun j : Fin 6 ↦ (1 : ZMod 2) * (y j + carrySeq6 y q c0 j.val + 1) + q j) =
        fun j : Fin 6 ↦ y j + (q j + 1) + carrySeq6 y q c0 j.val from funext fun j ↦ h1 _ _ _,
      carrySeq6_sum_mod64]
    have hcomp := bitsVal_add_one q
    have hq_lt := bitsVal_lt_two_pow q
    change (bitsVal y + bitsVal (fun i : Fin 6 ↦ q i + 1) + c0.val) % 64 = _
    have hb_d : ∀ (b d : ZMod 2),
        (1 + (b + 1) * d).val = 1 - (if b = 1 then 0 else d.val) ∧ d.val < 2 := by decide
    obtain ⟨hc0, hd_lt⟩ := hb_d b0 d0
    dsimp only [c0]
    rw [hc0]
    split_ifs
    all_goals omega
end ArithmeticLemmas
end Main
end PosSlots24CompactHead123
end
end ModPosSlots24CompactHead123

section ModPosSlots24CompactPhase288
@[expose] public section
namespace PosSlots24CompactPhase288
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open OctahedralOrbit Dyadic128CoulombMath
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
instance (priority := 100000) instNeZeroTwoPowMid254 (d : ℕ) : NeZero (2 ^ d) :=
  ⟨(Nat.two_pow_pos d).ne'⟩
@[simp] theorem qreg_slice_wires {m n : ℕ} (r : QRegister m n) (start len : ℕ) (h : start +
    len ≤ m) (i : Fin len) : (r.slice start len h).wires i = r.wires ⟨start + i.val, by omega⟩ :=
    rfl
@[simp] theorem qreg_concat_wires_left {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (h : r₁.DisjointWires r₂) (i : Fin k₁) : (r₁.concat r₂ h).wires (Fin.castAdd k₂ i) =
    r₁.wires i := QRegister.concat_apply_left r₁ r₂ h i
@[simp] theorem qreg_concat_wires_right {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (h : r₁.DisjointWires r₂) (j : Fin k₂) : (r₁.concat r₂ h).wires (Fin.natAdd k₁ j) =
    r₂.wires j := QRegister.concat_apply_right r₁ r₂ h j
@[simp] theorem qreg_block_wires {a b m : ℕ} (hab : a + b ≤ m) (i : Fin b) : (QRegister.block a b
    hab).wires i = ⟨a + i.val, by omega⟩ := rfl
@[simp] theorem qreg_singleton_wires {n : ℕ} (w0 : Wire n) (i : Fin 1) : (QRegister.singleton
    w0).wires i = w0 := rfl
theorem localIdx_congr_cross {k n₁ n₂ : ℕ} (r₁ : QRegister k n₁) (r₂ : QRegister k n₂) (β₁ :
    BitAssignment n₁) (β₂ : BitAssignment n₂) (h : ∀ i : Fin k, β₁ (r₁ i) = β₂ (r₂ i)) :
    localIdx r₁ β₁ = localIdx r₂ β₂ := by
  ext
  rw [localIdx_val, localIdx_val]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h i]
attribute [local irreducible] swapTreePow2Val lookup3xPow2Val
section MidTables
def tailLoTable28 (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 →
    Fin (2 ^ 30)) : ℕ → BitAssignment 28 :=
  fun idx j ↦ packTailTable31 tailSign tailMag30 idx ⟨j.val, by omega⟩
def tailTopTable3 (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 →
    Fin (2 ^ 30)) : ℕ → BitAssignment 3 :=
  fun idx j ↦ packTailTable31 tailSign tailMag30 idx ⟨28 + j.val, by omega⟩
def top3Slot0Bits (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 →
    Fin (2 ^ 30)) (idx : ℕ) : BitAssignment 3 :=
  fun j ↦ if idx < 3 * 2 ^ 14 then tailTopTable3 tailSign tailMag30 idx j else 0
def rRefOrbit16 : QRegister 16 243 := QRegister.block 0 16 (by decide)
def rRefMeas227 : QRegister 227 243 := QRegister.block 16 227 (by decide)
private theorem rRefOrbit16_disj_rRefMeas227 : rRefOrbit16.DisjointWires rRefMeas227 :=
  QRegister.block_disjoint_of_le 0 16 16 227 (by decide) (by decide) (by decide)
noncomputable def refInitAssign (idx : Fin (2 ^ 16)) : BitAssignment 243 :=
  fun q ↦ if h : q.val < 16 then basisBits 16 idx ⟨q.val, h⟩ else 0
noncomputable def refPostQromAssign (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin
    orbitCount47905 → Fin (2 ^ 30)) (idx : Fin (2 ^ 16)) : BitAssignment 243 :=
  let rBuf28 := rRefMeas227.slice 3 224 (by decide)
  let β₁ := writeReg (refInitAssign idx) (rRefMeas227.slice 0 3 (by decide))
    (top3Slot0Bits tailSign tailMag30 idx.val)
  swapTreePow2Val 3 28 (rRefOrbit16.slice 0 3 (by decide)) rBuf28
    (writeReg β₁ rBuf28 (fun k ↦ β₁ (rBuf28 k) + lookup3xPow2Val 11
      (packTablePow2 3 (tailLoTable28 tailSign tailMag30)) (rRefOrbit16.slice 3 13 (by decide)) β₁
        k))
noncomputable def unpackCoreBits (x : Fin (2 ^ (posCoreWires + 16))) : BitAssignment posCoreWires :=
  fun i ↦ basisBits (posCoreWires + 16) x (Fin.castAdd 16 i)
noncomputable def unpackOrbitIdx (x : Fin (2 ^ (posCoreWires + 16))) : Fin (2 ^ 16) :=
  (basisBitsEquiv 16).symm (fun j ↦ basisBits (posCoreWires + 16) x (Fin.natAdd posCoreWires j))
noncomputable def effEntryMag30 (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin
    orbitCount47905 → Fin (2 ^ 30)) (idx : Fin (2 ^ 16)) : ℕ :=
  let rTop2 := (rRefMeas227.slice 0 3 (by decide)).slice 0 2 (by decide)
  let rSlot0_28 := bufPow2Slot0 3 28 (rRefMeas227.slice 3 224 (by decide))
  let hDisj : rSlot0_28.DisjointWires rTop2 := QRegister.disjoint_iff.mpr fun a b heq ↦ by
    simp only [rSlot0_28, rTop2, bufPow2Slot0, QRegister.slice_apply] at heq
    have hv := congrArg Fin.val (rRefMeas227.wires.injective heq)
    dsimp only at hv
    omega
  regVal (rSlot0_28.concat rTop2 hDisj) (refPostQromAssign tailSign tailMag30 idx)
noncomputable def effEntrySign (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin
    orbitCount47905 → Fin (2 ^ 30)) (idx : Fin (2 ^ 16)) : Bool :=
  decide (refPostQromAssign tailSign tailMag30 idx
    ((rRefMeas227.slice 0 3 (by decide)) ⟨2, by decide⟩) = 1)
noncomputable def midPhaseBitSpec (_slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 →
    Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (x : Fin (2 ^ (posCoreWires +
    16))) : Bool :=
  let βL := unpackCoreBits x
  let idx := unpackOrbitIdx x
  let rCoreL := QRegExt.ofFin posCoreWires
  tailDecisionBool (βL (wSlot2Core rCoreL) == 1) (βL (wSlot1Core rCoreL) == 1)
    (βL (wSlot0Core rCoreL) == 1) (βL (wSubReject rCoreL) == 1) (βL (wIsHead rCoreL) == 1)
    (βL (wRejectZero rCoreL) == 1) (decide (regVal (rNucIdx rCoreL) βL < 216))
    (decide (regVal (rAnchorIdx rCoreL) βL < 218)) (decide (regVal (rPartnerIdx rCoreL) βL < 217))
    (decide (regVal (rTailKeep30 rCoreL) βL < effEntryMag30 tailSign tailMag30 idx))
    (effEntrySign tailSign tailMag30 idx)
theorem refInitAssign_orbit (idx : Fin (2 ^ 16)) (i : Fin 16) : refInitAssign idx (rRefOrbit16 i) =
    basisBits 16 idx i := by
  unfold refInitAssign
  split_ifs with h
  · exact congrArg (basisBits 16 idx) (Fin.ext (Nat.zero_add i.val))
  · exact absurd (show (rRefOrbit16 i).val < 16 by dsimp [rRefOrbit16]; omega) h
theorem localIdx_refOrbit16_eq (idx : Fin (2 ^ 16)) : localIdx rRefOrbit16 (refInitAssign idx) =
    idx := by
  refine (basisBitsEquiv 16).injective (funext fun i ↦ ?_)
  rw [show (basisBitsEquiv 16) (localIdx rRefOrbit16 (refInitAssign idx)) i = refInitAssign idx
    (rRefOrbit16 i) from congrFun ((basisBitsEquiv 16).apply_symm_apply _) i, refInitAssign_orbit]
theorem effEntry_eq_of_lt_orbit (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (rOrbit : Fin orbitCount47905) :
    let idx : Fin (2 ^ 16) := ⟨rOrbit.val, by
      have := rOrbit.isLt
      dsimp [orbitCount47905] at *
      omega⟩
    effEntryMag30 tailSign tailMag30 idx = (tailMag30 rOrbit).val ∧
      effEntrySign tailSign tailMag30 idx = tailSign rOrbit := by
  intro idx
  have hLt14 : idx.val < 3 * 2 ^ 14 := by
    have := rOrbit.isLt
    dsimp [orbitCount47905, idx] at *
    omega
  let rTop3 := rRefMeas227.slice 0 3 (by decide)
  let rBuf28 := rRefMeas227.slice 3 224 (by decide)
  let β₁ := writeReg (refInitAssign idx) rTop3 (top3Slot0Bits tailSign tailMag30 idx.val)
  let βRef := refPostQromAssign tailSign tailMag30 idx
  have hDisjTB : ∀ (j : Fin 3) (k : Fin 224), rTop3 j ≠ rBuf28 k := fun j k h ↦ by
    simp only [rTop3, rBuf28, QRegister.slice_apply] at h
    have hv := congrArg Fin.val (rRefMeas227.wires.injective h)
    dsimp only at hv
    omega
  have hOrbβ₁ : (localIdx rRefOrbit16 β₁ : ℕ) = rOrbit.val := by
    rw [localIdx_congr_cross _ _ _ _ fun i ↦ writeReg_apply_of_not_mem _ rTop3 _ _ fun ⟨k, hk⟩ ↦
      (rRefOrbit16_disj_rRefMeas227.compose_right _).ne i k hk.symm, localIdx_refOrbit16_eq]
  have hTopPres : ∀ j : Fin 3, βRef (rTop3 j) =
      packTailTable31 tailSign tailMag30 rOrbit.val ⟨28 + j.val, by omega⟩ := fun j ↦ by
    have hNotBuf : rTop3 j ∉ Set.range rBuf28.wires := fun ⟨k, hk⟩ ↦ hDisjTB j k hk.symm
    change swapTreePow2Val 3 28 _ rBuf28 _ (rTop3 j) = _
    rw [swapTreePow2Val_apply_other 3 28 _ rBuf28 _ hNotBuf,
      writeReg_apply_of_not_mem _ rBuf28 _ _ hNotBuf, writeReg_apply_reg]
    unfold top3Slot0Bits tailTopTable3
    simp only [hLt14, ↓reduceIte]
    rfl
  have hSlot0Lo : ∀ j : Fin 28, βRef (bufPow2Slot0 3 28 rBuf28 j) =
      packTailTable31 tailSign tailMag30 rOrbit.val ⟨j.val, by omega⟩ := fun j ↦
    (selectSwap3xPow2_slot0_eq 11 3 rRefOrbit16 rBuf28
      (rRefOrbit16_disj_rRefMeas227.compose_right _) (tailLoTable28 tailSign tailMag30) β₁
      (fun k ↦ (writeReg_apply_of_not_mem _ rTop3 _ _ fun ⟨j, hj⟩ ↦ hDisjTB j k hj).trans
        (dite_eq_right fun h ↦ by
          dsimp [rBuf28, QRegister.slice_apply, rRefMeas227] at h
          omega))
      (by
        rw [hOrbβ₁]
        exact hLt14) j).trans (by
        rw [hOrbβ₁]
        rfl)
  refine ⟨?_, ?_⟩
  · unfold effEntryMag30
    change regVal _ βRef = (tailMag30 rOrbit).val
    rw [← packTailTable31_low30_val tailSign tailMag30 rOrbit]
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only
    by_cases hj : j.val < 28
    · rw [show j = Fin.castAdd 2 ⟨j.val, hj⟩ from Fin.ext rfl, QRegister.concat_apply_left,
        hSlot0Lo ⟨j.val, hj⟩]
      rfl
    · let jt : Fin 2 := ⟨j.val - 28, by omega⟩
      rw [show j = Fin.natAdd 28 jt from Fin.ext (by dsimp [jt]; omega),
        QRegister.concat_apply_right,
        show ((rRefMeas227.slice 0 3 (by decide)).slice 0 2 (by decide)) jt =
            rTop3 ⟨jt.val, by omega⟩ by
          dsimp only [rTop3]
          rw [QRegister.slice_apply, QRegister.slice_apply, QRegister.slice_apply]
          exact congrArg rRefMeas227.wires (Fin.ext (by dsimp [jt]; omega)),
        hTopPres ⟨jt.val, by omega⟩]
      exact congrArg (· * 2 ^ (Fin.natAdd 28 jt).val)
        (congrArg (fun u ↦ (packTailTable31 tailSign tailMag30 rOrbit.val u).val)
          (Fin.ext (by dsimp [jt])))
  · unfold effEntrySign
    change decide (βRef (rTop3 ⟨2, by decide⟩) = 1) = tailSign rOrbit
    rw [hTopPres ⟨2, by decide⟩,
      show (⟨28 + (⟨2, by decide⟩ : Fin 3).val, by omega⟩ : Fin 31) = ⟨30, by decide⟩ from rfl,
      packTailTable31_sign_bit tailSign tailMag30 rOrbit]
    cases tailSign rOrbit <;> rfl
theorem midPhaseBitSpec_eq_tailAndSlackPhaseBitSpec
    (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (x : Fin (2 ^ (posCoreWires + 16)))
    (hOrbit :
      let βL := unpackCoreBits x
      let rCoreL := QRegExt.ofFin posCoreWires
      regVal (rAnchorIdx rCoreL) βL < 218 →
      (βL (wSlot0Core rCoreL) = 1 → regVal (rPartnerIdx rCoreL) βL < 217) →
      (unpackOrbitIdx x).val =
        (tetRank65 (canonTriple128 (tailOrbitCoord128 slot2SwappedTo0 βL))).val) :
    midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 x =
      tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 (unpackCoreBits x) := by
  unfold midPhaseBitSpec tailDecisionBool tailAndSlackPhaseBitSpec
  dsimp only
  cases hb2 : (unpackCoreBits x (wSlot2Core (QRegExt.ofFin posCoreWires)) == 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hb1 : (unpackCoreBits x (wSlot1Core (QRegExt.ofFin posCoreWires)) == 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show decide (Bool.not (unpackCoreBits x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) =
        true →
            decide (regVal (rNucIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 216) =
              true) =
          decide (Bool.not (unpackCoreBits x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) =
            true →
            regVal (rNucIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 216)
          from decide_eq_decide.mpr (by simp),
        show decide (((unpackCoreBits x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) &&
            Bool.not (unpackCoreBits x (wIsHead (QRegExt.ofFin posCoreWires)) == 1)) = true →
            decide (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 217) =
              true) =
          decide (((unpackCoreBits x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) &&
            Bool.not (unpackCoreBits x (wIsHead (QRegExt.ofFin posCoreWires)) == 1)) = true →
            regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 217)
          from decide_eq_decide.mpr (by simp)]
      set acc : Bool := Bool.not (unpackCoreBits x (wSubReject (QRegExt.ofFin posCoreWires)) ==
        1) &&
        decide (Bool.not (unpackCoreBits x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) = true →
          regVal (rNucIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 216) &&
        decide (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 218) &&
        decide (((unpackCoreBits x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) &&
          Bool.not (unpackCoreBits x (wIsHead (QRegExt.ofFin posCoreWires)) == 1)) = true →
          regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (unpackCoreBits x) < 217)
      cases hacc : acc
      · simp only [Bool.not_false, ↓reduceIte]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hih : (unpackCoreBits x (wIsHead (QRegExt.ofFin posCoreWires)) == 1)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hAnds : acc = true := hacc
          dsimp [acc] at hAnds
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hAnds
          let rOrbit :=
            tetRank65 (canonTriple128 (tailOrbitCoord128 slot2SwappedTo0 (unpackCoreBits x)))
          obtain ⟨hMag, hSgn⟩ := effEntry_eq_of_lt_orbit tailSign tailMag30 rOrbit
          rw [show unpackOrbitIdx x = ⟨rOrbit.val, by
                have := rOrbit.isLt
                dsimp [orbitCount47905] at *
                omega⟩ from
              Fin.ext (hOrbit hAnds.1.2 fun hs01 ↦ hAnds.2 ⟨by rw [hs01]; rfl, by rw [hih]; rfl⟩),
            hMag, hSgn]
          exact ite_congr decide_eq_true_eq (fun _ ↦ rfl) (fun _ ↦ rfl)
        · simp only [↓reduceIte]
    · simp only [↓reduceIte]
  · simp only [↓reduceIte]
end MidTables
set_option exponentiation.threshold 256
end PosSlots24CompactPhase288
end
end ModPosSlots24CompactPhase288

section ModPosSlots24SemanticBridge
@[expose] public section
namespace PosSlots24SemanticBridge
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz128
open BchCubeDecoder
open Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open HeavyHeadAndProjectile128 hiding FineCoord128
open PosSlots24BranchConcrete
open PosSlots24TopWrapper
open FullSysCatSegmentBridge
open PosMomSelectDynamic (unitaryConj)
open NuclearTwistRealizes (uTwistParam)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
lemma pos24ItePos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) (a b : α) : (if P then a else
    b) = a := ite_eq_left hp
lemma pos24IteNeg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) (a b : α) : (if P then a else
    b) = b := ite_eq_right hp
def pos24CutQb (wt : Fin 4) : ℕ :=
  match wt.val with | 0 => 2553265499 | 1 => 2629544206 | 2 => 2602730294 | _ => 2578361638
def pos24MinQb (wt : Fin 4) : ℕ :=
  match wt.val with | 0 => 1009605293 | 1 => 1001189304 | 2 => 1009625694 | _ => 1009631600
def pos24MidQb (wt : Fin 4) : ℕ :=
  match wt.val with | 0 => 1781435396 | 1 => 1815366755 | 2 => 1806177994 | _ => 1793996619
def pos24HalfSpanQb (wt : Fin 4) : ℕ :=
  match wt.val with | 0 => 771830103 | 1 => 814177451 | 2 => 796552300 | _ => 784365019
noncomputable def pos24CutNyq (b : NyqParity3D) : ℝ :=
  ((pos24CutQb (subGridParityWeight3 (nyqParityToBool b)) : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30
noncomputable def pos24MinNyq (b : NyqParity3D) : ℝ :=
  ((pos24MinQb (subGridParityWeight3 (nyqParityToBool b)) : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30
noncomputable def pos24TailSign (idx : Fin orbitCount47905) : Bool :=
  decide (min (w128OrbitBiasedQ30 idx) (pos24CutQb (orbitParityWeight idx)) <
    pos24MidQb (orbitParityWeight idx))
private lemma pos24_loMin_le_biasedQ30 (idx : Fin orbitCount47905) : loMinQbNat (orbitParityWeight
    idx).val ≤ w128OrbitBiasedQ30 idx := by
  set t := tetRank65.symm idx
  have ht_eq : tetUnrank65 idx = t := rfl
  have hwt_val : (orbitParityWeight idx).val = t.u.val % 2 + t.v.val % 2 + t.w.val % 2 := rfl
  have hok := canonicalTriple_orbitOk t
  dsimp only [orbitTripleOk] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have hqb_eq : (posConst328Nat + dot160 (wqVec160 (u56Col t.w.val) (u56Col t.v.val)) (u56Col
    t.u.val) - (negConst328Nat + (bBiasNat * sum160 (wqVec160 (u56Col t.w.val) (u56Col t.v.val)) +
      sumU328 t.u.val))) / shift298Nat = w128OrbitBiasedQ30 idx := by
    simp only [w128OrbitBiasedQ30, ht_eq, evalTripleBiasedQ30]
  rw [hqb_eq, ← hwt_val] at hok
  exact hok.1.1.1.2
lemma pos24TailMag30_le_halfSpan (idx : Fin orbitCount47905) :
    let wt := orbitParityWeight idx
    let tQb := min (w128OrbitBiasedQ30 idx) (pos24CutQb wt)
    let mQb := pos24MidQb wt
    (if tQb < mQb then mQb - tQb else tQb - mQb) ≤ pos24HalfSpanQb wt := by
  have hqb := pos24_loMin_le_biasedQ30 idx
  generalize orbitParityWeight idx = wt, w128OrbitBiasedQ30 idx = qb at hqb ⊢
  fin_cases wt <;>
    simp only [loMinQbNat, pos24CutQb, pos24MidQb, pos24HalfSpanQb, min_def] at hqb ⊢ <;>
    split_ifs <;> omega
noncomputable def pos24TailMag30 (idx : Fin orbitCount47905) : Fin (2 ^ 30) :=
  let wt := orbitParityWeight idx
  let tQb := min (w128OrbitBiasedQ30 idx) (pos24CutQb wt)
  let mQb := pos24MidQb wt
  have hspan : ∀ w : Fin 4, pos24HalfSpanQb w < 2 ^ 30 := by decide
  ⟨if tQb < mQb then mQb - tQb else tQb - mQb,
    lt_of_le_of_lt (pos24TailMag30_le_halfSpan idx) (hspan wt)⟩
lemma subGridParityWeight3_nyqParityToBool (p : Fin 3 → Fin 2) : (subGridParityWeight3
    (nyqParityToBool p)).val = (p 0).val + (p 1).val + (p 2).val := by
  revert p
  decide
lemma subGridWeight128_eq_nyqParity (d : NyqFine3D128) : subGridWeight128 d = subGridParityWeight3
    (nyqParityToBool (nyq128Equiv3D.symm d).2) := by
  apply Fin.ext
  rw [subGridParityWeight3_nyqParityToBool]
  have h0 := congrArg (fun x ↦ (x 0).val) (nyq128Equiv3D.apply_symm_apply d)
  have h1 := congrArg (fun x ↦ (x 1).val) (nyq128Equiv3D.apply_symm_apply d)
  have h2 := congrArg (fun x ↦ (x 2).val) (nyq128Equiv3D.apply_symm_apply d)
  rw [nyq128Equiv3D_val] at h0 h1 h2
  have hb0 := ((nyq128Equiv3D.symm d).2 0).isLt
  have hb1 := ((nyq128Equiv3D.symm d).2 1).isLt
  have hb2 := ((nyq128Equiv3D.symm d).2 2).isLt
  change (d 0).val % 2 + (d 1).val % 2 + (d 2).val % 2 = _
  omega
private lemma pos24_shell_tail_arith (wt : Fin 4) (qb : ℕ) (hmin : loMinQbNat wt.val ≤ qb) : ((if
    decide (min qb (pos24CutQb wt) < pos24MidQb wt) then (-1 : ℝ) else 1) *
    ((if min qb (pos24CutQb wt) < pos24MidQb wt then pos24MidQb wt - min qb (pos24CutQb wt) else min
      qb (pos24CutQb wt) - pos24MidQb wt : ℕ) : ℝ)) / 2 ^ 30 =
    min (((qb : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30) (((pos24CutQb wt : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30) -
      (((pos24CutQb wt : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30 +
    ((pos24MinQb wt : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30) / 2 := by
  have hmin_eq : min (((qb : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30) (((pos24CutQb wt : ℝ) - (2 ^ 30 : ℝ)) / 2
    ^ 30) = (((min qb (pos24CutQb wt) : ℕ) : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30 := by
    by_cases hle : qb ≤ pos24CutQb wt
    · rw [Nat.min_eq_left hle, min_eq_left]
      exact div_le_div_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr hle) _) (by norm_num)
    · have hle' : pos24CutQb wt ≤ qb := by omega
      rw [Nat.min_eq_right hle', min_eq_right]
      exact div_le_div_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr hle') _) (by norm_num)
  have hmid : 2 * pos24MidQb wt = pos24CutQb wt + pos24MinQb wt := by
    fin_cases wt <;> decide
  rw [hmin_eq]
  have hmid2 : 2 * (pos24MidQb wt : ℝ) = (pos24CutQb wt : ℝ) + (pos24MinQb wt : ℝ) := mod_cast hmid
  have hmidR : (pos24MidQb wt : ℝ) = ((pos24CutQb wt : ℝ) + (pos24MinQb wt : ℝ)) / 2 := by linarith
  by_cases hlt : min qb (pos24CutQb wt) < pos24MidQb wt
  · simp only [hlt, decide_true, ↓reduceIte]
    rw [Nat.cast_sub (le_of_lt hlt), hmidR]
    ring
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.cast_sub (le_of_not_gt hlt), hmidR]
    ring
private lemma pos24_shell_head_arith (wt : Fin 4) (qb r2 mult : ℕ) (hopt : (if r2 ≤ rSqOptNat wt.val
    then decide (loInOptQbNat wt.val ≤ qb) else decide (qb ≤ hiOutOptQbNat wt.val)) = true) :
    (mult : ℝ) * max (((qb : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30 - ((pos24CutQb wt : ℝ) - (2 ^ 30 : ℝ)) / 2
      ^ 30) 0 = (((if r2 ≤ rSqOptNat wt.val then mult * strictSubNat (1 + qb)
    (floorCutOptQbNat wt.val) else 0 : ℕ) : ℝ) / 2 ^ 30) := by
  have hfacts : floorCutOptQbNat wt.val = pos24CutQb wt + 1 ∧ pos24CutQb wt ≤ loInOptQbNat wt.val ∧
    hiOutOptQbNat wt.val ≤ pos24CutQb wt := by
    fin_cases wt <;> decide
  obtain ⟨hf, hi, ho⟩ := hfacts
  by_cases hr : r2 ≤ rSqOptNat wt.val
  · simp only [hr, ↓reduceIte, decide_eq_true_eq, strictSubNat_eq, hf] at hopt ⊢
    have hle : pos24CutQb wt ≤ qb := le_trans hi hopt
    have h1 : ((pos24CutQb wt : ℝ) - 2 ^ 30) / 2 ^ 30 ≤ ((qb : ℝ) - 2 ^ 30) / 2 ^ 30 :=
      div_le_div_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr hle) _) (by norm_num)
    rw [max_eq_left (sub_nonneg.mpr h1), show 1 + qb - (pos24CutQb wt + 1) = qb - pos24CutQb wt
      by omega, Nat.cast_mul, Nat.cast_sub hle]
    ring
  · simp only [hr, ↓reduceIte, decide_eq_true_eq] at hopt ⊢
    have hle : qb ≤ pos24CutQb wt := le_trans hopt ho
    have h1 : ((qb : ℝ) - 2 ^ 30) / 2 ^ 30 ≤ ((pos24CutQb wt : ℝ) - 2 ^ 30) / 2 ^ 30 :=
      div_le_div_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr hle) _) (by norm_num)
    rw [max_eq_right (sub_nonpos.mpr h1)]
    norm_num
theorem pos24_shell_cert (d : NyqFine3D128) :
    let idx := tetRank65 (canonTriple128 d)
    let signR : ℝ := if pos24TailSign idx then -1 else 1
    (signR * (pos24TailMag30 idx : ℝ)) / 2 ^ 30 =
        kTailShifted128 w128DualQ30 pos24CutNyq pos24MinNyq d ∧
      ((orbitMultNat (canonTriple128 d).u.val (canonTriple128 d).v.val (canonTriple128 d).w.val : ℝ)
        *
          DyadicSubgridToeplitz128.kHead128 w128DualQ30 pos24CutNyq d =
        ((orbitHeadQ30Opt idx : ℕ) : ℝ) / 2 ^ 30) := by
  let t := canonTriple128 d
  let idx := tetRank65 t
  let t' := tetRank65.symm idx
  have hsym : t' = t := tetRank65.symm_apply_apply t
  have hw_b : orbitParityWeight idx = subGridParityWeight3 (nyqParityToBool (nyq128Equiv3D.symm
    d).2) :=
    (subGridWeight128_eq_orbit d).symm.trans (subGridWeight128_eq_nyqParity d)
  have hq30_real : w128DualQ30 d = ((w128OrbitBiasedQ30 idx : ℝ) - (2 ^ 30 : ℝ)) / 2 ^ 30 := by
    unfold w128DualQ30 w128OrbitQ30Real w128OrbitQ30
    change (((w128OrbitBiasedQ30 idx : ℤ) - (2 ^ 30 : ℤ) : ℤ) : ℝ) / 2 ^ 30 = _
    push_cast
    norm_num
  have hok_raw := canonicalTriple_orbitOk t'
  dsimp only [orbitTripleOk] at hok_raw
  simp only [Bool.and_eq_true] at hok_raw
  have hr2 : t.u.val * t.u.val + t.v.val * t.v.val + t.w.val * t.w.val = canonicalNormSq65 t := by
    unfold canonicalNormSq65
    ring
  refine ⟨by
      dsimp only [pos24TailSign, pos24TailMag30, kTailShifted128,
        DyadicSubgridToeplitz128.kTail128, pos24CutNyq, pos24MinNyq]
      rw [hq30_real, ← hw_b]
      exact pos24_shell_tail_arith (orbitParityWeight idx) (w128OrbitBiasedQ30 idx)
        (pos24_loMin_le_biasedQ30 idx), ?_⟩
  have hraw : (if t'.u.val * t'.u.val + t'.v.val * t'.v.val + t'.w.val * t'.w.val ≤
        rSqOptNat (orbitParityWeight idx).val then
      decide (loInOptQbNat (orbitParityWeight idx).val ≤ w128OrbitBiasedQ30 idx)
    else decide (w128OrbitBiasedQ30 idx ≤ hiOutOptQbNat (orbitParityWeight idx).val)) = true :=
    hok_raw.1.1.2
  rw [hsym, hr2] at hraw
  dsimp only [DyadicSubgridToeplitz128.kHead128, pos24CutNyq, orbitHeadQ30Opt]
  rw [hq30_real, ← hw_b, show tetUnrank65 idx = t from hsym,
    show t.u.val % 2 + t.v.val % 2 + t.w.val % 2 = (orbitParityWeight idx).val from
      congrArg (fun c ↦ c.u.val % 2 + c.v.val % 2 + c.w.val % 2) hsym.symm, hr2]
  exact pos24_shell_head_arith (orbitParityWeight idx) (w128OrbitBiasedQ30 idx)
    (canonicalNormSq65 t) (orbitMultNat t.u.val t.v.val t.w.val) hraw
def pos24HeadU56 : Fin 56 → ℕ :=
  ![0, 0, 0, 1, 0, 0, 1, 0, 1, 2, 0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 0, 1, 0, 1, 2, 0, 1,
    2, 3, 0, 1, 2, 3, 4, 0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 5]
def pos24HeadV56 : Fin 56 → ℕ :=
  ![0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 0, 1, 1, 2, 2, 2, 3, 3,
    3, 3, 4, 4, 4, 4, 4, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5]
def pos24HeadW56 : Fin 56 → ℕ :=
  ![0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
def pos24HeadWeight56 : Fin 56 → ℕ :=
  ![22715236741, 54760703790, 68771346192, 34208170224, 17758053786, 65094721536,
    57680531760, 23079413100, 39134725656, 9985603888, 11637692592, 36895880832,
    32885364672, 25160219880, 47008606944, 16818043920, 7969827852, 14841024192,
    10241616864, 1912648904, 3570015162, 15755590992, 15500146632, 14158274256,
    21705959472, 9196259184, 6221741640, 12058503648, 5701527120, 72, 1301750808,
    9060312, 0, 0, 0, 2984867244, 6959905536, 5964692856, 2692479240, 5415067488, 72,
    129182784, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
abbrev fin56ToOrbit (k : Fin 56) : Fin orbitCount47905 :=
  ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩
private def pos24Canon56 (k : Fin 56) : CanonicalTriple65 :=
  ⟨⟨pos24HeadU56 k, (by decide : ∀ j : Fin 56, pos24HeadU56 j < 65) k⟩,
    ⟨pos24HeadV56 k, (by decide : ∀ j : Fin 56, pos24HeadV56 j < 65) k⟩,
    ⟨pos24HeadW56 k, (by decide : ∀ j : Fin 56, pos24HeadW56 j < 65) k⟩,
    (by decide : ∀ j : Fin 56, pos24HeadU56 j ≤ pos24HeadV56 j) k,
    (by decide : ∀ j : Fin 56, pos24HeadV56 j ≤ pos24HeadW56 j) k⟩
private theorem pos24Canon56_eq_unrank (k : Fin 56) : tetUnrank65 (fin56ToOrbit k) = pos24Canon56
    k := by
  refine tetRank65.symm_apply_eq.mpr ?_
  fin_cases k
  all_goals decide
theorem pos24HeadCoords56_eq (k : Fin 56) :
    let t := tetUnrank65 (fin56ToOrbit k)
    t.u.val = pos24HeadU56 k ∧ t.v.val = pos24HeadV56 k ∧ t.w.val = pos24HeadW56 k := by
  dsimp only
  rw [pos24Canon56_eq_unrank k]
  exact ⟨rfl, rfl, rfl⟩
theorem pos24HeadWeight56_eq (k : Fin 56) : pos24HeadWeight56 k = orbitHeadQ30Opt (fin56ToOrbit
    k) := by
  unfold orbitHeadQ30Opt w128OrbitBiasedQ30
  rw [pos24Canon56_eq_unrank k]
  fin_cases k
  all_goals decide
def pos24HeadSumNat : ℕ := 727884457843
def pos24TailSpanSumNat : ℕ := 6388384375
def pos24PermAxis (pid : Fin 6) (ax : Fin 3) : Fin 3 :=
  match pid.val, ax.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2 | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2 | 3, 0 => 1 | 3, 1 => 2 | 3, _ => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, _ => 1 | _, 0 => 2 | _, 1 => 1 | _, _ => 0
lemma pos24_oh_lt128 (neg : Bool) (c : ℕ) : (if neg then (128 - c) % 128 else c % 128) < 128 := by
  split_ifs <;> exact Nat.mod_lt _ (Nat.succ_pos 127)
def pos24OhPoint (u v w : ℕ) (pid : Fin 6) (sm : Fin 8) : FineCoord128 := fun ax ↦
  let c := (![u % 128, v % 128, w % 128] : Fin 3 → ℕ) (pos24PermAxis pid ax)
  let neg := ((sm.val / (2 ^ ax.val)) % 2) == 1
  ⟨if neg then (128 - c) % 128 else c % 128, pos24_oh_lt128 neg c⟩
lemma pos24_dpWeight_lt4 (dp : Fin 8) :
    (dp.val % 2) + ((dp.val / 2) % 2) + ((dp.val / 4) % 2) < 4 := by omega
def pos24TailSpan8 (dp : Fin 8) : ℕ :=
  pos24HalfSpanQb ⟨(dp.val % 2) + ((dp.val / 2) % 2) + ((dp.val / 4) % 2), pos24_dpWeight_lt4 dp⟩
theorem pos24_kHead128_eq_zero_of_idx_ge_56 (d : NyqFine3D128) (hge : 56 ≤ (tetRank65
    (canonTriple128 d)).val) : DyadicSubgridToeplitz128.kHead128 w128DualQ30 pos24CutNyq d = 0 := by
  set t := canonTriple128 d
  set idx := tetRank65 t
  have hw6 : 6 ≤ t.w.val := by
    by_contra hlt
    have h1 := tetRankPoly_lt_tetNum_succ t.uv t.vw
    have h2 : tetNum (t.w.val + 1) ≤ tetNum 6 := tetNum_mono (by omega)
    have h3 : tetNum 6 = 56 := by decide
    have hval : idx.val = tetRankPoly t.u.val t.v.val t.w.val := rfl
    omega
  have hr2 : 36 ≤ t.u.val * t.u.val + t.v.val * t.v.val + t.w.val * t.w.val := by nlinarith
  have hrSq_le : ∀ n : ℕ, rSqOptNat n ≤ 34 := fun
    | 0 | 1 | 2 | 3 => by decide
    | _ + 4 => by simp [rSqOptNat]
  have hopt0 : orbitHeadQ30Opt idx = 0 := by
    unfold orbitHeadQ30Opt
    rw [show tetUnrank65 idx = t from tetRank65.symm_apply_apply t]
    exact pos24IteNeg (by have := hrSq_le ((t.u.val % 2) + (t.v.val % 2) + (t.w.val % 2)); omega)
      _ _
  have hmult_pos : 0 < orbitMultNat t.u.val t.v.val t.w.val := by
    have hp : 0 < permMultNat t.u.val t.v.val t.w.val := by
      unfold permMultNat
      split_ifs <;> omega
    have ha : ∀ x : ℕ, 0 < axisMultNat x := fun x ↦ by
      unfold axisMultNat
      split_ifs <;> omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp (ha _)) (ha _)) (ha _)
  have hshell := (pos24_shell_cert d).2
  change (orbitMultNat t.u.val t.v.val t.w.val : ℝ) *
      DyadicSubgridToeplitz128.kHead128 w128DualQ30 pos24CutNyq d =
    ((orbitHeadQ30Opt idx : ℕ) : ℝ) / 2 ^ 30 at hshell
  rw [hopt0] at hshell
  norm_num at hshell
  exact hshell.resolve_left (Nat.ne_of_gt hmult_pos)
private lemma pos24_ohAct_lt128 (neg : Bool) (c : ℕ) : (if neg then (128 - c) % 128 else c % 128) <
    128 := pos24_oh_lt128 neg c
private def pos24OhAct (pid : Fin 6) (sm : Fin 8) (x : FineCoord128) : FineCoord128 :=
  fun ax ↦
    let c := (x (pos24PermAxis pid ax)).val
    let neg := ((sm.val / (2 ^ ax.val)) % 2) == 1
    ⟨if neg then (128 - c) % 128 else c % 128, pos24_ohAct_lt128 neg c⟩
private theorem pos24OhPoint_eq_act (k : Fin 56) (pid : Fin 6) (sm : Fin 8) : pos24OhPoint
    (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm =
    pos24OhAct pid sm (canonicalEmbed128 (tetUnrank65 (fin56ToOrbit k))) := by
  obtain ⟨hu, hv, hw⟩ := pos24HeadCoords56_eq k
  have hlt : pos24HeadU56 k < 128 ∧ pos24HeadV56 k < 128 ∧ pos24HeadW56 k < 128 := by
    fin_cases k
    all_goals decide
  funext ax
  apply Fin.ext
  dsimp only [pos24OhPoint, pos24OhAct]
  have harr : ∀ i : Fin 3, (![pos24HeadU56 k % 128, pos24HeadV56 k % 128,
      pos24HeadW56 k % 128] : Fin 3 → ℕ) i =
      (canonicalEmbed128 (tetUnrank65 (fin56ToOrbit k)) i).val := fun i ↦ by
    fin_cases i
    all_goals dsimp [canonicalEmbed128]
    all_goals omega
  rw [harr (pos24PermAxis pid ax)]
private theorem foldMag128_neg_mod (x : Fin 128) : foldMag128 ⟨(128 - x.val) % 128, Nat.mod_lt _ (by
    decide)⟩ = foldMag128 x := by
  revert x
  decide
private lemma fin65_val_min (x y : Fin 65) : (min x y).val = if x.val ≤ y.val then x.val else
    y.val := by
  by_cases h : x.val ≤ y.val
  · rw [min_eq_left (Fin.le_def.mpr h), pos24ItePos h]
  · rw [min_eq_right (le_of_not_ge (mt Fin.le_def.mp h)), pos24IteNeg h]
private lemma fin65_val_max (x y : Fin 65) : (max x y).val = if x.val ≤ y.val then y.val else
    x.val := by
  by_cases h : x.val ≤ y.val
  · rw [max_eq_right (Fin.le_def.mpr h), pos24ItePos h]
  · rw [max_eq_left (le_of_not_ge (mt Fin.le_def.mp h)), pos24IteNeg h]
private lemma sortTriple_val_0 (g : Fin 3 → Fin 65) : (sortTriple g 0).val =
    let m01 := if (g 0).val ≤ (g 1).val then (g 0).val else (g 1).val
    let M01 := if (g 0).val ≤ (g 1).val then (g 1).val else (g 0).val
    let m2 := if M01 ≤ (g 2).val then M01 else (g 2).val
    if m01 ≤ m2 then m01 else m2 := by
  change (min (min (g 0) (g 1)) (min (max (g 0) (g 1)) (g 2))).val = _
  rw [fin65_val_min, fin65_val_min, fin65_val_min, fin65_val_max]
private lemma sortTriple_val_1 (g : Fin 3 → Fin 65) : (sortTriple g 1).val =
    let m01 := if (g 0).val ≤ (g 1).val then (g 0).val else (g 1).val
    let M01 := if (g 0).val ≤ (g 1).val then (g 1).val else (g 0).val
    let m2 := if M01 ≤ (g 2).val then M01 else (g 2).val
    if m01 ≤ m2 then m2 else m01 := by
  change (max (min (g 0) (g 1)) (min (max (g 0) (g 1)) (g 2))).val = _
  rw [fin65_val_max, fin65_val_min, fin65_val_min, fin65_val_max]
private lemma sortTriple_val_2 (g : Fin 3 → Fin 65) : (sortTriple g 2).val =
    let M01 := if (g 0).val ≤ (g 1).val then (g 1).val else (g 0).val
    if M01 ≤ (g 2).val then (g 2).val else M01 := by
  change (max (max (g 0) (g 1)) (g 2)).val = _
  rw [fin65_val_max, fin65_val_max]
private lemma fun3_val_ext {g f : Fin 3 → Fin 65} (h0 : (g 0).val = (f 0).val) (h1 : (g 1).val =
    (f 1).val) (h2 : (g 2).val = (f 2).val) : g = f := by
  funext i
  fin_cases i
  · exact Fin.ext h0
  · exact Fin.ext h1
  · exact Fin.ext h2
private lemma sortTriple_swap01 (a b c : Fin 65) (g f : Fin 3 → Fin 65) (hg0 : g 0 = b) (hg1 : g 1 =
    a) (hg2 : g 2 = c) (hf0 : f 0 = a) (hf1 : f 1 = b) (hf2 : f 2 = c) :
    sortTriple g = sortTriple f := by
  refine fun3_val_ext ?_ ?_ ?_
  · rw [sortTriple_val_0, sortTriple_val_0, hg0, hg1, hg2, hf0, hf1, hf2]
    dsimp only
    split_ifs
    all_goals omega
  · rw [sortTriple_val_1, sortTriple_val_1, hg0, hg1, hg2, hf0, hf1, hf2]
    dsimp only
    split_ifs
    all_goals omega
  · rw [sortTriple_val_2, sortTriple_val_2, hg0, hg1, hg2, hf0, hf1, hf2]
    dsimp only
    split_ifs
    all_goals omega
private lemma sortTriple_swap12 (a b c : Fin 65) (g f : Fin 3 → Fin 65) (hg0 : g 0 = a) (hg1 : g 1 =
    c) (hg2 : g 2 = b) (hf0 : f 0 = a) (hf1 : f 1 = b) (hf2 : f 2 = c) :
    sortTriple g = sortTriple f := by
  refine fun3_val_ext ?_ ?_ ?_
  · rw [sortTriple_val_0, sortTriple_val_0, hg0, hg1, hg2, hf0, hf1, hf2]
    dsimp only
    split_ifs
    all_goals omega
  · rw [sortTriple_val_1, sortTriple_val_1, hg0, hg1, hg2, hf0, hf1, hf2]
    dsimp only
    split_ifs
    all_goals omega
  · rw [sortTriple_val_2, sortTriple_val_2, hg0, hg1, hg2, hf0, hf1, hf2]
    dsimp only
    split_ifs
    all_goals omega
private theorem sortTriple_perm6 (pid : Fin 6) (f : Fin 3 → Fin 65) : sortTriple (fun ax ↦
    f (pos24PermAxis pid ax)) = sortTriple f := by
  have h1 := sortTriple_swap12 (f 0) (f 1) (f 2) (fun ax ↦ f (pos24PermAxis 1 ax)) f
    rfl rfl rfl rfl rfl rfl
  have h2 := sortTriple_swap01 (f 0) (f 1) (f 2) (fun ax ↦ f (pos24PermAxis 2 ax)) f
    rfl rfl rfl rfl rfl rfl
  have h4 := (sortTriple_swap01 (f 0) (f 2) (f 1) (fun ax ↦ f (pos24PermAxis 4 ax))
    (fun ax ↦ f (pos24PermAxis 1 ax)) rfl rfl rfl rfl rfl rfl).trans h1
  fin_cases pid
  · exact congrArg sortTriple (fun3_val_ext rfl rfl rfl)
  · exact h1
  · exact h2
  · exact (sortTriple_swap12 (f 1) (f 0) (f 2) (fun ax ↦ f (pos24PermAxis 3 ax))
      (fun ax ↦ f (pos24PermAxis 2 ax)) rfl rfl rfl rfl rfl rfl).trans h2
  · exact h4
  · exact (sortTriple_swap12 (f 2) (f 0) (f 1) (fun ax ↦ f (pos24PermAxis 5 ax))
      (fun ax ↦ f (pos24PermAxis 4 ax)) rfl rfl rfl rfl rfl rfl).trans h4
private theorem canonTriple128_pos24OhAct (pid : Fin 6) (sm : Fin 8) (x : FineCoord128) :
    canonTriple128 (pos24OhAct pid sm x) = canonTriple128 x := by
  have hmag : (fun ax ↦ foldMag128 (pos24OhAct pid sm x ax)) =
      fun ax ↦ foldMag128 (x (pos24PermAxis pid ax)) := funext fun ax ↦ by
    dsimp only [pos24OhAct]
    cases hneg : ((sm.val / 2 ^ ax.val) % 2) == 1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg foldMag128 (Fin.ext (Nat.mod_eq_of_lt (x _).isLt))
    · simp only [↓reduceIte]
      exact foldMag128_neg_mod _
  have hs : sortTriple (fun ax ↦ foldMag128 (pos24OhAct pid sm x ax)) = sortTriple (fun ax ↦
    foldMag128 (x ax)) := by
    rw [hmag]
    exact sortTriple_perm6 pid (fun ax ↦ foldMag128 (x ax))
  unfold canonTriple128
  dsimp only
  congr 1
  · exact congrFun hs 0
  · exact congrFun hs 1
  · exact congrFun hs 2
private def pos24PermComp (p1 p2 : Fin 6) : Fin 6 :=
  match (pos24PermAxis p2 (pos24PermAxis p1 0)).val,
      (pos24PermAxis p2 (pos24PermAxis p1 1)).val with
  | 0, 1 => 0 | 0, _ => 1 | 1, 0 => 2 | 1, _ => 3 | _, 0 => 4 | _, _ => 5
private def pos24SmComp (p1 : Fin 6) (s1 s2 : Fin 8) : Fin 8 :=
  let b (ax : Fin 3) : ℕ :=
    ((s1.val / (2 ^ ax.val)) % 2) + ((s2.val / (2 ^ (pos24PermAxis p1 ax).val)) % 2)
  ⟨(b 0 % 2) + 2 * (b 1 % 2) + 4 * (b 2 % 2), by omega⟩
private theorem pos24PermComp_axis (p1 p2 : Fin 6) (ax : Fin 3) : pos24PermAxis (pos24PermComp p1
    p2) ax = pos24PermAxis p2 (pos24PermAxis p1 ax) := by
  revert p1 p2 ax
  decide
private theorem pos24SmComp_bit (p1 : Fin 6) (s1 s2 : Fin 8) (ax : Fin 3) : ((((pos24SmComp p1 s1
    s2).val / (2 ^ ax.val)) % 2) == 1) = Bool.xor (((s1.val / (2 ^ ax.val)) % 2) == 1)
    (((s2.val / (2 ^ (pos24PermAxis p1 ax).val)) % 2) == 1) := by
  revert p1 s1 s2 ax
  decide
private theorem pos24OhAct_comp (p1 p2 : Fin 6) (s1 s2 : Fin 8) (x : FineCoord128) : pos24OhAct p1
    s1 (pos24OhAct p2 s2 x) = pos24OhAct (pos24PermComp p1 p2) (pos24SmComp p1 s1 s2) x := by
  funext ax
  apply Fin.ext
  dsimp only [pos24OhAct]
  rw [pos24PermComp_axis, pos24SmComp_bit]
  exact (by decide : ∀ (b1 b2 : Bool) (cFin : Fin 128),
    (let c1 := if b2 then (128 - cFin.val) % 128 else cFin.val % 128
     if b1 then (128 - c1) % 128 else c1 % 128) =
    if Bool.xor b1 b2 then (128 - cFin.val) % 128 else cFin.val % 128) _ _ _
private def pos24PermInv (p : Fin 6) : Fin 6 :=
  match p.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | _ => 5
private def pos24SmInv (p : Fin 6) (s : Fin 8) : Fin 8 := pos24SmComp (pos24PermInv p) 0 s
private theorem pos24OhGroup_left_inv (g : Fin 6 × Fin 8) : pos24PermComp (pos24PermInv g.1) g.1 =
    0 ∧ pos24SmComp (pos24PermInv g.1) (pos24SmInv g.1 g.2) g.2 = 0 := by
  revert g
  decide
private theorem pos24OhGroup_right_inv (g : Fin 6 × Fin 8) : pos24PermComp g.1 (pos24PermInv g.1) =
    0 ∧ pos24SmComp g.1 g.2 (pos24SmInv g.1 g.2) = 0 := by
  revert g
  decide
private theorem pos24OhGroup_assoc (g1 g2 g3 : Fin 6 × Fin 8) : (pos24PermComp (pos24PermComp g1.1
    g2.1) g3.1, pos24SmComp (pos24PermComp g1.1 g2.1) (pos24SmComp g1.1 g1.2 g2.2) g3.2) =
    (pos24PermComp g1.1 (pos24PermComp g2.1 g3.1), pos24SmComp g1.1 g1.2 (pos24SmComp g2.1 g2.2
      g3.2)) := by
  rcases g1 with ⟨p1, s1⟩
  rcases g2 with ⟨p2, s2⟩
  rcases g3 with ⟨p3, s3⟩
  ext1
  · exact (by decide : ∀ a b c : Fin 6,
      pos24PermComp (pos24PermComp a b) c = pos24PermComp a (pos24PermComp b c)) p1 p2 p3
  · refine (by decide : ∀ a b : Fin 8,
      (∀ ax : Fin 3, (((a.val / 2 ^ ax.val) % 2) == 1) = (((b.val / 2 ^ ax.val) % 2) == 1)) →
      a = b) _ _ fun ax ↦ ?_
    dsimp only
    rw [pos24SmComp_bit, pos24SmComp_bit, pos24SmComp_bit, pos24SmComp_bit, pos24PermComp_axis,
      Bool.xor_assoc]
private theorem pos24OhAct_id (x : FineCoord128) : pos24OhAct 0 0 x = x := by
  funext ax
  apply Fin.ext
  fin_cases ax
  all_goals exact Nat.mod_eq_of_lt (x _).isLt
private theorem exists_pos24Perm_sortTriple (g : Fin 3 → Fin 65) : ∃ p : Fin 6, (fun ax : Fin 3 ↦
    sortTriple g (pos24PermAxis p ax)) = g := by
  refine ⟨if (g 0).val ≤ (g 1).val then
      if (g 1).val ≤ (g 2).val then 0 else if (g 0).val ≤ (g 2).val then 1 else 3
    else if (g 0).val ≤ (g 2).val then 2 else if (g 1).val ≤ (g 2).val then 4 else 5,
    fun3_val_ext ?_ ?_ ?_⟩
  all_goals by_cases h01 : (g 0).val ≤ (g 1).val
  all_goals by_cases h12 : (g 1).val ≤ (g 2).val
  all_goals by_cases h02 : (g 0).val ≤ (g 2).val
  all_goals simp only [h01, h12, h02, ↓reduceIte]
  all_goals dsimp [pos24PermAxis]
  all_goals simp only [sortTriple_val_0, sortTriple_val_1, sortTriple_val_2]
  all_goals try split_ifs
  all_goals omega
private theorem exists_pos24OhAct_canonical (d : FineCoord128) : ∃ g : Fin 6 × Fin 8, pos24OhAct g.1
    g.2 (canonicalEmbed128 (canonTriple128 d)) = d := by
  have hsign1D : ∀ z : Fin 128,
      ∃ b : Bool, (⟨if b then (128 - (foldMag128 z).val) % 128 else (foldMag128 z).val % 128,
        pos24_oh_lt128 b _⟩ : Fin 128) = z := by decide
  obtain ⟨b0, hb0⟩ := hsign1D (d 0)
  obtain ⟨b1, hb1⟩ := hsign1D (d 1)
  obtain ⟨b2, hb2⟩ := hsign1D (d 2)
  let s : Fin 8 := ⟨(if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) +
    4 * (if b2 then 1 else 0), by
      cases b0
      all_goals cases b1
      all_goals cases b2
      all_goals decide⟩
  obtain ⟨p, hp⟩ := exists_pos24Perm_sortTriple (fun w ↦ foldMag128 (d w))
  have hce_all : ∀ j : Fin 3, (canonicalEmbed128 (canonTriple128 d) j).val =
      (sortTriple (fun w ↦ foldMag128 (d w)) j).val := fun j ↦ by
    fin_cases j
    all_goals rfl
  have hbs_gen : ∀ (c0 c1 c2 : Bool) (ax : Fin 3),
      ((((if c0 then 1 else 0) + 2 * (if c1 then 1 else 0) +
        4 * (if c2 then 1 else 0)) / 2 ^ ax.val) % 2 == 1) = ![c0, c1, c2] ax := by decide
  have hbs : ∀ ax : Fin 3, (((s.val / 2 ^ ax.val) % 2) == 1) = ![b0, b1, b2] ax :=
    fun ax ↦ hbs_gen b0 b1 b2 ax
  refine ⟨(p, s), funext fun ax ↦ Fin.ext ?_⟩
  dsimp only [pos24OhAct]
  rw [hce_all (pos24PermAxis p ax), congrFun hp ax, hbs ax]
  fin_cases ax
  · exact congrArg Fin.val hb0
  · exact congrArg Fin.val hb1
  · exact congrArg Fin.val hb2
private theorem pos24_stabCard_mul_orbitMult_eq_48 (k : Fin 56) :
    let x0 := canonicalEmbed128 (tetUnrank65 (fin56ToOrbit k))
    (((Finset.univ : Finset (Fin 6 × Fin 8)).filter
      (fun g ↦ pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) g.1 g.2 =
        x0)).card) *
      orbitMultNat (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) = 48 := by
  dsimp only
  rw [pos24Canon56_eq_unrank k]
  fin_cases k
  all_goals decide
theorem pos24_oh_head_sum_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (F : NyqFine3D128 →
    M) : (∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8, (((pos24HeadWeight56 k : ℝ) / 2 ^ 30 : ℝ) :
    ℂ) • F (pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm)) = (48 : ℂ) • ∑
      d : NyqFine3D128, (DyadicSubgridToeplitz128.kHead128 w128DualQ30 pos24CutNyq d : ℂ) • F d :=
      by
  let pt (k : Fin 56) (g : Fin 6 × Fin 8) : NyqFine3D128 :=
    pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) g.1 g.2
  let wtR (k : Fin 56) : ℝ := (pos24HeadWeight56 k : ℝ) / 2 ^ 30
  have hpart : ∀ k : Fin 56, (∑ pid : Fin 6, ∑ sm : Fin 8, (wtR k : ℂ) • F (pt k (pid, sm))) =
      ∑ d : NyqFine3D128, ((((Finset.univ.filter (fun g ↦ pt k g = d)).card : ℕ) *
        wtR k : ℝ) : ℂ) • F d := fun k ↦ by
    rw [← Fintype.sum_prod_type',
      ← Finset.sum_fiberwise_of_maps_to (g := pt k) (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have hc : (∑ g ∈ Finset.univ.filter (fun g ↦ pt k g = d), (wtR k : ℂ) • F (pt k g)) =
      ∑ _g ∈ Finset.univ.filter (fun g ↦ pt k g = d), (wtR k : ℂ) • F d :=
      Finset.sum_congr rfl fun g hg ↦ by rw [(Finset.mem_filter.mp hg).2]
    rw [hc, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    push_cast
    rfl
  change (∑ k : Fin 56, ∑ pid : Fin 6, ∑ sm : Fin 8, (wtR k : ℂ) • F (pt k (pid, sm))) = _
  simp_rw [hpart]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  set idx := tetRank65 (canonTriple128 d)
  have hempty_of_ne : ∀ (k : Fin 56), k.val ≠ idx.val →
      Finset.univ.filter (fun g ↦ pt k g = d) = ∅ := fun k hne ↦ by
    refine Finset.filter_eq_empty_iff.mpr fun g _ hgd ↦ hne ?_
    dsimp only [pt] at hgd
    rw [pos24OhPoint_eq_act k] at hgd
    have hct := congrArg canonTriple128 hgd
    rw [canonTriple128_pos24OhAct, canonTriple128_canonicalEmbed128] at hct
    have hrk := congrArg (fun c ↦ (tetRank65 c).val) hct
    have hleft : (tetRank65 (tetUnrank65 (fin56ToOrbit k))).val = k.val := by
      change (tetRank65 (tetRank65.symm (fin56ToOrbit k))).val = k.val
      rw [tetRank65.apply_symm_apply]
    exact hleft.symm.trans hrk
  by_cases hlt : idx.val < 56
  · let k0 : Fin 56 := ⟨idx.val, hlt⟩
    rw [Finset.sum_eq_single k0]
    · obtain ⟨g0, hg0⟩ := exists_pos24OhAct_canonical d
      let x0 := canonicalEmbed128 (tetUnrank65 (fin56ToOrbit k0))
      have ht_eq : tetUnrank65 (fin56ToOrbit k0) = canonTriple128 d := by
        rw [show fin56ToOrbit k0 = idx from Fin.ext rfl]
        exact tetRank65.symm_apply_apply (canonTriple128 d)
      rw [show canonicalEmbed128 (canonTriple128 d) = x0 from congrArg canonicalEmbed128 ht_eq.symm]
        at hg0
      let g0Inv : Fin 6 × Fin 8 := (pos24PermInv g0.1, pos24SmInv g0.1 g0.2)
      have hcard_eq : (Finset.univ.filter (fun g ↦ pt k0 g = d)).card = (Finset.univ.filter (fun h ↦
        pt k0 h = x0)).card := by
        refine Finset.card_bij (fun g _ ↦ (pos24PermComp g0Inv.1 g.1,
          pos24SmComp g0Inv.1 g0Inv.2 g.2)) (fun g hg ↦ ?_) (fun g1 _ g2 _ heq ↦ ?_)
          (fun h hh ↦ ?_)
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          dsimp only [pt]
          rw [pos24OhPoint_eq_act k0, ← pos24OhAct_comp,
            (pos24OhPoint_eq_act k0 g.1 g.2).symm.trans (Finset.mem_filter.mp hg).2,
            ← hg0, pos24OhAct_comp, (pos24OhGroup_left_inv g0).1,
            (pos24OhGroup_left_inv g0).2, pos24OhAct_id]
        · have hmul : ∀ g : Fin 6 × Fin 8, (pos24PermComp g0.1 (pos24PermComp g0Inv.1 g.1),
              pos24SmComp g0.1 g0.2 (pos24SmComp g0Inv.1 g0Inv.2 g.2)) = g := fun g ↦ by
            rw [← pos24OhGroup_assoc g0 g0Inv g, (pos24OhGroup_right_inv g0).1,
              (pos24OhGroup_right_inv g0).2]
            revert g
            decide
          rw [← hmul g1, ← hmul g2, (Prod.mk.inj heq).1, (Prod.mk.inj heq).2]
        · refine ⟨(pos24PermComp g0.1 h.1, pos24SmComp g0.1 g0.2 h.2),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · dsimp only [pt]
            rw [pos24OhPoint_eq_act k0, ← pos24OhAct_comp,
              (pos24OhPoint_eq_act k0 h.1 h.2).symm.trans (Finset.mem_filter.mp hh).2, hg0]
          · rw [← pos24OhGroup_assoc g0Inv g0 h, (pos24OhGroup_left_inv g0).1,
              (pos24OhGroup_left_inv g0).2]
            exact (by decide : ∀ g : Fin 6 × Fin 8,
              (pos24PermComp 0 g.1, pos24SmComp 0 0 g.2) = g) h
      rw [hcard_eq, smul_smul]
      refine congrArg (· • F d) ?_
      have h48r : (((Finset.univ.filter (fun h ↦ pt k0 h = x0)).card : ℝ) * (orbitMultNat
        (pos24HeadU56 k0) (pos24HeadV56 k0) (pos24HeadW56 k0) : ℝ)) = 48 := by
        exact_mod_cast pos24_stabCard_mul_orbitMult_eq_48 k0
      have hshell := (pos24_shell_cert d).2
      obtain ⟨hu, hv, hw⟩ := pos24HeadCoords56_eq k0
      rw [ht_eq] at hu hv hw
      rw [hu, hv, hw, (pos24HeadWeight56_eq k0).symm] at hshell
      have hreal : ((Finset.univ.filter (fun h ↦ pt k0 h = x0)).card : ℝ) * wtR k0 = 48 *
        DyadicSubgridToeplitz128.kHead128 w128DualQ30 pos24CutNyq d := by
        dsimp only [wtR]
        linear_combination ((Finset.univ.filter (fun h ↦ pt k0 h = x0)).card : ℝ) * hshell.symm +
          DyadicSubgridToeplitz128.kHead128 w128DualQ30 pos24CutNyq d * h48r
      rw [hreal]
      push_cast
      ring
    · intro k _ hkne
      simp [hempty_of_ne k (Fin.val_ne_of_ne hkne)]
    · intro hk0
      exact absurd (Finset.mem_univ k0) hk0
  · rw [pos24_kHead128_eq_zero_of_idx_ge_56 d (Nat.le_of_not_lt hlt)]
    simp only [Complex.ofReal_zero, zero_smul, smul_zero]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    simp [hempty_of_ne k (Nat.ne_of_lt (lt_of_lt_of_le k.isLt (Nat.le_of_not_lt hlt)))]
lemma pos24_6_le_80 : 6 ≤ 80 := by decide
lemma pos24_22_le_80 : 22 ≤ 80 := by decide
lemma pos24_coreWires80_eq : FullSysCatSegmentBridge.fullSysCoreWires 80 = posCoreWires := rfl
noncomputable def castUnitaryPow2 {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a)) : Unitary (2 ^ b) :=
  h ▸ U
noncomputable def mulUnitaryPow2 {a b : ℕ} (U₁ : Unitary (2 ^ a)) (U₂ : Unitary (2 ^ b)) (hab : a =
    b) : Unitary (2 ^ a) := U₁ * (hab.symm ▸ U₂)
noncomputable def sysBlockAtPayloadGen {kCore : ℕ} (hk : posCoreWires = kCore) (M : Operator (2 ^
    kCore)) (s0 : Bool) (p80 : BitAssignment 80) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  Matrix.of fun x' x ↦
    let βOf (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : BitAssignment posCoreWires :=
        writeSubBits rPosSubLocal (fun w ↦ if hw : w.val < SpecsAux.SpecMirror.systemQubits then
        basisBits SpecsAux.SpecMirror.systemQubits z ⟨w.val, hw⟩ else if w.val == 3948 then (if s0
        then 1 else 0) else 0) p80
    let ix' : Fin (2 ^ kCore) := hk ▸ (basisBitsEquiv posCoreWires).symm (βOf x')
    let ix : Fin (2 ^ kCore) := hk ▸ (basisBitsEquiv posCoreWires).symm (βOf x)
    M ix' ix
lemma pos24_core80_eq_twist80 : FullSysCatSegmentBridge.fullSysCoreWires 80 =
    SpecsAux.SpecMirror.systemQubits + 6 + 80 := rfl
noncomputable def pos24ConjCore80 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (cfg :
    SpecsAux.SpecMirror.Configuration)
    : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires 80)) := unitaryConj
    (mulUnitaryPow2 (FullSysCatSegmentBridge.fullSysQftCoreUnitary pos24_6_le_80 qft)
    (uTwistParam true pos24_22_le_80 cfg) pos24_core80_eq_twist80) (castUnitaryPow2
    pos24_coreWires80_eq.symm (uPosPhase true pos24TailSign pos24TailMag30))
end PosSlots24SemanticBridge
end
end ModPosSlots24SemanticBridge

section ModPosSlots24SpectatorPhase
@[expose] public section
end
end ModPosSlots24SpectatorPhase

section ModSinglePassNuclearTwist288
@[expose] public section
namespace SinglePassNuclearTwist288Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end SinglePassNuclearTwist288Alt
namespace SinglePassNuclearTwist288
set_option maxRecDepth 200000
instance (priority := 1000000) instNeZeroTwoPowSinglePass (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open DyadicQft64WalkCircuit SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux.PhaseGradCatalystCore
open InPlaceFullAddSlice InPlaceStepEngine
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open FullSysCatSegmentBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
theorem gidney_bit_arith : ∀ u t c : ZMod 2, 2 * (((u + c) * (t + c) + c).val) + (u + t + c).val =
    u.val + t.val + c.val := by
  decide
theorem half_bit_arith : ∀ u t : ZMod 2, 2 * ((u * t).val) + (u + t).val = u.val + t.val := by
  decide
def gidneyFullStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t c : Wire M) (hut : u ≠ t) (hct : c ≠
    t) (hcu : c ≠ u) (hu : u.val < cur) (ht : t.val < cur) (hc : c.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  .seq (.seq (withCliffAlloc (.seq (.cnot c t hct) (.cnot c u hcu))
      (withTempBit u t ⟨cur, hcur⟩ hut (wire_ne_of_lt hu) (wire_ne_of_lt ht)
        (withCliffAlloc (.cnot c ⟨cur, hcur⟩ (wire_ne_of_lt hc)) body)))
    (.cliff (.cnot u t hut))) (.cliff (.cnot c t hct))
@[simp] theorem gidneyFullStep_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t c : Wire M)
    (hut : u ≠ t) (hct : c ≠ t) (hcu : c ≠ u) (hu : u.val < cur)
    (ht : t.val < cur) (hc : c.val < cur) (body : TempPhaseProg M) : (gidneyFullStep cur hcur u t c
      hut hct hcu hu ht hc body).countTempAnd = 1 + body.countTempAnd := by
  simp [gidneyFullStep, withCliffAlloc, withTempBit, TempPhaseProg.countTempAnd]
def gidneyHalfStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t : Wire M) (hut : u ≠ t) (hu : u.val <
    cur) (ht : t.val < cur) (body : TempPhaseProg M) : TempPhaseProg M :=
  let cout : Wire M := ⟨cur, hcur⟩
  .seq (withTempBit u t cout hut (wire_ne_of_lt hu) (wire_ne_of_lt ht) body)
    (.cliff (.cnot u t hut))
@[simp] theorem gidneyHalfStep_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t : Wire M)
    (hut : u ≠ t) (hu : u.val < cur) (ht : t.val < cur)
    (body : TempPhaseProg M) : (gidneyHalfStep cur hcur u t hut hu ht body).countTempAnd = 1 +
      body.countTempAnd := by
  simp [gidneyHalfStep, withTempBit, TempPhaseProg.countTempAnd]
theorem TargetBlock.seq_cnot_target {M targetEnd rem : ℕ} (hrem : rem ≤ M) (src dst : Wire M) (hsd :
    src ≠ dst) (hdst : dst.val = targetEnd) (hsrc_lo : targetEnd ≤ src.val)
    (_hsrc_hi : src.val < M - rem) {fBody : BitAssignment M → BitAssignment M} {sBody :
      BitAssignment M → ZMod 2} {p : TempPhaseProg M}
    (hp : TargetBlock M targetEnd rem fBody sBody p) : TargetBlock M (targetEnd + 1) rem (fun β w ↦
      if w = dst then β dst + β src else fBody β w) sBody (.seq p (.cliff (.cnot src dst hsd))) :=
      by
  refine ⟨⟨rem, hrem, hp.valid, trivial, fun β₁ hβ₁ w hw ↦ ?_⟩, fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
  · rw [hp.bits β₁ hβ₁ w, ite_eq_right (by omega)]
    exact hβ₁ w hw
  · dsimp only [TempPhaseProg.evalBits, CliffProg.eval]
    by_cases hw_dst : w = dst
    · subst hw_dst
      rw [Function.update_self, hp.bits β hβ w, hp.bits β hβ src]
      simp [hdst, not_lt_of_ge hsrc_lo]
    · rw [Function.update_of_ne hw_dst, hp.bits β hβ w]
      by_cases hlt : w.val < targetEnd
      · simp [hlt, show w.val < targetEnd + 1 by omega, hw_dst]
      · simp [hlt, show ¬(w.val < targetEnd + 1) from fun h1 ↦ hw_dst (Fin.ext (by omega))]
  · simpa only [TempPhaseProg.evalSign, add_zero] using hp.sign β hβ
theorem TargetBlock.seq_cnot_in_target {M targetEnd rem : ℕ} (hrem : rem ≤ M) (src dst : Wire M)
    (hsd : src ≠ dst) (hdst : dst.val < targetEnd)
    (hsrc_lo : targetEnd ≤ src.val) (_hsrc_hi : src.val < M - rem) {fBody : BitAssignment M →
      BitAssignment M} {sBody : BitAssignment M → ZMod 2}
    {p : TempPhaseProg M} (hp : TargetBlock M targetEnd rem fBody sBody p) : TargetBlock M targetEnd
      rem (fun β w ↦ if w = dst then fBody β dst + β src else fBody β w) sBody
    (.seq p (.cliff (.cnot src dst hsd))) := by
  refine ⟨⟨rem, hrem, hp.valid, trivial, fun β₁ hβ₁ w hw ↦ ?_⟩, fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
  · rw [hp.bits β₁ hβ₁ w, ite_eq_right (by omega)]
    exact hβ₁ w hw
  · dsimp only [TempPhaseProg.evalBits, CliffProg.eval]
    by_cases hw_dst : w = dst
    · subst hw_dst
      rw [Function.update_self, hp.bits β hβ w, hp.bits β hβ src]
      simp [hdst, not_lt_of_ge hsrc_lo]
    · rw [Function.update_of_ne hw_dst, hp.bits β hβ w]
      by_cases hlt : w.val < targetEnd
      · simp [hlt, hw_dst]
      · simp [hlt]
  · simpa only [TempPhaseProg.evalSign, add_zero] using hp.sign β hβ
theorem TargetBlock.nil_one {M rem : ℕ} : TargetBlock M 1 rem id (fun _ ↦ 0) .nil :=
  ⟨trivial, fun _ _ _ ↦ by split_ifs <;> rfl, fun _ _ ↦ rfl⟩
def gidneyFullStepInnerAssign {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t c : Wire M) (_hut : u ≠ t)
    (hct : c ≠ t) (hcu : c ≠ u) (hc : c.val < cur) (β : BitAssignment M) : BitAssignment M :=
  let cout : Wire M := ⟨cur, hcur⟩
  let cOuter : CliffProg M := .seq (.cnot c t hct) (.cnot c u hcu)
  let β₁ := cOuter.eval β
  (CliffProg.cnot c cout (wire_ne_of_lt hc)).eval (Function.update β₁ cout (β₁ u * β₁ t))
theorem gidneyFullStepInnerAssign_cout {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t c : Wire M)
    (hut : u ≠ t) (hct : c ≠ t) (hcu : c ≠ u) (hc : c.val < cur) (β : BitAssignment M) :
    gidneyFullStepInnerAssign cur hcur u t c hut hct hcu hc β ⟨cur, hcur⟩ = (β u + β c) * (β t +
      β c) + β c := by
  let cout : Wire M := ⟨cur, hcur⟩
  have hccout : c ≠ cout := wire_ne_of_lt hc
  simp [gidneyFullStepInnerAssign, CliffProg.eval, cout, hccout, hut, hut.symm, hct, hcu]
theorem gidneyFullStepInnerAssign_other {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t c : Wire M)
    (hut : u ≠ t) (hct : c ≠ t) (hcu : c ≠ u) (hc : c.val < cur)
    (β : BitAssignment M) (q : Wire M) (hqu : q ≠ u) (hqt : q ≠ t) (hqco : q ≠ ⟨cur,
      hcur⟩) : gidneyFullStepInnerAssign cur hcur u t c hut hct hcu hc β q = β q := by
  dsimp only [gidneyFullStepInnerAssign, CliffProg.eval]
  rw [Function.update_of_ne hqco, Function.update_of_ne hqco, Function.update_of_ne hqu,
    Function.update_of_ne hqt]
theorem TargetBlock.gidneyHalfStep_block {M targetEnd : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t :
    Wire M) (hut : u ≠ t) (ht_eq : t.val = targetEnd) (hu_lo : targetEnd < u.val)
    (hu : u.val < cur) (ht : t.val < cur) {fBody : BitAssignment M → BitAssignment M} {sBody :
      BitAssignment M → ZMod 2} {body : TempPhaseProg M}
    (hBody : TargetBlock M targetEnd (M - (cur + 1)) fBody sBody body) : TargetBlock M (targetEnd +
      1) (M - cur) (fun β w ↦ if w = t then β t + β u else fBody (Function.update β
    ⟨cur, hcur⟩ (β u * β t)) w) (fun β ↦ sBody (Function.update β ⟨cur, hcur⟩ (β u *
      β t))) (gidneyHalfStep cur hcur u t hut hu ht body) := by
  have h1 := TargetBlock.withTempBit_block (M := M) (targetEnd := targetEnd)
    cur hcur u t hut (by omega) (by omega) hu ht hBody
  exact TargetBlock.seq_cnot_target (M := M) (targetEnd := targetEnd) (rem := M - cur)
    (by omega) u t hut ht_eq (by omega) (by omega) h1
theorem TargetBlock.gidneyFullStep_block {M targetEnd : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (u t c :
    Wire M) (hut : u ≠ t) (hct : c ≠ t) (hcu : c ≠ u) (ht_eq : t.val = targetEnd)
    (hu_lo : targetEnd < u.val) (hc_lo : targetEnd < c.val) (hu : u.val < cur) (ht : t.val < cur)
      (hc : c.val < cur) {fBody : BitAssignment M → BitAssignment M}
    {sBody : BitAssignment M → ZMod 2} {body : TempPhaseProg M} (hBody : TargetBlock M targetEnd (M
      - (cur + 1)) fBody sBody body) : TargetBlock M
    (targetEnd + 1) (M - cur) (fun β w ↦ if w = t then β u + β t + β c else fBody
      (gidneyFullStepInnerAssign cur hcur u t c hut hct hcu hc β) w) (fun β ↦ sBody
    (gidneyFullStepInnerAssign cur hcur u t c hut hct hcu hc β)) (gidneyFullStep cur hcur u t c hut
      hct hcu hu ht hc body) := by
  let remIn := M - (cur + 1)
  let cout : Wire M := ⟨cur, hcur⟩
  have h1 := TargetBlock.withCliffAlloc_block (M := M) (targetEnd := targetEnd)
    (rem := remIn) (remIn := remIn) (by dsimp [remIn]; omega) le_rfl (by dsimp [remIn]; omega)
    (.cnot c cout (wire_ne_of_lt hc))
    ⟨⟨by omega, by dsimp [remIn]; omega⟩, ⟨by dsimp [cout]; omega, by dsimp [cout, remIn]; omega⟩⟩
    hBody
  have h2 := TargetBlock.withTempBit_block (M := M) (targetEnd := targetEnd)
    cur hcur u t hut (by omega) (by omega) hu ht h1
  have h3 := TargetBlock.withCliffAlloc_block (M := M) (targetEnd := targetEnd)
    (rem := M - cur) (remIn := M - cur) (by omega) le_rfl (by omega)
    (.seq (.cnot c t hct) (.cnot c u hcu))
    ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩ h2
  have h5 := TargetBlock.seq_cnot_in_target (M := M) (targetEnd := targetEnd + 1) (rem := M - cur)
    (by omega) c t hct (by omega) (by omega) (by omega)
    (TargetBlock.seq_cnot_target (M := M) (targetEnd := targetEnd) (rem := M - cur)
      (by omega) u t hut ht_eq (by omega) (by omega) h3)
  refine ⟨h5.valid, fun β hβ w ↦ ?_, fun β hβ ↦ h5.sign β hβ⟩
  dsimp only [gidneyFullStep]
  rw [h5.bits β hβ w]
  by_cases hlt : w.val < targetEnd + 1
  · by_cases hwt : w = t
    · subst hwt
      simp only [hlt, ↓reduceIte]
      ring
    · simp only [hlt, hwt, ↓reduceIte]
      rfl
  · simp only [hlt, ↓reduceIte]
def msbPrefixVal {M : ℕ} : (q : ℕ) → (q ≤ M) → BitAssignment M → ℕ
  | 0, _, _ => 0
  | q + 1, hq, β => 2 * msbPrefixVal q (by omega) β + (β ⟨q, hq⟩).val
theorem msbPrefixVal_congr {M : ℕ} {q : ℕ} (hq : q ≤ M) {β₁ β₂ : BitAssignment M} (h : ∀ w : Wire M,
    w.val < q → β₁ w = β₂ w) : msbPrefixVal q hq β₁ = msbPrefixVal q hq β₂ := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [msbPrefixVal]
      rw [ih (by omega) (fun w hw ↦ h w (by omega)), h ⟨q, hq⟩ (by dsimp; omega)]
theorem msbPrefixVal_eq_bitsVal_rev {M : ℕ} :
    ∀ (K : ℕ) (hK : K ≤ M) (β : BitAssignment M),
      msbPrefixVal K hK β = bitsVal (fun j : Fin K ↦ β ⟨K - 1 - j.val, by omega⟩)
  | 0, _, _ => rfl
  | K + 1, hK, β => by
      simp only [msbPrefixVal]
      rw [msbPrefixVal_eq_bitsVal_rev K (by omega) β]
      unfold bitsVal
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      have htail : (∑ i : Fin K, (β ⟨K + 1 - 1 - i.succ.val, by omega⟩).val * 2 ^ i.succ.val) =
        ∑ i : Fin K, 2 * ((β ⟨K - 1 - i.val, by omega⟩).val * 2 ^ i.val) :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [show (⟨K + 1 - 1 - i.succ.val, by omega⟩ : Wire M) = ⟨K - 1 - i.val, by omega⟩ from
            Fin.ext (by dsimp; omega), Fin.val_succ, pow_succ]
          ring
      dsimp only
      rw [htail, show (⟨K + 1 - 1 - (0 : Fin (K + 1)).val, by omega⟩ : Wire M) = ⟨K, hK⟩ from rfl]
      simp only [Fin.val_zero, _root_.pow_zero, mul_one]
      omega
theorem step_msb_mod_arith (q headVal uHigh coutVal tNew tOld uVal cVal : ℕ) (hBit : 2 * coutVal +
    tNew = tOld + uVal + cVal) : (2 * ((headVal + uHigh + coutVal) % 2 ^ q) + tNew) % 2 ^ (q + 1) =
    ((2 * headVal + tOld) + (2 * uHigh + uVal) + cVal) % 2 ^ (q + 1) := by
  have hdiv := Nat.div_add_mod' (headVal + uHigh + coutVal) (2 ^ q)
  set d := (headVal + uHigh + coutVal) / 2 ^ q
  set r := (headVal + uHigh + coutVal) % 2 ^ q
  have hEq : (2 * headVal + tOld) + (2 * uHigh + uVal) + cVal = (2 * r + tNew) + d * 2 ^ (q + 1) :=
    by
    rw [pow_succ]
    linarith
  rw [hEq, Nat.add_mul_mod_self_right]
def optBitVal {M : ℕ} (o : Option (Wire M)) (β : BitAssignment M) : ℕ :=
  match o with
  | none => 0
  | some w => (β w).val
def optMsbVal {M : ℕ} (uMSB : ℕ → Option (Wire M)) : ℕ → BitAssignment M → ℕ
  | 0, _ => 0
  | q + 1, β => 2 * optMsbVal uMSB q β + optBitVal (uMSB q) β
theorem ite_false {α : Sort*} {c : Prop} [Decidable c] (hnc : ¬c) {t e : α} : ite c t e = e :=
  ite_eq_right hnc
theorem ite_true {α : Sort*} {c : Prop} [Decidable c] (hc : c) {t e : α} : ite c t e = t :=
  ite_eq_left hc
theorem dite_false {α : Sort*} {c : Prop} [Decidable c] (hnc : ¬c) {t : c → α} {e : ¬c → α} : dite c
    t e = e hnc := dite_eq_right hnc
theorem dite_true {α : Sort*} {c : Prop} [Decidable c] (hc : c) {t : c → α} {e : ¬c → α} : dite c t
    e = t hc := dite_eq_left hc
theorem msbPrefixVal_succ {M q : ℕ} (hq : q + 1 ≤ M) (β : BitAssignment M) : msbPrefixVal (q +
    1) hq β = 2 * msbPrefixVal q (by omega) β + (β ⟨q, hq⟩).val := rfl
theorem optMsbVal_succ {M : ℕ} (uMSB : ℕ → Option (Wire M)) (q : ℕ) (β : BitAssignment M) :
    optMsbVal uMSB (q + 1) β = 2 * optMsbVal uMSB q β + optBitVal (uMSB q) β := rfl
private theorem optMsbVal_congr {M : ℕ} {uMSB : ℕ → Option (Wire M)} {q : ℕ} {β₁ β₂ : BitAssignment
    M} (h : ∀ m w, m < q → uMSB m = some w → β₁ w = β₂ w) :
    optMsbVal uMSB q β₁ = optMsbVal uMSB q β₂ := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [optMsbVal_succ, optMsbVal_succ, ih fun m w hm ↦ h m w (by omega)]
      rcases hum : uMSB q with _ | w
      · rfl
      · exact congrArg (2 * optMsbVal uMSB q β₂ + ZMod.val ·) (h q w (Nat.lt_succ_self q) hum)
def inPlaceModAddTop (M : ℕ) (u0 cin : Option (Wire M)) : TempPhaseProg M :=
  if hM : 1 ≤ M then
    let t0 : Wire M := ⟨0, hM⟩
    let p1 : TempPhaseProg M := match u0 with
      | none => .nil
      | some u =>
          if hu : 0 < u.val then .seq .nil (.cliff (.cnot u t0 (wire_ne_of_gt hu))) else .nil
    match cin with
    | none => p1
    | some c => if hc : 0 < c.val then .seq p1 (.cliff (.cnot c t0 (wire_ne_of_gt hc))) else p1
  else .nil
@[simp] theorem inPlaceModAddTop_countTempAnd (M : ℕ) (u0 cin : Option (Wire M)) : (inPlaceModAddTop
    M u0 cin).countTempAnd = 0 := by
  unfold inPlaceModAddTop
  split_ifs with hM
  · rcases u0 with _ | u
    all_goals rcases cin with _ | c
    all_goals dsimp only
    all_goals try split_ifs
    all_goals simp [TempPhaseProg.countTempAnd]
  · rfl
def inPlaceModAddRec (M : ℕ) :
    ℕ → ℕ → (ℕ → Option (Wire M)) → Option (Wire M) → TempPhaseProg M
  | 0, _cur, uMSB, cin => inPlaceModAddTop M (uMSB 0) cin
  | q + 1, cur, uMSB, cin =>
      if hM : q + 1 < M ∧ cur + 1 ≤ M then
        let tq : Wire M := ⟨q + 1, hM.1⟩
        let next := inPlaceModAddRec M q (cur + 1) uMSB (some ⟨cur, hM.2⟩)
        match uMSB (q + 1), cin with
        | none, none => inPlaceModAddRec M q cur uMSB none
        | some u, none => if hu : q + 1 < u.val ∧ u.val < cur then
            gidneyHalfStep cur hM.2 u tq (wire_ne_of_gt hu.1) hu.2 (lt_trans hu.1 hu.2) next else
              .nil
        | none, some c => if hc : q + 1 < c.val ∧ c.val < cur then
            gidneyHalfStep cur hM.2 c tq (wire_ne_of_gt hc.1) hc.2 (lt_trans hc.1 hc.2) next else
              .nil
        | some u, some c =>
            if huc : q + 1 < u.val ∧ u.val < cur ∧ q + 1 < c.val ∧ c.val < cur ∧ c ≠ u then
              gidneyFullStep cur hM.2 u tq c (wire_ne_of_gt huc.1) (wire_ne_of_gt huc.2.2.1)
                huc.2.2.2.2 huc.2.1 (lt_trans huc.1 huc.2.1) huc.2.2.2.1 next
            else .nil
      else .nil
theorem inPlaceModAddRec_countTempAnd_le (M : ℕ) :
    ∀ (q cur : ℕ) (uMSB : ℕ → Option (Wire M)) (cin : Option (Wire M)),
      (inPlaceModAddRec M q cur uMSB cin).countTempAnd ≤ q
  | 0, _, _, _ => by simp [inPlaceModAddRec]
  | q + 1, cur, uMSB, cin => by
      simp only [inPlaceModAddRec]
      split_ifs with hM
      · have ihc := inPlaceModAddRec_countTempAnd_le M q (cur + 1) uMSB (some ⟨cur, hM.2⟩)
        rcases uMSB (q + 1) with _ | u
        all_goals rcases cin with _ | c
        all_goals dsimp only
        · exact le_trans (inPlaceModAddRec_countTempAnd_le M q cur uMSB none) (by omega)
        all_goals split_ifs
        all_goals simp only [gidneyHalfStep_countTempAnd, gidneyFullStep_countTempAnd,
          TempPhaseProg.countTempAnd]
        all_goals omega
      · simp [TempPhaseProg.countTempAnd]
private theorem inPlaceModAddTop_spec {M : ℕ} (cur : ℕ) (hcur : 0 < cur) (hcur_M : cur ≤ M) (u0
    cin : Option (Wire M)) (hu_lo : ∀ w, u0 = some w → 0 < w.val)
    (hu_hi : ∀ w, u0 = some w → w.val < cur) (hc_lo : ∀ c, cin = some c → 0 < c.val) (hc_hi : ∀ c,
      cin = some c → c.val < cur) : ∃ fTarget : BitAssignment M → BitAssignment M,
    TargetBlock M 1 (M - cur) fTarget (fun _ ↦ 0) (inPlaceModAddTop M u0 cin) ∧ ∀ β : BitAssignment
      M, cleanRem M (M - cur) β → msbPrefixVal 1 (by omega) (fTarget β) =
    (msbPrefixVal 1 (by omega) β + optBitVal u0 β + optBitVal cin β) % 2 := by
  have hz2 : ∀ a b : ZMod 2, (a + b).val = (a.val + b.val) % 2 := by decide
  have hM : 1 ≤ M := by omega
  let addOpt (p : TempPhaseProg M) (o : Option (Wire M)) : TempPhaseProg M :=
    match o with
    | none => p
    | some w => if hw : 0 < w.val then .seq p (.cliff (.cnot w ⟨0, hM⟩ (wire_ne_of_gt hw))) else p
  have hStep : ∀ (o : Option (Wire M)) (_ : ∀ w, o = some w → 0 < w.val) (_ : ∀ w, o = some w →
    w.val < cur) {f₀ : BitAssignment M → BitAssignment M}
      {p : TempPhaseProg M}, TargetBlock M 1 (M - cur) f₀ (fun _ ↦ 0) p → ∃ f₁, TargetBlock M 1 (M -
        cur) f₁ (fun _ ↦ 0) (addOpt p o) ∧ ∀ β, msbPrefixVal 1 (by omega) (f₁ β) =
      (msbPrefixVal 1 (by omega) (f₀ β) + optBitVal o β) % 2 := by
    intro o hlo hhi f₀ p hp
    rcases o with _ | w
    · refine ⟨f₀, hp, fun β ↦ ?_⟩
      dsimp only [msbPrefixVal, optBitVal]
      have hlt := ZMod.val_lt (f₀ β ⟨0, hM⟩)
      omega
    · have hw0 : 0 < w.val := hlo w rfl
      dsimp only [addOpt]
      rw [dite_true hw0]
      refine ⟨_, TargetBlock.seq_cnot_in_target (M := M) (targetEnd := 1) (rem := M - cur)
        (by omega) w ⟨0, hM⟩ (wire_ne_of_gt hw0) Nat.zero_lt_one (by omega)
        (by have := hhi w rfl; omega) hp, fun β ↦ ?_⟩
      simp only [msbPrefixVal, optBitVal, ↓reduceIte]
      rw [hz2]
      omega
  unfold inPlaceModAddTop
  rw [dite_true hM]
  dsimp only
  obtain ⟨f₁, hTB₁, hVal₁⟩ := hStep u0 hu_lo hu_hi TargetBlock.nil_one
  obtain ⟨f₂, hTB₂, hVal₂⟩ := hStep cin hc_lo hc_hi hTB₁
  exact ⟨f₂, hTB₂, fun β _ ↦ by
    rw [hVal₂ β, hVal₁ β, Nat.mod_add_mod]
    rfl⟩
theorem inPlaceModAddRec_spec {M : ℕ} :
    ∀ (q cur : ℕ) (hq_cur : q < cur) (hcur_M : cur + q ≤ M)
      (uMSB : ℕ → Option (Wire M))
      (_hu_lo : ∀ m w, m ≤ q → uMSB m = some w → q < w.val)
      (_hu_hi : ∀ m w, m ≤ q → uMSB m = some w → w.val < cur)
      (_hu_disj : ∀ m₁ m₂ w₁ w₂, m₁ < m₂ → m₂ ≤ q →
        uMSB m₁ = some w₁ → uMSB m₂ = some w₂ → w₁ ≠ w₂)
      (cin : Option (Wire M))
      (_hc_lo : ∀ c, cin = some c → q < c.val)
      (_hc_hi : ∀ c, cin = some c → c.val < cur)
      (_hc_ne : ∀ m w c, m ≤ q → uMSB m = some w → cin = some c → c ≠ w),
      ∃ fTarget : BitAssignment M → BitAssignment M,
        TargetBlock M (q + 1) (M - cur) fTarget (fun _ ↦ 0)
          (inPlaceModAddRec M q cur uMSB cin) ∧
        ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          msbPrefixVal (q + 1) (by omega) (fTarget β) =
            (msbPrefixVal (q + 1) (by omega) β +
              optMsbVal uMSB (q + 1) β + optBitVal cin β) % 2 ^ (q + 1)
  | 0, cur, hq_cur, hcur_M, uMSB, hu_lo, hu_hi, _, cin, hc_lo, hc_hi, _ => by
      obtain ⟨fT, hTB, hVal⟩ := inPlaceModAddTop_spec cur hq_cur (by omega) (uMSB 0) cin
        (fun w hw ↦ hu_lo 0 w le_rfl hw) (fun w hw ↦ hu_hi 0 w le_rfl hw) hc_lo hc_hi
      exact ⟨fT, hTB, fun β hβ ↦ by simpa [inPlaceModAddRec, optMsbVal] using hVal β hβ⟩
  | q + 1, cur, hq_cur, hcur_M, uMSB, hu_lo, hu_hi, hu_disj, cin, hc_lo, hc_hi, hc_ne => by
      have hM : q + 1 < M ∧ cur + 1 ≤ M := ⟨by omega, by omega⟩
      let tq : Wire M := ⟨q + 1, hM.1⟩
      let cout : Wire M := ⟨cur, hM.2⟩
      have hlt2 : ∀ (x b : ℕ), x < 2 ^ (q + 1) → b < 2 → 2 * x + b < 2 ^ (q + 1 + 1) :=
        fun x b hx hb ↦ by
          rw [pow_succ]
          omega
      have hRecCarry := inPlaceModAddRec_spec q (cur + 1) (by omega) (by omega) uMSB
        (fun m w hm hw ↦ Nat.lt_of_succ_lt (hu_lo m w (by omega) hw))
        (fun m w hm hw ↦ Nat.lt_succ_of_lt (hu_hi m w (by omega) hw))
        (fun m₁ m₂ w₁ w₂ h₁ h₂ ↦ hu_disj m₁ m₂ w₁ w₂ h₁ (by omega))
        (some cout)
        (fun _ hc ↦ by cases hc; dsimp [cout]; omega)
        (fun _ hc ↦ by cases hc; dsimp [cout]; omega)
        (fun m w _ hm hw hc ↦ by cases hc; exact wire_ne_of_gt (hu_hi m w (by omega) hw))
      have halfStep : ∀ (x : Wire M) (hcond : q + 1 < x.val ∧ x.val < cur) (uBit cBit :
        BitAssignment M → ℕ) (_ : ∀ β, optBitVal (uMSB (q + 1)) β = uBit β) (_ : ∀ β, optBitVal cin
        β = cBit β)
          (_ : ∀ β, (β x).val = uBit β + cBit β), ∃ fT, TargetBlock M (q + 2) (M - cur) fT (fun _ ↦
            0) (gidneyHalfStep cur hM.2 x tq (wire_ne_of_gt hcond.1) hcond.2
          (lt_trans hcond.1 hcond.2) (inPlaceModAddRec M q (cur + 1) uMSB (some cout))) ∧ ∀ β,
            cleanRem M (M - cur) β → msbPrefixVal (q + 2) (by omega) (fT β) =
          (msbPrefixVal (q + 2) (by omega) β + optMsbVal uMSB (q + 2) β + optBitVal cin β) % 2 ^ (q
            + 2) := by
        intro x hcond uBit cBit hub hcb hsum
        obtain ⟨fIn, hTBIn, hValIn⟩ := hRecCarry
        refine ⟨_, TargetBlock.gidneyHalfStep_block (M := M) (targetEnd := q + 1) cur hM.2 x tq
          (wire_ne_of_gt hcond.1) rfl hcond.1 hcond.2 (lt_trans hcond.1 hcond.2) hTBIn,
          fun β hβ ↦ ?_⟩
        let β₁ := Function.update β cout (β x * β tq)
        have hpre1 : msbPrefixVal (q + 1) (by omega)
            (fun w ↦ if w = tq then β tq + β x else fIn β₁ w) =
            msbPrefixVal (q + 1) (by omega) (fIn β₁) :=
          msbPrefixVal_congr (by omega) fun w hw ↦ ite_eq_right (wire_ne_of_lt hw)
        rw [msbPrefixVal_succ (q := q + 1), msbPrefixVal_succ (q := q + 1),
          optMsbVal_succ (q := q + 1)]
        change (2 * msbPrefixVal (q + 1) _ (fun w ↦ if w = tq then β tq + β x else fIn β₁ w) +
          (if ⟨q + 1, _⟩ = tq then β tq + β x else fIn β₁ ⟨q + 1, _⟩).val) = _
        rw [hpre1,
          hValIn β₁ fun w hw ↦
            (Function.update_of_ne (wire_ne_of_gt (show cur < w.val by omega)) _ _).trans
              (hβ w (by omega)),
          msbPrefixVal_congr (by omega) fun w hw ↦
            Function.update_of_ne (wire_ne_of_lt (show w.val < cur by omega)) _ _,
          optMsbVal_congr fun m w _ h_um ↦
            Function.update_of_ne (wire_ne_of_lt (hu_hi m w (by omega) h_um)) _ _,
          show optBitVal (some cout) β₁ = (β x * β tq).val by
            dsimp only [optBitVal, β₁]
            rw [Function.update_self],
          hub β, hcb β, show (⟨q + 1, by omega⟩ : Wire M) = tq from rfl, ite_true rfl,
          ← Nat.mod_eq_of_lt (hlt2 _ _ (Nat.mod_lt _ (by positivity)) (ZMod.val_lt _))]
        have hbit := half_bit_arith (β x) (β tq)
        exact step_msb_mod_arith (q + 1) (msbPrefixVal (q + 1) (by omega) β)
          (optMsbVal uMSB (q + 1) β) (β x * β tq).val (β tq + β x).val (β tq).val
          (uBit β) (cBit β) (by have := hsum β; rw [add_comm (β tq) (β x)]; omega)
      unfold inPlaceModAddRec
      rw [dite_true hM]
      dsimp only
      rcases h_u : uMSB (q + 1) with _ | u
      · rcases cin with _ | c
        · obtain ⟨fIn, hTBIn, hValIn⟩ := inPlaceModAddRec_spec q cur (by omega) (by omega) uMSB
            (fun m w hm hw ↦ Nat.lt_of_succ_lt (hu_lo m w (by omega) hw))
            (fun m w hm hw ↦ hu_hi m w (by omega) hw)
            (fun m₁ m₂ w₁ w₂ h₁ h₂ ↦ hu_disj m₁ m₂ w₁ w₂ h₁ (by omega))
            none (fun _ hc ↦ by cases hc) (fun _ hc ↦ by cases hc)
            (fun _ _ _ _ _ hc ↦ by cases hc)
          let fOut : BitAssignment M → BitAssignment M := fun β w ↦
            if w.val < q + 1 then fIn β w else β w
          refine ⟨fOut, ⟨hTBIn.valid, fun β hβ w ↦ ?_, hTBIn.sign⟩, fun β hβ ↦ ?_⟩
          · rw [hTBIn.bits β hβ w]
            by_cases h1 : w.val < q + 1
            · rw [ite_true h1, ite_true (by omega)]
              dsimp only [fOut]
              rw [ite_true h1]
            · simp only [fOut, ite_false h1]
              split_ifs <;> rfl
          · have hpre : msbPrefixVal (q + 1) (by omega) (fOut β) =
                msbPrefixVal (q + 1) (by omega) (fIn β) :=
              msbPrefixVal_congr (by omega) fun w hw ↦ by
                dsimp only [fOut]
                exact ite_eq_left hw
            rw [msbPrefixVal_succ (q := q + 1), msbPrefixVal_succ (q := q + 1),
              optMsbVal_succ (q := q + 1), hpre,
              show fOut β ⟨q + 1, by omega⟩ = β ⟨q + 1, by omega⟩ by
                dsimp only [fOut]
                exact ite_eq_right (Nat.lt_irrefl _),
              hValIn β hβ,
              ← Nat.mod_eq_of_lt (hlt2 _ _ (Nat.mod_lt _ (by positivity)) (ZMod.val_lt _))]
            simpa [h_u, optBitVal] using step_msb_mod_arith (q + 1)
              (msbPrefixVal (q + 1) (by omega) β) (optMsbVal uMSB (q + 1) β)
              0 (β ⟨q + 1, by omega⟩).val (β ⟨q + 1, by omega⟩).val 0 0 (by omega)
        · have hcond : q + 1 < c.val ∧ c.val < cur := ⟨hc_lo c rfl, hc_hi c rfl⟩
          dsimp only
          rw [dite_true hcond]
          exact halfStep c hcond (fun _ ↦ 0) (fun β ↦ (β c).val)
            (fun _ ↦ by simp [h_u, optBitVal]) (fun _ ↦ rfl) (fun _ ↦ (Nat.zero_add _).symm)
      · rcases cin with _ | c
        · have hcond : q + 1 < u.val ∧ u.val < cur :=
            ⟨hu_lo (q + 1) u le_rfl h_u, hu_hi (q + 1) u le_rfl h_u⟩
          dsimp only
          rw [dite_true hcond]
          exact halfStep u hcond (fun β ↦ (β u).val) (fun _ ↦ 0)
            (fun _ ↦ by simp [h_u, optBitVal]) (fun _ ↦ rfl) (fun _ ↦ rfl)
        · have hcu : c ≠ u := hc_ne (q + 1) u c le_rfl h_u rfl
          have hcond : q + 1 < u.val ∧ u.val < cur ∧ q + 1 < c.val ∧ c.val < cur ∧ c ≠ u :=
            ⟨hu_lo (q + 1) u le_rfl h_u, hu_hi (q + 1) u le_rfl h_u, hc_lo c rfl, hc_hi c rfl, hcu⟩
          dsimp only
          rw [dite_true hcond]
          have hut : u ≠ tq := wire_ne_of_gt hcond.1
          have hct : c ≠ tq := wire_ne_of_gt hcond.2.2.1
          obtain ⟨fIn, hTBIn, hValIn⟩ := hRecCarry
          refine ⟨_, TargetBlock.gidneyFullStep_block (M := M) (targetEnd := q + 1) cur hM.2 u tq
            c hut hct hcu rfl hcond.1 hcond.2.2.1 hcond.2.1 (lt_trans hcond.1 hcond.2.1)
            hcond.2.2.2.1 hTBIn, fun β hβ ↦ ?_⟩
          let β₁ := gidneyFullStepInnerAssign cur hM.2 u tq c hut hct hcu hcond.2.2.2.1 β
          have hClean₁ : cleanRem M (M - (cur + 1)) β₁ := fun w hw ↦ by
            dsimp only [β₁]
            rw [gidneyFullStepInnerAssign_other cur hM.2 u tq c hut hct hcu hcond.2.2.2.1 β w
              (wire_ne_of_gt (by omega)) (wire_ne_of_gt (show q + 1 < w.val by omega))
              (wire_ne_of_gt (show cur < w.val by omega))]
            exact hβ w (by omega)
          have hpre1 : msbPrefixVal (q + 1) (by omega) (fun w ↦ if w = tq then β u + β tq +
            β c else fIn β₁ w) = msbPrefixVal (q + 1) (by omega) (fIn β₁) :=
            msbPrefixVal_congr (by omega) fun w hw ↦ ite_eq_right (wire_ne_of_lt hw)
          have hpreB : msbPrefixVal (q + 1) (by omega) β₁ = msbPrefixVal (q + 1) (by omega) β :=
            msbPrefixVal_congr (by omega) fun w hw ↦
              gidneyFullStepInnerAssign_other cur hM.2 u tq c hut hct hcu hcond.2.2.2.1 β w
                (wire_ne_of_lt (by omega)) (wire_ne_of_lt hw)
                (wire_ne_of_lt (show w.val < cur by omega))
          have huB : optMsbVal uMSB (q + 1) β₁ = optMsbVal uMSB (q + 1) β :=
            optMsbVal_congr fun m w hm h_um ↦
              gidneyFullStepInnerAssign_other cur hM.2 u tq c hut hct hcu hcond.2.2.2.1 β w
                (hu_disj m (q + 1) w u hm le_rfl h_um h_u)
                (wire_ne_of_gt (hu_lo m w (by omega) h_um))
                (wire_ne_of_lt (hu_hi m w (by omega) h_um))
          have hco : optBitVal (some cout) β₁ = ((β u + β c) * (β tq + β c) + β c).val := by
            dsimp only [optBitVal, β₁]
            rw [gidneyFullStepInnerAssign_cout cur hM.2 u tq c hut hct hcu hcond.2.2.2.1 β]
          rw [msbPrefixVal_succ (q := q + 1), msbPrefixVal_succ (q := q + 1), optMsbVal_succ (q :=
            q + 1), hpre1, hValIn β₁ hClean₁, hpreB, huB, hco]
          simp only [h_u, optBitVal]
          rw [show (⟨q + 1, by omega⟩ : Wire M) = tq from rfl, ite_true rfl,
            ← Nat.mod_eq_of_lt (hlt2 _ _ (Nat.mod_lt _ (by positivity)) (ZMod.val_lt _))]
          have hbit := gidney_bit_arith (β u) (β tq) (β c)
          exact step_msb_mod_arith (q + 1) (msbPrefixVal (q + 1) (by omega) β)
            (optMsbVal uMSB (q + 1) β) ((β u + β c) * (β tq + β c) + β c).val
            (β u + β tq + β c).val (β tq).val (β u).val (β c).val (by omega)
private theorem mod_of_lt_two_mul {a P : ℕ} (h : a < 2 * P) : a % P = if a < P then a else a - P :=
  by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
theorem complement_mod_add_arith {P X D : ℕ} (hX : X < P) : (P - 1) - (((P - 1 - X) + D) % P) = (X +
    (P - D % P)) % P := by
  have hr : D % P < P := Nat.mod_lt D (by omega)
  rw [show ((P - 1 - X) + D) % P = ((P - 1 - X) + D % P) % P by simp [Nat.add_mod],
    mod_of_lt_two_mul (a := (P - 1 - X) + D % P) (by omega),
    mod_of_lt_two_mul (a := X + (P - D % P)) (by omega)]
  split_ifs <;> omega
theorem catModAddUnitary_congr_mod (kSys B : ℕ) [NeZero (2 ^ (kSys + B))] {Δ₁ Δ₂ : BitAssignment
    kSys → ℕ} (h : ∀ γ, Δ₁ γ % 2 ^ B = Δ₂ γ % 2 ^ B) :
    catModAddUnitary kSys B Δ₁ = catModAddUnitary kSys B Δ₂ := by
  let rSys0 : QRegister kSys (kSys + B) := .block 0 kSys (by omega)
  let rCat0 : QRegister B (kSys + B) := .block kSys B le_rfl
  have hdisj : rSys0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys B (by omega) (by omega) (by omega)
  have hid : rSys0.concat rCat0 hdisj = QRegExt.idReg _ := by
    refine SinglePassNuclearTwist288Alt.qreg_ext fun i ↦ Fin.ext ?_
    by_cases hi : i.val < kSys
    · rw [show i = Fin.castAdd B ⟨i.val, hi⟩ from Fin.ext rfl, QRegister.concat_apply_left]
      exact Nat.zero_add i.val
    · rw [show i = Fin.natAdd kSys ⟨i.val - kSys, by omega⟩ from Fin.ext (by dsimp; omega),
        QRegister.concat_apply_right]
      rfl
  refine Subtype.ext (matrix_ext_basisKet fun β ↦ ?_)
  let m₁ : Fin (2 ^ B) := ⟨(regVal rCat0 β + Δ₁ (fun q ↦ β (rSys0 q))) % 2 ^ B,
    Nat.mod_lt _ (by positivity)⟩
  let β₁ : BitAssignment (kSys + B) :=
    basisBits (kSys + B) (rCat0.replaceIndex ((basisBitsEquiv (kSys + B)).symm β) m₁)
  have hout₁ : ∀ w, w ∉ rCat0.image → β₁ w = β w := fun w hw ↦ by
    simp only [β₁, rCat0.basisBits_replaceIndex_of_not_mem _ _ w
      (fun ⟨j, hj⟩ ↦ hw ((QRegister.mem_image rCat0 w).mpr ⟨j, hj⟩)),
      NuclearTwistRealizes.basisBits_symm_apply]
  have hval₁ : regVal rCat0 β₁ = m₁.val := by
    rw [regVal, show (fun j ↦ β₁ (rCat0 j)) = basisBits B m₁ from
      funext fun j ↦ rCat0.basisBits_replaceIndex_apply _ m₁ j, bitsVal_basisBits]
  have hev₁ := (catModAddUnitary_mulVec_basisKet rSys0 rCat0 hdisj Δ₁ (fun _ ↦ β₁) β hout₁
    hval₁).symm
  have hev₂ := (catModAddUnitary_mulVec_basisKet rSys0 rCat0 hdisj Δ₂ (fun _ ↦ β₁) β hout₁
    (by rw [hval₁]; dsimp only [m₁]; rw [Nat.add_mod, h _, ← Nat.add_mod])).symm
  rw [hid] at hev₁ hev₂
  simp only [embedUnitary_idReg_eq] at hev₁ hev₂
  exact hev₁.trans hev₂.symm
theorem catModAddUnitary_inv_eq (kSys B : ℕ) [NeZero (2 ^ (kSys + B))] (Δ : BitAssignment kSys →
    ℕ) : (catModAddUnitary kSys B Δ)⁻¹ = catModAddUnitary kSys B (fun γ ↦ 2 ^ B - Δ γ % 2 ^ B) := by
  apply mul_eq_one_iff_inv_eq.mp
  rw [catModAddUnitary_mul, catModAddUnitary_congr_mod kSys B (Δ₂ := fun _ ↦ 0)]
  · exact catModAddUnitary_one kSys B
  · intro γ
    have hlt : Δ γ % 2 ^ B < 2 ^ B := Nat.mod_lt _ (by positivity)
    by_cases hr : Δ γ % 2 ^ B = 0
    · simp [hr]
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (show 2 ^ B - Δ γ % 2 ^ B < 2 ^ B by omega),
        show 2 ^ B - Δ γ % 2 ^ B + Δ γ % 2 ^ B = 2 ^ B by omega, Nat.mod_self, Nat.zero_mod]
def xPrefix {M : ℕ} : (q : ℕ) → (q ≤ M) → CliffProg M
  | 0, _ => .nil
  | q + 1, hq => .seq (xPrefix q (Nat.le_of_succ_le hq)) (.x ⟨q, hq⟩)
theorem xPrefix_eval {M : ℕ} :
    ∀ (q : ℕ) (hq : q ≤ M) (β : BitAssignment M) (w : Wire M),
      (xPrefix q hq).eval β w = if w.val < q then β w + 1 else β w
  | 0, _, _, _ => by simp [xPrefix, CliffProg.eval]
  | q + 1, hq, β, w => by
      simp only [xPrefix, CliffProg.eval]
      by_cases hw : w = ⟨q, hq⟩
      · subst hw
        rw [Function.update_self, xPrefix_eval q (Nat.le_of_succ_le hq) β ⟨q, hq⟩,
          ite_false (Nat.lt_irrefl _), ite_true (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hw, xPrefix_eval q (Nat.le_of_succ_le hq) β w]
        by_cases h1 : w.val < q
        · rw [ite_true h1, ite_true (Nat.lt_succ_of_lt h1)]
        · rw [ite_false h1, ite_false fun h2 ↦ hw (Fin.ext (by dsimp; omega))]
theorem msbPrefixVal_lt {M : ℕ} :
    ∀ (q : ℕ) (hq : q ≤ M) (β : BitAssignment M), msbPrefixVal q hq β < 2 ^ q
  | 0, _, _ => by simp [msbPrefixVal]
  | q + 1, hq, β => by
      have ih := msbPrefixVal_lt q (by omega) β
      have hb := ZMod.val_lt (β ⟨q, hq⟩)
      rw [msbPrefixVal_succ, pow_succ]
      omega
theorem msbPrefixVal_xPrefix {M : ℕ} :
    ∀ (q : ℕ) (hq : q ≤ M) (β : BitAssignment M),
      msbPrefixVal q hq ((xPrefix q hq).eval β) = 2 ^ q - 1 - msbPrefixVal q hq β
  | 0, _, _ => rfl
  | q + 1, hq, β => by
      have hz : ∀ z : ZMod 2, (z + 1).val = 1 - z.val := by decide
      have hcongr : msbPrefixVal q (by omega) ((xPrefix (q + 1) hq).eval β) = msbPrefixVal q (by
        omega) ((xPrefix q (Nat.le_of_succ_le hq)).eval β) :=
        msbPrefixVal_congr (by omega) fun w hw ↦ by
          rw [xPrefix_eval, xPrefix_eval, ite_true (Nat.lt_succ_of_lt hw), ite_true hw]
      have ih := msbPrefixVal_lt q (by omega) β
      have hb := ZMod.val_lt (β ⟨q, hq⟩)
      rw [msbPrefixVal_succ, msbPrefixVal_succ, hcongr,
        msbPrefixVal_xPrefix q (Nat.le_of_succ_le hq) β,
        show (xPrefix (q + 1) hq).eval β ⟨q, hq⟩ = β ⟨q, hq⟩ + 1 by
          rw [xPrefix_eval, ite_true (Nat.lt_succ_self _)],
        hz, pow_succ]
      omega
def revReg {W n : ℕ} (rAcc : QRegister W n) : QRegister W n :=
  ⟨⟨fun i ↦ rAcc ⟨W - 1 - i.val, by omega⟩,
    fun _ _ hij ↦ Fin.ext (by
      have := congrArg Fin.val (rAcc.wires.injective hij); dsimp at this; omega)⟩⟩
theorem revReg_image_sub {W n : ℕ} (rAcc : QRegister W n) :
    (revReg rAcc).image ⊆ rAcc.image := fun w hw ↦ by
  obtain ⟨i, rfl⟩ := (QRegister.mem_image (revReg rAcc) w).mp hw
  exact (QRegister.mem_image rAcc _).mpr ⟨_, rfl⟩
def mkModAddCombReg {W kCore mClean mWork n : ℕ} (rCore : QRegister kCore n) (rAcc : QRegister W n)
    (rWork : QRegister mWork n) (hCA : rCore.DisjointWires rAcc)
    (hCW : rCore.DisjointWires rWork) (hAW : rAcc.DisjointWires rWork) (hmWork : mClean ≤ mWork) :
      QRegister ((W + kCore) + mClean) n :=
  let hARC : (revReg rAcc).DisjointWires rCore :=
    QRegExt.disjointWires_mono_left (QRegister.disjoint_comm.mp hCA) (revReg_image_sub rAcc)
  let hARW : (revReg rAcc).DisjointWires rWork :=
    QRegExt.disjointWires_mono_left hAW (revReg_image_sub rAcc)
  let rActInt : QRegister (W + kCore) n := (revReg rAcc).concat rCore hARC
  let hActW : rActInt.DisjointWires rWork := QRegExt.disjointWires_concat_left hARW hCW
  rActInt.concat (rWork.slice 0 mClean ((Nat.zero_add mClean).le.trans hmWork))
    (QRegExt.disjointWires_mono_right hActW (QRegister.image_compose_subset rWork _))
theorem mkModAddCombReg_left_acc {W kCore mClean mWork n : ℕ} (rCore : QRegister kCore n) (rAcc :
    QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork) (hAW : rAcc.DisjointWires
      rWork) (hmWork : mClean ≤ mWork) (idx : Fin ((W + kCore) + mClean)) (hi : idx.val < W) :
    mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork idx = rAcc ⟨W - 1 - idx.val, by omega⟩ := by
  have h1 : idx = Fin.castAdd mClean (Fin.castAdd kCore ⟨idx.val, hi⟩) := Fin.ext rfl
  conv_lhs => rw [h1]
  unfold mkModAddCombReg
  rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  rfl
def invertModAddProg {M W : ℕ} (hW : W ≤ M) (p : TempPhaseProg M) : TempPhaseProg M :=
  .seq (.cliff (xPrefix W hW)) (.seq p (.cliff (xPrefix W hW)))
@[simp] theorem invertModAddProg_countTempAnd {M W : ℕ} (hW : W ≤ M) (p : TempPhaseProg M) :
    (invertModAddProg hW p).countTempAnd = p.countTempAnd := by
  simp [invertModAddProg, TempPhaseProg.countTempAnd]
theorem w_le_comb (W kCore mClean : ℕ) : W ≤ (W + kCore) + mClean :=
  Nat.le_add_right_of_le (Nat.le_add_right W kCore)
theorem TargetBlock.toCatModAddPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {n W kCore mClean mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : mClean ≤ mWork) (Δ : BitAssignment kCore → ℕ)
    {fTarget : BitAssignment ((W + kCore) + mClean) → BitAssignment ((W + kCore) + mClean)}
    {p : TempPhaseProg ((W + kCore) + mClean)}
    (hTB : TargetBlock ((W + kCore) + mClean) W mClean fTarget (fun _ ↦ 0) p)
    (hVal : ∀ β : BitAssignment ((W + kCore) + mClean), cleanRem ((W + kCore) + mClean) mClean β →
      msbPrefixVal W (by omega) (fTarget β) =
        (msbPrefixVal W (by omega) β +
          Δ (fun q : Fin kCore ↦ β (Fin.castAdd mClean (Fin.natAdd W q)))) % 2 ^ W) :
    let rComb := mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork
    let pInv := invertModAddProg (w_le_comb W kCore mClean) p
    let dFwd := (p.onRegister rComb).toDyn v
    let dInv := (pInv.onRegister rComb).toDyn v
    RealizesCleanPair (rCore.concat rAcc hCA) rWork (catModAddUnitary kCore W Δ) dFwd dInv ∧
      dFwd.count PrimitiveGate.TOFF = 0 ∧
      dInv.count PrimitiveGate.TOFF = 0 ∧
      dFwd.count PrimitiveGate.T = 4 * p.countTempAnd ∧
      dInv.count PrimitiveGate.T = 4 * p.countTempAnd := by
  intro rComb pInv dFwd dInv
  let Mtot := (W + kCore) + mClean
  have hWM : W ≤ Mtot := w_le_comb W kCore mClean
  have hrem : mClean ≤ Mtot := Nat.le_add_left mClean (W + kCore)
  let P_small := projZeroAll mClean (tailScr rComb mClean hrem)
  let P_work := projZeroAll mWork rWork.wires
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mWork _
  have htail_work : ∀ j : Fin mClean, tailScr rComb mClean hrem j = rWork ⟨j.val, by omega⟩ :=
    fun j ↦ by
      dsimp [tailScr, rComb, mkModAddCombReg]
      rw [show (⟨(Mtot - mClean) + j.val, by omega⟩ : Fin Mtot) = Fin.natAdd (W + kCore) j from
        Fin.ext (by dsimp [Mtot]; omega), QRegister.concat_apply_right, QRegister.slice_apply]
      exact congrArg rWork.wires (Fin.ext (Nat.zero_add _))
  have hsub : P_small * P_work = P_work := by
    apply matrix_ext_ket
    intro β
    simp only [P_small, P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · simp [hw, fun j : Fin mClean ↦ (congrArg β (htail_work j)).trans (hw ⟨j.val, by omega⟩),
        ket_projZeroAll]
    · simp [hw]
  have hrj : ∀ j : Fin W, rComb ⟨W - 1 - j.val, by omega⟩ = rAcc j := fun j ↦ by
    rw [mkModAddCombReg_left_acc rCore rAcc rWork hCA hCW hAW hmWork _ (by dsimp only; omega)]
    exact congrArg rAcc.wires (Fin.ext (by dsimp only; omega))
  have hCleanOf : ∀ (Δ' : BitAssignment kCore → ℕ) {fT' : BitAssignment Mtot → BitAssignment Mtot}
    {p' : TempPhaseProg Mtot}, TargetBlock Mtot W mClean fT' (fun _ ↦ 0) p' →
      (∀ β, cleanRem Mtot mClean β → msbPrefixVal W hWM (fT' β) = (msbPrefixVal W hWM β +
        Δ' (fun q : Fin kCore ↦ β (Fin.castAdd mClean (Fin.natAdd W q)))) % 2 ^ W) →
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rAcc hCA) rWork
        (catModAddUnitary kCore W Δ') ((p'.onRegister rComb).toDyn v) ∧
      ((p'.onRegister rComb).toDyn v).count PrimitiveGate.TOFF = 0 ∧ ((p'.onRegister rComb).toDyn
        v).count PrimitiveGate.T = 4 * p'.countTempAnd := by
    intro Δ' fT' p' hTB' hVal'
    refine ⟨?_, TempPhaseProg.toDyn_count_toff v _, by
      rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd]⟩
    have hMono := RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose mClean _) hPw hsub
      (realizes_of_validCleanRem v rComb p' mClean hrem hTB'.valid)
    have hUeq : ((p'.onRegister rComb).toToffCircuit).eval.1 * P_work = ((rCore.concat rAcc
      hCA).embedUnitary (catModAddUnitary kCore W Δ')).1 * P_work := by
      apply matrix_ext_ket
      intro β
      simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
      by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
      · simp only [hw, imp_true_iff, ↓reduceIte, eval_onRegister_prog_ket]
        let βloc : BitAssignment Mtot := fun idx ↦ β (rComb idx)
        have hCleanLoc : cleanRem Mtot mClean βloc := fun idx hidx ↦ by
          let j : Fin mClean := ⟨idx.val - (W + kCore), by dsimp [Mtot] at hidx; omega⟩
          dsimp only [βloc, rComb, mkModAddCombReg]
          rw [show idx = Fin.natAdd (W + kCore) j from Fin.ext (by dsimp [j]; omega),
            QRegister.concat_apply_right, QRegister.slice_apply]
          simpa using hw ⟨j.val, by omega⟩
        rw [hTB'.sign βloc hCleanLoc]
        change ((-1 : ℂ) ^ (0 : ZMod 2).val) • ket (writeRegProg β rComb (p'.evalBits βloc)) = _
        simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
        let β' := writeRegProg β rComb (p'.evalBits βloc)
        have hket_eq : ∀ η : BitAssignment n, ket η = basisKet η := fun _ ↦ rfl
        rw [hket_eq β', hket_eq β]
        apply catModAddUnitary_mulVec_basisKet rCore rAcc hCA Δ' (fun _ ↦ β') β
        · intro z hz
          by_cases hmem : z ∈ Set.range rComb.wires
          · obtain ⟨idx, rfl⟩ := hmem
            dsimp only [β']
            rw [writeRegProg_apply_reg, hTB'.bits βloc hCleanLoc idx, ite_eq_right fun hiW ↦ hz ?_]
            rw [mkModAddCombReg_left_acc rCore rAcc rWork hCA hCW hAW hmWork idx hiW]
            exact (QRegister.mem_image rAcc _).mpr ⟨_, rfl⟩
          · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
        · rw [show regVal rAcc β' = msbPrefixVal W hWM (fT' βloc) by
              rw [msbPrefixVal_eq_bitsVal_rev]
              refine congrArg bitsVal (funext fun j ↦ ?_)
              rw [← hrj j]
              dsimp only [β']
              rw [writeRegProg_apply_reg, hTB'.bits βloc hCleanLoc _,
                ite_eq_left (by dsimp; omega)],
            hVal' βloc hCleanLoc,
            show regVal rAcc β = msbPrefixVal W hWM βloc by
              rw [msbPrefixVal_eq_bitsVal_rev]
              exact congrArg bitsVal (funext fun j ↦ congrArg β (hrj j).symm),
            show (fun q : Fin kCore ↦ βloc (Fin.castAdd mClean (Fin.natAdd W q))) =
                fun q ↦ β (rCore q) from funext fun q ↦ by
              dsimp only [βloc, rComb, mkModAddCombReg]
              rw [QRegister.concat_apply_left, QRegister.concat_apply_right]]
      · simp [hw]
    have hTarget := RealizesCleanUnitary.congr_unitary hPw hMono hUeq
    intro M_obs
    obtain ⟨M_out, hM_out⟩ := PreservesStoreConst_toDyn v (p'.onRegister rComb) M_obs
    refine ⟨M_out, hM_out, ?_⟩
    have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
    rw [← show wp ((p'.onRegister rComb).toDyn v).compile (fun _ ↦ M_obs) default = M_out from
        congrFun hM_out default, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
    simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
      congrArg Subtype.val hconj
  have hFwdAll := hCleanOf Δ hTB hVal
  let xC := xPrefix W hWM
  let fInv : BitAssignment Mtot → BitAssignment Mtot := fun β ↦ xC.eval (fTarget (xC.eval β))
  have hxClean : ∀ β : BitAssignment Mtot, cleanRem Mtot mClean β →
      cleanRem Mtot mClean (xC.eval β) := fun β hβ w hw ↦ by
    rw [xPrefix_eval, ite_false (by dsimp [Mtot] at hw; omega)]
    exact hβ w hw
  have hpClean : ∀ β : BitAssignment Mtot, cleanRem Mtot mClean β →
      cleanRem Mtot mClean (p.evalBits β) := fun β hβ w hw ↦ by
    rw [hTB.bits β hβ w, ite_false (by dsimp [Mtot] at hw; omega)]
    exact hβ w hw
  have hTBInv : TargetBlock Mtot W mClean fInv (fun _ ↦ 0) pInv := by
    refine ⟨⟨mClean, by dsimp [Mtot]; omega, trivial, ⟨mClean, by dsimp [Mtot]; omega, hTB.valid,
      trivial, hpClean⟩, hxClean⟩, fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
    · dsimp only [pInv, invertModAddProg, TempPhaseProg.evalBits]
      have hc1 := hxClean β hβ
      by_cases hwW : w.val < W
      · rw [ite_true hwW, xPrefix_eval, ite_true hwW, hTB.bits (xC.eval β) hc1 w, ite_true hwW]
        dsimp only [fInv, xC]
        rw [xPrefix_eval, ite_true hwW]
      · rw [ite_false hwW, xPrefix_eval, ite_false hwW, hTB.bits (xC.eval β) hc1 w, ite_false hwW,
          xPrefix_eval, ite_false hwW]
    · dsimp only [pInv, invertModAddProg, TempPhaseProg.evalSign]
      change 0 + (p.evalSign (xC.eval β) + 0) = 0
      simp [hTB.sign (xC.eval β) (hxClean β hβ)]
  have hValInv : ∀ β : BitAssignment Mtot, cleanRem Mtot mClean β → msbPrefixVal W hWM
      (fInv β) = (msbPrefixVal W hWM β + (2 ^ W - Δ (fun q : Fin kCore ↦ β (Fin.castAdd mClean
      (Fin.natAdd W q))) % 2 ^ W)) % 2 ^ W := fun β hβ ↦ by
    dsimp only [fInv, xC]
    rw [msbPrefixVal_xPrefix W hWM, hVal ((xPrefix W hWM).eval β) (hxClean β hβ),
      msbPrefixVal_xPrefix W hWM β,
      show (fun q : Fin kCore ↦ (xPrefix W hWM).eval β (Fin.castAdd mClean (Fin.natAdd W q))) =
        fun q : Fin kCore ↦ β (Fin.castAdd mClean (Fin.natAdd W q)) from
        funext fun q ↦ by rw [xPrefix_eval, ite_false (by dsimp; omega)]]
    exact complement_mod_add_arith (msbPrefixVal_lt W hWM β)
  have hInvAll := hCleanOf (fun γ ↦ 2 ^ W - Δ γ % 2 ^ W) hTBInv hValInv
  refine ⟨⟨hFwdAll.1, ?_⟩, hFwdAll.2.1, hInvAll.2.1, hFwdAll.2.2, ?_⟩
  · rw [@catModAddUnitary_inv_eq kCore W ⟨by positivity⟩]
    exact hInvAll.1
  · rw [hInvAll.2.2, invertModAddProg_countTempAnd]
theorem inComb_lt_M {W kCore S q : ℕ} (u : Wire kCore) :
    W + u.val < (W + kCore) + (S + q) := by omega
theorem cur0_add_S_le_M (W kCore S q : ℕ) :
    (W + kCore) + S ≤ (W + kCore) + (S + q) := by omega
def popMsbMap {K M : ℕ} (outW : Fin K → Wire M) (L : ℕ) (m : ℕ) : Option (Wire M) :=
  if _hm : m < L then if hk : L - 1 - m < K then some (outW ⟨L - 1 - m, hk⟩) else none else none
private theorem optMsbVal_eq_finSum {M : ℕ} (uMSB : ℕ → Option (Wire M)) :
    ∀ (q : ℕ) (β : BitAssignment M),
      optMsbVal uMSB q β = ∑ i : Fin q, 2 ^ (q - 1 - i.val) * optBitVal (uMSB i.val) β
  | 0, _ => rfl
  | q + 1, β => by
      rw [optMsbVal_succ, optMsbVal_eq_finSum uMSB q β, Fin.sum_univ_castSucc, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) (by simp)
      dsimp
      rw [show q - i.val = (q - 1 - i.val) + 1 by omega, pow_succ]
      ring
theorem optMsbVal_popMsbMap_mod_eq {M : ℕ} (L : ℕ) (β : BitAssignment M) : ∀ (K : ℕ) (outW : Fin K →
    Wire M), optMsbVal (popMsbMap outW L) L β % 2 ^ L =
    (∑ k : Fin K, 2 ^ k.val * (β (outW k)).val) % 2 ^ L := by
  have hLHS : ∀ (K : ℕ) (outW : Fin K → Wire M), optMsbVal (popMsbMap outW L) L β = ∑ j : Fin L,
      2 ^ j.val * (if hk : j.val < K then (β (outW ⟨j.val, hk⟩)).val else 0) := fun K outW ↦ by
    rw [optMsbVal_eq_finSum]
    let eRev : Fin L ≃ Fin L := ⟨fun j ↦ ⟨L - 1 - j.val, by omega⟩,
      fun i ↦ ⟨L - 1 - i.val, by omega⟩, fun _ ↦ Fin.ext (by dsimp; omega),
      fun _ ↦ Fin.ext (by dsimp; omega)⟩
    rw [← Equiv.sum_comp eRev]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show L - 1 - (eRev j).val = j.val by dsimp [eRev]; omega]
    congr 1
    dsimp [popMsbMap, eRev]
    rw [ite_true (by omega)]
    by_cases hk : j.val < K
    · rw [dite_true (by omega), dite_true hk]
      exact congrArg (fun u ↦ (β (outW u)).val) (Fin.ext (by dsimp; omega))
    · rw [dite_false (by omega), dite_false hk]
      rfl
  intro K outW
  rw [hLHS K outW]
  induction K with
  | zero => simp
  | succ K ih =>
      have ihPrev : (∑ j : Fin L, 2 ^ j.val * (if hk : j.val < K then (β (outW ⟨j.val,
        by
          omega⟩)).val else 0)) % 2 ^ L = (∑ k : Fin K, 2 ^ k.castSucc.val *
        (β (outW k.castSucc)).val) % 2 ^ L :=
        ih (fun k ↦ outW k.castSucc)
      rw [Fin.sum_univ_castSucc]
      by_cases hKL : K < L
      · have hsplit : (∑ j : Fin L, 2 ^ j.val *
            (if hk : j.val < K + 1 then (β (outW ⟨j.val, hk⟩)).val else 0)) =
            (∑ j : Fin L, 2 ^ j.val *
              (if hk : j.val < K then (β (outW ⟨j.val, by omega⟩)).val else 0)) +
            2 ^ K * (β (outW (Fin.last K))).val := by
          have hpt : ∀ j : Fin L,
              2 ^ j.val * (if hk : j.val < K + 1 then (β (outW ⟨j.val, hk⟩)).val else 0) =
              2 ^ j.val * (if hk : j.val < K then (β (outW ⟨j.val, by omega⟩)).val else 0) +
                if j = ⟨K, hKL⟩ then 2 ^ K * (β (outW (Fin.last K))).val else 0 := fun j ↦ by
            by_cases hjK : j = ⟨K, hKL⟩
            · subst hjK
              rw [dite_true (by dsimp; omega), dite_false (by dsimp; omega), ite_true rfl]
              dsimp [Fin.last]
              omega
            · have hne : j.val ≠ K := fun hv ↦ hjK (Fin.ext hv)
              rw [ite_false hjK, add_zero]
              by_cases hjlt : j.val < K
              · rw [dite_true (by omega), dite_true hjlt]
              · rw [dite_false (by omega), dite_false hjlt]
          rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_add_distrib, Finset.sum_ite_eq',
            ite_true (Finset.mem_univ _)]
        rw [hsplit, Nat.add_mod, ihPrev, ← Nat.add_mod]
        rfl
      · have hsame : (∑ j : Fin L, 2 ^ j.val *
            (if hk : j.val < K + 1 then (β (outW ⟨j.val, hk⟩)).val else 0)) =
            ∑ j : Fin L, 2 ^ j.val *
              (if hk : j.val < K then (β (outW ⟨j.val, by omega⟩)).val else 0) :=
          Finset.sum_congr rfl fun j _ ↦ by rw [dite_true (by omega), dite_true (by omega)]
        have hdvd : 2 ^ K * (β (outW (Fin.last K))).val = (2 ^ (K - L) * (β (outW (Fin.last
          K))).val) * 2 ^ L := by
          rw [show 2 ^ K = 2 ^ (K - L) * 2 ^ L by rw [← pow_add, Nat.sub_add_cancel (by omega)]]
          ring
        simp only [Fin.val_castSucc, Fin.val_last] at ihPrev ⊢
        rw [hsame, ihPrev, hdvd, Nat.add_mul_mod_self_right]
def inCombWire {N W kCore S q : ℕ} (inCore : Fin N → Wire kCore) (i : Fin N) : Wire ((W + kCore) +
    (S + q)) := ⟨W + (inCore i).val, inComb_lt_M (inCore i)⟩
theorem inCombWire_injective {N W kCore S q : ℕ} {inCore : Fin N → Wire kCore} (hInj :
    Function.Injective inCore) : Function.Injective (inCombWire (W := W) (S := S) (q :=
    q) inCore) :=
  fun _ _ hij ↦ hInj (Fin.ext (Nat.add_left_cancel (congrArg Fin.val hij)))
theorem inCombWire_lt_cur0 {N W kCore S q : ℕ} (inCore : Fin N → Wire kCore) (i : Fin N) :
    (inCombWire (W := W) (S := S) (q := q) inCore i).val < W + kCore :=
  Nat.add_lt_add_left (inCore i).isLt W
def elecAxisBitWire {mPayload : ℕ} (w : Fin 3) (r : Fin 6) (e : Fin numElectrons) : Wire
    (fullSysCoreWires mPayload) := rElecSlotAxis (QRegExt.idReg _) e w r
theorem slot2AxisSum_eq_bitPlane_sum {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) : slot2AxisSum w γ = ∑ r : Fin 6, 2 ^
    r.val * ∑ e : Fin numElectrons, (γ (elecAxisBitWire w r e)).val := by
  unfold slot2AxisSum elecAxisBitWire regVal bitsVal
  simp_rw [show ∀ e : Fin numElectrons, (∑ r : Fin 6, (γ (rElecSlotAxis (QRegExt.idReg _)
      e w r)).val * 2 ^ r.val) = ∑ r : Fin 6, 2 ^ r.val * (γ (rElecSlotAxis (QRegExt.idReg _)
      e w r)).val from fun _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ (Finset.mul_sum _ _ _).symm
theorem count_seq_eq {Var : Type} {n k : ℕ} (g : PrimitiveGate k) (d₁ d₂ : DynamicCircuit Var n) :
    (d₁.seq d₂).count g = d₁.count g + d₂.count g := rfl
end SinglePassNuclearTwist288
end
end ModSinglePassNuclearTwist288

end QuantumComputation.Specs.StoppingPowerSolution
