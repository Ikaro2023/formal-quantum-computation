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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosSlots24SemConc

set_option Elab.async false

@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModProjZ512QftAndTwist288
@[expose] public section
namespace ProjZ512QftAndTwist288Alt
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
end ProjZ512QftAndTwist288Alt
namespace ProjZ512QftAndTwist288
open Operator QProg Matrix HermitianMat Real SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64WalkCircuit
open SpecsAux.PhaseGradCatalystCore
open NuclearTwistAndXor654Concrete hiding IntertwinesLocalCat
open NuclearTwistRealizes
open SpecsAux.DyadicSubgridToeplitz512AndShift
  (NyqGrid3D256 NyqFine3D512 omega512 omega512_zero omega512_add star_omega512 omega512_mul_512
  omega512_periodic_emod sum_omega512_of_abs_lt projSubGridElem256_3D)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
lemma ite_pos_8 {α : Type*} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := ite_eq_left hp
lemma ite_neg_8 {α : Type*} {p : Prop} [Decidable p] (hp : ¬p) (a b : α) :
    (if p then a else b) = b := ite_eq_right hp
lemma dite_pos_8 {α : Sort*} {p : Prop} [Decidable p] (hp : p) {a : p → α} {b : ¬p → α} :
    dite p a b = a hp := dite_eq_left hp
lemma dite_neg_8 {α : Sort*} {p : Prop} [Decidable p] (hp : ¬p) {a : p → α} {b : ¬p → α} :
    dite p a b = b hp := dite_eq_right hp
noncomputable def cfgProjZ512 (zP : NyqFine3D512) : Configuration where
  nuclei := fun _ w ↦ ((zP w).val : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / 512)
  projectileMomentum := 0
  momentum_le := by simp [waveNumberSq, waveVector, dotProduct]
theorem cellLength_ne_zero : cellVolume ^ ((1 : ℝ) / 3) ≠ 0 :=
  ne_of_gt (Real.rpow_pos_of_pos (by unfold cellVolume; norm_num) _)
theorem nuclearM48_cfgProjZ512_eq (zP : NyqFine3D512) (l : Fin 216) (w : Fin 3) :
    nuclearM48 (cfgProjZ512 zP) l w = 2 ^ 39 * (zP w).val := by
  have hz := (zP w).isLt
  have hL : cellVolume ^ (1 / 3 : ℝ) ≠ 0 := by simpa [one_div] using cellLength_ne_zero
  unfold nuclearM48 cfgProjZ512
  have hdiv : ((zP w).val : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / 512) / cellVolume ^ (1 / 3 : ℝ) =
      ((zP w).val : ℝ) / 512 := by field_simp [hL]
  have hfl : ⌊(2 ^ 48 : ℝ) * (((zP w).val : ℝ) / 512) + 1 / 2⌋₊ = 2 ^ 39 * (zP w).val := by
    rw [show (2 ^ 48 : ℝ) * (((zP w).val : ℝ) / 512) + 1 / 2 =
      ((2 ^ 39 * (zP w).val : ℕ) : ℝ) + 1 / 2 by push_cast; ring]
    exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by norm_num, by push_cast; linarith⟩
  rw [hdiv, Int.fract_eq_self.mpr ⟨by positivity,
    (div_lt_one (by norm_num)).mpr (by exact_mod_cast hz)⟩, hfl]
  exact Nat.mod_eq_of_lt (by omega)
def projGridEquiv24 : Fin (2 ^ 24) ≃ NyqGrid3D256 where
  toFun u := fun w ↦ ⟨(u.val / 2 ^ (8 * w.val)) % 256, by omega⟩
  invFun g := ⟨(g 0).val + 256 * (g 1).val + 65536 * (g 2).val, by
    have := (g 0).isLt; have := (g 1).isLt; have := (g 2).isLt; omega⟩
  left_inv u := by
    have := u.isLt
    ext
    change ((u.val / 1) % 256 + 256 * ((u.val / 256) % 256) + 65536 * ((u.val / 65536) % 256)) =
      u.val
    omega
  right_inv g := by
    have := (g 0).isLt
    have := (g 1).isLt
    have := (g 2).isLt
    funext w
    ext
    fin_cases w <;> (dsimp; omega)
def projTwosMom3D (uIdx : Fin (2 ^ 24)) : Fin 3 → ℤ :=
  fun w ↦ Slots01AndGridGuardBridge.twosComp8Int (projGridEquiv24 uIdx w)
def twosComp8ToOffsetEquiv : Fin 256 ≃ Fin 256 where
  toFun u :=
    ⟨if u.val < 128 then u.val + 128 else u.val - 128, by have := u.isLt; split_ifs <;> omega⟩
  invFun v :=
    ⟨if v.val < 128 then v.val + 128 else v.val - 128, by have := v.isLt; split_ifs <;> omega⟩
  left_inv u := by have := u.isLt; ext; dsimp; split_ifs <;> omega
  right_inv v := by have := v.isLt; ext; dsimp; split_ifs <;> omega
def half512Equiv : Fin 2 × Fin 256 ≃ Fin 512 where
  toFun p := ⟨256 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun x := (⟨x.val / 256, by have := x.isLt; omega⟩, ⟨x.val % 256, by omega⟩)
  left_inv := fun ⟨s, k⟩ ↦ by
    have := s.isLt
    have := k.isLt
    apply Prod.ext <;> ext <;> dsimp <;> omega
  right_inv x := by ext; dsimp; omega
theorem twosComp8Int_of_offsetEquiv_symm (k : Fin 256) :
    Slots01AndGridGuardBridge.twosComp8Int
    (twosComp8ToOffsetEquiv.symm k) = (k.val : ℤ) - 128 := by
  have := k.isLt
  unfold twosComp8ToOffsetEquiv Slots01AndGridGuardBridge.twosComp8Int
  dsimp
  split_ifs <;> omega
noncomputable def uProjPlus512TwosMat1D (b : Fin 2) : Operator 256 := Matrix.of fun y u ↦
    (1 / 16 : ℂ) * omega512 (Slots01AndGridGuardBridge.twosComp8Int
    u * (2 * (y.val : ℤ) + (b.val : ℤ)))
theorem uProjPlus512TwosMat1D_mul_conjTranspose (b : Fin 2) :
    uProjPlus512TwosMat1D b * (uProjPlus512TwosMat1D b)ᴴ = 1 := by
  ext y₁ y₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm (u : Fin 256) : uProjPlus512TwosMat1D b y₁ u * (uProjPlus512TwosMat1D b)ᴴ u y₂ =
      (1 / 256 : ℂ) * omega512 (Slots01AndGridGuardBridge.twosComp8Int u *
        (2 * ((y₁.val : ℤ) - (y₂.val : ℤ)))) := by
    change uProjPlus512TwosMat1D b y₁ u * star (uProjPlus512TwosMat1D b y₂ u) = _
    simp only [uProjPlus512TwosMat1D, Matrix.of_apply, star_mul', star_div₀, star_one,
      (by norm_num : star (16 : ℂ) = 16), star_omega512]
    rw [show ∀ a c : ℂ, (1 / 16 : ℂ) * a * ((1 / 16 : ℂ) * c) = (1 / 256 : ℂ) * (a * c) from
      fun _ _ ↦ by ring, ← omega512_add]
    exact congrArg _ (by ring)
  let d : ℤ := (y₁.val : ℤ) - (y₂.val : ℤ)
  have hshift (k : Fin 256) :
      omega512 (((k.val : ℤ) - 128) * (2 * ((y₁.val : ℤ) - (y₂.val : ℤ)))) =
        omega512 (-256 * d) * omega512 ((2 * d) * (k.val : ℤ)) := by
    dsimp only [d]
    rw [← omega512_add]
    exact congrArg _ (by ring)
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Equiv.sum_comp twosComp8ToOffsetEquiv.symm]
  simp_rw [twosComp8Int_of_offsetEquiv_symm, hshift, ← Finset.mul_sum]
  by_cases hy : y₁ = y₂
  · subst hy
    simp [d, omega512_zero]
  · rw [ite_neg_8 hy]
    have hy1 := y₁.isLt
    have hy2 := y₂.isLt
    have hd : -512 < 2 * d ∧ 2 * d < 512 ∧ 2 * d ≠ 0 := by
      have hne : y₁.val ≠ y₂.val := Fin.val_ne_of_ne hy
      dsimp [d]
      omega
    have hsum : (2 : ℂ) * (∑ k : Fin 256, omega512 ((2 * d) * (k.val : ℤ))) = 0 := by
      refine (?_ : _ = ∑ x : Fin 512, omega512 ((2 * d) * (x.val : ℤ))).trans
        ((sum_omega512_of_abs_lt hd.1 hd.2.1).trans (ite_neg_8 hd.2.2 _ _))
      rw [← Equiv.sum_comp half512Equiv, Fintype.sum_prod_type, Fin.sum_univ_two]
      simp_rw [show ∀ k : Fin 256, ((half512Equiv (0, k)).val : ℤ) = k.val by simp [half512Equiv],
        show ∀ k : Fin 256, omega512 ((2 * d) * ((half512Equiv (1, k)).val : ℤ)) =
          omega512 ((2 * d) * (k.val : ℤ)) from fun k ↦ by
            rw [show ((half512Equiv (1, k)).val : ℤ) = 256 + (k.val : ℤ) by simp [half512Equiv],
              show (2 * d) * (256 + (k.val : ℤ)) = (2 * d) * (k.val : ℤ) + d * 512 by ring,
              omega512_add, omega512_mul_512, mul_one]]
      ring
    rw [(mul_eq_zero.mp hsum).resolve_left (by norm_num)]
    norm_num
noncomputable def uProjPlus512Twos_1D (b : Fin 2) : Unitary 256 :=
  ⟨uProjPlus512TwosMat1D b, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose]
    exact uProjPlus512TwosMat1D_mul_conjTranspose b)⟩
noncomputable abbrev uProjPlus512_1D (b : Fin 2) : Unitary 256 := uProjPlus512Twos_1D b
noncomputable def uProjPlus512TwosMat3D (b : Fin 3 → Fin 2) : Operator (2 ^ 24) := Matrix.of
    fun yIdx uIdx ↦ star (projSubGridElem256_3D b (projGridEquiv24 yIdx) (projTwosMom3D uIdx))
theorem uProjPlus512TwosMat3D_entry_factor (b : Fin 3 → Fin 2) (yIdx uIdx : Fin (2 ^ 24)) :
    uProjPlus512TwosMat3D b yIdx uIdx = ∏ w : Fin 3, uProjPlus512TwosMat1D (b w)
    (projGridEquiv24 yIdx w) (projGridEquiv24 uIdx w) := by
  have hsqrt : (√(256 : ℝ) : ℂ) = 16 := by
    exact_mod_cast (show √(256 : ℝ) = 16 by rw [show (256 : ℝ) = 16 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)])
  unfold uProjPlus512TwosMat3D projSubGridElem256_3D uProjPlus512TwosMat1D projTwosMom3D
  rw [Matrix.of_apply, RCLike.star_def, map_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Matrix.of_apply, hsqrt, ← RCLike.star_def, star_mul', star_div₀, star_one,
    (by norm_num : star (16 : ℂ) = 16), star_omega512]
  congr 2
  ring
def rProjAxis24 (w : Fin 3) : QRegister 8 24 :=
  QRegister.block (8 * w.val) 8 (by have := w.isLt; omega)
lemma block8_extractIndex_u24 (w : Fin 3) (u : Fin (2 ^ 24)) :
    (rProjAxis24 w).extractIndex u = projGridEquiv24 u w := by
  refine (basisBitsEquiv 8).injective (funext fun j ↦ ?_)
  have := j.isLt
  have := w.isLt
  change basisBits 8 ((rProjAxis24 w).extractIndex u) j = basisBits 8 (projGridEquiv24 u w) j
  rw [(rProjAxis24 w).basisBits_extractIndex u j]
  change basisBits 24 u ⟨8 * w.val + j.val, by omega⟩ = basisBits 8 (projGridEquiv24 u w) j
  rw [basisBits_eq_div_mod, basisBits_eq_div_mod, projGridEquiv24, Equiv.coe_fn_mk,
    Nat.pow_add 2 (8 * w.val) j.val, ← Nat.div_div_eq_div_mul]
  refine congrArg _ ?_
  fin_cases j <;> simp only [Nat.reducePow] <;> omega
noncomputable def uProjPlus512_3D (b : Fin 3 → Fin 2) : Unitary (2 ^ 24) :=
    (rProjAxis24 0).embedUnitary (uProjPlus512_1D (b 0)) * (rProjAxis24 1).embedUnitary
    (uProjPlus512_1D (b 1)) * (rProjAxis24 2).embedUnitary (uProjPlus512_1D (b 2))
theorem uProjPlus512_3D_val (b : Fin 3 → Fin 2) :
    (uProjPlus512_3D b).1 = uProjPlus512TwosMat3D b := by
  ext z u
  let r0 : QRegister 8 24 := rProjAxis24 0
  let r1 : QRegister 8 24 := rProjAxis24 1
  let r2 : QRegister 8 24 := rProjAxis24 2
  have hd01 : r0.DisjointWires r1 := disjoint_block_sep (by omega)
  have hd02 : r0.DisjointWires r2 := disjoint_block_sep (by omega)
  have hd12 : r1.DisjointWires r2 := disjoint_block_sep (by omega)
  let A0 := (uProjPlus512_1D (b 0)).1
  let A1 := (uProjPlus512_1D (b 1)).1
  let A2 := (uProjPlus512_1D (b 2)).1
  rw [show (uProjPlus512_3D b).1 z u =
      ((r0.embedMatrix A0 * r1.embedMatrix A1) * r2.embedMatrix A2) z u by
    simp only [uProjPlus512_3D, Submonoid.coe_mul, QRegister.embedUnitary_val, r0, r1, r2, A0,
      A1, A2]]
  have hpres2 (x y) (hxy : (r0.embedMatrix A0 * r1.embedMatrix A1) x y ≠ 0) :
      r2.extractIndex x = r2.extractIndex y := by
    rw [Matrix.mul_apply] at hxy
    obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
    exact (extractIndex_eq_of_disjoint_embedMatrix r0 r2 hd02 A0 (left_ne_zero_of_mul ht)).trans
      (extractIndex_eq_of_disjoint_embedMatrix r1 r2 hd12 A1 (right_ne_zero_of_mul ht))
  rw [mul_embedMatrix_of_extract_preserved _ r2 A2 hpres2 z u,
    mul_embedMatrix_of_extract_preserved _ r1 A1
      (fun x y hxy ↦ extractIndex_eq_of_disjoint_embedMatrix r0 r1 hd01 A0 hxy)]
  let u' := r1.replaceIndex (r2.replaceIndex u (r2.extractIndex z)) (r1.extractIndex z)
  have hu'_r1 : r1.extractIndex u' = r1.extractIndex z := r1.extractIndex_replaceIndex _ _
  have hu'_r2 : r2.extractIndex u' = r2.extractIndex z :=
    (extractIndex_replaceIndex_of_disjoint r1 r2 hd12 _ _).trans (r2.extractIndex_replaceIndex _ _)
  have hao0 : (r0.basisSplitEquiv z).2 = (r0.basisSplitEquiv u').2 := by
    refine (r0.basisSplit_environment_eq_iff z u').mpr fun w hw ↦ ?_
    have hw_eq : z = r0.replaceIndex u' (r0.extractIndex z) :=
      projGridEquiv24.injective (funext fun w ↦ by
        fin_cases w
        · exact (block8_extractIndex_u24 0 z).symm.trans
            ((r0.extractIndex_replaceIndex _ _).symm.trans (block8_extractIndex_u24 0 _))
        · exact (block8_extractIndex_u24 1 z).symm.trans ((hu'_r1.symm.trans
            (extractIndex_replaceIndex_of_disjoint r0 r1 hd01 _ _).symm).trans
            (block8_extractIndex_u24 1 _))
        · exact (block8_extractIndex_u24 2 z).symm.trans ((hu'_r2.symm.trans
            (extractIndex_replaceIndex_of_disjoint r0 r2 hd02 _ _).symm).trans
            (block8_extractIndex_u24 2 _)))
    conv_lhs => rw [hw_eq]
    exact r0.basisBits_replaceIndex_of_not_mem u' (r0.extractIndex z) w hw
  rw [show (r0.embedMatrix A0) z u' = A0 (r0.extractIndex z) (r0.extractIndex u) by
      simp only [QRegister.embedMatrix_apply, hao0, ite_true, mul_one, u',
        extractIndex_replaceIndex_of_disjoint r1 r0 hd01.symm,
        extractIndex_replaceIndex_of_disjoint r2 r0 hd02.symm],
    extractIndex_replaceIndex_of_disjoint r2 r1 hd12.symm]
  simp only [A0, A1, A2, r0, r1, r2, uProjPlus512TwosMat3D_entry_factor, Fin.prod_univ_three,
    block8_extractIndex_u24]
  rfl
def bit8 (x : Fin 256) (r : Fin 8) : ℕ := (x.val / 2 ^ r.val) % 2
lemma fin256_val_eq_bits (x : Fin 256) : x.val = ∑ r : Fin 8, 2 ^ r.val * bit8 x r := by
  have := x.isLt
  unfold bit8
  rw [Fin.sum_univ_eight]
  dsimp
  omega
lemma fin256_eq_of_bit8_eq {a b : Fin 256} (h : ∀ r : Fin 8, bit8 a r = bit8 b r) : a = b :=
  Fin.ext (by rw [fin256_val_eq_bits a, fin256_val_eq_bits b,
    Finset.sum_congr rfl fun r _ ↦ by rw [h r]])
def projPreM9 (x : Fin 256) : ℕ := x.val + 256 * bit8 x 7
lemma omega512_emod (m : ℤ) : omega512 (m % 512) = omega512 m := by
  simpa only [one_mul] using omega512_periodic_emod 1 m
lemma star_mul_omega512_self (m : ℤ) : star (omega512 m) * omega512 m = 1 := by
  rw [star_omega512, ← omega512_add, neg_add_cancel, omega512_zero]
noncomputable def preDiag8 (b : Fin 2) : Unitary 256 :=
  ⟨Matrix.diagonal fun u : Fin 256 ↦ omega512 ((b.val : ℤ) * (projPreM9 u : ℤ)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_mul_omega512_self _)⟩
noncomputable def wireHadamard8 (m : Fin 8) : Unitary 256 :=
  (QRegister.singleton m : QRegister 1 8).embedUnitary Qubit.H
def stageRowExp512 (m : Fin 8) (z : Fin 256) : ℤ :=
  ((2 ^ (8 - m.val) * bit8 z m * (z.val % 2 ^ m.val) : ℕ) : ℤ)
noncomputable def stageDiag8 (m : Fin 8) : Unitary 256 :=
  ⟨Matrix.diagonal fun z : Fin 256 ↦ omega512 (stageRowExp512 m z), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_mul_omega512_self _)⟩
def bitRev8Fun (z : Fin 256) : Fin 256 :=
  ⟨128 * bit8 z 0 + 64 * bit8 z 1 + 32 * bit8 z 2 + 16 * bit8 z 3 +
    8 * bit8 z 4 + 4 * bit8 z 5 + 2 * bit8 z 6 + bit8 z 7, by unfold bit8; omega⟩
lemma bit8_bitRev8Fun (z : Fin 256) (r : Fin 8) :
    bit8 (bitRev8Fun z) r = bit8 z ⟨7 - r.val, by omega⟩ := by
  have h (b0 b1 b2 b3 b4 b5 b6 b7 : ℕ) (_ : b0 < 2) (_ : b1 < 2) (_ : b2 < 2) (_ : b3 < 2)
      (_ : b4 < 2) (_ : b5 < 2) (_ : b6 < 2) (_ : b7 < 2) :
      let v := 128 * b0 + 64 * b1 + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7
      v / 1 % 2 = b7 ∧ v / 2 % 2 = b6 ∧ v / 4 % 2 = b5 ∧ v / 8 % 2 = b4 ∧
      v / 16 % 2 = b3 ∧ v / 32 % 2 = b2 ∧ v / 64 % 2 = b1 ∧ v / 128 % 2 = b0 := by
    dsimp only
    omega
  rcases h (bit8 z 0) (bit8 z 1) (bit8 z 2) (bit8 z 3) (bit8 z 4) (bit8 z 5) (bit8 z 6) (bit8 z 7)
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) with ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩
  fin_cases r
  exacts [e0, e1, e2, e3, e4, e5, e6, e7]
lemma bitRev8Fun_involutive : Function.Involutive bitRev8Fun := fun z ↦
  fin256_eq_of_bit8_eq fun r ↦ by
    rw [bit8_bitRev8Fun, bit8_bitRev8Fun]
    exact congrArg (bit8 z) (Fin.ext (by
      dsimp
      omega))
noncomputable def bitRev8Unitary : Unitary 256 :=
  Operator.permutationUnitary (Equiv.ofBijective bitRev8Fun bitRev8Fun_involutive.bijective)
lemma wireHadamard8_apply (m : Fin 8) (z w : Fin 256) : (wireHadamard8 m).1 z w = if ∀ r : Fin
    8, r ≠ m → bit8 z r = bit8 w r then (1 / (√2 : ℂ)) * omega512
    (256 * ((bit8 z m * bit8 w m : ℕ) : ℤ)) else 0 := by
  let reg : QRegister 1 8 := QRegister.singleton m
  have hbit_iff (a b : Fin 256) : (reg.basisSplitEquiv a).2 = (reg.basisSplitEquiv b).2 ↔ ∀ r
      : Fin 8, r ≠ m → bit8 a r = bit8 b r := by
    rw [reg.basisSplit_environment_eq_iff]
    refine ⟨fun h r hr ↦ ?_, fun h r hr ↦ ZMod.val_injective 2 ?_⟩
    · simpa [-Nat.reducePow, basisBits_eq_div_mod, bit8,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using
        congrArg ZMod.val (h r fun ⟨_, hidx⟩ ↦ hr hidx.symm)
    · simpa [-Nat.reducePow, basisBits_eq_div_mod, bit8,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using h r fun e ↦ hr ⟨0, e.symm⟩
  have hext_bit (a : Fin 256) : (reg.extractIndex a).val = bit8 a m := by
    rw [← (by decide : ∀ x : Fin 2, (basisBits 1 x 0).val = x.val), reg.basisBits_extractIndex]
    change (basisBits 8 a m).val = bit8 a m
    rw [basisBits_eq_div_mod]
    exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
  rw [wireHadamard8, QRegister.embedUnitary_val, reg.embedMatrix_apply]
  by_cases h : (reg.basisSplitEquiv z).2 = (reg.basisSplitEquiv w).2
  · simp only [h, ↓reduceIte, ← hext_bit z, ← hext_bit w, ite_pos_8 ((hbit_iff z w).mp h)]
    have ho256 : omega512 256 = -1 := by
      rw [omega512, show 2 * ↑π * ↑(256 : ℤ) * Complex.I / 512 = ↑π * Complex.I by
        push_cast
        ring, Complex.exp_pi_mul_I]
    generalize reg.extractIndex z = az
    generalize reg.extractIndex w = aw
    fin_cases az <;> fin_cases aw <;> simp [Qubit.H, omega512_zero, ho256]
  · simp only [h, show ¬(∀ r : Fin 8, r ≠ m → bit8 z r = bit8 w r) from
      fun hall ↦ h ((hbit_iff z w).mpr hall), ↓reduceIte, mul_zero]
lemma z_mod_eq_of_low_bits_eq (m : Fin 8) {z u : Fin 256}
    (hlow : ∀ r : Fin 8, r.val < m.val → bit8 z r = bit8 u r) :
    z.val % 2 ^ m.val = u.val % 2 ^ m.val := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hk : k < m.val
  · simp only [hk, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
    exact congrArg (fun n ↦ decide (n = 1)) (hlow ⟨k, by have := m.isLt; omega⟩ hk)
  · simp [hk]
theorem stageStep8_mulVec_state (u : Fin 256) (m : Fin 8) (k : ℕ) (hk : k = m.val + 1)
    (Φ : Fin 256 → ℤ) (hΦ : ∀ w₁ w₂ : Fin 256, (∀ r : Fin 8, m.val < r.val → bit8 w₁ r = bit8
    w₂ r) → Φ w₁ = Φ w₂) (c : ℂ) : ((stageDiag8 m * wireHadamard8 m).1.mulVec fun w ↦ if ∀ r :
    Fin 8, r.val < k → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0) = fun z ↦ if ∀ r :
    Fin 8, r.val < m.val → bit8 z r = bit8 u r then (c * (1 / (√2 : ℂ))) * omega512 (Φ z + ((2
    ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ (m.val + 1)) : ℕ) : ℤ)) else 0 := by
  subst hk
  let ψ_in : Fin 256 → ℂ := fun w ↦
    if ∀ r : Fin 8, r.val < m.val + 1 → bit8 w r = bit8 u r then c * omega512 (Φ w) else 0
  funext z
  change ((stageDiag8 m * wireHadamard8 m).1.mulVec ψ_in) z = _
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  change (Matrix.diagonal (fun w ↦ omega512 (stageRowExp512 m w))).mulVec
      ((wireHadamard8 m).1.mulVec ψ_in) z = _
  rw [Matrix.mulVec_diagonal, Matrix.mulVec, dotProduct]
  by_cases hz_low : ∀ r : Fin 8, r.val < m.val → bit8 z r = bit8 u r
  · rw [ite_pos_8 hz_low]
    let bitsPre (r : Fin 8) : ZMod 2 := if r = m then basisBits 8 u m else basisBits 8 z r
    let wPre : Fin 256 := (basisBitsEquiv 8).symm bitsPre
    have hwPre_bit (r : Fin 8) : bit8 wPre r = if r = m then bit8 u m else bit8 z r := by
      have hb : basisBits 8 wPre r = bitsPre r :=
        congrFun ((basisBitsEquiv 8).apply_symm_apply bitsPre) r
      by_cases hrk : r = m <;>
        simpa [-Nat.reducePow, bitsPre, hrk, basisBits_eq_div_mod, bit8,
          ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using congrArg ZMod.val hb
    have hwPre_low (r : Fin 8) (hr : r.val < m.val + 1) : bit8 wPre r = bit8 u r := by
      rw [hwPre_bit]
      split_ifs with hrk
      · exact congrArg (bit8 u) hrk.symm
      · exact hz_low r (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hr) (Fin.val_ne_of_ne hrk))
    have hwPre_hi (r : Fin 8) (hr : r ≠ m) : bit8 z r = bit8 wPre r := by simp [hwPre_bit, hr]
    rw [Finset.sum_eq_single wPre (fun w _ hne ↦ by
        rw [wireHadamard8_apply]
        split_ifs with hw_ag
        · dsimp only [ψ_in]
          rw [ite_neg_8 (fun hw_low ↦ hne (fin256_eq_of_bit8_eq fun r ↦ by
            rw [hwPre_bit]
            split_ifs with hrk
            · exact (congrArg (bit8 w) hrk).trans (hw_low m (Nat.lt_succ_self m.val))
            · exact (hw_ag r hrk).symm)), mul_zero]
        · exact zero_mul _) (fun hm_abs ↦ absurd (Finset.mem_univ _) hm_abs),
      wireHadamard8_apply, ite_pos_8 hwPre_hi]
    dsimp only [ψ_in]
    have hcombZ : ((256 * bit8 u m + 2 ^ (8 - m.val) * (u.val % 2 ^ m.val) : ℕ) : ℤ) =
        ((2 ^ (8 - m.val) * (u.val % 2 ^ (m.val + 1)) : ℕ) : ℤ) := by
      exact_mod_cast (show 256 * bit8 u m + 2 ^ (8 - m.val) * (u.val % 2 ^ m.val) =
          2 ^ (8 - m.val) * (u.val % 2 ^ (m.val + 1)) by
        have := u.isLt
        fin_cases m <;> simp only [bit8, Nat.reduceSub, Nat.reducePow] <;> omega)
    rw [ite_pos_8 hwPre_low,
      hΦ wPre z fun r hr ↦ (hwPre_hi r fun e ↦ Nat.ne_of_gt hr (congrArg Fin.val e)).symm,
      show bit8 wPre m = bit8 u m by simp [hwPre_bit],
      show stageRowExp512 m z = ((2 ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ m.val) : ℕ) : ℤ) by
        rw [stageRowExp512, z_mod_eq_of_low_bits_eq m hz_low],
      show omega512 ((2 ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ m.val) : ℕ)) *
          ((1 / (√2 : ℂ)) * omega512 (256 * ((bit8 z m * bit8 u m : ℕ) : ℤ)) * (c * omega512 (Φ z)))
        = (c * (1 / (√2 : ℂ))) * (omega512 (Φ z) * (omega512 (256 * ((bit8 z m * bit8 u m : ℕ) : ℤ))
          * omega512 ((2 ^ (8 - m.val) * bit8 z m * (u.val % 2 ^ m.val) : ℕ)))) by ring,
      ← omega512_add, ← omega512_add]
    congr 2
    push_cast at hcombZ ⊢
    linear_combination (bit8 z m : ℤ) * hcombZ
  · rw [ite_neg_8 hz_low, Finset.sum_eq_zero fun w _ ↦ by
      rw [wireHadamard8_apply]
      split_ifs with hw_ag
      · dsimp only [ψ_in]
        rw [ite_neg_8 (fun hw_low ↦ hz_low fun r hr ↦
          (hw_ag r fun e ↦ Nat.ne_of_lt hr (congrArg Fin.val e)).trans
            (hw_low r (Nat.lt_succ_of_lt hr))), mul_zero]
      · exact zero_mul _, mul_zero]
theorem eightStageProj512_eq_uProjPlus512_1D (b : Fin 2) : (bitRev8Unitary * wireHadamard8 0 *
    (stageDiag8 1 * wireHadamard8 1) * (stageDiag8 2 * wireHadamard8 2) * (stageDiag8 3 *
    wireHadamard8 3) * (stageDiag8 4 * wireHadamard8 4) * (stageDiag8 5 * wireHadamard8 5) *
    (stageDiag8 6 * wireHadamard8 6) * (stageDiag8 7 * wireHadamard8 7) * preDiag8 b).1 =
    (uProjPlus512_1D b).1 := by
  apply @matrix_ext_basisKet 8
  intro βu
  let u : Fin 256 := (basisBitsEquiv 8).symm βu
  rw [show basisKet βu = Pi.single u 1 from rfl]
  funext y
  let z : Fin 256 := bitRev8Fun y
  have hperm (v : Fin 256 → ℂ) : (bitRev8Unitary.1.mulVec v) y = v z := by
    conv_lhs => rw [show v = ∑ k : Fin 256, v k • Pi.single k (1 : ℂ) from
      funext fun k ↦ by simp [Pi.single_apply], Matrix.mulVec_sum]
    simp only [Finset.sum_apply, Matrix.mulVec_smul, Pi.smul_apply, bitRev8Unitary,
      Operator.permutationUnitary_mulVec_single]
    rw [Finset.sum_eq_single z (fun k _ hkz ↦ mul_eq_zero_of_right _ (Pi.single_eq_of_ne
        (fun e : y = bitRev8Fun k ↦ hkz (by simp [z, e, bitRev8Fun_involutive k])) _))
      (fun h ↦ absurd (Finset.mem_univ z) h)]
    simp [z, bitRev8Fun_involutive y]
  have hpre : (preDiag8 b).1.mulVec (Pi.single u 1) = fun w ↦ if ∀ r : Fin 8, r.val < 8 → bit8
      w r = bit8 u r then (1 : ℂ) * omega512 ((b.val : ℤ) * (projPreM9 u : ℤ)) else 0 :=
    funext fun w ↦ by
      rw [preDiag8, Matrix.diagonal_mulVec_single]
      by_cases hwu : w = u
      · subst hwu
        simp
      · rw [Pi.single_eq_of_ne hwu,
          ite_neg_8 (fun hall ↦ hwu (fin256_eq_of_bit8_eq fun r ↦ hall r r.isLt))]
  have h0_diag : stageDiag8 0 = 1 := Subtype.ext (Matrix.ext fun i j ↦ by
    by_cases hij : i = j <;>
      simp [stageDiag8, OneMemClass.coe_one, hij, stageRowExp512, omega512_zero])
  let rhs : ℂ := ((uProjPlus512_1D b).1.mulVec (Pi.single u 1)) y
  suffices hU8 : ((stageDiag8 0 * wireHadamard8 0).1.mulVec
      ((stageDiag8 1 * wireHadamard8 1).1.mulVec ((stageDiag8 2 * wireHadamard8 2).1.mulVec
      ((stageDiag8 3 * wireHadamard8 3).1.mulVec ((stageDiag8 4 * wireHadamard8 4).1.mulVec
      ((stageDiag8 5 * wireHadamard8 5).1.mulVec ((stageDiag8 6 * wireHadamard8 6).1.mulVec
      ((stageDiag8 7 * wireHadamard8 7).1.mulVec ((preDiag8 b).1.mulVec (Pi.single u 1)))))))))) z =
      rhs by
    rw [h0_diag, one_mul] at hU8
    simpa only [rhs, Submonoid.coe_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hperm] using hU8
  rw [hpre,
    stageStep8_mulVec_state u 7 8 rfl _ (fun _ _ _ ↦ rfl),
    stageStep8_mulVec_state u 6 (7 : Fin 8).val rfl _ (fun _ _ h ↦ by simp [h 7 (by decide)]),
    stageStep8_mulVec_state u 5 (6 : Fin 8).val rfl _ (fun _ _ h ↦
      by simp [h 7 (by decide), h 6 (by decide)]),
    stageStep8_mulVec_state u 4 (5 : Fin 8).val rfl _ (fun _ _ h ↦ by
      simp [h 7 (by decide), h 6 (by decide), h 5 (by decide)]),
    stageStep8_mulVec_state u 3 (4 : Fin 8).val rfl _ (fun _ _ h ↦ by
      simp [h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide)]),
    stageStep8_mulVec_state u 2 (3 : Fin 8).val rfl _ (fun _ _ h ↦ by
      simp [h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide), h 3 (by decide)]),
    stageStep8_mulVec_state u 1 (2 : Fin 8).val rfl _ (fun _ _ h ↦ by
      simp [h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide),
        h 3 (by decide), h 2 (by decide)]),
    stageStep8_mulVec_state u 0 (1 : Fin 8).val rfl _ (fun _ _ h ↦ by
      simp [h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide),
        h 3 (by decide), h 2 (by decide), h 1 (by decide)])]
  simp only [Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, ↓reduceIte]
  have hs2 : (√2 : ℂ) ^ 2 = 2 := by
    rw [sq]
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h16 : (1 : ℂ) * (1 / √2) * (1 / √2) * (1 / √2) * (1 / √2) *
      (1 / √2) * (1 / √2) * (1 / √2) * (1 / √2) = (1 / 16 : ℂ) := by
    rw [show (1 : ℂ) * (1 / √2) * (1 / √2) * (1 / √2) * (1 / √2) * (1 / √2) * (1 / √2) *
      (1 / √2) * (1 / √2) = ((1 / (√2 : ℂ)) ^ 2) ^ 4 by ring, div_pow, _root_.one_pow, hs2]
    norm_num
  rw [h16, show rhs = (1 / 16 : ℂ) * omega512
      (Slots01AndGridGuardBridge.twosComp8Int u *
        (2 * (y.val : ℤ) + (b.val : ℤ))) by
    dsimp only [rhs, uProjPlus512_1D, uProjPlus512Twos_1D]
    rw [Matrix.mulVec_single_one]
    rfl]
  congr 1
  have hy_val : y.val = 128 * bit8 z 0 + 64 * bit8 z 1 + 32 * bit8 z 2 + 16 * bit8 z 3 +
      8 * bit8 z 4 + 4 * bit8 z 5 + 2 * bit8 z 6 + bit8 z 7 := by
    change y.val = (bitRev8Fun z).val
    rw [bitRev8Fun_involutive y]
  let rawSum : ℕ := 2 * bit8 z 7 * (u.val % 256) + 4 * bit8 z 6 * (u.val % 128) + 8 * bit8 z 5
      * (u.val % 64) + 16 * bit8 z 4 * (u.val % 32) + 32 * bit8 z 3 * (u.val % 16) + 64 * bit8
      z 2 * (u.val % 8) + 128 * bit8 z 1 * (u.val % 4) + 256 * bit8 z 0 * (u.val % 2)
  have hexp_mod : ((rawSum : ℕ) : ℤ) % 512 =
      (Slots01AndGridGuardBridge.twosComp8Int u * (2 * (y.val : ℤ)))
      % 512 := by
    have hu_lt := u.isLt
    have hd (n : ℕ) : u.val = n * (u.val / n) + u.val % n := (Nat.div_add_mod u.val n).symm
    have hnat : rawSum % 512 = (2 * y.val * u.val) % 512 := by
      have hdiff : 2 * y.val * u.val = rawSum + 512 * (bit8 z 6 * (u.val / 128) + bit8 z 5 *
          (u.val / 64) + bit8 z 4 * (u.val / 32) + bit8 z 3 * (u.val / 16) + bit8 z 2 * (u.val
          / 8) + bit8 z 1 * (u.val / 4) + bit8 z 0 * (u.val / 2)) := by
        dsimp only [rawSum]
        rw [hy_val]
        linear_combination 2 * bit8 z 7 * (Nat.mod_eq_of_lt hu_lt).symm + 4 * bit8 z 6 * hd 128 +
          8 * bit8 z 5 * hd 64 + 16 * bit8 z 4 * hd 32 + 32 * bit8 z 3 * hd 16 +
          64 * bit8 z 2 * hd 8 + 128 * bit8 z 1 * hd 4 + 256 * bit8 z 0 * hd 2
      rw [hdiff, Nat.add_mul_mod_self_left]
    have htwos : (Slots01AndGridGuardBridge.twosComp8Int u *
        (2 * (y.val : ℤ))) % 512 = ((2 * y.val * u.val : ℕ) : ℤ) % 512 := by
      unfold Slots01AndGridGuardBridge.twosComp8Int
      split_ifs with h128
      · exact congrArg (· % 512) (by
          push_cast
          ring)
      · rw [show ((u.val : ℤ) - 256) * (2 * (y.val : ℤ)) =
          ((2 * y.val * u.val : ℕ) : ℤ) + (-(y.val : ℤ)) * 512 by
            push_cast
            ring, Int.add_mul_emod_self_right]
    rw [htwos]
    exact_mod_cast hnat
  trans omega512 ((b.val : ℤ) * (projPreM9 u : ℤ) + ((rawSum : ℕ) : ℤ))
  · exact congrArg omega512 (by
      dsimp [rawSum]
      ring)
  · have homega : omega512 ((b.val : ℤ) * (projPreM9 u : ℤ)) = omega512
        (Slots01AndGridGuardBridge.twosComp8Int u * (b.val : ℤ)) := by
      have := u.isLt
      unfold projPreM9 bit8 Slots01AndGridGuardBridge.twosComp8Int
      rw [show 2 ^ (7 : Fin 8).val = 128 from rfl]
      split_ifs with h128
      · rw [show u.val / 128 % 2 = 0 by omega]
        exact congrArg omega512 (by
          push_cast
          ring)
      · rw [show u.val / 128 % 2 = 1 by omega, show ((b.val : ℤ) * ((u.val + 256 * 1 : ℕ) : ℤ)) =
          ((u.val : ℤ) - 256) * (b.val : ℤ) + (b.val : ℤ) * 512 by
            push_cast
            ring, ← omega512_emod, Int.add_mul_emod_self_right, omega512_emod]
    rw [omega512_add, homega, ← omega512_emod ((rawSum : ℕ) : ℤ), hexp_mod, omega512_emod,
      ← omega512_add]
    exact congrArg omega512 (by ring)
lemma fullSysCoreWires_eq_add (mPayload : ℕ) : fullSysCoreWires mPayload = 3954 + mPayload := by
  unfold fullSysCoreWires SpecsAux.SpecMirror.systemQubits SpecsAux.SpecMirror.numElectrons
    SpecsAux.SpecMirror.electronBits SpecsAux.SpecMirror.projectileBits
  omega
def rProjCore {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) : QRegister 24 n :=
  rCore.slice 3924 24 (by rw [fullSysCoreWires_eq_add]; omega)
def rProjAxis {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) (w : Fin 3) :
    QRegister 8 n :=
  rCore.slice (3924 + 8 * w.val) 8
    (by have := w.isLt; rw [fullSysCoreWires_eq_add]; omega)
def rProjCosetP3 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) : QRegister 3 n := rCosetB0 hm rCore
lemma rProjCore_id_val {mPayload : ℕ} (i : Fin 24) :
    (rProjCore (QRegExt.idReg (fullSysCoreWires mPayload)) i).val = 3924 + i.val := rfl
lemma rProjAxis_id_val {mPayload : ℕ} (w : Fin 3) (k : Fin 8) :
    (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w k).val =
      3924 + 8 * w.val + k.val := rfl
lemma rProjCosetP3_id_val {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    (rProjCosetP3 hm (QRegExt.idReg (fullSysCoreWires mPayload)) w).val = 3957 + w.val := rfl
lemma rNucIdx_id_val {mPayload : ℕ} (hm : 22 ≤ mPayload) (i : Fin 8) :
    (rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) i).val = 3960 + i.val := rfl
def extractProj24 {mPayload : ℕ} (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin (2 ^ 24) :=
  (rProjCore (QRegExt.idReg _)).extractIndex ((basisBitsEquiv _).symm γ)
def extractCosetP3 {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin 3 → Fin 2 := fun w ↦
    ⟨(γ (rProjCosetP3 hm (QRegExt.idReg _) w)).val, ZMod.val_lt _⟩
def ctrl7Active {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Bool :=
  let rN := rNucIdx hm (QRegExt.idReg _)
  decide (γ (rN 7) = 1 ∧ (γ (rN 5) = 1 ∨ (γ (rN 4) = 1 ∧ γ (rN 3) = 1)))

lemma core_wire_ne {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    {i j : Fin (fullSysCoreWires mPayload)} (hij : i.val ≠ j.val) : rCore i ≠ rCore j := fun
    h ↦ hij (congrArg Fin.val (rCore.wires.injective h))
lemma support_seq_sub {n : ℕ} {S : Finset (Wire n)} {c₁ c₂ : Circuit n}
    (h₁ : c₁.support ⊆ S) (h₂ : c₂.support ⊆ S) : (c₁ ;;ᶜ c₂).support ⊆ S :=
  Circuit.support_seq c₁ c₂ ▸ Finset.union_subset h₁ h₂
lemma zmod2_and_not3 : ∀ a b c : ZMod 2,
    ((a + 1) * (b + 1)) * (c + 1) = if (a = 0 ∧ b = 0 ∧ c = 0) then 1 else 0 := by decide
lemma zmod2_ctrl7 : ∀ b7 b5 b4 b3 : ZMod 2, b7 * (1 + (b5 + 1) * (b4 * b3 + 1)) = if
    (b7 = 1 ∧ (b5 = 1 ∨ (b4 = 1 ∧ b3 = 1))) then 1 else 0 := by decide
lemma zmod2_add_self : ∀ x y : ZMod 2, x + y + y = x := by decide
lemma zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
noncomputable def vepWriteReg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
theorem vepEmbedMatrix_mulVec_basisKet {n k : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (basisKet β) = ∑ l : Fin (2 ^ k), A l
    ((basisBitsEquiv k).symm (fun i ↦ β (r i))) • basisKet (vepWriteReg β r (basisBits k l)) := by
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hket (γ : BitAssignment n) : basisKet γ = Pi.single ((basisBitsEquiv n).symm γ) (1 : ℂ) :=
    rfl
  rw [hket β, r.embedMatrix_mulVec_single_factors,
    show r.extractIndex ((basisBitsEquiv n).symm β) = (basisBitsEquiv k).symm (fun i ↦ β (r i)) by
      simp [QRegister.extractIndex], hcol, QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [vepWriteReg, hket]
def vepHighNuc {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Bool := coin0Active γ && ctrl7Active hm
    γ && decide (γ (rNucIdx hm (QRegExt.idReg _) 6) = 1)
theorem vepHighNuc_iff {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : vepHighNuc hm γ = true ↔ coin0Active γ
    = true ∧ 216 ≤ regVal (rNucIdx hm (QRegExt.idReg _)) γ := by
  let rN := rNucIdx hm (QRegExt.idReg _)
  have hlt : (γ (rN 0)).val < 2 ∧ (γ (rN 1)).val < 2 ∧ (γ (rN 2)).val < 2 ∧ (γ (rN 3)).val < 2 ∧
      (γ (rN 4)).val < 2 ∧ (γ (rN 5)).val < 2 ∧ (γ (rN 6)).val < 2 ∧ (γ (rN 7)).val < 2 :=
    ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
      ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _⟩
  simp only [vepHighNuc, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine and_congr_right' ?_
  change (decide (γ (rN 7) = 1 ∧ (γ (rN 5) = 1 ∨ (γ (rN 4) = 1 ∧ γ (rN 3) = 1))) = true ∧
      γ (rN 6) = 1) ↔ 216 ≤ regVal rN γ
  rw [show regVal rN γ = (γ (rN 0)).val + 2 * (γ (rN 1)).val + 4 * (γ (rN 2)).val +
      8 * (γ (rN 3)).val + 16 * (γ (rN 4)).val + 32 * (γ (rN 5)).val + 64 * (γ (rN 6)).val +
      128 * (γ (rN 7)).val by
    unfold regVal bitsVal
    rw [Fin.sum_univ_eight]
    dsimp
    ring]
  simp only [decide_eq_true_eq, (by decide : ∀ b : ZMod 2, b = 1 ↔ b.val = 1)]
  omega
theorem vepHighNuc_eq_of_high_eq {mPayload : ℕ} (hm : 22 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)} (hc : ∀ q : Fin (fullSysCoreWires
    mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) : vepHighNuc hm γ₁ = vepHighNuc hm γ₂ := by
  have hfcw := fullSysCoreWires_eq_add mPayload
  have hrN (k : Fin 8) : γ₁ ((rNucIdx hm (QRegExt.idReg _)).wires k) =
      γ₂ ((rNucIdx hm (QRegExt.idReg _)).wires k) := by
    have hv := rNucIdx_id_val hm k
    exact hc _ (by omega)
  unfold vepHighNuc coin0Active ctrl7Active NuclearTwistAndXor654Concrete.wSlot2
    NuclearTwistAndXor654Concrete.wSlot1 NuclearTwistAndXor654Concrete.wSlot0
  simp only [hrN]
  simp only [QRegExt.idReg, Function.Embedding.refl_apply, hc ⟨3948, by omega⟩ le_rfl,
    hc ⟨3949, by omega⟩ (Nat.le_succ_of_le le_rfl),
    hc ⟨3950, by omega⟩ (Nat.le_succ_of_le (Nat.le_succ_of_le le_rfl))]
lemma rProjAxis_embed_high_eq {mPayload : ℕ} (w : Fin 3) (A : Operator 256)
    {i j : Fin (2 ^ (fullSysCoreWires mPayload))}
    (hnz : ((rProjAxis (QRegExt.idReg _) w).embedMatrix A) i j ≠ 0) : ∀ q : Fin
    (fullSysCoreWires mPayload), 3948 ≤ q.val → basisBits _ i q = basisBits _ j q := by
  let rAx := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w
  refine fun q hq ↦ (rAx.basisSplit_environment_eq_iff i j).mp (by
    by_contra hne
    exact hnz (by rw [show rProjAxis (QRegExt.idReg _) w = rAx from rfl,
      QRegister.embedMatrix_apply, ite_neg_8 hne, mul_zero])) q fun ⟨k, hk⟩ ↦ ?_
  have hv := (rProjAxis_id_val (mPayload := mPayload) w k).symm.trans (congrArg Fin.val hk)
  have := w.isLt
  have := k.isLt
  omega
lemma extractCosetP3_eq_of_high_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hc : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) :
    extractCosetP3 hm γ₁ w = extractCosetP3 hm γ₂ w := by
  unfold extractCosetP3; congr 2; exact hc _ (by rw [rProjCosetP3_id_val]; omega)
noncomputable def uCtrlProj1DMat {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Operator 256) : Operator (2 ^ (fullSysCoreWires mPayload)) := Matrix.of fun
    i j ↦ if vepHighNuc hm (basisBits _ i) then ((rProjAxis (QRegExt.idReg _) w).embedMatrix
    (F (extractCosetP3 hm (basisBits _ i) w))) i j else if i = j then 1 else 0
theorem uCtrlProj1DMat_conjTranspose {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Operator 256) :
    (uCtrlProj1DMat hm w F)ᴴ = uCtrlProj1DMat hm w (fun b ↦ (F b)ᴴ) := by
  ext i j
  change star (uCtrlProj1DMat hm w F j i) = uCtrlProj1DMat hm w (fun b ↦ (F b)ᴴ) i j
  dsimp only [uCtrlProj1DMat, Matrix.of_apply]
  by_cases hhi : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val →
      basisBits _ i q = basisBits _ j q
  · rw [(vepHighNuc_eq_of_high_eq hm hhi).symm, (extractCosetP3_eq_of_high_eq hm w hhi).symm]
    by_cases hv_i : vepHighNuc hm (basisBits _ i)
    · rw [ite_pos_8 hv_i, ite_pos_8 hv_i, QRegister.embedMatrix_conjTranspose]
      rfl
    · rw [ite_neg_8 hv_i, ite_neg_8 hv_i]
      by_cases hij : i = j
      · subst hij
        simp
      · rw [ite_neg_8 (Ne.symm hij), ite_neg_8 hij, star_zero]
  · have hij : i ≠ j := fun e ↦ hhi fun q _ ↦ by rw [e]
    have hzL (b) : ((rProjAxis (QRegExt.idReg _) w).embedMatrix (F b)) j i = 0 := by
      by_contra hnz
      exact hhi fun q hq ↦ (rProjAxis_embed_high_eq w (F b) hnz q hq).symm
    have hzR (b) : ((rProjAxis (QRegExt.idReg _) w).embedMatrix (F b)ᴴ) i j = 0 := by
      by_contra hnz
      exact hhi fun q hq ↦ rProjAxis_embed_high_eq w (F b)ᴴ hnz q hq
    by_cases hvj : vepHighNuc hm (basisBits _ j) = true <;>
      by_cases hvi : vepHighNuc hm (basisBits _ i) = true <;>
      simp only [hvj, hvi, Bool.false_eq_true, ↓reduceIte, hij, hij.symm, hzL, hzR, star_zero]
theorem uCtrlProj1DMat_mul {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F G : Fin 2 → Operator 256) : uCtrlProj1DMat hm w F * uCtrlProj1DMat hm w G =
    uCtrlProj1DMat hm w (fun b ↦ F b * G b) := by
  let rAx := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w
  ext i j
  rw [Matrix.mul_apply]
  dsimp only [uCtrlProj1DMat, Matrix.of_apply]
  by_cases hv : vepHighNuc hm (basisBits _ i)
  · simp only [hv, ↓reduceIte]
    let b := extractCosetP3 hm (basisBits _ i) w
    rw [QRegister.embedMatrix_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hnz : (rAx.embedMatrix (F b)) i k = 0
    · rw [hnz, zero_mul, zero_mul]
    · have hhi := rProjAxis_embed_high_eq w (F b) hnz
      simp only [(vepHighNuc_eq_of_high_eq hm hhi).symm.trans hv,
        (extractCosetP3_eq_of_high_eq hm w hhi).symm, ↓reduceIte]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_eq_single i (fun k _ hki ↦ by rw [ite_neg_8 hki.symm, zero_mul])
      (fun hi_abs ↦ absurd (Finset.mem_univ i) hi_abs), ite_pos_8 rfl, one_mul, ite_neg_8 hv]
noncomputable def uCtrlProj1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Unitary 256) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  ⟨uCtrlProj1DMat hm w (fun b ↦ (F b).1), Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, uCtrlProj1DMat_conjTranspose, uCtrlProj1DMat_mul,
      show (fun b : Fin 2 ↦ (F b).1 * ((F b).1)ᴴ) = (fun _ ↦ 1) from funext fun b ↦
        Matrix.star_eq_conjTranspose (F b).1 ▸ Matrix.mem_unitaryGroup_iff.mp (F b).2]
    ext i j
    simp only [uCtrlProj1DMat, Matrix.of_apply, QRegister.embedMatrix_one, Matrix.one_apply]
    split_ifs <;> rfl)⟩
@[simp] theorem uCtrlProj1DCore_val {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Unitary 256) :
    (uCtrlProj1DCore hm w F).1 = uCtrlProj1DMat hm w (fun b ↦ (F b).1) := rfl
theorem uCtrlProj1DCore_mulVec_basisKet {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Unitary 256) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uCtrlProj1DCore hm w F).1.mulVec (basisKet γ) = if vepHighNuc hm γ then ((rProjAxis
    (QRegExt.idReg _) w).embedUnitary (F (extractCosetP3 hm γ w))).1.mulVec (basisKet γ)
    else basisKet γ := by
  let j₀ : Fin (2 ^ (fullSysCoreWires mPayload)) := (basisBitsEquiv _).symm γ
  have hb_ket : basisBits _ j₀ = γ := (basisBitsEquiv _).apply_symm_apply γ
  funext i
  rw [show basisKet γ = Pi.single j₀ (1 : ℂ) from rfl, Matrix.mulVec_single_one,
    uCtrlProj1DCore_val]
  dsimp only [Matrix.col_apply, uCtrlProj1DMat, Matrix.of_apply]
  by_cases hhi : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → basisBits _ i q = γ q
  · have hhi' : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val →
        basisBits _ i q = basisBits _ j₀ q := fun q hq ↦ (hhi q hq).trans (congrFun hb_ket.symm q)
    rw [vepHighNuc_eq_of_high_eq hm hhi', extractCosetP3_eq_of_high_eq hm w hhi', hb_ket]
    by_cases hv : vepHighNuc hm γ
    · rw [ite_pos_8 hv, ite_pos_8 hv, QRegister.embedUnitary_val, Matrix.mulVec_single_one]
      rfl
    · rw [ite_neg_8 hv, ite_neg_8 hv, Pi.single_apply]
  · have hij : i ≠ j₀ := fun e ↦ hhi fun q _ ↦ by rw [e, hb_ket]
    have hz (b) : ((rProjAxis (QRegExt.idReg _) w).embedMatrix (F b).1) i j₀ = 0 := by
      by_contra hnz
      exact hhi fun q hq ↦ (rProjAxis_embed_high_eq w (F b).1 hnz q hq).trans (congrFun hb_ket q)
    by_cases hvi : vepHighNuc hm (basisBits _ i) = true <;>
      by_cases hv : vepHighNuc hm γ = true <;>
      simp only [hvi, hv, Bool.false_eq_true, ↓reduceIte, hij, Pi.single_eq_of_ne hij,
        QRegister.embedUnitary_val, Matrix.mulVec_single_one, Matrix.col_apply, hz]
end ProjZ512QftAndTwist288
end
end ModProjZ512QftAndTwist288

section ModProjZ512TwistVepClosure288
@[expose] public section
namespace ProjZ512TwistVepClosure288Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
end ProjZ512TwistVepClosure288Alt
namespace ProjZ512QftAndTwist288
section ConfigProjZ512TwistVepClosure288
set_option maxRecDepth 65536
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open DyadicQft64WalkCircuit
open FullSysCatSegmentBridge
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
instance (priority := 1000000) instNeZeroTwoPowVepClosure (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
lemma fcw_eq_add (mPayload : ℕ) : fullSysCoreWires mPayload = 3954 + mPayload := rfl
lemma fcw_block_le (mPayload : ℕ) :
    0 + fullSysCoreWires mPayload ≤ fullSysCoreWires mPayload + 48 := by omega

lemma dyadicTurn48_shift39_eq_omega512 (k : ℕ) :
    DyadicQft64.dyadicTurn 48 ((2 ^ 39 * k : ℕ) : ℤ) = omega512 (k : ℤ) := by
  unfold DyadicQft64.dyadicTurn omega512
  congr 1
  push_cast
  ring
noncomputable def uCtrlProj3DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := uCtrlProj1DCore hm 0 uProjPlus512_1D *
    (uCtrlProj1DCore hm 1 uProjPlus512_1D * uCtrlProj1DCore hm 2 uProjPlus512_1D)
private lemma uCtrlProj1DCore_mulVec_embed_low {mPayload k : ℕ} (hm : 22 ≤ mPayload)
    (w : Fin 3) (rSub : QRegister k (fullSysCoreWires mPayload))
    (hrSub : ∀ j : Fin k, (rSub j).val < 3948) (V : Unitary (2 ^ k))
    (γ : BitAssignment (fullSysCoreWires mPayload)) (hv : vepHighNuc hm γ = true) :
    (uCtrlProj1DCore hm w uProjPlus512_1D).1.mulVec ((rSub.embedUnitary V).1.mulVec (basisKet γ)) =
      (((rProjAxis (QRegExt.idReg _) w).embedUnitary
          (uProjPlus512_1D (extractCosetP3 hm γ w))) *
        rSub.embedUnitary V).1.mulVec (basisKet γ) := by
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, rSub.embedUnitary_val V,
    vepEmbedMatrix_mulVec_basisKet rSub V.1 γ, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  congr 1
  have hhi (q : Fin (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) :
      vepWriteReg γ rSub (basisBits k l) q = γ q :=
    (QRegister.basisBits_replaceIndex_of_not_mem rSub _ _ q fun ⟨j, hj⟩ ↦ by
      have := hrSub j; rw [hj] at this; omega).trans
      (congrFun ((basisBitsEquiv _).apply_symm_apply γ) q)
  rw [uCtrlProj1DCore_mulVec_basisKet, ite_pos_8 ((vepHighNuc_eq_of_high_eq hm hhi).trans hv),
    extractCosetP3_eq_of_high_eq hm w hhi]
theorem uCtrlProj3DCore_mulVec_basisKet {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : (uCtrlProj3DCore hm).1.mulVec
    (basisKet γ) = if vepHighNuc hm γ then ∑ yIdx : Fin (2 ^ 24),
    (uProjPlus512_3D (extractCosetP3 hm γ)).1 yIdx (extractProj24 γ) • basisKet
    (vepWriteReg γ (rProjCore (QRegExt.idReg _)) (basisBits 24 yIdx)) else basisKet γ := by
  have hcompAx (w : Fin 3) :
      (rProjCore (QRegExt.idReg (fullSysCoreWires mPayload))).compose (rProjAxis24 w) =
        rProjAxis (QRegExt.idReg _) w :=
    ProjZ512TwistVepClosure288Alt.qreg_ext fun k ↦ Fin.ext (by
      have := w.isLt
      have := k.isLt
      simp only [QRegister.compose_apply, rProjCore_id_val, rProjAxis_id_val, rProjAxis24,
        ProjZ512TwistVepClosure288Alt.qreg_block_apply]
      omega)
  unfold uCtrlProj3DCore
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  by_cases hv : vepHighNuc hm γ
  · rw [ite_pos_8 hv, uCtrlProj1DCore_mulVec_basisKet, ite_pos_8 hv,
      uCtrlProj1DCore_mulVec_embed_low hm 1 (rProjAxis (QRegExt.idReg _) 2)
        (fun j ↦ by rw [rProjAxis_id_val]; have := j.isLt; omega) _ γ hv,
      show ((rProjAxis (QRegExt.idReg _) 1).embedUnitary
          (uProjPlus512_1D (extractCosetP3 hm γ 1))) *
        ((rProjAxis (QRegExt.idReg _) 2).embedUnitary
          (uProjPlus512_1D (extractCosetP3 hm γ 2))) =
        (rProjCore (QRegExt.idReg _)).embedUnitary
          ((rProjAxis24 1).embedUnitary (uProjPlus512_1D (extractCosetP3 hm γ 1)) *
            (rProjAxis24 2).embedUnitary (uProjPlus512_1D (extractCosetP3 hm γ 2))) by
        rw [← hcompAx 1, ← hcompAx 2, QRegister.embedUnitary_compose,
          QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul],
      uCtrlProj1DCore_mulVec_embed_low hm 0 (rProjCore (QRegExt.idReg _))
        (fun j ↦ by rw [rProjCore_id_val]; have := j.isLt; omega) _ γ hv,
      ← hcompAx 0, QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul, ← mul_assoc,
      show (rProjAxis24 0).embedUnitary (uProjPlus512_1D (extractCosetP3 hm γ 0)) *
          (rProjAxis24 1).embedUnitary (uProjPlus512_1D (extractCosetP3 hm γ 1)) *
          (rProjAxis24 2).embedUnitary (uProjPlus512_1D (extractCosetP3 hm γ 2)) =
        uProjPlus512_3D (extractCosetP3 hm γ) from rfl,
      QRegister.embedUnitary_val, vepEmbedMatrix_mulVec_basisKet]
    rw [show ((basisBitsEquiv 24).symm fun i ↦
        γ (rProjCore (QRegExt.idReg (fullSysCoreWires mPayload)) i)) = extractProj24 γ from
      (basisBitsEquiv 24).injective (by
        rw [(basisBitsEquiv 24).apply_symm_apply, extractProj24]
        exact funext fun i ↦ (QRegister.basisBits_extractIndex _ _ i).trans
          (congrFun ((basisBitsEquiv _).apply_symm_apply γ) _) |>.symm)]
  · rw [ite_neg_8 hv, uCtrlProj1DCore_mulVec_basisKet, ite_neg_8 hv,
      uCtrlProj1DCore_mulVec_basisKet, ite_neg_8 hv,
      uCtrlProj1DCore_mulVec_basisKet, ite_neg_8 hv]
def vepProj9CoreIdx {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) (j : Fin 9) :
    Fin (fullSysCoreWires mPayload) :=
  if hj0 : j.val = 0 then rProjCosetP3 hm (QRegExt.idReg _) w
  else rProjAxis (QRegExt.idReg _) w ⟨j.val - 1, by have := j.isLt; omega⟩
lemma bitsVal_vepProj9CoreIdx_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    bitsVal (fun j : Fin 9 ↦ γ (vepProj9CoreIdx hm w j)) =
      (nyq512ProjEquiv3D (projGridEquiv24 (extractProj24 γ), extractCosetP3 hm γ) w).val := by
  have hbits : (rProjAxis24 w).extractIndex (extractProj24 γ) =
      (basisBitsEquiv 8).symm (fun k ↦ γ (rProjAxis (QRegExt.idReg _) w k)) :=
    (basisBitsEquiv 8).injective (funext fun k ↦ by
      change basisBits 8 ((rProjAxis24 w).extractIndex (extractProj24 γ)) k =
        (basisBitsEquiv 8) ((basisBitsEquiv 8).symm _) k
      rw [(basisBitsEquiv 8).apply_symm_apply, QRegister.basisBits_extractIndex, extractProj24,
        QRegister.basisBits_extractIndex,
        congrFun ((basisBitsEquiv _).apply_symm_apply γ) _]
      exact congrArg γ (Fin.ext (by
        have := w.isLt
        have := k.isLt
        simp only [rProjCore_id_val, rProjAxis_id_val, rProjAxis24,
          ProjZ512TwistVepClosure288Alt.qreg_block_wires_apply]
        omega)))
  have hy_eq : (projGridEquiv24 (extractProj24 γ) w).val =
      bitsVal (fun k : Fin 8 ↦ γ (rProjAxis (QRegExt.idReg _) w k)) := by
    have hbv := bitsVal_basisBits ((rProjAxis24 w).extractIndex (extractProj24 γ))
    rw [hbits, show basisBits 8 ((basisBitsEquiv 8).symm _) = _ from
      (basisBitsEquiv 8).apply_symm_apply _] at hbv
    exact (congrArg Fin.val (block8_extractIndex_u24 w (extractProj24 γ)).symm).trans
      ((congrArg Fin.val hbits).trans hbv.symm)
  rw [nyq512ProjEquiv3D, Equiv.coe_fn_mk]
  dsimp only
  rw [hy_eq, show (extractCosetP3 hm γ w).val = (γ (rProjCosetP3 hm (QRegExt.idReg _) w)).val
      from rfl,
    show bitsVal (fun j : Fin 9 ↦ γ (vepProj9CoreIdx hm w j)) =
      (γ (vepProj9CoreIdx hm w 0)).val + (γ (vepProj9CoreIdx hm w 1)).val * 2 +
      (γ (vepProj9CoreIdx hm w 2)).val * 4 + (γ (vepProj9CoreIdx hm w 3)).val * 8 +
      (γ (vepProj9CoreIdx hm w 4)).val * 16 + (γ (vepProj9CoreIdx hm w 5)).val * 32 +
      (γ (vepProj9CoreIdx hm w 6)).val * 64 + (γ (vepProj9CoreIdx hm w 7)).val * 128 +
      (γ (vepProj9CoreIdx hm w 8)).val * 256 by
        unfold bitsVal
        rw [Fin.sum_univ_succAbove _ 8, Fin.sum_univ_eight]
        simp only [show ∀ r : Fin 8, Fin.succAbove (8 : Fin 9) r = ⟨r.val, by
            have := r.isLt
            omega⟩ from fun r ↦ Fin.ext (by simp [Fin.succAbove, Fin.lt_def, r.isLt])]
        dsimp
        ring]
  unfold bitsVal
  rw [Fin.sum_univ_eight]
  dsimp [vepProj9CoreIdx]
  omega
def vepOnlyM48Val {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ := if vepHighNuc hm γ then 2 ^ 39 *
    bitsVal (fun j : Fin 9 ↦ γ (vepProj9CoreIdx hm w j)) else 0
end ConfigProjZ512TwistVepClosure288
set_option maxRecDepth 4096
end ProjZ512QftAndTwist288
end
end ModProjZ512TwistVepClosure288

section ModProjZ512TwistVepTopBundle288
@[expose] public section
namespace ProjZ512QftAndTwist288
section ConfigProjZ512TwistVepTopBundle288
set_option maxRecDepth 65536
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open DyadicQft64WalkCircuit hiding wSlot2
open PosMomSelectSandwich (slotBitProj)
open FullSysCatSegmentBridge
open FullSysHoistedSelectStitch
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open FusedPreDiagFromTwist288
instance (priority := 1000000) instNeZeroTwoPowVepTop (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
noncomputable def vepLockVal {α : Sort _} (x : α) : α :=
  by exact Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)
lemma vepLockVal_eq {α : Sort _} (x : α) : vepLockVal x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)
noncomputable def vepSlot2TotalPhaseExp {mPayload : ℕ} (c : Configuration)
    (hm : 22 ≤ mPayload) (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ := ∑ w : Fin 3,
    (slot2AxisSum w γ : ℤ) * ((slot2M48Val c hm w γ + vepOnlyM48Val hm w γ : ℕ) : ℤ)
noncomputable def uVepSlot2KickCore {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (vepSlot2TotalPhaseExp c hm)
noncomputable def vepFusedSlot2AxisDelta {mPayload : ℕ} (c : Configuration)
    (hm : 22 ≤ mPayload) (w : Fin 3) (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
    slot2AxisSum w γ * (slot2M48Val c hm w γ + vepOnlyM48Val hm w γ + (1 - (γ
    (coreCosetB1Block (hm6_of_hm22 hm) w)).val) * 2 ^ 41)
abbrev rCoreBlock48 (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload) (fullSysCoreWires mPayload + 48) :=
  QRegister.block 0 (fullSysCoreWires mPayload) (fcw_block_le mPayload)
noncomputable def uVepTwistRest {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) := uVepSlot2KickCore c hm *
    (uSlot4KickCore hm * (uXor32Core mPayload * uCtrlProj3DCore hm))
private lemma mul_comm_of_comm {R : Type*} [Semigroup R] {a b p : R}
    (ha : a * p = p * a) (hb : b * p = p * b) : (a * b) * p = p * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
private lemma rCosetB1_id_val {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    (rCosetB1 hm (QRegExt.idReg (fullSysCoreWires mPayload)) w).val = 3954 + w.val := rfl
private lemma rAnchorIdx_id_val {mPayload : ℕ} (hm : 22 ≤ mPayload) (j : Fin 8) :
    (rAnchorIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) j).val = 3968 + j.val := rfl
private lemma rElecSlotAxis_id_val {mPayload : ℕ} (e : Fin numElectrons) (w : Fin 3) (j : Fin 6) :
    (rElecSlotAxis (QRegExt.idReg (fullSysCoreWires mPayload)) e w j).val =
      18 * e.val + 6 * w.val + j.val := rfl
lemma permutationUnitary_entry {d : ℕ} (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    (Operator.permutationUnitary σ).1 i j = if σ j = i then 1 else 0 := by
  have h := congrFun (Operator.permutationUnitary_mulVec_single σ j (1 : ℂ)) i
  rw [Matrix.mulVec_single_one] at h
  exact h.trans (by simp [Pi.single_apply, eq_comm])
lemma comm_slotBitProj_of_entry_eq {k : ℕ} (A : Operator (2 ^ k)) (q : Wire k) (b : Fin 2)
    (hInv : ∀ i j : Fin (2 ^ k), A i j ≠ 0 → basisBits k i q = basisBits k j q) :
    A * slotBitProj q b = slotBitProj q b * A := by
  ext i j
  unfold slotBitProj
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases h0 : A i j = 0
  · simp [h0]
  · rw [hInv i j h0]
theorem uCtrlProj1DCore_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (F : Fin 2 → Unitary 256) (q : Wire (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val)
    (b : Fin 2) : (uCtrlProj1DCore hm w F).1 * slotBitProj q b = slotBitProj q b *
    (uCtrlProj1DCore hm w F).1 := by
  refine comm_slotBitProj_of_entry_eq _ q b fun i j hnz ↦ ?_
  rw [uCtrlProj1DCore_val] at hnz
  dsimp only [uCtrlProj1DMat, Matrix.of_apply] at hnz
  by_cases hv : vepHighNuc hm (basisBits _ i)
  · rw [ite_pos_8 hv] at hnz
    exact rProjAxis_embed_high_eq w (F _).1 hnz q hq
  · rw [ite_neg_8 hv] at hnz
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [ite_neg_8 hij] at hnz
      exact absurd rfl hnz
lemma basisBits_symm_apply {k : ℕ} (γ : BitAssignment k) (q : Fin k) : basisBits k
    ((basisBitsEquiv k).symm γ) q = γ q := congrFun ((basisBitsEquiv k).apply_symm_apply γ) q
@[simp] lemma vepWriteReg_not_mem {k m : ℕ} (γ : BitAssignment k) (r : QRegister m k)
    (b : BitAssignment m) (q : Fin k) (hq : q ∉ Set.range r.wires) : vepWriteReg γ r b q = γ q
    := (QRegister.basisBits_replaceIndex_of_not_mem r ((basisBitsEquiv k).symm γ)
    ((basisBitsEquiv m).symm b) q hq).trans (basisBits_symm_apply γ q)
@[simp] lemma vepWriteReg_mem {k m : ℕ} (γ : BitAssignment k) (r : QRegister m k)
    (b : BitAssignment m) (i : Fin m) : vepWriteReg γ r b (r i) = b i :=
    (QRegister.basisBits_replaceIndex_apply r ((basisBitsEquiv k).symm γ) ((basisBitsEquiv
    m).symm b) i).trans (basisBits_symm_apply b i)
@[simp] lemma val_wSlot2_id {mPayload : ℕ} :
    (wSlot2 (QRegExt.idReg (fullSysCoreWires mPayload))).val = 3950 := rfl
@[simp] lemma val_wSlot1_id {mPayload : ℕ} :
    (wSlot1 (QRegExt.idReg (fullSysCoreWires mPayload))).val = 3949 := rfl
@[simp] lemma val_wSlot0_id {mPayload : ℕ} :
    (wSlot0 (QRegExt.idReg (fullSysCoreWires mPayload))).val = 3948 := rfl
theorem uXor32Core_comm_high_wire {mPayload : ℕ} (q : Wire (fullSysCoreWires mPayload))
    (hq : 3924 ≤ q.val) (b : Fin 2) : (uXor32Core mPayload).1 * slotBitProj q b = slotBitProj
    q b * (uXor32Core mPayload).1 := by
  refine comm_slotBitProj_of_entry_eq _ q b fun i j hnz ↦ ?_
  unfold uXor32Core at hnz
  rw [permutationUnitary_entry] at hnz
  by_cases hij : xor32CorePerm mPayload j = i
  · subst hij
    unfold xor32CorePerm
    change basisBits _ ((basisBitsEquiv _).symm (xor32BitFn mPayload (basisBits _ j))) q = _
    rw [basisBits_symm_apply _ q]
    unfold xor32BitFn
    exact ite_neg_8 (by omega : ¬(q.val < 3924 ∧ q.val % 6 = 5)) _ _
  · simp [hij] at hnz
noncomputable def uVepTwistRef {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) := uVepTwistRest hm c * uBarrelCore true hm
theorem uBarrelCore_comm_high_wire {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) (b : Fin 2) :
    (uBarrelCore swapOnSlot2 hm).1 * slotBitProj q b =
      slotBitProj q b * (uBarrelCore swapOnSlot2 hm).1 := by
  refine comm_slotBitProj_of_entry_eq _ q b fun i j hnz ↦ ?_
  unfold uBarrelCore at hnz
  rw [permutationUnitary_entry] at hnz
  by_cases hij : barrelCorePerm swapOnSlot2 hm j = i
  · subst hij
    unfold barrelCorePerm
    change basisBits _ ((basisBitsEquiv _).symm (barrelBitFn swapOnSlot2 hm (basisBits _ j))) q = _
    rw [basisBits_symm_apply _ q]
    exact barrelBitFn_high_eq swapOnSlot2 hm (basisBits _ j) q hq
  · simp [hij] at hnz
theorem uVepTwistRef_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) (b : Fin 2) :
    (uVepTwistRef hm c).1 * slotBitProj q b = slotBitProj q b * (uVepTwistRef hm c).1 := by
  have hDiag (Φ : BitAssignment (fullSysCoreWires mPayload) → ℤ) :
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 Φ).1 * slotBitProj q b =
        slotBitProj q b * (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 Φ).1 := by
    unfold DyadicQft64.dyadicDiagUnitary slotBitProj
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  exact mul_comm_of_comm
    (mul_comm_of_comm (hDiag _) (mul_comm_of_comm (hDiag _)
      (mul_comm_of_comm (uXor32Core_comm_high_wire q (by omega) b)
        (mul_comm_of_comm (uCtrlProj1DCore_comm_high_wire hm 0 uProjPlus512_1D q hq b)
          (mul_comm_of_comm (uCtrlProj1DCore_comm_high_wire hm 1 uProjPlus512_1D q hq b)
            (uCtrlProj1DCore_comm_high_wire hm 2 uProjPlus512_1D q hq b))))))
    (uBarrelCore_comm_high_wire true hm q (by omega) b)
noncomputable abbrev vepSwapNuc {mPayload : ℕ} (hm : 22 ≤ mPayload) (lVal : Fin (2 ^ 8)) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (rNucIdx hm (QRegExt.idReg _)).embedUnitary
    (Operator.permutationUnitary (Equiv.swap 0 lVal))
lemma uXor32Core_mulVec_basisKet {mPayload : ℕ} (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uXor32Core mPayload).1.mulVec (basisKet γ) = basisKet (xor32BitFn mPayload γ) := by
  let j₀ : Fin (2 ^ (fullSysCoreWires mPayload)) := (basisBitsEquiv _).symm γ
  rw [uXor32Core, show basisKet γ = Pi.single j₀ (1 : ℂ) from rfl,
    Operator.permutationUnitary_mulVec_single,
    show xor32CorePerm mPayload j₀ = (basisBitsEquiv _).symm (xor32BitFn mPayload γ) by
      simp [xor32CorePerm, j₀, (basisBitsEquiv _).apply_symm_apply]]
lemma uBarrelCore_mulVec_basisKet {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : (uBarrelCore swapOnSlot2 hm).1.mulVec
    (basisKet γ) = basisKet (barrelBitFn swapOnSlot2 hm γ) := by
  let j₀ : Fin (2 ^ (fullSysCoreWires mPayload)) := (basisBitsEquiv _).symm γ
  rw [uBarrelCore, show basisKet γ = Pi.single j₀ (1 : ℂ) from rfl,
    Operator.permutationUnitary_mulVec_single,
    show barrelCorePerm swapOnSlot2 hm j₀ =
        (basisBitsEquiv _).symm (barrelBitFn swapOnSlot2 hm γ) by
      simp [barrelCorePerm, j₀, (basisBitsEquiv _).apply_symm_apply]]
lemma xor32BitFn_high_eq {mPayload : ℕ} (γ : BitAssignment (fullSysCoreWires mPayload))
    (q : Fin (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) : xor32BitFn mPayload γ q = γ q := by
  unfold xor32BitFn; exact ite_neg_8 (by omega : ¬(q.val < 3924 ∧ q.val % 6 = 5)) _ _
lemma xor32BitFn_congr_at {mPayload : ℕ} {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (q : Fin (fullSysCoreWires mPayload)) (heq : γ₁ q = γ₂ q) : xor32BitFn mPayload γ₁ q =
    xor32BitFn mPayload γ₂ q := by unfold xor32BitFn; rw [heq]
lemma dyadicDiagUnitary_mulVec_basisKet {k m : ℕ} (Φ : BitAssignment k → ℤ) (γ : BitAssignment k) :
    (DyadicQft64.dyadicDiagUnitary k m Φ).1.mulVec (basisKet γ) =
      DyadicQft64.dyadicTurn m (Φ γ) • basisKet γ := by
  let idx := (basisBitsEquiv k).symm γ
  rw [show (DyadicQft64.dyadicDiagUnitary k m Φ).1 =
      Matrix.diagonal (fun x ↦ DyadicQft64.dyadicTurn m (Φ (basisBits k x))) from rfl,
    show basisKet γ = Pi.single idx (1 : ℂ) from rfl, Matrix.diagonal_mulVec_single,
    show basisBits k idx = γ from (basisBitsEquiv k).apply_symm_apply γ]
  ext i
  by_cases h : i = idx <;> simp [h]
lemma vepSwapNuc_mulVec_basisKet {mPayload : ℕ} (hm : 22 ≤ mPayload) (lVal : Fin (2 ^ 8))
    (γ : BitAssignment (fullSysCoreWires mPayload)) : (vepSwapNuc hm lVal).1.mulVec
    (basisKet γ) = basisKet (vepWriteReg γ (rNucIdx hm (QRegExt.idReg _)) (basisBits 8
    (Equiv.swap 0 lVal ((rNucIdx hm (QRegExt.idReg _)).extractIndex ((basisBitsEquiv _).symm
    γ))))) := by
  let rN := rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload))
  let s := rN.extractIndex ((basisBitsEquiv _).symm γ)
  rw [vepSwapNuc, QRegister.embedUnitary_val, vepEmbedMatrix_mulVec_basisKet,
    show ((basisBitsEquiv 8).symm fun i ↦ γ (rN i)) = s by
      apply (basisBitsEquiv 8).injective; rw [(basisBitsEquiv 8).apply_symm_apply]; funext i
      change _ = basisBits 8 s i; rw [QRegister.basisBits_extractIndex]
      exact (basisBits_symm_apply γ _).symm,
    Finset.sum_eq_single (Equiv.swap 0 lVal s)
      (fun l _ hne ↦ by rw [permutationUnitary_entry, ite_neg_8 (Ne.symm hne), zero_smul])
      (fun habs ↦ absurd (Finset.mem_univ _) habs),
    permutationUnitary_entry, ite_pos_8 rfl, one_smul]
theorem uVepTwistRef_host_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (hHost : vepHighNuc hm γ = false) :
    (uVepTwistRef hm c).1.mulVec (basisKet γ) = (uTwistParam true hm c).1.mulVec (basisKet γ) := by
  let γB := barrelBitFn true hm γ
  let γX := xor32BitFn mPayload γB
  have hBHi (q : Fin (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) : γB q = γ q :=
    barrelBitFn_high_eq true hm γ q (by omega)
  have hXHi (q : Fin (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) : γX q = γ q :=
    (xor32BitFn_high_eq γB q (by omega)).trans (hBHi q hq)
  simp only [uVepTwistRef, uVepTwistRest, uTwistParam, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [uBarrelCore_mulVec_basisKet, uCtrlProj3DCore_mulVec_basisKet,
    ite_neg_8 (Bool.eq_false_iff.mp ((vepHighNuc_eq_of_high_eq hm hBHi).trans hHost)),
    uXor32Core_mulVec_basisKet]
  simp only [uSlot4KickCore, uVepSlot2KickCore, uSlot2KickCore, dyadicDiagUnitary_mulVec_basisKet,
    Matrix.mulVec_smul]
  rw [show vepSlot2TotalPhaseExp c hm γX = slot2TotalPhaseExp c hm γX by
    unfold vepSlot2TotalPhaseExp slot2TotalPhaseExp slot2AxisDelta
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [show vepOnlyM48Val hm w γX = 0 from ite_neg_8
      (Bool.eq_false_iff.mp ((vepHighNuc_eq_of_high_eq hm hXHi).trans hHost)) _ _, add_zero]
    push_cast
    rfl]
attribute [local irreducible] uProjPlus512_3D
private lemma barrelBitFn_vepWriteReg_comm {mPayload m : ℕ} (hm : 22 ≤ mPayload)
    (r : QRegister m (fullSysCoreWires mPayload))
    (hr : ∀ i : Fin m, (3924 ≤ (r i).val ∧ (r i).val < 3948) ∨
      (3960 ≤ (r i).val ∧ (r i).val < 3968))
    (η : BitAssignment (fullSysCoreWires mPayload)) (b : BitAssignment m) :
    vepWriteReg (barrelBitFn true hm η) r b = barrelBitFn true hm (vepWriteReg η r b) := by
  have hout (q : Fin (fullSysCoreWires mPayload))
      (hq : ¬((3924 ≤ q.val ∧ q.val < 3948) ∨ (3960 ≤ q.val ∧ q.val < 3968))) :
      vepWriteReg η r b q = η q :=
    vepWriteReg_not_mem η r b q fun ⟨i, hi⟩ ↦ hq (hi ▸ hr i)
  funext q
  by_cases hqR : q ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hqR
    rw [vepWriteReg_mem, barrelBitFn_high_eq true hm _ (r i)
      (by rcases hr i with h | h <;> omega), vepWriteReg_mem]
  · rw [vepWriteReg_not_mem _ r b q hqR]
    by_cases hq24 : 3924 ≤ q.val
    · rw [barrelBitFn_high_eq true hm η q hq24, barrelBitFn_high_eq true hm _ q hq24,
        vepWriteReg_not_mem η r b q hqR]
    · have hactEq : barrelActive true (vepWriteReg η r b) = barrelActive true η := by
        unfold barrelActive
        rw [hout _ (by simp), hout _ (by simp), hout _ (by simp)]
      have hancEq : regVal (rAnchorIdx hm (QRegExt.idReg _)) (vepWriteReg η r b) =
          regVal (rAnchorIdx hm (QRegExt.idReg _)) η :=
        regVal_congr _ fun j ↦ hout _ (by
          rw [rAnchorIdx_id_val]
          have := j.isLt
          omega)
      unfold barrelBitFn
      simp only [hactEq, hancEq]
      by_cases hc : barrelActive true η = true ∧ regVal (rAnchorIdx hm (QRegExt.idReg _)) η < 218
      · rw [dite_pos_8 hc, dite_pos_8 hc]
        have := hc.2
        by_cases hk0 : q.val < 18
        · rw [dite_pos_8 hk0, dite_pos_8 hk0]
          exact (hout _ (by
            dsimp
            omega)).symm
        · rw [dite_neg_8 hk0, dite_neg_8 hk0]
          by_cases hk1 : 18 * regVal (rAnchorIdx hm (QRegExt.idReg _)) η ≤ q.val ∧
              q.val < 18 * regVal (rAnchorIdx hm (QRegExt.idReg _)) η + 18
          · rw [dite_pos_8 hk1, dite_pos_8 hk1]
            exact (hout _ (by
              dsimp
              omega)).symm
          · rw [dite_neg_8 hk1, dite_neg_8 hk1]
            exact (hout q (by omega)).symm
      · rw [dite_neg_8 hc, dite_neg_8 hc, hout q (by omega)]
theorem uVepTwistRef_vep_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration)
    (lVal : Fin (2 ^ 8)) (γ : BitAssignment (fullSysCoreWires mPayload))
    (hVep : vepHighNuc hm γ = true) (hNuc : (rNucIdx hm (QRegExt.idReg _)).extractIndex
    ((basisBitsEquiv _).symm γ) = lVal) : (uVepTwistRef hm c).1.mulVec (basisKet γ) = ∑ yIdx :
    Fin (2 ^ 24), (uProjPlus512_3D (extractCosetP3 hm γ)).1 yIdx (extractProj24 γ) •
    (vepSwapNuc hm lVal * uTwistParam true hm (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24
    yIdx, extractCosetP3 hm γ))) * vepSwapNuc hm lVal).1.mulVec (basisKet (vepWriteReg γ
    (rProjCore (QRegExt.idReg _)) (basisBits 24 yIdx))) := by
  let rP := rProjCore (QRegExt.idReg (fullSysCoreWires mPayload))
  let rN := rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload))
  have hrP_mem (q : Fin (fullSysCoreWires mPayload)) :
      q ∈ Set.range rP.wires ↔ 3924 ≤ q.val ∧ q.val < 3948 :=
    ⟨fun ⟨i, hi⟩ ↦ by
       have := i.isLt
       have hv : (rP i).val = 3924 + i.val := rProjCore_id_val (mPayload := mPayload) i
       rw [← hi]; change 3924 ≤ (rP i).val ∧ (rP i).val < 3948; omega,
     fun hq ↦
       ⟨⟨q.val - 3924, by omega⟩, Fin.ext (by dsimp [rP]; rw [rProjCore_id_val]; dsimp; omega)⟩⟩
  have hrN_mem (q : Fin (fullSysCoreWires mPayload)) :
      q ∈ Set.range rN.wires ↔ 3960 ≤ q.val ∧ q.val < 3968 :=
    ⟨fun ⟨i, hi⟩ ↦ by
       have := i.isLt
       have hv : (rN i).val = 3960 + i.val := rNucIdx_id_val hm i
       rw [← hi]; change 3960 ≤ (rN i).val ∧ (rN i).val < 3968; omega,
     fun hq ↦
       ⟨⟨q.val - 3960, by omega⟩, Fin.ext (by dsimp [rN]; rw [rNucIdx_id_val]; dsimp; omega)⟩⟩
  have hextEq {k : ℕ} (r : QRegister k (fullSysCoreWires mPayload)) (η) (x : Fin (2 ^ k))
      (h : ∀ i, η (r i) = basisBits k x i) : r.extractIndex ((basisBitsEquiv _).symm η) = x :=
    (basisBitsEquiv k).injective (funext fun i ↦ by
      change basisBits k _ i = basisBits k x i
      rw [QRegister.basisBits_extractIndex, basisBits_symm_apply, h i])
  have hB24 : ∀ q, 3924 ≤ q.val → barrelBitFn true hm γ q = γ q := barrelBitFn_high_eq true hm γ
  have hB48 : ∀ q, 3948 ≤ q.val → barrelBitFn true hm γ q = γ q := fun q hq ↦ hB24 q (by omega)
  have hProj_B : extractProj24 (barrelBitFn true hm γ) = extractProj24 γ :=
    hextEq rP _ _ fun i ↦ (hB24 (rP i) ((hrP_mem (rP i)).mp ⟨i, rfl⟩).1).trans
      (by rw [extractProj24, QRegister.basisBits_extractIndex, basisBits_symm_apply])
  unfold uVepTwistRef uVepTwistRest
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [uBarrelCore_mulVec_basisKet, uCtrlProj3DCore_mulVec_basisKet,
    ite_pos_8 ((vepHighNuc_eq_of_high_eq hm hB48).trans hVep),
    (show extractCosetP3 hm (barrelBitFn true hm γ) = extractCosetP3 hm γ from
      funext fun w ↦ extractCosetP3_eq_of_high_eq hm w hB48),
    hProj_B, Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  congr 1
  let γ_y := vepWriteReg γ rP (basisBits 24 yIdx)
  let zP_y := nyq512ProjEquiv3D (projGridEquiv24 yIdx, extractCosetP3 hm γ)
  have hγy_out (q) (hnq : ¬(3924 ≤ q.val ∧ q.val < 3948)) : γ_y q = γ q :=
    vepWriteReg_not_mem γ rP (basisBits 24 yIdx) q fun hm_p ↦ hnq ((hrP_mem q).mp hm_p)
  change (uVepSlot2KickCore c hm).1.mulVec ((uSlot4KickCore hm).1.mulVec
      ((uXor32Core mPayload).1.mulVec
        (basisKet (vepWriteReg (barrelBitFn true hm γ) rP (basisBits 24 yIdx))))) = _
  rw [barrelBitFn_vepWriteReg_comm hm rP (fun i ↦ Or.inl ((hrP_mem (rP i)).mp ⟨i, rfl⟩)) γ
    (basisBits 24 yIdx), uXor32Core_mulVec_basisKet]
  let δ_y := xor32BitFn mPayload (barrelBitFn true hm γ_y)
  have hδy_ge24 (q) (hq : 3924 ≤ q.val) : δ_y q = γ_y q :=
    (xor32BitFn_high_eq _ q hq).trans (barrelBitFn_high_eq true hm γ_y q hq)
  have hδy_ge48 (q) (hq : 3948 ≤ q.val) : δ_y q = γ q :=
    (hδy_ge24 q (by omega)).trans (hγy_out q (by omega))
  have hNuc_γy : rN.extractIndex ((basisBitsEquiv _).symm γ_y) = lVal :=
    hextEq rN γ_y lVal fun i ↦
      (hγy_out (rN i) (by have := (hrN_mem (rN i)).mp ⟨i, rfl⟩; omega)).trans
      (by rw [← hNuc, QRegister.basisBits_extractIndex, basisBits_symm_apply])
  let γ_y0 := vepWriteReg γ_y rN (basisBits 8 0)
  have hB_comm_N := (barrelBitFn_vepWriteReg_comm hm rN
    (fun i ↦ Or.inr ((hrN_mem (rN i)).mp ⟨i, rfl⟩)) γ_y (basisBits 8 0)).symm
  let δ_y0 := xor32BitFn mPayload (barrelBitFn true hm γ_y0)
  have hδy0_eq_write : δ_y0 = vepWriteReg δ_y rN (basisBits 8 0) := funext fun q ↦ by
    by_cases hqN : q ∈ Set.range rN.wires
    · obtain ⟨i, rfl⟩ := hqN
      have hq24 : 3924 ≤ (rN i).val := by have := (hrN_mem (rN i)).mp ⟨i, rfl⟩; omega
      dsimp [δ_y0]
      rw [xor32BitFn_high_eq _ (rN i) hq24, barrelBitFn_high_eq true hm γ_y0 (rN i) hq24]
      exact (vepWriteReg_mem γ_y rN (basisBits 8 0) i).trans
        (vepWriteReg_mem δ_y rN (basisBits 8 0) i).symm
    · rw [vepWriteReg_not_mem δ_y rN (basisBits 8 0) q hqN]
      exact xor32BitFn_congr_at q ((congrFun hB_comm_N q).trans
        (vepWriteReg_not_mem _ rN (basisBits 8 0) q hqN))
  have hδy0_out (q) (hnq : ¬(3960 ≤ q.val ∧ q.val < 3968)) : δ_y0 q = δ_y q :=
    hδy0_eq_write ▸ vepWriteReg_not_mem δ_y rN (basisBits 8 0) q fun hm_n ↦
      hnq ((hrN_mem q).mp hm_n)
  have hWriteBack : vepWriteReg δ_y0 rN (basisBits 8 lVal) = δ_y := funext fun q ↦ by
    by_cases hqN : q ∈ Set.range rN.wires
    · obtain ⟨i, rfl⟩ := hqN
      have hrNi := (hrN_mem (rN i)).mp ⟨i, rfl⟩
      rw [vepWriteReg_mem, ← hNuc, QRegister.basisBits_extractIndex, basisBits_symm_apply]
      exact (hδy_ge48 (rN i) (by omega)).symm
    · exact (vepWriteReg_not_mem δ_y0 rN (basisBits 8 lVal) q hqN).trans
        (hδy0_out q fun hh ↦ hqN ((hrN_mem q).mpr hh))
  dsimp only [uTwistParam, Submonoid.coe_mul]
  simp only [← Matrix.mulVec_mulVec]
  rw [show (vepSwapNuc hm lVal).1.mulVec (basisKet γ_y) = basisKet γ_y0 by
      rw [vepSwapNuc_mulVec_basisKet hm lVal γ_y]
      change basisKet (vepWriteReg γ_y rN (basisBits 8 (Equiv.swap 0 lVal _))) = _
      rw [hNuc_γy, Equiv.swap_apply_right],
    uBarrelCore_mulVec_basisKet, uXor32Core_mulVec_basisKet]
  simp only [uSlot4KickCore, uVepSlot2KickCore, uSlot2KickCore, dyadicDiagUnitary_mulVec_basisKet,
    Matrix.mulVec_smul]
  rw [show (vepSwapNuc hm lVal).1.mulVec (basisKet δ_y0) = basisKet δ_y by
      rw [vepSwapNuc_mulVec_basisKet hm lVal δ_y0]
      change basisKet (vepWriteReg δ_y0 rN (basisBits 8 (Equiv.swap 0 lVal _))) = _
      rw [hextEq rN δ_y0 0 fun i ↦ by rw [hδy0_eq_write, vepWriteReg_mem],
        Equiv.swap_apply_left, hWriteBack]]
  have hS4Eq : slot4TotalPhaseExp hm δ_y0 = slot4TotalPhaseExp hm δ_y := by
    unfold slot4TotalPhaseExp
    rw [hδy0_out (wSlot2 (QRegExt.idReg _)) (by simp),
      hδy0_out (wSlot1 (QRegExt.idReg _)) (by simp),
      hδy0_out (wSlot0 (QRegExt.idReg _)) (by simp)]
    split_ifs with hc4
    · refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [hδy0_out _ (by rw [rCosetB1_id_val]; have := w.isLt; omega),
        hδy0_out _ (by
          change ¬(3960 ≤ (rProjCosetP3 hm _ w).val ∧ _)
          rw [rProjCosetP3_id_val]; have := w.isLt; omega),
        regVal_congr _ fun j ↦ hδy0_out _ (by
          rw [rElecSlotAxis_id_val]; have := w.isLt; have := j.isLt; dsimp; omega)]
    · rfl
  have hS2Eq : vepSlot2TotalPhaseExp c hm δ_y = slot2TotalPhaseExp (cfgProjZ512 zP_y) hm δ_y0 := by
    have hv_δy : vepHighNuc hm δ_y = true := (vepHighNuc_eq_of_high_eq hm hδy_ge48).trans hVep
    obtain ⟨hc0_δy, hge216_δy⟩ := (vepHighNuc_iff hm δ_y).mp hv_δy
    have hc0_δy0 : coin0Active δ_y0 = true := by
      unfold coin0Active at hc0_δy ⊢
      rwa [hδy0_out _ (by simp), hδy0_out _ (by simp), hδy0_out _ (by simp)]
    have hreg0 : regVal (rNucIdx hm (QRegExt.idReg _)) δ_y0 = 0 := by
      unfold regVal bitsVal
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      dsimp only
      rw [show (rNucIdx hm (QRegExt.idReg _)).wires i = rN i from rfl,
        hδy0_eq_write, vepWriteReg_mem, (by decide +revert : ∀ i, basisBits 8 0 i = 0),
        ZMod.val_zero, zero_mul]
    unfold vepSlot2TotalPhaseExp slot2TotalPhaseExp slot2AxisDelta
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hlt : coin0Active δ_y0 = true ∧ regVal (rNucIdx hm (QRegExt.idReg _)) δ_y0 < 216 :=
      ⟨hc0_δy0, by omega⟩
    rw [show slot2AxisSum w δ_y = slot2AxisSum w δ_y0 from
        Finset.sum_congr rfl fun e _ ↦ regVal_congr _ fun j ↦ (hδy0_out _ (by
          have := e.isLt
          have := w.isLt
          have := j.isLt
          have hne218 : numElectrons = 218 := rfl
          rw [rElecSlotAxis_id_val]
          omega)).symm,
      show slot2M48Val c hm w δ_y = 0 from dite_neg_8 fun h ↦ by omega, zero_add,
      show vepOnlyM48Val hm w δ_y = 2 ^ 39 * (zP_y w).val by
        unfold vepOnlyM48Val
        rw [ite_pos_8 hv_δy, bitsVal_vepProj9CoreIdx_eq hm w δ_y,
          show extractProj24 δ_y = yIdx from hextEq rP δ_y yIdx fun i ↦ by
            rw [hδy_ge24 (rP i) ((hrP_mem (rP i)).mp ⟨i, rfl⟩).1]
            simp [γ_y],
          show extractCosetP3 hm δ_y = extractCosetP3 hm γ from
            funext fun w' ↦ extractCosetP3_eq_of_high_eq hm w' hδy_ge48],
      show slot2M48Val (cfgProjZ512 zP_y) hm w δ_y0 = 2 ^ 39 * (zP_y w).val by
        unfold slot2M48Val
        rw [dite_pos_8 hlt,
          show (⟨regVal _ δ_y0, hlt.2⟩ : Fin 216) = 0 from Fin.ext hreg0]
        exact nuclearM48_cfgProjZ512_eq zP_y 0 w]
    push_cast
    rfl
  rw [hS4Eq, hS2Eq]
end ConfigProjZ512TwistVepTopBundle288
set_option maxRecDepth 4096
end ProjZ512QftAndTwist288
end
end ModProjZ512TwistVepTopBundle288

section ModFusedVepCore288
@[expose] public section
namespace FusedVepCore288
section ConfigFusedVepCore288
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open DyadicQft64WalkCircuit hiding wSlot2
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288
local instance (priority := 1000000) instNeZeroTwoPowSFCore (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
lemma basisKet_eq_single {n : ℕ} (β : BitAssignment n) :
    basisKet β = Pi.single (M := fun _ ↦ ℂ) ((basisBitsEquiv n).symm β) (1 : ℂ) := rfl
private lemma basisKet_basisBits {n : ℕ} (k : Fin (2 ^ n)) :
    basisKet (basisBits n k) = Pi.single (M := fun _ ↦ ℂ) k (1 : ℂ) := by
  rw [basisKet_eq_single]
  change Pi.single (M := fun _ ↦ ℂ) ((basisBitsEquiv n).symm ((basisBitsEquiv n) k)) (1 : ℂ) = _
  rw [(basisBitsEquiv n).symm_apply_apply]
private lemma vec_eq_sum_basisKet {n : ℕ} (v : Fin (2 ^ n) → ℂ) :
    v = ∑ k : Fin (2 ^ n), v k • basisKet (basisBits n k) := by
  ext idx
  simp [Finset.sum_apply, basisKet_basisBits, Pi.single_apply]
lemma basisBits_zero_apply {k : ℕ} (i : Fin k) :
    (basisBitsEquiv k) (0 : Fin (2 ^ k)) i = 0 := by
  change (ZMod.finEquiv 2).symm (finFunctionFinEquiv.symm (0 : Fin (2 ^ k)) i) = 0
  rw [← show finFunctionFinEquiv (fun _ : Fin k ↦
    (0 : Fin 2)) = 0 by ext; simp [finFunctionFinEquiv],
    finFunctionFinEquiv.symm_apply_apply]
  rfl
theorem mat_ext_basisKet {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (basisKet β) = B.mulVec (basisKet β)) : A = B := by
  ext i j
  have hcol := congrFun (h (basisBits n j)) i
  rwa [basisKet_basisBits, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hcol
theorem reg_zero_proj_mulVec_basisKet {kW n : ℕ} (rW : QRegister kW n) (β : BitAssignment n) :
    (rW.basisOutcomeProjector 0).mulVec (basisKet β) = if (∀ i : Fin kW, β (rW i) = 0) then
    basisKet β else 0 := by
  rw [basisKet_eq_single, QRegister.basisOutcomeProjector_mulVec_single]
  have hiff : rW.extractIndex ((basisBitsEquiv n).symm β) = 0 ↔ ∀ i : Fin kW, β (rW i) = 0 := by
    refine ⟨fun h0 i ↦ ?_, fun hz ↦ (basisBitsEquiv kW).injective (funext fun i ↦ ?_)⟩
    · have hb := QRegister.basisBits_extractIndex rW ((basisBitsEquiv n).symm β) i
      change (basisBitsEquiv kW) _ i =
        (basisBitsEquiv n) ((basisBitsEquiv n).symm β) (rW.wires i) at hb
      rwa [(basisBitsEquiv n).apply_symm_apply, h0, basisBits_zero_apply, eq_comm] at hb
    · have hb := QRegister.basisBits_extractIndex rW ((basisBitsEquiv n).symm β) i
      change (basisBitsEquiv kW) _ i =
        (basisBitsEquiv n) ((basisBitsEquiv n).symm β) (rW.wires i) at hb
      rw [(basisBitsEquiv n).apply_symm_apply, hz i] at hb
      exact hb.trans (basisBits_zero_apply i).symm
  by_cases h1 : rW.extractIndex ((basisBitsEquiv n).symm β) = 0
  · rw [ite_eq_left_iff.mpr (absurd h1), ite_eq_left_iff.mpr (absurd (hiff.mp h1))]
  · rw [ite_eq_right_iff.mpr fun h ↦ absurd h h1, ite_eq_right_iff.mpr fun hz ↦
      absurd (hiff.mpr hz) h1]
def DiagOn {n : ℕ} (S : Finset (Wire n)) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  ∀ i j : Fin (2 ^ n), M i j ≠ 0 → ∀ u ∈ S, basisBits n i u = basisBits n j u
theorem DiagOn.mul {n : ℕ} {S : Finset (Wire n)} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hA : DiagOn S A) (hB : DiagOn S B) : DiagOn S (A * B) := fun i j hij u hu ↦ by
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact (hA i k (left_ne_zero_of_mul hne) u hu).trans (hB k j (right_ne_zero_of_mul hne) u hu)
theorem DiagOn.conjTranspose {n : ℕ} {S : Finset (Wire n)}
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : DiagOn S M) : DiagOn S Mᴴ := fun i j hij u hu ↦ by
  rw [Matrix.conjTranspose_apply, star_ne_zero] at hij
  exact (hM j i hij u hu).symm
theorem DiagOn.anti {n : ℕ} {S₁ S₂ : Finset (Wire n)} {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hSub : S₁ ⊆ S₂) (hM : DiagOn S₂ M) : DiagOn S₁ M :=
  fun i j hij u hu ↦ hM i j hij u (hSub hu)
theorem DiagOn.of_mulVec_basisKet {n : ℕ} {S : Finset (Wire n)}
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (h : ∀ (β : BitAssignment n) (i : Fin (2 ^ n)),
    (M.mulVec (basisKet β)) i ≠ 0 → ∀ u ∈ S, basisBits n i u = β u) : DiagOn S M :=
  fun i j hij u hu ↦ h (basisBits n j) i
    (by rw [basisKet_basisBits, Matrix.mulVec_single_one]; exact hij) u hu
theorem DiagOn.conj_involutive_perm {n : ℕ} {S : Finset (Wire n)}
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hM : DiagOn S M) {c : Circuit n}
    {f : BitAssignment n → BitAssignment n} (hc : PhasePerm ⊤ c (fun _ ↦ 1) f)
    (hInv : ∀ β, f (f β) = β) (hInjS : ∀ β₁ β₂ : BitAssignment n, (∀ u ∈ S, f β₁ u = f β₂ u) →
    ∀ u ∈ S, β₁ u = β₂ u) : DiagOn S (c.eval.1 * M * c.eval.1) := by
  refine DiagOn.of_mulVec_basisKet fun β i hi u hu ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc.evolve β, one_smul] at hi
  let v := M.mulVec (basisKet (f β))
  change (c.eval.1.mulVec v) i ≠ 0 at hi
  rw [vec_eq_sum_basisKet v, Matrix.mulVec_sum, Finset.sum_apply] at hi
  obtain ⟨k, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  rw [Matrix.mulVec_smul, hc.evolve (basisBits n k), one_smul, Pi.smul_apply] at hne
  have hketk := right_ne_zero_of_mul hne
  rw [basisKet_eq_single, Pi.single_apply] at hketk
  split_ifs at hketk with hEqI
  · subst hEqI
    have hEntry : M k ((basisBitsEquiv n).symm (f β)) ≠ 0 := by
      have hvk := left_ne_zero_of_mul hne
      dsimp only [v] at hvk
      rwa [basisKet_eq_single, Matrix.mulVec_single_one] at hvk
    change (basisBitsEquiv n) ((basisBitsEquiv n).symm (f (basisBits n k))) u = β u
    rw [(basisBitsEquiv n).apply_symm_apply]
    refine hInjS (f (basisBits n k)) β (fun x hx ↦ ?_) u hu
    rw [hInv]
    exact (hM k _ hEntry x hx).trans (DyadicQft64WalkCircuit.basisBits_symm_apply (f β) x)
  · exact absurd rfl hketk
theorem DiagOn.conj_X {n : ℕ} {S : Finset (Wire n)} (w : Wire n)
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hM : DiagOn S M) :
    DiagOn S ((Circuit.X w).eval.1 * M * (Circuit.X w).eval.1) :=
  DiagOn.conj_involutive_perm hM (phasePerm_X w)
    (fun β ↦ funext fun y ↦ by
      by_cases hy : y = w
      · subst hy; rw [Function.update_self, Function.update_self, zmod2_add_self]
      · rw [Function.update_of_ne hy, Function.update_of_ne hy])
    (fun β₁ β₂ hEq u hu ↦ by
      have h := hEq u hu
      by_cases hy : u = w
      · subst hy; rw [Function.update_self, Function.update_self] at h; linear_combination h
      · rwa [Function.update_of_ne hy, Function.update_of_ne hy] at h)
theorem DiagOn.conj_TOFF {n : ℕ} {S : Finset (Wire n)} (a b t : Wire n) (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) (ha : a ∈ S) (hb : b ∈ S)
    {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hM : DiagOn S M) : DiagOn S ((Circuit.TOFF a b
    t hab hat hbt).eval.1 * M * (Circuit.TOFF a b t hab hat hbt).eval.1) :=
  DiagOn.conj_involutive_perm hM (phasePerm_TOFF a b t hab hat hbt)
    (fun β ↦ funext fun y ↦ by
      by_cases hy : y = t
      · subst hy
        rw [Function.update_self, Function.update_self, Function.update_of_ne hat,
          Function.update_of_ne hbt, zmod2_add_self]
      · rw [Function.update_of_ne hy, Function.update_of_ne hy])
    (fun β₁ β₂ hEq u hu ↦ by
      have haEq : β₁ a = β₂ a := by
        simpa [Function.update_of_ne hat] using hEq a ha
      have hbEq : β₁ b = β₂ b := by
        simpa [Function.update_of_ne hbt] using hEq b hb
      have h := hEq u hu
      by_cases hy : u = t
      · subst hy; rw [Function.update_self, Function.update_self, haEq, hbEq] at h
        linear_combination h
      · rwa [Function.update_of_ne hy, Function.update_of_ne hy] at h)
def dAndSandwich {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dInner : DynamicCircuit Var n) : DynamicCircuit Var n
    := .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
    (.seq dInner (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
@[local simp]
theorem count_dAndSandwich_toff {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dInner : DynamicCircuit Var n) :
    (dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a dInner).count .TOFF = dInner.count .TOFF := by
  simp [dAndSandwich, DynamicCircuit.andCompute, DynamicCircuit.andUncompute,
    Circuit.andCompute, Circuit.andUncomputeFixup, Circuit.inverseGate, Circuit.sequence,
    DynamicCircuit.count, Circuit.count]
@[local simp] theorem count_dAndSandwich_t {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dInner : DynamicCircuit Var n) :
    (dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a dInner).count .T = 4 + dInner.count .T := by
  simp [dAndSandwich, DynamicCircuit.andCompute, DynamicCircuit.andUncompute,
    Circuit.andCompute, Circuit.andUncomputeFixup, Circuit.inverseGate, Circuit.sequence,
    DynamicCircuit.count, Circuit.count]
theorem storeConst_dAndSandwich {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {dInner : DynamicCircuit Var n} (hInner : GridGuard654ReflAux.StoreConst dInner) :
    GridGuard654ReflAux.StoreConst (dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a dInner) :=
  (GridGuard654ReflAux.StoreConst.circuit _).seq
    (hInner.seq (GridGuard654ReflAux.StoreConst.andUncompute v c₁ c₂ anc h₁₂))
def dPureConj {Var : Type} {n : ℕ} (cPre : Circuit n) (dInner : DynamicCircuit Var n) :
    DynamicCircuit Var n := .seq (.circuit cPre) (.seq dInner (.circuit cPre.inverse))
theorem count_dPureConj_toff {Var : Type} {n : ℕ} (cPre : Circuit n)
    (hc : cPre.count .TOFF = 0) (dInner : DynamicCircuit Var n) :
    (dPureConj cPre dInner).count .TOFF = dInner.count .TOFF := by
  simp [dPureConj, DynamicCircuit.count, hc,
    show cPre.inverse.count .TOFF = 0 by rw [count_inverse_toff, hc]]
theorem count_dPureConj_t {Var : Type} {n : ℕ} (cPre : Circuit n) (hc : cPre.count .T = 0)
    (dInner : DynamicCircuit Var n) : (dPureConj cPre dInner).count .T = dInner.count .T := by
  simp [dPureConj, DynamicCircuit.count, hc, count_inverse_t_of_zero hc]
theorem storeConst_dPureConj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (cPre : Circuit n) {dInner : DynamicCircuit Var n}
    (hInner : GridGuard654ReflAux.StoreConst dInner) : GridGuard654ReflAux.StoreConst
    (dPureConj cPre dInner) := (GridGuard654ReflAux.StoreConst.circuit cPre).seq
    (hInner.seq (GridGuard654ReflAux.StoreConst.circuit cPre.inverse))
structure CleanUnitaryWp {Var : Type} [Fintype Var] [DecidableEq Var]
    {mW n : ℕ} [NeZero (2 ^ n)]
    (rW : QRegister mW n) (u : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop where
  storeConst : GridGuard654ReflAux.StoreConst d
  wp_eq : ∀ M : Observable (Fin (2 ^ n)),
    CQAssertion.restrictToZeroAncilla (wp d.compile (fun _ ↦ M)) rW =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat u (fun _ ↦ M)) rW
theorem CleanUnitaryWp.identity {Var : Type} [Fintype Var] [DecidableEq Var]
    {mW n : ℕ} [NeZero (2 ^ n)] (rW : QRegister mW n) :
    CleanUnitaryWp (Var := Var) rW 1 .identity :=
  ⟨GridGuard654ReflAux.StoreConst.identity, fun M ↦ funext fun _ ↦
    Subtype.ext (by simp [qAssignObsMap])⟩
theorem CleanUnitaryWp.of_realizesClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {mA mW n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister mA n} {rW : QRegister mW n}
    {U : Unitary (2 ^ mA)} {d : DynamicCircuit Var n} (hd :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rW U d) : CleanUnitaryWp rW
    (rAct.embedUnitary U) d := by
  refine ⟨fun M ↦ ⟨(hd M).choose, (hd M).choose_spec.1⟩, fun M ↦ ?_⟩
  obtain ⟨M', h1, h2⟩ := hd M
  rw [h1]
  refine funext fun σ ↦ Subtype.ext (Subtype.ext ?_)
  change (CQAssertion.restrictToZeroAncilla (fun _ : Store Var ↦ M') rW σ).1.mat =
    (CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (rAct.embedUnitary U) (fun _ : Store Var ↦ M)) rW σ).1.mat
  rw [CQAssertion.restrictToZeroAncilla_coe, CQAssertion.restrictToZeroAncilla_coe,
    show (wpQAssignCompat (rAct.embedUnitary U) (fun _ : Store Var ↦ M) σ).1 =
      M.1.conj (rAct.embedUnitary U).1ᴴ by
      simp [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose],
    HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
    Matrix.conjTranspose_conjTranspose, QRegister.basisOutcomeProjector_conjTranspose rW 0]
  exact h2
theorem CleanUnitaryWp.to_realizesClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {mA mW n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister mA n} {rW : QRegister mW n}
    {U : Unitary (2 ^ mA)} {d : DynamicCircuit Var n}
    (hw : CleanUnitaryWp rW (rAct.embedUnitary U) d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rW U d := fun M ↦ by
  obtain ⟨M', h⟩ := hw.storeConst M
  refine ⟨M', h, ?_⟩
  have hMat :=
    congrArg (fun x : Observable (Fin (2 ^ n)) ↦ x.1.mat) (congrFun (hw.wp_eq M) (fun _ ↦ 0))
  rwa [h, CQAssertion.restrictToZeroAncilla_coe, CQAssertion.restrictToZeroAncilla_coe,
    show (wpQAssignCompat (rAct.embedUnitary U) (fun _ : Store Var ↦ M) (fun _ ↦ 0)).1 =
      M.1.conj (rAct.embedUnitary U).1ᴴ by
      simp [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose],
    HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
    Matrix.conjTranspose_conjTranspose, QRegister.basisOutcomeProjector_conjTranspose rW 0] at hMat
theorem CleanUnitaryWp.mono_workspace {Var : Type} [Fintype Var] [DecidableEq Var]
    {mSub mTot n : ℕ} [NeZero (2 ^ n)] {rSub : QRegister mSub n} {rTot : QRegister mTot n}
    (hSub : rSub.image ⊆ rTot.image) {u : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hw : CleanUnitaryWp rSub u d) : CleanUnitaryWp rTot u d := ⟨hw.storeConst, fun M ↦
    NuclearTwistMulKickAndBridge288.restrictAssertionToZeroAncilla_eq_of_subset hSub (hw.wp_eq M)⟩
theorem CleanUnitaryWp.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ}
    [NeZero (2 ^ n)] {rW : QRegister mW n} {u₁ u₂ : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hw : CleanUnitaryWp rW u₁ d) (hu : u₁ = u₂) : CleanUnitaryWp
    rW u₂ d := hu ▸ hw
theorem CleanUnitaryWp.congr_cleanKet {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ}
    [NeZero (2 ^ n)] {rW : QRegister mW n} {u₁ u₂ : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hw : CleanUnitaryWp rW u₁ d) (hKet : ∀ β : BitAssignment n, (∀
    i : Fin mW, β (rW i) = 0) → u₁.1.mulVec (basisKet β) = u₂.1.mulVec (basisKet β)) :
    CleanUnitaryWp rW u₂ d := by
  refine ⟨hw.storeConst, fun M ↦ (hw.wp_eq M).trans (funext fun σ ↦ Subtype.ext ?_)⟩
  let P₀ := rW.basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose rW 0
  have hUP : u₁.1 * P₀ = u₂.1 * P₀ := mat_ext_basisKet fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, reg_zero_proj_mulVec_basisKet]
    by_cases hz : ∀ i : Fin mW, β (rW i) = 0
    · rw [ite_eq_left_iff.mpr (absurd hz)]
      exact hKet β hz
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [show P₀ * u₁.1ᴴ = (u₁.1 * P₀)ᴴ by rw [conjTranspose_mul, hP₀_herm],
    show P₀ * u₂.1ᴴ = (u₂.1 * P₀)ᴴ by rw [conjTranspose_mul, hP₀_herm], hUP]
theorem CleanUnitaryWp.seq_of_diag {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ}
    [NeZero (2 ^ n)] {rW : QRegister mW n} {u₁ u₂ : Unitary (2 ^ n)}
    {d₁ d₂ : DynamicCircuit Var n} (hw₁ : CleanUnitaryWp rW u₁ d₁)
    (hw₂ : CleanUnitaryWp rW u₂ d₂) (hDiag₁ : DiagOn rW.image u₁.1) : CleanUnitaryWp rW
    (u₂ * u₁) (.seq d₁ d₂) := by
  let P₀ := rW.basisOutcomeProjector 0
  have hPres₁ : P₀ * (u₁.1 * P₀) = u₁.1 * P₀ := mat_ext_basisKet fun β ↦ by
    dsimp only [P₀]
    simp only [← Matrix.mulVec_mulVec, reg_zero_proj_mulVec_basisKet]
    by_cases hz : ∀ i : Fin mW, β (rW i) = 0
    · rw [ite_eq_left_iff.mpr (absurd hz)]
      let v := u₁.1.mulVec (basisKet β)
      change P₀.mulVec v = v
      rw [vec_eq_sum_basisKet v, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Matrix.mulVec_smul]
      by_cases hvk : v k = 0
      · simp [hvk]
      · congr 1
        have hEntry : u₁.1 k ((basisBitsEquiv n).symm β) ≠ 0 := by
          dsimp only [v] at hvk
          rwa [basisKet_eq_single, Matrix.mulVec_single_one] at hvk
        have hz_k (i : Fin mW) : basisBits n k (rW i) = 0 :=
          ((hDiag₁ k _ hEntry (rW i) ((QRegister.mem_image rW _).mpr ⟨i, rfl⟩)).trans
            (DyadicQft64WalkCircuit.basisBits_symm_apply β (rW i))).trans (hz i)
        dsimp only [P₀]
        rw [reg_zero_proj_mulVec_basisKet, ite_eq_left_iff.mpr (absurd hz_k)]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
  refine ⟨hw₁.storeConst.seq hw₂.storeConst, fun M ↦ ?_⟩
  obtain ⟨M₂, hM₂⟩ := hw₂.storeConst M
  rw [DynamicCircuit.compile_seq, wp, hM₂, hw₁.wp_eq M₂]
  have hadj : P₀ * u₁.1ᴴ * P₀ = P₀ * u₁.1ᴴ := by
    simpa [P₀, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose rW 0,
      ← Matrix.mul_assoc] using congrArg conjTranspose hPres₁
  refine funext fun σ ↦ Subtype.ext ?_
  have h2eq : M₂.1.conj P₀ = M.1.conj (P₀ * u₂.1ᴴ) := by
    simpa only [P₀, hM₂, CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj] using
      congrArg Subtype.val (congrFun (hw₂.wp_eq M) σ)
  dsimp only [P₀] at hadj h2eq ⊢
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, Submonoid.coe_mul,
    conjTranspose_mul, conj_conj]
  rw [← hadj, ← conj_conj, h2eq, conj_conj, ← Matrix.mul_assoc, hadj, Matrix.mul_assoc]
theorem CleanUnitaryWp.dPureConj {Var : Type} [Fintype Var] [DecidableEq Var] {mTot n : ℕ}
    [NeZero (2 ^ n)] (cPre : Circuit n) (rTot : QRegister mTot n)
    (hDisj : Disjoint cPre.support rTot.image) {uInner : Unitary (2 ^ n)}
    {dInner : DynamicCircuit Var n} (hwInner : CleanUnitaryWp rTot uInner dInner) :
    CleanUnitaryWp rTot (cPre.inverse.eval * uInner * cPre.eval)
    (FusedVepCore288.dPureConj cPre dInner) := by
  refine ⟨storeConst_dPureConj cPre hwInner.storeConst, fun M ↦ ?_⟩
  have hcompat : wpQAssignCompat cPre.inverse.eval (fun _ : Store Var ↦ M) =
      fun _ ↦ qAssignObsMap cPre.inverse.eval M := rfl
  change CQAssertion.restrictToZeroAncilla
    (wp cPre.compile (wp dInner.compile (wp cPre.inverse.compile (fun _ ↦ M)))) rTot = _
  rw [wp_circuit_compile_compat, wp_circuit_compile_compat,
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint cPre rTot hDisj,
    hcompat, hwInner.wp_eq _, ← hcompat,
    ← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint cPre rTot hDisj]
  simp only [wpQAssignCompat_comp, mul_assoc]
theorem CleanUnitaryWp.dAndSandwich {Var : Type} [Fintype Var] [DecidableEq Var]
    {mSub mTot n : ℕ} [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (rSub : QRegister mSub n) (rTot : QRegister mTot n)
    (hSubTot : rSub.image ⊆ rTot.image) (hAncTot : anc ∈ rTot.image)
    (hc1Sub : c₁ ∉ rSub.image) (hc2Sub : c₂ ∉ rSub.image) (hancSub : anc ∉ rSub.image)
    {uInner : Unitary (2 ^ n)} {dInner : DynamicCircuit Var n}
    (hDiag : DiagOn ({c₁, c₂, anc} : Finset (Wire n)) uInner.1)
    (hwInner : CleanUnitaryWp rSub uInner dInner) : CleanUnitaryWp rTot ((Circuit.TOFF c₁ c₂
    anc h₁₂ h₁a h₂a).eval * uInner * (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval)
    (FusedVepCore288.dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a dInner) := by
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  refine ⟨storeConst_dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a hwInner.storeConst, fun M ↦ ?_⟩
  obtain ⟨M_u, hMu⟩ := GridGuard654ReflAux.StoreConst.andUncompute v c₁ c₂ anc h₁₂ M
  let Θ_u := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (fun _ ↦ M)
  have hAndDisj : Disjoint (Circuit.andCompute c₁ c₂ anc h₁a h₂a).support rSub.image := by
    rw [Circuit.support_andCompute, Finset.disjoint_left]
    rintro u hu hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl; exacts [hc1Sub hm, hc2Sub hm, hancSub hm]
  have hStep1_sub :
      CQAssertion.restrictToZeroAncilla
        (wp (FusedVepCore288.dAndSandwich v c₁ c₂ anc h₁₂ h₁a h₂a dInner).compile (fun _ ↦ M))
        rSub =
      CQAssertion.restrictToZeroAncilla
        (wp (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
          (wpQAssignCompat uInner Θ_u)) rSub := by
    dsimp only [FusedVepCore288.dAndSandwich, DynamicCircuit.andCompute,
      DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp, Θ_u]
    simp only [wp_circuit_compile_compat, hMu,
      restrictToZeroAncilla_wp_qAssign_comm_of_disjoint _ rSub hAndDisj, hwInner.wp_eq M_u]
  refine (NuclearTwistMulKickAndBridge288.restrictAssertionToZeroAncilla_eq_of_subset
    hSubTot hStep1_sub).trans
    (NuclearTwistMulKickAndBridge288.restrictAssertionToZeroAncilla_eq_of_subset
      (by rw [QRegister.image_singleton, Finset.singleton_subset_iff]
          exact hAncTot) ?_)
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let V := T_anc * uInner * T_anc
  have hU_eq : uInner * T_anc = T_anc * V := by
    have hT_sq : T_anc * T_anc = 1 := by
      change (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval *
        (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).inverse.eval = 1
      rw [Circuit.eval_inverse, mul_inv_cancel]
    dsimp only [V]
    rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
  have hV_P₀ : P₀ * (V.1 * P₀) = V.1 * P₀ := mat_ext_basisKet fun β ↦ by
    have hP0_ket (γ : BitAssignment n) : P₀.mulVec (basisKet γ) =
        if γ anc = 0 then basisKet γ else 0 := by
      rw [reg_zero_proj_mulVec_basisKet]
      have hiff : (∀ i : Fin 1, γ ((QRegister.singleton anc) i) = 0) ↔ γ anc = 0 :=
        ⟨fun h ↦ h 0, fun h i ↦ Subsingleton.elim i 0 ▸ h⟩
      by_cases h0 : γ anc = 0
      · rw [ite_eq_left_iff.mpr (absurd (hiff.mpr h0)), ite_eq_left_iff.mpr (absurd h0)]
      · rw [ite_eq_right_iff.mpr fun h ↦ absurd (hiff.mp h) h0, ite_eq_right_iff.mpr fun h ↦
          absurd h h0]
    dsimp only [V, Submonoid.coe_mul]
    simp only [← Matrix.mulVec_mulVec, hP0_ket]
    by_cases hanc : β anc = 0
    · simp only [hanc, ↓reduceIte]
      have hp1 := (phasePerm_TOFF c₁ c₂ anc h₁₂ h₁a h₂a).evolve β
      rw [one_smul, hanc, zero_add] at hp1
      rw [hp1]
      let β₁ := Function.update β anc (β c₁ * β c₂)
      let v := uInner.1.mulVec (basisKet β₁)
      change P₀.mulVec (T_anc.1.mulVec v) = T_anc.1.mulVec v
      rw [vec_eq_sum_basisKet v, Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      by_cases hvk : v k = 0
      · simp [hvk]
      · congr 1
        have hEntry : uInner.1 k ((basisBitsEquiv n).symm β₁) ≠ 0 := by
          dsimp only [v] at hvk
          rwa [basisKet_eq_single, Matrix.mulVec_single_one] at hvk
        have hEqBits (u) (hu : u ∈ ({c₁, c₂, anc} : Finset (Wire n))) : basisBits n k u = β₁ u :=
          (hDiag k _ hEntry u hu).trans (DyadicQft64WalkCircuit.basisBits_symm_apply β₁ u)
        have hp2 := (phasePerm_TOFF c₁ c₂ anc h₁₂ h₁a h₂a).evolve (basisBits n k)
        rw [one_smul] at hp2
        change P₀.mulVec (T_anc.1.mulVec _) = T_anc.1.mulVec _
        rw [hp2, hP0_ket, ite_eq_left_iff.mpr (absurd (by
          rw [Function.update_self, (hEqBits anc (by simp)).trans (Function.update_self ..),
            (hEqBits c₁ (by simp)).trans (Function.update_of_ne (f := β) h₁a _),
            (hEqBits c₂ (by simp)).trans (Function.update_of_ne (f := β) h₂a _),
            show ∀ z : ZMod 2, z + z = 0 by decide]))]
    · simp [hanc]
  have hadj : P₀ * V.1ᴴ * P₀ = P₀ * V.1ᴴ := by
    simpa [P₀, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose _ 0,
      ← Matrix.mul_assoc] using congrArg conjTranspose hV_P₀
  have hV_restrict (Ψ : CQAssertionCompat Var (2 ^ n)) : CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat V (CQAssertion.restrictToZeroAncilla Ψ (QRegister.singleton anc)))
      (QRegister.singleton anc) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat V Ψ)
      (QRegister.singleton anc) :=
    funext fun σ ↦ Subtype.ext (by
      dsimp only [P₀] at hadj ⊢
      simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
      rw [← Matrix.mul_assoc, hadj])
  rw [DynCircuitExt.restrictToZeroAncilla_wp_andCompute_compat c₁ c₂ anc h₁₂ h₁a h₂a]
  change CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat T_anc (wpQAssignCompat uInner Θ_u)) (QRegister.singleton anc) =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat V (fun _ ↦ M)) (QRegister.singleton anc)
  rw [wpQAssignCompat_comp, hU_eq, ← wpQAssignCompat_comp, ← hV_restrict]
  dsimp only [Θ_u, T_anc]
  rw [DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
    v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M) (fun _ _ ↦ rfl), hV_restrict]
set_option backward.isDefEq.respectTransparency true
theorem DiagOn.conj_CNOT {n : ℕ} {S : Finset (Wire n)} (a b : Wire n) (hab : a ≠ b)
    (ha : a ∈ S) {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hM : DiagOn S M) :
    DiagOn S ((Circuit.CNOT a b hab).eval.1 * M * (Circuit.CNOT a b hab).eval.1) :=
  DiagOn.conj_involutive_perm hM (phasePerm_CNOT a b hab)
    (fun β ↦ funext fun y ↦ by
      by_cases hy : y = b
      · subst hy
        rw [Function.update_self, Function.update_self, Function.update_of_ne hab, zmod2_add_self]
      · rw [Function.update_of_ne hy, Function.update_of_ne hy])
    (fun β₁ β₂ hEq u hu ↦ by
      have haEq : β₁ a = β₂ a := by simpa [Function.update_of_ne hab] using hEq a ha
      have h := hEq u hu
      by_cases hy : u = b
      · subst hy; rw [Function.update_self, Function.update_self, haEq] at h; linear_combination h
      · rwa [Function.update_of_ne hy, Function.update_of_ne hy] at h)
def cnotAllCircuit {n : ℕ} : {q : ℕ} → (ctrl : Wire n) → (r : QRegister q n) →
    (∀ i : Fin q, ctrl ≠ r i) → Circuit n
  | 0, _, _, _ => Circuit.identity
  | q + 1, ctrl, r, hne =>
      Circuit.CNOT ctrl (r 0) (hne 0) ;;ᶜ
        cnotAllCircuit ctrl (r.slice 1 q (by omega))
          (fun j ↦ by
            rw [QRegister.slice_apply]
            exact hne _)
@[local simp] theorem count_cnotAllCircuit_toff {q n : ℕ} (ctrl : Wire n) (r : QRegister q n)
    (hne : ∀ i : Fin q, ctrl ≠ r i) : (cnotAllCircuit ctrl r hne).count .TOFF = 0 := by
  induction q <;> simp_all [cnotAllCircuit]
@[local simp] theorem count_cnotAllCircuit_t {q n : ℕ} (ctrl : Wire n) (r : QRegister q n)
    (hne : ∀ i : Fin q, ctrl ≠ r i) : (cnotAllCircuit ctrl r hne).count .T = 0 := by
  induction q <;> simp_all [cnotAllCircuit]
theorem support_cnotAllCircuit_sub {q n : ℕ} (ctrl : Wire n) (r : QRegister q n)
    (hne : ∀ i : Fin q, ctrl ≠ r i) :
    (cnotAllCircuit ctrl r hne).support ⊆ insert ctrl r.image := by
  induction q with
  | zero => simp [cnotAllCircuit]
  | succ q ih =>
      simp only [cnotAllCircuit, Circuit.support_seq, Finset.union_subset_iff]
      exact ⟨support_CNOT_sub (Finset.mem_insert_self ctrl r.image)
          (Finset.mem_insert_of_mem ((QRegister.mem_image r _).mpr ⟨0, rfl⟩)),
        (ih (r.slice 1 q (by omega)) _).trans
          (Finset.insert_subset_insert ctrl (QRegister.image_compose_subset r _))⟩
theorem cnotAllCircuit_evolve {q n : ℕ} (ctrl : Wire n) (r : QRegister q n)
    (hne : ∀ i : Fin q, ctrl ≠ r i) (ξ : BitAssignment n) :
    (cnotAllCircuit ctrl r hne).eval.1.mulVec (basisKet ξ) =
      basisKet (if ξ ctrl = 1 then flipRegBits r ξ else ξ) := by
  induction q generalizing ξ with
  | zero =>
      have hid : flipRegBits r ξ = ξ := by
        funext w; simp [flipRegBits, show r.image = ∅ by ext; simp [QRegister.mem_image]]
      rw [hid, ite_self]
      exact Matrix.one_mulVec (basisKet ξ)
  | succ q ih =>
      let r_tail := r.slice 1 q (by omega)
      have h0_not_tail : r 0 ∉ r_tail.image := QRegExt.head_not_mem_tail_image r
      have hmem_iff (w : Wire n) : w ∈ r.image ↔ w = r 0 ∨ w ∈ r_tail.image := by
        simp only [QRegister.mem_image]
        refine ⟨?_, fun h ↦ h.elim (fun e ↦ ⟨0, e.symm⟩) fun ⟨j, hj⟩ ↦ ⟨_, hj⟩⟩
        rintro ⟨i, rfl⟩; refine Fin.cases (Or.inl rfl) (fun j ↦ Or.inr ⟨j, ?_⟩) i
        dsimp only [r_tail]; rw [QRegister.slice_apply]; congr 1; ext; dsimp; omega
      have hp1 := (phasePerm_CNOT ctrl (r 0) (hne 0)).evolve ξ; rw [one_smul] at hp1
      let ξ₁ := Function.update ξ (r 0) (ξ (r 0) + ξ ctrl)
      have hctrl1 : ξ₁ ctrl = ξ ctrl := Function.update_of_ne (f := ξ) (hne 0) _
      simp only [cnotAllCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hp1, ih r_tail _ ξ₁, hctrl1]
      rcases zmod2_eq_zero_or_one (ξ ctrl) with hc0 | hc1
      · simp [hc0, show (0 : ZMod 2) ≠ 1 by decide, show ξ₁ = ξ from funext fun w ↦ by
          by_cases hw : w = r 0 <;> simp [ξ₁, hw, hc0]]
      · simp only [hc1, ↓reduceIte]
        refine congrArg basisKet (funext fun w ↦ ?_)
        by_cases hw0 : w = r 0
        · subst hw0
          simp [ξ₁, flipRegBits, hc1, h0_not_tail, (QRegister.mem_image r _).mpr ⟨0, rfl⟩]
        · by_cases hwt : w ∈ r_tail.image <;>
            simp [ξ₁, flipRegBits, hc1, hw0, hwt, hmem_iff]
theorem cnotAllCircuit_inverse_evolve {q n : ℕ} (ctrl : Wire n) (r : QRegister q n)
    (hne : ∀ i : Fin q, ctrl ≠ r i) (ξ : BitAssignment n) :
    (cnotAllCircuit ctrl r hne).inverse.eval.1.mulVec (basisKet ξ) =
      basisKet (if ξ ctrl = 1 then flipRegBits r ξ else ξ) := by
  have hnot : ctrl ∉ r.image := fun hm ↦
    let ⟨i, hi⟩ := (QRegister.mem_image r ctrl).mp hm; hne i hi.symm
  let η : BitAssignment n := if ξ ctrl = 1 then flipRegBits r ξ else ξ
  have hη_inv : (if η ctrl = 1 then flipRegBits r η else η) = ξ := by
    have hη_ctrl : η ctrl = ξ ctrl := by
      dsimp only [η]; split_ifs <;> simp [flipRegBits_outside r ξ hnot]
    rw [hη_ctrl]; dsimp only [η]; by_cases hc : ξ ctrl = 1 <;> simp [hc, flipRegBits_self_inv]
  have hf := cnotAllCircuit_evolve ctrl r hne η; rw [hη_inv] at hf
  exact circuit_inverse_evolve_of_evolve hf
theorem DiagOn.conj_cnotAllCircuit {q n : ℕ} {S : Finset (Wire n)} (ctrl : Wire n)
    (r : QRegister q n) (hne : ∀ i : Fin q, ctrl ≠ r i) (hDisj : Disjoint r.image S)
    {U : Unitary (2 ^ n)} (hU : DiagOn S U.1) : DiagOn S (((cnotAllCircuit ctrl r
    hne).inverse.eval * U * (cnotAllCircuit ctrl r hne).eval).1) := by
  have hDiagOf {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
      (he : ∀ ξ, M.mulVec (basisKet ξ) = basisKet (if ξ ctrl = 1 then flipRegBits r ξ else ξ)) :
      DiagOn S M := DiagOn.of_mulVec_basisKet fun β i hi u hu ↦ by
    rw [he, basisKet_eq_single] at hi
    by_cases hEq : i = (basisBitsEquiv n).symm (if β ctrl = 1 then flipRegBits r β else β)
    · subst hEq; change (basisBitsEquiv n) ((basisBitsEquiv n).symm _) u = β u
      rw [(basisBitsEquiv n).apply_symm_apply]
      have hnot : u ∉ r.image := fun hm ↦ Finset.disjoint_left.mp hDisj hm hu
      by_cases hc : β ctrl = 1 <;> simp [hc, flipRegBits_outside r β hnot]
    · rw [Pi.single_eq_of_ne hEq] at hi; exact absurd rfl hi
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  exact ((hDiagOf (cnotAllCircuit_inverse_evolve ctrl r hne)).mul hU).mul
    (hDiagOf (cnotAllCircuit_evolve ctrl r hne))
noncomputable def shiftCatKet {B n : ℕ} (rCat : QRegister B n) (ξ : BitAssignment n) (d : ℕ) :
    BitAssignment n := fun w ↦ if hw : ∃ j : Fin B, rCat j = w then basisBits B
    ⟨(regVal rCat ξ + d) % 2 ^ B, Nat.mod_lt _ (Nat.two_pow_pos B)⟩ hw.choose else ξ w
theorem shiftCatKet_outside {B n : ℕ} (rCat : QRegister B n) (ξ : BitAssignment n) (d : ℕ)
    {w : Wire n} (hw : w ∉ rCat.image) : shiftCatKet rCat ξ d w = ξ w := by
  unfold shiftCatKet
  exact NuclearTwistRealizes.dite_neg_eq fun ⟨j, hj⟩ ↦ hw ((QRegister.mem_image rCat w).mpr ⟨j, hj⟩)
theorem shiftCatKet_apply_reg {B n : ℕ} (rCat : QRegister B n) (ξ : BitAssignment n) (d : ℕ)
    (j : Fin B) : shiftCatKet rCat ξ d (rCat j) = basisBits B
    ⟨(regVal rCat ξ + d) % 2 ^ B, Nat.mod_lt _ (Nat.two_pow_pos B)⟩ j := by
  have hex : ∃ i : Fin B, rCat i = rCat j := ⟨j, rfl⟩
  unfold shiftCatKet
  rw [NuclearTwistRealizes.dite_pos_eq hex, rCat.wires.injective hex.choose_spec]
theorem regVal_shiftCatKet {B n : ℕ} (rCat : QRegister B n) (ξ : BitAssignment n) (d : ℕ) :
    regVal rCat (shiftCatKet rCat ξ d) = (regVal rCat ξ + d) % 2 ^ B := by
  let m : Fin (2 ^ B) := ⟨(regVal rCat ξ + d) % 2 ^ B, Nat.mod_lt _ (Nat.two_pow_pos B)⟩
  change bitsVal (fun j ↦ shiftCatKet rCat ξ d (rCat j)) = m.val
  rw [funext (shiftCatKet_apply_reg rCat ξ d), bitsVal_eq_symm_val]
  change ((basisBitsEquiv B).symm ((basisBitsEquiv B) m)).val = m.val
  rw [(basisBitsEquiv B).symm_apply_apply]
theorem eq_shiftCatKet_of_outside_and_regVal {B n : ℕ} (rCat : QRegister B n)
    (α ξ : BitAssignment n) (d : ℕ) (hout : ∀ w, w ∉ rCat.image → α w = ξ w)
    (hval : regVal rCat α = (regVal rCat ξ + d) % 2 ^ B) : α = shiftCatKet rCat ξ d := by
  funext w
  by_cases hw : ∃ j : Fin B, rCat j = w
  · rcases hw with ⟨j, rfl⟩
    rw [shiftCatKet_apply_reg, show (⟨(regVal rCat ξ + d) % 2 ^ B,
        Nat.mod_lt _ (Nat.two_pow_pos B)⟩ : Fin (2 ^ B)) =
      (basisBitsEquiv B).symm (fun t ↦ α (rCat t)) from Fin.ext (by
        change (regVal rCat ξ + d) % 2 ^ B = ((basisBitsEquiv B).symm (fun t ↦ α (rCat t))).val
        rw [← hval, regVal, bitsVal_eq_symm_val])]
    change α (rCat j) = (basisBitsEquiv B) ((basisBitsEquiv B).symm (fun t ↦ α (rCat t))) j
    rw [(basisBitsEquiv B).apply_symm_apply]
  · have hn : w ∉ rCat.image := fun hm ↦ hw ((QRegister.mem_image rCat w).mp hm)
    rw [hout w hn, shiftCatKet_outside rCat ξ d hn]
theorem shiftCatKet_shiftCatKet {B n : ℕ} (rCat : QRegister B n) (ξ : BitAssignment n)
    (d₁ d₂ : ℕ) : shiftCatKet rCat (shiftCatKet rCat ξ d₁) d₂ = shiftCatKet rCat ξ (d₁ + d₂) :=
  eq_shiftCatKet_of_outside_and_regVal rCat _ ξ (d₁ + d₂)
    (fun _ hw ↦ (shiftCatKet_outside rCat _ d₂ hw).trans (shiftCatKet_outside rCat ξ d₁ hw))
    (by rw [regVal_shiftCatKet, regVal_shiftCatKet, Nat.mod_add_mod, add_assoc])
def PurePermOutside {B n : ℕ} (rCat : QRegister B n)
    (c : Circuit n) (f : BitAssignment n → BitAssignment n) : Prop :=
  (∀ ξ : BitAssignment n, c.eval.1.mulVec (basisKet ξ) = basisKet (f ξ)) ∧
  (∀ (ξ : BitAssignment n) (δ : ℕ), f (shiftCatKet rCat ξ δ) = shiftCatKet rCat (f ξ) δ)
theorem update_comm_shiftCatKet {B n : ℕ} (rCat : QRegister B n) (ξ : BitAssignment n) (δ : ℕ)
    (t : Wire n) (ht : t ∉ rCat.image) (v₁ v₂ : ZMod 2) (hv : v₁ = v₂) : Function.update
    (shiftCatKet rCat ξ δ) t v₁ = shiftCatKet rCat (Function.update ξ t v₂) δ := by
  subst hv
  refine eq_shiftCatKet_of_outside_and_regVal rCat _ (Function.update ξ t v₁) δ (fun w hw ↦ ?_) ?_
  · by_cases hwt : w = t
    · subst hwt; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hwt, Function.update_of_ne hwt, shiftCatKet_outside rCat ξ δ hw]
  · have hreg_upd (η : BitAssignment n) : regVal rCat (Function.update η t v₁) = regVal rCat η :=
      regVal_congr rCat fun j ↦ Function.update_of_ne
        (fun h : rCat j = t ↦ ht ((QRegister.mem_image rCat t).mpr ⟨j, h⟩)) _ _
    rw [hreg_upd, hreg_upd, regVal_shiftCatKet]
theorem PurePermOutside.seq {B n : ℕ} {rCat : QRegister B n}
    {c₁ c₂ : Circuit n} {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : PurePermOutside rCat c₁ f₁) (h₂ : PurePermOutside rCat c₂ f₂) :
    PurePermOutside rCat (c₁ ;;ᶜ c₂) (f₂ ∘ f₁) :=
  ⟨fun ξ ↦
    by rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁.1 ξ, h₂.1 (f₁ ξ)]; rfl,
   fun ξ δ ↦ by dsimp only [Function.comp_apply]; rw [h₁.2 ξ δ, h₂.2 (f₁ ξ) δ]⟩
theorem PurePermOutside.X {B n : ℕ} {rCat : QRegister B n} (a : Wire n) (ha : a ∉ rCat.image) :
    PurePermOutside rCat (Circuit.X a) (fun ξ ↦ Function.update ξ a (ξ a + 1)) :=
  ⟨fun ξ ↦ by simpa only [one_smul] using (phasePerm_X a).evolve ξ,
   fun ξ δ ↦ update_comm_shiftCatKet rCat ξ δ a ha _ _ (by rw [shiftCatKet_outside rCat ξ δ ha])⟩
theorem PurePermOutside.CNOT {B n : ℕ} {rCat : QRegister B n} (a b : Wire n) (hab : a ≠ b)
    (ha : a ∉ rCat.image) (hb : b ∉ rCat.image) : PurePermOutside rCat (Circuit.CNOT a b hab)
    (fun ξ ↦ Function.update ξ b (ξ b + ξ a)) :=
  ⟨fun ξ ↦ by simpa only [one_smul] using (phasePerm_CNOT a b hab).evolve ξ,
   fun ξ δ ↦ update_comm_shiftCatKet rCat ξ δ b hb _ _
     (by rw [shiftCatKet_outside rCat ξ δ hb, shiftCatKet_outside rCat ξ δ ha])⟩
theorem PurePermOutside.TOFF {B n : ℕ} {rCat : QRegister B n} (a b t : Wire n) (h₁ : a ≠ b)
    (h₂ : a ≠ t) (h₃ : b ≠ t) (ha : a ∉ rCat.image) (hb : b ∉ rCat.image)
    (ht : t ∉ rCat.image) : PurePermOutside rCat (Circuit.TOFF a b t h₁ h₂ h₃)
    (fun ξ ↦ Function.update ξ t (ξ t + ξ a * ξ b)) :=
  ⟨fun ξ ↦ by simpa only [one_smul] using (phasePerm_TOFF a b t h₁ h₂ h₃).evolve ξ,
   fun ξ δ ↦ update_comm_shiftCatKet rCat ξ δ t ht _ _
     (by rw [shiftCatKet_outside rCat ξ δ ht, shiftCatKet_outside rCat ξ δ ha,
       shiftCatKet_outside rCat ξ δ hb])⟩
end ConfigFusedVepCore288
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000
end FusedVepCore288
end
end ModFusedVepCore288

section ModWeighted3ASingleCatSpine
@[expose] public section
namespace SingleCatSpineAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
end SingleCatSpineAlt
namespace SingleCatSpine
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open CatalystPrep
open BiGqspSegmentSpine
open scoped Matrix Matrix.Norms.L2Operator BigOperators
theorem U_cat_B_normalized_col_zero_singleCat (B : ℕ) (k : Fin (2 ^ B)) :
    (U_cat_B_normalized B).1 k 0 = PhaseGradCatalystCore.phaseGradientState B k := by
  refine (U_cat_B_normalized_col_zero B k).trans
    (?_ : PhaseGradCatalystCore.phaseGradientState B k = _).symm
  unfold PhaseGradCatalystCore.phaseGradientState FullScaleBESector.phaseGradientState
  rw [← Complex.ofReal_inv, show (Real.sqrt ((2 : ℝ) ^ B))⁻¹ = (2 : ℝ) ^ (-(B : ℝ) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (2 : ℝ) B,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
      congr 1
      ring,
    Complex.ofReal_cpow (by norm_num)]
  rfl
abbrev rLowCatSlice (B B_tot : ℕ) (hB : B ≤ B_tot) : QRegister (B_tot - B) B_tot :=
  QRegister.block 0 (B_tot - B) (by omega)
abbrev rTopCatSlice (B B_tot : ℕ) (hB : B ≤ B_tot) : QRegister B B_tot :=
  QRegister.block (B_tot - B) B (by omega)
theorem rLowCatSlice_disjoint_rTopCatSlice (B B_tot : ℕ) (hB : B ≤ B_tot) :
    (rLowCatSlice B B_tot hB).DisjointWires (rTopCatSlice B B_tot hB) :=
  QRegister.block_disjoint_of_le 0 (B_tot - B) (B_tot - B) B (by omega) (by omega) (by omega)
theorem seqProd_congr_eq {M : Type*} [Monoid M] {n m : ℕ} (h : n = m) (g : Fin m → M) :
    seqProd (fun i : Fin n ↦ g ⟨i.val, by omega⟩) = seqProd g := by subst h; rfl
theorem seqProd_add_split {M : Type*} [Monoid M] (a : ℕ) :
    ∀ (b : ℕ) (f : Fin (a + b) → M),
      seqProd f = seqProd (fun j : Fin b ↦ f ⟨a + j.val, by omega⟩) *
        seqProd (fun i : Fin a ↦ f ⟨i.val, by omega⟩)
  | 0, f => by simp only [seqProd, one_mul]; exact (seqProd_congr_eq (Nat.add_zero a) f).symm
  | b + 1, f => by
      rw [seqProd_succ_last f, seqProd_succ_last (fun j : Fin (b + 1) ↦ f ⟨a + j.val, by omega⟩),
        mul_assoc]
      exact congrArg (_ * ·) (seqProd_add_split a b fun k : Fin (a + b) ↦ f k.castSucc)
noncomputable def uLowCatTailPrep (B K : ℕ) : Unitary (2 ^ K) := seqProd (fun j :
    Fin K ↦ (QRegister.singleton j.rev).embedUnitary (idealPhaseGradDiagBit (B + j.val)) *
    (Circuit.H j.rev).eval)
noncomputable def phaseGradTailPhase (B K : ℕ) : ℂ :=
  ∏ j : Fin K, phaseGradBitGlobalPhase (B + j.val)
noncomputable def uLowCatTailNorm (B K : ℕ) : Unitary (2 ^ K) :=
  ⟨star (phaseGradTailPhase B K) • (uLowCatTailPrep B K).1,
    smul_mem_unitaryGroup_of_norm_eq_one
      (by
        rw [norm_star, phaseGradTailPhase, norm_prod]
        exact Finset.prod_eq_one fun j _ ↦ norm_phaseGradBitGlobalPhase (B + j.val))
      (uLowCatTailPrep B K).2⟩
theorem U_cat_B_normalized_eq_topSlice_mul_lowTail (B B_tot : ℕ) (hB : B ≤ B_tot) :
    U_cat_B_normalized B_tot = (rTopCatSlice B B_tot hB).embedUnitary (U_cat_B_normalized B) *
    (rLowCatSlice B B_tot hB).embedUnitary (uLowCatTailNorm B (B_tot - B)) := by
  let rL := rLowCatSlice B B_tot hB
  let rT := rTopCatSlice B B_tot hB
  have hPrep : U_cat_B_prep B_tot = rL.embedUnitary (uLowCatTailPrep B (B_tot - B)) *
      rT.embedUnitary (U_cat_B_prep B) := Subtype.ext (by
    rw [Submonoid.coe_mul, show (rL.embedUnitary (uLowCatTailPrep B (B_tot - B))).1 =
        seqProd (fun j : Fin (B_tot - B) ↦ ((QRegister.singleton (rL j.rev)).embedUnitary
          (idealPhaseGradDiagBit (B + j.val)) * (Circuit.H (rL j.rev)).eval).1) by
      rw [uLowCatTailPrep, ← seqProd_embedUnitary, seqProd_coe_unitary]
      refine congrArg seqProd (funext fun j ↦ ?_)
      have hc : rL.compose (QRegister.singleton j.rev) = QRegister.singleton (rL j.rev) :=
        SingleCatSpineAlt.qreg_ext fun a ↦ Subsingleton.elim a 0 ▸ rfl
      simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← QRegister.embedUnitary_compose,
        hc, QRegister.embedUnitary_val, Circuit.eval_single],
      embed_U_cat_B_prep_eq_seqProd_gen rT, U_cat_B_prep, seqProd_coe_unitary]
    let g : Fin B_tot → Operator (2 ^ B_tot) := fun idx ↦ ((QRegister.singleton
        idx.rev).embedUnitary (idealPhaseGradDiagBit idx.val) * (Circuit.H idx.rev).eval).1
    change seqProd g = _
    rw [← seqProd_congr_eq (by omega : B + (B_tot - B) = B_tot) g,
      seqProd_add_split B (B_tot - B) (fun idx : Fin (B + (B_tot - B)) ↦ g ⟨idx.val, by omega⟩)]
    exact congrArg₂ (· * ·)
      (congrArg seqProd (funext fun j ↦ by
        dsimp only [g]
        rw [show (⟨B + j.val, by omega⟩ : Fin B_tot).rev = rL j.rev from Fin.ext (by
          simp only [rL, rLowCatSlice, SingleCatSpineAlt.qreg_block_apply,
            Fin.val_rev]
          omega)]))
      (congrArg seqProd (funext fun i ↦ by
        dsimp only [g]
        rw [show (⟨i.val, by omega⟩ : Fin B_tot).rev = rT i.rev from Fin.ext (by
          simp only [rT, rTopCatSlice, SingleCatSpineAlt.qreg_block_apply,
            Fin.val_rev]
          omega)])))
  have hPhase : phaseGradGlobalPhase B_tot =
      phaseGradGlobalPhase B * phaseGradTailPhase B (B_tot - B) := by
    have hPr {n m : ℕ} (h : n = m) (g : Fin m → ℂ) :
        (∏ i : Fin n, g ⟨i.val, by omega⟩) = ∏ j : Fin m, g j := by
      subst h
      rfl
    rw [phaseGradGlobalPhase, phaseGradGlobalPhase, phaseGradTailPhase,
      ← hPr (by omega : B + (B_tot - B) = B_tot)
        (fun idx : Fin B_tot ↦ phaseGradBitGlobalPhase idx.val), Fin.prod_univ_add]
    rfl
  apply Subtype.ext
  rw [Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    ← rL.embedMatrix_comm_of_disjoint rT (rLowCatSlice_disjoint_rTopCatSlice B B_tot hB)
      (uLowCatTailNorm B (B_tot - B)).1 (U_cat_B_normalized B).1]
  change (star (phaseGradGlobalPhase B_tot) • (U_cat_B_prep B_tot).1) = _
  rw [hPrep, hPhase, Submonoid.coe_mul]
  change (star (phaseGradGlobalPhase B * phaseGradTailPhase B (B_tot - B))) • ((rL.embedUnitary
    (uLowCatTailPrep B (B_tot - B))).1 * (rT.embedUnitary (U_cat_B_prep B)).1) =
    (rL.embedMatrix (star (phaseGradTailPhase B (B_tot - B)) • (uLowCatTailPrep B (B_tot - B)).1)) *
    (rT.embedMatrix (star (phaseGradGlobalPhase B) • (U_cat_B_prep B).1))
  rw [QRegister.embedMatrix_smul, QRegister.embedMatrix_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_mul]
  rfl
theorem intertwinesCat_topCatSlice_of_embed {n m_sub B B_tot : ℕ} (hB : B ≤ B_tot)
    (rSub : QRegister m_sub n) (rCatTot : QRegister B_tot n)
    (hDisj : rSub.DisjointWires rCatTot)
    (M_cat : Operator (2 ^ (m_sub + B)))
    (M_eff : Operator (2 ^ m_sub))
    (hSub :
      let rSubTop := rSub.concat (rCatTot.compose (rTopCatSlice B B_tot hB))
        (hDisj.compose_right _)
      IntertwinesCat
        ((rCatTot.compose (rTopCatSlice B B_tot hB)).embedUnitary (U_cat_B_normalized B)).1
        ((rCatTot.compose (rTopCatSlice B B_tot hB)).basisOutcomeProjector 0)
        (rSubTop.embedMatrix M_cat)
        (rSub.embedMatrix M_eff)) :
    IntertwinesCat
      (rCatTot.embedUnitary (U_cat_B_normalized B_tot)).1
      (rCatTot.basisOutcomeProjector 0)
      ((rSub.concat (rCatTot.compose (rTopCatSlice B B_tot hB))
        (hDisj.compose_right _)).embedMatrix M_cat)
      (rSub.embedMatrix M_eff) := by
  let rTop := rCatTot.compose (rTopCatSlice B B_tot hB)
  let rLow := rCatTot.compose (rLowCatSlice B B_tot hB)
  have hSubLow : rSub.DisjointWires rLow := hDisj.compose_right _
  have hTopLow : rTop.DisjointWires rLow := QRegister.disjoint_iff.mpr fun i j h ↦
    (rLowCatSlice_disjoint_rTopCatSlice B B_tot hB).ne j i (rCatTot.wires.injective h.symm)
  set U_top := (rTop.embedUnitary (U_cat_B_normalized B)).1
  set U_low := (rLow.embedUnitary (uLowCatTailNorm B (B_tot - B))).1
  set P_top0 := rTop.basisOutcomeProjector 0
  set P_low0 := rLow.basisOutcomeProjector 0
  have hEffLowU : (rSub.embedMatrix M_eff) * U_low = U_low * (rSub.embedMatrix M_eff) :=
    rSub.embedMatrix_comm_of_disjoint rLow hSubLow M_eff _
  have hEffLowP : (rSub.embedMatrix M_eff) * P_low0 = P_low0 * (rSub.embedMatrix M_eff) :=
    rSub.embedMatrix_comm_of_disjoint rLow hSubLow M_eff (compProj 0)
  have hPtop_Ulow : P_top0 * U_low = U_low * P_top0 :=
    rTop.embedMatrix_comm_of_disjoint rLow hTopLow (compProj 0) _
  have hProj : rCatTot.basisOutcomeProjector 0 = P_top0 * P_low0 := by
    have hIff (g : Fin (2 ^ n)) : rCatTot.extractIndex g = 0 ↔
        rTop.extractIndex g = 0 ∧ rLow.extractIndex g = 0 := by
      simp only [zero_extract_iff_bits_zero]
      refine ⟨fun h ↦ ⟨fun i ↦ h (rTopCatSlice B B_tot hB i),
          fun j ↦ h (rLowCatSlice B B_tot hB j)⟩, fun ⟨hT, hL⟩ idx ↦ ?_⟩
      by_cases hlt : idx.val < B_tot - B
      · rw [show idx = rLowCatSlice B B_tot hB ⟨idx.val, hlt⟩ from Fin.ext (by
          simp [rLowCatSlice])]
        exact hL _
      · rw [show idx = rTopCatSlice B B_tot hB ⟨idx.val - (B_tot - B), by omega⟩ from Fin.ext (by
          simp [rTopCatSlice]
          omega)]
        exact hT _
    dsimp only [P_top0, P_low0]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    by_cases hT : rTop.extractIndex g = 0 <;> by_cases hL : rLow.extractIndex g = 0 <;>
      simp [hIff g, hT, hL]
  rw [show (rCatTot.embedUnitary (U_cat_B_normalized B_tot)).1 = U_top * U_low by
      rw [U_cat_B_normalized_eq_topSlice_mul_lowTail B B_tot hB, QRegister.embedUnitary_mul,
        Submonoid.coe_mul, ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose],
    hProj]
  refine ⟨?_, ?_, ?_⟩
  · calc _ * (U_top * U_low) * (P_top0 * P_low0)
      _ = (_ * U_top * P_top0) * U_low * P_low0 := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc U_low P_top0, ← hPtop_Ulow, Matrix.mul_assoc]
      _ = U_top * U_low * (rSub.embedMatrix M_eff) * (P_top0 * P_low0) := by
            rw [hSub.1]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P_top0 U_low, hPtop_Ulow, Matrix.mul_assoc,
              ← Matrix.mul_assoc (rSub.embedMatrix M_eff) U_low, hEffLowU, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, hSub.2.1, Matrix.mul_assoc, hEffLowU, ← Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, hSub.2.2, Matrix.mul_assoc, hEffLowP, ← Matrix.mul_assoc]
end SingleCatSpine
set_option maxRecDepth 4096
end
end ModWeighted3ASingleCatSpine

end QuantumComputation.Specs.StoppingPowerSolution
