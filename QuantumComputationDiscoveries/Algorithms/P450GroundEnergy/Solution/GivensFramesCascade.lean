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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalyticMuxFrames

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open CircuitModular GivensOps
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 4B-1: Generalized Givens Frames, Sub-Slice Lifting, `inPlaceUVStep`, Cascade &
Spin-Swap -/

section Phase4B1

theorem givensPlaneUnitary_zero : GivensOps.givensPlaneUnitary 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GivensOps.givensPlaneMatrix]

/-- Generalized two-qubit positive Givens frame
`cliffPostPos * diag(genKick4 α₀ α₁) * cliffPrePos`. -/
noncomputable def genGivensPosUnitary (α₀ α₁ : ℝ) : Unitary (2 ^ 2) :=
  cliffPostPos.eval * phaseDiagUnitary (genKick4 α₀ α₁) (genKick4_unit α₀ α₁) * cliffPrePos.eval

/-- Generalized two-qubit negative Givens frame
`cliffPostNeg * diag(genKick4 α₀ α₁) * cliffPreNeg`. -/
noncomputable def genGivensNegUnitary (α₀ α₁ : ℝ) : Unitary (2 ^ 2) :=
  cliffPostNeg.eval * phaseDiagUnitary (genKick4 α₀ α₁) (genKick4_unit α₀ α₁) * cliffPreNeg.eval

theorem genGivensPosUnitary_zero_left (α : ℝ) :
    genGivensPosUnitary 0 α = GivensOps.givensPlaneUnitary α :=
  cliffFramePos_eq α

theorem genGivensPosUnitary_zero_zero : genGivensPosUnitary 0 0 = 1 := by
  rw [genGivensPosUnitary_zero_left, givensPlaneUnitary_zero]

private noncomputable def x0Mat4 : Operator (2 ^ 2) :=
  !![(0 : ℂ), 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

private theorem eval_ket2_entry (c : Circuit 2) (i j : Fin (2 ^ 2)) :
    c.eval.1 i j = c.eval.1.mulVec (ket (basisBits 2 j)) i := by
  rw [← single_eq_ket, Matrix.mulVec_single_one]
  rfl

private theorem ket2_val (β : BitAssignment 2) (i : Fin (2 ^ 2)) :
    ket β i = if basisBits 2 i 0 = β 0 ∧ basisBits 2 i 1 = β 1 then 1 else 0 := by
  unfold ket basisState
  by_cases h : i = (basisBits 2).symm β
  · subst h
    have hb0 : basisBits 2 ((basisBits 2).symm β) 0 = β 0 :=
      congrFun (basisBits_symm_eq β) 0
    have hb1 : basisBits 2 ((basisBits 2).symm β) 1 = β 1 :=
      congrFun (basisBits_symm_eq β) 1
    simp only [Pi.single_eq_same, hb0, hb1, and_self, ↓reduceIte]
  · rw [Pi.single_eq_of_ne h]
    have hnot : ¬(basisBits 2 i 0 = β 0 ∧ basisBits 2 i 1 = β 1) := by
      rintro ⟨h0, h1⟩
      apply h
      apply (basisBits 2).injective
      rw [basisBits_symm_eq]
      funext w; fin_cases w
      · exact h0
      · exact h1
    simp only [hnot, ↓reduceIte]

private theorem basisBits2_apply' (x : Fin (2 ^ 2)) :
    basisBits 2 x = fun (w : Wire 2) => ((x.val / 2 ^ w.val % 2 : ℕ) : ZMod 2) :=
  funext (basisBits_eq_div_mod 2 x)

private theorem zmod2_val_2' : (2 : ZMod 2).val = 0 := rfl
private theorem zmod2_val_3' : (3 : ZMod 2).val = 1 := rfl

private theorem cliffPreNeg_mul_cliffPostPos :
    (cliffPreNeg.eval.1 * cliffPostPos.eval.1 : Operator (2 ^ 2)) = x0Mat4 := by
  have hseq : cliffPreNeg.eval.1 * cliffPostPos.eval.1 = (cliffPostPos ;;ᶜ cliffPreNeg).eval.1 :=
    rfl
  rw [hseq]
  have hs2 := sqrtHalfC_sq
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  rw [eval_ket2_entry _ i j]
  dsimp only [cliffPostPos, cliffPreNeg]
  simp only [eval_seq_mulVec, evolve_H_ket, Matrix.mulVec_add, Matrix.mulVec_smul,
    evolve_sdagCircuit_ket, evolve_CNOT_ket, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ket2_val,
    basisBits2_apply']
  fin_cases j <;> fin_cases i <;>
    simp only [Nat.zero_div, Nat.zero_mod, Nat.cast_zero, Fin.isValue, Function.update_self,
      ZMod.val_zero, pow_zero, Function.update_eq_self, ne_eq, one_ne_zero, not_false_eq_true,
      Function.update_of_ne, add_zero, zero_ne_one, Fin.coe_ofNat_eq_mod, Nat.div_one,
      Nat.mod_succ, pow_one, and_self, ↓reduceIte, and_true, mul_zero, mul_one, one_mul,
      zmod2_val_one, zero_add, zmod2_add_self, Function.update_idem, neg_mul, mul_neg, neg_neg,
      x0Mat4, Nat.reducePow, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_fin_one, Order.lt_one_iff, Nat.div_self, Nat.cast_one, Nat.reduceDiv, Fin.mk_one,
      cons_val_one, Nat.mod_self, Order.lt_two_iff, zero_le, and_false, Fin.reduceFinMk,
      cons_val, Nat.reduceMod, ZMod.natCast_mod] <;>
    (ring_nf; try simp only [hs2, hI2]; ring)

private theorem cliffPostNeg_mul_x0_mul_cliffPrePos :
    (cliffPostNeg.eval.1 * x0Mat4 * cliffPrePos.eval.1 : Operator (2 ^ 2)) = 1 := by
  have hx0 : (Circuit.X (0 : Wire 2)).eval.1 = x0Mat4 := by
    ext i j
    rw [eval_ket2_entry _ i j]
    simp only [evolve_X_ket, ket2_val, basisBits2_apply']
    fin_cases j <;> fin_cases i <;>
      simp [x0Mat4]
  have hseq : cliffPostNeg.eval.1 * x0Mat4 * cliffPrePos.eval.1 =
      (cliffPrePos ;;ᶜ Circuit.X 0 ;;ᶜ cliffPostNeg).eval.1 := by
    rw [← hx0]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hseq]
  have hs2 := sqrtHalfC_sq
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  rw [eval_ket2_entry _ i j]
  dsimp only [cliffPrePos, cliffPostNeg]
  simp only [eval_seq_mulVec, evolve_CNOT_ket, evolve_S_ket, Matrix.mulVec_smul, evolve_H_ket,
    Matrix.mulVec_add, evolve_X_ket, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ket2_val,
    basisBits2_apply']
  fin_cases j <;> fin_cases i <;>
    simp only [Nat.zero_div, Nat.zero_mod, Nat.cast_zero, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, pow_one, pow_zero, Nat.div_one, add_zero, ne_eq, zero_ne_one,
      not_false_eq_true, Function.update_of_ne, ZMod.val_zero, Function.update_eq_self,
      Function.update_self, zero_add, Function.update_idem, one_ne_zero, and_self, ↓reduceIte,
      mul_one, zmod2_val_one, mul_zero, zmod2_add_self, one_mul, one_apply_eq, Order.lt_one_iff,
      Nat.div_self, Nat.cast_one, Nat.reduceDiv, and_true, and_false, Nat.reducePow,
      Fin.mk_one, Fin.zero_eta, one_apply_ne, Nat.mod_self, Order.lt_two_iff, zero_le,
      Fin.reduceFinMk, Fin.reduceEq, Nat.reduceMod, neg_mul, mul_neg, neg_add_cancel,
      ZMod.natCast_mod, add_neg_cancel, Nat.cast_ofNat, zmod2_val_2', zmod2_val_3'] <;>
    (ring_nf; try simp only [hs2, hI2]; ring)

/-- Exact inverse property for ALL `(α₀, α₁ : ℝ)` (including multi-hot states where `α₀ ≠ 0`):
`genGivensNegUnitary α₀ α₁ = (genGivensPosUnitary α₀ α₁)⁻¹`. -/
theorem genGivensNegUnitary_eq_inv (α₀ α₁ : ℝ) :
    genGivensNegUnitary α₀ α₁ = (genGivensPosUnitary α₀ α₁)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  let D := Matrix.diagonal (genKick4 α₀ α₁)
  have hDXD : D * x0Mat4 * D = x0Mat4 := by
    have hexp0 (θ : ℝ) :
        Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    have hexp1 (θ : ℝ) :
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    ext i j
    have hsum : ∀ f : Fin (2 ^ 2) → ℂ, (∑ x, f x) = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four
    simp only [D, Matrix.mul_apply, hsum, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [x0Mat4, genKick4, hexp0, hexp1]
  change (cliffPostNeg.eval.1 * D * cliffPreNeg.eval.1) *
      (cliffPostPos.eval.1 * D * cliffPrePos.eval.1) = 1
  calc
    (cliffPostNeg.eval.1 * D * cliffPreNeg.eval.1) *
        (cliffPostPos.eval.1 * D * cliffPrePos.eval.1)
        = cliffPostNeg.eval.1 * (D * (cliffPreNeg.eval.1 * cliffPostPos.eval.1) * D) *
            cliffPrePos.eval.1 := by simp only [Matrix.mul_assoc]
    _ = cliffPostNeg.eval.1 * (D * x0Mat4 * D) * cliffPrePos.eval.1 := by
          rw [cliffPreNeg_mul_cliffPostPos]
    _ = cliffPostNeg.eval.1 * x0Mat4 * cliffPrePos.eval.1 := by rw [hDXD]
    _ = 1 := cliffPostNeg_mul_x0_mul_cliffPrePos

/-- Sub-slice factorization of `phaseGradientFineLow (b_skip + B) b_high` into
`phaseGradientFineLow b_skip (B + b_high)` on `locLeft b_skip B` and `phaseGradientFineLow B b_high`
on `locRight b_skip B`. -/
theorem phaseGradientFineLow_eq_prodState_top (b_skip B b_high : ℕ) :
    phaseGradientFineLow (b_skip + B) b_high =
      prodState (phaseGradientFineLow b_skip (B + b_high)) (phaseGradientFineLow B b_high) := by
  funext g
  simp only [prodState, prodStateOf, phaseGradientFineLow]
  have hsqrt :
      (Real.sqrt (2 ^ (b_skip + B)) : ℂ)⁻¹ =
        (Real.sqrt (2 ^ b_skip) : ℂ)⁻¹ * (Real.sqrt (2 ^ B) : ℂ)⁻¹ := by
    have hr : Real.sqrt ((2 : ℝ) ^ (b_skip + B)) =
        Real.sqrt ((2 : ℝ) ^ b_skip) * Real.sqrt ((2 : ℝ) ^ B) := by
      rw [pow_add, Real.sqrt_mul (by positivity)]
    have hr' : Real.sqrt (2 ^ (b_skip + B)) = Real.sqrt (2 ^ b_skip) * Real.sqrt (2 ^ B) := by
      simpa using hr
    rw [hr', Complex.ofReal_mul, _root_.mul_inv_rev, mul_comm]
  have hexp :
      Complex.exp (-(2 * Real.pi * Complex.I * g.val) / 2 ^ ((b_skip + B) + b_high)) =
        Complex.exp (-(2 * Real.pi * Complex.I * ((locLeft b_skip B).extractIndex g).val) /
            2 ^ (b_skip + (B + b_high))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((locRight b_skip B).extractIndex g).val) /
            2 ^ (B + b_high)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [val_eq_locLeft_add_mul_locRight b_skip B g]
    have hassoc : (b_skip + B) + b_high = b_skip + (B + b_high) := by omega
    rw [hassoc]
    have hpow : (2 : ℂ) ^ (b_skip + (B + b_high)) =
        (2 : ℂ) ^ b_skip * (2 : ℂ) ^ (B + b_high) := pow_add 2 _ _
    have hneL : (2 : ℂ) ^ b_skip ≠ 0 := pow_ne_zero _ two_ne_zero
    have hneH : (2 : ℂ) ^ (B + b_high) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [hpow]
    push_cast
    field_simp [hneL, hneH]
    ring
  rw [hsqrt, hexp]
  ring

/-- Action of a control-multiplexed unitary `muxCtrlUnitary G` embedded on `rTgt.concat rCtrl`
applied to any computational basis ket `ket β`. -/
theorem embedUnitary_muxCtrlUnitary_mulVec_ket
    {n k_tgt k_ctrl : ℕ} (rTgt : QRegister k_tgt n) (rCtrl : QRegister k_ctrl n)
    (htc : rTgt.DisjointWires rCtrl)
    (G : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_tgt)) (β : BitAssignment n) :
    ((rTgt.concat rCtrl htc).embedUnitary (muxCtrlUnitary G)).1.mulVec (ket β) =
      (rTgt.embedUnitary (G (localIdx rCtrl β))).1.mulVec (ket β) := by
  let rAct := rTgt.concat rCtrl htc
  let e := blockSplitEquiv k_tgt k_ctrl
  let t := localIdx rTgt β
  let c := localIdx rCtrl β
  let x := localIdx rAct β
  have hx : blockSplitEquiv k_tgt k_ctrl x = (t, c) := by
    ext1
    · apply (basisBits k_tgt).injective; funext i
      change basisBits k_tgt ((locLeft k_tgt k_ctrl).extractIndex x) i = basisBits k_tgt t i
      rw [(locLeft k_tgt k_ctrl).basisBits_extractIndex, basisBits_symm_eq, basisBits_symm_eq]
      have hi : rAct (locLeft k_tgt k_ctrl i) = rTgt i := by
        have hc : locLeft k_tgt k_ctrl i = Fin.castAdd k_ctrl i := by
          ext; simp [locLeft, locLeftOf]
        simp [rAct, hc]
      rw [hi]
    · apply (basisBits k_ctrl).injective; funext j
      change basisBits k_ctrl ((locRight k_tgt k_ctrl).extractIndex x) j = basisBits k_ctrl c j
      rw [(locRight k_tgt k_ctrl).basisBits_extractIndex, basisBits_symm_eq, basisBits_symm_eq]
      have hj : rAct (locRight k_tgt k_ctrl j) = rCtrl j := by
        have hn : locRight k_tgt k_ctrl j = Fin.natAdd k_tgt j := by
          ext; simp [locRight, locRightOf]
        simp [rAct, hn]
      rw [hj]
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, embedMatrix_mulVec_ket,
    embedMatrix_mulVec_ket]
  rw [← e.symm.sum_comp (fun l =>
    (muxCtrlUnitary G).1 l x • ket (writeReg β rAct (basisBits (k_tgt + k_ctrl) l))),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single c]
  · have he_pc : blockSplitEquiv k_tgt k_ctrl (e.symm (p, c)) = (p, c) :=
      e.apply_symm_apply (p, c)
    have hmat : (muxCtrlUnitary G).1 (e.symm (p, c)) x = (G c).1 p t := by
      simp only [muxCtrlUnitary_val, muxCtrlMatrix, he_pc, hx, ↓reduceIte]
    have hwr : writeReg β rAct (basisBits (k_tgt + k_ctrl) (e.symm (p, c))) =
        writeReg β rTgt (basisBits k_tgt p) := by
      let l₀ := e.symm (p, c)
      have hl₀_L : (locLeft k_tgt k_ctrl).extractIndex l₀ = p := congrArg Prod.fst he_pc
      have hl₀_R : (locRight k_tgt k_ctrl).extractIndex l₀ = c := congrArg Prod.snd he_pc
      funext w
      by_cases hw : w ∈ Set.range rAct.wires
      · obtain ⟨idx, rfl⟩ := hw
        rw [writeReg_apply_reg]
        refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
        · have hli : Fin.castAdd k_ctrl i = locLeft k_tgt k_ctrl i := by
            ext; simp [locLeft, locLeftOf]
          have hr_eq : rAct (Fin.castAdd k_ctrl i) = rTgt i := by simp [rAct]
          rw [hr_eq, writeReg_apply_reg, hli, ← (locLeft k_tgt k_ctrl).basisBits_extractIndex,
            hl₀_L]
        · have hrj : Fin.natAdd k_tgt j = locRight k_tgt k_ctrl j := by
            ext; simp [locRight, locRightOf]
          have hr_eq : rAct (Fin.natAdd k_tgt j) = rCtrl j := by simp [rAct]
          have hnot_tgt : rCtrl j ∉ Set.range rTgt.wires := by
            rintro ⟨i, hi⟩
            exact QRegister.disjoint_iff.mp htc i j hi
          rw [hr_eq, writeReg_apply_of_not_mem _ _ _ _ hnot_tgt, hrj,
            ← (locRight k_tgt k_ctrl).basisBits_extractIndex, hl₀_R]
          exact congrFun (basisBits_symm_eq (fun j' => β (rCtrl j'))) j
      · have hnot_tgt : w ∉ Set.range rTgt.wires := by
          rintro ⟨i, rfl⟩
          exact hw ⟨Fin.castAdd k_ctrl i, by simp [rAct]⟩
        rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hnot_tgt]
    rw [hmat, hwr]
  · intro c' _ hc'
    have he_pc' : blockSplitEquiv k_tgt k_ctrl (e.symm (p, c')) = (p, c') :=
      e.apply_symm_apply (p, c')
    have hzero : (muxCtrlUnitary G).1 (e.symm (p, c')) x = 0 := by
      simp only [muxCtrlUnitary_val, muxCtrlMatrix, he_pc', hx]
      exact ite_eq_right_of_eq_false _ _ (eq_false hc')
    rw [hzero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- In-place `(u, v)` Rank-2 Bilinear pair-bit splitter (`4 T`, `0 TOFF`, `1` clean ancilla `w_v`):
given `(w_ctrl, sub)` and clean `w_v = 0`, sets `w_v := w_ctrl * sub` and
`w_ctrl := w_ctrl * (1 + sub)`
(so `u := w_ctrl` and `v := w_v` satisfy `u * v = 0`, selecting `0` when `w_ctrl = 0`, `(1, 0)` when
`w_ctrl = 1, sub = 0`, and `(0, 1)` when `w_ctrl = 1, sub = 1`), and cleanly restores both on exit!
-/
def inPlaceUVStep {n : ℕ} (w_ctrl sub w_v : Wire n)
    (hcs : w_ctrl ≠ sub) (hcv : w_ctrl ≠ w_v) (hsv : sub ≠ w_v) : PhasedStep n where
  c₁ := w_ctrl
  c₂ := sub
  anc := w_v
  h₁₂ := hcs
  h₁a := hcv
  h₂a := hsv
  pre := .identity
  midPre := Circuit.CNOT w_v w_ctrl hcv.symm
  midPost := Circuit.CNOT w_v w_ctrl hcv.symm
  post := .identity

theorem isCliffordWrapper_inPlaceUVStep {n : ℕ} (w_ctrl sub w_v : Wire n)
    (hcs : w_ctrl ≠ sub) (hcv : w_ctrl ≠ w_v) (hsv : sub ≠ w_v) :
    (inPlaceUVStep w_ctrl sub w_v hcs hcv hsv).IsCliffordWrapper := by
  simp [inPlaceUVStep, PhasedStep.IsCliffordWrapper]

theorem inPlaceUVStep_wrap_spec {n : ℕ} (w_ctrl sub w_v : Wire n)
    (hcs : w_ctrl ≠ sub) (hcv : w_ctrl ≠ w_v) (hsv : sub ≠ w_v)
    {c_in : Circuit n} {φ_in : BitAssignment n → ℂ} {f_in : BitAssignment n → BitAssignment n}
    (hperm_in : PhasedPerm c_in φ_in f_in)
    (hfix_ctrl : ∀ β, f_in β w_ctrl = β w_ctrl)
    (hfix_sub : ∀ β, f_in β sub = β sub)
    (hfix_v : ∀ β, f_in β w_v = β w_v) :
    let s := inPlaceUVStep w_ctrl sub w_v hcs hcv hsv
    let β_in : BitAssignment n → BitAssignment n := fun β =>
      let v_new := β w_v + β w_ctrl * β sub
      Function.update (Function.update β w_v v_new) w_ctrl (β w_ctrl + v_new)
    let φ_out : BitAssignment n → ℂ := fun β => φ_in (β_in β)
    let f_out : BitAssignment n → BitAssignment n := fun β =>
      let γ := f_in (β_in β)
      let c_rest := γ w_ctrl + γ w_v
      Function.update (Function.update γ w_ctrl c_rest) w_v (γ w_v + c_rest * γ sub)
    PhasedPerm (s.wrapCircuit c_in) φ_out f_out ∧
    (∀ β, f_out β w_ctrl = β w_ctrl) ∧
    (∀ β, f_out β sub = β sub) ∧
    (∀ β, β w_v = 0 → f_out β w_v = 0) ∧
    (∀ β w, w ≠ w_ctrl → w ≠ w_v → f_out β w = f_in (β_in β) w) ∧
    (let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
     let T_anc := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1
     P₀ * (T_anc * (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost).eval.1 * T_anc * P₀) =
       T_anc * (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost).eval.1 * T_anc * P₀) := by
  intro s β_in φ_out f_out
  have hbody : ∃ φ_b f_b,
      PhasedPerm (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost) φ_b f_b ∧
      (∀ β, f_b β w_ctrl = β w_ctrl) ∧
      (∀ β, f_b β sub = β sub) ∧
      (∀ β, f_b β w_v = β w_v) := by
    let β_mp : BitAssignment n → BitAssignment n :=
      fun β => Function.update β w_ctrl (β w_ctrl + β w_v)
    let f_b : BitAssignment n → BitAssignment n :=
      fun β => Function.update (f_in (β_mp β)) w_ctrl (f_in (β_mp β) w_ctrl + f_in (β_mp β) w_v)
    refine ⟨fun β => φ_in (β_mp β), f_b, ?_, ?_, ?_, ?_⟩
    · intro β
      dsimp only [s, inPlaceUVStep]
      simp only [eval_seq_mulVec, evolve_CNOT_ket]
      change (Circuit.CNOT w_v w_ctrl hcv.symm).eval.1.mulVec (c_in.eval.1.mulVec (ket (β_mp β))) =
        _
      rw [hperm_in (β_mp β), Matrix.mulVec_smul, evolve_CNOT_ket]
    · intro β
      dsimp [f_b, β_mp]
      rw [Function.update_self, hfix_ctrl, hfix_v, Function.update_self,
        Function.update_of_ne hcv.symm, zmod2_add_cancel_right]
    · intro β
      dsimp [f_b, β_mp]
      rw [Function.update_of_ne hcs.symm, hfix_sub, Function.update_of_ne hcs.symm]
    · intro β
      dsimp [f_b, β_mp]
      rw [Function.update_of_ne hcv.symm, hfix_v, Function.update_of_ne hcv.symm]
  have hperm_out : PhasedPerm (s.wrapCircuit c_in) φ_out f_out := by
    intro β
    dsimp only [s, inPlaceUVStep, PhasedStep.wrapCircuit]
    simp only [eval_seq_mulVec, eval_identity_mulVec, evolve_TOFF_ket, evolve_CNOT_ket]
    have hβ_eq : Function.update
        (Function.update β w_v (β w_v + β w_ctrl * β sub))
        w_ctrl
        (Function.update β w_v (β w_v + β w_ctrl * β sub) w_ctrl +
          Function.update β w_v (β w_v + β w_ctrl * β sub) w_v) = β_in β := by
      dsimp [β_in]
      rw [Function.update_of_ne hcv, Function.update_self]
    rw [hβ_eq, hperm_in (β_in β), Matrix.mulVec_smul, evolve_CNOT_ket, Matrix.mulVec_smul,
      evolve_TOFF_ket]
    congr 1; apply congrArg ket
    dsimp [f_out]
    rw [Function.update_self, Function.update_of_ne hcv.symm, Function.update_of_ne hcs.symm]
  have hf_ctrl : ∀ β, f_out β w_ctrl = β w_ctrl := by
    intro β
    dsimp [f_out, β_in]
    rw [Function.update_of_ne hcv, Function.update_self, hfix_ctrl, hfix_v,
      Function.update_self, Function.update_of_ne hcv.symm, Function.update_self,
      zmod2_add_cancel_right]
  have hf_sub : ∀ β, f_out β sub = β sub := by
    intro β
    dsimp [f_out, β_in]
    rw [Function.update_of_ne hsv, Function.update_of_ne hcs.symm, hfix_sub,
      Function.update_of_ne hcs.symm, Function.update_of_ne hsv]
  have hf_v0 : ∀ β, β w_v = 0 → f_out β w_v = 0 := by
    intro β hv0
    dsimp [f_out, β_in]
    rw [Function.update_self, hfix_ctrl, hfix_v, hfix_sub, Function.update_self,
      Function.update_of_ne hcv.symm, Function.update_self,
      Function.update_of_ne hcs.symm, Function.update_of_ne hsv, hv0, zero_add,
      zmod2_add_cancel_right, zmod2_add_self]
  have hf_other : ∀ β w, w ≠ w_ctrl → w ≠ w_v → f_out β w = f_in (β_in β) w := by
    intro β w hwc hwv
    dsimp [f_out]
    rw [Function.update_of_ne hwv, Function.update_of_ne hwc]
  refine ⟨hperm_out, hf_ctrl, hf_sub, hf_v0, hf_other, ?_⟩
  obtain ⟨φ_b, f_b, hpb, hc1, hc2, hca⟩ := hbody
  exact toffoli_conj_preserves_zero_ancilla_of_phasedPerm w_ctrl sub w_v hcs hcv hsv
    _ _ _ hpb hc1 hc2 hca

/-! ### Generic `(N - 1)`-Plane Catalytic Cascade (`dTailPos ;; apex ;; dTailNeg`) -/

/-- Reverse-order tail circuit `planePos (t + 1) ;; ... ;; planePos 1`, realizing
`G_1 * G_2 * ... * G_{t + 1}`. -/
def genericTailPosDyn {Var : Type} {n N : ℕ}
    (planePos : (p : ℕ) → p + 1 < N → DynamicCircuit Var n) :
    (t : ℕ) → t + 1 < N → DynamicCircuit Var n
  | 0, _ => .identity
  | t + 1, ht => .seq (planePos (t + 1) ht) (genericTailPosDyn planePos t (by omega))

/-- Forward-order inverse tail circuit `planeNeg 1 ;; ... ;; planeNeg (t + 1)`, realizing
`G_{t + 1}⁻¹ * ... * G_1⁻¹ = (G_1 * ... * G_{t + 1})⁻¹`. -/
def genericTailNegDyn {Var : Type} {n N : ℕ}
    (planeNeg : (p : ℕ) → p + 1 < N → DynamicCircuit Var n) :
    (t : ℕ) → t + 1 < N → DynamicCircuit Var n
  | 0, _ => .identity
  | t + 1, ht => .seq (genericTailNegDyn planeNeg t (by omega)) (planeNeg (t + 1) ht)

/-- Full `(N - 1)`-plane fused-apex Givens cascade
`dTailPos (N - 2) ;; apex ;; dTailNeg (N - 2)`. -/
def genericCascadeDyn {Var : Type} {n N : ℕ} (hN : 1 < N)
    (planePos planeNeg : (p : ℕ) → p + 1 < N → DynamicCircuit Var n)
    (apex : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.seq (genericTailPosDyn planePos (N - 2) (by omega)) apex)
    (genericTailNegDyn planeNeg (N - 2) (by omega))

theorem count_genericCascadeDyn_toff {Var : Type} {n N : ℕ} (hN : 1 < N)
    (planePos planeNeg : (p : ℕ) → p + 1 < N → DynamicCircuit Var n)
    (apex : DynamicCircuit Var n)
    (hpos : ∀ p hp, (planePos p hp).count .TOFF = 0)
    (hneg : ∀ p hp, (planeNeg p hp).count .TOFF = 0)
    (hapex : apex.count .TOFF = 0) :
    (genericCascadeDyn hN planePos planeNeg apex).count .TOFF = 0 := by
  have htpos : ∀ t (ht : t + 1 < N), (genericTailPosDyn planePos t ht).count .TOFF = 0 := by
    intro t; induction t with
    | zero => intro _; rfl
    | succ t ih => intro ht; simp [genericTailPosDyn, hpos, ih (by omega)]
  have htneg : ∀ t (ht : t + 1 < N), (genericTailNegDyn planeNeg t ht).count .TOFF = 0 := by
    intro t; induction t with
    | zero => intro _; rfl
    | succ t ih => intro ht; simp [genericTailNegDyn, hneg, ih (by omega)]
  simp [genericCascadeDyn, htpos, htneg, hapex]

theorem count_genericCascadeDyn_t {Var : Type} {n N : ℕ} (hN : 1 < N)
    (planePos planeNeg : (p : ℕ) → p + 1 < N → DynamicCircuit Var n)
    (apex : DynamicCircuit Var n) (t_plane t_apex : ℕ)
    (hpos : ∀ p hp, (planePos p hp).count .T = t_plane)
    (hneg : ∀ p hp, (planeNeg p hp).count .T = t_plane)
    (hapex : apex.count .T = t_apex) :
    (genericCascadeDyn hN planePos planeNeg apex).count .T =
      2 * (N - 2) * t_plane + t_apex := by
  have htpos : ∀ t (ht : t + 1 < N), (genericTailPosDyn planePos t ht).count .T = t * t_plane := by
    intro t; induction t with
    | zero => intro _; simp [genericTailPosDyn]
    | succ t ih =>
        intro ht
        simp only [genericTailPosDyn, DynamicCircuit.count, hpos, ih (by omega)]
        ring
  have htneg : ∀ t (ht : t + 1 < N), (genericTailNegDyn planeNeg t ht).count .T = t * t_plane := by
    intro t; induction t with
    | zero => intro _; simp [genericTailNegDyn]
    | succ t ih =>
        intro ht
        simp only [genericTailNegDyn, DynamicCircuit.count, hneg, ih (by omega)]
        ring
  simp only [genericCascadeDyn, DynamicCircuit.count, htpos, htneg, hapex]
  ring

/-- Control-multiplexed generalized Givens tail product on `N` qubits. -/
noncomputable def genTailUnitary (N : ℕ) (α₀ α₁ : ℕ → ℝ) :
    (t : ℕ) → t + 1 < N → Unitary (2 ^ N)
  | 0, _ => 1
  | t + 1, ht =>
      genTailUnitary N α₀ α₁ t (by omega) *
        (GivensOps.pairAdj N (t + 1) ht).embedUnitary
          (genGivensPosUnitary (α₀ (t + 1)) (α₁ (t + 1)))

theorem genTailUnitary_eq_givensCascadeTail (N : ℕ) (φ : ℕ → ℝ)
    {α₀ α₁ : ℕ → ℝ} (t : ℕ) (ht : t + 1 < N)
    (h0 : ∀ p, 1 ≤ p → p ≤ t → α₀ p = 0)
    (h1 : ∀ p, 1 ≤ p → p ≤ t → α₁ p = φ p) :
    genTailUnitary N α₀ α₁ t ht = GivensOps.givensCascadeTail N φ t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [genTailUnitary, GivensOps.givensCascadeTail,
        ih (by omega) (fun p hp1 hpt => h0 p hp1 (by omega)) (fun p hp1 hpt => h1 p hp1 (by omega)),
        h0 (t + 1) (by omega) le_rfl, h1 (t + 1) (by omega) le_rfl,
        genGivensPosUnitary_zero_left]
      rfl

/-! ### `cswapSpinBlockDyn` (`4 * N` `T`, `0 TOFF`, `1` Clean Scratch Wire) -/

section SubstStoreConst
attribute [local irreducible] PreservesStoreConst

end SubstStoreConst

end Phase4B1

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
