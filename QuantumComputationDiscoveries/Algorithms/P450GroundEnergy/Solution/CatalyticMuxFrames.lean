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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalystCleanBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SpinSegregationGivens
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensDataCerts
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.UnsignedPhaseKickEngine

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open CircuitModular GivensOps
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 4A: `muxCtrlUnitary`, `4 × 4` Clifford Frames & Master Catalytic Phase-Kick Bridge -/

section MuxAndCliffordFrames

/-- Control-multiplexed operator on `k_sys + k_ctrl` wires (`locLeft k_sys k_ctrl` target,
`locRight k_sys k_ctrl` control). -/
noncomputable def muxCtrlMatrix {k_sys k_ctrl : ℕ}
    (F : Fin (2 ^ k_ctrl) → Operator (2 ^ k_sys)) : Operator (2 ^ (k_sys + k_ctrl)) :=
  fun i j =>
    let pi := blockSplitEquiv k_sys k_ctrl i
    let pj := blockSplitEquiv k_sys k_ctrl j
    if pi.2 = pj.2 then F pi.2 pi.1 pj.1 else 0

theorem muxCtrlMatrix_one {k_sys k_ctrl : ℕ} :
    muxCtrlMatrix (fun _ : Fin (2 ^ k_ctrl) => (1 : Operator (2 ^ k_sys))) = 1 := by
  ext i j
  simp only [muxCtrlMatrix, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · by_cases hc : (blockSplitEquiv k_sys k_ctrl i).2 = (blockSplitEquiv k_sys k_ctrl j).2
    · have hx : (blockSplitEquiv k_sys k_ctrl i).1 ≠ (blockSplitEquiv k_sys k_ctrl j).1 := by
        intro hx
        exact hij ((blockSplitEquiv k_sys k_ctrl).injective (Prod.ext hx hc))
      simp only [hc, ↓reduceIte, hij, hx]
    · simp only [hc, ↓reduceIte, hij]

theorem muxCtrlMatrix_mul {k_sys k_ctrl : ℕ}
    (F₁ F₂ : Fin (2 ^ k_ctrl) → Operator (2 ^ k_sys)) :
    muxCtrlMatrix F₁ * muxCtrlMatrix F₂ = muxCtrlMatrix (fun c => F₁ c * F₂ c) := by
  ext i j
  simp only [Matrix.mul_apply, muxCtrlMatrix]
  rw [← Equiv.sum_comp (blockSplitEquiv k_sys k_ctrl).symm, Fintype.sum_prod_type, Finset.sum_comm]
  by_cases hc : (blockSplitEquiv k_sys k_ctrl i).2 = (blockSplitEquiv k_sys k_ctrl j).2
  · simp only [hc, ↓reduceIte]
    rw [Fintype.sum_eq_single (blockSplitEquiv k_sys k_ctrl j).2]
    · simp only [Equiv.apply_symm_apply, ↓reduceIte]
    · intro c' hc'
      simp [Equiv.apply_symm_apply, Ne.symm hc', hc']
  · simp only [hc, ↓reduceIte]
    apply Finset.sum_eq_zero; intro c' _; apply Finset.sum_eq_zero; intro x' _
    simp only [Equiv.apply_symm_apply]
    by_cases h1 : (blockSplitEquiv k_sys k_ctrl i).2 = c'
    · have h2 : c' ≠ (blockSplitEquiv k_sys k_ctrl j).2 := fun h => hc (h1.trans h)
      simp only [h1, h2, ↓reduceIte, mul_zero]
    · simp only [h1, ↓reduceIte, zero_mul]

theorem muxCtrlMatrix_conjTranspose {k_sys k_ctrl : ℕ}
    (F : Fin (2 ^ k_ctrl) → Operator (2 ^ k_sys)) :
    (muxCtrlMatrix F)ᴴ = muxCtrlMatrix (fun c => (F c)ᴴ) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, muxCtrlMatrix]
  by_cases hc : (blockSplitEquiv k_sys k_ctrl i).2 = (blockSplitEquiv k_sys k_ctrl j).2
  · have hji : (blockSplitEquiv k_sys k_ctrl j).2 = (blockSplitEquiv k_sys k_ctrl i).2 := hc.symm
    rw [ite_eq_left_of_eq_true _ _ (eq_true hji), ite_eq_left_of_eq_true _ _ (eq_true hc), hc]
  · have hji : (blockSplitEquiv k_sys k_ctrl j).2 ≠ (blockSplitEquiv k_sys k_ctrl i).2 := Ne.symm hc
    simp only [hc, hji, ↓reduceIte, star_zero]

/-- Control-multiplexed unitary on `k_sys + k_ctrl` wires. -/
noncomputable def muxCtrlUnitary {k_sys k_ctrl : ℕ}
    (F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)) : Unitary (2 ^ (k_sys + k_ctrl)) :=
  ⟨muxCtrlMatrix (fun c => (F c).1), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      muxCtrlMatrix_conjTranspose, muxCtrlMatrix_mul]
    have h1 : (fun c => (F c).1ᴴ * (F c).1) = (fun _ => (1 : Operator (2 ^ k_sys))) := by
      funext c; rw [← Matrix.star_eq_conjTranspose]; exact (F c).2.1
    rw [h1, muxCtrlMatrix_one]⟩

@[simp]
theorem muxCtrlUnitary_val {k_sys k_ctrl : ℕ} (F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)) :
    (muxCtrlUnitary F).1 = muxCtrlMatrix (fun c => (F c).1) := rfl

@[simp]
theorem muxCtrlUnitary_one {k_sys k_ctrl : ℕ} :
    muxCtrlUnitary (fun _ : Fin (2 ^ k_ctrl) => (1 : Unitary (2 ^ k_sys))) = 1 := by
  apply Subtype.ext; exact muxCtrlMatrix_one

@[simp]
theorem muxCtrlUnitary_mul {k_sys k_ctrl : ℕ}
    (F₁ F₂ : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)) :
    muxCtrlUnitary F₁ * muxCtrlUnitary F₂ = muxCtrlUnitary (fun c => F₁ c * F₂ c) := by
  apply Subtype.ext
  change muxCtrlMatrix (fun c => (F₁ c).1) * muxCtrlMatrix (fun c => (F₂ c).1) =
    muxCtrlMatrix (fun c => (F₁ c).1 * (F₂ c).1)
  exact muxCtrlMatrix_mul _ _

@[simp]
theorem muxCtrlUnitary_inv {k_sys k_ctrl : ℕ}
    (F : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sys)) :
    (muxCtrlUnitary F)⁻¹ = muxCtrlUnitary (fun c => (F c)⁻¹) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [muxCtrlUnitary_mul]
  simp

/-- Constant `muxCtrlUnitary` equals `locLeft` embedding. -/
theorem locLeft_embedUnitary_eq_muxCtrlUnitary {k_sys k_ctrl : ℕ} (U : Unitary (2 ^ k_sys)) :
    (locLeft k_sys k_ctrl).embedUnitary U = muxCtrlUnitary (fun _ => U) := by
  apply Subtype.ext
  ext i j
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside, muxCtrlUnitary_val]
  dsimp only [muxCtrlMatrix, blockSplitEquiv, Equiv.coe_fn_mk]
  have hagree : (locLeft k_sys k_ctrl).AgreeOutside i j ↔
      (locRight k_sys k_ctrl).extractIndex i = (locRight k_sys k_ctrl).extractIndex j := by
    rw [← (basisBits k_ctrl).apply_eq_iff_eq, funext_iff]
    simp only [QRegister.AgreeOutside,
      QRegister.basisBits_extractIndex]
    constructor
    · intro h idx
      apply h (locRight k_sys k_ctrl idx)
      rintro ⟨l, hl⟩
      have hv := congrArg Fin.val hl
      simp [locLeft, locLeftOf, locRight, locRightOf, QRegister.block] at hv
      omega
    · intro h w hw
      have hge : k_sys ≤ w.val := by
        by_contra hlt
        exact hw ⟨⟨w.val, by omega⟩, by ext; simp [locLeft, locLeftOf]⟩
      have hw_eq : w = locRight k_sys k_ctrl ⟨w.val - k_sys, by omega⟩ := by
        ext; simp [locRight, locRightOf]; omega
      rw [hw_eq]; exact h ⟨w.val - k_sys, by omega⟩
  by_cases hc : (locRight k_sys k_ctrl).extractIndex i = (locRight k_sys k_ctrl).extractIndex j
  · have ha := hagree.mpr hc
    simp only [hc, ha, ↓reduceIte, mul_one]
  · have hna := mt hagree.mp hc
    simp only [hc, hna, ↓reduceIte, mul_zero]

theorem muxLiftDisj (k_sys k_ctrl : ℕ) {k_sub : ℕ} (sel : QRegister k_sub k_sys) :
    ((locLeft k_sys k_ctrl).compose sel).DisjointWires (locRight k_sys k_ctrl) := by
  rw [QRegister.disjoint_iff]
  intro a b hab
  have hv := congrArg Fin.val hab
  have hlt := (sel a).isLt
  simp [QRegister.compose, locLeft, locLeftOf, locRight, locRightOf, QRegister.block] at hv
  omega

/-- Subregister selector lifting `sel : QRegister k_sub k_sys` together with
`locRight k_sys k_ctrl`. -/
def muxLiftReg (k_sys k_ctrl : ℕ) {k_sub : ℕ} (sel : QRegister k_sub k_sys) :
    QRegister (k_sub + k_ctrl) (k_sys + k_ctrl) :=
  ((locLeft k_sys k_ctrl).compose sel).concat (locRight k_sys k_ctrl) (muxLiftDisj k_sys k_ctrl sel)

theorem compose_muxLiftReg {n k_sys k_ctrl k_sub : ℕ}
    (rSys : QRegister k_sys n) (rCtrl : QRegister k_ctrl n) (hsc : rSys.DisjointWires rCtrl)
    (sel : QRegister k_sub k_sys) (hsc_sub : (rSys.compose sel).DisjointWires rCtrl) :
    (rSys.concat rCtrl hsc).compose (muxLiftReg k_sys k_ctrl sel) =
      (rSys.compose sel).concat rCtrl hsc_sub := by
  ext idx
  refine Fin.addCases (fun a => ?_) (fun b => ?_) idx
  · have ha : muxLiftReg k_sys k_ctrl sel (Fin.castAdd k_ctrl a) = Fin.castAdd k_ctrl (sel a) := by
      ext; simp [muxLiftReg, QRegister.compose, locLeft, locLeftOf, QRegister.block]
    simp [QRegister.compose, ha]
  · have hb : muxLiftReg k_sys k_ctrl sel (Fin.natAdd k_sub b) = Fin.natAdd k_sys b := by
      ext; simp [muxLiftReg, locRight, locRightOf, QRegister.block]
    simp [QRegister.compose, hb]

theorem muxLiftReg_embedUnitary_muxCtrlUnitary {k_sys k_ctrl k_sub : ℕ}
    (sel : QRegister k_sub k_sys) (G : Fin (2 ^ k_ctrl) → Unitary (2 ^ k_sub)) :
    (muxLiftReg k_sys k_ctrl sel).embedUnitary (muxCtrlUnitary G) =
      muxCtrlUnitary (fun c => sel.embedUnitary (G c)) := by
  let rLift := muxLiftReg k_sys k_ctrl sel
  have hLiftL : rLift.compose (locLeft k_sub k_ctrl) = (locLeft k_sys k_ctrl).compose sel := by
    ext a
    have ha : locLeft k_sub k_ctrl a = Fin.castAdd k_ctrl a := by
      ext; simp [locLeft, locLeftOf, QRegister.block]
    simp [rLift, muxLiftReg, QRegister.compose, ha]
  have hLiftR : rLift.compose (locRight k_sub k_ctrl) = locRight k_sys k_ctrl := by
    ext b
    have hb : locRight k_sub k_ctrl b = Fin.natAdd k_sub b := by
      ext; simp [locRight, locRightOf, QRegister.block]
    simp [rLift, muxLiftReg, QRegister.compose, hb]
  apply Subtype.ext
  ext i j
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside, muxCtrlUnitary_val,
    muxCtrlUnitary_val]
  dsimp only [muxCtrlMatrix]
  have hextL : ∀ g, (blockSplitEquiv k_sub k_ctrl (rLift.extractIndex g)).1 =
      sel.extractIndex ((blockSplitEquiv k_sys k_ctrl g).1) := by
    intro g
    change (locLeft k_sub k_ctrl).extractIndex (rLift.extractIndex g) =
      sel.extractIndex ((locLeft k_sys k_ctrl).extractIndex g)
    rw [← QRegister.extractIndex_compose, hLiftL, QRegister.extractIndex_compose]
  have hextR : ∀ g, (blockSplitEquiv k_sub k_ctrl (rLift.extractIndex g)).2 =
      (blockSplitEquiv k_sys k_ctrl g).2 := by
    intro g
    change (locRight k_sub k_ctrl).extractIndex (rLift.extractIndex g) =
      (locRight k_sys k_ctrl).extractIndex g
    rw [← QRegister.extractIndex_compose, hLiftR]
  rw [hextL i, hextL j, hextR i, hextR j]
  by_cases hc : (blockSplitEquiv k_sys k_ctrl i).2 = (blockSplitEquiv k_sys k_ctrl j).2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc),
      QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside]
    have hagree : rLift.AgreeOutside i j ↔
        sel.AgreeOutside ((blockSplitEquiv k_sys k_ctrl i).1)
          ((blockSplitEquiv k_sys k_ctrl j).1) := by
      have hc_bits : ∀ b : Fin k_ctrl,
          basisBits (k_sys + k_ctrl) i (locRight k_sys k_ctrl b) =
            basisBits (k_sys + k_ctrl) j (locRight k_sys k_ctrl b) := by
        intro b
        have h : basisBits k_ctrl ((locRight k_sys k_ctrl).extractIndex i) b =
            basisBits k_ctrl ((locRight k_sys k_ctrl).extractIndex j) b :=
          congrFun (congrArg (basisBits k_ctrl) hc) b
        rwa [(locRight k_sys k_ctrl).basisBits_extractIndex,
          (locRight k_sys k_ctrl).basisBits_extractIndex] at h
      constructor
      · intro h w hw
        have hw' : locLeft k_sys k_ctrl w ∉ Set.range rLift.wires := by
          rintro ⟨idx, hidx⟩
          refine Fin.addCases (fun a ha => ?_) (fun b hb => ?_) idx hidx
          · simp only [rLift, muxLiftReg, QRegister.concat_apply_left,
              QRegister.compose_apply] at ha
            exact hw ⟨a, (locLeft k_sys k_ctrl).wires.injective ha⟩
          · have hv := congrArg Fin.val hb
            have hlt := w.isLt
            simp [rLift, muxLiftReg, locLeft, locLeftOf, locRight, locRightOf,
              QRegister.block] at hv
            omega
        have hi := (locLeft k_sys k_ctrl).basisBits_extractIndex i w
        have hj := (locLeft k_sys k_ctrl).basisBits_extractIndex j w
        change basisBits k_sys ((locLeft k_sys k_ctrl).extractIndex i) w =
          basisBits k_sys ((locLeft k_sys k_ctrl).extractIndex j) w
        rw [hi, hj]
        exact h _ hw'
      · intro h w hw
        by_cases hlt : w.val < k_sys
        · let w0 : Fin k_sys := ⟨w.val, hlt⟩
          have hw_eq : w = locLeft k_sys k_ctrl w0 := by
            ext; simp [locLeft, locLeftOf, w0, QRegister.block]
          have hw0 : w0 ∉ Set.range sel.wires := by
            rintro ⟨a, ha⟩
            exact hw ⟨Fin.castAdd k_ctrl a, by simp [rLift, muxLiftReg, hw_eq, ha]⟩
          have hi := (locLeft k_sys k_ctrl).basisBits_extractIndex i w0
          have hj := (locLeft k_sys k_ctrl).basisBits_extractIndex j w0
          rw [hw_eq, ← hi, ← hj]
          exact h w0 hw0
        · have hw_eq : w = locRight k_sys k_ctrl ⟨w.val - k_sys, by omega⟩ := by
            ext; simp [locRight, locRightOf]; omega
          rw [hw_eq]
          exact hc_bits _
    by_cases ha : (muxLiftReg k_sys k_ctrl sel).AgreeOutside i j
    · have ha' := hagree.mp ha
      simp only [ha, ha', ↓reduceIte, mul_one]
    · have hna' := mt hagree.mpr ha
      simp only [ha, hna', ↓reduceIte, mul_zero]
  · simp only [hc, ↓reduceIte, zero_mul]

/-- Diagonal 4-state phase vector `[e^{i α₀}, e^{-i α₀}, e^{i α₁}, e^{-i α₁}]`. -/
noncomputable def genKick4 (α₀ α₁ : ℝ) : Fin (2 ^ 2) → ℂ :=
  ![Complex.exp ((α₀ : ℂ) * Complex.I),
    Complex.exp (-((α₀ : ℂ) * Complex.I)),
    Complex.exp ((α₁ : ℂ) * Complex.I),
    Complex.exp (-((α₁ : ℂ) * Complex.I))]

theorem genKick4_unit (α₀ α₁ : ℝ) (x : Fin (2 ^ 2)) :
    star (genKick4 α₀ α₁ x) * genKick4 α₀ α₁ x = 1 := by
  have hpos (θ : ℝ) : star (Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj]
    simp [← Complex.exp_add]
  have hneg (θ : ℝ) : star (Complex.exp (-((θ : ℂ) * Complex.I))) *
      Complex.exp (-((θ : ℂ) * Complex.I)) = 1 := by
    have := hpos (-θ)
    simpa using this
  fin_cases x
  · exact hpos α₀
  · exact hneg α₀
  · exact hpos α₁
  · exact hneg α₁

/-- Standard single-excitation diagonal phase vector `[1, 1, e^{i α}, e^{-i α}]` (`α₀ = 0`). -/
noncomputable abbrev planeKick4 (α : ℝ) : Fin (2 ^ 2) → ℂ := genKick4 0 α

/-- Two-wire Clifford pre/post frames for `G(+α)` and `G(-α)` (`0 T`, `0 TOFF`). -/
def cliffPrePos : Circuit 2 :=
  Circuit.CNOT 0 1 (by decide) ;;ᶜ Circuit.S 0 ;;ᶜ Circuit.H 0

def cliffPostPos : Circuit 2 :=
  Circuit.H 0 ;;ᶜ sdagCircuit 0 ;;ᶜ Circuit.CNOT 0 1 (by decide)

def cliffPreNeg : Circuit 2 :=
  Circuit.CNOT 0 1 (by decide) ;;ᶜ sdagCircuit 0 ;;ᶜ Circuit.H 0

def cliffPostNeg : Circuit 2 :=
  Circuit.H 0 ;;ᶜ Circuit.S 0 ;;ᶜ Circuit.CNOT 0 1 (by decide)

@[simp] theorem count_cliffPrePos_t : cliffPrePos.count .T = 0 := by simp [cliffPrePos]
@[simp] theorem count_cliffPrePos_toff : cliffPrePos.count .TOFF = 0 := by simp [cliffPrePos]
@[simp] theorem count_cliffPostPos_t : cliffPostPos.count .T = 0 := by simp [cliffPostPos]
@[simp] theorem count_cliffPostPos_toff : cliffPostPos.count .TOFF = 0 := by simp [cliffPostPos]
@[simp] theorem count_cliffPreNeg_t : cliffPreNeg.count .T = 0 := by simp [cliffPreNeg]
@[simp] theorem count_cliffPreNeg_toff : cliffPreNeg.count .TOFF = 0 := by simp [cliffPreNeg]
@[simp] theorem count_cliffPostNeg_t : cliffPostNeg.count .T = 0 := by simp [cliffPostNeg]
@[simp] theorem count_cliffPostNeg_toff : cliffPostNeg.count .TOFF = 0 := by simp [cliffPostNeg]

private theorem eval_ket_fin4_entry (c : Circuit 2) (i j : Fin (2 ^ 2)) :
    c.eval.1 i j = c.eval.1.mulVec (ket (basisBits 2 j)) i := by
  rw [← single_eq_ket, Matrix.mulVec_single_one]
  rfl

private theorem ket2_apply (β : BitAssignment 2) (i : Fin (2 ^ 2)) :
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

private noncomputable def cliffPrePosMat : Operator (2 ^ 2) :=
  let s := sqrtHalfC
  !![s, 0, 0, Complex.I * s;
     s, 0, 0, -Complex.I * s;
     0, Complex.I * s, s, 0;
     0, -Complex.I * s, s, 0]

private noncomputable def cliffPostPosMat : Operator (2 ^ 2) :=
  let s := sqrtHalfC
  !![s, s, 0, 0;
     0, 0, -Complex.I * s, Complex.I * s;
     0, 0, s, s;
     -Complex.I * s, Complex.I * s, 0, 0]

private theorem basisBits2_apply (x : Fin (2 ^ 2)) :
    basisBits 2 x = fun (w : Wire 2) => ((x.val / 2 ^ w.val % 2 : ℕ) : ZMod 2) :=
  funext (basisBits_eq_div_mod 2 x)

private theorem zmod2_val_2 : (2 : ZMod 2).val = 0 := rfl
private theorem zmod2_val_3 : (3 : ZMod 2).val = 1 := rfl

private theorem cliffPrePos_eval_val : cliffPrePos.eval.1 = cliffPrePosMat := by
  ext i j
  rw [eval_ket_fin4_entry cliffPrePos i j]
  dsimp only [cliffPrePos]
  simp only [eval_seq_mulVec, evolve_CNOT_ket, evolve_S_ket, Matrix.mulVec_smul, evolve_H_ket,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, ket2_apply, basisBits2_apply]
  fin_cases j <;> fin_cases i <;>
    simp [cliffPrePosMat, zmod2_val_2, zmod2_val_3]

private theorem cliffPostPos_eval_val : cliffPostPos.eval.1 = cliffPostPosMat := by
  ext i j
  rw [eval_ket_fin4_entry cliffPostPos i j]
  dsimp only [cliffPostPos]
  simp only [eval_seq_mulVec, evolve_H_ket, Matrix.mulVec_add, Matrix.mulVec_smul,
    evolve_sdagCircuit_ket, evolve_CNOT_ket, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ket2_apply,
    basisBits2_apply]
  fin_cases j <;> fin_cases i <;>
    simp [cliffPostPosMat] <;> ring

private theorem sum_fin4_2pow (f : Fin (2 ^ 2) → ℂ) :
    (∑ x : Fin (2 ^ 2), f x) = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/-- Exact `4 × 4` positive Givens frame identity:
`cliffPostPos * diag(planeKick4 α) * cliffPrePos = givensPlaneUnitary α`. -/
theorem cliffFramePos_eq (α : ℝ) :
    cliffPostPos.eval * phaseDiagUnitary (planeKick4 α) (genKick4_unit 0 α) * cliffPrePos.eval =
      GivensOps.givensPlaneUnitary α := by
  have he_pos : Complex.exp ((α : ℂ) * Complex.I) =
      (Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have he_neg : Complex.exp (-((α : ℂ) * Complex.I)) =
      (Real.cos α : ℂ) - (Real.sin α : ℂ) * Complex.I := by
    have h := Complex.exp_mul_I (-(α : ℂ))
    rw [neg_mul] at h
    rw [h, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hs2 := sqrtHalfC_sq
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  apply Subtype.ext
  change (cliffPostPos.eval.1 * Matrix.diagonal (planeKick4 α) * cliffPrePos.eval.1 : Operator
    (2 ^ 2)) =
    GivensOps.givensPlaneMatrix α
  rw [cliffPostPos_eval_val, cliffPrePos_eval_val]
  ext i j
  simp only [Matrix.mul_apply, sum_fin4_2pow, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [cliffPostPosMat, neg_mul, Nat.reducePow, Fin.zero_eta, Fin.isValue, of_apply,
      cons_val', cons_val_zero, cons_val_fin_one, ↓reduceIte, planeKick4, genKick4,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero, neg_zero, he_pos, Complex.ofReal_cos,
      Complex.ofReal_sin, he_neg, mul_one, cons_val_one, one_ne_zero, mul_zero, add_zero,
      cons_val, Fin.reduceEq, cliffPrePosMat, zero_ne_one, zero_add, givensPlaneMatrix,
      Fin.mk_one, mul_neg, Fin.reduceFinMk, add_neg_cancel, neg_add_cancel] <;>
    (ring_nf; try simp only [hs2, hI2]; ring)

/-- Single-spin orbital reflection `1 - 2 • singleSpinOrbitalNumberOp N (givensLeaf b k)` packaged
as a `Unitary (2 ^ N)` via `givensCascadeTail_conj_fusedApex`. -/
noncomputable def singleSpinReflectionUnitary (N : ℕ) (hN : 1 < N) (b : ℕ) (k : Fin N → ℤ) :
    Unitary (2 ^ N) :=
  let z0 : Fin N := ⟨0, by omega⟩
  let U_tail := GivensOps.givensCascadeTail N (GivensOps.givensLeafAngle N b k) (N - 2) (by omega)
  U_tail⁻¹ *
    ((QRegister.singleton z0).embedUnitary Qubit.Z *
      GivensOps.givensAdjUnitary N 0 hN (2 * GivensOps.givensLeafAngle N b k 0)) *
    U_tail

theorem singleSpinReflectionUnitary_val (N : ℕ) (hN : 1 < N) (b : ℕ) (k : Fin N → ℤ) :
    (singleSpinReflectionUnitary N hN b k).1 =
      1 - (2 : ℂ) • GivensOps.singleSpinOrbitalNumberOp N (givensLeaf b k) := by
  let U_tail := GivensOps.givensCascadeTail N (GivensOps.givensLeafAngle N b k) (N - 2) (by omega)
  have hinv : (U_tail⁻¹).1 = U_tail.1ᴴ := rfl
  dsimp only [singleSpinReflectionUnitary]
  simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
  rw [hinv]
  exact GivensOps.givensCascadeTail_conj_fusedApex N hN b k

end MuxAndCliffordFrames

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
