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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.K6SweepAndLoad273
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ZeroAncUspGates

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosPostPrep80MergedVepS3Aux
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80MergedVepS3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section PosPostPrep80MergedVepS3

section ModPosPostPrep80MergedVepS3
public section
namespace PosPostPrep80MergedVepS3Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
end PosPostPrep80MergedVepS3Alt
namespace PosPostPrep80MergedVepS3
section ConfigPosPostPrep80MergedVepS3
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instLoc_PosPostPrep80MergedVepS3_1InstNeZeroTwoPowPo (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket bit_cases)
open ZeroAncillaUSPS3 hiding ket
open Pos24HeadCoordXor80 (bitsVal3_lt8 headCoordXorLocal67 rHeadAct37In80)
theorem itePosLocal {α : Type*} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by simp [hp]
theorem iteNegLocal {α : Type*} {p : Prop} [Decidable p] (hp : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [hp]
theorem ket_eq_single_local {N : ℕ} (β : BitAssignment N) :
    ket β = (Pi.single ((basisBitsEquiv N).symm β) (1 : ℂ) : Fin (2 ^ N) → ℂ) :=
  funext fun x ↦ by simp [MeasureBranchHadamardSem.ket]
theorem basisBits_symm_local {N : ℕ} (β : BitAssignment N) : basisBits N
    ((basisBitsEquiv N).symm β) = β := (basisBitsEquiv N).apply_symm_apply β
noncomputable def lockPosPostVal {α : Sort*} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem lockPosPostVal_eq {α : Sort*} (x : α) : lockPosPostVal x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem wCore3967_lt : 3967 < FullSysCatSegmentBridge.fullSysCoreWires 80 := by decide
theorem wCore4029_lt : 4029 < FullSysCatSegmentBridge.fullSysCoreWires 80 := by decide
def wCore3967 : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80) := ⟨3967, wCore3967_lt⟩
def wCore4029 : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80) := ⟨4029, wCore4029_lt⟩
theorem wCore3967_ne_4029 : wCore3967 ≠ wCore4029 :=
  fun h ↦ absurd (congrArg Fin.val h) (by decide)
def swapCore3967Fn (β : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80)) :
    BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  fun q ↦ β (Equiv.swap wCore3967 wCore4029 q)
@[scoped simp] theorem swapCore3967Fn_involutive
    (β : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80)) :
    swapCore3967Fn (swapCore3967Fn β) = β :=
  funext fun q ↦ by simp [swapCore3967Fn]
def cSwap2 {n : ℕ} (a b : Wire n) (hne : a ≠ b) : Circuit n := .seq (Circuit.CNOT a b hne)
    (.seq (Circuit.CNOT b a hne.symm) (Circuit.CNOT a b hne))
def cSwapCore3967 : Circuit (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  cSwap2 wCore3967 wCore4029 wCore3967_ne_4029
theorem zmod2_swap_a (x y : ZMod 2) : x + (y + x) = y := by decide +revert
theorem zmod2_swap_b (x y : ZMod 2) : y + x + (x + (y + x)) = x := by decide +revert
noncomputable def uSwapCore3967 : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires 80)) :=
  lockPosPostVal cSwapCore3967.eval
theorem uSwapCore3967_mulVec_ket
    (β : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80)) :
    uSwapCore3967.1.mulVec (ket β) = ket (swapCore3967Fn β) := by
  rw [uSwapCore3967, lockPosPostVal_eq]
  unfold cSwapCore3967 cSwap2 swapCore3967Fn
  rw [MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_CNOT,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_CNOT,
    MeasureBranchHadamardSem.ket_CNOT]
  refine congrArg ket (funext fun q ↦ ?_)
  by_cases h1 : q = wCore3967
  · simp [h1, wCore3967_ne_4029, wCore3967_ne_4029.symm, zmod2_swap_a]
  · by_cases h2 : q = wCore4029
    · simp [h2, wCore3967_ne_4029, wCore3967_ne_4029.symm, zmod2_swap_b]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
@[scoped simp] theorem uSwapCore3967_mul_self : uSwapCore3967 * uSwapCore3967 = 1 :=
  Subtype.ext <| MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ by
    rw [Submonoid.coe_mul, OneMemClass.coe_one, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      uSwapCore3967_mulVec_ket, uSwapCore3967_mulVec_ket, swapCore3967Fn_involutive]
theorem unitary_conjTranspose_of_mul_self {K : ℕ} (U : Unitary K) (h : U * U = 1) :
    U.1ᴴ = U.1 := by
  rw [← Matrix.mul_one U.1ᴴ, ← show U.1 * U.1 = 1 from congrArg Subtype.val h,
    ← Matrix.mul_assoc, show U.1ᴴ * U.1 = 1 from Unitary.coe_star_mul_self U, Matrix.one_mul]
@[scoped simp] theorem uSwapCore3967_conjTranspose : uSwapCore3967.1ᴴ = uSwapCore3967.1 :=
  unitary_conjTranspose_of_mul_self uSwapCore3967 uSwapCore3967_mul_self
def cHalfH {n : ℕ} (q : Wire n) : Circuit n :=
  .seq (Circuit.S q) (.seq (Circuit.H q) (Circuit.T q))
def chCircuit {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) : Circuit n :=
  .seq (cHalfH targ) (.seq (Circuit.CNOT ctrl targ hne) (cHalfH targ).inverse)
@[scoped simp] theorem chCircuit_count_toff {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) :
    (chCircuit ctrl targ hne).count PrimitiveGate.TOFF = 0 := by
  simp [chCircuit, cHalfH, Circuit.inverse, inverseGate]
@[scoped simp] theorem chCircuit_count_t {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) :
    (chCircuit ctrl targ hne).count PrimitiveGate.T = 2 := by
  simp [chCircuit, cHalfH, Circuit.inverse, inverseGate]
theorem halfH_conj_x_mul_h : (PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval .h)⁻¹ *
    (PrimitiveGate.eval .t)⁻¹ * PrimitiveGate.eval .x * PrimitiveGate.eval .t *
    PrimitiveGate.eval .h * PrimitiveGate.eval .s * PrimitiveGate.eval .h = (1 : Unitary 2) := by
  have hsq4 : ((√(2 : ℝ) : ℂ) ^ 4) = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      show ((√(2 : ℝ) : ℂ) ^ 2) = 2 by exact_mod_cast Real.sq_sqrt (by norm_num)]
    norm_num
  have h2nz : (√(2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  refine Subtype.ext ( Matrix.ext fun i j ↦ ?_ )
  change (((PrimitiveGate.eval .s).1ᴴ * (PrimitiveGate.eval .h).1ᴴ * (PrimitiveGate.eval .t).1ᴴ *
      (PrimitiveGate.eval .x).1 * (PrimitiveGate.eval .t).1 * (PrimitiveGate.eval .h).1 *
      (PrimitiveGate.eval .s).1 * (PrimitiveGate.eval .h).1) i j) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [PrimitiveGate.eval_s_val, PrimitiveGate.eval_t_val]
  fin_cases i <;> fin_cases j <;>
    simp [PrimitiveGate.eval, Qubit.H, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [h2nz] <;> ring_nf <;> simp only [hsq4, Complex.I_sq] <;> ring
theorem eval_h_mul_h : PrimitiveGate.eval .h * PrimitiveGate.eval .h = (1 : Unitary 2) :=
  Subtype.ext <| Matrix.ext fun i j ↦ by
    change (((PrimitiveGate.eval .h).1 * (PrimitiveGate.eval .h).1) i j) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.H, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
theorem halfH_conj_x_eq_h : (PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval .h)⁻¹ *
    (PrimitiveGate.eval .t)⁻¹ * PrimitiveGate.eval .x * PrimitiveGate.eval .t *
    PrimitiveGate.eval .h * PrimitiveGate.eval .s = PrimitiveGate.eval .h := by
  have hmul := congrArg (· * PrimitiveGate.eval .h) halfH_conj_x_mul_h
  rwa [mul_assoc _ (PrimitiveGate.eval .h) (PrimitiveGate.eval .h), eval_h_mul_h,
    mul_one, one_mul] at hmul
theorem cHalfH_eval_eq_singleton {n : ℕ} (q : Wire n) : (cHalfH q).eval =
    (QRegister.singleton q).embedUnitary (PrimitiveGate.eval .t * PrimitiveGate.eval .h *
    PrimitiveGate.eval .s) := by
  change (Circuit.single .t q).eval * (Circuit.single .h q).eval * (Circuit.single .s q).eval = _
  rw [Circuit.eval_single, Circuit.eval_single, Circuit.eval_single,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
theorem cHalfH_inv_eval_eq_singleton {n : ℕ} (q : Wire n) : (cHalfH q).inverse.eval =
    (QRegister.singleton q).embedUnitary ((PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval
    .h)⁻¹ * (PrimitiveGate.eval .t)⁻¹) := by
  rw [Circuit.eval_inverse, cHalfH_eval_eq_singleton]
  apply mul_eq_one_iff_inv_eq.mp
  rw [← (QRegister.singleton q).embedUnitary_mul,
    show (PrimitiveGate.eval .t * PrimitiveGate.eval .h * PrimitiveGate.eval .s) *
      ((PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval .h)⁻¹ * (PrimitiveGate.eval .t)⁻¹) = 1 by
      group,
    QRegister.embedUnitary_one]
theorem cHalfH_comm_proj {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) (b : Fin (2 ^ 1)) :
    (cHalfH targ).eval.1 * (QRegister.singleton ctrl).basisOutcomeProjector b =
      (QRegister.singleton ctrl).basisOutcomeProjector b * (cHalfH targ).eval.1 := by
  rw [cHalfH_eval_eq_singleton]
  exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _
    (QRegister.disjoint_iff.mpr fun _ _ h ↦ hne h.symm) _ b
theorem chCircuit_mulVec_ket_ctrl_zero {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ)
    (β : BitAssignment n) (hc : β ctrl = 0) :
    (chCircuit ctrl targ hne).eval.1.mulVec (ket β) = ket β := by
  let P₀ := (QRegister.singleton ctrl).basisOutcomeProjector 0
  have hcomm := cHalfH_comm_proj ctrl targ hne 0
  have hcnot : (Circuit.CNOT ctrl targ hne).eval.1 * P₀ = P₀ :=
    MeasureBranchHadamardSem.matrix_ext_ket fun γ ↦ by
      rw [← Matrix.mulVec_mulVec, MeasureBranchHadamardSem.ket_projector_zero]
      split_ifs with hγ
      · rw [MeasureBranchHadamardSem.ket_CNOT, hγ, add_zero, Function.update_eq_self]
      · exact Matrix.mulVec_zero _
  have hMat : (chCircuit ctrl targ hne).eval.1 * P₀ = P₀ := by
    change (((cHalfH targ).inverse.eval.1 * (Circuit.CNOT ctrl targ hne).eval.1) *
      (cHalfH targ).eval.1) * P₀ = P₀
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hcomm,
      ← Matrix.mul_assoc (Circuit.CNOT ctrl targ hne).eval.1, hcnot, ← hcomm, ← Matrix.mul_assoc,
      show (cHalfH targ).inverse.eval.1 * (cHalfH targ).eval.1 =
        ((cHalfH targ).inverse.eval * (cHalfH targ).eval).1 from rfl,
      Circuit.eval_inverse, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  rw [← show P₀.mulVec (ket β) = ket β by
    rw [MeasureBranchHadamardSem.ket_projector_zero, itePosLocal hc], Matrix.mulVec_mulVec, hMat]
theorem cnot_eq_x_on_ctrl_one {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) :
    let P₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
      (QRegister.singleton ctrl).basisOutcomeProjector 1
    (Circuit.CNOT ctrl targ hne).eval.1 * P₁ = (Circuit.X targ).eval.1 * P₁ := by
  intro P₁
  refine MeasureBranchHadamardSem.matrix_ext_ket fun γ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    MeasureBranchHadamardSem.ket_projector_one]
  split_ifs with hγ
  · rw [MeasureBranchHadamardSem.ket_CNOT, MeasureBranchHadamardSem.ket_X, hγ]
  · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem chCircuit_mulVec_ket_ctrl_one {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ)
    (β : BitAssignment n) (hc1 : β ctrl = 1) : (chCircuit ctrl targ hne).eval.1.mulVec (ket β)
    = (Circuit.H targ).eval.1.mulVec (ket β) := by
  let P₁ := (QRegister.singleton ctrl).basisOutcomeProjector 1
  have hcommW := cHalfH_comm_proj ctrl targ hne 1
  have hEqH : (cHalfH targ).inverse.eval * (Circuit.X targ).eval * (cHalfH targ).eval =
      (Circuit.H targ).eval := by
    rw [cHalfH_inv_eval_eq_singleton, cHalfH_eval_eq_singleton, Circuit.eval_single,
      Circuit.eval_single, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
    exact congrArg _ (by rw [← mul_assoc, ← mul_assoc, halfH_conj_x_eq_h])
  have hMat : (chCircuit ctrl targ hne).eval.1 * P₁ = (Circuit.H targ).eval.1 * P₁ := by
    change (((cHalfH targ).inverse.eval.1 * (Circuit.CNOT ctrl targ hne).eval.1) *
      (cHalfH targ).eval.1) * P₁ = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hcommW,
      ← Matrix.mul_assoc (Circuit.CNOT ctrl targ hne).eval.1,
      cnot_eq_x_on_ctrl_one ctrl targ hne, Matrix.mul_assoc (Circuit.X targ).eval.1, ← hcommW,
      ← Matrix.mul_assoc (cHalfH targ).inverse.eval.1,
      ← Matrix.mul_assoc ((cHalfH targ).inverse.eval.1 * (Circuit.X targ).eval.1),
      show ((cHalfH targ).inverse.eval.1 * (Circuit.X targ).eval.1) * (cHalfH targ).eval.1 =
        ((cHalfH targ).inverse.eval * (Circuit.X targ).eval * (cHalfH targ).eval).1 from rfl, hEqH]
  rw [← show P₁.mulVec (ket β) = ket β by
    rw [MeasureBranchHadamardSem.ket_projector_one, itePosLocal hc1],
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMat]
@[scoped simp] theorem circuit_inverse_count_T {n : ℕ} (c : Circuit n) :
    c.inverse.count PrimitiveGate.T = c.count PrimitiveGate.T := by simp
@[scoped simp] theorem circuit_inverse_count_TOFF {n : ℕ} (c : Circuit n) :
    c.inverse.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := by simp
def padZeroBits {k a w : ℕ} (_hwa : k + a = w) (γ : BitAssignment k) : BitAssignment w :=
  fun q ↦ if hq : q.val < k then γ ⟨q.val, hq⟩ else 0
def wCoin0_128 : Wire 128 := ⟨0, by decide⟩
def wCoin1_128 : Wire 128 := ⟨1, by decide⟩
def wCoin2_128 : Wire 128 := ⟨2, by decide⟩
theorem wP80_128_lt (j : Fin 80) : 6 + j.val < 128 := by omega
def wP80_128 (j : Fin 80) : Wire 128 := ⟨6 + j.val, wP80_128_lt j⟩
def rP80_128 : QRegister 80 128 := QRegister.block 6 80 (by decide)
def rB1_128 : QRegister 3 128 := QRegister.block 6 3 (by decide)
def rB0_128 : QRegister 3 128 := QRegister.block 9 3 (by decide)
def rNuc_128 : QRegister 8 128 := QRegister.block 12 8 (by decide)
def rAnc_128 : QRegister 8 128 := QRegister.block 20 8 (by decide)
def rPart_128 : QRegister 8 128 := QRegister.block 28 8 (by decide)
def wIsHead_128 : Wire 128 := ⟨36, by decide⟩
def rTwoUnif_128 : QRegister 2 128 where
  wires := ⟨![⟨37, by decide⟩, ⟨85, by decide⟩], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp at h <;> rfl⟩
def rFine30_128 : QRegister 30 128 := QRegister.block 38 30 (by decide)
def rK_128 : QRegister 6 128 := QRegister.block 69 6 (by decide)
def rPid_128 : QRegister 3 128 := QRegister.block 75 3 (by decide)
def rSm_128 : QRegister 3 128 := QRegister.block 78 3 (by decide)
def scr30_128 : QRegister 30 128 := QRegister.block 86 30 (by decide)
def wEnPos_128 : Wire 128 := ⟨116, by decide⟩
def wEnS0_128 : Wire 128 := ⟨117, by decide⟩
def wEnC0_128 : Wire 128 := ⟨118, by decide⟩
def wEnHead_128 : Wire 128 := ⟨119, by decide⟩
def wEnTail_128 : Wire 128 := ⟨120, by decide⟩
def wEnC0Head_128 : Wire 128 := ⟨121, by decide⟩
def wEnAnc_128 : Wire 128 := ⟨122, by decide⟩
def wEnS0Tail_128 : Wire 128 := ⟨123, by decide⟩
def wPopT01_128 : Wire 128 := ⟨124, by decide⟩
def wPopMaj_128 : Wire 128 := ⟨125, by decide⟩
def wPopPar_128 : Wire 128 := ⟨126, by decide⟩
def wBrTop_128 : Wire 128 := ⟨127, by decide⟩
def computeEnPos {n : ℕ} (c1 c2 anc : Wire n) : Circuit n :=
  Circuit.X c1 ;;ᶜ Circuit.X c2 ;;ᶜ andComputeIf c1 c2 anc ;;ᶜ Circuit.X c1 ;;ᶜ Circuit.X c2
def chIf {n : ℕ} (ctrl targ : Wire n) : Circuit n :=
  if hne : ctrl = targ then Circuit.identity else chCircuit ctrl targ hne
@[scoped simp] theorem count_toff_chIf {n : ℕ} (ctrl targ : Wire n) :
    (chIf ctrl targ).count PrimitiveGate.TOFF = 0 := by
  dsimp [chIf]
  split_ifs <;> simp
theorem count_t_chIf_le {n : ℕ} (ctrl targ : Wire n) :
    (chIf ctrl targ).count PrimitiveGate.T ≤ 2 := by
  dsimp [chIf]
  split_ifs <;> simp
def unHadamardList {n : ℕ} (ctrl : Wire n) : List (Wire n) → Circuit n
  | [] => Circuit.identity
  | q :: qs => unHadamardList ctrl qs ;;ᶜ chIf ctrl q
@[scoped simp] theorem count_toff_unHadamardList {n : ℕ} (ctrl : Wire n) :
    ∀ qs : List (Wire n), (unHadamardList ctrl qs).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | _ :: qs => by simp [unHadamardList, count_toff_unHadamardList ctrl qs]
theorem count_t_unHadamardList_le {n : ℕ} (ctrl : Wire n) :
    ∀ qs : List (Wire n), (unHadamardList ctrl qs).count PrimitiveGate.T ≤ 2 * qs.length
  | [] => by simp [unHadamardList]
  | q :: qs => by
    simpa [unHadamardList, List.length_cons, Nat.mul_add] using
      Nat.add_le_add (count_t_unHadamardList_le ctrl qs) (count_t_chIf_le ctrl q)
def wPmPar_128 : Wire 128 := scr30_128 ⟨20, by decide⟩
def scr20_128 (i : Fin 20) : Wire 128 := scr30_128 ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
def cUnaryFork {n : ℕ} (u t uRight : Wire n) : Circuit n :=
  andComputeIf u t uRight ;;ᶜ cnotIf uRight u
def withUnaryFork {n : ℕ} (u t uRight : Wire n) (body : Circuit n) : Circuit n :=
  cUnaryFork u t uRight ;;ᶜ body ;;ᶜ (cUnaryFork u t uRight).inverse
def isHeadPmBranches : List (Wire 128 × List (Fin 4)) :=
  [(wEnC0_128, isHeadS0FalseOdds), (wEnS0_128, isHeadS0TrueOdds)]
def cIsHeadPmRaw_128 : Circuit 128 :=
  cPmSplit 44 isHeadPmBranches [] (scr30_128 ⟨0, by decide⟩) wIsHead_128 ;;ᶜ
  cnotIf wEnC0_128 wIsHead_128 ;;ᶜ
  cnotIf wEnS0_128 wIsHead_128
noncomputable def cIsHeadPm_128 : Circuit 128 := lockPosPostVal cIsHeadPmRaw_128
theorem count_toff_cIsHeadPm_128 : cIsHeadPm_128.count PrimitiveGate.TOFF = 0 := by
  simp [cIsHeadPm_128, lockPosPostVal_eq, cIsHeadPmRaw_128]
theorem count_t_cIsHeadPm_128_le : cIsHeadPm_128.count PrimitiveGate.T ≤ 88 := by
  simp [cIsHeadPm_128, lockPosPostVal_eq, cIsHeadPmRaw_128, count_t_cnotIf]
def hsBranchesIdx_0 : List (Fin 20 × List (Fin 4)) := [(⟨0, by decide⟩, hstPoolOdds_2)]
def hsBranches_0 : List (Wire 128 × List (Fin 4)) := hsBranchesIdx_0.map fun p =>
    (scr20_128 p.1, p.2)
def hsFlipsIdx_0 : List (Fin 20) := []
def hsFlips_0 : List (Wire 128) := hsFlipsIdx_0.map scr20_128
def cHsSplit_0 : Circuit 128 := cPmSplit 38 hsBranches_0 hsFlips_0 wPmPar_128 (rK_128 ⟨5,
    by decide⟩)
def hsBranchesIdx_1 : List (Fin 20 × List (Fin 4)) := [(⟨0, by decide⟩, hstPoolOdds_3)]
def hsBranches_1 : List (Wire 128 × List (Fin 4)) := hsBranchesIdx_1.map fun p =>
    (scr20_128 p.1, p.2)
def hsFlipsIdx_1 : List (Fin 20) := []
def hsFlips_1 : List (Wire 128) := hsFlipsIdx_1.map scr20_128
def cHsSplit_1 : Circuit 128 := cPmSplit 40 hsBranches_1 hsFlips_1 wPmPar_128 (rK_128 ⟨4,
    by decide⟩)
def hsBranchesIdx_2 : List (Fin 20 × List (Fin 4)) :=
  [(⟨0, by decide⟩, hstPoolOdds_4), (⟨2, by decide⟩, hstPoolOdds_5), (⟨1, by decide⟩,
    hstPoolOdds_6)]
def hsBranches_2 : List (Wire 128 × List (Fin 4)) := hsBranchesIdx_2.map fun p =>
    (scr20_128 p.1, p.2)
def hsFlipsIdx_2 : List (Fin 20) := []
def hsFlips_2 : List (Wire 128) := hsFlipsIdx_2.map scr20_128
def cHsSplit_2 : Circuit 128 := cPmSplit 44 hsBranches_2 hsFlips_2 wPmPar_128 (rK_128 ⟨3,
    by decide⟩)
def hsBranchesIdx_3 : List (Fin 20 × List (Fin 4)) :=
  [(⟨0, by decide⟩, hstPoolOdds_7), (⟨3, by decide⟩, hstPoolOdds_8), (⟨2, by decide⟩,
    hstPoolOdds_9), (⟨4, by decide⟩, hstPoolOdds_10), (⟨1, by decide⟩, hstPoolOdds_11)]
def hsBranches_3 : List (Wire 128 × List (Fin 4)) := hsBranchesIdx_3.map fun p =>
    (scr20_128 p.1, p.2)
def hsFlipsIdx_3 : List (Fin 20) := []
def hsFlips_3 : List (Wire 128) := hsFlipsIdx_3.map scr20_128
def cHsSplit_3 : Circuit 128 := cPmSplit 47 hsBranches_3 hsFlips_3 wPmPar_128 (rK_128 ⟨2,
    by decide⟩)
def hsBranchesIdx_4 : List (Fin 20 × List (Fin 4)) :=
  [(⟨0, by decide⟩, hstPoolOdds_12), (⟨6, by decide⟩, hstPoolOdds_13), (⟨3, by decide⟩,
    hstPoolOdds_14), (⟨7, by decide⟩, hstPoolOdds_15), (⟨2, by decide⟩, hstPoolOdds_16), (⟨8,
    by
      decide⟩, hstPoolOdds_17), (⟨4, by decide⟩, hstPoolOdds_18), (⟨9, by decide⟩, hstPoolOdds_19),
    (⟨10, by decide⟩, hstPoolOdds_20)]
def hsBranches_4 : List (Wire 128 × List (Fin 4)) := hsBranchesIdx_4.map fun p =>
    (scr20_128 p.1, p.2)
def hsFlipsIdx_4 : List (Fin 20) := [⟨1, by decide⟩]
def hsFlips_4 : List (Wire 128) := hsFlipsIdx_4.map scr20_128
def cHsSplit_4 : Circuit 128 := cPmSplit 47 hsBranches_4 hsFlips_4 wPmPar_128 (rK_128 ⟨1,
    by decide⟩)
def hsBranchesIdx_5 : List (Fin 20 × List (Fin 4)) :=
  [(⟨0, by decide⟩, hstPoolOdds_21), (⟨11, by decide⟩, hstPoolOdds_22), (⟨6, by decide⟩,
    hstPoolOdds_23), (⟨12, by decide⟩, hstPoolOdds_24), (⟨3, by decide⟩, hstPoolOdds_25), (⟨13,
    by
      decide⟩, hstPoolOdds_26), (⟨7, by decide⟩, hstPoolOdds_27), (⟨14, by decide⟩, hstPoolOdds_28),
    (⟨2, by decide⟩, hstPoolOdds_29), (⟨15, by decide⟩, hstPoolOdds_30), (⟨8, by decide⟩,
    hstPoolOdds_31), (⟨16, by decide⟩, hstPoolOdds_32), (⟨4, by decide⟩, hstPoolOdds_33), (⟨17,
    by
      decide⟩, hstPoolOdds_34), (⟨9, by decide⟩, hstPoolOdds_35), (⟨18, by decide⟩, hstPoolOdds_36),
    (⟨10, by decide⟩, hstPoolOdds_37), (⟨19, by decide⟩, hstPoolOdds_38), (⟨5, by decide⟩,
    hstPoolOdds_39)]
def hsBranches_5 : List (Wire 128 × List (Fin 4)) := hsBranchesIdx_5.map fun p =>
    (scr20_128 p.1, p.2)
def hsFlipsIdx_5 : List (Fin 20) := [⟨1, by decide⟩]
def hsFlips_5 : List (Wire 128) := hsFlipsIdx_5.map scr20_128
def cHsSplit_5 : Circuit 128 := cPmSplit 47 hsBranches_5 hsFlips_5 wPmPar_128 (rK_128 ⟨0,
    by decide⟩)
def cHsDepth5 : Circuit 128 := cHsSplit_5
def cHsFork_4_9 : Circuit 128 := cHsDepth5
def cHsFork_4_8 : Circuit 128 := withUnaryFork (scr20_128 ⟨10, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨19, by decide⟩) cHsFork_4_9
def cHsFork_4_7 : Circuit 128 := withUnaryFork (scr20_128 ⟨9, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨18, by decide⟩) cHsFork_4_8
def cHsFork_4_6 : Circuit 128 := withUnaryFork (scr20_128 ⟨4, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨17, by decide⟩) cHsFork_4_7
def cHsFork_4_5 : Circuit 128 := withUnaryFork (scr20_128 ⟨8, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨16, by decide⟩) cHsFork_4_6
def cHsFork_4_4 : Circuit 128 := withUnaryFork (scr20_128 ⟨2, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨15, by decide⟩) cHsFork_4_5
def cHsFork_4_3 : Circuit 128 := withUnaryFork (scr20_128 ⟨7, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨14, by decide⟩) cHsFork_4_4
def cHsFork_4_2 : Circuit 128 := withUnaryFork (scr20_128 ⟨3, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨13, by decide⟩) cHsFork_4_3
def cHsFork_4_1 : Circuit 128 := withUnaryFork (scr20_128 ⟨6, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨12, by decide⟩) cHsFork_4_2
def cHsFork_4_0 : Circuit 128 := withUnaryFork (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨1, by decide⟩)
    (scr20_128 ⟨11, by decide⟩) cHsFork_4_1
def cHsDepth4 : Circuit 128 := cHsSplit_4 ;;ᶜ cHsFork_4_0
def cHsFork_3_5 : Circuit 128 := cHsDepth4
def cHsFork_3_4 : Circuit 128 := withUnaryFork (scr20_128 ⟨1, by decide⟩) (rK_128 ⟨2, by decide⟩)
    (scr20_128 ⟨10, by decide⟩) cHsFork_3_5
def cHsFork_3_3 : Circuit 128 := withUnaryFork (scr20_128 ⟨4, by decide⟩) (rK_128 ⟨2, by decide⟩)
    (scr20_128 ⟨9, by decide⟩) cHsFork_3_4
def cHsFork_3_2 : Circuit 128 := withUnaryFork (scr20_128 ⟨2, by decide⟩) (rK_128 ⟨2, by decide⟩)
    (scr20_128 ⟨8, by decide⟩) cHsFork_3_3
def cHsFork_3_1 : Circuit 128 := withUnaryFork (scr20_128 ⟨3, by decide⟩) (rK_128 ⟨2, by decide⟩)
    (scr20_128 ⟨7, by decide⟩) cHsFork_3_2
def cHsFork_3_0 : Circuit 128 := withUnaryFork (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨2, by decide⟩)
    (scr20_128 ⟨6, by decide⟩) cHsFork_3_1
def cHsDepth3 : Circuit 128 := cHsSplit_3 ;;ᶜ cHsFork_3_0
def cHsFork_2_3 : Circuit 128 := cHsDepth3
def cHsFork_2_2 : Circuit 128 := withUnaryFork (scr20_128 ⟨1, by decide⟩) (rK_128 ⟨3, by decide⟩)
    (scr20_128 ⟨5, by decide⟩) cHsFork_2_3
def cHsFork_2_1 : Circuit 128 := withUnaryFork (scr20_128 ⟨2, by decide⟩) (rK_128 ⟨3, by decide⟩)
    (scr20_128 ⟨4, by decide⟩) cHsFork_2_2
def cHsFork_2_0 : Circuit 128 := withUnaryFork (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨3, by decide⟩)
    (scr20_128 ⟨3, by decide⟩) cHsFork_2_1
def cHsDepth2 : Circuit 128 := cHsSplit_2 ;;ᶜ cHsFork_2_0
def cHsFork_1_1 : Circuit 128 := cHsDepth2
def cHsFork_1_0 : Circuit 128 := withUnaryFork (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨4, by decide⟩)
    (scr20_128 ⟨2, by decide⟩) cHsFork_1_1
def cHsDepth1 : Circuit 128 := cHsSplit_1 ;;ᶜ cHsFork_1_0
def cHsFork_0_1 : Circuit 128 := cHsDepth1
def cHsFork_0_0 : Circuit 128 := withUnaryFork (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨5, by decide⟩)
    (scr20_128 ⟨1, by decide⟩) cHsFork_0_1
def cHsDepth0 : Circuit 128 := cHsSplit_0 ;;ᶜ cHsFork_0_0
def cHeadShell64PmSbm_128 : Circuit 128 :=
  cnotIf wEnHead_128 (scr30_128 ⟨0, by decide⟩) ;;ᶜ
  cHsDepth0 ;;ᶜ
  cnotIf wEnHead_128 (scr30_128 ⟨0, by decide⟩)
noncomputable def cLeafHeadShell64 : Circuit 128 := lockPosPostVal cHeadShell64PmSbm_128
def cOpen_128 : Circuit 128 :=
  computeEnPos wCoin1_128 wCoin2_128 wEnPos_128 ;;ᶜ
  andComputeIf wEnPos_128 wCoin0_128 wEnS0_128 ;;ᶜ
  cnotIf wEnPos_128 wEnC0_128 ;;ᶜ
  cnotIf wEnS0_128 wEnC0_128
def cFlags2_128 : Circuit 128 :=
  andComputeIf wEnPos_128 wIsHead_128 wEnHead_128 ;;ᶜ
  cnotIf wEnPos_128 wEnTail_128 ;;ᶜ
  cnotIf wEnHead_128 wEnTail_128 ;;ᶜ
  andComputeIf wEnS0_128 wEnTail_128 wEnS0Tail_128 ;;ᶜ
  andComputeIf wEnC0_128 wIsHead_128 wEnC0Head_128 ;;ᶜ
  cnotIf wEnPos_128 wEnAnc_128 ;;ᶜ
  cnotIf wEnC0Head_128 wEnAnc_128 ;;ᶜ
  (andComputeIf wEnC0_128 wIsHead_128 wEnC0Head_128).inverse
def headMap67In128 (i : Fin 67) : Wire 128 := if _h0 : i.val = 0 then wEnHead_128 else if h37
    : i.val < 37 then wP80_128 (rHeadAct37In80 ⟨i.val, h37⟩) else scr30_128
    ⟨i.val - 37, by omega⟩
theorem headMap67In128_val_of_zero {i : Fin 67} (hi0 : i.val = 0) :
    (headMap67In128 i).val = 119 := by
  simp only [headMap67In128, hi0, ↓reduceDIte, wEnHead_128]
theorem headMap67In128_val_of_lt37 {i : Fin 67} (hi0 : i.val ≠ 0) (hi37 : i.val < 37) :
    (headMap67In128 i).val = 6 + (rHeadAct37In80 ⟨i.val, hi37⟩).val := by
  simp only [headMap67In128, hi0, hi37, ↓reduceDIte, wP80_128]
theorem headMap67In128_val_of_ge37 {i : Fin 67} (hi0 : i.val ≠ 0) (hi37 : ¬ i.val < 37) :
    (headMap67In128 i).val = 86 + (i.val - 37) := by
  simp only [headMap67In128, hi0, hi37, ↓reduceDIte, scr30_128,
    PosPostPrep80MergedVepS3Alt.qreg_block_apply]
theorem headMap67In128_injective : Function.Injective headMap67In128 := by
  have hlt116 {k : Fin 67} (hk : k.val ≠ 0) : (headMap67In128 k).val < 116 := by
    by_cases hk37 : k.val < 37
    · have := (rHeadAct37In80 ⟨k.val, hk37⟩).isLt
      linarith [headMap67In128_val_of_lt37 hk hk37]
    · rw [headMap67In128_val_of_ge37 hk hk37]
      have := k.isLt
      omega
  intro i j hij
  have hv := congrArg Fin.val hij
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
  · exact Fin.ext (by omega)
  · linarith [hlt116 hj0, headMap67In128_val_of_zero hi0]
  · linarith [hlt116 hi0, headMap67In128_val_of_zero hj0]
  · by_cases hi37 : i.val < 37 <;> by_cases hj37 : j.val < 37
    · rw [headMap67In128_val_of_lt37 hi0 hi37, headMap67In128_val_of_lt37 hj0 hj37] at hv
      have harg : (⟨i.val, hi37⟩ : Fin 37) = ⟨j.val, hj37⟩ :=
        rHeadAct37In80.wires.injective (Fin.ext (by omega))
      exact Fin.ext (congrArg (Fin.val : Fin 37 → ℕ) harg)
    · rw [headMap67In128_val_of_lt37 hi0 hi37, headMap67In128_val_of_ge37 hj0 hj37] at hv
      have := (rHeadAct37In80 ⟨i.val, hi37⟩).isLt
      omega
    · rw [headMap67In128_val_of_ge37 hi0 hi37, headMap67In128_val_of_lt37 hj0 hj37] at hv
      have := (rHeadAct37In80 ⟨j.val, hj37⟩).isLt
      omega
    · rw [headMap67In128_val_of_ge37 hi0 hi37, headMap67In128_val_of_ge37 hj0 hj37] at hv
      exact Fin.ext (by omega)
def rHead67_128 : QRegister 67 128 where
  wires := ⟨headMap67In128, headMap67In128_injective⟩
noncomputable def cLeafHeadCoordXor : Circuit 128 :=
  lockPosPostVal (headCoordXorLocal67.onRegister rHead67_128)
set_option maxRecDepth 2000000
set_option exponentiation.threshold 256
def toffIf {n : ℕ} (c1 c2 targ : Wire n) : Circuit n := if h12 : c1 = c2 then Circuit.identity
    else if h1t : c1 = targ then Circuit.identity else if h2t : c2 = targ then
    Circuit.identity else Circuit.TOFF c1 c2 targ h12 h1t h2t
@[scoped simp] theorem count_t_toffIf {n : ℕ} (c1 c2 targ : Wire n) :
    (toffIf c1 c2 targ).count PrimitiveGate.T = 0 := by
  unfold toffIf; split_ifs <;> rfl
def cczIf {n : ℕ} (c1 c2 targ : Wire n) : Circuit n :=
  Circuit.H targ ;;ᶜ toffIf c1 c2 targ ;;ᶜ Circuit.H targ
@[scoped simp] theorem count_t_cczIf {n : ℕ} (c1 c2 targ : Wire n) :
    (cczIf c1 c2 targ).count PrimitiveGate.T = 0 := by simp [cczIf]
def cFinishXorToff_128 (isMerged218 : Bool) : Circuit 128 :=
  let ctrlDp := if isMerged218 then wEnS0Tail_128 else wEnTail_128
  toffIf ctrlDp (rB1_128 ⟨0, by decide⟩) (wP80_128 ⟨75, by decide⟩) ;;ᶜ
  toffIf ctrlDp (rB1_128 ⟨1, by decide⟩) (wP80_128 ⟨76, by decide⟩) ;;ᶜ
  toffIf ctrlDp (rB1_128 ⟨2, by decide⟩) (wP80_128 ⟨77, by decide⟩) ;;ᶜ
  toffIf wEnS0_128 (rB0_128 ⟨0, by decide⟩) (rB1_128 ⟨0, by decide⟩) ;;ᶜ
  toffIf wEnS0_128 (rB0_128 ⟨1, by decide⟩) (rB1_128 ⟨1, by decide⟩) ;;ᶜ
  toffIf wEnS0_128 (rB0_128 ⟨2, by decide⟩) (rB1_128 ⟨2, by decide⟩)
@[scoped simp] theorem count_t_cFinishXorToff (isMerged218 : Bool) :
    (cFinishXorToff_128 isMerged218).count PrimitiveGate.T = 0 := by simp [cFinishXorToff_128]
def wSubReject_128 : Wire 128 := ⟨68, by decide⟩
theorem joint33Map_lt (i : Fin 33) : (if i.val < 3 then 6 + i.val else 35 + i.val) < 128 := by
  split_ifs <;> omega
def joint33Wire (i : Fin 33) : Wire 128 := ⟨if i.val < 3 then 6 + i.val else 35 + i.val,
    joint33Map_lt i⟩
theorem joint33Wire_injective : Function.Injective joint33Wire := fun _ _ h ↦ by
  have hv := congrArg Fin.val h
  dsimp [joint33Wire] at hv
  split_ifs at hv <;> exact Fin.ext (by omega)
def rJoint33_128 : QRegister 33 128 where wires := ⟨joint33Wire, joint33Wire_injective⟩
theorem rJoint33_payload_not36 (i : Fin 33) :
    6 ≤ (rJoint33_128 i).val ∧ (rJoint33_128 i).val < 86 ∧ (rJoint33_128 i).val ≠ 36 := by
  dsimp [rJoint33_128, joint33Wire]
  split_ifs <;> omega
def rJoint16_128 : QRegister 16 128 := QRegister.block 12 16 (by decide)
theorem rJoint16_payload_not36 (i : Fin 16) :
    6 ≤ (rJoint16_128 i).val ∧ (rJoint16_128 i).val < 86 ∧ (rJoint16_128 i).val ≠ 36 := by
  dsimp [rJoint16_128, PosPostPrep80MergedVepS3Alt.qreg_block_apply]
  omega
def rest21Wire (i : Fin 21) : Wire 128 := ⟨if i.val < 8 then 28 + i.val else if i.val < 15
    then 60 + i.val else if i.val < 17 then 61 + i.val else 64 + i.val, by split_ifs <;> omega⟩
def rRest21_128 : QRegister 21 128 where
  wires := ⟨rest21Wire, fun _ _ h ↦ by
    have hv := congrArg Fin.val h
    dsimp [rest21Wire] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩
theorem rRest21_payload_not36 (i : Fin 21) :
    6 ≤ (rRest21_128 i).val ∧ (rRest21_128 i).val < 86 ∧ (rRest21_128 i).val ≠ 36 := by
  dsimp [rRest21_128, rest21Wire]
  split_ifs <;> omega
def mThresh4 : Fin 4 → ℕ := ![771830103, 814177451, 796552300, 784365019]
def kAdd4 (k : Fin 4) : ℕ := 2 ^ 30 - mThresh4 k
theorem mThresh4_pos (k : Fin 4) : 0 < mThresh4 k := by fin_cases k <;> decide
theorem mThresh4_le_pow30 (k : Fin 4) : mThresh4 k ≤ 2 ^ 30 := by fin_cases k <;> decide
theorem kAdd4_lt_pow30 (k : Fin 4) : kAdd4 k < 2 ^ 30 := by fin_cases k <;> decide
def natBit (x i : ℕ) : ℕ := (x / 2 ^ i) % 2
def z2Bit (x i : ℕ) : ZMod 2 := ((natBit x i : ℕ) : ZMod 2)
theorem natBit_zero_or_one (x i : ℕ) : natBit x i = 0 ∨ natBit x i = 1 := by
  dsimp [natBit]; omega
def natCarry (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (natBit a i + natBit b i + natCarry a b i) / 2
theorem mod_pow_succ_two (x n : ℕ) : x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * natBit x n := by
  have hdiv : x / 2 ^ n = natBit x n + 2 * ((x / 2 ^ n) / 2) := by
    dsimp [natBit]
    omega
  have hlt : x % 2 ^ n + 2 ^ n * natBit x n < 2 ^ n * 2 := by
    have := Nat.mod_lt x (Nat.two_pow_pos n)
    rcases natBit_zero_or_one x n with h | h <;> simp only [h] <;> omega
  conv_lhs => rw [pow_succ, ← Nat.mod_add_div x (2 ^ n), hdiv]
  rw [show x % 2 ^ n + 2 ^ n * (natBit x n + 2 * (x / 2 ^ n / 2)) =
    (x % 2 ^ n + 2 ^ n * natBit x n) + (x / 2 ^ n / 2) * (2 ^ n * 2) by ring,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
theorem natCarry_eq_div_pow (a b : ℕ) :
    ∀ n : ℕ, natCarry a b n = ((a % 2 ^ n) + (b % 2 ^ n)) / 2 ^ n
  | 0 => by simp [natCarry, Nat.mod_one]
  | n + 1 => by
      have hp : 0 < 2 ^ n := Nat.two_pow_pos n
      have hdiv_step : (a % 2 ^ (n + 1) + b % 2 ^ (n + 1)) / 2 ^ n = natBit a n + natBit b n +
          (a % 2 ^ n + b % 2 ^ n) / 2 ^ n := by
        rw [mod_pow_succ_two a n, mod_pow_succ_two b n,
          show (a % 2 ^ n + 2 ^ n * natBit a n) + (b % 2 ^ n + 2 ^ n * natBit b n) =
            (a % 2 ^ n + b % 2 ^ n) + (natBit a n + natBit b n) * 2 ^ n by ring,
          Nat.add_mul_div_right _ _ hp]
        omega
      rw [natCarry, natCarry_eq_div_pow a b n, ← hdiv_step, Nat.div_div_eq_div_mul, ← pow_succ]
theorem natCarry_zero_or_one (a b n : ℕ) : natCarry a b n = 0 ∨ natCarry a b n = 1 := by
  have hp := Nat.two_pow_pos n
  have hlt : natCarry a b n < 2 := by
    rw [natCarry_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by linarith [Nat.mod_lt a hp, Nat.mod_lt b hp])
  omega
theorem natCarry_kAdd4_eq_zero_iff {fine : ℕ} (hfine : fine < 2 ^ 30) (k : Fin 4) :
    natCarry fine (kAdd4 k) 30 = 0 ↔ fine < mThresh4 k := by
  rw [natCarry_eq_div_pow, Nat.mod_eq_of_lt hfine, Nat.mod_eq_of_lt (kAdd4_lt_pow30 k)]
  have := mThresh4_pos k
  have := mThresh4_le_pow30 k
  dsimp [kAdd4]
  refine ⟨fun h0 ↦ by_contra fun hge ↦ ?_, fun _ ↦ Nat.div_eq_of_lt (by omega)⟩
  have := Nat.div_pos (by omega : 2 ^ 30 ≤ fine + (2 ^ 30 - mThresh4 k)) (Nat.two_pow_pos 30)
  omega
theorem z2_maj_eq_nat_carry {a b c : ℕ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) : (((a + b + c) / 2 : ℕ) : ZMod 2) = ((a : ZMod 2) + (c : ZMod 2)) *
    ((b : ZMod 2) + (c : ZMod 2)) + (c : ZMod 2) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide
theorem bitsVal_lt_two_pow {m : ℕ} (γ : BitAssignment m) :
    Pos24HeadCoordXor80.bitsVal γ < 2 ^ m := by
  induction m with
  | zero => simp [Pos24HeadCoordXor80.bitsVal]
  | succ m ih =>
      unfold Pos24HeadCoordXor80.bitsVal at ih ⊢
      rw [Fin.sum_univ_castSucc, Fin.val_last, pow_succ]
      have := ih (fun i ↦ γ i.castSucc)
      have : (γ (Fin.last m)).val * 2 ^ m ≤ 1 * 2 ^ m :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (ZMod.val_lt _))
      simp only [Fin.val_castSucc]
      omega
structure Anf4 where
  c0 : ZMod 2
  cd : ZMod 2
  cm : ZMod 2
  cmp : ZMod 2
  deriving DecidableEq
def anfZero : Anf4 := ⟨0, 0, 0, 0⟩
def anfOne : Anf4 := ⟨1, 0, 0, 0⟩
def anfXor (a b : Anf4) : Anf4 := ⟨a.c0 + b.c0, a.cd + b.cd, a.cm + b.cm, a.cmp + b.cmp⟩
def evalAnf4 (a : Anf4) (par maj : ZMod 2) : ZMod 2 :=
  a.c0 + a.cd * par + a.cm * maj + a.cmp * (maj * par)
theorem evalAnf4_zero (par maj : ZMod 2) : evalAnf4 anfZero par maj = 0 := by
  simp [evalAnf4, anfZero]
theorem evalAnf4_one (par maj : ZMod 2) : evalAnf4 anfOne par maj = 1 := by simp [evalAnf4, anfOne]
theorem evalAnf4_anfXor (a b : Anf4) (par maj : ZMod 2) :
    evalAnf4 (anfXor a b) par maj = evalAnf4 a par maj + evalAnf4 b par maj := by
  dsimp [evalAnf4, anfXor]; ring
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by decide +revert
def pop3Idx (d0 d1 d2 : ZMod 2) : Fin 4 :=
  ⟨d0.val + d1.val + d2.val, by linarith [ZMod.val_lt d0, ZMod.val_lt d1, ZMod.val_lt d2]⟩
def anfOfStage (i : ℕ) : Anf4 :=
  ⟨z2Bit (kAdd4 0) i, z2Bit (kAdd4 0) i + z2Bit (kAdd4 1) i,
    z2Bit (kAdd4 0) i + z2Bit (kAdd4 2) i,
    z2Bit (kAdd4 0) i + z2Bit (kAdd4 1) i + z2Bit (kAdd4 2) i + z2Bit (kAdd4 3) i⟩
theorem evalAnf4_anfOfStage (i : ℕ) (d0 d1 d2 : ZMod 2) : evalAnf4 (anfOfStage i)
    (d0 + d1 + d2) (d0 * d1 + (d0 + d1) * d2) = z2Bit (kAdd4 (pop3Idx d0 d1 d2)) i := by
  rcases bit_cases d0 with rfl | rfl <;> rcases bit_cases d1 with rfl | rfl <;>
    rcases bit_cases d2 with rfl | rfl <;>
    simp only [evalAnf4, anfOfStage, pop3Idx, ZMod.val_zero, ZMod.val_one,
      zmod2_add_self, add_zero, zero_add, mul_zero, mul_one] <;>
    ring_nf <;> simp [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl]
def cPopBasis_128 : Circuit 128 :=
  let d0 := rB1_128 ⟨0, by decide⟩
  let d1 := rB1_128 ⟨1, by decide⟩
  let d2 := rB1_128 ⟨2, by decide⟩
  cnotIf d0 wPopPar_128 ;;ᶜ
  cnotIf d1 wPopPar_128 ;;ᶜ
  cnotIf d2 wPopPar_128 ;;ᶜ
  cnotIf d0 d1 ;;ᶜ
  cnotIf d0 d2 ;;ᶜ
  andComputeIf d1 d2 wPopMaj_128 ;;ᶜ
  cnotIf d0 d1 ;;ᶜ
  cnotIf d0 d2 ;;ᶜ
  cnotIf d0 wPopMaj_128 ;;ᶜ
  andComputeIf wPopMaj_128 wPopPar_128 wBrTop_128
@[scoped simp] theorem count_toff_cPopBasis_128 : cPopBasis_128.count PrimitiveGate.TOFF = 0 := by
  simp [cPopBasis_128]
def emitSigXor_128 (δ : Anf4) : Circuit 128 :=
  (if δ.c0 = 1 then Circuit.X wPopT01_128 else Circuit.identity) ;;ᶜ
  (if δ.cd = 1 then cnotIf wPopPar_128 wPopT01_128 else Circuit.identity) ;;ᶜ
  (if δ.cm = 1 then cnotIf wPopMaj_128 wPopT01_128 else Circuit.identity) ;;ᶜ
  (if δ.cmp = 1 then cnotIf wBrTop_128 wPopT01_128 else Circuit.identity)
@[scoped simp] theorem count_toff_emitSigXor_128 (δ : Anf4) :
    (emitSigXor_128 δ).count PrimitiveGate.TOFF = 0 := by
  dsimp [emitSigXor_128]
  repeat' (split_ifs <;> simp)
@[scoped simp] theorem count_t_emitSigXor_128 (δ : Anf4) :
    (emitSigXor_128 δ).count PrimitiveGate.T = 0 := by
  dsimp [emitSigXor_128]
  repeat' (split_ifs <;> simp)
def carryPrefix : (k : ℕ) → k ≤ 30 → Circuit 128 × Anf4
  | 0, _ => (Circuit.identity, anfZero)
  | i + 1, hi =>
      let prev := carryPrefix i (Nat.le_of_succ_le hi)
      let fi := rFine30_128 ⟨i, hi⟩
      let ciOut := scr30_128 ⟨i, hi⟩
      let a := anfOfStage i
      if h0 : i = 0 then
        (prev.1 ;;ᶜ emitSigXor_128 (anfXor prev.2 a) ;;ᶜ
          andComputeIf fi wPopT01_128 ciOut, a)
      else
        let ciIn := scr30_128 ⟨i - 1, by omega⟩
        if a = anfZero then
          (prev.1 ;;ᶜ andComputeIf fi ciIn ciOut, prev.2)
        else if a = anfOne then
          (prev.1 ;;ᶜ (Circuit.X fi ;;ᶜ andComputeIf fi ciIn ciOut ;;ᶜ
            Circuit.X fi ;;ᶜ cnotIf fi ciOut), prev.2)
        else
          (prev.1 ;;ᶜ emitSigXor_128 (anfXor prev.2 a) ;;ᶜ
            (cnotIf ciIn fi ;;ᶜ cnotIf ciIn wPopT01_128 ;;ᶜ
              andComputeIf fi wPopT01_128 ciOut ;;ᶜ
              cnotIf ciIn fi ;;ᶜ cnotIf ciIn wPopT01_128 ;;ᶜ
              cnotIf ciIn ciOut), a)
def cCarry32_128 : Circuit 128 :=
  let p30 := carryPrefix 30 le_rfl
  cPopBasis_128 ;;ᶜ p30.1 ;;ᶜ emitSigXor_128 p30.2
theorem count_toff_carryPrefix : ∀ (k : ℕ) (hk : k ≤ 30),
    (carryPrefix k hk).1.count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | i + 1, hi => by
      have ih := count_toff_carryPrefix i (Nat.le_of_succ_le hi)
      have hX : (Circuit.X (rFine30_128 ⟨i, hi⟩)).count PrimitiveGate.TOFF = 0 := rfl
      dsimp only [carryPrefix]
      split_ifs <;> simp [ih, hX]
@[scoped simp] theorem count_toff_cCarry32_128 : cCarry32_128.count PrimitiveGate.TOFF = 0 := by
  simp [cCarry32_128, count_toff_carryPrefix]
def hadamardReg {n : ℕ} : (m : ℕ) → QRegister m n → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, r => Circuit.H (r (Fin.last m)) ;;ᶜ hadamardReg m (qregInit r)
@[scoped simp] theorem count_t_hadamardReg {n : ℕ} : ∀ (m : ℕ) (r : QRegister m n),
    (hadamardReg m r).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, r => by simp [hadamardReg, count_t_hadamardReg m (qregInit r)]
@[scoped simp] theorem count_toff_hadamardReg {n : ℕ} : ∀ (m : ℕ) (r : QRegister m n),
    (hadamardReg m r).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, r => by simp [hadamardReg, count_toff_hadamardReg m (qregInit r)]
def cSGood34_128 (auxGood : Bool) : Circuit 128 :=
  let c29 := scr30_128 ⟨29, by decide⟩
  let flipSub := if auxGood then Circuit.identity else Circuit.X wSubReject_128
  cCarry32_128 ;;ᶜ
  flipSub ;;ᶜ
  Circuit.X c29 ;;ᶜ
  cczIf wEnTail_128 wSubReject_128 c29 ;;ᶜ
  Circuit.X c29 ;;ᶜ
  flipSub ;;ᶜ
  cCarry32_128.inverse
def zeroRefl34Wire (k : Fin 34) : Wire 128 :=
  if hk : k.val < 33 then rJoint33_128 ⟨k.val, hk⟩ else wSubReject_128
theorem zeroRefl34Wire_val_le68 (k : Fin 34) : (zeroRefl34Wire k).val ≤ 68 := by
  have hj33 (x : Fin 33) : (rJoint33_128 x).val = if x.val < 3 then 6 + x.val else 35 + x.val := rfl
  dsimp only [zeroRefl34Wire]
  split_ifs <;> simp only [hj33, show wSubReject_128.val = 68 from rfl] <;>
    (try split_ifs) <;> omega
def xPrefix34 : (k : ℕ) → k ≤ 34 → Circuit 128
  | 0, _ => Circuit.identity
  | k + 1, hk => xPrefix34 k (Nat.le_of_succ_le hk) ;;ᶜ Circuit.X (zeroRefl34Wire ⟨k, hk⟩)
def zAccWire (m : ℕ) (hm : m ≤ 32) : Wire 128 :=
  if m = 0 then wEnTail_128
  else if h30 : m ≤ 30 then scr30_128 ⟨m - 1, by omega⟩
  else if m = 31 then wPopT01_128
  else wPopMaj_128
theorem zAccWire_val_ge86 (m : ℕ) (hm : m ≤ 32) : 86 ≤ (zAccWire m hm).val := by
  dsimp only [zAccWire]
  split_ifs <;>
    (try dsimp [wEnTail_128, wPopT01_128, wPopMaj_128, scr30_128,
      PosPostPrep80MergedVepS3Alt.qreg_block_apply]) <;>
    omega
theorem zAccWire_eq_iff {m₁ m₂ : ℕ} (h₁ : m₁ ≤ 32) (h₂ : m₂ ≤ 32) :
    zAccWire m₁ h₁ = zAccWire m₂ h₂ ↔ m₁ = m₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  have hv := congrArg Fin.val h
  dsimp only [zAccWire] at hv
  split_ifs at hv <;>
    (try dsimp [wEnTail_128, wPopT01_128, wPopMaj_128, scr30_128,
      PosPostPrep80MergedVepS3Alt.qreg_block_apply] at hv) <;>
    omega
def zAndPrefix : (m : ℕ) → m ≤ 32 → Circuit 128
  | 0, _ => Circuit.identity
  | m + 1, hm =>
      zAndPrefix m (Nat.le_of_succ_le hm) ;;ᶜ
      andComputeIf (zAccWire m (Nat.le_of_succ_le hm))
        (zeroRefl34Wire ⟨m, by omega⟩) (zAccWire (m + 1) hm)
def cZeroReflSetup_128 : Circuit 128 := xPrefix34 34 le_rfl ;;ᶜ zAndPrefix 32 le_rfl
def cZeroRefl34_128 : Circuit 128 :=
  cZeroReflSetup_128 ;;ᶜ
  cczIf wPopMaj_128 (rJoint33_128 ⟨32, by decide⟩) wSubReject_128 ;;ᶜ
  cZeroReflSetup_128.inverse ;;ᶜ
  Circuit.Z wEnTail_128
def cPrepA_128 (w : List HSTGate) : Circuit 128 :=
  hadamardReg 33 rJoint33_128 ;;ᶜ ctrlProbIf w wEnTail_128 wSubReject_128
def cJointTailBhmt_128 (w : List HSTGate) (auxGood : Bool) : Circuit 128 :=
  ctrlProbIf w wEnTail_128 wSubReject_128 ;;ᶜ
  cSGood34_128 auxGood ;;ᶜ
  (cPrepA_128 w).inverse ;;ᶜ
  cZeroRefl34_128 ;;ᶜ
  cPrepA_128 w ;;ᶜ
  (if auxGood then cnotIf wEnTail_128 wSubReject_128 else Circuit.identity)
@[scoped simp] theorem count_toff_cPrepA (w : List HSTGate) :
    (cPrepA_128 w).count PrimitiveGate.TOFF = 0 := by simp [cPrepA_128]
section SecJointTailCardAndBridge
set_option exponentiation.threshold 28
theorem card_prod_lt {α : Type*} [Fintype α] {N : ℕ} (f : α → ℕ) (hf : ∀ a, f a ≤ N) :
    (Finset.univ.filter (fun p : α × Fin N ↦ p.2.val < f p.1)).card = ∑ a : α, f a := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, ← Finset.card_fin (f a)]
  exact Finset.card_bij (fun x hx ↦ ⟨x.val, (Finset.mem_filter.mp hx).2⟩)
    (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ Fin.ext (congrArg (Fin.val : Fin (f a) → ℕ) h))
    (fun i _ ↦ ⟨⟨i.val, i.isLt.trans_le (hf a)⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, rfl⟩)
end SecJointTailCardAndBridge
section Part53Certs
def wJointTailFast19 : List HSTGate :=
  [.T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H,
   .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H]
@[scoped simp] theorem hstWordTCount_wJointTailFast19 : hstWordTCount wJointTailFast19 = 19 := rfl
end Part53Certs
section SecJunctionCerts
def oddsJointHead218_L20 : List (Fin 4) := [0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1,
    0]
def oddsJointS2Tail218_L20 : List (Fin 4) := [1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0,
    0, 1]
def oddsJointS0Tail217_L20 : List (Fin 4) := [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    0, 0]
def oddsJointC0Head216_L20 : List (Fin 4) := [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1,
    0, 1]
def oddsJointS2Tail216_L20 : List (Fin 4) := [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0,
    1, 0]
abbrev wJointHead218_L20 : List HSTGate := oddsToHst oddsJointHead218_L20
abbrev wJointS2Tail218_L20 : List HSTGate := oddsToHst oddsJointS2Tail218_L20
abbrev wJointS0Tail217_L20 : List HSTGate := oddsToHst oddsJointS0Tail217_L20
abbrev wJointC0Head216_L20 : List HSTGate := oddsToHst oddsJointC0Head216_L20
abbrev wJointS2Tail216_L20 : List HSTGate := oddsToHst oddsJointS2Tail216_L20
end SecJunctionCerts
inductive CleanComputeProg : Type
  | id : CleanComputeProg
  | x (q : Wire 128) : CleanComputeProg
  | cnot (c t : Wire 128) : CleanComputeProg
  | tempAnd (c₁ c₂ anc : Wire 128) : CleanComputeProg
  | seq (p₁ p₂ : CleanComputeProg) : CleanComputeProg
def CleanComputeProg.toCircuit : CleanComputeProg → Circuit 128
  | .id => Circuit.identity
  | .x q => Circuit.X q
  | .cnot c t => cnotIf c t
  | .tempAnd c₁ c₂ anc => andComputeIf c₁ c₂ anc
  | .seq p₁ p₂ => p₁.toCircuit ;;ᶜ p₂.toCircuit
def CleanComputeProg.numTempAnd : CleanComputeProg → ℕ
  | .id => 0
  | .x _ => 0
  | .cnot _ _ => 0
  | .tempAnd _ _ _ => 1
  | .seq p₁ p₂ => p₁.numTempAnd + p₂.numTempAnd
def z2BitOfNat (x i : ℕ) : ZMod 2 := if ((x / 2 ^ i) % 2) == 1 then 1 else 0
def headWitnessPayload80 (b0Val nuc anc : ℕ) (k : Fin 56) (pid : Fin 6) (sm : Fin 8)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  let dH := PosSlots24SemanticBridge.pos24OhPoint (PosSlots24SemanticBridge.pos24HeadU56 k)
      (PosSlots24SemanticBridge.pos24HeadV56 k) (PosSlots24SemanticBridge.pos24HeadW56 k) pid
      sm
  let dpH := ((dH 0).val % 2) + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2)
  let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
  let b1Val := Nat.xor b0Val dpH
  fun q ↦
    let i := q.val
    if i < 3 then z2BitOfNat b1Val i else if i < 6 then z2BitOfNat b0Val (i - 3)
    else if i < 14 then z2BitOfNat nuc (i - 6) else if i < 22 then z2BitOfNat anc (i - 14)
    else if i < 30 then 0 else if i == 30 then 1 else if i == 31 then (if thresh then 1 else 0)
    else if i < 62 then z2BitOfNat fineH (i - 32) else if i == 62 then 0
    else if i < 69 then z2BitOfNat k.val (i - 63) else if i < 72 then z2BitOfNat pid.val (i - 69)
    else if i < 75 then z2BitOfNat sm.val (i - 72) else if i < 79 then 0
    else (if rej0 then 1 else 0)
def tailWitnessPayload80 (b0Val nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  let b1Val := Nat.xor b0Val dp.val
  fun q ↦
    let i := q.val
    if i < 3 then z2BitOfNat b1Val i else if i < 6 then z2BitOfNat b0Val (i - 3)
    else if i < 14 then z2BitOfNat nuc (i - 6) else if i < 22 then z2BitOfNat anc (i - 14)
    else if i < 30 then z2BitOfNat part (i - 22) else if i == 30 then 0
    else if i == 31 then (if thresh then 1 else 0) else if i < 62 then z2BitOfNat keep (i - 32)
    else if i == 62 then 0 else if i < 75 then 0 else if i < 78 then z2BitOfNat dp.val (i - 75)
    else if i == 78 then 0 else (if rej0 then 1 else 0)
def pos80SubIdx (off m : ℕ) (h : off + m ≤ 80) (j : Fin m) : Fin 80 :=
  ⟨off + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h⟩
noncomputable def pos80IdealDist (s0 : Bool) (p80 : BitAssignment 80) : ℝ :=
  let _b1Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 ⟨j.val, Nat.lt_trans j.isLt (by
    decide)⟩)
  let b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 3 3 (by decide) j))
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 6 8 (by decide) j))
  let anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j))
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j))
  let fine30 := Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ p80 (pos80SubIdx 32 30 (by decide) j))
  if p80 62 != 0 then 0
  else if p80 30 == 1 then
    let kVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ p80 (pos80SubIdx 63 6 (by decide) j))
    let pidVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 69 3 (by decide) j))
    let smVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 72 3 (by decide) j))
    let remZero := (p80 75 == 0) && (p80 76 == 0) && (p80 77 == 0) && (p80 78 == 0)
    let metaOk := if s0 then (nuc == 0) && decide (anc < 218)
      else decide (b0Val == 0) && decide (nuc < 216) && (anc == 0)
    if hk : kVal < 56 then
      if hp : pidVal < 6 then
        let k : Fin 56 := ⟨kVal, hk⟩
        let pid : Fin 6 := ⟨pidVal, hp⟩
        let sm : Fin 8 := ⟨smVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
        if remZero && metaOk && (part == 0) &&
            (p80 == headWitnessPayload80 b0Val nuc anc k pid sm (p80 31 == 1) (p80 79 == 1)) then
          if s0 then
            (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) /
              (8 * 218 * 48 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat)
          else
            (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) /
              (216 * 48 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat)
        else 0
      else 0
    else 0
  else
    let scratchZero := decide (∀ j : Fin 12, p80 (pos80SubIdx 63 12 (by decide) j) = 0) && (p80 78
      == 0)
    let dpVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 75 3 (by decide) j))
    let dp : Fin 8 := ⟨dpVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
    let metaOk := if s0 then (nuc == 0) && decide (anc < 218) && decide (part < 217)
      else (b0Val == 0) && decide (nuc < 216) && decide (anc < 218) && (part == 0)
    if scratchZero && metaOk && decide (fine30 < PosSlots24SemanticBridge.pos24TailSpan8 dp) &&
        (p80 == tailWitnessPayload80 b0Val nuc anc part dp fine30 (p80 31 == 1) (p80 79 == 1)) then
      if s0 then
        (1 : ℝ) / (8 * 218 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat)
      else
        (1 : ℝ) / (216 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat)
    else 0
def flipTailDpScratch80 (p : BitAssignment 80) : BitAssignment 80 := if p 30 == 1 then p else
    fun q ↦ if q.val == 75 then p 75 + p 0 else if q.val == 76 then p 76 + p 1 else if q.val
    == 77 then p 77 + p 2 else p q
def p80ClearCosetAndNucLocal (p : BitAssignment 80) : BitAssignment 80 :=
  fun q ↦ if 3 ≤ q.val ∧ q.val < 14 then 0 else p q
noncomputable def muSlot2Ideal216 (p : BitAssignment 80) : ℝ :=
  pos80IdealDist false (flipTailDpScratch80 p)
noncomputable def muSlot2Ideal218 (p : BitAssignment 80) : ℝ :=
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j))
  if nuc < 216 then
    (108 / 109 : ℝ) * muSlot2Ideal216 p
  else if nuc < 218 then
    (27 / 218 : ℝ) * muSlot2Ideal216 (p80ClearCosetAndNucLocal p)
  else 0
def tailKeepSpanOfDp (dp : Fin 8) : ℕ :=
  match dp.val with
  | 0 => 771830103
  | 1 | 2 | 4 => 814177451
  | 3 | 5 | 6 => 796552300
  | _ => 784365019
def p80ClearB0Local (p : BitAssignment 80) : BitAssignment 80 :=
  fun q ↦ if 3 ≤ q.val ∧ q.val < 6 then 0 else p q
def headJointPayload80 (b0Val nuc anc part : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  if hp : pidVal < 6 then
    let base := headWitnessPayload80 b0Val nuc anc k ⟨pidVal, hp⟩ sm thresh rej0
    fun q ↦ if 22 ≤ q.val ∧ q.val < 30 then z2BitOfNat part (q.val - 22) else base q
  else
    fun q ↦
      let i := q.val
      if i < 3 then z2BitOfNat b0Val i else if i < 6 then z2BitOfNat b0Val (i - 3)
      else if i < 14 then z2BitOfNat nuc (i - 6) else if i < 22 then z2BitOfNat anc (i - 14)
      else if i < 30 then z2BitOfNat part (i - 22) else if i == 30 then 1
      else if i == 31 then (if thresh then 1 else 0) else if i < 62 then 0 else if i == 62 then 0
      else if i < 69 then z2BitOfNat k.val (i - 63) else if i < 72 then z2BitOfNat pidVal (i - 69)
      else if i < 75 then z2BitOfNat sm.val (i - 72) else if i < 79 then 0
      else (if rej0 then 1 else 0)
def headGeneralPayload80 (b0Val nuc anc : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  headJointPayload80 b0Val nuc anc 0 k pidVal sm thresh rej0
theorem bitsVal_lt_two_pow_local : ∀ {m : ℕ} (γ : BitAssignment m),
    Pos24HeadCoordXor80.bitsVal γ < 2 ^ m :=
  fun γ ↦ bitsVal_lt_two_pow γ
noncomputable abbrev bhmtBranchProb (sSq goodN denom aGood aBad : ℝ)
    (good : Prop) [Decidable good] (bAux : Bool) : ℝ :=
  if !bAux then
    if good then (sSq * (3 - 4 * sSq) ^ 2) / goodN
    else ((1 - 4 * sSq) ^ 2 * aGood) / denom
  else ((1 - 4 * sSq) ^ 2 * aBad) / denom
noncomputable def jointTailSSq : ℝ :=
  ((6388384375 : ℝ) / (2 : ℝ) ^ 33) * ‖alpha0 wJointTailFast19‖ ^ 2
noncomputable def jointTailBhmtProb (dp : Fin 8) (fine30 : ℕ) (bSub : Bool) : ℝ :=
  bhmtBranchProb jointTailSSq 6388384375 ((2 : ℝ) ^ 33)
    (‖alpha0 wJointTailFast19‖ ^ 2) (‖alpha1 wJointTailFast19‖ ^ 2)
    (fine30 < tailKeepSpanOfDp dp) bSub
noncomputable def jointHeadSSq (isMerged218 s0 : Bool) : ℝ :=
  if isMerged218 || s0 then ((1308 : ℝ) / (2048 : ℝ)) * ‖alpha1 wJointHead218_L20‖ ^ 2
  else ((1296 : ℝ) / (2048 : ℝ)) * ‖alpha0 wJointC0Head216_L20‖ ^ 2
noncomputable def jointHeadBhmtProb (isMerged218 s0 : Bool) (U pidVal : ℕ) (bAux : Bool) : ℝ :=
  let sSq := jointHeadSSq isMerged218 s0
  if isMerged218 || s0 then
    bhmtBranchProb sSq 1308 2048 (‖alpha1 wJointHead218_L20‖ ^ 2)
      (‖alpha0 wJointHead218_L20‖ ^ 2) (U < 218 && pidVal < 6) bAux
  else
    bhmtBranchProb sSq 1296 2048 (‖alpha0 wJointC0Head216_L20‖ ^ 2)
      (‖alpha1 wJointC0Head216_L20‖ ^ 2) (U < 216 && pidVal < 6) bAux
noncomputable def jointSmallTailSSq (isMerged218 s0 : Bool) : ℝ := if s0 then
    ((47306 : ℝ) / (65536 : ℝ)) * ‖alpha1 wJointS0Tail217_L20‖ ^ 2 else if isMerged218 then
    ((47524 : ℝ) / (65536 : ℝ)) * ‖alpha0 wJointS2Tail218_L20‖ ^ 2 else
    ((47088 : ℝ) / (65536 : ℝ)) * ‖alpha0 wJointS2Tail216_L20‖ ^ 2
noncomputable def jointSmallTailBhmtProb (isMerged218 s0 : Bool) (U V : ℕ) (bAux : Bool) : ℝ :=
  let sSq := jointSmallTailSSq isMerged218 s0
  if s0 then
    bhmtBranchProb sSq 47306 65536 (‖alpha1 wJointS0Tail217_L20‖ ^ 2)
      (‖alpha0 wJointS0Tail217_L20‖ ^ 2) (U < 218 && V < 217) bAux
  else if isMerged218 then
    bhmtBranchProb sSq 47524 65536 (‖alpha0 wJointS2Tail218_L20‖ ^ 2)
      (‖alpha1 wJointS2Tail218_L20‖ ^ 2) (U < 218 && V < 218) bAux
  else
    bhmtBranchProb sSq 47088 65536 (‖alpha0 wJointS2Tail216_L20‖ ^ 2)
      (‖alpha1 wJointS2Tail216_L20‖ ^ 2) (U < 218 && V < 216) bAux
noncomputable def muActualFactor80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : ℝ :=
  let b0Raw := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j))
  let q := if !s0 then (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local p) else
      p80ClearB0Local p) else p
  let b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j))
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j))
  let anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j))
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j))
  let fine30 := Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ q (pos80SubIdx 32 30 (by decide) j))
  let splitWord := if s0 then isHeadS0TrueWord else isHeadS0FalseWord
  let pB0 : ℝ := if s0 then (1 / 8 : ℝ) else if isMerged218 then if (nuc &&& 216) == 216 then
      (1 / 8 : ℝ) else (if b0Raw == 0 then 1 else 0) else if b0Raw == 0 then 1 else 0
  if q 30 == 1 then
    if q 62 != 0 then 0
    else
      let kVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j))
      let pidVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 69 3 (by decide) j))
      let smVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 72 3 (by decide) j))
      let remZero := (q 75 == 0) && (q 76 == 0) && (q 77 == 0) && (q 78 == 0)
      let metaRouteOk := decide (part < 2) && (if s0 then nuc == 0 else anc == 0)
      if hk : kVal < 56 then
        let k : Fin 56 := ⟨kVal, hk⟩
        let sm : Fin 8 := ⟨smVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
        if remZero && metaRouteOk &&
            (q == headJointPayload80 b0Val nuc anc part k pidVal sm (q 31 == 1) (q 79 == 1)) then
          ‖alpha0 splitWord‖ ^ 2 * pB0 *
            jointHeadBhmtProb isMerged218 s0 (if s0 then anc else nuc) pidVal (part == 1) *
            ‖sbmAmp 6 headShell64Words ⟨kVal, bitsVal_lt_two_pow_local _⟩‖ ^ 2 *
            (1 / 8 : ℝ) * (1 / 4 : ℝ)
        else 0
      else 0
  else
    let q0 := Function.update q 62 0
    let scratchZero := decide (∀ j : Fin 12, q (pos80SubIdx 63 12 (by decide) j) = 0) && (q 78 == 0)
    let dpVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 75 3 (by decide) j))
    let dp : Fin 8 := ⟨dpVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
    let auxOk := if s0 then decide (nuc < 2) else decide (part < 2)
    if scratchZero && auxOk &&
        (q0 == tailWitnessPayload80 b0Val nuc anc part dp fine30 (q 31 == 1) (q 79 == 1)) then
      ‖alpha1 splitWord‖ ^ 2 * pB0 *
        jointSmallTailBhmtProb isMerged218 s0 anc (if s0 then part else nuc)
          (if s0 then nuc == 1 else part == 1) *
        jointTailBhmtProb dp fine30 (q 62 == 1) *
        (1 / 4 : ℝ)
    else 0
set_option maxRecDepth 2000
end ConfigPosPostPrep80MergedVepS3

end PosPostPrep80MergedVepS3
end
end ModPosPostPrep80MergedVepS3
end PosPostPrep80MergedVepS3
end
set_option exponentiation.threshold 256
end PosPostPrep80MergedVepS3Aux

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
