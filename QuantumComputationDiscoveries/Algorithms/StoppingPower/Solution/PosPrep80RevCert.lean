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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80Tail128

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosPostPrep80CertS3_p1
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80CertS3_p1 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section PosPostPrep80CertS3
local instance (priority :=
  1000000) instLoc_PosPostPrep80CertS3_1InstNeZeroTwoPowCertS3 (k : Nat) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

section ModPosPostPrep80CertS3
public section
namespace PosPostPrep80CertS3Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end PosPostPrep80CertS3Alt
namespace PosPostPrep80CertS3
section ConfigPosPostPrep80CertS3
set_option backward.isDefEq.respectTransparency true
local instance (priority :=
  1000000) instLoc_PosPostPrep80CertS3_2InstNeZeroTwoPowCert {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket sqrtHalf)
open ZeroAncillaUSPS3 hiding ket
open FullSysMomSlots0135Concrete (coinBitFin2)
open PosPostPrep80MergedVepS3
open PosPostPrep80InnerAmpS3
theorem sqrtHalf_eq_one_div_sqrt2 : (sqrtHalf : ℂ) = (1 / √(2 : ℝ) : ℂ) := by
  unfold sqrtHalf
  rw [one_div, Real.sqrt_inv]
  push_cast
  exact inv_eq_one_div _
theorem diagonal_mulVec_ket_cert {N : ℕ} (f : Fin (2 ^ N) → ℂ) (β : BitAssignment N) :
    (Matrix.diagonal f).mulVec (ket β) = f ((basisBitsEquiv N).symm β) • ket β := by
  rw [ket_eq_single_local β, Matrix.diagonal_mulVec_single]
  exact funext fun y ↦ by by_cases hy : y = (basisBitsEquiv N).symm β <;> simp [hy]
theorem embedUnitary_mulVec_ket_eq_self_of_ket {N m : ℕ} (r : QRegister m N)
    (V : Unitary (2 ^ m)) (β : BitAssignment N) (hV : V.1.mulVec (ket (fun i : Fin m ↦ β (r
    i))) = ket (fun i : Fin m ↦ β (r i))) : (r.embedUnitary V).1.mulVec (ket β) = ket β := by
  let idx := (basisBitsEquiv N).symm β
  have hext : ket (fun i : Fin m ↦ β (r i)) = Pi.single (r.extractIndex idx) (1 : ℂ) := by
    rw [ket_eq_single_local]
    refine congrArg (fun x ↦ Pi.single x (1 : ℂ))
      ((basisBitsEquiv m).injective (funext fun i ↦ ?_))
    rw [(basisBitsEquiv m).apply_symm_apply]
    change β (r i) = basisBits m (r.extractIndex idx) i
    rw [QRegister.basisBits_extractIndex, basisBits_symm_local]
  rw [hext] at hV
  rw [QRegister.embedUnitary_val, ket_eq_single_local β,
    r.embedMatrix_mulVec_single_factors V.1 idx, hV,
    ← Matrix.one_mulVec (Pi.single (r.extractIndex idx) (1 : ℂ)),
    ← r.embedMatrix_mulVec_single_factors (1 : Operator (2 ^ m)) idx,
    r.embedMatrix_one, Matrix.one_mulVec]
theorem embedAnc86_mul_coinDiag_nonPos {kSys : ℕ}
    (V : Unitary (2 ^ 86))
    (hNonPos : ∀ γ : BitAssignment 86,
      ¬(γ ⟨1, by decide⟩ = 0 ∧ γ ⟨2, by decide⟩ = 0) → V.1.mulVec (ket γ) = ket γ)
    (w₀ w₁ w₂ : Wire (kSys + 86))
    (hw₁ : w₁ = (QRegister.block kSys 86 le_rfl) ⟨1, by decide⟩)
    (hw₂ : w₂ = (QRegister.block kSys 86 le_rfl) ⟨2, by decide⟩)
    (c : Fin 8) (hc : 2 ≤ c.val) :
    let rAnc : QRegister 86 (kSys + 86) := QRegister.block kSys 86 le_rfl
    let d : Fin (2 ^ (kSys + 86)) → ℂ := fun x ↦
      (if (basisBits (kSys + 86) x w₀).val = (coinBitFin2 c 0).val then (1 : ℂ) else 0) *
      (if (basisBits (kSys + 86) x w₁).val = (coinBitFin2 c 1).val then (1 : ℂ) else 0) *
      (if (basisBits (kSys + 86) x w₂).val = (coinBitFin2 c 2).val then (1 : ℂ) else 0)
    (rAnc.embedUnitary V).1 * Matrix.diagonal d = Matrix.diagonal d := by
  intro rAnc d
  refine MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, diagonal_mulVec_ket_cert d β]
  by_cases hzero : β (rAnc ⟨1, by decide⟩) = 0 ∧ β (rAnc ⟨2, by decide⟩) = 0
  · have hnot : ¬((coinBitFin2 c 1).val = 0 ∧ (coinBitFin2 c 2).val = 0) := by
      revert c hc
      decide
    have hdx : d ((basisBitsEquiv (kSys + 86)).symm β) = 0 := by
      dsimp only [d]
      rw [congrArg ZMod.val (by rw [basisBits_symm_local, hw₁, hzero.1] : basisBits _ _ w₁ = 0),
        congrArg ZMod.val (by rw [basisBits_symm_local, hw₂, hzero.2] : basisBits _ _ w₂ = 0)]
      by_cases h1 : 0 = (coinBitFin2 c 1).val
      · simp [show 0 ≠ (coinBitFin2 c 2).val from fun h2 ↦ hnot ⟨h1.symm, h2.symm⟩]
      · simp [h1]
    rw [hdx, zero_smul, Matrix.mulVec_zero]
  · rw [Matrix.mulVec_smul, embedUnitary_mulVec_ket_eq_self_of_ket rAnc V β (hNonPos _ hzero)]
section Junction
open HermitianMat
open scoped ComplexOrder MatrixOrder
open _root_.QuantumComputation.Specs.StoppingPowerSolution (CliffProg TempPhaseProg writeRegProg
  writeRegProg_apply_reg writeRegProg_apply_of_not_mem localIdxProg embedMatrix_mulVec_ket_prog
  mul_mulVec_prog)
open MeasureBranchHadamardSem (RealizesCleanUnitary ket_projector_zero toffoli_eval_sq
  matrix_ext_ket ket_CNOT ket_TOFF)
open StreamingBchComparator (PreservesStoreConst)
open Pos24HeadCoordXor80 (isOut24Idx rOut24In67 headOutMask24 xorRegBits xorRegBits_apply_reg
  xorRegBits_apply_of_not_mem xorRegBits_comp)
inductive CliffOp76 where
  | x (q : Fin 76)
  | cnot (c t : Fin 76)
  deriving DecidableEq
inductive RevProg76 where
  | nil
  | cliff (ops : List CliffOp76)
  | seq (p₁ p₂ : RevProg76)
  | withCliff (ops : List CliffOp76) (body : RevProg76)
  | tempAnd (c₁ c₂ anc : Fin 76) (body : RevProg76)
  deriving DecidableEq
def compileCliffOp76 : CliffOp76 → CliffProg 76
  | .x q => .x q
  | .cnot c t =>
      if h : c ≠ t then .cnot c t h else .nil
theorem compileCliffOp76_cnot_ne {c t : Fin 76} (h : c ≠ t) : compileCliffOp76 (.cnot c t) =
    .cnot c t h := by simp [compileCliffOp76, h]
def compileCliff76 : List CliffOp76 → CliffProg 76
  | [] => .nil
  | op :: ops => .seq (compileCliffOp76 op) (compileCliff76 ops)
def compile76 : RevProg76 → TempPhaseProg 76
  | .nil => .nil
  | .cliff ops => .cliff (compileCliff76 ops)
  | .seq p₁ p₂ => .seq (compile76 p₁) (compile76 p₂)
  | .withCliff ops body =>
      let c := compileCliff76 ops
      .seq (.cliff c) (.seq (compile76 body) (.cliff c.inv))
  | .tempAnd c₁ c₂ anc body =>
      if h12 : c₁ ≠ c₂ then
        if h1a : c₁ ≠ anc then
          if h2a : c₂ ≠ anc then
            .tempAnd c₁ c₂ anc h12 h1a h2a (compile76 body)
          else .nil
        else .nil
      else .nil
theorem compile76_tempAnd_ne {c₁ c₂ anc : Fin 76} (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ anc)
    (h2a : c₂ ≠ anc) (body : RevProg76) :
    compile76 (.tempAnd c₁ c₂ anc body) = .tempAnd c₁ c₂ anc h12 h1a h2a (compile76 body) := by
  conv_lhs => unfold compile76
  rw [dite_eq_left_of_eq_true (eq_true h12), dite_eq_left_of_eq_true (eq_true h1a),
    dite_eq_left_of_eq_true (eq_true h2a)]
def fanOps76 : List CliffOp76 :=
  [.cnot 16 17, .cnot 16 18, .cnot 16 19, .cnot 23 24, .cnot 23 25, .cnot 23 26, .cnot 30 31,
    .cnot 30 32, .cnot 30 33]
inductive RevGate76 where
  | x (t : Fin 76)
  | cnot (c t : Fin 76)
  | toff (c1 c2 t : Fin 76)
  deriving DecidableEq
theorem compile76_evalSign_zero : ∀ (p : RevProg76) (γ : BitAssignment 76),
    (compile76 p).evalSign γ = 0
  | .nil, _ => rfl
  | .cliff _, _ => rfl
  | .seq p₁ p₂, γ => by
      simp only [compile76, TempPhaseProg.evalSign,
        compile76_evalSign_zero p₁, compile76_evalSign_zero p₂, add_zero]
  | .withCliff ops body, γ => by
      simp only [compile76, TempPhaseProg.evalSign, TempPhaseProg.evalBits,
        compile76_evalSign_zero body, add_zero]
  | .tempAnd c₁ c₂ anc body, γ => by
      dsimp only [compile76]
      split_ifs
      · simp only [TempPhaseProg.evalSign, compile76_evalSign_zero body]
      all_goals rfl
def isOut24Wire76 (w : Fin 76) : Bool := decide (13 ≤ w.val ∧ w.val < 37)
def checkWriteOut24Op76 : CliffOp76 → Bool
  | .x q => isOut24Wire76 q
  | .cnot c t => decide (c ≠ t) && !isOut24Wire76 c && isOut24Wire76 t
def checkScopedOp76 (bound : ℕ) : CliffOp76 → Bool
  | .x q => decide (q.val < bound) && !isOut24Wire76 q
  | .cnot c t =>
      decide (c ≠ t) && decide (c.val < bound) && decide (t.val < bound) &&
        !isOut24Wire76 c && !isOut24Wire76 t
def checkFanCnot76 : CliffOp76 → Bool
  | .x _ => false
  | .cnot c t => decide (c ≠ t) && isOut24Wire76 c && isOut24Wire76 t
def checkCore76 : ℕ → RevProg76 → Bool
  | _, .nil => true
  | _, .cliff ops => ops.all checkWriteOut24Op76
  | rem, .seq p₁ p₂ => checkCore76 rem p₁ && checkCore76 rem p₂
  | rem, .withCliff ops body => ops.all (checkScopedOp76 (76 - rem)) && checkCore76 rem body
  | rem, .tempAnd c₁ c₂ anc body =>
      decide (c₁ ≠ c₂) && decide (c₁ ≠ anc) && decide (c₂ ≠ anc) &&
        decide (37 ≤ anc.val) && decide (76 - rem ≤ anc.val) &&
        !isOut24Wire76 c₁ && !isOut24Wire76 c₂ && !isOut24Wire76 anc &&
        checkCore76 (76 - (anc.val + 1)) body
theorem checkFanCnot76_fanOps76 : fanOps76.all checkFanCnot76 = true := by
  decide +kernel
def RevGate76.wf : RevGate76 → Bool
  | .x _ => true
  | .cnot c t => c != t
  | .toff c1 c2 t => (c1 != c2) && (c1 != t) && (c2 != t)
def unpackMask76 (m : ℕ) : BitAssignment 76 := fun q ↦ if m.testBit q.val then 1 else 0
def stepMask76 (g : RevGate76) (m : ℕ) : ℕ :=
  match g with
  | .x t => m ^^^ (2 ^ t.val)
  | .cnot c t => if m.testBit c.val then m ^^^ (2 ^ t.val) else m
  | .toff c1 c2 t =>
      if m.testBit c1.val && m.testBit c2.val then m ^^^ (2 ^ t.val) else m
def runMask76 : List RevGate76 → ℕ → ℕ
  | [], m => m
  | g :: gs, m => runMask76 gs (stepMask76 g m)
def flattenOp76 : CliffOp76 → RevGate76
  | .x q => .x q
  | .cnot c t => .cnot c t
def flattenCliff76 (ops : List CliffOp76) : List RevGate76 := ops.map flattenOp76
def flatten76 : RevProg76 → List RevGate76
  | .nil => []
  | .cliff ops => flattenCliff76 ops
  | .seq p₁ p₂ => flatten76 p₁ ++ flatten76 p₂
  | .withCliff ops body =>
      let c := flattenCliff76 ops
      c ++ flatten76 body ++ c.reverse
  | .tempAnd c₁ c₂ anc body =>
      [.toff c₁ c₂ anc] ++ flatten76 body ++ [.toff c₁ c₂ anc]
def wfCliffOp76 : CliffOp76 → Bool
  | .x _ => true
  | .cnot c t => decide (c ≠ t)
def wfRevProg76 : RevProg76 → Bool
  | .nil => true
  | .cliff ops => ops.all wfCliffOp76
  | .seq p₁ p₂ => wfRevProg76 p₁ && wfRevProg76 p₂
  | .withCliff ops body => ops.all wfCliffOp76 && wfRevProg76 body
  | .tempAnd c₁ c₂ anc body =>
      decide (c₁ ≠ c₂) && decide (c₁ ≠ anc) && decide (c₂ ≠ anc) && wfRevProg76 body
def pack13Aux (γ : BitAssignment 76) : (k : ℕ) → k ≤ 13 → ℕ
  | 0, _ => 0
  | k' + 1, hk =>
      pack13Aux γ k' (Nat.le_of_succ_le hk) ^^^
        (if γ ⟨k', by omega⟩ = 1 then 2 ^ k' else 0)
def pack13Mask (γ : BitAssignment 76) : ℕ := pack13Aux γ 13 le_rfl
private theorem out24In67_mem_iff_isOut24Idx (q : Fin 67) :
    q ∈ rOut24In67.image ↔ isOut24Idx q.val = true := by
  rw [QRegister.mem_image]
  refine ⟨fun ⟨j, hj⟩ ↦ ?_, fun h ↦ ?_⟩
  · subst hj
    dsimp [isOut24Idx]
    rw [show (rOut24In67 j).val = 13 + j.val from rfl, decide_eq_true_eq]
    omega
  · simp only [isOut24Idx, decide_eq_true_eq] at h
    refine ⟨⟨q.val - 13, by omega⟩, Fin.ext ?_⟩
    change 13 + (q.val - 13) = q.val
    omega
theorem head67CleanMap_add_out24 (α δ : BitAssignment 67)
    (hδ : ∀ q : Fin 67, isOut24Idx q.val = false → δ q = 0) :
    head67CleanMap (α + δ) = head67CleanMap α + δ := by
  have hlo {i : ℕ} (hi : i < 13) : (α + δ) ⟨i, by omega⟩ = α ⟨i, by omega⟩ := by
    change α ⟨i, by omega⟩ + δ ⟨i, by omega⟩ = α ⟨i, by omega⟩
    rw [hδ ⟨i, by omega⟩ (by simp only [isOut24Idx, decide_eq_false_iff_not]; omega), add_zero]
  have hmask :
      headOutMask24 ((α + δ) ⟨0, by decide⟩) (fun i : Fin 6 ↦ (α + δ) ⟨1 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ (α + δ) ⟨7 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ (α + δ) ⟨10 + i.val, by omega⟩) =
      headOutMask24 (α ⟨0, by decide⟩) (fun i : Fin 6 ↦ α ⟨1 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ α ⟨7 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ α ⟨10 + i.val, by omega⟩) := by
    congr 1
    · exact hlo (by decide)
    all_goals exact funext fun _ ↦ hlo (by omega)
  funext q
  change head67CleanMap (α + δ) q = head67CleanMap α q + δ q
  unfold head67CleanMap
  rw [hmask]
  by_cases hmem : q ∈ rOut24In67.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut24In67 q).mp hmem
    rw [xorRegBits_apply_reg, xorRegBits_apply_reg]
    change (α (rOut24In67 j) + δ (rOut24In67 j)) + _ = (α (rOut24In67 j) + _) + δ (rOut24In67 j)
    ring
  · rw [xorRegBits_apply_of_not_mem _ _ _ hmem, xorRegBits_apply_of_not_mem _ _ _ hmem]
    rfl
theorem head67CleanMap_involutive (α : BitAssignment 67) :
    head67CleanMap (head67CleanMap α) = α := by
  have hlo {i : ℕ} (hi : i < 13) : head67CleanMap α ⟨i, by omega⟩ = α ⟨i, by omega⟩ :=
    xorRegBits_apply_of_not_mem _ _ _ (by
      rw [out24In67_mem_iff_isOut24Idx]
      simp only [isOut24Idx, decide_eq_true_eq]
      omega)
  have hmask :
      headOutMask24 (head67CleanMap α ⟨0, by decide⟩)
        (fun i : Fin 6 ↦ head67CleanMap α ⟨1 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ head67CleanMap α ⟨7 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ head67CleanMap α ⟨10 + i.val, by omega⟩) =
      headOutMask24 (α ⟨0, by decide⟩) (fun i : Fin 6 ↦ α ⟨1 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ α ⟨7 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ α ⟨10 + i.val, by omega⟩) := by
    congr 1
    · exact hlo (by decide)
    all_goals exact funext fun _ ↦ hlo (by omega)
  funext q
  nth_rw 1 [head67CleanMap]
  rw [hmask]
  unfold head67CleanMap
  rw [xorRegBits_comp]
  by_cases hmem : q ∈ rOut24In67.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut24In67 q).mp hmem
    rw [xorRegBits_apply_reg, CharTwo.add_self_eq_zero, add_zero]
  · exact xorRegBits_apply_of_not_mem _ _ _ hmem
private theorem inv_mul_val_cert {M : ℕ} (U : Unitary M) : (U⁻¹).1 *
    U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
theorem splitAux_PosPostPrep80CertS3_mul_assoc {M : ℕ}
    (A B C : Unitary M) : A * B * C = A * (B * C) := mul_assoc A B C
theorem splitAux_PosPostPrep80CertS3_mul_inv_rev {M : ℕ}
    (A B : Unitary M) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := _root_.mul_inv_rev A B
open Classical in
noncomputable def diagProj {N : ℕ} (S : BitAssignment N → Prop) : Matrix (Fin (2 ^ N))
    (Fin (2 ^ N)) ℂ := Matrix.diagonal (fun x ↦ if S (basisBits N x) then (1 : ℂ) else 0)
theorem diagProj_conjTranspose {N : ℕ} (S : BitAssignment N → Prop) :
    (diagProj S)ᴴ = diagProj S := by
  rw [diagProj, Matrix.diagonal_conjTranspose]
  exact congrArg Matrix.diagonal (funext fun x ↦ by by_cases h : S (basisBits N x) <;> simp [h])
theorem diagProj_mul_self {N : ℕ} (S : BitAssignment N → Prop) :
    diagProj S * diagProj S = diagProj S := by
  rw [diagProj, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun x ↦ by by_cases h : S (basisBits N x) <;> simp [h])
open Classical in
theorem diagProj_mulVec_ket {N : ℕ} (S : BitAssignment N → Prop) (β : BitAssignment N) :
    (diagProj S).mulVec (ket β) = if S β then ket β else 0 := by
  have hb : basisBits N ((basisBitsEquiv N).symm β) = β := (basisBitsEquiv N).apply_symm_apply β
  rw [diagProj, diagonal_mulVec_ket_cert, hb]
  by_cases h : S β <;> simp [h]
open Classical in
theorem diagProj_mulVec_apply {N : ℕ} (S : BitAssignment N → Prop) (ψ : Fin (2 ^ N) → ℂ)
    (x : Fin (2 ^ N)) : (diagProj S).mulVec ψ x = if S (basisBits N x) then ψ x else 0 := by
  dsimp only [diagProj, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single x]
  · simp only [Matrix.diagonal_apply_eq]
    by_cases h : S (basisBits N x) <;> simp only [h, ↓reduceIte, one_mul, zero_mul]
  · intro b _ hbx
    rw [Matrix.diagonal_apply_ne _ hbx.symm, zero_mul]
  · intro hx; exact absurd (Finset.mem_univ x) hx
theorem mem_of_diagProj_mulVec_eq {N : ℕ} {S : BitAssignment N → Prop} {ψ : Fin (2 ^ N) → ℂ}
    {x : Fin (2 ^ N)} (hpres : (diagProj S).mulVec ψ x = ψ x) (hnz : ψ x ≠ 0) : S
    (basisBits N x) := by
  rw [diagProj_mulVec_apply] at hpres
  by_contra hns
  simp only [hns, ↓reduceIte] at hpres
  exact hnz hpres.symm
theorem diagProj_mulVec_of_mem_ketSpan {N : ℕ} {S : BitAssignment N → Prop}
    {ψ : Fin (2 ^ N) → ℂ} (hψ : ψ ∈ KetSpan S) : (diagProj S).mulVec ψ = ψ := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨γ, hγ, rfl⟩
      simp only [diagProj_mulVec_ket, hγ, ↓reduceIte]
  | zero => exact Matrix.mulVec_zero _
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy]
  | smul a x _ ihx => rw [Matrix.mulVec_smul, ihx]
theorem diagProj_mul_of_preservesSpan {N : ℕ} {S₁ S₂ : BitAssignment N → Prop}
    {c : Circuit N} (hc : PreservesSpan S₁ S₂ c) :
    diagProj S₂ * (c.eval.1 * diagProj S₁) = c.eval.1 * diagProj S₁ := by
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, diagProj_mulVec_ket]
  by_cases h : S₁ β
  · simp only [h, ↓reduceIte]
    exact diagProj_mulVec_of_mem_ketSpan (hc β h)
  · simp only [h, ↓reduceIte, Matrix.mulVec_zero]
theorem diagProj_mul_inv_of_self {N : ℕ} (S : BitAssignment N → Prop) (U : Unitary (2 ^ N))
    (hU : diagProj S * (U.1 * diagProj S) = U.1 * diagProj S) : diagProj S *
    ((U⁻¹).1 * diagProj S) = (U⁻¹).1 * diagProj S := by
  let P := diagProj S
  have hP_herm : Pᴴ = P := diagProj_conjTranspose S
  have hP_sq : P * P = P := diagProj_mul_self S
  have hU_left : U.1ᴴ * U.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hU_right : U.1 * U.1ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  let Y := U.1 * P
  let Z := U.1ᴴ * P
  let B := Z - P * Z
  have hY_sq : Yᴴ * Y = P := by
    dsimp only [Y]
    rw [conjTranspose_mul, hP_herm, Matrix.mul_assoc, ← Matrix.mul_assoc U.1ᴴ U.1 P,
      hU_left, Matrix.one_mul, hP_sq]
  have hZ_sq : Zᴴ * Z = P := by
    dsimp only [Z]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hP_herm, Matrix.mul_assoc,
      ← Matrix.mul_assoc U.1 U.1ᴴ P, hU_right, Matrix.one_mul, hP_sq]
  have hZPZ : Zᴴ * (P * Z) = Y * Yᴴ := by
    calc Zᴴ * (P * Z)
        = (P * U.1) * (P * P) * (U.1ᴴ * P) := by
            simp only [Z, conjTranspose_mul, conjTranspose_conjTranspose, hP_herm,
              hP_sq, Matrix.mul_assoc]
      _ = (P * Y) * (P * Y)ᴴ := by simp only [Y, conjTranspose_mul, hP_herm, Matrix.mul_assoc]
      _ = Y * Yᴴ := by rw [show P * Y = Y from hU]
  have hBB : Bᴴ * B = P - Y * Yᴴ := by
    have h1 : (Zᴴ * P) * Z = Zᴴ * (P * Z) := by simp only [Matrix.mul_assoc]
    have h2 : (Zᴴ * P) * (P * Z) = Zᴴ * (P * Z) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P P Z, hP_sq]
    calc Bᴴ * B
        = (Zᴴ - Zᴴ * P) * (Z - P * Z) := by
            simp only [B, conjTranspose_sub, conjTranspose_mul, hP_herm]
      _ = Zᴴ * Z - Zᴴ * (P * Z) - (Zᴴ * P) * Z + (Zᴴ * P) * (P * Z) := by
            rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
            abel
      _ = P - Y * Yᴴ := by
            rw [h1, h2, hZ_sq, hZPZ]
            abel
  have hTrEq : (∑ i : Fin (2 ^ N), (Y * Yᴴ) i i) = ∑ i : Fin (2 ^ N), P i i := by
    rw [show (∑ i : Fin (2 ^ N), (Y * Yᴴ) i i) =
        ∑ i : Fin (2 ^ N), ∑ j : Fin (2 ^ N), Y i j * (Yᴴ) j i from rfl, Finset.sum_comm]
    refine (Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ mul_comm _ _).trans ?_
    exact congrArg (fun M : Matrix _ _ ℂ ↦ ∑ j : Fin (2 ^ N), M j j) hY_sq
  have hReZero : ∑ i : Fin (2 ^ N), ∑ j : Fin (2 ^ N),
      ((B j i).re * (B j i).re + (B j i).im * (B j i).im) = 0 := by
    have hRe := congrArg Complex.re (show (∑ i : Fin (2 ^ N), (Bᴴ * B) i i) = 0 by
      rw [hBB]
      simp only [Matrix.sub_apply, Finset.sum_sub_distrib, hTrEq, sub_self])
    simp only [Complex.zero_re, Complex.re_sum] at hRe
    rw [← hRe]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change _ = (∑ j : Fin (2 ^ N), (Bᴴ) i j * B j i).re
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      simp [Matrix.conjTranspose_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hNN (j i : Fin (2 ^ N)) : 0 ≤ (B j i).re * (B j i).re + (B j i).im * (B j i).im :=
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hB_zero : B = 0 := Matrix.ext fun j i ↦ by
    rw [Matrix.zero_apply]
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i' _ ↦ Finset.sum_nonneg fun j' _ ↦ hNN j' i')).mp hReZero i (Finset.mem_univ i)
    have hj0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j' _ ↦ hNN j' i)).mp hi0 j (Finset.mem_univ j)
    refine Complex.ext ?_ ?_ <;> dsimp only [Complex.zero_re, Complex.zero_im] <;>
      nlinarith [mul_self_nonneg (B j i).re, mul_self_nonneg (B j i).im]
  simpa [P, Z, show (U⁻¹).1 = U.1ᴴ by simp [Matrix.star_eq_conjTranspose]]
    using (sub_eq_zero.mp hB_zero).symm
private theorem presAux {m : ℕ}
    {P_pre P_mid A B C : Matrix (Fin m) (Fin m) ℂ}
    (hFwd : P_mid * (C * P_pre) = C * P_pre)
    (hMid : P_mid * (B * P_mid) = B * P_mid)
    (hBwd : P_pre * (A * P_mid) = A * P_mid) :
    P_pre * ((A * B * C) * P_pre) = (A * B * C) * P_pre := by
  have h1 : (A * B * C) * P_pre = (A * P_mid) * (B * (C * P_pre)) := by
    calc (A * B * C) * P_pre
        = A * (B * (P_mid * (C * P_pre))) := by
            simp only [Matrix.mul_assoc]
            rw [hFwd]
      _ = A * ((P_mid * (B * P_mid)) * (C * P_pre)) := by
            rw [← Matrix.mul_assoc B, hMid]
      _ = (A * P_mid) * (B * (C * P_pre)) := by
            simp only [Matrix.mul_assoc]
            rw [hFwd]
  rw [h1, ← Matrix.mul_assoc P_pre, hBwd]
theorem inv_congr_of_diagProj_eq {N : ℕ} (S : BitAssignment N → Prop)
    (U₁ U₂ : Unitary (2 ^ N)) (hEq : U₁.1 * diagProj S = U₂.1 * diagProj S)
    (hPres₂ : diagProj S * (U₂.1 * diagProj S) = U₂.1 * diagProj S) : (U₁⁻¹).1 * diagProj S =
    (U₂⁻¹).1 * diagProj S ∧ diagProj S * ((U₂⁻¹).1 * diagProj S) = (U₂⁻¹).1 * diagProj S := by
  have hInv₁ := diagProj_mul_inv_of_self S U₁ (by rw [hEq, hPres₂])
  have hInv₂ := diagProj_mul_inv_of_self S U₂ hPres₂
  have hAdj : diagProj S * (U₁⁻¹).1 = diagProj S * (U₂⁻¹).1 := by
    simpa [Unitary.coe_inv, Matrix.star_eq_conjTranspose, conjTranspose_mul,
      diagProj_conjTranspose] using congrArg conjTranspose hEq
  exact ⟨by rw [← hInv₁, ← Matrix.mul_assoc, hAdj, Matrix.mul_assoc, hInv₂], hInv₂⟩
theorem RealizesCleanUnitary.withTempAnd_diag
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (S_pre S_mid : BitAssignment n → Prop)
    (hPreZero : ∀ β, S_pre β → β anc = 0)
    (hMidEq : ∀ δ, S_mid δ → δ anc = δ c₁ * δ c₂)
    (hStepFwd : ∀ β, S_pre β → S_mid (Function.update β anc (β c₁ * β c₂)))
    (hStepBwd : ∀ δ, S_mid δ → S_pre (Function.update δ anc 0))
    (body : DynamicCircuit Var n) (U_body : Unitary (2 ^ n))
    (hbody : RealizesCleanUnitary v (diagProj S_mid) body U_body)
    (hBodyPres : diagProj S_mid * (U_body.1 * diagProj S_mid) = U_body.1 * diagProj S_mid) :
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
    RealizesCleanUnitary v (diagProj S_pre)
      (.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq body (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂)))
      (T_anc * U_body * T_anc) ∧
    diagProj S_pre * ((T_anc * U_body * T_anc).1 * diagProj S_pre) =
      (T_anc * U_body * T_anc).1 * diagProj S_pre := by
  intro T_anc
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let P_pre := diagProj S_pre
  let P_mid := diagProj S_mid
  let V := T_anc * U_body * T_anc
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hPpre_herm : P_preᴴ = P_pre := diagProj_conjTranspose S_pre
  have hPmid_herm : P_midᴴ = P_mid := diagProj_conjTranspose S_mid
  have hT_sq : T_anc * T_anc = 1 := toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a
  have hP₀_Ppre : P₀ * P_pre = P_pre := matrix_ext_ket fun β ↦ by
    simp only [P₀, P_pre, mul_mulVec_prog, diagProj_mulVec_ket]
    by_cases hs : S_pre β
    · simp only [hs, ↓reduceIte, ket_projector_zero, hPreZero β hs]
    · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
  have hPpre_P₀ : P_pre * P₀ = P_pre := by
    simpa [conjTranspose_mul, hP₀_herm, hPpre_herm] using congrArg conjTranspose hP₀_Ppre
  have hFwd_T : P_mid * (T_anc.1 * P_pre) = T_anc.1 * P_pre := matrix_ext_ket fun β ↦ by
    simp only [P_mid, P_pre, T_anc, mul_mulVec_prog, diagProj_mulVec_ket]
    by_cases hs : S_pre β
    · simp only [hs, ↓reduceIte, ket_TOFF, hPreZero β hs, zero_add,
        diagProj_mulVec_ket, hStepFwd β hs]
    · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
  have hFwd_T_adj : (P_pre * T_anc.1ᴴ) * P_mid = P_pre * T_anc.1ᴴ := by
    simpa [conjTranspose_mul, hPpre_herm, hPmid_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hFwd_T
  have hBwd_T : P_pre * (T_anc.1 * P_mid) = T_anc.1 * P_mid := matrix_ext_ket fun δ ↦ by
    simp only [P_pre, P_mid, T_anc, mul_mulVec_prog, diagProj_mulVec_ket]
    by_cases hs : S_mid δ
    · simp only [hs, ↓reduceIte, ket_TOFF,
        show δ anc + δ c₁ * δ c₂ = 0 by rw [hMidEq δ hs, CharTwo.add_self_eq_zero],
        diagProj_mulVec_ket, hStepBwd δ hs]
    · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
  have hV_pres : P_pre * (V.1 * P_pre) = V.1 * P_pre :=
    presAux hFwd_T hBodyPres hBwd_T
  have hV_P₀ : P₀ * (V.1 * P_pre) = V.1 * P_pre := by
    nth_rw 1 [← hV_pres]
    rw [← Matrix.mul_assoc P₀, hP₀_Ppre, hV_pres]
  have hV_P₀_adj : (P_pre * V.1ᴴ) * P₀ = P_pre * V.1ᴴ := by
    have h := congrArg conjTranspose hV_P₀
    simpa [conjTranspose_mul, hP₀_herm, hPpre_herm, ← Matrix.mul_assoc] using h
  have hTU_adj : T_anc.1ᴴ * U_body.1ᴴ = V.1ᴴ * T_anc.1ᴴ := by
    have hU_eq : U_body * T_anc = T_anc * V := by
      dsimp [V]
      rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
    have h := congrArg (fun W : Unitary (2 ^ n) ↦ W.1ᴴ) hU_eq
    simpa [Submonoid.coe_mul, conjTranspose_mul] using h
  refine ⟨⟨fun Ψ _ σ val => ?_, fun Θ hΘ σ => ?_⟩, hV_pres⟩
  · simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_seq,
      DynamicCircuit.compile_circuit, wp_qSeq, wp_circuit_compile_compat, wpQAssignCompat]
    congr 1
    have hinner := hbody.1 (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Ψ)
      (fun σ' v' => wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Ψ σ' v') σ val
    exact congrArg (fun x => (x : Observable (Fin (2 ^ n)))) hinner
  · let Ψ := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
    have hΨ_inv : ∀ σ' v', Ψ (Function.update σ' v v') = Ψ σ' :=
      fun σ' v' => wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' v'
    have hstep1 :
        ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
            (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)) Θ σ).1).conj
          P₀ = ((wpQAssignCompat T_anc (wp body.compile Ψ) σ).1).conj P₀ :=
      congrArg Subtype.val (congrFun
        (restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a
          (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile) Θ) σ)
    have hstep_uncomp : ((wpQAssignCompat T_anc Ψ σ).1).conj P₀ = (Θ σ).1.conj P₀ :=
      congrArg Subtype.val (congrFun
        (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
          v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ) σ)
    change ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
        (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)) Θ σ).1).conj
      P_pre = ((wpQAssignCompat V Θ σ).1).conj P_pre
    conv_lhs => rw [← hPpre_P₀]
    rw [← conj_conj, hstep1]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc P_pre P₀ T_anc.1ᴴ, hPpre_P₀, ← hFwd_T_adj,
      ← conj_conj, hbody.2 Ψ hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc (P_pre * T_anc.1ᴴ) (diagProj S_mid) U_body.1ᴴ,
      show (P_pre * T_anc.1ᴴ) * diagProj S_mid = P_pre * T_anc.1ᴴ from hFwd_T_adj,
      Matrix.mul_assoc P_pre T_anc.1ᴴ U_body.1ᴴ, hTU_adj,
      ← Matrix.mul_assoc P_pre V.1ᴴ T_anc.1ᴴ, ← hV_P₀_adj]
    have hfold : (Ψ σ).1.conj (((P_pre * V.1ᴴ) * P₀) * T_anc.1ᴴ) =
        (((wpQAssignCompat T_anc Ψ σ).1).conj P₀).conj (P_pre * V.1ᴴ) := by
      simp [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, conj_conj, Matrix.mul_assoc]
    rw [hfold, hstep_uncomp, conj_conj, hV_P₀_adj]
def Lift128 {n : ℕ} (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (S : BitAssignment 128 → Prop) (β : BitAssignment n) : Prop :=
  S (fun i ↦ β (rFull128 i)) ∧ ∀ j : Fin 9, β (rExtra9 j) = 0
private theorem localIdxProg_eq {k n : ℕ} (r : QRegister k n)
    (β : BitAssignment n) (l : Fin (2 ^ k)) : ∀ M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ,
    M.mulVec (ket (fun i ↦ β (r i))) l = M l (localIdxProg r β) := by
  intro M
  rw [ket_eq_single_local, Matrix.mulVec_single_one]; rfl
private theorem vec_eq_sum_ketAux {k : ℕ} (ψ : Fin (2 ^ k) → ℂ) :
    ψ = ∑ x : Fin (2 ^ k), ψ x • ket (basisBits k x) := funext fun y ↦ by
  rw [Finset.sum_apply]
  have hterm (x : Fin (2 ^ k)) :
      (ψ x • ket (basisBits k x)) y = if y = x then ψ x else 0 := by
    rw [Pi.smul_apply, smul_eq_mul, ket_eq_single_local, (basisBitsEquiv k).symm_apply_apply]
    by_cases hyx : y = x <;> simp [hyx]
  simp [hterm]
private theorem unitary_mul_diagProj_Lift128_eq {n : ℕ}
    (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n) (S : BitAssignment 128 → Prop)
    (U₁ U₂ : Unitary (2 ^ 128)) (hEq : U₁.1 * diagProj S = U₂.1 * diagProj S) :
    (rFull128.embedUnitary U₁).1 * diagProj (Lift128 rFull128 rExtra9 S) =
    (rFull128.embedUnitary U₂).1 * diagProj (Lift128 rFull128 rExtra9 S) := by
  apply matrix_ext_ket; intro β
  simp only [mul_mulVec_prog, diagProj_mulVec_ket]
  by_cases hL : Lift128 rFull128 rExtra9 S β
  · simp only [hL, ↓reduceIte, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hcol : U₁.1 l (localIdxProg rFull128 β) = U₂.1 l (localIdxProg rFull128 β) := by
      rw [← localIdxProg_eq rFull128 β l U₁.1, ← localIdxProg_eq rFull128 β l U₂.1]
      have hv := congrArg (fun M ↦ M.mulVec (ket (fun i ↦ β (rFull128 i))) l) hEq
      simp only [mul_mulVec_prog, diagProj_mulVec_ket, hL.1, ↓reduceIte] at hv
      exact hv
    rw [hcol]
  · simp only [hL, ↓reduceIte, Matrix.mulVec_zero]
private theorem proj_Lift128_mul_embedUnitary {n : ℕ}
    (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (hDisjExtra : rFull128.DisjointWires rExtra9) (S₁ S₂ : BitAssignment 128 → Prop)
    (U : Unitary (2 ^ 128)) (hPres : diagProj S₂ * (U.1 * diagProj S₁) = U.1 * diagProj S₁) :
    diagProj (Lift128 rFull128 rExtra9 S₂) * ((rFull128.embedUnitary U).1 * diagProj (Lift128
    rFull128 rExtra9 S₁)) = (rFull128.embedUnitary U).1 * diagProj
    (Lift128 rFull128 rExtra9 S₁) := by
  apply matrix_ext_ket; intro β
  simp only [mul_mulVec_prog, diagProj_mulVec_ket]
  by_cases hL : Lift128 rFull128 rExtra9 S₁ β
  · simp only [hL, ↓reduceIte, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog,
      Matrix.mulVec_sum, Matrix.mulVec_smul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    by_cases hnz : U.1 l (localIdxProg rFull128 β) = 0
    · simp only [hnz, zero_smul]
    · have hS₂ : S₂ (basisBits 128 l) := by
        have hv := congrArg (fun M ↦ M.mulVec (ket (fun i ↦ β (rFull128 i))) l) hPres
        simp only [mul_mulVec_prog, diagProj_mulVec_ket, hL.1, ↓reduceIte] at hv
        exact mem_of_diagProj_mulVec_eq hv (by rwa [localIdxProg_eq])
      have hLift₂ : Lift128 rFull128 rExtra9 S₂ (writeRegProg β rFull128 (basisBits 128 l)) :=
        ⟨by rwa [show (fun i ↦ writeRegProg β rFull128 (basisBits 128 l) (rFull128 i)) =
              basisBits 128 l from funext (writeRegProg_apply_reg _ _ _)],
         fun j ↦ by
           rw [writeRegProg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hDisjExtra.ne i j hi), hL.2 j]⟩
      simp only [diagProj_mulVec_ket, hLift₂, ↓reduceIte]
  · simp only [hL, ↓reduceIte, Matrix.mulVec_zero]
structure DynPair128 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (S : BitAssignment 128 → Prop) (t : ℕ)
    (dFwd dInv : DynamicCircuit Var n) (U_loc : Unitary (2 ^ 128)) : Prop where
  toffFwd : dFwd.count PrimitiveGate.TOFF = 0
  toffInv : dInv.count PrimitiveGate.TOFF = 0
  tFwd : dFwd.count PrimitiveGate.T ≤ t
  tInv : dInv.count PrimitiveGate.T ≤ t
  storeFwd : PreservesStoreConst dFwd
  storeInv : PreservesStoreConst dInv
  presLoc : diagProj S * (U_loc.1 * diagProj S) = U_loc.1 * diagProj S
  realFwd : RealizesCleanUnitary v (diagProj (Lift128 rFull128 rExtra9 S)) dFwd
    (rFull128.embedUnitary U_loc)
  realInv : RealizesCleanUnitary v (diagProj (Lift128 rFull128 rExtra9 S)) dInv
    (rFull128.embedUnitary U_loc⁻¹)
theorem DynPair128.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t : ℕ} {dFwd dInv : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ 128)} (hEq : U₁ = U₂)
    (hp : DynPair128 v rFull128 rExtra9 S t dFwd dInv U₁) : DynPair128 v rFull128 rExtra9 S t
    dFwd dInv U₂ := by
  subst hEq
  exact hp
theorem DynPair128.congr_fwd {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t : ℕ} {dFwd dInv : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ 128)} (hp : DynPair128 v rFull128 rExtra9 S t dFwd dInv U₁) (hEq : ∀
    α : BitAssignment 128, S α → U₁.1.mulVec (ket α) = U₂.1.mulVec (ket α)) : DynPair128 v
    rFull128 rExtra9 S t dFwd dInv U₂ := by
  have hMatEq : U₁.1 * diagProj S = U₂.1 * diagProj S := by
    apply matrix_ext_ket; intro α
    simp only [mul_mulVec_prog, diagProj_mulVec_ket]
    by_cases hs : S α
    · simp only [hs, ↓reduceIte, hEq α hs]
    · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
  have hPres₂ : diagProj S * (U₂.1 * diagProj S) = U₂.1 * diagProj S := by
    rw [← hMatEq, hp.presLoc]
  obtain ⟨hMatInvEq, _⟩ := inv_congr_of_diagProj_eq S U₁ U₂ hMatEq hPres₂
  have hPL_herm : (diagProj (Lift128 rFull128 rExtra9 S))ᴴ =
      diagProj (Lift128 rFull128 rExtra9 S) := diagProj_conjTranspose _
  exact {
    toffFwd := hp.toffFwd
    toffInv := hp.toffInv
    tFwd := hp.tFwd
    tInv := hp.tInv
    storeFwd := hp.storeFwd
    storeInv := hp.storeInv
    presLoc := hPres₂
    realFwd := RealizesCleanUnitary.congr_unitary hPL_herm hp.realFwd
      (unitary_mul_diagProj_Lift128_eq rFull128 rExtra9 S U₁ U₂ hMatEq)
    realInv := RealizesCleanUnitary.congr_unitary hPL_herm hp.realInv
      (unitary_mul_diagProj_Lift128_eq rFull128 rExtra9 S U₁⁻¹ U₂⁻¹ hMatInvEq)
  }
theorem DynPair128.static {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (S : BitAssignment 128 → Prop) (c : Circuit 128) (hToff : c.count PrimitiveGate.TOFF = 0)
    (hSpan : PreservesSpan S S c) : DynPair128 v rFull128 rExtra9 S (c.count PrimitiveGate.T)
    (.circuit (c.onRegister rFull128)) (.circuit (c.inverse.onRegister rFull128)) c.eval := by
  have hEvFwd : (c.onRegister rFull128).eval = rFull128.embedUnitary c.eval := by
    rw [Circuit.eval_onRegister]
  have hEvInv : (c.inverse.onRegister rFull128).eval = rFull128.embedUnitary (c.eval)⁻¹ := by
    rw [Circuit.eval_onRegister, Circuit.eval_inverse]
  exact {
    toffFwd := by simp [DynamicCircuit.count, Circuit.count_onRegister, hToff]
    toffInv := by simp [DynamicCircuit.count, Circuit.count_onRegister, hToff]
    tFwd := by simp [DynamicCircuit.count, Circuit.count_onRegister]
    tInv := by simp [DynamicCircuit.count, Circuit.count_onRegister]
    storeFwd := PreservesStoreConst.circuit _
    storeInv := PreservesStoreConst.circuit _
    presLoc := diagProj_mul_of_preservesSpan hSpan
    realFwd := hEvFwd ▸ RealizesCleanUnitary.circuit v _ (c.onRegister rFull128)
    realInv := hEvInv ▸ RealizesCleanUnitary.circuit v _ (c.inverse.onRegister rFull128)
  }
theorem DynPair128.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) {S : BitAssignment 128 → Prop} {t₁ t₂ : ℕ}
    {dFwd₁ dInv₁ dFwd₂ dInv₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ 128)}
    (h₁ : DynPair128 v rFull128 rExtra9 S t₁ dFwd₁ dInv₁ U₁)
    (h₂ : DynPair128 v rFull128 rExtra9 S t₂ dFwd₂ dInv₂ U₂) : DynPair128 v rFull128 rExtra9 S
    (t₁ + t₂) (.seq dFwd₁ dFwd₂) (.seq dInv₂ dInv₁) (U₂ * U₁) := by
  have hPL_herm : (diagProj (Lift128 rFull128 rExtra9 S))ᴴ =
      diagProj (Lift128 rFull128 rExtra9 S) := diagProj_conjTranspose _
  have hPres₁_L := proj_Lift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S S U₁ h₁.presLoc
  have hInv₂_loc := diagProj_mul_inv_of_self S U₂ h₂.presLoc
  have hPresInv₂_L :=
    proj_Lift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S S U₂⁻¹ hInv₂_loc
  have hEmbFwd : rFull128.embedUnitary U₂ * rFull128.embedUnitary U₁ =
      rFull128.embedUnitary (U₂ * U₁) := (rFull128.embedUnitary_mul U₂ U₁).symm
  have hEmbInv : rFull128.embedUnitary U₁⁻¹ * rFull128.embedUnitary U₂⁻¹ =
      rFull128.embedUnitary (U₂ * U₁)⁻¹ := by
    rw [splitAux_PosPostPrep80CertS3_mul_inv_rev, rFull128.embedUnitary_mul]
  exact {
    toffFwd := by simp [DynamicCircuit.count, h₁.toffFwd, h₂.toffFwd]
    toffInv := by simp [DynamicCircuit.count, h₁.toffInv, h₂.toffInv]
    tFwd := by
      simp only [DynamicCircuit.count]
      exact Nat.add_le_add h₁.tFwd h₂.tFwd
    tInv := by
      simp only [DynamicCircuit.count]
      exact Nat.add_le_add_iff_left.mpr (le_refl _) |>.trans (by
        exact (Nat.add_comm _ _) ▸ Nat.add_le_add h₁.tInv h₂.tInv)
    storeFwd := PreservesStoreConst.seq h₁.storeFwd h₂.storeFwd
    storeInv := PreservesStoreConst.seq h₂.storeInv h₁.storeInv
    presLoc := by
      simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      nth_rw 1 [← h₁.presLoc]
      rw [← Matrix.mul_assoc U₂.1 (diagProj S), ← Matrix.mul_assoc (diagProj S),
        h₂.presLoc, Matrix.mul_assoc U₂.1, h₁.presLoc]
    realFwd := hEmbFwd ▸ RealizesCleanUnitary.seq hPL_herm h₁.realFwd h₂.realFwd hPres₁_L
    realInv := hEmbInv ▸ RealizesCleanUnitary.seq hPL_herm h₂.realInv h₁.realInv hPresInv₂_L
  }
theorem RealizesCleanUnitary.circuitAux {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] {v : Var}
    {P_pre P_mid : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hPpre : P_preᴴ = P_pre)
    (hPmid : P_midᴴ = P_mid) (cFwd cBwd : Circuit n)
    (hFwd : P_mid * (cFwd.eval.1 * P_pre) = cFwd.eval.1 * P_pre) {body : DynamicCircuit Var n}
    {U_body : Unitary (2 ^ n)} (hbody : RealizesCleanUnitary v P_mid body U_body) :
    RealizesCleanUnitary v P_pre (.seq (.circuit cFwd) (.seq body (.circuit cBwd)))
    (cBwd.eval * U_body * cFwd.eval) := by
  have hadj : (P_pre * cFwd.eval.1ᴴ) * P_mid = P_pre * cFwd.eval.1ᴴ := by
    simpa [conjTranspose_mul, hPpre, hPmid, ← Matrix.mul_assoc] using congrArg conjTranspose hFwd
  refine ⟨fun Ψ hΨ σ val => ?_, fun Θ hΘ σ => ?_⟩
  · simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
      wp_circuit_compile_compat, wpQAssignCompat]
    exact congrArg (qAssignObsMap cFwd.eval)
      (hbody.1 (wpQAssignCompat cBwd.eval Ψ) (fun σ' val' ↦
        by simp only [wpQAssignCompat, hΨ σ' val']) σ val)
  · simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
      wp_circuit_compile_compat, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [← hadj, ← conj_conj,
      hbody.2 (wpQAssignCompat cBwd.eval Θ) (fun σ' val' ↦
        by simp only [wpQAssignCompat, hΘ σ' val']) σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, Submonoid.coe_mul,
      conjTranspose_mul]
    rw [← Matrix.mul_assoc (P_pre * cFwd.eval.1ᴴ) P_mid, hadj]
    simp only [Matrix.mul_assoc]
theorem DynPair128.withCliff {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) {S_pre S_mid : BitAssignment 128 → Prop}
    {t : ℕ} (C : Circuit 128) (hCToff : C.count PrimitiveGate.TOFF = 0)
    (hCT : C.count PrimitiveGate.T = 0) (hCFwd : PreservesSpan S_pre S_mid C)
    (hCBwd : PreservesSpan S_mid S_pre C.inverse) {bFwd bInv : DynamicCircuit Var n}
    {U_body : Unitary (2 ^ 128)} (hb : DynPair128 v rFull128 rExtra9 S_mid t bFwd bInv U_body)
    : DynPair128 v rFull128 rExtra9 S_pre t (.seq (.circuit (C.onRegister rFull128)) (.seq
    bFwd (.circuit (C.inverse.onRegister rFull128)))) (.seq (.circuit (C.onRegister rFull128))
    (.seq bInv (.circuit (C.inverse.onRegister rFull128)))) (C.inverse.eval * U_body * C.eval)
    := by
  let P_preL := diagProj (Lift128 rFull128 rExtra9 S_pre)
  let P_midL := diagProj (Lift128 rFull128 rExtra9 S_mid)
  have hPpre_herm : P_preLᴴ = P_preL := diagProj_conjTranspose _
  have hPmid_herm : P_midLᴴ = P_midL := diagProj_conjTranspose _
  have hCFwd_loc : diagProj S_mid * (C.eval.1 * diagProj S_pre) = C.eval.1 * diagProj S_pre :=
    diagProj_mul_of_preservesSpan hCFwd
  have hCBwd_loc : diagProj S_pre * (C.inverse.eval.1 * diagProj S_mid) = C.inverse.eval.1 *
      diagProj S_mid := diagProj_mul_of_preservesSpan hCBwd
  have hCFwd_L :=
    proj_Lift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S_pre S_mid C.eval hCFwd_loc
  have hEvC : (C.onRegister rFull128).eval = rFull128.embedUnitary C.eval := by
    rw [Circuit.eval_onRegister]
  have hEvCI : (C.inverse.onRegister rFull128).eval = rFull128.embedUnitary C.inverse.eval := by
    rw [Circuit.eval_onRegister]
  have hCFwd_onReg : P_midL * ((C.onRegister rFull128).eval.1 * P_preL) =
      (C.onRegister rFull128).eval.1 * P_preL := by
    rw [hEvC]; exact hCFwd_L
  have hStepFwd := RealizesCleanUnitary.circuitAux hPpre_herm hPmid_herm
    (C.onRegister rFull128) (C.inverse.onRegister rFull128) hCFwd_onReg hb.realFwd
  have hStepInv := RealizesCleanUnitary.circuitAux hPpre_herm hPmid_herm
    (C.onRegister rFull128) (C.inverse.onRegister rFull128) hCFwd_onReg hb.realInv
  have hEmbFwd : ((C.inverse.onRegister rFull128).eval * rFull128.embedUnitary U_body) *
      (C.onRegister rFull128).eval = rFull128.embedUnitary (C.inverse.eval * U_body * C.eval)
      := by
    rw [hEvC, hEvCI, ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  have hU_inv_eq :
      (C.inverse.eval * U_body * C.eval)⁻¹ = C.inverse.eval * U_body⁻¹ * C.eval := by
    rw [splitAux_PosPostPrep80CertS3_mul_inv_rev, splitAux_PosPostPrep80CertS3_mul_inv_rev,
      Circuit.eval_inverse, inv_inv,
      ← splitAux_PosPostPrep80CertS3_mul_assoc]
  have hEmbInv : ((C.inverse.onRegister rFull128).eval * rFull128.embedUnitary U_body⁻¹) *
      (C.onRegister rFull128).eval = rFull128.embedUnitary
      (C.inverse.eval * U_body * C.eval)⁻¹ := by
    rw [hEvC, hEvCI, hU_inv_eq, ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  exact {
    toffFwd := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCToff, hb.toffFwd]
    toffInv := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCToff, hb.toffInv]
    tFwd := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCT, hb.tFwd]
    tInv := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCT, hb.tInv]
    storeFwd := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq hb.storeFwd (PreservesStoreConst.circuit _))
    storeInv := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq hb.storeInv (PreservesStoreConst.circuit _))
    presLoc := presAux hCFwd_loc hb.presLoc hCBwd_loc
    realFwd := hEmbFwd ▸ hStepFwd
    realInv := hEmbInv ▸ hStepInv
  }
private theorem andComputeIf_of_zero_cert {N : ℕ} (c₁ c₂ anc : Wire N)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (α : BitAssignment N) (h0 : α anc = 0) :
    (andComputeIf c₁ c₂ anc).eval.1.mulVec (ket α) =
      ket (Function.update α anc (α c₁ * α c₂)) := by
  simp only [andComputeIf, h₁a, h₂a, ↓reduceDIte]
  exact ket_andCompute_of_zero c₁ c₂ anc h₁a h₂a α h0
private theorem andComputeIf_inv_of_eq {N : ℕ} (c₁ c₂ anc : Wire N)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (δ : BitAssignment N) (heq : δ anc = δ c₁ * δ c₂) :
    (andComputeIf c₁ c₂ anc).inverse.eval.1.mulVec (ket δ) =
      ket (Function.update δ anc 0) := by
  let δ₀ := Function.update δ anc 0
  have hupd : Function.update δ₀ anc (δ₀ c₁ * δ₀ c₂) = δ := funext fun w ↦ by
    dsimp only [δ₀]
    rw [Function.update_of_ne h₁a 0 δ, Function.update_of_ne h₂a 0 δ, ← heq]
    by_cases hw : w = anc
    · subst hw
      simp
    · simp [Function.update_of_ne hw]
  rw [show ket δ = (andComputeIf c₁ c₂ anc).eval.1.mulVec (ket δ₀) by
      rw [andComputeIf_of_zero_cert c₁ c₂ anc h₁a h₂a δ₀
        (Function.update_self anc 0 δ), hupd],
    ← mul_mulVec_prog, Circuit.eval_inverse,
    inv_mul_val_cert (andComputeIf c₁ c₂ anc).eval, Matrix.one_mulVec]
theorem DynPair128.withTempAnd {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) (c₁ c₂ anc : Wire 128) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) {S_pre S_mid : BitAssignment 128 → Prop} {t : ℕ}
    (hPreZero : ∀ α, S_pre α → α anc = 0) (hMidEq : ∀ δ, S_mid δ → δ anc = δ c₁ * δ c₂)
    (hStepFwd : ∀ α, S_pre α → S_mid (Function.update α anc (α c₁ * α c₂)))
    (hStepBwd : ∀ δ, S_mid δ → S_pre (Function.update δ anc 0))
    {bFwd bInv : DynamicCircuit Var n} {U_body : Unitary (2 ^ 128)}
    (hb : DynPair128 v rFull128 rExtra9 S_mid t bFwd bInv U_body) : DynPair128 v rFull128
    rExtra9 S_pre (t + 4) (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂)
    (rFull128 anc) (rFull128.wires.injective.ne h₁a) (rFull128.wires.injective.ne h₂a)) (.seq
    bFwd (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
    (rFull128.wires.injective.ne h₁₂)))) (.seq (DynamicCircuit.andCompute (rFull128 c₁)
    (rFull128 c₂) (rFull128 anc) (rFull128.wires.injective.ne h₁a)
    (rFull128.wires.injective.ne h₂a)) (.seq bInv (DynamicCircuit.andUncompute v (rFull128 c₁)
    (rFull128 c₂) (rFull128 anc) (rFull128.wires.injective.ne h₁₂)))) ((andComputeIf c₁ c₂
    anc).inverse.eval * U_body * (andComputeIf c₁ c₂ anc).eval) := by
  have h₁₂' : rFull128 c₁ ≠ rFull128 c₂ := rFull128.wires.injective.ne h₁₂
  have h₁a' : rFull128 c₁ ≠ rFull128 anc := rFull128.wires.injective.ne h₁a
  have h₂a' : rFull128 c₂ ≠ rFull128 anc := rFull128.wires.injective.ne h₂a
  let L_pre := Lift128 rFull128 rExtra9 S_pre
  let L_mid := Lift128 rFull128 rExtra9 S_mid
  have hAncNotExtra : ∀ j : Fin 9, rExtra9 j ≠ rFull128 anc :=
    fun j h ↦ hDisjExtra.ne anc j h.symm
  have hUpdPull : ∀ (β : BitAssignment n) (b : ZMod 2),
      (fun i ↦ Function.update β (rFull128 anc) b (rFull128 i)) =
        Function.update (fun i ↦ β (rFull128 i)) anc b := by
    intro β b; funext i
    by_cases hia : i = anc
    · subst hia; simp
    · simp [Function.update_of_ne hia, Function.update_of_ne (rFull128.wires.injective.ne hia)]
  have hL_preZero : ∀ β, L_pre β → β (rFull128 anc) = 0 := fun β h ↦ hPreZero _ h.1
  have hL_midEq : ∀ δ, L_mid δ → δ (rFull128 anc) = δ (rFull128 c₁) * δ (rFull128 c₂) :=
    fun δ h ↦ hMidEq _ h.1
  have hL_fwd : ∀ β, L_pre β →
      L_mid (Function.update β (rFull128 anc) (β (rFull128 c₁) * β (rFull128 c₂))) := by
    intro β ⟨h1, h2⟩
    refine ⟨?_, fun j ↦ by rw [Function.update_of_ne (hAncNotExtra j), h2 j]⟩
    rw [hUpdPull]; exact hStepFwd _ h1
  have hL_bwd : ∀ δ, L_mid δ → L_pre (Function.update δ (rFull128 anc) 0) := by
    intro δ ⟨h1, h2⟩
    refine ⟨?_, fun j ↦ by rw [Function.update_of_ne (hAncNotExtra j), h2 j]⟩
    rw [hUpdPull]; exact hStepBwd _ h1
  have hBodyFwd_L :=
    proj_Lift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S_mid S_mid U_body hb.presLoc
  have hInvBody_loc := diagProj_mul_inv_of_self S_mid U_body hb.presLoc
  have hBodyInv_L :=
    proj_Lift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S_mid S_mid U_body⁻¹ hInvBody_loc
  obtain ⟨hRealFwd_T, _⟩ := RealizesCleanUnitary.withTempAnd_diag v (rFull128 c₁)
      (rFull128 c₂) (rFull128 anc) h₁₂' h₁a' h₂a' L_pre L_mid hL_preZero hL_midEq hL_fwd
      hL_bwd bFwd (rFull128.embedUnitary U_body) hb.realFwd hBodyFwd_L
  obtain ⟨hRealInv_T, _⟩ := RealizesCleanUnitary.withTempAnd_diag v (rFull128 c₁)
      (rFull128 c₂) (rFull128 anc) h₁₂' h₁a' h₂a' L_pre L_mid hL_preZero hL_midEq hL_fwd
      hL_bwd bInv (rFull128.embedUnitary U_body⁻¹) hb.realInv hBodyInv_L
  let T_loc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  have hToffOnReg : (Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a'
      h₂a').eval = rFull128.embedUnitary T_loc := by
    have hon : (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).onRegister rFull128 =
        Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a' h₂a' := by
      dsimp only [Circuit.TOFF, Circuit.onRegister]
      congr 1
      apply PosPostPrep80CertS3Alt.qreg_ext
      intro i
      fin_cases i <;> rfl
    rw [← hon, Circuit.eval_onRegister]
  have hEmbFwd : ((Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a'
      h₂a').eval * rFull128.embedUnitary U_body) * (Circuit.TOFF (rFull128 c₁) (rFull128 c₂)
      (rFull128 anc) h₁₂' h₁a' h₂a').eval = rFull128.embedUnitary (T_loc * U_body * T_loc)
      := by
    rw [hToffOnReg, ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  have hTloc_inv : T_loc⁻¹ = T_loc :=
    inv_eq_of_mul_eq_one_right (toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a)
  have hU_inv_eq : (T_loc * U_body * T_loc)⁻¹ = T_loc * U_body⁻¹ * T_loc := by
    rw [splitAux_PosPostPrep80CertS3_mul_inv_rev, splitAux_PosPostPrep80CertS3_mul_inv_rev,
      hTloc_inv, ← splitAux_PosPostPrep80CertS3_mul_assoc]
  have hEmbInv : ((Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a'
      h₂a').eval * rFull128.embedUnitary U_body⁻¹) * (Circuit.TOFF (rFull128 c₁) (rFull128 c₂)
      (rFull128 anc) h₁₂' h₁a' h₂a').eval = rFull128.embedUnitary (T_loc * U_body * T_loc)⁻¹
      := by
    rw [hU_inv_eq, hToffOnReg, ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  have hPresLoc_T : diagProj S_pre * ((T_loc * U_body * T_loc).1 * diagProj S_pre) =
      (T_loc * U_body * T_loc).1 * diagProj S_pre := by
    have hFT : diagProj S_mid * (T_loc.1 * diagProj S_pre) = T_loc.1 * diagProj S_pre :=
      matrix_ext_ket fun α ↦ by
        simp only [T_loc, mul_mulVec_prog, diagProj_mulVec_ket]
        by_cases hs : S_pre α
        · simp only [hs, ↓reduceIte, ket_TOFF, hPreZero α hs, zero_add,
            diagProj_mulVec_ket, hStepFwd α hs]
        · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
    have hBT : diagProj S_pre * (T_loc.1 * diagProj S_mid) = T_loc.1 * diagProj S_mid :=
      matrix_ext_ket fun δ ↦ by
        simp only [T_loc, mul_mulVec_prog, diagProj_mulVec_ket]
        by_cases hs : S_mid δ
        · simp only [hs, ↓reduceIte, ket_TOFF,
            show δ anc + δ c₁ * δ c₂ = 0 by rw [hMidEq δ hs, CharTwo.add_self_eq_zero],
            diagProj_mulVec_ket, hStepBwd δ hs]
        · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
    exact presAux hFT hb.presLoc hBT
  have hPairT :
      DynPair128 v rFull128 rExtra9 S_pre (t + 4)
        (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁a' h₂a')
          (.seq bFwd (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
            h₁₂')))
        (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁a' h₂a')
          (.seq bInv (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
            h₁₂')))
        (T_loc * U_body * T_loc) := {
    toffFwd := by
      simp [DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, hb.toffFwd]
    toffInv := by
      simp [DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, hb.toffInv]
    tFwd := by
      simp only [DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, Nat.add_zero]
      have := hb.tFwd
      exact Nat.add_comm 4 _ ▸ Nat.add_le_add_left this 4
    tInv := by
      simp only [DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, Nat.add_zero]
      have := hb.tInv
      exact Nat.add_comm 4 _ ▸ Nat.add_le_add_left this 4
    storeFwd := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq hb.storeFwd (PreservesStoreConst.andUncompute v _ _ _ h₁₂'))
    storeInv := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq hb.storeInv (PreservesStoreConst.andUncompute v _ _ _ h₁₂'))
    presLoc := hPresLoc_T
    realFwd := hEmbFwd ▸ hRealFwd_T
    realInv := hEmbInv ▸ hRealInv_T
  }
  refine hPairT.congr_fwd fun α hα ↦ ?_
  simp only [Submonoid.coe_mul, mul_mulVec_prog]
  rw [show T_loc.1.mulVec (ket α) = ket (Function.update α anc (α c₁ * α c₂)) by
      dsimp only [T_loc]
      rw [ket_TOFF, hPreZero α hα, zero_add],
    andComputeIf_of_zero_cert c₁ c₂ anc h₁a h₂a α (hPreZero α hα)]
  let α_mid := Function.update α anc (α c₁ * α c₂)
  have hα_mid : S_mid α_mid := hStepFwd α hα
  let ψ := U_body.1.mulVec (ket α_mid)
  have hψ_pres : (diagProj S_mid).mulVec ψ = ψ := by
    have hv := congrArg (fun M ↦ M.mulVec (ket α_mid)) hb.presLoc
    simp only [mul_mulVec_prog, diagProj_mulVec_ket, hα_mid, ↓reduceIte] at hv
    exact hv
  change T_loc.1.mulVec ψ = (andComputeIf c₁ c₂ anc).inverse.eval.1.mulVec ψ
  rw [vec_eq_sum_ketAux ψ, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx0 : ψ x = 0
  · simp only [hx0, zero_smul, Matrix.mulVec_zero]
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hSx : S_mid (basisBits 128 x) := mem_of_diagProj_mulVec_eq (congrFun hψ_pres x) hx0
    let δ := basisBits 128 x
    change ψ x • T_loc.1.mulVec (ket δ) =
      ψ x • (andComputeIf c₁ c₂ anc).inverse.eval.1.mulVec (ket δ)
    rw [show T_loc.1.mulVec (ket δ) = ket (Function.update δ anc 0) by
        dsimp only [T_loc]
        rw [ket_TOFF, show δ anc + δ c₁ * δ c₂ = 0 by rw [hMidEq δ hSx, CharTwo.add_self_eq_zero]],
      andComputeIf_inv_of_eq c₁ c₂ anc h₁a h₂a δ (hMidEq δ hSx)]
def rHead76Of {n : ℕ} (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (hDisjExtra : rFull128.DisjointWires rExtra9) : QRegister 76 n :=
  (rFull128.compose rHead67_128).concat rExtra9 (hDisjExtra.compose_left rHead67_128)
private theorem unitary_mulVec_ket_of_ket {k n : ℕ} (r : QRegister k n)
    (U : Unitary (2 ^ k)) (β : BitAssignment n) (α' : BitAssignment k)
    (h : U.1.mulVec (ket (fun i ↦ β (r i))) = ket α') :
    (r.embedUnitary U).1.mulVec (ket β) = ket (writeRegProg β r α') := by
  rw [QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
  have hcol : ∀ l : Fin (2 ^ k),
      U.1 l (localIdxProg r β) = if l = (basisBitsEquiv k).symm α' then (1 : ℂ) else 0 := by
    intro l
    rw [← localIdxProg_eq r β l U.1, h, ket_eq_single_local]
    by_cases hl : l = (basisBitsEquiv k).symm α' <;> simp [hl]
  simp_rw [hcol, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hb : basisBits k ((basisBitsEquiv k).symm α') = α' :=
    (basisBitsEquiv k).apply_symm_apply α'
  rw [hb]
theorem DynPair128.mono_t {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t t' : ℕ} {dFwd dInv : DynamicCircuit Var n}
    {U : Unitary (2 ^ 128)} (hp : DynPair128 v rFull128 rExtra9 S t dFwd dInv U) (ht : t ≤ t')
    : DynPair128 v rFull128 rExtra9 S t' dFwd dInv U :=
  { hp with tFwd := hp.tFwd.trans ht, tInv := hp.tInv.trans ht }
def mkWithCliffDyn {Var : Type} {n : ℕ} (rFull128 : QRegister 128 n) (C : Circuit 128)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n := .seq
    (.circuit (C.onRegister rFull128)) (.seq body (.circuit (C.inverse.onRegister rFull128)))
def mkWithTempAndDyn {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n)
    (c₁ c₂ anc : Wire 128) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n := .seq (DynamicCircuit.andCompute
    (rFull128 c₁) (rFull128 c₂) (rFull128 anc) (rFull128.wires.injective.ne h₁a)
    (rFull128.wires.injective.ne h₂a)) (.seq body (DynamicCircuit.andUncompute v (rFull128 c₁)
    (rFull128 c₂) (rFull128 anc) (rFull128.wires.injective.ne h₁₂)))
@[simp] theorem splitAux_PosPostPrep80CertS3_toff_mkWithTempAndDyn
    {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) (c₁ c₂ anc : Wire 128)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : DynamicCircuit Var n) :
    (mkWithTempAndDyn v rFull128 c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.TOFF =
    body.count PrimitiveGate.TOFF := by
  simp [mkWithTempAndDyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
    DynamicCircuit.count_andUncompute_toff]
@[simp] theorem splitAux_PosPostPrep80CertS3_t_mkWithTempAndDyn
    {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) (c₁ c₂ anc : Wire 128)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : DynamicCircuit Var n) :
    (mkWithTempAndDyn v rFull128 c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.T = 4 +
    body.count PrimitiveGate.T := by
  simp [mkWithTempAndDyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
    DynamicCircuit.count_andUncompute_t]
theorem DynPair128.symm {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t : ℕ}
    {dFwd dInv : DynamicCircuit Var n} {U_loc : Unitary (2 ^ 128)}
    (hp : DynPair128 v rFull128 rExtra9 S t dFwd dInv U_loc) :
    DynPair128 v rFull128 rExtra9 S t dInv dFwd U_loc⁻¹ := {
  toffFwd := hp.toffInv
  toffInv := hp.toffFwd
  tFwd := hp.tInv
  tInv := hp.tFwd
  storeFwd := hp.storeInv
  storeInv := hp.storeFwd
  presLoc := diagProj_mul_inv_of_self S U_loc hp.presLoc
  realFwd := hp.realInv
  realInv := by rw [inv_inv]; exact hp.realFwd
}
def mkToffExtra0Dyn {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n)
    (rExtra9 : QRegister 9 n) (hDisjExtra : rFull128.DisjointWires rExtra9)
    (c₁ c₂ targ : Wire 128) (h₁₂ : c₁ ≠ c₂) : DynamicCircuit Var n :=
  let anc : Wire n := rExtra9 ⟨0, by decide⟩
  .seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) anc
          (hDisjExtra.ne c₁ ⟨0, by decide⟩) (hDisjExtra.ne c₂ ⟨0, by decide⟩))
    (.seq (.circuit (Circuit.CNOT anc (rFull128 targ)
            (hDisjExtra.ne targ ⟨0, by decide⟩).symm))
          (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) anc
            (rFull128.wires.injective.ne h₁₂)))
@[simp] theorem toff_mkToffExtra0Dyn {Var : Type} {n : ℕ} (v : Var)
    (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (hDisjExtra : rFull128.DisjointWires rExtra9)
    (c₁ c₂ targ : Wire 128) (h₁₂ : c₁ ≠ c₂) :
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂).count PrimitiveGate.TOFF = 0 :=
      by
  simp [mkToffExtra0Dyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
    DynamicCircuit.count_andUncompute_toff]
@[simp] theorem t_mkToffExtra0Dyn {Var : Type} {n : ℕ} (v : Var)
    (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (hDisjExtra : rFull128.DisjointWires rExtra9)
    (c₁ c₂ targ : Wire 128) (h₁₂ : c₁ ≠ c₂) :
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂).count PrimitiveGate.T = 4 := by
  simp [mkToffExtra0Dyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
    DynamicCircuit.count_andUncompute_t]
theorem DynPair128.toffIf_extra0 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) {S : BitAssignment 128 → Prop}
    (c₁ c₂ targ : Wire 128) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ targ) (h₂t : c₂ ≠ targ)
    (hIndep : WireIndep S targ) : DynPair128 v rFull128 rExtra9 S 4
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂)
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂) (toffIf c₁ c₂ targ).eval
    := by
  let anc : Wire n := rExtra9 ⟨0, by decide⟩
  have h₁₂' : rFull128 c₁ ≠ rFull128 c₂ := rFull128.wires.injective.ne h₁₂
  have h₁a' : rFull128 c₁ ≠ anc := hDisjExtra.ne c₁ ⟨0, by decide⟩
  have h₂a' : rFull128 c₂ ≠ anc := hDisjExtra.ne c₂ ⟨0, by decide⟩
  have hat' : anc ≠ rFull128 targ := (hDisjExtra.ne targ ⟨0, by decide⟩).symm
  have h₁t' : rFull128 c₁ ≠ rFull128 targ := rFull128.wires.injective.ne h₁t
  have h₂t' : rFull128 c₂ ≠ rFull128 targ := rFull128.wires.injective.ne h₂t
  let L_pre : BitAssignment n → Prop := Lift128 rFull128 rExtra9 S
  let L_mid : BitAssignment n → Prop := fun δ ↦ S (fun i ↦ δ (rFull128 i)) ∧ δ anc = δ
      (rFull128 c₁) * δ (rFull128 c₂) ∧ ∀ j : Fin 9, j.val ≠ 0 → δ (rExtra9 j) = 0
  let cBody : Circuit n := Circuit.CNOT anc (rFull128 targ) hat'
  have hL_preZero : ∀ β, L_pre β → β anc = 0 := fun β h ↦ h.2 ⟨0, by decide⟩
  have hL_midEq : ∀ δ, L_mid δ → δ anc = δ (rFull128 c₁) * δ (rFull128 c₂) := fun δ h ↦ h.2.1
  have hL_fwd : ∀ β, L_pre β →
      L_mid (Function.update β anc (β (rFull128 c₁) * β (rFull128 c₂))) := by
    intro β ⟨hS, hEx⟩
    refine ⟨?_, ?_, fun j hj ↦ ?_⟩
    · have hpull : (fun i ↦
      Function.update β anc (β (rFull128 c₁) * β (rFull128 c₂)) (rFull128 i)) =
          fun i ↦ β (rFull128 i) := by
        funext i; exact Function.update_of_ne (hDisjExtra.ne i ⟨0, by decide⟩) _ β
      rwa [hpull]
    · simp [Function.update_self, Function.update_of_ne h₁a', Function.update_of_ne h₂a']
    · have hj0 : j ≠ ⟨0, by decide⟩ := fun heq ↦ hj (congrArg Fin.val heq)
      rw [Function.update_of_ne (rExtra9.wires.injective.ne hj0), hEx j]
  have hL_bwd : ∀ δ, L_mid δ → L_pre (Function.update δ anc 0) := by
    intro δ ⟨hS, _, hEx⟩
    refine ⟨?_, fun j ↦ ?_⟩
    · have hpull : (fun i ↦ Function.update δ anc 0 (rFull128 i)) = fun i ↦ δ (rFull128 i) := by
        funext i; exact Function.update_of_ne (hDisjExtra.ne i ⟨0, by decide⟩) _ δ
      rwa [hpull]
    · by_cases hj0 : j = ⟨0, by decide⟩
      · subst hj0; exact Function.update_self anc 0 δ
      · rw [Function.update_of_ne (rExtra9.wires.injective.ne hj0)]
        exact hEx j (fun hv ↦ hj0 (Fin.ext hv))
  have hBodyPres : diagProj L_mid * (cBody.eval.1 * diagProj L_mid) =
      cBody.eval.1 * diagProj L_mid := matrix_ext_ket fun δ ↦ by
    simp only [cBody, mul_mulVec_prog, diagProj_mulVec_ket]
    by_cases hs : L_mid δ
    · simp only [hs, ↓reduceIte, ket_CNOT, diagProj_mulVec_ket]
      have hs' : L_mid (Function.update δ (rFull128 targ) (δ (rFull128 targ) + δ anc)) := by
        refine ⟨?_, ?_, fun j hj ↦ ?_⟩
        · rw [show (fun i ↦ Function.update δ (rFull128 targ)
              (δ (rFull128 targ) + δ anc) (rFull128 i)) =
              Function.update (fun i ↦ δ (rFull128 i)) targ (δ (rFull128 targ) + δ anc) from
            funext fun i ↦ by
              by_cases hit : i = targ
              · subst hit
                simp
              · simp [Function.update_of_ne hit,
                  Function.update_of_ne (rFull128.wires.injective.ne hit)]]
          exact hIndep _ _ hs.1
        · rw [Function.update_of_ne hat', Function.update_of_ne h₁t', Function.update_of_ne h₂t',
            hs.2.1]
        · rw [Function.update_of_ne (hDisjExtra.ne targ j).symm]
          exact hs.2.2 j hj
      simp only [hs', ↓reduceIte]
    · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
  obtain ⟨hRealRaw, _⟩ := RealizesCleanUnitary.withTempAnd_diag v (rFull128 c₁) (rFull128 c₂)
      anc h₁₂' h₁a' h₂a' L_pre L_mid hL_preZero hL_midEq hL_fwd hL_bwd (.circuit cBody)
      cBody.eval (RealizesCleanUnitary.circuit v (diagProj L_mid) cBody) hBodyPres
  let T_anc := (Circuit.TOFF (rFull128 c₁) (rFull128 c₂) anc h₁₂' h₁a' h₂a').eval
  have hMatEq : (T_anc * cBody.eval * T_anc).1 * diagProj L_pre =
      (rFull128.embedUnitary (toffIf c₁ c₂ targ).eval).1 * diagProj L_pre := by
    apply matrix_ext_ket; intro β
    simp only [mul_mulVec_prog, diagProj_mulVec_ket]
    by_cases hL : L_pre β
    · simp only [hL, ↓reduceIte, Submonoid.coe_mul, mul_mulVec_prog, T_anc, cBody,
        ket_TOFF, hL_preZero β hL, zero_add, ket_CNOT]
      let p := β (rFull128 c₁) * β (rFull128 c₂)
      let β₁ := Function.update β anc p
      let β₂ := Function.update β₁ (rFull128 targ) (β₁ (rFull128 targ) + β₁ anc)
      have hz : β₂ anc + β₂ (rFull128 c₁) * β₂ (rFull128 c₂) = 0 := by
        dsimp [β₂, β₁, p]
        rw [Function.update_of_ne hat', Function.update_of_ne h₁t', Function.update_of_ne h₂t',
          Function.update_self, Function.update_of_ne h₁a', Function.update_of_ne h₂a',
          CharTwo.add_self_eq_zero]
      change ket (Function.update β₂ anc (β₂ anc + β₂ (rFull128 c₁) * β₂ (rFull128 c₂))) = _
      rw [hz,
        unitary_mulVec_ket_of_ket rFull128 (toffIf c₁ c₂ targ).eval β _
          (ket_toffIf_ne c₁ c₂ targ h₁₂ h₁t h₂t (fun i ↦ β (rFull128 i)))]
      congr 1; funext w
      by_cases hwa : w = anc
      · subst hwa
        rw [Function.update_self]
        have hnot : anc ∉ Set.range rFull128.wires := by
          rintro ⟨i, hi⟩; exact hDisjExtra.ne i ⟨0, by decide⟩ hi
        rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot, hL.2 ⟨0, by decide⟩]
      · rw [Function.update_of_ne hwa]
        by_cases hwt : w = rFull128 targ
        · subst hwt
          dsimp [β₂, β₁, p]
          rw [Function.update_self, Function.update_of_ne hat'.symm, Function.update_self,
            writeRegProg_apply_reg, Function.update_self]
        · dsimp [β₂, β₁]
          rw [Function.update_of_ne hwt, Function.update_of_ne hwa]
          by_cases hmem : w ∈ Set.range rFull128.wires
          · obtain ⟨i, rfl⟩ := hmem
            have hit : i ≠ targ := fun heq ↦ hwt (congrArg rFull128 heq)
            rw [writeRegProg_apply_reg, Function.update_of_ne hit]
          · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem]
    · simp only [hL, ↓reduceIte, Matrix.mulVec_zero]
  have hPl : (diagProj L_pre)ᴴ = diagProj L_pre := diagProj_conjTranspose _
  have hRealFwd := RealizesCleanUnitary.congr_unitary hPl hRealRaw hMatEq
  have hToffInv : ((toffIf c₁ c₂ targ).eval)⁻¹ = (toffIf c₁ c₂ targ).eval := by
    have ht : toffIf c₁ c₂ targ = Circuit.TOFF c₁ c₂ targ h₁₂ h₁t h₂t := by
      simp [toffIf, h₁₂, h₁t, h₂t]
    rw [ht]
    exact inv_eq_of_mul_eq_one_right (toffoli_eval_sq c₁ c₂ targ h₁₂ h₁t h₂t)
  exact {
    toffFwd := toff_mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂
    toffInv := toff_mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂
    tFwd := le_of_eq (t_mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂)
    tInv := le_of_eq (t_mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra c₁ c₂ targ h₁₂)
    storeFwd := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.andUncompute v _ _ _ h₁₂'))
    storeInv := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.andUncompute v _ _ _ h₁₂'))
    presLoc := diagProj_mul_of_preservesSpan (preservesSpan_toffIf c₁ c₂ targ hIndep)
    realFwd := hRealFwd
    realInv := hToffInv.symm ▸ hRealFwd
  }
def openCore128 (β : BitAssignment 128) : Prop := β wEnPos_128 = (1 - β wCoin1_128) *
    (1 - β wCoin2_128) ∧ β wEnS0_128 = β wEnPos_128 * β wCoin0_128 ∧ β wEnC0_128 = β
    wEnPos_128 + β wEnS0_128 ∧ (∀ j : Fin 30, β (scr30_128 j) = 0) ∧ β wEnC0Head_128 = 0 ∧ β
    wPopT01_128 = 0 ∧ β wPopMaj_128 = 0 ∧ β wPopPar_128 = 0 ∧ β wBrTop_128 = 0
def FlInv1 (β : BitAssignment 128) : Prop := openCore128 β ∧ β wEnHead_128 = β wEnPos_128 * β
    wIsHead_128 ∧ β wEnTail_128 = 0 ∧ β wEnAnc_128 = 0 ∧ β wEnS0Tail_128 = 0
def FlInv2 (β : BitAssignment 128) : Prop :=
  openCore128 β ∧ β wEnHead_128 = β wEnPos_128 * β wIsHead_128 ∧
  β wEnTail_128 = β wEnPos_128 + β wEnHead_128 ∧ β wEnAnc_128 = 0 ∧ β wEnS0Tail_128 = 0
def FlInv3 (β : BitAssignment 128) : Prop := openCore128 β ∧ β wEnHead_128 = β wEnPos_128 * β
    wIsHead_128 ∧ β wEnTail_128 = β wEnPos_128 + β wEnHead_128 ∧ β wEnS0Tail_128 = β wEnS0_128
    * β wEnTail_128 ∧ β wEnAnc_128 = 0
def cFlTail_128 : Circuit 128 :=
  cnotIf wEnPos_128 wEnTail_128 ;;ᶜ cnotIf wEnHead_128 wEnTail_128
def cFlags2AncFast_128 : Circuit 128 :=
  cnotIf wEnTail_128 wEnAnc_128 ;;ᶜ
  cnotIf wEnS0_128 wEnAnc_128 ;;ᶜ
  cnotIf wEnS0Tail_128 wEnAnc_128
def cFlags2AncOrig_128 : Circuit 128 :=
  andComputeIf wEnC0_128 wIsHead_128 wEnC0Head_128 ;;ᶜ
  cnotIf wEnPos_128 wEnAnc_128 ;;ᶜ
  cnotIf wEnC0Head_128 wEnAnc_128 ;;ᶜ
  (andComputeIf wEnC0_128 wIsHead_128 wEnC0Head_128).inverse
noncomputable def dFlags2Wrap {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n := mkWithTempAndDyn v rFull128
    wEnPos_128 wIsHead_128 wEnHead_128 (by decide) (by decide) (by decide) (mkWithCliffDyn
    rFull128 cFlTail_128 (mkWithTempAndDyn v rFull128 wEnS0_128 wEnTail_128 wEnS0Tail_128
    (by decide) (by decide) (by decide) (mkWithCliffDyn rFull128 cFlags2AncFast_128 body)))
def isCleanList (clean : List (Wire 128)) (w : Wire 128) : Bool :=
  clean.any (fun x ↦ decide (x = w))
def dropCleanList (clean : List (Wire 128)) (q : Wire 128) : List (Wire 128) :=
  clean.filter (fun x ↦ decide (x ≠ q))
end Junction
end ConfigPosPostPrep80CertS3
end PosPostPrep80CertS3
namespace PosPostPrep80MergedVepS3.CleanComputeProg
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open PosPostPrep80MergedVepS3 PosPostPrep80InnerAmpS3 ZeroAncillaUSPS3 PosPostPrep80CertS3
def wrapDyn {Var : Type} {n : ℕ} (p : CleanComputeProg)
    (v : Var) (rFull128 : QRegister 128 n) (body : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  match p with
  | .id => body
  | .x q => mkWithCliffDyn rFull128 (Circuit.X q) body
  | .cnot c t => mkWithCliffDyn rFull128 (cnotIf c t) body
  | .tempAnd c₁ c₂ anc =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ anc ∧ c₂ ≠ anc then
        mkWithTempAndDyn v rFull128 c₁ c₂ anc h.1 h.2.1 h.2.2 body
      else
        body
  | .seq p₁ p₂ => p₁.wrapDyn v rFull128 (p₂.wrapDyn v rFull128 body)
def checkProg : CleanComputeProg → List (Wire 128) → Bool × List (Wire 128)
  | .id, clean => (true, clean)
  | .x q, clean => (true, dropCleanList clean q)
  | .cnot c t, clean =>
      (decide (c ≠ t ∧ c ≠ wSubReject_128 ∧ t ≠ wSubReject_128), dropCleanList clean t)
  | .tempAnd c₁ c₂ anc, clean =>
      (isCleanList clean anc &&
        decide (c₁ ≠ c₂ ∧ c₁ ≠ anc ∧ c₂ ≠ anc ∧
          c₁ ≠ wSubReject_128 ∧ c₂ ≠ wSubReject_128 ∧ anc ≠ wSubReject_128),
       dropCleanList clean anc)
  | .seq p₁ p₂, clean =>
      let r₁ := p₁.checkProg clean
      let r₂ := p₂.checkProg r₁.2
      (r₁.1 && r₂.1, r₂.2)
def PostInv : CleanComputeProg → (BitAssignment 128 → Prop) → (BitAssignment 128 → Prop)
  | .id, S => S
  | .x q, S => fun δ ↦ S (Function.update δ q (δ q + 1))
  | .cnot c t, S => fun δ ↦ S (Function.update δ t (δ t + δ c))
  | .tempAnd c₁ c₂ anc, S => fun δ ↦ S (Function.update δ anc 0) ∧ δ anc = δ c₁ * δ c₂
  | .seq p₁ p₂, S => p₂.PostInv (p₁.PostInv S)
def touchesWire : CleanComputeProg → Wire 128 → Bool
  | .id, _ => false
  | .x q, w => decide (q = w)
  | .cnot c t, w => decide (c = w ∨ t = w)
  | .tempAnd c₁ c₂ anc, w => decide (c₁ = w ∨ c₂ = w ∨ anc = w)
  | .seq p₁ p₂, w => p₁.touchesWire w || p₂.touchesWire w
end PosPostPrep80MergedVepS3.CleanComputeProg
namespace PosPostPrep80CertS3
section ConfigPosPostPrep80CertS3
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instLoc_PosPostPrep80CertS3_2b {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket sqrtHalf)
open ZeroAncillaUSPS3 hiding ket
open FullSysMomSlots0135Concrete (coinBitFin2)
open PosPostPrep80MergedVepS3 PosPostPrep80InnerAmpS3
section Junction
open HermitianMat
open scoped ComplexOrder MatrixOrder
open _root_.QuantumComputation.Specs.StoppingPowerSolution (CliffProg TempPhaseProg writeRegProg
  writeRegProg_apply_reg writeRegProg_apply_of_not_mem localIdxProg embedMatrix_mulVec_ket_prog
  mul_mulVec_prog)
open MeasureBranchHadamardSem (RealizesCleanUnitary ket_projector_zero toffoli_eval_sq
  matrix_ext_ket ket_CNOT ket_TOFF)
open StreamingBchComparator (PreservesStoreConst)
open Pos24HeadCoordXor80 (isOut24Idx rOut24In67 headOutMask24 xorRegBits xorRegBits_apply_reg
  xorRegBits_apply_of_not_mem xorRegBits_comp)
def RespectsClean (clean : List (Wire 128)) (S : BitAssignment 128 → Prop) : Prop :=
    (∀ α, S α → ∀ w, w ∈ clean → α w = 0) ∧ wSubReject_128 ∉ clean ∧ WireIndep S
    wSubReject_128
def initClean128 : List (Wire 128) := (List.finRange 30).map scr30_128 ++
    [wPopT01_128, wPopMaj_128, wPopPar_128, wBrTop_128]
def dFinishXorFwd {Var : Type} {n : ℕ} (v : Var)
    (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (hDisjExtra : rFull128.DisjointWires rExtra9) : DynamicCircuit Var n :=
  .seq (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
          wEnS0Tail_128 (rB1_128 ⟨0, by decide⟩) (wP80_128 ⟨75, by decide⟩) (by decide))
  (.seq (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
          wEnS0Tail_128 (rB1_128 ⟨1, by decide⟩) (wP80_128 ⟨76, by decide⟩) (by decide))
  (.seq (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
          wEnS0Tail_128 (rB1_128 ⟨2, by decide⟩) (wP80_128 ⟨77, by decide⟩) (by decide))
  (.seq (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
          wEnS0_128 (rB0_128 ⟨0, by decide⟩) (rB1_128 ⟨0, by decide⟩) (by decide))
  (.seq (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
          wEnS0_128 (rB0_128 ⟨1, by decide⟩) (rB1_128 ⟨1, by decide⟩) (by decide))
        (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
          wEnS0_128 (rB0_128 ⟨2, by decide⟩) (rB1_128 ⟨2, by decide⟩) (by decide))))))
def dFinishXorInv {Var : Type} {n : ℕ} (v : Var)
    (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (hDisjExtra : rFull128.DisjointWires rExtra9) : DynamicCircuit Var n :=
  .seq (.seq (.seq (.seq (.seq
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
      wEnS0_128 (rB0_128 ⟨2, by decide⟩) (rB1_128 ⟨2, by decide⟩) (by decide))
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
      wEnS0_128 (rB0_128 ⟨1, by decide⟩) (rB1_128 ⟨1, by decide⟩) (by decide)))
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
      wEnS0_128 (rB0_128 ⟨0, by decide⟩) (rB1_128 ⟨0, by decide⟩) (by decide)))
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
      wEnS0Tail_128 (rB1_128 ⟨2, by decide⟩) (wP80_128 ⟨77, by decide⟩) (by decide)))
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
      wEnS0Tail_128 (rB1_128 ⟨1, by decide⟩) (wP80_128 ⟨76, by decide⟩) (by decide)))
    (mkToffExtra0Dyn v rFull128 rExtra9 hDisjExtra
      wEnS0Tail_128 (rB1_128 ⟨0, by decide⟩) (wP80_128 ⟨75, by decide⟩) (by decide))
def pForkStep (u t uRight : Wire 128) : CleanComputeProg :=
  .seq (.tempAnd u t uRight) (.cnot uRight u)
def pHsOuter : CleanComputeProg :=
  .cnot wEnHead_128 (scr30_128 ⟨0, by decide⟩)
def pHsForks_0 : CleanComputeProg :=
  pForkStep (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨5, by decide⟩) (scr20_128 ⟨1, by decide⟩)
def pHsForks_1 : CleanComputeProg :=
  pForkStep (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨4, by decide⟩) (scr20_128 ⟨2, by decide⟩)
def pHsForks_2 : CleanComputeProg :=
  .seq (pForkStep (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨3, by decide⟩) (scr20_128 ⟨3, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨2, by decide⟩) (rK_128 ⟨3, by decide⟩) (scr20_128 ⟨4, by decide⟩))
        (pForkStep (scr20_128 ⟨1, by decide⟩) (rK_128 ⟨3, by decide⟩) (scr20_128 ⟨5, by decide⟩)))
def pHsForks_3 : CleanComputeProg :=
  .seq (pForkStep (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨2, by decide⟩) (scr20_128 ⟨6, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨3, by decide⟩) (rK_128 ⟨2, by decide⟩) (scr20_128 ⟨7, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨2, by decide⟩) (rK_128 ⟨2, by decide⟩) (scr20_128 ⟨8, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨4, by decide⟩) (rK_128 ⟨2, by decide⟩) (scr20_128 ⟨9, by decide⟩))
        (pForkStep (scr20_128 ⟨1, by decide⟩) (rK_128 ⟨2, by decide⟩) (scr20_128 ⟨10, by
          decide⟩)))))
def pHsForks_4 : CleanComputeProg :=
  .seq (pForkStep (scr20_128 ⟨0, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨11, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨6, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨12, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨3, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨13, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨7, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨14, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨2, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨15, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨8, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨16, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨4, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨17, by decide⟩))
  (.seq (pForkStep (scr20_128 ⟨9, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨18, by decide⟩))
        (pForkStep (scr20_128 ⟨10, by decide⟩) (rK_128 ⟨1, by decide⟩) (scr20_128 ⟨19, by
          decide⟩)))))))))
def dHsDepth5Fwd {Var : Type} {n : ℕ} (rFull128 : QRegister 128 n) : DynamicCircuit Var n :=
  .circuit (cHsSplit_5.onRegister rFull128)
def dHsDepth5Inv {Var : Type} {n : ℕ} (rFull128 : QRegister 128 n) : DynamicCircuit Var n :=
  .circuit (cHsSplit_5.inverse.onRegister rFull128)
def dHsDepth4Fwd {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (.circuit (cHsSplit_4.onRegister rFull128))
    (pHsForks_4.wrapDyn v rFull128 (dHsDepth5Fwd rFull128))
def dHsDepth4Inv {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (pHsForks_4.wrapDyn v rFull128 (dHsDepth5Inv rFull128))
    (.circuit (cHsSplit_4.inverse.onRegister rFull128))
def dHsDepth3Fwd {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (.circuit (cHsSplit_3.onRegister rFull128))
    (pHsForks_3.wrapDyn v rFull128 (dHsDepth4Fwd v rFull128))
def dHsDepth3Inv {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (pHsForks_3.wrapDyn v rFull128 (dHsDepth4Inv v rFull128))
    (.circuit (cHsSplit_3.inverse.onRegister rFull128))
def dHsDepth2Fwd {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (.circuit (cHsSplit_2.onRegister rFull128))
    (pHsForks_2.wrapDyn v rFull128 (dHsDepth3Fwd v rFull128))
def dHsDepth2Inv {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (pHsForks_2.wrapDyn v rFull128 (dHsDepth3Inv v rFull128))
    (.circuit (cHsSplit_2.inverse.onRegister rFull128))
def dHsDepth1Fwd {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (.circuit (cHsSplit_1.onRegister rFull128))
    (pHsForks_1.wrapDyn v rFull128 (dHsDepth2Fwd v rFull128))
def dHsDepth1Inv {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (pHsForks_1.wrapDyn v rFull128 (dHsDepth2Inv v rFull128))
    (.circuit (cHsSplit_1.inverse.onRegister rFull128))
def dHsDepth0Fwd {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (.circuit (cHsSplit_0.onRegister rFull128))
    (pHsForks_0.wrapDyn v rFull128 (dHsDepth1Fwd v rFull128))
def dHsDepth0Inv {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) : DynamicCircuit Var n
    :=
  .seq (pHsForks_0.wrapDyn v rFull128 (dHsDepth1Inv v rFull128))
    (.circuit (cHsSplit_0.inverse.onRegister rFull128))
def dLeafHeadShell64Fwd {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) :
    DynamicCircuit Var n := pHsOuter.wrapDyn v rFull128 (dHsDepth0Fwd v rFull128)
def dLeafHeadShell64Inv {Var : Type} {n : ℕ} (v : Var) (rFull128 : QRegister 128 n) :
    DynamicCircuit Var n := pHsOuter.wrapDyn v rFull128 (dHsDepth0Inv v rFull128)
def pHsCum_0 : CleanComputeProg := pHsOuter
def pHsCum_1 : CleanComputeProg := .seq pHsCum_0 pHsForks_0
def pHsCum_2 : CleanComputeProg := .seq pHsCum_1 pHsForks_1
def pHsCum_3 : CleanComputeProg := .seq pHsCum_2 pHsForks_2
def pHsCum_4 : CleanComputeProg := .seq pHsCum_3 pHsForks_3
def pHsCum_5 : CleanComputeProg := .seq pHsCum_4 pHsForks_4
def hsClean_0 : List (Wire 128) := (pHsOuter.checkProg initClean128).2
def hsClean_1 : List (Wire 128) := (pHsForks_0.checkProg hsClean_0).2
def hsClean_2 : List (Wire 128) := (pHsForks_1.checkProg hsClean_1).2
def hsClean_3 : List (Wire 128) := (pHsForks_2.checkProg hsClean_2).2
def hsClean_4 : List (Wire 128) := (pHsForks_3.checkProg hsClean_3).2
def hsClean_5 : List (Wire 128) := (pHsForks_4.checkProg hsClean_4).2
def HsInv_0 : BitAssignment 128 → Prop := pHsOuter.PostInv FlagsInv128
def HsInv_1 : BitAssignment 128 → Prop := pHsForks_0.PostInv HsInv_0
def HsInv_2 : BitAssignment 128 → Prop := pHsForks_1.PostInv HsInv_1
def HsInv_3 : BitAssignment 128 → Prop := pHsForks_2.PostInv HsInv_2
def HsInv_4 : BitAssignment 128 → Prop := pHsForks_3.PostInv HsInv_3
def HsInv_5 : BitAssignment 128 → Prop := pHsForks_4.PostInv HsInv_4
end Junction
end ConfigPosPostPrep80CertS3
end PosPostPrep80CertS3
end
end ModPosPostPrep80CertS3
end PosPostPrep80CertS3
end
end PosPostPrep80CertS3_p1

end QuantumComputation.Specs.StoppingPowerSolution
