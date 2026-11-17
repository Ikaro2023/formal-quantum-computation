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

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import QuantumComputation.QuantumHoareLogic.CQAssertion
public import QuantumComputation.QuantumHoareLogic.CQState
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3BoothPartner
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Bell18StreamOff

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModBell18TeleportCore
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256
open Operator QProg Matrix HermitianMat Real
open MeasureBranchHadamardSem
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
namespace Bell18TeleportCore
/-! ## Section 1: Subspace-Step & Clean-Workspace Calculus -/
/-- Exact store-closed backward-observable relation mapping input operator `E_in` to `E_out`. -/
def SubspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in E_out : Operator (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦
    M) = (fun _ ↦ M') ∧
    E_inᴴ * M'.1.1 * E_in = E_outᴴ * M.1.1 * E_out
theorem SubspaceStep.refl {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E : Operator (2 ^ n)) : SubspaceStep E E (.identity : DynamicCircuit Var n) := fun M ↦
  ⟨M, rfl, rfl⟩
theorem SubspaceStep.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E₁ E₂ E₃ : Operator (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStep E₁ E₂ d₁) (h₂ : SubspaceStep E₂ E₃ d₂) :
    SubspaceStep E₁ E₃ (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, heq₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, heq₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, heq₁.trans heq₂⟩
  funext σ
  simp only [DynamicCircuit.compile_seq, wp_qSeq, hwp₂, hwp₁]
theorem subspaceStep_of_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (c : Circuit n) (E : Operator (2 ^ n)) :
    SubspaceStep (Var := Var) E (c.eval.1 * E) (.circuit c) := by
  intro M
  refine ⟨qAssignObsMap c.eval M, ?_, ?_⟩
  · funext σ
    rw [DynamicCircuit.compile_circuit, wp_circuit_compile_compat]
    rfl
  · simp [qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem subspaceStep_congr_in {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {E₁ E₁' E₂ : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    (hE : E₁ = E₁') (h : SubspaceStep E₁' E₂ d) : SubspaceStep E₁ E₂ d := hE ▸ h
theorem subspaceStep_congr_out {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {E₁ E₂ E₂' : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    (hE : E₂' = E₂) (h : SubspaceStep E₁ E₂' d) : SubspaceStep E₁ E₂ d := hE ▸ h
/-- Uniform `2^K`-branch X-measurement + reset collapse on `SubspaceStep`. -/
theorem subspaceStep_measureXReset {Var : Type} [Fintype Var] [DecidableEq Var]
    {n K : ℕ} [NeZero (2 ^ n)] (v : Var) (r : QRegister K n)
    (cont : (Fin K → Bool) → DynamicCircuit Var n) (E_in E_out : Operator (2 ^ n))
    (hBranch : ∀ f : Fin K → Bool, SubspaceStep (DynCircuitExt.xResetKraus r f * E_in)
        ((((√(1 / 2)) ^ K : ℝ) : ℂ) • E_out) (cont f)) :
    SubspaceStep E_in E_out (DynCircuitExt.measureXResetAndBranch v K r cont) := by
  intro M
  choose MCont hwp heq using fun f ↦ hBranch f M
  obtain ⟨MOut, hOut_wp, hOut_mat⟩ :=
    DynCircuitExt.wp_measureXResetAndBranch_const v K r cont M MCont hwp
  refine ⟨MOut, hOut_wp, ?_⟩
  rw [hOut_mat, Matrix.mul_sum, Matrix.sum_mul]
  have hTerm : ∀ f : Fin K → Bool, E_inᴴ * ((DynCircuitExt.xResetKraus r f)ᴴ * (MCont f).1.1 *
        DynCircuitExt.xResetKraus r f) * E_in =
      ((((√(1 / 2)) ^ K : ℝ) ^ 2 : ℝ) : ℂ) • (E_outᴴ * M.1.1 * E_out) := by
    intro f
    have hf := heq f
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc] at hf ⊢
    convert hf using 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun f _ ↦ hTerm f, ← Finset.sum_smul]
  have hSum : (∑ _f : Fin K → Bool, ((((√(1 / 2)) ^ K : ℝ) ^ 2 : ℝ) : ℂ)) = 1 := by
    exact_mod_cast DynCircuitExt.sum_sqrt_half_pow_sq K
  rw [hSum, one_smul]
/-- Realization of a global unitary `U` on input subspace operator `P` (`rfl`-matched to
`HoistBorrow42ProjBridge.RealizesOnProj` / `Bell18Seq6Bridge.RealizesOnProj`). -/
def RealizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (P : Operator (2 ^ n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦
    M) = (fun _ ↦ M') ∧
    Pᴴ * M'.1.1 * P = Pᴴ * (U.1ᴴ * M.1.1 * U.1) * P
private theorem RealizesOnProj.iff_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} : RealizesOnProj P U d ↔ SubspaceStep P (U.1 * P) d := by
  constructor <;> intro h M <;> obtain ⟨M', hwp, heq⟩ := h M <;> refine ⟨M', hwp, ?_⟩
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using heq
  · simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using heq
theorem RealizesOnProj.of_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (h : SubspaceStep P (U.1 * P) d) : RealizesOnProj P U d :=
  RealizesOnProj.iff_subspaceStep.mpr h
/-! ## Section 2: Basis Kets, Diagonal Sign Unitaries, & 0-T Hadamard/CNOT/CZ Walls -/
theorem disjointWires_symm {n k m : ℕ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) : s.DisjointWires r := QRegister.disjoint_comm.mp h
private theorem matrix_ext_single {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ g : Fin d, A.mulVec (Pi.single g 1) = B.mulVec (Pi.single g 1)) : A = B := by
  ext i g
  have hgi := congrFun (h g) i
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hgi
  exact hgi
private theorem ket_basisBits_eq_single {n : ℕ} (g : Fin (2 ^ n)) :
    ket (basisBits n g) = (Pi.single g 1 : Fin (2 ^ n) → ℂ) := by
  simp [ket, basisState]
private theorem basisOutcomeProjector_zero_mulVec_single {n w : ℕ}
    (r : QRegister w n) (g : Fin (2 ^ n)) : (r.basisOutcomeProjector 0).mulVec (Pi.single g 1) =
      if r.extractIndex g = 0 then Pi.single g 1 else 0 := by
  funext i
  rw [Matrix.mulVec_single_one, QRegister.basisOutcomeProjector_eq_diagonal]
  by_cases hig : i = g
  · subst hig
    by_cases hz : r.extractIndex i = 0 <;> simp [Matrix.diagonal, hz]
  · by_cases hz : r.extractIndex g = 0 <;> simp [Matrix.diagonal, hig, hz]
/-- Overwrites the bits of `β` on `r` with `γ`. -/
noncomputable def writeReg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp]
theorem writeReg_apply_reg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]
theorem writeReg_apply_of_not_mem {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
/-- Diagonal `±1` phase unitary (`rfl`-matched to `_root_.bellDiagSign` in
`TableXUncompute`). -/
noncomputable def bellDiagSign {k : ℕ} (phase : Fin (2 ^ k) → Bool) : Unitary (2 ^ k) :=
  ⟨Matrix.diagonal fun x ↦ if phase x then (-1 : ℂ) else 1, by
    have hsq : (Matrix.diagonal fun x : Fin (2 ^ k) ↦ if phase x then (-1 : ℂ) else 1) *
        Matrix.diagonal (fun x ↦ if phase x then (-1 : ℂ) else 1) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext x y
      by_cases hxy : x = y
      · subst hxy
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        cases phase x <;> norm_num
      · simp [Matrix.diagonal, hxy]
    have hsa : star (Matrix.diagonal fun x : Fin (2 ^ k) ↦ if phase x then (-1 : ℂ) else 1) =
        Matrix.diagonal fun x ↦ if phase x then (-1 : ℂ) else 1 := by
      ext x y
      by_cases hxy : x = y
      · subst hxy
        simp only [Matrix.star_apply, Matrix.diagonal_apply_eq]
        cases phase x <;> simp
      · simp [Matrix.diagonal, Ne.symm hxy, hxy]
    exact ⟨hsa.symm ▸ hsq, hsa.symm ▸ hsq⟩⟩
private theorem embedUnitary_bellDiagSign_mulVec_single {n k : ℕ}
    (r : QRegister k n) (phase : Fin (2 ^ k) → Bool) (g : Fin (2 ^ n)) :
    (r.embedUnitary (bellDiagSign phase)).1.mulVec (Pi.single g 1) =
      (if phase (r.extractIndex g) then (-1 : ℂ) else 1) • Pi.single g 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (r.embedMatrix (Matrix.diagonal fun z ↦ if phase z then (-1 : ℂ) else 1)) i g =
    ((if phase (r.extractIndex g) then (-1 : ℂ) else 1) • (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ)) i
  rw [QRegister.embedMatrix_apply]
  by_cases hig : i = g
  · subst hig; simp [Matrix.diagonal]
  · simp only [Pi.smul_apply, Pi.single_eq_of_ne hig, smul_zero]
    by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2
    · have hex : r.extractIndex i ≠ r.extractIndex g := fun heq ↦ hig
        (r.basisSplitEquiv.injective
          (Prod.ext (by simpa [QRegister.basisSplitEquiv_apply_fst] using heq) henv))
      simp [henv, Matrix.diagonal, hex]
    · simp [henv]
/-- `𝔽₂` inner-product parity (`rfl`-matched to `_root_.f2Parity` in `TableXUncompute`). -/
def bellF2Parity (b : ℕ) (f : Fin b → Bool) (v : Fin (2 ^ b)) : Bool :=
  (List.finRange b).foldr (fun i acc ↦ xor (f i && decide (basisBits b v i ≠ 0)) acc) false
private theorem sign_xor_bool (a b : Bool) : (if xor a b then (-1 : ℂ) else 1) =
      (if a then (-1 : ℂ) else 1) * (if b then (-1 : ℂ) else 1) := by
  cases a <;> cases b <;> norm_num
private theorem sign_foldr_xor {α : Type*} (l : List α) (p : α → Bool) :
    (if l.foldr (fun i acc ↦ xor (p i) acc) false then (-1 : ℂ) else 1) =
      (l.map fun i ↦ if p i then (-1 : ℂ) else 1).prod := by
  induction l with
  | nil => simp
  | cons a tl ih => rw [List.foldr_cons, List.map_cons, List.prod_cons, sign_xor_bool, ih]
private theorem sign_bellF2Parity_eq_prod (b : ℕ) (f : Fin b → Bool) (v : Fin (2 ^ b)) :
    (if bellF2Parity b f v then (-1 : ℂ) else 1) =
      ∏ i : Fin b, if f i && decide (basisBits b v i ≠ 0) then (-1 : ℂ) else 1 := by
  unfold bellF2Parity
  rw [sign_foldr_xor, Fin.prod_univ_def]
/-- Table-write operator (`rfl`-matched to `_root_.setTableOp` in `TableXUncompute`). -/
noncomputable def bellSetTableOp {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n) (tbl : Fin (2 ^ k) → Fin (2 ^ b)) :
    Operator (2 ^ n) :=
  Matrix.of fun i h ↦ if i = rMeas.replaceIndex h (tbl (rData.extractIndex h)) then 1 else 0
private theorem bellSetTableOp_mulVec_single {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n) (tbl : Fin (2 ^ k) → Fin (2 ^ b))
    (h : Fin (2 ^ n)) : (bellSetTableOp rData rMeas tbl).mulVec (Pi.single h 1) =
      Pi.single (rMeas.replaceIndex h (tbl (rData.extractIndex h))) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change bellSetTableOp rData rMeas tbl i h =
    (Pi.single (rMeas.replaceIndex h (tbl (rData.extractIndex h))) (1 : ℂ) : Fin (2 ^ n) → ℂ) i
  unfold bellSetTableOp
  rw [Matrix.of_apply]
  by_cases hi : i = rMeas.replaceIndex h (tbl (rData.extractIndex h))
  · subst hi; simp
  · simp [hi]
private theorem bellTableXReset_mul_setTableOp_mul_zeroMeas {n k b : ℕ}
    (rData : QRegister k n) (rMeas : QRegister b n)
    (tbl : Fin (2 ^ k) → Fin (2 ^ b)) (f : Fin b → Bool) :
    (rData.embedUnitary (bellDiagSign (fun x ↦ bellF2Parity b f (tbl x)))).1 *
      DynCircuitExt.xResetKraus rMeas f * bellSetTableOp rData rMeas tbl *
      rMeas.basisOutcomeProjector 0 =
    (((√(1 / 2)) ^ b : ℝ) : ℂ) • rMeas.basisOutcomeProjector 0 := by
  apply matrix_ext_single
  intro g
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    basisOutcomeProjector_zero_mulVec_single, Matrix.smul_mulVec,
    basisOutcomeProjector_zero_mulVec_single]
  by_cases hg0 : rMeas.extractIndex g = 0
  · simp only [hg0, ↓reduceIte]
    rw [bellSetTableOp_mulVec_single]
    let g' := rMeas.replaceIndex g (tbl (rData.extractIndex g))
    change (rData.embedUnitary (bellDiagSign (fun x ↦ bellF2Parity b f (tbl x)))).1.mulVec
      ((DynCircuitExt.xResetKraus rMeas f).mulVec (Pi.single g' 1)) = _
    have hEx : rMeas.extractIndex g' = tbl (rData.extractIndex g) :=
      rMeas.extractIndex_replaceIndex g _
    have hRep : rMeas.replaceIndex g' 0 = g := by
      apply rMeas.basisSplitEquiv.injective
      rw [rMeas.basisSplitEquiv_replaceIndex, rMeas.basisSplitEquiv_replaceIndex]
      exact Prod.ext (by simp [QRegister.basisSplitEquiv_apply_fst, hg0]) rfl
    rw [DynCircuitExt.xResetKraus_mulVec_single, hEx, hRep, ← sign_bellF2Parity_eq_prod,
      Matrix.mulVec_smul, embedUnitary_bellDiagSign_mulVec_single, smul_smul]
    refine congrArg₂ (· • ·) ?_ rfl
    cases bellF2Parity b f (tbl (rData.extractIndex g)) <;> simp
  · simp [hg0]
private theorem bellDiagSign_mulVec_ket {n : ℕ} (phase : Fin (2 ^ n) → Bool) (α : BitAssignment n) :
    (bellDiagSign phase).1.mulVec (ket α) =
      (if phase ((basisBitsEquiv n).symm α) then (-1 : ℂ) else 1) • ket α := by
  let g := (basisBitsEquiv n).symm α
  have hket : ket α = Pi.single g 1 := by simp [ket, basisState, g]
  rw [hket]
  funext i
  rw [Matrix.mulVec_single_one]
  change Matrix.diagonal (fun x ↦ if phase x then (-1 : ℂ) else 1) i g =
    ((if phase g then (-1 : ℂ) else 1) • (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ)) i
  by_cases hig : i = g
  · subst hig; simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hig]
private theorem bellDiagSign_mul_self {k : ℕ} (phase : Fin (2 ^ k) → Bool) :
    bellDiagSign phase * bellDiagSign phase = 1 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, OneMemClass.coe_one]
  dsimp only [bellDiagSign]
  rw [Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    cases phase x <;> norm_num
  · simp [Matrix.diagonal, hxy]
private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide
private theorem sign_decide_zmod2_add (x y : ZMod 2) :
    (if decide (x + y = 1) then (-1 : ℂ) else 1) =
      (if decide (x = 1) then (-1 : ℂ) else 1) * (if decide (y = 1) then (-1 : ℂ) else 1) := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 by decide, show (0 : ZMod 2) ≠ 1 by decide]
private theorem eval_H_mul_self {n : ℕ} (q : Wire n) :
    (Circuit.H q).eval * (Circuit.H q).eval = 1 := by
  rw [Circuit.eval_single, ← QRegister.embedUnitary_mul, PrimitiveGate.eval, Qubit.H_sq,
      QRegister.embedUnitary_one]
private theorem eval_H_comm {n : ℕ} {q₁ q₂ : Wire n} (hne : q₁ ≠ q₂) :
    (Circuit.H q₁).eval * (Circuit.H q₂).eval = (Circuit.H q₂).eval * (Circuit.H q₁).eval := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro α
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ket_H q₂ α, ket_H q₁ α, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    ket_H q₁ (Function.update α q₂ 0), ket_H q₁ (Function.update α q₂ 1),
    ket_H q₂ (Function.update α q₁ 0), ket_H q₂ (Function.update α q₁ 1),
    Function.update_of_ne hne, Function.update_of_ne hne,
    Function.update_of_ne hne.symm, Function.update_of_ne hne.symm,
    Function.update_comm hne.symm 0 0 α, Function.update_comm hne.symm 0 1 α,
    Function.update_comm hne.symm 1 0 α, Function.update_comm hne.symm 1 1 α]
  simp only [smul_add, smul_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
/-- Prefix Hadamard wall on the first `k` wires of `r`. -/
def cHadRegAux {n K : ℕ} (r : QRegister K n) : (k : ℕ) → k ≤ K → Circuit n
  | 0, _ => .identity
  | k + 1, hk => cHadRegAux r k (by omega) ;;ᶜ Circuit.H (r ⟨k, hk⟩)
@[simp]
private theorem cHadRegAux_zero {n K : ℕ} (r : QRegister K n) (hk : 0 ≤ K) :
    cHadRegAux r 0 hk = .identity := rfl
private theorem cHadRegAux_succ {n K : ℕ} (r : QRegister K n) (k : ℕ) (hk : k + 1 ≤ K) :
    cHadRegAux r (k + 1) hk = cHadRegAux r k (by omega) ;;ᶜ Circuit.H (r ⟨k, hk⟩) := rfl
/-- Full `K`-wire Hadamard wall (`0 T`, `0 TOFF`). -/
def cHadReg {n K : ℕ} (r : QRegister K n) : Circuit n := cHadRegAux r K le_rfl
private theorem cHadRegAux_count_t {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHadRegAux r k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, _ => by simp [cHadRegAux, cHadRegAux_count_t r k (by omega)]
private theorem cHadRegAux_count_toff {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHadRegAux r k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, _ => by simp [cHadRegAux, cHadRegAux_count_toff r k (by omega)]
@[simp]
theorem cHadReg_count_t {n K : ℕ} (r : QRegister K n) : (cHadReg r).count .T = 0 :=
  cHadRegAux_count_t r K le_rfl
@[simp]
theorem cHadReg_count_toff {n K : ℕ} (r : QRegister K n) : (cHadReg r).count .TOFF = 0 :=
  cHadRegAux_count_toff r K le_rfl
private theorem cHadRegAux_comm_H {n K : ℕ} (r : QRegister K n) (q : Wire n) :
    ∀ (k : ℕ) (hk : k ≤ K), (∀ i : Fin k, r ⟨i.val, by omega⟩ ≠ q) →
      (cHadRegAux r k hk).eval * (Circuit.H q).eval = (Circuit.H q).eval * (cHadRegAux r k hk).eval
  | 0, _, _ => by
      rw [cHadRegAux_zero, Circuit.eval_identity, one_mul, mul_one]
  | k + 1, hk, hne => by
      have ih := cHadRegAux_comm_H r q k (by omega) fun i ↦ hne ⟨i.val, by omega⟩
      have hlast := eval_H_comm (hne ⟨k, Nat.lt_succ_self k⟩)
      rw [cHadRegAux_succ, Circuit.eval_seq, mul_assoc, ih, ← mul_assoc, hlast, mul_assoc]
private theorem cHadRegAux_eval_mul_self {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHadRegAux r k hk).eval * (cHadRegAux r k hk).eval = 1
  | 0, _ => by rw [cHadRegAux_zero, Circuit.eval_identity, mul_one]
  | k + 1, hk => by
      have ih := cHadRegAux_eval_mul_self r k (by omega)
      have hcomm := cHadRegAux_comm_H r (r ⟨k, hk⟩) k (by omega) fun i ↦
        r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
      rw [cHadRegAux_succ, Circuit.eval_seq, mul_assoc,
          ← mul_assoc (cHadRegAux r k (by omega)).eval, hcomm,
          mul_assoc (Circuit.H (r ⟨k, hk⟩)).eval, ih, mul_one, eval_H_mul_self]
@[simp]
private theorem cHadReg_eval_mul_self {n K : ℕ} (r : QRegister K n) :
    (cHadReg r).eval * (cHadReg r).eval = 1 := cHadRegAux_eval_mul_self r K le_rfl
private theorem eval_H_comm_embedMatrix {n m : ℕ} {q : Wire n} {r₂ : QRegister m n}
    (hq : ∀ j : Fin m, q ≠ r₂ j) (M : Operator (2 ^ m)) :
    (Circuit.H q).eval.1 * r₂.embedMatrix M = r₂.embedMatrix M * (Circuit.H q).eval.1 := by
  have hDisj : (QRegister.singleton q).DisjointWires r₂ := by
    rw [QRegister.disjoint_iff]
    intro i j
    fin_cases i
    exact hq j
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  exact (QRegister.singleton q).embedMatrix_comm_of_disjoint r₂ hDisj (PrimitiveGate.eval .H).1 M
private theorem cHadRegAux_comm_embedMatrix_of_disjoint {n K m : ℕ}
    (r₁ : QRegister K n) (r₂ : QRegister m n) (hDisj : r₁.DisjointWires r₂)
    (M : Operator (2 ^ m)) : ∀ (k : ℕ) (hk : k ≤ K),
      (cHadRegAux r₁ k hk).eval.1 * r₂.embedMatrix M =
        r₂.embedMatrix M * (cHadRegAux r₁ k hk).eval.1
  | 0, _ => by
      rw [cHadRegAux_zero, Circuit.eval_identity, OneMemClass.coe_one,
          Matrix.one_mul, Matrix.mul_one]
  | k + 1, hk => by
      have ih := cHadRegAux_comm_embedMatrix_of_disjoint r₁ r₂ hDisj M k (by omega)
      have hlast := eval_H_comm_embedMatrix (fun j ↦ hDisj.ne ⟨k, hk⟩ j) M
      rw [cHadRegAux_succ, Circuit.eval_seq, Submonoid.coe_mul,
          Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hlast, Matrix.mul_assoc]
theorem cHadReg_comm_embedMatrix_of_disjoint {n K m : ℕ}
    (r₁ : QRegister K n) (r₂ : QRegister m n) (hDisj : r₁.DisjointWires r₂)
    (M : Operator (2 ^ m)) :
    (cHadReg r₁).eval.1 * r₂.embedMatrix M = r₂.embedMatrix M * (cHadReg r₁).eval.1 :=
  cHadRegAux_comm_embedMatrix_of_disjoint r₁ r₂ hDisj M K le_rfl
theorem cHadReg_comm_embedUnitary_of_disjoint {n K m : ℕ}
    (r₁ : QRegister K n) (r₂ : QRegister m n) (hDisj : r₁.DisjointWires r₂) (u : Unitary (2 ^ m)) :
    (cHadReg r₁).eval * r₂.embedUnitary u = r₂.embedUnitary u * (cHadReg r₁).eval := by
  apply Subtype.ext
  exact cHadReg_comm_embedMatrix_of_disjoint r₁ r₂ hDisj u.1
theorem cHadReg_comm_basisOutcomeProjector {n K m : ℕ}
    (r₁ : QRegister K n) (r₂ : QRegister m n) (hDisj : r₁.DisjointWires r₂) (o : Fin (2 ^ m)) :
    (cHadReg r₁).eval.1 * r₂.basisOutcomeProjector o =
      r₂.basisOutcomeProjector o * (cHadReg r₁).eval.1 :=
  cHadReg_comm_embedMatrix_of_disjoint r₁ r₂ hDisj (compProj o)
private theorem cHadRegAux_comm_of_disjoint {n K₁ K₂ : ℕ}
    (r₁ : QRegister K₁ n) (r₂ : QRegister K₂ n) (hDisj : r₁.DisjointWires r₂) :
    ∀ (k : ℕ) (hk : k ≤ K₁), (cHadRegAux r₁ k hk).eval * (cHadReg r₂).eval =
        (cHadReg r₂).eval * (cHadRegAux r₁ k hk).eval
  | 0, _ => by
      rw [cHadRegAux_zero, Circuit.eval_identity, one_mul, mul_one]
  | k + 1, hk => by
      have ih := cHadRegAux_comm_of_disjoint r₁ r₂ hDisj k (by omega)
      have hlast : (Circuit.H (r₁ ⟨k, hk⟩)).eval * (cHadReg r₂).eval =
          (cHadReg r₂).eval * (Circuit.H (r₁ ⟨k, hk⟩)).eval :=
        (cHadRegAux_comm_H r₂ (r₁ ⟨k, hk⟩) K₂ le_rfl
          (fun j ↦ (hDisj.ne ⟨k, hk⟩ ⟨j.val, by omega⟩).symm)).symm
      rw [cHadRegAux_succ, Circuit.eval_seq, mul_assoc, ih, ← mul_assoc, hlast, mul_assoc]
private theorem cHadReg_comm_of_disjoint {n K₁ K₂ : ℕ}
    (r₁ : QRegister K₁ n) (r₂ : QRegister K₂ n) (hDisj : r₁.DisjointWires r₂) :
    (cHadReg r₁).eval * (cHadReg r₂).eval = (cHadReg r₂).eval * (cHadReg r₁).eval :=
  cHadRegAux_comm_of_disjoint r₁ r₂ hDisj K₁ le_rfl
private theorem singleHad_conj_phase_ket {n : ℕ} (q : Wire n) (b : BitAssignment n → ZMod 2)
    (hb : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → b α₁ = b α₂)
    (α : BitAssignment n) :
    let U₁ : Unitary (2 ^ n) :=
      bellDiagSign (fun g ↦ decide (b (basisBits n g) * basisBits n g q = 1))
    ((Circuit.H q).eval * U₁ * (Circuit.H q).eval).1.mulVec (ket α) =
      ket (Function.update α q (α q + b α)) := by
  intro U₁
  have hb0 : b (Function.update α q 0) = b α := hb _ _ fun w hw ↦ Function.update_of_ne hw _ _
  have hb1 : b (Function.update α q 1) = b α := hb _ _ fun w hw ↦ Function.update_of_ne hw _ _
  have hMid : U₁.1.mulVec ((Circuit.H q).eval.1.mulVec (ket α)) =
      (Circuit.H q).eval.1.mulVec (ket (Function.update α q (α q + b α))) := by
    rw [ket_H q α, ket_H q (Function.update α q (α q + b α)),
        Function.update_idem, Function.update_idem, Function.update_self,
        Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul]
    dsimp only [U₁]
    rw [bellDiagSign_mulVec_ket, bellDiagSign_mulVec_ket]
    have hEq0 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 0)) =
        Function.update α q 0 := (basisBitsEquiv n).apply_symm_apply _
    have hEq1 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 1)) =
        Function.update α q 1 := (basisBitsEquiv n).apply_symm_apply _
    simp only [hEq0, hEq1, hb0, hb1, Function.update_self, mul_zero, mul_one]
    rcases bit_cases (α q) with hq | hq <;> rcases bit_cases (b α) with hba | hba <;>
      simp [hq, hba, bitSign]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMid, Matrix.mulVec_mulVec]
  have hHH : (Circuit.H q).eval.1 * (Circuit.H q).eval.1 = 1 :=
    congrArg Subtype.val (eval_H_mul_self q)
  rw [hHH, Matrix.one_mulVec]
private theorem comm_H_bellDiagSign_of_ignores {n : ℕ} (q : Wire n) (p : BitAssignment n → Bool)
    (hp : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → p α₁ = p α₂) :
    (Circuit.H q).eval * bellDiagSign (fun g ↦ p (basisBits n g)) =
      bellDiagSign (fun g ↦ p (basisBits n g)) * (Circuit.H q).eval := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro α
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      bellDiagSign_mulVec_ket, Matrix.mulVec_smul, ket_H q α,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      bellDiagSign_mulVec_ket, bellDiagSign_mulVec_ket]
  have hS : basisBits n ((basisBitsEquiv n).symm α) = α := (basisBitsEquiv n).apply_symm_apply _
  have h0 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 0)) =
      Function.update α q 0 := (basisBitsEquiv n).apply_symm_apply _
  have h1 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 1)) =
      Function.update α q 1 := (basisBitsEquiv n).apply_symm_apply _
  rw [hS, h0, h1, hp (Function.update α q 0) α (fun w hw ↦ Function.update_of_ne hw 0 α),
      hp (Function.update α q 1) α (fun w hw ↦ Function.update_of_ne hw 1 α)]
  by_cases hpa : p α <;> simp [hpa, smul_add, smul_smul, mul_comm]
private theorem cHadRegAux_comm_bellDiagSign {n K : ℕ} (r : QRegister K n)
    (p : BitAssignment n → Bool) : ∀ (k : ℕ) (hk : k ≤ K),
      (∀ (i : Fin k) (α₁ α₂ : BitAssignment n),
        (∀ w, w ≠ r ⟨i.val, by omega⟩ → α₁ w = α₂ w) → p α₁ = p α₂) →
      (cHadRegAux r k hk).eval * bellDiagSign (fun g ↦ p (basisBits n g)) =
        bellDiagSign (fun g ↦ p (basisBits n g)) * (cHadRegAux r k hk).eval
  | 0, _, _ => by
      rw [cHadRegAux_zero, Circuit.eval_identity, one_mul, mul_one]
  | k + 1, hk, hp => by
      have ihStep := cHadRegAux_comm_bellDiagSign r p k (by omega)
        fun i α₁ α₂ h ↦ hp ⟨i.val, by omega⟩ α₁ α₂ h
      have hlast := comm_H_bellDiagSign_of_ignores (r ⟨k, hk⟩) p (hp ⟨k, Nat.lt_succ_self k⟩)
      rw [cHadRegAux_succ, Circuit.eval_seq, mul_assoc, ihStep, ← mul_assoc, hlast, mul_assoc]
private theorem bellDiagSign_sum_zero {n : ℕ} (F : Fin 0 → Fin (2 ^ n) → ZMod 2) :
    (bellDiagSign fun g ↦ decide ((∑ i : Fin 0, F i g) = 1)) = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro α
  rw [bellDiagSign_mulVec_ket, OneMemClass.coe_one, Matrix.one_mulVec]
  simp
private theorem bellDiagSign_sum_succ {n m : ℕ} (r : QRegister m n)
    (b : Fin m → BitAssignment n → ZMod 2) (k : ℕ) (hk : k + 1 ≤ m) : (bellDiagSign fun g ↦
      decide ((∑ i : Fin (k + 1), b ⟨i.val, by omega⟩ (basisBits n g) *
        basisBits n g (r ⟨i.val, by omega⟩)) = 1)) = (bellDiagSign fun g ↦
      decide (b ⟨k, hk⟩ (basisBits n g) * basisBits n g (r ⟨k, hk⟩) = 1)) * (bellDiagSign fun g ↦
      decide ((∑ i : Fin k, b ⟨i.val, by omega⟩ (basisBits n g) *
        basisBits n g (r ⟨i.val, by omega⟩)) = 1)) := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro α
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, bellDiagSign_mulVec_ket, bellDiagSign_mulVec_ket,
      Matrix.mulVec_smul, bellDiagSign_mulVec_ket, smul_smul]
  have hα : basisBits n ((basisBitsEquiv n).symm α) = α := (basisBitsEquiv n).apply_symm_apply _
  simp only [hα]
  refine congrArg (· • ket α) ?_
  rw [Fin.sum_univ_castSucc]
  dsimp only [Fin.val_castSucc, Fin.val_last]
  rw [sign_decide_zmod2_add, mul_comm]
private theorem update_prefix_dite_eq {n m : ℕ} (r : QRegister m n)
    (k : ℕ) (hk : k + 1 ≤ m) (β : BitAssignment n) (δ : Fin m → ZMod 2) : Function.update
      (fun w ↦ if h : ∃ i : Fin k, w = r ⟨i.val, by omega⟩ then
        β w + δ ⟨h.choose.val, by omega⟩ else β w) (r ⟨k, hk⟩) (β (r ⟨k, hk⟩) + δ ⟨k, hk⟩) =
    (fun w ↦ if h : ∃ i : Fin (k + 1), w = r ⟨i.val, by omega⟩ then
      β w + δ ⟨h.choose.val, by omega⟩ else β w) := by
  funext w
  by_cases hwq : w = r ⟨k, hk⟩
  · subst hwq
    rw [Function.update_self]
    have hexSucc : ∃ i : Fin (k + 1), r ⟨k, hk⟩ = r ⟨i.val, by omega⟩ :=
      ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩
    rw [dite_eq_left hexSucc]
    have hch : (⟨hexSucc.choose.val, by omega⟩ : Fin m) = ⟨k, hk⟩ :=
      r.wires.injective hexSucc.choose_spec.symm
    rw [hch]
  · rw [Function.update_of_ne hwq]
    by_cases hex : ∃ i : Fin k, w = r ⟨i.val, by omega⟩
    · obtain ⟨i₀, hi₀⟩ := hex
      have hex1 : ∃ i : Fin (k + 1), w = r ⟨i.val, by omega⟩ := ⟨⟨i₀.val, by omega⟩, hi₀⟩
      rw [dite_eq_left ⟨i₀, hi₀⟩, dite_eq_left hex1]
      have hch0 : (⟨(Exists.choose
          (⟨i₀, hi₀⟩ : ∃ i : Fin k, w = r ⟨i.val, by omega⟩)).val, by omega⟩ : Fin m) =
          ⟨i₀.val, by omega⟩ := r.wires.injective ((Exists.choose_spec
          (⟨i₀, hi₀⟩ : ∃ i : Fin k, w = r ⟨i.val, by omega⟩)).symm.trans hi₀)
      have hch1 : (⟨hex1.choose.val, by omega⟩ : Fin m) = ⟨i₀.val, by omega⟩ :=
        r.wires.injective (hex1.choose_spec.symm.trans hi₀)
      rw [hch0, hch1]
    · have hex1 : ¬ ∃ i : Fin (k + 1), w = r ⟨i.val, by omega⟩ := fun ⟨i, hi⟩ ↦ by
        by_cases hik : i.val = k
        · exact hwq (hi.trans (congrArg r.wires (Fin.ext (by dsimp; omega))))
        · exact hex ⟨⟨i.val, by omega⟩, hi⟩
      rw [dite_eq_right hex, dite_eq_right hex1]
private theorem cHadRegAux_conj_phase_ket {n K : ℕ} (r : QRegister K n)
    (b : Fin K → BitAssignment n → ZMod 2) (hb : ∀ (i : Fin K) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ t : Fin K, w ≠ r t) → α₁ w = α₂ w) → b i α₁ = b i α₂) :
    ∀ (k : ℕ) (hk : k ≤ K) (β : BitAssignment n), ((cHadRegAux r k hk).eval * bellDiagSign (fun g ↦
          decide ((∑ i : Fin k, b ⟨i.val, by omega⟩ (basisBits n g) *
            basisBits n g (r ⟨i.val, by omega⟩)) = 1)) *
        (cHadRegAux r k hk).eval).1.mulVec (ket β) =
        ket (fun w ↦ if h : ∃ i : Fin k, w = r ⟨i.val, by omega⟩ then
          β w + b ⟨h.choose.val, by omega⟩ β else β w) := by
  intro k
  induction k with
  | zero =>
      intro hk β
      rw [bellDiagSign_sum_zero, cHadRegAux_zero, Circuit.eval_identity,
          mul_one, mul_one, OneMemClass.coe_one, Matrix.one_mulVec]
      simp
  | succ k ih =>
      intro hk β
      let U_pref : Unitary (2 ^ n) := bellDiagSign fun g ↦
        decide ((∑ i : Fin (k + 1), b ⟨i.val, by omega⟩ (basisBits n g) *
          basisBits n g (r ⟨i.val, by omega⟩)) = 1)
      let q := r ⟨k, hk⟩
      let p_prev : BitAssignment n → Bool := fun α ↦
        decide ((∑ i : Fin k, b ⟨i.val, by omega⟩ α * α (r ⟨i.val, by omega⟩)) = 1)
      let p_one : BitAssignment n → Bool := fun α ↦ decide (b ⟨k, hk⟩ α * α q = 1)
      let U_prev : Unitary (2 ^ n) := bellDiagSign fun g ↦ p_prev (basisBits n g)
      let U_one : Unitary (2 ^ n) := bellDiagSign fun g ↦ p_one (basisBits n g)
      have hU_split : U_pref = U_one * U_prev := bellDiagSign_sum_succ r b k hk
      have hCommH_Had : (cHadRegAux r k (by omega)).eval * (Circuit.H q).eval =
          (Circuit.H q).eval * (cHadRegAux r k (by omega)).eval :=
        cHadRegAux_comm_H r q k (by omega)
          (fun i ↦ r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))
      have hCommH_Prev : (Circuit.H q).eval * U_prev = U_prev * (Circuit.H q).eval :=
        comm_H_bellDiagSign_of_ignores q p_prev fun α₁ α₂ h ↦ by
          dsimp only [p_prev]
          congr 1; congr 1; refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hri : r ⟨i.val, by omega⟩ ≠ q :=
            r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
          rw [h _ hri, hb ⟨i.val, by omega⟩ α₁ α₂ (fun w hw ↦ h w (hw ⟨k, hk⟩))]
      have hCommHad_One : (cHadRegAux r k (by omega)).eval * U_one =
          U_one * (cHadRegAux r k (by omega)).eval :=
        cHadRegAux_comm_bellDiagSign r p_one k (by omega) fun i α₁ α₂ h ↦ by
          dsimp only [p_one]
          have hqi : q ≠ r ⟨i.val, by omega⟩ :=
            r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
          rw [h q hqi, hb ⟨k, hk⟩ α₁ α₂ (fun w hw ↦ h w (hw ⟨i.val, by omega⟩))]
      have hFactor : (cHadRegAux r (k + 1) hk).eval * U_pref * (cHadRegAux r (k + 1) hk).eval =
          ((Circuit.H q).eval * U_one * (Circuit.H q).eval) *
            ((cHadRegAux r k (by omega)).eval * U_prev * (cHadRegAux r k (by omega)).eval) := by
        simp only [cHadRegAux_succ, Circuit.eval_seq, hU_split, mul_assoc]
        rw [← mul_assoc (cHadRegAux r k (by omega)).eval U_one, hCommHad_One, mul_assoc U_one,
            ← mul_assoc U_prev (Circuit.H q).eval, ← hCommH_Prev, mul_assoc (Circuit.H q).eval,
            ← mul_assoc (cHadRegAux r k (by omega)).eval (Circuit.H q).eval, hCommH_Had,
            mul_assoc (Circuit.H q).eval]
      let β_prev : BitAssignment n := fun w ↦ if h : ∃ i : Fin k, w = r ⟨i.val, by omega⟩ then
          β w + b ⟨h.choose.val, by omega⟩ β else β w
      have ihStep : ((cHadRegAux r k (by omega)).eval * U_prev *
          (cHadRegAux r k (by omega)).eval).1.mulVec (ket β) = ket β_prev := ih (by omega) β
      rw [show (bellDiagSign _) = U_pref from rfl,
          hFactor, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ihStep,
          singleHad_conj_phase_ket q (b ⟨k, hk⟩)
            (fun α₁ α₂ h ↦ hb ⟨k, hk⟩ α₁ α₂ fun w hw ↦ h w (hw ⟨k, hk⟩)) β_prev]
      have hb_prev : b ⟨k, hk⟩ β_prev = b ⟨k, hk⟩ β :=
        hb ⟨k, hk⟩ β_prev β fun w' hw' ↦ dite_eq_right (fun ⟨i, hi⟩ ↦ hw' ⟨i.val, by omega⟩ hi)
      have hPrevQ : β_prev q = β q := dite_eq_right fun ⟨i, hi⟩ ↦
        r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)) hi.symm
      rw [hb_prev, hPrevQ]
      exact congrArg ket (update_prefix_dite_eq r k hk β (fun t ↦ b t β))
private theorem cHadReg_conj_phase_ket {n K : ℕ} (r : QRegister K n)
    (b : Fin K → BitAssignment n → ZMod 2) (hb : ∀ (i : Fin K) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ t : Fin K, w ≠ r t) → α₁ w = α₂ w) → b i α₁ = b i α₂) (β : BitAssignment n) :
    ((cHadReg r).eval * bellDiagSign (fun g ↦
        decide ((∑ i : Fin K, b i (basisBits n g) * basisBits n g (r i)) = 1)) *
      (cHadReg r).eval).1.mulVec (ket β) = ket (writeReg β r (fun i ↦ β (r i) + b i β)) := by
  have hAux := cHadRegAux_conj_phase_ket r b hb K le_rfl β
  have hUEq : (bellDiagSign fun g : Fin (2 ^ n) ↦
      decide ((∑ i : Fin K, b ⟨i.val, by omega⟩ (basisBits n g) *
        basisBits n g (r ⟨i.val, by omega⟩)) = 1)) = bellDiagSign (fun g ↦
        decide ((∑ i : Fin K, b i (basisBits n g) * basisBits n g (r i)) = 1)) :=
    congrArg bellDiagSign (funext fun _ ↦ rfl)
  rw [hUEq] at hAux
  dsimp only [cHadReg]
  rw [hAux]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i₀, rfl⟩ := hw
    have hex : ∃ i : Fin K, r i₀ = r ⟨i.val, by omega⟩ := ⟨i₀, rfl⟩
    rw [dite_eq_left hex, writeReg_apply_reg]
    have hch : (⟨hex.choose.val, by omega⟩ : Fin K) = i₀ := r.wires.injective hex.choose_spec.symm
    rw [hch]
  · have hnot : ¬ ∃ i : Fin K, w = r ⟨i.val, by omega⟩ :=
      fun ⟨i, hi⟩ ↦ hw ⟨⟨i.val, by omega⟩, hi.symm⟩
    rw [dite_eq_right hnot, writeReg_apply_of_not_mem _ _ _ _ hw]
/-! ## Section 3: Bitwise XOR, Transversal CNOT/CZ Walls, & Symbolic `SlotKLens` -/
/-- Bitwise XOR on `Fin (2 ^ K)` via `basisBitsEquiv K`. -/
noncomputable def xorK {K : ℕ} (a b : Fin (2 ^ K)) : Fin (2 ^ K) :=
  (basisBitsEquiv K).symm (fun i ↦ basisBits K a i + basisBits K b i)
@[simp]
private theorem basisBits_xorK {K : ℕ} (a b : Fin (2 ^ K)) :
    basisBits K (xorK a b) = fun i ↦ basisBits K a i + basisBits K b i :=
  (basisBitsEquiv K).apply_symm_apply _
@[simp]
theorem xorK_self {K : ℕ} (a : Fin (2 ^ K)) : xorK a a = 0 := by
  rw [← (basisBitsEquiv K).apply_eq_iff_eq]
  change basisBits K (xorK a a) = basisBits K 0
  rw [basisBits_xorK]
  funext i
  rw [zmod2_add_self]
  simp [-Nat.reducePow, basisBits_eq_div_mod]
@[simp]
private theorem xorK_zero_right {K : ℕ} (a : Fin (2 ^ K)) : xorK a 0 = a := by
  rw [← (basisBitsEquiv K).apply_eq_iff_eq]
  change basisBits K (xorK a 0) = basisBits K a
  rw [basisBits_xorK]
  funext i
  have h0 : basisBits K 0 i = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
  rw [h0, add_zero]
@[simp]
theorem xorK_zero_left {K : ℕ} (a : Fin (2 ^ K)) : xorK 0 a = a := by
  rw [← (basisBitsEquiv K).apply_eq_iff_eq]
  change basisBits K (xorK 0 a) = basisBits K a
  rw [basisBits_xorK]
  funext i
  have h0 : basisBits K 0 i = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
  rw [h0, zero_add]
theorem xorK_comm {K : ℕ} (a b : Fin (2 ^ K)) : xorK a b = xorK b a := by
  simp only [xorK, add_comm]
private theorem xorK_assoc {K : ℕ} (a b c : Fin (2 ^ K)) :
    xorK (xorK a b) c = xorK a (xorK b c) := by
  rw [← (basisBitsEquiv K).apply_eq_iff_eq]
  change basisBits K (xorK (xorK a b) c) = basisBits K (xorK a (xorK b c))
  simp only [basisBits_xorK, add_assoc]
@[simp]
theorem xorK_cancel_right {K : ℕ} (a b : Fin (2 ^ K)) : xorK (xorK a b) b = a := by
  rw [xorK_assoc, xorK_self, xorK_zero_right]
@[simp]
private theorem xorK_cancel_left {K : ℕ} (a b : Fin (2 ^ K)) : xorK a (xorK a b) = b := by
  rw [← xorK_assoc, xorK_self, xorK_zero_left]
/-- Prefix transversal `CNOT` wall from `rCtrl` onto `rTgt`. -/
def cCnotRegAux {n K : ℕ} (rCtrl rTgt : QRegister K n) (hDisj : rCtrl.DisjointWires rTgt) :
    (k : ℕ) → k ≤ K → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      cCnotRegAux rCtrl rTgt hDisj k (by omega) ;;ᶜ
        Circuit.CNOT (rCtrl ⟨k, hk⟩) (rTgt ⟨k, hk⟩) (hDisj.ne ⟨k, hk⟩ ⟨k, hk⟩)
@[simp]
private theorem cCnotRegAux_zero {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) (hk : 0 ≤ K) :
    cCnotRegAux rCtrl rTgt hDisj 0 hk = .identity := rfl
private theorem cCnotRegAux_succ {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) (k : ℕ) (hk : k + 1 ≤ K) :
    cCnotRegAux rCtrl rTgt hDisj (k + 1) hk = cCnotRegAux rCtrl rTgt hDisj k (by omega) ;;ᶜ
        Circuit.CNOT (rCtrl ⟨k, hk⟩) (rTgt ⟨k, hk⟩) (hDisj.ne ⟨k, hk⟩ ⟨k, hk⟩) := rfl
/-- Transversal `K`-wire `CNOT` wall from `rCtrl` onto `rTgt` (`0 T`, `0 TOFF`). -/
def cCnotReg {n K : ℕ} (rCtrl rTgt : QRegister K n) (hDisj : rCtrl.DisjointWires rTgt) :
    Circuit n := cCnotRegAux rCtrl rTgt hDisj K le_rfl
private theorem cCnotRegAux_count_t {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) :
    ∀ (k : ℕ) (hk : k ≤ K), (cCnotRegAux rCtrl rTgt hDisj k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, _ => by simp [cCnotRegAux, cCnotRegAux_count_t rCtrl rTgt hDisj k (by omega)]
private theorem cCnotRegAux_count_toff {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) :
    ∀ (k : ℕ) (hk : k ≤ K), (cCnotRegAux rCtrl rTgt hDisj k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, _ => by simp [cCnotRegAux, cCnotRegAux_count_toff rCtrl rTgt hDisj k (by omega)]
@[simp]
theorem cCnotReg_count_t {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) : (cCnotReg rCtrl rTgt hDisj).count .T = 0 :=
  cCnotRegAux_count_t rCtrl rTgt hDisj K le_rfl
@[simp]
theorem cCnotReg_count_toff {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) : (cCnotReg rCtrl rTgt hDisj).count .TOFF = 0 :=
  cCnotRegAux_count_toff rCtrl rTgt hDisj K le_rfl
private theorem cCnotRegAux_mulVec_ket {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) : ∀ (k : ℕ) (hk : k ≤ K) (β : BitAssignment n),
      (cCnotRegAux rCtrl rTgt hDisj k hk).eval.1.mulVec (ket β) =
        ket (fun w ↦ if h : ∃ i : Fin k, w = rTgt ⟨i.val, by omega⟩ then
          β w + β (rCtrl ⟨h.choose.val, by omega⟩) else β w) := by
  intro k
  induction k with
  | zero =>
      intro hk β
      rw [cCnotRegAux_zero, Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec]
      simp
  | succ k ih =>
      intro hk β
      let β_prev : BitAssignment n := fun w ↦ if h : ∃ i : Fin k, w = rTgt ⟨i.val, by omega⟩ then
          β w + β (rCtrl ⟨h.choose.val, by omega⟩) else β w
      have ihStep : (cCnotRegAux rCtrl rTgt hDisj k (by omega)).eval.1.mulVec (ket β) =
          ket β_prev := ih (by omega) β
      have hPrevC : β_prev (rCtrl ⟨k, hk⟩) = β (rCtrl ⟨k, hk⟩) :=
        dite_eq_right fun ⟨i, hi⟩ ↦ hDisj.ne ⟨k, hk⟩ ⟨i.val, by omega⟩ hi
      have hPrevT : β_prev (rTgt ⟨k, hk⟩) = β (rTgt ⟨k, hk⟩) := dite_eq_right fun ⟨i, hi⟩ ↦
          rTgt.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)) hi.symm
      rw [cCnotRegAux_succ, eval_seq_mulVec, ihStep, ket_CNOT, hPrevT, hPrevC]
      exact congrArg ket (update_prefix_dite_eq rTgt k hk β fun i ↦ β (rCtrl i))
private theorem cCnotReg_mulVec_ket {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) (β : BitAssignment n) :
    (cCnotReg rCtrl rTgt hDisj).eval.1.mulVec (ket β) =
      ket (writeReg β rTgt (fun i ↦ β (rTgt i) + β (rCtrl i))) := by
  dsimp only [cCnotReg]
  rw [cCnotRegAux_mulVec_ket]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w ∈ Set.range rTgt.wires
  · obtain ⟨i₀, rfl⟩ := hw
    have hex : ∃ i : Fin K, rTgt i₀ = rTgt ⟨i.val, by omega⟩ := ⟨i₀, rfl⟩
    rw [dite_eq_left hex, writeReg_apply_reg]
    have hch : (⟨hex.choose.val, by omega⟩ : Fin K) = i₀ :=
      rTgt.wires.injective hex.choose_spec.symm
    rw [hch]
  · have hnot : ¬ ∃ i : Fin K, w = rTgt ⟨i.val, by omega⟩ :=
      fun ⟨i, hi⟩ ↦ hw ⟨⟨i.val, by omega⟩, hi.symm⟩
    rw [dite_eq_right hnot, writeReg_apply_of_not_mem _ _ _ _ hw]
theorem cCnotReg_mulVec_single {n K : ℕ} (rCtrl rTgt : QRegister K n)
    (hDisj : rCtrl.DisjointWires rTgt) (g : Fin (2 ^ n)) :
    (cCnotReg rCtrl rTgt hDisj).eval.1.mulVec (Pi.single g 1) =
      Pi.single (rTgt.replaceIndex g (xorK (rTgt.extractIndex g) (rCtrl.extractIndex g))) 1 := by
  rw [← ket_basisBits_eq_single g, cCnotReg_mulVec_ket]
  have hWr : writeReg (basisBits n g) rTgt
      (fun i ↦ basisBits n g (rTgt i) + basisBits n g (rCtrl i)) =
      basisBits n (rTgt.replaceIndex g (xorK (rTgt.extractIndex g) (rCtrl.extractIndex g))) := by
    dsimp only [writeReg, xorK]
    rw [(basisBitsEquiv n).symm_apply_apply]
    refine congrArg (fun v ↦ basisBits n (rTgt.replaceIndex g v)) ?_
    refine congrArg (basisBitsEquiv K).symm (funext fun i ↦ ?_)
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  rw [hWr, ket_basisBits_eq_single]
/-- `0 T`, `0 TOFF` Bell-pair preparation on `(rMeas, rHeld)`:
`H^⊗K` on `rHeld` then CNOT `rHeld → rMeas`. -/
def cBellPrep {n K : ℕ} (rMeas rHeld : QRegister K n) (hMH : rMeas.DisjointWires rHeld) :
    Circuit n := cHadReg rHeld ;;ᶜ cCnotReg rHeld rMeas (disjointWires_symm hMH)
@[simp]
theorem cBellPrep_count_t {n K : ℕ} (rMeas rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld) : (cBellPrep rMeas rHeld hMH).count .T = 0 := by
  rw [cBellPrep, Circuit.count_seq, cHadReg_count_t, cCnotReg_count_t]
@[simp]
theorem cBellPrep_count_toff {n K : ℕ} (rMeas rHeld : QRegister K n)
    (hMH : rMeas.DisjointWires rHeld) : (cBellPrep rMeas rHeld hMH).count .TOFF = 0 := by
  rw [cBellPrep, Circuit.count_seq, cHadReg_count_toff, cCnotReg_count_toff]
/-- Two-wire `CZ` gate decomposed as `H t ;;ᶜ CNOT c t ;;ᶜ H t` (`0 T`, `0 TOFF`). -/
def czCircuit {n : ℕ} (c t : Wire n) (hct : c ≠ t) : Circuit n :=
  Circuit.H t ;;ᶜ Circuit.CNOT c t hct ;;ᶜ Circuit.H t
@[simp]
theorem czCircuit_count_t {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).count .T = 0 := by
  simp [czCircuit]
@[simp]
theorem czCircuit_count_toff {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).count .TOFF = 0 := by
  simp [czCircuit]
private theorem czCircuit_eval_eq_bellDiagSign {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).eval =
      bellDiagSign (fun g ↦ decide (basisBits n g c * basisBits n g t = 1)) := by
  let D : Unitary (2 ^ n) := bellDiagSign (fun g ↦ decide (basisBits n g c * basisBits n g t = 1))
  have hConj : (Circuit.H t).eval * D * (Circuit.H t).eval = (Circuit.CNOT c t hct).eval := by
    apply Subtype.ext; apply matrix_ext_ket; intro β
    rw [singleHad_conj_phase_ket t (fun α ↦ α c) (fun _ _ h ↦ h c hct) β, ket_CNOT]
  rw [czCircuit, Circuit.eval_seq, Circuit.eval_seq, ← hConj]
  simp only [ ← mul_assoc, eval_H_mul_self, one_mul]
  rw [mul_assoc, eval_H_mul_self, mul_one]
/-- Prefix transversal `CZ` wall between `rHeld` and `rReg`. -/
def cHeldCzAllAux {n K : ℕ} (rHeld rReg : QRegister K n) (hHR : rHeld.DisjointWires rReg) :
    (k : ℕ) → k ≤ K → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      cHeldCzAllAux rHeld rReg hHR k (by omega) ;;ᶜ
        czCircuit (rHeld ⟨k, hk⟩) (rReg ⟨k, hk⟩) (hHR.ne ⟨k, hk⟩ ⟨k, hk⟩)
@[simp]
private theorem cHeldCzAllAux_zero {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) (hk : 0 ≤ K) :
    cHeldCzAllAux rHeld rReg hHR 0 hk = .identity := rfl
private theorem cHeldCzAllAux_succ {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) (k : ℕ) (hk : k + 1 ≤ K) :
    cHeldCzAllAux rHeld rReg hHR (k + 1) hk = cHeldCzAllAux rHeld rReg hHR k (by omega) ;;ᶜ
        czCircuit (rHeld ⟨k, hk⟩) (rReg ⟨k, hk⟩) (hHR.ne ⟨k, hk⟩ ⟨k, hk⟩) := rfl
/-- Transversal `K`-wire `CZ` wall between `rHeld` and `rReg` (`0 T`, `0 TOFF`). -/
def cHeldCzAll {n K : ℕ} (rHeld rReg : QRegister K n) (hHR : rHeld.DisjointWires rReg) :
    Circuit n := cHeldCzAllAux rHeld rReg hHR K le_rfl
private theorem cHeldCzAllAux_count_t {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHeldCzAllAux rHeld rReg hHR k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      rw [cHeldCzAllAux_succ, Circuit.count_seq,
          cHeldCzAllAux_count_t rHeld rReg hHR k (by omega), czCircuit_count_t]
private theorem cHeldCzAllAux_count_toff {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHeldCzAllAux rHeld rReg hHR k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      rw [cHeldCzAllAux_succ, Circuit.count_seq,
          cHeldCzAllAux_count_toff rHeld rReg hHR k (by omega), czCircuit_count_toff]
@[simp]
private theorem cHeldCzAll_count_t {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) : (cHeldCzAll rHeld rReg hHR).count .T = 0 :=
  cHeldCzAllAux_count_t rHeld rReg hHR K le_rfl
@[simp]
private theorem cHeldCzAll_count_toff {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) : (cHeldCzAll rHeld rReg hHR).count .TOFF = 0 :=
  cHeldCzAllAux_count_toff rHeld rReg hHR K le_rfl
private theorem cHeldCzAllAux_eval_eq_bellDiagSign {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) : ∀ (k : ℕ) (hk : k ≤ K),
      (cHeldCzAllAux rHeld rReg hHR k hk).eval = bellDiagSign (fun g ↦ decide ((∑ i : Fin k,
          basisBits n g (rHeld ⟨i.val, by omega⟩) * basisBits n g (rReg ⟨i.val, by omega⟩)) = 1))
  | 0, _ => by
      rw [cHeldCzAllAux_zero, Circuit.eval_identity, bellDiagSign_sum_zero]
  | k + 1, hk => by
      rw [cHeldCzAllAux_succ, Circuit.eval_seq,
          cHeldCzAllAux_eval_eq_bellDiagSign rHeld rReg hHR k (by omega),
          czCircuit_eval_eq_bellDiagSign]
      exact (bellDiagSign_sum_succ rReg (fun i α ↦ α (rHeld i)) k hk).symm
private theorem cHeldCzAll_eval_eq_bellDiagSign {n K : ℕ} (rHeld rReg : QRegister K n)
    (hHR : rHeld.DisjointWires rReg) : (cHeldCzAll rHeld rReg hHR).eval = bellDiagSign (fun g ↦
        decide ((∑ i : Fin K, basisBits n g (rHeld i) * basisBits n g (rReg i)) = 1)) := by
  dsimp only [cHeldCzAll]
  rw [cHeldCzAllAux_eval_eq_bellDiagSign]
/-- First `kData` wires of a combined `(kData + K)`-wire active register. -/
abbrev selDataInAct (K kData : ℕ) : QRegister kData (kData + K) :=
  QRegister.block 0 kData (by omega)
/-- Trailing `K` wires of a combined `(kData + K)`-wire active register. -/
abbrev selMeasInAct (K kData : ℕ) : QRegister K (kData + K) := QRegister.block kData K (by omega)
theorem selDataInAct_disj_selMeasInAct (K kData : ℕ) :
    (selDataInAct K kData).DisjointWires (selMeasInAct K kData) :=
  QRegister.block_disjoint_of_le 0 kData kData K (by omega) (by omega) (by omega)
private theorem qreg_ext_local {n k : ℕ} {r₁ r₂ : QRegister k n}
    (h : ∀ i : Fin k, r₁ i = r₂ i) : r₁ = r₂ := by
  ext i
  exact congrArg Fin.val (h i)
theorem concat_compose_selDataInAct {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas) :
    (rData.concat rMeas hDM).compose (selDataInAct K kData) = rData := qreg_ext_local fun i ↦ by
    have hEq : selDataInAct K kData i = Fin.castAdd K i := Fin.ext (by simp [selDataInAct])
    change (rData.concat rMeas hDM) (selDataInAct K kData i) = rData i
    rw [hEq, QRegister.concat_apply_left]
theorem concat_compose_selMeasInAct {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas) :
    (rData.concat rMeas hDM).compose (selMeasInAct K kData) = rMeas := qreg_ext_local fun j ↦ by
    have hEq : selMeasInAct K kData j = Fin.natAdd kData j := Fin.ext (by simp [selMeasInAct])
    change (rData.concat rMeas hDM) (selMeasInAct K kData j) = rMeas j
    rw [hEq, QRegister.concat_apply_right]
private theorem extractIndex_compose_eq_local {n m k : ℕ}
    (rOuter : QRegister m n) (rInner : QRegister k m) (g : Fin (2 ^ n)) :
    rInner.extractIndex (rOuter.extractIndex g) = (rOuter.compose rInner).extractIndex g := by
  rw [← (basisBitsEquiv k).apply_eq_iff_eq]
  funext i
  change basisBits k (rInner.extractIndex (rOuter.extractIndex g)) i =
    basisBits k ((rOuter.compose rInner).extractIndex g) i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex]
  rfl
private theorem replaceIndex_compose_eq_local {n m k : ℕ}
    (rOuter : QRegister m n) (rInner : QRegister k m) (g : Fin (2 ^ n)) (v : Fin (2 ^ k)) :
    rOuter.replaceIndex g (rInner.replaceIndex (rOuter.extractIndex g) v) =
      (rOuter.compose rInner).replaceIndex g v := by
  rw [← (basisBitsEquiv n).apply_eq_iff_eq]
  funext w
  change basisBits n _ w = basisBits n _ w
  by_cases hwOuter : w ∈ Set.range rOuter.wires
  · obtain ⟨u, rfl⟩ := hwOuter
    rw [QRegister.basisBits_replaceIndex_apply]
    by_cases huInner : u ∈ Set.range rInner.wires
    · obtain ⟨i, rfl⟩ := huInner
      change basisBits m (rInner.replaceIndex (rOuter.extractIndex g) v) (rInner i) =
        basisBits n ((rOuter.compose rInner).replaceIndex g v) ((rOuter.compose rInner) i)
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ huInner,
          QRegister.basisBits_extractIndex,
          QRegister.basisBits_replaceIndex_of_not_mem (rOuter.compose rInner) g v (rOuter u)
            (fun ⟨i, hi⟩ ↦ huInner ⟨i, rOuter.wires.injective hi⟩)]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwOuter,
        QRegister.basisBits_replaceIndex_of_not_mem (rOuter.compose rInner) g v w
          (fun ⟨i, hi⟩ ↦ hwOuter ⟨rInner i, hi⟩)]
/-- Abstract `K`-bit slot lens `(tbl, updSlot)` on `Fin (2 ^ kData)` (`rfl`-matched at `K = 18`). -/
structure SlotKLens (K kData : ℕ) where
  tbl : Fin (2 ^ kData) → Fin (2 ^ K)
  updSlot : Fin (2 ^ kData) → Fin (2 ^ K) → Fin (2 ^ kData)
  get_put : ∀ d v, tbl (updSlot d v) = v
  put_get : ∀ d, updSlot d (tbl d) = d
  put_put : ∀ d v₁ v₂, updSlot (updSlot d v₁) v₂ = updSlot d v₂
/-- `18`-bit specialization of `SlotKLens`. -/
abbrev Slot18Lens := SlotKLens 18
noncomputable def lensLoadPerm {K kData : ℕ} (L : SlotKLens K kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ K)) : Fin (2 ^ kData) × Fin (2 ^ K) :=
  (p.1, xorK p.2 (L.tbl p.1))
noncomputable def lensWritePerm {K kData : ℕ} (L : SlotKLens K kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ K)) : Fin (2 ^ kData) × Fin (2 ^ K) :=
  (L.updSlot p.1 (xorK (L.tbl p.1) p.2), p.2)
noncomputable def lensSwapPerm {K kData : ℕ} (L : SlotKLens K kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ K)) : Fin (2 ^ kData) × Fin (2 ^ K) :=
  (L.updSlot p.1 p.2, L.tbl p.1)
theorem lensLoadPerm_involutive {K kData : ℕ} (L : SlotKLens K kData) :
    Function.Involutive (lensLoadPerm L) := by
  rintro ⟨d, y⟩; dsimp only [lensLoadPerm]; rw [xorK_cancel_right]
theorem lensWritePerm_involutive {K kData : ℕ} (L : SlotKLens K kData) :
    Function.Involutive (lensWritePerm L) := by
  rintro ⟨d, y⟩; dsimp only [lensWritePerm]
  rw [L.get_put, L.put_put, xorK_cancel_right, L.put_get]
theorem lensSwapPerm_involutive {K kData : ℕ} (L : SlotKLens K kData) :
    Function.Involutive (lensSwapPerm L) := by
  rintro ⟨d, y⟩; dsimp only [lensSwapPerm]; rw [L.get_put, L.put_put, L.put_get]
abbrev extractPairK {K kData : ℕ} (g : Fin (2 ^ (kData + K))) : Fin (2 ^ kData) × Fin (2 ^ K) :=
  ((selDataInAct K kData).extractIndex g, (selMeasInAct K kData).extractIndex g)
noncomputable def liftPairIdxK {K kData : ℕ}
    (F : Fin (2 ^ kData) × Fin (2 ^ K) → Fin (2 ^ kData) × Fin (2 ^ K))
    (g : Fin (2 ^ (kData + K))) : Fin (2 ^ (kData + K)) :=
  let p := F (extractPairK g)
  (selMeasInAct K kData).replaceIndex ((selDataInAct K kData).replaceIndex g p.1) p.2
@[simp]
private theorem extractPairK_liftPairIdxK {K kData : ℕ}
    (F : Fin (2 ^ kData) × Fin (2 ^ K) → Fin (2 ^ kData) × Fin (2 ^ K))
    (g : Fin (2 ^ (kData + K))) : extractPairK (liftPairIdxK F g) = F (extractPairK g) := by
  dsimp only [extractPairK, liftPairIdxK]
  ext
  · rw [QRegister.extractIndex_replaceIndex_of_disjoint
        (selDataInAct K kData) (selMeasInAct K kData) (selDataInAct_disj_selMeasInAct K kData),
      QRegister.extractIndex_replaceIndex]
  · rw [QRegister.extractIndex_replaceIndex]
@[simp]
private theorem liftPairIdxK_comp {K kData : ℕ}
    (G F : Fin (2 ^ kData) × Fin (2 ^ K) → Fin (2 ^ kData) × Fin (2 ^ K))
    (g : Fin (2 ^ (kData + K))) :
    liftPairIdxK G (liftPairIdxK F g) = liftPairIdxK (fun p ↦ G (F p)) g := by
  have hEx := extractPairK_liftPairIdxK F g
  dsimp only [liftPairIdxK] at hEx ⊢
  rw [hEx, QRegister.replaceIndex_comm_of_disjoint
        (selDataInAct K kData) (selMeasInAct K kData) (selDataInAct_disj_selMeasInAct K kData),
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_replaceIndex]
@[simp]
private theorem liftPairIdxK_id {K kData : ℕ} (g : Fin (2 ^ (kData + K))) :
    liftPairIdxK id g = g := by
  dsimp only [liftPairIdxK, extractPairK, id]
  rw [QRegister.replaceIndex_extractIndex, QRegister.replaceIndex_extractIndex]
theorem liftPairIdxK_involutive {K kData : ℕ}
    {F : Fin (2 ^ kData) × Fin (2 ^ K) → Fin (2 ^ kData) × Fin (2 ^ K)}
    (hF : Function.Involutive F) : Function.Involutive (liftPairIdxK F) := fun g ↦ by
  rw [liftPairIdxK_comp, show (fun p ↦ F (F p)) = id from funext hF, liftPairIdxK_id]
noncomputable def lensLoadEquiv {K kData : ℕ} (L : SlotKLens K kData) :
    Equiv.Perm (Fin (2 ^ (kData + K))) := Equiv.ofBijective (liftPairIdxK (lensLoadPerm L))
    (liftPairIdxK_involutive (lensLoadPerm_involutive L)).bijective
noncomputable def lensWriteEquiv {K kData : ℕ} (L : SlotKLens K kData) :
    Equiv.Perm (Fin (2 ^ (kData + K))) := Equiv.ofBijective (liftPairIdxK (lensWritePerm L))
    (liftPairIdxK_involutive (lensWritePerm_involutive L)).bijective
noncomputable def lensSwapEquiv {K kData : ℕ} (L : SlotKLens K kData) :
    Equiv.Perm (Fin (2 ^ (kData + K))) := Equiv.ofBijective (liftPairIdxK (lensSwapPerm L))
    (liftPairIdxK_involutive (lensSwapPerm_involutive L)).bijective
noncomputable def uLensLoad {K kData : ℕ} (L : SlotKLens K kData) : Unitary (2 ^ (kData + K)) :=
  Operator.permutationUnitary (lensLoadEquiv L)
noncomputable def uLensWrite {K kData : ℕ} (L : SlotKLens K kData) : Unitary (2 ^ (kData + K)) :=
  Operator.permutationUnitary (lensWriteEquiv L)
noncomputable def uLensSwap {K kData : ℕ} (L : SlotKLens K kData) : Unitary (2 ^ (kData + K)) :=
  Operator.permutationUnitary (lensSwapEquiv L)
/-- Active-slot zero projector `P_slot0 L` on `(kData + K)` wires. -/
noncomputable def P_slot0 {K kData : ℕ} (L : SlotKLens K kData) : Operator (2 ^ (kData + K)) :=
  (uLensSwap L).1 * (selMeasInAct K kData).basisOutcomeProjector 0 * (uLensSwap L).1
private theorem permUnitary_mulVec_single_one_local {d : ℕ} (σ : Equiv.Perm (Fin d)) (w : Fin d) :
    (Operator.permutationUnitary σ).1.mulVec (Pi.single w 1) = Pi.single (σ w) 1 :=
  Operator.permutationUnitary_mulVec_single σ w 1
theorem embedUnitary_permutationUnitary_mulVec_single {n k : ℕ}
    (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k))) (g : Fin (2 ^ n)) :
    (r.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (Pi.single g 1) =
      Pi.single (r.replaceIndex g (σ (r.extractIndex g))) 1 := by
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      permUnitary_mulVec_single_one_local, QRegister.tensorState_single_replaceIndex]
private theorem basisBits_inj_local {m : ℕ} {x y : Fin (2 ^ m)}
    (h : ∀ w : Fin m, basisBits m x w = basisBits m y w) : x = y :=
  (basisBitsEquiv m).injective (funext h)
theorem embedUnitary_uLensLoad_mulVec_single {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) (g : Fin (2 ^ n)) :
    ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1.mulVec (Pi.single g 1) =
      Pi.single (rMeas.replaceIndex g
        (xorK (rMeas.extractIndex g) (L.tbl (rData.extractIndex g)))) 1 := by
  let rAct := rData.concat rMeas hDM
  let selD := selDataInAct K kData
  let selM := selMeasInAct K kData
  have hD : rAct.compose selD = rData := concat_compose_selDataInAct rData rMeas hDM
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  have hDg : selD.extractIndex (rAct.extractIndex g) = rData.extractIndex g :=
    (extractIndex_compose_eq_local rAct selD g).trans
      (congrArg (fun r : QRegister kData n ↦ r.extractIndex g) hD)
  have hMg : selM.extractIndex (rAct.extractIndex g) = rMeas.extractIndex g :=
    (extractIndex_compose_eq_local rAct selM g).trans
      (congrArg (fun r : QRegister K n ↦ r.extractIndex g) hM)
  dsimp only [uLensLoad]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let v := xorK (rMeas.extractIndex g) (L.tbl (rData.extractIndex g))
  have hApp : lensLoadEquiv L (rAct.extractIndex g) =
      selM.replaceIndex (rAct.extractIndex g) v := by
    change liftPairIdxK (lensLoadPerm L) (rAct.extractIndex g) = _
    dsimp only [liftPairIdxK, extractPairK, lensLoadPerm]
    rw [QRegister.replaceIndex_extractIndex, hMg, hDg]
  rw [hApp]
  exact (replaceIndex_compose_eq_local rAct selM g v).trans
    (congrArg (fun r : QRegister K n ↦ r.replaceIndex g v) hM)
theorem embedUnitary_uLensWrite_mulVec_single {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) (g : Fin (2 ^ n)) :
    ((rData.concat rMeas hDM).embedUnitary (uLensWrite L)).1.mulVec (Pi.single g 1) =
      Pi.single (rData.replaceIndex g (L.updSlot (rData.extractIndex g)
          (xorK (L.tbl (rData.extractIndex g)) (rMeas.extractIndex g)))) 1 := by
  let rAct := rData.concat rMeas hDM
  let selD := selDataInAct K kData
  let selM := selMeasInAct K kData
  have hD : rAct.compose selD = rData := concat_compose_selDataInAct rData rMeas hDM
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  have hDg : selD.extractIndex (rAct.extractIndex g) = rData.extractIndex g :=
    (extractIndex_compose_eq_local rAct selD g).trans
      (congrArg (fun r : QRegister kData n ↦ r.extractIndex g) hD)
  have hMg : selM.extractIndex (rAct.extractIndex g) = rMeas.extractIndex g :=
    (extractIndex_compose_eq_local rAct selM g).trans
      (congrArg (fun r : QRegister K n ↦ r.extractIndex g) hM)
  dsimp only [uLensWrite]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let dNew := L.updSlot (rData.extractIndex g)
    (xorK (L.tbl (rData.extractIndex g)) (rMeas.extractIndex g))
  have hApp : lensWriteEquiv L (rAct.extractIndex g) =
      selD.replaceIndex (rAct.extractIndex g) dNew := by
    change liftPairIdxK (lensWritePerm L) (rAct.extractIndex g) = _
    dsimp only [liftPairIdxK, extractPairK, lensWritePerm]
    rw [hDg, hMg]
    refine basisBits_inj_local fun w ↦ ?_
    by_cases hw : w ∈ Set.range selM.wires
    · obtain ⟨j, rfl⟩ := hw
      rw [QRegister.basisBits_replaceIndex_apply,
          QRegister.basisBits_replaceIndex_of_not_mem selD _ _ (selM j)
            (fun ⟨i, hi⟩ ↦ (selDataInAct_disj_selMeasInAct K kData).ne i j hi),
          ← hMg, QRegister.basisBits_extractIndex]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem selM _ _ w hw]
  rw [hApp]
  exact (replaceIndex_compose_eq_local rAct selD g dNew).trans
    (congrArg (fun r : QRegister kData n ↦ r.replaceIndex g dNew) hD)
theorem embedUnitary_uLensSwap_mulVec_single {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) (g : Fin (2 ^ n)) :
    ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1.mulVec (Pi.single g 1) =
      Pi.single (rMeas.replaceIndex
        (rData.replaceIndex g (L.updSlot (rData.extractIndex g) (rMeas.extractIndex g)))
        (L.tbl (rData.extractIndex g))) 1 := by
  let rAct := rData.concat rMeas hDM
  let selD := selDataInAct K kData
  let selM := selMeasInAct K kData
  have hD : rAct.compose selD = rData := concat_compose_selDataInAct rData rMeas hDM
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  have hDg : selD.extractIndex (rAct.extractIndex g) = rData.extractIndex g :=
    (extractIndex_compose_eq_local rAct selD g).trans
      (congrArg (fun r : QRegister kData n ↦ r.extractIndex g) hD)
  have hMg : selM.extractIndex (rAct.extractIndex g) = rMeas.extractIndex g :=
    (extractIndex_compose_eq_local rAct selM g).trans
      (congrArg (fun r : QRegister K n ↦ r.extractIndex g) hM)
  dsimp only [uLensSwap]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let dNew := L.updSlot (rData.extractIndex g) (rMeas.extractIndex g)
  let mNew := L.tbl (rData.extractIndex g)
  have hApp : lensSwapEquiv L (rAct.extractIndex g) =
      selM.replaceIndex (selD.replaceIndex (rAct.extractIndex g) dNew) mNew := by
    change liftPairIdxK (lensSwapPerm L) (rAct.extractIndex g) = _
    dsimp only [liftPairIdxK, extractPairK, lensSwapPerm]
    rw [hDg, hMg]
  rw [hApp]
  refine basisBits_inj_local fun w ↦ ?_
  by_cases hwAct : w ∈ Set.range rAct.wires
  · obtain ⟨u, rfl⟩ := hwAct
    rw [QRegister.basisBits_replaceIndex_apply]
    by_cases hu : u.val < kData
    · let i : Fin kData := ⟨u.val, hu⟩
      have huEq : u = selD i := Fin.ext (by simp [selD, selDataInAct, i])
      have hrD : rAct (selD i) = rData i := congrArg (fun r : QRegister kData n ↦ r i) hD
      rw [huEq, QRegister.basisBits_replaceIndex_of_not_mem selM _ _ (selD i)
            (fun ⟨j, hj⟩ ↦ (selDataInAct_disj_selMeasInAct K kData).ne i j hj.symm),
          QRegister.basisBits_replaceIndex_apply, hrD,
          QRegister.basisBits_replaceIndex_of_not_mem rMeas _ _ (rData i)
            (fun ⟨j, hj⟩ ↦ hDM.ne i j hj.symm), QRegister.basisBits_replaceIndex_apply]
    · have hltK : u.val - kData < K := by have := u.isLt; omega
      let j : Fin K := ⟨u.val - kData, hltK⟩
      have huEq : u = selM j := Fin.ext (by simp [selM, selMeasInAct, j]; omega)
      have hrM : rAct (selM j) = rMeas j := congrArg (fun r : QRegister K n ↦ r j) hM
      rw [huEq, QRegister.basisBits_replaceIndex_apply, hrM, QRegister.basisBits_replaceIndex_apply]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem rAct _ _ w hwAct,
        QRegister.basisBits_replaceIndex_of_not_mem rMeas _ _ w
          (fun ⟨j, hj⟩ ↦ hwAct ⟨selM j, (congrArg (fun r : QRegister K n ↦ r j) hM).trans hj⟩),
        QRegister.basisBits_replaceIndex_of_not_mem rData _ _ w
          (fun ⟨i, hi⟩ ↦ hwAct ⟨selD i, (congrArg (fun r : QRegister kData n ↦ r i) hD).trans hi⟩)]
private theorem uLensSwap_mul_self {K kData : ℕ} (L : SlotKLens K kData) :
    uLensSwap L * uLensSwap L = 1 := by
  apply Subtype.ext; apply matrix_ext_single; intro g
  rw [Submonoid.coe_mul, OneMemClass.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  dsimp only [uLensSwap]
  rw [permUnitary_mulVec_single_one_local, permUnitary_mulVec_single_one_local]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ (kData + K)) → ℂ)) ?_
  dsimp only [lensSwapEquiv]
  rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply]
  exact liftPairIdxK_involutive (lensSwapPerm_involutive L) g
private theorem embedMatrix_selMeas_proj0_mulVec_single {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (h : Fin (2 ^ n)) : ((rData.concat rMeas hDM).embedMatrix
      ((selMeasInAct K kData).basisOutcomeProjector 0)).mulVec (Pi.single h 1) =
      if rMeas.extractIndex h = 0 then Pi.single h 1 else 0 := by
  let rAct := rData.concat rMeas hDM
  let selM := selMeasInAct K kData
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  have hMh : selM.extractIndex (rAct.extractIndex h) = rMeas.extractIndex h :=
    (extractIndex_compose_eq_local rAct selM h).trans
      (congrArg (fun r : QRegister K n ↦ r.extractIndex h) hM)
  rw [rAct.embedMatrix_mulVec_single_factors, basisOutcomeProjector_zero_mulVec_single, hMh]
  by_cases hz : rMeas.extractIndex h = 0
  · simp only [hz, ↓reduceIte]
    rw [QRegister.tensorState_single_replaceIndex, QRegister.replaceIndex_extractIndex]
  · simp only [hz, ↓reduceIte]
    have h0 : (0 : Fin (2 ^ (kData + K)) → ℂ) = (0 : ℂ) • Pi.single 0 1 := by simp
    rw [h0, QRegister.tensorState_smul_left, zero_smul]
private theorem embedMatrix_P_slot0_mulVec_single {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) (g : Fin (2 ^ n)) :
    ((rData.concat rMeas hDM).embedMatrix (P_slot0 L)).mulVec (Pi.single g 1) =
      if L.tbl (rData.extractIndex g) = 0 then Pi.single g 1 else 0 := by
  let rAct := rData.concat rMeas hDM
  have hSplit : rAct.embedMatrix (P_slot0 L) = (rAct.embedUnitary (uLensSwap L)).1 *
        rAct.embedMatrix ((selMeasInAct K kData).basisOutcomeProjector 0) *
        (rAct.embedUnitary (uLensSwap L)).1 := by
    dsimp only [P_slot0, QRegister.embedUnitary_val]
    rw [rAct.embedMatrix_mul, rAct.embedMatrix_mul]
  rw [hSplit, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      embedUnitary_uLensSwap_mulVec_single, embedMatrix_selMeas_proj0_mulVec_single]
  let h₁ := rMeas.replaceIndex
    (rData.replaceIndex g (L.updSlot (rData.extractIndex g) (rMeas.extractIndex g)))
    (L.tbl (rData.extractIndex g))
  have hExM : rMeas.extractIndex h₁ = L.tbl (rData.extractIndex g) :=
    rMeas.extractIndex_replaceIndex _ _
  rw [hExM]
  by_cases h0 : L.tbl (rData.extractIndex g) = 0
  · simp only [h0, ↓reduceIte]
    have hBack : (rAct.embedUnitary (uLensSwap L)).1.mulVec (Pi.single h₁ 1) = Pi.single g 1 := by
      have hInv :
          (rAct.embedUnitary (uLensSwap L)).1 * (rAct.embedUnitary (uLensSwap L)).1 = 1 := by
        rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uLensSwap_mul_self,
            QRegister.embedUnitary_one, OneMemClass.coe_one]
      have h1 := embedUnitary_uLensSwap_mulVec_single rData rMeas hDM L g
      change (rAct.embedUnitary (uLensSwap L)).1.mulVec _ = Pi.single h₁ 1 at h1
      rw [← h1, Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
    have h1Eq : h₁ = rMeas.replaceIndex
        (rData.replaceIndex g (L.updSlot (rData.extractIndex g) (rMeas.extractIndex g))) 0 := by
      dsimp only [h₁]; rw [h0]
    rw [← h1Eq]
    exact hBack
  · simp only [h0, ↓reduceIte, Matrix.mulVec_zero]
private theorem uLensLoad_mul_projMeas0_eq_setTableOp {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) :
    ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1 * rMeas.basisOutcomeProjector 0 =
      bellSetTableOp rData rMeas L.tbl * rMeas.basisOutcomeProjector 0 := by
  apply matrix_ext_single; intro g
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_mulVec_single]
  by_cases hg0 : rMeas.extractIndex g = 0
  · simp only [hg0, ↓reduceIte]
    rw [embedUnitary_uLensLoad_mulVec_single, bellSetTableOp_mulVec_single, hg0, xorK_zero_left]
  · simp only [hg0, ↓reduceIte, Matrix.mulVec_zero]
private theorem uLensWrite_mul_P_slot0_eq_setTableOp_mul_uLensSwap {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) : ((rData.concat rMeas hDM).embedUnitary (uLensWrite L)).1 *
        (rData.concat rMeas hDM).embedMatrix (P_slot0 L) =
      bellSetTableOp rData rMeas L.tbl * rMeas.basisOutcomeProjector 0 *
        ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 *
        (rData.concat rMeas hDM).embedMatrix (P_slot0 L) := by
  apply matrix_ext_single; intro g
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, embedMatrix_P_slot0_mulVec_single]
  by_cases h0 : L.tbl (rData.extractIndex g) = 0
  · simp only [h0, ↓reduceIte]
    rw [embedUnitary_uLensWrite_mulVec_single, h0, xorK_zero_left,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, embedUnitary_uLensSwap_mulVec_single, h0,
        basisOutcomeProjector_zero_mulVec_single]
    let dNew := L.updSlot (rData.extractIndex g) (rMeas.extractIndex g)
    let g₁ := rMeas.replaceIndex (rData.replaceIndex g dNew) 0
    have hg₁M : rMeas.extractIndex g₁ = 0 := rMeas.extractIndex_replaceIndex _ 0
    rw [show rMeas.replaceIndex (rData.replaceIndex g dNew) 0 = g₁ from rfl]
    simp only [hg₁M, ↓reduceIte]
    rw [bellSetTableOp_mulVec_single]
    have hg₁D : rData.extractIndex g₁ = dNew := by
      dsimp only [g₁]
      rw [QRegister.extractIndex_replaceIndex_of_disjoint rData rMeas hDM,
          QRegister.extractIndex_replaceIndex]
    have hTbl : L.tbl (rData.extractIndex g₁) = rMeas.extractIndex g := by
      rw [hg₁D]; exact L.get_put _ _
    rw [hTbl]
    dsimp only [g₁]
    rw [QRegister.replaceIndex_replaceIndex]
    have hKeepM : rMeas.extractIndex (rData.replaceIndex g dNew) = rMeas.extractIndex g :=
      QRegister.extractIndex_replaceIndex_of_disjoint rMeas rData (disjointWires_symm hDM) g dNew
    have hRhs : rMeas.replaceIndex (rData.replaceIndex g dNew) (rMeas.extractIndex g) =
        rData.replaceIndex g dNew := by
      rw [← hKeepM, QRegister.replaceIndex_extractIndex]
    rw [hRhs]
  · simp only [h0, ↓reduceIte, Matrix.mulVec_zero]
/-! ## Section 4: Slot Phase Kick, Hadamard Walls, & `+0 T` Pre-Swap Bell Preparation -/
/-- Phase kick `(-1)^{⟨L.tbl d, reg⟩}` on `(rData, rReg)` as a global diagonal sign unitary. -/
noncomputable def uKickSlotGlobal {n K kData : ℕ}
    (rData : QRegister kData n) (rReg : QRegister K n) (L : SlotKLens K kData) : Unitary (2 ^ n) :=
  bellDiagSign (fun g ↦ decide ((∑ j : Fin K,
      basisBits K (L.tbl (rData.extractIndex g)) j * basisBits n g (rReg j)) = 1))
private theorem cHadReg_reg_conj_uKickSlotGlobal_eq_uLensLoad {n K kData : ℕ}
    (rData : QRegister kData n) (rReg : QRegister K n) (hDR : rData.DisjointWires rReg)
    (L : SlotKLens K kData) :
    (cHadReg rReg).eval * uKickSlotGlobal rData rReg L * (cHadReg rReg).eval =
      (rData.concat rReg hDR).embedUnitary (uLensLoad L) := by
  let b : Fin K → BitAssignment n → ZMod 2 := fun j α ↦
    basisBits K (L.tbl (rData.extractIndex ((basisBitsEquiv n).symm α))) j
  have hb : ∀ (j : Fin K) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ t : Fin K, w ≠ rReg t) → α₁ w = α₂ w) → b j α₁ = b j α₂ := by
    intro j α₁ α₂ h
    dsimp only [b]
    have hEx : rData.extractIndex ((basisBitsEquiv n).symm α₁) =
        rData.extractIndex ((basisBitsEquiv n).symm α₂) := by
      rw [← (basisBitsEquiv kData).apply_eq_iff_eq]
      funext i
      change basisBits kData _ i = basisBits kData _ i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
          (basisBitsEquiv n).apply_symm_apply, (basisBitsEquiv n).apply_symm_apply]
      exact h (rData i) fun t ht ↦ hDR.ne i t ht
    rw [hEx]
  apply Subtype.ext; apply matrix_ext_single; intro g
  rw [← ket_basisBits_eq_single g]
  have hU : uKickSlotGlobal rData rReg L = bellDiagSign (fun g' ↦
        decide ((∑ j : Fin K, b j (basisBits n g') * basisBits n g' (rReg j)) = 1)) := by
    refine congrArg bellDiagSign (funext fun g' ↦ ?_)
    dsimp only [b]
    simp only [(basisBitsEquiv n).symm_apply_apply]
  rw [hU, cHadReg_conj_phase_ket rReg b hb (basisBits n g), ket_basisBits_eq_single g,
      embedUnitary_uLensLoad_mulVec_single]
  have hWr : writeReg (basisBits n g) rReg
      (fun j ↦ basisBits n g (rReg j) + b j (basisBits n g)) = basisBits n (rReg.replaceIndex g
        (xorK (rReg.extractIndex g) (L.tbl (rData.extractIndex g)))) := by
    dsimp only [writeReg, xorK, b]
    rw [(basisBitsEquiv n).symm_apply_apply]
    refine congrArg (fun v ↦ basisBits n (rReg.replaceIndex g v)) ?_
    refine congrArg (basisBitsEquiv K).symm (funext fun j ↦ ?_)
    rw [QRegister.basisBits_extractIndex]
  rw [hWr, ket_basisBits_eq_single]
/-- Structural witness that `L : SlotKLens K kData` addresses an active `K`-wire slot inside `rElec`
determined by wires outside `rElec`. -/
structure IsBankSlotLens {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n) (L : SlotKLens K kData) where
  slotWires : BitAssignment n → QRegister K n
  slot_ignores_elec : ∀ α₁ α₂ : BitAssignment n,
    (∀ w, (∀ t : Fin mElec, w ≠ rElec t) → α₁ w = α₂ w) → slotWires α₁ = slotWires α₂
  slot_in_elec : ∀ (α : BitAssignment n) (j : Fin K), (slotWires α) j ∈ Set.range rElec.wires
  tbl_eq_slot : ∀ (g : Fin (2 ^ n)) (j : Fin K),
    basisBits K (L.tbl (rData.extractIndex g)) j = basisBits n g (slotWires (basisBits n g) j)
  updSlot_eq_writeReg : ∀ (g : Fin (2 ^ n)) (v : Fin (2 ^ K)),
    basisBits n (rData.replaceIndex g (L.updSlot (rData.extractIndex g) v)) =
      writeReg (basisBits n g) (slotWires (basisBits n g)) (basisBits K v)
private theorem IsBankSlotLens.prod_elec_eq_slot {M : Type*} [CommMonoid M]
    {n mElec K kData : ℕ} {rData : QRegister kData n} {rElec : QRegister mElec n}
    {L : SlotKLens K kData} (hBank : IsBankSlotLens rData rElec L)
    (α : BitAssignment n) (F : Fin mElec → M) (G : Fin K → M)
    (hOff : ∀ t, (¬ ∃ j : Fin K, rElec t = hBank.slotWires α j) → F t = 1)
    (hOn : ∀ (t : Fin mElec) (j : Fin K), rElec t = hBank.slotWires α j → F t = G j) :
    (∏ t : Fin mElec, F t) = ∏ j : Fin K, G j := by
  let sw := hBank.slotWires α
  let idxOf : Fin K → Fin mElec := fun j ↦ (hBank.slot_in_elec α j).choose
  have hIdx : ∀ j : Fin K, rElec (idxOf j) = sw j := fun j ↦ (hBank.slot_in_elec α j).choose_spec
  have hInj : Function.Injective idxOf := fun j₁ j₂ heq ↦
    sw.wires.injective ((hIdx j₁).symm.trans ((congrArg rElec.wires heq).trans (hIdx j₂)))
  symm
  calc (∏ j : Fin K, G j)
      = ∏ j : Fin K, F (idxOf j) := Finset.prod_congr rfl fun j _ ↦ (hOn (idxOf j) j (hIdx j)).symm
    _ = ∏ t ∈ Finset.univ.image idxOf, F t := (Finset.prod_image fun _ _ _ _ h ↦ hInj h).symm
    _ = ∏ t : Fin mElec, F t := Finset.prod_subset (Finset.subset_univ _) fun t _ ht ↦
          hOff t fun ⟨j, hj⟩ ↦ ht (Finset.mem_image.mpr
            ⟨j, Finset.mem_univ j, rElec.wires.injective ((hIdx j).trans hj.symm)⟩)
private theorem IsBankSlotLens.sum_elec_eq_slot {M : Type*} [AddCommMonoid M]
    {n mElec K kData : ℕ} {rData : QRegister kData n} {rElec : QRegister mElec n}
    {L : SlotKLens K kData} (hBank : IsBankSlotLens rData rElec L)
    (α : BitAssignment n) (F : Fin mElec → M) (G : Fin K → M)
    (hOff : ∀ t, (¬ ∃ j : Fin K, rElec t = hBank.slotWires α j) → F t = 0)
    (hOn : ∀ (t : Fin mElec) (j : Fin K), rElec t = hBank.slotWires α j → F t = G j) :
    (∑ t : Fin mElec, F t) = ∑ j : Fin K, G j := by
  let sw := hBank.slotWires α
  let idxOf : Fin K → Fin mElec := fun j ↦ (hBank.slot_in_elec α j).choose
  have hIdx : ∀ j : Fin K, rElec (idxOf j) = sw j := fun j ↦ (hBank.slot_in_elec α j).choose_spec
  have hInj : Function.Injective idxOf := fun j₁ j₂ heq ↦
    sw.wires.injective ((hIdx j₁).symm.trans ((congrArg rElec.wires heq).trans (hIdx j₂)))
  symm
  calc (∑ j : Fin K, G j)
      = ∑ j : Fin K, F (idxOf j) := Finset.sum_congr rfl fun j _ ↦ (hOn (idxOf j) j (hIdx j)).symm
    _ = ∑ t ∈ Finset.univ.image idxOf, F t := (Finset.sum_image fun _ _ _ _ h ↦ hInj h).symm
    _ = ∑ t : Fin mElec, F t := Finset.sum_subset (Finset.subset_univ _) fun t _ ht ↦
          hOff t fun ⟨j, hj⟩ ↦ ht (Finset.mem_image.mpr
            ⟨j, Finset.mem_univ j, rElec.wires.injective ((hIdx j).trans hj.symm)⟩)
private theorem cHadReg_elec_conj_bank_phase_mulVec_single {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n)
    (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L)
    (val : BitAssignment n → Fin K → ZMod 2) (hIgn : ∀ (j : Fin K) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ s : Fin mElec, w ≠ rElec s) → α₁ w = α₂ w) → val α₁ j = val α₂ j)
    (mask : Fin (2 ^ n) → Fin (2 ^ K)) (hMask : ∀ (g : Fin (2 ^ n)) (j : Fin K),
      val (basisBits n g) j = basisBits K (mask g) j) {U : Unitary (2 ^ n)}
    (hU : U = bellDiagSign (fun g' ↦ decide ((∑ j : Fin K, val (basisBits n g') j *
        basisBits K (L.tbl (rData.extractIndex g')) j) = 1))) (g : Fin (2 ^ n)) :
    ((cHadReg rElec).eval * U * (cHadReg rElec).eval).1.mulVec (Pi.single g 1) =
      Pi.single (rData.replaceIndex g (L.updSlot (rData.extractIndex g)
          (xorK (L.tbl (rData.extractIndex g)) (mask g)))) 1 := by
  let b : Fin mElec → BitAssignment n → ZMod 2 := fun t α ↦
    if h : ∃ j : Fin K, rElec t = hBank.slotWires α j then val α h.choose else 0
  have hbOn : ∀ (α : BitAssignment n) (t : Fin mElec) (j : Fin K),
      rElec t = hBank.slotWires α j → b t α = val α j := by
    intro α t j hj
    dsimp only [b]
    rw [dite_eq_left ⟨j, hj⟩]
    exact congrArg (val α) ((hBank.slotWires α).wires.injective
      ((Exists.choose_spec
        (⟨j, hj⟩ : ∃ j' : Fin K, rElec t = hBank.slotWires α j')).symm.trans hj))
  have hb : ∀ (t : Fin mElec) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ s : Fin mElec, w ≠ rElec s) → α₁ w = α₂ w) → b t α₁ = b t α₂ := by
    intro t α₁ α₂ h
    have hSlot : hBank.slotWires α₁ = hBank.slotWires α₂ := hBank.slot_ignores_elec α₁ α₂ h
    by_cases hex1 : ∃ j : Fin K, rElec t = hBank.slotWires α₁ j
    · obtain ⟨j₀, hj₀⟩ := hex1
      rw [hbOn α₁ t j₀ hj₀, hbOn α₂ t j₀ (hSlot ▸ hj₀)]
      exact hIgn j₀ α₁ α₂ h
    · have hex2 : ¬ ∃ j : Fin K, rElec t = hBank.slotWires α₂ j :=
        fun ⟨j, hj⟩ ↦ hex1 ⟨j, hSlot.symm ▸ hj⟩
      dsimp only [b]
      rw [dite_eq_right hex1, dite_eq_right hex2]
  have hSumEq : ∀ g' : Fin (2 ^ n),
      (∑ t : Fin mElec, b t (basisBits n g') * basisBits n g' (rElec t)) =
      (∑ j : Fin K, val (basisBits n g') j *
        basisBits K (L.tbl (rData.extractIndex g')) j) := fun g' ↦
    hBank.sum_elec_eq_slot (basisBits n g') _ _
      (fun t hnot ↦ by simp only [b, dite_eq_right hnot, zero_mul])
      (fun t j hj ↦ by rw [hbOn _ t j hj, hj, hBank.tbl_eq_slot g' j])
  rw [← ket_basisBits_eq_single g]
  have hUb : U = bellDiagSign (fun g' ↦
      decide ((∑ t : Fin mElec, b t (basisBits n g') * basisBits n g' (rElec t)) = 1)) := by
    rw [hU]
    exact congrArg bellDiagSign (funext fun g' ↦ by rw [hSumEq g'])
  rw [hUb, cHadReg_conj_phase_ket rElec b hb (basisBits n g)]
  let α := basisBits n g
  let v := xorK (L.tbl (rData.extractIndex g)) (mask g)
  have hWr : writeReg α rElec (fun t ↦ α (rElec t) + b t α) =
      basisBits n (rData.replaceIndex g (L.updSlot (rData.extractIndex g) v)) := by
    rw [hBank.updSlot_eq_writeReg g v]
    funext w
    by_cases hwSw : w ∈ Set.range (hBank.slotWires α).wires
    · obtain ⟨j₀, rfl⟩ := hwSw
      obtain ⟨t₀, ht₀⟩ := hBank.slot_in_elec α j₀
      have hTbl0 : α (hBank.slotWires α j₀) = basisBits K (L.tbl (rData.extractIndex g)) j₀ :=
        (hBank.tbl_eq_slot g j₀).symm
      rw [← ht₀, writeReg_apply_reg, ht₀, writeReg_apply_reg, hbOn α t₀ j₀ ht₀, hTbl0]
      dsimp only [v, α]
      rw [basisBits_xorK, hMask g j₀]
    · rw [writeReg_apply_of_not_mem _ _ _ w hwSw]
      by_cases hwEl : w ∈ Set.range rElec.wires
      · obtain ⟨t₀, rfl⟩ := hwEl
        have hbt : b t₀ α = 0 := dite_eq_right fun ⟨j, hj⟩ ↦ hwSw ⟨j, hj.symm⟩
        rw [writeReg_apply_reg, hbt, add_zero]
      · exact writeReg_apply_of_not_mem _ _ _ w hwEl
  rw [hWr, ket_basisBits_eq_single]
private theorem cHadReg_elec_conj_uKickSlotGlobal_eq_uLensWrite {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n) (rReg : QRegister K n)
    (hDR : rData.DisjointWires rReg) (hER : rElec.DisjointWires rReg)
    (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L) :
    (cHadReg rElec).eval * uKickSlotGlobal rData rReg L * (cHadReg rElec).eval =
      (rData.concat rReg hDR).embedUnitary (uLensWrite L) := by
  apply Subtype.ext
  apply matrix_ext_single
  intro g
  rw [embedUnitary_uLensWrite_mulVec_single]
  exact cHadReg_elec_conj_bank_phase_mulVec_single rData rElec L hBank
    (fun α j ↦ α (rReg j))
    (fun j _ _ h ↦ h (rReg j) fun s hs ↦ hER.ne s j hs.symm)
    (fun g' ↦ rReg.extractIndex g')
    (fun g' j ↦ (QRegister.basisBits_extractIndex rReg g' j).symm)
    (congrArg bellDiagSign (funext fun g' ↦ by simp only [mul_comm])) g
/-- Bell-entangled active-slot preparation unitary `U_Write(rData, rHeld) * H^⊗K(rHeld)`. -/
noncomputable def uBellSlot {n K kData : ℕ}
    (rData : QRegister kData n) (rHeld : QRegister K n) (hDH : rData.DisjointWires rHeld)
    (L : SlotKLens K kData) : Unitary (2 ^ n) :=
  (rData.concat rHeld hDH).embedUnitary (uLensWrite L) * (cHadReg rHeld).eval
private theorem bell_hadamard_wall_inv_eq {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n) (rHeld : QRegister K n)
    (hDH : rData.DisjointWires rHeld) (hEH : rElec.DisjointWires rHeld)
    (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L) :
    (cHadReg rHeld).eval * (cHadReg rElec).eval * uBellSlot rData rHeld hDH L =
      (rData.concat rHeld hDH).embedUnitary (uLensLoad L) * (cHadReg rElec).eval := by
  dsimp only [uBellSlot]
  rw [← cHadReg_elec_conj_uKickSlotGlobal_eq_uLensWrite rData rElec rHeld hDH hEH L hBank]
  simp only [mul_assoc]
  rw [← mul_assoc (cHadReg rElec).eval (cHadReg rElec).eval, cHadReg_eval_mul_self, one_mul,
      cHadReg_comm_of_disjoint rElec rHeld hEH,
      ← mul_assoc _ _ (cHadReg rElec).eval, ← mul_assoc (cHadReg rHeld).eval,
      ← mul_assoc (cHadReg rHeld).eval, cHadReg_reg_conj_uKickSlotGlobal_eq_uLensLoad]
private theorem cHeldCzAll_mul_setTableOp_held_eq {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas rHeld : QRegister K n)
    (hHM : rHeld.DisjointWires rMeas) (L : SlotKLens K kData) :
    (cHeldCzAll rHeld rMeas hHM).eval.1 * bellSetTableOp rData rHeld L.tbl *
        rHeld.basisOutcomeProjector 0 =
      bellSetTableOp rData rHeld L.tbl * rHeld.basisOutcomeProjector 0 *
        (uKickSlotGlobal rData rMeas L).1 := by
  apply matrix_ext_single; intro g
  have hKickG : (uKickSlotGlobal rData rMeas L).1.mulVec (Pi.single g 1) =
      (if decide ((∑ j : Fin K,
        basisBits K (L.tbl (rData.extractIndex g)) j * basisBits n g (rMeas j)) = 1)
      then (-1 : ℂ) else 1) • Pi.single g 1 := by
    dsimp only [uKickSlotGlobal]
    rw [← ket_basisBits_eq_single g, bellDiagSign_mulVec_ket,
        (basisBitsEquiv n).symm_apply_apply, ket_basisBits_eq_single g]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hKickG, Matrix.mulVec_smul, basisOutcomeProjector_zero_mulVec_single]
  by_cases hg0 : rHeld.extractIndex g = 0
  · simp only [hg0, ↓reduceIte]
    rw [bellSetTableOp_mulVec_single, cHeldCzAll_eval_eq_bellDiagSign, Matrix.mulVec_smul,
        bellSetTableOp_mulVec_single]
    let g₁ := rHeld.replaceIndex g (L.tbl (rData.extractIndex g))
    rw [← ket_basisBits_eq_single g₁, bellDiagSign_mulVec_ket,
        (basisBitsEquiv n).symm_apply_apply, ket_basisBits_eq_single g₁]
    refine congrArg (· • Pi.single g₁ 1) (congrArg (fun b ↦ if b then (-1 : ℂ) else 1)
      (congrArg (decide <| · = 1) (Finset.sum_congr rfl fun j _ ↦ ?_)))
    dsimp only [g₁]
    rw [QRegister.basisBits_replaceIndex_apply,
        QRegister.basisBits_replaceIndex_of_not_mem rHeld _ _ (rMeas j)
          (fun ⟨i, hi⟩ ↦ hHM.ne i j hi)]
  · simp [hg0]
/-! ## Section 5: Pre-Swap Wrapper, Mid Intertwining, 4-Kraus-Branch MBU, & Master Round-Trip -/
private theorem dynCount_seq {Var : Type} {n k : ℕ} (d₁ d₂ : DynamicCircuit Var n)
    (g : PrimitiveGate k) : (DynamicCircuit.seq d₁ d₂).count g = d₁.count g + d₂.count g := rfl
private theorem dynCount_circuit {Var : Type} {n k : ℕ} (c : Circuit n) (g : PrimitiveGate k) :
    (DynamicCircuit.circuit c : DynamicCircuit Var n).count g = c.count g := rfl
private theorem SubspaceStep.smul {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {E₁ E₂ : Operator (2 ^ n)} {d : DynamicCircuit Var n} (c : ℂ)
    (h : SubspaceStep E₁ E₂ d) : SubspaceStep (c • E₁) (c • E₂) d := by
  intro M
  obtain ⟨M', hwp, heq⟩ := h M
  refine ⟨M', hwp, ?_⟩
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [heq]
/-- Branch phase-fix diagonal unitary `(-1)^{⟨f, L.tbl d⟩}` on `rData`. -/
noncomputable def uSlotFix {K kData : ℕ} (L : SlotKLens K kData) (f : Fin K → Bool) :
    Unitary (2 ^ kData) := bellDiagSign (fun d ↦ bellF2Parity K f (L.tbl d))
private theorem uSlotFix_mul_self {K kData : ℕ} (L : SlotKLens K kData) (f : Fin K → Bool) :
    uSlotFix L f * uSlotFix L f = 1 := bellDiagSign_mul_self _
private theorem embedUnitary_uSlotFix_val_mul_self {n K kData : ℕ}
    (rData : QRegister kData n) (L : SlotKLens K kData) (f : Fin K → Bool) :
    (rData.embedUnitary (uSlotFix L f)).1 * (rData.embedUnitary (uSlotFix L f)).1 = 1 := by
  rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uSlotFix_mul_self,
      QRegister.embedUnitary_one, OneMemClass.coe_one]
private theorem xReset_setTableOp_proj0_eq_fix_smul {n K kData : ℕ}
    (rData : QRegister kData n) (rReg : QRegister K n) (L : SlotKLens K kData) (f : Fin K → Bool) :
    DynCircuitExt.xResetKraus rReg f * bellSetTableOp rData rReg L.tbl *
        rReg.basisOutcomeProjector 0 = (((√(1 / 2)) ^ K : ℝ) : ℂ) •
        ((rData.embedUnitary (uSlotFix L f)).1 * rReg.basisOutcomeProjector 0) := by
  let U := (rData.embedUnitary (uSlotFix L f)).1
  have hU2 : U * U = 1 := embedUnitary_uSlotFix_val_mul_self rData L f
  have hColl : U * (DynCircuitExt.xResetKraus rReg f * bellSetTableOp rData rReg L.tbl *
      rReg.basisOutcomeProjector 0) =
      (((√(1 / 2)) ^ K : ℝ) : ℂ) • rReg.basisOutcomeProjector 0 := by
    simpa only [U, uSlotFix, Matrix.mul_assoc] using
      bellTableXReset_mul_setTableOp_mul_zeroMeas rData rReg L.tbl f
  have h := congrArg (U * ·) hColl
  rw [← Matrix.mul_assoc U U, hU2, Matrix.one_mul, Matrix.mul_smul] at h
  exact h
private theorem bellDiagSign_comm_basisOutcomeProjector_zero {n w : ℕ}
    (phase : Fin (2 ^ n) → Bool) (r : QRegister w n) :
    r.basisOutcomeProjector 0 * (bellDiagSign phase).1 =
      (bellDiagSign phase).1 * r.basisOutcomeProjector 0 := by
  dsimp only [bellDiagSign]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]
private theorem embedMatrix_selMeas_proj0_eq {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas) :
    (rData.concat rMeas hDM).embedMatrix ((selMeasInAct K kData).basisOutcomeProjector 0) =
      rMeas.basisOutcomeProjector 0 := by
  apply matrix_ext_single; intro g
  rw [embedMatrix_selMeas_proj0_mulVec_single, basisOutcomeProjector_zero_mulVec_single]
private theorem embedUnitary_uLensSwap_val_mul_self {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) : ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 *
      ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 = 1 := by
  rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uLensSwap_mul_self,
      QRegister.embedUnitary_one, OneMemClass.coe_one]
theorem embedMatrix_P_slot0_eq {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) : (rData.concat rMeas hDM).embedMatrix (P_slot0 L) =
      ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 * rMeas.basisOutcomeProjector 0 *
        ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 := by
  dsimp only [P_slot0, QRegister.embedUnitary_val]
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, embedMatrix_selMeas_proj0_eq]
private theorem projMeas0_mul_uLensSwap_of_slot0 {n K kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister K n) (hDM : rData.DisjointWires rMeas)
    (L : SlotKLens K kData) {R : Operator (2 ^ n)}
    (hSlot0 : (rData.concat rMeas hDM).embedMatrix (P_slot0 L) * R = R) :
    rMeas.basisOutcomeProjector 0 * (((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 * R) =
      ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 * R := by
  let USwap := ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1
  have hS2 : USwap * USwap = 1 := embedUnitary_uLensSwap_val_mul_self rData rMeas hDM L
  have hPEq := embedMatrix_P_slot0_eq rData rMeas hDM L
  rw [← Matrix.one_mul (rMeas.basisOutcomeProjector 0 * (USwap * R)), ← hS2]
  simpa only [Matrix.mul_assoc] using
    congrArg (USwap * ·) (by simpa only [Matrix.mul_assoc, hPEq] using hSlot0)
/-! ## Section 6: Fused Single-Fixup Pauli-Clifford Bell Uncompute (`856 T`, `-436 T/Select`) -/
private theorem SubspaceStep.of_unit_smul_out {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {E₁ E₂ : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    {ω : ℂ} (hω : star ω * ω = 1) (h : SubspaceStep E₁ (ω • E₂) d) : SubspaceStep E₁ E₂ d := by
  have hω' : ω * star ω = 1 := by rw [mul_comm, hω]
  intro M
  obtain ⟨M', hwp, heq⟩ := h M
  refine ⟨M', hwp, ?_⟩
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hω', one_smul] at heq
  exact heq
private theorem slice_disjoint_right_local {n b m offset width : ℕ}
    (r : QRegister b n) (r₂ : QRegister m n)
    (h : offset + width ≤ b) (hdisj : r.DisjointWires r₂) :
    (r.slice offset width h).DisjointWires r₂ := by
  rw [QRegister.disjoint_iff] at hdisj ⊢
  intro i j heq
  exact hdisj ⟨offset + i.val, by omega⟩ j heq
private theorem wireXResetKraus_comm_embedMatrix_of_disjoint {n m : ℕ}
    (q : QRegister 1 n) (r₂ : QRegister m n) (hdisj : q.DisjointWires r₂)
    (bit : Bool) (M : Operator (2 ^ m)) : DynCircuitExt.wireXResetKraus q bit * r₂.embedMatrix M =
      r₂.embedMatrix M * DynCircuitExt.wireXResetKraus q bit := by
  rw [DynCircuitExt.wireXResetKraus_eq_embedMatrix]
  exact q.embedMatrix_comm_of_disjoint r₂ hdisj _ M
private theorem xResetKraus_comm_embedMatrix_of_disjoint {n m : ℕ} :
    ∀ (b : ℕ) (r : QRegister b n) (r₂ : QRegister m n), r.DisjointWires r₂ →
      ∀ (f : Fin b → Bool) (M : Operator (2 ^ m)),
        DynCircuitExt.xResetKraus r f * r₂.embedMatrix M =
          r₂.embedMatrix M * DynCircuitExt.xResetKraus r f
  | 0, _, _, _, _, _ => by simp [DynCircuitExt.xResetKraus]
  | b + 1, r, r₂, hdisj, f, M => by
      simp only [DynCircuitExt.xResetKraus]
      have h0 := wireXResetKraus_comm_embedMatrix_of_disjoint (r.slice 0 1 (by omega)) r₂
        (slice_disjoint_right_local r r₂ _ hdisj) (f 0) M
      have h1 := xResetKraus_comm_embedMatrix_of_disjoint b (r.slice 1 b (by omega)) r₂
        (slice_disjoint_right_local r r₂ _ hdisj) (Fin.tail f) M
      rw [Matrix.mul_assoc, h0, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
/-- Encodes `f : Fin K → Bool` as a `K`-bit index in `Fin (2 ^ K)`. -/
noncomputable def boolMaskK {K : ℕ} (f : Fin K → Bool) : Fin (2 ^ K) :=
  (basisBitsEquiv K).symm (fun j ↦ if f j then 1 else 0)
@[simp]
private theorem basisBits_boolMaskK {K : ℕ} (f : Fin K → Bool) (j : Fin K) :
    basisBits K (boolMaskK f) j = if f j then 1 else 0 :=
  congrFun ((basisBitsEquiv K).apply_symm_apply _) j
/-- Active-slot bitwise `XOR` by `f` on `Fin (2 ^ kData)`. -/
noncomputable def slotXorPerm {K kData : ℕ} (L : SlotKLens K kData) (f : Fin K → Bool)
    (d : Fin (2 ^ kData)) : Fin (2 ^ kData) := L.updSlot d (xorK (L.tbl d) (boolMaskK f))
theorem slotXorPerm_involutive {K kData : ℕ} (L : SlotKLens K kData) (f : Fin K → Bool) :
    Function.Involutive (slotXorPerm L f) := fun d ↦ by
  dsimp only [slotXorPerm]
  rw [L.get_put, L.put_put, xorK_cancel_right, L.put_get]
/-- Active-slot bitwise `X^f` unitary on `rData`. -/
noncomputable def uSlotXor {K kData : ℕ} (L : SlotKLens K kData) (f : Fin K → Bool) :
    Unitary (2 ^ kData) := Operator.permutationUnitary
    (Equiv.ofBijective (slotXorPerm L f) (slotXorPerm_involutive L f).bijective)
private theorem embedUnitary_uSlotXor_mulVec_single {n K kData : ℕ}
    (rData : QRegister kData n) (L : SlotKLens K kData) (f : Fin K → Bool) (g : Fin (2 ^ n)) :
    (rData.embedUnitary (uSlotXor L f)).1.mulVec (Pi.single g 1) = Pi.single (rData.replaceIndex g
        (L.updSlot (rData.extractIndex g)
          (xorK (L.tbl (rData.extractIndex g)) (boolMaskK f)))) 1 := by
  dsimp only [uSlotXor]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  simp only [Equiv.ofBijective_apply, slotXorPerm]
private theorem sign_decide_sum_eq_prod {ι : Type*} (s : Finset ι) (x : ι → ZMod 2) :
    (if decide ((∑ i ∈ s, x i) = 1) then (-1 : ℂ) else 1) =
      ∏ i ∈ s, if decide (x i = 1) then (-1 : ℂ) else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_decide_zmod2_add, ih]
private theorem bool_eq_of_sign_eq {b₁ b₂ : Bool}
    (h : (if b₁ then (-1 : ℂ) else 1) = (if b₂ then (-1 : ℂ) else 1)) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · norm_num at h
  · norm_num at h
  · rfl
private theorem bellF2Parity_eq_decide_sum {K : ℕ} (f : Fin K → Bool) (v : Fin (2 ^ K)) :
    bellF2Parity K f v =
      decide ((∑ j : Fin K, (if f j then (1 : ZMod 2) else 0) * basisBits K v j) = 1) := by
  apply bool_eq_of_sign_eq
  rw [sign_bellF2Parity_eq_prod, sign_decide_sum_eq_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rcases bit_cases (basisBits K v j) with hb | hb <;> cases f j <;> simp [hb]
private theorem embedUnitary_uSlotFix_eq_bellDiagSign {n K kData : ℕ}
    (rData : QRegister kData n) (L : SlotKLens K kData) (f : Fin K → Bool) :
    rData.embedUnitary (uSlotFix L f) =
      bellDiagSign (fun g ↦ bellF2Parity K f (L.tbl (rData.extractIndex g))) := by
  apply Subtype.ext; apply matrix_ext_single; intro g
  rw [uSlotFix, embedUnitary_bellDiagSign_mulVec_single,
      ← ket_basisBits_eq_single g, bellDiagSign_mulVec_ket,
      (basisBitsEquiv n).symm_apply_apply, ket_basisBits_eq_single g]
private theorem cHadReg_elec_conj_uSlotFix_eq_uSlotXor {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n)
    (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L) (f : Fin K → Bool) :
    (cHadReg rElec).eval * rData.embedUnitary (uSlotFix L f) * (cHadReg rElec).eval =
      rData.embedUnitary (uSlotXor L f) := by
  apply Subtype.ext
  apply matrix_ext_single
  intro g
  rw [embedUnitary_uSlotXor_mulVec_single]
  refine cHadReg_elec_conj_bank_phase_mulVec_single rData rElec L hBank
    (fun _ j ↦ if f j then 1 else 0) (fun _ _ _ _ ↦ rfl) (fun _ ↦ boolMaskK f)
    (fun _ j ↦ (basisBits_boolMaskK f j).symm) ?_ g
  rw [embedUnitary_uSlotFix_eq_bellDiagSign]
  exact congrArg bellDiagSign (funext fun g' ↦ bellF2Parity_eq_decide_sum f _)
private theorem cHadReg_elec_mul_uSlotFix_eq_uSlotXor_mul {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n)
    (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L) (f : Fin K → Bool) :
    (cHadReg rElec).eval * rData.embedUnitary (uSlotFix L f) =
      rData.embedUnitary (uSlotXor L f) * (cHadReg rElec).eval := by
  simpa only [mul_assoc, cHadReg_eval_mul_self, mul_one] using
    congrArg (· * (cHadReg rElec).eval)
      (cHadReg_elec_conj_uSlotFix_eq_uSlotXor rData rElec L hBank f)
private theorem ket_S {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) = (if β q = 0 then (1 : ℂ) else Complex.I) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val]
  change ((QRegister.singleton q).embedMatrix _).mulVec (OctahedralOrbit.ket β) = _
  rw [OctahedralOrbit.singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb
  · have hupd : Function.update β q 0 = β := by rw [← hb, Function.update_eq_self]
    simp [OctahedralOrbit.ket, ket, hb, hupd]
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have hupd : Function.update β q 1 = β := by rw [← hb, Function.update_eq_self]
    simp [OctahedralOrbit.ket, ket, hb, h10, hupd]
/-- Local `1`-qubit unitary of `cPauliWireFwd`. -/
noncomputable def uPauliLocalFwd (b₁ b₂ : Bool) : Unitary (2 ^ 1) :=
  match b₁, b₂ with
  | false, _ => 1
  | true, false => Qubit.H
  | true, true => Qubit.H * (Qubit.Z * Qubit.S)
/-- Local `1`-qubit unitary of `cPauliWireInv`. -/
noncomputable def uPauliLocalInv (b₁ b₂ : Bool) : Unitary (2 ^ 1) :=
  match b₁, b₂ with
  | false, _ => 1
  | true, false => Qubit.H
  | true, true => Qubit.S * Qubit.H
private theorem uPauliLocalInv_mul_uPauliLocalFwd (b₁ b₂ : Bool) :
    uPauliLocalInv b₁ b₂ * uPauliLocalFwd b₁ b₂ = 1 := by
  cases b₁ <;> cases b₂
  · exact mul_one 1
  · exact mul_one 1
  · exact Qubit.H_sq
  · simp only [uPauliLocalInv, uPauliLocalFwd, mul_assoc]
    rw [← mul_assoc Qubit.H Qubit.H, Qubit.H_sq, one_mul, Qubit.Z_mul_S_eq_S_inv, mul_inv_cancel]
/-- Single-wire forward Clifford basis change (`0 T`, `0 TOFF`):
`(false, _) ↦ I`, `(true, false) ↦ H`, `(true, true) ↦ S ;;ᶜ Z ;;ᶜ H`. -/
def cPauliWireFwd {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) : Circuit n :=
  match b₁, b₂ with
  | false, _ => .identity
  | true, false => Circuit.H q
  | true, true => (Circuit.S q ;;ᶜ Circuit.Z q) ;;ᶜ Circuit.H q
/-- Single-wire inverse Clifford basis change (`0 T`, `0 TOFF`):
`(false, _) ↦ I`, `(true, false) ↦ H`, `(true, true) ↦ H ;;ᶜ S`. -/
def cPauliWireInv {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) : Circuit n :=
  match b₁, b₂ with
  | false, _ => .identity
  | true, false => Circuit.H q
  | true, true => Circuit.H q ;;ᶜ Circuit.S q
@[simp]
private theorem cPauliWireFwd_count_t {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireFwd b₁ b₂ q).count .T = 0 := by
  cases b₁ <;> cases b₂ <;> simp [cPauliWireFwd]
@[simp]
private theorem cPauliWireFwd_count_toff {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireFwd b₁ b₂ q).count .TOFF = 0 := by
  cases b₁ <;> cases b₂ <;> simp [cPauliWireFwd]
@[simp]
private theorem cPauliWireInv_count_t {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireInv b₁ b₂ q).count .T = 0 := by
  cases b₁ <;> cases b₂ <;> simp [cPauliWireInv]
@[simp]
private theorem cPauliWireInv_count_toff {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireInv b₁ b₂ q).count .TOFF = 0 := by
  cases b₁ <;> cases b₂ <;> simp [cPauliWireInv]
private theorem cPauliWireFwd_eval {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireFwd b₁ b₂ q).eval =
      (QRegister.singleton q).embedUnitary (uPauliLocalFwd b₁ b₂) := by
  cases b₁ <;> cases b₂
  · simp [cPauliWireFwd, uPauliLocalFwd]
  · simp [cPauliWireFwd, uPauliLocalFwd]
  · simp [cPauliWireFwd, uPauliLocalFwd, PrimitiveGate.eval]
  · simp only [cPauliWireFwd, uPauliLocalFwd, Circuit.eval_seq, Circuit.eval_single,
      PrimitiveGate.eval, ← (QRegister.singleton q).embedUnitary_mul]
private theorem cPauliWireInv_eval {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireInv b₁ b₂ q).eval =
      (QRegister.singleton q).embedUnitary (uPauliLocalInv b₁ b₂) := by
  cases b₁ <;> cases b₂
  · simp [cPauliWireInv, uPauliLocalInv]
  · simp [cPauliWireInv, uPauliLocalInv]
  · simp [cPauliWireInv, uPauliLocalInv, PrimitiveGate.eval]
  · simp only [cPauliWireInv, uPauliLocalInv, Circuit.eval_seq, Circuit.eval_single,
      PrimitiveGate.eval, ← (QRegister.singleton q).embedUnitary_mul]
private theorem cPauliWireInv_mul_cPauliWireFwd {n : ℕ} (b₁ b₂ : Bool) (q : Wire n) :
    (cPauliWireInv b₁ b₂ q).eval * (cPauliWireFwd b₁ b₂ q).eval = 1 := by
  rw [cPauliWireInv_eval, cPauliWireFwd_eval, ← (QRegister.singleton q).embedUnitary_mul,
      uPauliLocalInv_mul_uPauliLocalFwd, QRegister.embedUnitary_one]
private theorem singleton_embedMatrix_comm_embedMatrix {n m : ℕ} {q : Wire n} {r₂ : QRegister m n}
    (hq : ∀ j : Fin m, q ≠ r₂ j) (U : Operator (2 ^ 1)) (M : Operator (2 ^ m)) :
    (QRegister.singleton q).embedMatrix U * r₂.embedMatrix M =
      r₂.embedMatrix M * (QRegister.singleton q).embedMatrix U := by
  have hDisj : (QRegister.singleton q).DisjointWires r₂ := by
    rw [QRegister.disjoint_iff]; intro i j; fin_cases i; exact hq j
  exact (QRegister.singleton q).embedMatrix_comm_of_disjoint r₂ hDisj U M
private theorem singleton_embedUnitary_comm_of_ne {n : ℕ} {q₁ q₂ : Wire n} (hne : q₁ ≠ q₂)
    (u₁ u₂ : Unitary (2 ^ 1)) :
    (QRegister.singleton q₁).embedUnitary u₁ * (QRegister.singleton q₂).embedUnitary u₂ =
      (QRegister.singleton q₂).embedUnitary u₂ * (QRegister.singleton q₁).embedUnitary u₁ := by
  apply Subtype.ext
  exact singleton_embedMatrix_comm_embedMatrix (fun j ↦ by fin_cases j; exact hne) u₁.1 u₂.1
private theorem singleton_embedUnitary_comm_bellDiagSign_of_ignores {n : ℕ} (q : Wire n)
    (u : Unitary (2 ^ 1)) (p : BitAssignment n → Bool)
    (hp : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → p α₁ = p α₂) :
    (QRegister.singleton q).embedUnitary u * bellDiagSign (fun g ↦ p (basisBits n g)) =
      bellDiagSign (fun g ↦ p (basisBits n g)) * (QRegister.singleton q).embedUnitary u := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  dsimp only [QRegister.embedUnitary_val, bellDiagSign]
  ext x y
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, QRegister.embedMatrix_apply]
  by_cases henv : ((QRegister.singleton q).basisSplitEquiv x).2 =
      ((QRegister.singleton q).basisSplitEquiv y).2
  · have hOut := ((QRegister.singleton q).basisSplit_environment_eq_iff x y).mp henv
    have hpEq : p (basisBits n x) = p (basisBits n y) :=
      hp _ _ fun w hw ↦ hOut w fun ⟨i, hi⟩ ↦ hw (by fin_cases i; exact hi.symm)
    simp [henv, hpEq, mul_comm]
  · simp [henv]
private theorem singlePauli_conj_phase_ket {n : ℕ} (b₁ b₂ : Bool) (q : Wire n)
    (act : BitAssignment n → Bool)
    (hact : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → act α₁ = act α₂)
    (α : BitAssignment n) :
    let b : BitAssignment n → ZMod 2 := fun β ↦ if act β && (b₁ || b₂) then 1 else 0
    let U₁ : Unitary (2 ^ n) :=
      bellDiagSign (fun g ↦ decide (b (basisBits n g) * basisBits n g q = 1))
    ((cPauliWireInv b₁ b₂ q).eval * U₁ * (cPauliWireFwd b₁ b₂ q).eval).1.mulVec (ket α) =
      ((if act α && (b₁ && b₂) then Complex.I else 1) *
        (if act α && (b₂ && decide (α q = 1)) then (-1 : ℂ) else 1)) •
        ket (Function.update α q (α q + if act α && b₁ then 1 else 0)) := by
  intro b U₁
  have hb : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → b α₁ = b α₂ :=
    fun α₁ α₂ h ↦ by dsimp only [b]; rw [hact α₁ α₂ h]
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  cases b₁ <;> cases b₂
  · dsimp only [cPauliWireInv, cPauliWireFwd, U₁]
    rw [Circuit.eval_identity, one_mul, mul_one, bellDiagSign_mulVec_ket,
        (basisBitsEquiv n).apply_symm_apply]
    simp [b]
  · dsimp only [cPauliWireInv, cPauliWireFwd, U₁]
    rw [Circuit.eval_identity, one_mul, mul_one, bellDiagSign_mulVec_ket,
        (basisBitsEquiv n).apply_symm_apply,
        show Function.update α q (α q + if (act α && false) = true then 1 else 0) = α by simp]
    have hd_eq : decide (b α * α q = 1) = (act α && decide (α q = 1)) := by
      rcases bit_cases (α q) with hq | hq
      · simp [hq]
      · by_cases ha : act α = true
        · simp [b, ha, hq]
        · have ha0 : act α = false := Bool.eq_false_iff.mpr ha
          simp [b, ha0]
    rw [hd_eq]
    simp
  · dsimp only [cPauliWireInv, cPauliWireFwd]
    rw [singleHad_conj_phase_ket q b hb α]
    simp [b]
  · dsimp only [cPauliWireInv, cPauliWireFwd]
    have hAssoc : ((Circuit.H q ;;ᶜ Circuit.S q).eval * U₁ *
        ((Circuit.S q ;;ᶜ Circuit.Z q) ;;ᶜ Circuit.H q).eval) =
        (Circuit.S q).eval * ((Circuit.H q).eval * U₁ * (Circuit.H q).eval) *
          (Circuit.Z q).eval * (Circuit.S q).eval := by
      simp only [Circuit.eval_seq, mul_assoc]
    rw [hAssoc, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ket_S q α, Matrix.mulVec_smul, ket_Z q α, smul_smul,
        Matrix.mulVec_smul, singleHad_conj_phase_ket q b hb α,
        Matrix.mulVec_smul, ket_S q _, Function.update_self, smul_smul]
    have hb_eq : b α = if act α then 1 else 0 := by simp [b]
    rw [hb_eq]
    rcases bit_cases (α q) with hq | hq <;> cases hact_v : act α
    · simp [hq, bitSign]
    · simp [hq, bitSign, h10]
    · simp [hq, bitSign, h10, Complex.I_mul_I]
    · have h110 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [hq, bitSign, h10, h110]
/-- Prefix forward Pauli-basis Clifford wall on the first `k` wires of `rElec`. -/
def cPauliBankFwdAux {n mElec K : ℕ} (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (f₁ f₂ : Fin K → Bool) : (k : ℕ) → k ≤ mElec → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let j := bitOf ⟨k, hk⟩
      cPauliBankFwdAux rElec bitOf f₁ f₂ k (by omega) ;;ᶜ
        cPauliWireFwd (f₁ j) (f₂ j) (rElec ⟨k, hk⟩)
/-- Prefix inverse Pauli-basis Clifford wall on the first `k` wires of `rElec`. -/
def cPauliBankInvAux {n mElec K : ℕ} (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (f₁ f₂ : Fin K → Bool) : (k : ℕ) → k ≤ mElec → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let j := bitOf ⟨k, hk⟩
      cPauliWireInv (f₁ j) (f₂ j) (rElec ⟨k, hk⟩) ;;ᶜ
        cPauliBankInvAux rElec bitOf f₁ f₂ k (by omega)
/-- Full `mElec`-wire forward Pauli-basis Clifford wall (`0 T`, `0 TOFF`). -/
def cPauliBankFwd {n mElec K : ℕ} (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (f₁ f₂ : Fin K → Bool) : Circuit n := cPauliBankFwdAux rElec bitOf f₁ f₂ mElec le_rfl
/-- Full `mElec`-wire inverse Pauli-basis Clifford wall (`0 T`, `0 TOFF`). -/
def cPauliBankInv {n mElec K : ℕ} (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (f₁ f₂ : Fin K → Bool) : Circuit n := cPauliBankInvAux rElec bitOf f₁ f₂ mElec le_rfl
private theorem cPauliBankFwdAux_count_t {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    ∀ (k : ℕ) (hk : k ≤ mElec), (cPauliBankFwdAux rElec bitOf f₁ f₂ k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, _ => by simp [cPauliBankFwdAux, cPauliBankFwdAux_count_t rElec bitOf f₁ f₂ k (by omega)]
private theorem cPauliBankFwdAux_count_toff {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    ∀ (k : ℕ) (hk : k ≤ mElec), (cPauliBankFwdAux rElec bitOf f₁ f₂ k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, _ => by
      simp [cPauliBankFwdAux, cPauliBankFwdAux_count_toff rElec bitOf f₁ f₂ k (by omega)]
private theorem cPauliBankInvAux_count_t {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    ∀ (k : ℕ) (hk : k ≤ mElec), (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, _ => by simp [cPauliBankInvAux, cPauliBankInvAux_count_t rElec bitOf f₁ f₂ k (by omega)]
private theorem cPauliBankInvAux_count_toff {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    ∀ (k : ℕ) (hk : k ≤ mElec), (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, _ => by
      simp [cPauliBankInvAux, cPauliBankInvAux_count_toff rElec bitOf f₁ f₂ k (by omega)]
@[simp]
theorem cPauliBankFwd_count_t {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    (cPauliBankFwd rElec bitOf f₁ f₂).count .T = 0 :=
  cPauliBankFwdAux_count_t rElec bitOf f₁ f₂ mElec le_rfl
@[simp]
theorem cPauliBankFwd_count_toff {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    (cPauliBankFwd rElec bitOf f₁ f₂).count .TOFF = 0 :=
  cPauliBankFwdAux_count_toff rElec bitOf f₁ f₂ mElec le_rfl
@[simp]
theorem cPauliBankInv_count_t {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    (cPauliBankInv rElec bitOf f₁ f₂).count .T = 0 :=
  cPauliBankInvAux_count_t rElec bitOf f₁ f₂ mElec le_rfl
@[simp]
theorem cPauliBankInv_count_toff {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    (cPauliBankInv rElec bitOf f₁ f₂).count .TOFF = 0 :=
  cPauliBankInvAux_count_toff rElec bitOf f₁ f₂ mElec le_rfl
private theorem cPauliBankInvAux_mul_cPauliBankFwdAux {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) : ∀ (k : ℕ) (hk : k ≤ mElec),
      (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).eval *
        (cPauliBankFwdAux rElec bitOf f₁ f₂ k hk).eval = 1
  | 0, _ => by simp [cPauliBankInvAux, cPauliBankFwdAux]
  | k + 1, hk => by
      have ih := cPauliBankInvAux_mul_cPauliBankFwdAux rElec bitOf f₁ f₂ k (by omega)
      simp only [cPauliBankInvAux, cPauliBankFwdAux, Circuit.eval_seq, mul_assoc]
      rw [← mul_assoc (cPauliWireInv _ _ _).eval, cPauliWireInv_mul_cPauliWireFwd, one_mul, ih]
private theorem cPauliBankInv_mul_cPauliBankFwd {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    (cPauliBankInv rElec bitOf f₁ f₂).eval * (cPauliBankFwd rElec bitOf f₁ f₂).eval = 1 :=
  cPauliBankInvAux_mul_cPauliBankFwdAux rElec bitOf f₁ f₂ mElec le_rfl
private theorem cPauliBankFwd_mul_cPauliBankInv {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) :
    (cPauliBankFwd rElec bitOf f₁ f₂).eval * (cPauliBankInv rElec bitOf f₁ f₂).eval = 1 := by
  have hInv : (cPauliBankInv rElec bitOf f₁ f₂).eval = (cPauliBankFwd rElec bitOf f₁ f₂).eval⁻¹ :=
    eq_inv_of_mul_eq_one_left (cPauliBankInv_mul_cPauliBankFwd rElec bitOf f₁ f₂)
  rw [hInv, mul_inv_cancel]
private theorem cPauliWireFwd_onRegister {n mElec : ℕ} (rElec : QRegister mElec n)
    (b₁ b₂ : Bool) (t : Fin mElec) :
    (cPauliWireFwd b₁ b₂ (QRegister.whole mElec t)).onRegister rElec =
      cPauliWireFwd b₁ b₂ (rElec t) := by
  change (cPauliWireFwd b₁ b₂ t).onRegister rElec = cPauliWireFwd b₁ b₂ (rElec t)
  have hReg : rElec.compose (QRegister.singleton t) = QRegister.singleton (rElec t) :=
    qreg_ext_local fun i ↦ by fin_cases i; rfl
  cases b₁ <;> cases b₂ <;>
    simp only [cPauliWireFwd, Circuit.H, Circuit.S, Circuit.Z, Circuit.single,
      Circuit.onRegister_identity, Circuit.onRegister_seq, Circuit.onRegister_relocates_gate, hReg]
private theorem cPauliBankFwd_eval_eq_embed {n mElec K : ℕ} (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool) : (cPauliBankFwd rElec bitOf f₁ f₂).eval =
      rElec.embedUnitary (cPauliBankFwd (QRegister.whole mElec) bitOf f₁ f₂).eval := by
  suffices ∀ (k : ℕ) (hk : k ≤ mElec),
      (cPauliBankFwdAux (QRegister.whole mElec) bitOf f₁ f₂ k hk).onRegister rElec =
        cPauliBankFwdAux rElec bitOf f₁ f₂ k hk by
    unfold cPauliBankFwd
    rw [← this mElec le_rfl, Circuit.eval_onRegister]
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      dsimp only [cPauliBankFwdAux]
      rw [Circuit.onRegister_seq, ih (by omega), cPauliWireFwd_onRegister]
theorem cPauliBankFwd_preserves_disjoint_wire {M n mElec K : ℕ}
    (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool)
    (rComb : QRegister M n) (hDisj : rElec.DisjointWires rComb) :
    ∀ (idx : Wire M) (i j : Fin (2 ^ n)), (cPauliBankFwd rElec bitOf f₁ f₂).eval.1 i j ≠ 0 →
      basisBits n i (rComb idx) = basisBits n j (rComb idx) := by
  intro idx i j hnz
  rw [cPauliBankFwd_eval_eq_embed, QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
  by_contra hne
  apply hnz
  have hnot : rComb idx ∉ Set.range rElec.wires := fun ⟨u, hu⟩ ↦ hDisj.ne u idx hu
  have hrest : (rElec.basisSplitEquiv i).2 ≠ (rElec.basisSplitEquiv j).2 :=
    fun hr ↦ hne (congrFun hr ⟨rComb idx, hnot⟩)
  simp [hrest]
private theorem cPauliBankInvAux_comm_singleton {n mElec K : ℕ}
    (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool)
    (q : Wire n) (u : Unitary (2 ^ 1)) : ∀ (k : ℕ) (hk : k ≤ mElec),
      (∀ i : Fin k, rElec ⟨i.val, by omega⟩ ≠ q) →
      (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).eval * (QRegister.singleton q).embedUnitary u =
        (QRegister.singleton q).embedUnitary u * (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).eval
  | 0, _, _ => by simp [cPauliBankInvAux]
  | k + 1, hk, hne => by
      have ih := cPauliBankInvAux_comm_singleton rElec bitOf f₁ f₂ q u k (by omega)
        fun i ↦ hne ⟨i.val, by omega⟩
      have hlast : (cPauliWireInv (f₁ (bitOf ⟨k, hk⟩)) (f₂ (bitOf ⟨k, hk⟩)) (rElec ⟨k, hk⟩)).eval *
          (QRegister.singleton q).embedUnitary u = (QRegister.singleton q).embedUnitary u *
            (cPauliWireInv (f₁ (bitOf ⟨k, hk⟩)) (f₂ (bitOf ⟨k, hk⟩)) (rElec ⟨k, hk⟩)).eval := by
        rw [cPauliWireInv_eval]
        exact singleton_embedUnitary_comm_of_ne (hne ⟨k, Nat.lt_succ_self k⟩) _ u
      dsimp only [cPauliBankInvAux]
      rw [Circuit.eval_seq, mul_assoc, hlast, ← mul_assoc, ih, mul_assoc]
private theorem cPauliBankInvAux_comm_bellDiagSign {n mElec K : ℕ}
    (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool)
    (p : BitAssignment n → Bool) : ∀ (k : ℕ) (hk : k ≤ mElec),
      (∀ (i : Fin k) (α₁ α₂ : BitAssignment n),
        (∀ w, w ≠ rElec ⟨i.val, by omega⟩ → α₁ w = α₂ w) → p α₁ = p α₂) →
      (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).eval * bellDiagSign (fun g ↦ p (basisBits n g)) =
        bellDiagSign (fun g ↦ p (basisBits n g)) * (cPauliBankInvAux rElec bitOf f₁ f₂ k hk).eval
  | 0, _, _ => by simp [cPauliBankInvAux]
  | k + 1, hk, hp => by
      have ih := cPauliBankInvAux_comm_bellDiagSign rElec bitOf f₁ f₂ p k (by omega)
        fun i α₁ α₂ h ↦ hp ⟨i.val, by omega⟩ α₁ α₂ h
      have hlast : (cPauliWireInv (f₁ (bitOf ⟨k, hk⟩)) (f₂ (bitOf ⟨k, hk⟩)) (rElec ⟨k, hk⟩)).eval *
          bellDiagSign (fun g ↦ p (basisBits n g)) = bellDiagSign (fun g ↦ p (basisBits n g)) *
            (cPauliWireInv (f₁ (bitOf ⟨k, hk⟩)) (f₂ (bitOf ⟨k, hk⟩)) (rElec ⟨k, hk⟩)).eval := by
        rw [cPauliWireInv_eval]
        exact singleton_embedUnitary_comm_bellDiagSign_of_ignores (rElec ⟨k, hk⟩) _ p
          (hp ⟨k, Nat.lt_succ_self k⟩)
      dsimp only [cPauliBankInvAux]
      rw [Circuit.eval_seq, mul_assoc, hlast, ← mul_assoc, ih, mul_assoc]
/-- Purely classical unit-modulus phase `∏_{j : Fin K} i^{f₁ j && f₂ j}` (`|ω| = 1`). -/
noncomputable def pauliPhaseScalar {K : ℕ} (f₁ f₂ : Fin K → Bool) : ℂ :=
  ∏ j : Fin K, if f₁ j && f₂ j then Complex.I else 1
private theorem star_pauliPhaseScalar_mul_self {K : ℕ} (f₁ f₂ : Fin K → Bool) :
    star (pauliPhaseScalar f₁ f₂) * pauliPhaseScalar f₁ f₂ = 1 := by
  dsimp only [pauliPhaseScalar]
  rw [Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ ↦ ?_
  cases f₁ j && f₂ j
  · simp
  · simp [Complex.conj_I, Complex.I_mul_I]
private theorem pauliPhaseScalar_mul_star_self {K : ℕ} (f₁ f₂ : Fin K → Bool) :
    pauliPhaseScalar f₁ f₂ * star (pauliPhaseScalar f₁ f₂) = 1 := by
  rw [mul_comm, star_pauliPhaseScalar_mul_self]
private theorem cPauliBankAux_conj_phase_ket {n mElec K : ℕ}
    (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K) (f₁ f₂ : Fin K → Bool)
    (act : Fin mElec → BitAssignment n → Bool) (hact : ∀ (t : Fin mElec) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ s : Fin mElec, w ≠ rElec s) → α₁ w = α₂ w) → act t α₁ = act t α₂) :
    ∀ (k : ℕ) (hk : k ≤ mElec) (β : BitAssignment n),
      ((cPauliBankInvAux rElec bitOf f₁ f₂ k hk).eval * bellDiagSign (fun g ↦ decide ((∑ i : Fin k,
            (if act ⟨i.val, by omega⟩ (basisBits n g) &&
              (f₁ (bitOf ⟨i.val, by omega⟩) || f₂ (bitOf ⟨i.val, by omega⟩)) then
              (1 : ZMod 2) else 0) * basisBits n g (rElec ⟨i.val, by omega⟩)) = 1)) *
        (cPauliBankFwdAux rElec bitOf f₁ f₂ k hk).eval).1.mulVec (ket β) = ((∏ i : Fin k,
            if act ⟨i.val, by omega⟩ β &&
              (f₁ (bitOf ⟨i.val, by omega⟩) && f₂ (bitOf ⟨i.val, by omega⟩)) then
              Complex.I else 1) * (∏ i : Fin k, if act ⟨i.val, by omega⟩ β &&
              (f₂ (bitOf ⟨i.val, by omega⟩) && decide (β (rElec ⟨i.val, by omega⟩) = 1)) then
              (-1 : ℂ) else 1)) • ket (fun w ↦ if h : ∃ i : Fin k, w = rElec ⟨i.val, by omega⟩ then
            β w + (if act ⟨h.choose.val, by omega⟩ β &&
              f₁ (bitOf ⟨h.choose.val, by omega⟩) then 1 else 0) else β w) := by
  intro k
  induction k with
  | zero =>
      intro hk β
      dsimp only [cPauliBankInvAux, cPauliBankFwdAux]
      rw [bellDiagSign_sum_zero, Circuit.eval_identity, mul_one, mul_one,
          OneMemClass.coe_one, Matrix.one_mulVec]
      simp
  | succ k ih =>
      intro hk β
      let q := rElec ⟨k, hk⟩
      let j := bitOf ⟨k, hk⟩
      let b_fn : Fin mElec → BitAssignment n → ZMod 2 := fun t α ↦
        if act t α && (f₁ (bitOf t) || f₂ (bitOf t)) then 1 else 0
      let U_pref : Unitary (2 ^ n) := bellDiagSign fun g ↦
        decide ((∑ i : Fin (k + 1), b_fn ⟨i.val, by omega⟩ (basisBits n g) *
          basisBits n g (rElec ⟨i.val, by omega⟩)) = 1)
      let p_prev : BitAssignment n → Bool := fun α ↦
        decide ((∑ i : Fin k, b_fn ⟨i.val, by omega⟩ α * α (rElec ⟨i.val, by omega⟩)) = 1)
      let p_one : BitAssignment n → Bool := fun α ↦ decide (b_fn ⟨k, hk⟩ α * α q = 1)
      let U_prev : Unitary (2 ^ n) := bellDiagSign fun g ↦ p_prev (basisBits n g)
      let U_one : Unitary (2 ^ n) := bellDiagSign fun g ↦ p_one (basisBits n g)
      have hU_split : U_pref = U_one * U_prev := bellDiagSign_sum_succ rElec b_fn k hk
      let wFwd := cPauliWireFwd (f₁ j) (f₂ j) q
      let wInv := cPauliWireInv (f₁ j) (f₂ j) q
      let bFwd := cPauliBankFwdAux rElec bitOf f₁ f₂ k (by omega)
      let bInv := cPauliBankInvAux rElec bitOf f₁ f₂ k (by omega)
      have hPrev_wFwd : U_prev * wFwd.eval = wFwd.eval * U_prev := by
        symm
        rw [show wFwd.eval = (QRegister.singleton q).embedUnitary (uPauliLocalFwd (f₁ j) (f₂ j))
          from cPauliWireFwd_eval _ _ q]
        refine singleton_embedUnitary_comm_bellDiagSign_of_ignores q _ p_prev fun α₁ α₂ h ↦ ?_
        dsimp only [p_prev, b_fn]
        congr 1; congr 1; refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hri : rElec ⟨i.val, by omega⟩ ≠ q :=
          rElec.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
        rw [h _ hri, hact ⟨i.val, by omega⟩ α₁ α₂ (fun w hw ↦ h w (hw ⟨k, hk⟩))]
      have hbInv_wInv : bInv.eval * wInv.eval = wInv.eval * bInv.eval := by
        rw [show wInv.eval = (QRegister.singleton q).embedUnitary (uPauliLocalInv (f₁ j) (f₂ j))
          from cPauliWireInv_eval _ _ q]
        exact cPauliBankInvAux_comm_singleton rElec bitOf f₁ f₂ q _ k (by omega) fun i ↦
          rElec.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
      have hbInv_wFwd : bInv.eval * wFwd.eval = wFwd.eval * bInv.eval := by
        rw [show wFwd.eval = (QRegister.singleton q).embedUnitary (uPauliLocalFwd (f₁ j) (f₂ j))
          from cPauliWireFwd_eval _ _ q]
        exact cPauliBankInvAux_comm_singleton rElec bitOf f₁ f₂ q _ k (by omega) fun i ↦
          rElec.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
      have hbInv_Uone : bInv.eval * U_one = U_one * bInv.eval :=
        cPauliBankInvAux_comm_bellDiagSign rElec bitOf f₁ f₂ p_one k (by omega) fun i α₁ α₂ h ↦ by
          have hqi : q ≠ rElec ⟨i.val, by omega⟩ :=
            rElec.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
          have hEq : b_fn ⟨k, hk⟩ α₁ * α₁ q = b_fn ⟨k, hk⟩ α₂ * α₂ q := by
            dsimp only [b_fn]
            rw [h q hqi, hact ⟨k, hk⟩ α₁ α₂ (fun w hw ↦ h w (hw ⟨i.val, by omega⟩))]
          dsimp only [p_one]
          rw [decide_eq_decide, hEq]
      have hFactor : (cPauliBankInvAux rElec bitOf f₁ f₂ (k + 1) hk).eval * U_pref *
          (cPauliBankFwdAux rElec bitOf f₁ f₂ (k + 1) hk).eval =
          (wInv.eval * U_one * wFwd.eval) * (bInv.eval * U_prev * bFwd.eval) := by
        dsimp only [cPauliBankInvAux, cPauliBankFwdAux]
        rw [Circuit.eval_seq, Circuit.eval_seq, hU_split]
        change (bInv.eval * wInv.eval) * (U_one * U_prev) * (wFwd.eval * bFwd.eval) = _
        simp only [mul_assoc]
        rw [← mul_assoc U_prev wFwd.eval, hPrev_wFwd, mul_assoc wFwd.eval,
            ← mul_assoc bInv.eval wInv.eval, hbInv_wInv, mul_assoc wInv.eval,
            ← mul_assoc bInv.eval U_one, hbInv_Uone, mul_assoc U_one,
            ← mul_assoc bInv.eval wFwd.eval, hbInv_wFwd, mul_assoc wFwd.eval]
      let β_prev : BitAssignment n := fun w ↦ if h : ∃ i : Fin k, w = rElec ⟨i.val, by omega⟩ then
          β w + (if act ⟨h.choose.val, by omega⟩ β &&
            f₁ (bitOf ⟨h.choose.val, by omega⟩) then 1 else 0) else β w
      have ihStep := ih (by omega) β
      rw [show (bellDiagSign _) = U_pref from rfl,
          hFactor, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ihStep, Matrix.mulVec_smul]
      have hact_prev : act ⟨k, hk⟩ β_prev = act ⟨k, hk⟩ β := hact ⟨k, hk⟩ β_prev β fun w' hw' ↦
          dite_eq_right (fun ⟨i, hi⟩ ↦ hw' ⟨i.val, by omega⟩ hi)
      have hq_prev : β_prev q = β q := dite_eq_right fun ⟨i, hi⟩ ↦
          rElec.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)) hi.symm
      have hOneStep := singlePauli_conj_phase_ket (f₁ j) (f₂ j) q (act ⟨k, hk⟩)
        (fun α₁ α₂ h ↦ hact ⟨k, hk⟩ α₁ α₂ fun w hw ↦ h w (hw ⟨k, hk⟩)) β_prev
      dsimp only [wInv, wFwd, U_one, p_one, b_fn, j] at hOneStep ⊢
      rw [hOneStep, hact_prev, hq_prev, smul_smul]
      refine congrArg₂ (· • ·) ?_ (congrArg ket ?_)
      · rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
        dsimp only [Fin.val_castSucc, Fin.val_last]
        ring
      · exact update_prefix_dite_eq rElec k hk β
          (fun t ↦ if act t β && f₁ (bitOf t) then 1 else 0)
private theorem zmod2_decide_eq_one_eq_ne_zero (x : ZMod 2) :
    decide (x = 1) = decide (x ≠ 0) := by
  fin_cases x <;> decide
private theorem cPauliBank_conj_uSlotFix_or_eq_smul_xor_mul_fix {n mElec K kData : ℕ}
    (rData : QRegister kData n) (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L)
    (hBitOf : ∀ (t : Fin mElec) (α : BitAssignment n) (j : Fin K),
      rElec t = hBank.slotWires α j → bitOf t = j) (f₁ f₂ : Fin K → Bool) :
    ((cPauliBankInv rElec bitOf f₁ f₂).eval *
      rData.embedUnitary (uSlotFix L (fun j ↦ f₁ j || f₂ j)) *
      (cPauliBankFwd rElec bitOf f₁ f₂).eval).1 = pauliPhaseScalar f₁ f₂ •
      ((rData.embedUnitary (uSlotXor L f₁)).1 * (rData.embedUnitary (uSlotFix L f₂)).1) := by
  let act : Fin mElec → BitAssignment n → Bool := fun t α ↦
    decide (∃ j : Fin K, rElec t = hBank.slotWires α j)
  have hact : ∀ (t : Fin mElec) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ s : Fin mElec, w ≠ rElec s) → α₁ w = α₂ w) → act t α₁ = act t α₂ := by
    intro t α₁ α₂ h
    dsimp only [act]
    rw [hBank.slot_ignores_elec α₁ α₂ h]
  have hSumOr : ∀ g : Fin (2 ^ n), (∑ t : Fin mElec,
        (if act t (basisBits n g) && (f₁ (bitOf t) || f₂ (bitOf t)) then (1 : ZMod 2) else 0) *
          basisBits n g (rElec t)) = (∑ j : Fin K, (if f₁ j || f₂ j then (1 : ZMod 2) else 0) *
          basisBits K (L.tbl (rData.extractIndex g)) j) := fun g ↦
    hBank.sum_elec_eq_slot (basisBits n g) _ _
      (fun t hnot ↦ by simp [act, decide_eq_false hnot])
      (fun t j hj ↦ by
        rw [show act t (basisBits n g) = true from decide_eq_true ⟨j, hj⟩,
            hBitOf t _ j hj, Bool.true_and, hj, hBank.tbl_eq_slot g j])
  apply matrix_ext_single
  intro g
  rw [← ket_basisBits_eq_single g]
  have hUOr : rData.embedUnitary (uSlotFix L (fun j ↦ f₁ j || f₂ j)) = bellDiagSign (fun g' ↦
        decide ((∑ i : Fin mElec, (if act ⟨i.val, i.isLt⟩ (basisBits n g') &&
            (f₁ (bitOf ⟨i.val, i.isLt⟩) || f₂ (bitOf ⟨i.val, i.isLt⟩)) then
            (1 : ZMod 2) else 0) * basisBits n g' (rElec ⟨i.val, i.isLt⟩)) = 1)) := by
    rw [embedUnitary_uSlotFix_eq_bellDiagSign]
    refine congrArg bellDiagSign (funext fun g' ↦ ?_)
    rw [bellF2Parity_eq_decide_sum, ← hSumOr g']
  dsimp only [cPauliBankInv, cPauliBankFwd]
  rw [hUOr, cPauliBankAux_conj_phase_ket rElec bitOf f₁ f₂ act hact mElec le_rfl (basisBits n g)]
  let α := basisBits n g
  let sw := hBank.slotWires α
  have hProd1 : (∏ i : Fin mElec, if act ⟨i.val, i.isLt⟩ α &&
        (f₁ (bitOf ⟨i.val, i.isLt⟩) && f₂ (bitOf ⟨i.val, i.isLt⟩)) then Complex.I else 1) =
      pauliPhaseScalar f₁ f₂ := hBank.prod_elec_eq_slot α _ _
      (fun t hnot ↦ by simp [act, decide_eq_false hnot])
      (fun t j hj ↦ by
        rw [show act t α = true from decide_eq_true ⟨j, hj⟩, hBitOf t α j hj, Bool.true_and])
  have hProd2 : (∏ i : Fin mElec, if act ⟨i.val, i.isLt⟩ α &&
        (f₂ (bitOf ⟨i.val, i.isLt⟩) && decide (α (rElec ⟨i.val, i.isLt⟩) = 1)) then
        (-1 : ℂ) else 1) =
      if bellF2Parity K f₂ (L.tbl (rData.extractIndex g)) then (-1 : ℂ) else 1 := by
    rw [sign_bellF2Parity_eq_prod]
    exact hBank.prod_elec_eq_slot α _ _
      (fun t hnot ↦ by simp [act, decide_eq_false hnot])
      (fun t j hj ↦ by
        have hBitEq : α (rElec t) = basisBits K (L.tbl (rData.extractIndex g)) j := by
          rw [hj]
          exact (hBank.tbl_eq_slot g j).symm
        have hDec : decide (α (rElec t) = 1) =
            decide (basisBits K (L.tbl (rData.extractIndex g)) j ≠ 0) := by
          rw [decide_eq_decide, hBitEq, ← decide_eq_decide]
          exact zmod2_decide_eq_one_eq_ne_zero _
        rw [show act t α = true from decide_eq_true ⟨j, hj⟩, hBitOf t α j hj, Bool.true_and, hDec])
  let v := xorK (L.tbl (rData.extractIndex g)) (boolMaskK f₁)
  have hKetEq : (fun w ↦ if h : ∃ i : Fin mElec, w = rElec ⟨i.val, i.isLt⟩ then
      α w + (if act ⟨h.choose.val, h.choose.isLt⟩ α &&
        f₁ (bitOf ⟨h.choose.val, h.choose.isLt⟩) then 1 else 0) else α w) =
      basisBits n (rData.replaceIndex g (L.updSlot (rData.extractIndex g) v)) := by
    rw [hBank.updSlot_eq_writeReg g v]
    funext w
    by_cases hwSw : w ∈ Set.range sw.wires
    · obtain ⟨j₀, rfl⟩ := hwSw
      obtain ⟨t₀, ht₀⟩ := hBank.slot_in_elec α j₀
      have hex : ∃ i : Fin mElec, sw j₀ = rElec ⟨i.val, i.isLt⟩ := ⟨t₀, ht₀.symm⟩
      rw [dite_eq_left hex, writeReg_apply_reg]
      have hch : (⟨hex.choose.val, hex.choose.isLt⟩ : Fin mElec) = t₀ :=
        rElec.wires.injective (hex.choose_spec.symm.trans ht₀.symm)
      have ha1 : act t₀ α = true := decide_eq_true ⟨j₀, ht₀⟩
      have hTbl0 : α (sw j₀) = basisBits K (L.tbl (rData.extractIndex g)) j₀ :=
        (hBank.tbl_eq_slot g j₀).symm
      rw [hch, ha1, hBitOf t₀ α j₀ ht₀, Bool.true_and, hTbl0]
      dsimp only [v]
      rw [basisBits_xorK]
      dsimp only
      rw [basisBits_boolMaskK]
    · rw [writeReg_apply_of_not_mem _ _ _ w hwSw]
      by_cases hwEl : w ∈ Set.range rElec.wires
      · obtain ⟨t₀, rfl⟩ := hwEl
        have hex : ∃ i : Fin mElec, rElec t₀ = rElec ⟨i.val, i.isLt⟩ := ⟨t₀, rfl⟩
        rw [dite_eq_left hex]
        have hch : (⟨hex.choose.val, hex.choose.isLt⟩ : Fin mElec) = t₀ :=
          rElec.wires.injective hex.choose_spec.symm
        have hnot : ¬ ∃ j : Fin K, rElec t₀ = sw j := fun ⟨j, hj⟩ ↦ hwSw ⟨j, hj.symm⟩
        have ha0 : act t₀ α = false := decide_eq_false hnot
        rw [hch, ha0, Bool.false_and]
        simp [α]
      · have hnot : ¬ ∃ i : Fin mElec, w = rElec ⟨i.val, i.isLt⟩ := fun ⟨i, hi⟩ ↦ hwEl ⟨i, hi.symm⟩
        rw [dite_eq_right hnot]
  rw [hProd1, hProd2, hKetEq, ket_basisBits_eq_single, ket_basisBits_eq_single g,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, uSlotFix,
      embedUnitary_bellDiagSign_mulVec_single rData _ g,
      Matrix.mulVec_smul, embedUnitary_uSlotXor_mulVec_single rData L f₁ g, smul_smul]
/-- Fused single-fixup (`≤ B` `T`, `0 TOFF`, e.g. `436 T` inner + `420 T` context = `856 T`)
Bell-`K` uncompute core: defers `f₁` across `cHadReg rElec` and fuses `X_{s₀}^{f₁} Z_{s₀}^{f₂}`
into one `dFix (f₁ || f₂)` call via `0-T` Pauli-Clifford basis walls! -/
def dPostBellInnerFused {Var : Type} {n mElec K : ℕ}
    (v : Var) (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (rMeas rHeld : QRegister K n) (hHM : rHeld.DisjointWires rMeas)
    (dFix : (Fin K → Bool) → DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (cHadReg rElec ;;ᶜ cHadReg rHeld ;;ᶜ cHeldCzAll rHeld rMeas hHM))
    (DynCircuitExt.measureXResetAndBranch v K rHeld fun f₁ ↦ .seq (.circuit (cHadReg rElec))
        (DynCircuitExt.measureXResetAndBranch v K rMeas fun f₂ ↦
          .seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
            (.seq (dFix (fun j ↦ f₁ j || f₂ j))
              (.circuit (cPauliBankInv rElec bitOf f₁ f₂)))))
theorem dPostBellInnerFused_count_toff {Var : Type} {n mElec K : ℕ}
    (v : Var) (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (rMeas rHeld : QRegister K n) (hHM : rHeld.DisjointWires rMeas)
    {dFix : (Fin K → Bool) → DynamicCircuit Var n} (hFix : ∀ f, (dFix f).count .TOFF = 0) :
    (dPostBellInnerFused v rElec bitOf rMeas rHeld hHM dFix).count .TOFF = 0 := by
  have hLeaf : ∀ f₁ f₂ : Fin K → Bool,
      (DynamicCircuit.seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
        (.seq (dFix (fun j ↦ f₁ j || f₂ j))
          (.circuit (cPauliBankInv rElec bitOf f₁ f₂)))).count .TOFF = 0 := fun f₁ f₂ ↦ by
    rw [dynCount_seq, dynCount_seq, dynCount_circuit, dynCount_circuit,
        cPauliBankFwd_count_toff, cPauliBankInv_count_toff, hFix]
  have hb1 : (DynCircuitExt.measureXResetAndBranch v K rHeld fun f₁ ↦
      .seq (.circuit (cHadReg rElec))
        (DynCircuitExt.measureXResetAndBranch v K rMeas fun f₂ ↦
          .seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
            (.seq (dFix (fun j ↦ f₁ j || f₂ j))
              (.circuit (cPauliBankInv rElec bitOf f₁ f₂))))).count .TOFF = 0 := by
    refine Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v K rHeld _ 0
      fun f₁ ↦ Nat.le_of_eq ?_)
    have hb2 : (DynCircuitExt.measureXResetAndBranch v K rMeas fun f₂ ↦
        .seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
          (.seq (dFix (fun j ↦ f₁ j || f₂ j))
            (.circuit (cPauliBankInv rElec bitOf f₁ f₂)))).count .TOFF = 0 :=
      Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v K rMeas _ 0
        fun f₂ ↦ Nat.le_of_eq (hLeaf f₁ f₂))
    rw [dynCount_seq, dynCount_circuit, cHadReg_count_toff, hb2]
  dsimp only [dPostBellInnerFused]
  rw [dynCount_seq, dynCount_circuit, hb1]
  simp [Circuit.count_seq]
theorem dPostBellInnerFused_count_t_le {Var : Type} {n mElec K B : ℕ}
    (v : Var) (rElec : QRegister mElec n) (bitOf : Fin mElec → Fin K)
    (rMeas rHeld : QRegister K n) (hHM : rHeld.DisjointWires rMeas)
    {dFix : (Fin K → Bool) → DynamicCircuit Var n} (hFix : ∀ f, (dFix f).count .T ≤ B) :
    (dPostBellInnerFused v rElec bitOf rMeas rHeld hHM dFix).count .T ≤ B := by
  have hLeaf : ∀ f₁ f₂ : Fin K → Bool,
      (DynamicCircuit.seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
        (.seq (dFix (fun j ↦ f₁ j || f₂ j))
          (.circuit (cPauliBankInv rElec bitOf f₁ f₂)))).count .T ≤ B := fun f₁ f₂ ↦ by
    have hf := hFix (fun j ↦ f₁ j || f₂ j)
    rw [dynCount_seq, dynCount_seq, dynCount_circuit, dynCount_circuit,
        cPauliBankFwd_count_t, cPauliBankInv_count_t]
    omega
  have hb1 : (DynCircuitExt.measureXResetAndBranch v K rHeld fun f₁ ↦
      .seq (.circuit (cHadReg rElec))
        (DynCircuitExt.measureXResetAndBranch v K rMeas fun f₂ ↦
          .seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
            (.seq (dFix (fun j ↦ f₁ j || f₂ j))
              (.circuit (cPauliBankInv rElec bitOf f₁ f₂))))).count .T ≤ B := by
    refine DynCircuitExt.count_measureXResetAndBranch_T_le v K rHeld _ B fun f₁ ↦ ?_
    have hb2 := DynCircuitExt.count_measureXResetAndBranch_T_le v K rMeas _ B (hLeaf f₁)
    rw [dynCount_seq, dynCount_circuit, cHadReg_count_t]
    omega
  have hc1 : (cHadReg rElec ;;ᶜ cHadReg rHeld ;;ᶜ cHeldCzAll rHeld rMeas hHM).count .T = 0 := by
    simp [Circuit.count_seq]
  dsimp only [dPostBellInnerFused]
  rw [dynCount_seq, dynCount_circuit, hc1]
  omega
theorem subspaceStep_dPostBellInnerFused {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mElec K kData : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rData : QRegister kData n) (rElec : QRegister mElec n)
    (bitOf : Fin mElec → Fin K) (rMeas rHeld : QRegister K n)
    (hDM : rData.DisjointWires rMeas) (hDH : rData.DisjointWires rHeld)
    (hHM : rHeld.DisjointWires rMeas)
    (hEH : rElec.DisjointWires rHeld) (hEM : rElec.DisjointWires rMeas)
    (L : SlotKLens K kData) (hBank : IsBankSlotLens rData rElec L)
    (hBitOf : ∀ (t : Fin mElec) (α : BitAssignment n) (j : Fin K),
      rElec t = hBank.slotWires α j → bitOf t = j) {dFix : (Fin K → Bool) → DynamicCircuit Var n}
    {R : Operator (2 ^ n)} (hSlot0 : (rData.concat rMeas hDM).embedMatrix (P_slot0 L) * R = R)
    (hH0 : rHeld.basisOutcomeProjector 0 * R = R) (hFix : ∀ (f f₁ f₂ : Fin K → Bool),
      let R_fwd := (cPauliBankFwd rElec bitOf f₁ f₂).eval.1 *
        (((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 * R)
      SubspaceStep ((rData.embedUnitary (uSlotFix L f)).1 * R_fwd) R_fwd (dFix f)) :
    SubspaceStep
      ((uBellSlot rData rHeld hDH L).1 * R)
      (((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 * R)
      (dPostBellInnerFused v rElec bitOf rMeas rHeld hHM dFix) := by
  let R_had := (cHadReg rElec).eval.1 * R
  let R_kick := (uKickSlotGlobal rData rMeas L).1 * R_had
  let R_out := ((rData.concat rMeas hDM).embedUnitary (uLensSwap L)).1 * R
  have hH0_had : rHeld.basisOutcomeProjector 0 * R_had = R_had := by
    dsimp only [R_had]
    rw [← Matrix.mul_assoc, (cHadReg_comm_basisOutcomeProjector rElec rHeld hEH 0).symm,
        Matrix.mul_assoc, hH0]
  have hH0_kick : rHeld.basisOutcomeProjector 0 * R_kick = R_kick := by
    dsimp only [R_kick, uKickSlotGlobal]
    rw [← Matrix.mul_assoc, bellDiagSign_comm_basisOutcomeProjector_zero _ rHeld,
        Matrix.mul_assoc, hH0_had]
  have hWallEval : (cHadReg rElec ;;ᶜ cHadReg rHeld ;;ᶜ cHeldCzAll rHeld rMeas hHM).eval =
      (cHeldCzAll rHeld rMeas hHM).eval * ((cHadReg rHeld).eval * (cHadReg rElec).eval) := by
    simp only [Circuit.eval_seq, mul_assoc]
  have hWallEq :
      (cHadReg rElec ;;ᶜ cHadReg rHeld ;;ᶜ cHeldCzAll rHeld rMeas hHM).eval.1 *
        ((uBellSlot rData rHeld hDH L).1 * R) =
      (bellSetTableOp rData rHeld L.tbl * rHeld.basisOutcomeProjector 0) * R_kick := by
    calc (cHadReg rElec ;;ᶜ cHadReg rHeld ;;ᶜ cHeldCzAll rHeld rMeas hHM).eval.1 *
          ((uBellSlot rData rHeld hDH L).1 * R)
        = (cHeldCzAll rHeld rMeas hHM).eval.1 * ((((cHadReg rHeld).eval * (cHadReg rElec).eval) *
              uBellSlot rData rHeld hDH L).1 * R) := by
            rw [hWallEval]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (cHeldCzAll rHeld rMeas hHM).eval.1 *
            (((rData.concat rHeld hDH).embedUnitary (uLensLoad L)).1 * R_had) := by
            rw [bell_hadamard_wall_inv_eq rData rElec rHeld hDH hEH L hBank]
            simp only [R_had, Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (cHeldCzAll rHeld rMeas hHM).eval.1 *
            ((((rData.concat rHeld hDH).embedUnitary (uLensLoad L)).1 *
              rHeld.basisOutcomeProjector 0) * R_had) := by
            rw [Matrix.mul_assoc _ (rHeld.basisOutcomeProjector 0), hH0_had]
      _ = ((cHeldCzAll rHeld rMeas hHM).eval.1 * bellSetTableOp rData rHeld L.tbl *
            rHeld.basisOutcomeProjector 0) * R_had := by
            rw [uLensLoad_mul_projMeas0_eq_setTableOp rData rHeld hDH L]
            simp only [Matrix.mul_assoc]
      _ = (bellSetTableOp rData rHeld L.tbl * rHeld.basisOutcomeProjector 0) * R_kick := by
            rw [cHeldCzAll_mul_setTableOp_held_eq rData rMeas rHeld hHM L]
            simp only [R_kick, Matrix.mul_assoc]
  have s1 := subspaceStep_congr_out (Var := Var) hWallEq
    (subspaceStep_of_circuit (cHadReg rElec ;;ᶜ cHadReg rHeld ;;ᶜ cHeldCzAll rHeld rMeas hHM)
      ((uBellSlot rData rHeld hDH L).1 * R))
  have hHad2Eq : (cHadReg rElec).eval.1 * R_kick =
      (bellSetTableOp rData rMeas L.tbl * rMeas.basisOutcomeProjector 0) * R_out := by
    calc (cHadReg rElec).eval.1 * R_kick
        = ((cHadReg rElec).eval * uKickSlotGlobal rData rMeas L * (cHadReg rElec).eval).1 * R := by
            simp only [R_kick, R_had, Submonoid.coe_mul, Matrix.mul_assoc]
      _ = ((rData.concat rMeas hDM).embedUnitary (uLensWrite L)).1 * R := by
            rw [cHadReg_elec_conj_uKickSlotGlobal_eq_uLensWrite rData rElec rMeas hDM hEM L hBank]
      _ = (((rData.concat rMeas hDM).embedUnitary (uLensWrite L)).1 *
            (rData.concat rMeas hDM).embedMatrix (P_slot0 L)) * R := by
            rw [Matrix.mul_assoc, hSlot0]
      _ = (bellSetTableOp rData rMeas L.tbl * rMeas.basisOutcomeProjector 0) * R_out := by
            rw [uLensWrite_mul_P_slot0_eq_setTableOp_mul_uLensSwap rData rMeas hDM L]
            simp only [R_out, Matrix.mul_assoc, hSlot0]
  have hM0_out : rMeas.basisOutcomeProjector 0 * R_out = R_out :=
    projMeas0_mul_uLensSwap_of_slot0 rData rMeas hDM L hSlot0
  have s2 : SubspaceStep
      ((bellSetTableOp rData rHeld L.tbl * rHeld.basisOutcomeProjector 0) * R_kick)
      R_out
      (DynCircuitExt.measureXResetAndBranch v K rHeld fun f₁ ↦ .seq (.circuit (cHadReg rElec))
          (DynCircuitExt.measureXResetAndBranch v K rMeas fun f₂ ↦
            .seq (.circuit (cPauliBankFwd rElec bitOf f₁ f₂))
              (.seq (dFix (fun j ↦ f₁ j || f₂ j))
                (.circuit (cPauliBankInv rElec bitOf f₁ f₂))))) := by
    refine subspaceStep_measureXReset v rHeld _ _ R_out fun f₁ ↦ ?_
    have hColl1 : DynCircuitExt.xResetKraus rHeld f₁ *
        ((bellSetTableOp rData rHeld L.tbl * rHeld.basisOutcomeProjector 0) * R_kick) =
        (((√(1 / 2)) ^ K : ℝ) : ℂ) • ((rData.embedUnitary (uSlotFix L f₁)).1 * R_kick) := by
      rw [← Matrix.mul_assoc (DynCircuitExt.xResetKraus rHeld f₁),
          ← Matrix.mul_assoc (DynCircuitExt.xResetKraus rHeld f₁),
          xReset_setTableOp_proj0_eq_fix_smul rData rHeld L f₁,
          Matrix.smul_mul, Matrix.mul_assoc (rData.embedUnitary (uSlotFix L f₁)).1, hH0_kick]
    refine subspaceStep_congr_in hColl1 (SubspaceStep.smul (((√(1 / 2)) ^ K : ℝ) : ℂ) ?_)
    have hHad1Eq : (cHadReg rElec).eval.1 * ((rData.embedUnitary (uSlotFix L f₁)).1 * R_kick) =
        (rData.embedUnitary (uSlotXor L f₁)).1 *
          ((bellSetTableOp rData rMeas L.tbl * rMeas.basisOutcomeProjector 0) * R_out) := by
      rw [← Matrix.mul_assoc, ← Submonoid.coe_mul,
          cHadReg_elec_mul_uSlotFix_eq_uSlotXor_mul rData rElec L hBank f₁,
          Submonoid.coe_mul, Matrix.mul_assoc, hHad2Eq]
    have sHad := subspaceStep_congr_out (Var := Var) hHad1Eq
      (subspaceStep_of_circuit (cHadReg rElec) ((rData.embedUnitary (uSlotFix L f₁)).1 * R_kick))
    refine sHad.seq (subspaceStep_measureXReset v rMeas _ _ R_out fun f₂ ↦ ?_)
    have hCommK : DynCircuitExt.xResetKraus rMeas f₂ * (rData.embedUnitary (uSlotXor L f₁)).1 =
        (rData.embedUnitary (uSlotXor L f₁)).1 * DynCircuitExt.xResetKraus rMeas f₂ :=
      xResetKraus_comm_embedMatrix_of_disjoint K rMeas rData (disjointWires_symm hDM) f₂
        (uSlotXor L f₁).1
    have hColl2 : DynCircuitExt.xResetKraus rMeas f₂ * ((rData.embedUnitary (uSlotXor L f₁)).1 *
        ((bellSetTableOp rData rMeas L.tbl * rMeas.basisOutcomeProjector 0) * R_out)) =
        (((√(1 / 2)) ^ K : ℝ) : ℂ) • ((rData.embedUnitary (uSlotXor L f₁)).1 *
          (rData.embedUnitary (uSlotFix L f₂)).1 * R_out) := by
      rw [← Matrix.mul_assoc (DynCircuitExt.xResetKraus rMeas f₂), hCommK,
          Matrix.mul_assoc (rData.embedUnitary (uSlotXor L f₁)).1,
          ← Matrix.mul_assoc (DynCircuitExt.xResetKraus rMeas f₂),
          ← Matrix.mul_assoc (DynCircuitExt.xResetKraus rMeas f₂),
          xReset_setTableOp_proj0_eq_fix_smul rData rMeas L f₂, Matrix.smul_mul, Matrix.mul_smul]
      simp only [Matrix.mul_assoc, hM0_out]
    refine subspaceStep_congr_in hColl2 (SubspaceStep.smul (((√(1 / 2)) ^ K : ℝ) : ℂ) ?_)
    let ω := pauliPhaseScalar f₁ f₂
    let fOr : Fin K → Bool := fun j ↦ f₁ j || f₂ j
    let cFwd := cPauliBankFwd rElec bitOf f₁ f₂
    let cInv := cPauliBankInv rElec bitOf f₁ f₂
    let R_fwd := cFwd.eval.1 * R_out
    have hConj := cPauliBank_conj_uSlotFix_or_eq_smul_xor_mul_fix
      rData rElec bitOf L hBank hBitOf f₁ f₂
    have hFwdIn : cFwd.eval.1 * ((rData.embedUnitary (uSlotXor L f₁)).1 *
          (rData.embedUnitary (uSlotFix L f₂)).1 * R_out) =
        star ω • ((rData.embedUnitary (uSlotFix L fOr)).1 * R_fwd) := by
      have hXZ : (rData.embedUnitary (uSlotXor L f₁)).1 * (rData.embedUnitary (uSlotFix L f₂)).1 =
          star ω • (cInv.eval.1 * (rData.embedUnitary (uSlotFix L fOr)).1 * cFwd.eval.1) := by
        have h1 := congrArg (star ω • ·) hConj
        rw [smul_smul, star_pauliPhaseScalar_mul_self, one_smul] at h1
        exact h1.symm
      have hFI : cFwd.eval.1 * cInv.eval.1 = 1 :=
        congrArg Subtype.val (cPauliBankFwd_mul_cPauliBankInv rElec bitOf f₁ f₂)
      rw [hXZ, Matrix.smul_mul, Matrix.mul_smul]
      refine congrArg (star ω • ·) ?_
      dsimp only [R_fwd]
      simpa only [Matrix.mul_assoc] using
        congrArg (· * ((rData.embedUnitary (uSlotFix L fOr)).1 * (cFwd.eval.1 * R_out)))
          (hFI.trans rfl) |>.trans (Matrix.one_mul _)
    have hIF : cInv.eval.1 * R_fwd = R_out := by
      dsimp only [R_fwd]
      rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, cPauliBankInv_mul_cPauliBankFwd,
          OneMemClass.coe_one, Matrix.one_mul]
    have sFwd := subspaceStep_congr_out (Var := Var) hFwdIn
      (subspaceStep_of_circuit cFwd
        ((rData.embedUnitary (uSlotXor L f₁)).1 * (rData.embedUnitary (uSlotFix L f₂)).1 * R_out))
    have sFix := SubspaceStep.smul (star ω) (hFix fOr f₁ f₂)
    have sInv := SubspaceStep.smul (star ω)
      (subspaceStep_congr_out (Var := Var) hIF (subspaceStep_of_circuit cInv R_fwd))
    have hUnitStar : star (star ω) * star ω = 1 := by
      rw [star_star]
      exact pauliPhaseScalar_mul_star_self f₁ f₂
    exact SubspaceStep.of_unit_smul_out hUnitStar (sFwd.seq (sFix.seq sInv))
  exact s1.seq s2
end Bell18TeleportCore
end ModBell18TeleportCore
end QuantumComputation.Specs.StoppingPowerSolution
end

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

set_option Elab.async false

section Bell18Seq6Bridge

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 512
set_option exponentiation.threshold 256

namespace Bell18Seq6Bridge

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation


/-- Exact `.T`-gate count of `c1` (`16,404 T`) plus fused `c6` (`856 T`): `17,260 T`. -/
abbrev tOuterAnchorBell18PairFused : ℕ := 16404 + 856






/-- Store-closed partial-isometry / subspace `wp` realization on `E_in`. -/
def RealizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in : Operator (2 ^ n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    E_inᴴ * M'.1.1 * E_in = E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in

theorem RealizesOnProj.identity
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in : Operator (2 ^ n)) :
    RealizesOnProj (Var := Var) E_in 1 DynamicCircuit.identity := by
  intro M
  refine ⟨M, ?_, ?_⟩
  · funext σ
    simp [DynamicCircuit.compile]
  · simp

theorem RealizesOnProj.of_circuit
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in : Operator (2 ^ n)) (c : Circuit n) :
    RealizesOnProj (Var := Var) E_in c.eval (.circuit c) := by
  intro M
  refine ⟨qAssignObsMap c.eval M, ?_, ?_⟩
  · funext σ
    rw [compile_circuit, wp_circuit_compile_compat]
    rfl
  · simp [qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]


theorem RealizesOnProj.mul_right
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E_in : Operator (2 ^ n)} (R : Operator (2 ^ n))
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : RealizesOnProj E_in U d) :
    RealizesOnProj (E_in * R) U d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  calc (E_in * R)ᴴ * M'.1.1 * (E_in * R)
      = Rᴴ * (E_inᴴ * M'.1.1 * E_in) * R := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Rᴴ * (E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in) * R := by rw [hproj]
    _ = (E_in * R)ᴴ * (U.1ᴴ * M.1.1 * U.1) * (E_in * R) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem RealizesOnProj.seq_intertwine
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E₁ E₂ V : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (hTrans : U₁.1 * E₁ = E₂ * V)
    (h₁ : RealizesOnProj E₁ U₁ d₁) (h₂ : RealizesOnProj E₂ U₂ d₂) :
    RealizesOnProj E₁ (U₂ * U₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, ?_⟩
  · simp only [compile_seq, wp_qSeq, hwp₂, hwp₁]
  · have hAdj : E₁ᴴ * U₁.1ᴴ = Vᴴ * E₂ᴴ := by
      simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hTrans
    calc E₁ᴴ * M₁.1.1 * E₁
        = (E₁ᴴ * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * E₁) := by
            simpa only [Matrix.mul_assoc] using hproj₁
      _ = Vᴴ * (E₂ᴴ * M₂.1.1 * E₂) * V := by
            rw [hAdj, hTrans]; simp only [Matrix.mul_assoc]
      _ = Vᴴ * (E₂ᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * E₂) * V := by rw [hproj₂]
      _ = (Vᴴ * E₂ᴴ) * U₂.1ᴴ * M.1.1 * U₂.1 * (E₂ * V) := by simp only [Matrix.mul_assoc]
      _ = E₁ᴴ * ((U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1) * E₁ := by
            rw [← hAdj, ← hTrans]
            simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem RealizesOnProj.of_cleanWorkspace_proj
    {Var : Type} [Fintype Var] [DecidableEq Var] {k m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {rWork : QRegister m n}
    (E_pre : Operator (2 ^ n)) {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d) :
    RealizesOnProj (rWork.basisOutcomeProjector 0 * E_pre) (rAct.embedUnitary u) d := by
  have hProjAdj : (rWork.basisOutcomeProjector 0)ᴴ = rWork.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_conjTranspose]
    apply congrArg Matrix.diagonal
    funext g
    by_cases h : rWork.extractIndex g = 0 <;> simp [h]
  refine RealizesOnProj.mul_right E_pre fun M ↦ ?_
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  simpa only [hProjAdj] using hproj

/-- `+0 T`, `0 TOFF` pre-swap Bell-18 wrapper (`c1`): runs `cBellPrep`, unchanged `dSwap`
(`dPreAnchor64x4Fast`, `16,404 T`), then fixed-wire `cCnotHeldToAnc` (`18` `CNOT`s). -/
def dPreBellWrap {Var : Type} {n : ℕ}
    (cBellPrep cCnotHeldToAnc : Circuit n) (dSwap : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  .seq (.circuit cBellPrep) (.seq dSwap (.circuit cCnotHeldToAnc))

theorem dPreBellWrap_counts {Var : Type} {n cT : ℕ}
    {cBellPrep cCnotHeldToAnc : Circuit n} {dSwap : DynamicCircuit Var n}
    (hToffPrep : cBellPrep.count TOFF = 0) (hToffCnot : cCnotHeldToAnc.count TOFF = 0)
    (hToffSwap : dSwap.count TOFF = 0)
    (hTPrep : cBellPrep.count T = 0) (hTCnot : cCnotHeldToAnc.count T = 0)
    (hTSwap : dSwap.count T ≤ cT) :
    (dPreBellWrap cBellPrep cCnotHeldToAnc dSwap).count TOFF = 0 ∧
      (dPreBellWrap cBellPrep cCnotHeldToAnc dSwap).count T ≤ cT := by
  unfold dPreBellWrap
  refine ⟨?_, ?_⟩
  · simp only [DynamicCircuit.count, hToffPrep, hToffCnot, hToffSwap, add_zero]
  · simp only [DynamicCircuit.count, hTPrep, hTCnot, zero_add, add_zero]
    exact hTSwap


/-- `+0 T`, `0 TOFF` Bell-18 PreDiag Clifford wrapper (`p1`/`p3`): appends `cSHeld` (`cS18` on
`rHeld18`) to `cPreDiag` and `cSDagHeld` (`cSDag18` on `rHeld18`) to `cPreDiagInv`. -/
def dWrapPreDiagBell {Var : Type} {n : ℕ}
    (cPreDiag cSHeld cPreDiagInv cSDagHeld : Circuit n)
    (dInner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (cPreDiag ;;ᶜ cSHeld))
    (.seq dInner (.circuit (cPreDiagInv ;;ᶜ cSDagHeld)))

theorem dWrapPreDiagBell_counts {Var : Type} {n cT : ℕ}
    {cPreDiag cSHeld cPreDiagInv cSDagHeld : Circuit n} {dInner : DynamicCircuit Var n}
    (hToff : cPreDiag.count TOFF = 0 ∧ cSHeld.count TOFF = 0 ∧
      cPreDiagInv.count TOFF = 0 ∧ cSDagHeld.count TOFF = 0 ∧ dInner.count TOFF = 0)
    (hT0 : cPreDiag.count T = 0 ∧ cSHeld.count T = 0 ∧
      cPreDiagInv.count T = 0 ∧ cSDagHeld.count T = 0)
    (hTInner : dInner.count T ≤ cT) :
    (dWrapPreDiagBell cPreDiag cSHeld cPreDiagInv cSDagHeld dInner).count TOFF = 0 ∧
      (dWrapPreDiagBell cPreDiag cSHeld cPreDiagInv cSDagHeld dInner).count T ≤ cT := by
  rcases hToff with ⟨h1, h2, h3, h4, h5⟩
  rcases hT0 with ⟨t1, t2, t3, t4⟩
  unfold dWrapPreDiagBell
  refine ⟨?_, ?_⟩
  · simp only [DynamicCircuit.count, Circuit.count_seq, h1, h2, h3, h4, h5, add_zero]
  · simp only [DynamicCircuit.count, Circuit.count_seq, t1, t2, t3, t4, zero_add, add_zero]
    exact hTInner



/-- Parametric opaque-unitary 6-stage Bell-18 `seq6Locked` composition
(`c1 ;; c2 ;; c3 ;; c4 ;; c5 ;; c6`) with outer `.T`-bounds `(t1, t6)` and `0 TOFF`. -/
theorem seq6Bell18_realizesOnProj_gen
    {Var : Type} [Fintype Var] [DecidableEq Var] {n t1 t2 t3 t4 t5 t6 : ℕ} [NeZero (2 ^ n)]
    {E0 E1 E2 E3 E4 E5 V1 V2 V3 V4 V5 : Operator (2 ^ n)}
    {U1 U2 U3 U4 U5 U6 U_tot : Unitary (2 ^ n)}
    {c1 c2 c3 c4 c5 c6 : DynamicCircuit Var n}
    (hTot : U_tot = U6 * (U5 * (U4 * (U3 * (U2 * U1)))))
    (hI1 : U1.1 * E0 = E1 * V1) (hI2 : U2.1 * E1 = E2 * V2)
    (hI3 : U3.1 * E2 = E3 * V3) (hI4 : U4.1 * E3 = E4 * V4) (hI5 : U5.1 * E4 = E5 * V5)
    (hR1 : RealizesOnProj E0 U1 c1) (hR2 : RealizesOnProj E1 U2 c2)
    (hR3 : RealizesOnProj E2 U3 c3) (hR4 : RealizesOnProj E3 U4 c4)
    (hR5 : RealizesOnProj E4 U5 c5) (hR6 : RealizesOnProj E5 U6 c6)
    (hToff : c1.count TOFF = 0 ∧ c2.count TOFF = 0 ∧ c3.count TOFF = 0 ∧
      c4.count TOFF = 0 ∧ c5.count TOFF = 0 ∧ c6.count TOFF = 0)
    (hT1 : c1.count T ≤ t1) (hT2 : c2.count T ≤ t2) (hT3 : c3.count T ≤ t3)
    (hT4 : c4.count T ≤ t4) (hT5 : c5.count T ≤ t5) (hT6 : c6.count T ≤ t6) :
    let d6 := DynamicCircuit.seq c1 (.seq c2 (.seq c3 (.seq c4 (.seq c5 c6))))
    d6.count TOFF = 0 ∧
      d6.count T ≤ (t1 + t6) + (t2 + t3 + t4 + t5) ∧
      RealizesOnProj E0 U_tot d6 := by
  intro d6
  rcases hToff with ⟨z1, z2, z3, z4, z5, z6⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [d6, DynamicCircuit.count, z1, z2, z3, z4, z5, z6, add_zero]
  · simp only [d6, DynamicCircuit.count]
    omega
  · have s56 := hR5.seq_intertwine hI5 hR6
    have s46 := hR4.seq_intertwine hI4 s56
    have s36 := hR3.seq_intertwine hI3 s46
    have s26 := hR2.seq_intertwine hI2 s36
    have s16 := hR1.seq_intertwine hI1 s26
    have hAssoc : U6 * (U5 * (U4 * (U3 * (U2 * U1)))) =
        ((((U6 * U5) * U4) * U3) * U2) * U1 := by
      simp only [mul_assoc]
    rw [hTot, hAssoc]
    exact s16


/-- Fused `856-T` 6-stage Bell-18 `seq6Locked` composition (`c1 ;; c2 ;; c3 ;; c4 ;; c5 ;; c6`)
with `.T`-count `≤ 17,260 + cMid` (`c1 ≤ 16,404`, `c6 ≤ 856` via `dPostBellInnerFused`)
and `0 TOFF`. -/
theorem seq6Bell18_realizesOnProj_fused
    {Var : Type} [Fintype Var] [DecidableEq Var] {n t2 t3 t4 t5 : ℕ} [NeZero (2 ^ n)]
    {E0 E1 E2 E3 E4 E5 V1 V2 V3 V4 V5 : Operator (2 ^ n)}
    {U1 U2 U3 U4 U5 U6 U_tot : Unitary (2 ^ n)}
    {c1 c2 c3 c4 c5 c6 : DynamicCircuit Var n}
    (hTot : U_tot = U6 * (U5 * (U4 * (U3 * (U2 * U1)))))
    (hI1 : U1.1 * E0 = E1 * V1) (hI2 : U2.1 * E1 = E2 * V2)
    (hI3 : U3.1 * E2 = E3 * V3) (hI4 : U4.1 * E3 = E4 * V4) (hI5 : U5.1 * E4 = E5 * V5)
    (hR1 : RealizesOnProj E0 U1 c1) (hR2 : RealizesOnProj E1 U2 c2)
    (hR3 : RealizesOnProj E2 U3 c3) (hR4 : RealizesOnProj E3 U4 c4)
    (hR5 : RealizesOnProj E4 U5 c5) (hR6 : RealizesOnProj E5 U6 c6)
    (hToff : c1.count TOFF = 0 ∧ c2.count TOFF = 0 ∧ c3.count TOFF = 0 ∧
      c4.count TOFF = 0 ∧ c5.count TOFF = 0 ∧ c6.count TOFF = 0)
    (hT1 : c1.count T ≤ 16404) (hT2 : c2.count T ≤ t2) (hT3 : c3.count T ≤ t3)
    (hT4 : c4.count T ≤ t4) (hT5 : c5.count T ≤ t5) (hT6 : c6.count T ≤ 856) :
    let d6 := DynamicCircuit.seq c1 (.seq c2 (.seq c3 (.seq c4 (.seq c5 c6))))
    d6.count TOFF = 0 ∧
      d6.count T ≤ tOuterAnchorBell18PairFused + (t2 + t3 + t4 + t5) ∧
      RealizesOnProj E0 U_tot d6 :=
  seq6Bell18_realizesOnProj_gen hTot hI1 hI2 hI3 hI4 hI5 hR1 hR2 hR3 hR4 hR5 hR6
    hToff hT1 hT2 hT3 hT4 hT5 hT6

end Bell18Seq6Bridge

end Bell18Seq6Bridge

set_option exponentiation.threshold 256
end QuantumComputation.Specs.StoppingPowerSolution
end

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

set_option Elab.async false

noncomputable section Bell18StageABridgeJunction

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false
set_option genSizeOf false

namespace Bell18StageABridgeJunction

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instNeZero_B18Junction (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast_B18Junction (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFast_B18Junction (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFast_B18Junction D).toSemigroup

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_concat_left disjointWires_compose_of_disjoint)
open InterWalkRSum42Hoist
  (kFull80 rCoreFull rSum0 qreg_ext qreg_block_apply)
open Leaf4Ext48TopStitch (rCoreFull_disj_rSum0)
open DoubleDutyFoldedRealizesBridge
  (rPG7Full hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap
  (rFullSysElecSlot_val)
open Slot0SubAdd14And217Stream
  (rSum14Slice42 selCoreSum14In42 slot0AxisInCore slot0AxisVal uSlot0AxisAdd14 uSlot0Sum42Add)
open FullConcrete7StepAndTrueSwapSelect
  (selCoreSum42InAct selCatInCoreSum42PG7 concat_compose_selCoreSum42InAct)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct)
open StageAConjHAndStreamBridge
  (activeOneElecExpQftStage128 rCSFull80 rActStageAFull80)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (uAnchorFrame embedMatrix_selSubstSlot0_eq rDataSubstSlot0_apply_of_not_mem
   rDataSubstSlot0_apply_slot0 rSlot0InCore rSlot0InFull selSubstSlot0 uSlot0MeasSwap)
open StageADeconstrAndQftShare
  (uSlot0MeasSwap_conj_uSlot0Sum42Add_eq)
open Bell18StreamOffset
  (splitSysCatEquiv catModAddMidPerm catModAddPerm catModAddUnitary
   rAxis6In18 elec18AxisWire elec18AxisVal elec18AxisVal_eq_sum
   uElec18AxisAdd14 selElec18Sum14In42 compose_selElec18Sum14In42 uElec18Sum42Add)

theorem basisBits_catModAdd_replaceIndex {N k B : ℕ}
    (rSys : QRegister k N) (rCat : QRegister B N) (hSC : rSys.DisjointWires rCat)
    (shift : BitAssignment k → ℕ) (idx₀ : Fin (2 ^ N)) (w : Fin N) :
    basisBits N ((rSys.concat rCat hSC).replaceIndex idx₀
      (catModAddPerm k B shift ((rSys.concat rCat hSC).extractIndex idx₀))) w =
      if hw : w ∈ Set.range rCat.wires then
        basisBits B ⟨(((basisBitsEquiv B).symm (fun i ↦ basisBits N idx₀ (rCat i))).val +
          shift (fun i ↦ basisBits N idx₀ (rSys i))) % 2 ^ B,
          Nat.mod_lt _ (Nat.two_pow_pos B)⟩ (Classical.choose hw)
      else
        basisBits N idx₀ w := by
  let rSC := rSys.concat rCat hSC
  let β := basisBits N idx₀
  have hext_sys :
      (splitSysCatEquiv k B (rSC.extractIndex idx₀)).1 = fun i ↦ β (rSys i) := by
    funext i
    dsimp only [splitSysCatEquiv, Equiv.trans_apply]
    change basisBits (k + B) (rSC.extractIndex idx₀) (Fin.castAdd B i) = β (rSys i)
    simp [rSC, β]
  have hext_cat_fin :
      (splitSysCatEquiv k B (rSC.extractIndex idx₀)).2 =
        (basisBitsEquiv B).symm (fun i ↦ β (rCat i)) := by
    change (basisBitsEquiv B).symm
        (fun j ↦ basisBits (k + B) (rSC.extractIndex idx₀) (Fin.natAdd k j)) =
      (basisBitsEquiv B).symm (fun i ↦ β (rCat i))
    congr 1
    funext j
    simp [rSC, β]
  have hcat_eq :
      catModAddPerm k B shift (rSC.extractIndex idx₀) =
        (splitSysCatEquiv k B).symm
          (fun i ↦ β (rSys i),
            ⟨(((basisBitsEquiv B).symm (fun i ↦ β (rCat i))).val +
              shift (fun i ↦ β (rSys i))) % 2 ^ B,
              Nat.mod_lt _ (Nat.two_pow_pos B)⟩) := by
    simp only [catModAddPerm, Equiv.trans_apply]
    congr 1
    ext
    · dsimp only [catModAddMidPerm, Equiv.coe_fn_mk]
      exact congrFun hext_sys _
    · simp only [catModAddMidPerm, Equiv.coe_fn_mk, hext_sys, hext_cat_fin]
  by_cases hwSC : w ∈ Set.range rSC.wires
  · rcases hwSC with ⟨idx, rfl⟩
    rw [rSC.basisBits_replaceIndex_apply, hcat_eq]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      have hi_not : rSys i ∉ Set.range rCat.wires := fun ⟨q, hq⟩ ↦ hSC.ne i q hq.symm
      rw [dite_eq_right hi_not]
      simp [splitSysCatEquiv, β]
    · rw [QRegister.concat_apply_right]
      have hj_mem : rCat j ∈ Set.range rCat.wires := ⟨j, rfl⟩
      rw [dite_eq_left hj_mem]
      have hj_eq : Classical.choose hj_mem = j :=
        rCat.wires.injective (Classical.choose_spec hj_mem)
      rw [hj_eq]
      simp [splitSysCatEquiv, β]
  · have hw_not : w ∉ Set.range rCat.wires := fun ⟨j, hj⟩ ↦
      hwSC ⟨Fin.natAdd k j, by
        dsimp only [rSC]
        rw [QRegister.concat_apply_right]
        exact hj⟩
    rw [rSC.basisBits_replaceIndex_of_not_mem idx₀ _ w hwSC, dite_eq_right hw_not]

private theorem embedUnitary_catModAddUnitary_congr_sys {N k₁ k₂ B : ℕ}
    (rSys₁ : QRegister k₁ N) (rSys₂ : QRegister k₂ N) (rCat : QRegister B N)
    (h₁ : rSys₁.DisjointWires rCat) (h₂ : rSys₂.DisjointWires rCat)
    (shift₁ : BitAssignment k₁ → ℕ) (shift₂ : BitAssignment k₂ → ℕ)
    (hShift : ∀ β : BitAssignment N,
      shift₁ (fun i ↦ β (rSys₁ i)) = shift₂ (fun i ↦ β (rSys₂ i))) :
    (rSys₁.concat rCat h₁).embedUnitary (catModAddUnitary k₁ B shift₁) =
      (rSys₂.concat rCat h₂).embedUnitary (catModAddUnitary k₂ B shift₂) := by
  let rSC₁ := rSys₁.concat rCat h₁
  let rSC₂ := rSys₂.concat rCat h₂
  apply Subtype.ext
  ext i j
  have hCol :
      (rSC₁.embedUnitary (catModAddUnitary k₁ B shift₁)).1.mulVec (Pi.single j 1) =
        (rSC₂.embedUnitary (catModAddUnitary k₂ B shift₂)).1.mulVec (Pi.single j 1) := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, catModAddUnitary, catModAddUnitary,
      rSC₁.embedMatrix_mulVec_single_factors, rSC₂.embedMatrix_mulVec_single_factors,
      permutationUnitary_mulVec_single, permutationUnitary_mulVec_single,
      rSC₁.tensorState_single_replaceIndex, rSC₂.tensorState_single_replaceIndex]
    congr 1
    apply (basisBitsEquiv N).injective
    funext w
    change basisBits N (rSC₁.replaceIndex j _) w = basisBits N (rSC₂.replaceIndex j _) w
    dsimp only [rSC₁, rSC₂]
    rw [basisBits_catModAdd_replaceIndex rSys₁ rCat h₁ shift₁ j w,
        basisBits_catModAdd_replaceIndex rSys₂ rCat h₂ shift₂ j w, hShift (basisBits N j)]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hCol i

private theorem slot0AxisVal_eq_sum {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    slot0AxisVal w γ = ∑ r : Fin 6, 2 ^ r.val * (γ (slot0AxisInCore w r)).val := by
  change (∑ r : Fin 6, (γ (slot0AxisInCore w r)).val * 2 ^ r.val) = _
  exact Finset.sum_congr rfl fun r _ ↦ mul_comm _ _

private theorem compose_selCoreSum14In42 {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n)
    (hCSum42 : rCore.DisjointWires rSum42) (w : Fin 3) :
    (rCore.concat rSum42 hCSum42).compose (selCoreSum14In42 mPayload w) =
      rCore.concat (rSum42.compose (rSum14Slice42 w))
        (hCSum42.compose_right (rSum14Slice42 w)) := by
  apply qreg_ext; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) idx
  · dsimp only [selCoreSum14In42]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hc : QRegister.block 0 (fullSysCoreWires mPayload)
        (by omega : 0 + fullSysCoreWires mPayload ≤ fullSysCoreWires mPayload + 42) iC =
        Fin.castAdd 42 iC :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_left]
  · dsimp only [selCoreSum14In42]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right, QRegister.compose_apply,
      QRegister.compose_apply]
    have hc : QRegister.block (fullSysCoreWires mPayload) 42 le_rfl (rSum14Slice42 w j14) =
        Fin.natAdd (fullSysCoreWires mPayload) (rSum14Slice42 w j14) :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_right]

private theorem slot0AxisInCore80_val_eq_elec18AxisWire (w : Fin 3) (r : Fin 6) :
    (slot0AxisInCore (mPayload := 80) w r).val = (elec18AxisWire w r).val := by
  have hL : (slot0AxisInCore (mPayload := 80) w r).val = (18 * 0 + 6 * w.val) + r.val := rfl
  have hR : (elec18AxisWire w r).val = 6 * w.val + r.val := by
    simp [elec18AxisWire, rAxis6In18]
  omega

/-- Embedding `uSlot0Sum42Add 80` on `rCore ++ rSum42` agrees with `uElec18Sum42Add` on `rE18`. -/
theorem embed_uSlot0Sum42Add_eq_uElec18Sum42Add {N : ℕ}
    (rCore : QRegister (fullSysCoreWires 80) N)
    (rE18 : QRegister 18 N) (rSum42 : QRegister 42 N)
    (hCS : rCore.DisjointWires rSum42) (hES : rE18.DisjointWires rSum42)
    (hSlot0 : ∀ q : Fin 18,
      rCore ⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ = rE18 q) :
    (rCore.concat rSum42 hCS).embedUnitary (uSlot0Sum42Add 80) =
      (rE18.concat rSum42 hES).embedUnitary uElec18Sum42Add := by
  have hAx : ∀ w : Fin 3,
      (rCore.concat rSum42 hCS).embedUnitary
        ((selCoreSum14In42 80 w).embedUnitary (uSlot0AxisAdd14 w)) =
      (rE18.concat rSum42 hES).embedUnitary
        ((selElec18Sum14In42 w).embedUnitary (uElec18AxisAdd14 w)) := fun w ↦ by
    rw [← QRegister.embedUnitary_compose, compose_selCoreSum14In42,
        ← QRegister.embedUnitary_compose, compose_selElec18Sum14In42]
    change (rCore.concat (rSum42.compose (rSum14Slice42 w)) (hCS.compose_right _)).embedUnitary
          (catModAddUnitary (fullSysCoreWires 80) 14 (slot0AxisVal w)) =
        (rE18.concat (rSum42.compose (rSum14Slice42 w)) (hES.compose_right _)).embedUnitary
          (catModAddUnitary 18 14 (elec18AxisVal w))
    refine embedUnitary_catModAddUnitary_congr_sys rCore rE18
      (rSum42.compose (rSum14Slice42 w))
      (hCS.compose_right _) (hES.compose_right _)
      (slot0AxisVal w) (elec18AxisVal w) fun β ↦ ?_
    rw [slot0AxisVal_eq_sum, elec18AxisVal_eq_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hIdx : slot0AxisInCore (mPayload := 80) w r =
        ⟨(elec18AxisWire w r).val,
          lt_of_lt_of_le (elec18AxisWire w r).isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ :=
      Fin.ext (slot0AxisInCore80_val_eq_elec18AxisWire w r)
    rw [hIdx, hSlot0 (elec18AxisWire w r)]
  unfold uSlot0Sum42Add uElec18Sum42Add
  simp only [QRegister.embedUnitary_mul, hAx 0, hAx 1, hAx 2]

/-- Transport `RealizesEmbeddedUnitaryWithCleanWorkspace` across equal embedded unitaries. -/
theorem realizesClean_congr_embed
    {Var : Type} [Fintype Var] [DecidableEq Var] {k₁ k₂ m n : ℕ} [NeZero (2 ^ n)]
    {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n} {rW : QRegister m n}
    {U₁ : Unitary (2 ^ k₁)} {U₂ : Unitary (2 ^ k₂)} {d : DynamicCircuit Var n}
    (hU : r₁.embedUnitary U₁ = r₂.embedUnitary U₂)
    (h : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₁ rW U₁ d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₂ rW U₂ d := by
  intro M
  obtain ⟨M', hwp, hEq⟩ := h M
  rw [hU] at hEq
  exact ⟨M', hwp, hEq⟩

/-- Full-width (`kFull80`) `uSlot0Sum42Add 80` unitary at the Stage-A / Stage-B seam. -/
noncomputable abbrev uAddStageAFull : Unitary (2 ^ kFull80) :=
  rActStageAFull80.embedUnitary (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80))

/-- Combined `(18 + 42)`-wire selector `(rAnchor18, rSum0)` inside `kFull80 + 18`. -/
def selAncSum0InFull18 : QRegister (18 + 42) (kFull80 + 18) :=
  (selMeasInAct kFull80).concat ((selDataInAct kFull80).compose rSum0)
    ((QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kFull80)).compose_right rSum0)

/-- Anchor-slot `18`-electron addition into `rSum0` directly on `kFull80 + 18`. -/
noncomputable def uAdd0AncFull18 : Unitary (2 ^ (kFull80 + 18)) :=
  selAncSum0InFull18.embedUnitary uElec18Sum42Add

theorem uAnchorFrame_uAddStageAFull_eq :
    uAnchorFrame uAddStageAFull = uAdd0AncFull18 := by
  have hSwap := uSlot0MeasSwap_conj_uSlot0Sum42Add_eq.1
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uAddStageAFull * uSlot0MeasSwap =
    uAnchorFrame uAddStageAFull at hSwap
  have hSubMat : (selSubstSlot0 rSlot0InFull).embedUnitary uAddStageAFull =
      uAnchorFrame uAddStageAFull := by
    rw [← hSwap]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull uAddStageAFull.1)
  rw [← hSubMat]
  unfold uAddStageAFull uAdd0AncFull18
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
  let rSub := selSubstSlot0 rSlot0InFull
  let rSubCore := rSub.compose rCoreFull
  let rSubSum := rSub.compose rSum0
  let rSubPG7 := rSub.compose rPG7Full
  let hSubCS := disjointWires_compose_of_disjoint rSub rCoreFull_disj_rSum0
  let hSubCPG := disjointWires_compose_of_disjoint rSub hCoreFull_disj_rPG7Full
  let hSubSPG := disjointWires_compose_of_disjoint rSub rSum0_disj_rPG7Full
  have hSubActEq : rSub.compose rActStageAFull80 =
      (rSubCore.concat rSubSum hSubCS).concat rSubPG7
        (disjointWires_concat_left hSubCS hSubCPG hSubSPG) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun iCS ↦ ?_) (fun mPG ↦ ?_) idx
    · refine Fin.addCases (fun iC ↦ ?_) (fun jS ↦ ?_) iCS
      · simp [rSubCore, rActStageAFull80, rCSFull80, QRegister.concat_apply_left]
      · simp [rSubSum, rActStageAFull80, rCSFull80, QRegister.concat_apply_left,
        QRegister.concat_apply_right]
    · simp [rSubPG7, rActStageAFull80, QRegister.concat_apply_right]
  have hSubCSComp : (rSub.compose rActStageAFull80).compose selCoreSum42InAct =
      rSubCore.concat rSubSum hSubCS := by
    rw [hSubActEq, concat_compose_selCoreSum42InAct _ rSubPG7
      (disjointWires_concat_left hSubCS hSubCPG hSubSPG)]
  rw [hSubCSComp]
  have hSumEq : rSubSum = (selDataInAct kFull80).compose rSum0 := by
    apply qreg_ext; intro j
    have hnot : rSum0 j ∉ Set.range rSlot0InFull.wires := by
      rintro ⟨q, hq⟩
      have hDisj : rSlot0InFull.DisjointWires rSum0 :=
        rCoreFull_disj_rSum0.compose_left rSlot0InCore
      exact hDisj.ne q j hq
    dsimp only [rSubSum, rSub, QRegister.compose_apply]
    rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem rSlot0InFull _ _ _ hnot]
  have hDisjM : (selMeasInAct kFull80).DisjointWires rSubSum := by
    rw [hSumEq]
    exact (QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kFull80)).compose_right rSum0
  have hSlot0 : ∀ q : Fin 18,
      rSubCore ⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ =
        selMeasInAct kFull80 q := fun q ↦ by
    have hq : (⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ :
        Fin (fullSysCoreWires 80)) = rSlot0InCore q :=
      Fin.ext (by rw [rSlot0InCore, rFullSysElecSlot_val]; simp)
    rw [hq]
    dsimp only [rSubCore, rSub, QRegister.compose_apply]
    change selSubstSlot0 rSlot0InFull (rSlot0InFull q) = selMeasInAct kFull80 q
    rw [selSubstSlot0, rDataSubstSlot0_apply_slot0]
  rw [embed_uSlot0Sum42Add_eq_uElec18Sum42Add rSubCore (selMeasInAct kFull80) rSubSum
    hSubCS hDisjM hSlot0]
  refine congrArg (fun r : QRegister (18 + 42) (kFull80 + 18) ↦ r.embedUnitary _)
    (qreg_ext fun idx ↦ ?_)
  refine Fin.addCases (fun q ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.concat_apply_left, selAncSum0InFull18, QRegister.concat_apply_left]
  · rw [QRegister.concat_apply_right, selAncSum0InFull18, QRegister.concat_apply_right, hSumEq]

/-- Full-width (`kFull80`) `activeOneElecExpQftStage128.uCat` unitary at Stage-A/B seam. -/
noncomputable abbrev uExpQftStageAFull : Unitary (2 ^ kFull80) :=
  rActStageAFull80.embedUnitary
    (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat)

/-- Full-width (`kFull80`) raw-catalyst seam unitary `uAddStageAFull * uExpQftStageAFull⁻¹`. -/
noncomputable abbrev uJunctionRawFull : Unitary (2 ^ kFull80) :=
  uAddStageAFull * uExpQftStageAFull⁻¹

end Bell18StageABridgeJunction

end Bell18StageABridgeJunction

section B18_SelfContainedBorrow136
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option maxSynthPendingDepth 3
namespace Bell18StageABridge_Borrow136.ChiralA
noncomputable section Impl
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
set_option exponentiation.threshold 512
set_option maxRecDepth 200000
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice
open InPlaceStepEngine
open NuclearTwistAndXor654Concrete (dXor32All654 count_dXor32All654_t count_dXor32All654_toff)
open NuclearTwistRealizes (RealizesCleanPair uXor32Core dXor32All654_realizesPair slot2AxisSum
  bitsVal_eq_of_testBit)
open SinglePassNuclearTwist288
open HybridStream288Aux
open HybridStream168Aux
local instance (priority := 1000000) instNeZeroTwoPowStageABrgA (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-- Local irreducible wrapper for `dXor32All654`. -/
noncomputable def dXor32CoreLoc {Var : Type} {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) : DynamicCircuit Var n :=
  dXor32All654 (Var := Var) rCore
theorem count_dXor32CoreLoc_t {Var : Type} {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dXor32CoreLoc (Var := Var) rCore).count T = 0 :=
  count_dXor32All654_t rCore
theorem count_dXor32CoreLoc_toff {Var : Type} {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dXor32CoreLoc (Var := Var) rCore).count TOFF = 0 :=
  count_dXor32All654_toff rCore
theorem dXor32CoreLoc_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload kWork n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister kWork n) :
    RealizesCleanPair rCore rWork (uXor32Core mPayload)
      (dXor32CoreLoc (Var := Var) rCore) (dXor32CoreLoc (Var := Var) rCore) :=
  dXor32All654_realizesPair (Var := Var) rCore rWork
attribute [irreducible] dXor32CoreLoc
theorem step1XorK_inComb_geK {N kCore K S : ℕ} (inCore : Fin N → Wire kCore) (i : Fin N) :
    K ≤ (inCombWire (W := K) (S := S) (q := 0) inCore i).val := by
  dsimp [inCombWire]; omega
theorem step1XorK_cur0_geK (K kCore : ℕ) : K ≤ K + kCore :=
  Nat.le_add_right K kCore
theorem step1XorK_le_M (K kCore S : ℕ) : K ≤ (K + kCore) + S := by omega
/-- Parametric `TempPhaseProg` (`spec` + `K` CNOTs, `S` `TempAnd`s, self-inverse)
for any carry-free `K`-bit `WeightedCsa3GenSpec B₀ B₁ B₂ K S`. -/
noncomputable def step1XorKProg {B₀ B₁ B₂ K S kCore : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    InPlaceFullAddSlice.TempPhaseProg ((K + kCore) + S) :=
  let cur₀ := K + kCore
  let inComb := inCombWire (W := K) (S := S) (q := 0) inCore
  let hb₀ : cur₀ + S ≤ (K + kCore) + S := le_rfl
  let outW := spec.outWire cur₀ inComb hb₀
  let hOutGe : ∀ k : Fin K, K ≤ (outW k).val :=
    fun k ↦
      spec.outWire_ge cur₀ inComb (step1XorK_inComb_geK inCore) (step1XorK_cur0_geK K kCore) hb₀ k
  withWeightedCsa3Gen spec cur₀ inComb
    (inCombWire_injective hInj)
    (inCombWire_lt_cur0 inCore)
    hb₀
    (xorOutLoop (step1XorK_le_M K kCore S) outW hOutGe K le_rfl)
/-- Parametric `DynamicCircuit` wrapper for `step1XorKProg` consuming `S ≤ mWork` clean workspace
  wires. -/
noncomputable def dStep1XorK {Var : Type} {B₀ B₁ B₂ K S kCore mWork n : ℕ}
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (hK : 0 < K)
    (rCore : QRegister kCore n) (rAcc : QRegister K n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : S ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    DynamicCircuit Var n :=
  let _ := hK
  let rComb := mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork
  ((step1XorKProg spec inCore hInj).onRegister rComb).toDyn v
theorem dStep1XorK_counts {Var : Type} {B₀ B₁ B₂ K S kCore mWork n : ℕ}
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (hK : 0 < K)
    (rCore : QRegister kCore n) (rAcc : QRegister K n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : S ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    let dyn := dStep1XorK v spec hK rCore rAcc rWork hCA hCW hAW hmWork inCore hInj
    dyn.count TOFF = 0 ∧ dyn.count T = 4 * S := by
  intro dyn
  refine ⟨InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _, ?_⟩
  dsimp [dyn, dStep1XorK]
  rw [InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
    InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd]
  simp [step1XorKProg]
theorem dStep1XorK_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {B₀ B₁ B₂ K S kCore mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (hK : 0 < K)
    (hCin : spec.cinWire = none)
    (hMax : B₀ + 2 * B₁ + 4 * B₂ < 2 ^ K)
    (rCore : QRegister kCore n) (rAcc : QRegister K n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : S ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    let dyn := dStep1XorK v spec hK rCore rAcc rWork hCA hCW hAW hmWork inCore hInj
    RealizesCleanPair (rCore.concat rAcc hCA) rWork
      (uBitXor kCore K (weightedGenBatchVal inCore)) dyn dyn := by
  let M := (K + kCore) + S
  let cur₀ := K + kCore
  let inComb : Fin (B₀ + B₁ + B₂) → Wire M := inCombWire (W := K) (S := S) (q := 0) inCore
  have hInjComb : Function.Injective inComb := inCombWire_injective hInj
  have hGeK : ∀ i : Fin (B₀ + B₁ + B₂), K ≤ (inComb i).val := fun i ↦
    by dsimp [inComb, inCombWire]; omega
  have hLtComb : ∀ i : Fin (B₀ + B₁ + B₂), (inComb i).val < cur₀ := inCombWire_lt_cur0 inCore
  have hb₀ : cur₀ + S ≤ M := le_rfl
  let outW : Fin K → Wire M := spec.outWire cur₀ inComb hb₀
  have hOutGeK : ∀ k : Fin K, K ≤ (outW k).val :=
    fun k ↦ spec.outWire_ge cur₀ inComb hGeK (by dsimp [cur₀]; omega) hb₀ k
  have hOutLt : ∀ k : Fin K, (outW k).val < M :=
    fun k ↦ spec.outWire_lt cur₀ inComb hLtComb hb₀ k
  have hTBXor := xorOutLoop_spec (M := M) (W := K) (rem := 0) (Nat.zero_le M)
    (by dsimp [M]; omega) outW hOutGeK (fun k ↦
      by simp only [Nat.sub_zero]; exact hOutLt k) K le_rfl
  have hrem0 : M - (cur₀ + S) = 0 := by dsimp [M, cur₀]; omega
  have hTBXor' : TargetBlock M K (M - (cur₀ + S))
      (fun β w ↦
        if _hw : w.val < K then
          if _hkm : K - 1 - w.val < K then β w + β (outW ⟨K - 1 - w.val, by omega⟩) else β w
        else β w)
      (fun _ ↦ 0)
      (xorOutLoop (by omega) outW hOutGeK K le_rfl) := by
    rw [hrem0]; exact hTBXor
  have hTB1 := HybridStream168Aux.TargetBlock.withWeightedCsa3Gen_block
    (targetEnd := K) spec cur₀ inComb
    hInjComb hGeK hLtComb (by dsimp [cur₀]; omega) hb₀ hTBXor'
  have hremS : M - cur₀ = S := by dsimp [M, cur₀]; omega
  have hTBFull : TargetBlock M K S
      (fun β w ↦
        let βcsa := evalWeightedCsa3Gen spec cur₀ inComb hInjComb hLtComb hb₀ β
        if _hw : w.val < K then
          if _hkm : K - 1 - w.val < K then βcsa w + βcsa (outW ⟨K - 1 - w.val, by omega⟩) else
            βcsa w
        else βcsa w)
      (fun _ ↦ 0)
      (step1XorKProg spec inCore hInj) := by
    refine ⟨?_, fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
    · have hv := hTB1.valid; rw [hremS] at hv; exact hv
    · have hβ' : InPlaceFullAddSlice.cleanRem M (M - cur₀) β := by rw [hremS]; exact hβ
      exact hTB1.bits β hβ' w
    · have hβ' : InPlaceFullAddSlice.cleanRem M (M - cur₀) β := by rw [hremS]; exact hβ
      exact hTB1.sign β hβ'
  refine TargetBlock.toBitXorPair v rCore rAcc rWork hCA hCW hAW hmWork
    (weightedGenBatchVal inCore) hTBFull fun β _ j ↦ ?_
  let βcsa := evalWeightedCsa3Gen spec cur₀ inComb hInjComb hLtComb hb₀ β
  have hjLt := j.isLt
  have hjK : K - 1 - j.val < K := by omega
  have hkm : K - 1 - (K - 1 - j.val) < K := by omega
  dsimp only
  simp only [hjK, hkm, ↓reduceDIte]
  have hfin : (⟨K - 1 - (K - 1 - j.val), by omega⟩ : Fin K) = j := Fin.ext (by dsimp; omega)
  rw [hfin]
  change βcsa ⟨K - 1 - j.val, by omega⟩ + βcsa (outW j) = _
  have hUnt : βcsa ⟨K - 1 - j.val, by omega⟩ = β ⟨K - 1 - j.val, by omega⟩ :=
    evalWeightedCsa3Gen_untouched spec cur₀ inComb hInjComb hLtComb hb₀ β _
      (fun i ↦ wire_ne_of_lt (by have := hGeK i; dsimp; omega))
      (by dsimp [cur₀]; omega)
  rw [hUnt]
  let xCore : BitAssignment kCore := fun q ↦ β (Fin.castAdd S (Fin.natAdd K q))
  have hSumEq := evalWeightedCsa3Gen_sum_eq spec cur₀ inComb hInjComb hLtComb hb₀ β
  have hCin0 : optBitVal (spec.cinOutWire cur₀ inComb hb₀) βcsa = 0 := by
    simp [WeightedCsa3GenSpec.cinOutWire, hCin, optBitVal]
  rw [hCin0, add_zero] at hSumEq
  have hBitsLhs : bitsVal (fun k : Fin K ↦ βcsa (outW k)) =
      ∑ k : Fin K, 2 ^ k.val * (βcsa (outW k)).val := by
    unfold bitsVal
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hRhsEq :
      ((∑ i : Fin B₀, (β (inComb ⟨i.val, by omega⟩)).val) +
        (∑ i : Fin B₁, 2 * (β (inComb ⟨B₀ + i.val, by omega⟩)).val) +
        (∑ i : Fin B₂, 4 * (β (inComb ⟨(B₀ + B₁) + i.val, by omega⟩)).val)) =
      weightedGenBatchVal inCore xCore := rfl
  have hValLt : weightedGenBatchVal inCore xCore < 2 ^ K := by
    have := weightedGenBatchVal_le inCore xCore
    omega
  have hBitsEq : (fun k : Fin K ↦ βcsa (outW k)) =
      (fun k : Fin K ↦ if (weightedGenBatchVal inCore xCore).testBit k.val then 1 else 0) := by
    apply bitsVal_injective
    rw [hBitsLhs, hSumEq, hRhsEq, bitsVal_eq_of_testBit K _ hValLt]
  rw [congrFun hBitsEq j]
attribute [irreducible] dStep1XorK
/-- Opaque local forward wrapper around `dWeightedGenModAdd` preventing kernel AST unfolding. -/
noncomputable def dWeightedModAdd {Var : Type} {B₀ B₁ B₂ K S kCore W mWork n : ℕ}
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hW : 0 < W) (hmWork : S + (W - 1) ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    DynamicCircuit Var n :=
  dWeightedGenModAdd v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
/-- Opaque local inverse wrapper around `dWeightedGenModInv` preventing kernel AST unfolding. -/
noncomputable def dWeightedModInv {Var : Type} {B₀ B₁ B₂ K S kCore W mWork n : ℕ}
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hW : 0 < W) (hmWork : S + (W - 1) ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    DynamicCircuit Var n :=
  dWeightedGenModInv v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
theorem dWeightedModAdd_counts {Var : Type} {B₀ B₁ B₂ K S kCore W mWork n : ℕ}
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hW : 0 < W) (hmWork : S + (W - 1) ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    let dFwd := dWeightedModAdd v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
    let dInv := dWeightedModInv v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
    dFwd.count TOFF = 0 ∧ dInv.count TOFF = 0 ∧
      dFwd.count T ≤ 4 * (S + (W - 1)) ∧ dInv.count T ≤ 4 * (S + (W - 1)) :=
  dWeightedGenModAdd_counts v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
theorem dWeightedModAdd_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {B₀ B₁ B₂ K S kCore W mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hW : 0 < W) (hmWork : S + (W - 1) ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    RealizesCleanPair (rCore.concat rAcc hCA) rWork
      (catModAddUnitary kCore W (weightedGenBatchVal inCore))
      (dWeightedModAdd v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj)
      (dWeightedModInv v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj) :=
  dWeightedGenModAdd_realizesPair v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
attribute [irreducible] dWeightedModAdd dWeightedModInv
theorem accInvar_step1_bitXorK {kCore n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister kCore n) (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14)
    (K : ℕ) (hSliceK : 0 + K ≤ 14)
    (V : BitAssignment kCore → ℕ)
    (β₀ : BitAssignment n) (hInv0 : accInvar rSum14 0 β₀ β₀)
    (hVlt : V (fun q ↦ β₀ (rCore q)) < 2 ^ K) :
    ∃ β₁ : BitAssignment n,
      ((rCore.concat rSum14 hCSum).embedUnitary
          ((selCoreSlice kCore 0 K hSliceK).embedUnitary (uBitXor kCore K V))).1.mulVec
        (basisKet β₀) = basisKet β₁ ∧
      accInvar rSum14 (V (fun q ↦ β₀ (rCore q))) β₀ β₁ := by
  let rSliceK := rSum14.slice 0 K hSliceK
  let xCore : BitAssignment kCore := fun q ↦ β₀ (rCore q)
  let β₁ : BitAssignment n := fun z ↦
    if hz : z ∈ rSum14.image then
      if (V xCore).testBit (Classical.choose ((QRegister.mem_image rSum14 z).mp hz)).val
      then 1 else 0
    else β₀ z
  have hout14 : ∀ z : Wire n, z ∉ rSum14.image → β₁ z = β₀ z := fun z hz ↦ by
    simp only [β₁, hz, ↓reduceDIte]
  have hin14 : ∀ i : Fin 14, β₁ (rSum14 i) = if (V xCore).testBit i.val then 1 else 0 := fun i ↦ by
    have hm : rSum14 i ∈ rSum14.image := (QRegister.mem_image rSum14 _).mpr ⟨i, rfl⟩
    have hch : Classical.choose ((QRegister.mem_image rSum14 (rSum14 i)).mp hm) = i :=
      rSum14.wires.injective (Classical.choose_spec ((QRegister.mem_image rSum14 (rSum14 i)).mp hm))
    simp only [β₁, hm, ↓reduceDIte, hch]
  refine ⟨β₁, ?_, hout14, hin14⟩
  rw [embedUnitary_selCoreSlice_val]
  refine uBitXor_mulVec_basisKet rCore rSliceK (disj_slice14 hCSum 0 K hSliceK) V β₀ β₁
    (fun z hzK ↦ ?_) (fun j ↦ ?_)
  · by_cases hz14 : z ∈ rSum14.image
    · obtain ⟨i, rfl⟩ := (QRegister.mem_image rSum14 z).mp hz14
      have hgeK : K ≤ i.val := by
        by_contra hlt
        refine hzK ((QRegister.mem_image rSliceK _).mpr ⟨⟨i.val, by omega⟩, ?_⟩)
        rw [QRegister.slice_apply]; congr 1; ext; simp
      have htb_false : (V xCore).testBit i.val = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hVlt (Nat.pow_le_pow_right (by decide) hgeK))
      have hz0 : β₀ (rSum14 i) = 0 := by simpa using hInv0.2 i
      rw [hin14 i, htb_false, hz0]
      rfl
    · exact hout14 z hz14
  · have hjLt := j.isLt
    have hrj : rSliceK j = rSum14 ⟨j.val, by omega⟩ := by
      rw [QRegister.slice_apply]; congr 1; ext; simp
    have hz0 : β₀ (rSum14 ⟨j.val, by omega⟩) = 0 := by simpa using hInv0.2 ⟨j.val, by omega⟩
    rw [hrj, hin14 ⟨j.val, by omega⟩, hz0, zero_add]
/-- Core bit value at axis `w`, plane `r`, electron `e`. -/
def corePlaneBitVal {mPayload : ℕ} (w : Fin 3) (r : Fin 6)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (e : Fin numElectrons) : ℕ :=
  (γ (elecAxisBitWire w r e)).val
/-- Flexible 3-plane chunk wire map on `fullSysCoreWires mPayload` supporting `pBase ∈ {0..5}`
whenever out-of-range planes have count `0`. -/
def flexCoreChunkWire {mPayload : ℕ} (w : Fin 3) (pBase : ℕ)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ)
    (hp₀ : 0 < B₀ → pBase < 6)
    (hp₁ : 0 < B₁ → pBase + 1 < 6)
    (hp₂ : 0 < B₂ → pBase + 2 < 6)
    (he₀ : eOff₀ + B₀ ≤ 218) (he₁ : eOff₁ + B₁ ≤ 218) (he₂ : eOff₂ + B₂ ≤ 218)
    (u : Fin (B₀ + B₁ + B₂)) :
    Wire (fullSysCoreWires mPayload) :=
  if h1 : u.val < B₀ then
    elecAxisBitWire w ⟨pBase, hp₀ (by omega)⟩
      ⟨eOff₀ + u.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
  else if h2 : u.val < B₀ + B₁ then
    elecAxisBitWire w ⟨pBase + 1, hp₁ (by omega)⟩
      ⟨eOff₁ + (u.val - B₀), by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
  else
    elecAxisBitWire w ⟨pBase + 2, hp₂ (by have := u.isLt; omega)⟩
      ⟨eOff₂ + (u.val - (B₀ + B₁)), by
        have :=
          u.isLt; dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
theorem flexCoreChunkWire_injective {mPayload : ℕ} (w : Fin 3) (pBase : ℕ)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ)
    (hp₀ : 0 < B₀ → pBase < 6)
    (hp₁ : 0 < B₁ → pBase + 1 < 6)
    (hp₂ : 0 < B₂ → pBase + 2 < 6)
    (he₀ : eOff₀ + B₀ ≤ 218) (he₁ : eOff₁ + B₁ ≤ 218) (he₂ : eOff₂ + B₂ ≤ 218) :
    Function.Injective
      (flexCoreChunkWire (mPayload := mPayload) w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂
        hp₀ hp₁ hp₂ he₀ he₁ he₂) := by
  intro u₁ u₂ h
  have hu₁ := u₁.isLt; have hu₂ := u₂.isLt
  have hv := congrArg Fin.val h
  dsimp only [flexCoreChunkWire] at hv
  split_ifs at hv <;> {
    simp only [elecAxisBitWire_val] at hv
    exact Fin.ext (by omega)
  }
theorem sum_fin218_zero_offset (f : Fin numElectrons → ℕ) :
    (∑ e : Fin numElectrons, f e) =
      ∑ i : Fin 218, f ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩ := by
  let eqv : Fin 218 ≃ Fin numElectrons := finCongr rfl
  rw [← Equiv.sum_comp eqv]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [eqv]))
theorem sum_fin218_interval_split (off a b ab : ℕ) (hab : a + b = ab) (hbound : off + ab ≤ 218)
    (f : Fin numElectrons → ℕ) :
    (∑ i : Fin ab, f ⟨off + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) =
      (∑ i : Fin a, f ⟨off + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin b, f ⟨(off + a) + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) := by
  subst hab
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext rfl)
  · exact Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by dsimp; omega))
/-- Opaque slice sum of `cnt` electron bits starting at `off` on axis `w`, plane `r` (`N = 218`). -/
def corePlaneSliceSum {mPayload : ℕ} (w : Fin 3) (r : ℕ)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (off cnt : ℕ) : ℕ :=
  if hr : r < 6 then
    if hb : off + cnt ≤ 218 then
      ∑ i : Fin cnt, corePlaneBitVal w ⟨r, hr⟩ γ
        ⟨off + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
    else 0
  else 0
theorem corePlaneSliceSum_zero {mPayload : ℕ} (w : Fin 3) (r : ℕ)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (off : ℕ) :
    corePlaneSliceSum w r γ off 0 = 0 := by
  unfold corePlaneSliceSum; split_ifs <;> simp
theorem corePlaneSliceSum_split {mPayload : ℕ} (w : Fin 3) (r : ℕ)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (off a b ab oab : ℕ)
    (hab : a + b = ab) (hoab : off + a = oab) (hbound : off + ab ≤ 218) :
    corePlaneSliceSum w r γ off ab =
      corePlaneSliceSum w r γ off a + corePlaneSliceSum w r γ oab b := by
  subst hoab
  unfold corePlaneSliceSum
  by_cases hr : r < 6
  · have hb1 : off + a ≤ 218 := by omega
    have hb2 : (off + a) + b ≤ 218 := by omega
    simp only [hr, hbound, hb1, hb2, ↓reduceDIte]
    exact sum_fin218_interval_split off a b ab hab hbound (corePlaneBitVal w ⟨r, hr⟩ γ)
  · simp [hr]
theorem weightedGenBatchVal_flexCoreChunk {mPayload : ℕ} (w : Fin 3)
    (pBase p1 p2 : ℕ) (hp1_eq : pBase + 1 = p1) (hp2_eq : pBase + 2 = p2)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ)
    (hp₀ : 0 < B₀ → pBase < 6)
    (hp₁ : 0 < B₁ → pBase + 1 < 6)
    (hp₂ : 0 < B₂ → pBase + 2 < 6)
    (he₀ : eOff₀ + B₀ ≤ 218) (he₁ : eOff₁ + B₁ ≤ 218) (he₂ : eOff₂ + B₂ ≤ 218)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    weightedGenBatchVal
        (flexCoreChunkWire (mPayload := mPayload) w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂
          hp₀ hp₁ hp₂ he₀ he₁ he₂) γ =
      corePlaneSliceSum w pBase γ eOff₀ B₀ +
      2 * corePlaneSliceSum w p1 γ eOff₁ B₁ +
      4 * corePlaneSliceSum w p2 γ eOff₂ B₂ := by
  subst hp1_eq; subst hp2_eq
  unfold weightedGenBatchVal corePlaneSliceSum
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · by_cases hB : B₀ = 0
    · subst hB; split_ifs <;> simp
    · have h0 : pBase < 6 := hp₀ (Nat.pos_of_ne_zero hB)
      simp only [h0, he₀, ↓reduceDIte]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := i.isLt
      dsimp [flexCoreChunkWire, corePlaneBitVal]
      simp only [hi, ↓reduceDIte]
  · by_cases hB : B₁ = 0
    · subst hB; split_ifs <;> simp
    · have h1 : pBase + 1 < 6 := hp₁ (Nat.pos_of_ne_zero hB)
      simp only [h1, he₁, ↓reduceDIte, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := i.isLt
      have hWire : flexCoreChunkWire (mPayload := mPayload) w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂
          hp₀ hp₁ hp₂ he₀ he₁ he₂ ⟨B₀ + i.val, by omega⟩ =
          elecAxisBitWire w ⟨pBase + 1, h1⟩
            ⟨eOff₁ + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩ := by
        dsimp [flexCoreChunkWire]
        split_ifs <;> first | omega | (congr 1; ext; dsimp; omega)
      rw [hWire]; rfl
  · by_cases hB : B₂ = 0
    · subst hB; split_ifs <;> simp
    · have h2 : pBase + 2 < 6 := hp₂ (Nat.pos_of_ne_zero hB)
      simp only [h2, he₂, ↓reduceDIte, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := i.isLt
      have hWire : flexCoreChunkWire (mPayload := mPayload) w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂
          hp₀ hp₁ hp₂ he₀ he₁ he₂ ⟨(B₀ + B₁) + i.val, by omega⟩ =
          elecAxisBitWire w ⟨pBase + 2, h2⟩
            ⟨eOff₂ + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩ := by
        dsimp [flexCoreChunkWire]
        split_ifs <;> first | omega | (congr 1; ext; dsimp; omega)
      rw [hWire]; rfl
attribute [irreducible] flexCoreChunkWire
theorem slot2AxisSum_eq_bitPlane_sum_core {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    slot2AxisSum w γ =
      corePlaneSliceSum w 0 γ 0 218 +
      2 * corePlaneSliceSum w 1 γ 0 218 +
      4 * corePlaneSliceSum w 2 γ 0 218 +
      8 * corePlaneSliceSum w 3 γ 0 218 +
      16 * corePlaneSliceSum w 4 γ 0 218 +
      32 * corePlaneSliceSum w 5 γ 0 218 := by
  have f0 : (⟨0, by decide⟩ : Fin 6) = 0 := rfl
  have f1 : (⟨1, by decide⟩ : Fin 6) = 1 := rfl
  have f2 : (⟨2, by decide⟩ : Fin 6) = 2 := rfl
  have f3 : (⟨3, by decide⟩ : Fin 6) = 3 := rfl
  have f4 : (⟨4, by decide⟩ : Fin 6) = 4 := rfl
  have f5 : (⟨5, by decide⟩ : Fin 6) = 5 := rfl
  unfold corePlaneSliceSum
  simp only [show (0 < 6) from by decide, show (1 < 6) from by decide,
    show (2 < 6) from by decide, show (3 < 6) from by decide,
    show (4 < 6) from by decide, show (5 < 6) from by decide,
    show (0 + 218 ≤ 218) from by decide, ↓reduceDIte]
  rw [← sum_fin218_zero_offset, ← sum_fin218_zero_offset, ← sum_fin218_zero_offset,
      ← sum_fin218_zero_offset, ← sum_fin218_zero_offset, ← sum_fin218_zero_offset]
  rw [f0, f1, f2, f3, f4, f5, slot2AxisSum_eq_bitPlane_sum w γ, Fin.sum_univ_six]
  dsimp only [corePlaneBitVal]
  simp only [
    show (0 : Fin 6).val = 0 from rfl,
    show (1 : Fin 6).val = 1 from rfl,
    show (2 : Fin 6).val = 2 from rfl,
    show (3 : Fin 6).val = 3 from rfl,
    show (4 : Fin 6).val = 4 from rfl,
    show (5 : Fin 6).val = 5 from rfl]
  ring
attribute [irreducible] corePlaneSliceSum
/-- Balanced binary tree over `ℕ` accelerating `runWeightList` kernel checks from `O(S * M^2)`
unary Peano reduction to `O(S * log₂ M)` binary `Nat.blt` updates. -/
inductive WTree : Type
  | empty : WTree
  | leaf : ℕ → WTree
  | node : ℕ → WTree → WTree → WTree
/-- Flatten `WTree` into the represented `List ℕ`. -/
def WTree.toList : WTree → List ℕ
  | .empty => []
  | .leaf v => [v]
  | .node _ l r => l.toList ++ r.toList
/-- Well-formedness invariant recording exact left-subtree sizes. -/
def WTree.wf : WTree → Prop
  | .empty => True
  | .leaf _ => True
  | .node m l r => l.toList.length = m ∧ l.wf ∧ r.wf
/-- Linear fallback `WTree` builder (structurally recursive on `List ℕ`). -/
def WTree.ofListLinear : List ℕ → WTree
  | [] => .empty
  | [x] => .leaf x
  | x :: y :: ys => .node 1 (.leaf x) (WTree.ofListLinear (y :: ys))
theorem WTree.toList_ofListLinear : ∀ (L : List ℕ), (WTree.ofListLinear L).toList = L
  | [] => rfl
  | [_] => rfl
  | x :: y :: ys => by
      dsimp only [WTree.ofListLinear, WTree.toList]
      rw [WTree.toList_ofListLinear (y :: ys)]
      rfl
theorem WTree.wf_ofListLinear : ∀ (L : List ℕ), (WTree.ofListLinear L).wf
  | [] => trivial
  | [_] => trivial
  | _ :: y :: ys => ⟨rfl, trivial, WTree.wf_ofListLinear (y :: ys)⟩
/-- Build a balanced `WTree` of depth at most `d` from `L` (structurally recursive on `d : ℕ`). -/
def WTree.build : ℕ → List ℕ → WTree
  | 0, L => WTree.ofListLinear L
  | d + 1, L =>
      match L with
      | [] => .empty
      | [x] => .leaf x
      | _ :: _ :: _ =>
          let m := L.length / 2
          .node m (WTree.build d (L.take m)) (WTree.build d (L.drop m))
theorem WTree.toList_build : ∀ (d : ℕ) (L : List ℕ), (WTree.build d L).toList = L
  | 0, L => WTree.toList_ofListLinear L
  | d + 1, [] => rfl
  | d + 1, [_] => rfl
  | d + 1, x :: y :: ys => by
      dsimp only [WTree.build, WTree.toList]
      rw [WTree.toList_build d, WTree.toList_build d, List.take_append_drop]
theorem WTree.wf_build : ∀ (d : ℕ) (L : List ℕ), (WTree.build d L).wf
  | 0, L => WTree.wf_ofListLinear L
  | d + 1, [] => trivial
  | d + 1, [_] => trivial
  | d + 1, x :: y :: ys => by
      dsimp only [WTree.build, WTree.wf]
      refine ⟨?_, WTree.wf_build d _, WTree.wf_build d _⟩
      rw [WTree.toList_build, List.length_take]
      exact Nat.min_eq_left (Nat.div_le_self _ _)
/-- Fast binary `O(log₂ M)` read on `WTree`. -/
def WTree.get : WTree → ℕ → ℕ
  | .empty, _ => 0
  | .leaf v, i => if Nat.beq i 0 then v else 0
  | .node m l r, i => if Nat.blt i m then l.get i else r.get (i - m)
/-- Fast binary `O(log₂ M)` point update on `WTree`. -/
def WTree.set : WTree → ℕ → ℕ → WTree
  | .empty, _, _ => .empty
  | .leaf v, i, w => if Nat.beq i 0 then .leaf w else .leaf v
  | .node m l r, i, w =>
      if Nat.blt i m then .node m (l.set i w) r else .node m l (r.set (i - m) w)
theorem listSet_append : ∀ (A B : List ℕ) (i w : ℕ),
    listSet (A ++ B) i w =
      if i < A.length then listSet A i w ++ B else A ++ listSet B (i - A.length) w
  | [], B, i, w => by simp
  | a :: as, B, 0, w => by simp [listSet]
  | a :: as, B, i + 1, w => by
      simp only [List.cons_append, listSet, List.length_cons, Nat.succ_lt_succ_iff,
        Nat.succ_sub_succ_eq_sub]
      rw [listSet_append as B i w]
      split_ifs <;> rfl
theorem WTree.get_eq_listGet : ∀ {t : WTree}, t.wf → ∀ i : ℕ, t.get i = listGet t.toList i
  | .empty, _, _ => rfl
  | .leaf _, _, 0 => rfl
  | .leaf _, _, _ + 1 => rfl
  | .node m l r, ⟨hm, hl, hr⟩, i => by
      dsimp only [WTree.get, WTree.toList]
      rw [listGet_append, hm, WTree.get_eq_listGet hl, WTree.get_eq_listGet hr]
      cases h : Nat.blt i m
      · have hge : ¬ i < m := fun hlt ↦ by rw [Nat.blt_eq.mpr hlt] at h; cases h
        simp [hge]
      · have hlt : i < m := Nat.blt_eq.mp h
        simp [hlt]
theorem WTree.set_spec : ∀ {t : WTree}, t.wf → ∀ i w : ℕ,
    (t.set i w).toList = listSet t.toList i w ∧ (t.set i w).wf
  | .empty, _, _, _ => ⟨rfl, trivial⟩
  | .leaf _, _, 0, _ => ⟨rfl, trivial⟩
  | .leaf _, _, _ + 1, _ => ⟨rfl, trivial⟩
  | .node m l r, ⟨hm, hl, hr⟩, i, w => by
      dsimp only [WTree.set]
      cases h : Nat.blt i m
      · have hge : ¬ i < m := fun hlt ↦ by rw [Nat.blt_eq.mpr hlt] at h; cases h
        obtain ⟨hrL, hrW⟩ := WTree.set_spec hr (i - m) w
        simp only [Bool.false_eq_true, ↓reduceIte, WTree.toList, WTree.wf]
        rw [listSet_append, hm, ite_eq_right hge, hrL]
        exact ⟨rfl, rfl, hl, hrW⟩
      · have hlt : i < m := Nat.blt_eq.mp h
        obtain ⟨hlL, hlW⟩ := WTree.set_spec hl i w
        simp only [↓reduceIte, WTree.toList, WTree.wf]
        rw [listSet_append, hm, ite_eq_left hlt, hlL]
        exact ⟨rfl, (listSet_length l.toList i w).trans hm, hlW, hr⟩
/-- Fast single-step weight transition on `WTree`. -/
def stepWTree (cur : ℕ) (t : WTree) : InPlaceStep → Option WTree
  | .fa a b c =>
      let wa := t.get a
      if (t.get cur == 0) && decide (wa > 0) && (t.get b == wa) && (t.get c == wa) then
        some ((((t.set a 0).set c 0).set b wa).set cur (2 * wa))
      else none
  | .ha a b =>
      let wa := t.get a
      if (t.get cur == 0) && decide (wa > 0) && (t.get b == wa) then
        some (((t.set a 0).set b wa).set cur (2 * wa))
      else none
theorem stepWTree_spec {t : WTree} (hwf : t.wf) (cur : ℕ) (s : InPlaceStep) :
    match stepWTree cur t s with
    | none => stepWeightList cur t.toList s = none
    | some t' => stepWeightList cur t.toList s = some t'.toList ∧ t'.wf := by
  cases s with
  | fa a b c =>
      dsimp only [stepWTree, stepWeightList]
      rw [WTree.get_eq_listGet hwf a, WTree.get_eq_listGet hwf cur,
          WTree.get_eq_listGet hwf b, WTree.get_eq_listGet hwf c]
      split_ifs with hc
      · obtain ⟨h1, wf1⟩ := WTree.set_spec hwf a 0
        obtain ⟨h2, wf2⟩ := WTree.set_spec wf1 c 0
        obtain ⟨h3, wf3⟩ := WTree.set_spec wf2 b (listGet t.toList a)
        obtain ⟨h4, wf4⟩ := WTree.set_spec wf3 cur (2 * listGet t.toList a)
        refine ⟨?_, wf4⟩
        rw [h4, h3, h2, h1]
      · rfl
  | ha a b =>
      dsimp only [stepWTree, stepWeightList]
      rw [WTree.get_eq_listGet hwf a, WTree.get_eq_listGet hwf cur,
          WTree.get_eq_listGet hwf b]
      split_ifs with hc
      · obtain ⟨h1, wf1⟩ := WTree.set_spec hwf a 0
        obtain ⟨h2, wf2⟩ := WTree.set_spec wf1 b (listGet t.toList a)
        obtain ⟨h3, wf3⟩ := WTree.set_spec wf2 cur (2 * listGet t.toList a)
        refine ⟨?_, wf3⟩
        rw [h3, h2, h1]
      · rfl
/-- Fast multi-step weight transition on `WTree` with zero `forceList` overhead. -/
def runWTree : ℕ → List InPlaceStep → WTree → Option WTree
  | _, [], t => some t
  | cur, s :: rest, t =>
      match stepWTree cur t s with
      | none => none
      | some t' => runWTree (cur + 1) rest t'
theorem runWTree_spec : ∀ (cur : ℕ) (steps : List InPlaceStep) {t : WTree}, t.wf →
    match runWTree cur steps t with
    | none => runWeightList cur steps t.toList = none
    | some t' => runWeightList cur steps t.toList = some t'.toList
  | _, [], _, _ => rfl
  | cur, s :: rest, t, hwf => by
      dsimp only [runWTree, runWeightList]
      have hst := stepWTree_spec hwf cur s
      cases hs : stepWTree cur t s with
      | none =>
          rw [hs] at hst
          rw [hst]
      | some t' =>
          rw [hs] at hst
          rw [hst.1]
          dsimp only
          rw [match_forceList_apply (runWeightList (cur + 1) rest) t'.toList]
          exact runWTree_spec (cur + 1) rest hst.2
/-- Fast binary `List ℕ` equality check avoiding polymorphic `BEq` overhead. -/
def listBeqNat : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && listBeqNat xs ys
  | _, _ => false
theorem listBeqNat_eq_true : ∀ {L₁ L₂ : List ℕ}, listBeqNat L₁ L₂ = true → L₁ = L₂
  | [], [], _ => rfl
  | _ :: _, [], h => by cases h
  | [], _ :: _, h => by cases h
  | x :: xs, y :: ys, h => by
      simp only [listBeqNat, Bool.and_eq_true, Nat.beq_eq] at h
      rw [h.1, listBeqNat_eq_true h.2]
/-- Fast `O(S * log₂ M)` boolean certificate for `WeightedCsa3GenSpec.hRun`. -/
def checkCsaTree (B₀ B₁ B₂ S : ℕ) (steps : List InPlaceStep) (expOut : List ℕ) : Bool :=
  match runWTree (B₀ + B₁ + B₂) steps (WTree.build 9 (init3PlaneGenWeights B₀ B₁ B₂ S)) with
  | none => false
  | some tOut => listBeqNat tOut.toList expOut
theorem runWeightList_of_checkCsaTree (B₀ B₁ B₂ S : ℕ) (steps : List InPlaceStep) (expOut : List ℕ)
    (h : checkCsaTree B₀ B₁ B₂ S steps expOut = true) :
    runWeightList (B₀ + B₁ + B₂) steps (init3PlaneGenWeights B₀ B₁ B₂ S) = some expOut := by
  dsimp only [checkCsaTree] at h
  have hr := runWTree_spec (B₀ + B₁ + B₂) steps
    (WTree.wf_build 9 (init3PlaneGenWeights B₀ B₁ B₂ S))
  rw [WTree.toList_build] at hr
  cases hm : runWTree (B₀ + B₁ + B₂) steps (WTree.build 9 (init3PlaneGenWeights B₀ B₁ B₂ S)) with
  | none => rw [hm] at h; cases h
  | some tOut =>
      rw [hm] at h hr
      rw [hr, listBeqNat_eq_true h]
/-!
## Section 2A: Deduplicated Verified 3-Plane CSA Batch Schedules (`wcsa00 .. wcsa31`)
-/
/-- CSA step list for `wcsa00`. -/
def wcsa00Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38, .fa 39 40 41,
  .fa 42 43 44, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62,
  .fa 1 4 7, .fa 10 13 16, .fa 19 22 25, .fa 28 31 34] : List InPlaceStep) ++ (([.fa 37 40 43,
  .fa 46 49 52, .fa 55 58 61, .fa 4 13 22, .fa 31 40 49, .fa 58 13 40, .fa 63 64 65, .fa 66 67 68,
  .fa 69 70 71, .fa 72 73 74, .fa 75 76 77, .fa 78 79 80, .fa 81 82 83, .fa 84 85 86, .fa 87 88 89,
  .fa 90 91 92, .fa 93 64 67, .fa 70 73 76, .fa 79 82 85, .fa 88 91 64, .fa 73 82 91, .fa 94 95 96,
  .fa 97 98 99, .fa 100 101 102, .fa 103 104 105] : List InPlaceStep) ++ ([.fa 106 107 108,
  .fa 95 98 101, .fa 104 107 98, .fa 109 110 111, .fa 112 113 114, .fa 115 110 113,
  .fa 116 117 118] : List InPlaceStep)))
/-- Output wire map for `wcsa00`. -/
def wcsa00OutWires : Fin 6 → Wire 120
  | 0 => ⟨13, by decide⟩
  | 1 => ⟨82, by decide⟩
  | 2 => ⟨107, by decide⟩
  | 3 => ⟨110, by decide⟩
  | 4 => ⟨117, by decide⟩
  | 5 => ⟨119, by decide⟩
theorem wcsa00OutWires_injective : Function.Injective wcsa00OutWires := by
  intro i j h; revert i j h; decide
/-- Verified 3-plane CSA schedule `wcsa00`. -/
def wcsa00Spec : WeightedCsa3GenSpec 63 0 0 6 57 where
  steps := wcsa00Steps
  outWires := wcsa00OutWires
  cinWire := none
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa00OutWires_injective
  hCinNe := fun _ _ hcw ↦ by cases hcw
  hRun :=
    runWeightList_of_checkCsaTree 63 0 0 57 wcsa00Steps (expectedOutWeightsCin wcsa00OutWires none)
    rfl
theorem wcsa00Spec_cinWire : wcsa00Spec.cinWire = none := rfl
attribute [irreducible] wcsa00Steps wcsa00Spec
/-- CSA step list for `wcsa01`. -/
def wcsa01Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38, .fa 39 40 41,
  .fa 42 43 44, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62,
  .fa 63 1 4, .fa 7 10 13, .fa 16 19 22, .fa 25 28 31] : List InPlaceStep) ++ (([.fa 34 37 40,
  .fa 43 46 49, .fa 52 55 58, .fa 61 1 10, .fa 19 28 37, .fa 46 55 1, .fa 64 65 66, .fa 67 68 69,
  .fa 70 71 72, .fa 73 74 75, .fa 76 77 78, .fa 79 80 81, .fa 82 83 84, .fa 85 86 87, .fa 88 89 90,
  .fa 91 92 93, .fa 94 65 68, .fa 71 74 77, .fa 80 83 86, .fa 89 92 65, .fa 74 83 92, .fa 95 96 97,
  .fa 98 99 100, .fa 101 102 103, .fa 104 105 106] : List InPlaceStep) ++ ([.fa 107 108 109,
  .fa 96 99 102, .fa 105 108 99, .fa 110 111 112, .fa 113 114 115, .fa 116 111 114,
  .fa 117 118 119] : List InPlaceStep)))
/-- Output wire map for `wcsa01`. -/
def wcsa01OutWires : Fin 6 → Wire 121
  | 0 => ⟨55, by decide⟩
  | 1 => ⟨83, by decide⟩
  | 2 => ⟨108, by decide⟩
  | 3 => ⟨111, by decide⟩
  | 4 => ⟨118, by decide⟩
  | 5 => ⟨120, by decide⟩
theorem wcsa01OutWires_injective : Function.Injective wcsa01OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa01`. -/
def wcsa01CinWire : Wire 121 := ⟨28, by decide⟩
theorem wcsa01CinWire_ne_out (k : Fin 6) : wcsa01CinWire ≠ wcsa01OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa01`. -/
def wcsa01Spec : WeightedCsa3GenSpec 64 0 0 6 57 where
  steps := wcsa01Steps
  outWires := wcsa01OutWires
  cinWire := (some wcsa01CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa01OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa01CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 64 0 0 57 wcsa01Steps (expectedOutWeightsCin wcsa01OutWires (some
    wcsa01CinWire)) rfl
attribute [irreducible] wcsa01Steps wcsa01Spec
/-- CSA step list for `wcsa02`. -/
def wcsa02Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38, .fa 39 40 41,
  .fa 42 43 44, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62,
  .fa 63 64 65, .fa 66 67 68, .fa 69 70 71, .fa 72 73 74] : List InPlaceStep) ++ (([.fa 75 76 77,
  .fa 78 79 80, .fa 81 82 83, .fa 84 85 86, .fa 87 88 89, .fa 1 4 7, .fa 10 13 16, .fa 19 22 25,
  .fa 28 31 34, .fa 37 40 43, .fa 46 49 52, .fa 55 58 61, .fa 64 67 70, .fa 73 76 79, .fa 82 85 88,
  .fa 4 13 22, .fa 31 40 49, .fa 58 67 76, .fa 85 13 40, .fa 90 91 92, .fa 93 94 95, .fa 96 97 98,
  .fa 99 100 101, .fa 102 103 104, .fa 105 106 107] : List InPlaceStep) ++ (([.fa 108 109 110,
  .fa 111 112 113, .fa 114 115 116, .fa 117 118 119, .fa 120 121 122, .fa 123 124 125,
  .fa 126 127 128, .fa 129 130 131, .fa 132 133 134, .fa 135 136 137, .fa 138 139 140,
  .fa 141 142 143, .fa 144 145 146, .fa 147 148 149, .fa 150 151 152, .fa 91 94 97, .fa 100 103 106,
  .fa 109 112 115, .fa 118 121 124, .fa 127 130 133, .fa 136 139 142, .fa 145 148 151,
  .fa 94 103 112, .fa 121 130 139, .fa 148 103 130] : List InPlaceStep) ++ (([.fa 153 154 155,
  .fa 156 157 158, .fa 159 160 161, .fa 162 163 164, .fa 165 166 167, .fa 168 169 170,
  .fa 171 172 173, .fa 174 175 176, .fa 177 178 179, .fa 180 181 182, .fa 183 154 157,
  .fa 160 163 166, .fa 169 172 175, .fa 178 181 154, .fa 163 172 181, .fa 184 185 186,
  .fa 187 188 189, .fa 190 191 192, .fa 193 194 195, .fa 196 197 198, .fa 185 188 191,
  .fa 194 197 188, .fa 199 200 201, .fa 202 203 204,
  .fa 205 200 203] : List InPlaceStep) ++ ([.fa 206 207 208] : List InPlaceStep)))))
/-- Output wire map for `wcsa02`. -/
def wcsa02OutWires : Fin 7 → Wire 210
  | 0 => ⟨13, by decide⟩
  | 1 => ⟨103, by decide⟩
  | 2 => ⟨172, by decide⟩
  | 3 => ⟨197, by decide⟩
  | 4 => ⟨200, by decide⟩
  | 5 => ⟨207, by decide⟩
  | 6 => ⟨209, by decide⟩
theorem wcsa02OutWires_injective : Function.Injective wcsa02OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa02`. -/
def wcsa02CinWire : Wire 210 := ⟨67, by decide⟩
theorem wcsa02CinWire_ne_out (k : Fin 7) : wcsa02CinWire ≠ wcsa02OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa02`. -/
def wcsa02Spec : WeightedCsa3GenSpec 90 19 0 7 101 where
  steps := wcsa02Steps
  outWires := wcsa02OutWires
  cinWire := (some wcsa02CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa02OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa02CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 90 19 0 101 wcsa02Steps (expectedOutWeightsCin wcsa02OutWires
    (some wcsa02CinWire)) rfl
attribute [irreducible] wcsa02Steps wcsa02Spec
/-- CSA step list for `wcsa03`. -/
def wcsa03Steps : List InPlaceStep :=
  (([.fa 1 2 3, .fa 4 5 6, .fa 7 8 9, .fa 10 11 12, .fa 13 14 15, .fa 16 17 18, .fa 19 20 21,
  .fa 22 23 24, .fa 25 26 27, .fa 28 29 30, .fa 31 32 33, .fa 34 35 36, .fa 37 38 39, .fa 40 41 42,
  .fa 43 44 45, .fa 46 47 48, .fa 49 50 51, .fa 52 53 54, .fa 55 56 57, .fa 58 59 60, .fa 61 62 63,
  .fa 64 65 66, .fa 67 68 69, .fa 70 71 72, .fa 73 74 75] : List InPlaceStep) ++ (([.fa 76 77 78,
  .fa 79 80 81, .fa 82 83 84, .fa 85 86 87, .fa 88 89 90, .fa 91 92 93, .fa 94 95 96, .fa 97 98 99,
  .fa 100 101 102, .fa 103 104 105, .fa 106 107 108, .fa 109 110 111, .fa 112 113 114,
  .fa 115 116 117, .fa 118 119 120, .fa 121 122 123, .fa 124 125 126, .fa 127 2 5, .fa 8 11 14,
  .fa 17 20 23, .fa 26 29 32, .fa 35 38 41, .fa 44 47 50, .fa 53 56 59,
  .fa 62 65 68] : List InPlaceStep) ++ (([.fa 71 74 77, .fa 80 83 86, .fa 89 92 95, .fa 98 101 104,
  .fa 107 110 113, .fa 116 119 122, .fa 125 2 11, .fa 20 29 38, .fa 47 56 65, .fa 74 83 92,
  .fa 101 110 119, .fa 2 29 56, .fa 83 110 29, .fa 128 129 130, .fa 131 132 133, .fa 134 135 136,
  .fa 137 138 139, .fa 140 141 142, .fa 143 144 145, .fa 146 147 148, .fa 149 150 151,
  .fa 152 153 154, .fa 155 156 157, .fa 158 159 160,
  .fa 161 162 163] : List InPlaceStep) ++ (([.fa 164 165 166, .fa 167 168 169, .fa 170 171 172,
  .fa 173 174 175, .fa 176 177 178, .fa 179 180 181, .fa 182 183 184, .fa 185 186 187,
  .fa 188 189 190, .fa 129 132 135, .fa 138 141 144, .fa 147 150 153, .fa 156 159 162,
  .fa 165 168 171, .fa 174 177 180, .fa 183 186 189, .fa 132 141 150, .fa 159 168 177,
  .fa 186 141 168, .fa 191 192 193, .fa 194 195 196, .fa 197 198 199, .fa 200 201 202,
  .fa 203 204 205, .fa 206 207 208] : List InPlaceStep) ++ ([.fa 209 210 211, .fa 212 213 214,
  .fa 215 216 217, .fa 218 219 220, .fa 221 192 195, .fa 198 201 204, .fa 207 210 213,
  .fa 216 219 192, .fa 201 210 219, .fa 222 223 224, .fa 225 226 227, .fa 228 229 230,
  .fa 231 232 233, .fa 234 235 236, .fa 223 226 229, .fa 232 235 226, .fa 237 238 239,
  .fa 240 241 242, .fa 243 238 241, .fa 244 245 246] : List InPlaceStep)))))
/-- Output wire map for `wcsa03`. -/
def wcsa03OutWires : Fin 8 → Wire 248
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨110, by decide⟩
  | 2 => ⟨141, by decide⟩
  | 3 => ⟨210, by decide⟩
  | 4 => ⟨235, by decide⟩
  | 5 => ⟨238, by decide⟩
  | 6 => ⟨245, by decide⟩
  | 7 => ⟨247, by decide⟩
theorem wcsa03OutWires_injective : Function.Injective wcsa03OutWires := by
  intro i j h; revert i j h; decide
/-- Verified 3-plane CSA schedule `wcsa03`. -/
def wcsa03Spec : WeightedCsa3GenSpec 1 127 0 8 120 where
  steps := wcsa03Steps
  outWires := wcsa03OutWires
  cinWire := none
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa03OutWires_injective
  hCinNe := fun _ _ hcw ↦ by cases hcw
  hRun :=
    runWeightList_of_checkCsaTree 1 127 0 120 wcsa03Steps (expectedOutWeightsCin wcsa03OutWires
    none) rfl
attribute [irreducible] wcsa03Steps wcsa03Spec
/-- CSA step list for `wcsa04`. -/
def wcsa04Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 1, .fa 4 7 10,
  .fa 13 16 19, .fa 22 25 28, .fa 31 34 37, .fa 7 16 25, .fa 38 39 40, .fa 41 42 43, .fa 44 45 46,
  .fa 47 48 49, .fa 50 51 52, .fa 53 54 55, .fa 56 57 58] : List InPlaceStep) ++ (([.fa 59 60 61,
  .fa 62 63 64, .fa 65 66 67, .fa 68 69 70, .fa 71 72 73, .fa 74 75 76, .fa 77 78 79, .fa 80 81 82,
  .fa 83 84 85, .fa 86 87 88, .fa 89 90 91, .fa 92 93 94, .fa 95 96 97, .fa 98 99 100,
  .fa 101 102 103, .fa 104 105 106, .fa 107 108 109, .fa 110 111 112, .fa 113 114 115,
  .fa 116 117 118, .fa 119 120 121, .fa 122 123 124, .fa 125 126 127, .fa 128 129 130,
  .fa 131 132 133] : List InPlaceStep) ++ (([.fa 134 135 136, .fa 137 138 139, .fa 140 141 142,
  .fa 143 144 145, .fa 146 147 148, .fa 149 150 151, .fa 152 153 154, .fa 155 156 157,
  .fa 158 159 160, .fa 161 162 163, .fa 164 39 42, .fa 45 48 51, .fa 54 57 60, .fa 63 66 69,
  .fa 72 75 78, .fa 81 84 87, .fa 90 93 96, .fa 99 102 105, .fa 108 111 114, .fa 117 120 123,
  .fa 126 129 132, .fa 135 138 141, .fa 144 147 150, .fa 153 156 159,
  .fa 162 39 48] : List InPlaceStep) ++ (([.fa 57 66 75, .fa 84 93 102, .fa 111 120 129,
  .fa 138 147 156, .fa 39 66 93, .fa 120 147 66, .fa 165 166 167, .fa 168 169 170, .fa 171 172 173,
  .fa 174 175 176, .fa 177 178 179, .fa 180 181 182, .fa 183 184 185, .fa 186 187 188,
  .fa 189 190 191, .fa 192 193 194, .fa 195 196 197, .fa 198 199 200, .fa 201 202 203,
  .fa 204 205 206, .fa 207 208 209, .fa 210 211 212, .fa 213 214 215, .fa 216 217 218,
  .fa 219 220 221] : List InPlaceStep) ++ (([.fa 222 223 224, .fa 225 226 227, .fa 166 169 172,
  .fa 175 178 181, .fa 184 187 190, .fa 193 196 199, .fa 202 205 208, .fa 211 214 217,
  .fa 220 223 226, .fa 169 178 187, .fa 196 205 214, .fa 223 178 205, .fa 228 229 230,
  .fa 231 232 233, .fa 234 235 236, .fa 237 238 239, .fa 240 241 242, .fa 243 244 245,
  .fa 246 247 248, .fa 249 250 251, .fa 252 253 254, .fa 255 256 257, .fa 258 229 232,
  .fa 235 238 241, .fa 244 247 250] : List InPlaceStep) ++ ([.fa 253 256 229, .fa 238 247 256,
  .fa 259 260 261, .fa 262 263 264, .fa 265 266 267, .fa 268 269 270, .fa 271 272 273,
  .fa 260 263 266, .fa 269 272 263, .fa 274 275 276, .fa 277 278 279, .fa 280 275 278,
  .fa 281 282 283] : List InPlaceStep))))))
/-- Output wire map for `wcsa04`. -/
def wcsa04OutWires : Fin 8 → Wire 285
  | 0 => ⟨16, by decide⟩
  | 1 => ⟨147, by decide⟩
  | 2 => ⟨178, by decide⟩
  | 3 => ⟨247, by decide⟩
  | 4 => ⟨272, by decide⟩
  | 5 => ⟨275, by decide⟩
  | 6 => ⟨282, by decide⟩
  | 7 => ⟨284, by decide⟩
theorem wcsa04OutWires_injective : Function.Injective wcsa04OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa04`. -/
def wcsa04CinWire : Wire 285 := ⟨34, by decide⟩
theorem wcsa04CinWire_ne_out (k : Fin 8) : wcsa04CinWire ≠ wcsa04OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa04`. -/
def wcsa04Spec : WeightedCsa3GenSpec 38 109 0 8 138 where
  steps := wcsa04Steps
  outWires := wcsa04OutWires
  cinWire := (some wcsa04CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa04OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa04CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 38 109 0 138 wcsa04Steps (expectedOutWeightsCin wcsa04OutWires
    (some wcsa04CinWire)) rfl
attribute [irreducible] wcsa04Steps wcsa04Spec
/-- CSA step list for `wcsa05`. -/
def wcsa05Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 1 4, .fa 7 10 13, .fa 16 19 22,
  .fa 25 28 31, .fa 1 10 19, .fa 34 35 36, .fa 37 38 39, .fa 40 41 42, .fa 43 44 45, .fa 46 47 48,
  .fa 49 50 51, .fa 52 53 54, .fa 55 56 57, .fa 58 59 60] : List InPlaceStep) ++ (([.fa 61 62 63,
  .fa 64 65 66, .fa 67 68 69, .fa 70 71 72, .fa 73 74 75, .fa 76 77 78, .fa 79 80 81, .fa 82 83 84,
  .fa 85 86 87, .fa 88 89 90, .fa 91 92 93, .fa 94 95 96, .fa 97 98 99, .fa 100 101 102,
  .fa 103 104 105, .fa 106 107 108, .fa 109 110 111, .fa 112 113 114, .fa 115 116 117,
  .fa 118 119 120, .fa 121 122 123, .fa 124 125 126, .fa 127 128 129, .fa 130 131 132,
  .fa 133 134 135] : List InPlaceStep) ++ (([.fa 136 137 138, .fa 139 140 141, .fa 142 144 145,
  .fa 146 147 148, .fa 149 150 151, .fa 152 153 154, .fa 155 156 157, .fa 158 159 35, .fa 38 41 44,
  .fa 47 50 53, .fa 56 59 62, .fa 65 68 71, .fa 74 77 80, .fa 83 86 89, .fa 92 95 98,
  .fa 101 104 107, .fa 110 113 116, .fa 119 122 125, .fa 128 131 134, .fa 137 140 144,
  .fa 147 150 153, .fa 156 159 41, .fa 50 59 68, .fa 77 86 95,
  .fa 104 113 122] : List InPlaceStep) ++ (([.fa 131 140 150, .fa 159 59 86, .fa 113 140 59,
  .fa 143 160 161, .fa 162 163 164, .fa 165 166 167, .fa 168 169 170, .fa 171 172 173,
  .fa 174 175 176, .fa 177 178 179, .fa 180 181 182, .fa 183 184 185, .fa 186 187 188,
  .fa 189 190 191, .fa 192 193 194, .fa 195 196 197, .fa 198 199 200, .fa 201 202 203,
  .fa 204 205 206, .fa 207 208 209, .fa 210 211 212, .fa 213 214 215, .fa 216 217 218,
  .fa 219 220 221, .fa 160 163 166] : List InPlaceStep) ++ (([.fa 169 172 175, .fa 178 181 184,
  .fa 187 190 193, .fa 196 199 202, .fa 205 208 211, .fa 214 217 220, .fa 163 172 181,
  .fa 190 199 208, .fa 217 172 199, .fa 222 223 224, .fa 225 226 227, .fa 228 229 230,
  .fa 231 232 233, .fa 234 235 236, .fa 237 238 239, .fa 240 241 242, .fa 243 244 245,
  .fa 246 247 248, .fa 249 250 251, .fa 252 223 226, .fa 229 232 235, .fa 238 241 244,
  .fa 247 250 223, .fa 232 241 250, .fa 253 254 255] : List InPlaceStep) ++ ([.fa 256 257 258,
  .fa 259 260 261, .fa 262 263 264, .fa 265 266 267, .fa 254 257 260, .fa 263 266 257,
  .fa 268 269 270, .fa 271 272 273, .fa 274 269 272, .fa 275 276 277] : List InPlaceStep))))))
/-- Output wire map for `wcsa05`. -/
def wcsa05OutWires : Fin 8 → Wire 279
  | 0 => ⟨10, by decide⟩
  | 1 => ⟨140, by decide⟩
  | 2 => ⟨172, by decide⟩
  | 3 => ⟨241, by decide⟩
  | 4 => ⟨266, by decide⟩
  | 5 => ⟨269, by decide⟩
  | 6 => ⟨276, by decide⟩
  | 7 => ⟨278, by decide⟩
theorem wcsa05OutWires_injective : Function.Injective wcsa05OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa05`. -/
def wcsa05CinWire : Wire 279 := ⟨28, by decide⟩
theorem wcsa05CinWire_ne_out (k : Fin 8) : wcsa05CinWire ≠ wcsa05OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa05`. -/
def wcsa05Spec : WeightedCsa3GenSpec 34 109 1 8 135 where
  steps := wcsa05Steps
  outWires := wcsa05OutWires
  cinWire := (some wcsa05CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa05OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa05CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 34 109 1 135 wcsa05Steps (expectedOutWeightsCin wcsa05OutWires
    (some wcsa05CinWire)) rfl
attribute [irreducible] wcsa05Steps wcsa05Spec
/-- CSA step list for `wcsa06`. -/
def wcsa06Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38, .fa 39 40 41,
  .fa 42 43 44, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 1, .fa 4 7 10, .fa 13 16 19,
  .fa 22 25 28, .fa 31 34 37, .fa 40 43 46, .fa 49 52 55] : List InPlaceStep) ++ (([.fa 7 16 25,
  .fa 34 43 52, .fa 56 57 58, .fa 59 60 61, .fa 62 63 64, .fa 65 66 67, .fa 68 69 70, .fa 71 72 73,
  .fa 74 75 76, .fa 77 78 79, .fa 80 81 82, .fa 83 84 85, .fa 86 87 88, .fa 89 90 91, .fa 92 93 94,
  .fa 95 96 97, .fa 98 99 100, .fa 101 102 103, .fa 104 105 106, .fa 107 108 109, .fa 110 111 112,
  .fa 113 114 115, .fa 116 117 118, .fa 119 120 121,
  .fa 122 123 124] : List InPlaceStep) ++ (([.fa 125 126 127, .fa 128 129 130, .fa 131 132 133,
  .fa 134 135 146, .fa 147 148 149, .fa 150 151 152, .fa 153 154 155, .fa 156 157 158,
  .fa 159 160 161, .fa 162 163 164, .fa 165 166 167, .fa 168 169 170, .fa 171 172 57, .fa 60 63 66,
  .fa 69 72 75, .fa 78 81 84, .fa 87 90 93, .fa 96 99 102, .fa 105 108 111, .fa 114 117 120,
  .fa 123 126 129, .fa 132 135 148, .fa 151 154 157, .fa 160 163 166,
  .fa 169 172 63] : List InPlaceStep) ++ (([.fa 72 81 90, .fa 99 108 117, .fa 126 135 154,
  .fa 163 172 81, .fa 108 135 172, .fa 136 137 138, .fa 139 140 141, .fa 142 143 144,
  .fa 145 173 174, .fa 175 176 177, .fa 178 179 180, .fa 181 182 183, .fa 184 185 186,
  .fa 187 188 189, .fa 190 191 192, .fa 193 194 195, .fa 196 197 198, .fa 199 200 201,
  .fa 202 203 204, .fa 205 206 207, .fa 208 209 210, .fa 211 212 213, .fa 214 215 216,
  .fa 217 218 219, .fa 220 221 222] : List InPlaceStep) ++ (([.fa 223 224 225, .fa 137 140 143,
  .fa 173 176 179, .fa 182 185 188, .fa 191 194 197, .fa 200 203 206, .fa 209 212 215,
  .fa 218 221 224, .fa 140 176 185, .fa 194 203 212, .fa 221 176 203, .fa 226 227 228,
  .fa 229 230 231, .fa 232 233 234, .fa 235 236 237, .fa 238 239 240, .fa 241 242 243,
  .fa 244 245 246, .fa 247 248 249, .fa 250 251 252, .fa 253 254 255, .fa 256 227 230,
  .fa 233 236 239, .fa 242 245 248, .fa 251 254 227] : List InPlaceStep) ++ ([.fa 236 245 254,
  .fa 257 258 259, .fa 260 261 262, .fa 263 264 265, .fa 266 267 268, .fa 269 270 271,
  .fa 258 261 264, .fa 267 270 261, .fa 272 273 274, .fa 275 276 277, .fa 278 273 276,
  .fa 279 280 281] : List InPlaceStep))))))
/-- Output wire map for `wcsa06`. -/
def wcsa06OutWires : Fin 8 → Wire 283
  | 0 => ⟨43, by decide⟩
  | 1 => ⟨135, by decide⟩
  | 2 => ⟨176, by decide⟩
  | 3 => ⟨245, by decide⟩
  | 4 => ⟨270, by decide⟩
  | 5 => ⟨273, by decide⟩
  | 6 => ⟨280, by decide⟩
  | 7 => ⟨282, by decide⟩
theorem wcsa06OutWires_injective : Function.Injective wcsa06OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa06`. -/
def wcsa06CinWire : Wire 283 := ⟨16, by decide⟩
theorem wcsa06CinWire_ne_out (k : Fin 8) : wcsa06CinWire ≠ wcsa06OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa06`. -/
def wcsa06Spec : WeightedCsa3GenSpec 56 80 10 8 137 where
  steps := wcsa06Steps
  outWires := wcsa06OutWires
  cinWire := (some wcsa06CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa06OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa06CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 56 80 10 137 wcsa06Steps (expectedOutWeightsCin wcsa06OutWires
    (some wcsa06CinWire)) rfl
attribute [irreducible] wcsa06Steps wcsa06Spec
/-- CSA step list for `wcsa07`. -/
def wcsa07Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38, .fa 39 40 41,
  .fa 42 43 44, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62,
  .fa 63 64 65, .fa 66 67 68, .fa 69 70 71, .fa 72 73 74] : List InPlaceStep) ++ (([.fa 75 76 77,
  .fa 78 79 80, .fa 81 82 83, .fa 84 85 86, .fa 87 88 89, .fa 90 91 92, .fa 93 94 95, .fa 96 97 98,
  .fa 99 100 101, .fa 102 103 104, .fa 105 106 107, .fa 1 4 7, .fa 10 13 16, .fa 19 22 25,
  .fa 28 31 34, .fa 37 40 43, .fa 46 49 52, .fa 55 58 61, .fa 64 67 70, .fa 73 76 79, .fa 82 85 88,
  .fa 91 94 97, .fa 100 103 106, .fa 4 13 22, .fa 31 40 49] : List InPlaceStep) ++ (([.fa 58 67 76,
  .fa 85 94 103, .fa 13 40 67, .fa 108 109 146, .fa 147 148 149, .fa 150 151 152, .fa 153 154 155,
  .fa 156 157 158, .fa 159 160 161, .fa 162 163 164, .fa 165 166 167, .fa 168 169 170,
  .fa 171 172 173, .fa 174 175 176, .fa 177 178 179, .fa 180 181 182, .fa 183 184 185,
  .fa 186 187 188, .fa 189 190 191, .fa 192 193 194, .fa 195 196 197, .fa 198 109 148,
  .fa 151 154 157, .fa 160 163 166, .fa 169 172 175] : List InPlaceStep) ++ (([.fa 178 181 184,
  .fa 187 190 193, .fa 196 109 154, .fa 163 172 181, .fa 190 109 172, .fa 110 111 112,
  .fa 113 114 115, .fa 116 117 118, .fa 119 120 121, .fa 122 123 124, .fa 125 126 127,
  .fa 128 129 130, .fa 131 132 133, .fa 134 135 136, .fa 137 138 139, .fa 140 141 142,
  .fa 143 144 145, .fa 199 200 201, .fa 202 203 204, .fa 205 206 207, .fa 208 209 210,
  .fa 211 212 213, .fa 214 215 216, .fa 217 218 219,
  .fa 220 221 222] : List InPlaceStep) ++ (([.fa 223 224 225, .fa 111 114 117, .fa 120 123 126,
  .fa 129 132 135, .fa 138 141 144, .fa 200 203 206, .fa 209 212 215, .fa 218 221 224,
  .fa 114 123 132, .fa 141 203 212, .fa 221 123 203, .fa 226 227 228, .fa 229 230 231,
  .fa 232 233 234, .fa 235 236 237, .fa 238 239 240, .fa 241 242 243, .fa 244 245 246,
  .fa 247 248 249, .fa 250 251 252, .fa 253 254 255, .fa 256 227 230, .fa 233 236 239,
  .fa 242 245 248, .fa 251 254 227] : List InPlaceStep) ++ ([.fa 236 245 254, .fa 257 258 259,
  .fa 260 261 262, .fa 263 264 265, .fa 266 267 268, .fa 269 270 271, .fa 258 261 264,
  .fa 267 270 261, .fa 272 273 274, .fa 275 276 277, .fa 278 273 276,
  .fa 279 280 281] : List InPlaceStep))))))
/-- Output wire map for `wcsa07`. -/
def wcsa07OutWires : Fin 8 → Wire 283
  | 0 => ⟨40, by decide⟩
  | 1 => ⟨109, by decide⟩
  | 2 => ⟨123, by decide⟩
  | 3 => ⟨245, by decide⟩
  | 4 => ⟨270, by decide⟩
  | 5 => ⟨273, by decide⟩
  | 6 => ⟨280, by decide⟩
  | 7 => ⟨282, by decide⟩
theorem wcsa07OutWires_injective : Function.Injective wcsa07OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa07`. -/
def wcsa07CinWire : Wire 283 := ⟨94, by decide⟩
theorem wcsa07CinWire_ne_out (k : Fin 8) : wcsa07CinWire ≠ wcsa07OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa07`. -/
def wcsa07Spec : WeightedCsa3GenSpec 108 2 36 8 137 where
  steps := wcsa07Steps
  outWires := wcsa07OutWires
  cinWire := (some wcsa07CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa07OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa07CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 108 2 36 137 wcsa07Steps (expectedOutWeightsCin wcsa07OutWires
    (some wcsa07CinWire)) rfl
attribute [irreducible] wcsa07Steps wcsa07Spec
/-- CSA step list for `wcsa08`. -/
def wcsa08Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 1 4, .fa 10 11 12, .fa 13 14 15, .fa 16 17 18,
  .fa 19 20 21, .fa 22 23 24, .fa 25 26 27, .fa 28 29 30, .fa 146 147 148, .fa 149 11 14,
  .fa 17 20 23, .fa 26 29 147, .fa 11 20 29, .fa 31 32 33, .fa 34 35 36, .fa 37 38 39, .fa 40 41 42,
  .fa 43 44 45, .fa 46 47 48, .fa 49 50 51, .fa 52 53 54,
  .fa 55 56 57] : List InPlaceStep) ++ (([.fa 58 59 60, .fa 61 62 63, .fa 64 65 66, .fa 67 68 69,
  .fa 70 71 72, .fa 73 74 75, .fa 76 77 78, .fa 79 80 81, .fa 82 83 84, .fa 85 86 87, .fa 88 89 90,
  .fa 91 92 93, .fa 94 95 96, .fa 97 98 99, .fa 100 101 102, .fa 103 104 105, .fa 106 107 108,
  .fa 109 110 111, .fa 112 113 114, .fa 115 116 117, .fa 118 119 120, .fa 121 122 123,
  .fa 124 125 126, .fa 127 128 129, .fa 130 131 132] : List InPlaceStep) ++ (([.fa 133 134 135,
  .fa 136 137 138, .fa 139 140 141, .fa 142 143 144, .fa 145 150 151, .fa 152 153 154,
  .fa 155 156 157, .fa 158 159 160, .fa 161 32 35, .fa 38 41 44, .fa 47 50 53, .fa 56 59 62,
  .fa 65 68 71, .fa 74 77 80, .fa 83 86 89, .fa 92 95 98, .fa 101 104 107, .fa 110 113 116,
  .fa 119 122 125, .fa 128 131 134, .fa 137 140 143, .fa 150 153 156, .fa 159 32 41, .fa 50 59 68,
  .fa 77 86 95] : List InPlaceStep) ++ (([.fa 104 113 122, .fa 131 140 153, .fa 32 59 86,
  .fa 113 140 59, .fa 162 163 164, .fa 165 166 167, .fa 168 169 170, .fa 171 172 173,
  .fa 174 175 176, .fa 177 178 179, .fa 180 181 182, .fa 183 184 185, .fa 186 187 188,
  .fa 189 190 191, .fa 192 193 194, .fa 195 196 197, .fa 198 199 200, .fa 201 202 203,
  .fa 204 205 206, .fa 207 208 209, .fa 210 211 212, .fa 213 214 215, .fa 216 217 218,
  .fa 219 220 221, .fa 222 223 224] : List InPlaceStep) ++ (([.fa 163 166 169, .fa 172 175 178,
  .fa 181 184 187, .fa 190 193 196, .fa 199 202 205, .fa 208 211 214, .fa 217 220 223,
  .fa 166 175 184, .fa 193 202 211, .fa 220 175 202, .fa 225 226 227, .fa 228 229 230,
  .fa 231 232 233, .fa 234 235 236, .fa 237 238 239, .fa 240 241 242, .fa 243 244 245,
  .fa 246 247 248, .fa 249 250 251, .fa 252 253 254, .fa 255 226 229, .fa 232 235 238,
  .fa 241 244 247, .fa 250 253 226, .fa 235 244 253] : List InPlaceStep) ++ ([.fa 256 257 258,
  .fa 259 260 261, .fa 262 263 264, .fa 265 266 267, .fa 268 269 270, .fa 257 260 263,
  .fa 266 269 260, .fa 271 272 273, .fa 274 275 276, .fa 277 272 275,
  .fa 278 279 280] : List InPlaceStep))))))
/-- Output wire map for `wcsa08`. -/
def wcsa08OutWires : Fin 9 → Wire 282
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨20, by decide⟩
  | 2 => ⟨140, by decide⟩
  | 3 => ⟨175, by decide⟩
  | 4 => ⟨244, by decide⟩
  | 5 => ⟨269, by decide⟩
  | 6 => ⟨272, by decide⟩
  | 7 => ⟨279, by decide⟩
  | 8 => ⟨281, by decide⟩
theorem wcsa08OutWires_injective : Function.Injective wcsa08OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa08`. -/
def wcsa08CinWire : Wire 282 := ⟨7, by decide⟩
theorem wcsa08CinWire_ne_out (k : Fin 9) : wcsa08CinWire ≠ wcsa08OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa08`. -/
def wcsa08Spec : WeightedCsa3GenSpec 10 21 115 9 136 where
  steps := wcsa08Steps
  outWires := wcsa08OutWires
  cinWire := (some wcsa08CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa08OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa08CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 10 21 115 136 wcsa08Steps (expectedOutWeightsCin wcsa08OutWires
    (some wcsa08CinWire)) rfl
attribute [irreducible] wcsa08Steps wcsa08Spec
/-- CSA step list for `wcsa09`. -/
def wcsa09Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 1, .fa 5 6 7, .fa 8 9 10, .fa 68 69 6, .ha 9 69, .fa 11 12 13, .fa 14 15 16,
  .fa 17 18 19, .fa 20 21 22, .fa 23 24 25, .fa 26 27 28, .fa 29 30 31, .fa 32 33 34, .fa 35 36 37,
  .fa 38 39 40, .fa 41 42 43, .fa 44 45 46, .fa 47 48 49, .fa 50 51 52, .fa 53 54 55, .fa 56 57 58,
  .fa 59 60 61, .fa 62 63 64, .fa 65 66 67] : List InPlaceStep) ++ (([.fa 70 71 72, .fa 73 12 15,
  .fa 18 21 24, .fa 27 30 33, .fa 36 39 42, .fa 45 48 51, .fa 54 57 60, .fa 63 66 71, .fa 12 21 30,
  .fa 39 48 57, .fa 66 21 48, .fa 74 75 76, .fa 77 78 79, .fa 80 81 82, .fa 83 84 85, .fa 86 87 88,
  .fa 89 90 91, .fa 92 93 94, .fa 95 96 97, .fa 98 99 100, .fa 101 102 103, .fa 75 78 81,
  .fa 84 87 90, .fa 93 96 99, .fa 102 78 87] : List InPlaceStep) ++ ([.ha 96 78, .fa 104 105 106,
  .fa 107 108 109, .fa 110 111 112, .fa 113 114 115, .fa 116 117 118, .fa 105 108 111,
  .fa 114 117 108, .fa 119 120 121, .fa 122 123 124, .fa 125 120 123,
  .fa 126 127 128] : List InPlaceStep)))
/-- Output wire map for `wcsa09`. -/
def wcsa09OutWires : Fin 8 → Wire 130
  | 0 => ⟨4, by decide⟩
  | 1 => ⟨69, by decide⟩
  | 2 => ⟨21, by decide⟩
  | 3 => ⟨78, by decide⟩
  | 4 => ⟨117, by decide⟩
  | 5 => ⟨120, by decide⟩
  | 6 => ⟨127, by decide⟩
  | 7 => ⟨129, by decide⟩
theorem wcsa09OutWires_injective : Function.Injective wcsa09OutWires := by
  intro i j h; revert i j h; decide
/-- Verified 3-plane CSA schedule `wcsa09`. -/
def wcsa09Spec : WeightedCsa3GenSpec 5 6 57 8 62 where
  steps := wcsa09Steps
  outWires := wcsa09OutWires
  cinWire := none
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa09OutWires_injective
  hCinNe := fun _ _ hcw ↦ by cases hcw
  hRun :=
    runWeightList_of_checkCsaTree 5 6 57 62 wcsa09Steps (expectedOutWeightsCin wcsa09OutWires none)
    rfl
attribute [irreducible] wcsa09Steps wcsa09Spec
/-- CSA step list for `wcsa10`. -/
def wcsa10Steps : List InPlaceStep :=
  (([.fa 2 3 4, .fa 5 6 7, .fa 8 9 10, .fa 11 12 13, .fa 14 15 16, .fa 17 18 19, .fa 20 21 22,
  .fa 23 24 25, .fa 26 27 28, .fa 29 30 31, .fa 32 33 34, .fa 35 36 37, .fa 38 39 40, .fa 41 42 43,
  .fa 44 45 46, .fa 47 48 49, .fa 50 51 52, .fa 53 54 55, .fa 56 57 58, .fa 59 60 61, .fa 62 63 64,
  .fa 65 66 67, .fa 68 69 70, .fa 71 72 73, .fa 74 75 76] : List InPlaceStep) ++ (([.fa 77 78 79,
  .fa 80 81 82, .fa 83 84 85, .fa 86 87 88, .fa 89 90 91, .fa 92 93 94, .fa 95 96 97, .fa 98 99 100,
  .fa 101 102 103, .fa 104 105 106, .fa 107 108 109, .fa 110 111 112, .fa 113 114 115,
  .fa 116 117 118, .fa 119 120 121, .fa 122 123 124, .fa 125 126 127, .fa 128 3 6, .fa 9 12 15,
  .fa 18 21 24, .fa 27 30 33, .fa 36 39 42, .fa 45 48 51, .fa 54 57 60,
  .fa 63 66 69] : List InPlaceStep) ++ (([.fa 72 75 78, .fa 81 84 87, .fa 90 93 96, .fa 99 102 105,
  .fa 108 111 114, .fa 117 120 123, .fa 126 3 12, .fa 21 30 39, .fa 48 57 66, .fa 75 84 93,
  .fa 102 111 120, .fa 3 30 57, .fa 84 111 30, .fa 129 130 131, .fa 132 133 134, .fa 135 136 137,
  .fa 138 139 140, .fa 141 142 143, .fa 144 145 146, .fa 147 148 149, .fa 150 151 152,
  .fa 153 154 155, .fa 156 157 158, .fa 159 160 161,
  .fa 162 163 164] : List InPlaceStep) ++ (([.fa 165 166 167, .fa 168 169 170, .fa 171 172 173,
  .fa 174 175 176, .fa 177 178 179, .fa 180 181 182, .fa 183 184 185, .fa 186 187 188,
  .fa 189 190 191, .fa 130 133 136, .fa 139 142 145, .fa 148 151 154, .fa 157 160 163,
  .fa 166 169 172, .fa 175 178 181, .fa 184 187 190, .fa 133 142 151, .fa 160 169 178,
  .fa 187 142 169, .fa 192 193 194, .fa 195 196 197, .fa 198 199 200, .fa 201 202 203,
  .fa 204 205 206, .fa 207 208 209] : List InPlaceStep) ++ ([.fa 210 211 212, .fa 213 214 215,
  .fa 216 217 218, .fa 219 220 221, .fa 222 193 196, .fa 199 202 205, .fa 208 211 214,
  .fa 217 220 193, .fa 202 211 220, .fa 223 224 225, .fa 226 227 228, .fa 229 230 231,
  .fa 232 233 234, .fa 235 236 237, .fa 224 227 230, .fa 233 236 227, .fa 238 239 240,
  .fa 241 242 243, .fa 244 239 242, .fa 245 246 247] : List InPlaceStep)))))
/-- Output wire map for `wcsa10`. -/
def wcsa10OutWires : Fin 8 → Wire 249
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨111, by decide⟩
  | 2 => ⟨142, by decide⟩
  | 3 => ⟨211, by decide⟩
  | 4 => ⟨236, by decide⟩
  | 5 => ⟨239, by decide⟩
  | 6 => ⟨246, by decide⟩
  | 7 => ⟨248, by decide⟩
theorem wcsa10OutWires_injective : Function.Injective wcsa10OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa10`. -/
def wcsa10CinWire : Wire 249 := ⟨0, by decide⟩
theorem wcsa10CinWire_ne_out (k : Fin 8) : wcsa10CinWire ≠ wcsa10OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa10`. -/
def wcsa10Spec : WeightedCsa3GenSpec 2 127 0 8 120 where
  steps := wcsa10Steps
  outWires := wcsa10OutWires
  cinWire := (some wcsa10CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa10OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa10CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 2 127 0 120 wcsa10Steps (expectedOutWeightsCin wcsa10OutWires
    (some wcsa10CinWire)) rfl
attribute [irreducible] wcsa10Steps wcsa10Spec
/-- CSA step list for `wcsa11`. -/
def wcsa11Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 1, .fa 4 7 10,
  .fa 13 16 19, .fa 22 25 28, .fa 31 34 37, .fa 7 16 25, .fa 38 39 40, .fa 41 42 43, .fa 44 45 46,
  .fa 47 48 49, .fa 50 51 52, .fa 53 54 55, .fa 56 57 58] : List InPlaceStep) ++ (([.fa 59 60 61,
  .fa 62 63 64, .fa 65 66 67, .fa 68 69 70, .fa 71 72 73, .fa 74 75 76, .fa 77 78 79, .fa 80 81 82,
  .fa 83 84 85, .fa 86 87 88, .fa 89 90 91, .fa 92 93 94, .fa 95 96 97, .fa 98 99 100,
  .fa 101 102 103, .fa 104 105 106, .fa 107 108 128, .fa 129 130 131, .fa 132 133 134,
  .fa 135 136 137, .fa 138 139 140, .fa 141 142 143, .fa 144 145 39, .fa 42 45 48,
  .fa 51 54 57] : List InPlaceStep) ++ (([.fa 60 63 66, .fa 69 72 75, .fa 78 81 84, .fa 87 90 93,
  .fa 96 99 102, .fa 105 108 130, .fa 133 136 139, .fa 142 145 45, .fa 54 63 72, .fa 81 90 99,
  .fa 108 136 145, .fa 63 90 136, .fa 109 110 111, .fa 112 113 114, .fa 115 116 117,
  .fa 118 119 120, .fa 121 122 123, .fa 124 125 126, .fa 127 146 147, .fa 148 149 150,
  .fa 151 152 153, .fa 154 155 156, .fa 157 158 159, .fa 160 161 162,
  .fa 163 164 165] : List InPlaceStep) ++ (([.fa 166 167 168, .fa 169 170 171, .fa 172 173 174,
  .fa 175 176 177, .fa 178 179 180, .fa 181 182 183, .fa 184 185 186, .fa 187 188 189,
  .fa 110 113 116, .fa 119 122 125, .fa 146 149 152, .fa 155 158 161, .fa 164 167 170,
  .fa 173 176 179, .fa 182 185 188, .fa 113 122 149, .fa 158 167 176, .fa 185 122 167,
  .fa 190 191 192, .fa 193 194 195, .fa 196 197 198, .fa 199 200 201, .fa 202 203 204,
  .fa 205 206 207, .fa 208 209 210] : List InPlaceStep) ++ ([.fa 211 212 213, .fa 214 215 216,
  .fa 217 218 219, .fa 220 191 194, .fa 197 200 203, .fa 206 209 212, .fa 215 218 191,
  .fa 200 209 218, .fa 221 222 223, .fa 224 225 226, .fa 227 228 229, .fa 230 231 232,
  .fa 233 234 235, .fa 222 225 228, .fa 231 234 225, .fa 236 237 238, .fa 239 240 241,
  .fa 242 237 240, .fa 243 244 245] : List InPlaceStep)))))
/-- Output wire map for `wcsa11`. -/
def wcsa11OutWires : Fin 8 → Wire 247
  | 0 => ⟨16, by decide⟩
  | 1 => ⟨90, by decide⟩
  | 2 => ⟨122, by decide⟩
  | 3 => ⟨209, by decide⟩
  | 4 => ⟨234, by decide⟩
  | 5 => ⟨237, by decide⟩
  | 6 => ⟨244, by decide⟩
  | 7 => ⟨246, by decide⟩
theorem wcsa11OutWires_injective : Function.Injective wcsa11OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa11`. -/
def wcsa11CinWire : Wire 247 := ⟨34, by decide⟩
theorem wcsa11CinWire_ne_out (k : Fin 8) : wcsa11CinWire ≠ wcsa11OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa11`. -/
def wcsa11Spec : WeightedCsa3GenSpec 38 71 19 8 119 where
  steps := wcsa11Steps
  outWires := wcsa11OutWires
  cinWire := (some wcsa11CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa11OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa11CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 38 71 19 119 wcsa11Steps (expectedOutWeightsCin wcsa11OutWires
    (some wcsa11CinWire)) rfl
attribute [irreducible] wcsa11Steps wcsa11Spec
/-- CSA step list for `wcsa12`. -/
def wcsa12Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 1, .fa 4 7 10, .fa 13 16 19, .fa 22 25 28,
  .fa 31 7 16, .fa 32 33 34, .fa 35 36 37, .fa 38 39 40, .fa 41 42 43, .fa 44 45 46, .fa 47 48 49,
  .fa 50 51 98, .fa 99 100 101, .fa 102 103 104,
  .fa 105 106 107] : List InPlaceStep) ++ (([.fa 108 109 110, .fa 111 112 33, .fa 36 39 42,
  .fa 45 48 51, .fa 100 103 106, .fa 109 112 39, .fa 48 103 112, .fa 52 53 54, .fa 55 56 57,
  .fa 58 59 60, .fa 61 62 63, .fa 64 65 66, .fa 67 68 69, .fa 70 71 72, .fa 73 74 75, .fa 76 77 78,
  .fa 79 80 81, .fa 82 83 84, .fa 85 86 87, .fa 88 89 90, .fa 91 92 93, .fa 94 95 96,
  .fa 97 113 114, .fa 115 116 117, .fa 118 119 120] : List InPlaceStep) ++ (([.fa 121 122 123,
  .fa 124 125 126, .fa 127 128 129, .fa 53 56 59, .fa 62 65 68, .fa 71 74 77, .fa 80 83 86,
  .fa 89 92 95, .fa 113 116 119, .fa 122 125 128, .fa 56 65 74, .fa 83 92 116, .fa 125 65 92,
  .fa 130 131 132, .fa 133 134 135, .fa 136 137 138, .fa 139 140 141, .fa 142 143 144,
  .fa 145 146 147, .fa 148 149 150, .fa 151 152 153, .fa 154 155 156, .fa 157 158 159,
  .fa 160 131 134, .fa 137 140 143] : List InPlaceStep) ++ ([.fa 146 149 152, .fa 155 158 131,
  .fa 140 149 158, .fa 161 162 163, .fa 164 165 166, .fa 167 168 169, .fa 170 171 172,
  .fa 173 174 175, .fa 162 165 168, .fa 171 174 165, .fa 176 177 178, .fa 179 180 181,
  .fa 182 177 180, .fa 183 184 185] : List InPlaceStep))))
/-- Output wire map for `wcsa12`. -/
def wcsa12OutWires : Fin 8 → Wire 187
  | 0 => ⟨7, by decide⟩
  | 1 => ⟨103, by decide⟩
  | 2 => ⟨65, by decide⟩
  | 3 => ⟨149, by decide⟩
  | 4 => ⟨174, by decide⟩
  | 5 => ⟨177, by decide⟩
  | 6 => ⟨184, by decide⟩
  | 7 => ⟨186, by decide⟩
theorem wcsa12OutWires_injective : Function.Injective wcsa12OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa12`. -/
def wcsa12CinWire : Wire 187 := ⟨25, by decide⟩
theorem wcsa12CinWire_ne_out (k : Fin 8) : wcsa12CinWire ≠ wcsa12OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa12`. -/
def wcsa12Spec : WeightedCsa3GenSpec 32 20 46 8 89 where
  steps := wcsa12Steps
  outWires := wcsa12OutWires
  cinWire := (some wcsa12CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa12OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa12CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 32 20 46 89 wcsa12Steps (expectedOutWeightsCin wcsa12OutWires
    (some wcsa12CinWire)) rfl
attribute [irreducible] wcsa12Steps wcsa12Spec
/-- CSA step list for `wcsa13`. -/
def wcsa13Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38, .fa 39 40 41,
  .fa 42 43 44, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62,
  .fa 63 64 65, .fa 66 67 68, .fa 69 70 71, .fa 72 73 74] : List InPlaceStep) ++ (([.fa 75 76 77,
  .fa 78 79 1, .fa 4 7 10, .fa 13 16 19, .fa 22 25 28, .fa 31 34 37, .fa 40 43 46, .fa 49 52 55,
  .fa 58 61 64, .fa 67 70 73, .fa 76 79 7, .fa 16 25 34, .fa 43 52 61, .fa 70 79 25, .fa 80 81 82,
  .fa 83 84 85, .fa 86 87 128, .fa 129 130 131, .fa 132 133 134, .fa 135 136 137, .fa 138 139 140,
  .fa 141 142 143, .fa 144 145 146, .fa 147 148 149,
  .fa 150 151 152] : List InPlaceStep) ++ (([.fa 153 154 155, .fa 156 157 158, .fa 159 160 161,
  .fa 162 163 164, .fa 165 166 81, .fa 84 87 130, .fa 133 136 139, .fa 142 145 148, .fa 151 154 157,
  .fa 160 163 166, .fa 87 136 145, .fa 154 163 136, .fa 88 89 90, .fa 91 92 93, .fa 94 95 96,
  .fa 97 98 99, .fa 100 101 102, .fa 103 104 105, .fa 106 107 108, .fa 109 110 111, .fa 112 113 114,
  .fa 115 116 117, .fa 118 119 120, .fa 121 122 123,
  .fa 124 125 126] : List InPlaceStep) ++ (([.fa 127 167 168, .fa 169 170 171, .fa 172 173 174,
  .fa 175 176 177, .fa 178 179 180, .fa 181 182 183, .fa 184 185 186, .fa 187 188 189, .fa 89 92 95,
  .fa 98 101 104, .fa 107 110 113, .fa 116 119 122, .fa 125 167 170, .fa 173 176 179,
  .fa 182 185 188, .fa 92 101 110, .fa 119 167 176, .fa 185 101 167, .fa 190 191 192,
  .fa 193 194 195, .fa 196 197 198, .fa 199 200 201, .fa 202 203 204, .fa 205 206 207,
  .fa 208 209 210] : List InPlaceStep) ++ ([.fa 211 212 213, .fa 214 215 216, .fa 217 218 219,
  .fa 220 191 194, .fa 197 200 203, .fa 206 209 212, .fa 215 218 191, .fa 200 209 218,
  .fa 221 222 223, .fa 224 225 226, .fa 227 228 229, .fa 230 231 232, .fa 233 234 235,
  .fa 222 225 228, .fa 231 234 225, .fa 236 237 238, .fa 239 240 241, .fa 242 237 240,
  .fa 243 244 245] : List InPlaceStep)))))
/-- Output wire map for `wcsa13`. -/
def wcsa13OutWires : Fin 8 → Wire 247
  | 0 => ⟨79, by decide⟩
  | 1 => ⟨163, by decide⟩
  | 2 => ⟨101, by decide⟩
  | 3 => ⟨209, by decide⟩
  | 4 => ⟨234, by decide⟩
  | 5 => ⟨237, by decide⟩
  | 6 => ⟨244, by decide⟩
  | 7 => ⟨246, by decide⟩
theorem wcsa13OutWires_injective : Function.Injective wcsa13OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa13`. -/
def wcsa13CinWire : Wire 247 := ⟨52, by decide⟩
theorem wcsa13CinWire_ne_out (k : Fin 8) : wcsa13CinWire ≠ wcsa13OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa13`. -/
def wcsa13Spec : WeightedCsa3GenSpec 80 8 40 8 119 where
  steps := wcsa13Steps
  outWires := wcsa13OutWires
  cinWire := (some wcsa13CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa13OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa13CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 80 8 40 119 wcsa13Steps (expectedOutWeightsCin wcsa13OutWires
    (some wcsa13CinWire)) rfl
attribute [irreducible] wcsa13Steps wcsa13Spec
/-- CSA step list for `wcsa14`. -/
def wcsa14Steps : List InPlaceStep :=
  (([.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
  .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 1 4, .fa 7 10 13, .fa 16 19 22,
  .fa 25 28 31, .fa 1 10 19, .fa 34 35 36, .fa 37 38 39, .fa 40 41 42, .fa 43 44 95, .fa 96 97 98,
  .fa 99 100 101, .fa 102 103 104, .fa 105 106 107,
  .fa 108 109 110] : List InPlaceStep) ++ (([.fa 35 38 41, .fa 44 97 100, .fa 103 106 109,
  .fa 38 97 106, .fa 45 46 47, .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62,
  .fa 63 64 65, .fa 66 67 68, .fa 69 70 71, .fa 72 73 74, .fa 75 76 77, .fa 78 79 80, .fa 81 82 83,
  .fa 84 85 86, .fa 87 88 89, .fa 90 91 92, .fa 93 94 111, .fa 112 113 114, .fa 115 116 117,
  .fa 118 119 120, .fa 121 122 123] : List InPlaceStep) ++ (([.fa 46 49 52, .fa 55 58 61,
  .fa 64 67 70, .fa 73 76 79, .fa 82 85 88, .fa 91 94 113, .fa 116 119 122, .fa 49 58 67,
  .fa 76 85 94, .fa 119 58 85, .fa 124 125 126, .fa 127 128 129, .fa 130 131 132, .fa 133 134 135,
  .fa 136 137 138, .fa 139 140 141, .fa 142 143 144, .fa 145 146 147, .fa 148 149 150,
  .fa 151 152 153, .fa 154 125 128, .fa 131 134 137, .fa 140 143 146, .fa 149 152 125,
  .fa 134 143 152] : List InPlaceStep) ++ ([.fa 155 156 157, .fa 158 159 160, .fa 161 162 163,
  .fa 164 165 166, .fa 167 168 169, .fa 156 159 162, .fa 165 168 159, .fa 170 171 172,
  .fa 173 174 175, .fa 176 171 174, .fa 177 178 179] : List InPlaceStep))))
/-- Output wire map for `wcsa14`. -/
def wcsa14OutWires : Fin 8 → Wire 181
  | 0 => ⟨10, by decide⟩
  | 1 => ⟨97, by decide⟩
  | 2 => ⟨58, by decide⟩
  | 3 => ⟨143, by decide⟩
  | 4 => ⟨168, by decide⟩
  | 5 => ⟨171, by decide⟩
  | 6 => ⟨178, by decide⟩
  | 7 => ⟨180, by decide⟩
theorem wcsa14OutWires_injective : Function.Injective wcsa14OutWires := by
  intro i j h; revert i j h; decide
/-- Carry-in wire for `wcsa14`. -/
def wcsa14CinWire : Wire 181 := ⟨28, by decide⟩
theorem wcsa14CinWire_ne_out (k : Fin 8) : wcsa14CinWire ≠ wcsa14OutWires k := by
  revert k; decide
/-- Verified 3-plane CSA schedule `wcsa14`. -/
def wcsa14Spec : WeightedCsa3GenSpec 34 11 50 8 86 where
  steps := wcsa14Steps
  outWires := wcsa14OutWires
  cinWire := (some wcsa14CinWire)
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa14OutWires_injective
  hCinNe := fun cw k hcw ↦ by injection hcw with hce; rw [← hce]; exact wcsa14CinWire_ne_out k
  hRun :=
    runWeightList_of_checkCsaTree 34 11 50 86 wcsa14Steps (expectedOutWeightsCin wcsa14OutWires
    (some wcsa14CinWire)) rfl
attribute [irreducible] wcsa14Steps wcsa14Spec
/-- CSA step list for `wcsa15`. -/
def wcsa15Steps : List InPlaceStep :=
  (([.fa 1 2 3, .fa 4 5 6, .fa 7 8 9, .fa 10 11 12, .fa 13 14 15, .fa 16 17 18, .fa 19 20 21,
  .fa 22 23 24, .fa 25 26 27, .fa 28 29 30, .fa 31 32 33, .fa 34 35 36, .fa 37 38 39, .fa 40 41 42,
  .fa 43 44 45, .fa 46 47 48, .fa 49 50 51, .fa 52 53 54, .fa 55 56 57, .fa 58 59 60, .fa 61 62 63,
  .fa 64 65 66, .fa 67 68 69, .fa 70 71 72, .fa 73 74 75] : List InPlaceStep) ++ (([.fa 76 77 78,
  .fa 79 80 81, .fa 82 83 84, .fa 85 86 87, .fa 88 89 90, .fa 91 92 93, .fa 94 95 96, .fa 97 98 99,
  .fa 100 101 102, .fa 103 104 105, .fa 106 107 108, .fa 109 2 5, .fa 8 11 14, .fa 17 20 23,
  .fa 26 29 32, .fa 35 38 41, .fa 44 47 50, .fa 53 56 59, .fa 62 65 68, .fa 71 74 77, .fa 80 83 86,
  .fa 89 92 95, .fa 98 101 104, .fa 107 2 11, .fa 20 29 38] : List InPlaceStep) ++ (([.fa 47 56 65,
  .fa 74 83 92, .fa 101 2 29, .fa 56 83 2, .fa 110 111 112, .fa 113 114 115, .fa 116 117 118,
  .fa 119 120 121, .fa 122 123 124, .fa 125 126 127, .fa 128 129 130, .fa 131 132 133,
  .fa 134 135 136, .fa 137 138 139, .fa 140 141 142, .fa 143 144 145, .fa 146 147 148,
  .fa 149 150 151, .fa 152 153 154, .fa 155 156 157, .fa 158 159 160, .fa 161 162 163,
  .fa 111 114 117, .fa 120 123 126, .fa 129 132 135] : List InPlaceStep) ++ (([.fa 138 141 144,
  .fa 147 150 153, .fa 156 159 162, .fa 114 123 132, .fa 141 150 159, .ha 123 150, .fa 164 165 166,
  .fa 167 168 169, .fa 170 171 172, .fa 173 174 175, .fa 176 177 178, .fa 179 180 181,
  .fa 182 183 184, .fa 185 186 187, .fa 188 189 190, .fa 165 168 171, .fa 174 177 180,
  .fa 183 186 189, .fa 168 177 186, .fa 191 192 193, .fa 194 195 196, .fa 197 198 199,
  .fa 200 201 202, .fa 203 192 195, .fa 198 201 192] : List InPlaceStep) ++ ([.fa 204 205 206,
  .fa 207 208 209, .ha 205 208, .fa 210 211 212] : List InPlaceStep)))))
/-- Output wire map for `wcsa15`. -/
def wcsa15OutWires : Fin 8 → Wire 214
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨83, by decide⟩
  | 2 => ⟨150, by decide⟩
  | 3 => ⟨177, by decide⟩
  | 4 => ⟨201, by decide⟩
  | 5 => ⟨208, by decide⟩
  | 6 => ⟨211, by decide⟩
  | 7 => ⟨213, by decide⟩
theorem wcsa15OutWires_injective : Function.Injective wcsa15OutWires := by
  intro i j h; revert i j h; decide
/-- Verified 3-plane CSA schedule `wcsa15`. -/
def wcsa15Spec : WeightedCsa3GenSpec 1 109 0 8 104 where
  steps := wcsa15Steps
  outWires := wcsa15OutWires
  cinWire := none
  hLen := rfl
  hValid := rfl
  hOutInj := wcsa15OutWires_injective
  hCinNe := fun _ _ hcw ↦ by cases hcw
  hRun :=
    runWeightList_of_checkCsaTree 1 109 0 104 wcsa15Steps (expectedOutWeightsCin wcsa15OutWires
    none) rfl
attribute [irreducible] wcsa15Steps wcsa15Spec
end Impl
end Bell18StageABridge_Borrow136.ChiralA

namespace Bell18StageABridge_Borrow136.ChiralB
noncomputable section Impl
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
set_option exponentiation.threshold 512
set_option maxRecDepth 200000
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice
open InPlaceStepEngine
open NuclearTwistRealizes (RealizesCleanPair CleanComputePair slot2AxisSum)
open SinglePassNuclearTwist288
open HybridStream288Aux
open HybridStream168Aux
local instance (priority := 1000000) instNeZeroTwoPowStageABrgB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Bell18StageABridge_Borrow136.ChiralA
/-!
## Section 3: Unconditional 1-Axis `Stream218` (`slot2AxisSum`) Variants (`146w .. 96w`)
-/
-- ============================================================================
-- Variant `218_146`: N=218 electrons, mWork >= 146, 1302 TempAnds = 5208 T/axis (11 layers)
-- ============================================================================
theorem h218_146_s1 {mWork : ℕ} (hm : 146 ≤ mWork) : 57 ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `1`. -/
def wChunk_218_146_s1 {mPayload : ℕ} (w : Fin 3) : Fin (63 + 0 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 0 63 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s1_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s1
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 0 63 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by
    decide) (by decide)
theorem wChunk_218_146_s1_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s1 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 0 63 +
      2 * corePlaneSliceSum w 1 γ 0 0 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 0 63 0 0 0 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s1
theorem h218_146_s2 {mWork : ℕ} (hm : 146 ≤ mWork) : 57 + (7 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `2`. -/
def wChunk_218_146_s2 {mPayload : ℕ} (w : Fin 3) : Fin (64 + 0 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 63 64 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s2_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s2
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 63 64 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by
    decide) (by decide)
theorem wChunk_218_146_s2_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s2 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 63 64 +
      2 * corePlaneSliceSum w 1 γ 0 0 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 63 64 0 0 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s2
theorem h218_146_s3 {mWork : ℕ} (hm : 146 ≤ mWork) : 101 + (8 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `3`. -/
def wChunk_218_146_s3 {mPayload : ℕ} (w : Fin 3) : Fin (90 + 19 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 127 90 0 19 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s3_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s3
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 127 90 0 19 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s3_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s3 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 127 90 +
      2 * corePlaneSliceSum w 1 γ 0 19 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 127 90 0 19 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s3
theorem h218_146_s4 {mWork : ℕ} (hm : 146 ≤ mWork) : 120 + (9 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `4`. -/
def wChunk_218_146_s4 {mPayload : ℕ} (w : Fin 3) : Fin (1 + 127 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 217 1 19 127 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s4_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s4
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 217 1 19 127 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s4_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s4 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 217 1 +
      2 * corePlaneSliceSum w 1 γ 19 127 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 217 1 19 127 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s4
theorem h218_146_s5 {mWork : ℕ} (hm : 146 ≤ mWork) : 138 + (9 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `5`. -/
def wChunk_218_146_s5 {mPayload : ℕ} (w : Fin 3) : Fin (38 + 109 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 1 146 38 0 109 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s5_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s5
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 1 146 38 0 109 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s5_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s5 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 1 γ 146 38 +
      2 * corePlaneSliceSum w 2 γ 0 109 +
      4 * corePlaneSliceSum w 3 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 1 2 3 rfl rfl 146 38 0 109 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s5
theorem h218_146_s6 {mWork : ℕ} (hm : 146 ≤ mWork) : 135 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `6`. -/
def wChunk_218_146_s6 {mPayload : ℕ} (w : Fin 3) : Fin (34 + 109 + 1) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 1 184 34 109 109 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s6_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s6
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 1 184 34 109 109 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s6_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s6 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 1 γ 184 34 +
      2 * corePlaneSliceSum w 2 γ 109 109 +
      4 * corePlaneSliceSum w 3 γ 0 1 :=
  weightedGenBatchVal_flexCoreChunk w 1 2 3 rfl rfl 184 34 109 109 0 1 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s6
theorem h218_146_s7 {mWork : ℕ} (hm : 146 ≤ mWork) : 138 + (9 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `7`. -/
def wChunk_218_146_s7 {mPayload : ℕ} (w : Fin 3) : Fin (38 + 109 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 1 38 0 109 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s7_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s7
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 1 38 0 109 0 0 (by decide) (by decide) (by decide) (by decide) (by
    decide) (by decide)
theorem wChunk_218_146_s7_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s7 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 1 38 +
      2 * corePlaneSliceSum w 4 γ 0 109 +
      4 * corePlaneSliceSum w 5 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 1 38 0 109 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s7
theorem h218_146_s8 {mWork : ℕ} (hm : 146 ≤ mWork) : 137 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `8`. -/
def wChunk_218_146_s8 {mPayload : ℕ} (w : Fin 3) : Fin (56 + 80 + 10) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 39 56 109 80 0 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s8_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s8
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 39 56 109 80 0 10 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s8_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s8 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 39 56 +
      2 * corePlaneSliceSum w 4 γ 109 80 +
      4 * corePlaneSliceSum w 5 γ 0 10 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 39 56 109 80 0 10 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s8
theorem h218_146_s9 {mWork : ℕ} (hm : 146 ≤ mWork) : 137 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `9`. -/
def wChunk_218_146_s9 {mPayload : ℕ} (w : Fin 3) : Fin (108 + 2 + 36) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 95 108 189 2 10 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s9_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s9
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 95 108 189 2 10 36 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s9_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s9 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 95 108 +
      2 * corePlaneSliceSum w 4 γ 189 2 +
      4 * corePlaneSliceSum w 5 γ 10 36 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 95 108 189 2 10 36 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s9
theorem h218_146_s10 {mWork : ℕ} (hm : 146 ≤ mWork) : 136 + (11 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `10`. -/
def wChunk_218_146_s10 {mPayload : ℕ} (w : Fin 3) : Fin (10 + 21 + 115) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 203 10 191 21 46 115 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
theorem wChunk_218_146_s10_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s10
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 203 10 191 21 46 115 (by decide) (by decide) (by decide) (by
    decide) (by decide) (by decide)
theorem wChunk_218_146_s10_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s10 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 203 10 +
      2 * corePlaneSliceSum w 4 γ 191 21 +
      4 * corePlaneSliceSum w 5 γ 46 115 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 203 10 191 21 46 115 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s10
theorem h218_146_s11 {mWork : ℕ} (hm : 146 ≤ mWork) : 62 + (11 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_146`, Wave `11`. -/
def wChunk_218_146_s11 {mPayload : ℕ} (w : Fin 3) : Fin (5 + 6 + 57) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 213 5 212 6 161 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_146_s11_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_146_s11
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 213 5 212 6 161 57 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_146_s11_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_146_s11 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 213 5 +
      2 * corePlaneSliceSum w 4 γ 212 6 +
      4 * corePlaneSliceSum w 5 γ 161 57 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 213 5 212 6 161 57 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_146_s11
theorem hybrid218_146_batch_eq_axisSum {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment
    (fullSysCoreWires mPayload)) :
    let w1 := (wChunk_218_146_s1 (mPayload := mPayload) w)
    let w2 := (wChunk_218_146_s2 (mPayload := mPayload) w)
    let w3 := (wChunk_218_146_s3 (mPayload := mPayload) w)
    let w4 := (wChunk_218_146_s4 (mPayload := mPayload) w)
    let w5 := (wChunk_218_146_s5 (mPayload := mPayload) w)
    let w6 := (wChunk_218_146_s6 (mPayload := mPayload) w)
    let w7 := (wChunk_218_146_s7 (mPayload := mPayload) w)
    let w8 := (wChunk_218_146_s8 (mPayload := mPayload) w)
    let w9 := (wChunk_218_146_s9 (mPayload := mPayload) w)
    let w10 := (wChunk_218_146_s10 (mPayload := mPayload) w)
    let w11 := (wChunk_218_146_s11 (mPayload := mPayload) w)
    ((((((((((weightedGenBatchVal w1 γ + 2 ^ 0 * weightedGenBatchVal w2 γ) + 2 ^ 0 *
      weightedGenBatchVal w3 γ) + 2 ^ 0 * weightedGenBatchVal w4 γ) + 2 ^ 1 *
      weightedGenBatchVal w5 γ) + 2 ^ 1 * weightedGenBatchVal w6 γ) + 2 ^ 3 *
      weightedGenBatchVal w7 γ) + 2 ^ 3 * weightedGenBatchVal w8 γ) + 2 ^ 3 *
      weightedGenBatchVal w9 γ) + 2 ^ 3 * weightedGenBatchVal w10 γ) + 2 ^ 3 *
      weightedGenBatchVal w11 γ) = slot2AxisSum w γ := by
  intro w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  have hw1 := (wChunk_218_146_s1_val (mPayload := mPayload) w γ)
  have hw2 := (wChunk_218_146_s2_val (mPayload := mPayload) w γ)
  have hw3 := (wChunk_218_146_s3_val (mPayload := mPayload) w γ)
  have hw4 := (wChunk_218_146_s4_val (mPayload := mPayload) w γ)
  have hw5 := (wChunk_218_146_s5_val (mPayload := mPayload) w γ)
  have hw6 := (wChunk_218_146_s6_val (mPayload := mPayload) w γ)
  have hw7 := (wChunk_218_146_s7_val (mPayload := mPayload) w γ)
  have hw8 := (wChunk_218_146_s8_val (mPayload := mPayload) w γ)
  have hw9 := (wChunk_218_146_s9_val (mPayload := mPayload) w γ)
  have hw10 := (wChunk_218_146_s10_val (mPayload := mPayload) w γ)
  have hw11 := (wChunk_218_146_s11_val (mPayload := mPayload) w γ)
  rw [hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11]
  simp only [corePlaneSliceSum_zero, mul_zero, add_zero]
  have hp0 : corePlaneSliceSum w 0 γ 0 218 = (corePlaneSliceSum w 0 γ 0 63 +
    (corePlaneSliceSum w 0 γ 63 64 + (corePlaneSliceSum w 0 γ 127 90 +
    corePlaneSliceSum w 0 γ 217 1))) := by
    rw [corePlaneSliceSum_split w 0 γ 0 63 155 218 63 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 0 γ 63 64 91 155 127 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 0 γ 127 90 1 91 217 rfl rfl (by decide)]
  have hp1 : corePlaneSliceSum w 1 γ 0 218 = (corePlaneSliceSum w 1 γ 0 19 +
    (corePlaneSliceSum w 1 γ 19 127 + (corePlaneSliceSum w 1 γ 146 38 +
    corePlaneSliceSum w 1 γ 184 34))) := by
    rw [corePlaneSliceSum_split w 1 γ 0 19 199 218 19 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 1 γ 19 127 72 199 146 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 1 γ 146 38 34 72 184 rfl rfl (by decide)]
  have hp2 : corePlaneSliceSum w 2 γ 0 218 = (corePlaneSliceSum w 2 γ 0 109 +
    corePlaneSliceSum w 2 γ 109 109) := by
    rw [corePlaneSliceSum_split w 2 γ 0 109 109 218 109 rfl rfl (by decide)]
  have hp3 : corePlaneSliceSum w 3 γ 0 218 = (corePlaneSliceSum w 3 γ 0 1 +
    (corePlaneSliceSum w 3 γ 1 38 + (corePlaneSliceSum w 3 γ 39 56 +
    (corePlaneSliceSum w 3 γ 95 108 + (corePlaneSliceSum w 3 γ 203 10 +
    corePlaneSliceSum w 3 γ 213 5))))) := by
    rw [corePlaneSliceSum_split w 3 γ 0 1 217 218 1 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 1 38 179 217 39 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 39 56 123 179 95 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 95 108 15 123 203 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 203 10 5 15 213 rfl rfl (by decide)]
  have hp4 : corePlaneSliceSum w 4 γ 0 218 = (corePlaneSliceSum w 4 γ 0 109 +
    (corePlaneSliceSum w 4 γ 109 80 + (corePlaneSliceSum w 4 γ 189 2 +
    (corePlaneSliceSum w 4 γ 191 21 + corePlaneSliceSum w 4 γ 212 6)))) := by
    rw [corePlaneSliceSum_split w 4 γ 0 109 109 218 109 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 4 γ 109 80 29 109 189 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 4 γ 189 2 27 29 191 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 4 γ 191 21 6 27 212 rfl rfl (by decide)]
  have hp5 : corePlaneSliceSum w 5 γ 0 218 = (corePlaneSliceSum w 5 γ 0 10 +
    (corePlaneSliceSum w 5 γ 10 36 + (corePlaneSliceSum w 5 γ 46 115 +
    corePlaneSliceSum w 5 γ 161 57))) := by
    rw [corePlaneSliceSum_split w 5 γ 0 10 208 218 10 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 5 γ 10 36 172 208 46 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 5 γ 46 115 57 172 161 rfl rfl (by decide)]
  rw [slot2AxisSum_eq_bitPlane_sum_core w γ]
  rw [hp0, hp1, hp2, hp3, hp4, hp5]
  omega
/-- Forward 218-electron stream circuit (`146 ≤ mWork`, `5208 T`, `0 TOFF`). -/
noncomputable def dCleanHybridStreamAdd218_146 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 146 ≤ mWork) : DynamicCircuit Var n :=
  let s1 :=
    dStep1XorK v wcsa00Spec (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork (disj_slice14
    hCSum 0 6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_146_s1 hmWork)
    (wChunk_218_146_s1 (mPayload := mPayload) w) (wChunk_218_146_s1_inj (mPayload := mPayload) w)
  let s2 :=
    dWeightedModAdd v wcsa01Spec rCore (rSum14.slice 0 7 (by decide)) rWork (disj_slice14 hCSum 0 7
    (by decide)) hCW (disj_slice14_work hSW 0 7 (by decide)) (by decide) (h218_146_s2 hmWork)
    (wChunk_218_146_s2 (mPayload := mPayload) w) (wChunk_218_146_s2_inj (mPayload := mPayload) w)
  let s3 :=
    dWeightedModAdd v wcsa02Spec rCore (rSum14.slice 0 8 (by decide)) rWork (disj_slice14 hCSum 0 8
    (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) (by decide) (h218_146_s3 hmWork)
    (wChunk_218_146_s3 (mPayload := mPayload) w) (wChunk_218_146_s3_inj (mPayload := mPayload) w)
  let s4 :=
    dWeightedModAdd v wcsa03Spec rCore (rSum14.slice 0 9 (by decide)) rWork (disj_slice14 hCSum 0 9
    (by decide)) hCW (disj_slice14_work hSW 0 9 (by decide)) (by decide) (h218_146_s4 hmWork)
    (wChunk_218_146_s4 (mPayload := mPayload) w) (wChunk_218_146_s4_inj (mPayload := mPayload) w)
  let s5 :=
    dWeightedModAdd v wcsa04Spec rCore (rSum14.slice 1 9 (by decide)) rWork (disj_slice14 hCSum 1 9
    (by decide)) hCW (disj_slice14_work hSW 1 9 (by decide)) (by decide) (h218_146_s5 hmWork)
    (wChunk_218_146_s5 (mPayload := mPayload) w) (wChunk_218_146_s5_inj (mPayload := mPayload) w)
  let s6 :=
    dWeightedModAdd v wcsa05Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1
    10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_146_s6 hmWork)
    (wChunk_218_146_s6 (mPayload := mPayload) w) (wChunk_218_146_s6_inj (mPayload := mPayload) w)
  let s7 :=
    dWeightedModAdd v wcsa04Spec rCore (rSum14.slice 3 9 (by decide)) rWork (disj_slice14 hCSum 3 9
    (by decide)) hCW (disj_slice14_work hSW 3 9 (by decide)) (by decide) (h218_146_s7 hmWork)
    (wChunk_218_146_s7 (mPayload := mPayload) w) (wChunk_218_146_s7_inj (mPayload := mPayload) w)
  let s8 :=
    dWeightedModAdd v wcsa06Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s8 hmWork)
    (wChunk_218_146_s8 (mPayload := mPayload) w) (wChunk_218_146_s8_inj (mPayload := mPayload) w)
  let s9 :=
    dWeightedModAdd v wcsa07Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s9 hmWork)
    (wChunk_218_146_s9 (mPayload := mPayload) w) (wChunk_218_146_s9_inj (mPayload := mPayload) w)
  let s10 :=
    dWeightedModAdd v wcsa08Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3
    11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s10 hmWork)
    (wChunk_218_146_s10 (mPayload := mPayload) w) (wChunk_218_146_s10_inj (mPayload := mPayload) w)
  let s11 :=
    dWeightedModAdd v wcsa09Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3
    11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s11 hmWork)
    (wChunk_218_146_s11 (mPayload := mPayload) w) (wChunk_218_146_s11_inj (mPayload := mPayload) w)
  (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq s1 s2) s3) s4) s5) s6) s7) s8) s9)
    s10) s11)
/-- Inverse 218-electron stream circuit (`146 ≤ mWork`, `5208 T`, `0 TOFF`). -/
noncomputable def dCleanHybridStreamInv218_146 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 146 ≤ mWork) : DynamicCircuit Var n :=
  let s1 :=
    dStep1XorK v wcsa00Spec (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork (disj_slice14
    hCSum 0 6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_146_s1 hmWork)
    (wChunk_218_146_s1 (mPayload := mPayload) w) (wChunk_218_146_s1_inj (mPayload := mPayload) w)
  let s2 :=
    dWeightedModInv v wcsa01Spec rCore (rSum14.slice 0 7 (by decide)) rWork (disj_slice14 hCSum 0 7
    (by decide)) hCW (disj_slice14_work hSW 0 7 (by decide)) (by decide) (h218_146_s2 hmWork)
    (wChunk_218_146_s2 (mPayload := mPayload) w) (wChunk_218_146_s2_inj (mPayload := mPayload) w)
  let s3 :=
    dWeightedModInv v wcsa02Spec rCore (rSum14.slice 0 8 (by decide)) rWork (disj_slice14 hCSum 0 8
    (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) (by decide) (h218_146_s3 hmWork)
    (wChunk_218_146_s3 (mPayload := mPayload) w) (wChunk_218_146_s3_inj (mPayload := mPayload) w)
  let s4 :=
    dWeightedModInv v wcsa03Spec rCore (rSum14.slice 0 9 (by decide)) rWork (disj_slice14 hCSum 0 9
    (by decide)) hCW (disj_slice14_work hSW 0 9 (by decide)) (by decide) (h218_146_s4 hmWork)
    (wChunk_218_146_s4 (mPayload := mPayload) w) (wChunk_218_146_s4_inj (mPayload := mPayload) w)
  let s5 :=
    dWeightedModInv v wcsa04Spec rCore (rSum14.slice 1 9 (by decide)) rWork (disj_slice14 hCSum 1 9
    (by decide)) hCW (disj_slice14_work hSW 1 9 (by decide)) (by decide) (h218_146_s5 hmWork)
    (wChunk_218_146_s5 (mPayload := mPayload) w) (wChunk_218_146_s5_inj (mPayload := mPayload) w)
  let s6 :=
    dWeightedModInv v wcsa05Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1
    10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_146_s6 hmWork)
    (wChunk_218_146_s6 (mPayload := mPayload) w) (wChunk_218_146_s6_inj (mPayload := mPayload) w)
  let s7 :=
    dWeightedModInv v wcsa04Spec rCore (rSum14.slice 3 9 (by decide)) rWork (disj_slice14 hCSum 3 9
    (by decide)) hCW (disj_slice14_work hSW 3 9 (by decide)) (by decide) (h218_146_s7 hmWork)
    (wChunk_218_146_s7 (mPayload := mPayload) w) (wChunk_218_146_s7_inj (mPayload := mPayload) w)
  let s8 :=
    dWeightedModInv v wcsa06Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s8 hmWork)
    (wChunk_218_146_s8 (mPayload := mPayload) w) (wChunk_218_146_s8_inj (mPayload := mPayload) w)
  let s9 :=
    dWeightedModInv v wcsa07Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s9 hmWork)
    (wChunk_218_146_s9 (mPayload := mPayload) w) (wChunk_218_146_s9_inj (mPayload := mPayload) w)
  let s10 :=
    dWeightedModInv v wcsa08Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3
    11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s10 hmWork)
    (wChunk_218_146_s10 (mPayload := mPayload) w) (wChunk_218_146_s10_inj (mPayload := mPayload) w)
  let s11 :=
    dWeightedModInv v wcsa09Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3
    11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s11 hmWork)
    (wChunk_218_146_s11 (mPayload := mPayload) w) (wChunk_218_146_s11_inj (mPayload := mPayload) w)
  (.seq s11 (.seq s10 (.seq s9 (.seq s8 (.seq s7 (.seq s6 (.seq s5 (.seq s4 (.seq s3 (.seq s2
    s1))))))))))
/-- Ideal 218-electron stream unitary for Variant `218_146`. -/
noncomputable def uHybridStream218_146 {mPayload : ℕ} (w : Fin 3) : Unitary (2 ^ (fullSysCoreWires
    mPayload + 14)) :=
  let u1 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 6 (by decide)).embedUnitary (uBitXor
    (fullSysCoreWires mPayload) 6 (weightedGenBatchVal (wChunk_218_146_s1 (mPayload :=
    mPayload) w)))
  let u2 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 7 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 7 (weightedGenBatchVal (wChunk_218_146_s2 (mPayload :=
    mPayload) w)))
  let u3 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 8 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 8 (weightedGenBatchVal (wChunk_218_146_s3 (mPayload :=
    mPayload) w)))
  let u4 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 9 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 9 (weightedGenBatchVal (wChunk_218_146_s4 (mPayload :=
    mPayload) w)))
  let u5 :=
    (selCoreSlice (fullSysCoreWires mPayload) 1 9 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 9 (weightedGenBatchVal (wChunk_218_146_s5 (mPayload :=
    mPayload) w)))
  let u6 :=
    (selCoreSlice (fullSysCoreWires mPayload) 1 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_146_s6 (mPayload :=
    mPayload) w)))
  let u7 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 9 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 9 (weightedGenBatchVal (wChunk_218_146_s7 (mPayload :=
    mPayload) w)))
  let u8 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_146_s8 (mPayload :=
    mPayload) w)))
  let u9 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_146_s9 (mPayload :=
    mPayload) w)))
  let u10 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 11 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 11 (weightedGenBatchVal (wChunk_218_146_s10 (mPayload :=
    mPayload) w)))
  let u11 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 11 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 11 (weightedGenBatchVal (wChunk_218_146_s11 (mPayload :=
    mPayload) w)))
  (u11 * (u10 * (u9 * (u8 * (u7 * (u6 * (u5 * (u4 * (u3 * (u2 * u1))))))))))
theorem dCleanHybridStream218_146_counts {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 146 ≤ mWork) :
    let dFwd := dCleanHybridStreamAdd218_146 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    let dInv := dCleanHybridStreamInv218_146 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    dFwd.count TOFF = 0 ∧ dInv.count TOFF = 0 ∧ dFwd.count T ≤ 5208 ∧ dInv.count T ≤ 5208 := by
  intro dFwd dInv
  have c1 :=
    dStep1XorK_counts v wcsa00Spec (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork
    (disj_slice14 hCSum 0 6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_146_s1
    hmWork) (wChunk_218_146_s1 (mPayload := mPayload) w) (wChunk_218_146_s1_inj (mPayload :=
    mPayload) w)
  have c2 :=
    dWeightedModAdd_counts v wcsa01Spec rCore (rSum14.slice 0 7 (by decide)) rWork (disj_slice14
    hCSum 0 7 (by decide)) hCW (disj_slice14_work hSW 0 7 (by decide)) (by decide) (h218_146_s2
    hmWork) (wChunk_218_146_s2 (mPayload := mPayload) w) (wChunk_218_146_s2_inj (mPayload :=
    mPayload) w)
  have c3 :=
    dWeightedModAdd_counts v wcsa02Spec rCore (rSum14.slice 0 8 (by decide)) rWork (disj_slice14
    hCSum 0 8 (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) (by decide) (h218_146_s3
    hmWork) (wChunk_218_146_s3 (mPayload := mPayload) w) (wChunk_218_146_s3_inj (mPayload :=
    mPayload) w)
  have c4 :=
    dWeightedModAdd_counts v wcsa03Spec rCore (rSum14.slice 0 9 (by decide)) rWork (disj_slice14
    hCSum 0 9 (by decide)) hCW (disj_slice14_work hSW 0 9 (by decide)) (by decide) (h218_146_s4
    hmWork) (wChunk_218_146_s4 (mPayload := mPayload) w) (wChunk_218_146_s4_inj (mPayload :=
    mPayload) w)
  have c5 :=
    dWeightedModAdd_counts v wcsa04Spec rCore (rSum14.slice 1 9 (by decide)) rWork (disj_slice14
    hCSum 1 9 (by decide)) hCW (disj_slice14_work hSW 1 9 (by decide)) (by decide) (h218_146_s5
    hmWork) (wChunk_218_146_s5 (mPayload := mPayload) w) (wChunk_218_146_s5_inj (mPayload :=
    mPayload) w)
  have c6 :=
    dWeightedModAdd_counts v wcsa05Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14
    hCSum 1 10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_146_s6
    hmWork) (wChunk_218_146_s6 (mPayload := mPayload) w) (wChunk_218_146_s6_inj (mPayload :=
    mPayload) w)
  have c7 :=
    dWeightedModAdd_counts v wcsa04Spec rCore (rSum14.slice 3 9 (by decide)) rWork (disj_slice14
    hCSum 3 9 (by decide)) hCW (disj_slice14_work hSW 3 9 (by decide)) (by decide) (h218_146_s7
    hmWork) (wChunk_218_146_s7 (mPayload := mPayload) w) (wChunk_218_146_s7_inj (mPayload :=
    mPayload) w)
  have c8 :=
    dWeightedModAdd_counts v wcsa06Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14
    hCSum 3 10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s8
    hmWork) (wChunk_218_146_s8 (mPayload := mPayload) w) (wChunk_218_146_s8_inj (mPayload :=
    mPayload) w)
  have c9 :=
    dWeightedModAdd_counts v wcsa07Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14
    hCSum 3 10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s9
    hmWork) (wChunk_218_146_s9 (mPayload := mPayload) w) (wChunk_218_146_s9_inj (mPayload :=
    mPayload) w)
  have c10 :=
    dWeightedModAdd_counts v wcsa08Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14
    hCSum 3 11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s10
    hmWork) (wChunk_218_146_s10 (mPayload := mPayload) w) (wChunk_218_146_s10_inj (mPayload :=
    mPayload) w)
  have c11 :=
    dWeightedModAdd_counts v wcsa09Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14
    hCSum 3 11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s11
    hmWork) (wChunk_218_146_s11 (mPayload := mPayload) w) (wChunk_218_146_s11_inj (mPayload :=
    mPayload) w)
  dsimp only [dFwd, dInv, dCleanHybridStreamAdd218_146, dCleanHybridStreamInv218_146]
  simp only [count_seq_eq]
  refine ⟨by rw [c1.1, c2.1, c3.1, c4.1, c5.1, c6.1, c7.1, c8.1, c9.1, c10.1, c11.1], by
    rw [c11.2.1, c10.2.1, c9.2.1, c8.2.1, c7.2.1, c6.2.1, c5.2.1, c4.2.1, c3.2.1, c2.2.1, c1.1], ?_,
    ?_⟩
  · have h1 := c1.2;
    have h2 := c2.2.2.1;
    have h3 := c3.2.2.1;
    have h4 := c4.2.2.1;
    have h5 :=
      c5.2.2.1; have h6 := c6.2.2.1; have h7 := c7.2.2.1; have h8 := c8.2.2.1; have h9 :=
      c9.2.2.1; have h10 := c10.2.2.1; have h11 := c11.2.2.1; omega
  · have h1 := c1.2;
    have h2 := c2.2.2.2;
    have h3 := c3.2.2.2;
    have h4 := c4.2.2.2;
    have h5 :=
      c5.2.2.2; have h6 := c6.2.2.2; have h7 := c7.2.2.2; have h8 := c8.2.2.2; have h9 :=
      c9.2.2.2; have h10 := c10.2.2.2; have h11 := c11.2.2.2; omega
theorem uHybridStream218_146_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)]
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) :
    ∀ β₀ : Fin n → ZMod 2, (∀ i : Fin 14, β₀ (rSum14 i) = 0) →
      ∃ β : Fin n → ZMod 2,
        ((rCore.concat rSum14 hCSum).embedUnitary (uHybridStream218_146 w)).1.mulVec
          (basisKet β₀) = basisKet β ∧
        (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧
        (∀ i : Fin 14,
          β (rSum14 i) = if (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) :=
            by
  intro β₀ hz
  let w1 := (wChunk_218_146_s1 (mPayload := mPayload) w)
  have hb1 : weightedGenBatchVal w1 (fun q ↦ β₀ (rCore q)) ≤ 63 := weightedGenBatchVal_le w1 _
  let w2 := (wChunk_218_146_s2 (mPayload := mPayload) w)
  have hb2 : weightedGenBatchVal w2 (fun q ↦ β₀ (rCore q)) ≤ 64 := weightedGenBatchVal_le w2 _
  let w3 := (wChunk_218_146_s3 (mPayload := mPayload) w)
  have hb3 : weightedGenBatchVal w3 (fun q ↦ β₀ (rCore q)) ≤ 128 := weightedGenBatchVal_le w3 _
  let w4 := (wChunk_218_146_s4 (mPayload := mPayload) w)
  have hb4 : weightedGenBatchVal w4 (fun q ↦ β₀ (rCore q)) ≤ 255 := weightedGenBatchVal_le w4 _
  let w5 := (wChunk_218_146_s5 (mPayload := mPayload) w)
  have hb5 : weightedGenBatchVal w5 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w5 _
  let w6 := (wChunk_218_146_s6 (mPayload := mPayload) w)
  have hb6 : weightedGenBatchVal w6 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w6 _
  let w7 := (wChunk_218_146_s7 (mPayload := mPayload) w)
  have hb7 : weightedGenBatchVal w7 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w7 _
  let w8 := (wChunk_218_146_s8 (mPayload := mPayload) w)
  have hb8 : weightedGenBatchVal w8 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w8 _
  let w9 := (wChunk_218_146_s9 (mPayload := mPayload) w)
  have hb9 : weightedGenBatchVal w9 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w9 _
  let w10 := (wChunk_218_146_s10 (mPayload := mPayload) w)
  have hb10 : weightedGenBatchVal w10 (fun q ↦ β₀ (rCore q)) ≤ 512 := weightedGenBatchVal_le w10 _
  let w11 := (wChunk_218_146_s11 (mPayload := mPayload) w)
  have hb11 : weightedGenBatchVal w11 (fun q ↦ β₀ (rCore q)) ≤ 245 := weightedGenBatchVal_le w11 _
  obtain ⟨b1, hket1, hInv1⟩ :=
    accInvar_step1_bitXorK rCore rSum14 hCSum 6 (by decide) (weightedGenBatchVal w1) β₀
    (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨b2, hket2, hInv2⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 0 7 (by decide) (weightedGenBatchVal w2) _ β₀ b1
    hInv1 (by omega) (by omega)
  obtain ⟨b3, hket3, hInv3⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 0 8 (by decide) (weightedGenBatchVal w3) _ β₀ b2
    hInv2 (by omega) (by omega)
  obtain ⟨b4, hket4, hInv4⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 0 9 (by decide) (weightedGenBatchVal w4) _ β₀ b3
    hInv3 (by omega) (by omega)
  obtain ⟨b5, hket5, hInv5⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 1 9 (by decide) (weightedGenBatchVal w5) _ β₀ b4
    hInv4 (by omega) (by omega)
  obtain ⟨b6, hket6, hInv6⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 1 10 (by decide) (weightedGenBatchVal w6) _ β₀ b5
    hInv5 (by omega) (by omega)
  obtain ⟨b7, hket7, hInv7⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 9 (by decide) (weightedGenBatchVal w7) _ β₀ b6
    hInv6 (by omega) (by omega)
  obtain ⟨b8, hket8, hInv8⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide) (weightedGenBatchVal w8) _ β₀ b7
    hInv7 (by omega) (by omega)
  obtain ⟨b9, hket9, hInv9⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide) (weightedGenBatchVal w9) _ β₀ b8
    hInv8 (by omega) (by omega)
  obtain ⟨b10, hket10, hInv10⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide) (weightedGenBatchVal w10) _ β₀ b9
    hInv9 (by omega) (by omega)
  obtain ⟨b11, hket11, hInv11⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide) (weightedGenBatchVal w11) _ β₀ b10
    hInv10 (by omega) (by omega)
  have hSumEq := hybrid218_146_batch_eq_axisSum w (fun q ↦ β₀ (rCore q))
  dsimp only at hSumEq
  rw [hSumEq] at hInv11
  refine ⟨b11, ?_, hInv11.1, hInv11.2⟩
  simp only [uHybridStream218_146, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket1, hket2, hket3, hket4, hket5, hket6, hket7, hket8, hket9, hket10, hket11]
theorem dCleanHybridStream218_146_cleanPair_explicit {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 146 ≤ mWork) :
    CleanComputePair rCore rSum14 rWork hCSum (uHybridStream218_146 w)
      (fun x i ↦ if (slot2AxisSum w x).testBit i.val then 1 else 0)
      (dCleanHybridStreamAdd218_146 v w rCore rSum14 rWork hCSum hCW hSW hmWork)
      (dCleanHybridStreamInv218_146 v w rCore rSum14 rWork hCSum hCW hSW hmWork) := by
  have hActW : (rCore.concat rSum14 hCSum).DisjointWires rWork :=
    QRegExt.disjointWires_concat_left hCW hSW
  have p1 :=
    liftCleanPair_slice14 hCSum 0 6 (by decide) (dStep1XorK_realizesPair v wcsa00Spec (by decide)
    wcsa00Spec_cinWire (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork (disj_slice14 hCSum 0
    6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_146_s1 hmWork)
    (wChunk_218_146_s1 (mPayload := mPayload) w) (wChunk_218_146_s1_inj (mPayload := mPayload) w))
  have p2 :=
    liftCleanPair_slice14 hCSum 0 7 (by decide) (dWeightedModAdd_realizesPair v wcsa01Spec rCore
    (rSum14.slice 0 7 (by decide)) rWork (disj_slice14 hCSum 0 7 (by decide)) hCW (disj_slice14_work
    hSW 0 7 (by decide)) (by decide) (h218_146_s2 hmWork) (wChunk_218_146_s2 (mPayload :=
    mPayload) w) (wChunk_218_146_s2_inj (mPayload := mPayload) w))
  have p3 :=
    liftCleanPair_slice14 hCSum 0 8 (by decide) (dWeightedModAdd_realizesPair v wcsa02Spec rCore
    (rSum14.slice 0 8 (by decide)) rWork (disj_slice14 hCSum 0 8 (by decide)) hCW (disj_slice14_work
    hSW 0 8 (by decide)) (by decide) (h218_146_s3 hmWork) (wChunk_218_146_s3 (mPayload :=
    mPayload) w) (wChunk_218_146_s3_inj (mPayload := mPayload) w))
  have p4 :=
    liftCleanPair_slice14 hCSum 0 9 (by decide) (dWeightedModAdd_realizesPair v wcsa03Spec rCore
    (rSum14.slice 0 9 (by decide)) rWork (disj_slice14 hCSum 0 9 (by decide)) hCW (disj_slice14_work
    hSW 0 9 (by decide)) (by decide) (h218_146_s4 hmWork) (wChunk_218_146_s4 (mPayload :=
    mPayload) w) (wChunk_218_146_s4_inj (mPayload := mPayload) w))
  have p5 :=
    liftCleanPair_slice14 hCSum 1 9 (by decide) (dWeightedModAdd_realizesPair v wcsa04Spec rCore
    (rSum14.slice 1 9 (by decide)) rWork (disj_slice14 hCSum 1 9 (by decide)) hCW (disj_slice14_work
    hSW 1 9 (by decide)) (by decide) (h218_146_s5 hmWork) (wChunk_218_146_s5 (mPayload :=
    mPayload) w) (wChunk_218_146_s5_inj (mPayload := mPayload) w))
  have p6 :=
    liftCleanPair_slice14 hCSum 1 10 (by decide) (dWeightedModAdd_realizesPair v wcsa05Spec rCore
    (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1 10 (by decide)) hCW
    (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_146_s6 hmWork) (wChunk_218_146_s6
    (mPayload := mPayload) w) (wChunk_218_146_s6_inj (mPayload := mPayload) w))
  have p7 :=
    liftCleanPair_slice14 hCSum 3 9 (by decide) (dWeightedModAdd_realizesPair v wcsa04Spec rCore
    (rSum14.slice 3 9 (by decide)) rWork (disj_slice14 hCSum 3 9 (by decide)) hCW (disj_slice14_work
    hSW 3 9 (by decide)) (by decide) (h218_146_s7 hmWork) (wChunk_218_146_s7 (mPayload :=
    mPayload) w) (wChunk_218_146_s7_inj (mPayload := mPayload) w))
  have p8 :=
    liftCleanPair_slice14 hCSum 3 10 (by decide) (dWeightedModAdd_realizesPair v wcsa06Spec rCore
    (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3 10 (by decide)) hCW
    (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s8 hmWork) (wChunk_218_146_s8
    (mPayload := mPayload) w) (wChunk_218_146_s8_inj (mPayload := mPayload) w))
  have p9 :=
    liftCleanPair_slice14 hCSum 3 10 (by decide) (dWeightedModAdd_realizesPair v wcsa07Spec rCore
    (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3 10 (by decide)) hCW
    (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_146_s9 hmWork) (wChunk_218_146_s9
    (mPayload := mPayload) w) (wChunk_218_146_s9_inj (mPayload := mPayload) w))
  have p10 :=
    liftCleanPair_slice14 hCSum 3 11 (by decide) (dWeightedModAdd_realizesPair v wcsa08Spec rCore
    (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3 11 (by decide)) hCW
    (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s10 hmWork) (wChunk_218_146_s10
    (mPayload := mPayload) w) (wChunk_218_146_s10_inj (mPayload := mPayload) w))
  have p11 :=
    liftCleanPair_slice14 hCSum 3 11 (by decide) (dWeightedModAdd_realizesPair v wcsa09Spec rCore
    (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3 11 (by decide)) hCW
    (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_146_s11 hmWork) (wChunk_218_146_s11
    (mPayload := mPayload) w) (wChunk_218_146_s11_inj (mPayload := mPayload) w))
  have pAll :=
    ((((((((((p1.seq hActW p2).seq hActW p3).seq hActW p4).seq hActW p5).seq hActW p6).seq hActW
    p7).seq hActW p8).seq hActW p9).seq hActW p10).seq hActW p11)
  change RealizesCleanPair (rCore.concat rSum14 hCSum) rWork (uHybridStream218_146 w) _ _ at pAll
  exact ⟨pAll, uHybridStream218_146_compute_ket w rCore rSum14 hCSum⟩
attribute [irreducible] dCleanHybridStreamAdd218_146 dCleanHybridStreamInv218_146
  uHybridStream218_146
-- ============================================================================
-- Variant `218_128`: N=218 electrons, mWork >= 128, 1303 TempAnds = 5212 T/axis (12 layers)
-- ============================================================================
theorem h218_128_s1 {mWork : ℕ} (hm : 128 ≤ mWork) : 57 ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `1`. -/
def wChunk_218_128_s1 {mPayload : ℕ} (w : Fin 3) : Fin (63 + 0 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 0 63 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s1_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s1
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 0 63 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by
    decide) (by decide)
theorem wChunk_218_128_s1_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s1 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 0 63 +
      2 * corePlaneSliceSum w 1 γ 0 0 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 0 63 0 0 0 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s1
theorem h218_128_s2 {mWork : ℕ} (hm : 128 ≤ mWork) : 57 + (7 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `2`. -/
def wChunk_218_128_s2 {mPayload : ℕ} (w : Fin 3) : Fin (64 + 0 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 63 64 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s2_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s2
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 63 64 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by
    decide) (by decide)
theorem wChunk_218_128_s2_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s2 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 63 64 +
      2 * corePlaneSliceSum w 1 γ 0 0 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 63 64 0 0 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s2
theorem h218_128_s3 {mWork : ℕ} (hm : 128 ≤ mWork) : 101 + (8 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `3`. -/
def wChunk_218_128_s3 {mPayload : ℕ} (w : Fin 3) : Fin (90 + 19 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 127 90 0 19 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s3_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s3
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 127 90 0 19 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s3_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s3 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 127 90 +
      2 * corePlaneSliceSum w 1 γ 0 19 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 127 90 0 19 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s3
theorem h218_128_s4 {mWork : ℕ} (hm : 128 ≤ mWork) : 120 + (9 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `4`. -/
def wChunk_218_128_s4 {mPayload : ℕ} (w : Fin 3) : Fin (1 + 127 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 0 217 1 19 127 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s4_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s4
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 0 217 1 19 127 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s4_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s4 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 0 γ 217 1 +
      2 * corePlaneSliceSum w 1 γ 19 127 +
      4 * corePlaneSliceSum w 2 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 0 1 2 rfl rfl 217 1 19 127 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s4
theorem h218_128_s5 {mWork : ℕ} (hm : 128 ≤ mWork) : 120 + (9 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `5`. -/
def wChunk_218_128_s5 {mPayload : ℕ} (w : Fin 3) : Fin (2 + 127 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 1 146 2 0 127 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s5_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s5
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 1 146 2 0 127 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s5_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s5 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 1 γ 146 2 +
      2 * corePlaneSliceSum w 2 γ 0 127 +
      4 * corePlaneSliceSum w 3 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 1 2 3 rfl rfl 146 2 0 127 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s5
theorem h218_128_s6 {mWork : ℕ} (hm : 128 ≤ mWork) : 119 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `6`. -/
def wChunk_218_128_s6 {mPayload : ℕ} (w : Fin 3) : Fin (38 + 71 + 19) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 1 148 38 127 71 0 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s6_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s6
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 1 148 38 127 71 0 19 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s6_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s6 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 1 γ 148 38 +
      2 * corePlaneSliceSum w 2 γ 127 71 +
      4 * corePlaneSliceSum w 3 γ 0 19 :=
  weightedGenBatchVal_flexCoreChunk w 1 2 3 rfl rfl 148 38 127 71 0 19 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s6
theorem h218_128_s7 {mWork : ℕ} (hm : 128 ≤ mWork) : 89 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `7`. -/
def wChunk_218_128_s7 {mPayload : ℕ} (w : Fin 3) : Fin (32 + 20 + 46) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 1 186 32 198 20 19 46 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
theorem wChunk_218_128_s7_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s7
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 1 186 32 198 20 19 46 (by decide) (by decide) (by decide) (by
    decide) (by decide) (by decide)
theorem wChunk_218_128_s7_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s7 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 1 γ 186 32 +
      2 * corePlaneSliceSum w 2 γ 198 20 +
      4 * corePlaneSliceSum w 3 γ 19 46 :=
  weightedGenBatchVal_flexCoreChunk w 1 2 3 rfl rfl 186 32 198 20 19 46 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s7
theorem h218_128_s8 {mWork : ℕ} (hm : 128 ≤ mWork) : 120 + (9 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `8`. -/
def wChunk_218_128_s8 {mPayload : ℕ} (w : Fin 3) : Fin (1 + 127 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 65 1 0 127 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s8_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s8
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 65 1 0 127 0 0 (by decide) (by decide) (by decide) (by decide) (by
    decide) (by decide)
theorem wChunk_218_128_s8_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s8 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 65 1 +
      2 * corePlaneSliceSum w 4 γ 0 127 +
      4 * corePlaneSliceSum w 5 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 65 1 0 127 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s8
theorem h218_128_s9 {mWork : ℕ} (hm : 128 ≤ mWork) : 119 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `9`. -/
def wChunk_218_128_s9 {mPayload : ℕ} (w : Fin 3) : Fin (38 + 71 + 19) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 66 38 127 71 0 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s9_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s9
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 66 38 127 71 0 19 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s9_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s9 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 66 38 +
      2 * corePlaneSliceSum w 4 γ 127 71 +
      4 * corePlaneSliceSum w 5 γ 0 19 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 66 38 127 71 0 19 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s9
theorem h218_128_s10 {mWork : ℕ} (hm : 128 ≤ mWork) : 119 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `10`. -/
def wChunk_218_128_s10 {mPayload : ℕ} (w : Fin 3) : Fin (80 + 8 + 40) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 104 80 198 8 19 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s10_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s10
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 104 80 198 8 19 40 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s10_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s10 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 104 80 +
      2 * corePlaneSliceSum w 4 γ 198 8 +
      4 * corePlaneSliceSum w 5 γ 19 40 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 104 80 198 8 19 40 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s10
theorem h218_128_s11 {mWork : ℕ} (hm : 128 ≤ mWork) : 86 + (11 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `11`. -/
def wChunk_218_128_s11 {mPayload : ℕ} (w : Fin 3) : Fin (34 + 11 + 50) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 3 184 34 206 11 59 50 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
theorem wChunk_218_128_s11_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s11
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 3 184 34 206 11 59 50 (by decide) (by decide) (by decide) (by
    decide) (by decide) (by decide)
theorem wChunk_218_128_s11_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s11 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 3 γ 184 34 +
      2 * corePlaneSliceSum w 4 γ 206 11 +
      4 * corePlaneSliceSum w 5 γ 59 50 :=
  weightedGenBatchVal_flexCoreChunk w 3 4 5 rfl rfl 184 34 206 11 59 50 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s11
theorem h218_128_s12 {mWork : ℕ} (hm : 128 ≤ mWork) : 104 + (10 - 1) ≤ mWork := by omega
/-- Chunk wire map for Variant `218_128`, Wave `12`. -/
def wChunk_218_128_s12 {mPayload : ℕ} (w : Fin 3) : Fin (1 + 109 + 0) →
    Wire (fullSysCoreWires mPayload) :=
  flexCoreChunkWire (mPayload :=
    mPayload) w 4 217 1 109 109 0 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by
    decide)
theorem wChunk_218_128_s12_inj {mPayload : ℕ} (w : Fin 3) : Function.Injective (wChunk_218_128_s12
    (mPayload := mPayload) w) :=
  flexCoreChunkWire_injective w 4 217 1 109 109 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
theorem wChunk_218_128_s12_val {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires
    mPayload)) :
    weightedGenBatchVal (wChunk_218_128_s12 (mPayload := mPayload) w) γ =
      corePlaneSliceSum w 4 γ 217 1 +
      2 * corePlaneSliceSum w 5 γ 109 109 +
      4 * corePlaneSliceSum w 6 γ 0 0 :=
  weightedGenBatchVal_flexCoreChunk w 4 5 6 rfl rfl 217 1 109 109 0 0 (by decide) (by decide) (by
    decide) (by decide) (by decide) (by decide) γ
attribute [irreducible] wChunk_218_128_s12
theorem hybrid218_128_batch_eq_axisSum {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment
    (fullSysCoreWires mPayload)) :
    let w1 := (wChunk_218_128_s1 (mPayload := mPayload) w)
    let w2 := (wChunk_218_128_s2 (mPayload := mPayload) w)
    let w3 := (wChunk_218_128_s3 (mPayload := mPayload) w)
    let w4 := (wChunk_218_128_s4 (mPayload := mPayload) w)
    let w5 := (wChunk_218_128_s5 (mPayload := mPayload) w)
    let w6 := (wChunk_218_128_s6 (mPayload := mPayload) w)
    let w7 := (wChunk_218_128_s7 (mPayload := mPayload) w)
    let w8 := (wChunk_218_128_s8 (mPayload := mPayload) w)
    let w9 := (wChunk_218_128_s9 (mPayload := mPayload) w)
    let w10 := (wChunk_218_128_s10 (mPayload := mPayload) w)
    let w11 := (wChunk_218_128_s11 (mPayload := mPayload) w)
    let w12 := (wChunk_218_128_s12 (mPayload := mPayload) w)
    (((((((((((weightedGenBatchVal w1 γ + 2 ^ 0 * weightedGenBatchVal w2 γ) + 2 ^ 0 *
      weightedGenBatchVal w3 γ) + 2 ^ 0 * weightedGenBatchVal w4 γ) + 2 ^ 1 *
      weightedGenBatchVal w5 γ) + 2 ^ 1 * weightedGenBatchVal w6 γ) + 2 ^ 1 *
      weightedGenBatchVal w7 γ) + 2 ^ 3 * weightedGenBatchVal w8 γ) + 2 ^ 3 *
      weightedGenBatchVal w9 γ) + 2 ^ 3 * weightedGenBatchVal w10 γ) + 2 ^ 3 *
      weightedGenBatchVal w11 γ) + 2 ^ 4 * weightedGenBatchVal w12 γ) = slot2AxisSum w γ := by
  intro w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
  have hw1 := (wChunk_218_128_s1_val (mPayload := mPayload) w γ)
  have hw2 := (wChunk_218_128_s2_val (mPayload := mPayload) w γ)
  have hw3 := (wChunk_218_128_s3_val (mPayload := mPayload) w γ)
  have hw4 := (wChunk_218_128_s4_val (mPayload := mPayload) w γ)
  have hw5 := (wChunk_218_128_s5_val (mPayload := mPayload) w γ)
  have hw6 := (wChunk_218_128_s6_val (mPayload := mPayload) w γ)
  have hw7 := (wChunk_218_128_s7_val (mPayload := mPayload) w γ)
  have hw8 := (wChunk_218_128_s8_val (mPayload := mPayload) w γ)
  have hw9 := (wChunk_218_128_s9_val (mPayload := mPayload) w γ)
  have hw10 := (wChunk_218_128_s10_val (mPayload := mPayload) w γ)
  have hw11 := (wChunk_218_128_s11_val (mPayload := mPayload) w γ)
  have hw12 := (wChunk_218_128_s12_val (mPayload := mPayload) w γ)
  rw [hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12]
  simp only [corePlaneSliceSum_zero, mul_zero, add_zero]
  have hp0 : corePlaneSliceSum w 0 γ 0 218 = (corePlaneSliceSum w 0 γ 0 63 +
    (corePlaneSliceSum w 0 γ 63 64 + (corePlaneSliceSum w 0 γ 127 90 +
    corePlaneSliceSum w 0 γ 217 1))) := by
    rw [corePlaneSliceSum_split w 0 γ 0 63 155 218 63 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 0 γ 63 64 91 155 127 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 0 γ 127 90 1 91 217 rfl rfl (by decide)]
  have hp1 : corePlaneSliceSum w 1 γ 0 218 = (corePlaneSliceSum w 1 γ 0 19 +
    (corePlaneSliceSum w 1 γ 19 127 + (corePlaneSliceSum w 1 γ 146 2 +
    (corePlaneSliceSum w 1 γ 148 38 + corePlaneSliceSum w 1 γ 186 32)))) := by
    rw [corePlaneSliceSum_split w 1 γ 0 19 199 218 19 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 1 γ 19 127 72 199 146 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 1 γ 146 2 70 72 148 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 1 γ 148 38 32 70 186 rfl rfl (by decide)]
  have hp2 : corePlaneSliceSum w 2 γ 0 218 = (corePlaneSliceSum w 2 γ 0 127 +
    (corePlaneSliceSum w 2 γ 127 71 + corePlaneSliceSum w 2 γ 198 20)) := by
    rw [corePlaneSliceSum_split w 2 γ 0 127 91 218 127 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 2 γ 127 71 20 91 198 rfl rfl (by decide)]
  have hp3 : corePlaneSliceSum w 3 γ 0 218 = (corePlaneSliceSum w 3 γ 0 19 +
    (corePlaneSliceSum w 3 γ 19 46 + (corePlaneSliceSum w 3 γ 65 1 +
    (corePlaneSliceSum w 3 γ 66 38 + (corePlaneSliceSum w 3 γ 104 80 +
    corePlaneSliceSum w 3 γ 184 34))))) := by
    rw [corePlaneSliceSum_split w 3 γ 0 19 199 218 19 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 19 46 153 199 65 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 65 1 152 153 66 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 66 38 114 152 104 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 3 γ 104 80 34 114 184 rfl rfl (by decide)]
  have hp4 : corePlaneSliceSum w 4 γ 0 218 = (corePlaneSliceSum w 4 γ 0 127 +
    (corePlaneSliceSum w 4 γ 127 71 + (corePlaneSliceSum w 4 γ 198 8 +
    (corePlaneSliceSum w 4 γ 206 11 + corePlaneSliceSum w 4 γ 217 1)))) := by
    rw [corePlaneSliceSum_split w 4 γ 0 127 91 218 127 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 4 γ 127 71 20 91 198 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 4 γ 198 8 12 20 206 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 4 γ 206 11 1 12 217 rfl rfl (by decide)]
  have hp5 : corePlaneSliceSum w 5 γ 0 218 = (corePlaneSliceSum w 5 γ 0 19 +
    (corePlaneSliceSum w 5 γ 19 40 + (corePlaneSliceSum w 5 γ 59 50 +
    corePlaneSliceSum w 5 γ 109 109))) := by
    rw [corePlaneSliceSum_split w 5 γ 0 19 199 218 19 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 5 γ 19 40 159 199 59 rfl rfl (by decide)]
    rw [corePlaneSliceSum_split w 5 γ 59 50 109 159 109 rfl rfl (by decide)]
  rw [slot2AxisSum_eq_bitPlane_sum_core w γ]
  rw [hp0, hp1, hp2, hp3, hp4, hp5]
  omega
/-- Forward 218-electron stream circuit (`128 ≤ mWork`, `5212 T`, `0 TOFF`). -/
noncomputable def dCleanHybridStreamAdd218_128 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 128 ≤ mWork) : DynamicCircuit Var n :=
  let s1 :=
    dStep1XorK v wcsa00Spec (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork (disj_slice14
    hCSum 0 6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_128_s1 hmWork)
    (wChunk_218_128_s1 (mPayload := mPayload) w) (wChunk_218_128_s1_inj (mPayload := mPayload) w)
  let s2 :=
    dWeightedModAdd v wcsa01Spec rCore (rSum14.slice 0 7 (by decide)) rWork (disj_slice14 hCSum 0 7
    (by decide)) hCW (disj_slice14_work hSW 0 7 (by decide)) (by decide) (h218_128_s2 hmWork)
    (wChunk_218_128_s2 (mPayload := mPayload) w) (wChunk_218_128_s2_inj (mPayload := mPayload) w)
  let s3 :=
    dWeightedModAdd v wcsa02Spec rCore (rSum14.slice 0 8 (by decide)) rWork (disj_slice14 hCSum 0 8
    (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) (by decide) (h218_128_s3 hmWork)
    (wChunk_218_128_s3 (mPayload := mPayload) w) (wChunk_218_128_s3_inj (mPayload := mPayload) w)
  let s4 :=
    dWeightedModAdd v wcsa03Spec rCore (rSum14.slice 0 9 (by decide)) rWork (disj_slice14 hCSum 0 9
    (by decide)) hCW (disj_slice14_work hSW 0 9 (by decide)) (by decide) (h218_128_s4 hmWork)
    (wChunk_218_128_s4 (mPayload := mPayload) w) (wChunk_218_128_s4_inj (mPayload := mPayload) w)
  let s5 :=
    dWeightedModAdd v wcsa10Spec rCore (rSum14.slice 1 9 (by decide)) rWork (disj_slice14 hCSum 1 9
    (by decide)) hCW (disj_slice14_work hSW 1 9 (by decide)) (by decide) (h218_128_s5 hmWork)
    (wChunk_218_128_s5 (mPayload := mPayload) w) (wChunk_218_128_s5_inj (mPayload := mPayload) w)
  let s6 :=
    dWeightedModAdd v wcsa11Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1
    10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s6 hmWork)
    (wChunk_218_128_s6 (mPayload := mPayload) w) (wChunk_218_128_s6_inj (mPayload := mPayload) w)
  let s7 :=
    dWeightedModAdd v wcsa12Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1
    10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s7 hmWork)
    (wChunk_218_128_s7 (mPayload := mPayload) w) (wChunk_218_128_s7_inj (mPayload := mPayload) w)
  let s8 :=
    dWeightedModAdd v wcsa03Spec rCore (rSum14.slice 3 9 (by decide)) rWork (disj_slice14 hCSum 3 9
    (by decide)) hCW (disj_slice14_work hSW 3 9 (by decide)) (by decide) (h218_128_s8 hmWork)
    (wChunk_218_128_s8 (mPayload := mPayload) w) (wChunk_218_128_s8_inj (mPayload := mPayload) w)
  let s9 :=
    dWeightedModAdd v wcsa11Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s9 hmWork)
    (wChunk_218_128_s9 (mPayload := mPayload) w) (wChunk_218_128_s9_inj (mPayload := mPayload) w)
  let s10 :=
    dWeightedModAdd v wcsa13Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s10 hmWork)
    (wChunk_218_128_s10 (mPayload := mPayload) w) (wChunk_218_128_s10_inj (mPayload := mPayload) w)
  let s11 :=
    dWeightedModAdd v wcsa14Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3
    11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_128_s11 hmWork)
    (wChunk_218_128_s11 (mPayload := mPayload) w) (wChunk_218_128_s11_inj (mPayload := mPayload) w)
  let s12 :=
    dWeightedModAdd v wcsa15Spec rCore (rSum14.slice 4 10 (by decide)) rWork (disj_slice14 hCSum 4
    10 (by decide)) hCW (disj_slice14_work hSW 4 10 (by decide)) (by decide) (h218_128_s12 hmWork)
    (wChunk_218_128_s12 (mPayload := mPayload) w) (wChunk_218_128_s12_inj (mPayload := mPayload) w)
  (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq s1 s2) s3) s4) s5) s6) s7) s8)
    s9) s10) s11) s12)
/-- Inverse 218-electron stream circuit (`128 ≤ mWork`, `5212 T`, `0 TOFF`). -/
noncomputable def dCleanHybridStreamInv218_128 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 128 ≤ mWork) : DynamicCircuit Var n :=
  let s1 :=
    dStep1XorK v wcsa00Spec (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork (disj_slice14
    hCSum 0 6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_128_s1 hmWork)
    (wChunk_218_128_s1 (mPayload := mPayload) w) (wChunk_218_128_s1_inj (mPayload := mPayload) w)
  let s2 :=
    dWeightedModInv v wcsa01Spec rCore (rSum14.slice 0 7 (by decide)) rWork (disj_slice14 hCSum 0 7
    (by decide)) hCW (disj_slice14_work hSW 0 7 (by decide)) (by decide) (h218_128_s2 hmWork)
    (wChunk_218_128_s2 (mPayload := mPayload) w) (wChunk_218_128_s2_inj (mPayload := mPayload) w)
  let s3 :=
    dWeightedModInv v wcsa02Spec rCore (rSum14.slice 0 8 (by decide)) rWork (disj_slice14 hCSum 0 8
    (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) (by decide) (h218_128_s3 hmWork)
    (wChunk_218_128_s3 (mPayload := mPayload) w) (wChunk_218_128_s3_inj (mPayload := mPayload) w)
  let s4 :=
    dWeightedModInv v wcsa03Spec rCore (rSum14.slice 0 9 (by decide)) rWork (disj_slice14 hCSum 0 9
    (by decide)) hCW (disj_slice14_work hSW 0 9 (by decide)) (by decide) (h218_128_s4 hmWork)
    (wChunk_218_128_s4 (mPayload := mPayload) w) (wChunk_218_128_s4_inj (mPayload := mPayload) w)
  let s5 :=
    dWeightedModInv v wcsa10Spec rCore (rSum14.slice 1 9 (by decide)) rWork (disj_slice14 hCSum 1 9
    (by decide)) hCW (disj_slice14_work hSW 1 9 (by decide)) (by decide) (h218_128_s5 hmWork)
    (wChunk_218_128_s5 (mPayload := mPayload) w) (wChunk_218_128_s5_inj (mPayload := mPayload) w)
  let s6 :=
    dWeightedModInv v wcsa11Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1
    10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s6 hmWork)
    (wChunk_218_128_s6 (mPayload := mPayload) w) (wChunk_218_128_s6_inj (mPayload := mPayload) w)
  let s7 :=
    dWeightedModInv v wcsa12Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1
    10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s7 hmWork)
    (wChunk_218_128_s7 (mPayload := mPayload) w) (wChunk_218_128_s7_inj (mPayload := mPayload) w)
  let s8 :=
    dWeightedModInv v wcsa03Spec rCore (rSum14.slice 3 9 (by decide)) rWork (disj_slice14 hCSum 3 9
    (by decide)) hCW (disj_slice14_work hSW 3 9 (by decide)) (by decide) (h218_128_s8 hmWork)
    (wChunk_218_128_s8 (mPayload := mPayload) w) (wChunk_218_128_s8_inj (mPayload := mPayload) w)
  let s9 :=
    dWeightedModInv v wcsa11Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s9 hmWork)
    (wChunk_218_128_s9 (mPayload := mPayload) w) (wChunk_218_128_s9_inj (mPayload := mPayload) w)
  let s10 :=
    dWeightedModInv v wcsa13Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3
    10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s10 hmWork)
    (wChunk_218_128_s10 (mPayload := mPayload) w) (wChunk_218_128_s10_inj (mPayload := mPayload) w)
  let s11 :=
    dWeightedModInv v wcsa14Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3
    11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_128_s11 hmWork)
    (wChunk_218_128_s11 (mPayload := mPayload) w) (wChunk_218_128_s11_inj (mPayload := mPayload) w)
  let s12 :=
    dWeightedModInv v wcsa15Spec rCore (rSum14.slice 4 10 (by decide)) rWork (disj_slice14 hCSum 4
    10 (by decide)) hCW (disj_slice14_work hSW 4 10 (by decide)) (by decide) (h218_128_s12 hmWork)
    (wChunk_218_128_s12 (mPayload := mPayload) w) (wChunk_218_128_s12_inj (mPayload := mPayload) w)
  (.seq s12 (.seq s11 (.seq s10 (.seq s9 (.seq s8 (.seq s7 (.seq s6 (.seq s5 (.seq s4 (.seq s3 (.seq
    s2 s1)))))))))))
/-- Ideal 218-electron stream unitary for Variant `218_128`. -/
noncomputable def uHybridStream218_128 {mPayload : ℕ} (w : Fin 3) : Unitary (2 ^ (fullSysCoreWires
    mPayload + 14)) :=
  let u1 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 6 (by decide)).embedUnitary (uBitXor
    (fullSysCoreWires mPayload) 6 (weightedGenBatchVal (wChunk_218_128_s1 (mPayload :=
    mPayload) w)))
  let u2 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 7 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 7 (weightedGenBatchVal (wChunk_218_128_s2 (mPayload :=
    mPayload) w)))
  let u3 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 8 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 8 (weightedGenBatchVal (wChunk_218_128_s3 (mPayload :=
    mPayload) w)))
  let u4 :=
    (selCoreSlice (fullSysCoreWires mPayload) 0 9 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 9 (weightedGenBatchVal (wChunk_218_128_s4 (mPayload :=
    mPayload) w)))
  let u5 :=
    (selCoreSlice (fullSysCoreWires mPayload) 1 9 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 9 (weightedGenBatchVal (wChunk_218_128_s5 (mPayload :=
    mPayload) w)))
  let u6 :=
    (selCoreSlice (fullSysCoreWires mPayload) 1 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_128_s6 (mPayload :=
    mPayload) w)))
  let u7 :=
    (selCoreSlice (fullSysCoreWires mPayload) 1 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_128_s7 (mPayload :=
    mPayload) w)))
  let u8 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 9 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 9 (weightedGenBatchVal (wChunk_218_128_s8 (mPayload :=
    mPayload) w)))
  let u9 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_128_s9 (mPayload :=
    mPayload) w)))
  let u10 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_128_s10 (mPayload :=
    mPayload) w)))
  let u11 :=
    (selCoreSlice (fullSysCoreWires mPayload) 3 11 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 11 (weightedGenBatchVal (wChunk_218_128_s11 (mPayload :=
    mPayload) w)))
  let u12 :=
    (selCoreSlice (fullSysCoreWires mPayload) 4 10 (by decide)).embedUnitary (catModAddUnitary
    (fullSysCoreWires mPayload) 10 (weightedGenBatchVal (wChunk_218_128_s12 (mPayload :=
    mPayload) w)))
  (u12 * (u11 * (u10 * (u9 * (u8 * (u7 * (u6 * (u5 * (u4 * (u3 * (u2 * u1)))))))))))
theorem dCleanHybridStream218_128_counts {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 128 ≤ mWork) :
    let dFwd := dCleanHybridStreamAdd218_128 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    let dInv := dCleanHybridStreamInv218_128 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    dFwd.count TOFF = 0 ∧ dInv.count TOFF = 0 ∧ dFwd.count T ≤ 5212 ∧ dInv.count T ≤ 5212 := by
  intro dFwd dInv
  have c1 :=
    dStep1XorK_counts v wcsa00Spec (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork
    (disj_slice14 hCSum 0 6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_128_s1
    hmWork) (wChunk_218_128_s1 (mPayload := mPayload) w) (wChunk_218_128_s1_inj (mPayload :=
    mPayload) w)
  have c2 :=
    dWeightedModAdd_counts v wcsa01Spec rCore (rSum14.slice 0 7 (by decide)) rWork (disj_slice14
    hCSum 0 7 (by decide)) hCW (disj_slice14_work hSW 0 7 (by decide)) (by decide) (h218_128_s2
    hmWork) (wChunk_218_128_s2 (mPayload := mPayload) w) (wChunk_218_128_s2_inj (mPayload :=
    mPayload) w)
  have c3 :=
    dWeightedModAdd_counts v wcsa02Spec rCore (rSum14.slice 0 8 (by decide)) rWork (disj_slice14
    hCSum 0 8 (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) (by decide) (h218_128_s3
    hmWork) (wChunk_218_128_s3 (mPayload := mPayload) w) (wChunk_218_128_s3_inj (mPayload :=
    mPayload) w)
  have c4 :=
    dWeightedModAdd_counts v wcsa03Spec rCore (rSum14.slice 0 9 (by decide)) rWork (disj_slice14
    hCSum 0 9 (by decide)) hCW (disj_slice14_work hSW 0 9 (by decide)) (by decide) (h218_128_s4
    hmWork) (wChunk_218_128_s4 (mPayload := mPayload) w) (wChunk_218_128_s4_inj (mPayload :=
    mPayload) w)
  have c5 :=
    dWeightedModAdd_counts v wcsa10Spec rCore (rSum14.slice 1 9 (by decide)) rWork (disj_slice14
    hCSum 1 9 (by decide)) hCW (disj_slice14_work hSW 1 9 (by decide)) (by decide) (h218_128_s5
    hmWork) (wChunk_218_128_s5 (mPayload := mPayload) w) (wChunk_218_128_s5_inj (mPayload :=
    mPayload) w)
  have c6 :=
    dWeightedModAdd_counts v wcsa11Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14
    hCSum 1 10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s6
    hmWork) (wChunk_218_128_s6 (mPayload := mPayload) w) (wChunk_218_128_s6_inj (mPayload :=
    mPayload) w)
  have c7 :=
    dWeightedModAdd_counts v wcsa12Spec rCore (rSum14.slice 1 10 (by decide)) rWork (disj_slice14
    hCSum 1 10 (by decide)) hCW (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s7
    hmWork) (wChunk_218_128_s7 (mPayload := mPayload) w) (wChunk_218_128_s7_inj (mPayload :=
    mPayload) w)
  have c8 :=
    dWeightedModAdd_counts v wcsa03Spec rCore (rSum14.slice 3 9 (by decide)) rWork (disj_slice14
    hCSum 3 9 (by decide)) hCW (disj_slice14_work hSW 3 9 (by decide)) (by decide) (h218_128_s8
    hmWork) (wChunk_218_128_s8 (mPayload := mPayload) w) (wChunk_218_128_s8_inj (mPayload :=
    mPayload) w)
  have c9 :=
    dWeightedModAdd_counts v wcsa11Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14
    hCSum 3 10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s9
    hmWork) (wChunk_218_128_s9 (mPayload := mPayload) w) (wChunk_218_128_s9_inj (mPayload :=
    mPayload) w)
  have c10 :=
    dWeightedModAdd_counts v wcsa13Spec rCore (rSum14.slice 3 10 (by decide)) rWork (disj_slice14
    hCSum 3 10 (by decide)) hCW (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s10
    hmWork) (wChunk_218_128_s10 (mPayload := mPayload) w) (wChunk_218_128_s10_inj (mPayload :=
    mPayload) w)
  have c11 :=
    dWeightedModAdd_counts v wcsa14Spec rCore (rSum14.slice 3 11 (by decide)) rWork (disj_slice14
    hCSum 3 11 (by decide)) hCW (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_128_s11
    hmWork) (wChunk_218_128_s11 (mPayload := mPayload) w) (wChunk_218_128_s11_inj (mPayload :=
    mPayload) w)
  have c12 :=
    dWeightedModAdd_counts v wcsa15Spec rCore (rSum14.slice 4 10 (by decide)) rWork (disj_slice14
    hCSum 4 10 (by decide)) hCW (disj_slice14_work hSW 4 10 (by decide)) (by decide) (h218_128_s12
    hmWork) (wChunk_218_128_s12 (mPayload := mPayload) w) (wChunk_218_128_s12_inj (mPayload :=
    mPayload) w)
  dsimp only [dFwd, dInv, dCleanHybridStreamAdd218_128, dCleanHybridStreamInv218_128]
  simp only [count_seq_eq]
  refine ⟨by rw [c1.1, c2.1, c3.1, c4.1, c5.1, c6.1, c7.1, c8.1, c9.1, c10.1, c11.1, c12.1], by
    rw [c12.2.1, c11.2.1, c10.2.1, c9.2.1, c8.2.1, c7.2.1, c6.2.1, c5.2.1, c4.2.1, c3.2.1, c2.2.1,
    c1.1], ?_, ?_⟩
  · have h1 := c1.2;
    have h2 := c2.2.2.1;
    have h3 := c3.2.2.1;
    have h4 := c4.2.2.1;
    have h5 :=
      c5.2.2.1; have h6 := c6.2.2.1; have h7 := c7.2.2.1; have h8 := c8.2.2.1; have h9 :=
      c9.2.2.1; have h10 := c10.2.2.1; have h11 := c11.2.2.1; have h12 := c12.2.2.1; omega
  · have h1 := c1.2;
    have h2 := c2.2.2.2;
    have h3 := c3.2.2.2;
    have h4 := c4.2.2.2;
    have h5 :=
      c5.2.2.2; have h6 := c6.2.2.2; have h7 := c7.2.2.2; have h8 := c8.2.2.2; have h9 :=
      c9.2.2.2; have h10 := c10.2.2.2; have h11 := c11.2.2.2; have h12 := c12.2.2.2; omega
theorem uHybridStream218_128_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)]
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) :
    ∀ β₀ : Fin n → ZMod 2, (∀ i : Fin 14, β₀ (rSum14 i) = 0) →
      ∃ β : Fin n → ZMod 2,
        ((rCore.concat rSum14 hCSum).embedUnitary (uHybridStream218_128 w)).1.mulVec
          (basisKet β₀) = basisKet β ∧
        (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧
        (∀ i : Fin 14,
          β (rSum14 i) = if (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) :=
            by
  intro β₀ hz
  let w1 := (wChunk_218_128_s1 (mPayload := mPayload) w)
  have hb1 : weightedGenBatchVal w1 (fun q ↦ β₀ (rCore q)) ≤ 63 := weightedGenBatchVal_le w1 _
  let w2 := (wChunk_218_128_s2 (mPayload := mPayload) w)
  have hb2 : weightedGenBatchVal w2 (fun q ↦ β₀ (rCore q)) ≤ 64 := weightedGenBatchVal_le w2 _
  let w3 := (wChunk_218_128_s3 (mPayload := mPayload) w)
  have hb3 : weightedGenBatchVal w3 (fun q ↦ β₀ (rCore q)) ≤ 128 := weightedGenBatchVal_le w3 _
  let w4 := (wChunk_218_128_s4 (mPayload := mPayload) w)
  have hb4 : weightedGenBatchVal w4 (fun q ↦ β₀ (rCore q)) ≤ 255 := weightedGenBatchVal_le w4 _
  let w5 := (wChunk_218_128_s5 (mPayload := mPayload) w)
  have hb5 : weightedGenBatchVal w5 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w5 _
  let w6 := (wChunk_218_128_s6 (mPayload := mPayload) w)
  have hb6 : weightedGenBatchVal w6 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w6 _
  let w7 := (wChunk_218_128_s7 (mPayload := mPayload) w)
  have hb7 : weightedGenBatchVal w7 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w7 _
  let w8 := (wChunk_218_128_s8 (mPayload := mPayload) w)
  have hb8 : weightedGenBatchVal w8 (fun q ↦ β₀ (rCore q)) ≤ 255 := weightedGenBatchVal_le w8 _
  let w9 := (wChunk_218_128_s9 (mPayload := mPayload) w)
  have hb9 : weightedGenBatchVal w9 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w9 _
  let w10 := (wChunk_218_128_s10 (mPayload := mPayload) w)
  have hb10 : weightedGenBatchVal w10 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w10 _
  let w11 := (wChunk_218_128_s11 (mPayload := mPayload) w)
  have hb11 : weightedGenBatchVal w11 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w11 _
  let w12 := (wChunk_218_128_s12 (mPayload := mPayload) w)
  have hb12 : weightedGenBatchVal w12 (fun q ↦ β₀ (rCore q)) ≤ 219 := weightedGenBatchVal_le w12 _
  obtain ⟨b1, hket1, hInv1⟩ :=
    accInvar_step1_bitXorK rCore rSum14 hCSum 6 (by decide) (weightedGenBatchVal w1) β₀
    (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨b2, hket2, hInv2⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 0 7 (by decide) (weightedGenBatchVal w2) _ β₀ b1
    hInv1 (by omega) (by omega)
  obtain ⟨b3, hket3, hInv3⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 0 8 (by decide) (weightedGenBatchVal w3) _ β₀ b2
    hInv2 (by omega) (by omega)
  obtain ⟨b4, hket4, hInv4⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 0 9 (by decide) (weightedGenBatchVal w4) _ β₀ b3
    hInv3 (by omega) (by omega)
  obtain ⟨b5, hket5, hInv5⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 1 9 (by decide) (weightedGenBatchVal w5) _ β₀ b4
    hInv4 (by omega) (by omega)
  obtain ⟨b6, hket6, hInv6⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 1 10 (by decide) (weightedGenBatchVal w6) _ β₀ b5
    hInv5 (by omega) (by omega)
  obtain ⟨b7, hket7, hInv7⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 1 10 (by decide) (weightedGenBatchVal w7) _ β₀ b6
    hInv6 (by omega) (by omega)
  obtain ⟨b8, hket8, hInv8⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 9 (by decide) (weightedGenBatchVal w8) _ β₀ b7
    hInv7 (by omega) (by omega)
  obtain ⟨b9, hket9, hInv9⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide) (weightedGenBatchVal w9) _ β₀ b8
    hInv8 (by omega) (by omega)
  obtain ⟨b10, hket10, hInv10⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide) (weightedGenBatchVal w10) _ β₀ b9
    hInv9 (by omega) (by omega)
  obtain ⟨b11, hket11, hInv11⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide) (weightedGenBatchVal w11) _ β₀ b10
    hInv10 (by omega) (by omega)
  obtain ⟨b12, hket12, hInv12⟩ :=
    accInvar_step_sliceModAdd rCore rSum14 hCSum 4 10 (by decide) (weightedGenBatchVal w12) _ β₀ b11
    hInv11 (by omega) (by omega)
  have hSumEq := hybrid218_128_batch_eq_axisSum w (fun q ↦ β₀ (rCore q))
  dsimp only at hSumEq
  rw [hSumEq] at hInv12
  refine ⟨b12, ?_, hInv12.1, hInv12.2⟩
  simp only [uHybridStream218_128, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket1, hket2, hket3, hket4, hket5, hket6, hket7, hket8, hket9, hket10, hket11, hket12]
theorem dCleanHybridStream218_128_cleanPair_explicit {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n) (rWork : QRegister
      mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 128 ≤ mWork) :
    CleanComputePair rCore rSum14 rWork hCSum (uHybridStream218_128 w)
      (fun x i ↦ if (slot2AxisSum w x).testBit i.val then 1 else 0)
      (dCleanHybridStreamAdd218_128 v w rCore rSum14 rWork hCSum hCW hSW hmWork)
      (dCleanHybridStreamInv218_128 v w rCore rSum14 rWork hCSum hCW hSW hmWork) := by
  have hActW : (rCore.concat rSum14 hCSum).DisjointWires rWork :=
    QRegExt.disjointWires_concat_left hCW hSW
  have p1 :=
    liftCleanPair_slice14 hCSum 0 6 (by decide) (dStep1XorK_realizesPair v wcsa00Spec (by decide)
    wcsa00Spec_cinWire (by decide) rCore (rSum14.slice 0 6 (by decide)) rWork (disj_slice14 hCSum 0
    6 (by decide)) hCW (disj_slice14_work hSW 0 6 (by decide)) (h218_128_s1 hmWork)
    (wChunk_218_128_s1 (mPayload := mPayload) w) (wChunk_218_128_s1_inj (mPayload := mPayload) w))
  have p2 :=
    liftCleanPair_slice14 hCSum 0 7 (by decide) (dWeightedModAdd_realizesPair v wcsa01Spec rCore
    (rSum14.slice 0 7 (by decide)) rWork (disj_slice14 hCSum 0 7 (by decide)) hCW (disj_slice14_work
    hSW 0 7 (by decide)) (by decide) (h218_128_s2 hmWork) (wChunk_218_128_s2 (mPayload :=
    mPayload) w) (wChunk_218_128_s2_inj (mPayload := mPayload) w))
  have p3 :=
    liftCleanPair_slice14 hCSum 0 8 (by decide) (dWeightedModAdd_realizesPair v wcsa02Spec rCore
    (rSum14.slice 0 8 (by decide)) rWork (disj_slice14 hCSum 0 8 (by decide)) hCW (disj_slice14_work
    hSW 0 8 (by decide)) (by decide) (h218_128_s3 hmWork) (wChunk_218_128_s3 (mPayload :=
    mPayload) w) (wChunk_218_128_s3_inj (mPayload := mPayload) w))
  have p4 :=
    liftCleanPair_slice14 hCSum 0 9 (by decide) (dWeightedModAdd_realizesPair v wcsa03Spec rCore
    (rSum14.slice 0 9 (by decide)) rWork (disj_slice14 hCSum 0 9 (by decide)) hCW (disj_slice14_work
    hSW 0 9 (by decide)) (by decide) (h218_128_s4 hmWork) (wChunk_218_128_s4 (mPayload :=
    mPayload) w) (wChunk_218_128_s4_inj (mPayload := mPayload) w))
  have p5 :=
    liftCleanPair_slice14 hCSum 1 9 (by decide) (dWeightedModAdd_realizesPair v wcsa10Spec rCore
    (rSum14.slice 1 9 (by decide)) rWork (disj_slice14 hCSum 1 9 (by decide)) hCW (disj_slice14_work
    hSW 1 9 (by decide)) (by decide) (h218_128_s5 hmWork) (wChunk_218_128_s5 (mPayload :=
    mPayload) w) (wChunk_218_128_s5_inj (mPayload := mPayload) w))
  have p6 :=
    liftCleanPair_slice14 hCSum 1 10 (by decide) (dWeightedModAdd_realizesPair v wcsa11Spec rCore
    (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1 10 (by decide)) hCW
    (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s6 hmWork) (wChunk_218_128_s6
    (mPayload := mPayload) w) (wChunk_218_128_s6_inj (mPayload := mPayload) w))
  have p7 :=
    liftCleanPair_slice14 hCSum 1 10 (by decide) (dWeightedModAdd_realizesPair v wcsa12Spec rCore
    (rSum14.slice 1 10 (by decide)) rWork (disj_slice14 hCSum 1 10 (by decide)) hCW
    (disj_slice14_work hSW 1 10 (by decide)) (by decide) (h218_128_s7 hmWork) (wChunk_218_128_s7
    (mPayload := mPayload) w) (wChunk_218_128_s7_inj (mPayload := mPayload) w))
  have p8 :=
    liftCleanPair_slice14 hCSum 3 9 (by decide) (dWeightedModAdd_realizesPair v wcsa03Spec rCore
    (rSum14.slice 3 9 (by decide)) rWork (disj_slice14 hCSum 3 9 (by decide)) hCW (disj_slice14_work
    hSW 3 9 (by decide)) (by decide) (h218_128_s8 hmWork) (wChunk_218_128_s8 (mPayload :=
    mPayload) w) (wChunk_218_128_s8_inj (mPayload := mPayload) w))
  have p9 :=
    liftCleanPair_slice14 hCSum 3 10 (by decide) (dWeightedModAdd_realizesPair v wcsa11Spec rCore
    (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3 10 (by decide)) hCW
    (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s9 hmWork) (wChunk_218_128_s9
    (mPayload := mPayload) w) (wChunk_218_128_s9_inj (mPayload := mPayload) w))
  have p10 :=
    liftCleanPair_slice14 hCSum 3 10 (by decide) (dWeightedModAdd_realizesPair v wcsa13Spec rCore
    (rSum14.slice 3 10 (by decide)) rWork (disj_slice14 hCSum 3 10 (by decide)) hCW
    (disj_slice14_work hSW 3 10 (by decide)) (by decide) (h218_128_s10 hmWork) (wChunk_218_128_s10
    (mPayload := mPayload) w) (wChunk_218_128_s10_inj (mPayload := mPayload) w))
  have p11 :=
    liftCleanPair_slice14 hCSum 3 11 (by decide) (dWeightedModAdd_realizesPair v wcsa14Spec rCore
    (rSum14.slice 3 11 (by decide)) rWork (disj_slice14 hCSum 3 11 (by decide)) hCW
    (disj_slice14_work hSW 3 11 (by decide)) (by decide) (h218_128_s11 hmWork) (wChunk_218_128_s11
    (mPayload := mPayload) w) (wChunk_218_128_s11_inj (mPayload := mPayload) w))
  have p12 :=
    liftCleanPair_slice14 hCSum 4 10 (by decide) (dWeightedModAdd_realizesPair v wcsa15Spec rCore
    (rSum14.slice 4 10 (by decide)) rWork (disj_slice14 hCSum 4 10 (by decide)) hCW
    (disj_slice14_work hSW 4 10 (by decide)) (by decide) (h218_128_s12 hmWork) (wChunk_218_128_s12
    (mPayload := mPayload) w) (wChunk_218_128_s12_inj (mPayload := mPayload) w))
  have pAll :=
    (((((((((((p1.seq hActW p2).seq hActW p3).seq hActW p4).seq hActW p5).seq hActW p6).seq hActW
    p7).seq hActW p8).seq hActW p9).seq hActW p10).seq hActW p11).seq hActW p12)
  change RealizesCleanPair (rCore.concat rSum14 hCSum) rWork (uHybridStream218_128 w) _ _ at pAll
  exact ⟨pAll, uHybridStream218_128_compute_ket w rCore rSum14 hCSum⟩
attribute [irreducible] dCleanHybridStreamAdd218_128 dCleanHybridStreamInv218_128
  uHybridStream218_128
end Impl
end Bell18StageABridge_Borrow136.ChiralB

namespace Bell18StageABridge_Borrow136.ChiralD
noncomputable section Impl
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
set_option exponentiation.threshold 512
set_option maxRecDepth 200000
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint
  disjointWires_concat_left fullSys_zero_add_le_of_le)
open InPlaceFullAddSlice
open InPlaceStepEngine
open NuclearTwistRealizes (RealizesCleanPair uXor32Core slot2AxisSum)
open UltraAsymVepTwist288 (realizesClean_of_workspace_subset)
open SingleCatClosure (compose_concat_eq_singleCat)
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open SinglePassNuclearTwist288
open HybridStream288Aux
open HybridStream168Aux
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum14In42 rSum14Full hCoreFull_disj_Sum14 rCSFull
  uXor32Full pSum42Zero E_stream42 streamProjOpGen streamProjOpGen_mulVec_basisKet streamTarget42
  basisBits_streamTarget42 embedUnitary_inv_symm qreg_ext qreg_block_apply)
open Slot1AndStreamInitOpt
  (CommutesWithReg RealizesClean RealizesOnProj basisOutcomeProjector_concat_zero
   basisOutcomeProjector_conjTranspose)
open BoothOpt_06_Stream217ZeroSave0Width128 (widenActivePair_of_eq rSum14Slice42 selCoreSum14In42
  compose_selCoreSum14In42)
local instance (priority := 1000000) instNeZeroTwoPowStageABrgD (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Bell18StageABridge_Borrow136.ChiralA
open Bell18StageABridge_Borrow136.ChiralB
open StageAConjHAndStreamBridge
  (rActLoc rZLoc rActLoc_disj_rZLoc rActLoc_concat_rZLoc_eq_idReg joinAZ
   extract_rActLoc_joinAZ extract_rZLoc_joinAZ joinAZ_extract_self
   pSum42CoreZero eStream42CoreOf eStream218Core
   rZLoc_basisOutcomeProjector_zero_mulVec_basisKet pSum42CoreZero_mulVec_basisKet
   eStream42CoreOf_mulVec_basisKet)
theorem ket_eq_basisKet_loc {n : ℕ} (β : BitAssignment n) :
    MeasureBranchHadamardSem.ket β = basisKet β := by
  ext y; simp [MeasureBranchHadamardSem.ket, basisKet, basisState]
theorem embedUnitary_idReg_eq_loc {k : ℕ} (U : Unitary (2 ^ k)) :
    (QRegExt.idReg k).embedUnitary U = U := by
  apply Subtype.ext; ext x y
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply]
  have hx : (QRegExt.idReg k).extractIndex x = x :=
    (basisBitsEquiv k).injective (funext fun q ↦ by
      change basisBits k _ q = basisBits k _ q; rw [QRegister.basisBits_extractIndex]; rfl)
  have hy : (QRegExt.idReg k).extractIndex y = y :=
    (basisBitsEquiv k).injective (funext fun q ↦ by
      change basisBits k _ q = basisBits k _ q; rw [QRegister.basisBits_extractIndex]; rfl)
  have hEnv : ((QRegExt.idReg k).basisSplitEquiv x).2 = ((QRegExt.idReg k).basisSplitEquiv y).2 :=
    by
    rw [QRegister.basisSplit_environment_eq_iff]
    intro w hw; exact False.elim (hw ⟨w, rfl⟩)
  rw [ite_eq_left hEnv, hx, hy, mul_one]
theorem basisKet_eq_single_symm_loc {n : ℕ} (β : BitAssignment n) :
    basisKet β = Pi.single ((basisBitsEquiv n).symm β) 1 := by
  ext y; simp [basisKet, basisState, Pi.single_apply]
/-- Generic 1-axis stream specification for arbitrary `sumFn` (`slot2AxisSum` or
  `spectatorSum217`). -/
structure AxisStreamSpecOf (sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ)
    (mScr tAxis : ℕ) where
  uAxis : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))
  hKet : ∀ (w : Fin 3) {n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum14 : QRegister 14 n)
    (hCS : rCore.DisjointWires rSum14) (β₀ : Fin n → ZMod 2),
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) →
    ∃ β : Fin n → ZMod 2,
      ((rCore.concat rSum14 hCS).embedUnitary (uAxis w)).1.mulVec (basisKet β₀) = basisKet β ∧
      (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧
      (∀ i : Fin 14, β (rSum14 i) = if (sumFn w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0)
  dAdd : ∀ {Var : Type} {mWork n : ℕ}, Var → Fin 3 →
    (rCore : QRegister (fullSysCoreWires 80) n) → (rSum14 : QRegister 14 n) →
    (rWork : QRegister mWork n) → rCore.DisjointWires rSum14 →
    rCore.DisjointWires rWork → rSum14.DisjointWires rWork → mScr ≤ mWork → DynamicCircuit Var n
  dInv : ∀ {Var : Type} {mWork n : ℕ}, Var → Fin 3 →
    (rCore : QRegister (fullSysCoreWires 80) n) → (rSum14 : QRegister 14 n) →
    (rWork : QRegister mWork n) → rCore.DisjointWires rSum14 →
    rCore.DisjointWires rWork → rSum14.DisjointWires rWork → mScr ≤ mWork → DynamicCircuit Var n
  hCounts : ∀ {Var : Type} {mWork n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCS : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork) (hm : mScr ≤ mWork),
    (dAdd v w rCore rSum14 rWork hCS hCW hSW hm).count TOFF = 0 ∧
    (dInv v w rCore rSum14 rWork hCS hCW hSW hm).count TOFF = 0 ∧
    (dAdd v w rCore rSum14 rWork hCS hCW hSW hm).count T ≤ tAxis ∧
    (dInv v w rCore rSum14 rWork hCS hCW hSW hm).count T ≤ tAxis
  hRealPair : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hCS : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hm : mScr ≤ mWork),
    RealizesCleanPair (rCore.concat rSum14 hCS) rWork (uAxis w)
      (dAdd v w rCore rSum14 rWork hCS hCW hSW hm)
      (dInv v w rCore rSum14 rWork hCS hCW hSW hm)
/-- Combined 3-axis stream unitary on `fullSysCoreWires 80 + 42` from per-axis `u0, u1, u2`. -/
noncomputable def uStr3AxisTri
    (u0 u1 u2 : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) :
    Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  ((selCoreSum14In42 80 2).embedUnitary (u2 2) *
    (selCoreSum14In42 80 1).embedUnitary (u1 1)) *
    (selCoreSum14In42 80 0).embedUnitary (u0 0)
theorem rSum14Slice42_disj_ne {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) :
    (rSum14Slice42 w₁).DisjointWires (rSum14Slice42 w₂) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have hi := i.isLt; have hj := j.isLt
  fin_cases w₁ <;> fin_cases w₂ <;> first | contradiction | (simp [rSum14Slice42] at hv; omega)
theorem uStr3AxisTri_compute_ket
    {sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ}
    {m0 t0 m1 t1 m2 t2 n : ℕ} [NeZero (2 ^ n)]
    (s0 : AxisStreamSpecOf sumFn m0 t0)
    (s1 : AxisStreamSpecOf sumFn m1 t1)
    (s2 : AxisStreamSpecOf sumFn m2 t2)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (β₀ : Fin n → ZMod 2) (hz42 : ∀ j : Fin 42, β₀ (rSum42 j) = 0) :
    ∃ β : Fin n → ZMod 2,
      ((rCore.concat rSum42 hCSum42).embedUnitary (uStr3AxisTri s0.uAxis s1.uAxis
        s2.uAxis)).1.mulVec
        (basisKet β₀) = basisKet β ∧
      (∀ g : Fin n, g ∉ rSum42.image → β g = β₀ g) ∧
      (∀ w : Fin 3, ∀ i : Fin 14,
        β ((rSum42.compose (rSum14Slice42 w)) i) =
          if (sumFn w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  let rCS := rCore.concat rSum42 hCSum42
  let rS (w : Fin 3) := rSum42.compose (rSum14Slice42 w)
  have hSub (w : Fin 3) : (rS w).image ⊆ rSum42.image := QRegister.image_compose_subset rSum42 _
  have hDisjS {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) : (rS w₁).DisjointWires (rS w₂) :=
    disjointWires_compose_of_disjoint rSum42 (rSum14Slice42_disj_ne hne)
  have hMat (w : Fin 3) (U : Unitary (2 ^ (fullSysCoreWires 80 + 14))) :
      (rCS.embedUnitary ((selCoreSum14In42 80 w).embedUnitary U)).1 =
      ((rCore.concat (rS w) (hCSum42.compose_right _)).embedUnitary U).1 := by
    change rCS.embedMatrix ((selCoreSum14In42 80 w).embedUnitary U).1 =
      (rCore.concat (rS w) (hCSum42.compose_right _)).embedMatrix U.1
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, compose_selCoreSum14In42]
  have hz0 : ∀ i : Fin 14, β₀ (rS 0 i) = 0 := fun i ↦ hz42 _
  obtain ⟨β₁, hk₁, ho₁, hb₁⟩ := s0.hKet 0 rCore (rS 0) (hCSum42.compose_right _) β₀ hz0
  have hz1 : ∀ i : Fin 14, β₁ (rS 1 i) = 0 := fun i ↦ by
    rw [ho₁ _ ((hDisjS (by decide : (1 : Fin 3) ≠ 0)).apply_not_mem_right i)]; exact hz42 _
  obtain ⟨β₂, hk₂, ho₂, hb₂⟩ := s1.hKet 1 rCore (rS 1) (hCSum42.compose_right _) β₁ hz1
  have hz2 : ∀ i : Fin 14, β₂ (rS 2 i) = 0 := fun i ↦ by
    rw [ho₂ _ ((hDisjS (by decide : (2 : Fin 3) ≠ 1)).apply_not_mem_right i),
      ho₁ _ ((hDisjS (by decide : (2 : Fin 3) ≠ 0)).apply_not_mem_right i)]
    exact hz42 _
  obtain ⟨β₃, hk₃, ho₃, hb₃⟩ := s2.hKet 2 rCore (rS 2) (hCSum42.compose_right _) β₂ hz2
  have hCore₁ : (fun q ↦ β₁ (rCore q)) = (fun q ↦ β₀ (rCore q)) :=
    funext fun q ↦ ho₁ _ ((hCSum42.compose_right _).apply_not_mem_right q)
  have hCore₂ : (fun q ↦ β₂ (rCore q)) = (fun q ↦ β₀ (rCore q)) :=
    funext fun q ↦
      (ho₂ _ ((hCSum42.compose_right _).apply_not_mem_right q)).trans (congrFun hCore₁ q)
  refine ⟨β₃, ?_, fun g hg ↦ ?_, fun w i ↦ ?_⟩
  · dsimp only [rCS] at hMat
    simp only [uStr3AxisTri, QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      hMat 0, hMat 1, hMat 2]
    rw [hk₁, hk₂, hk₃]
  · rw [ho₃ g (fun m ↦ hg (hSub 2 m)), ho₂ g (fun m ↦ hg (hSub 1 m)), ho₁ g (fun m ↦ hg (hSub 0 m))]
  · fin_cases w
    · change β₃ (rS 0 i) = if (sumFn 0 fun q ↦ β₀ (rCore q)).testBit i.val then 1 else 0
      rw [ho₃ _ ((hDisjS (by decide : (0 : Fin 3) ≠ 2)).apply_not_mem_right i),
        ho₂ _ ((hDisjS (by decide : (0 : Fin 3) ≠ 1)).apply_not_mem_right i), hb₁ i]
    · change β₃ (rS 1 i) = if (sumFn 1 fun q ↦ β₀ (rCore q)).testBit i.val then 1 else 0
      rw [ho₃ _ ((hDisjS (by decide : (1 : Fin 3) ≠ 2)).apply_not_mem_right i), hb₂ i, hCore₁]
    · change β₃ (rS 2 i) = if (sumFn 2 fun q ↦ β₀ (rCore q)).testBit i.val then 1 else 0
      rw [hb₃ i, hCore₂]
theorem uStr3AxisTri_mul_pSum42CoreZero_eq_eStream42CoreOf
    {sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ}
    {m0 t0 m1 t1 m2 t2 : ℕ}
    (s0 : AxisStreamSpecOf sumFn m0 t0)
    (s1 : AxisStreamSpecOf sumFn m1 t1)
    (s2 : AxisStreamSpecOf sumFn m2 t2) :
    (uStr3AxisTri s0.uAxis s1.uAxis s2.uAxis).1 * pSum42CoreZero = eStream42CoreOf sumFn := by
  let kC := fullSysCoreWires 80
  let rA := rActLoc kC 42
  let rZ := rZLoc kC 42
  apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
  rw [ket_eq_basisKet_loc, ← Matrix.mulVec_mulVec, pSum42CoreZero_mulVec_basisKet,
      eStream42CoreOf_mulVec_basisKet]
  let y := (basisBitsEquiv (kC + 42)).symm β
  by_cases h0 : rZ.extractIndex y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hz42 : ∀ j : Fin 42, β (rZ j) = 0 := by
      have hx := ((QRegExt.extractIndex_eq_zero_iff rZ) y).mp h0
      intro j; simpa [y] using hx j
    obtain ⟨β₁, hk₁, hout₁, hbits₁⟩ :=
      uStr3AxisTri_compute_ket s0 s1 s2 rA rZ (rActLoc_disj_rZLoc kC 42) β hz42
    rw [rActLoc_concat_rZLoc_eq_idReg kC 42, embedUnitary_idReg_eq_loc] at hk₁
    rw [hk₁]
    refine congrArg basisKet (funext fun g ↦ ?_)
    have haBits : basisBits kC (rA.extractIndex y) = fun q ↦ β (rA q) := by
      funext q; simp [y, QRegister.basisBits_extractIndex]
    by_cases hg : g.val < kC
    · have hnZ : g ∉ rZ.image := by
        intro hm; obtain ⟨j, rfl⟩ := (QRegister.mem_image rZ _).mp hm
        simp [rZ, rZLoc] at hg
      have hga : rA ⟨g.val, hg⟩ = g := Fin.ext (by simp [rA, rActLoc])
      rw [hout₁ g hnZ, joinAZ, rZ.basisBits_replaceIndex_of_not_mem _ _ g
        (fun ⟨j, hj⟩ ↦ hnZ ((QRegister.mem_image rZ _).mpr ⟨j, hj⟩)),
        ← hga, rA.basisBits_replaceIndex_apply, haBits]
    · let j42 : Fin 42 := ⟨g.val - kC, by have := g.isLt; omega⟩
      let w : Fin 3 := ⟨j42.val / 14, by have := j42.isLt; omega⟩
      let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
      have hgz : rZ j42 = g := Fin.ext (by have := g.isLt; simp [rZ, rZLoc, j42]; omega)
      have hjSlice : rSum14Slice42 w i14 = j42 :=
        Fin.ext (by simp [rSum14Slice42, w, i14]; omega)
      have hjIn42 : rSum14In42 w i14 = j42 :=
        Fin.ext (by simp [rSum14In42, w, i14]; omega)
      have hgComp : (rZ.compose (rSum14Slice42 w)) i14 = g := by
        rw [QRegister.compose_apply, hjSlice, hgz]
      rw [← hgComp, hbits₁ w i14, hgComp, ← hgz, joinAZ, rZ.basisBits_replaceIndex_apply,
        ← hjIn42, basisBits_streamTarget42, haBits]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem rSum14Slice42_zero_disj_slice14_28 {n : ℕ} (rSum42 : QRegister 42 n) :
    (rSum42.compose (rSum14Slice42 0)).DisjointWires (rSum42.slice 14 28 (by decide)) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val (rSum42.wires.injective hij)
  have hi := i.isLt; have hj := j.isLt
  simp only [rSum14Slice42, qreg_block_apply] at hv
  omega
theorem rSum14Slice42_one_disj_slice28_14 {n : ℕ} (rSum42 : QRegister 42 n) :
    (rSum42.compose (rSum14Slice42 1)).DisjointWires (rSum42.slice 28 14 (by decide)) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val (rSum42.wires.injective hij)
  have hi := i.isLt; have hj := j.isLt
  simp only [rSum14Slice42, qreg_block_apply] at hv
  omega
theorem rZSlice_proj0_mul_pSum42CoreZero (off len : ℕ) (h : off + len ≤ 42) :
    ((rZLoc (fullSysCoreWires 80) 42).slice off len h).basisOutcomeProjector 0 *
      pSum42CoreZero = pSum42CoreZero := by
  let rZ := rZLoc (fullSysCoreWires 80) 42
  let rSl := rZ.slice off len h
  unfold pSum42CoreZero
  rw [rSl.basisOutcomeProjector_eq_diagonal, rZ.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  by_cases hz : rZ.extractIndex x = 0
  · have hsl : rSl.extractIndex x = 0 := by
      rw [(QRegExt.extractIndex_eq_zero_iff rSl)]
      intro i
      have hx := ((QRegExt.extractIndex_eq_zero_iff rZ) x).mp hz ⟨off + i.val, by omega⟩
      have hEq : rSl i = rZ ⟨off + i.val, by omega⟩ := by
        rw [QRegister.slice_apply]
      rwa [hEq]
    simp [hz, hsl]
  · simp [hz]
theorem selCoreSum14In42_disj_rZSlice (w : Fin 3) (off len : ℕ) (h : off + len ≤ 42)
    (hSep : 14 * (w.val + 1) ≤ off) :
    (selCoreSum14In42 80 w).DisjointWires ((rZLoc (fullSysCoreWires 80) 42).slice off len h) := by
  rw [QRegister.disjoint_iff]
  intro idx j
  refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) idx
  · intro hij
    have hv := congrArg Fin.val hij
    dsimp only [selCoreSum14In42] at hv
    rw [QRegister.concat_apply_left] at hv
    have hi := iC.isLt; have hj := j.isLt
    simp only [rZLoc, QRegister.slice, QRegister.compose_apply, qreg_block_apply] at hv
    omega
  · intro hij
    have hv := congrArg Fin.val hij
    dsimp only [selCoreSum14In42] at hv
    rw [QRegister.concat_apply_right, QRegister.compose_apply] at hv
    have hj14 := j14.isLt; have hj := j.isLt
    simp only [rSum14Slice42, rZLoc, QRegister.slice, QRegister.compose_apply,
      qreg_block_apply] at hv
    omega
theorem realizesOnProj_of_clean_embed
    {Var : Type} [Fintype Var] [DecidableEq Var] {kAct mWork n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister kAct n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork)
    (E : Operator (2 ^ kAct)) {U : Unitary (2 ^ kAct)} {d : DynamicCircuit Var n}
    (hd : RealizesClean rAct rWork U d) :
    RealizesOnProj (rAct.embedMatrix E * rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary U) d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  let PW := rWork.basisOutcomeProjector 0
  let B := rAct.embedMatrix E
  have hBPW : B * PW = PW * B :=
    (CommutesWithReg.of_disjoint hDisj E).comm_basisOutcomeProjector 0
  have hEinH : (B * PW)ᴴ = Bᴴ * PW := by
    rw [hBPW, Matrix.conjTranspose_mul, basisOutcomeProjector_conjTranspose]
  rw [hEinH]
  calc (Bᴴ * PW) * M'.1.1 * (B * PW)
      = Bᴴ * (PW * M'.1.1 * PW) * B := by rw [hBPW]; simp only [Matrix.mul_assoc]
    _ = Bᴴ * (PW * ((rAct.embedUnitary U).1ᴴ * M.1.1 * (rAct.embedUnitary U).1) * PW) * B := by
          rw [hproj]
    _ = (Bᴴ * PW) * ((rAct.embedUnitary U).1ᴴ * M.1.1 * (rAct.embedUnitary U).1) * (B * PW) := by
          rw [hBPW]; simp only [Matrix.mul_assoc]
/-- Generic 3-tier borrowed-`rSum42` (`+28w` on Axis `0`, `+14w` on Axis `1`, `+0w` on Axis `2`)
forward Stage-A stream circuit on `(rCore, rSum42, rWork)`. -/
noncomputable def dStrAdd3AxisBorrow
    {sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ}
    {m0 t0 m1 t1 m2 t2 : ℕ}
    (s0 : AxisStreamSpecOf sumFn m0 t0)
    (s1 : AxisStreamSpecOf sumFn m1 t1)
    (s2 : AxisStreamSpecOf sumFn m2 t2)
    {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hm0 : m0 ≤ 28 + mWork) (hm1 : m1 ≤ 14 + mWork) (hm2 : m2 ≤ mWork) :
    DynamicCircuit Var n :=
  let rHi28 := rSum42.slice 14 28 (by decide)
  let hHi28W : rHi28.DisjointWires rWork := hSW42.compose_left _
  let rWork0 : QRegister (28 + mWork) n := rHi28.concat rWork hHi28W
  let hCW0 : rCore.DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS0W0 : (rSum42.compose (rSum14Slice42 0)).DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (rSum14Slice42_zero_disj_slice14_28 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let rHi14 := rSum42.slice 28 14 (by decide)
  let hHi14W : rHi14.DisjointWires rWork := hSW42.compose_left _
  let rWork1 : QRegister (14 + mWork) n := rHi14.concat rWork hHi14W
  let hCW1 : rCore.DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS1W1 : (rSum42.compose (rSum14Slice42 1)).DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (rSum14Slice42_one_disj_slice28_14 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let d0 := s0.dAdd v 0 rCore (rSum42.compose (rSum14Slice42 0)) rWork0
    (hCSum42.compose_right _) hCW0 hS0W0 hm0
  let d1 := s1.dAdd v 1 rCore (rSum42.compose (rSum14Slice42 1)) rWork1
    (hCSum42.compose_right _) hCW1 hS1W1 hm1
  let d2 := s2.dAdd v 2 rCore (rSum42.compose (rSum14Slice42 2)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hm2
  .seq d0 (.seq d1 d2)
/-- Generic 3-tier borrowed-`rSum42` (`+0w` on Axis `2`, `+14w` on Axis `1`, `+28w` on Axis `0`)
inverse Stage-A stream circuit on `(rCore, rSum42, rWork)`. -/
noncomputable def dStrInv3AxisBorrow
    {sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ}
    {m0 t0 m1 t1 m2 t2 : ℕ}
    (s0 : AxisStreamSpecOf sumFn m0 t0)
    (s1 : AxisStreamSpecOf sumFn m1 t1)
    (s2 : AxisStreamSpecOf sumFn m2 t2)
    {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hm0 : m0 ≤ 28 + mWork) (hm1 : m1 ≤ 14 + mWork) (hm2 : m2 ≤ mWork) :
    DynamicCircuit Var n :=
  let rHi28 := rSum42.slice 14 28 (by decide)
  let hHi28W : rHi28.DisjointWires rWork := hSW42.compose_left _
  let rWork0 : QRegister (28 + mWork) n := rHi28.concat rWork hHi28W
  let hCW0 : rCore.DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS0W0 : (rSum42.compose (rSum14Slice42 0)).DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (rSum14Slice42_zero_disj_slice14_28 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let rHi14 := rSum42.slice 28 14 (by decide)
  let hHi14W : rHi14.DisjointWires rWork := hSW42.compose_left _
  let rWork1 : QRegister (14 + mWork) n := rHi14.concat rWork hHi14W
  let hCW1 : rCore.DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS1W1 : (rSum42.compose (rSum14Slice42 1)).DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (rSum14Slice42_one_disj_slice28_14 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let i0 := s0.dInv v 0 rCore (rSum42.compose (rSum14Slice42 0)) rWork0
    (hCSum42.compose_right _) hCW0 hS0W0 hm0
  let i1 := s1.dInv v 1 rCore (rSum42.compose (rSum14Slice42 1)) rWork1
    (hCSum42.compose_right _) hCW1 hS1W1 hm1
  let i2 := s2.dInv v 2 rCore (rSum42.compose (rSum14Slice42 2)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hm2
  .seq (.seq i2 i1) i0
theorem dStr3AxisBorrow_counts
    {sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ}
    {m0 t0 m1 t1 m2 t2 : ℕ}
    (s0 : AxisStreamSpecOf sumFn m0 t0)
    (s1 : AxisStreamSpecOf sumFn m1 t1)
    (s2 : AxisStreamSpecOf sumFn m2 t2)
    {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hm0 : m0 ≤ 28 + mWork) (hm1 : m1 ≤ 14 + mWork) (hm2 : m2 ≤ mWork) :
    let dAdd := dStrAdd3AxisBorrow s0 s1 s2 v rCore rSum42 rWork hCSum42 hCW hSW42 hm0 hm1 hm2
    let dInv := dStrInv3AxisBorrow s0 s1 s2 v rCore rSum42 rWork hCSum42 hCW hSW42 hm0 hm1 hm2
    dAdd.count TOFF = 0 ∧ dInv.count TOFF = 0 ∧
      dAdd.count T ≤ t0 + t1 + t2 ∧ dInv.count T ≤ t0 + t1 + t2 ∧
      dInv.count T + dAdd.count T ≤ 2 * (t0 + t1 + t2) := by
  intro dAdd dInv
  let rHi28 := rSum42.slice 14 28 (by decide)
  let hHi28W : rHi28.DisjointWires rWork := hSW42.compose_left _
  let rWork0 : QRegister (28 + mWork) n := rHi28.concat rWork hHi28W
  let hCW0 : rCore.DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS0W0 : (rSum42.compose (rSum14Slice42 0)).DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (rSum14Slice42_zero_disj_slice14_28 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let rHi14 := rSum42.slice 28 14 (by decide)
  let hHi14W : rHi14.DisjointWires rWork := hSW42.compose_left _
  let rWork1 : QRegister (14 + mWork) n := rHi14.concat rWork hHi14W
  let hCW1 : rCore.DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS1W1 : (rSum42.compose (rSum14Slice42 1)).DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (rSum14Slice42_one_disj_slice28_14 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  have c0 := s0.hCounts v 0 rCore (rSum42.compose (rSum14Slice42 0)) rWork0
    (hCSum42.compose_right _) hCW0 hS0W0 hm0
  have c1 := s1.hCounts v 1 rCore (rSum42.compose (rSum14Slice42 1)) rWork1
    (hCSum42.compose_right _) hCW1 hS1W1 hm1
  have c2 := s2.hCounts v 2 rCore (rSum42.compose (rSum14Slice42 2)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hm2
  dsimp only [dAdd, dInv, dStrAdd3AxisBorrow, dStrInv3AxisBorrow, rWork0, rHi28, rWork1,
    rHi14] at c0 c1 ⊢
  simp only [count_seq_eq]
  have := c0.2.2.1; have := c0.2.2.2
  have := c1.2.2.1; have := c1.2.2.2
  have := c2.2.2.1; have := c2.2.2.2
  refine ⟨by rw [c0.1, c1.1, c2.1], by rw [c2.2.1, c1.2.1, c0.2.1], by omega, by omega, by omega⟩
theorem dStr3AxisBorrow_realizesOnProj
    {sumFn : Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ}
    {m0 t0 m1 t1 m2 t2 : ℕ}
    (s0 : AxisStreamSpecOf sumFn m0 t0)
    (s1 : AxisStreamSpecOf sumFn m1 t1)
    (s2 : AxisStreamSpecOf sumFn m2 t2)
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hm0 : m0 ≤ 28 + mWork) (hm1 : m1 ≤ 14 + mWork) (hm2 : m2 ≤ mWork) :
    let rCS := rCore.concat rSum42 hCSum42
    RealizesOnProj (rCS.embedMatrix pSum42CoreZero * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary (uStr3AxisTri s0.uAxis s1.uAxis s2.uAxis))
      (dStrAdd3AxisBorrow s0 s1 s2 v rCore rSum42 rWork hCSum42 hCW hSW42 hm0 hm1 hm2) ∧
    RealizesOnProj (rCS.embedMatrix (eStream42CoreOf sumFn) * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary (uStr3AxisTri s0.uAxis s1.uAxis s2.uAxis)⁻¹)
      (dStrInv3AxisBorrow s0 s1 s2 v rCore rSum42 rWork hCSum42 hCW hSW42 hm0 hm1 hm2) := by
  intro rCS
  have hCSW : rCS.DisjointWires rWork := QRegExt.disjointWires_concat_left hCW hSW42
  let rHi28 := rSum42.slice 14 28 (by decide)
  let hHi28W : rHi28.DisjointWires rWork := hSW42.compose_left _
  let rWork0 : QRegister (28 + mWork) n := rHi28.concat rWork hHi28W
  let hCW0 : rCore.DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS0W0 : (rSum42.compose (rSum14Slice42 0)).DisjointWires rWork0 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi28W (QRegExt.disjointWires_symm
      (rSum14Slice42_zero_disj_slice14_28 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let rSub0 := rCore.concat (rSum42.compose (rSum14Slice42 0)) (hCSum42.compose_right _)
  have hSub0W0 : rSub0.DisjointWires rWork0 := QRegExt.disjointWires_concat_left hCW0 hS0W0
  let rHi14 := rSum42.slice 28 14 (by decide)
  let hHi14W : rHi14.DisjointWires rWork := hSW42.compose_left _
  let rWork1 : QRegister (14 + mWork) n := rHi14.concat rWork hHi14W
  let hCW1 : rCore.DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (hCSum42.compose_right _)) (QRegExt.disjointWires_symm hCW)))
  let hS1W1 : (rSum42.compose (rSum14Slice42 1)).DisjointWires rWork1 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hHi14W (QRegExt.disjointWires_symm
      (rSum14Slice42_one_disj_slice28_14 rSum42))
      (QRegExt.disjointWires_symm (hSW42.compose_left _))))
  let rSub1 := rCore.concat (rSum42.compose (rSum14Slice42 1)) (hCSum42.compose_right _)
  have hSub1W1 : rSub1.DisjointWires rWork1 := QRegExt.disjointWires_concat_left hCW1 hS1W1
  let U0 := (selCoreSum14In42 80 0).embedUnitary (s0.uAxis 0)
  let U1 := (selCoreSum14In42 80 1).embedUnitary (s1.uAxis 1)
  let U2 := (selCoreSum14In42 80 2).embedUnitary (s2.uAxis 2)
  have hSub0Eq : rSub0 = rCS.compose (selCoreSum14In42 80 0) :=
    (compose_selCoreSum14In42 rCore rSum42 hCSum42 0).symm
  have hSub1Eq : rSub1 = rCS.compose (selCoreSum14In42 80 1) :=
    (compose_selCoreSum14In42 rCore rSum42 hCSum42 1).symm
  have hHi28Compose : rCS.compose ((rZLoc (fullSysCoreWires 80) 42).slice 14 28 (by decide)) =
    rHi28 := by
    apply qreg_ext; intro j
    have hj : rZLoc (fullSysCoreWires 80) 42 (QRegister.block (n := 42) 14 28 (by decide) j) =
        Fin.natAdd (fullSysCoreWires 80) (QRegister.block (n := 42) 14 28 (by decide) j) :=
      Fin.ext (by simp [rZLoc])
    exact show rCS (rZLoc (fullSysCoreWires 80) 42 (QRegister.block (n :=
      42) 14 28 (by decide) j)) =
        rSum42 (QRegister.block (n := 42) 14 28 (by decide) j) from by
      rw [hj, QRegister.concat_apply_right]
  have hHi14Compose : rCS.compose ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by decide)) =
    rHi14 := by
    apply qreg_ext; intro j
    have hj : rZLoc (fullSysCoreWires 80) 42 (QRegister.block (n := 42) 28 14 (by decide) j) =
        Fin.natAdd (fullSysCoreWires 80) (QRegister.block (n := 42) 28 14 (by decide) j) :=
      Fin.ext (by simp [rZLoc])
    exact show rCS (rZLoc (fullSysCoreWires 80) 42 (QRegister.block (n :=
      42) 28 14 (by decide) j)) =
        rSum42 (QRegister.block (n := 42) 28 14 (by decide) j) from by
      rw [hj, QRegister.concat_apply_right]
  have hProjHi28 : rHi28.basisOutcomeProjector 0 =
      rCS.embedMatrix (((rZLoc (fullSysCoreWires 80) 42).slice 14 28 (by
        decide)).basisOutcomeProjector 0) := by
    rw [QRegister.basisOutcomeProjector, ← hHi28Compose, QRegister.embedMatrix_compose,
        ← QRegister.basisOutcomeProjector]
  have hProjHi14 : rHi14.basisOutcomeProjector 0 =
      rCS.embedMatrix (((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by
        decide)).basisOutcomeProjector 0) := by
    rw [QRegister.basisOutcomeProjector, ← hHi14Compose, QRegister.embedMatrix_compose,
        ← QRegister.basisOutcomeProjector]
  have hWork0Proj : rWork0.basisOutcomeProjector 0 =
      rHi28.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 :=
    basisOutcomeProjector_concat_zero rHi28 rWork hHi28W
  have hWork1Proj : rWork1.basisOutcomeProjector 0 =
      rHi14.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 :=
    basisOutcomeProjector_concat_zero rHi14 rWork hHi14W
  have hp0 := s0.hRealPair v 0 rCore (rSum42.compose (rSum14Slice42 0)) rWork0
    (hCSum42.compose_right _) hCW0 hS0W0 hm0
  have hp1 := s1.hRealPair v 1 rCore (rSum42.compose (rSum14Slice42 1)) rWork1
    (hCSum42.compose_right _) hCW1 hS1W1 hm1
  have hp2Raw := s2.hRealPair v 2 rCore (rSum42.compose (rSum14Slice42 2)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hm2
  have hp2 := widenActivePair_of_eq (compose_selCoreSum14In42 rCore rSum42 hCSum42 2).symm hp2Raw
  have hCommW (M : Operator (2 ^ (fullSysCoreWires 80 + 42))) :
      rWork.basisOutcomeProjector 0 * rCS.embedMatrix M =
        rCS.embedMatrix M * rWork.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rWork hCSW M 0).symm
  have hU0CommHi28 : ((rZLoc (fullSysCoreWires 80) 42).slice 14 28 (by
    decide)).basisOutcomeProjector 0 * U0.1 =
      U0.1 * ((rZLoc (fullSysCoreWires 80) 42).slice 14 28 (by decide)).basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selCoreSum14In42 80 0)) _
      (selCoreSum14In42_disj_rZSlice 0 14 28 (by decide) (by decide)) (s0.uAxis 0).1 0).symm
  have hU0CommHi14 : ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by
    decide)).basisOutcomeProjector 0 * U0.1 =
      U0.1 * ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by decide)).basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selCoreSum14In42 80 0)) _
      (selCoreSum14In42_disj_rZSlice 0 28 14 (by decide) (by decide)) (s0.uAxis 0).1 0).symm
  have hU1CommHi14 : ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by
    decide)).basisOutcomeProjector 0 * U1.1 =
      U1.1 * ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by decide)).basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selCoreSum14In42 80 1)) _
      (selCoreSum14In42_disj_rZSlice 1 28 14 (by decide) (by decide)) (s1.uAxis 1).1 0).symm
  have hMulE := uStr3AxisTri_mul_pSum42CoreZero_eq_eStream42CoreOf s0 s1 s2
  refine ⟨?_, ?_⟩
  · -- Forward: d0 ; (d1 ; d2)
    have h0Base := realizesOnProj_of_clean_embed hSub0W0 (1 : Operator _) hp0.fwd
    rw [QRegister.embedMatrix_one, one_mul, hWork0Proj, hSub0Eq,
      QRegister.embedUnitary_compose] at h0Base
    have h0Mul := RealizesOnProj.mul_right (rCS.embedMatrix pSum42CoreZero) h0Base
    have hP0Eq : (rHi28.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) *
          rCS.embedMatrix pSum42CoreZero =
        rCS.embedMatrix pSum42CoreZero * rWork.basisOutcomeProjector 0 := by
      rw [Matrix.mul_assoc, hCommW pSum42CoreZero, ← Matrix.mul_assoc, hProjHi28,
          ← rCS.embedMatrix_mul, rZSlice_proj0_mul_pSum42CoreZero 14 28 (by decide)]
    rw [hP0Eq] at h0Mul
    have h1Base := realizesOnProj_of_clean_embed hSub1W1 (1 : Operator _) hp1.fwd
    rw [QRegister.embedMatrix_one, one_mul, hWork1Proj, hSub1Eq,
      QRegister.embedUnitary_compose] at h1Base
    have h1Mul := RealizesOnProj.mul_right (rCS.embedMatrix (U0.1 * pSum42CoreZero)) h1Base
    have hP1Eq : (rHi14.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) *
          rCS.embedMatrix (U0.1 * pSum42CoreZero) =
        rCS.embedMatrix (U0.1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0 := by
      rw [Matrix.mul_assoc, hCommW (U0.1 * pSum42CoreZero), ← Matrix.mul_assoc, hProjHi14,
          ← rCS.embedMatrix_mul, ← Matrix.mul_assoc, hU0CommHi14, Matrix.mul_assoc,
          rZSlice_proj0_mul_pSum42CoreZero 28 14 (by decide)]
    rw [hP1Eq] at h1Mul
    have h2On := realizesOnProj_of_clean_embed hCSW ((U1 * U0).1 * pSum42CoreZero) hp2.fwd
    have hI1 : (rCS.embedUnitary U1).1 * (rCS.embedMatrix (U0.1 * pSum42CoreZero) *
      rWork.basisOutcomeProjector 0) =
        (rCS.embedMatrix ((U1 * U0).1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0) * 1 := by
      rw [mul_one, QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rCS.embedMatrix_mul,
          Submonoid.coe_mul, Matrix.mul_assoc]
    have h12 := h1Mul.seq_intertwine hI1 h2On
    have hI0 : (rCS.embedUnitary U0).1 * (rCS.embedMatrix pSum42CoreZero *
      rWork.basisOutcomeProjector 0) =
        (rCS.embedMatrix (U0.1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0) * 1 := by
      rw [mul_one, QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rCS.embedMatrix_mul]
    have h012 := h0Mul.seq_intertwine hI0 h12
    have hUFwd : (rCS.embedUnitary U2 * rCS.embedUnitary U1) * rCS.embedUnitary U0 =
        rCS.embedUnitary (uStr3AxisTri s0.uAxis s1.uAxis s2.uAxis) := by
      dsimp only [U2, U1, U0, uStr3AxisTri]
      simp only [← QRegister.embedUnitary_mul]
    rwa [hUFwd] at h012
  · -- Inverse: (i2 ; i1) ; i0
    have h2InvOn := realizesOnProj_of_clean_embed hCSW (eStream42CoreOf sumFn) hp2.inv
    have h1InvBase := realizesOnProj_of_clean_embed hSub1W1 (1 : Operator _) hp1.inv
    rw [QRegister.embedMatrix_one, one_mul, hWork1Proj, hSub1Eq,
        ← embedUnitary_inv_symm, QRegister.embedUnitary_compose] at h1InvBase
    have h1InvMul :=
      RealizesOnProj.mul_right (rCS.embedMatrix ((U1 * U0).1 * pSum42CoreZero)) h1InvBase
    have hInner1Inv :
        ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by decide)).basisOutcomeProjector 0 *
            ((U1.1 * U0.1) * pSum42CoreZero) =
          (U1.1 * U0.1) * pSum42CoreZero :=
      calc ((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by decide)).basisOutcomeProjector 0 *
              ((U1.1 * U0.1) * pSum42CoreZero)
          = U1.1 * (U0.1 *
            (((rZLoc (fullSysCoreWires 80) 42).slice 28 14 (by decide)).basisOutcomeProjector 0 *
              pSum42CoreZero)) := by
                rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU1CommHi14,
                    Matrix.mul_assoc U1.1, hU0CommHi14, Matrix.mul_assoc U1.1,
                      Matrix.mul_assoc U0.1]
        _ = (U1.1 * U0.1) * pSum42CoreZero := by
              rw [rZSlice_proj0_mul_pSum42CoreZero 28 14 (by decide), Matrix.mul_assoc]
    have hP1InvEq : (rHi14.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) *
          rCS.embedMatrix ((U1 * U0).1 * pSum42CoreZero) =
        rCS.embedMatrix ((U1 * U0).1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0 := by
      rw [Matrix.mul_assoc, hCommW ((U1 * U0).1 * pSum42CoreZero), ← Matrix.mul_assoc, hProjHi14,
          ← rCS.embedMatrix_mul, Submonoid.coe_mul, hInner1Inv]
    rw [hP1InvEq] at h1InvMul
    have hU2InvE : (U2⁻¹).1 * eStream42CoreOf sumFn = (U1 * U0).1 * pSum42CoreZero := by
      have hFact2 : uStr3AxisTri s0.uAxis s1.uAxis s2.uAxis = U2 * (U1 * U0) := by
        dsimp only [uStr3AxisTri, U2, U1, U0]; simp only [mul_assoc]
      calc (U2⁻¹).1 * eStream42CoreOf sumFn
          = (U2⁻¹).1 * ((U2 * (U1 * U0)).1 * pSum42CoreZero) := by rw [← hFact2, hMulE]
        _ = ((U2⁻¹ * U2).1) * ((U1 * U0).1 * pSum42CoreZero) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = (U1 * U0).1 * pSum42CoreZero := by
          rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
    have hI2 : (rCS.embedUnitary U2⁻¹).1 *
          (rCS.embedMatrix (eStream42CoreOf sumFn) * rWork.basisOutcomeProjector 0) =
        (rCS.embedMatrix ((U1 * U0).1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0) * 1 := by
      rw [mul_one, QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rCS.embedMatrix_mul, hU2InvE]
    have h21Inv := h2InvOn.seq_intertwine hI2 h1InvMul
    have h0InvBase := realizesOnProj_of_clean_embed hSub0W0 (1 : Operator _) hp0.inv
    rw [QRegister.embedMatrix_one, one_mul, hWork0Proj, hSub0Eq,
        ← embedUnitary_inv_symm, QRegister.embedUnitary_compose] at h0InvBase
    have h0InvMul := RealizesOnProj.mul_right (rCS.embedMatrix (U0.1 * pSum42CoreZero)) h0InvBase
    have hP0InvEq : (rHi28.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) *
          rCS.embedMatrix (U0.1 * pSum42CoreZero) =
        rCS.embedMatrix (U0.1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0 := by
      rw [Matrix.mul_assoc, hCommW (U0.1 * pSum42CoreZero), ← Matrix.mul_assoc, hProjHi28,
          ← rCS.embedMatrix_mul, ← Matrix.mul_assoc, hU0CommHi28, Matrix.mul_assoc,
          rZSlice_proj0_mul_pSum42CoreZero 14 28 (by decide)]
    rw [hP0InvEq] at h0InvMul
    have hU21InvE : ((U2 * U1)⁻¹).1 * eStream42CoreOf sumFn = U0.1 * pSum42CoreZero := by
      calc ((U2 * U1)⁻¹).1 * eStream42CoreOf sumFn
          = ((U2 * U1)⁻¹).1 * (((U2 * U1) * U0).1 * pSum42CoreZero) := by rw [← hMulE]; rfl
        _ = (((U2 * U1)⁻¹ * (U2 * U1)).1) * (U0.1 * pSum42CoreZero) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = U0.1 * pSum42CoreZero := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
    have hU21Eq : (rCS.embedUnitary U1)⁻¹ * rCS.embedUnitary U2⁻¹ =
        rCS.embedUnitary (U2 * U1)⁻¹ := by
      rw [embedUnitary_inv_symm, ← QRegister.embedUnitary_mul, ← _root_.mul_inv_rev]
    rw [hU21Eq] at h21Inv
    have hI21 : (rCS.embedUnitary (U2 * U1)⁻¹).1 *
          (rCS.embedMatrix (eStream42CoreOf sumFn) * rWork.basisOutcomeProjector 0) =
        (rCS.embedMatrix (U0.1 * pSum42CoreZero) * rWork.basisOutcomeProjector 0) * 1 := by
      rw [mul_one, QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rCS.embedMatrix_mul, hU21InvE]
    have h210Inv := h21Inv.seq_intertwine hI21 h0InvMul
    have hUInv : (rCS.embedUnitary U0)⁻¹ * rCS.embedUnitary (U2 * U1)⁻¹ =
        rCS.embedUnitary (uStr3AxisTri s0.uAxis s1.uAxis s2.uAxis)⁻¹ := by
      rw [embedUnitary_inv_symm, ← QRegister.embedUnitary_mul, ← _root_.mul_inv_rev]; rfl
    rwa [hUInv] at h210Inv
/-- `164`-wire (`5,204 T`) `AxisStreamSpecOf slot2AxisSum` wrapping `HybridStream168`. -/
noncomputable def axSpec218_164 : AxisStreamSpecOf slot2AxisSum 164 5204 where
  uAxis := HybridStream168Aux.uHybridStream164
  hKet := fun w {_} [_] rCore rSum14 hCS ↦
    HybridStream168Aux.uHybridStream164_compute_ket w rCore rSum14 hCS
  dAdd := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    HybridStream168Aux.dCleanHybridStreamAdd164 v w rCore rSum14 rWork hCS hCW hSW hm
  dInv := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    HybridStream168Aux.dCleanHybridStreamInv164 v w rCore rSum14 rWork hCS hCW hSW hm
  hCounts := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    HybridStream168Aux.dCleanHybridStream164_counts v w rCore rSum14 rWork hCS hCW hSW hm
  hRealPair := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    (HybridStream168Aux.dCleanHybridStream164_cleanPair_explicit
      v w rCore rSum14 rWork hCS hCW hSW hm).1
/-- `146`-wire (`5208 T`) `AxisStreamSpecOf slot2AxisSum`. -/
noncomputable def axSpec218_146 : AxisStreamSpecOf slot2AxisSum 146 5208 where
  uAxis := uHybridStream218_146
  hKet := fun w {_} [_] rCore rSum14 hCS ↦ uHybridStream218_146_compute_ket w rCore rSum14 hCS
  dAdd := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    dCleanHybridStreamAdd218_146 v w rCore rSum14 rWork hCS hCW hSW hm
  dInv := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    dCleanHybridStreamInv218_146 v w rCore rSum14 rWork hCS hCW hSW hm
  hCounts := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    dCleanHybridStream218_146_counts v w rCore rSum14 rWork hCS hCW hSW hm
  hRealPair := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    (dCleanHybridStream218_146_cleanPair_explicit v w rCore rSum14 rWork hCS hCW hSW hm).1
/-- `128`-wire (`5212 T`) `AxisStreamSpecOf slot2AxisSum`. -/
noncomputable def axSpec218_128 : AxisStreamSpecOf slot2AxisSum 128 5212 where
  uAxis := uHybridStream218_128
  hKet := fun w {_} [_] rCore rSum14 hCS ↦ uHybridStream218_128_compute_ket w rCore rSum14 hCS
  dAdd := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    dCleanHybridStreamAdd218_128 v w rCore rSum14 rWork hCS hCW hSW hm
  dInv := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    dCleanHybridStreamInv218_128 v w rCore rSum14 rWork hCS hCW hSW hm
  hCounts := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    dCleanHybridStream218_128_counts v w rCore rSum14 rWork hCS hCW hSW hm
  hRealPair := fun v w rCore rSum14 rWork hCS hCW hSW hm ↦
    (dCleanHybridStream218_128_cleanPair_explicit v w rCore rSum14 rWork hCS hCW hSW hm).1
/-- 3-tier `rSum42`-borrowed `218`-electron Stage-A unitary at `136 ≤ mWork` (`31248 T` pair). -/
noncomputable def uStr218_3AxisBorrow_136 : Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  uStr3AxisTri axSpec218_164.uAxis axSpec218_146.uAxis axSpec218_128.uAxis
/-- 3-tier `rSum42`-borrowed forward `218`-electron Stage-A stream (`136 ≤ mWork`, `15624 T`, `0
  TOFF`). -/
noncomputable def dStrAdd218_3AxisBorrow_136 {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) : DynamicCircuit Var n :=
  dStrAdd3AxisBorrow axSpec218_164 axSpec218_146 axSpec218_128 v rCore rSum42 rWork hCSum42 hCW
    hSW42
    (by omega) (by omega) (by omega)
/-- 3-tier `rSum42`-borrowed inverse `218`-electron Stage-A stream (`136 ≤ mWork`, `15624 T`, `0
  TOFF`). -/
noncomputable def dStrInv218_3AxisBorrow_136 {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) : DynamicCircuit Var n :=
  dStrInv3AxisBorrow axSpec218_164 axSpec218_146 axSpec218_128 v rCore rSum42 rWork hCSum42 hCW
    hSW42
    (by omega) (by omega) (by omega)
theorem uStr218_3AxisBorrow_136_mul_pSum42CoreZero :
    (uStr218_3AxisBorrow_136).1 * pSum42CoreZero = eStream218Core :=
  uStr3AxisTri_mul_pSum42CoreZero_eq_eStream42CoreOf axSpec218_164 axSpec218_146 axSpec218_128
theorem dStr218_3AxisBorrow_136_counts {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) :
    let dAdd := dStrAdd218_3AxisBorrow_136 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
    let dInv := dStrInv218_3AxisBorrow_136 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
    dAdd.count TOFF = 0 ∧ dInv.count TOFF = 0 ∧
      dAdd.count T ≤ 15624 ∧ dInv.count T ≤ 15624 ∧
      dInv.count T + dAdd.count T ≤ 31248 :=
  dStr3AxisBorrow_counts axSpec218_164 axSpec218_146 axSpec218_128 v rCore rSum42 rWork hCSum42 hCW
    hSW42
    (by omega) (by omega) (by omega)
theorem dStr218_3AxisBorrow_136_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) :
    let rCS := rCore.concat rSum42 hCSum42
    RealizesOnProj (rCS.embedMatrix pSum42CoreZero * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary uStr218_3AxisBorrow_136)
      (dStrAdd218_3AxisBorrow_136 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork) ∧
    RealizesOnProj (rCS.embedMatrix eStream218Core * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary uStr218_3AxisBorrow_136⁻¹)
      (dStrInv218_3AxisBorrow_136 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork) :=
  dStr3AxisBorrow_realizesOnProj axSpec218_164 axSpec218_146 axSpec218_128 v rCore rSum42 rWork
    hCSum42 hCW hSW42
    (by omega) (by omega) (by omega)
attribute [irreducible] dStrAdd218_3AxisBorrow_136 dStrInv218_3AxisBorrow_136
  uStr218_3AxisBorrow_136
end Impl
end Bell18StageABridge_Borrow136.ChiralD

namespace Bell18StageABridge_Borrow136
noncomputable section Impl
open Operator QProg Matrix
local instance (priority := 1000000) instGroupUnitaryFast_B18Borrow136 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_B18Borrow136 (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
local instance (priority := 1000000) instNeZero_B18Borrow136 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (TOFF T)
open FullSysCatSegmentBridge (fullSysCoreWires)
open HoistBorrow42ProjBridge (RealizesOnProj)
open StageAConjHAndStreamBridge
  (pSum42CoreZero eStream218Core)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (realizesOnProj_congr_unitary)
open StageADeconstrAndQftShare
  (uStr218_3Axis uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core
   inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero)
open Bell18StageABridge_Borrow136.ChiralD
  (dStrAdd218_3AxisBorrow_136 dStrInv218_3AxisBorrow_136
   uStr218_3AxisBorrow_136_mul_pSum42CoreZero
   dStr218_3AxisBorrow_136_counts dStr218_3AxisBorrow_136_realizesOnProj)
private theorem realizesOnProj_uStr218_3Axis_of_stream_eq_loc
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    {uStr : Unitary (2 ^ (fullSysCoreWires 80 + 42))}
    (hUStr : uStr.1 * pSum42CoreZero = eStream218Core)
    {rCore : QRegister (fullSysCoreWires 80) n}
    {rSum42 : QRegister 42 n} {rWork : QRegister mWork n}
    (hCSum42 : rCore.DisjointWires rSum42)
    {dAdd dInv : DynamicCircuit Var n}
    (hAdd : RealizesOnProj
      ((rCore.concat rSum42 hCSum42).embedMatrix pSum42CoreZero * rWork.basisOutcomeProjector 0)
      ((rCore.concat rSum42 hCSum42).embedUnitary uStr) dAdd)
    (hInv : RealizesOnProj
      ((rCore.concat rSum42 hCSum42).embedMatrix eStream218Core * rWork.basisOutcomeProjector 0)
      ((rCore.concat rSum42 hCSum42).embedUnitary uStr⁻¹) dInv) :
    let rCS := rCore.concat rSum42 hCSum42
    RealizesOnProj (rCS.embedMatrix pSum42CoreZero * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary uStr218_3Axis) dAdd ∧
    RealizesOnProj (rCS.embedMatrix eStream218Core * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary uStr218_3Axis⁻¹) dInv := by
  intro rCS
  have hUStrInv : (uStr⁻¹).1 * eStream218Core = pSum42CoreZero := by
    calc (uStr⁻¹).1 * eStream218Core
        = (uStr⁻¹).1 * (uStr.1 * pSum42CoreZero) := by rw [← hUStr]
      _ = ((uStr⁻¹ * uStr).1) * pSum42CoreZero := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = pSum42CoreZero := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  refine ⟨realizesOnProj_congr_unitary ?_ hAdd, realizesOnProj_congr_unitary ?_ hInv⟩
  · rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc,
        ← rCS.embedMatrix_mul, ← rCS.embedMatrix_mul, hUStr,
        uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core]
  · rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc,
        ← rCS.embedMatrix_mul, ← rCS.embedMatrix_mul, hUStrInv,
        inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero]
/-- Self-contained `rSum42`-borrowed forward `218`-electron stream (`136 ≤ mWork`, `0 TOFF`). -/
noncomputable def dStrAdd218_3AxisBorrow_auto {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) : DynamicCircuit Var n :=
  dStrAdd218_3AxisBorrow_136 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
/-- Self-contained `rSum42`-borrowed inverse `218`-electron stream (`136 ≤ mWork`, `0 TOFF`). -/
noncomputable def dStrInv218_3AxisBorrow_auto {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) : DynamicCircuit Var n :=
  dStrInv218_3AxisBorrow_136 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
theorem dStr218_3AxisBorrow_auto_counts {Var : Type} {mWork n : ℕ}
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) :
    let dAdd := dStrAdd218_3AxisBorrow_auto v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
    let dInv := dStrInv218_3AxisBorrow_auto v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
    dAdd.count TOFF = 0 ∧ dInv.count TOFF = 0 ∧
      dAdd.count T + dInv.count T ≤ 31248 := by
  dsimp only [dStrAdd218_3AxisBorrow_auto, dStrInv218_3AxisBorrow_auto]
  have hc := dStr218_3AxisBorrow_136_counts (Var :=
    Var) v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
  exact ⟨hc.1, hc.2.1, (Nat.add_comm _ _).trans_le hc.2.2.2.2⟩
theorem dStr218_3AxisBorrow_auto_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork) (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 136 ≤ mWork) :
    let rCS := rCore.concat rSum42 hCSum42
    RealizesOnProj (rCS.embedMatrix pSum42CoreZero * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary uStr218_3Axis)
      (dStrAdd218_3AxisBorrow_auto v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork) ∧
    RealizesOnProj (rCS.embedMatrix eStream218Core * rWork.basisOutcomeProjector 0)
      (rCS.embedUnitary uStr218_3Axis⁻¹)
      (dStrInv218_3AxisBorrow_auto v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork) := by
  dsimp only [dStrAdd218_3AxisBorrow_auto, dStrInv218_3AxisBorrow_auto]
  have hr := dStr218_3AxisBorrow_136_realizesOnProj v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
  exact realizesOnProj_uStr218_3Axis_of_stream_eq_loc uStr218_3AxisBorrow_136_mul_pSum42CoreZero
    hCSum42 hr.1 hr.2
attribute [irreducible] dStrAdd218_3AxisBorrow_auto dStrInv218_3AxisBorrow_auto
end Impl
end Bell18StageABridge_Borrow136
set_option exponentiation.threshold 256
end B18_SelfContainedBorrow136

noncomputable section Bell18StageAAAZ

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
set_option genSizeOf false

namespace Bell18StageABridge

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn

local instance (priority := 1000000) instNeZero_B18 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast_B18 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open Operator QProg Matrix Real
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
open InterWalkRSum42Hoist
  (kFull80 rCoreFull rSegFull rSum0 E_rawStream42 pSum42Zero qreg_ext qreg_block_apply)
open Barrel3PassSelectStitch (rCoreSeg)
open SelectCtrlStitch (rSegFull_compose_rCoreSeg_eq)
open CoinDispatchedBarrel288 (uBarrelFast)
open PosPostPrep80MergedVep (uSwapCore3967)
open Leaf4Ext48TopStitch
  (rCoreFull_disj_rSum0 rPGIdle pPGIdleZero hSum0_disj_PGIdle)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_concat_left disjointWires_compose_of_disjoint)
open PosSlots24BranchConcrete (posCoreWires)
open NuclearTwistRealizes (slot2AxisSum)
open ForestQft117BundleNoTopBridge
  (pStream217Core pStream218Core rCoreInCoreSum42)
open Slot0SubAdd14And217Stream (rSum14Slice42)
open CoinBarrelPureCnotLoad
  (uBarrelFast_comm_E_rawStream42)
open BoothOpt_06_Stream217ZeroSave0Width128 (uStream217Spec131)
open ZeroHypElecHadHCompAndPass123Closure (uLensSwap)
open DoubleDutyFoldedRealizesBridge
  (rPG7Full selPosCoreInCore80)
open StageADeconstrCore
  (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
   concat_compose_selDataInAct concat_compose_selMeasInAct
   selDataInAct_disj_selMeasInAct)
open StageAConjHAndStreamBridge
  (rCSFull80 embedMatrix_diagonal_local uPointElec18
   pSum42CoreZero eStream217Core eStream218Core rZLoc uStr3AxisOfSpec
   uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core eStream217Core_mul_conjTranspose
   eStream218Core_mul_conjTranspose basisOutcomeProjector_mul_conjTranspose_assoc
   unitary_inv_val_eq_conjTranspose_assoc conj_fix_of_comm_assoc
   embedMatrix_basisOutcomeProjector_zero_assoc basisBits_extractIndex_assoc
   diagonal_comm_op_assoc)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (uAnchorFrame embedMatrix_selSubstSlot0_eq L_slot0 L_slot0Of
   embedUnitary_permutationUnitary_eq liftRegPerm rDataSubstSlot0_apply_slot0
   rSlot0InCore rSlot0InFull selLiftAct selSubstSlot0 uBarrelFastAct
   uBarrelFastAct_mul_self uBarrelFastAct_eq_embedData_rCoreFull
   uSlot0MeasSwap uSlot0MeasSwap_mul_self)
open StageADeconstrAndQftShare
  (rPosCoreInFull E_raw217 uStr218_3Axis
   rCSFull80_embedMatrix_eStream218Core uSlot0MeasSwap_conj_uSlot0Sum42Add_eq
   uSlot0Sum42Full_inv_mul_E_rawStream42 selSubstSlot0_embedMatrix_E_raw217_eq
   uBarrelSlot0_comm_pSum42Zero uInnerSwapFull selAAZ_AA selAAZ_Z selAAZ_Data selAAZ_Anc
   selAAZ_Data_disj_Z selAAZ_Anc_disj_Data selAAZ_Anc_disj_Z uSw_AAZ uXorSubst_AAZ
   uXorData_AAZ uPhiAnc_AAZ uPhi217_AAZ uStr218_AAZ uStr217_AAZ uHeadAnc_AAZ uHeadData_AAZ
   F_AAZ Finv_AAZ F_AAZ_mul_Finv_AAZ uData9_AAZ uData9_AAZ_eq_prod9 uData9_AAZ_mul_PZ_eq
   Finv_mul_uXorSubst_mul_F_eq Finv_mul_uPhiAnc_mul_F_eq Finv_mul_uHeadAnc_mul_F_eq
   Pc2_AAZ Pc2_AAZ_zero_add_one F_AAZ_comm_Pc2_AAZ Finv_mul_uSw_mul_F_on_Pc20
   uSw_AAZ_mul_self uXorSubst_AAZ_mul_self uCSDiag_comm_AAZ stream42DiagFn P218_AAZ P217_AAZ
   P218_AAZ_def P218_AAZ_eq_diag Pc2_AAZ_eq_rCS_diagonal uStr217_AAZ_comm_Pc2
   uHeadData_and_Anc_Pc2 uLensSwap_L_slot0Of_eq_embed18 uStr218_AAZ_def uSw_AAZ_def
   uSw_AAZ_comm_Pc2_and_streams uData9_AAZ_fix_Pc21 F_AAZ_InnerSwap_Finv_eq
   uMid3_AAZ_fix_Pc21_P218 D_carry_AAZ rCore24InPos carryIdxOfAncAnd24 selAAZ_HeldAct
   uPhiAnc_AAZ_def D_carry_AAZ_eq_sum_anc_core24 uMid5_AAZ_comm_D_carry_on_P218
   rCSFull80_compose_rCoreInCoreSum42_eq embedMatrix_basisOutcomeProjector_gen_part4
   conjTranspose_comm_of_comm_selfAdj_part4 uBarrelAndSlot0_comm_pPGIdle11
   rCoreFull_disj_rPGIdle11 rSlot0InFull_disj_rPGIdle11 sum_diagonal_part4)
open Bell18StreamOffset
  (splitSysCatEquiv catModAddMidPerm catModAddPerm catModAddUnitary
   elec18AxisVal uElec18AxisAdd14 selElec18Sum14In42 compose_selElec18Sum14In42
   uElec18Sum42Add)
open Bell18StageABridgeJunction
  (basisBits_catModAdd_replaceIndex uAddStageAFull selAncSum0InFull18
   uAdd0AncFull18 uAnchorFrame_uAddStageAFull_eq)

private lemma uStr218_mul_pSum42 : uStr218_3Axis.1 * pSum42CoreZero = eStream218Core :=
  StageADeconstrAndQftShare.uStr218_3Axis_mul_pSum42CoreZero_eq_eStream218Core

private abbrev F_AAZ_def :=
  @StageADeconstrAndQftShare.F_AAZ.eq_1
private abbrev Finv_AAZ_def :=
  @StageADeconstrAndQftShare.Finv_AAZ.eq_1
private abbrev P217_AAZ_def :=
  @StageADeconstrAndQftShare.P217_AAZ.eq_1
private abbrev E_raw217_def :=
  @StageADeconstrAndQftShare.E_raw217.eq_1
private abbrev uStr217_AAZ_def :=
  @StageADeconstrAndQftShare.uStr217_AAZ.eq_1
private abbrev uHeadData_AAZ_def :=
  @StageADeconstrAndQftShare.uHeadData_AAZ.eq_1
private abbrev Pc2_AAZ_def :=
  @StageADeconstrAndQftShare.Pc2_AAZ.eq_1
private abbrev uPhi217_AAZ_def :=
  @StageADeconstrAndQftShare.uPhi217_AAZ.eq_1
private abbrev uXorData_AAZ_def :=
  @StageADeconstrAndQftShare.uXorData_AAZ.eq_1

/-! ## Section 1: `pEqReg` Projector and `uElec18Sum42Add` Swap / Commutation -/

private lemma qreg_ext_addCases {a b n : ℕ} {r₁ r₂ : QRegister (a + b) n}
    (hl : ∀ i : Fin a, r₁ (Fin.castAdd b i) = r₂ (Fin.castAdd b i))
    (hr : ∀ j : Fin b, r₁ (Fin.natAdd a j) = r₂ (Fin.natAdd a j)) :
    r₁ = r₂ := by
  apply qreg_ext; intro idx
  exact Fin.addCases (motive := fun x ↦ r₁ x = r₂ x) hl hr idx

/-- Indicator `{0, 1}` function for computational-basis equality of `r₁` and `r₂`. -/
def eqRegFn {k n : ℕ} (r₁ r₂ : QRegister k n) (x : Fin (2 ^ n)) : ℂ :=
  if ∀ i : Fin k, basisBits n x (r₁ i) = basisBits n x (r₂ i) then 1 else 0

/-- Orthogonal diagonal projector onto `{ |x⟩ : ∀ i, x[r₁ i] = x[r₂ i] }`. -/
def pEqReg {k n : ℕ} (r₁ r₂ : QRegister k n) : Operator (2 ^ n) :=
  Matrix.diagonal (eqRegFn r₁ r₂)

theorem pEqReg_conjTranspose {k n : ℕ} (r₁ r₂ : QRegister k n) :
    (pEqReg r₁ r₂)ᴴ = pEqReg r₁ r₂ := by
  rw [pEqReg, Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  simp only [Pi.star_apply, eqRegFn]; split_ifs <;> simp

theorem pEqReg_mul_self {k n : ℕ} (r₁ r₂ : QRegister k n) :
    pEqReg r₁ r₂ * pEqReg r₁ r₂ = pEqReg r₁ r₂ := by
  rw [pEqReg, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  unfold eqRegFn; split_ifs <;> simp

theorem pEqReg_symm {k n : ℕ} (r₁ r₂ : QRegister k n) :
    pEqReg r₁ r₂ = pEqReg r₂ r₁ := by
  unfold pEqReg eqRegFn
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  exact if_congr ⟨fun h i ↦ (h i).symm, fun h i ↦ (h i).symm⟩ rfl rfl

theorem pEqReg_comm_diagonal {k n : ℕ} (r₁ r₂ : QRegister k n) (f : Fin (2 ^ n) → ℂ) :
    pEqReg r₁ r₂ * Matrix.diagonal f = Matrix.diagonal f * pEqReg r₁ r₂ := by
  rw [pEqReg]
  exact diagonal_comm_op_assoc _ _

theorem embedMatrix_pEqReg {k m n : ℕ} (r : QRegister m n) (s₁ s₂ : QRegister k m) :
    r.embedMatrix (pEqReg s₁ s₂) = pEqReg (r.compose s₁) (r.compose s₂) := by
  rw [pEqReg, pEqReg, embedMatrix_diagonal_local]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  unfold eqRegFn
  by_cases h : ∀ i : Fin k,
      basisBits n x ((r.compose s₁) i) = basisBits n x ((r.compose s₂) i)
  · have h' : ∀ i : Fin k,
        basisBits m (r.extractIndex x) (s₁ i) = basisBits m (r.extractIndex x) (s₂ i) := by
      simpa only [basisBits_extractIndex_assoc, QRegister.compose_apply] using h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ ∀ i : Fin k,
        basisBits m (r.extractIndex x) (s₁ i) = basisBits m (r.extractIndex x) (s₂ i) := by
      simpa only [basisBits_extractIndex_assoc, QRegister.compose_apply] using h
    rw [ite_eq_right h', ite_eq_right h]

theorem embedMatrix_comm_pEqReg_of_disjoint {k m n : ℕ}
    (rM : QRegister m n) (r₁ r₂ : QRegister k n)
    (h₁₂ : r₁.DisjointWires r₂) (hM₁ : rM.DisjointWires r₁) (hM₂ : rM.DisjointWires r₂)
    (A : Operator (2 ^ m)) :
    rM.embedMatrix A * pEqReg r₁ r₂ = pEqReg r₁ r₂ * rM.embedMatrix A := by
  let rPair : QRegister (k + k) n := r₁.concat r₂ h₁₂
  let s₁ : QRegister k (k + k) := ⟨Fin.castAdd k, Fin.castAdd_injective k k⟩
  let s₂ : QRegister k (k + k) := ⟨Fin.natAdd k, Fin.natAdd_injective k k⟩
  have hs₁ : rPair.compose s₁ = r₁ := by
    apply qreg_ext; intro i
    change (r₁.concat r₂ h₁₂) (Fin.castAdd k i) = r₁ i
    rw [QRegister.concat_apply_left]
  have hs₂ : rPair.compose s₂ = r₂ := by
    apply qreg_ext; intro i
    change (r₁.concat r₂ h₁₂) (Fin.natAdd k i) = r₂ i
    rw [QRegister.concat_apply_right]
  have hDisj : rM.DisjointWires rPair :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left h₁₂ (QRegExt.disjointWires_symm hM₁)
      (QRegExt.disjointWires_symm hM₂)))
  have hEq : pEqReg r₁ r₂ = rPair.embedMatrix (pEqReg s₁ s₂) := by
    rw [embedMatrix_pEqReg, hs₁, hs₂]
  rw [hEq]
  exact rM.embedMatrix_comm_of_disjoint rPair hDisj A _

private lemma matrix_ext_mulVec_single {d : ℕ} {A B : Operator d}
    (h : ∀ j : Fin d, A.mulVec (Pi.single j 1) = B.mulVec (Pi.single j 1)) : A = B := by
  ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (h j) i

private lemma diagonal_mulVec_single {d : ℕ} (f : Fin d → ℂ) (j : Fin d) :
    (Matrix.diagonal f).mulVec (Pi.single j 1) = f j • Pi.single j 1 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.diagonal_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  · intro b _ hbj; simp [hbj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private lemma embed_catModAddUnitary_mulVec_single {N k B : ℕ}
    (rSys : QRegister k N) (rCat : QRegister B N) (hSC : rSys.DisjointWires rCat)
    (shift : BitAssignment k → ℕ) (j : Fin (2 ^ N)) :
    ((rSys.concat rCat hSC).embedUnitary (catModAddUnitary k B shift)).1.mulVec (Pi.single j 1) =
      Pi.single ((rSys.concat rCat hSC).replaceIndex j
        (catModAddPerm k B shift ((rSys.concat rCat hSC).extractIndex j))) 1 := by
  let rSC := rSys.concat rCat hSC
  rw [QRegister.embedUnitary_val, catModAddUnitary, rSC.embedMatrix_mulVec_single_factors,
    permutationUnitary_mulVec_single, rSC.tensorState_single_replaceIndex]

private lemma embed_catModAddUnitary_comm_pEqReg {N k q B : ℕ}
    (rSys : QRegister k N) (rCat : QRegister B N) (hSC : rSys.DisjointWires rCat)
    (r₁ r₂ : QRegister q N) (h₁C : r₁.DisjointWires rCat) (h₂C : r₂.DisjointWires rCat)
    (shift : BitAssignment k → ℕ) :
    ((rSys.concat rCat hSC).embedUnitary (catModAddUnitary k B shift)).1 * pEqReg r₁ r₂ =
      pEqReg r₁ r₂ * ((rSys.concat rCat hSC).embedUnitary (catModAddUnitary k B shift)).1 := by
  refine matrix_ext_mulVec_single fun j ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pEqReg,
      diagonal_mulVec_single, Matrix.mulVec_smul,
      embed_catModAddUnitary_mulVec_single, diagonal_mulVec_single]
  have hEqFn : eqRegFn r₁ r₂ ((rSys.concat rCat hSC).replaceIndex j
      (catModAddPerm k B shift ((rSys.concat rCat hSC).extractIndex j))) =
      eqRegFn r₁ r₂ j := by
    unfold eqRegFn
    refine if_congr ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩ rfl rfl
    · have h1 := basisBits_catModAdd_replaceIndex rSys rCat hSC shift j (r₁ i)
      have h2 := basisBits_catModAdd_replaceIndex rSys rCat hSC shift j (r₂ i)
      rw [dite_eq_right (fun ⟨c, hc⟩ ↦ h₁C.ne i c hc.symm)] at h1
      rw [dite_eq_right (fun ⟨c, hc⟩ ↦ h₂C.ne i c hc.symm)] at h2
      exact h1.symm.trans ((h i).trans h2)
    · have h1 := basisBits_catModAdd_replaceIndex rSys rCat hSC shift j (r₁ i)
      have h2 := basisBits_catModAdd_replaceIndex rSys rCat hSC shift j (r₂ i)
      rw [dite_eq_right (fun ⟨c, hc⟩ ↦ h₁C.ne i c hc.symm)] at h1
      rw [dite_eq_right (fun ⟨c, hc⟩ ↦ h₂C.ne i c hc.symm)] at h2
      exact h1.trans ((h i).trans h2.symm)
  rw [hEqFn]

private lemma embed_catModAddUnitary_mul_pEqReg_eq {N k B : ℕ}
    (r₁ r₂ : QRegister k N) (rCat : QRegister B N)
    (h₁C : r₁.DisjointWires rCat) (h₂C : r₂.DisjointWires rCat)
    (shift : BitAssignment k → ℕ) :
    ((r₁.concat rCat h₁C).embedUnitary (catModAddUnitary k B shift)).1 * pEqReg r₁ r₂ =
      ((r₂.concat rCat h₂C).embedUnitary (catModAddUnitary k B shift)).1 * pEqReg r₁ r₂ := by
  refine matrix_ext_mulVec_single fun j ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pEqReg, diagonal_mulVec_single,
      Matrix.mulVec_smul, Matrix.mulVec_smul,
      embed_catModAddUnitary_mulVec_single, embed_catModAddUnitary_mulVec_single]
  by_cases hEq : ∀ i : Fin k, basisBits N j (r₁ i) = basisBits N j (r₂ i)
  · have hShiftEq : shift (fun i ↦ basisBits N j (r₁ i)) =
        shift (fun i ↦ basisBits N j (r₂ i)) :=
      congrArg shift (funext hEq)
    have hIdx : (r₁.concat rCat h₁C).replaceIndex j
          (catModAddPerm k B shift ((r₁.concat rCat h₁C).extractIndex j)) =
        (r₂.concat rCat h₂C).replaceIndex j
          (catModAddPerm k B shift ((r₂.concat rCat h₂C).extractIndex j)) := by
      apply eq_of_basisBits_eq; intro w
      rw [basisBits_catModAdd_replaceIndex r₁ rCat h₁C shift j w,
          basisBits_catModAdd_replaceIndex r₂ rCat h₂C shift j w, hShiftEq]
    rw [hIdx]
  · have hZero : eqRegFn r₁ r₂ j = 0 := ite_eq_right hEq
    rw [hZero, zero_smul, zero_smul]

private lemma unitary_inv_comm {d : ℕ} (U : Unitary d) {P : Operator d}
    (h : U.1 * P = P * U.1) : (U⁻¹).1 * P = P * (U⁻¹).1 := by
  have hR : U.1 * (U⁻¹).1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hL : (U⁻¹).1 * U.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc (U⁻¹).1 * P
      = (U⁻¹).1 * (P * (U.1 * (U⁻¹).1)) := by rw [hR, Matrix.mul_one]
    _ = ((U⁻¹).1 * U.1) * (P * (U⁻¹).1) := by
          rw [← Matrix.mul_assoc P U.1 (U⁻¹).1, ← h]
          simp only [Matrix.mul_assoc]
    _ = P * (U⁻¹).1 := by rw [hL, Matrix.one_mul]

private lemma mul_comm_op {d : ℕ} {A B P : Operator d}
    (hA : A * P = P * A) (hB : B * P = P * B) :
    (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

/-- Both `uElec18Sum42Add` and `uElec18Sum42Add⁻¹` on `(rSys, rSum42)` commute with `pEqReg r₁ r₂`
whenever `r₁` and `r₂` are wire-disjoint from `rSum42`. -/
theorem embed_uElec18Sum42Add_comm_pEqReg {n q : ℕ}
    (rSys : QRegister 18 n) (rSum42 : QRegister 42 n) (hSS : rSys.DisjointWires rSum42)
    (r₁ r₂ : QRegister q n) (h₁S : r₁.DisjointWires rSum42) (h₂S : r₂.DisjointWires rSum42) :
    let U := (rSys.concat rSum42 hSS).embedUnitary uElec18Sum42Add
    U.1 * pEqReg r₁ r₂ = pEqReg r₁ r₂ * U.1 ∧
    (U⁻¹).1 * pEqReg r₁ r₂ = pEqReg r₁ r₂ * (U⁻¹).1 := by
  intro U
  have hAxis : ∀ (w : Fin 3) (sh : BitAssignment 18 → ℕ),
      (((rSys.concat rSum42 hSS).compose (selElec18Sum14In42 w)).embedUnitary
        (catModAddUnitary 18 14 sh)).1 * pEqReg r₁ r₂ =
      pEqReg r₁ r₂ * (((rSys.concat rSum42 hSS).compose (selElec18Sum14In42 w)).embedUnitary
        (catModAddUnitary 18 14 sh)).1 := fun w sh ↦ by
    rw [compose_selElec18Sum14In42 rSys rSum42 hSS w]
    exact embed_catModAddUnitary_comm_pEqReg rSys (rSum42.compose (rSum14Slice42 w))
      (hSS.compose_right _) r₁ r₂ (h₁S.compose_right _) (h₂S.compose_right _) sh
  have hFwd : U.1 * pEqReg r₁ r₂ = pEqReg r₁ r₂ * U.1 := by
    dsimp only [U]
    rw [uElec18Sum42Add, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose]
    unfold uElec18AxisAdd14
    simp only [Submonoid.coe_mul]
    exact mul_comm_op (mul_comm_op (hAxis 2 _) (hAxis 1 _)) (hAxis 0 _)
  exact ⟨hFwd, unitary_inv_comm U hFwd⟩

/-- On `pEqReg r₁ r₂`, `uElec18Sum42Add` (and inverse) swaps `r₁` to `r₂`. -/
theorem embed_uElec18Sum42Add_mul_pEqReg_eq {n : ℕ}
    (r₁ r₂ : QRegister 18 n) (rSum42 : QRegister 42 n)
    (h₁S : r₁.DisjointWires rSum42) (h₂S : r₂.DisjointWires rSum42) :
    let U₁ := (r₁.concat rSum42 h₁S).embedUnitary uElec18Sum42Add
    let U₂ := (r₂.concat rSum42 h₂S).embedUnitary uElec18Sum42Add
    U₁.1 * pEqReg r₁ r₂ = U₂.1 * pEqReg r₁ r₂ ∧
    (U₁⁻¹).1 * pEqReg r₁ r₂ = (U₂⁻¹).1 * pEqReg r₁ r₂ := by
  intro U₁ U₂
  have hSwapAxis : ∀ (w : Fin 3) (sh : BitAssignment 18 → ℕ),
      (((r₁.concat rSum42 h₁S).compose (selElec18Sum14In42 w)).embedUnitary
        (catModAddUnitary 18 14 sh)).1 * pEqReg r₁ r₂ =
      (((r₂.concat rSum42 h₂S).compose (selElec18Sum14In42 w)).embedUnitary
        (catModAddUnitary 18 14 sh)).1 * pEqReg r₁ r₂ := fun w sh ↦ by
    rw [compose_selElec18Sum14In42 r₁ rSum42 h₁S w,
        compose_selElec18Sum14In42 r₂ rSum42 h₂S w]
    exact embed_catModAddUnitary_mul_pEqReg_eq r₁ r₂ (rSum42.compose (rSum14Slice42 w))
      (h₁S.compose_right _) (h₂S.compose_right _) sh
  have hCommAxis : ∀ (rSys : QRegister 18 n) (hSS : rSys.DisjointWires rSum42)
      (w : Fin 3) (sh : BitAssignment 18 → ℕ),
      (((rSys.concat rSum42 hSS).compose (selElec18Sum14In42 w)).embedUnitary
        (catModAddUnitary 18 14 sh)).1 * pEqReg r₁ r₂ =
      pEqReg r₁ r₂ * (((rSys.concat rSum42 hSS).compose (selElec18Sum14In42 w)).embedUnitary
        (catModAddUnitary 18 14 sh)).1 := fun rSys hSS w sh ↦ by
    rw [compose_selElec18Sum14In42 rSys rSum42 hSS w]
    exact embed_catModAddUnitary_comm_pEqReg rSys (rSum42.compose (rSum14Slice42 w))
      (hSS.compose_right _) r₁ r₂ (h₁S.compose_right _) (h₂S.compose_right _) sh
  have hFwd : U₁.1 * pEqReg r₁ r₂ = U₂.1 * pEqReg r₁ r₂ := by
    dsimp only [U₁, U₂]
    rw [uElec18Sum42Add, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    unfold uElec18AxisAdd14
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rw [hSwapAxis 0 _, hCommAxis r₂ h₂S 0 _, ← Matrix.mul_assoc _ (pEqReg r₁ r₂),
        hSwapAxis 1 _, hCommAxis r₂ h₂S 1 _, Matrix.mul_assoc (pEqReg r₁ r₂),
        ← Matrix.mul_assoc _ (pEqReg r₁ r₂), hSwapAxis 2 _,
        Matrix.mul_assoc _ (pEqReg r₁ r₂), ← Matrix.mul_assoc (pEqReg r₁ r₂),
        ← hCommAxis r₂ h₂S 1 _, Matrix.mul_assoc _ (pEqReg r₁ r₂),
        ← hCommAxis r₂ h₂S 0 _]
  have hComm₂ : U₂.1 * pEqReg r₁ r₂ = pEqReg r₁ r₂ * U₂.1 :=
    (embed_uElec18Sum42Add_comm_pEqReg r₂ rSum42 h₂S r₁ r₂ h₁S h₂S).1
  have hR₂ : U₂.1 * (U₂⁻¹).1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hL₁ : (U₁⁻¹).1 * U₁.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  refine ⟨hFwd, ?_⟩
  calc (U₁⁻¹).1 * pEqReg r₁ r₂
      = (U₁⁻¹).1 * (pEqReg r₁ r₂ * (U₂.1 * (U₂⁻¹).1)) := by rw [hR₂, Matrix.mul_one]
    _ = ((U₁⁻¹).1 * U₁.1) * (pEqReg r₁ r₂ * (U₂⁻¹).1) := by
          rw [← Matrix.mul_assoc (pEqReg r₁ r₂) U₂.1 (U₂⁻¹).1, ← hComm₂, ← hFwd]
          simp only [Matrix.mul_assoc]
    _ = (U₂⁻¹).1 * pEqReg r₁ r₂ := by
          rw [hL₁, Matrix.one_mul, ← unitary_inv_comm U₂ hComm₂]

/-! ## Section 2: `cStr218_AAZ` Stream Conjugation on `AAZ` Without `P_anc0` -/

/-- `uAdd0AncFull18` lifted to `AAZ = (kFull80 + 18) + 18`. -/
noncomputable def uAddAnc_AAZ : Unitary (2 ^ ((kFull80 + 18) + 18)) :=
  selAAZ_AA.embedUnitary uAdd0AncFull18

theorem uAddAnc_AAZ_eq_embed :
    uAddAnc_AAZ =
      (selAAZ_Anc.concat (selAAZ_Data.compose rSum0)
        (selAAZ_Anc_disj_Data.compose_right rSum0)).embedUnitary uElec18Sum42Add := by
  unfold uAddAnc_AAZ uAdd0AncFull18
  rw [← QRegister.embedUnitary_compose]
  refine congrArg (fun r : QRegister (18 + 42) ((kFull80 + 18) + 18) ↦ r.embedUnitary _) ?_
  apply qreg_ext; intro idx
  unfold selAncSum0InFull18
  refine Fin.addCases (fun q ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left]
    rfl
  · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right]
    rfl

private lemma pSum42Zero_eq_rCS_pSum42CoreZero :
    rCSFull80.embedMatrix pSum42CoreZero = pSum42Zero := by
  unfold pSum42CoreZero pSum42Zero
  rw [embedMatrix_basisOutcomeProjector_zero_assoc]
  refine congrArg (fun r : QRegister 42 kFull80 ↦ r.basisOutcomeProjector 0) (qreg_ext fun j ↦ ?_)
  have hj : rZLoc (fullSysCoreWires 80) 42 j = Fin.natAdd (fullSysCoreWires 80) j :=
    Fin.ext (by simp [rZLoc])
  rw [QRegister.compose_apply, hj]
  dsimp only [rCSFull80]
  rw [QRegister.concat_apply_right]

/-- Exact action of `Finv_AAZ * uStr218_AAZ * F_AAZ` on `pSum42Zero` without `P_anc0`. -/
theorem cStr218_AAZ_mul_P_sum0 :
    (Finv_AAZ * uStr218_AAZ * F_AAZ).1 * selAAZ_Data.embedMatrix pSum42Zero =
      uAddAnc_AAZ.1 * selAAZ_Data.embedMatrix E_raw217 := by
  let F0 : Unitary (2 ^ (kFull80 + 18)) := uBarrelFastAct * uSlot0MeasSwap
  let F0inv : Unitary (2 ^ (kFull80 + 18)) := uSlot0MeasSwap * uBarrelFastAct
  let U218_0 : Unitary (2 ^ (kFull80 + 18)) :=
    (selDataInAct kFull80).embedUnitary (rCSFull80.embedUnitary uStr218_3Axis)
  let P0_0 : Operator (2 ^ (kFull80 + 18)) := (selDataInAct kFull80).embedMatrix pSum42Zero
  let E217_0 : Operator (2 ^ (kFull80 + 18)) := (selDataInAct kFull80).embedMatrix E_raw217
  have hS0Sq : uSlot0MeasSwap.1 * uSlot0MeasSwap.1 = 1 := by
    rw [← Submonoid.coe_mul, uSlot0MeasSwap_mul_self, OneMemClass.coe_one]
  have hF0inv_F0 : F0inv.1 * F0.1 = 1 := by
    have h1 : F0inv * F0 = 1 := by
      dsimp only [F0inv, F0]
      rw [_root_.mul_assoc uSlot0MeasSwap uBarrelFastAct,
          ← _root_.mul_assoc uBarrelFastAct uBarrelFastAct,
          uBarrelFastAct_mul_self, one_mul, uSlot0MeasSwap_mul_self]
    rw [← Submonoid.coe_mul, h1, OneMemClass.coe_one]
  have hU218_P0 : U218_0.1 * P0_0 = (selDataInAct kFull80).embedMatrix E_rawStream42 := by
    dsimp only [U218_0, P0_0]
    rw [← pSum42Zero_eq_rCS_pSum42CoreZero, QRegister.embedUnitary_val,
        QRegister.embedUnitary_val, ← (selDataInAct kFull80).embedMatrix_mul,
        ← rCSFull80.embedMatrix_mul, uStr218_mul_pSum42,
        rCSFull80_embedMatrix_eStream218Core]
  have hBar_E42 : uBarrelFastAct.1 * (selDataInAct kFull80).embedMatrix E_rawStream42 =
      (selDataInAct kFull80).embedMatrix E_rawStream42 * uBarrelFastAct.1 := by
    have hBFull : rCoreFull.embedUnitary (uBarrelFast (le_refl 80)) =
        rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80))) := by
      rw [← QRegister.embedUnitary_compose, rSegFull_compose_rCoreSeg_eq]
    rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val,
        ← (selDataInAct kFull80).embedMatrix_mul, hBFull, uBarrelFast_comm_E_rawStream42,
        ← hBFull, (selDataInAct kFull80).embedMatrix_mul]
  have hE42_eq : (selDataInAct kFull80).embedMatrix E_rawStream42 =
      ((selDataInAct kFull80).embedUnitary uAddStageAFull).1 * E217_0 := by
    dsimp only [E217_0]
    rw [QRegister.embedUnitary_val, ← (selDataInAct kFull80).embedMatrix_mul,
        uSlot0Sum42Full_inv_mul_E_rawStream42.2]
  have hS0Step : ∀ {X Y : Operator (2 ^ (kFull80 + 18))},
      uSlot0MeasSwap.1 * X * uSlot0MeasSwap.1 = Y →
      uSlot0MeasSwap.1 * X = Y * uSlot0MeasSwap.1 := fun {X Y} h ↦ by
    rw [← h, Matrix.mul_assoc _ uSlot0MeasSwap.1 uSlot0MeasSwap.1, hS0Sq, Matrix.mul_one]
  have hS0_Add : uSlot0MeasSwap.1 * ((selDataInAct kFull80).embedUnitary uAddStageAFull).1 =
      uAdd0AncFull18.1 * uSlot0MeasSwap.1 := by
    have h1 := congrArg Subtype.val uSlot0MeasSwap_conj_uSlot0Sum42Add_eq.1
    change (uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uAddStageAFull *
      uSlot0MeasSwap).1 = (uAnchorFrame uAddStageAFull).1 at h1
    rw [uAnchorFrame_uAddStageAFull_eq] at h1
    simp only [Submonoid.coe_mul] at h1
    exact hS0Step h1
  have hS0_E217 : uSlot0MeasSwap.1 * E217_0 = E217_0 * uSlot0MeasSwap.1 := by
    have hConj := (embedMatrix_selSubstSlot0_eq rSlot0InFull E_raw217).symm
    rw [selSubstSlot0_embedMatrix_E_raw217_eq] at hConj
    exact hS0Step hConj
  have hAA : (F0inv * U218_0 * F0).1 * P0_0 = uAdd0AncFull18.1 * E217_0 := by
    have hFP0 : F0.1 * P0_0 = P0_0 * F0.1 := uBarrelSlot0_comm_pSum42Zero
    calc (F0inv * U218_0 * F0).1 * P0_0
        = F0inv.1 * (U218_0.1 * (F0.1 * P0_0)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = uSlot0MeasSwap.1 * (uBarrelFastAct.1 *
            ((selDataInAct kFull80).embedMatrix E_rawStream42 * F0.1)) := by
            rw [hFP0, ← Matrix.mul_assoc U218_0.1, hU218_P0]
            dsimp only [F0inv]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (uSlot0MeasSwap.1 * ((selDataInAct kFull80).embedUnitary uAddStageAFull).1) *
            E217_0 * (uBarrelFastAct.1 * F0.1) := by
            rw [← Matrix.mul_assoc uBarrelFastAct.1, hBar_E42, hE42_eq]
            simp only [Matrix.mul_assoc]
      _ = uAdd0AncFull18.1 * E217_0 * (F0inv.1 * F0.1) := by
            rw [hS0_Add, Matrix.mul_assoc uAdd0AncFull18.1, hS0_E217]
            dsimp only [F0inv]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = uAdd0AncFull18.1 * E217_0 := by rw [hF0inv_F0, Matrix.mul_one]
  have hLift := congrArg selAAZ_AA.embedMatrix hAA
  have hStrEq : selAAZ_AA.embedUnitary U218_0 = uStr218_AAZ := by
    dsimp only [U218_0]
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, ← uStr218_AAZ_def]
  rw [selAAZ_AA.embedMatrix_mul, selAAZ_AA.embedMatrix_mul, ← QRegister.embedMatrix_compose,
      ← QRegister.embedMatrix_compose, ← QRegister.embedUnitary_val,
      ← QRegister.embedUnitary_val, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
      ← F_AAZ_def, ← Finv_AAZ_def, hStrEq] at hLift
  exact hLift

/-- On `P217_AAZ`, `(uAddAnc_AAZ⁻¹ * cStr218 * uHeadData_AAZ * cStr218⁻¹ * uAddAnc_AAZ)` collapses
to `uStr217_AAZ * uHeadData_AAZ * uStr217_AAZ⁻¹` with zero `P_anc0` assumption. -/
theorem cStr218_AAZ_mid5_on_P217 :
    let cStr218 := Finv_AAZ * uStr218_AAZ * F_AAZ
    (uAddAnc_AAZ⁻¹ * (cStr218 * (uHeadData_AAZ * (cStr218⁻¹ * uAddAnc_AAZ)))).1 * P217_AAZ =
      (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * P217_AAZ := by
  intro cStr218
  let P0 := selAAZ_Data.embedMatrix pSum42Zero
  let E217 := selAAZ_Data.embedMatrix E_raw217
  have hP217_decomp : P217_AAZ = E217 * E217ᴴ := by
    dsimp only [E217]
    rw [P217_AAZ_def, E_raw217_def, ← QRegister.embedMatrix_conjTranspose,
        ← selAAZ_Data.embedMatrix_mul, ← QRegister.embedMatrix_conjTranspose,
        ← rCSFull80.embedMatrix_mul, eStream217Core_mul_conjTranspose,
        QRegister.embedMatrix_compose]
  have h217_P0 : uStr217_AAZ.1 * P0 = E217 := by
    dsimp only [P0, E217]
    rw [uStr217_AAZ_def, E_raw217_def, ← pSum42Zero_eq_rCS_pSum42CoreZero,
        QRegister.embedUnitary_val, QRegister.embedMatrix_compose,
        ← selAAZ_Data.embedMatrix_mul, ← rCSFull80.embedMatrix_mul,
        uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
  have h217Inv_E : (uStr217_AAZ⁻¹).1 * E217 = P0 := by
    rw [← h217_P0, ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel,
        OneMemClass.coe_one, Matrix.one_mul]
  have hcInv_E : (cStr218⁻¹ * uAddAnc_AAZ).1 * E217 = P0 := by
    rw [Submonoid.coe_mul, Matrix.mul_assoc, ← cStr218_AAZ_mul_P_sum0,
        ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel,
        OneMemClass.coe_one, Matrix.one_mul]
  have hHead_P0 : uHeadData_AAZ.1 * P0 = P0 * uHeadData_AAZ.1 := by
    dsimp only [P0]
    rw [uHeadData_AAZ_def, pSum42Zero, QRegister.embedUnitary_val, QRegister.embedMatrix_compose,
        ← selAAZ_Data.embedMatrix_mul, ← selAAZ_Data.embedMatrix_mul]
    refine congrArg selAAZ_Data.embedMatrix ?_
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rPosCoreInFull) rSum0
      (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80) _ 0
  rw [hP217_decomp]
  calc (uAddAnc_AAZ⁻¹ * (cStr218 * (uHeadData_AAZ * (cStr218⁻¹ * uAddAnc_AAZ)))).1 *
          (E217 * E217ᴴ)
      = (uAddAnc_AAZ⁻¹).1 * (cStr218.1 * (uHeadData_AAZ.1 *
          (((cStr218⁻¹ * uAddAnc_AAZ).1 * E217) * E217ᴴ))) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (uAddAnc_AAZ⁻¹).1 * ((cStr218.1 * P0) * (uHeadData_AAZ.1 * E217ᴴ)) := by
          rw [hcInv_E, ← Matrix.mul_assoc uHeadData_AAZ.1 P0, hHead_P0]
          simp only [Matrix.mul_assoc]
    _ = ((uAddAnc_AAZ⁻¹ * uAddAnc_AAZ).1 * E217) * (uHeadData_AAZ.1 * E217ᴴ) := by
          dsimp only [cStr218, P0, E217]
          rw [cStr218_AAZ_mul_P_sum0]
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = E217 * (uHeadData_AAZ.1 * E217ᴴ) := by
          rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
    _ = (uStr217_AAZ.1 * P0) * (uHeadData_AAZ.1 * E217ᴴ) := by rw [h217_P0]
    _ = (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * (E217 * E217ᴴ) := by
          rw [Matrix.mul_assoc uStr217_AAZ.1, ← Matrix.mul_assoc P0, ← hHead_P0,
              ← h217Inv_E]
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]

/-! ## Section 3: `AAZH = ((kFull80 + 18) + 18) + 18` Bell-18 Inner-Swap Closure -/

abbrev kAAZ : ℕ := (kFull80 + 18) + 18
abbrev kAAZH : ℕ := kAAZ + 18

abbrev selAAZH_AAZ : QRegister kAAZ kAAZH := selDataInAct kAAZ
abbrev selAAZH_Held : QRegister 18 kAAZH := selMeasInAct kAAZ
abbrev selAAZH_AA : QRegister (kFull80 + 18) kAAZH := selAAZH_AAZ.compose selAAZ_AA
abbrev selAAZH_Data : QRegister kFull80 kAAZH := selAAZH_AAZ.compose selAAZ_Data
abbrev selAAZH_Anc : QRegister 18 kAAZH := selAAZH_AAZ.compose selAAZ_Anc
abbrev selAAZH_Z : QRegister 18 kAAZH := selAAZH_AAZ.compose selAAZ_Z

theorem selAAZH_AAZ_disj_Held : selAAZH_AAZ.DisjointWires selAAZH_Held :=
  selDataInAct_disj_selMeasInAct kAAZ

theorem selAAZH_Anc_disj_Held : selAAZH_Anc.DisjointWires selAAZH_Held :=
  selAAZH_AAZ_disj_Held.compose_left selAAZ_Anc

theorem selAAZH_Data_disj_Held : selAAZH_Data.DisjointWires selAAZH_Held :=
  selAAZH_AAZ_disj_Held.compose_left selAAZ_Data

/-- Bell-partner `rHeld18` addition into `rSum0` on `AAZH`. -/
noncomputable def uAddHeld_AAZH : Unitary (2 ^ kAAZH) :=
  (selAAZH_Held.concat (selAAZH_Data.compose rSum0)
    (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))).embedUnitary
      uElec18Sum42Add

/-- Anchor `rAnchor18` addition into `rSum0` on `AAZH`. -/
noncomputable def uAddAnc_AAZH : Unitary (2 ^ kAAZH) :=
  selAAZH_AAZ.embedUnitary uAddAnc_AAZ

/-- 7-step Bell-18 middle unitary `uPhiAnc⁻¹ * uAddHeld⁻¹ * uMid3 * uAddHeld * uPhiAnc`. -/
noncomputable def uMid7_Bell18_AAZH : Unitary (2 ^ kAAZH) :=
  (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ⁻¹ *
    (uAddHeld_AAZH⁻¹ *
      (selAAZH_AAZ.embedUnitary (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)) *
        uAddHeld_AAZH))) *
    selAAZH_AAZ.embedUnitary uPhiAnc_AAZ

/-- Full 11-step (`uSw * uXorSubst * uMid7_Bell18 * uXorSubst * uSw`) Bell-18 unitary on `AAZH`. -/
noncomputable def uC9_Bell18_AAZH : Unitary (2 ^ kAAZH) :=
  (selAAZH_AAZ.embedUnitary uSw_AAZ * selAAZH_AAZ.embedUnitary uXorSubst_AAZ) *
    (uMid7_Bell18_AAZH *
      (selAAZH_AAZ.embedUnitary uXorSubst_AAZ * selAAZH_AAZ.embedUnitary uSw_AAZ))

/-- Bell-shifted stream projector `(uAddHeld⁻¹) * P218 * uAddHeld` on `AAZH` (`rSum42 = S_217`). -/
noncomputable def P218_Bell_AAZH : Operator (2 ^ kAAZH) :=
  (uAddHeld_AAZH⁻¹).1 * selAAZH_AAZ.embedMatrix P218_AAZ * uAddHeld_AAZH.1

/-- Pebbled carry-wire diagonal lifted to `AAZH`. -/
noncomputable def D_carry_Bell_AAZH (u : Fin (2 ^ 18)) : Operator (2 ^ kAAZH) :=
  selAAZH_AAZ.embedMatrix (D_carry_AAZ u)

/-- Un-anchored Bell-18 base state (`E_raw217` on `Data`, `Anc == Held`, `Z = 0`). -/
noncomputable def E_base_Bell_AAZH : Operator (2 ^ kAAZH) :=
  selAAZH_Data.embedMatrix E_raw217 * pEqReg selAAZH_Anc selAAZH_Held *
    selAAZH_Z.basisOutcomeProjector 0

/-- Anchor-frame Bell-18 initial state `F_AAZ * E_base_Bell_AAZH` entering `dInnerSwapBell18`. -/
noncomputable def E_init_Bell_AAZH : Operator (2 ^ kAAZH) :=
  (selAAZH_AAZ.embedUnitary F_AAZ).1 * E_base_Bell_AAZH

private lemma permUnitary_inv_conj_diagonal {d : ℕ} (σ : Equiv.Perm (Fin d)) (f : Fin d → ℂ) :
    ((permutationUnitary σ)⁻¹).1 * Matrix.diagonal f * (permutationUnitary σ).1 =
      Matrix.diagonal (fun x ↦ f (σ x)) := by
  have hInv : (permutationUnitary σ)⁻¹ = permutationUnitary σ.symm := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    apply Subtype.ext
    refine matrix_ext_mulVec_single fun j ↦ ?_
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      permutationUnitary_mulVec_single, Equiv.symm_apply_apply]
  refine matrix_ext_mulVec_single fun j ↦ ?_
  rw [hInv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      permutationUnitary_mulVec_single, diagonal_mulVec_single,
      Matrix.mulVec_smul, permutationUnitary_mulVec_single, Equiv.symm_apply_apply,
      diagonal_mulVec_single]

private def permElec18Sum42_CSH :
    Equiv.Perm (Fin (2 ^ ((fullSysCoreWires 80 + 42) + 18))) :=
  let sCS := selDataInAct (fullSysCoreWires 80 + 42)
  let sH := selMeasInAct (fullSysCoreWires 80 + 42)
  let sS42 := sCS.compose (QRegister.block (fullSysCoreWires 80) 42 le_rfl)
  let hHS : sH.DisjointWires sS42 :=
    (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct (fullSysCoreWires 80 +
      42)).compose_left _))
  let rHS := sH.concat sS42 hHS
  let σAxis (w : Fin 3) :=
    liftRegPerm (rHS.compose (selElec18Sum14In42 w)) (catModAddPerm 18 14 (elec18AxisVal w))
  (σAxis 0).trans ((σAxis 1).trans (σAxis 2))

private lemma P218_Bell_AAZH_eq_rCSH_diagonal :
    ∃ F : Fin (2 ^ ((fullSysCoreWires 80 + 42) + 18)) → ℂ,
      (∀ z, F z = 0 ∨ F z = 1) ∧
      P218_Bell_AAZH =
        ((selAAZH_Data.compose rCSFull80).concat selAAZH_Held
          (selAAZH_Data_disj_Held.compose_left rCSFull80)).embedMatrix (Matrix.diagonal F) := by
  let kCS := fullSysCoreWires 80 + 42
  let rCS_H := (selAAZH_Data.compose rCSFull80).concat selAAZH_Held
    (selAAZH_Data_disj_Held.compose_left rCSFull80)
  let sCS := selDataInAct kCS
  let sH := selMeasInAct kCS
  let sS42 := sCS.compose (QRegister.block (fullSysCoreWires 80) 42 le_rfl)
  let hHS : sH.DisjointWires sS42 :=
    (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct kCS).compose_left _))
  let rHS := sH.concat sS42 hHS
  have hCompCS : rCS_H.compose sCS = selAAZH_Data.compose rCSFull80 :=
    concat_compose_selDataInAct _ _ _
  have hCompH : rCS_H.compose sH = selAAZH_Held :=
    concat_compose_selMeasInAct _ _ _
  have hCompHS : rCS_H.compose rHS =
      selAAZH_Held.concat (selAAZH_Data.compose rSum0)
        (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0)) := by
    let rR := selAAZH_Held.concat (selAAZH_Data.compose rSum0)
      (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))
    change rCS_H.compose rHS = rR
    apply qreg_ext; intro idx
    refine Fin.addCases (motive := fun idx ↦ (rCS_H.compose rHS) idx = rR idx)
      (fun q ↦ ?_) (fun j ↦ ?_) idx
    · dsimp only [rHS, rR]
      rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
          ← QRegister.compose_apply rCS_H sH, hCompH]
    · change (rCS_H.compose (sH.concat
          (sCS.compose (QRegister.block (fullSysCoreWires 80) 42 le_rfl)) hHS))
          (Fin.natAdd 18 j) =
        (selAAZH_Held.concat (selAAZH_Data.compose rSum0)
          (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))) (Fin.natAdd 18
            j)
      have hj : QRegister.block (fullSysCoreWires 80) 42 le_rfl j =
          Fin.natAdd (fullSysCoreWires 80) j :=
        Fin.ext (by simp)
      rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          QRegister.compose_apply, hj, ← QRegister.compose_apply rCS_H sCS, hCompCS,
          QRegister.compose_apply, rCSFull80, QRegister.concat_apply_right,
          ← QRegister.compose_apply selAAZH_Data rSum0]
  have hU_perm : rHS.embedUnitary uElec18Sum42Add =
      permutationUnitary permElec18Sum42_CSH := by
    rw [uElec18Sum42Add, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose]
    unfold uElec18AxisAdd14 catModAddUnitary
    rw [embedUnitary_permutationUnitary_eq, embedUnitary_permutationUnitary_eq,
        embedUnitary_permutationUnitary_eq]
    apply Subtype.ext
    refine matrix_ext_mulVec_single fun j ↦ ?_
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, permutationUnitary_mulVec_single]
    exact congrArg (fun idx ↦ Pi.single idx (1 : ℂ)) rfl
  let d0 : Fin (2 ^ (kCS + 18)) → ℂ := fun z ↦
    stream42DiagFn slot2AxisSum (sCS.extractIndex z)
  refine ⟨fun z ↦ d0 (permElec18Sum42_CSH z), fun z ↦ ?_, ?_⟩
  · dsimp only [d0, stream42DiagFn]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have hP218_embed : selAAZH_AAZ.embedMatrix P218_AAZ =
        rCS_H.embedMatrix (Matrix.diagonal d0) := by
      rw [← P218_AAZ_eq_diag, ← QRegister.embedMatrix_compose, ← QRegister.compose_assoc,
          ← hCompCS, QRegister.embedMatrix_compose, embedMatrix_diagonal_local]
    have hAdd_embed : uAddHeld_AAZH =
        rCS_H.embedUnitary (permutationUnitary permElec18Sum42_CSH) := by
      unfold uAddHeld_AAZH
      rw [← hCompHS, QRegister.embedUnitary_compose, hU_perm]
    unfold P218_Bell_AAZH
    rw [hP218_embed, hAdd_embed, ← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
        QRegister.embedUnitary_val, ← rCS_H.embedMatrix_mul, ← rCS_H.embedMatrix_mul,
        permUnitary_inv_conj_diagonal]

theorem P218_Bell_AAZH_herm : P218_Bell_AAZHᴴ = P218_Bell_AAZH := by
  obtain ⟨F, h01, hEq⟩ := P218_Bell_AAZH_eq_rCSH_diagonal
  rw [hEq, embedMatrix_diagonal_local, Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  rw [Pi.star_apply]
  rcases h01 (((selAAZH_Data.compose rCSFull80).concat selAAZH_Held
    (selAAZH_Data_disj_Held.compose_left rCSFull80)).extractIndex x) with h | h <;>
    (rw [h]; simp only [star_zero, star_one])

theorem D_carry_Bell_AAZH_comm_P218_Bell (u : Fin (2 ^ 18)) :
    D_carry_Bell_AAZH u * P218_Bell_AAZH = P218_Bell_AAZH * D_carry_Bell_AAZH u := by
  obtain ⟨F, _, hEq⟩ := P218_Bell_AAZH_eq_rCSH_diagonal
  unfold D_carry_Bell_AAZH D_carry_AAZ
  rw [hEq, embedMatrix_diagonal_local, embedMatrix_diagonal_local]
  exact diagonal_comm_op_assoc _ _

private lemma embedAAZH_comm_P218_Bell_of_CSDiag (M : Operator (2 ^ kAAZ))
    (hComm : ∀ f : Fin (2 ^ (fullSysCoreWires 80 + 42)) → ℂ,
      M * (selAAZ_Data.compose rCSFull80).embedMatrix (Matrix.diagonal f) =
        (selAAZ_Data.compose rCSFull80).embedMatrix (Matrix.diagonal f) * M) :
    selAAZH_AAZ.embedMatrix M * P218_Bell_AAZH =
      P218_Bell_AAZH * selAAZH_AAZ.embedMatrix M := by
  obtain ⟨F, _, hEq⟩ := P218_Bell_AAZH_eq_rCSH_diagonal
  let kCS := fullSysCoreWires 80 + 42
  let sCS := selDataInAct kCS
  let sH := selMeasInAct kCS
  let pairIdx (c : Fin (2 ^ kCS)) (h : Fin (2 ^ 18)) : Fin (2 ^ (kCS + 18)) :=
    (basisBitsEquiv (kCS + 18)).symm (Fin.addCases (basisBits kCS c) (basisBits 18 h))
  have hPairId : ∀ z : Fin (2 ^ (kCS + 18)),
      pairIdx (sCS.extractIndex z) (sH.extractIndex z) = z := by
    intro z
    apply eq_of_basisBits_eq; intro idx
    dsimp only [pairIdx]
    change (basisBitsEquiv (kCS + 18))
      ((basisBitsEquiv (kCS + 18)).symm (Fin.addCases (basisBits kCS (sCS.extractIndex z))
        (basisBits 18 (sH.extractIndex z)))) idx = basisBits (kCS + 18) z idx
    rw [(basisBitsEquiv (kCS + 18)).apply_symm_apply]
    refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
    · rw [Fin.addCases_left, basisBits_extractIndex_assoc]
      dsimp only [sCS]; rw [selDataInAct_apply]
    · rw [Fin.addCases_right, basisBits_extractIndex_assoc]
      dsimp only [sH]; rw [selMeasInAct_apply]
  have hDiagSum : (Matrix.diagonal F : Operator (2 ^ (kCS + 18))) =
      ∑ h : Fin (2 ^ 18),
        sCS.embedMatrix (Matrix.diagonal (fun c ↦ F (pairIdx c h))) *
          sH.basisOutcomeProjector h := by
    have hTerm : ∀ h : Fin (2 ^ 18),
        sCS.embedMatrix (Matrix.diagonal (fun c ↦ F (pairIdx c h))) *
          sH.basisOutcomeProjector h =
        Matrix.diagonal (fun z ↦ if sH.extractIndex z = h then
          F (pairIdx (sCS.extractIndex z) h) else 0) := by
      intro h
      rw [embedMatrix_diagonal_local, QRegister.basisOutcomeProjector_eq_diagonal,
          Matrix.diagonal_mul_diagonal]
      refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
      by_cases hz : sH.extractIndex z = h <;> simp [hz]
    simp_rw [hTerm]
    rw [sum_diagonal_part4]
    refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
    rw [Finset.sum_eq_single (sH.extractIndex z)]
    · rw [ite_eq_left rfl, hPairId z]
    · intro b _ hb; exact ite_eq_right hb.symm
    · intro hz; exact absurd (Finset.mem_univ _) hz
  let rCS_H := (selAAZH_Data.compose rCSFull80).concat selAAZH_Held
    (selAAZH_Data_disj_Held.compose_left rCSFull80)
  have hCompCS : rCS_H.compose sCS = selAAZH_Data.compose rCSFull80 :=
    concat_compose_selDataInAct _ _ _
  have hCompH : rCS_H.compose sH = selAAZH_Held :=
    concat_compose_selMeasInAct _ _ _
  have hP218Sum : P218_Bell_AAZH =
      ∑ h : Fin (2 ^ 18),
        selAAZH_AAZ.embedMatrix
          ((selAAZ_Data.compose rCSFull80).embedMatrix
            (Matrix.diagonal (fun c ↦ F (pairIdx c h)))) *
          selAAZH_Held.basisOutcomeProjector h := by
    rw [hEq, hDiagSum, rCS_H.embedMatrix_sum]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [rCS_H.embedMatrix_mul, ← QRegister.embedMatrix_compose, hCompCS,
        QRegister.compose_assoc, QRegister.embedMatrix_compose,
        embedMatrix_basisOutcomeProjector_gen_part4, hCompH]
  rw [hP218Sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  have hMH : selAAZH_AAZ.embedMatrix M * selAAZH_Held.basisOutcomeProjector h =
      selAAZH_Held.basisOutcomeProjector h * selAAZH_AAZ.embedMatrix M :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZH_AAZ) selAAZH_Held
      selAAZH_AAZ_disj_Held M h
  rw [← Matrix.mul_assoc, ← selAAZH_AAZ.embedMatrix_mul, hComm _,
      selAAZH_AAZ.embedMatrix_mul, Matrix.mul_assoc, hMH, ← Matrix.mul_assoc]

/-- Commutation of `uPhiAnc_AAZ`, `uPhiAnc_AAZ⁻¹`, `uXorSubst_AAZ`, `uSw_AAZ` with `P218_Bell`. -/
theorem uOps_AAZH_comm_P218_Bell :
    (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ).1 * P218_Bell_AAZH =
      P218_Bell_AAZH * (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ).1 ∧
    (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ⁻¹).1 * P218_Bell_AAZH =
      P218_Bell_AAZH * (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ⁻¹).1 ∧
    (selAAZH_AAZ.embedUnitary uXorSubst_AAZ).1 * P218_Bell_AAZH =
      P218_Bell_AAZH * (selAAZH_AAZ.embedUnitary uXorSubst_AAZ).1 ∧
    (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * P218_Bell_AAZH =
      P218_Bell_AAZH * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 := by
  refine ⟨embedAAZH_comm_P218_Bell_of_CSDiag uPhiAnc_AAZ.1 (fun f ↦ (uCSDiag_comm_AAZ f).2.2.2.1),
    embedAAZH_comm_P218_Bell_of_CSDiag (uPhiAnc_AAZ⁻¹).1 (fun f ↦ (uCSDiag_comm_AAZ f).2.2.2.2.1),
    embedAAZH_comm_P218_Bell_of_CSDiag uXorSubst_AAZ.1 (fun f ↦ (uCSDiag_comm_AAZ f).2.2.2.2.2),
    ?_⟩
  have hDisjSwAdd : (selAAZH_Data.compose rCoreFull).DisjointWires
      (selAAZH_Held.concat (selAAZH_Data.compose rSum0)
        (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))) :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left _
      (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rCoreFull))
      (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZH_Data
        rCoreFull_disj_rSum0))))
  have hSwEq : selAAZH_AAZ.embedUnitary uSw_AAZ =
      (selAAZH_Data.compose rCoreFull).embedUnitary uSwapCore3967 := by
    rw [uSw_AAZ_def, ← QRegister.embedUnitary_compose, ← QRegister.compose_assoc]
  have hSwAdd : (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * uAddHeld_AAZH.1 =
      uAddHeld_AAZH.1 * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 := by
    rw [hSwEq]; unfold uAddHeld_AAZH
    exact (selAAZH_Data.compose rCoreFull).embedMatrix_comm_of_disjoint _ hDisjSwAdd _ _
  have hSwP218 :
      (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * selAAZH_AAZ.embedMatrix P218_AAZ =
      selAAZH_AAZ.embedMatrix P218_AAZ * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 := by
    rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul,
        uSw_AAZ_comm_Pc2_and_streams.2.1, selAAZH_AAZ.embedMatrix_mul]
  unfold P218_Bell_AAZH
  exact (mul_comm_op
    (mul_comm_op (unitary_inv_comm uAddHeld_AAZH hSwAdd.symm) hSwP218.symm)
    hSwAdd.symm).symm

private lemma conj_inv_comm_on {d : ℕ} (U M : Unitary d) {D P Q : Operator d}
    (hUD : U.1 * D = D * U.1) (hUPQ : U.1 * P = Q * U.1)
    (hM : M.1 * (D * Q) = D * (M.1 * Q)) :
    ((U⁻¹ * M) * U).1 * (D * P) = D * (((U⁻¹ * M) * U).1 * P) := by
  have hUID : (U⁻¹).1 * D = D * (U⁻¹).1 := unitary_inv_comm U hUD
  have hUDP : U.1 * (D * P) = (D * Q) * U.1 := by
    rw [← Matrix.mul_assoc, hUD, Matrix.mul_assoc, hUPQ, ← Matrix.mul_assoc]
  simp only [Submonoid.coe_mul]
  calc ((U⁻¹).1 * M.1 * U.1) * (D * P)
      = (U⁻¹).1 * ((M.1 * (D * Q)) * U.1) := by
          rw [Matrix.mul_assoc ((U⁻¹).1 * M.1) U.1 (D * P), hUDP]
          simp only [Matrix.mul_assoc]
    _ = ((U⁻¹).1 * D) * (M.1 * (Q * U.1)) := by
          rw [hM]
          simp only [Matrix.mul_assoc]
    _ = D * (((U⁻¹).1 * M.1 * U.1) * P) := by
          rw [hUID, ← hUPQ]
          simp only [Matrix.mul_assoc]

private lemma selAAZ_HeldAct_disj_Anc : selAAZ_HeldAct.DisjointWires selAAZ_Anc := by
  dsimp only [selAAZ_HeldAct]
  exact disjointWires_concat_left _
    (disjointWires_concat_left _
      (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rCSFull80))
        (QRegExt.disjointWires_symm selAAZ_Anc_disj_Z))
    (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rPG7Full))

theorem uMid7_Bell18_AAZH_comm_D_carry_on_P218_Bell (u : Fin (2 ^ 18)) :
    uMid7_Bell18_AAZH.1 * (D_carry_Bell_AAZH u * P218_Bell_AAZH) =
      D_carry_Bell_AAZH u * (uMid7_Bell18_AAZH.1 * P218_Bell_AAZH) := by
  let rCore24_AAZ := (selAAZ_Data.compose rPosCoreInFull).compose rCore24InPos
  have hPhiCommD : uPhiAnc_AAZ.1 * D_carry_AAZ u = D_carry_AAZ u * uPhiAnc_AAZ.1 := by
    rw [D_carry_AAZ_eq_sum_anc_core24 u, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hPhiAncA : uPhiAnc_AAZ.1 * selAAZ_Anc.basisOutcomeProjector a =
        selAAZ_Anc.basisOutcomeProjector a * uPhiAnc_AAZ.1 := by
      rw [uPhiAnc_AAZ_def, QRegister.embedUnitary_val]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZ_HeldAct)
        selAAZ_Anc selAAZ_HeldAct_disj_Anc _ a
    let rCore24InCS : QRegister (3 + 21) (fullSysCoreWires 80 + 42) :=
      (rCoreInCoreSum42 80).compose (selPosCoreInCore80.compose rCore24InPos)
    have hComp24 : (selAAZ_Data.compose rCSFull80).compose rCore24InCS = rCore24_AAZ := by
      apply qreg_ext
      intro i
      have h0 := congrArg
        (fun r : QRegister _ _ ↦ r ((selPosCoreInCore80.compose rCore24InPos) i))
        rCSFull80_compose_rCoreInCoreSum42_eq
      dsimp only [rCore24InCS, rCore24_AAZ, rPosCoreInFull,
        QRegister.compose, Function.comp] at h0 ⊢
      exact congrArg selAAZ_Data h0
    let g24 := fun c ↦ if carryIdxOfAncAnd24 a c = u then (1 : ℂ) else 0
    have hfCS : rCore24_AAZ.embedMatrix (Matrix.diagonal g24) =
        (selAAZ_Data.compose rCSFull80).embedMatrix
          (Matrix.diagonal fun y ↦ g24 (rCore24InCS.extractIndex y)) := by
      rw [← hComp24, QRegister.embedMatrix_compose, embedMatrix_diagonal_local]
    have hPhiB := (uCSDiag_comm_AAZ (fun y ↦ g24 (rCore24InCS.extractIndex y))).2.2.2.1
    rw [← hfCS] at hPhiB
    exact (mul_comm_op hPhiAncA.symm hPhiB.symm).symm
  have hAddCommD : uAddHeld_AAZH.1 * D_carry_Bell_AAZH u =
      D_carry_Bell_AAZH u * uAddHeld_AAZH.1 := by
    unfold D_carry_Bell_AAZH
    rw [D_carry_AAZ_eq_sum_anc_core24 u, selAAZH_AAZ.embedMatrix_sum,
        Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    let rAdd := selAAZH_Held.concat (selAAZH_Data.compose rSum0)
      (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))
    have hDisjAnc : rAdd.DisjointWires selAAZH_Anc :=
      disjointWires_concat_left _ (QRegExt.disjointWires_symm selAAZH_Anc_disj_Held)
        (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZH_AAZ
          (selAAZ_Anc_disj_Data.compose_right rSum0)))
    have hDisj24 : rAdd.DisjointWires (selAAZH_AAZ.compose rCore24_AAZ) := by
      refine disjointWires_concat_left _
        (QRegExt.disjointWires_symm (selAAZH_AAZ_disj_Held.compose_left rCore24_AAZ)) ?_
      dsimp only [rCore24_AAZ, selAAZH_Data]
      rw [← QRegister.compose_assoc, ← QRegister.compose_assoc]
      exact disjointWires_compose_of_disjoint selAAZH_AAZ
        (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZ_Data
          ((rCoreFull_disj_rSum0.compose_left selPosCoreInCore80).compose_left rCore24InPos)))
    have hTA : uAddHeld_AAZH.1 * selAAZH_Anc.basisOutcomeProjector a =
        selAAZH_Anc.basisOutcomeProjector a * uAddHeld_AAZH.1 :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAdd) selAAZH_Anc hDisjAnc _ a
    have hTB := rAdd.embedMatrix_comm_of_disjoint (selAAZH_AAZ.compose rCore24_AAZ) hDisj24
      uElec18Sum42Add.1
      (Matrix.diagonal fun c ↦ if carryIdxOfAncAnd24 a c = u then (1 : ℂ) else 0)
    rw [selAAZH_AAZ.embedMatrix_mul, embedMatrix_basisOutcomeProjector_gen_part4,
        ← QRegister.embedMatrix_compose]
    exact (mul_comm_op hTA.symm hTB.symm).symm
  let uMid3 := uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹)
  let uMid5 := (uPhiAnc_AAZ⁻¹ * uMid3) * uPhiAnc_AAZ
  have hPhi218 : uPhiAnc_AAZ.1 * P218_AAZ = P218_AAZ * uPhiAnc_AAZ.1 := by
    have h := (uCSDiag_comm_AAZ (stream42DiagFn slot2AxisSum)).2.2.2.1
    rwa [P218_AAZ_eq_diag] at h
  have hMid3CommD : uMid3.1 * (D_carry_AAZ u * P218_AAZ) =
      D_carry_AAZ u * (uMid3.1 * P218_AAZ) := by
    have h3 := conj_inv_comm_on uPhiAnc_AAZ⁻¹ uMid5
      (unitary_inv_comm _ hPhiCommD) (unitary_inv_comm _ hPhi218)
      (uMid5_AAZ_comm_D_carry_on_P218 u)
    have hSimp3 : ((uPhiAnc_AAZ⁻¹)⁻¹ * uMid5) * uPhiAnc_AAZ⁻¹ = uMid3 := by
      dsimp only [uMid5]
      rw [inv_inv]
      calc (uPhiAnc_AAZ * ((uPhiAnc_AAZ⁻¹ * uMid3) * uPhiAnc_AAZ)) * uPhiAnc_AAZ⁻¹
          = (uPhiAnc_AAZ * uPhiAnc_AAZ⁻¹) * uMid3 * (uPhiAnc_AAZ * uPhiAnc_AAZ⁻¹) := by
              simp only [_root_.mul_assoc]
        _ = uMid3 := by rw [mul_inv_cancel, one_mul, mul_one]
    rwa [hSimp3] at h3
  have hMid3Lift :
      (selAAZH_AAZ.embedUnitary uMid3).1 *
        (D_carry_Bell_AAZH u * selAAZH_AAZ.embedMatrix P218_AAZ) =
      D_carry_Bell_AAZH u *
        ((selAAZH_AAZ.embedUnitary uMid3).1 * selAAZH_AAZ.embedMatrix P218_AAZ) := by
    have h := congrArg selAAZH_AAZ.embedMatrix hMid3CommD
    simpa only [selAAZH_AAZ.embedMatrix_mul, QRegister.embedUnitary_val,
      D_carry_Bell_AAZH] using h
  have hPhiHD : (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ).1 * D_carry_Bell_AAZH u =
      D_carry_Bell_AAZH u * (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ).1 := by
    unfold D_carry_Bell_AAZH
    rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul, hPhiCommD,
        selAAZH_AAZ.embedMatrix_mul]
  have hAddP218 : uAddHeld_AAZH.1 * P218_Bell_AAZH =
      selAAZH_AAZ.embedMatrix P218_AAZ * uAddHeld_AAZH.1 := by
    unfold P218_Bell_AAZH
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Submonoid.coe_mul, mul_inv_cancel,
        OneMemClass.coe_one, Matrix.one_mul]
  have hStep5 := conj_inv_comm_on uAddHeld_AAZH (selAAZH_AAZ.embedUnitary uMid3)
    hAddCommD hAddP218 hMid3Lift
  rw [_root_.mul_assoc uAddHeld_AAZH⁻¹] at hStep5
  have hStep7 := conj_inv_comm_on (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ) _
    hPhiHD uOps_AAZH_comm_P218_Bell.1 hStep5
  unfold uMid7_Bell18_AAZH
  rw [QRegister.embedUnitary_inv]
  exact hStep7

private lemma F_AAZH_comm_uAddHeld_AAZH :
    selAAZH_AAZ.embedUnitary F_AAZ * uAddHeld_AAZH =
      uAddHeld_AAZH * selAAZH_AAZ.embedUnitary F_AAZ ∧
    selAAZH_AAZ.embedUnitary Finv_AAZ * uAddHeld_AAZH =
      uAddHeld_AAZH * selAAZH_AAZ.embedUnitary Finv_AAZ := by
  let rAdd := selAAZH_Held.concat (selAAZH_Data.compose rSum0)
    (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))
  have hDisjCore : (selAAZH_Data.compose rCoreFull).DisjointWires rAdd :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left _
      (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rCoreFull))
      (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZH_Data
        rCoreFull_disj_rSum0))))
  have hBarComm : selAAZH_AA.embedUnitary uBarrelFastAct * uAddHeld_AAZH =
      uAddHeld_AAZH * selAAZH_AA.embedUnitary uBarrelFastAct := by
    apply Subtype.ext; simp only [Submonoid.coe_mul]
    rw [uBarrelFastAct_eq_embedData_rCoreFull, ← QRegister.embedUnitary_compose,
        ← QRegister.embedUnitary_compose]
    change ((selAAZH_Data.compose rCoreFull).embedUnitary _).1 * uAddHeld_AAZH.1 =
      uAddHeld_AAZH.1 * ((selAAZH_Data.compose rCoreFull).embedUnitary _).1
    unfold uAddHeld_AAZH
    exact (selAAZH_Data.compose rCoreFull).embedMatrix_comm_of_disjoint rAdd hDisjCore _ _
  have hDisjLift : (selAAZH_AA.compose (selLiftAct rSlot0InFull)).DisjointWires rAdd := by
    have hCompLift : selAAZH_AA.compose (selLiftAct rSlot0InFull) =
        (selAAZH_Data.compose rSlot0InFull).concat selAAZH_Anc
          (QRegExt.disjointWires_symm ((disjointWires_compose_of_disjoint selAAZH_AAZ
            selAAZ_Anc_disj_Data).compose_right rSlot0InFull)) := by
      unfold selLiftAct
      refine qreg_ext_addCases (fun q ↦ ?_) (fun q ↦ ?_)
      · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left]
        simp only [selAAZH_AA, selAAZH_Data, selAAZ_Data, QRegister.compose_apply]
      · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right]
        simp only [selAAZH_AA, selAAZH_Anc, selAAZ_Anc, QRegister.compose_apply]
    rw [hCompLift]
    refine disjointWires_concat_left _ ?_ ?_
    · exact (QRegExt.disjointWires_symm (disjointWires_concat_left _
        (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSlot0InFull))
        (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZH_Data
          (rCoreFull_disj_rSum0.compose_left rSlot0InCore)))))
    · exact (QRegExt.disjointWires_symm (disjointWires_concat_left _ (QRegExt.disjointWires_symm
      selAAZH_Anc_disj_Held)
        (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZH_AAZ
          (selAAZ_Anc_disj_Data.compose_right rSum0)))))
  have hS0Comm : selAAZH_AA.embedUnitary uSlot0MeasSwap * uAddHeld_AAZH =
      uAddHeld_AAZH * selAAZH_AA.embedUnitary uSlot0MeasSwap := by
    apply Subtype.ext; simp only [Submonoid.coe_mul]
    rw [uSlot0MeasSwap, L_slot0, ← uLensSwap_L_slot0Of_eq_embed18 rSlot0InFull,
        ← QRegister.embedUnitary_compose]
    unfold uAddHeld_AAZH
    exact (selAAZH_AA.compose (selLiftAct rSlot0InFull)).embedMatrix_comm_of_disjoint
      rAdd hDisjLift _ _
  refine ⟨?_, ?_⟩
  · rw [F_AAZ_def, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_mul]
    change (selAAZH_AA.embedUnitary uBarrelFastAct *
      selAAZH_AA.embedUnitary uSlot0MeasSwap) * uAddHeld_AAZH = _
    rw [_root_.mul_assoc, hS0Comm, ← _root_.mul_assoc, hBarComm, _root_.mul_assoc]
  · rw [Finv_AAZ_def, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_mul]
    change (selAAZH_AA.embedUnitary uSlot0MeasSwap *
      selAAZH_AA.embedUnitary uBarrelFastAct) * uAddHeld_AAZH = _
    rw [_root_.mul_assoc, hBarComm, ← _root_.mul_assoc, hS0Comm, _root_.mul_assoc]

private lemma unitary_mul_pSum42CoreZero_idem
    (U : Unitary (2 ^ (fullSysCoreWires 80 + 42))) :
    let E := U.1 * pSum42CoreZero
    (E * Eᴴ) * E = E := by
  intro E
  have hP0Adj : pSum42CoreZero * (pSum42CoreZero)ᴴ = pSum42CoreZero :=
    basisOutcomeProjector_mul_conjTranspose_assoc _ _
  dsimp only [E]
  rw [Matrix.conjTranspose_mul, ← unitary_inv_val_eq_conjTranspose_assoc]
  calc (U.1 * pSum42CoreZero) * ((pSum42CoreZero)ᴴ * (U⁻¹).1) * (U.1 * pSum42CoreZero)
      = U.1 * ((pSum42CoreZero * (pSum42CoreZero)ᴴ) *
          (((U⁻¹ * U).1) * pSum42CoreZero)) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = U.1 * pSum42CoreZero := by
          rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul, hP0Adj]
          unfold pSum42CoreZero
          rw [QRegister.basisOutcomeProjector_mul_self]

private lemma uAddHeld_AAZH_mul_pEqReg :
    uAddHeld_AAZH.1 * pEqReg selAAZH_Anc selAAZH_Held =
      uAddAnc_AAZH.1 * pEqReg selAAZH_Anc selAAZH_Held := by
  rw [pEqReg_symm selAAZH_Anc selAAZH_Held]
  have hS := (embed_uElec18Sum42Add_mul_pEqReg_eq selAAZH_Held selAAZH_Anc
    (selAAZH_Data.compose rSum0)
    (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))
    ((disjointWires_compose_of_disjoint selAAZH_AAZ
      selAAZ_Anc_disj_Data).compose_right rSum0)).1
  have hAncEq : (selAAZH_Anc.concat (selAAZH_Data.compose rSum0)
      ((disjointWires_compose_of_disjoint selAAZH_AAZ
        selAAZ_Anc_disj_Data).compose_right rSum0)).embedUnitary
      uElec18Sum42Add = uAddAnc_AAZH := by
    unfold uAddAnc_AAZH
    rw [uAddAnc_AAZ_eq_embed, ← QRegister.embedUnitary_compose]
    refine congrArg (fun r : QRegister (18 + 42) kAAZH ↦ r.embedUnitary _)
      (qreg_ext_addCases (fun _ ↦ ?_) (fun _ ↦ ?_))
    · simp only [selAAZH_Anc, QRegister.concat_apply_left, QRegister.compose_apply]
    · simp only [selAAZH_Data, QRegister.concat_apply_right, QRegister.compose_apply]
  unfold uAddHeld_AAZH at *
  rwa [hAncEq] at hS

private lemma selAAZH_Z_proj0_mul_E_base_Bell :
    selAAZH_Z.basisOutcomeProjector 0 * E_base_Bell_AAZH = E_base_Bell_AAZH := by
  have hZ_E217 : selAAZH_Z.basisOutcomeProjector 0 * selAAZH_Data.embedMatrix E_raw217 =
      selAAZH_Data.embedMatrix E_raw217 * selAAZH_Z.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZH_Data) selAAZH_Z
      (disjointWires_compose_of_disjoint selAAZH_AAZ selAAZ_Data_disj_Z) _ 0).symm
  have hZ_Peq : selAAZH_Z.basisOutcomeProjector 0 * pEqReg selAAZH_Anc selAAZH_Held =
      pEqReg selAAZH_Anc selAAZH_Held * selAAZH_Z.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    exact (pEqReg_comm_diagonal _ _ _).symm
  unfold E_base_Bell_AAZH
  rw [← Matrix.mul_assoc (selAAZH_Z.basisOutcomeProjector 0),
      ← Matrix.mul_assoc (selAAZH_Z.basisOutcomeProjector 0), hZ_E217,
      Matrix.mul_assoc (selAAZH_Data.embedMatrix E_raw217)
        (selAAZH_Z.basisOutcomeProjector 0), hZ_Peq]
  simp only [Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]

/-- Exact stream-support invariance: `E_init_Bell_AAZH` lies in `P218_Bell_AAZH`. -/
theorem P218_Bell_AAZH_mul_E_init_Bell :
    P218_Bell_AAZH * E_init_Bell_AAZH = E_init_Bell_AAZH := by
  have hP218_e218 : pStream218Core 80 * eStream218Core = eStream218Core := by
    rw [← eStream218Core_mul_conjTranspose, ← uStr218_mul_pSum42]
    exact unitary_mul_pSum42CoreZero_idem uStr218_3Axis
  have hP218_U218 : P218_AAZ * (uStr218_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero) =
      uStr218_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero := by
    rw [P218_AAZ_def, uStr218_AAZ_def, ← pSum42Zero_eq_rCS_pSum42CoreZero,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
        ← (selAAZ_Data.compose rCSFull80).embedMatrix_mul,
        ← (selAAZ_Data.compose rCSFull80).embedMatrix_mul,
        uStr218_mul_pSum42, hP218_e218]
  have hF_cStr : F_AAZ.1 * (uAddAnc_AAZ.1 * selAAZ_Data.embedMatrix E_raw217) =
      (uStr218_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero) * F_AAZ.1 := by
    rw [← cStr218_AAZ_mul_P_sum0]
    have hFP0 : F_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero =
        selAAZ_Data.embedMatrix pSum42Zero * F_AAZ.1 := by
      dsimp only [selAAZ_Data]
      rw [F_AAZ_def, QRegister.embedUnitary_val, QRegister.embedMatrix_compose,
          ← selAAZ_AA.embedMatrix_mul, uBarrelSlot0_comm_pSum42Zero,
          selAAZ_AA.embedMatrix_mul]
    calc F_AAZ.1 * ((Finv_AAZ * uStr218_AAZ * F_AAZ).1 * selAAZ_Data.embedMatrix pSum42Zero)
        = (F_AAZ * Finv_AAZ).1 * uStr218_AAZ.1 *
            (F_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = (uStr218_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero) * F_AAZ.1 := by
            rw [F_AAZ_mul_Finv_AAZ.1, OneMemClass.coe_one, Matrix.one_mul, hFP0,
                Matrix.mul_assoc]
  have hE217_Peq : selAAZH_Data.embedMatrix E_raw217 * pEqReg selAAZH_Anc selAAZH_Held =
      pEqReg selAAZH_Anc selAAZH_Held * selAAZH_Data.embedMatrix E_raw217 :=
    embedMatrix_comm_pEqReg_of_disjoint selAAZH_Data selAAZH_Anc selAAZH_Held
      selAAZH_Anc_disj_Held
      (disjointWires_compose_of_disjoint selAAZH_AAZ (QRegExt.disjointWires_symm
        selAAZ_Anc_disj_Data))
      selAAZH_Data_disj_Held E_raw217
  have hHeld_Init : uAddHeld_AAZH.1 * E_init_Bell_AAZH =
      selAAZH_AAZ.embedMatrix (uStr218_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero) *
        (selAAZH_AAZ.embedUnitary F_AAZ).1 *
        pEqReg selAAZH_Anc selAAZH_Held * selAAZH_Z.basisOutcomeProjector 0 := by
    have hFU := congrArg Subtype.val F_AAZH_comm_uAddHeld_AAZH.1.symm
    simp only [Submonoid.coe_mul] at hFU
    unfold E_init_Bell_AAZH E_base_Bell_AAZH
    calc uAddHeld_AAZH.1 * ((selAAZH_AAZ.embedUnitary F_AAZ).1 *
            (selAAZH_Data.embedMatrix E_raw217 * pEqReg selAAZH_Anc selAAZH_Held *
              selAAZH_Z.basisOutcomeProjector 0))
        = (selAAZH_AAZ.embedUnitary F_AAZ).1 *
            ((uAddHeld_AAZH.1 * pEqReg selAAZH_Anc selAAZH_Held) *
              selAAZH_Data.embedMatrix E_raw217) *
            selAAZH_Z.basisOutcomeProjector 0 := by
            rw [← Matrix.mul_assoc uAddHeld_AAZH.1, hFU, hE217_Peq]
            simp only [Matrix.mul_assoc]
      _ = ((selAAZH_AAZ.embedUnitary F_AAZ).1 *
            (uAddAnc_AAZH.1 * selAAZH_Data.embedMatrix E_raw217)) *
            pEqReg selAAZH_Anc selAAZH_Held * selAAZH_Z.basisOutcomeProjector 0 := by
            rw [uAddHeld_AAZH_mul_pEqReg, Matrix.mul_assoc uAddAnc_AAZH.1, ← hE217_Peq]
            simp only [Matrix.mul_assoc]
      _ = selAAZH_AAZ.embedMatrix (uStr218_AAZ.1 * selAAZ_Data.embedMatrix pSum42Zero) *
            (selAAZH_AAZ.embedUnitary F_AAZ).1 *
            pEqReg selAAZH_Anc selAAZH_Held * selAAZH_Z.basisOutcomeProjector 0 := by
            have hLift := congrArg selAAZH_AAZ.embedMatrix hF_cStr
            rw [selAAZH_AAZ.embedMatrix_mul, selAAZH_AAZ.embedMatrix_mul,
                selAAZH_AAZ.embedMatrix_mul, ← QRegister.embedMatrix_compose] at hLift
            change (selAAZH_AAZ.embedUnitary F_AAZ).1 *
              (uAddAnc_AAZH.1 * selAAZH_Data.embedMatrix E_raw217) = _ at hLift
            rw [hLift]
            simp only [QRegister.embedUnitary_val, Matrix.mul_assoc]
  unfold P218_Bell_AAZH
  calc (uAddHeld_AAZH⁻¹).1 * selAAZH_AAZ.embedMatrix P218_AAZ * uAddHeld_AAZH.1 *
          E_init_Bell_AAZH
      = (uAddHeld_AAZH⁻¹).1 *
          (selAAZH_AAZ.embedMatrix P218_AAZ * (uAddHeld_AAZH.1 * E_init_Bell_AAZH)) := by
          simp only [Matrix.mul_assoc]
    _ = (uAddHeld_AAZH⁻¹).1 * (uAddHeld_AAZH.1 * E_init_Bell_AAZH) := by
          rw [hHeld_Init, ← Matrix.mul_assoc (selAAZH_AAZ.embedMatrix P218_AAZ),
              ← Matrix.mul_assoc (selAAZH_AAZ.embedMatrix P218_AAZ),
              ← Matrix.mul_assoc (selAAZH_AAZ.embedMatrix P218_AAZ),
              ← selAAZH_AAZ.embedMatrix_mul, hP218_U218]
    _ = E_init_Bell_AAZH := by
          rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel,
              OneMemClass.coe_one, Matrix.one_mul]

/-- Clean `Z = 0` ancilla invariance on `E_init_Bell_AAZH`. -/
theorem selAAZH_Z_proj0_mul_E_init_Bell :
    selAAZH_Z.basisOutcomeProjector 0 * E_init_Bell_AAZH = E_init_Bell_AAZH := by
  have hZ_F : selAAZH_Z.basisOutcomeProjector 0 * (selAAZH_AAZ.embedUnitary F_AAZ).1 =
      (selAAZH_AAZ.embedUnitary F_AAZ).1 * selAAZH_Z.basisOutcomeProjector 0 := by
    rw [F_AAZ_def, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZH_AA) selAAZH_Z
      (disjointWires_compose_of_disjoint selAAZH_AAZ
        (selDataInAct_disj_selMeasInAct (kFull80 + 18))) _ 0).symm
  unfold E_init_Bell_AAZH
  rw [← Matrix.mul_assoc, hZ_F, Matrix.mul_assoc, selAAZH_Z_proj0_mul_E_base_Bell]

/-- Generic active-idle ancilla commutation for `uBarrelFastAct` and `uSlot0MeasSwap`. -/
theorem uBarrelAndSlot0_comm_idle {kIdle : ℕ} (rIdle : QRegister kIdle kFull80)
    (hCore : rCoreFull.DisjointWires rIdle) :
    let P_idle := (selDataInAct kFull80).embedMatrix (rIdle.basisOutcomeProjector 0)
    uBarrelFastAct.1 * P_idle = P_idle * uBarrelFastAct.1 ∧
    uSlot0MeasSwap.1 * P_idle = P_idle * uSlot0MeasSwap.1 := by
  intro P_idle
  refine ⟨?_, ?_⟩
  · dsimp only [P_idle]
    rw [uBarrelFastAct_eq_embedData_rCoreFull, QRegister.embedUnitary_val,
        QRegister.embedUnitary_val, ← (selDataInAct kFull80).embedMatrix_mul,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreFull) rIdle hCore _ 0,
        (selDataInAct kFull80).embedMatrix_mul]
  · have hP : P_idle = ((selDataInAct kFull80).compose rIdle).basisOutcomeProjector 0 :=
      embedMatrix_basisOutcomeProjector_zero_assoc (selDataInAct kFull80) rIdle
    have hDisj : (selLiftAct rSlot0InFull).DisjointWires
        ((selDataInAct kFull80).compose rIdle) :=
      disjointWires_concat_left _
        (disjointWires_compose_of_disjoint (selDataInAct kFull80)
          (hCore.compose_left rSlot0InCore))
        (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct kFull80).compose_left rIdle))
    rw [hP, uSlot0MeasSwap, L_slot0, ← uLensSwap_L_slot0Of_eq_embed18 rSlot0InFull]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selLiftAct rSlot0InFull))
      _ hDisj _ 0

/-- Generic active-idle ancilla commutation for `E_init_Bell_AAZH` and `E_init * E_initᴴ`. -/
theorem E_init_Bell_AAZH_comm_idle {kIdle : ℕ} (rIdle : QRegister kIdle kFull80)
    (hCore : rCoreFull.DisjointWires rIdle) (hSum : rSum0.DisjointWires rIdle) :
    let P_idle := (selAAZH_Data.compose rIdle).basisOutcomeProjector 0
    E_init_Bell_AAZH * P_idle = P_idle * E_init_Bell_AAZH ∧
    (E_init_Bell_AAZH * E_init_Bell_AAZHᴴ) * P_idle =
      P_idle * (E_init_Bell_AAZH * E_init_Bell_AAZHᴴ) := by
  intro P_idle
  have hF_idle : (selAAZH_AAZ.embedUnitary F_AAZ).1 * P_idle =
      P_idle * (selAAZH_AAZ.embedUnitary F_AAZ).1 := by
    have hP0 : (selAAZH_AA.compose ((selDataInAct kFull80).compose
        rIdle)).basisOutcomeProjector 0 = P_idle := by
      congr 1
    have hBS := uBarrelAndSlot0_comm_idle rIdle hCore
    have hF0 : (uBarrelFastAct * uSlot0MeasSwap).1 *
        (selDataInAct kFull80).embedMatrix (rIdle.basisOutcomeProjector 0) =
        (selDataInAct kFull80).embedMatrix (rIdle.basisOutcomeProjector 0) *
        (uBarrelFastAct * uSlot0MeasSwap).1 := by
      simp only [Submonoid.coe_mul]
      rw [Matrix.mul_assoc, hBS.2, ← Matrix.mul_assoc, hBS.1, Matrix.mul_assoc]
    have hLift := congrArg selAAZH_AA.embedMatrix hF0
    rw [selAAZH_AA.embedMatrix_mul, selAAZH_AA.embedMatrix_mul,
        embedMatrix_basisOutcomeProjector_zero_assoc,
        embedMatrix_basisOutcomeProjector_gen_part4,
        hP0, ← QRegister.embedUnitary_val, QRegister.embedUnitary_compose,
        ← F_AAZ_def] at hLift
    exact hLift
  have hE217_idle : selAAZH_Data.embedMatrix E_raw217 * P_idle =
      P_idle * selAAZH_Data.embedMatrix E_raw217 := by
    dsimp only [P_idle]
    rw [E_raw217_def, ← QRegister.embedMatrix_compose]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZH_Data.compose
      rCSFull80))
      (selAAZH_Data.compose rIdle)
      (disjointWires_compose_of_disjoint selAAZH_Data
        (disjointWires_concat_left _ hCore hSum))
      _ 0
  have hPeq_idle : pEqReg selAAZH_Anc selAAZH_Held * P_idle =
      P_idle * pEqReg selAAZH_Anc selAAZH_Held := by
    dsimp only [P_idle]; rw [QRegister.basisOutcomeProjector_eq_diagonal]
    exact pEqReg_comm_diagonal _ _ _
  have hZ_idle : selAAZH_Z.basisOutcomeProjector 0 * P_idle =
      P_idle * selAAZH_Z.basisOutcomeProjector 0 := by
    dsimp only [P_idle]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
    exact diagonal_comm_op_assoc _ _
  have hFwd : E_init_Bell_AAZH * P_idle = P_idle * E_init_Bell_AAZH := by
    unfold E_init_Bell_AAZH E_base_Bell_AAZH
    exact mul_comm_op hF_idle (mul_comm_op (mul_comm_op hE217_idle hPeq_idle) hZ_idle)
  refine ⟨hFwd, ?_⟩
  have hSelfAdj : P_idleᴴ = P_idle := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hAdj := conjTranspose_comm_of_comm_selfAdj_part4 hSelfAdj hFwd
  rw [Matrix.mul_assoc, ← hAdj, ← Matrix.mul_assoc, hFwd, Matrix.mul_assoc]

set_option maxHeartbeats 3200000 in
-- Multi-branch Bell-18 11-step unitary conjugation and projector commutation
/-- Exact 11-step Bell-18 inner-swap operator equality on `E_init_Bell_AAZH` (`0` `P_anc0`). -/
theorem uC9_Bell18_AAZH_eq_on_E_init_Bell :
    uC9_Bell18_AAZH.1 * E_init_Bell_AAZH =
      (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 * E_init_Bell_AAZH := by
  let Pc2_H (b : Fin 2) : Operator (2 ^ kAAZH) := selAAZH_AAZ.embedMatrix (Pc2_AAZ b)
  let F_H := selAAZH_AAZ.embedUnitary F_AAZ
  let Finv_H := selAAZH_AAZ.embedUnitary Finv_AAZ
  have hPc2Sum : Pc2_H 0 + Pc2_H 1 = 1 := by
    dsimp only [Pc2_H]
    rw [← selAAZH_AAZ.embedMatrix_add, Pc2_AAZ_zero_add_one, selAAZH_AAZ.embedMatrix_one]
  have hSplit : E_init_Bell_AAZH = Pc2_H 0 * E_init_Bell_AAZH + Pc2_H 1 * E_init_Bell_AAZH := by
    calc E_init_Bell_AAZH = 1 * E_init_Bell_AAZH := (Matrix.one_mul _).symm
      _ = (Pc2_H 0 + Pc2_H 1) * E_init_Bell_AAZH := by rw [hPc2Sum]
      _ = Pc2_H 0 * E_init_Bell_AAZH + Pc2_H 1 * E_init_Bell_AAZH := Matrix.add_mul _ _ _
  have hFPc2 : ∀ b : Fin 2, F_H.1 * Pc2_H b = Pc2_H b * F_H.1 := fun b ↦ by
    dsimp only [F_H, Pc2_H]
    rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul, (F_AAZ_comm_Pc2_AAZ b).1,
        selAAZH_AAZ.embedMatrix_mul]
  -- Branch `b = 1`: both sides fix `Pc2_H 1 * E_init_Bell_AAZH`
  have hFFinv : F_H * Finv_H = 1 := by
    dsimp only [F_H, Finv_H]
    rw [← QRegister.embedUnitary_mul, F_AAZ_mul_Finv_AAZ.1, QRegister.embedUnitary_one]
  have hFinvF : Finv_H * F_H = 1 := by
    dsimp only [F_H, Finv_H]
    rw [← QRegister.embedUnitary_mul, F_AAZ_mul_Finv_AAZ.2, QRegister.embedUnitary_one]
  have hFrame : selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull) =
      F_H * selAAZH_Data.embedUnitary uInnerSwapFull * Finv_H := by
    dsimp only [selAAZH_AA, selAAZH_Data, F_H, Finv_H]
    rw [QRegister.embedUnitary_compose, ← F_AAZ_InnerSwap_Finv_eq,
        QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
  have hPc2_Z : ∀ b : Fin 2,
      Pc2_H b * selAAZH_Z.basisOutcomeProjector 0 =
        selAAZH_Z.basisOutcomeProjector 0 * Pc2_H b := fun b ↦ by
    dsimp only [Pc2_H]
    rw [Pc2_AAZ_def, ← QRegister.embedMatrix_compose, ← QRegister.compose_assoc]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZH_Data.compose
      rCoreFull))
      selAAZH_Z
      (disjointWires_compose_of_disjoint selAAZH_AAZ
        (selAAZ_Data_disj_Z.compose_left rCoreFull)) _ 0
  have hZ_Pc2Base : ∀ b : Fin 2,
      selAAZH_Z.basisOutcomeProjector 0 * (Pc2_H b * E_base_Bell_AAZH) =
        Pc2_H b * E_base_Bell_AAZH := fun b ↦ by
    rw [← Matrix.mul_assoc, ← hPc2_Z b, Matrix.mul_assoc, selAAZH_Z_proj0_mul_E_base_Bell]
  have hData9_Z : (selAAZH_AAZ.embedUnitary uData9_AAZ).1 *
      selAAZH_Z.basisOutcomeProjector 0 =
      (selAAZH_Data.embedUnitary uInnerSwapFull).1 * selAAZH_Z.basisOutcomeProjector 0 := by
    have h := congrArg selAAZH_AAZ.embedMatrix uData9_AAZ_mul_PZ_eq
    rw [selAAZH_AAZ.embedMatrix_mul, selAAZH_AAZ.embedMatrix_mul,
        embedMatrix_basisOutcomeProjector_gen_part4,
        ← QRegister.embedUnitary_val, ← QRegister.embedUnitary_val,
        ← QRegister.embedUnitary_compose] at h
    exact h
  have hBranch1 : uC9_Bell18_AAZH.1 * (Pc2_H 1 * E_init_Bell_AAZH) =
      (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
        (Pc2_H 1 * E_init_Bell_AAZH) := by
    obtain ⟨f1, hf1⟩ := Pc2_AAZ_eq_rCS_diagonal 1
    let P1_B := Pc2_H 1 * P218_Bell_AAZH
    have hLiftP1 : ∀ {U : Unitary (2 ^ kAAZ)},
        U.1 * Pc2_AAZ 1 = Pc2_AAZ 1 * U.1 →
        (selAAZH_AAZ.embedUnitary U).1 * P218_Bell_AAZH =
          P218_Bell_AAZH * (selAAZH_AAZ.embedUnitary U).1 →
        (selAAZH_AAZ.embedUnitary U).1 * P1_B =
          P1_B * (selAAZH_AAZ.embedUnitary U).1 := fun h1 h2 ↦ by
      dsimp only [P1_B, Pc2_H]
      rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul,
          h1, selAAZH_AAZ.embedMatrix_mul, ← QRegister.embedUnitary_val,
          Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
    have hSwP1 := hLiftP1 (uSw_AAZ_comm_Pc2_and_streams.1 1) uOps_AAZH_comm_P218_Bell.2.2.2
    have hXorP1 := hLiftP1 (by
      have h := (uCSDiag_comm_AAZ f1).2.2.2.2.2
      rwa [← hf1] at h) uOps_AAZH_comm_P218_Bell.2.2.1
    have hPhiP1 := hLiftP1 (by
      have h := (uCSDiag_comm_AAZ f1).2.2.2.1
      rwa [← hf1] at h) uOps_AAZH_comm_P218_Bell.1
    have hAddPc21 : uAddHeld_AAZH.1 * Pc2_H 1 = Pc2_H 1 * uAddHeld_AAZH.1 := by
      dsimp only [Pc2_H]
      rw [Pc2_AAZ_def, ← QRegister.embedMatrix_compose, ← QRegister.compose_assoc]
      unfold uAddHeld_AAZH
      have hDisjCoreAdd := (QRegExt.disjointWires_symm (disjointWires_concat_left
        (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))
        (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rCoreFull))
        (QRegExt.disjointWires_symm (disjointWires_compose_of_disjoint selAAZH_Data
          rCoreFull_disj_rSum0))))
      exact ((selAAZH_Data.compose rCoreFull).embedMatrix_comm_of_disjoint _
        hDisjCoreAdd _ _).symm
    have hAddP218 : uAddHeld_AAZH.1 * P218_Bell_AAZH =
        selAAZH_AAZ.embedMatrix P218_AAZ * uAddHeld_AAZH.1 := by
      unfold P218_Bell_AAZH
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Submonoid.coe_mul, mul_inv_cancel,
          OneMemClass.coe_one, Matrix.one_mul]
    have hAddP1 : uAddHeld_AAZH.1 * P1_B =
        selAAZH_AAZ.embedMatrix (Pc2_AAZ 1 * P218_AAZ) * uAddHeld_AAZH.1 := by
      dsimp only [P1_B, Pc2_H]
      rw [← Matrix.mul_assoc, hAddPc21, Matrix.mul_assoc, hAddP218,
          ← Matrix.mul_assoc, ← selAAZH_AAZ.embedMatrix_mul]
    have hConjFix : ∀ {U M : Unitary (2 ^ kAAZH)} {Q : Operator (2 ^ kAAZH)},
        U.1 * P1_B = Q * U.1 → M.1 * Q = Q → (U⁻¹ * (M * U)).1 * P1_B = P1_B :=
      fun {U M Q} hUP hMQ ↦ by
        simp only [Submonoid.coe_mul]
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hUP, ← Matrix.mul_assoc M.1 Q U.1, hMQ,
            ← hUP, ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel,
            OneMemClass.coe_one, Matrix.one_mul]
    have hMid3Fix :
        (selAAZH_AAZ.embedUnitary (uStr218_AAZ * (uHeadAnc_AAZ * uStr218_AAZ⁻¹))).1 *
          selAAZH_AAZ.embedMatrix (Pc2_AAZ 1 * P218_AAZ) =
          selAAZH_AAZ.embedMatrix (Pc2_AAZ 1 * P218_AAZ) := by
      rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul, uMid3_AAZ_fix_Pc21_P218]
    have hMid5Fix := hConjFix hAddP1 hMid3Fix
    have hMid7Fix : uMid7_Bell18_AAZH.1 * P1_B = P1_B := by
      unfold uMid7_Bell18_AAZH
      rw [_root_.mul_assoc, QRegister.embedUnitary_inv]
      exact hConjFix hPhiP1 hMid5Fix
    have hC9Fix : uC9_Bell18_AAZH.1 * P1_B = P1_B := by
      let U_xs := selAAZH_AAZ.embedUnitary uXorSubst_AAZ * selAAZH_AAZ.embedUnitary uSw_AAZ
      have hUxsInv :
          U_xs⁻¹ = selAAZH_AAZ.embedUnitary uSw_AAZ * selAAZH_AAZ.embedUnitary uXorSubst_AAZ := by
        refine inv_eq_of_mul_eq_one_left ?_
        dsimp only [U_xs]
        rw [_root_.mul_assoc (selAAZH_AAZ.embedUnitary uSw_AAZ),
            ← _root_.mul_assoc (selAAZH_AAZ.embedUnitary uXorSubst_AAZ),
            ← QRegister.embedUnitary_mul, uXorSubst_AAZ_mul_self, QRegister.embedUnitary_one,
            one_mul, ← QRegister.embedUnitary_mul, uSw_AAZ_mul_self, QRegister.embedUnitary_one]
      unfold uC9_Bell18_AAZH
      rw [← hUxsInv]
      exact hConjFix (mul_comm_op hXorP1 hSwP1) hMid7Fix
    have hLHS1 : uC9_Bell18_AAZH.1 * (Pc2_H 1 * E_init_Bell_AAZH) =
        Pc2_H 1 * E_init_Bell_AAZH := by
      rw [← P218_Bell_AAZH_mul_E_init_Bell, ← Matrix.mul_assoc (Pc2_H 1),
          ← Matrix.mul_assoc uC9_Bell18_AAZH.1, hC9Fix, Matrix.mul_assoc,
          P218_Bell_AAZH_mul_E_init_Bell]
    have hData9Fix : (selAAZH_AAZ.embedUnitary uData9_AAZ).1 * Pc2_H 1 = Pc2_H 1 := by
      dsimp only [Pc2_H]
      rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul, uData9_AAZ_fix_Pc21]
    have hRHS1 : (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
        (Pc2_H 1 * E_init_Bell_AAZH) = Pc2_H 1 * E_init_Bell_AAZH := by
      rw [hFrame]
      unfold E_init_Bell_AAZH
      calc (F_H * selAAZH_Data.embedUnitary uInnerSwapFull * Finv_H).1 *
              (Pc2_H 1 * (F_H.1 * E_base_Bell_AAZH))
          = F_H.1 * (((selAAZH_Data.embedUnitary uInnerSwapFull).1 *
              selAAZH_Z.basisOutcomeProjector 0) * (Pc2_H 1 * E_base_Bell_AAZH)) := by
              rw [← Matrix.mul_assoc (Pc2_H 1), ← hFPc2 1]
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
              conv_lhs =>
                rw [← Matrix.mul_assoc Finv_H.1 F_H.1, ← Submonoid.coe_mul, hFinvF,
                    OneMemClass.coe_one, Matrix.one_mul, ← hZ_Pc2Base 1]
        _ = Pc2_H 1 * (F_H.1 * E_base_Bell_AAZH) := by
              rw [← hData9_Z, Matrix.mul_assoc (selAAZH_AAZ.embedUnitary uData9_AAZ).1,
                  hZ_Pc2Base 1, ← Matrix.mul_assoc (selAAZH_AAZ.embedUnitary uData9_AAZ).1,
                  hData9Fix, ← Matrix.mul_assoc F_H.1, hFPc2 1, Matrix.mul_assoc]
    rw [hLHS1, hRHS1]
  -- Branch `b = 0`: conjugate by `Finv_H ... F_H`, swap `uAddHeld -> uAddAnc`,
  -- and reduce to `uData9`
  have hBranch0 : uC9_Bell18_AAZH.1 * (Pc2_H 0 * E_init_Bell_AAZH) =
      (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
        (Pc2_H 0 * E_init_Bell_AAZH) := by
    have hConjMul : ∀ A B : Unitary (2 ^ kAAZH),
        Finv_H * (A * B) * F_H = (Finv_H * A * F_H) * (Finv_H * B * F_H) := fun A B ↦ by
      calc Finv_H * (A * B) * F_H
          = (Finv_H * A) * (F_H * Finv_H) * (B * F_H) := by
              rw [hFFinv, mul_one]
              simp only [_root_.mul_assoc]
        _ = (Finv_H * A * F_H) * (Finv_H * B * F_H) := by simp only [_root_.mul_assoc]
    have hConjLift : ∀ U : Unitary (2 ^ kAAZ),
        Finv_H * selAAZH_AAZ.embedUnitary U * F_H =
          selAAZH_AAZ.embedUnitary (Finv_AAZ * U * F_AAZ) := fun U ↦ by
      dsimp only [Finv_H, F_H]
      rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul]
    have hConjAdd : Finv_H * uAddHeld_AAZH * F_H = uAddHeld_AAZH ∧
        Finv_H * uAddHeld_AAZH⁻¹ * F_H = uAddHeld_AAZH⁻¹ := by
      refine ⟨?_, ?_⟩
      · rw [_root_.mul_assoc, ← F_AAZH_comm_uAddHeld_AAZH.1, ← _root_.mul_assoc, hFinvF, one_mul]
      · have hI : uAddHeld_AAZH⁻¹ * F_H = F_H * uAddHeld_AAZH⁻¹ := by
          calc uAddHeld_AAZH⁻¹ * F_H
              = uAddHeld_AAZH⁻¹ * (F_H * uAddHeld_AAZH) * uAddHeld_AAZH⁻¹ := by
                  simp [_root_.mul_assoc]
            _ = uAddHeld_AAZH⁻¹ * (uAddHeld_AAZH * F_H) * uAddHeld_AAZH⁻¹ := by
                  rw [F_AAZH_comm_uAddHeld_AAZH.1]
            _ = F_H * uAddHeld_AAZH⁻¹ := by simp [← _root_.mul_assoc]
        rw [_root_.mul_assoc, hI, ← _root_.mul_assoc, hFinvF, one_mul]
    let cStr218 := Finv_AAZ * uStr218_AAZ * F_AAZ
    have hcStr218Inv : Finv_AAZ * uStr218_AAZ⁻¹ * F_AAZ = cStr218⁻¹ := by
      symm
      refine inv_eq_of_mul_eq_one_left ?_
      dsimp only [cStr218]
      calc (Finv_AAZ * uStr218_AAZ⁻¹ * F_AAZ) * (Finv_AAZ * uStr218_AAZ * F_AAZ)
          = Finv_AAZ * (uStr218_AAZ⁻¹ * ((F_AAZ * Finv_AAZ) * uStr218_AAZ)) * F_AAZ := by
              simp only [_root_.mul_assoc]
        _ = 1 := by
            rw [F_AAZ_mul_Finv_AAZ.1, one_mul, inv_mul_cancel, mul_one,
              F_AAZ_mul_Finv_AAZ.2]
    let uPE18_AAZ := selAAZ_Anc.embedUnitary uPointElec18
    have hPEPhiComm : uPE18_AAZ⁻¹ * uPhi217_AAZ⁻¹ = uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹ := by
      apply Subtype.ext
      simp only [Submonoid.coe_mul]
      dsimp only [uPE18_AAZ]
      rw [← QRegister.embedUnitary_inv, uPhi217_AAZ_def, ← QRegister.embedUnitary_inv]
      exact selAAZ_Anc.embedMatrix_comm_of_disjoint _ (QRegExt.disjointWires_symm
        selAAZ_HeldAct_disj_Anc) _ _
    let B_Held := uAddHeld_AAZH⁻¹ *
      (selAAZH_AAZ.embedUnitary (cStr218 * (uHeadData_AAZ * cStr218⁻¹)) * uAddHeld_AAZH)
    let M_anc_H := selAAZH_AAZ.embedUnitary (uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
      (B_Held * selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ))
    let M_data := (uXorData_AAZ * uPhi217_AAZ⁻¹) *
      ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) * (uPhi217_AAZ * uXorData_AAZ))
    let cSw_H := selAAZH_AAZ.embedUnitary (Finv_AAZ * uSw_AAZ * F_AAZ)
    have hConjC9 : Finv_H * uC9_Bell18_AAZH * F_H = cSw_H * (M_anc_H * cSw_H) := by
      have hPhiI : Finv_AAZ * uPhiAnc_AAZ⁻¹ * F_AAZ = uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹ := by
        rw [Finv_mul_uPhiAnc_mul_F_eq.2]
        exact hPEPhiComm
      unfold uC9_Bell18_AAZH uMid7_Bell18_AAZH
      simp only [QRegister.embedUnitary_mul, hConjMul, hConjLift, hConjAdd.1, hConjAdd.2,
        Finv_mul_uXorSubst_mul_F_eq, Finv_mul_uPhiAnc_mul_F_eq.1, hPhiI,
        Finv_mul_uHeadAnc_mul_F_eq, hcStr218Inv]
      dsimp only [cSw_H, M_anc_H, B_Held, cStr218, uPE18_AAZ]
      simp only [QRegister.embedUnitary_mul, _root_.mul_assoc]
    let P217_H := selAAZH_AAZ.embedMatrix P217_AAZ
    let P_eq := pEqReg selAAZH_Anc selAAZH_Held
    have hP217_Peq : P217_H * P_eq = P_eq * P217_H := by
      dsimp only [P217_H, P_eq]
      rw [P217_AAZ_def, ← QRegister.embedMatrix_compose, ← QRegister.compose_assoc]
      exact embedMatrix_comm_pEqReg_of_disjoint (selAAZH_Data.compose rCSFull80)
        selAAZH_Anc selAAZH_Held selAAZH_Anc_disj_Held
        (disjointWires_compose_of_disjoint selAAZH_AAZ
          (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rCSFull80)))
        (selAAZH_Data_disj_Held.compose_left rCSFull80) _
    have hDataU : ∃ U0 : Unitary (2 ^ kFull80),
        uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹) = selAAZ_Data.embedUnitary U0 := by
      simp only [uStr217_AAZ_def, uHeadData_AAZ_def, ← QRegister.embedUnitary_inv,
        QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul]
      exact ⟨_, rfl⟩
    have hBHeld_Eq : B_Held.1 * (P217_H * P_eq) =
        (selAAZH_AAZ.embedUnitary (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))).1 *
          (P217_H * P_eq) := by
      have hMid5_AAZ : (cStr218 * (uHeadData_AAZ * (cStr218⁻¹ * uAddAnc_AAZ))).1 * P217_AAZ =
          uAddAnc_AAZ.1 * ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * P217_AAZ) := by
        have h0 := cStr218_AAZ_mid5_on_P217
        dsimp only at h0
        calc (cStr218 * (uHeadData_AAZ * (cStr218⁻¹ * uAddAnc_AAZ))).1 * P217_AAZ
            = (uAddAnc_AAZ * uAddAnc_AAZ⁻¹).1 *
                ((cStr218 * (uHeadData_AAZ * (cStr218⁻¹ * uAddAnc_AAZ))).1 * P217_AAZ) := by
                rw [mul_inv_cancel, OneMemClass.coe_one, Matrix.one_mul]
          _ = uAddAnc_AAZ.1 *
                ((uAddAnc_AAZ⁻¹ * (cStr218 * (uHeadData_AAZ * (cStr218⁻¹ * uAddAnc_AAZ)))).1 *
                  P217_AAZ) := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]
          _ = uAddAnc_AAZ.1 * ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)).1 * P217_AAZ) := by
                rw [h0]
      have hMid5_H : (selAAZH_AAZ.embedUnitary (cStr218 * (uHeadData_AAZ * cStr218⁻¹))).1 *
          (uAddAnc_AAZH.1 * P217_H) =
          uAddAnc_AAZH.1 *
            ((selAAZH_AAZ.embedUnitary (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))).1 *
              P217_H) := by
        unfold uAddAnc_AAZH
        dsimp only [P217_H]
        simp only [QRegister.embedUnitary_val]
        rw [← selAAZH_AAZ.embedMatrix_mul, ← selAAZH_AAZ.embedMatrix_mul,
            ← selAAZH_AAZ.embedMatrix_mul, ← selAAZH_AAZ.embedMatrix_mul]
        refine congrArg selAAZH_AAZ.embedMatrix ?_
        rw [← hMid5_AAZ]
        simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      have hAddSwap : uAddHeld_AAZH.1 * P_eq = uAddAnc_AAZH.1 * P_eq := uAddHeld_AAZH_mul_pEqReg
      have hM3_Peq : (selAAZH_AAZ.embedUnitary
          (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))).1 * P_eq =
          P_eq * (selAAZH_AAZ.embedUnitary
            (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))).1 := by
        obtain ⟨U0, hU0⟩ := hDataU
        rw [hU0, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
        exact embedMatrix_comm_pEqReg_of_disjoint selAAZH_Data selAAZH_Anc selAAZH_Held
          selAAZH_Anc_disj_Held
          (disjointWires_compose_of_disjoint selAAZH_AAZ (QRegExt.disjointWires_symm
            selAAZ_Anc_disj_Data))
          selAAZH_Data_disj_Held U0.1
      dsimp only [B_Held]
      calc (uAddHeld_AAZH⁻¹ *
              (selAAZH_AAZ.embedUnitary (cStr218 * (uHeadData_AAZ * cStr218⁻¹)) *
                uAddHeld_AAZH)).1 * (P217_H * P_eq)
          = (uAddHeld_AAZH⁻¹).1 *
              (((selAAZH_AAZ.embedUnitary (cStr218 * (uHeadData_AAZ * cStr218⁻¹))).1 *
                (uAddAnc_AAZH.1 * P217_H)) * P_eq) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
              rw [hP217_Peq, ← Matrix.mul_assoc uAddHeld_AAZH.1 P_eq, hAddSwap,
                  Matrix.mul_assoc uAddAnc_AAZH.1 P_eq]
        _ = (uAddHeld_AAZH⁻¹).1 *
              ((uAddAnc_AAZH.1 * P_eq) *
                ((selAAZH_AAZ.embedUnitary (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))).1 *
                  P217_H)) := by
              rw [hMid5_H]
              simp only [Matrix.mul_assoc]
              rw [hP217_Peq, ← Matrix.mul_assoc _ P_eq P217_H, hM3_Peq, Matrix.mul_assoc P_eq]
        _ = (selAAZH_AAZ.embedUnitary (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))).1 *
              (P217_H * P_eq) := by
              rw [← hAddSwap]
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (uAddHeld_AAZH⁻¹).1 uAddHeld_AAZH.1,
                  ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul,
                  ← Matrix.mul_assoc P_eq, ← hM3_Peq, Matrix.mul_assoc, ← hP217_Peq]
    have hMidEq : M_anc_H.1 * (P217_H * P_eq) =
        (selAAZH_AAZ.embedUnitary M_data).1 * (P217_H * P_eq) := by
      obtain ⟨f217, hf217⟩ : ∃ f, pStream217Core 80 = Matrix.diagonal f := ⟨_, rfl⟩
      have hP217Diag : P217_AAZ =
          (selAAZ_Data.compose rCSFull80).embedMatrix (Matrix.diagonal f217) := by
        rw [P217_AAZ_def, hf217]
      obtain ⟨hPhi217, _, hXor217, _, _, _⟩ := uCSDiag_comm_AAZ f217
      rw [← hP217Diag] at hPhi217 hXor217
      have hPE_P217 : uPE18_AAZ.1 * P217_AAZ = P217_AAZ * uPE18_AAZ.1 := by
        rw [P217_AAZ_def]
        exact selAAZ_Anc.embedMatrix_comm_of_disjoint _
          (selAAZ_Anc_disj_Data.compose_right rCSFull80) _ _
      have hPre_P217 : ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ).1 * P217_AAZ =
          P217_AAZ * ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ).1 := by
        simp only [Submonoid.coe_mul]
        exact mul_comm_op (mul_comm_op hPE_P217 hPhi217) hXor217
      have hPE_Peq : (selAAZH_AAZ.embedUnitary uPE18_AAZ).1 * P_eq =
          P_eq * (selAAZH_AAZ.embedUnitary uPE18_AAZ).1 := by
        obtain ⟨d18, hd18⟩ : ∃ d, uPointElec18.1 = Matrix.diagonal d := ⟨_, rfl⟩
        dsimp only [uPE18_AAZ, P_eq]
        rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, hd18,
            embedMatrix_diagonal_local]
        exact (pEqReg_comm_diagonal _ _ _).symm
      have hPhi_Peq : (selAAZH_AAZ.embedUnitary uPhi217_AAZ).1 * P_eq =
          P_eq * (selAAZH_AAZ.embedUnitary uPhi217_AAZ).1 := by
        dsimp only [P_eq]
        rw [uPhi217_AAZ_def, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
        exact embedMatrix_comm_pEqReg_of_disjoint _ selAAZH_Anc selAAZH_Held
          selAAZH_Anc_disj_Held
          (disjointWires_compose_of_disjoint selAAZH_AAZ selAAZ_HeldAct_disj_Anc)
          (selAAZH_AAZ_disj_Held.compose_left _) _
      have hXor_Peq : (selAAZH_AAZ.embedUnitary uXorData_AAZ).1 * P_eq =
          P_eq * (selAAZH_AAZ.embedUnitary uXorData_AAZ).1 := by
        dsimp only [P_eq]
        rw [uXorData_AAZ_def, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
        have hDisjAnc : ((selAAZ_Data.compose rPosCoreInFull).concat selAAZ_Z
            (selAAZ_Data_disj_Z.compose_left rPosCoreInFull)).DisjointWires selAAZ_Anc :=
          disjointWires_concat_left _
            (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rPosCoreInFull))
              (QRegExt.disjointWires_symm selAAZ_Anc_disj_Z)
        exact embedMatrix_comm_pEqReg_of_disjoint _ selAAZH_Anc selAAZH_Held
          selAAZH_Anc_disj_Held (disjointWires_compose_of_disjoint selAAZH_AAZ hDisjAnc)
          (selAAZH_AAZ_disj_Held.compose_left _) _
      have hPre_PP : (selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ)).1 *
          (P217_H * P_eq) =
          (P217_H * P_eq) *
            (selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ)).1 := by
        have hL217 := congrArg selAAZH_AAZ.embedMatrix hPre_P217
        simp only [selAAZH_AAZ.embedMatrix_mul] at hL217
        have hLPeq : (selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ)).1 *
            P_eq = P_eq *
              (selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ)).1 := by
          simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
          exact mul_comm_op (mul_comm_op hPE_Peq hPhi_Peq) hXor_Peq
        rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, hL217, ← QRegister.embedUnitary_val,
            Matrix.mul_assoc, hLPeq, ← Matrix.mul_assoc]
      have hPEI_M3 : uPE18_AAZ⁻¹ * (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) =
          (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) * uPE18_AAZ⁻¹ := by
        obtain ⟨U0, hU0⟩ := hDataU
        dsimp only [uPE18_AAZ]
        rw [← QRegister.embedUnitary_inv, hU0]
        apply Subtype.ext
        simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
        exact selAAZ_Anc.embedMatrix_comm_of_disjoint selAAZ_Data selAAZ_Anc_disj_Data _ _
      dsimp only [M_anc_H, M_data]
      calc (selAAZH_AAZ.embedUnitary (uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
              (B_Held * selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ))).1 *
              (P217_H * P_eq)
          = (selAAZH_AAZ.embedUnitary (uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹))).1 *
              ((B_Held.1 * (P217_H * P_eq)) *
                (selAAZH_AAZ.embedUnitary ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ)).1) := by
              have hP' := hPre_PP
              simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul,
                Matrix.mul_assoc] at hP' ⊢
              rw [hP']
        _ = (selAAZH_AAZ.embedUnitary
              ((uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
                (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) *
                ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ))).1 * (P217_H * P_eq) := by
              rw [hBHeld_Eq, Matrix.mul_assoc _ (P217_H * P_eq), ← hPre_PP]
              simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc]
        _ = (selAAZH_AAZ.embedUnitary
              ((uXorData_AAZ * uPhi217_AAZ⁻¹) *
                ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) *
                  (uPhi217_AAZ * uXorData_AAZ)))).1 * (P217_H * P_eq) := by
              have hCancel : (uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
                  (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) *
                  ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ) =
                  (uXorData_AAZ * uPhi217_AAZ⁻¹) *
                  ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) *
                    (uPhi217_AAZ * uXorData_AAZ)) := by
                calc (uXorData_AAZ * (uPhi217_AAZ⁻¹ * uPE18_AAZ⁻¹)) *
                        (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) *
                        ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ)
                    = (uXorData_AAZ * uPhi217_AAZ⁻¹) *
                        (uPE18_AAZ⁻¹ * (uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹))) *
                        ((uPE18_AAZ * uPhi217_AAZ) * uXorData_AAZ) := by
                        simp only [_root_.mul_assoc]
                  _ = (uXorData_AAZ * uPhi217_AAZ⁻¹) *
                        ((uStr217_AAZ * (uHeadData_AAZ * uStr217_AAZ⁻¹)) *
                          ((uPE18_AAZ⁻¹ * uPE18_AAZ) * (uPhi217_AAZ * uXorData_AAZ))) := by
                        rw [hPEI_M3]
                        simp only [_root_.mul_assoc]
                  _ = _ := by rw [inv_mul_cancel, one_mul]
              rw [hCancel]
    have hMDataComm0 : (selAAZH_AAZ.embedUnitary M_data).1 * Pc2_H 0 =
        Pc2_H 0 * (selAAZH_AAZ.embedUnitary M_data).1 := by
      have h0 : M_data.1 * Pc2_AAZ 0 = Pc2_AAZ 0 * M_data.1 := by
        obtain ⟨f0, hf0⟩ := Pc2_AAZ_eq_rCS_diagonal 0
        obtain ⟨hPhi0, hPhiI0, hXor0, _, _, _⟩ := uCSDiag_comm_AAZ f0
        rw [← hf0] at hPhi0 hPhiI0 hXor0
        have hStr0 := uStr217_AAZ_comm_Pc2 0
        have hHead0 := uHeadData_and_Anc_Pc2.2.1
        dsimp only [M_data]
        simp only [Submonoid.coe_mul]
        exact mul_comm_op (mul_comm_op hXor0 hPhiI0)
          (mul_comm_op (mul_comm_op hStr0.1 (mul_comm_op hHead0 hStr0.2))
            (mul_comm_op hPhi0 hXor0))
      dsimp only [Pc2_H]
      rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul, h0,
          selAAZH_AAZ.embedMatrix_mul]
    have hPP_SwBase : (P217_H * P_eq) * (Pc2_H 0 *
        ((selAAZH_AAZ.embedUnitary uSw_AAZ).1 * E_base_Bell_AAZH)) =
        Pc2_H 0 * ((selAAZH_AAZ.embedUnitary uSw_AAZ).1 * E_base_Bell_AAZH) := by
      have hPP_Pc20 : (P217_H * P_eq) * Pc2_H 0 = Pc2_H 0 * (P217_H * P_eq) := by
        obtain ⟨f0, hf0⟩ := Pc2_AAZ_eq_rCS_diagonal 0
        obtain ⟨f217, hf217⟩ : ∃ f, pStream217Core 80 = Matrix.diagonal f := ⟨_, rfl⟩
        have h217_0 : P217_H * Pc2_H 0 = Pc2_H 0 * P217_H := by
          dsimp only [P217_H, Pc2_H]
          rw [P217_AAZ_def, hf217, hf0, ← selAAZH_AAZ.embedMatrix_mul,
              ← QRegister.embedMatrix_mul, diagonal_comm_op_assoc,
              QRegister.embedMatrix_mul, selAAZH_AAZ.embedMatrix_mul]
        have hPeq_0 : P_eq * Pc2_H 0 = Pc2_H 0 * P_eq := by
          dsimp only [Pc2_H, P_eq]
          rw [hf0, embedMatrix_diagonal_local, embedMatrix_diagonal_local]
          exact pEqReg_comm_diagonal _ _ _
        exact mul_comm_op h217_0 hPeq_0
      have hSw_PP : (P217_H * P_eq) * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 =
          (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * (P217_H * P_eq) := by
        have hSw217 : P217_H * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 =
            (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * P217_H := by
          dsimp only [P217_H]
          rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul,
              uSw_AAZ_comm_Pc2_and_streams.2.2.symm, selAAZH_AAZ.embedMatrix_mul]
        have hSwPeq : P_eq * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 =
            (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * P_eq := by
          dsimp only [P_eq]
          rw [uSw_AAZ_def, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
          exact (embedMatrix_comm_pEqReg_of_disjoint _ selAAZH_Anc selAAZH_Held
            selAAZH_Anc_disj_Held
            (disjointWires_compose_of_disjoint selAAZH_AAZ
              (QRegExt.disjointWires_symm (selAAZ_Anc_disj_Data.compose_right rCoreFull)))
            (selAAZH_Data_disj_Held.compose_left rCoreFull) _).symm
        exact mul_comm_op hSw217 hSwPeq
      have hPP_Base : (P217_H * P_eq) * E_base_Bell_AAZH = E_base_Bell_AAZH := by
        have h217_e217 : pStream217Core 80 * eStream217Core = eStream217Core := by
          rw [← eStream217Core_mul_conjTranspose,
              ← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
          exact unitary_mul_pSum42CoreZero_idem (uStr3AxisOfSpec uStream217Spec131)
        have hP217H_E : P217_H * selAAZH_Data.embedMatrix E_raw217 =
            selAAZH_Data.embedMatrix E_raw217 := by
          dsimp only [P217_H, selAAZH_Data]
          rw [QRegister.embedMatrix_compose, ← selAAZH_AAZ.embedMatrix_mul,
              P217_AAZ_def, E_raw217_def, ← QRegister.embedMatrix_compose,
              ← (selAAZ_Data.compose rCSFull80).embedMatrix_mul, h217_e217]
        have hE217_Peq : P_eq * selAAZH_Data.embedMatrix E_raw217 =
            selAAZH_Data.embedMatrix E_raw217 * P_eq :=
          (embedMatrix_comm_pEqReg_of_disjoint selAAZH_Data selAAZH_Anc selAAZH_Held
            selAAZH_Anc_disj_Held
            (disjointWires_compose_of_disjoint selAAZH_AAZ (QRegExt.disjointWires_symm
              selAAZ_Anc_disj_Data))
            selAAZH_Data_disj_Held E_raw217).symm
        unfold E_base_Bell_AAZH
        change (P217_H * P_eq) * (selAAZH_Data.embedMatrix E_raw217 * P_eq *
          selAAZH_Z.basisOutcomeProjector 0) = _
        calc (P217_H * P_eq) *
                (selAAZH_Data.embedMatrix E_raw217 * P_eq * selAAZH_Z.basisOutcomeProjector 0)
            = (P217_H * selAAZH_Data.embedMatrix E_raw217) * (P_eq * P_eq) *
                selAAZH_Z.basisOutcomeProjector 0 := by
                rw [Matrix.mul_assoc P217_H P_eq,
                    ← Matrix.mul_assoc P_eq (selAAZH_Data.embedMatrix E_raw217 * P_eq),
                    ← Matrix.mul_assoc P_eq (selAAZH_Data.embedMatrix E_raw217), hE217_Peq]
                simp only [Matrix.mul_assoc]
          _ = selAAZH_Data.embedMatrix E_raw217 * P_eq *
                selAAZH_Z.basisOutcomeProjector 0 := by rw [hP217H_E, pEqReg_mul_self]
      rw [← Matrix.mul_assoc (P217_H * P_eq) (Pc2_H 0), hPP_Pc20,
          Matrix.mul_assoc (Pc2_H 0), ← Matrix.mul_assoc (P217_H * P_eq),
          hSw_PP, Matrix.mul_assoc _ (P217_H * P_eq), hPP_Base]
    have hcSw_Pc20 : cSw_H.1 * Pc2_H 0 =
        (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * Pc2_H 0 := by
      dsimp only [cSw_H, Pc2_H]
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
          ← selAAZH_AAZ.embedMatrix_mul, Finv_mul_uSw_mul_F_on_Pc20,
          selAAZH_AAZ.embedMatrix_mul]
    have hSw_Pc20 : (selAAZH_AAZ.embedUnitary uSw_AAZ).1 * Pc2_H 0 =
        Pc2_H 0 * (selAAZH_AAZ.embedUnitary uSw_AAZ).1 := by
      dsimp only [Pc2_H]
      rw [QRegister.embedUnitary_val, ← selAAZH_AAZ.embedMatrix_mul,
          uSw_AAZ_comm_Pc2_and_streams.1 0, selAAZH_AAZ.embedMatrix_mul]
    have hCore0 : (Finv_H * uC9_Bell18_AAZH * F_H).1 * (Pc2_H 0 * E_base_Bell_AAZH) =
        (selAAZH_Data.embedUnitary uInnerSwapFull).1 * (Pc2_H 0 * E_base_Bell_AAZH) := by
      have hData9Prod : selAAZH_AAZ.embedUnitary uSw_AAZ *
          (selAAZH_AAZ.embedUnitary M_data * selAAZH_AAZ.embedUnitary uSw_AAZ) =
          selAAZH_AAZ.embedUnitary uData9_AAZ := by
        rw [← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul, uData9_AAZ_eq_prod9]
        dsimp only [M_data]
        simp only [_root_.mul_assoc]
      rw [hConjC9]
      calc (cSw_H * (M_anc_H * cSw_H)).1 * (Pc2_H 0 * E_base_Bell_AAZH)
          = cSw_H.1 * (M_anc_H.1 *
              (Pc2_H 0 * ((selAAZH_AAZ.embedUnitary uSw_AAZ).1 * E_base_Bell_AAZH))) := by
              simp only [Submonoid.coe_mul]
              rw [Matrix.mul_assoc cSw_H.1, Matrix.mul_assoc M_anc_H.1,
                  ← Matrix.mul_assoc cSw_H.1 (Pc2_H 0), hcSw_Pc20, hSw_Pc20, Matrix.mul_assoc]
        _ = cSw_H.1 * ((selAAZH_AAZ.embedUnitary M_data).1 *
              (Pc2_H 0 * ((selAAZH_AAZ.embedUnitary uSw_AAZ).1 * E_base_Bell_AAZH))) := by
              rw [← hPP_SwBase, ← Matrix.mul_assoc M_anc_H.1 (P217_H * P_eq), hMidEq,
                  Matrix.mul_assoc _ (P217_H * P_eq), hPP_SwBase]
        _ = (selAAZH_AAZ.embedUnitary uData9_AAZ).1 * (Pc2_H 0 * E_base_Bell_AAZH) := by
              rw [← Matrix.mul_assoc (selAAZH_AAZ.embedUnitary M_data).1 (Pc2_H 0),
                  hMDataComm0, Matrix.mul_assoc (Pc2_H 0),
                  ← Matrix.mul_assoc cSw_H.1 (Pc2_H 0), hcSw_Pc20,
                  Matrix.mul_assoc (selAAZH_AAZ.embedUnitary uSw_AAZ).1 (Pc2_H 0),
                  ← Matrix.mul_assoc (Pc2_H 0) (selAAZH_AAZ.embedUnitary M_data).1,
                  ← hMDataComm0, Matrix.mul_assoc (selAAZH_AAZ.embedUnitary M_data).1 (Pc2_H 0),
                  ← Matrix.mul_assoc (Pc2_H 0) (selAAZH_AAZ.embedUnitary uSw_AAZ).1,
                  ← hSw_Pc20, ← hData9Prod]
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = (selAAZH_Data.embedUnitary uInnerSwapFull).1 * (Pc2_H 0 * E_base_Bell_AAZH) := by
              rw [← hZ_Pc2Base 0, ← Matrix.mul_assoc _ (selAAZH_Z.basisOutcomeProjector 0),
                  hData9_Z, Matrix.mul_assoc, hZ_Pc2Base 0]
    rw [hFrame]
    unfold E_init_Bell_AAZH
    calc uC9_Bell18_AAZH.1 * (Pc2_H 0 * (F_H.1 * E_base_Bell_AAZH))
        = (F_H * Finv_H).1 * (uC9_Bell18_AAZH.1 * (F_H.1 * (Pc2_H 0 * E_base_Bell_AAZH))) := by
            rw [hFFinv, OneMemClass.coe_one, Matrix.one_mul, ← Matrix.mul_assoc (Pc2_H 0),
                ← hFPc2 0, Matrix.mul_assoc]
      _ = F_H.1 * ((Finv_H * uC9_Bell18_AAZH * F_H).1 * (Pc2_H 0 * E_base_Bell_AAZH)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = F_H.1 * ((selAAZH_Data.embedUnitary uInnerSwapFull).1 *
            ((Finv_H * F_H).1 * (Pc2_H 0 * E_base_Bell_AAZH))) := by
            rw [hCore0, hFinvF, OneMemClass.coe_one, Matrix.one_mul]
      _ = (F_H * selAAZH_Data.embedUnitary uInnerSwapFull * Finv_H).1 *
            (Pc2_H 0 * (F_H.1 * E_base_Bell_AAZH)) := by
            rw [← Matrix.mul_assoc (Pc2_H 0), ← hFPc2 0]
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hSplit, Matrix.mul_add, Matrix.mul_add, hBranch0, hBranch1]


/-! ## Section 4: Concrete `n`-Wire Bell-18 Site-1 Stage-A (`48,093 T`, `0 TOFF`) -/

section Part4_Bell18StageA48093

set_option exponentiation.threshold 8192
set_option genSizeOf false

open scoped Circuit.Notation
open LocalClassicalPerm
open SpecsAux
open OctahedralOrbit
  (ket matrix_ext_ket writeReg writeReg_apply_reg writeReg_apply_of_not_mem)
open CanonRank7Circuit
  (copyXorRegCircuit copyXorRegCircuit_classicalPerm ket_eq_basisKet)
open MeasureBranchHadamardSem
  (ket_projZeroAll projZeroAll_eq_basisOutcomeProjector_zero)
open HoistBorrow42ProjBridge (RealizesOnProj)
open HeldMsbInc7Sandwich288
  (basisOutcomeProjector_zero_concat_eq_mul)
open PosPostPrep80MergedVep
  (cSwapCore3967 uSwapCore3967_mul_self)
open Leaf4Ext48TopStitch
  (rUnusedCtrl3Full rExt6Full pExt6Zero pExt6IdleZero pExt6IdleZero_eq_mul
   pCtrl3Zero hSum0_disj_PGIdle)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap
  (rFullSysElecSlot_val)
open DoubleDutyFoldedRealizesBridge
  (selPosCoreInCore80 hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
open HeldStreamFoldedPass123Bridge
  (E_rawCtrl3Ext E_rawSegExt)
open Slot0SubAdd14And217Stream
  (uSlot0Sum42Add dAddSlot0ToSum42 dSubSlot0FromSum42
   dAddSubSlot0Sum42_counts dAddSubSlot0Sum42_realizesPair)
open FullConcrete7StepAndTrueSwapSelect
  (selCoreSum42InAct selCatInCoreSum42PG7 concat_compose_selCoreSum42InAct)
open ForestQft117BundleNoTopBridge
  (dCanonStage128Fwd count_dCanonStage128Fwd_toff count_dCanonStage128Fwd_t
   dCanonStage128Fwd_realizes)
open ZeroHypSlot0CommAndHMidClosure
  (basisOutcomeProjector_zero_mul_self)
open GridGuard654ReflAux
  (symWrapDynList symWrapDynList_count_TOFF symWrapDynList_count_T symStepFwdList)
open PosSlots24BranchConcrete
open PosSlots24TopWrapper
open PosSlots24CompactHead123
open PosHeadRev18CacheAux
open PosHeadMod4_15476
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter
open StageADeconstrAndQftShare
  (basisOutcomeProjector_comm_part4
   realizesOnProj_of_clean_proj0 realizesOnProj_seq_part4 disj_concat_right_part4
   rHold36OfSub18 rCarry18OfSub18 rZ18OfSub18 rWRestOfSub18
   rCarry18OfSub18_disj_rZ18OfSub18 rZ18OfSub18_disj_rWRestOfSub18
   rCarry18OfSub18_disj_rWRestOfSub18 rCarry18OfSub18_proj0_mul_rZ18OfSub18_proj0
   rHold36OfSub18_proj0_mul_rWRestOfSub18_proj0
   uSlot0MeasSwap_conj_activeOneElecExpQft_eq uExpQft0Full_comm_E_raw217
   uInnerSwapFull_def rActStageAFull80_disj_rPGIdle11
   rCoreFull_disj_rPGIdle11 rPG7Full_disj_rPGIdle11
   unitary_mul_partial_isom_part4 partial_isom_mul_proj_part4
   dPhiOnHeldZ18AnchorFwd128 dPhiOnHeldZ18AnchorInv128
   dPhiOnHeldZ18AnchorFwd128_realizes dPhiOnHeldZ18AnchorInv128_realizes
   count_dPhiOnHeldZ18AnchorFwd128_t count_dPhiOnHeldZ18AnchorInv128_t
   uPhiHeldZ18AnchorCat dHeadAnchorConjH172 dHeadAnchorConjH172_realizes
   count_dHeadAnchorConjH172_t uHeadAnchorConjH uHeadAnc_AAZ_def
   uXorCarry18 uXorCarry18_mul_self uXorConst18 uXorSubst_AAZ_def
   ket_embedUnitary_uXorCarry18
   embedUnitary_uXorCarry18_eq_sum_D_carry sum_mul_comm_part4 mul_sum_mul_part4
   selAAZ_Subst selAAZ_Subst_disj_Z zTargetSteps36_eval_carry
   uSymStepFwdList ket_uSymStepFwdList
   realizesOnProj_symWrapDynList singleton_proj0_mul_reg_proj0
   eval_eq_inv_of_classicalPerm_id
   PebRealizes pebRealizes_iff_realizesOnProj)
open Bell18StageABridgeJunction
  (embed_uSlot0Sum42Add_eq_uElec18Sum42Add realizesClean_congr_embed
   uExpQftStageAFull uJunctionRawFull)
open Bell18StageABridge_Borrow136
  (dStrAdd218_3AxisBorrow_auto dStrInv218_3AxisBorrow_auto
   dStr218_3AxisBorrow_auto_counts dStr218_3AxisBorrow_auto_realizesOnProj)
/-- Active-idle ancilla bundle (`11 ≤ kIdle ≤ 38`) for Bell-18 Site-1 Stage-A (`kIdle = 11` on
`Ctrl`, `kIdle = 3 + 11` via `rSlackIdleFull 11` on `Cat`). -/
structure IdleAnchorSpec (kIdle : ℕ) where
  rIdle : QRegister kIdle kFull80
  hk11 : 11 ≤ kIdle
  hk38 : kIdle ≤ 38
  hCore : rCoreFull.DisjointWires rIdle
  hSum : rSum0.DisjointWires rIdle
  hPG7 : rPG7Full.DisjointWires rIdle

/-- All-`|0⟩` active-idle projector inside `kFull80`. -/
noncomputable abbrev IdleAnchorSpec.pZero {kIdle : ℕ}
    (spec : IdleAnchorSpec kIdle) : Operator (2 ^ kFull80) :=
  spec.rIdle.basisOutcomeProjector 0

theorem IdleAnchorSpec.hSlot0 {kIdle : ℕ} (spec : IdleAnchorSpec kIdle) :
    rSlot0InFull.DisjointWires spec.rIdle :=
  spec.hCore.compose_left rSlot0InCore

theorem IdleAnchorSpec.hActStageA {kIdle : ℕ} (spec : IdleAnchorSpec kIdle) :
    rActStageAFull80.DisjointWires spec.rIdle :=
  disjointWires_concat_left _
    (disjointWires_concat_left _ spec.hCore spec.hSum) spec.hPG7

theorem IdleAnchorSpec.comm_E_init {kIdle : ℕ} (spec : IdleAnchorSpec kIdle) :
    let P_idle := (selAAZH_Data.compose spec.rIdle).basisOutcomeProjector 0
    E_init_Bell_AAZH * P_idle = P_idle * E_init_Bell_AAZH ∧
    (E_init_Bell_AAZH * E_init_Bell_AAZHᴴ) * P_idle =
      P_idle * (E_init_Bell_AAZH * E_init_Bell_AAZHᴴ) :=
  E_init_Bell_AAZH_comm_idle spec.rIdle spec.hCore spec.hSum

/-- Canonical `11`-wire active-idle bundle (`rPGIdle 11`), valid on both `Ctrl` and `Cat`. -/
noncomputable def idleSpec11 : IdleAnchorSpec 11 where
  rIdle := rPGIdle 11 (by decide)
  hk11 := le_refl 11
  hk38 := by decide
  hCore := rCoreFull_disj_rPGIdle11
  hSum := hSum0_disj_PGIdle 11 (by decide)
  hPG7 := rPG7Full_disj_rPGIdle11

/-- `kIdle`-parametric Stage-A stream callback type on `((mWorkSub18 - 36) + kIdle)` scratch. -/
abbrev StrCallbackGen (Var : Type) (kIdle mWorkSub18 n : ℕ) :=
  (rCore : QRegister (fullSysCoreWires 80) n) →
  (rSum42 : QRegister 42 n) →
  (rW : QRegister ((mWorkSub18 - 36) + kIdle) n) →
  rCore.DisjointWires rSum42 → rCore.DisjointWires rW → rSum42.DisjointWires rW →
  DynamicCircuit Var n

local instance (priority := 1000000) instSemigroupUnitaryFastPart4 (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFast_B18 D).toSemigroup

private theorem inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero :
    (uStr218_3Axis⁻¹).1 * eStream218Core = pSum42CoreZero := by
  rw [← uStr218_mul_pSum42, ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel,
      OneMemClass.coe_one, Matrix.one_mul]

private theorem pEqReg_comm_basisOutcomeProjector {k m n : ℕ}
    (r₁ r₂ : QRegister k n) (s : QRegister m n) (o : Fin (2 ^ m)) :
    pEqReg r₁ r₂ * s.basisOutcomeProjector o = s.basisOutcomeProjector o * pEqReg r₁ r₂ := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  exact pEqReg_comm_diagonal r₁ r₂ _

theorem E_init_Bell_AAZH_mul_conjTranspose_mul_self :
    (E_init_Bell_AAZH * E_init_Bell_AAZHᴴ) * E_init_Bell_AAZH = E_init_Bell_AAZH := by
  have hE217 : (eStream217Core * eStream217Coreᴴ) * eStream217Core = eStream217Core := by
    rw [← uStr3Axis131_mul_pSum42CoreZero_eq_eStream217Core]
    exact unitary_mul_pSum42CoreZero_idem (uStr3AxisOfSpec uStream217Spec131)
  let ED := selAAZH_Data.embedMatrix E_raw217
  have hED : (ED * EDᴴ) * ED = ED := by
    dsimp only [ED]
    rw [E_raw217_def, ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_conjTranspose,
        ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul, hE217]
  have hEDQ := partial_isom_mul_proj_part4 hED (pEqReg_conjTranspose _ _) (pEqReg_mul_self _ _)
    (embedMatrix_comm_pEqReg_of_disjoint selAAZH_Data selAAZH_Anc selAAZH_Held
      selAAZH_Anc_disj_Held
      (disjointWires_compose_of_disjoint selAAZH_AAZ (QRegExt.disjointWires_symm
        selAAZ_Anc_disj_Data))
      selAAZH_Data_disj_Held E_raw217)
  have hCommZ : (ED * pEqReg selAAZH_Anc selAAZH_Held) * selAAZH_Z.basisOutcomeProjector 0 =
      selAAZH_Z.basisOutcomeProjector 0 * (ED * pEqReg selAAZH_Anc selAAZH_Held) :=
    mul_comm_op
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZH_Data) selAAZH_Z
        (disjointWires_compose_of_disjoint selAAZH_AAZ selAAZ_Data_disj_Z) E_raw217 0)
      (pEqReg_comm_basisOutcomeProjector selAAZH_Anc selAAZH_Held selAAZH_Z 0)
  unfold E_init_Bell_AAZH
  exact unitary_mul_partial_isom_part4 (selAAZH_AAZ.embedUnitary F_AAZ)
    (partial_isom_mul_proj_part4 hEDQ (QRegister.basisOutcomeProjector_conjTranspose _ 0)
      (basisOutcomeProjector_zero_mul_self _) hCommZ)

/-- Polymorphic Bell-18 anchor-frame subspace operator `(F * E_ext) * PW * G_bell`. -/
noncomputable def E_bell18Gen {mWork n : ℕ} (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (G_bell : Operator (2 ^ n)) : Operator (2 ^ n) :=
  (rAct.concat rAnchor18 hAA).embedMatrix (uBarrelFastAct * uSlot0MeasSwap).1 *
    (rAct.embedMatrix E_ext * rWork.basisOutcomeProjector 0 * G_bell)

/-- Canonical Bell-18 anchor-frame subspace operator with `G_bell = pEqReg rAnchor18 rHeld18`. -/
noncomputable abbrev E_bell18 {mWork n : ℕ} (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) : Operator (2 ^ n) :=
  E_bell18Gen E_ext rAct rAnchor18 rWork hAA (pEqReg rAnchor18 rHeld18)

theorem E_bell18Gen_mul_right_of_comm {mWork n : ℕ} (E₁ E₂ : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) {G_bell : Operator (2 ^ n)}
    (hCommG : rAct.embedMatrix E₂ * G_bell = G_bell * rAct.embedMatrix E₂) :
    E_bell18Gen (E₁ * E₂) rAct rAnchor18 rWork hAA G_bell =
      E_bell18Gen E₁ rAct rAnchor18 rWork hAA G_bell * rAct.embedMatrix E₂ := by
  have hWG := mul_comm_op
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hAW E₂ 0).symm
      hCommG.symm
  unfold E_bell18Gen
  rw [rAct.embedMatrix_mul, Matrix.mul_assoc (rAct.embedMatrix E₁) (rAct.embedMatrix E₂) _,
      Matrix.mul_assoc (rAct.embedMatrix E₁) _ G_bell,
      Matrix.mul_assoc (rAct.embedMatrix E₂) _ G_bell, ← hWG]
  simp only [Matrix.mul_assoc]

theorem E_bell18_mul_right {mWork n : ℕ} (E₁ E₂ : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAH : rAct.DisjointWires rHeld18) (hAnH : rAnchor18.DisjointWires rHeld18) :
    E_bell18 (E₁ * E₂) rAct rAnchor18 rWork rHeld18 hAA =
      E_bell18 E₁ rAct rAnchor18 rWork rHeld18 hAA * rAct.embedMatrix E₂ :=
  E_bell18Gen_mul_right_of_comm E₁ E₂ rAct rAnchor18 rWork hAA hAW
    (embedMatrix_comm_pEqReg_of_disjoint rAct rAnchor18 rHeld18 hAnH hAA hAH E₂)

theorem uAnchorFrame_step_E_bell18Gen {mWork n : ℕ}
    {U : Unitary (2 ^ kFull80)} {E₁ E₂ V : Operator (2 ^ kFull80)}
    (hUE : U.1 * E₁ = E₂ * V)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) {G_bell : Operator (2 ^ n)}
    (hCommG : rAct.embedMatrix V * G_bell = G_bell * rAct.embedMatrix V) :
    ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame U)).1 *
        E_bell18Gen E₁ rAct rAnchor18 rWork hAA G_bell =
      E_bell18Gen E₂ rAct rAnchor18 rWork hAA G_bell * rAct.embedMatrix V := by
  rw [← E_bell18Gen_mul_right_of_comm E₂ V rAct rAnchor18 rWork hAA hAW hCommG, ← hUE]
  have hCancel : uAnchorFrame U * (uBarrelFastAct * uSlot0MeasSwap) =
      (uBarrelFastAct * uSlot0MeasSwap) * (selDataInAct kFull80).embedUnitary U := by
    unfold uAnchorFrame
    rw [_root_.mul_assoc _ (uSlot0MeasSwap * uBarrelFastAct),
        _root_.mul_assoc uSlot0MeasSwap uBarrelFastAct,
        ← _root_.mul_assoc uBarrelFastAct uBarrelFastAct,
        uBarrelFastAct_mul_self, one_mul, uSlot0MeasSwap_mul_self, mul_one]
  unfold E_bell18Gen
  rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← QRegister.embedMatrix_mul,
      ← Submonoid.coe_mul, hCancel, Submonoid.coe_mul, QRegister.embedMatrix_mul,
      QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      concat_compose_selDataInAct, rAct.embedMatrix_mul]
  simp only [Matrix.mul_assoc]

theorem uAnchorFrame_step_E_bell18 {mWork n : ℕ}
    {U : Unitary (2 ^ kFull80)} {E₁ E₂ V : Operator (2 ^ kFull80)}
    (hUE : U.1 * E₁ = E₂ * V)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWork n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAH : rAct.DisjointWires rHeld18) (hAnH : rAnchor18.DisjointWires rHeld18) :
    ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame U)).1 *
        E_bell18 E₁ rAct rAnchor18 rWork rHeld18 hAA =
      E_bell18 E₂ rAct rAnchor18 rWork rHeld18 hAA * rAct.embedMatrix V :=
  uAnchorFrame_step_E_bell18Gen hUE rAct rAnchor18 rWork hAA hAW
    (embedMatrix_comm_pEqReg_of_disjoint rAct rAnchor18 rHeld18 hAnH hAA hAH V)

open Classical in
/-- `kIdle`-parametric Bell-18 inverse stream callback (`+156 T`, `0 TOFF`): adds `rHeld18`
(`+z`) into `rS` before `dStrInv218_3AxisBorrow_auto`. -/
noncomputable def dStrInvBell18Gen {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle)
    (v : Var) (rHeld18 : QRegister 18 n) :
    StrCallbackGen Var kIdle mWorkSub18 n :=
  fun rC rS rWE hCS hCW hSW ↦
    have hk38 := spec.hk38
    if hH : rC.DisjointWires rHeld18 ∧ rS.DisjointWires rHeld18 ∧
        rWE.DisjointWires rHeld18 then
      let rSubC := rDataSubstSlot0 rSlot0InCore rC rHeld18 hH.1
      let hSubCS := rDataSubstSlot0_disj_of_disj rSlot0InCore hH.1 hCS hH.2.1.symm
      let hSubCW := rDataSubstSlot0_disj_of_disj rSlot0InCore hH.1 hCW hH.2.2.symm
      .seq
        (dAddSlot0ToSum42 v rSubC rS rWE hSubCS hSubCW hSW (by omega))
        (dStrInv218_3AxisBorrow_auto v rC rS rWE hCS hCW hSW (by omega))
    else
      .identity

open Classical in
/-- `kIdle`-parametric Bell-18 forward stream callback (`+156 T`, `0 TOFF`): runs
`dStrAdd218_3AxisBorrow_auto` then subtracts `rHeld18` (`-z`) from `rS`. -/
noncomputable def dStrAddBell18Gen {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle)
    (v : Var) (rHeld18 : QRegister 18 n) :
    StrCallbackGen Var kIdle mWorkSub18 n :=
  fun rC rS rWE hCS hCW hSW ↦
    have hk38 := spec.hk38
    if hH : rC.DisjointWires rHeld18 ∧ rS.DisjointWires rHeld18 ∧
        rWE.DisjointWires rHeld18 then
      let rSubC := rDataSubstSlot0 rSlot0InCore rC rHeld18 hH.1
      let hSubCS := rDataSubstSlot0_disj_of_disj rSlot0InCore hH.1 hCS hH.2.1.symm
      let hSubCW := rDataSubstSlot0_disj_of_disj rSlot0InCore hH.1 hCW hH.2.2.symm
      .seq
        (dStrAdd218_3AxisBorrow_auto v rC rS rWE hCS hCW hSW (by omega))
        (dSubSlot0FromSum42 v rSubC rS rWE hSubCS hSubCW hSW (by omega))
    else
      .identity

theorem dStrBell18Gen_counts {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle)
    (v : Var) (rHeld18 : QRegister 18 n)
    (rC : QRegister (fullSysCoreWires 80) n) (rS : QRegister 42 n)
    (rWE : QRegister ((mWorkSub18 - 36) + kIdle) n)
    (hCS : rC.DisjointWires rS) (hCW : rC.DisjointWires rWE)
    (hSW : rS.DisjointWires rWE) :
    (dStrAddBell18Gen spec hm v rHeld18 rC rS rWE hCS hCW hSW).count TOFF = 0 ∧
      (dStrInvBell18Gen spec hm v rHeld18 rC rS rWE hCS hCW hSW).count TOFF = 0 ∧
      (dStrAddBell18Gen spec hm v rHeld18 rC rS rWE hCS hCW hSW).count T +
        (dStrInvBell18Gen spec hm v rHeld18 rC rS rWE hCS hCW hSW).count T ≤
        31560 := by
  have hk38 := spec.hk38
  unfold dStrAddBell18Gen dStrInvBell18Gen
  by_cases hH : rC.DisjointWires rHeld18 ∧ rS.DisjointWires rHeld18 ∧
      rWE.DisjointWires rHeld18
  · rw [dite_eq_left hH, dite_eq_left hH]
    let rSubC := rDataSubstSlot0 rSlot0InCore rC rHeld18 hH.1
    let hSubCS := rDataSubstSlot0_disj_of_disj rSlot0InCore hH.1 hCS hH.2.1.symm
    let hSubCW := rDataSubstSlot0_disj_of_disj rSlot0InCore hH.1 hCW hH.2.2.symm
    have hAddSub := dAddSubSlot0Sum42_counts (Var := Var) v rSubC rS rWE
      hSubCS hSubCW hSW (by omega)
    have hStr := dStr218_3AxisBorrow_auto_counts (Var := Var) v rC rS rWE
      hCS hCW hSW (by omega)
    dsimp only [DynamicCircuit.count]
    refine ⟨?_, ?_, ?_⟩
    · rw [hStr.1, hAddSub.2.1]
    · rw [hAddSub.1, hStr.2.1]
    · have h1 := hAddSub.2.2.1
      have h2 := hAddSub.2.2.2
      have h3 := hStr.2.2
      dsimp only [rSubC, hSubCS, hSubCW] at h1 h2
      omega
  · rw [dite_eq_right hH, dite_eq_right hH]
    exact ⟨rfl, rfl, Nat.zero_le _⟩

theorem dAddSubHeld18_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rC : QRegister (fullSysCoreWires 80) n)
    (rS : QRegister 42 n) (rWE : QRegister mW n) (rHeld18 : QRegister 18 n)
    (hCS : rC.DisjointWires rS) (hCW : rC.DisjointWires rWE)
    (hSW : rS.DisjointWires rWE) (hCH : rC.DisjointWires rHeld18)
    (hSH : rS.DisjointWires rHeld18) (hWH : rWE.DisjointWires rHeld18)
    (hm13 : 13 ≤ mW) :
    let rSubC := rDataSubstSlot0 rSlot0InCore rC rHeld18 hCH
    let hSubCS := rDataSubstSlot0_disj_of_disj rSlot0InCore hCH hCS (QRegExt.disjointWires_symm hSH)
    let hSubCW := rDataSubstSlot0_disj_of_disj rSlot0InCore hCH hCW (QRegExt.disjointWires_symm hWH)
    let rHS := rHeld18.concat rS (QRegExt.disjointWires_symm hSH)
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rHS rWE uElec18Sum42Add
      (dAddSlot0ToSum42 v rSubC rS rWE hSubCS hSubCW hSW hm13) ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rHS rWE uElec18Sum42Add⁻¹
      (dSubSlot0FromSum42 v rSubC rS rWE hSubCS hSubCW hSW hm13) := by
  intro rSubC hSubCS hSubCW rHS
  have hPair := dAddSubSlot0Sum42_realizesPair v rSubC rS rWE hSubCS hSubCW hSW hm13
  have hSlot0 : ∀ q : Fin 18,
      rSubC ⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ =
        rHeld18 q := fun q ↦ by
    have hIdx : (⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ :
        Fin (fullSysCoreWires 80)) = rSlot0InCore q := by
      apply Fin.ext
      rw [rSlot0InCore, rFullSysElecSlot_val]
      simp
    rw [hIdx]
    exact rDataSubstSlot0_apply_slot0 rSlot0InCore rC rHeld18 hCH q
  have hEmbed := embed_uSlot0Sum42Add_eq_uElec18Sum42Add rSubC rHeld18 rS
    hSubCS (QRegExt.disjointWires_symm hSH) hSlot0
  have hEmbedInv :
      (rSubC.concat rS hSubCS).embedUnitary (uSlot0Sum42Add 80)⁻¹ =
        rHS.embedUnitary uElec18Sum42Add⁻¹ := by
    have hFwd := congrArg Subtype.val hEmbed
    apply Subtype.ext
    change (rSubC.concat rS hSubCS).embedMatrix (uSlot0Sum42Add 80).1ᴴ =
      rHS.embedMatrix uElec18Sum42Add.1ᴴ
    rw [QRegister.embedMatrix_conjTranspose, QRegister.embedMatrix_conjTranspose]
    exact congrArg Matrix.conjTranspose hFwd
  exact ⟨realizesClean_congr_embed hEmbed hPair.fwd,
    realizesClean_congr_embed hEmbedInv hPair.inv⟩

/-- Qubit Hilbert-space dimension `2 ^ k`. -/
abbrev qDim (k : ℕ) : ℕ := 2 ^ k

/-- Projector-level Bell-18 stream-pair contract: requires agreement with
`uElec18Sum42Add⁻¹ * uStr218_3Axis` only on `pSum42CoreZero * PW` and `eBell * PW`, allowing
`rSum42` scratch borrowing and carry-free `uBitXor`. -/
noncomputable def StrPairRealizesBell18 {Var : Type} [Fintype Var] [DecidableEq Var]
    {kIdle mWorkSub18 n : ℕ} [NeZero (qDim n)]
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (rHeld18 : QRegister 18 n)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (rWE : QRegister ((mWorkSub18 - 36) + kIdle) n)
    (hCS : rCore.DisjointWires rSum42) (hCW : rCore.DisjointWires rWE)
    (hSW : rSum42.DisjointWires rWE) (hSH : rSum42.DisjointWires rHeld18) : Prop :=
  let rCS := rCore.concat rSum42 hCS
  let rHS := rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSH)
  let uRef := rHS.embedUnitary uElec18Sum42Add⁻¹ * rCS.embedUnitary uStr218_3Axis
  let eBell := (rHS.embedUnitary uElec18Sum42Add⁻¹).1 * rCS.embedMatrix eStream218Core
  RealizesOnProj (rCS.embedMatrix pSum42CoreZero * rWE.basisOutcomeProjector 0) uRef
    (dStrAdd rCore rSum42 rWE hCS hCW hSW) ∧
  RealizesOnProj (eBell * rWE.basisOutcomeProjector 0) uRef⁻¹
    (dStrInv rCore rSum42 rWE hCS hCW hSW)

theorem strPairRealizesBell18_of_stream_eq {Var : Type} [Fintype Var] [DecidableEq Var]
    {kIdle mWorkSub18 n : ℕ} [NeZero (qDim n)]
    {dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n}
    {rHeld18 : QRegister 18 n}
    {rCore : QRegister (fullSysCoreWires 80) n} {rSum42 : QRegister 42 n}
    {rWE : QRegister ((mWorkSub18 - 36) + kIdle) n}
    (hCS : rCore.DisjointWires rSum42) (hCW : rCore.DisjointWires rWE)
    (hSW : rSum42.DisjointWires rWE) (hSH : rSum42.DisjointWires rHeld18)
    {uFwd : Unitary (qDim n)}
    (hEq : uFwd.1 * (rCore.concat rSum42 hCS).embedMatrix pSum42CoreZero =
      ((rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSH)).embedUnitary uElec18Sum42Add⁻¹).1 *
        (rCore.concat rSum42 hCS).embedMatrix eStream218Core)
    (hAdd : RealizesOnProj
      ((rCore.concat rSum42 hCS).embedMatrix pSum42CoreZero * rWE.basisOutcomeProjector 0)
      uFwd (dStrAdd rCore rSum42 rWE hCS hCW hSW))
    (hInv : RealizesOnProj
      (((rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSH)).embedUnitary uElec18Sum42Add⁻¹).1 *
        (rCore.concat rSum42 hCS).embedMatrix eStream218Core * rWE.basisOutcomeProjector 0)
      uFwd⁻¹ (dStrInv rCore rSum42 rWE hCS hCW hSW)) :
    StrPairRealizesBell18 dStrAdd dStrInv rHeld18 rCore rSum42 rWE hCS hCW hSW hSH := by
  let rCS := rCore.concat rSum42 hCS
  let rHS := rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSH)
  let uRef := rHS.embedUnitary uElec18Sum42Add⁻¹ * rCS.embedUnitary uStr218_3Axis
  let P0 := rCS.embedMatrix pSum42CoreZero
  let PW := rWE.basisOutcomeProjector 0
  let eBell := (rHS.embedUnitary uElec18Sum42Add⁻¹).1 * rCS.embedMatrix eStream218Core
  have hRefEq : uRef.1 * P0 = eBell := by
    dsimp only [uRef, P0, eBell]
    rw [Submonoid.coe_mul, Matrix.mul_assoc]
    refine congrArg (_ * ·) ?_
    rw [QRegister.embedUnitary_val, ← rCS.embedMatrix_mul, uStr218_mul_pSum42]
  have hInvL : ∀ (U : Unitary (qDim n)), U.1 * P0 = eBell → (U⁻¹).1 * eBell = P0 :=
    fun U hU ↦ by
      rw [← hU, ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel,
          OneMemClass.coe_one, Matrix.one_mul]
  have hFwdEq : uFwd.1 * P0 = eBell := hEq
  have hAddEq : uFwd.1 * (P0 * PW) = uRef.1 * (P0 * PW) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact congrArg (· * PW) (hFwdEq.trans hRefEq.symm)
  have hInvEq : (uFwd⁻¹).1 * (eBell * PW) = (uRef⁻¹).1 * (eBell * PW) := by
    rw [← Matrix.mul_assoc (uFwd⁻¹).1 eBell PW, ← Matrix.mul_assoc (uRef⁻¹).1 eBell PW]
    exact congrArg (· * PW) ((hInvL uFwd hFwdEq).trans (hInvL uRef hRefEq).symm)
  exact ⟨realizesOnProj_congr_unitary hAddEq hAdd,
    realizesOnProj_congr_unitary hInvEq hInv⟩

theorem dStrBell18Gen_strPairRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {kIdle mWorkSub18 n : ℕ} [NeZero (qDim n)]
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle)
    (v : Var) (rHeld18 : QRegister 18 n)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (rWE : QRegister ((mWorkSub18 - 36) + kIdle) n)
    (hCS : rCore.DisjointWires rSum42) (hCW : rCore.DisjointWires rWE)
    (hSW : rSum42.DisjointWires rWE) (hCH : rCore.DisjointWires rHeld18)
    (hSH : rSum42.DisjointWires rHeld18) (hWH : rWE.DisjointWires rHeld18) :
    StrPairRealizesBell18 (dStrAddBell18Gen spec hm v rHeld18)
      (dStrInvBell18Gen spec hm v rHeld18) rHeld18 rCore rSum42 rWE hCS hCW hSW hSH := by
  have hk38 := spec.hk38
  have hH : rCore.DisjointWires rHeld18 ∧ rSum42.DisjointWires rHeld18 ∧
      rWE.DisjointWires rHeld18 := ⟨hCH, hSH, hWH⟩
  let rCS := rCore.concat rSum42 hCS
  let rHS := rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSH)
  let PW := rWE.basisOutcomeProjector 0
  have hCSW : rCS.DisjointWires rWE := disjointWires_concat_left hCS hCW hSW
  have hHSW : rHS.DisjointWires rWE :=
    disjointWires_concat_left (QRegExt.disjointWires_symm hSH) (QRegExt.disjointWires_symm hWH) hSW
  have hHeldPair := dAddSubHeld18_realizesPair v rCore rSum42 rWE rHeld18
    hCS hCW hSW hCH hSH hWH (by omega)
  have hStrPair := dStr218_3AxisBorrow_auto_realizesOnProj v rCore rSum42 rWE
    hCS hCW hSW (by omega)
  unfold StrPairRealizesBell18 dStrAddBell18Gen dStrInvBell18Gen
  rw [dite_eq_left hH, dite_eq_left hH]
  refine ⟨?_, ?_⟩
  · have hSubProj := realizesOnProj_of_clean_proj0 hHSW hHeldPair.2
    have hTransA : (rCS.embedUnitary uStr218_3Axis).1 *
        (rCS.embedMatrix pSum42CoreZero * PW) =
        PW * ((rCS.embedUnitary uStr218_3Axis).1 * rCS.embedMatrix pSum42CoreZero) := by
      rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, ← rCS.embedMatrix_mul,
          (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rWE hCSW _ 0,
          rCS.embedMatrix_mul]
    exact realizesOnProj_seq_part4 hTransA hStrPair.1 hSubProj
  · let eBell := (rHS.embedUnitary uElec18Sum42Add⁻¹).1 * rCS.embedMatrix eStream218Core
    have hEBellCommW : eBell * PW = PW * eBell :=
      mul_comm_op
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHS) rWE hHSW _ 0)
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rWE hCSW _ 0)
    have hAddProj := realizesOnProj_mul_right eBell
      (realizesOnProj_of_clean_proj0 hHSW hHeldPair.1)
    rw [← hEBellCommW] at hAddProj
    have hCancelHS : (rHS.embedUnitary uElec18Sum42Add).1 *
        (rHS.embedUnitary uElec18Sum42Add⁻¹).1 = 1 := by
      rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, mul_inv_cancel,
          QRegister.embedUnitary_one, OneMemClass.coe_one]
    have hTransI : (rHS.embedUnitary uElec18Sum42Add).1 * (eBell * PW) =
        (rCS.embedMatrix eStream218Core * PW) * 1 := by
      dsimp only [eBell]
      rw [Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCancelHS, Matrix.one_mul]
    have hSeqI := realizesOnProj_seq_part4 hTransI hAddProj hStrPair.2
    have hInvEq : rCS.embedUnitary uStr218_3Axis⁻¹ * rHS.embedUnitary uElec18Sum42Add =
        (rHS.embedUnitary uElec18Sum42Add⁻¹ * rCS.embedUnitary uStr218_3Axis)⁻¹ := by
      rw [_root_.mul_inv_rev, ← QRegister.embedUnitary_inv,
          ← QRegister.embedUnitary_inv, inv_inv]
    rwa [hInvEq] at hSeqI


/-- Reducible Bell-18 Site-1 inner-swap circuit (`155 ≤ mWorkSub18`, `16,260 + tStrPair` `T`,
`0 TOFF`), defined without `@[irreducible]` opacity prior to
`dInnerSwapAnchor_bell18_realizesOnProj` (zero unsafe reducibility). -/
noncomputable def dInnerSwapBell18_ofStrGen {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    DynamicCircuit Var n :=
  have hk38 := spec.hk38
  have hm36 : 36 ≤ mWorkSub18 := by omega
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  let rHold36 := rHold36OfSub18 hm36 rWork
  let rZ18 := rZ18OfSub18 hm36 rWork
  let rWRest := rWRestOfSub18 hm36 rWork
  let rIdle11 := rAct.compose spec.rIdle
  let hWRestIdle : rWRest.DisjointWires rIdle11 :=
    (QRegExt.disjointWires_symm ((hAW.compose_left spec.rIdle).compose_right _))
  let rW136 : QRegister ((mWorkSub18 - 36) + kIdle) n := rWRest.concat rIdle11 hWRestIdle
  let rCore := rAct.compose rCoreFull
  let rSum42 := rAct.compose rSum0
  let rPG7 := rAct.compose rPG7Full
  let hCSum42 := disjointWires_compose_of_disjoint rAct rCoreFull_disj_rSum0
  let hCPG := disjointWires_compose_of_disjoint rAct hCoreFull_disj_rPG7Full
  let hSPG := disjointWires_compose_of_disjoint rAct rSum0_disj_rPG7Full
  let hCW136 : rCore.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rCoreFull).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hCore)
  let hSW136 : rSum42.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rSum0).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hSum)
  let hPGW136 : rPG7.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rPG7Full).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hPG7)
  let hZW136 : rZ18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (rZ18OfSub18_disj_rWRestOfSub18 hm36 rWork)
      (QRegExt.disjointWires_symm ((hAW.compose_left spec.rIdle).compose_right _))
  let hCZ : rCore.DisjointWires rZ18 := (hAW.compose_left rCoreFull).compose_right _
  let hSZ : rSum42.DisjointWires rZ18 := (hAW.compose_left rSum0).compose_right _
  let hPGZ : rPG7.DisjointWires rZ18 := (hAW.compose_left rPG7Full).compose_right _
  let rCS := rCore.concat rSum42 hCSum42
  let hCS_Z := disjointWires_concat_left hCSum42 hCZ hSZ
  let hCS_PG := disjointWires_concat_left hCSum42 hCPG hSPG
  let rHeldAct := (rCS.concat rZ18 hCS_Z).concat rPG7
    (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm hPGZ))
  let hCS_W136 := disjointWires_concat_left hCSum42 hCW136 hSW136
  let hHeldW136 : rHeldAct.DisjointWires rW136 :=
    disjointWires_concat_left (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm
      hPGZ))
      (disjointWires_concat_left hCS_Z hCS_W136 hZW136) hPGW136
  let rSubstPos := rSubst.compose rPosCoreInFull
  let hSubPHold : rSubstPos.DisjointWires rHold36 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hSubPZ : rSubstPos.DisjointWires rZ18 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hQDisj : (phcHead_rQRev18 rSubstPos).DisjointWires rZ18 :=
    QRegister.disjoint_iff.mpr fun k j heq ↦ by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rSubstPos _).mp (phcHead_rQRev18_mem_core rSubstPos k)
      exact hSubPZ.ne i j (hi.trans heq)
  let rCorePos := rAct.compose rPosCoreInFull
  let rScr178 : QRegister (((mWorkSub18 - 36) + kIdle) + 42) n :=
    rW136.concat rSum42 (QRegExt.disjointWires_symm hSW136)
  let hCPSum : rCorePos.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rAct (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80)
  let hCPScr : rCorePos.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136) (hCW136.compose_left
      selPosCoreInCore80) hCPSum
  let hAnW136 : rAnchor18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (hAnW.compose_right _)
      (QRegExt.disjointWires_symm (hAA.compose_left spec.rIdle))
  let hAnScr : rAnchor18.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136) hAnW136 (QRegExt.disjointWires_symm
      (hAA.compose_left rSum0))
  let cXorQ : Circuit n := copyXorRegCircuit (phcHead_rQRev18 rSubstPos) rZ18 hQDisj
  let dSw : DynamicCircuit Var n := .circuit (cSwapCore3967.onRegister rCore)
  let dPhiF := dPhiOnHeldZ18AnchorFwd128 (by omega : 128 ≤ (mWorkSub18 - 36) + kIdle)
    v rHeldAct rW136 hHeldW136
  let dPhiI := dPhiOnHeldZ18AnchorInv128 (by omega : 128 ≤ (mWorkSub18 - 36) + kIdle)
    v rHeldAct rW136 hHeldW136
  let dStrI := dStrInv rCore rSum42 rW136 hCSum42 hCW136 hSW136
  let dHead := dHeadAnchorConjH172 (by omega : 172 ≤ ((mWorkSub18 - 36) + kIdle) + 42) v
    rCorePos rAnchor18 rScr178 (hAA.compose_left rPosCoreInFull) hCPScr hAnScr
  let dStrA := dStrAdd rCore rSum42 rW136 hCSum42 hCW136 hSW136
  let dMid5 : DynamicCircuit Var n :=
    .seq dPhiF (.seq dStrI (.seq dHead (.seq dStrA dPhiI)))
  let dPeb : DynamicCircuit Var n :=
    symWrapDynList v (zTargetSteps36 (le_refl 36) rSubstPos rHold36 hSubPHold)
      (.seq (.circuit cXorQ) (.seq dMid5 (.circuit cXorQ)))
  .seq dSw (.seq dPeb dSw)

@[simp]
theorem count_dInnerSwapBell18_ofStrGen_toff {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (hToff : ∀ rC rS rW hCS hCW hSW,
      (dStrAdd rC rS rW hCS hCW hSW).count TOFF = 0 ∧
      (dStrInv rC rS rW hCS hCW hSW).count TOFF = 0)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dInnerSwapBell18_ofStrGen spec hm v dStrAdd dStrInv
      rAct rAnchor18 rWork hAA hAW hAnW).count TOFF = 0 := by
  have hAdd := fun rC rS rW hCS hCW hSW ↦ (hToff rC rS rW hCS hCW hSW).1
  have hInv := fun rC rS rW hCS hCW hSW ↦ (hToff rC rS rW hCS hCW hSW).2
  dsimp only [dInnerSwapBell18_ofStrGen]
  simp [symWrapDynList_count_TOFF, cSwapCore3967_counts.1, hAdd, hInv]

theorem count_dInnerSwapBell18_ofStrGen_t_le {Var : Type} {kIdle mWorkSub18 n tStrPair : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (hT : ∀ rC rS rW hCS hCW hSW,
      (dStrAdd rC rS rW hCS hCW hSW).count T +
      (dStrInv rC rS rW hCS hCW hSW).count T ≤ tStrPair)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dInnerSwapBell18_ofStrGen spec hm v dStrAdd dStrInv
      rAct rAnchor18 rWork hAA hAW hAnW).count T ≤ 16260 + tStrPair := by
  have hk38 := spec.hk38
  have hm36 : 36 ≤ mWorkSub18 := by omega
  let rWRest := rWRestOfSub18 hm36 rWork
  let rIdle11 := rAct.compose spec.rIdle
  let hWRestIdle : rWRest.DisjointWires rIdle11 :=
    (QRegExt.disjointWires_symm ((hAW.compose_left spec.rIdle).compose_right _))
  let rW136 : QRegister ((mWorkSub18 - 36) + kIdle) n := rWRest.concat rIdle11 hWRestIdle
  have hStr := hT (rAct.compose rCoreFull) (rAct.compose rSum0) rW136
    (disjointWires_compose_of_disjoint rAct rCoreFull_disj_rSum0)
    (disj_concat_right_part4 hWRestIdle ((hAW.compose_left rCoreFull).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hCore))
    (disj_concat_right_part4 hWRestIdle ((hAW.compose_left rSum0).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hSum))
  dsimp only [dInnerSwapBell18_ofStrGen]
  dsimp only [rW136, rWRest, rIdle11] at hStr
  simp only [DynamicCircuit.count, symWrapDynList_count_T, length_zTargetSteps36]
  have hXorT : ∀ {k : ℕ} {a b : QRegister k n} (h : a.DisjointWires b),
      (copyXorRegCircuit a b h).count T = 0 :=
    fun {_} {a b} h ↦ count_copyXorRegCircuit_t a b h
  rw [Circuit.count_onRegister, cSwapCore3967_counts.2, hXorT,
      count_dPhiOnHeldZ18AnchorFwd128_t, count_dPhiOnHeldZ18AnchorInv128_t,
      count_dHeadAnchorConjH172_t]
  omega


set_option maxHeartbeats 3200000 in
-- Full 11-step Bell-18 inner-swap anchor projector realization proof
theorem dInnerSwapAnchor_bell18_realizesOnProj_ofStrGen
    {Var : Type} [Fintype Var] [DecidableEq Var] {kIdle mWorkSub18 n : ℕ} [NeZero (qDim n)]
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18)
    (hStr : ∀ (rC : QRegister (fullSysCoreWires 80) n) (rS : QRegister 42 n)
      (rWE : QRegister ((mWorkSub18 - 36) + kIdle) n)
      (hCS : rC.DisjointWires rS) (hCW : rC.DisjointWires rWE)
      (hSW : rS.DisjointWires rWE),
      rC.DisjointWires rHeld18 →
      ∀ (hSH : rS.DisjointWires rHeld18),
      rWE.DisjointWires rHeld18 →
      StrPairRealizesBell18 dStrAdd dStrInv rHeld18 rC rS rWE hCS hCW hSW hSH) :
    RealizesOnProj
      (E_bell18 (E_raw217 * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame uInnerSwapFull))
      (dInnerSwapBell18_ofStrGen spec hm v dStrAdd dStrInv
        rAct rAnchor18 rWork hAA hAW hAnW) := by
  have hk38 := spec.hk38
  have hm36 : 36 ≤ mWorkSub18 := by omega
  let rAA := rAct.concat rAnchor18 hAA
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  let rHold36 := rHold36OfSub18 hm36 rWork
  let rCarry18 := rCarry18OfSub18 hm36 rWork
  let rZ18 := rZ18OfSub18 hm36 rWork
  let rWRest := rWRestOfSub18 hm36 rWork
  let rIdle11 := rAct.compose spec.rIdle
  let hWRestIdle : rWRest.DisjointWires rIdle11 :=
    (QRegExt.disjointWires_symm ((hAW.compose_left spec.rIdle).compose_right _))
  let rW136 : QRegister ((mWorkSub18 - 36) + kIdle) n := rWRest.concat rIdle11 hWRestIdle
  let hAA_Z : rAA.DisjointWires rZ18 :=
    disjointWires_concat_left hAA (hAW.compose_right _) (hAnW.compose_right _)
  let rAAZ : QRegister kAAZ n := rAA.concat rZ18 hAA_Z
  let hAAZ_Held : rAAZ.DisjointWires rHeld18 :=
    disjointWires_concat_left hAA_Z
      (disjointWires_concat_left hAA hAH hAnH) (hWH.compose_left _)
  let rAAZH : QRegister kAAZH n := rAAZ.concat rHeld18 hAAZ_Held
  let hAAZ_Carry : rAAZ.DisjointWires rCarry18 :=
    disjointWires_concat_left hAA_Z
      (disjointWires_concat_left hAA (hAW.compose_right _) (hAnW.compose_right _))
      (QRegExt.disjointWires_symm (rCarry18OfSub18_disj_rZ18OfSub18 hm36 rWork))
  let hAAZH_Carry : rAAZH.DisjointWires rCarry18 :=
    disjointWires_concat_left hAAZ_Held hAAZ_Carry (QRegExt.disjointWires_symm (hWH.compose_left _))
  let hAAZH_WRest : rAAZH.DisjointWires rWRest :=
    disjointWires_concat_left hAAZ_Held
      (disjointWires_concat_left hAA_Z
        (disjointWires_concat_left hAA (hAW.compose_right _) (hAnW.compose_right _))
        (rZ18OfSub18_disj_rWRestOfSub18 hm36 rWork))
      (QRegExt.disjointWires_symm (hWH.compose_left _))
  let hCarryW136 : rCarry18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (rCarry18OfSub18_disj_rWRestOfSub18 hm36 rWork)
      (QRegExt.disjointWires_symm ((hAW.compose_left spec.rIdle).compose_right _))
  let rCore := rAct.compose rCoreFull
  let rSum42 := rAct.compose rSum0
  let rPG7 := rAct.compose rPG7Full
  let hCSum42 := disjointWires_compose_of_disjoint rAct rCoreFull_disj_rSum0
  let hCPG := disjointWires_compose_of_disjoint rAct hCoreFull_disj_rPG7Full
  let hSPG := disjointWires_compose_of_disjoint rAct rSum0_disj_rPG7Full
  let hCW136 : rCore.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rCoreFull).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hCore)
  let hSW136 : rSum42.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rSum0).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hSum)
  let hPGW136 : rPG7.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle ((hAW.compose_left rPG7Full).compose_right _)
      (disjointWires_compose_of_disjoint rAct spec.hPG7)
  let hZW136 : rZ18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (rZ18OfSub18_disj_rWRestOfSub18 hm36 rWork)
      (QRegExt.disjointWires_symm ((hAW.compose_left spec.rIdle).compose_right _))
  let hCZ : rCore.DisjointWires rZ18 := (hAW.compose_left rCoreFull).compose_right _
  let hSZ : rSum42.DisjointWires rZ18 := (hAW.compose_left rSum0).compose_right _
  let hPGZ : rPG7.DisjointWires rZ18 := (hAW.compose_left rPG7Full).compose_right _
  let rCS := rCore.concat rSum42 hCSum42
  let hCS_Z := disjointWires_concat_left hCSum42 hCZ hSZ
  let hCS_PG := disjointWires_concat_left hCSum42 hCPG hSPG
  let rHeldAct := (rCS.concat rZ18 hCS_Z).concat rPG7
    (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm hPGZ))
  let hCS_W136 := disjointWires_concat_left hCSum42 hCW136 hSW136
  let hHeldW136 : rHeldAct.DisjointWires rW136 :=
    disjointWires_concat_left (disjointWires_concat_left hCS_Z hCS_PG (QRegExt.disjointWires_symm
      hPGZ))
      (disjointWires_concat_left hCS_Z hCS_W136 hZW136) hPGW136
  let rSubstPos := rSubst.compose rPosCoreInFull
  let hSubPHold : rSubstPos.DisjointWires rHold36 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hSubPCarry : rSubstPos.DisjointWires rCarry18 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hSubPZ : rSubstPos.DisjointWires rZ18 :=
    (hSubW.compose_left rPosCoreInFull).compose_right _
  let hQDisj : (phcHead_rQRev18 rSubstPos).DisjointWires rZ18 :=
    QRegister.disjoint_iff.mpr fun k j heq ↦ by
      obtain ⟨i, hi⟩ := (QRegister.mem_image rSubstPos _).mp
        (phcHead_rQRev18_mem_core rSubstPos k)
      exact hSubPZ.ne i j (hi.trans heq)
  let rCorePos := rAct.compose rPosCoreInFull
  let rScr178 : QRegister (((mWorkSub18 - 36) + kIdle) + 42) n :=
    rW136.concat rSum42 (QRegExt.disjointWires_symm hSW136)
  let hCPSum : rCorePos.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rAct
      (rCoreFull_disj_rSum0.compose_left selPosCoreInCore80)
  let hCPScr : rCorePos.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136) (hCW136.compose_left
      selPosCoreInCore80) hCPSum
  let hAnW136 : rAnchor18.DisjointWires rW136 :=
    disj_concat_right_part4 hWRestIdle (hAnW.compose_right _)
      (QRegExt.disjointWires_symm (hAA.compose_left spec.rIdle))
  let hAnScr : rAnchor18.DisjointWires rScr178 :=
    disj_concat_right_part4 (QRegExt.disjointWires_symm hSW136) hAnW136 (QRegExt.disjointWires_symm
      (hAA.compose_left rSum0))
  let rHeadAct := rCorePos.concat rAnchor18 (hAA.compose_left rPosCoreInFull)
  have hHeadDisjScr : rHeadAct.DisjointWires rScr178 :=
    disjointWires_concat_left (hAA.compose_left rPosCoreInFull) hCPScr hAnScr
  have hHeadDisjW136 : rHeadAct.DisjointWires rW136 :=
    disjointWires_concat_left (hAA.compose_left rPosCoreInFull)
      (hCW136.compose_left selPosCoreInCore80) hAnW136
  have hAAZH_AAZ : rAAZH.compose selAAZH_AAZ = rAAZ :=
    concat_compose_selDataInAct rAAZ rHeld18 hAAZ_Held
  have hAAZH_Held : rAAZH.compose selAAZH_Held = rHeld18 :=
    concat_compose_selMeasInAct rAAZ rHeld18 hAAZ_Held
  have hAAZ_AA : rAAZ.compose selAAZ_AA = rAA :=
    concat_compose_selDataInAct rAA rZ18 hAA_Z
  have hAAZ_Z : rAAZ.compose selAAZ_Z = rZ18 :=
    concat_compose_selMeasInAct rAA rZ18 hAA_Z
  have hAAZ_Data : rAAZ.compose selAAZ_Data = rAct := by
    rw [← QRegister.compose_assoc, hAAZ_AA]
    exact concat_compose_selDataInAct rAct rAnchor18 hAA
  have hAAZ_Anc : rAAZ.compose selAAZ_Anc = rAnchor18 := by
    dsimp only [selAAZ_Anc]
    rw [← QRegister.compose_assoc, hAAZ_AA]
    exact concat_compose_selMeasInAct rAct rAnchor18 hAA
  have hAAZH_AA : rAAZH.compose selAAZH_AA = rAA := by
    dsimp only [selAAZH_AA]; rw [← QRegister.compose_assoc, hAAZH_AAZ, hAAZ_AA]
  have hAAZH_Data : rAAZH.compose selAAZH_Data = rAct := by
    dsimp only [selAAZH_Data]; rw [← QRegister.compose_assoc, hAAZH_AAZ, hAAZ_Data]
  have hAAZH_Anc : rAAZH.compose selAAZH_Anc = rAnchor18 := by
    dsimp only [selAAZH_Anc]; rw [← QRegister.compose_assoc, hAAZH_AAZ, hAAZ_Anc]
  have hAAZH_Z : rAAZH.compose selAAZH_Z = rZ18 := by
    dsimp only [selAAZH_Z]; rw [← QRegister.compose_assoc, hAAZH_AAZ, hAAZ_Z]
  have hAAZ_Subst : rAAZ.compose selAAZ_Subst = rSubst := by
    dsimp only [selAAZ_Subst, rSubst, rActAnchorSubst]
    rw [← QRegister.compose_assoc, hAAZ_AA]
    exact concat_compose_selSubstSlot0 rSlot0InFull rAct rAnchor18 hAA
  have hCompCore : rAAZ.compose (selAAZ_Data.compose rCoreFull) = rCore := by
    rw [← QRegister.compose_assoc, hAAZ_Data]
  have hCompCS : rAAZ.compose (selAAZ_Data.compose rCSFull80) = rCS := by
    rw [← QRegister.compose_assoc, hAAZ_Data]
    refine qreg_ext_addCases (fun i ↦ ?_) (fun j ↦ ?_)
    · simp [rCS, rCore, rCSFull80, QRegister.concat_apply_left]
    · simp [rCS, rSum42, rCSFull80, QRegister.concat_apply_right]
  have hCompSubPos : rAAZ.compose (selAAZ_Subst.compose rPosCoreInFull) = rSubstPos := by
    rw [← QRegister.compose_assoc, hAAZ_Subst]
  have hCompSubstPZ : rAAZ.compose
        ((selAAZ_Subst.compose rPosCoreInFull).concat selAAZ_Z
          (selAAZ_Subst_disj_Z.compose_left rPosCoreInFull)) =
      rSubstPos.concat rZ18 hSubPZ := by
    refine qreg_ext_addCases (fun i ↦ ?_) (fun j ↦ ?_)
    · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
          ← QRegister.compose_apply rAAZ, hCompSubPos]
    · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          ← QRegister.compose_apply rAAZ, hAAZ_Z]
  have hCompHeld : rAAZ.compose selAAZ_HeldAct = rHeldAct := by
    refine qreg_ext_addCases (fun iCZ ↦ ?_) (fun mPG ↦ ?_)
    · refine Fin.addCases
        (motive := fun x ↦ (rAAZ.compose selAAZ_HeldAct) (Fin.castAdd 7 x) =
          rHeldAct (Fin.castAdd 7 x))
        (fun iCS ↦ ?_) (fun jZ ↦ ?_) iCZ
      · dsimp only [selAAZ_HeldAct, rHeldAct]
        rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
            QRegister.concat_apply_left, QRegister.concat_apply_left,
            ← QRegister.compose_apply rAAZ, hCompCS]
      · dsimp only [selAAZ_HeldAct, rHeldAct]
        rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_right,
            QRegister.concat_apply_left, QRegister.concat_apply_right,
            ← QRegister.compose_apply rAAZ, hAAZ_Z]
    · dsimp only [selAAZ_HeldAct, rHeldAct, rPG7]
      rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          ← QRegister.compose_apply rAAZ, ← QRegister.compose_assoc, hAAZ_Data]
  have hCompHead : rAAZ.compose (selAAZ_AA.compose (selLiftAct rPosCoreInFull)) =
      rHeadAct := by
    refine qreg_ext_addCases (fun i ↦ ?_) (fun q ↦ ?_)
    · dsimp only [selLiftAct, rHeadAct, rCorePos]
      rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.concat_apply_left,
          QRegister.concat_apply_left, ← QRegister.compose_apply rAAZ selAAZ_AA, hAAZ_AA,
          QRegister.compose_apply, ← QRegister.compose_apply rAA (selDataInAct kFull80),
          concat_compose_selDataInAct, ← QRegister.compose_apply rAct rPosCoreInFull]
    · dsimp only [selLiftAct, rHeadAct]
      rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.concat_apply_right,
          QRegister.concat_apply_right, ← QRegister.compose_apply rAAZ selAAZ_AA, hAAZ_AA,
          ← QRegister.compose_apply rAA (selMeasInAct kFull80), concat_compose_selMeasInAct]
  -- Step 1: `RealizesOnProj` for 7-step Bell-18 `dMid5` on `P218_Bell_n * PW136`
  let PW136 := rW136.basisOutcomeProjector 0
  let P218_n := rAAZ.embedMatrix P218_AAZ
  let P218_Bell_n := rAAZH.embedMatrix P218_Bell_AAZH
  have hP218_CS : P218_n = rCS.embedMatrix (pStream218Core 80) := by
    dsimp only [P218_n]; rw [P218_AAZ_def, ← QRegister.embedMatrix_compose, hCompCS]
  have hP218_comm_W136 : P218_n * PW136 = PW136 * P218_n := by
    rw [hP218_CS]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0
  have hCHeld : rCore.DisjointWires rHeld18 := hAH.compose_left rCoreFull
  have hSHeld : rSum42.DisjointWires rHeld18 := hAH.compose_left rSum0
  have hW136Held : rW136.DisjointWires rHeld18 :=
    disjointWires_concat_left hWRestIdle (hWH.compose_left _)
      (hAH.compose_left spec.rIdle)
  have hHSW136 : (rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSHeld)).DisjointWires rW136 :=
    disjointWires_concat_left (QRegExt.disjointWires_symm hSHeld) (QRegExt.disjointWires_symm
      hW136Held) hSW136
  have hCompHS : rAAZH.compose
        (selAAZH_Held.concat (selAAZH_Data.compose rSum0)
          (QRegExt.disjointWires_symm (selAAZH_Data_disj_Held.compose_left rSum0))) =
      rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSHeld) := by
    refine qreg_ext_addCases (fun i ↦ ?_) (fun j ↦ ?_)
    · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
          ← QRegister.compose_apply rAAZH, hAAZH_Held]
    · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
          ← QRegister.compose_apply rAAZH, ← QRegister.compose_assoc, hAAZH_Data]
  have hAddHeldUnitEq : (rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSHeld)).embedUnitary
    uElec18Sum42Add =
      rAAZH.embedUnitary uAddHeld_AAZH := by
    unfold uAddHeld_AAZH
    rw [← QRegister.embedUnitary_compose, hCompHS]
  have hSubHeldUnitEq : (rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSHeld)).embedUnitary
    uElec18Sum42Add⁻¹ =
      rAAZH.embedUnitary uAddHeld_AAZH⁻¹ := by
    rw [QRegister.embedUnitary_inv, QRegister.embedUnitary_inv, hAddHeldUnitEq]
  have hAddHeldCommW136 : (rAAZH.embedUnitary uAddHeld_AAZH).1 * PW136 =
      PW136 * (rAAZH.embedUnitary uAddHeld_AAZH).1 := by
    rw [← hAddHeldUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rHeld18.concat rSum42
      (QRegExt.disjointWires_symm hSHeld)))
      rW136 hHSW136 _ 0
  have hSubHeldCommW136 : (rAAZH.embedUnitary uAddHeld_AAZH⁻¹).1 * PW136 =
      PW136 * (rAAZH.embedUnitary uAddHeld_AAZH⁻¹).1 := by
    rw [← hSubHeldUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rHeld18.concat rSum42
      (QRegExt.disjointWires_symm hSHeld)))
      rW136 hHSW136 _ 0
  have hP218Bell_eq : P218_Bell_n =
      (rAAZH.embedUnitary uAddHeld_AAZH⁻¹).1 * P218_n *
        (rAAZH.embedUnitary uAddHeld_AAZH).1 := by
    dsimp only [P218_Bell_n, P218_n]
    unfold P218_Bell_AAZH
    rw [rAAZH.embedMatrix_mul, rAAZH.embedMatrix_mul, QRegister.embedUnitary_val,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, hAAZH_AAZ]
  have hP218Bell_comm_W136 : P218_Bell_n * PW136 = PW136 * P218_Bell_n := by
    rw [hP218Bell_eq]
    exact mul_comm_op (mul_comm_op hSubHeldCommW136 hP218_comm_W136) hAddHeldCommW136
  have hPhiFUnitEq : rHeldAct.embedUnitary uPhiHeldZ18AnchorCat =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ) := by
    rw [← QRegister.embedUnitary_compose, hAAZH_AAZ, ← hCompHeld,
        QRegister.embedUnitary_compose, ← uPhiAnc_AAZ_def]
  have hPhiIUnitEq : rHeldAct.embedUnitary uPhiHeldZ18AnchorCat⁻¹ =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ⁻¹) := by
    rw [QRegister.embedUnitary_inv, QRegister.embedUnitary_inv,
        QRegister.embedUnitary_inv, hPhiFUnitEq]
  have hPhiIProj := realizesOnProj_of_clean_proj0 hHeldW136
    (dPhiOnHeldZ18AnchorInv128_realizes (by omega : 128 ≤ (mWorkSub18 - 36) + kIdle) v
      rHeldAct rW136 hHeldW136)
  rw [hPhiIUnitEq] at hPhiIProj
  have hPhiFRaw := realizesOnProj_of_clean_proj0 hHeldW136
    (dPhiOnHeldZ18AnchorFwd128_realizes (by omega : 128 ≤ (mWorkSub18 - 36) + kIdle) v
      rHeldAct rW136 hHeldW136)
  rw [hPhiFUnitEq] at hPhiFRaw
  have hPhiFProj := realizesOnProj_mul_right P218_Bell_n hPhiFRaw
  rw [← hP218Bell_comm_W136] at hPhiFProj
  obtain ⟨hStrAProj, hStrIProj⟩ :=
    hStr rCore rSum42 rW136 hCSum42 hCW136 hSW136 hCHeld hSHeld hW136Held
  have hHeadRaw := realizesOnProj_of_clean_proj0 hHeadDisjScr
    (dHeadAnchorConjH172_realizes (by omega : 172 ≤ ((mWorkSub18 - 36) + kIdle) + 42) v
      rCorePos rAnchor18 rScr178 (hAA.compose_left rPosCoreInFull) hCPScr hAnScr)
  have hScrProjEq : rScr178.basisOutcomeProjector 0 =
      rCS.embedMatrix pSum42CoreZero * PW136 := by
    have hSumProj : rCS.embedMatrix pSum42CoreZero = rSum42.basisOutcomeProjector 0 := by
      rw [pSum42CoreZero, embedMatrix_basisOutcomeProjector_zero_assoc]
      apply congrArg (fun r : QRegister 42 n ↦ r.basisOutcomeProjector 0)
      apply qreg_ext; intro j
      have hj : rZLoc (fullSysCoreWires 80) 42 j =
          Fin.natAdd (fullSysCoreWires 80) j :=
        Fin.ext (by simp [rZLoc])
      rw [QRegister.compose_apply, hj]
      dsimp only [rCS]
      rw [QRegister.concat_apply_right]
    rw [basisOutcomeProjector_zero_concat_eq_mul rW136 rSum42 (QRegExt.disjointWires_symm hSW136),
      hSumProj]
    exact basisOutcomeProjector_comm_part4 rW136 rSum42 0 0
  have hHeadUnitEq : rHeadAct.embedUnitary uHeadAnchorConjH =
      rAAZ.embedUnitary uHeadAnc_AAZ := by
    rw [← hCompHead, QRegister.embedUnitary_compose, ← uHeadAnc_AAZ_def]
  have hHeadLift : rAAZ.embedUnitary uHeadAnc_AAZ =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ) := by
    rw [← QRegister.embedUnitary_compose, hAAZH_AAZ]
  rw [hScrProjEq, hHeadUnitEq, hHeadLift] at hHeadRaw
  have hStrAUnitEq : rCS.embedUnitary uStr218_3Axis = rAAZ.embedUnitary uStr218_AAZ := by
    rw [← hCompCS, QRegister.embedUnitary_compose, ← uStr218_AAZ_def]
  have hStrALift : rCS.embedUnitary uStr218_3Axis =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ) := by
    rw [hStrAUnitEq, ← QRegister.embedUnitary_compose, hAAZH_AAZ]
  have hStrILift : rCS.embedUnitary uStr218_3Axis⁻¹ =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹) := by
    rw [QRegister.embedUnitary_inv, QRegister.embedUnitary_inv,
        QRegister.embedUnitary_inv, hStrALift]
  have hURefEq : (rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSHeld)).embedUnitary
    uElec18Sum42Add⁻¹ *
        rCS.embedUnitary uStr218_3Axis =
      rAAZH.embedUnitary (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ) := by
    rw [hSubHeldUnitEq, hStrALift, ← QRegister.embedUnitary_mul]
  have hURefInvEq :
      ((rHeld18.concat rSum42 (QRegExt.disjointWires_symm hSHeld)).embedUnitary uElec18Sum42Add⁻¹ *
        rCS.embedUnitary uStr218_3Axis)⁻¹ =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH) := by
    rw [hURefEq, ← QRegister.embedUnitary_inv, _root_.mul_inv_rev, inv_inv,
        QRegister.embedUnitary_inv]
  rw [hURefEq] at hStrAProj
  rw [hURefInvEq, hSubHeldUnitEq] at hStrIProj
  let eBell := (rAAZH.embedUnitary uAddHeld_AAZH⁻¹).1 * rCS.embedMatrix eStream218Core
  have hTransHead :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)).1 *
        (rCS.embedMatrix pSum42CoreZero * PW136) =
      (rCS.embedMatrix pSum42CoreZero * PW136) *
        (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)).1 := by
    rw [← hScrProjEq, ← hHeadLift, ← hHeadUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeadAct)
      rScr178 hHeadDisjScr _ 0
  have hHeadStrA := realizesOnProj_seq_part4 hTransHead hHeadRaw hStrAProj
  have hBellILeft :
      (rAAZH.embedUnitary
        (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 * eBell =
      rCS.embedMatrix pSum42CoreZero := by
    have hCancel : (rAAZH.embedUnitary uAddHeld_AAZH).1 *
        (rAAZH.embedUnitary uAddHeld_AAZH⁻¹).1 = 1 := by
      rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, mul_inv_cancel,
          QRegister.embedUnitary_one, OneMemClass.coe_one]
    dsimp only [eBell]
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (rAAZH.embedUnitary uAddHeld_AAZH).1, hCancel, Matrix.one_mul,
        ← hStrILift, QRegister.embedUnitary_val, ← rCS.embedMatrix_mul,
        inv_uStr218_3Axis_mul_eStream218Core_eq_pSum42CoreZero]
  have hTransBellI :
      (rAAZH.embedUnitary
        (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 * (eBell * PW136) =
      (rCS.embedMatrix pSum42CoreZero * PW136) * 1 := by
    rw [Matrix.mul_one, ← Matrix.mul_assoc, hBellILeft]
  have hMidE := realizesOnProj_seq_part4 hTransBellI hStrIProj hHeadStrA
  have hSubInvConj : (rAAZH.embedUnitary uAddHeld_AAZH⁻¹).1ᴴ =
      (rAAZH.embedUnitary uAddHeld_AAZH).1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv,
        ← QRegister.embedUnitary_inv, inv_inv]
  have hEBellHCommW : PW136 * eBellᴴ = eBellᴴ * PW136 := by
    have hCommE : PW136 * rCS.embedMatrix eStream218Coreᴴ =
        rCS.embedMatrix eStream218Coreᴴ * PW136 :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0).symm
    dsimp only [eBell]
    rw [Matrix.conjTranspose_mul, ← QRegister.embedMatrix_conjTranspose, hSubInvConj,
        ← Matrix.mul_assoc, hCommE, Matrix.mul_assoc, hAddHeldCommW136.symm,
        ← Matrix.mul_assoc]
  have hEBellMulH : eBell * eBellᴴ = P218_Bell_n := by
    dsimp only [eBell]
    rw [Matrix.conjTranspose_mul, ← QRegister.embedMatrix_conjTranspose, hSubInvConj,
        Matrix.mul_assoc, ← Matrix.mul_assoc (rCS.embedMatrix eStream218Core),
        ← rCS.embedMatrix_mul, eStream218Core_mul_conjTranspose, ← hP218_CS,
        ← Matrix.mul_assoc, ← hP218Bell_eq]
  have hP218BellMulEq : (eBell * PW136) * eBellᴴ = P218_Bell_n * PW136 := by
    rw [Matrix.mul_assoc, hEBellHCommW, ← Matrix.mul_assoc, hEBellMulH]
  have hMidBell := realizesOnProj_mul_right eBellᴴ hMidE
  rw [hP218BellMulEq] at hMidBell
  have hStrACommW :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ)).1 * PW136 =
      PW136 * (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ)).1 := by
    rw [← hStrALift]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0
  have hStrICommW :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹)).1 * PW136 =
      PW136 * (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹)).1 := by
    rw [← hStrILift]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCS) rW136 hCS_W136 _ 0
  have hHeadCommW :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)).1 * PW136 =
      PW136 * (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)).1 := by
    rw [← hHeadLift, ← hHeadUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeadAct)
      rW136 hHeadDisjW136 _ 0
  have hUACommW :
      (rAAZH.embedUnitary (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ)).1 *
        PW136 =
      PW136 * (rAAZH.embedUnitary
        (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ)).1 := by
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    exact mul_comm_op hSubHeldCommW136 hStrACommW
  have hUICommW :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 *
        PW136 =
      PW136 * (rAAZH.embedUnitary
        (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 := by
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    exact mul_comm_op hStrICommW hAddHeldCommW136
  have hMid5CommW :
      ((rAAZH.embedUnitary (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ) *
        rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)) *
        rAAZH.embedUnitary
          (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 * PW136 =
      PW136 * ((rAAZH.embedUnitary
          (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ) *
        rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)) *
        rAAZH.embedUnitary
          (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 := by
    simp only [Submonoid.coe_mul]
    exact mul_comm_op (mul_comm_op hUACommW hHeadCommW) hUICommW
  have hPhiFCommW136 :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ)).1 * PW136 =
      PW136 * (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ)).1 := by
    rw [← hPhiFUnitEq]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHeldAct) rW136 hHeldW136 _ 0
  have hPhiFCommP218Bell :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ)).1 *
        (P218_Bell_n * PW136) =
      (P218_Bell_n * PW136) *
        (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ)).1 := by
    dsimp only [P218_Bell_n]
    rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, ← rAAZH.embedMatrix_mul,
        uOps_AAZH_comm_P218_Bell.1, rAAZH.embedMatrix_mul, Matrix.mul_assoc,
        ← QRegister.embedUnitary_val, hPhiFCommW136, ← Matrix.mul_assoc]
  have hMid5TransW :
      ((rAAZH.embedUnitary (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ) *
        rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)) *
        rAAZH.embedUnitary
          (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 *
        (P218_Bell_n * PW136) =
      PW136 * (((rAAZH.embedUnitary
          (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ) *
        rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)) *
        rAAZH.embedUnitary
          (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH)).1 * P218_Bell_n) := by
    rw [hP218Bell_comm_W136, ← Matrix.mul_assoc, hMid5CommW, Matrix.mul_assoc]
  have hMid6 := realizesOnProj_seq_part4 hMid5TransW hMidBell hPhiIProj
  have hMid7Seq := realizesOnProj_seq_part4 hPhiFCommP218Bell hPhiFProj hMid6
  let U_mid7 := rAAZH.embedUnitary uMid7_Bell18_AAZH
  have hMid7UnitEq :
      (rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ⁻¹) *
        ((rAAZH.embedUnitary (uAddHeld_AAZH⁻¹ * selAAZH_AAZ.embedUnitary uStr218_AAZ) *
          rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uHeadAnc_AAZ)) *
          rAAZH.embedUnitary
            (selAAZH_AAZ.embedUnitary uStr218_AAZ⁻¹ * uAddHeld_AAZH))) *
        rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uPhiAnc_AAZ) = U_mid7 := by
    dsimp only [U_mid7, uMid7_Bell18_AAZH]
    simp only [QRegister.embedUnitary_mul, _root_.mul_assoc]
  rw [hMid7UnitEq] at hMid7Seq
  let dMid5Seq :=
    DynamicCircuit.seq
      (dPhiOnHeldZ18AnchorFwd128 (by omega : 128 ≤ (mWorkSub18 - 36) + kIdle) v
        rHeldAct rW136 hHeldW136)
      (.seq (dStrInv rCore rSum42 rW136 hCSum42 hCW136 hSW136)
        (.seq (dHeadAnchorConjH172 (by omega : 172 ≤ ((mWorkSub18 - 36) + kIdle) + 42) v
            rCorePos rAnchor18 rScr178 (hAA.compose_left rPosCoreInFull) hCPScr hAnScr)
          (.seq (dStrAdd rCore rSum42 rW136 hCSum42 hCW136 hSW136)
            (dPhiOnHeldZ18AnchorInv128 (by omega : 128 ≤ (mWorkSub18 - 36) + kIdle) v
              rHeldAct rW136 hHeldW136))))
  have hMid7Proj : RealizesOnProj (P218_Bell_n * PW136) U_mid7 dMid5Seq := by
    intro M
    obtain ⟨M', hwp, heq⟩ := hMid7Seq M
    refine ⟨M', ?_, heq⟩
    simpa only [dMid5Seq, DynamicCircuit.compile_seq, wp_qSeq] using hwp
  -- Step 2: Single-sum commutation of `C_18` with `U_mid7` on `P218_Bell_n * PW136`
  let C_18 : Unitary (2 ^ n) := (rSubstPos.concat rCarry18 hSubPCarry).embedUnitary uXorCarry18
  have hC18_sq : C_18.1 * C_18.1 = 1 := by
    dsimp only [C_18]
    rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uXorCarry18_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hC18_herm : C_18.1ᴴ = C_18.1 := by
    have hinv : C_18⁻¹ = C_18 := mul_eq_one_iff_inv_eq.mp (Subtype.ext hC18_sq)
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hinv]
  have hP218W_herm : (P218_Bell_n * PW136)ᴴ = P218_Bell_n * PW136 := by
    have hP218H : P218_Bell_nᴴ = P218_Bell_n := by
      dsimp only [P218_Bell_n]
      rw [← QRegister.embedMatrix_conjTranspose, P218_Bell_AAZH_herm]
    rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose, hP218H,
        hP218Bell_comm_W136.symm]
  have hC18_sum0 := embedUnitary_uXorCarry18_eq_sum_D_carry rAAZ rSubstPos rCarry18
    hSubPCarry hCompSubPos
  have hD_lift : ∀ u : Fin (2 ^ 18),
      rAAZ.embedMatrix (D_carry_AAZ u) = rAAZH.embedMatrix (D_carry_Bell_AAZH u) := fun u ↦ by
    unfold D_carry_Bell_AAZH
    rw [← QRegister.embedMatrix_compose, hAAZH_AAZ]
  have hC18_sum : ((rSubstPos.concat rCarry18 hSubPCarry).embedUnitary uXorCarry18).1 =
      ∑ u : Fin (2 ^ 18),
        rAAZH.embedMatrix (D_carry_Bell_AAZH u) *
          (rCarry18.embedUnitary (uXorConst18 u)).1 := by
    rw [hC18_sum0]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [hD_lift u]
  have hD_comm_W136 : ∀ u : Fin (2 ^ 18),
      rAAZH.embedMatrix (D_carry_Bell_AAZH u) * PW136 =
        PW136 * rAAZH.embedMatrix (D_carry_Bell_AAZH u) := fun u ↦ by
    rw [← hD_lift u]
    unfold D_carry_AAZ PW136
    rw [embedMatrix_diagonal_local, QRegister.basisOutcomeProjector_eq_diagonal]
    exact diagonal_comm_op_assoc _ _
  have hC18_comm_P218W :
      C_18.1 * (P218_Bell_n * PW136) = (P218_Bell_n * PW136) * C_18.1 := by
    dsimp only [C_18]
    rw [hC18_sum]
    refine sum_mul_comm_part4 _ _ fun u ↦ ?_
    let X_u := (rCarry18.embedUnitary (uXorConst18 u)).1
    have hX_P218 : X_u * P218_Bell_n = P218_Bell_n * X_u :=
      (rAAZH.embedMatrix_comm_of_disjoint rCarry18 hAAZH_Carry
        P218_Bell_AAZH (uXorConst18 u).1).symm
    have hX_W136 : X_u * PW136 = PW136 * X_u :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCarry18) rW136 hCarryW136 _ 0
    have hD_P218 : rAAZH.embedMatrix (D_carry_Bell_AAZH u) * P218_Bell_n =
        P218_Bell_n * rAAZH.embedMatrix (D_carry_Bell_AAZH u) := by
      dsimp only [P218_Bell_n]
      rw [← rAAZH.embedMatrix_mul, D_carry_Bell_AAZH_comm_P218_Bell u, rAAZH.embedMatrix_mul]
    exact mul_comm_op
      (mul_comm_op hD_P218.symm (hD_comm_W136 u).symm).symm
      (mul_comm_op hX_P218.symm hX_W136.symm).symm
  have hC18_conj_Umid7 :
      (C_18.1 * U_mid7.1 * C_18.1ᴴ) * (P218_Bell_n * PW136) =
        U_mid7.1 * (P218_Bell_n * PW136) := by
    have hInter : U_mid7.1 * (C_18.1 * (P218_Bell_n * PW136)) =
        C_18.1 * (U_mid7.1 * (P218_Bell_n * PW136)) := by
      dsimp only [C_18]; rw [hC18_sum]
      refine mul_sum_mul_part4 _ _ _ fun u ↦ ?_
      let X_u := (rCarry18.embedUnitary (uXorConst18 u)).1
      have hU_X : U_mid7.1 * X_u = X_u * U_mid7.1 :=
        rAAZH.embedMatrix_comm_of_disjoint rCarry18 hAAZH_Carry
          uMid7_Bell18_AAZH.1 (uXorConst18 u).1
      have hD_X : rAAZH.embedMatrix (D_carry_Bell_AAZH u) * X_u =
          X_u * rAAZH.embedMatrix (D_carry_Bell_AAZH u) :=
        rAAZH.embedMatrix_comm_of_disjoint rCarry18 hAAZH_Carry
          (D_carry_Bell_AAZH u) (uXorConst18 u).1
      have hUMidD : U_mid7.1 * (rAAZH.embedMatrix (D_carry_Bell_AAZH u) * P218_Bell_n) =
          rAAZH.embedMatrix (D_carry_Bell_AAZH u) * (U_mid7.1 * P218_Bell_n) := by
        dsimp only [U_mid7, P218_Bell_n]
        rw [QRegister.embedUnitary_val, ← rAAZH.embedMatrix_mul, ← rAAZH.embedMatrix_mul,
            uMid7_Bell18_AAZH_comm_D_carry_on_P218_Bell u,
            rAAZH.embedMatrix_mul, rAAZH.embedMatrix_mul]
      rw [hD_X, Matrix.mul_assoc X_u, ← Matrix.mul_assoc U_mid7.1 X_u, hU_X,
          Matrix.mul_assoc X_u U_mid7.1,
          ← Matrix.mul_assoc (rAAZH.embedMatrix (D_carry_Bell_AAZH u)) P218_Bell_n PW136,
          ← Matrix.mul_assoc U_mid7.1 _ PW136, hUMidD,
          Matrix.mul_assoc (rAAZH.embedMatrix (D_carry_Bell_AAZH u)),
          Matrix.mul_assoc U_mid7.1 P218_Bell_n PW136, ← Matrix.mul_assoc X_u, ← hD_X]
    rw [hC18_herm, Matrix.mul_assoc (C_18.1 * U_mid7.1) C_18.1,
        Matrix.mul_assoc C_18.1 U_mid7.1, hInter, ← Matrix.mul_assoc C_18.1 C_18.1,
        hC18_sq, Matrix.one_mul]
  have hMid7Peb₀ : PebRealizes (P218_Bell_n * PW136) U_mid7.1 dMid5Seq :=
    (pebRealizes_iff_realizesOnProj hP218W_herm U_mid7 dMid5Seq).mpr hMid7Proj
  have hMid7PebC18 := hMid7Peb₀.congr_op hP218W_herm hC18_conj_Umid7.symm
  -- Step 3: Forward pebbled unitary `V_tot` on `PHold36_0` agrees with `C_18 * U_xorZ`
  let L := zTargetSteps36 (le_refl 36) rSubstPos rHold36 hSubPHold
  let cXorQ : Circuit n := copyXorRegCircuit (phcHead_rQRev18 rSubstPos) rZ18 hQDisj
  let V_tot : Unitary (2 ^ n) := cXorQ.eval * uSymStepFwdList L
  let U_xorZ : Unitary (2 ^ n) := rAAZ.embedUnitary uXorSubst_AAZ
  have hUxorZ_AAZH : U_xorZ =
      rAAZH.embedUnitary (selAAZH_AAZ.embedUnitary uXorSubst_AAZ) := by
    dsimp only [U_xorZ]; rw [← QRegister.embedUnitary_compose, hAAZH_AAZ]
  have hUxorZ_eq : U_xorZ = (rSubstPos.concat rZ18 hSubPZ).embedUnitary uXorZTarget18 := by
    dsimp only [U_xorZ]; rw [uXorSubst_AAZ_def, ← QRegister.embedUnitary_compose, hCompSubstPZ]
  have hUxorZ_sq : U_xorZ.1 * U_xorZ.1 = 1 := by
    rw [hUxorZ_eq, ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uXorZTarget18_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hUxorZ_herm : U_xorZ.1ᴴ = U_xorZ.1 := by
    have hinv : U_xorZ⁻¹ = U_xorZ := mul_eq_one_iff_inv_eq.mp (Subtype.ext hUxorZ_sq)
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hinv]
  let PHold36_0 := rHold36.basisOutcomeProjector 0
  let PCarry18_0 := rCarry18.basisOutcomeProjector 0
  let PZ18_0 := rZ18.basisOutcomeProjector 0
  have hVtot_PHold : V_tot.1 * PHold36_0 = (C_18 * U_xorZ).1 * PHold36_0 := by
    apply matrix_ext_ket; intro β
    have hket : ∀ γ : BitAssignment n, ket γ = MeasureBranchHadamardSem.ket γ := fun _ ↦ rfl
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [PHold36_0]
    rw [← projZeroAll_eq_basisOutcomeProjector_zero]
    by_cases hClean : ∀ idx : Fin 36, β (rHold36 idx) = 0
    · rw [hket β, ket_projZeroAll, ite_eq_left hClean, ← hket β]
      dsimp only [V_tot]
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, ket_uSymStepFwdList]
      have hcXorQKet : ∀ γ : BitAssignment n,
          cXorQ.eval.1.mulVec (ket γ) =
            ket (writeReg γ rZ18 fun k ↦ γ (rZ18 k) + γ (phcHead_rQRev18 rSubstPos k)) :=
        fun γ ↦ by simpa only [ket_eq_basisKet] using
          copyXorRegCircuit_classicalPerm (phcHead_rQRev18 rSubstPos) rZ18 hQDisj γ
      rw [hcXorQKet, hUxorZ_eq, ket_embedUnitary_uXorZTarget18, ket_embedUnitary_uXorCarry18]
      obtain ⟨_, heL⟩ := zTargetSteps36_valid_and_eval (le_refl 36) rSubstPos rHold36 hSubPHold
        ∅ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
      obtain ⟨hMuxVal, hOutL⟩ := heL β hClean
      let β' := writeReg β rZ18 fun k ↦
        β (rZ18 k) + basisBits 18 (headTargetPoint18 (fun i ↦ β (rSubstPos i))) k
      have hSubPos_β' : (fun i ↦ β' (rSubstPos i)) = fun i ↦ β (rSubstPos i) :=
        funext fun i ↦ writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦ hSubPZ.ne i k hk.symm)
      refine congrArg ket (funext fun z ↦ ?_)
      by_cases hCz : ∃ k : Fin 18, rCarry18 k = z
      · obtain ⟨k, rfl⟩ := hCz
        have hNotZ : rCarry18 k ∉ Set.range rZ18.wires :=
          fun ⟨j, hj⟩ ↦ (rCarry18OfSub18_disj_rZ18OfSub18 hm36 rWork).ne k j hj.symm
        rw [writeReg_apply_of_not_mem _ _ _ _ hNotZ, writeReg_apply_reg,
            writeReg_apply_of_not_mem _ _ _ _ hNotZ, hSubPos_β']
        have hCarryIdx : rCarry18 k = rHold36 ⟨k.val, by have := k.isLt; omega⟩ := by
          simp only [rCarry18, rHold36, rCarry18OfSub18, rHold36OfSub18, QRegister.slice_apply]
        rw [hCarryIdx, hClean _, zero_add]
        exact zTargetSteps36_eval_carry rSubstPos rHold36 hSubPHold β hClean k
      · rw [writeReg_apply_of_not_mem _ _ _ _ hCz]
        by_cases hZz : ∃ k : Fin 18, rZ18 k = z
        · obtain ⟨k, rfl⟩ := hZz
          rw [writeReg_apply_reg, writeReg_apply_reg]
          have hZIdx : rZ18 k = rHold36 ⟨18 + k.val, by have := k.isLt; omega⟩ := by
            dsimp only [rZ18, rHold36, rZ18OfSub18, rHold36OfSub18]
            rw [QRegister.slice_apply, QRegister.slice_apply]
            exact congrArg rWork (Fin.ext (by dsimp only; omega))
          rw [hZIdx, hClean _, zero_add]
          have hQ_L : symStepFwdList L β (phcHead_rQRev18 rSubstPos k) =
              β (phcHead_rQRev18 rSubstPos k) :=
            hOutL _ fun idx heq ↦ by
              obtain ⟨i, hi⟩ := (QRegister.mem_image rSubstPos _).mp
                (phcHead_rQRev18_mem_core rSubstPos k)
              exact hSubPHold.ne i idx (hi.trans heq)
          rw [hQ_L]
          let w : Fin 3 := ⟨k.val / 6, by have := k.isLt; omega⟩
          let j : Fin 6 := ⟨5 - k.val % 6, by omega⟩
          have hk_eq : k =
              ⟨6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩ :=
            Fin.ext (by dsimp only [w, j]; have := k.isLt; omega)
          have hHoldIdx : (⟨18 + k.val, by have := k.isLt; omega⟩ : Fin 36) =
              ⟨18 + 6 * w.val + (5 - j.val), by have := w.isLt; have := j.isLt; omega⟩ :=
            Fin.ext (by dsimp only [w, j]; have := k.isLt; omega)
          have hQIdx : phcHead_rQRev18 rSubstPos k =
              rHeadFine21 rSubstPos
                ⟨7 * w.val + j.val + 1, by have := w.isLt; have := j.isLt; omega⟩ :=
            congrArg (rHeadFine21 rSubstPos).wires
              (Fin.ext (by dsimp [phcHead_rQRev18, w, j]))
          have hBit := headTargetPoint18_bit_eq_mux_xor_q rSubstPos β w j
          rw [← hk_eq] at hBit
          rw [hHoldIdx, hMuxVal w j, hQIdx, hBit]
        · rw [writeReg_apply_of_not_mem _ _ _ _ hZz, writeReg_apply_of_not_mem _ _ _ _ hZz]
          exact hOutL z fun idx heq ↦ by
            by_cases hlt18 : idx.val < 18
            · exact hCz ⟨⟨idx.val, hlt18⟩, by
                rw [heq]
                simp only [rCarry18, rHold36, rCarry18OfSub18, rHold36OfSub18,
                  QRegister.slice_apply]⟩
            · exact hZz ⟨⟨idx.val - 18, by have := idx.isLt; omega⟩, by
                rw [heq]
                dsimp only [rZ18, rHold36, rZ18OfSub18, rHold36OfSub18]
                rw [QRegister.slice_apply, QRegister.slice_apply]
                exact congrArg rWork (Fin.ext (by dsimp only; omega))⟩
    · rw [hket β, ket_projZeroAll, ite_eq_right hClean, Matrix.mulVec_zero, Matrix.mulVec_zero]
  -- Step 4: Projectors `P_init_n`, `P_sw_n`, `P_mid` & wrapping `dMid5` -> `dPeb` -> `dInnerSwap`
  let uSw_H := selAAZH_AAZ.embedUnitary uSw_AAZ
  let uXor_H := selAAZH_AAZ.embedUnitary uXorSubst_AAZ
  let P_init_H := E_init_Bell_AAZH * E_init_Bell_AAZHᴴ
  let P_sw_H := uSw_H.1 * P_init_H * uSw_H.1ᴴ
  have hPinitH_herm : P_init_Hᴴ = P_init_H := by
    simp [P_init_H, Matrix.conjTranspose_mul]
  have hPswH_herm : P_sw_Hᴴ = P_sw_H := by
    simp [P_sw_H, Matrix.conjTranspose_mul, hPinitH_herm, Matrix.mul_assoc]
  have hSwSq_AAZ : uSw_AAZ * uSw_AAZ = 1 := uSw_AAZ_mul_self
  have hSwSq_H : uSw_H * uSw_H = 1 := by
    dsimp only [uSw_H]
    rw [← QRegister.embedUnitary_mul, hSwSq_AAZ, QRegister.embedUnitary_one]
  have hSwHerm_H : uSw_H.1ᴴ = uSw_H.1 := by
    have hinv : uSw_H⁻¹ = uSw_H := mul_eq_one_iff_inv_eq.mp hSwSq_H
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hinv]
  have hPW136_split : PW136 =
      rWRest.basisOutcomeProjector 0 * rIdle11.basisOutcomeProjector 0 :=
    basisOutcomeProjector_zero_concat_eq_mul rWRest rIdle11 hWRestIdle
  have hIdleProj_H : rIdle11.basisOutcomeProjector 0 =
      rAAZH.embedMatrix
        ((selAAZH_Data.compose spec.rIdle).basisOutcomeProjector 0) := by
    rw [embedMatrix_basisOutcomeProjector_gen_part4, ← QRegister.compose_assoc, hAAZH_Data]
  have hCommW136_of_idle : ∀ {M : Operator (2 ^ kAAZH)},
      M * (selAAZH_Data.compose spec.rIdle).basisOutcomeProjector 0 =
        (selAAZH_Data.compose spec.rIdle).basisOutcomeProjector 0 * M →
      rAAZH.embedMatrix M * PW136 = PW136 * rAAZH.embedMatrix M := fun {M} hIdle ↦ by
    have h1 : rAAZH.embedMatrix M * rWRest.basisOutcomeProjector 0 =
        rWRest.basisOutcomeProjector 0 * rAAZH.embedMatrix M :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZH) rWRest hAAZH_WRest M 0
    have h2 : rAAZH.embedMatrix M * rIdle11.basisOutcomeProjector 0 =
        rIdle11.basisOutcomeProjector 0 * rAAZH.embedMatrix M := by
      rw [hIdleProj_H, ← rAAZH.embedMatrix_mul, hIdle, rAAZH.embedMatrix_mul]
    rw [hPW136_split, ← Matrix.mul_assoc, h1,
        Matrix.mul_assoc _ _ (rIdle11.basisOutcomeProjector 0), h2, ← Matrix.mul_assoc]
  have hEinit_comm_W136 := hCommW136_of_idle spec.comm_E_init.1
  have hPinit_comm_W136 := hCommW136_of_idle spec.comm_E_init.2
  have hSwCore : rAAZH.embedUnitary uSw_H = rCore.embedUnitary uSwapCore3967 := by
    dsimp only [uSw_H]
    rw [← QRegister.embedUnitary_compose, hAAZH_AAZ, uSw_AAZ_def,
        ← QRegister.embedUnitary_compose, hCompCore]
  have hSw_comm_W136 :
      (rAAZH.embedUnitary uSw_H).1 * PW136 = PW136 * (rAAZH.embedUnitary uSw_H).1 := by
    rw [hSwCore]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCore) rW136 hCW136 _ 0
  have hPsw_comm_W136 :
      rAAZH.embedMatrix P_sw_H * PW136 = PW136 * rAAZH.embedMatrix P_sw_H := by
    dsimp only [P_sw_H]
    rw [hSwHerm_H, rAAZH.embedMatrix_mul, rAAZH.embedMatrix_mul, ← QRegister.embedUnitary_val]
    exact mul_comm_op (mul_comm_op hSw_comm_W136 hPinit_comm_W136) hSw_comm_W136
  let P_CW := PCarry18_0 * PW136
  have hPCW_herm : P_CWᴴ = P_CW := by
    dsimp only [P_CW, PCarry18_0, PW136]
    rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
        QRegister.basisOutcomeProjector_conjTranspose]
    exact (basisOutcomeProjector_comm_part4 rCarry18 rW136 0 0).symm
  let P_init_n := rAAZH.embedMatrix P_init_H * P_CW
  let P_sw_n := rAAZH.embedMatrix P_sw_H * P_CW
  have hCommPCW_of_W136 : ∀ {M : Operator (2 ^ kAAZH)},
      rAAZH.embedMatrix M * PW136 = PW136 * rAAZH.embedMatrix M →
      rAAZH.embedMatrix M * P_CW = P_CW * rAAZH.embedMatrix M := fun hW ↦ by
    dsimp only [P_CW]
    rw [← Matrix.mul_assoc,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZH) rCarry18 hAAZH_Carry _ 0,
        Matrix.mul_assoc, hW, ← Matrix.mul_assoc]
  have hPinit_comm_PCW := hCommPCW_of_W136 hPinit_comm_W136
  have hPsw_comm_PCW := hCommPCW_of_W136 hPsw_comm_W136
  have hPinit_n_herm : P_init_nᴴ = P_init_n := by
    dsimp only [P_init_n]
    rw [Matrix.conjTranspose_mul, hPCW_herm, ← QRegister.embedMatrix_conjTranspose,
        hPinitH_herm, hPinit_comm_PCW.symm]
  have hPsw_n_herm : P_sw_nᴴ = P_sw_n := by
    dsimp only [P_sw_n]
    rw [Matrix.conjTranspose_mul, hPCW_herm, ← QRegister.embedMatrix_conjTranspose,
        hPswH_herm, hPsw_comm_PCW.symm]
  let uC7_H := uXor_H * uMid7_Bell18_AAZH * uXor_H
  let U_peb := rAAZH.embedUnitary uC7_H
  let U_C9 := rAAZH.embedUnitary uC9_Bell18_AAZH
  have huC9_eq_sw_uC7 : uC9_Bell18_AAZH = uSw_H * uC7_H * uSw_H := by
    unfold uC9_Bell18_AAZH
    dsimp only [uSw_H, uC7_H, uXor_H]
    simp only [_root_.mul_assoc]
  have hSwZ_H : selAAZH_Z.basisOutcomeProjector 0 * uSw_H.1 =
      uSw_H.1 * selAAZH_Z.basisOutcomeProjector 0 := by
    have hEq : uSw_H = (selAAZH_Data.compose rCoreFull).embedUnitary uSwapCore3967 := by
      dsimp only [uSw_H]
      rw [uSw_AAZ_def, ← QRegister.embedUnitary_compose]
      exact congrArg (fun r : QRegister _ _ ↦ r.embedUnitary uSwapCore3967)
        (qreg_ext fun _ ↦ rfl)
    rw [hEq, QRegister.embedUnitary_val]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (selAAZH_Data.compose
      rCoreFull))
      selAAZH_Z
      (disjointWires_compose_of_disjoint selAAZH_AAZ
        (selAAZ_Data_disj_Z.compose_left rCoreFull)) _ 0).symm
  have hPZ_PswH : selAAZH_Z.basisOutcomeProjector 0 * P_sw_H = P_sw_H := by
    dsimp only [P_sw_H, P_init_H]
    rw [← Matrix.mul_assoc _ _ uSw_H.1ᴴ, ← Matrix.mul_assoc _ uSw_H.1, hSwZ_H,
        Matrix.mul_assoc uSw_H.1, ← Matrix.mul_assoc _ E_init_Bell_AAZH,
        selAAZH_Z_proj0_mul_E_init_Bell]
  have hPZ_UpebPswH :
      selAAZH_Z.basisOutcomeProjector 0 * (uC7_H.1 * P_sw_H) = uC7_H.1 * P_sw_H := by
    have hAA_Z_comm : selAAZH_Z.basisOutcomeProjector 0 *
        (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 =
        (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
          selAAZH_Z.basisOutcomeProjector 0 :=
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAAZH_AA) selAAZH_Z
        (disjointWires_compose_of_disjoint selAAZH_AAZ
          (selDataInAct_disj_selMeasInAct (kFull80 + 18))) _ 0).symm
    have hC7Sw : uC7_H.1 * uSw_H.1 * E_init_Bell_AAZH =
        uSw_H.1 * ((selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)).1 *
          E_init_Bell_AAZH) := by
      have hSwSqM : uSw_H.1 * uSw_H.1 = 1 := by
        rw [← Submonoid.coe_mul, hSwSq_H, OneMemClass.coe_one]
      have hC9M := uC9_Bell18_AAZH_eq_on_E_init_Bell
      rw [huC9_eq_sw_uC7, Submonoid.coe_mul, Submonoid.coe_mul] at hC9M
      rw [← hC9M, ← Matrix.mul_assoc uSw_H.1, ← Matrix.mul_assoc uSw_H.1 (uSw_H.1 * uC7_H.1),
          ← Matrix.mul_assoc uSw_H.1 uSw_H.1, hSwSqM, Matrix.one_mul]
    dsimp only [P_sw_H, P_init_H]
    have hAssoc : uC7_H.1 * (uSw_H.1 * (E_init_Bell_AAZH * E_init_Bell_AAZHᴴ) * uSw_H.1ᴴ) =
        ((uC7_H.1 * uSw_H.1 * E_init_Bell_AAZH) * E_init_Bell_AAZHᴴ) * uSw_H.1ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [hAssoc, hC7Sw, ← Matrix.mul_assoc _ _ uSw_H.1ᴴ,
        ← Matrix.mul_assoc _ _ E_init_Bell_AAZHᴴ, ← Matrix.mul_assoc _ uSw_H.1, hSwZ_H,
        Matrix.mul_assoc uSw_H.1,
        ← Matrix.mul_assoc _ _ E_init_Bell_AAZH, hAA_Z_comm,
        Matrix.mul_assoc _ _ E_init_Bell_AAZH, selAAZH_Z_proj0_mul_E_init_Bell]
  have hPHold_split : PHold36_0 = PZ18_0 * PCarry18_0 := by
    dsimp only [PHold36_0, PZ18_0, PCarry18_0]
    rw [← rCarry18OfSub18_proj0_mul_rZ18OfSub18_proj0 hm36 rWork]
    exact basisOutcomeProjector_comm_part4 rCarry18 rZ18 0 0
  have hPZ_eq_H : PZ18_0 = rAAZH.embedMatrix (selAAZH_Z.basisOutcomeProjector 0) := by
    dsimp only [PZ18_0]; rw [embedMatrix_basisOutcomeProjector_gen_part4, hAAZH_Z]
  have hPHold_of_Z : ∀ {M : Operator (2 ^ kAAZH)},
      selAAZH_Z.basisOutcomeProjector 0 * M = M →
      PHold36_0 * (rAAZH.embedMatrix M * P_CW) = rAAZH.embedMatrix M * P_CW :=
    fun {M} hZM ↦ by
      dsimp only [P_CW]
      rw [hPHold_split, hPZ_eq_H]
      calc (rAAZH.embedMatrix (selAAZH_Z.basisOutcomeProjector 0) * PCarry18_0) *
              (rAAZH.embedMatrix M * (PCarry18_0 * PW136))
          = (rAAZH.embedMatrix (selAAZH_Z.basisOutcomeProjector 0) * rAAZH.embedMatrix M) *
              (PCarry18_0 * PCarry18_0) * PW136 := by
              rw [Matrix.mul_assoc (rAAZH.embedMatrix (selAAZH_Z.basisOutcomeProjector 0)),
                  ← Matrix.mul_assoc PCarry18_0,
                  ← (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZH)
                    rCarry18 hAAZH_Carry M 0]
              dsimp only [PCarry18_0]
              simp only [Matrix.mul_assoc]
        _ = rAAZH.embedMatrix M * (PCarry18_0 * PW136) := by
              dsimp only [PCarry18_0]
              rw [← rAAZH.embedMatrix_mul, hZM, basisOutcomeProjector_zero_mul_self,
                  Matrix.mul_assoc]
  have hPHold_Psw : PHold36_0 * P_sw_n = P_sw_n := hPHold_of_Z hPZ_PswH
  have hPHold_UpebPsw : PHold36_0 * (U_peb.1 * P_sw_n) = U_peb.1 * P_sw_n := by
    dsimp only [P_sw_n, U_peb]
    rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc (rAAZH.embedMatrix uC7_H.1),
        ← rAAZH.embedMatrix_mul]
    exact hPHold_of_Z hPZ_UpebPswH
  let P_mid := V_tot.1 * P_sw_n * V_tot.1ᴴ
  have hPmid_herm : P_midᴴ = P_mid := by
    simp [P_mid, Matrix.conjTranspose_mul, hPsw_n_herm, Matrix.mul_assoc]
  have hVtot_Psw : V_tot.1 * P_sw_n = (C_18 * U_xorZ).1 * P_sw_n := by
    rw [← hPHold_Psw, ← Matrix.mul_assoc, hVtot_PHold, Matrix.mul_assoc]
  have hadj : P_sw_n * V_tot.1ᴴ = P_sw_n * (C_18 * U_xorZ).1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPsw_n_herm] using congrArg (·ᴴ) hVtot_Psw
  have hPmid_eq : P_mid = (C_18 * U_xorZ).1 * P_sw_n * (C_18 * U_xorZ).1ᴴ := by
    dsimp only [P_mid]
    rw [hVtot_Psw, Matrix.mul_assoc _ P_sw_n V_tot.1ᴴ, hadj, ← Matrix.mul_assoc]
  have hUxorZ_comm_P218W :
      U_xorZ.1 * (P218_Bell_n * PW136) = (P218_Bell_n * PW136) * U_xorZ.1 := by
    have hSubIdle : rSubst.compose spec.rIdle = rIdle11 := by
      apply qreg_ext; intro j
      dsimp only [rSubst, rActAnchorSubst, rIdle11]
      rw [QRegister.compose_apply, QRegister.compose_apply,
          rDataSubstSlot0_apply_of_not_mem _ _ _ _
            (fun ⟨q, hq⟩ ↦ spec.hSlot0.ne q j hq)]
    have hSubPosIdle : rSubstPos.DisjointWires rIdle11 := by
      rw [← hSubIdle]
      exact disjointWires_compose_of_disjoint rSubst
        (spec.hCore.compose_left selPosCoreInCore80)
    have hSubPZ_W136 : (rSubstPos.concat rZ18 hSubPZ).DisjointWires rW136 :=
      disjointWires_concat_left hSubPZ
        (disj_concat_right_part4 hWRestIdle
          ((hSubW.compose_left rPosCoreInFull).compose_right _) hSubPosIdle)
        hZW136
    have hUW : U_xorZ.1 * PW136 = PW136 * U_xorZ.1 := by
      rw [hUxorZ_eq]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rSubstPos.concat rZ18
        hSubPZ))
        rW136 hSubPZ_W136 _ 0
    rw [hUxorZ_AAZH] at hUW ⊢
    dsimp only [P218_Bell_n]
    rw [← Matrix.mul_assoc, QRegister.embedUnitary_val, ← rAAZH.embedMatrix_mul,
        uOps_AAZH_comm_P218_Bell.2.2.1, rAAZH.embedMatrix_mul, Matrix.mul_assoc,
        ← QRegister.embedUnitary_val, hUW, ← Matrix.mul_assoc]
  have hP218W_sub_Pmid : (P218_Bell_n * PW136) * P_mid = P_mid := by
    have hP218_PswH : P218_Bell_AAZH * P_sw_H = P_sw_H := by
      dsimp only [P_sw_H, P_init_H, uSw_H]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← uOps_AAZH_comm_P218_Bell.2.2.2,
          Matrix.mul_assoc _ P218_Bell_AAZH, ← Matrix.mul_assoc P218_Bell_AAZH,
          P218_Bell_AAZH_mul_E_init_Bell]
    have hPW_PCW : PW136 * P_CW = P_CW := by
      dsimp only [P_CW, PCarry18_0, PW136]
      rw [← Matrix.mul_assoc, (basisOutcomeProjector_comm_part4 rCarry18 rW136 0 0).symm,
          Matrix.mul_assoc, basisOutcomeProjector_zero_mul_self]
    have hP218W_Psw : (P218_Bell_n * PW136) * P_sw_n = P_sw_n := by
      dsimp only [P_sw_n, P218_Bell_n]
      rw [Matrix.mul_assoc (rAAZH.embedMatrix P218_Bell_AAZH) PW136,
          ← Matrix.mul_assoc PW136 _ P_CW, hPsw_comm_W136.symm,
          Matrix.mul_assoc _ PW136 P_CW, hPW_PCW, ← Matrix.mul_assoc,
          ← rAAZH.embedMatrix_mul, hP218_PswH]
    have hCU_comm :
        (P218_Bell_n * PW136) * (C_18 * U_xorZ).1 =
          (C_18 * U_xorZ).1 * (P218_Bell_n * PW136) :=
      (mul_comm_op hC18_comm_P218W hUxorZ_comm_P218W).symm
    rw [hPmid_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCU_comm,
        Matrix.mul_assoc (C_18 * U_xorZ).1 _ P_sw_n, hP218W_Psw]
  have hOpOnPmid : (C_18.1 * U_mid7.1 * C_18.1ᴴ) * P_mid =
      (V_tot.1 * U_peb.1 * V_tot.1ᴴ) * P_mid := by
    have hConjMul : ∀ (W : Unitary (2 ^ n)) (A B : Operator (2 ^ n)),
        (W.1 * A * W.1ᴴ) * (W.1 * B * W.1ᴴ) = W.1 * (A * B) * W.1ᴴ := fun W A B ↦ by
      have hWU : W.1ᴴ * W.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp W.2
      calc (W.1 * A * W.1ᴴ) * (W.1 * B * W.1ᴴ)
          = W.1 * A * (W.1ᴴ * W.1) * B * W.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = W.1 * (A * B) * W.1ᴴ := by rw [hWU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have hVtot_UpebPsw : V_tot.1 * (U_peb.1 * P_sw_n) =
        (C_18 * U_xorZ).1 * (U_peb.1 * P_sw_n) := by
      rw [← hPHold_UpebPsw, ← Matrix.mul_assoc, hVtot_PHold, Matrix.mul_assoc]
    have hUpeb_unf : U_peb.1 = U_xorZ.1 * U_mid7.1 * U_xorZ.1 := by
      dsimp only [U_peb, uC7_H, uXor_H, U_mid7]
      rw [hUxorZ_AAZH]; simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    have hConjC7 : (C_18 * U_xorZ).1 * U_peb.1 * (C_18 * U_xorZ).1ᴴ =
        C_18.1 * U_mid7.1 * C_18.1ᴴ := by
      rw [Submonoid.coe_mul, Matrix.conjTranspose_mul, hUxorZ_herm, hUpeb_unf]
      calc (C_18.1 * U_xorZ.1) * (U_xorZ.1 * U_mid7.1 * U_xorZ.1) * (U_xorZ.1 * C_18.1ᴴ)
          = C_18.1 * (U_xorZ.1 * U_xorZ.1) * U_mid7.1 * (U_xorZ.1 * U_xorZ.1) *
              C_18.1ᴴ := by simp only [Matrix.mul_assoc]
        _ = C_18.1 * U_mid7.1 * C_18.1ᴴ := by rw [hUxorZ_sq, Matrix.mul_one, Matrix.mul_one]
    rw [← hConjC7, hPmid_eq, hConjMul (C_18 * U_xorZ), ← hVtot_UpebPsw,
        ← Matrix.mul_assoc V_tot.1 U_peb.1 P_sw_n, Matrix.mul_assoc (V_tot.1 * U_peb.1) P_sw_n,
        ← hadj, ← Matrix.mul_assoc (V_tot.1 * U_peb.1) P_sw_n,
        Matrix.mul_assoc V_tot.1 U_peb.1 P_sw_n, ← hConjMul V_tot U_peb.1 P_sw_n, ← hPmid_eq]
  have hMid7PebMid :=
    (Pass1BarrelIdxPebbled273.RealizesOnProj.mono_proj
      hP218W_herm hPmid_herm hP218W_sub_Pmid hMid7PebC18).congr_op hPmid_herm hOpOnPmid
  have hcXorQ_inv : cXorQ.eval = cXorQ.eval⁻¹ :=
    eval_eq_inv_of_classicalPerm_id
      (copyXorRegCircuit_classicalPerm (phcHead_rQRev18 rSubstPos) rZ18 hQDisj)
      (copyXorRegCircuit_classicalPerm (phcHead_rQRev18 rSubstPos) rZ18 hQDisj)
      (fun β ↦ by
        funext z
        by_cases hz : ∃ k : Fin 18, rZ18 k = z
        · obtain ⟨k, rfl⟩ := hz
          have hQNotZ : phcHead_rQRev18 rSubstPos k ∉ Set.range rZ18.wires :=
            fun ⟨j, hj⟩ ↦ hQDisj.ne k j hj.symm
          rw [writeReg_apply_reg, writeReg_apply_reg,
              writeReg_apply_of_not_mem _ _ _ _ hQNotZ,
              add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · rw [writeReg_apply_of_not_mem _ _ _ _ hz,
              writeReg_apply_of_not_mem _ _ _ _ hz])
  have hBodyPeb : PebRealizes
      ((uSymStepFwdList L).1 * P_sw_n * (uSymStepFwdList L).1ᴴ)
      ((uSymStepFwdList L).1 * U_peb.1 * (uSymStepFwdList L).1ᴴ)
      (.seq (.circuit cXorQ) (.seq dMid5Seq (.circuit cXorQ))) := by
    refine Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit
      cXorQ cXorQ hcXorQ_inv ?_
    have hP_assoc :
        cXorQ.eval.1 * ((uSymStepFwdList L).1 * P_sw_n * (uSymStepFwdList L).1ᴴ) *
          cXorQ.eval.1ᴴ = P_mid := by
      dsimp only [P_mid, V_tot]
      simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hU_assoc :
        cXorQ.eval.1 * ((uSymStepFwdList L).1 * U_peb.1 * (uSymStepFwdList L).1ᴴ) *
          cXorQ.eval.1ᴴ = V_tot.1 * U_peb.1 * V_tot.1ᴴ := by
      dsimp only [V_tot]
      simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rwa [hP_assoc, hU_assoc]
  have hvL := (zTargetSteps36_valid_and_eval (le_refl 36) rSubstPos rHold36 hSubPHold
    ∅ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)).1
  have hTailPsw :
      Pass1BarrelIdxPebbled273.HasCleanTailFrom rHold36 0 P_sw_n :=
    fun q _ ↦ by
      rw [← hPHold_Psw, ← Matrix.mul_assoc, singleton_proj0_mul_reg_proj0 rHold36 q, hPHold_Psw]
  have hTailUpeb :
      Pass1BarrelIdxPebbled273.HasCleanTailFrom
        rHold36 0 (U_peb.1 * P_sw_n) :=
    fun q _ ↦ by
      rw [← hPHold_UpebPsw, ← Matrix.mul_assoc,
          singleton_proj0_mul_reg_proj0 rHold36 q, hPHold_UpebPsw]
  have hPebWrap := realizesOnProj_symWrapDynList v rHold36 0 L hvL hPsw_n_herm
    hTailPsw hTailUpeb hBodyPeb
  let cSw := cSwapCore3967.onRegister rCore
  have hcSw_eval : cSw.eval = rAAZH.embedUnitary uSw_H := by
    dsimp only [cSw]
    rw [Circuit.eval_onRegister, ← uSwapCore3967_eq_eval, ← hSwCore]
  have hcSw_sq : cSw.eval * cSw.eval = 1 := by
    rw [hcSw_eval, ← QRegister.embedUnitary_mul, hSwSq_H, QRegister.embedUnitary_one]
  have hcSw_inv : cSw.eval = cSw.eval⁻¹ := eq_inv_of_mul_eq_one_left hcSw_sq
  have hcSw_herm : cSw.eval.1ᴴ = cSw.eval.1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, ← hcSw_inv]
  have hcSw_comm_PCW : cSw.eval.1 * P_CW = P_CW * cSw.eval.1 := by
    rw [hcSw_eval]; dsimp only [P_CW, PCarry18_0]
    rw [← Matrix.mul_assoc, QRegister.embedUnitary_val,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAAZH) rCarry18 hAAZH_Carry _ 0,
        ← QRegister.embedUnitary_val, Matrix.mul_assoc, hSw_comm_W136, ← Matrix.mul_assoc]
  have hInnerPeb : PebRealizes P_init_n U_C9.1
      (dInnerSwapBell18_ofStrGen spec hm v dStrAdd dStrInv
        rAct rAnchor18 rWork hAA hAW hAnW) := by
    unfold dInnerSwapBell18_ofStrGen
    refine Pass1BarrelIdxPebbled273.RealizesOnProj.withConjCircuit
      cSw cSw hcSw_inv ?_
    have hP_eq : cSw.eval.1 * P_init_n * cSw.eval.1ᴴ = P_sw_n := by
      dsimp only [P_init_n, P_sw_n, P_sw_H]
      rw [hcSw_herm, hSwHerm_H, Matrix.mul_assoc _ _ cSw.eval.1,
          Matrix.mul_assoc _ P_CW cSw.eval.1, ← hcSw_comm_PCW,
          ← Matrix.mul_assoc _ cSw.eval.1 P_CW, ← Matrix.mul_assoc cSw.eval.1,
          hcSw_eval, QRegister.embedUnitary_val, ← rAAZH.embedMatrix_mul,
          ← rAAZH.embedMatrix_mul, ← Matrix.mul_assoc uSw_H.1]
    have hU_eq : cSw.eval.1 * U_C9.1 * cSw.eval.1ᴴ = U_peb.1 := by
      dsimp only [U_C9, U_peb]
      rw [hcSw_herm, hcSw_eval, huC9_eq_sw_uC7, ← Submonoid.coe_mul, ← Submonoid.coe_mul,
          ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
      refine congrArg (fun x ↦ (rAAZH.embedUnitary x).1) ?_
      calc uSw_H * (uSw_H * uC7_H * uSw_H) * uSw_H
          = (uSw_H * uSw_H) * uC7_H * (uSw_H * uSw_H) := by simp only [_root_.mul_assoc]
        _ = uC7_H := by rw [hSwSq_H, one_mul, mul_one]
    rwa [hP_eq, hU_eq]
  -- Step 5: Convert `PebRealizes P_init_n` to `RealizesOnProj` on `E_bell18`
  have hInnerProj := (pebRealizes_iff_realizesOnProj hPinit_n_herm U_C9 _).mp hInnerPeb
  have hEinit_comm_PCW := hCommPCW_of_W136 hEinit_comm_W136
  have hEBellEq :
      E_bell18 (E_raw217 * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA =
        rAAZH.embedMatrix E_init_Bell_AAZH * P_CW := by
    rw [E_bell18_mul_right E_raw217 (spec.pZero)
      rAct rAnchor18 rWork rHeld18 hAA hAW hAH hAnH]
    have hIdleEmbed : rAct.embedMatrix spec.pZero =
        rIdle11.basisOutcomeProjector 0 :=
      embedMatrix_basisOutcomeProjector_zero_assoc rAct spec.rIdle
    have hFEq : rAAZH.embedMatrix (selAAZH_AAZ.embedUnitary F_AAZ).1 =
        rAA.embedMatrix (uBarrelFastAct * uSlot0MeasSwap).1 := by
      rw [F_AAZ_def, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
          ← QRegister.embedMatrix_compose, hAAZH_AAZ,
          ← QRegister.embedMatrix_compose, hAAZ_AA]
    have hBaseEq : rAAZH.embedMatrix E_base_Bell_AAZH =
        rAct.embedMatrix E_raw217 * pEqReg rAnchor18 rHeld18 * PZ18_0 := by
      unfold E_base_Bell_AAZH
      rw [rAAZH.embedMatrix_mul, rAAZH.embedMatrix_mul,
          ← QRegister.embedMatrix_compose, hAAZH_Data,
          embedMatrix_pEqReg, hAAZH_Anc, hAAZH_Held, hPZ_eq_H]
    unfold E_bell18 E_bell18Gen E_init_Bell_AAZH
    have hPHold_split' : (rHold36OfSub18 hm36 rWork).basisOutcomeProjector 0 =
        PZ18_0 * PCarry18_0 := hPHold_split
    dsimp only [P_CW, rAA, rWRest]
    rw [hIdleEmbed, rAAZH.embedMatrix_mul, hFEq, hBaseEq, hPW136_split,
        Matrix.mul_assoc (rAct.embedMatrix E_raw217) (rWork.basisOutcomeProjector 0),
        ← pEqReg_comm_basisOutcomeProjector rAnchor18 rHeld18 rWork 0,
        ← rHold36OfSub18_proj0_mul_rWRestOfSub18_proj0 hm36 rWork, hPHold_split']
    simp only [rAA, rWRest, Matrix.mul_assoc]
  have hAbsorbInit : P_init_n * (rAAZH.embedMatrix E_init_Bell_AAZH * P_CW) =
      E_bell18 (E_raw217 * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA := by
    have hPCW_idem : P_CW * P_CW = P_CW := by
      dsimp only [P_CW, PCarry18_0, PW136]
      rw [Matrix.mul_assoc (rCarry18.basisOutcomeProjector 0),
          ← Matrix.mul_assoc (rW136.basisOutcomeProjector 0),
          (basisOutcomeProjector_comm_part4 rCarry18 rW136 0 0).symm,
          Matrix.mul_assoc _ (rW136.basisOutcomeProjector 0),
          ← Matrix.mul_assoc (rCarry18.basisOutcomeProjector 0) _,
          basisOutcomeProjector_zero_mul_self, basisOutcomeProjector_zero_mul_self]
    rw [hEBellEq]
    dsimp only [P_init_n, P_init_H]
    rw [Matrix.mul_assoc _ P_CW, ← Matrix.mul_assoc P_CW, hEinit_comm_PCW.symm,
        Matrix.mul_assoc _ P_CW P_CW, hPCW_idem, ← Matrix.mul_assoc,
        ← rAAZH.embedMatrix_mul, E_init_Bell_AAZH_mul_conjTranspose_mul_self]
  have hOnInit := realizesOnProj_mul_right (rAAZH.embedMatrix E_init_Bell_AAZH * P_CW) hInnerProj
  rw [hAbsorbInit] at hOnInit
  refine realizesOnProj_congr_unitary ?_ hOnInit
  have hTargetUnit : rAA.embedUnitary (uAnchorFrame uInnerSwapFull) =
      rAAZH.embedUnitary (selAAZH_AA.embedUnitary (uAnchorFrame uInnerSwapFull)) := by
    rw [← QRegister.embedUnitary_compose, hAAZH_AA]
  dsimp only [U_C9]
  rw [hEBellEq, hTargetUnit, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← Matrix.mul_assoc _ _ P_CW, ← Matrix.mul_assoc _ _ P_CW,
      ← rAAZH.embedMatrix_mul, ← rAAZH.embedMatrix_mul,
      uC9_Bell18_AAZH_eq_on_E_init_Bell]


attribute [irreducible] dInnerSwapBell18_ofStrGen

set_option exponentiation.threshold 256
set_option genSizeOf false

/-- Reducible `3`-step open-QFT Bell-18 Stage-A circuit (`155 ≤ mWorkSub18`, `16,533 + tStrPair`
`T`, `0 TOFF`), matching `P1_OpenAnchorAdd0TwoLoad.dStageARawOpenQftBell18_ofStr` without
`@[irreducible]` opacity prior to `dStageARawOpenQftBell18Borrow48093_realizesOnProj_rawStream`. -/
noncomputable def dStageARawOpenQftBell18_ofStrGen {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    DynamicCircuit Var n :=
  have hk38 := spec.hk38
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  let rSubCore := rSubst.compose rCoreFull
  let rSubSum42 := rSubst.compose rSum0
  let rSubPG7 := rSubst.compose rPG7Full
  let hSubCS := disjointWires_compose_of_disjoint rSubst rCoreFull_disj_rSum0
  let hSubCPG := disjointWires_compose_of_disjoint rSubst hCoreFull_disj_rPG7Full
  let hSubSPG := disjointWires_compose_of_disjoint rSubst rSum0_disj_rPG7Full
  let hSubCW := hSubW.compose_left rCoreFull
  let hSubSW := hSubW.compose_left rSum0
  let rSubAct := (rSubCore.concat rSubSum42 hSubCS).concat rSubPG7
    (disjointWires_concat_left hSubCS hSubCPG hSubSPG)
  let rSubCat := rSubAct.compose selCatInCoreSum42PG7
  let hSubCatW : rSubCat.DisjointWires rWork :=
    (disjointWires_concat_left _ (disjointWires_concat_left hSubCS hSubCW hSubSW)
      (hSubW.compose_left rPG7Full)).compose_left selCatInCoreSum42PG7
  let dSub0 := dSubSlot0FromSum42 v rSubCore rSubSum42 rWork hSubCS hSubCW hSubSW (by omega)
  let dQftF := dCanonStage128Fwd activeOneElecExpQftStage128 (by omega : 128 ≤ mWorkSub18)
    v rSubCat rWork hSubCatW
  let dInner := dInnerSwapBell18_ofStrGen spec hm v dStrAdd dStrInv
    rAct rAnchor18 rWork hAA hAW hAnW
  .seq dSub0 (.seq dQftF dInner)

theorem count_dStageARawOpenQftBell18_ofStrGen_toff {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (hToff : ∀ rC rS rW hCS hCW hSW,
      (dStrAdd rC rS rW hCS hCW hSW).count TOFF = 0 ∧
      (dStrInv rC rS rW hCS hCW hSW).count TOFF = 0)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dStageARawOpenQftBell18_ofStrGen spec hm v dStrAdd dStrInv
      rAct rAnchor18 rWork hAA hAW hAnW).count TOFF = 0 := by
  have hk38 := spec.hk38
  let rSub := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  have hCnt := dAddSubSlot0Sum42_counts (Var := Var) v (rSub.compose rCoreFull)
    (rSub.compose rSum0) rWork (disjointWires_compose_of_disjoint rSub rCoreFull_disj_rSum0)
    (hSubW.compose_left rCoreFull) (hSubW.compose_left rSum0) (by omega)
  dsimp only [rSub, hSubW] at hCnt
  dsimp only [dStageARawOpenQftBell18_ofStrGen, DynamicCircuit.count]
  rw [hCnt.2.1, count_dCanonStage128Fwd_toff,
      count_dInnerSwapBell18_ofStrGen_toff spec hm v dStrAdd dStrInv hToff]

theorem count_dStageARawOpenQftBell18_ofStrGen_t_le
    {Var : Type} {kIdle mWorkSub18 n tStrPair : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (hT : ∀ rC rS rW hCS hCW hSW,
      (dStrAdd rC rS rW hCS hCW hSW).count T +
      (dStrInv rC rS rW hCS hCW hSW).count T ≤ tStrPair)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWorkSub18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dStageARawOpenQftBell18_ofStrGen spec hm v dStrAdd dStrInv
      rAct rAnchor18 rWork hAA hAW hAnW).count T ≤ 16533 + tStrPair := by
  have hk38 := spec.hk38
  let rSub := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  have hCnt := dAddSubSlot0Sum42_counts (Var := Var) v (rSub.compose rCoreFull)
    (rSub.compose rSum0) rWork (disjointWires_compose_of_disjoint rSub rCoreFull_disj_rSum0)
    (hSubW.compose_left rCoreFull) (hSubW.compose_left rSum0) (by omega)
  dsimp only [rSub, hSubW] at hCnt
  have hInT := count_dInnerSwapBell18_ofStrGen_t_le spec hm v dStrAdd dStrInv hT
    rAct rAnchor18 rWork hAA hAW hAnW
  dsimp only [dStageARawOpenQftBell18_ofStrGen, DynamicCircuit.count]
  rw [count_dCanonStage128Fwd_t, activeOneElecExpQftStage128_tCost]
  exact (Nat.add_le_add hCnt.2.2.2 (Nat.add_le_add (le_refl _) hInT)).trans (by omega)

/-- `kIdle`-parametric Bell-18 Site-1 open-QFT Stage-A circuit (`166 ≤ mWorkSub18 + kIdle`,
`0 TOFF`), dispatching `dStr{Add,Inv}218_3AxisBorrow_wide` on `((mWorkSub18 - 36) + kIdle)`. -/
noncomputable def dStageARawOpenQftBell18Gen {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    DynamicCircuit Var n :=
  dStageARawOpenQftBell18_ofStrGen spec (by omega) v
    (dStrAddBell18Gen spec hm v rHeld18) (dStrInvBell18Gen spec hm v rHeld18)
    rAct rAnchor18 rWork hAA hAW hAnW

theorem dStageARawOpenQftBell18Gen_count_toff {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dStageARawOpenQftBell18Gen spec hm v rAct rAnchor18 rWork rHeld18
      hAA hAW hAnW).count TOFF = 0 :=
  count_dStageARawOpenQftBell18_ofStrGen_toff spec (by omega) v _ _
    (fun rC rS rWE hCS hCW hSW ↦
      let hc := dStrBell18Gen_counts (Var := Var) spec hm v rHeld18 rC rS rWE hCS hCW hSW
      ⟨hc.1, hc.2.1⟩)
    rAct rAnchor18 rWork hAA hAW hAnW

theorem dStageARawOpenQftBell18Gen_count_t_le {Var : Type} {kIdle mWorkSub18 n : ℕ}
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18)
    (hAW : rAct.DisjointWires rWork) (hAnW : rAnchor18.DisjointWires rWork) :
    (dStageARawOpenQftBell18Gen spec hm v rAct rAnchor18 rWork rHeld18
      hAA hAW hAnW).count T ≤ 48093 := by
  unfold dStageARawOpenQftBell18Gen
  have h := count_dStageARawOpenQftBell18_ofStrGen_t_le
    (tStrPair := 31560) spec (by omega) v
    (dStrAddBell18Gen spec hm v rHeld18) (dStrInvBell18Gen spec hm v rHeld18)
    (fun rC rS rWE hCS hCW hSW ↦
      (dStrBell18Gen_counts (Var := Var) spec hm v rHeld18 rC rS rWE hCS hCW hSW).2.2)
    rAct rAnchor18 rWork hAA hAW hAnW
  omega

set_option maxHeartbeats 6400000 in
-- 3-step open-QFT Bell-18 Stage-A projector realization composition
theorem dStageARawOpenQftBell18_ofStrGen_realizesOnProj_of_step
    {Var : Type} [Fintype Var] [DecidableEq Var] {kIdle mWorkSub18 n : ℕ} [NeZero (qDim n)]
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    {eStr e217 : Operator (qDim kFull80)}
    (hSub0 : (uAddStageAFull⁻¹).1 * eStr = e217)
    (hQft0 : uExpQftStageAFull.1 * e217 = e217 * uExpQftStageAFull.1)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18)
    (s3 : RealizesOnProj
      (E_bell18 (e217 * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary (uAnchorFrame uInnerSwapFull))
      (dInnerSwapBell18_ofStrGen spec hm v dStrAdd dStrInv
        rAct rAnchor18 rWork hAA hAW hAnW)) :
    RealizesOnProj
      (E_bell18 (eStr * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageARawOpenQftBell18_ofStrGen spec hm v dStrAdd dStrInv
        rAct rAnchor18 rWork hAA hAW hAnW) := by
  have hk38 := spec.hk38
  unfold dStageARawOpenQftBell18_ofStrGen
  let rAA := rAct.concat rAnchor18 hAA
  have hAAW : rAA.DisjointWires rWork := disjointWires_concat_left hAA hAW hAnW
  let rSubst := rActAnchorSubst rAct rAnchor18 hAA
  let hSubW := rActAnchorSubst_disj_of_disj hAA hAW hAnW
  let rSubCore := rSubst.compose rCoreFull
  let rSubSum42 := rSubst.compose rSum0
  let rSubPG7 := rSubst.compose rPG7Full
  let hSubCS := disjointWires_compose_of_disjoint rSubst rCoreFull_disj_rSum0
  let hSubCPG := disjointWires_compose_of_disjoint rSubst hCoreFull_disj_rPG7Full
  let hSubSPG := disjointWires_compose_of_disjoint rSubst rSum0_disj_rPG7Full
  let hSubCW := hSubW.compose_left rCoreFull
  let hSubSW := hSubW.compose_left rSum0
  let rSubAct := (rSubCore.concat rSubSum42 hSubCS).concat rSubPG7
    (disjointWires_concat_left hSubCS hSubCPG hSubSPG)
  let rSubCat := rSubAct.compose selCatInCoreSum42PG7
  let hSubCatW : rSubCat.DisjointWires rWork :=
    (disjointWires_concat_left _ (disjointWires_concat_left hSubCS hSubCW hSubSW)
      (hSubW.compose_left rPG7Full)).compose_left selCatInCoreSum42PG7
  have hSubAA : rAA.compose (selSubstSlot0 rSlot0InFull) = rSubst :=
    concat_compose_selSubstSlot0 rSlot0InFull rAct rAnchor18 hAA
  have hSubActEq : rSubst.compose rActStageAFull80 = rSubAct := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun iCS ↦ ?_) (fun mPG ↦ ?_) idx
    · refine Fin.addCases (fun iC ↦ ?_) (fun jS ↦ ?_) iCS
      · simp [rSubAct, rSubCore, rActStageAFull80, rCSFull80, QRegister.concat_apply_left]
      · simp [rSubAct, rSubSum42, rActStageAFull80, rCSFull80,
          QRegister.concat_apply_left, QRegister.concat_apply_right]
    · simp [rSubAct, rSubPG7, rActStageAFull80, QRegister.concat_apply_right]
  have hSubCSComp : rSubst.compose (rActStageAFull80.compose selCoreSum42InAct) =
      rSubCore.concat rSubSum42 hSubCS := by
    rw [← QRegister.compose_assoc, hSubActEq,
        concat_compose_selCoreSum42InAct _ rSubPG7
          (disjointWires_concat_left hSubCS hSubCPG hSubSPG)]
  have hSubCatComp : rSubst.compose (rActStageAFull80.compose selCatInCoreSum42PG7) =
      rSubCat := by
    rw [← QRegister.compose_assoc, hSubActEq]
  let UQ0 := uExpQftStageAFull
  have hSubstUnit : ∀ (U : Unitary (2 ^ kFull80)),
      uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary U * uSlot0MeasSwap =
        uAnchorFrame U →
      rSubst.embedUnitary U = rAA.embedUnitary (uAnchorFrame U) := fun U hFrame ↦ by
    rw [← hSubAA, QRegister.embedUnitary_compose]
    refine congrArg rAA.embedUnitary ?_
    rw [← hFrame]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull U.1)
  have hPair0 := dAddSubSlot0Sum42_realizesPair v rSubCore rSubSum42 rWork
    hSubCS hSubCW hSubSW (by omega)
  have hSubClean := widenActive_inv_of_compose_eq_assoc hSubCSComp hPair0.inv
  have hUAddInvEq :
      ((rActStageAFull80.compose selCoreSum42InAct).embedUnitary (uSlot0Sum42Add 80))⁻¹ =
        uAddStageAFull⁻¹ := by
    dsimp only [uAddStageAFull]; rw [QRegister.embedUnitary_compose]
  rw [hUAddInvEq] at hSubClean
  have hQftFClean := widenActive_of_compose_eq_assoc hSubCatComp
    (dCanonStage128Fwd_realizes activeOneElecExpQftStage128 (by omega : 128 ≤ mWorkSub18)
      v rSubCat rWork hSubCatW)
  rw [QRegister.embedUnitary_compose] at hQftFClean
  have s1 := realizesOnProj_of_clean_proj0 hSubW hSubClean
  rw [hSubstUnit uAddStageAFull⁻¹ uSlot0MeasSwap_conj_uSlot0Sum42Add_eq.2] at s1
  have s2 := realizesOnProj_of_clean_proj0 hSubW hQftFClean
  rw [hSubstUnit UQ0 uSlot0MeasSwap_conj_activeOneElecExpQft_eq.1] at s2
  have hLiftBell : ∀ (M : Operator (2 ^ kFull80)) (U : Unitary (2 ^ (kFull80 + 18)))
      (d : DynamicCircuit Var n),
      RealizesOnProj (rWork.basisOutcomeProjector 0) (rAA.embedUnitary U) d →
      RealizesOnProj (E_bell18 M rAct rAnchor18 rWork rHeld18 hAA) (rAA.embedUnitary U) d :=
    fun M U d hd ↦ by
      have hComm1 := mul_comm_op
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAA) rWork hAAW
          (uBarrelFastAct * uSlot0MeasSwap).1 0)
        ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hAW M 0)
      have hL := realizesOnProj_mul_right
        ((rAA.embedMatrix (uBarrelFastAct * uSlot0MeasSwap).1 * rAct.embedMatrix M) *
          pEqReg rAnchor18 rHeld18) hd
      have hEqE : rWork.basisOutcomeProjector 0 *
          ((rAA.embedMatrix (uBarrelFastAct * uSlot0MeasSwap).1 * rAct.embedMatrix M) *
            pEqReg rAnchor18 rHeld18) =
          E_bell18 M rAct rAnchor18 rWork rHeld18 hAA := by
        rw [← Matrix.mul_assoc, ← hComm1]
        dsimp only [rAA]
        unfold E_bell18 E_bell18Gen
        simp only [Matrix.mul_assoc]
      rwa [hEqE] at hL
  let PIdle := spec.pZero
  have s1_218 := hLiftBell (eStr * PIdle) (uAnchorFrame uAddStageAFull⁻¹) _ s1
  have s2_217 := hLiftBell (e217 * PIdle) (uAnchorFrame UQ0) _ s2
  have hAddStep : (uAddStageAFull⁻¹).1 * (eStr * PIdle) =
      (e217 * PIdle) * 1 := by
    rw [Matrix.mul_one, ← Matrix.mul_assoc, hSub0]
  have hTrans1 := uAnchorFrame_step_E_bell18 hAddStep
    rAct rAnchor18 rWork rHeld18 hAA hAW hAH hAnH
  have hQftStep : UQ0.1 * (e217 * PIdle) = (e217 * PIdle) * UQ0.1 := by
    have hIdleComm : UQ0.1 * PIdle = PIdle * UQ0.1 := by
      dsimp only [UQ0, uExpQftStageAFull, PIdle, IdleAnchorSpec.pZero]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rActStageAFull80)
        spec.rIdle spec.hActStageA _ 0
    rw [← Matrix.mul_assoc, hQft0, Matrix.mul_assoc, hIdleComm, ← Matrix.mul_assoc]
  have hTrans2 := uAnchorFrame_step_E_bell18 hQftStep
    rAct rAnchor18 rWork rHeld18 hAA hAW hAH hAnH
  have s23 := realizesOnProj_seq_part4 hTrans2 s2_217 s3
  have s123 := realizesOnProj_seq_part4 hTrans1 s1_218 s23
  refine realizesOnProj_congr_unitary ?_ s123
  have h7Step : uAddStageAFull * (UQ0⁻¹ * (uInnerSwapFull * UQ0) * uAddStageAFull⁻¹) =
      uStageARawFull := by
    rw [uInnerSwapFull_def]
    dsimp only [uAddStageAFull, UQ0, uExpQftStageAFull, uStageARawFull,
      uStageA7StepCat, uStageA5StepCat]
    simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv, _root_.mul_assoc]
  have h3Step : (uInnerSwapFull * UQ0) * uAddStageAFull⁻¹ =
      uJunctionRawFull⁻¹ * uStageARawFull := by
    have hJunctionInv : uJunctionRawFull⁻¹ = UQ0 * uAddStageAFull⁻¹ := by
      apply inv_eq_of_mul_eq_one_left
      dsimp only [UQ0, uJunctionRawFull]
      rw [_root_.mul_assoc uExpQftStageAFull, ← _root_.mul_assoc uAddStageAFull⁻¹,
          inv_mul_cancel, one_mul, mul_inv_cancel]
    rw [hJunctionInv, ← h7Step, _root_.mul_assoc UQ0 uAddStageAFull⁻¹,
        ← _root_.mul_assoc uAddStageAFull⁻¹ uAddStageAFull, inv_mul_cancel, one_mul,
        ← _root_.mul_assoc UQ0 (UQ0⁻¹ * (uInnerSwapFull * UQ0)),
        ← _root_.mul_assoc UQ0 UQ0⁻¹, mul_inv_cancel, one_mul]
  have hFrameProd :
      (rAA.embedUnitary (uAnchorFrame uInnerSwapFull) *
        rAA.embedUnitary (uAnchorFrame UQ0)) *
        rAA.embedUnitary (uAnchorFrame uAddStageAFull⁻¹) =
      rAA.embedUnitary (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)) := by
    simp only [← QRegister.embedUnitary_mul, uAnchorFrame_mul, ← h3Step]
  rw [hFrameProd]

theorem dStageARawOpenQftBell18_ofStrGen_realizesOnProj_rawStream
    {Var : Type} [Fintype Var] [DecidableEq Var] {kIdle mWorkSub18 n : ℕ} [NeZero (qDim n)]
    (spec : IdleAnchorSpec kIdle) (hm : 166 ≤ mWorkSub18 + kIdle) (v : Var)
    (dStrAdd dStrInv : StrCallbackGen Var kIdle mWorkSub18 n)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18)
    (hStr : ∀ (rC : QRegister (fullSysCoreWires 80) n) (rS : QRegister 42 n)
      (rWE : QRegister ((mWorkSub18 - 36) + kIdle) n)
      (hCS : rC.DisjointWires rS) (hCW : rC.DisjointWires rWE)
      (hSW : rS.DisjointWires rWE),
      rC.DisjointWires rHeld18 →
      ∀ (hSH : rS.DisjointWires rHeld18),
      rWE.DisjointWires rHeld18 →
      StrPairRealizesBell18 dStrAdd dStrInv rHeld18 rC rS rWE hCS hCW hSW hSH) :
    RealizesOnProj
      (E_bell18 (E_rawStream42 * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageARawOpenQftBell18_ofStrGen spec hm v dStrAdd dStrInv
        rAct rAnchor18 rWork hAA hAW hAnW) :=
  dStageARawOpenQftBell18_ofStrGen_realizesOnProj_of_step spec hm v dStrAdd dStrInv
    uSlot0Sum42Full_inv_mul_E_rawStream42.1 uExpQft0Full_comm_E_raw217
    rAct rAnchor18 rWork rHeld18 hAA hAW hAnW hAH hAnH
    (dInnerSwapAnchor_bell18_realizesOnProj_ofStrGen spec hm v dStrAdd dStrInv
      rAct rAnchor18 rWork rHeld18 hAA hAW hAnW hAH hAnH hWH hStr)

theorem dStageARawOpenQftBell18Gen_realizesOnProj_rawStream
    {Var : Type} [Fintype Var] [DecidableEq Var] {kIdle mWorkSub18 n : ℕ} [NeZero (2 ^ n)]
    (spec : IdleAnchorSpec kIdle) (hm : 172 ≤ mWorkSub18 + kIdle) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18) :
    RealizesOnProj
      (E_bell18 (E_rawStream42 * spec.pZero) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageARawOpenQftBell18Gen spec hm v rAct rAnchor18 rWork rHeld18
        hAA hAW hAnW) :=
  dStageARawOpenQftBell18_ofStrGen_realizesOnProj_rawStream spec (by omega) v _ _
    rAct rAnchor18 rWork rHeld18 hAA hAW hAnW hAH hAnH hWH
    (dStrBell18Gen_strPairRealizes spec hm v rHeld18)

theorem realizesOnProj_ctrl_of_rawStream11
    {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ} [NeZero (qDim n)]
    {rAct : QRegister kFull80 n} {rAn : QRegister 18 n} {rW : QRegister mW n} {rH : QRegister 18 n}
    {hAA : rAct.DisjointWires rAn} (hAW : rAct.DisjointWires rW)
    (hAH : rAct.DisjointWires rH) (hAnH : rAn.DisjointWires rH)
    {u : Unitary (qDim n)} {d : DynamicCircuit Var n}
    (hRaw : RealizesOnProj (E_bell18 (E_rawStream42 * idleSpec11.pZero) rAct rAn rW rH hAA) u d) :
    RealizesOnProj (E_bell18 (E_rawCtrl3Ext 11 (by decide)) rAct rAn rW rH hAA) u d := by
  change RealizesOnProj
    (E_bell18 (E_rawStream42 * (pCtrl3Zero * pPGIdleZero 11 (by decide))) rAct rAn rW rH hAA) u d
  have hComm : pCtrl3Zero * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * pCtrl3Zero :=
    basisOutcomeProjector_comm_part4 rUnusedCtrl3Full (rPGIdle 11 (by decide)) 0 0
  rw [hComm, ← Matrix.mul_assoc,
      E_bell18_mul_right (E_rawStream42 * pPGIdleZero 11 (by decide)) pCtrl3Zero
        rAct rAn rW rH hAA hAW hAH hAnH]
  exact realizesOnProj_mul_right _ hRaw

theorem realizesOnProj_cat_of_rawStream11
    {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ} [NeZero (qDim n)]
    {rAct : QRegister kFull80 n} {rAn : QRegister 18 n} {rW : QRegister mW n} {rH : QRegister 18 n}
    {hAA : rAct.DisjointWires rAn} (hAW : rAct.DisjointWires rW)
    (hAH : rAct.DisjointWires rH) (hAnH : rAn.DisjointWires rH)
    {u : Unitary (qDim n)} {d : DynamicCircuit Var n}
    (hRaw : RealizesOnProj (E_bell18 (E_rawStream42 * idleSpec11.pZero) rAct rAn rW rH hAA) u d) :
    RealizesOnProj (E_bell18 (E_rawSegExt 11 (by decide)) rAct rAn rW rH hAA) u d := by
  change RealizesOnProj
    (E_bell18 (E_rawStream42 * pExt6IdleZero 11 (by decide)) rAct rAn rW rH hAA) u d
  have hComm : pExt6Zero * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * pExt6Zero :=
    basisOutcomeProjector_comm_part4 rExt6Full (rPGIdle 11 (by decide)) 0 0
  rw [pExt6IdleZero_eq_mul, hComm, ← Matrix.mul_assoc,
      E_bell18_mul_right (E_rawStream42 * pPGIdleZero 11 (by decide)) pExt6Zero
        rAct rAn rW rH hAA hAW hAH hAnH]
  exact realizesOnProj_mul_right _ hRaw

theorem realizesOnProj_gen_of_bell18
    {Var : Type} [Fintype Var] [DecidableEq Var] {mWorkSub18 n : ℕ} [NeZero (qDim n)]
    {eExt : Operator (qDim kFull80)}
    {rAct : QRegister kFull80 n} {rAnchor18 : QRegister 18 n}
    {rWork : QRegister mWorkSub18 n} {rHeld18 : QRegister 18 n}
    {hAA : rAct.DisjointWires rAnchor18} {G_bell : Operator (qDim n)}
    (hAbs : pEqReg rAnchor18 rHeld18 * G_bell = G_bell)
    {u : Unitary (qDim n)} {d : DynamicCircuit Var n}
    (h0 : RealizesOnProj (E_bell18 eExt rAct rAnchor18 rWork rHeld18 hAA) u d) :
    RealizesOnProj (E_bell18Gen eExt rAct rAnchor18 rWork hAA G_bell) u d := by
  have h1 := realizesOnProj_mul_right G_bell h0
  have hEq : E_bell18 eExt rAct rAnchor18 rWork rHeld18 hAA * G_bell =
      E_bell18Gen eExt rAct rAnchor18 rWork hAA G_bell := by
    unfold E_bell18 E_bell18Gen
    simp only [Matrix.mul_assoc, hAbs]
  rwa [hEq] at h1

attribute [irreducible] dStageARawOpenQftBell18Gen dStageARawOpenQftBell18_ofStrGen
end Part4_Bell18StageA48093


end Bell18StageABridge

end Bell18StageAAAZ

end QuantumComputation.Specs.StoppingPowerSolution
end

public section

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Bell18StageAWitness

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256
set_option genSizeOf false

namespace Bell18StageABridge

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instNeZero_B18W (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast_B18W (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFast_B18W (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

open PrimitiveGate (T TOFF)
open InterWalkRSum42Hoist (kFull80)
open HoistBorrow42ProjBridge (RealizesOnProj)
open HeldStreamFoldedPass123Bridge
  (E_rawCtrl3Ext E_rawSegExt)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (uAnchorFrame)
open StageAConjHAndStreamBridge
  (uStageARawFull)
open Bell18StageABridgeJunction (uJunctionRawFull)

/-- Packaged Bell-18 Site-1 open-QFT Stage-A witness (`48,093 T` standalone, `47,929 T` fused,
`0 TOFF`), consumed by `_ofStageA` endpoint roots. -/
structure StageABell18Witness where
  dStageA : {Var : Type} → {mWorkSub18 n : ℕ} → 161 ≤ mWorkSub18 → Var →
    (rAct : QRegister kFull80 n) → (rAnchor18 : QRegister 18 n) →
    (rWork : QRegister mWorkSub18 n) → (rHeld18 : QRegister 18 n) →
    rAct.DisjointWires rAnchor18 → rAct.DisjointWires rWork →
    rAnchor18.DisjointWires rWork → DynamicCircuit Var n
  count_toff : ∀ {Var : Type} {mWorkSub18 n : ℕ} (hm161 : 161 ≤ mWorkSub18) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork),
    (dStageA hm161 v rAct rAnchor18 rWork rHeld18 hAA hAW hAnW).count TOFF = 0
  count_t_le : ∀ {Var : Type} {mWorkSub18 n : ℕ} (hm161 : 161 ≤ mWorkSub18) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork),
    (dStageA hm161 v rAct rAnchor18 rWork rHeld18 hAA hAW hAnW).count T ≤ 48093
  realizesOnProj_ctrl : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWorkSub18 n : ℕ} [NeZero (2 ^ n)] (hm161 : 161 ≤ mWorkSub18) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18),
    RealizesOnProj
      (E_bell18 (E_rawCtrl3Ext 11 (by decide)) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageA hm161 v rAct rAnchor18 rWork rHeld18 hAA hAW hAnW)
  realizesOnProj_cat : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWorkSub18 n : ℕ} [NeZero (2 ^ n)] (hm161 : 161 ≤ mWorkSub18) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18),
    RealizesOnProj
      (E_bell18 (E_rawSegExt 11 (by decide)) rAct rAnchor18 rWork rHeld18 hAA)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageA hm161 v rAct rAnchor18 rWork rHeld18 hAA hAW hAnW)
  realizesOnProj_ctrl_gen : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWorkSub18 n : ℕ} [NeZero (2 ^ n)] (hm161 : 161 ≤ mWorkSub18) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18)
    {G_bell : Operator (2 ^ n)},
    pEqReg rAnchor18 rHeld18 * G_bell = G_bell →
    RealizesOnProj
      (E_bell18Gen (E_rawCtrl3Ext 11 (by decide)) rAct rAnchor18 rWork hAA G_bell)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageA hm161 v rAct rAnchor18 rWork rHeld18 hAA hAW hAnW)
  realizesOnProj_cat_gen : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWorkSub18 n : ℕ} [NeZero (2 ^ n)] (hm161 : 161 ≤ mWorkSub18) (v : Var)
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mWorkSub18 n) (rHeld18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) (hAW : rAct.DisjointWires rWork)
    (hAnW : rAnchor18.DisjointWires rWork) (hAH : rAct.DisjointWires rHeld18)
    (hAnH : rAnchor18.DisjointWires rHeld18) (hWH : rWork.DisjointWires rHeld18)
    {G_bell : Operator (2 ^ n)},
    pEqReg rAnchor18 rHeld18 * G_bell = G_bell →
    RealizesOnProj
      (E_bell18Gen (E_rawSegExt 11 (by decide)) rAct rAnchor18 rWork hAA G_bell)
      ((rAct.concat rAnchor18 hAA).embedUnitary
        (uAnchorFrame (uJunctionRawFull⁻¹ * uStageARawFull)))
      (dStageA hm161 v rAct rAnchor18 rWork rHeld18 hAA hAW hAnW)

/-- Canonical `48,093`-`T` (`47,929`-`T` fused, `0 TOFF`) Bell-18 Site-1 Stage-A witness. -/
noncomputable def stageABell18Witness : StageABell18Witness where
  dStageA _ v rA rAn rW rH hAA hAW hAnW :=
    dStageARawOpenQftBell18Gen idleSpec11 (by omega) v rA rAn rW rH hAA hAW hAnW
  count_toff _ v rA rAn rW rH hAA hAW hAnW :=
    dStageARawOpenQftBell18Gen_count_toff idleSpec11 (by omega) v rA rAn rW rH hAA hAW hAnW
  count_t_le _ v rA rAn rW rH hAA hAW hAnW :=
    dStageARawOpenQftBell18Gen_count_t_le idleSpec11 (by omega) v rA rAn rW rH hAA hAW hAnW
  realizesOnProj_ctrl _ v rA rAn rW rH hAA hAW hAnW hAH hAnH hWH :=
    realizesOnProj_ctrl_of_rawStream11 hAW hAH hAnH
      (dStageARawOpenQftBell18Gen_realizesOnProj_rawStream idleSpec11 (by omega) v
        rA rAn rW rH hAA hAW hAnW hAH hAnH hWH)
  realizesOnProj_cat _ v rA rAn rW rH hAA hAW hAnW hAH hAnH hWH :=
    realizesOnProj_cat_of_rawStream11 hAW hAH hAnH
      (dStageARawOpenQftBell18Gen_realizesOnProj_rawStream idleSpec11 (by omega) v
        rA rAn rW rH hAA hAW hAnW hAH hAnH hWH)
  realizesOnProj_ctrl_gen _ v rA rAn rW rH hAA hAW hAnW hAH hAnH hWH := fun hAbs ↦
    realizesOnProj_gen_of_bell18 hAbs (realizesOnProj_ctrl_of_rawStream11 hAW hAH hAnH
      (dStageARawOpenQftBell18Gen_realizesOnProj_rawStream idleSpec11 (by omega) v
        rA rAn rW rH hAA hAW hAnW hAH hAnH hWH))
  realizesOnProj_cat_gen _ v rA rAn rW rH hAA hAW hAnW hAH hAnH hWH := fun hAbs ↦
    realizesOnProj_gen_of_bell18 hAbs (realizesOnProj_cat_of_rawStream11 hAW hAH hAnH
      (dStageARawOpenQftBell18Gen_realizesOnProj_rawStream idleSpec11 (by omega) v
        rA rAn rW rH hAA hAW hAnW hAH hAnH hWH))

end Bell18StageABridge

end Bell18StageAWitness

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
end
