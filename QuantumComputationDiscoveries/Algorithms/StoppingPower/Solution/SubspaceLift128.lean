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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FusedVepSlot2Kick


@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosPostPrep80FastSubblocks
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80FastSubblocks (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Zero-`TOFF` Fast Subblocks for `80`-Wire Post-Hadamard Preparation (`PosPostPrep80FastSubblocks`)

Standalone, cone-minimal zero-`.TOFF` dynamic and static subblocks for `PosPostPrep80FastCircuit`,
importing only `PhaseGradCatalystCore`, `MeasureBranchHadamardSem`, `ZeroAncillaUSP`, and
`PosPostPrep80MergedVep`:

1. **`SubLift128`, `subDiagProj`, & `SubDynPair128` Clean-Subspace Lowering**:
   Reducible `SubLift128` and `subDiagProj` unifying definitionally with `diagProj (Lift128 ...)`,
   plus paired forward/inverse clean-subspace combinators (`static`, `seq`, `withCliff`,
   `withTempAnd`, `withUnaryFork`, `ccnotClean`).
2. **Word-Parametric 3-Level `tailDp8` (`cTailDp8Pm_128`, `dTailDp8FastFwd`, `dTailDp8FastInv`)**:
   Uses `ZeroAncillaUSP.cPmSplit` + `3` dynamic `TempAnd` unary forks on `scr30_128[0..4)` with
   parity wire `scr30_128 4`, controlled by `wEnTail_128` and writing `rB1_128` (`rB1_128 2` MSB,
   `rB1_128 1`, `rB1_128 0` LSB), with `[Fintype Var]`-free `count_TOFF = 0`,
   `count_T ≤ 2 * (dpL0 + dpL1 + dpL2) + 12`, `PreservesStoreConst`, `RealizesCleanUnitary` on
   `subDiagProj (SubLift128 rFull128 rExtra9 S)`, and exact `ket` theorems
   `cTailDp8Pm_mulVec_ket_zero` and `cTailDp8Pm_mulVec_ket_one`.
3. **Dynamic `dFinishXorFastFwd` / `dFinishXorFastInv`**:
   6 sequential `TempAnd + cnotIf` scopes on `scr30_128 0` (`count_TOFF = 0`, `count_T ≤ 24`,
   `PreservesStoreConst`) realizing `(cFinishXor_128 true).eval` and its inverse on
   `subDiagProj (SubLift128 rFull128 rExtra9 S)`.
4. **Staged `unHadamard` Circuits & `ket_chIf_xor_split`**:
   Exports `listP42_128` (`42` payload wires), `cStagedH42_128` (`≤ 84 T`), `cH30Head_128`
   (`≤ 60 T`), `cH3SmTail_128` (`≤ 6 T`), `cHB0Xor_128` (`≤ 6 T`), `ket_chIf_xor_split`, and
   `cHB0Xor_mulVec_ket`.
-/

public section

namespace PosPostPrep80FastSubblocks

section ConfigPosPostPrep80FastSubblocks

set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open HermitianMat (conj_conj)
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open MeasureBranchHadamardSem
  (RealizesCleanUnitary eval_seq_mulVec ket ket_CNOT ket_TOFF
   ket_projector_zero matrix_ext_ket toffoli_eval_sq)
open StreamingBchComparator (PreservesStoreConst)
open ZeroAncillaUSP (andComputeIf cnotIf ket_andCompute_of_zero)
open PosPostPrep80MergedVep
  (chCircuit_mulVec_ket_ctrl_one chCircuit_mulVec_ket_ctrl_zero chIf
   ket_eq_single_local unHadamardList)

/-! ## Section 1: `SubLift128`, `subDiagProj`, and `SubDynPair128` Clean-Subspace Lowering -/

theorem ite_pos_sub {α : Sort _} {P : Prop} {inst : Decidable P} {a b : α} (h : P) :
    @ite α P inst a b = a := match inst with | isTrue _ => rfl | isFalse hn => absurd h hn

theorem ite_neg_sub {α : Sort _} {P : Prop} {inst : Decidable P} {a b : α} (h : ¬P) :
    @ite α P inst a b = b := match inst with | isTrue hp => absurd hp h | isFalse _ => rfl

theorem dite_neg_sub {α : Sort _} {P : Prop} {inst : Decidable P} {a : P → α} {b : ¬P → α}
    (h : ¬P) : @dite α P inst a b = b h :=
  match inst with | isTrue hp => absurd hp h | isFalse _ => rfl

theorem qreg_ext_sub {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)

theorem mul_mulVec_sub {M : ℕ} (A B : Matrix (Fin M) (Fin M) ℂ) (v : Fin M → ℂ) :
    (A * B).mulVec v = A.mulVec (B.mulVec v) := (Matrix.mulVec_mulVec v A B).symm

theorem diagonal_mulVec_ket_sub {N : ℕ} (f : Fin (2 ^ N) → ℂ) (β : BitAssignment N) :
    (Matrix.diagonal f).mulVec (ket β) = f ((basisBitsEquiv N).symm β) • ket β := by
  ext y
  simp [ket_eq_single_local, Pi.single_apply]

/-- Local basis index extracted from `β` along `r`. -/
noncomputable abbrev localIdxSub {k n : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin
    (2 ^ k) := (basisBitsEquiv k).symm (fun i ↦ β (r i))

theorem embedMatrix_mulVec_ket_sub {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdxSub r β) •
        ket (ZeroAncillaUSP.writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBitsEquiv n).symm β) = localIdxSub r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 :=
    funext fun x ↦ by simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [ZeroAncillaUSP.writeReg, ket, basisState]

theorem ket_localIdxSub_eq {k n : ℕ} (r : QRegister k n) (β : BitAssignment n)
    (l : Fin (2 ^ k)) (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    M.mulVec (ket (fun i ↦ β (r i))) l = M l (localIdxSub r β) := by
  rw [ket_eq_single_local, Matrix.mulVec_single_one]
  rfl

theorem mulVec_eq_sum_ket_sub {k : ℕ} (ψ : Fin (2 ^ k) → ℂ) :
    ψ = ∑ x : Fin (2 ^ k), ψ x • ket (basisBits k x) := by
  funext y
  simp [Finset.sum_apply, ket_eq_single_local, (basisBitsEquiv k).symm_apply_apply,
    Pi.single_apply]

/-- Linear span of computational basis states `ket β` satisfying `P β`. -/
noncomputable def KetSpanSub {n : ℕ} (P : BitAssignment n → Prop) :
    Submodule ℂ (Fin (2 ^ n) → ℂ) :=
  Submodule.span ℂ { ψ | ∃ β : BitAssignment n, P β ∧ ψ = ket β }

/-- Static circuit `c` maps every basis state `ket β` satisfying `P β` into `KetSpanSub Q`. -/
def PreservesSpanSub {n : ℕ} (P Q : BitAssignment n → Prop) (c : Circuit n) : Prop :=
  ∀ β : BitAssignment n, P β → c.eval.1.mulVec (ket β) ∈ KetSpanSub Q

/-- Predicate `P` is invariant under arbitrary updates to wire `w`. -/
def WireIndepSub {n : ℕ} (P : BitAssignment n → Prop) (w : Wire n) : Prop :=
  ∀ (β : BitAssignment n) (b : ZMod 2), P β → P (Function.update β w b)

theorem ket_mem_ketSpanSub {n : ℕ} {P : BitAssignment n → Prop} {β : BitAssignment n}
    (h : P β) : ket β ∈ KetSpanSub P := Submodule.subset_span ⟨β, h, rfl⟩

theorem preservesSpanSub_id {n : ℕ} {P : BitAssignment n → Prop} :
    PreservesSpanSub P P (Circuit.identity : Circuit n) := fun β hβ ↦ by
  simpa [Circuit.eval_identity] using ket_mem_ketSpanSub hβ

theorem preservesSpanSub_singleton_matrix {n : ℕ} {P : BitAssignment n → Prop} (q : Wire n)
    (hq : WireIndepSub P q) (M : Matrix (Fin 2) (Fin 2) ℂ) (β : BitAssignment n) (hβ : P β) :
    ((QRegister.singleton q).embedMatrix M).mulVec (ket β) ∈ KetSpanSub P := by
  rw [ZeroAncillaUSP.singleton_embedMatrix_mulVec_ket]
  have hm (a b : ℂ) := (KetSpanSub P).add_mem
    ((KetSpanSub P).smul_mem a (ket_mem_ketSpanSub (hq β 0 hβ)))
    ((KetSpanSub P).smul_mem b (ket_mem_ketSpanSub (hq β 1 hβ)))
  split_ifs
  · exact hm _ _
  · exact hm _ _

theorem preservesSpanSub_cnotIf {n : ℕ} {P : BitAssignment n → Prop}
    (c t : Wire n) (ht : WireIndepSub P t) :
    PreservesSpanSub P P (cnotIf c t) := fun β hβ ↦ by
  unfold cnotIf
  split_ifs with hct
  · exact preservesSpanSub_id β hβ
  · rw [ket_CNOT]
    exact ket_mem_ketSpanSub (ht β _ hβ)

theorem inv_mulVec_ket_of_fwd_sub {n : ℕ} (c : Circuit n) (β₀ β₁ : BitAssignment n)
    (hFwd : c.eval.1.mulVec (ket β₀) = ket β₁) :
    c.inverse.eval.1.mulVec (ket β₁) = ket β₀ := by
  rw [← hFwd, Circuit.eval_inverse, Matrix.mulVec_mulVec,
    show (c.eval⁻¹).1 * c.eval.1 = 1 from congrArg Subtype.val (inv_mul_cancel c.eval),
    Matrix.one_mulVec]

theorem unitary_mul_assoc_sub {M : ℕ} (A B C : Unitary M) : A * B * C = A * (B * C) :=
  mul_assoc A B C

theorem unitary_mul_inv_rev_sub {M : ℕ} (A B : Unitary M) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  _root_.mul_inv_rev A B

open Classical in
/-- Orthogonal diagonal projector onto computational basis states satisfying `S`. -/
noncomputable abbrev subDiagProj {N : ℕ} (S : BitAssignment N → Prop) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ :=
  Matrix.diagonal (fun x ↦ if S (basisBits N x) then (1 : ℂ) else 0)

/-- Global `n`-qubit lift of a `128`-wire predicate `S` with clean `9`-wire `rExtra9 = 0`. -/
abbrev SubLift128 {n : ℕ} (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (S : BitAssignment 128 → Prop) (β : BitAssignment n) : Prop :=
  S (fun i ↦ β (rFull128 i)) ∧ ∀ j : Fin 9, β (rExtra9 j) = 0

open Classical in
theorem subDiagProj_conjTranspose {N : ℕ} (S : BitAssignment N → Prop) :
    (subDiagProj S)ᴴ = subDiagProj S :=
  (Matrix.diagonal_conjTranspose _).trans (congrArg Matrix.diagonal
    (funext fun x ↦ if h : S (basisBits N x) then by simp [h] else by simp [h]))

open Classical in
theorem subDiagProj_mul_self {N : ℕ} (S : BitAssignment N → Prop) :
    subDiagProj S * subDiagProj S = subDiagProj S :=
  (Matrix.diagonal_mul_diagonal _ _).trans (congrArg Matrix.diagonal
    (funext fun x ↦ if h : S (basisBits N x) then by simp [h] else by simp [h]))

open Classical in
theorem subDiagProj_mulVec_ket {N : ℕ} (S : BitAssignment N → Prop) (β : BitAssignment N) :
    (subDiagProj S).mulVec (ket β) = if S β then ket β else 0 := by
  rw [subDiagProj, diagonal_mulVec_ket_sub, (basisBitsEquiv N).apply_symm_apply]
  exact if h : S β then by simp [h] else by simp [h]

open Classical in
theorem subDiagProj_mulVec_apply {N : ℕ} (S : BitAssignment N → Prop)
    (ψ : Fin (2 ^ N) → ℂ) (x : Fin (2 ^ N)) :
    (subDiagProj S).mulVec ψ x = if S (basisBits N x) then ψ x else 0 := by
  rw [subDiagProj, Matrix.mulVec_diagonal]
  exact if h : S (basisBits N x) then by simp [h] else by simp [h]

open Classical in
theorem mem_of_subDiagProj_mulVec_eq {N : ℕ} {S : BitAssignment N → Prop}
    {ψ : Fin (2 ^ N) → ℂ} {x : Fin (2 ^ N)} (hpres : (subDiagProj S).mulVec ψ x = ψ x)
    (hnz : ψ x ≠ 0) : S (basisBits N x) := by
  rw [subDiagProj_mulVec_apply] at hpres
  by_contra hns
  simp only [hns, ↓reduceIte] at hpres
  exact hnz hpres.symm

open Classical in
theorem subDiagProj_mulVec_of_mem_ketSpanSub {N : ℕ} {S : BitAssignment N → Prop}
    {ψ : Fin (2 ^ N) → ℂ} (hψ : ψ ∈ KetSpanSub S) : (subDiagProj S).mulVec ψ = ψ := by
  induction hψ using Submodule.span_induction with
  | mem _ hx =>
      rcases hx with ⟨γ, hγ, rfl⟩
      rw [subDiagProj_mulVec_ket, ite_pos_sub hγ]
  | zero => exact Matrix.mulVec_zero _
  | add _ _ _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy]
  | smul _ _ _ ihx => rw [Matrix.mulVec_smul, ihx]

open Classical in
theorem subDiagProj_mul_of_preservesSpanSub {N : ℕ} {S₁ S₂ : BitAssignment N → Prop}
    {c : Circuit N} (hc : PreservesSpanSub S₁ S₂ c) :
    subDiagProj S₂ * (c.eval.1 * subDiagProj S₁) = c.eval.1 * subDiagProj S₁ :=
  matrix_ext_ket fun β ↦ by
    simp only [mul_mulVec_sub, subDiagProj_mulVec_ket]
    exact if h : S₁ β then by
      simpa [h] using subDiagProj_mulVec_of_mem_ketSpanSub (hc β h)
    else by simp [h]

private theorem proj_comp_pres {M : ℕ} {P₁ P₂ P₃ A B : Matrix (Fin M) (Fin M) ℂ}
    (hB : P₂ * (B * P₁) = B * P₁) (hA : P₃ * (A * P₂) = A * P₂) :
    P₃ * (A * (B * P₁)) = A * (B * P₁) := by
  rw [← hB, ← Matrix.mul_assoc A, ← Matrix.mul_assoc P₃, hA, Matrix.mul_assoc A, hB]

theorem subDiagProj_mul_inv_of_self {N : ℕ} (S : BitAssignment N → Prop) (U : Unitary (2 ^ N))
    (hU : subDiagProj S * (U.1 * subDiagProj S) = U.1 * subDiagProj S) :
    subDiagProj S * ((U⁻¹).1 * subDiagProj S) = (U⁻¹).1 * subDiagProj S := by
  let P := subDiagProj S
  have hP_herm : Pᴴ = P := subDiagProj_conjTranspose S
  have hP_sq : P * P = P := subDiagProj_mul_self S
  have hU_coe_inv : (U⁻¹).1 = U.1ᴴ := by simp [Matrix.star_eq_conjTranspose]
  have hU_left : U.1ᴴ * U.1 = 1 :=
    (congrArg (· * U.1) (Matrix.star_eq_conjTranspose U.1).symm).trans (Unitary.coe_star_mul_self U)
  have hU_right : U.1 * U.1ᴴ = 1 :=
    (congrArg (U.1 * ·) (Matrix.star_eq_conjTranspose U.1).symm).trans (Unitary.coe_mul_star_self U)
  let Y := U.1 * P
  let Z := U.1ᴴ * P
  let B := Z - P * Z
  have hY_sq : Yᴴ * Y = P := by
    have h1 : (P * U.1ᴴ) * (U.1 * P) = P * (U.1ᴴ * U.1) * P := by simp [Matrix.mul_assoc]
    simpa [Y, conjTranspose_mul, hP_herm, hU_left, hP_sq] using h1
  have hZ_sq : Zᴴ * Z = P := by
    have h1 : (P * U.1) * (U.1ᴴ * P) = P * (U.1 * U.1ᴴ) * P := by simp [Matrix.mul_assoc]
    simpa [Z, conjTranspose_mul, hP_herm, hU_right, hP_sq] using h1
  have hZPZ : Zᴴ * (P * Z) = Y * Yᴴ := by
    have h1 : (P * U.1) * (P * (U.1ᴴ * P)) = (P * Y) * (Yᴴ * P) := by
      simp only [Y, conjTranspose_mul, hP_herm]
      calc (P * U.1) * (P * (U.1ᴴ * P)) = P * U.1 * (P * P) * U.1ᴴ * P := by
            simp [hP_sq, Matrix.mul_assoc]
        _ = (P * (U.1 * P)) * ((P * U.1ᴴ) * P) := by simp [Matrix.mul_assoc]
    have hY_adj : (P * Y)ᴴ = Yᴴ * P := by simp [conjTranspose_mul, hP_herm]
    rw [show Zᴴ = P * U.1 by simp [Z, conjTranspose_mul, hP_herm]]
    dsimp only [Z]
    rw [h1, ← hY_adj, show P * Y = Y from hU]
  have hBB : Bᴴ * B = P - Y * Yᴴ := by
    have h2 : (Zᴴ * P) * (P * Z) = Zᴴ * (P * Z) := by
      calc (Zᴴ * P) * (P * Z) = Zᴴ * (P * P) * Z := by simp [Matrix.mul_assoc]
        _ = Zᴴ * (P * Z) := by simp [hP_sq, Matrix.mul_assoc]
    rw [show Bᴴ = Zᴴ - Zᴴ * P by simp [B, conjTranspose_sub, conjTranspose_mul, hP_herm],
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h2, Matrix.mul_assoc Zᴴ P Z,
      sub_self, sub_zero, hZ_sq, hZPZ]
  have hTrEq : (∑ i : Fin (2 ^ N), (Y * Yᴴ) i i) = ∑ i : Fin (2 ^ N), P i i := by
    rw [← hY_sq]
    dsimp only [Matrix.mul_apply]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _)
  have hTrZero : (∑ i : Fin (2 ^ N), (Bᴴ * B) i i) = 0 := by
    simp only [hBB, Matrix.sub_apply, Finset.sum_sub_distrib, hTrEq, sub_self]
  have hReZero : ∑ i : Fin (2 ^ N), ∑ j : Fin (2 ^ N),
      ((B j i).re * (B j i).re + (B j i).im * (B j i).im) = 0 := by
    have hRe := congrArg Complex.re hTrZero
    simp only [Complex.zero_re, Complex.re_sum] at hRe
    refine hRe ▸ Finset.sum_congr rfl fun i _ ↦ ?_
    change _ = (∑ j : Fin (2 ^ N), (Bᴴ) i j * B j i).re
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [Matrix.conjTranspose_apply, Complex.mul_re]
  have hNN : ∀ j i : Fin (2 ^ N), 0 ≤ (B j i).re * (B j i).re + (B j i).im * (B j i).im :=
    fun _ _ ↦ add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hB0 : B = 0 := Matrix.ext fun j i ↦ by
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg
      fun i' _ ↦ Finset.sum_nonneg fun j' _ ↦ hNN j' i').mp hReZero i (Finset.mem_univ i)
    have hj0 := (Finset.sum_eq_zero_iff_of_nonneg fun j' _ ↦ hNN j' i).mp hi0 j (Finset.mem_univ j)
    apply Complex.ext
    · change (B j i).re = 0
      nlinarith [mul_self_nonneg (B j i).re, mul_self_nonneg (B j i).im]
    · change (B j i).im = 0
      nlinarith [mul_self_nonneg (B j i).re, mul_self_nonneg (B j i).im]
  simpa [P, Z, hU_coe_inv] using (sub_eq_zero.mp hB0).symm

theorem inv_congr_of_subDiagProj_eq {N : ℕ} (S : BitAssignment N → Prop)
    (U₁ U₂ : Unitary (2 ^ N)) (hEq : U₁.1 * subDiagProj S = U₂.1 * subDiagProj S)
    (hPres₂ : subDiagProj S * (U₂.1 * subDiagProj S) = U₂.1 * subDiagProj S) :
    (U₁⁻¹).1 * subDiagProj S = (U₂⁻¹).1 * subDiagProj S ∧
      subDiagProj S * ((U₂⁻¹).1 * subDiagProj S) = (U₂⁻¹).1 * subDiagProj S := by
  let P := subDiagProj S
  have hP_herm : Pᴴ = P := subDiagProj_conjTranspose S
  have hPres₁ : P * (U₁.1 * P) = U₁.1 * P := by
    dsimp [P]
    rw [hEq, hPres₂]
  have hInv₁ : P * ((U₁⁻¹).1 * P) = (U₁⁻¹).1 * P := subDiagProj_mul_inv_of_self S U₁ hPres₁
  have hInv₂ : P * ((U₂⁻¹).1 * P) = (U₂⁻¹).1 * P := subDiagProj_mul_inv_of_self S U₂ hPres₂
  have hC₁ : (U₁⁻¹).1 = U₁.1ᴴ := by simp [Matrix.star_eq_conjTranspose]
  have hC₂ : (U₂⁻¹).1 = U₂.1ᴴ := by simp [Matrix.star_eq_conjTranspose]
  have hAdj : P * U₁.1ᴴ = P * U₂.1ᴴ := by
    simpa [P, conjTranspose_mul, hP_herm] using congrArg conjTranspose hEq
  refine ⟨?_, hInv₂⟩
  calc (U₁⁻¹).1 * P
      = P * ((U₁⁻¹).1 * P) := hInv₁.symm
    _ = (P * U₁.1ᴴ) * P := by simp [hC₁, Matrix.mul_assoc]
    _ = (P * U₂.1ᴴ) * P := by rw [hAdj]
    _ = P * ((U₂⁻¹).1 * P) := by simp [hC₂, Matrix.mul_assoc]
    _ = (U₂⁻¹).1 * P := hInv₂

open Classical in
private theorem toff_pres_sub {N : ℕ} [NeZero (2 ^ N)] (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (S₁ S₂ : BitAssignment N → Prop)
    (hStep : ∀ β, S₁ β → S₂ (Function.update β anc (β anc + β c₁ * β c₂))) :
    subDiagProj S₂ * ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * subDiagProj S₁) =
      (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * subDiagProj S₁ :=
  matrix_ext_ket fun β ↦ by
    simp only [mul_mulVec_sub, subDiagProj_mulVec_ket]
    exact if hs : S₁ β then by
      simp only [hs, ↓reduceIte, ket_TOFF, subDiagProj_mulVec_ket, hStep β hs]
    else by simp [hs]

open Classical in
theorem realizesCleanUnitary_withTempAnd_subDiag
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (S_pre S_mid : BitAssignment n → Prop)
    (hPreZero : ∀ β, S_pre β → β anc = 0)
    (hMidEq : ∀ δ, S_mid δ → δ anc = δ c₁ * δ c₂)
    (hStepFwd : ∀ β, S_pre β → S_mid (Function.update β anc (β c₁ * β c₂)))
    (hStepBwd : ∀ δ, S_mid δ → S_pre (Function.update δ anc 0))
    (body : DynamicCircuit Var n) (U_body : Unitary (2 ^ n))
    (hbody : RealizesCleanUnitary v (subDiagProj S_mid) body U_body)
    (hBodyPres :
      subDiagProj S_mid * (U_body.1 * subDiagProj S_mid) = U_body.1 * subDiagProj S_mid) :
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
    RealizesCleanUnitary v (subDiagProj S_pre)
      (.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq body (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂)))
      (T_anc * U_body * T_anc) ∧
    subDiagProj S_pre * ((T_anc * U_body * T_anc).1 * subDiagProj S_pre) =
      (T_anc * U_body * T_anc).1 * subDiagProj S_pre := by
  intro T_anc
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let P_pre := subDiagProj S_pre
  let P_mid := subDiagProj S_mid
  let V := T_anc * U_body * T_anc
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hPpre_herm : P_preᴴ = P_pre := subDiagProj_conjTranspose S_pre
  have hPmid_herm : P_midᴴ = P_mid := subDiagProj_conjTranspose S_mid
  have hP₀_Ppre : P₀ * P_pre = P_pre := matrix_ext_ket fun β ↦ by
    simp only [P₀, P_pre, mul_mulVec_sub, subDiagProj_mulVec_ket]
    exact if hs : S_pre β then by simp [hs, ket_projector_zero, hPreZero β hs] else by simp [hs]
  have hPpre_P₀ : P_pre * P₀ = P_pre := by
    simpa [conjTranspose_mul, hP₀_herm, hPpre_herm] using congrArg conjTranspose hP₀_Ppre
  have hFwd_T : P_mid * (T_anc.1 * P_pre) = T_anc.1 * P_pre :=
    toff_pres_sub c₁ c₂ anc h₁₂ h₁a h₂a S_pre S_mid fun β hs ↦ by
      simpa [hPreZero β hs] using hStepFwd β hs
  have hFwd_T_adj : (P_pre * T_anc.1ᴴ) * P_mid = P_pre * T_anc.1ᴴ := by
    simpa [conjTranspose_mul, hPpre_herm, hPmid_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hFwd_T
  have hBwd_T : P_pre * (T_anc.1 * P_mid) = T_anc.1 * P_mid :=
    toff_pres_sub c₁ c₂ anc h₁₂ h₁a h₂a S_mid S_pre fun δ hs ↦ by
      simpa [hMidEq δ hs, CharTwo.add_self_eq_zero] using hStepBwd δ hs
  have hV_pres : P_pre * (V.1 * P_pre) = V.1 * P_pre := by
    simpa [V, Submonoid.coe_mul, Matrix.mul_assoc] using
      proj_comp_pres (proj_comp_pres hFwd_T hBodyPres) hBwd_T
  have hV_P₀_adj : (P_pre * V.1ᴴ) * P₀ = P_pre * V.1ᴴ := by
    have hV_P₀ : P₀ * (V.1 * P_pre) = V.1 * P_pre := by
      rw [← hV_pres, ← Matrix.mul_assoc, hP₀_Ppre, hV_pres]
    simpa [conjTranspose_mul, hP₀_herm, hPpre_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hV_P₀
  have hTU_adj : T_anc.1ᴴ * U_body.1ᴴ = V.1ᴴ * T_anc.1ᴴ := by
    have hU_eq : U_body * T_anc = T_anc * V := by
      dsimp [V]
      rw [← mul_assoc, ← mul_assoc, toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a, one_mul]
    simpa [Submonoid.coe_mul, conjTranspose_mul] using
      congrArg (fun W : Unitary (2 ^ n) ↦ W.1ᴴ) hU_eq
  refine ⟨⟨fun Ψ _ σ val => ?_, fun Θ hΘ σ => ?_⟩, hV_pres⟩
  · simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_seq,
      DynamicCircuit.compile_circuit, wp_qSeq, wp_circuit_compile_compat, wpQAssignCompat]
    exact congrArg _ (congrArg (fun x => (x : Observable (Fin (2 ^ n))))
      (hbody.1 (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Ψ)
        (fun σ' v' => wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Ψ σ' v') σ val))
  · let Ψ := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
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
    rw [← Matrix.mul_assoc P_pre P₀ T_anc.1ᴴ, hPpre_P₀, ← hFwd_T_adj, ← conj_conj,
      hbody.2 Ψ (fun σ' v' => wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' v') σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc (P_pre * T_anc.1ᴴ) P_mid U_body.1ᴴ, hFwd_T_adj,
      Matrix.mul_assoc P_pre T_anc.1ᴴ U_body.1ᴴ, hTU_adj,
      ← Matrix.mul_assoc P_pre V.1ᴴ T_anc.1ᴴ, ← hV_P₀_adj,
      show (Ψ σ).1.conj (((P_pre * V.1ᴴ) * P₀) * T_anc.1ᴴ) =
        (((wpQAssignCompat T_anc Ψ σ).1).conj P₀).conj (P_pre * V.1ᴴ) by
          simp [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
            Matrix.star_eq_conjTranspose, conj_conj, Matrix.mul_assoc],
      hstep_uncomp, conj_conj, hV_P₀_adj]

open Classical in
theorem embedUnitary_mul_subDiagProj_SubLift128_eq {n : ℕ} (rFull128 : QRegister 128 n)
    (rExtra9 : QRegister 9 n) (S : BitAssignment 128 → Prop) (U₁ U₂ : Unitary (2 ^ 128))
    (hEq : U₁.1 * subDiagProj S = U₂.1 * subDiagProj S) :
    (rFull128.embedUnitary U₁).1 * subDiagProj (SubLift128 rFull128 rExtra9 S) =
      (rFull128.embedUnitary U₂).1 * subDiagProj (SubLift128 rFull128 rExtra9 S) :=
  matrix_ext_ket fun β ↦ by
    simp only [mul_mulVec_sub, subDiagProj_mulVec_ket]
    by_cases hL : SubLift128 rFull128 rExtra9 S β
    · rw [ite_pos_sub hL, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        embedMatrix_mulVec_ket_sub, embedMatrix_mulVec_ket_sub]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have hcol : U₁.1 l (localIdxSub rFull128 β) = U₂.1 l (localIdxSub rFull128 β) := by
        rw [← ket_localIdxSub_eq rFull128 β l U₁.1, ← ket_localIdxSub_eq rFull128 β l U₂.1]
        have hv := congrArg (fun M ↦ M.mulVec (ket (fun i ↦ β (rFull128 i))) l) hEq
        simp only [mul_mulVec_sub, subDiagProj_mulVec_ket, hL.1, ↓reduceIte] at hv
        exact hv
      rw [hcol]
    · rw [ite_neg_sub hL, Matrix.mulVec_zero, Matrix.mulVec_zero]

open Classical in
theorem subDiagProj_SubLift128_mul_embedUnitary {n : ℕ} (rFull128 : QRegister 128 n)
    (rExtra9 : QRegister 9 n) (hDisjExtra : rFull128.DisjointWires rExtra9)
    (S₁ S₂ : BitAssignment 128 → Prop) (U : Unitary (2 ^ 128))
    (hPres : subDiagProj S₂ * (U.1 * subDiagProj S₁) = U.1 * subDiagProj S₁) :
    subDiagProj (SubLift128 rFull128 rExtra9 S₂) *
      ((rFull128.embedUnitary U).1 * subDiagProj (SubLift128 rFull128 rExtra9 S₁)) =
      (rFull128.embedUnitary U).1 * subDiagProj (SubLift128 rFull128 rExtra9 S₁) :=
  matrix_ext_ket fun β ↦ by
    simp only [mul_mulVec_sub, subDiagProj_mulVec_ket]
    by_cases hL : SubLift128 rFull128 rExtra9 S₁ β
    · rw [ite_pos_sub hL, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_sub, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Matrix.mulVec_smul]
      by_cases hnz : U.1 l (localIdxSub rFull128 β) = 0
      · simp only [hnz, zero_smul]
      · have hv := congrArg (fun M ↦ M.mulVec (ket (fun i ↦ β (rFull128 i))) l) hPres
        simp only [mul_mulVec_sub, subDiagProj_mulVec_ket, hL.1, ↓reduceIte] at hv
        have hLift₂ : SubLift128 rFull128 rExtra9 S₂
            (ZeroAncillaUSP.writeReg β rFull128 (basisBits 128 l)) :=
          ⟨by simpa [funext (ZeroAncillaUSP.writeReg_apply_reg β rFull128 (basisBits 128 l))]
                using mem_of_subDiagProj_mulVec_eq hv (by rwa [ket_localIdxSub_eq]),
           fun j ↦ (ZeroAncillaUSP.writeReg_apply_of_not_mem _ _ _ _
             fun ⟨i, hi⟩ ↦ hDisjExtra.ne i j hi).trans (hL.2 j)⟩
        rw [subDiagProj_mulVec_ket, ite_pos_sub hLift₂]
    · rw [ite_neg_sub hL, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Paired forward & inverse zero-`TOFF` dynamic realization on `(rFull128, rExtra9)` under
local `128`-wire invariant `S`, simultaneously tracking `U_loc` and `U_loc⁻¹` at `T`-budget `t`. -/
structure SubDynPair128 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (S : BitAssignment 128 → Prop) (t : ℕ)
    (dFwd dInv : DynamicCircuit Var n) (U_loc : Unitary (2 ^ 128)) : Prop where
  toffFwd : dFwd.count PrimitiveGate.TOFF = 0
  toffInv : dInv.count PrimitiveGate.TOFF = 0
  tFwd : dFwd.count PrimitiveGate.T ≤ t
  tInv : dInv.count PrimitiveGate.T ≤ t
  storeFwd : PreservesStoreConst dFwd
  storeInv : PreservesStoreConst dInv
  presLoc : subDiagProj S * (U_loc.1 * subDiagProj S) = U_loc.1 * subDiagProj S
  realFwd : RealizesCleanUnitary v (subDiagProj (SubLift128 rFull128 rExtra9 S)) dFwd
    (rFull128.embedUnitary U_loc)
  realInv : RealizesCleanUnitary v (subDiagProj (SubLift128 rFull128 rExtra9 S)) dInv
    (rFull128.embedUnitary U_loc⁻¹)

theorem SubDynPair128.mono_t {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t₁ t₂ : ℕ} {dFwd dInv : DynamicCircuit Var n}
    {U : Unitary (2 ^ 128)} (ht : t₁ ≤ t₂)
    (hp : SubDynPair128 v rFull128 rExtra9 S t₁ dFwd dInv U) : SubDynPair128 v rFull128
    rExtra9 S t₂ dFwd dInv U :=
  { hp with tFwd := hp.tFwd.trans ht, tInv := hp.tInv.trans ht }

theorem SubDynPair128.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t : ℕ} {dFwd dInv : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ 128)} (hEq : U₁ = U₂)
    (hp : SubDynPair128 v rFull128 rExtra9 S t dFwd dInv U₁) :
    SubDynPair128 v rFull128 rExtra9 S t dFwd dInv U₂ :=
  hEq ▸ hp

open Classical in
theorem SubDynPair128.congr_fwd {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    {S : BitAssignment 128 → Prop} {t : ℕ} {dFwd dInv : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ 128)} (hp : SubDynPair128 v rFull128 rExtra9 S t dFwd dInv U₁)
    (hEq : ∀ α : BitAssignment 128, S α → U₁.1.mulVec (ket α) = U₂.1.mulVec (ket α)) :
    SubDynPair128 v rFull128 rExtra9 S t dFwd dInv U₂ := by
  have hMatEq : U₁.1 * subDiagProj S = U₂.1 * subDiagProj S := matrix_ext_ket fun α ↦ by
    simp only [mul_mulVec_sub, subDiagProj_mulVec_ket]
    exact if hs : S α then by simp [hs, hEq α hs] else by simp [hs]
  have hPres₂ : subDiagProj S * (U₂.1 * subDiagProj S) = U₂.1 * subDiagProj S := by
    rw [← hMatEq, hp.presLoc]
  have hPL_herm := subDiagProj_conjTranspose (SubLift128 rFull128 rExtra9 S)
  exact ⟨hp.toffFwd, hp.toffInv, hp.tFwd, hp.tInv, hp.storeFwd, hp.storeInv, hPres₂,
    RealizesCleanUnitary.congr_unitary hPL_herm hp.realFwd
      (embedUnitary_mul_subDiagProj_SubLift128_eq rFull128 rExtra9 S U₁ U₂ hMatEq),
    RealizesCleanUnitary.congr_unitary hPL_herm hp.realInv
      (embedUnitary_mul_subDiagProj_SubLift128_eq rFull128 rExtra9 S U₁⁻¹ U₂⁻¹
        (inv_congr_of_subDiagProj_eq S U₁ U₂ hMatEq hPres₂).1)⟩

theorem SubDynPair128.static {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rFull128 : QRegister 128 n) (rExtra9 : QRegister 9 n)
    (S : BitAssignment 128 → Prop) (c : Circuit 128) (hToff : c.count PrimitiveGate.TOFF = 0)
    (hSpan : PreservesSpanSub S S c) :
    SubDynPair128 v rFull128 rExtra9 S (c.count PrimitiveGate.T)
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
    presLoc := subDiagProj_mul_of_preservesSpanSub hSpan
    realFwd := hEvFwd ▸ RealizesCleanUnitary.circuit v _ (c.onRegister rFull128)
    realInv := hEvInv ▸ RealizesCleanUnitary.circuit v _ (c.inverse.onRegister rFull128)
  }

theorem SubDynPair128.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) {S : BitAssignment 128 → Prop} {t₁ t₂ : ℕ}
    {dFwd₁ dInv₁ dFwd₂ dInv₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ 128)}
    (h₁ : SubDynPair128 v rFull128 rExtra9 S t₁ dFwd₁ dInv₁ U₁)
    (h₂ : SubDynPair128 v rFull128 rExtra9 S t₂ dFwd₂ dInv₂ U₂) :
    SubDynPair128 v rFull128 rExtra9 S (t₁ + t₂) (.seq dFwd₁ dFwd₂) (.seq dInv₂ dInv₁)
      (U₂ * U₁) := by
  have hPL_herm := subDiagProj_conjTranspose (SubLift128 rFull128 rExtra9 S)
  have hEmbInv : rFull128.embedUnitary U₁⁻¹ * rFull128.embedUnitary U₂⁻¹ =
      rFull128.embedUnitary (U₂ * U₁)⁻¹ := by
    rw [unitary_mul_inv_rev_sub, rFull128.embedUnitary_mul]
  exact
    { toffFwd := by simp [DynamicCircuit.count, h₁.toffFwd, h₂.toffFwd]
      toffInv := by simp [DynamicCircuit.count, h₁.toffInv, h₂.toffInv]
      tFwd := Nat.add_le_add h₁.tFwd h₂.tFwd
      tInv := (Nat.add_comm _ _) ▸ Nat.add_le_add h₂.tInv h₁.tInv
      storeFwd := PreservesStoreConst.seq h₁.storeFwd h₂.storeFwd
      storeInv := PreservesStoreConst.seq h₂.storeInv h₁.storeInv
      presLoc := by simpa [Submonoid.coe_mul, Matrix.mul_assoc] using
        proj_comp_pres h₁.presLoc h₂.presLoc
      realFwd := (rFull128.embedUnitary_mul U₂ U₁).symm ▸
        RealizesCleanUnitary.seq hPL_herm h₁.realFwd h₂.realFwd
          (subDiagProj_SubLift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S S U₁ h₁.presLoc)
      realInv := hEmbInv ▸ RealizesCleanUnitary.seq hPL_herm h₂.realInv h₁.realInv
        (subDiagProj_SubLift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S S U₂⁻¹
          (subDiagProj_mul_inv_of_self S U₂ h₂.presLoc)) }

theorem realizesCleanUnitary_sandwich_circuit_sub {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {v : Var} {P_pre P_mid : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hPpre : P_preᴴ = P_pre) (hPmid : P_midᴴ = P_mid) (cFwd cBwd : Circuit n)
    (hFwd : P_mid * (cFwd.eval.1 * P_pre) = cFwd.eval.1 * P_pre)
    {body : DynamicCircuit Var n} {U_body : Unitary (2 ^ n)}
    (hbody : RealizesCleanUnitary v P_mid body U_body) :
    RealizesCleanUnitary v P_pre (.seq (.circuit cFwd) (.seq body (.circuit cBwd)))
      (cBwd.eval * U_body * cFwd.eval) := by
  have hadj : (P_pre * cFwd.eval.1ᴴ) * P_mid = P_pre * cFwd.eval.1ᴴ := by
    simpa [conjTranspose_mul, hPpre, hPmid, ← Matrix.mul_assoc] using congrArg conjTranspose hFwd
  refine ⟨fun Ψ hΨ σ val => ?_, fun Θ hΘ σ => ?_⟩
  · simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
      wp_circuit_compile_compat, wpQAssignCompat]
    exact congrArg (qAssignObsMap cFwd.eval) (hbody.1 (wpQAssignCompat cBwd.eval Ψ)
      (fun σ' val' => by simp only [wpQAssignCompat, hΨ σ' val']) σ val)
  · simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
      wp_circuit_compile_compat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [show ((wp body.compile (wpQAssignCompat cBwd.eval Θ) σ).1).conj (P_pre * cFwd.eval.1ᴴ) =
        (((wp body.compile (wpQAssignCompat cBwd.eval Θ) σ).1).conj P_mid).conj
          (P_pre * cFwd.eval.1ᴴ) by rw [conj_conj, hadj],
      hbody.2 _ (fun σ' val' => by simp only [wpQAssignCompat, hΘ σ' val']) σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj, Submonoid.coe_mul, conjTranspose_mul,
      ← Matrix.mul_assoc, hadj]

theorem SubDynPair128.withCliff {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) {S_pre S_mid : BitAssignment 128 → Prop}
    {t : ℕ} (C : Circuit 128) (hCToff : C.count PrimitiveGate.TOFF = 0)
    (hCT : C.count PrimitiveGate.T = 0) (hCFwd : PreservesSpanSub S_pre S_mid C)
    (hCBwd : PreservesSpanSub S_mid S_pre C.inverse)
    {bFwd bInv : DynamicCircuit Var n} {U_body : Unitary (2 ^ 128)}
    (hb : SubDynPair128 v rFull128 rExtra9 S_mid t bFwd bInv U_body) :
    SubDynPair128 v rFull128 rExtra9 S_pre t
      (.seq (.circuit (C.onRegister rFull128))
        (.seq bFwd (.circuit (C.inverse.onRegister rFull128))))
      (.seq (.circuit (C.onRegister rFull128))
        (.seq bInv (.circuit (C.inverse.onRegister rFull128))))
      (C.inverse.eval * U_body * C.eval) := by
  have hCFwd_loc := subDiagProj_mul_of_preservesSpanSub hCFwd
  have hCBwd_loc := subDiagProj_mul_of_preservesSpanSub hCBwd
  have hCFwd_onReg : subDiagProj (SubLift128 rFull128 rExtra9 S_mid) *
      ((C.onRegister rFull128).eval.1 * subDiagProj (SubLift128 rFull128 rExtra9 S_pre)) =
      (C.onRegister rFull128).eval.1 * subDiagProj (SubLift128 rFull128 rExtra9 S_pre) := by
    rw [Circuit.eval_onRegister]
    exact subDiagProj_SubLift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S_pre S_mid
      C.eval hCFwd_loc
  have hEmbFwd : ((C.inverse.onRegister rFull128).eval * rFull128.embedUnitary U_body) *
      (C.onRegister rFull128).eval = rFull128.embedUnitary (C.inverse.eval * U_body * C.eval) := by
    rw [Circuit.eval_onRegister, Circuit.eval_onRegister,
      ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  have hEmbInv : ((C.inverse.onRegister rFull128).eval * rFull128.embedUnitary U_body⁻¹) *
      (C.onRegister rFull128).eval =
      rFull128.embedUnitary (C.inverse.eval * U_body * C.eval)⁻¹ := by
    rw [Circuit.eval_onRegister, Circuit.eval_onRegister, unitary_mul_inv_rev_sub,
      unitary_mul_inv_rev_sub, Circuit.eval_inverse, inv_inv, ← unitary_mul_assoc_sub,
      ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  exact {
    toffFwd := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCToff, hb.toffFwd]
    toffInv := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCToff, hb.toffInv]
    tFwd := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCT, hb.tFwd]
    tInv := by simp [DynamicCircuit.count, Circuit.count_onRegister, hCT, hb.tInv]
    storeFwd := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq hb.storeFwd (PreservesStoreConst.circuit _))
    storeInv := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq hb.storeInv (PreservesStoreConst.circuit _))
    presLoc := by
      simpa [Submonoid.coe_mul, Matrix.mul_assoc] using
        proj_comp_pres (proj_comp_pres hCFwd_loc hb.presLoc) hCBwd_loc
    realFwd := hEmbFwd ▸ realizesCleanUnitary_sandwich_circuit_sub
      (subDiagProj_conjTranspose _) (subDiagProj_conjTranspose _)
      (C.onRegister rFull128) (C.inverse.onRegister rFull128) hCFwd_onReg hb.realFwd
    realInv := hEmbInv ▸ realizesCleanUnitary_sandwich_circuit_sub
      (subDiagProj_conjTranspose _) (subDiagProj_conjTranspose _)
      (C.onRegister rFull128) (C.inverse.onRegister rFull128) hCFwd_onReg hb.realInv
  }

theorem ket_andComputeIf_of_zero_sub {N : ℕ} (c₁ c₂ anc : Wire N) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (α : BitAssignment N) (h0 : α anc = 0) :
    (andComputeIf c₁ c₂ anc).eval.1.mulVec (ket α) =
      ket (Function.update α anc (α c₁ * α c₂)) := by
  simpa only [andComputeIf, h₁a, h₂a, ↓reduceDIte] using
    ket_andCompute_of_zero c₁ c₂ anc h₁a h₂a α h0

theorem ket_andComputeIf_inv_of_eq_sub {N : ℕ} (c₁ c₂ anc : Wire N) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (δ : BitAssignment N) (heq : δ anc = δ c₁ * δ c₂) :
    (andComputeIf c₁ c₂ anc).inverse.eval.1.mulVec (ket δ) = ket (Function.update δ anc 0) := by
  refine inv_mulVec_ket_of_fwd_sub _ _ _ ?_
  rw [ket_andComputeIf_of_zero_sub c₁ c₂ anc h₁a h₂a _ (Function.update_self anc 0 δ),
    Function.update_of_ne h₁a 0 δ, Function.update_of_ne h₂a 0 δ, ← heq]
  exact congrArg ket (funext fun w ↦
    if hw : w = anc then by simp [hw] else by simp [Function.update_of_ne hw])

open Classical in
theorem SubDynPair128.withTempAnd {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rFull128 : QRegister 128 n} {rExtra9 : QRegister 9 n}
    (hDisjExtra : rFull128.DisjointWires rExtra9) (c₁ c₂ anc : Wire 128) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) {S_pre S_mid : BitAssignment 128 → Prop} {t : ℕ}
    (hPreZero : ∀ α, S_pre α → α anc = 0) (hMidEq : ∀ δ, S_mid δ → δ anc = δ c₁ * δ c₂)
    (hStepFwd : ∀ α, S_pre α → S_mid (Function.update α anc (α c₁ * α c₂)))
    (hStepBwd : ∀ δ, S_mid δ → S_pre (Function.update δ anc 0))
    {bFwd bInv : DynamicCircuit Var n} {U_body : Unitary (2 ^ 128)}
    (hb : SubDynPair128 v rFull128 rExtra9 S_mid t bFwd bInv U_body) :
    SubDynPair128 v rFull128 rExtra9 S_pre (t + 4)
      (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
        (rFull128.wires.injective.ne h₁a) (rFull128.wires.injective.ne h₂a))
        (.seq bFwd (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
          (rFull128.wires.injective.ne h₁₂))))
      (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
        (rFull128.wires.injective.ne h₁a) (rFull128.wires.injective.ne h₂a))
        (.seq bInv (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc)
          (rFull128.wires.injective.ne h₁₂))))
      ((andComputeIf c₁ c₂ anc).inverse.eval * U_body * (andComputeIf c₁ c₂ anc).eval) := by
  have h₁₂' : rFull128 c₁ ≠ rFull128 c₂ := rFull128.wires.injective.ne h₁₂
  have h₁a' : rFull128 c₁ ≠ rFull128 anc := rFull128.wires.injective.ne h₁a
  have h₂a' : rFull128 c₂ ≠ rFull128 anc := rFull128.wires.injective.ne h₂a
  let L_pre := SubLift128 rFull128 rExtra9 S_pre
  let L_mid := SubLift128 rFull128 rExtra9 S_mid
  have hUpdPull (β : BitAssignment n) (b : ZMod 2) :
      (fun i ↦ Function.update β (rFull128 anc) b (rFull128 i)) =
        Function.update (fun i ↦ β (rFull128 i)) anc b :=
    funext fun i ↦ if hia : i = anc then by
      rw [hia, Function.update_self, Function.update_self]
    else by rw [Function.update_of_ne (rFull128.wires.injective.ne hia), Function.update_of_ne hia]
  have hL_fwd : ∀ β, L_pre β →
      L_mid (Function.update β (rFull128 anc) (β (rFull128 c₁) * β (rFull128 c₂))) :=
    fun β ⟨h1, h2⟩ ↦ ⟨(hUpdPull β _).symm ▸ hStepFwd _ h1,
      fun j ↦ (Function.update_of_ne (fun h ↦ hDisjExtra.ne anc j h.symm) _ β).trans (h2 j)⟩
  have hL_bwd : ∀ δ, L_mid δ → L_pre (Function.update δ (rFull128 anc) 0) :=
    fun δ ⟨h1, h2⟩ ↦ ⟨(hUpdPull δ 0).symm ▸ hStepBwd _ h1,
      fun j ↦ (Function.update_of_ne (fun h ↦ hDisjExtra.ne anc j h.symm) 0 δ).trans (h2 j)⟩
  let hSub := subDiagProj_SubLift128_mul_embedUnitary rFull128 rExtra9 hDisjExtra S_mid S_mid
  obtain ⟨hRealFwd_T, _⟩ := realizesCleanUnitary_withTempAnd_subDiag v (rFull128 c₁)
    (rFull128 c₂) (rFull128 anc) h₁₂' h₁a' h₂a' L_pre L_mid (fun _ h ↦ hPreZero _ h.1)
    (fun _ h ↦ hMidEq _ h.1) hL_fwd hL_bwd bFwd (rFull128.embedUnitary U_body) hb.realFwd
    (hSub U_body hb.presLoc)
  obtain ⟨hRealInv_T, _⟩ := realizesCleanUnitary_withTempAnd_subDiag v (rFull128 c₁)
    (rFull128 c₂) (rFull128 anc) h₁₂' h₁a' h₂a' L_pre L_mid (fun _ h ↦ hPreZero _ h.1)
    (fun _ h ↦ hMidEq _ h.1) hL_fwd hL_bwd bInv (rFull128.embedUnitary U_body⁻¹) hb.realInv
    (hSub U_body⁻¹ (subDiagProj_mul_inv_of_self S_mid U_body hb.presLoc))
  let T_loc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  have hToffOnReg : (Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a'
      h₂a').eval = rFull128.embedUnitary T_loc := by
    have hon : (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).onRegister rFull128 =
        Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a' h₂a' := by
      dsimp only [Circuit.TOFF, Circuit.onRegister]
      congr 1
      apply qreg_ext_sub
      intro i
      fin_cases i
      · rfl
      · rfl
      · rfl
    rw [← hon, Circuit.eval_onRegister]
  have hEmbFwd : ((Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a'
      h₂a').eval * rFull128.embedUnitary U_body) * (Circuit.TOFF (rFull128 c₁) (rFull128 c₂)
      (rFull128 anc) h₁₂' h₁a' h₂a').eval = rFull128.embedUnitary (T_loc * U_body * T_loc) := by
    rw [hToffOnReg, ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  have hTloc_inv : T_loc⁻¹ = T_loc :=
    inv_eq_of_mul_eq_one_right (toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a)
  have hU_inv_eq : (T_loc * U_body * T_loc)⁻¹ = T_loc * U_body⁻¹ * T_loc := by
    rw [unitary_mul_inv_rev_sub, unitary_mul_inv_rev_sub, hTloc_inv, ← unitary_mul_assoc_sub]
  have hEmbInv : ((Circuit.TOFF (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂' h₁a'
      h₂a').eval * rFull128.embedUnitary U_body⁻¹) * (Circuit.TOFF (rFull128 c₁) (rFull128 c₂)
      (rFull128 anc) h₁₂' h₁a' h₂a').eval = rFull128.embedUnitary (T_loc * U_body * T_loc)⁻¹ := by
    rw [hU_inv_eq, hToffOnReg, ← rFull128.embedUnitary_mul, ← rFull128.embedUnitary_mul]
  have hPresLoc_T : subDiagProj S_pre * ((T_loc * U_body * T_loc).1 * subDiagProj S_pre) =
      (T_loc * U_body * T_loc).1 * subDiagProj S_pre := by
    have hFT := toff_pres_sub c₁ c₂ anc h₁₂ h₁a h₂a S_pre S_mid fun α hs ↦ by
      simpa [hPreZero α hs] using hStepFwd α hs
    have hBT := toff_pres_sub c₁ c₂ anc h₁₂ h₁a h₂a S_mid S_pre fun δ hs ↦ by
      simpa [hMidEq δ hs, CharTwo.add_self_eq_zero] using hStepBwd δ hs
    simpa [T_loc, Submonoid.coe_mul, Matrix.mul_assoc] using
      proj_comp_pres (proj_comp_pres hFT hb.presLoc) hBT
  have hPairT : SubDynPair128 v rFull128 rExtra9 S_pre (t + 4)
      (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁a' h₂a')
        (.seq bFwd (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂')))
      (.seq (DynamicCircuit.andCompute (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁a' h₂a')
        (.seq bInv (DynamicCircuit.andUncompute v (rFull128 c₁) (rFull128 c₂) (rFull128 anc) h₁₂')))
      (T_loc * U_body * T_loc) :=
    { toffFwd := by simp [DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, hb.toffFwd]
      toffInv := by simp [DynamicCircuit.count, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, hb.toffInv]
      tFwd := by
        simp only [DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
          DynamicCircuit.count_andUncompute_t, Nat.add_zero]
        exact Nat.add_comm 4 _ ▸ Nat.add_le_add_left hb.tFwd 4
      tInv := by
        simp only [DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
          DynamicCircuit.count_andUncompute_t, Nat.add_zero]
        exact Nat.add_comm 4 _ ▸ Nat.add_le_add_left hb.tInv 4
      storeFwd := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq hb.storeFwd (PreservesStoreConst.andUncompute v _ _ _ h₁₂'))
      storeInv := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq hb.storeInv (PreservesStoreConst.andUncompute v _ _ _ h₁₂'))
      presLoc := hPresLoc_T
      realFwd := hEmbFwd ▸ hRealFwd_T
      realInv := hEmbInv ▸ hRealInv_T }
  refine hPairT.congr_fwd fun α hα ↦ ?_
  simp only [Submonoid.coe_mul, mul_mulVec_sub]
  rw [show T_loc.1.mulVec (ket α) = ket (Function.update α anc (α c₁ * α c₂)) by
        simp only [T_loc, ket_TOFF, hPreZero α hα, zero_add],
      ket_andComputeIf_of_zero_sub c₁ c₂ anc h₁a h₂a α (hPreZero α hα)]
  let α_mid := Function.update α anc (α c₁ * α c₂)
  have hα_mid : S_mid α_mid := hStepFwd α hα
  let ψ := U_body.1.mulVec (ket α_mid)
  have hψ_pres : (subDiagProj S_mid).mulVec ψ = ψ := by
    have hv := congrArg (fun M ↦ M.mulVec (ket α_mid)) hb.presLoc
    simp only [mul_mulVec_sub, subDiagProj_mulVec_ket, hα_mid, ↓reduceIte] at hv
    exact hv
  change T_loc.1.mulVec ψ = (andComputeIf c₁ c₂ anc).inverse.eval.1.mulVec ψ
  rw [mulVec_eq_sum_ket_sub ψ, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx0 : ψ x = 0
  · simp only [hx0, zero_smul, Matrix.mulVec_zero]
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hSx : S_mid (basisBits 128 x) := mem_of_subDiagProj_mulVec_eq (congrFun hψ_pres x) hx0
    have hOut₁ : T_loc.1.mulVec (ket (basisBits 128 x)) =
        ket (Function.update (basisBits 128 x) anc 0) := by
      simp only [T_loc, ket_TOFF, hMidEq _ hSx, CharTwo.add_self_eq_zero]
    rw [ket_andComputeIf_inv_of_eq_sub c₁ c₂ anc h₁a h₂a _ (hMidEq _ hSx)]
    exact congrArg (ψ x • ·) hOut₁

/-! ## Section 2: Dynamic `dFinishXorFastFwd` and `dFinishXorFastInv` (`24` `.T`, `0` `.TOFF`) -/

theorem cnotIf_inverse_eq_self {n : ℕ} (c t : Wire n) : (cnotIf c t).inverse = cnotIf c t := by
  unfold cnotIf
  split_ifs
  · rfl
  · simp [Circuit.CNOT, Circuit.inverse, inverseGate]

theorem chIf_mulVec_ket_zero {N : ℕ} (c q : Wire N) (hcq : c ≠ q) (β : BitAssignment N)
    (hc0 : β c = 0) : (chIf c q).eval.1.mulVec (ket β) = ket β := by
  rw [chIf, dite_neg_sub hcq]
  exact chCircuit_mulVec_ket_ctrl_zero c q hcq β hc0

theorem chIf_mulVec_ket_one {N : ℕ} (c q : Wire N) (hcq : c ≠ q) (β : BitAssignment N)
    (hc1 : β c = 1) : (chIf c q).eval.1.mulVec (ket β) = (Circuit.H q).eval.1.mulVec (ket β) := by
  rw [chIf, dite_neg_sub hcq]
  exact chCircuit_mulVec_ket_ctrl_one c q hcq β hc1

theorem unHadamardList_mulVec_ket_zero {N : ℕ} (c : Wire N) (qs : List (Wire N))
    (hdisj : ∀ q ∈ qs, c ≠ q) (β : BitAssignment N) (hc0 : β c = 0) :
    (unHadamardList c qs).eval.1.mulVec (ket β) = ket β := by
  induction qs with
  | nil => simp only [unHadamardList, Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec]
  | cons q qs ih =>
      rw [unHadamardList, eval_seq_mulVec, ih (fun r hr ↦ hdisj r (List.mem_cons_of_mem q hr)),
          chIf_mulVec_ket_zero c q (hdisj q List.mem_cons_self) β hc0]

end ConfigPosPostPrep80FastSubblocks

end PosPostPrep80FastSubblocks
end
end PosPostPrep80FastSubblocks

end QuantumComputation.Specs.StoppingPowerSolution
