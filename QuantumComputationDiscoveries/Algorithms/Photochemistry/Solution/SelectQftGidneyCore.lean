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
public import Mathlib.Data.Nat.Bitwise
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.DiagonalShiftBridge
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.BlockEncodedWalkSpec
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.ReedMullerStage4Load

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators

noncomputable section
set_option exponentiation.threshold 8192
section
open scoped Circuit.Notation
section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectRefl
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop
theorem ket_basisOutcomeProjector_zero {d k : ℕ} (r : QRegister k d) (β : BitAssignment d) :
    (r.basisOutcomeProjector 0).mulVec (ket β) = if ∀ i : Fin k, β (r i) = 0 then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h0b : ∀ i : Fin k, basisBits k 0 i = 0 := fun i ↦ by
    apply Fin.ext; simp [basisBits, finFunctionFinEquiv]
  have hiff : r.extractIndex ((basisBitsEquiv d).symm β) = 0 ↔ (∀ i : Fin k, β (r i) = 0) := by
    constructor
    · intro h0 i;
      have hb :=
          (QRegExt.basisBits_extractIdx r) ((basisBitsEquiv d).symm β) i;
              rw [basisBits_basisBitsEquiv_symm,
          h0, h0b i] at hb; exact hb.symm
    · intro hall; apply (basisBitsEquiv k).injective; ext i;
      change basisBits k (r.extractIndex ((basisBitsEquiv d).symm β)) i = basisBits k 0 i;
      rw [(QRegExt.basisBits_extractIdx r), basisBits_basisBitsEquiv_symm, hall i, h0b i]
  simp only [hiff]
theorem reflMat_mulVec_ket {d lcuL : ℕ} (q : Wire d) (rLcu : QRegister lcuL d)
    (β : BitAssignment d) : (1 - (2 : ℂ) • ((QRegister.singleton q).basisOutcomeProjector 1 *
    (1 - rLcu.basisOutcomeProjector 0))).mulVec (ket β) = bitSign (β q * (if ∀ i : Fin lcuL,
    β (rLcu i) = 0 then (0 : ZMod 2) else 1)) • ket β := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, ket_basisOutcomeProjector_zero]
  by_cases hl : ∀ i : Fin lcuL, β (rLcu i) = 0
  · simp [hl, bitSign_zero]
  · simp only [hl, ↓reduceIte, sub_zero, mul_one, DynCircExt.ket_projector_one]
    rcases bit_cases (β q) with hq0 | hq1
    · simp [hq0, zero_ne_one, bitSign_zero]
    · simp only [hq1, ↓reduceIte, bitSign_one]; ext idx;
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
noncomputable def reflU_sym {d lcuL : ℕ} (q : Wire d) (rLcu : QRegister lcuL d)
    (hq : ∀ i : Fin lcuL, q ≠ rLcu i) : Unitary (2 ^ d) := by
  let M : Operator (2 ^ d) :=
      1 - (2 : ℂ) • ((QRegister.singleton q).basisOutcomeProjector 1 *
      (1 - rLcu.basisOutcomeProjector 0))
  have hherm : Mᴴ = M := by
    have hcomm : (QRegister.singleton q).basisOutcomeProjector 1 * rLcu.basisOutcomeProjector 0 =
        rLcu.basisOutcomeProjector 0 * (QRegister.singleton q).basisOutcomeProjector 1 :=
      (QRegister.singleton q).embedMatrix_comm_of_disjoint rLcu
        (QRegister.disjoint_iff.mpr fun u i hui ↦ by fin_cases u; exact hq i hui) _ _
    have hcomm1 : (1 - rLcu.basisOutcomeProjector 0) *
        (QRegister.singleton q).basisOutcomeProjector 1 =
        (QRegister.singleton q).basisOutcomeProjector 1 * (1 - rLcu.basisOutcomeProjector 0) := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hcomm]
    dsimp only [M];
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, star_ofNat, conjTranspose_mul,
        conjTranspose_sub, conjTranspose_one,
        (QRegister.singleton q).basisOutcomeProjector_conjTranspose 1,
        rLcu.basisOutcomeProjector_conjTranspose 0, hcomm1]
  have hmul : M * M = 1 := by
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, reflMat_mulVec_ket, Matrix.mulVec_smul,
        reflMat_mulVec_ket, smul_smul, bitSign_mul_self, one_smul]
  exact ⟨M, by rw [Matrix.star_eq_conjTranspose, hherm, hmul],
    by rw [Matrix.star_eq_conjTranspose, hherm, hmul]⟩
@[simp] theorem reflU_sym_val {d lcuL : ℕ} (q : Wire d) (rLcu : QRegister lcuL d)
    {hq : ∀ i : Fin lcuL, q ≠ rLcu i} :
    (reflU_sym q rLcu hq).1 =
      1 - (2 : ℂ) • ((QRegister.singleton q).basisOutcomeProjector 1 *
        (1 - rLcu.basisOutcomeProjector 0)) :=
  rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectRefl
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.SelectRefl
def tailReg {d m : ℕ} (r : QRegister (m + 1) d) : QRegister m d where
  wires :=
    { toFun := fun j ↦ r j.succ
      inj' := fun _ _ hij ↦ Fin.succ_inj.mp (r.wires.injective hij) }
def hadamardRegSym {Var : Type} {d : ℕ} (wAnc : Wire d) :
    (m : ℕ) → (r : QRegister m d) → (∀ i, r i ≠ wAnc) → SymDyn Var d wAnc
  | 0, _, _ => .fold 0 Fin.elim0
  | m + 1, r, hdisj =>
      .seq (.hadamard (r 0) (hdisj 0))
        (hadamardRegSym wAnc m (tailReg r) (fun j ↦ hdisj j.succ))
theorem hadamardRegSym_comm_disjoint {Var : Type} {d k : ℕ} (wAnc : Wire d) :
    ∀ (m : ℕ) (r : QRegister m d) (hdisj : ∀ i, r i ≠ wAnc)
      (rOut : QRegister k d) (_ : r.DisjointWires rOut) (M : Operator (2 ^ k)),
      (hadamardRegSym (Var := Var) wAnc m r hdisj).unitary.1 * rOut.embedMatrix M =
        rOut.embedMatrix M * (hadamardRegSym (Var := Var) wAnc m r hdisj).unitary.1
  | 0, _, _, rOut, _, M => by
      change (1 : Operator (2 ^ d)) * rOut.embedMatrix M = rOut.embedMatrix M * 1;
      rw [one_mul, mul_one]
  | m + 1, r, hdisj, rOut, hro, M => by
      have hc0 : (Circuit.H (r 0)).eval.1 * rOut.embedMatrix M = rOut.embedMatrix M *
          (Circuit.H (r 0)).eval.1 := by
        rw [Circuit.eval_single, QRegister.embedUnitary_val]
        exact (QRegister.singleton (r 0)).embedMatrix_comm_of_disjoint rOut
          (QRegister.disjoint_iff.mpr fun _ j hij ↦ QRegister.disjoint_iff.mp hro 0 j hij) _ M
      change (hadamardRegSym (Var := Var) wAnc m (tailReg r) (fun j ↦ hdisj j.succ)).unitary.1 *
          (Circuit.H (r 0)).eval.1 * rOut.embedMatrix M =
        rOut.embedMatrix M * ((hadamardRegSym (Var := Var) wAnc m (tailReg r)
            (fun j ↦ hdisj j.succ)).unitary.1 *
          (Circuit.H (r 0)).eval.1)
      rw [mul_assoc, hc0, ← mul_assoc, hadamardRegSym_comm_disjoint (Var := Var) wAnc m (tailReg r)
        (fun j ↦ hdisj j.succ) rOut (QRegister.disjoint_iff.mpr fun i j hij ↦
            QRegister.disjoint_iff.mp hro i.succ j hij) M, mul_assoc]
theorem writeReg_update_tailReg {d m : ℕ} (r : QRegister (m + 1) d) (β : BitAssignment d)
    (b : ZMod 2) (δ : BitAssignment m) :
    writeReg (Function.update β (r 0) b) (tailReg r) δ = writeReg β r (Fin.cons b δ) := by
  ext u
  by_cases hu0 : u = r 0
  · subst hu0
    have hnm : r 0 ∉ Set.range (tailReg r).wires := fun ⟨j, hj⟩ ↦
        Fin.succ_ne_zero j (r.wires.injective hj)
    rw [writeReg_apply_of_not_mem _ _ _ _ hnm, Function.update_self, writeReg_apply_reg,
        Fin.cons_zero]
  · by_cases hut : u ∈ Set.range (tailReg r).wires
    · rcases hut with ⟨j, rfl⟩
      change writeReg _ (tailReg r) δ (tailReg r j) = writeReg β r (Fin.cons b δ) (r j.succ)
      rw [writeReg_apply_reg, writeReg_apply_reg, Fin.cons_succ]
    · have hnm_r : u ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦
        Fin.cases (fun h0 : r 0 = u ↦ hu0 h0.symm) (fun j (hj : r j.succ = u) ↦ hut ⟨j, hj⟩) i hi
      rw [writeReg_apply_of_not_mem _ _ _ _ hut, Function.update_of_ne hu0,
          writeReg_apply_of_not_mem _ _ _ _ hnm_r]
theorem hadamardRegSym_unitary_mulVec_zero {Var : Type} {d : ℕ} (wAnc : Wire d) :
    ∀ (m : ℕ) (r : QRegister m d) (hdisj : ∀ i, r i ≠ wAnc) (β : BitAssignment d)
      (_ : ∀ i : Fin m, β (r i) = 0),
      (hadamardRegSym (Var := Var) wAnc m r hdisj).unitary.1.mulVec (ket β) =
        (sqrtHalf ^ m) • ∑ γ : BitAssignment m, ket (writeReg β r γ)
  | 0, r, hdisj, β, _ => by
      have hu1 : (hadamardRegSym (Var := Var) wAnc 0 r hdisj).unitary = 1 := rfl
      simp_rw [hu1, Submonoid.coe_one, Matrix.one_mulVec,
        show ∀ γ : BitAssignment 0, writeReg β r γ = β from
          fun γ ↦ funext fun u ↦ writeReg_apply_of_not_mem β r γ u fun ⟨i, _⟩ ↦ Fin.elim0 i]
      simp [Finset.sum_const]
  | m + 1, r, hdisj, β, h0 => by
      have hdisj' : ∀ i : Fin m, tailReg r i ≠ wAnc := fun j ↦ hdisj j.succ
      have htail0 (b : ZMod 2) (j : Fin m) : Function.update β (r 0) b (tailReg r j) = 0 :=
        (Function.update_of_ne (r.wires.injective.ne (Fin.succ_ne_zero j)) b β).trans (h0 j.succ)
      change ((hadamardRegSym (Var := Var) wAnc m (tailReg r) hdisj').unitary.1 *
          (Circuit.H (r 0)).eval.1).mulVec (ket β) = _
      rw [← Matrix.mulVec_mulVec, ket_H_apply (r 0) β, h0 0, bitSign_zero, one_smul,
          Matrix.mulVec_smul, Matrix.mulVec_add,
          hadamardRegSym_unitary_mulVec_zero wAnc m (tailReg r) hdisj' _ (htail0 0),
          hadamardRegSym_unitary_mulVec_zero wAnc m (tailReg r) hdisj' _ (htail0 1), ← smul_add,
          smul_smul, ← pow_succ']; congr 1
      simp_rw [writeReg_update_tailReg r β]
      symm
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) ↦ ZMod 2))
          (fun γ ↦ ket (writeReg β r γ)), Fintype.sum_prod_type]
      exact Fin.sum_univ_two fun b ↦ ∑ δ : BitAssignment m, ket (writeReg β r (Fin.cons b δ))
theorem proj_zero_mul_hadamardRegSym_inv_mulVec {Var : Type} {d : ℕ} (wAnc : Wire d) :
    ∀ (m : ℕ) (r : QRegister m d) (hdisj : ∀ i, r i ≠ wAnc) (β : BitAssignment d)
      (_ : ∀ i : Fin m, β (r i) = 0) (γ : BitAssignment m),
      (r.basisOutcomeProjector 0 *
          ((hadamardRegSym (Var := Var) wAnc m r hdisj).unitary⁻¹).1).mulVec
          (ket (writeReg β r γ)) =
        (sqrtHalf ^ m) • ket β
  | 0, r, hdisj, β, _, γ => by
      rw [show writeReg β r γ = β from funext fun u ↦ writeReg_apply_of_not_mem β r γ u fun ⟨i, _⟩ ↦
          Fin.elim0 i,
        show (hadamardRegSym (Var := Var) wAnc 0 r hdisj).unitary = 1 from rfl,
        inv_one, Submonoid.coe_one, mul_one, SelectRefl.ket_basisOutcomeProjector_zero]
      simp
  | m + 1, r, hdisj, β, h0, γ => by
      have hdisj' : ∀ i : Fin m, tailReg r i ≠ wAnc := fun j ↦ hdisj j.succ
      have hp_split : r.basisOutcomeProjector 0 =
          (QRegister.singleton (r 0)).basisOutcomeProjector 0 *
          (tailReg r).basisOutcomeProjector 0 := by
        refine matrix_ext_ket fun δ ↦ ?_
        rw [SelectRefl.ket_basisOutcomeProjector_zero, ← Matrix.mulVec_mulVec,
            SelectRefl.ket_basisOutcomeProjector_zero]
        by_cases ht : ∀ j : Fin m, δ (tailReg r j) = 0
        · rw [ite_eq_left ht, SelectRefl.ket_basisOutcomeProjector_zero]
          have hiff : (∀ u : Fin 1, δ (QRegister.singleton (r 0) u) = 0) ↔
              (∀ i : Fin (m + 1), δ (r i) = 0) :=
            ⟨fun hu0 i ↦ Fin.cases (hu0 0) (fun j ↦ ht j) i, fun hall _ ↦ hall 0⟩
          simp only [hiff]
        · have hnall : ¬ (∀ i : Fin (m + 1), δ (r i) = 0) :=
            fun hall ↦ ht fun j ↦ hall j.succ
          rw [ite_eq_right ht, ite_eq_right hnall, Matrix.mulVec_zero]
      have hU_inv : ((hadamardRegSym (Var := Var) wAnc (m + 1) r hdisj).unitary)⁻¹ =
          (Circuit.H (r 0)).eval *
              ((hadamardRegSym (Var := Var) wAnc m (tailReg r) hdisj').unitary)⁻¹ := by
        change ((hadamardRegSym (Var := Var) wAnc m (tailReg r) hdisj').unitary *
            (Circuit.H (r 0)).eval)⁻¹ = _
        rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right (eval_H_mul_self (r 0))]
      have hcomm : (tailReg r).basisOutcomeProjector 0 * (Circuit.H (r 0)).eval.1 =
          (Circuit.H (r 0)).eval.1 * (tailReg r).basisOutcomeProjector 0 := by
        rw [Circuit.eval_single, QRegister.embedUnitary_val, QRegister.basisOutcomeProjector]
        exact (tailReg r).embedMatrix_comm_of_disjoint (QRegister.singleton (r 0))
          (QRegister.disjoint_iff.mpr fun j _ hju ↦
              r.wires.injective.ne (Fin.succ_ne_zero j) hju) _ _
      have hwr : writeReg β r γ = writeReg (Function.update β (r 0) (γ 0)) (tailReg r)
          (fun j ↦ γ j.succ) := by
        rw [writeReg_update_tailReg]
        exact congrArg (writeReg β r) (funext (Fin.cases (by rw [Fin.cons_zero]) fun _ ↦
            by rw [Fin.cons_succ]))
      have htail0 (j : Fin m) : Function.update β (r 0) (γ 0) (tailReg r j) = 0 :=
        (Function.update_of_ne (r.wires.injective.ne j.succ_ne_zero) (γ 0) β).trans (h0 j.succ)
      rw [hp_split, hU_inv, hwr]
      have hpH : ((QRegister.singleton (r 0)).basisOutcomeProjector 0 *
          (Circuit.H (r 0)).eval.1).mulVec (ket (Function.update β (r 0) (γ 0))) =
          sqrtHalf • ket β := by
        have hp0 (c : ZMod 2) : ((QRegister.singleton (r 0)).basisOutcomeProjector 0).mulVec
            (ket (Function.update β (r 0) c)) = if c = 0 then ket β else 0 := by
          rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
          simp only [show (∀ i : Fin 1,
              Function.update β (r 0) c (QRegister.singleton (r 0) i) = 0) ↔ c = 0 from
            ⟨fun hc ↦ by simpa using hc 0, fun hc _ ↦ by simpa using hc⟩]
          split_ifs with hc
          · exact congrArg ket ((congrArg (Function.update β (r 0))
              (hc.trans (h0 0).symm)).trans (Function.update_eq_self _ β))
          · rfl
        rw [← Matrix.mulVec_mulVec, ket_H_apply, Function.update_self, Function.update_idem,
          Function.update_idem, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
          hp0 0, hp0 1]
        simp only [↓reduceIte, one_ne_zero, smul_zero, add_zero]
      have reassoc : ((QRegister.singleton (r 0)).basisOutcomeProjector 0 *
          (tailReg r).basisOutcomeProjector 0) *
          ((Circuit.H (r 0)).eval *
              ((hadamardRegSym (Var := Var) wAnc m (tailReg r) hdisj').unitary)⁻¹).1 =
          ((QRegister.singleton (r 0)).basisOutcomeProjector 0 * (Circuit.H (r 0)).eval.1) *
            ((tailReg r).basisOutcomeProjector 0 *
              ((hadamardRegSym (Var := Var) wAnc m (tailReg r) hdisj').unitary⁻¹).1) := by
        simp only [Submonoid.coe_mul, ← mul_assoc]
        congr 1
        rw [mul_assoc, hcomm, ← mul_assoc]
      rw [reassoc, ← Matrix.mulVec_mulVec,
        proj_zero_mul_hadamardRegSym_inv_mulVec wAnc m (tailReg r) hdisj' _ htail0 _,
        Matrix.mulVec_smul, hpH, smul_smul, mul_comm, ← pow_succ']
end QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix QFT PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.QubitizationKapteyn
theorem basisBits_symm_apply {d : ℕ} (γ : BitAssignment d)
    (w : Wire d) : basisBits d ((basisBitsEquiv d).symm γ) w = γ w :=
    congrFun ((basisBitsEquiv d).apply_symm_apply γ) w
noncomputable def readRegIdx {d b : ℕ} (r : QRegister b d) (δ : BitAssignment d) : Fin (2 ^ b) :=
    r.extractIndex ((basisBitsEquiv d).symm δ)
theorem basisBits_readRegIdx {d b : ℕ} (r : QRegister b d) (δ : BitAssignment d)
    (i : Fin b) : basisBits b (readRegIdx r δ) i = δ (r i) := by
  dsimp only [readRegIdx]; rw [(QRegExt.basisBits_extractIdx r), basisBits_symm_apply]
theorem readRegIdx_eq_of_bits {d b : ℕ} (r : QRegister b d) (δ : BitAssignment d) (x : Fin (2 ^ b))
    (h : ∀ i : Fin b, δ (r i) = basisBits b x i) : readRegIdx r δ = x := by
  apply (basisBitsEquiv b).injective; ext i;
  change basisBits b (readRegIdx r δ) i = basisBits b x i; rw [basisBits_readRegIdx, h i]
noncomputable def set16 {d : ℕ} (rP rCat : QRegister 8 d) (α : BitAssignment d)
    (z' y' : Fin (2 ^ 8)) : BitAssignment d :=
    writeReg (writeReg α rP (basisBits 8 z')) rCat (basisBits 8 y')
def LocalOnQft16 {d : ℕ} (rP rCat : QRegister 8 d) (M : Operator (2 ^ d)) : Prop :=
    ∀ (α : BitAssignment d) (G : Operator (2 ^ d)), (∀ z' y' : Fin (2 ^ 8),
    G.mulVec (ket (set16 rP rCat α z' y')) = 0) → G.mulVec (M.mulVec (ket α)) = 0
theorem writeReg_extractIndex_self_sym {d b : ℕ} (r : QRegister b d) (α : BitAssignment d) :
    writeReg α r (basisBits b (readRegIdx r α)) = α := by
  ext u
  by_cases hu : u ∈ Set.range r.wires
  · rcases hu with ⟨i, rfl⟩
    rw [writeReg_apply_reg, basisBits_readRegIdx]
  · exact writeReg_apply_of_not_mem α r _ u hu
theorem set16_eq_of_outside {d : ℕ} (rP rCat : QRegister 8 d) (α β : BitAssignment d)
    (z y : Fin (2 ^ 8))
    (h : ∀ u : Wire d, u ∉ Set.range rP.wires → u ∉ Set.range rCat.wires → α u = β u) :
    set16 rP rCat α z y = set16 rP rCat β z y := by
  ext u
  dsimp only [set16]
  by_cases hcat : u ∈ Set.range rCat.wires
  · rcases hcat with ⟨j, rfl⟩
    rw [writeReg_apply_reg, writeReg_apply_reg]
  · by_cases hp : u ∈ Set.range rP.wires
    · rcases hp with ⟨i, rfl⟩
      rw [writeReg_apply_of_not_mem _ rCat _ _ hcat, writeReg_apply_of_not_mem _ rCat _ _ hcat,
        writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ rCat _ _ hcat, writeReg_apply_of_not_mem _ rP _ _ hp,
        writeReg_apply_of_not_mem _ rCat _ _ hcat, writeReg_apply_of_not_mem _ rP _ _ hp,
            h u hp hcat]
theorem set16_self {d : ℕ} (rP rCat : QRegister 8 d) (α : BitAssignment d) :
    set16 rP rCat α (readRegIdx rP α) (readRegIdx rCat α) = α := by
  dsimp only [set16];
  rw [writeReg_extractIndex_self_sym rP α, writeReg_extractIndex_self_sym rCat α]
theorem LocalOnQft16.id {d : ℕ} (rP rCat : QRegister 8 d) :
    LocalOnQft16 rP rCat 1 := fun α G hG ↦ by
  rw [Matrix.one_mulVec, ← set16_self rP rCat α]; exact hG _ _
theorem LocalOnQft16.mul {d : ℕ} (rP rCat : QRegister 8 d)
    {A B : Operator (2 ^ d)}
    (hA : LocalOnQft16 rP rCat A) (hB : LocalOnQft16 rP rCat B) :
    LocalOnQft16 rP rCat (A * B) := fun α G hG ↦ by
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  refine hB α (G * A) fun z₁ y₁ ↦ ?_
  rw [← Matrix.mulVec_mulVec]
  refine hA (set16 rP rCat α z₁ y₁) G fun z₂ y₂ ↦ ?_
  rw [set16_eq_of_outside rP rCat _ α z₂ y₂ fun u hp hcat ↦ by
    dsimp only [set16]
    rw [writeReg_apply_of_not_mem _ rCat _ _ hcat, writeReg_apply_of_not_mem _ rP _ _ hp]]
  exact hG z₂ y₂
theorem eq_set16_of_pres_outside {d : ℕ} (rP rCat : QRegister 8 d) (α β : BitAssignment d)
    (hpres : ∀ u : Wire d, u ∉ Set.range rP.wires → u ∉ Set.range rCat.wires → β u = α u) :
    β = set16 rP rCat α (readRegIdx rP β) (readRegIdx rCat β) :=
  (set16_self rP rCat β).symm.trans (set16_eq_of_outside rP rCat β α _ _ hpres)
theorem embedMatrix_mulVec_ket_sym {d b : ℕ} (r : QRegister b d) (M : Operator (2 ^ b))
    (β : BitAssignment d) :
    (r.embedMatrix M).mulVec (ket β) = ∑ z' : Fin (2 ^ b),
        M z' (readRegIdx r β) • ket (writeReg β r (basisBits b z')) := by
  have hidx : readRegIdx r β = localIdx r β := by
    simp [readRegIdx, localIdx, QRegister.extractIndex]
  rw [hidx]
  exact DynCircExt.embedMatrix_mulVec_ket r M β
theorem LocalOnQft16.of_embed_rP {d : ℕ} (rP rCat : QRegister 8 d)
    (A : Operator (2 ^ 8)) :
    LocalOnQft16 rP rCat (rP.embedMatrix A) := fun α G hG ↦ by
  rw [embedMatrix_mulVec_ket_sym rP A α, Matrix.mulVec_sum]
  refine Finset.sum_eq_zero fun z' _ ↦ ?_
  rw [Matrix.mulVec_smul];
  have hwr : writeReg α rP (basisBits 8 z') =
      set16 rP rCat α z' (readRegIdx rCat (writeReg α rP (basisBits 8 z'))) :=
      (writeReg_extractIndex_self_sym rCat (writeReg α rP (basisBits 8 z'))).symm; rw [hwr, hG,
      smul_zero]
end QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastRouterCore
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
theorem sum_bit_mul_pow_eq_mod :
    ∀ (b val : ℕ), ∑ i : Fin b, ((val / 2 ^ i.val) % 2) * 2 ^ i.val = val % 2 ^ b
  | 0, val => (Nat.mod_one val).symm
  | b + 1, val => by
      rw [Fin.sum_univ_succ];
      simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one, Fin.val_succ, pow_succ]
      have hsub : ∀ k : Fin b, (val / (2 ^ k.val * 2)) % 2 * (2 ^ k.val * 2) =
          2 * (((val / 2) / 2 ^ k.val) % 2 * 2 ^ k.val) := fun k ↦ by
        have hd : val / (2 ^ k.val * 2) = (val / 2) / 2 ^ k.val := by
          rw [mul_comm, Nat.div_div_eq_div_mul]
        rw [hd]; ring
      simp_rw [hsub, ← Finset.mul_sum, sum_bit_mul_pow_eq_mod b (val / 2)]
      have hlt : val % 2 + 2 * ((val / 2) % 2 ^ b) < 2 ^ (b + 1) := by
        have h1 : val % 2 < 2 := Nat.mod_lt val (by decide)
        have h2 : (val / 2) % 2 ^ b < 2 ^ b := Nat.mod_lt _ (pow_pos (by decide) b)
        have h3 : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
        omega
      calc val % 2 + 2 * ((val / 2) % 2 ^ b)
          = (val % 2 + 2 * ((val / 2) % 2 ^ b) + 2 ^ (b + 1) * ((val / 2) / 2 ^ b)) % 2 ^ (b + 1)
              := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        _ = val % 2 ^ (b + 1) := by
            congr 1; have hdiv1 := Nat.mod_add_div val 2;
            have hdiv2 := Nat.mod_add_div (val / 2) (2 ^ b)
            have hp : 2 ^ (b + 1) * ((val / 2) / 2 ^ b) = 2 * (2 ^ b * ((val / 2) / 2 ^ b)) := by
              ring
            omega
theorem basisBits_val_eq {b : ℕ} (z : Fin (2 ^ b)) (i : Fin b) : (basisBits b z i).val =
    (z.val / 2 ^ i.val) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (z.val / 2 ^ i.val) with h | h <;>
    (simp [basisBits, finFunctionFinEquiv, h]; try rfl)
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastRouterCore
end
end

noncomputable section
variable {Var : Type}
namespace QuantumComputation.Specs.PhotochemistrySolution.KinB
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Circuit.Notation
open Operator Matrix QProg HermitianMat WithLp DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
noncomputable def prodState (n : ℕ) (v : Fin n → (ZMod 2 → ℂ)) : Fin (2 ^ n) → ℂ := fun j ↦
    ∏ k : Fin n, v k (basisBits n j k)
noncomputable def plusPhase (θ : ℝ) : ZMod 2 → ℂ := fun b ↦
    (1 / Real.sqrt 2 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (θ * (b.val : ℝ) : ℂ))
noncomputable def phaseGradientState (b : ℕ) : Fin (2 ^ b) → ℂ :=
    prodState b (fun r : Fin b ↦ plusPhase (-(1 : ℝ) / (2 ^ (b - r.val) : ℝ)))
noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
    basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm β) = β :=
  (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j :=
  (basisBitsEquiv q).symm_apply_apply j
theorem matrix_ext_ket {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := DynCircExt.matrix_ext_ket h
noncomputable def writeReg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
    basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeReg_apply_reg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegExt.basisBits_replaceIdx_apply]
theorem writeReg_apply_of_not_mem {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegExt.basisBits_replaceIdx_of_not_mem _ _ _ _ hw]
theorem writeReg_eq_update {n k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) : writeReg β r γ = Function.update β (r i₀)
        (γ i₀) :=
  DynCircExt.writeReg_eq_update β r γ i₀ hγ
noncomputable abbrev localIdx {n k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
    (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {n k : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k))
    (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) = ∑ l : Fin (2 ^ k),
        A l (localIdx r β) • ket (writeReg β r (basisBits k l)) :=
  DynCircExt.embedMatrix_mulVec_ket r A β
theorem embedMatrix_permMatrix_mulVec_ket {n k : ℕ} (r : QRegister k n)
    (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
        ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) :=
  PhotochemistrySolution.XMeasUnld.embedMatrix_permMatrix_mulVec_ket r σ β
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
abbrev dynBrk_bitPhaseI (b : ZMod 2) : ℂ := if b = 0 then 1 else Complex.I
noncomputable def dynBrk_omega8 : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
noncomputable abbrev dynBrk_bitPhaseT (b : ZMod 2) : ℂ := if b = 0 then 1 else dynBrk_omega8
noncomputable abbrev dynBrk_bitPhaseTInv (b : ZMod 2) : ℂ :=
    bitSign b * dynBrk_bitPhaseI b * dynBrk_bitPhaseT b
theorem dynBrk_bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b
theorem eval_seq_mulVec {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]; rfl
theorem ket_X {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) :=
        DynCircExt.ket_X q β
theorem dynBrk_ket_Z {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β := DynCircExt.gad_ket_Z q β
theorem dynBrk_ket_S {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) = dynBrk_bitPhaseI (β q) • ket β :=
  DynCircExt.gad_ket_S q β
theorem dynBrk_ket_T {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket β) = dynBrk_bitPhaseT (β q) • ket β :=
  DynCircExt.gad_ket_T q β
theorem dynBrk_ket_T_inv {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).inverse.eval.1.mulVec (ket β) = dynBrk_bitPhaseTInv (β q) • ket β :=
  DynCircExt.gad_ket_T_inv q β
theorem ket_CNOT {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) :=
  DynCircExt.ket_CNOT c t h β
theorem ket_TOFF {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      ket (Function.update β t (β t + β c₁ * β c₂)) :=
  DynCircExt.ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t β
def andComputeCircuit {n : ℕ} (c₁ c₂ anc : Wire n) (_h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) : Circuit n :=
  Circuit.H anc ;;ᶜ
  Circuit.T anc ;;ᶜ
  Circuit.CNOT c₂ anc h₂a ;;ᶜ
  (Circuit.T anc).inverse ;;ᶜ
  Circuit.CNOT c₁ anc h₁a ;;ᶜ
  Circuit.T anc ;;ᶜ
  Circuit.CNOT c₂ anc h₂a ;;ᶜ
  (Circuit.T anc).inverse ;;ᶜ
  Circuit.CNOT c₁ anc h₁a ;;ᶜ
  Circuit.H anc ;;ᶜ
  Circuit.S anc
abbrev andUncomputeDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : DynamicCircuit Var n :=
    DynCircExt.andUncompute_loc v c₁ c₂ anc h₁₂ h₁a h₂a
@[simp] theorem count_andComputeCircuit_t {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).count .T = 4 :=
  CircExt.count_andCompute_t_loc c₁ c₂ anc h₁₂ h₁a h₂a
@[simp] theorem count_andComputeCircuit_toff {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF = 0 :=
  CircExt.count_andCompute_toff_loc c₁ c₂ anc h₁₂ h₁a h₂a
@[simp] theorem count_andUncomputeDyn_t {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).count .T = 0 :=
  DynCircExt.count_andUncompute_t_loc v c₁ c₂ anc h₁₂ h₁a h₂a
@[simp] theorem count_andUncomputeDyn_toff {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF = 0 :=
  DynCircExt.count_andUncompute_toff_loc v c₁ c₂ anc h₁₂ h₁a h₂a
theorem andComputeCircuit_mulVec_ket_of_zero {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (β : BitAssignment n) (hanc : β anc = 0) :
    (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1.mulVec (ket β) =
      ket (Function.update β anc (β c₁ * β c₂)) :=
  DynCircExt.andCompute_mulVec_ket_of_zero c₁ c₂ anc h₁₂ h₁a h₂a β hanc
def cleanProj {n : ℕ} (S : Finset (Wire n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    Matrix.diagonal fun z : Fin (2 ^ n) ↦ if ∀ w ∈ S, basisBits n z w = 0 then (1 : ℂ) else 0
@[simp] theorem cleanProj_mulVec_ket {n : ℕ} (S : Finset (Wire n)) (β : BitAssignment n) :
    (cleanProj S).mulVec (ket β) =
      if ∀ w ∈ S, β w = 0 then ket β else 0 := by
  funext i
  by_cases h : ∀ w ∈ S, β w = 0
  · simp [cleanProj, ket, basisState, Pi.single_apply, ite_eq_left h]
  · simp [cleanProj, ket, basisState, ite_eq_right h]
@[simp] theorem cleanProj_conjTranspose {n : ℕ} (S : Finset (Wire n)) :
    (cleanProj S)ᴴ = cleanProj S := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ∀ w ∈ S, basisBits n i w = 0 <;> simp [cleanProj, h]
  · simp [cleanProj, Matrix.diagonal_apply_ne, hij, Ne.symm hij]
@[simp] theorem cleanProj_mul_self {n : ℕ} (S : Finset (Wire n)) :
    cleanProj S * cleanProj S = cleanProj S := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  by_cases h : ∀ w ∈ S, β w = 0
  · rw [ite_eq_left h, cleanProj_mulVec_ket, ite_eq_left h]
  · rw [ite_eq_right h, Matrix.mulVec_zero]
theorem cleanProj_union {n : ℕ} (S₁ S₂ : Finset (Wire n)) : cleanProj (S₁ ∪ S₂) = cleanProj S₁ *
    cleanProj S₂ := by
  apply matrix_ext_ket; intro β
  rw [cleanProj_mulVec_ket, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  by_cases h₂ : ∀ w ∈ S₂, β w = 0
  · rw [ite_eq_left h₂, cleanProj_mulVec_ket]
    have hiff : (∀ w ∈ S₁ ∪ S₂, β w = 0) ↔ ∀ w ∈ S₁, β w = 0 :=
        ⟨fun h w hw ↦ h w (Finset.mem_union_left S₂ hw), fun h w hw ↦
        (Finset.mem_union.mp hw).elim (h w) (h₂ w)⟩
    by_cases h₁ : ∀ w ∈ S₁, β w = 0
    · rw [ite_eq_left (hiff.mpr h₁), ite_eq_left h₁]
    · rw [ite_eq_right (mt hiff.mp h₁), ite_eq_right h₁]
  · rw [ite_eq_right h₂, Matrix.mulVec_zero, ite_eq_right]
    exact fun h ↦ h₂ (fun w hw ↦ h w (Finset.mem_union_right S₁ hw))
def andInvProj {n : ℕ} (c₁ c₂ anc : Wire n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    Matrix.diagonal fun z : Fin (2 ^ n) ↦
    if basisBits n z anc = basisBits n z c₁ * basisBits n z c₂ then (1 : ℂ) else 0
@[simp] theorem andInvProj_mulVec_ket {n : ℕ} (c₁ c₂ anc : Wire n) (β : BitAssignment n) :
    (andInvProj c₁ c₂ anc).mulVec (ket β) =
      if β anc = β c₁ * β c₂ then ket β else 0 := by
  funext i
  by_cases h : β anc = β c₁ * β c₂ <;> simp [andInvProj, ket, basisState, h]
@[simp] theorem andInvProj_conjTranspose {n : ℕ} (c₁ c₂ anc : Wire n) :
    (andInvProj c₁ c₂ anc)ᴴ = andInvProj c₁ c₂ anc := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : basisBits n i anc = basisBits n i c₁ * basisBits n i c₂ <;>
      simp [andInvProj, h]
  · simp [andInvProj, Matrix.diagonal_apply_ne, hij, Ne.symm hij]
theorem andCompute_eq_toff_on_cleanProj {n : ℕ} (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (S : Finset (Wire n))
    (hanc : anc ∈ S) : (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * cleanProj S =
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * cleanProj S := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  split_ifs with hS
  · rw [andComputeCircuit_mulVec_ket_of_zero c₁ c₂ anc h₁₂ h₁a h₂a β (hS anc hanc), ket_TOFF,
        hS anc hanc, zero_add]
  · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem andInvProj_mul_toff_mul_cleanProj {n : ℕ} (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (S : Finset (Wire n))
    (hanc : anc ∈ S) : andInvProj c₁ c₂ anc * ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 *
    cleanProj S) = (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * cleanProj S := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  split_ifs with hS
  · rw [ket_TOFF, andInvProj_mulVec_ket, Function.update_self, Function.update_of_ne h₁a,
        Function.update_of_ne h₂a, hS anc hanc, zero_add, ite_eq_left rfl]
  · simp
@[simp] theorem dynBrk_qAssign_val {d : ℕ} (U : 𝐔[Fin d]) (M : Observable (Fin d)) :
    (qAssign_obs_map U M).1 = U.1ᴴ * M.1 * U.1 := by
  change (star U.1) * M.1 * (star U.1)ᴴ = U.1ᴴ * M.1 * U.1;
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
@[simp] theorem dynBrk_wp_qAssign_val {Var : Type} [Fintype Var] {d : ℕ}
    (U : 𝐔[Fin d]) (Θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (wpQAssignCompat U Θ σ).1 = U.1ᴴ * (Θ σ).1 * U.1 := dynBrk_qAssign_val U (Θ σ)
theorem andInvProj_mul_wp_andUncomputeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) (σ : Store Var) : andInvProj c₁ c₂ anc *
    ((wp (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ σ).1) * andInvProj c₁ c₂ anc =
    andInvProj c₁ c₂ anc * ((wpQAssignCompat (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval Θ σ).1) *
    andInvProj c₁ c₂ anc := by
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0;
  let T_u := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval; let T_gate := T_u.1;
  have hP₀ : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hT_sq : T_gate * T_gate = 1 := by
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ket_TOFF, ket_TOFF, Function.update_self, Function.update_of_ne h₁a,
        Function.update_of_ne h₂a, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero,
        add_zero, Function.update_eq_self, Matrix.one_mulVec]
  have hunit : T_gateᴴ * T_gate = 1 := T_u.2.1
  have hT_herm : T_gateᴴ = T_gate := by
    rw [← Matrix.mul_one T_gateᴴ, ← hT_sq, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  have hPand_eq : andInvProj c₁ c₂ anc = T_gate * P₀ * T_gate := by
    apply matrix_ext_ket; intro β
    rw [andInvProj_mulVec_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_TOFF,
        ket_projector_zero, Function.update_self]
    by_cases hinv : β anc = β c₁ * β c₂
    · rw [ite_eq_left hinv, hinv, CharTwo.add_self_eq_zero, ite_eq_left rfl, ket_TOFF,
          Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
          Function.update_idem, zero_add, ← hinv, Function.update_eq_self]
    · have hsum1 : β anc + β c₁ * β c₂ ≠ 0 := by
        rcases dynBrk_bit_cases (β anc) with h₁ | h₁ <;>
          rcases dynBrk_bit_cases (β c₁ * β c₂) with h₂ | h₂ <;>
          first | exact absurd (h₁.trans h₂.symm) hinv | simp [h₁, h₂]
      simp [hinv, hsum1]
  have hrest :=
      congrArg (fun Φ ↦ (Φ σ).1.1)
      (DynCircExt.restrictZeroAnc_wp_qAssign_toffoli_andUncomp_upd_eq v c₁ c₂ anc h₁₂ h₁a h₂a Θ
      hΘ)
  simp only [restrictAssertionToZeroAncilla_coe_loc, wpQAssignCompat,
      QhlAux.qAssign_obs_map_val] at hrest; change P₀ *
      (T_gateᴴ * ((wp (DynCircExt.andUncompute_loc v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ σ).1.1) *
      (T_gateᴴ)ᴴ) * P₀ᴴ = P₀ * (Θ σ).1.1 * P₀ᴴ at hrest; rw [Matrix.conjTranspose_conjTranspose,
      hP₀] at hrest; dsimp only [andUncomputeDyn]; rw [dynBrk_wp_qAssign_val, hPand_eq]
  rw [show (T_gate * P₀ * T_gate) *
      ((wp (DynCircExt.andUncompute_loc v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ σ).1) *
          (T_gate * P₀ * T_gate) =
        T_gate *
            (P₀ *
            (T_gateᴴ *
            ((wp (DynCircExt.andUncompute_loc v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ σ).1) *
            T_gate) * P₀) *
          T_gate by rw [hT_herm]; simp only [Matrix.mul_assoc],
      show (T_gate * P₀ * T_gate) * (T_gateᴴ * (Θ σ).1 * T_gate) * (T_gate * P₀ * T_gate) =
          T_gate * (P₀ * (Θ σ).1 * P₀) * T_gate by
        rw [hT_herm]
        exact (by simp only [Matrix.mul_assoc] :
          (T_gate * P₀ * T_gate) * (T_gate * (Θ σ).1 * T_gate) * (T_gate * P₀ * T_gate) =
            T_gate * P₀ * (T_gate * T_gate) * (Θ σ).1 * (T_gate * T_gate) * P₀ * T_gate).trans
          (by simp only [hT_sq, Matrix.mul_one, Matrix.mul_assoc])]
  exact congrArg (fun M ↦ T_gate * M * T_gate) hrest
inductive AndBracketProg (n : ℕ) where
  | id : AndBracketProg n
  | prim (c : Circuit n) : AndBracketProg n
  | seq (p₁ p₂ : AndBracketProg n) : AndBracketProg n
  | tempAnd (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : AndBracketProg n) : AndBracketProg n
namespace AndBracketProg
def toCircuit {n : ℕ} : AndBracketProg n → Circuit n
  | .id => .identity
  | .prim c => c
  | .seq p₁ p₂ => p₁.toCircuit ;;ᶜ p₂.toCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ
        body.toCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
def toDyn {Var : Type} {n : ℕ} (v : Var) : AndBracketProg n → DynamicCircuit Var n
  | .id => .identity
  | .prim c => .circuit c
  | .seq p₁ p₂ => .seq (p₁.toDyn v) (p₂.toDyn v)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (.circuit (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a))
        (.seq (body.toDyn v) (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a))
def numTempAnd {n : ℕ} : AndBracketProg n → ℕ
  | .id => 0
  | .prim _ => 0
  | .seq p₁ p₂ => p₁.numTempAnd + p₂.numTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.numTempAnd
def IsCliffordPrim {n : ℕ} : AndBracketProg n → Prop
  | .id => True
  | .prim c => c.count .T = 0 ∧ c.count .TOFF = 0
  | .seq p₁ p₂ => IsCliffordPrim p₁ ∧ IsCliffordPrim p₂
  | .tempAnd _ _ _ _ _ _ body => IsCliffordPrim body
theorem count_toDyn_toff {Var : Type} {n : ℕ} (v : Var) {p : AndBracketProg n}
    (hp : IsCliffordPrim p) : (p.toDyn v).count .TOFF = 0 := by
  induction p with
  | id => rfl
  | prim _ => exact hp.2
  | seq p₁ p₂ ih₁ ih₂ =>
      change (p₁.toDyn v).count .TOFF + (p₂.toDyn v).count .TOFF = 0; rw [ih₁ hp.1, ih₂ hp.2]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      change (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF + ((body.toDyn v).count .TOFF +
          (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF) =
          0; rw [count_andComputeCircuit_toff, ih hp, count_andUncomputeDyn_toff]
theorem count_toDyn_t {Var : Type} {n : ℕ} (v : Var) {p : AndBracketProg n}
    (hp : IsCliffordPrim p) : (p.toDyn v).count .T = 4 * p.numTempAnd := by
  induction p with
  | id => rfl
  | prim _ => simp [toDyn, numTempAnd, hp.1]
  | seq p₁ p₂ ih₁ ih₂ =>
      change (p₁.toDyn v).count .T + (p₂.toDyn v).count .T = 4 * (p₁.numTempAnd + p₂.numTempAnd)
      rw [ih₁ hp.1, ih₂ hp.2]; ring
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      change (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).count .T + ((body.toDyn v).count .T +
          (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).count .T) = 4 *
          (1 + body.numTempAnd); rw [count_andComputeCircuit_t, ih hp,
          count_andUncomputeDyn_t]; ring
def RealizesOnClean {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (S : Finset (Wire n)) (p : AndBracketProg n) : Prop :=
    cleanProj S * (p.toCircuit.eval.1 * cleanProj S) = p.toCircuit.eval.1 * cleanProj S ∧
    (∀ (Θ : CQAssertion (Store Var) (2 ^ n)), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, wp (p.toDyn v).compile Θ (Function.update σ v val) = wp (p.toDyn v).compile Θ σ) ∧
    (∀ (Θ : CQAssertion (Store Var) (2 ^ n)), (∀ σ val, Θ (Function.update σ v val) = Θ σ) → ∀ σ,
    cleanProj S * (wp (p.toDyn v).compile Θ σ).1 * cleanProj S = cleanProj S *
    (wpQAssignCompat p.toCircuit.eval Θ σ).1 * cleanProj S)
theorem RealizesOnClean.id {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (S : Finset (Wire n)) : RealizesOnClean v S .id := by
  refine ⟨by simp [toCircuit, cleanProj_mul_self], fun Θ hΘ σ val ↦ ?_, fun Θ _ σ ↦ ?_⟩
  · simpa [toDyn, DynamicCircuit.identity, Circuit.compile, wp] using hΘ σ val
  · simp [toDyn, toCircuit, DynamicCircuit.identity, Circuit.compile]
theorem RealizesOnClean.prim {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (S : Finset (Wire n)) (c : Circuit n)
    (hpres : cleanProj S * (c.eval.1 * cleanProj S) = c.eval.1 * cleanProj S) :
    RealizesOnClean v S (.prim c) := by
  refine ⟨hpres, fun Θ hΘ σ val ↦ ?_, fun Θ _ σ ↦ ?_⟩
  · simp [toDyn, wpQAssignCompat, hΘ σ val]
  · simp [toDyn, toCircuit]
theorem RealizesOnClean.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {v : Var} {S : Finset (Wire n)} {p₁ p₂ : AndBracketProg n} (h₁ : RealizesOnClean v S p₁)
    (h₂ : RealizesOnClean v S p₂) : RealizesOnClean v S (.seq p₁ p₂) := by
  let U₁ := p₁.toCircuit.eval.1; let U₂ := p₂.toCircuit.eval.1;
  have hpres₁ : cleanProj S * (U₁ * cleanProj S) = U₁ * cleanProj S := h₁.1;
  have hpres₂ : cleanProj S * (U₂ * cleanProj S) = U₂ * cleanProj S := h₂.1; refine ⟨?_, ?_, ?_⟩
  · simp only [toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
    calc cleanProj S * ((U₂ * U₁) * cleanProj S)
        = (cleanProj S * (U₂ * cleanProj S)) * (U₁ * cleanProj S) := by
            simpa only [Matrix.mul_assoc] using
              congrArg (fun X ↦ cleanProj S * (U₂ * X)) hpres₁.symm
      _ = (U₂ * U₁) * cleanProj S := by rw [hpres₂, Matrix.mul_assoc, hpres₁, Matrix.mul_assoc]
  · intro Θ hΘ σ val; simp only [toDyn, DynamicCircuit.compile, wp];
    exact h₁.2.1 (wp (p₂.toDyn v).compile Θ) (h₂.2.1 Θ hΘ) σ val
  · intro Θ hΘ σ;
    simp only [toDyn, toCircuit, DynamicCircuit.compile, wp, Circuit.eval_seq,
        h₁.2.2 _ (h₂.2.1 Θ hΘ) σ, dynBrk_wp_qAssign_val]
    have h₁_adj : cleanProj S * U₁ᴴ = cleanProj S * U₁ᴴ * cleanProj S := by
      simpa only [Matrix.conjTranspose_mul, cleanProj_conjTranspose, Matrix.mul_assoc] using
        (congrArg Matrix.conjTranspose hpres₁).symm
    have hstep := h₂.2.2 Θ hΘ σ; rw [dynBrk_wp_qAssign_val] at hstep
    calc cleanProj S * (U₁ᴴ * (wp (p₂.toDyn v).compile Θ σ).1 * U₁) * cleanProj S
        = cleanProj S * U₁ᴴ * (cleanProj S * (U₂ᴴ * (Θ σ).1 * U₂) * cleanProj S) *
            (U₁ * cleanProj S) := by
            rw [← hstep]
            let M₂ : Operator (2 ^ n) := (wp (p₂.toDyn v).compile Θ σ).1
            simpa only [M₂, Matrix.mul_assoc] using
              congrArg₂ (fun L R : Operator (2 ^ n) ↦ L * M₂ * R) h₁_adj hpres₁.symm
      _ = cleanProj S * ((U₂ * U₁)ᴴ * (Θ σ).1 * (U₂ * U₁)) * cleanProj S := by
            simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
              congrArg₂ (fun L R : Operator (2 ^ n) ↦ L * (U₂ᴴ * (Θ σ).1 * U₂) *
                  R) h₁_adj.symm hpres₁
theorem RealizesOnClean.tempAnd {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {S : Finset (Wire n)} (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hanc : anc ∈ S) {body : AndBracketProg n}
    (hbody : RealizesOnClean v (S.erase anc) body)
    (hcomm : body.toCircuit.eval.1 * andInvProj c₁ c₂ anc = andInvProj c₁ c₂ anc *
    body.toCircuit.eval.1)
    (hpresS : cleanProj S *
    (((AndBracketProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit).eval.1 * cleanProj S) =
    ((AndBracketProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit).eval.1 * cleanProj S) :
    RealizesOnClean v S (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  have hP_erase_S : cleanProj (S.erase anc) * cleanProj S = cleanProj S := by
    rw [← cleanProj_union, Finset.union_eq_right.mpr (Finset.erase_subset anc S)]
  have hwp_uncomp_indep : ∀ (Θ : CQAssertion (Store Var) (2 ^ n)) σ val,
      wp (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ (Function.update σ v val) =
      wp (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ σ := fun Θ σ val ↦
      DynCircExt.wp_andUncompute_update_self_loc v c₁ c₂ anc h₁₂ h₁a h₂a Θ σ val
  refine ⟨hpresS, ?_, ?_⟩
  · intro Θ _ σ val; simp only [toDyn, DynamicCircuit.compile, wp, wp_circuit_compile_loc];
    have hind :=
        hbody.2.1 _ (hwp_uncomp_indep Θ) σ val; simpa [wpQAssignCompat] using congrArg
        (qAssign_obs_map _) hind
  · intro Θ hΘ σ
    simp only [toDyn, toCircuit, DynamicCircuit.compile, wp, wp_circuit_compile_loc,
      dynBrk_wp_qAssign_val, Circuit.eval_seq, Submonoid.coe_mul]
    let P_S := cleanProj S
    let P_e := cleanProj (S.erase anc)
    let P_a := andInvProj c₁ c₂ anc
    let U_t := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
    let U_b := body.toCircuit.eval.1
    let M_0 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := (Θ σ).1
    let M_u : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
      (wp (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ σ).1
    let M_d : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
      (wp (body.toDyn v).compile (wp (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).compile Θ) σ).1
    have hb := hbody.2.2 _ (hwp_uncomp_indep Θ) σ
    have hu := andInvProj_mul_wp_andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ σ
    rw [dynBrk_wp_qAssign_val] at hb hu
    have hcomm_e : P_e * U_t = U_t * P_e := matrix_ext_ket fun β ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_TOFF, cleanProj_mulVec_ket,
        cleanProj_mulVec_ket]
      have hiff : (∀ w ∈ S.erase anc, Function.update β anc (β anc + β c₁ * β c₂) w = 0) ↔
          (∀ w ∈ S.erase anc, β w = 0) :=
        forall₂_congr fun w hw ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
      by_cases h : ∀ w ∈ S.erase anc, β w = 0
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h, ket_TOFF]
      · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h, Matrix.mulVec_zero]
    have hc_eq : (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * P_S = P_e * (U_t * P_S) := by
      rw [andCompute_eq_toff_on_cleanProj c₁ c₂ anc h₁₂ h₁a h₂a S hanc, ← Matrix.mul_assoc,
        hcomm_e, Matrix.mul_assoc, hP_erase_S]
    have hc_adj : P_S * (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1ᴴ =
        (U_t * P_S)ᴴ * P_e := by
      simpa only [P_S, P_e, Matrix.conjTranspose_mul, cleanProj_conjTranspose,
        Matrix.mul_assoc] using congrArg Matrix.conjTranspose hc_eq
    have hb_r : P_a * (U_b * (U_t * P_S)) = U_b * (U_t * P_S) := by
      rw [← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc,
        andInvProj_mul_toff_mul_cleanProj c₁ c₂ anc h₁₂ h₁a h₂a S hanc]
    have hb_l : (U_b * (U_t * P_S))ᴴ * P_a = (U_b * (U_t * P_S))ᴴ := by
      simpa only [P_a, Matrix.conjTranspose_mul, andInvProj_conjTranspose] using
        congrArg Matrix.conjTranspose hb_r
    have hslide : U_b * (P_e * (U_t * P_S)) = P_a * (U_b * (U_t * P_S)) := by
      rw [← Matrix.mul_assoc P_e, hcomm_e, Matrix.mul_assoc U_t, hP_erase_S, hb_r]
    have hslide_adj : (U_t * P_S)ᴴ * P_e * U_bᴴ = (U_b * (U_t * P_S))ᴴ * P_a := by
      simpa only [P_S, P_e, P_a, Matrix.conjTranspose_mul, cleanProj_conjTranspose,
        andInvProj_conjTranspose, Matrix.mul_assoc] using congrArg Matrix.conjTranspose hslide
    calc P_S * ((andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1ᴴ * M_d *
          (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1) * P_S
        = (U_t * P_S)ᴴ * (P_e * (U_bᴴ * M_u * U_b) * P_e) * (U_t * P_S) := by
            rw [← hb]
            simpa only [Matrix.mul_assoc] using congrArg₂ (fun L R ↦ L * M_d * R) hc_adj hc_eq
      _ = (U_b * (U_t * P_S))ᴴ * (P_a * (U_tᴴ * M_0 * U_t) * P_a) * (U_b * (U_t * P_S)) := by
            rw [← hu]
            simpa only [Matrix.mul_assoc] using
              congrArg₂ (fun L R ↦ L * M_u * R) hslide_adj hslide
      _ = P_S * ((U_t * U_b * U_t)ᴴ * M_0 * (U_t * U_b * U_t)) * P_S := by
            simpa only [P_S, Matrix.conjTranspose_mul, cleanProj_conjTranspose,
              Matrix.mul_assoc] using
              congrArg₂ (fun L R ↦ L * (U_tᴴ * M_0 * U_t) * R) hb_l hb_r
end AndBracketProg
end QuantumComputation.Specs.PhotochemistrySolution.KinB
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastDistKin
open scoped Circuit.Notation
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.SelectFastRouterCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
inductive GateOp (n : ℕ) : Type
  | x (w : Fin n)
  | cx (c t : Fin n)
  | ccx (c₁ c₂ t : Fin n)
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastDistKin
end
end

section
noncomputable section PhaseGradientSec
set_option exponentiation.threshold 8192
section
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
namespace QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.Circuit
def isOneQubitCircuit : Circuit 1 → Bool
  | .identity => true
  | .gate (k := 1) _ _ => true
  | .gate (k := _) _ _ => false
  | .seq c₁ c₂ => (isOneQubitCircuit c₁) && (isOneQubitCircuit c₂)
def evalCyclotomicAux : Circuit 1 → CyclotomicState → CyclotomicState
  | .identity, s => s
  | .gate (k := 1) g _, s => s.applyGate1 g
  | .gate (k := _) _ _, s => s
  | .seq c₁ c₂, s => evalCyclotomicAux c₂ (evalCyclotomicAux c₁ s)
def evalCyclotomic (c : Circuit 1) : CyclotomicState := evalCyclotomicAux c CyclotomicState.ketZero
theorem evalCyclotomicAux_toStateVector (c : Circuit 1) (s : CyclotomicState)
    (hc : (isOneQubitCircuit c) = true) : c.eval.1.mulVec s.toStateVector =
    (evalCyclotomicAux c s).toStateVector := by
  induction c generalizing s with
  | identity => simp [evalCyclotomicAux]
  | @gate k g r =>
      match k, g, r, hc with
      | 1, g, r, _ =>
          simpa [eval_gate, (show r = QRegister.whole 1 by
            ext i; exact (Nat.lt_one_iff.mp (r i).isLt).trans (Nat.lt_one_iff.mp i.isLt).symm),
            evalCyclotomicAux] using CyclotomicState.applyGate1_toStateVector g s
  | seq c₁ c₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hc
      simpa [eval_seq, ← Matrix.mulVec_mulVec, evalCyclotomicAux, ih₁ s h₁] using ih₂ _ h₂
theorem evalCyclotomic_toStateVector (c : Circuit 1) (hc : (isOneQubitCircuit c) = true) :
    c.eval.1 *ᵥ basisState 0 = (evalCyclotomic c).toStateVector := by
  rw [← CyclotomicState.ketZero_toStateVector];
  exact evalCyclotomicAux_toStateVector c CyclotomicState.ketZero hc
end QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.CircExt
end
end PhaseGradientSec

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution
namespace QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.KinB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket ket_CNOT ket_TOFF
  ket_X matrix_ext_ket
set_option exponentiation.threshold 8192 in
/-- Unsigned little-endian `B`-bit value `∑_{i < B} 2^i * (f i).val`. -/
def finBitsVal : ∀ {B : ℕ}, (Fin B → ZMod 2) → ℕ
  | 0, _ => 0
  | B + 1, f => (f 0).val + 2 * finBitsVal (fun i : Fin B ↦ f i.succ)
set_option exponentiation.threshold 8192 in
theorem finBitsVal_lt : ∀ {B : ℕ} (f : Fin B → ZMod 2), finBitsVal f < 2 ^ B
  | 0, _ => Nat.zero_lt_one
  | B + 1, f => by
      rw [finBitsVal, pow_succ']
      have := ZMod.val_lt (f 0)
      have := finBitsVal_lt fun i : Fin B ↦ f i.succ
      omega
set_option exponentiation.threshold 8192 in
theorem finBitsVal_succ {n : ℕ} (f : Fin (n + 1) → ZMod 2) :
    finBitsVal f = (f 0).val + 2 * finBitsVal (fun i ↦ f i.succ) := rfl
end QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd

namespace QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
/-- Even-octave shift index `k ∈ [0..8]` such that `m <<< (16 - 2 * k) ∈ [65536..262143]`. -/
def evenOctKRef (m : ℕ) : ℕ :=
  if m < 4 then 0 else if m < 16 then 1 else if m < 64 then 2 else if m < 256 then 3
  else if m < 1024 then 4 else if m < 4096 then 5 else if m < 16384 then 6
  else if m < 65536 then 7 else 8
/-- Clamped even-octave normalizer returning `(idx8, t10, k4)` for `(isNN, d2)`. -/
def evenOctIdxT10K (isNN : Bool) (d2 : ℕ) : ℕ × ℕ × ℕ :=
  let m := max d2 (if isNN then 8 else 1)
  let k := evenOctKRef m; let u := m <<< (16 - 2 * k)
  let idx := if u < 131072 then (u - 65536) / 512 else 128 + (u - 131072) / 1024
  let t10 := if u < 131072 then (u % 512) * 2 else u % 1024
  (idx, t10, k)
theorem evenOctIdxT10K_bounds (isNN : Bool) {d2 : ℕ} (hd2 : d2 < 262144) :
    let p := evenOctIdxT10K isNN d2
    p.1 < 256 ∧ p.2.1 < 1024 ∧ p.2.2 ≤ 8 := by
  dsimp only [evenOctIdxT10K]
  set m := max d2 (if isNN then 8 else 1)
  have hm : 1 ≤ m ∧ m < 262144 := by cases isNN <;> simp [m, le_max_iff, max_lt_iff, hd2]
  have hu : evenOctKRef m ≤ 8 ∧ 65536 ≤ m <<< (16 - 2 * evenOctKRef m) ∧
      m <<< (16 - 2 * evenOctKRef m) < 262144 := by
    unfold evenOctKRef; split_ifs <;> simp only [Nat.shiftLeft_eq] <;> omega
  refine ⟨?_, ?_, hu.1⟩ <;> split_ifs <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
set_option exponentiation.threshold 8192
open Real PhotochemistrySolution.ClusterPotSlice
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.TelescopeSlice
  PhotochemistrySolution.EvenOctB70
def idx7OfParts (p : ℕ × ℕ × ℕ) : ℕ := p.1 / 2
/-- `11`-bit sub-interval coordinate `(idx8 % 2) * 1024 + t10 ∈ [0..2047]`. -/
def t11OfParts (p : ℕ × ℕ × ℕ) : ℕ := (p.1 % 2) * 1024 + p.2.1
/-- Top-bin guard `k.testBit 3 && (idx7 == 95)` (`d2 ∈ [194560..195075]`). -/
def isClamp95Parts (p : ℕ × ℕ × ℕ) : Bool :=
  p.2.2.testBit 3 && (idx7OfParts p == 95)
/-- Polymorphic popcount `j ∈ {0, 1, 2, 3}` of three independent `M`-ary coins `< t`. -/
def popBernJGen {M : ℕ} (t : ℕ) (c : Fin 3 → Fin M) : ℕ :=
  (if (c 0).val < t then 1 else 0) +
  (if (c 1).val < t then 1 else 0) +
  (if (c 2).val < t then 1 else 0)
/-- Popcount `j ∈ {0, 1, 2, 3}` of three independent `11`-bit coins `< t11`. -/
abbrev popBernJ : ℕ → (Fin 3 → Fin 2048) → ℕ := @popBernJGen 2048
/-- Exact per-coin-triple `36`-bit output with `2`-point `k = 8, idx7 = 95` clamp. -/
def y36PopBernClamped (word512 : ℕ → ℕ) (yClamp0 yClamp1 : ℕ) (isNN : Bool) (d2 : ℕ)
    (c : Fin 3 → Fin 2048) : ℕ :=
  let p := evenOctIdxT10K isNN d2
  if isClamp95Parts p then
    if (t11OfParts p).testBit 9 then yClamp1 else yClamp0
  else
    (word512 (4 * idx7OfParts p + popBernJ (t11OfParts p) c)) >>> p.2.2
def Is3DBoxDistSq (d2 : ℕ) : Prop :=
    ∃ a b c : ℕ, a ≤ 255 ∧ b ≤ 255 ∧ c ≤ 255 ∧ d2 = a ^ 2 + b ^ 2 + c ^ 2
theorem popBernJGen_lt_four {M : ℕ} (t : ℕ) (c : Fin 3 → Fin M) : popBernJGen t c < 4 := by
  dsimp only [popBernJGen]; split_ifs <;> omega
theorem popBernJ_lt_four (t11 : ℕ) (c : Fin 3 → Fin 2048) : popBernJ t11 c < 4 :=
    popBernJGen_lt_four t11 c
theorem popBernJ_zero_of_t11_zero (c : Fin 3 → Fin 2048) : popBernJ 0 c = 0 := by
  simp [popBernJ, popBernJGen]
theorem parts_popBern_bounds (isNN : Bool) {d2 : ℕ} (hd2 : d2 < 262144) :
    let p := evenOctIdxT10K isNN d2
    idx7OfParts p < 128 ∧ t11OfParts p < 2048 ∧ p.2.2 ≤ 8 := by
  have hb := evenOctIdxT10K_bounds isNN hd2; dsimp only [idx7OfParts, t11OfParts] at hb ⊢; omega
theorem is3DBoxDistSq_le {d2 : ℕ} (h : Is3DBoxDistSq d2) : d2 ≤ 195075 := by
  rcases h with ⟨a, b, c, ha, hb, hc, rfl⟩; nlinarith
theorem openBoxDist1D_le_255 (a b : Fin 256) : openBoxDist1D a b ≤ 255 := by
  unfold openBoxDist1D twosComplement_frozen
  have hp : (0 : ℕ) < 2 ^ gridBits_frozen := by decide
  obtain ⟨_, _, _, _, _⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ :=
      ⟨Int.le_bmod (x := (a.val : ℤ)) hp, Int.bmod_lt (x := (a.val : ℤ)) hp,
    Int.le_bmod (x := (b.val : ℤ)) hp, Int.bmod_lt (x := (b.val : ℤ)) hp,
        (by decide : ((2 ^ gridBits_frozen : ℕ) : ℤ) = 256)⟩
  omega
theorem is3DBoxDistSq_pairOpenDistSq (x : Fin (2 ^ systemQubits_frozen)) (p q : Particle_frozen) :
    Is3DBoxDistSq (pairOpenDistSq x p q) := by
  rw [pairOpenDistSq, Fin.sum_univ_three]
  exact ⟨_, _, _, openBoxDist1D_le_255 _ _, openBoxDist1D_le_255 _ _, openBoxDist1D_le_255 _ _, rfl⟩
theorem openDistSq_ge_194560_iff {d2 : ℕ} (h3d : Is3DBoxDistSq d2) (hge : 194560 ≤ d2) : d2 =
    194566 ∨ d2 = 195075 := by
  rcases h3d with ⟨a, b, c, ha, hb, hc, rfl⟩
  have ⟨_, _, _⟩ : 254 ≤ a ∧ 254 ≤ b ∧ 254 ≤ c := ⟨by nlinarith, by nlinarith, by nlinarith⟩
  rcases (by omega : a = 254 ∨ a = 255) with rfl | rfl <;>
      rcases (by omega : b = 254 ∨ b = 255) with rfl | rfl <;>
    rcases (by omega : c = 254 ∨ c = 255) with rfl | rfl <;> omega
theorem isClamp95Parts_iff_ge_194560 (isNN : Bool) {d2 : ℕ} (hd2 : d2 ≤ 195075) :
    isClamp95Parts (evenOctIdxT10K isNN d2) = true ↔ 194560 ≤ d2 := by
  dsimp only [isClamp95Parts, idx7OfParts, evenOctIdxT10K]
  set m := max d2 (if isNN then 8 else 1)
  have hm : m ≤ 195075 ∧ (194560 ≤ m ↔ 194560 ≤ d2) := by
    cases isNN <;> simp only [m, ↓reduceIte, Bool.false_eq_true, max_le_iff, le_max_iff] <;> omega
  rw [← hm.2]
  by_cases hm65 : m < 65536
  · simp [show (evenOctKRef m).testBit 3 = false by unfold evenOctKRef; split_ifs <;> decide,
      show ¬194560 ≤ m by omega]
  · simp only [show evenOctKRef m = 8 by unfold evenOctKRef; split_ifs <;> omega,
      show (8 : ℕ).testBit 3 = true from rfl, Bool.true_and, beq_iff_eq, Nat.shiftLeft_eq]
    split_ifs <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

/- # Top-Level Unitary Restriction & Ket-Support Framework -/
namespace QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open scoped ComplexOrder
open Operator QProg Matrix Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
/--
Pointwise ket-support predicate on `n`-qubit state vectors `Fin (2 ^ n) → ℂ`
indexed via `BitAssignment n` (`(basisBitsEquiv n).symm`).
-/
def inKetPred {n : ℕ} (Pred : BitAssignment n → Prop) (v : Fin (2 ^ n) → ℂ) : Prop :=
    ∀ β : BitAssignment n, v ((basisBitsEquiv n).symm β) ≠ 0 → Pred β
theorem inKetPred_zero {n : ℕ} (Pred : BitAssignment n → Prop) : inKetPred Pred (0 : Fin (2 ^ n) →
    ℂ) :=
  fun _ h => False.elim (h rfl)
theorem inKetPred_add {n : ℕ} {Pred : BitAssignment n → Prop} {v w : Fin (2 ^ n) → ℂ}
    (hv : inKetPred Pred v) (hw : inKetPred Pred w) : inKetPred Pred (v + w) := fun β h => by
  by_cases h1 : v ((basisBitsEquiv n).symm β) = 0
  · exact hw β (by simpa [h1] using h)
  · exact hv β h1
theorem inKetPred_smul {n : ℕ} {Pred : BitAssignment n → Prop} (c : ℂ) {v : Fin (2 ^ n) → ℂ}
    (hv : inKetPred Pred v) : inKetPred Pred (c • v) := by
  intro β h; rw [Pi.smul_apply, smul_eq_mul] at h; exact hv β (right_ne_zero_of_mul h)
theorem ket_eq_single_symm {n : ℕ} (α : BitAssignment n) : ket α =
    (Pi.single ((basisBitsEquiv n).symm α) (1 : ℂ) : Fin (2 ^ n) → ℂ) := by
  have h1 := DynCircExt.single_eq_ket ((basisBitsEquiv n).symm α);
  have h2 : basisBits n ((basisBitsEquiv n).symm α) = α :=
      (basisBitsEquiv n).apply_symm_apply α; exact Eq.trans (congrArg DynCircExt.ket h2.symm)
      h1.symm
theorem inKetPred_ket {n : ℕ} {Pred : BitAssignment n → Prop} {α : BitAssignment n}
    (hα : Pred α) : inKetPred Pred (ket α) := fun β h => by
  classical
  by_contra hP
  exact h (ket_eq_single_symm α ▸ Pi.single_eq_of_ne (fun e : (basisBitsEquiv n).symm β =
      (basisBitsEquiv n).symm α => hP (((basisBitsEquiv n).symm.injective e).symm ▸ hα)) 1)
theorem inKetPred_sum {n : ℕ} {ι : Type*} [Fintype ι] {Pred : BitAssignment n → Prop}
    (f : ι → Fin (2 ^ n) → ℂ) (hf : ∀ i, inKetPred Pred (f i)) : inKetPred Pred (∑ i, f i) := by
  intro β h; rw [Finset.sum_apply] at h;
  have ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h; exact hf i β hi
theorem vec_eq_sum_ket {n : ℕ} (v : Fin (2 ^ n) → ℂ) : v = ∑ α : BitAssignment n,
    v ((basisBitsEquiv n).symm α) • ket α := by
  classical
  ext idx
  rw [Finset.sum_apply, Finset.sum_eq_single (basisBits n idx)]
  · simp [ket_eq_single_symm, (basisBitsEquiv n).symm_apply_apply]
  · intro α _ hα
    simp [ket_eq_single_symm, Pi.single_eq_of_ne (fun e : idx = (basisBitsEquiv n).symm α =>
        hα (e ▸ ((basisBitsEquiv n).apply_symm_apply α).symm))]
  · exact fun h => (h (Finset.mem_univ _)).elim
/-- Compose a ket-by-ket transition across `M.mulVec`. -/
theorem inKetPred_mulVec {n : ℕ} {P Q : BitAssignment n → Prop} (M : Operator (2 ^ n))
    (hStep : ∀ α : BitAssignment n, P α → inKetPred Q (M.mulVec (ket α))) {v : Fin (2 ^ n) → ℂ}
    (hv : inKetPred P v) : inKetPred Q (M.mulVec v) := by
  rw [vec_eq_sum_ket v, Matrix.mulVec_sum]
  refine inKetPred_sum _ fun α => ?_
  rw [Matrix.mulVec_smul]
  by_cases h0 : v ((basisBitsEquiv n).symm α) = 0
  · simpa [h0] using inKetPred_zero Q
  · exact inKetPred_smul _ (hStep α (hv α h0))
/-- Block product on `(A * P + (1 - P)) * (B * P + (1 - P))`. -/
theorem proj_block_mul {d : ℕ} (A B P : Operator d) (hPIdem : P * P = P) (hCommB : P * B = B * P)
    (hAB : A * B = 1) : (A * P + (1 - P)) * (B * P + (1 - P)) = 1 := by
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPIdem, sub_self]
  have h1 : A * P * (B * P) = P := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P B P, hCommB, Matrix.mul_assoc B P P,
      ← Matrix.mul_assoc A B, hAB, one_mul, hPIdem]
  rw [add_mul, mul_add, mul_add, h1, Matrix.mul_assoc A P, mul_sub P 1 P, mul_one, hPIdem,
    sub_self, mul_zero, ← hCommB, ← Matrix.mul_assoc (1 - P) P B, hQP, zero_mul,
    mul_sub (1 - P), mul_one, hQP, sub_zero, add_zero, zero_add, add_sub_cancel]
/--
Restrict a unitary `M` that commutes with self-adjoint projector `P` to `M` on `P`
and `1` on `1 - P`.
-/
noncomputable def unitaryOnProj {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) : Unitary d :=
  ⟨M.1 * P + (1 - P), by
    have hU1 : M.1ᴴ * M.1 = 1 := M.2.1; have hU2 : M.1 * M.1ᴴ = 1 := M.2.2
    have hCommH : P * M.1ᴴ = M.1ᴴ * P := by
      have h :=
          congrArg Matrix.conjTranspose hComm; simpa only [Matrix.conjTranspose_mul,
          hPHerm] using h.symm
    have hStar : star (M.1 * P + (1 - P)) = M.1ᴴ * P + (1 - P) := by
      change (M.1 * P + (1 - P))ᴴ = M.1ᴴ * P + (1 - P);
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_one, hPHerm, ← hCommH]
    refine ⟨?_, ?_⟩
    · rw [hStar]; exact proj_block_mul M.1ᴴ M.1 P hPIdem hComm hU1
    · rw [hStar]
      exact proj_block_mul M.1 M.1ᴴ P hPIdem hCommH hU2⟩
@[simp] theorem unitaryOnProj_val {d : ℕ} (M : Unitary d) (P : Operator d)
    (hPHerm : Pᴴ = P) (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) :
    (unitaryOnProj M P hPHerm hPIdem hComm).1 = M.1 * P + (1 - P) := rfl
theorem unitaryOnProj_mul_proj {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) : (unitaryOnProj M P hPHerm hPIdem hComm).1 *
    P = M.1 * P := by
  rw [unitaryOnProj_val, add_mul, Matrix.mul_assoc, hPIdem, sub_mul, one_mul, hPIdem, sub_self,
      add_zero]
theorem proj_mul_unitaryOnProj {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) : P *
    (unitaryOnProj M P hPHerm hPIdem hComm).1 = M.1 * P := by
  rw [unitaryOnProj_val, mul_add, ← Matrix.mul_assoc, hComm, Matrix.mul_assoc, hPIdem,
    mul_sub, mul_one, hPIdem, sub_self, add_zero]
theorem unitaryOnProj_comm_proj {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) :
    Commute (unitaryOnProj M P hPHerm hPIdem hComm).1 P :=
    (unitaryOnProj_mul_proj M P hPHerm hPIdem hComm).trans (proj_mul_unitaryOnProj M P hPHerm hPIdem
    hComm).symm
theorem unitaryOnProj_mul_compl {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) : (unitaryOnProj M P hPHerm hPIdem hComm).1 *
    (1 - P) = 1 - P := by
  rw [unitaryOnProj_val, add_mul, Matrix.mul_assoc, mul_sub P, mul_one, hPIdem, sub_self,
    mul_zero, zero_add, mul_sub, mul_one, sub_mul, one_mul, hPIdem, sub_self, sub_zero]
theorem unitaryOnProj_sq_one {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) (hInvol : M.1 * (M.1 * P) = P) :
    (unitaryOnProj M P hPHerm hPIdem hComm).1 * (unitaryOnProj M P hPHerm hPIdem hComm).1 = 1 := by
  set U := (unitaryOnProj M P hPHerm hPIdem hComm).1
  have hUP : U * P = M.1 * P := unitaryOnProj_mul_proj M P hPHerm hPIdem hComm
  have hUQ : U * (1 - P) = 1 - P := unitaryOnProj_mul_compl M P hPHerm hPIdem hComm
  calc U * U = U * (U * (P + (1 - P))) := by rw [add_sub_cancel, mul_one]
    _ = 1 := by rw [mul_add, mul_add, hUQ, hUQ, hUP, ← hComm, ← Matrix.mul_assoc U P M.1, hUP,
        Matrix.mul_assoc M.1 P M.1, hComm, hInvol, add_sub_cancel]
theorem unitaryOnProj_herm {d : ℕ} (M : Unitary d) (P : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hComm : P * M.1 = M.1 * P) (hInvol : M.1 * (M.1 * P) = P) :
    (unitaryOnProj M P hPHerm hPIdem hComm).1ᴴ = (unitaryOnProj M P hPHerm hPIdem hComm).1 := by
  set U := unitaryOnProj M P hPHerm hPIdem hComm
  calc U.1ᴴ = U.1ᴴ * (U.1 * U.1) := by
          rw [unitaryOnProj_sq_one M P hPHerm hPIdem hComm hInvol, mul_one]
    _ = U.1 := by rw [← Matrix.mul_assoc, show U.1ᴴ * U.1 = 1 from U.2.1, one_mul]
/--
Universal ring identity turning controlled action on `Q` into controlled action on
`unitaryOnProj`.
-/
theorem unitaryOnProj_ctrl_eq {d : ℕ} (C A : Unitary d) (P Q : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hCommC : P * C.1 = C.1 * P) (hCommA : P * A.1 = A.1 * P)
    (hCtrl : C.1 = (1 - Q) + Q * A.1) : (unitaryOnProj C P hPHerm hPIdem hCommC).1 = (1 - Q) + Q *
    (unitaryOnProj A P hPHerm hPIdem hCommA).1 := by
  rw [unitaryOnProj_val, unitaryOnProj_val, hCtrl]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc]; abel
/-- Universal ring identity transporting right-projected equality across `unitaryOnProj`. -/
theorem unitaryOnProj_mul_right {d : ℕ} (A B : Unitary d) (P K : Operator d) (hPHerm : Pᴴ = P)
    (hPIdem : P * P = P) (hCommA : P * A.1 = A.1 * P) (hCommB : P * B.1 = B.1 * P)
    (hPK : P * K = K * P) (hAB : A.1 * K = B.1 * K) : (unitaryOnProj A P hPHerm hPIdem hCommA).1 *
    K = (unitaryOnProj B P hPHerm hPIdem hCommB).1 * K := by
  rw [unitaryOnProj_val, unitaryOnProj_val, add_mul, add_mul, Matrix.mul_assoc, hPK,
    ← Matrix.mul_assoc A.1, hAB, Matrix.mul_assoc B.1, ← hPK, Matrix.mul_assoc]
/-- Inverse commutation with any operator `Q` from forward commutation with `W : Unitary d`. -/
theorem unitary_inv_comm {d : ℕ} (W : Unitary d) (Q : Operator d) (hWQ : W.1 * Q = Q * W.1) :
    (W⁻¹).1 * Q = Q * (W⁻¹).1 := by
  calc (W⁻¹).1 * Q = (W⁻¹).1 * (Q * (W.1 * (W⁻¹).1)) := by
          rw [show W.1 * (W⁻¹).1 = 1 from W.2.2, mul_one]
    _ = ((W⁻¹).1 * W.1) * (Q * (W⁻¹).1) := by
      rw [← Matrix.mul_assoc Q, ← hWQ]; simp only [Matrix.mul_assoc]
    _ = Q * (W⁻¹).1 := by rw [show (W⁻¹).1 * W.1 = 1 from W.2.1, one_mul]
/-- Right-projected equality is preserved under conjugation by any `W` commuting with `Q`. -/
theorem unitary_conj_mul_right {d : ℕ} (W A B : Unitary d) (Q : Operator d)
    (hWQ : W.1 * Q = Q * W.1) (hAB : A.1 * Q = B.1 * Q) : (W⁻¹ * A * W).1 * Q = (W⁻¹ * B * W).1 *
    Q := by
  change (W⁻¹).1 * A.1 * W.1 * Q = (W⁻¹).1 * B.1 * W.1 * Q
  calc (W⁻¹).1 * A.1 * W.1 * Q = (W⁻¹).1 * (A.1 * Q) * W.1 := by simp only [Matrix.mul_assoc, hWQ]
    _ = (W⁻¹).1 * B.1 * W.1 * Q := by rw [hAB]; simp only [Matrix.mul_assoc, ← hWQ]
/-- `(1 - Q) + Q * A` is preserved under conjugation by any `W` commuting with `Q`. -/
theorem unitary_conj_ctrl {d : ℕ} (W C A : Unitary d) (Q : Operator d) (hWQ : W.1 * Q = Q * W.1)
    (hCtrl : C.1 = (1 - Q) + Q * A.1) : (W⁻¹ * C * W).1 = (1 - Q) + Q * (W⁻¹ * A * W).1 := by
  have h1 : (W⁻¹).1 * W.1 = 1 := W.2.1
  change (W⁻¹).1 * C.1 * W.1 = (1 - Q) + Q * ((W⁻¹).1 * A.1 * W.1)
  rw [hCtrl]; simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, ← Matrix.mul_assoc,
    unitary_inv_comm W Q hWQ]; rw [h1, Matrix.mul_assoc Q (W⁻¹).1 W.1, h1, mul_one]
end QuantumComputation.Specs.PhotochemistrySolution.KetSupport
end

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
def natLeB (a b : ℕ) : Bool := Nat.beq (a - b) 0
def natLtB (a b : ℕ) : Bool := natLeB (a + 1) b
def zNonnegB : ℤ → Bool
  | Int.ofNat _ => true
  | Int.negSucc _ => false
def zLeB (a b : ℤ) : Bool := zNonnegB (b - a)
def maxDistPopB (isNN : Bool) (d2 : ℕ) : ℕ :=
    cond isNN (cond (natLtB d2 8) 8 d2) (cond (natLtB d2 1) 1 d2)
def evenOctKFast (m : ℕ) : ℕ :=
    cond (natLtB m 4) 0 (cond (natLtB m 16) 1 (cond (natLtB m 64) 2 (cond (natLtB m 256) 3
    (cond (natLtB m 1024) 4 (cond (natLtB m 4096) 5 (cond (natLtB m 16384) 6 (cond (natLtB m 65536)
    7 8)))))))
def evenOctPartsFast (isNN : Bool) (d2 : ℕ) : ℕ × ℕ × ℕ :=
  let m := maxDistPopB isNN d2; let k := evenOctKFast m; let u := m <<< (16 - 2 * k)
  (cond (natLtB u 131072) ((u - 65536) / 512) (128 + (u - 131072) / 1024),
   cond (natLtB u 131072) ((u % 512) * 2) (u % 1024), k)
def fin8BinFast (d : ℕ) : ℕ :=
    cond (natLtB d 1) 1 (cond (natLtB d 2) 2 (cond (natLtB d 4) 3 (cond (natLtB d 8) 4
    (cond (natLtB d 16) 5 (cond (natLtB d 32) 6 (cond (natLtB d 48) 7 0))))))
def allRangePow2 : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, lo, f => f lo
  | b + 1, lo, f => allRangePow2 b lo f && allRangePow2 b (lo + (1 <<< b)) f
def allRange (b n : ℕ) (f : ℕ → Bool) : Bool :=
    allRangePow2 b 0 (fun i ↦ cond (natLtB i n) (f i) true)
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open Real PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.EvenOctB70
@[simp] theorem zNonnegB_eq_true {x : ℤ} : (zNonnegB x = true) = (0 ≤ x) := by
  cases x <;> simp [zNonnegB]
@[simp] theorem zLeB_eq_true {a b : ℤ} : (zLeB a b = true) = (a ≤ b) := by
  simp only [zLeB, zNonnegB_eq_true]; exact propext sub_nonneg
@[simp] theorem natLeB_eq_true {a b : ℕ} : (natLeB a b = true) = (a ≤ b) := by
  simp only [natLeB, Nat.beq_eq, Nat.sub_eq_zero_iff_le]
@[simp] theorem natLtB_eq_true {a b : ℕ} : (natLtB a b = true) = (a < b) := by
  simp only [natLtB, natLeB_eq_true]; exact propext Nat.succ_le_iff
theorem cond_false_of_not {b : Bool} {x y : Bool} (h : b = true → False) : cond b x y = y := by
  cases b <;> simp_all
theorem cond_eq_ite {α : Type*} (b : Bool) (P : Prop) [Decidable P] (hb : (b = true) = P)
    (x y : α) : cond b x y = if P then x else y := by
  cases b <;> simp_all
theorem maxDistPopB_eq (isNN : Bool) (d2 : ℕ) : maxDistPopB isNN d2 = max d2 (if isNN then 8 else 1)
    := by
  unfold maxDistPopB
  cases isNN <;> simp only [Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ↓reduceIte,
    cond_eq_ite _ _ natLtB_eq_true, Nat.max_def] <;> split_ifs <;> omega
theorem evenOctKFast_eq (m : ℕ) : evenOctKFast m = evenOctKRef m := by
  unfold evenOctKFast evenOctKRef; simp only [cond_eq_ite _ _ natLtB_eq_true]
theorem evenOctPartsFast_eq (isNN : Bool) (d2 : ℕ) : evenOctPartsFast isNN d2 =
    evenOctIdxT10K isNN d2 := by
  unfold evenOctPartsFast evenOctIdxT10K;
  simp only [maxDistPopB_eq, evenOctKFast_eq, cond_eq_ite _ _ natLtB_eq_true]
theorem fin8BinFast_eq : ∀ d : Fin 48, fin8BinFast d.val = (fin8Bin d.val).val := by decide
theorem allRangePow2_eq_true {b lo : ℕ} {f : ℕ → Bool} (hPf : allRangePow2 b lo f = true) {i : ℕ}
    (hlo : lo ≤ i) (hhi : i < lo + 2 ^ b) : f i = true := by
  induction b generalizing lo with
  | zero => exact (by omega : i = lo) ▸ hPf
  | succ b ih =>
    simp only [allRangePow2, Bool.and_eq_true, Nat.shiftLeft_eq, one_mul] at hPf
    rw [pow_succ'] at hhi
    exact if hm : i < lo + 2 ^ b then ih hPf.1 hlo hm else ih hPf.2 (by omega) (by omega)
theorem allRange_eq_true {b n : ℕ} {f : ℕ → Bool} (hb : n ≤ 2 ^ b) (h : allRange b n f = true)
    {i : ℕ} (hi : i < n) : f i = true := by
  simpa only [natLtB_eq_true.mpr hi, Bool.cond_true] using allRangePow2_eq_true h (Nat.zero_le i)
      (by omega)
theorem clamp95_eval_194566 (isNN : Bool) : evenOctIdxT10K isNN 194566 = (190, 6, 8) ∧
    isClamp95Parts (190, 6, 8) = true ∧ (t11OfParts (190, 6, 8)).testBit 9 = false := by
  cases isNN <;> exact ⟨rfl, rfl, rfl⟩
theorem clamp95_eval_195075 (isNN : Bool) : evenOctIdxT10K isNN 195075 = (190, 515, 8) ∧
    isClamp95Parts (190, 515, 8) = true ∧ (t11OfParts (190, 515, 8)).testBit 9 = true := by
  cases isNN <;> exact ⟨rfl, rfl, rfl⟩
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
end

noncomputable section
set_option exponentiation.threshold 512
section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (zLeB natLeB natLtB)
def mulCeil24 (a b : ℕ) : ℕ := (a * b + 999999999999999999999999) / 1000000000000000000000000
def stepExp200 (a : ℕ) : ℕ := (a * 995012480 + 999999999) / 1000000000
def powExp200Fast : ℕ → ℕ → ℕ
  | 0, _ => 1000000000000000000000000
  | fuel + 1, k =>
      let h := powExp200Fast fuel (k / 2); let h2 := mulCeil24 h h
      if k % 2 = 1 then stepExp200 h2 else h2
def d0ShellZ : ℤ := 20000000 * 80000001
def dropDenZ : ℤ := 24 * d0ShellZ ^ 4
def oneSubShellDropNum (A : ℕ) : ℤ :=
  let uNum : ℤ := if A = 0 then 0 else 31415926 * (4 * (A : ℤ) - 1)
  dropDenZ - 12 * uNum ^ 2 * d0ShellZ ^ 2 + uNum ^ 4
def logLb6Num (P Q : ℤ) : ℤ :=
    60 * P * Q ^ 5 - 30 * P ^ 2 * Q ^ 4 + 20 * P ^ 3 * Q ^ 3 - 15 * P ^ 4 * Q ^ 2 + 12 * P ^ 5 * Q -
    10 * P ^ 6
def checkNegExpZ (K P Q mNeg : ℕ) : Bool :=
  let lNum := logLb6Num P Q; let Qz : ℤ := Q
  zLeB (-10 * (K + 1 : ℤ) * lNum) (-3 * (mNeg : ℤ) * Qz ^ 6) && natLtB mNeg 65536
def distCenter (j : ℕ) : ℕ := if j < 20000000 then 20000000 - j else j - 20000000
def shellCard (A R : ℕ) : ℕ := if A = 0 then 2 * R - 1 else 2 * (R - A)
def outerCard (A : ℕ) : ℕ := if A = 0 then 40000001 else 40000002 - 2 * A
def evalShellSum : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], A, mLast => outerCard A * powExp200Fast 16 mLast
  | (R, mk) :: rest, A, mLast =>
      shellCard A R * powExp200Fast 16 mk + evalShellSum rest R mLast
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
end
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
open PhotochemistrySolution.GQSP PhotochemistrySolution.TightWalkCauchyA
  PhotochemistrySolution.TightWalkCauchyB PhotochemistrySolution.TightWalkCauchy
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (zLeB zLeB_eq_true natLeB
    natLeB_eq_true natLtB natLtB_eq_true)
lemma exp_neg_200th_le : Real.exp (-(1 / 200 : ℝ)) ≤ (995012480 : ℝ) / 1000000000 := by
  by_contra! hlt
  have hpow : (Real.exp (-(1 / 200 : ℝ))) ^ 200 = (Real.exp 1)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
  linarith [hpow, pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 200 ≠ 0),
    ((inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr (by linarith [Real.exp_one_gt_d9] :
      (2718281827 : ℝ) / 10 ^ 9 ≤
          Real.exp 1)).trans (by norm_num : _ ≤ ((995012480 : ℝ) / 1000000000) ^ 200)]
lemma mulCeil24_ge (a b : ℕ) : ((a : ℝ) / 10 ^ 24) * ((b : ℝ) / 10 ^ 24) ≤ (mulCeil24 a b : ℝ) /
    10 ^ 24 := by
  have hr : (a : ℝ) * b ≤ mulCeil24 a b * 10 ^ 24 := by
    exact_mod_cast (by unfold mulCeil24; omega : a * b ≤ mulCeil24 a b * 10 ^ 24)
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
lemma stepExp200_ge (a : ℕ) : ((a : ℝ) / 10 ^ 24) * ((995012480 : ℝ) / 1000000000) ≤
    (stepExp200 a : ℝ) / 10 ^ 24 := by
  have hr : (a : ℝ) * 995012480 ≤ (stepExp200 a : ℝ) * 1000000000 := by
    exact_mod_cast (by unfold stepExp200; omega : a * 995012480 ≤ stepExp200 a * 1000000000)
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
theorem exp_neg_div200_le_powExp200Fast :
    ∀ (fuel k : ℕ), k < 2 ^ fuel →
      Real.exp (-(k : ℝ) / 200) ≤ (powExp200Fast fuel k : ℝ) / 10 ^ 24
  | 0, k, hk => by cases Nat.lt_one_iff.mp hk; norm_num [powExp200Fast]
  | fuel + 1, k, hk => by
      have ih := exp_neg_div200_le_powExp200Fast fuel (k / 2) (by rw [pow_succ'] at hk; omega)
      have hsq := (mul_le_mul ih ih (Real.exp_pos _).le (by positivity)).trans (mulCeil24_ge _ _)
      dsimp only [powExp200Fast]; by_cases hm : k % 2 = 1
      · have hcast : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) + 1 := by
          exact_mod_cast (by omega : k = 2 * (k / 2) + 1)
        simp only [hm, ↓reduceIte, show -(k : ℝ) / 200 =
          (-((k / 2 : ℕ) : ℝ) / 200 + -((k / 2 : ℕ) : ℝ) / 200) + -(1 / 200 : ℝ) by linarith,
              Real.exp_add]
        exact (mul_le_mul hsq exp_neg_200th_le (Real.exp_pos _).le (by positivity)).trans
            (stepExp200_ge _)
      · have hcast : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : k = 2 * (k / 2))
        simpa only [hm, ↓reduceIte, show -(k : ℝ) / 200 =
          -((k / 2 : ℕ) : ℝ) / 200 + -((k / 2 : ℕ) : ℝ) / 200 by linarith, Real.exp_add] using hsq
def logLb6 (x : ℝ) : ℝ := x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5 - x ^ 6 / 6
lemma logLb6_le_log {x : ℝ} (hx : 0 ≤ x) : logLb6 x ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun t ↦ Real.log (1 + t) - logLb6 t
  have hderiv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt g (t ^ 6 / (1 + t)) t := by
    have h1t : 1 + t ≠ 0 := by linarith only [ht]
    have hlogd : HasDerivAt (fun u ↦ Real.log (1 + u)) (1 / (1 + t)) t := by
      simpa using ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).log h1t
    exact (hlogd.sub (show HasDerivAt logLb6 _ t from
      ((((((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3)).sub ((hasDerivAt_pow 4 t).div_const 4)).add
        ((hasDerivAt_pow 5 t).div_const 5)).sub ((hasDerivAt_pow 6 t).div_const 6)))).congr_deriv
      (by field_simp [h1t]; ring)
  have hg0 : g 0 ≤ g x := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht ↦ div_nonneg (pow_nonneg (interior_subset ht) 6)
      (by linarith [show (0 : ℝ) ≤ t from interior_subset ht]))
    (le_rfl : (0 : ℝ) ∈ Set.Ici 0) (Set.mem_Ici.mpr hx) hx
  linarith [hg0, show g 0 = 0 by norm_num [g, logLb6]]
lemma oneSubShellDrop_eq (A : ℕ) : 1 - shellDrop A = (oneSubShellDropNum A : ℝ) / (dropDenZ : ℝ)
    := by
  unfold shellDrop oneSubShellDropNum dropDenZ d0ShellZ
  cases A <;> simp only [Nat.succ_ne_zero, ↓reduceIte] <;> push_cast <;>
    field_simp [show (20000000 * 80000001 : ℝ) ≠ 0 by norm_num] <;> ring
lemma logLb6_rat_eq {P Q : ℕ} (hQ : 0 < Q) : logLb6 ((P : ℝ) / (Q : ℝ)) = (logLb6Num P Q : ℝ) /
    (60 * (Q : ℝ) ^ 6) := by
  unfold logLb6 logLb6Num; push_cast; field_simp [Nat.cast_ne_zero.mpr hQ.ne']; ring
lemma neg_exp_of_checkZ {K P Q mNeg : ℕ} (hQ : 0 < Q) (hchk : checkNegExpZ K P Q mNeg = true) :
    mNeg < 65536 ∧ -(((K + 1 : ℕ) : ℝ) * logLb6 ((P : ℝ) / (Q : ℝ))) ≤ -(mNeg : ℝ) / 200 := by
  simp only [checkNegExpZ, Bool.and_eq_true, zLeB_eq_true, natLtB_eq_true] at hchk
  have hineqR := (Int.cast_le (R := ℝ)).mpr hchk.1
  push_cast at hineqR
  refine ⟨hchk.2, ?_⟩; rw [logLb6_rat_eq hQ, ← sub_nonpos]
  refine nonpos_of_mul_nonpos_left ?_ (by positivity : (0 : ℝ) < 600 * (Q : ℝ) ^ 6)
  push_cast; field_simp [Nat.cast_ne_zero.mpr hQ.ne']; linarith
lemma le_distCenter_iff {A j : ℕ} (hA : A ≤ 20000000) : A ≤ distCenter j ↔ (j ≤ 20000000 - A ∨
    20000000 + A ≤ j) := by unfold distCenter; split_ifs <;> omega
def shellUpperFn : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℝ
  | [], A, mLast, j =>
      if A ≤ distCenter j ∧ j < 40000001 then (powExp200Fast 16 mLast : ℝ) / 10 ^ 24 else 0
  | (R, mk) :: rest, A, mLast, j =>
      (if A ≤ distCenter j ∧ distCenter j < R ∧ j < 40000001 then
        (powExp200Fast 16 mk : ℝ) / 10 ^ 24
       else 0) + shellUpperFn rest R mLast j
lemma shellUpperFn_nonneg (shells : List (ℕ × ℕ)) (A mLast j : ℕ) : 0 ≤
    shellUpperFn shells A mLast j := by
  induction shells generalizing A with
  | nil => unfold shellUpperFn; split_ifs <;> positivity
  | cons hd rest ih =>
        unfold shellUpperFn; exact add_nonneg (by split_ifs <;> positivity) (ih hd.1)
lemma card_annulus_le {A R : ℕ} (hR0 : 0 < R) (hAR : A ≤ R) (hR : R ≤ 20000000) :
    ((Finset.range 80000001).filter (fun j ↦ A ≤ distCenter j ∧ distCenter j < R ∧ j <
    40000001)).card ≤ shellCard A R := by
  unfold shellCard
  by_cases hA0 : A = 0
  · subst hA0
    refine (Finset.card_le_card (t := Finset.Icc (20000001 - R) (19999999 + R)) fun j hj ↦ ?_).trans
      (by simp [Nat.card_Icc]; omega)
    rcases Finset.mem_filter.mp hj with ⟨_, hj⟩
    unfold distCenter at hj; simp only [Finset.mem_Icc]; split_ifs at hj <;> omega
  · simp only [hA0, ↓reduceIte]
    refine (Finset.card_le_card (t := Finset.Ico (20000001 - R) (20000001 - A) ∪
        Finset.Ico (20000000 + A) (20000000 + R)) fun j hj ↦ ?_).trans
      ((Finset.card_union_le _ _).trans (by simp only [Nat.card_Ico]; omega))
    rcases Finset.mem_filter.mp hj with ⟨_, hj⟩
    unfold distCenter at hj; simp only [Finset.mem_union, Finset.mem_Ico]; split_ifs at hj <;>
        omega
lemma card_outer_le {A : ℕ} (hA : A ≤ 20000000) : ((Finset.range 80000001).filter (fun j ↦ A ≤
    distCenter j ∧ j < 40000001)).card ≤ outerCard A := by
  unfold outerCard
  by_cases hA0 : A = 0
  · subst hA0
    exact (Finset.card_le_card (t := Finset.range 40000001) fun j hj ↦
        Finset.mem_range.mpr (Finset.mem_filter.mp hj).2.2).trans (by simp)
  · simp only [hA0, ↓reduceIte]
    refine (Finset.card_le_card (t := Finset.Ico 0 (20000001 - A) ∪ Finset.Ico (20000000 +
        A) 40000001)
      fun j hj ↦
          ?_).trans ((Finset.card_union_le _ _).trans (by simp only [Nat.card_Ico]; omega))
    rcases Finset.mem_filter.mp hj with ⟨_, hj⟩
    unfold distCenter at hj; simp only [Finset.mem_union, Finset.mem_Ico]; split_ifs at hj <;>
        omega

lemma sum_Icc_split {a b c : ℕ} (f : ℕ → ℝ) (h1 : a ≤ b + 1) (h2 : b ≤ c) : ∑ n ∈ Finset.Icc a c,
    f n = (∑ n ∈ Finset.Icc a b, f n) + (∑ n ∈ Finset.Icc (b + 1) c, f n) := by
  rw [show Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega]
  exact Finset.sum_union (Finset.disjoint_left.mpr fun _ hx1 hx2 ↦ by
    simp only [Finset.mem_Icc] at hx1 hx2; omega)
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
end
end

set_option exponentiation.threshold 512
section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (zLeB natLeB natLtB)
/-- Exact integer shell exponent check for arbitrary `s <= (sNum : ℝ) / 10000`. -/
def checkShellExpZGen (sNum K P Q A mk : ℕ) : Bool :=
  let osNum := oneSubShellDropNum A; let lNum := logLb6Num P Q; let Pz : ℤ := P; let Qz : ℤ := Q;
  let lhs : ℤ := -((K + 1 : ℤ) * lNum * 10000 * (Qz + Pz) * dropDenZ) + (sNum : ℤ) * 30 * Qz ^ 5 *
      (2 * Pz * Qz + Pz ^ 2) *
      osNum; let rhs : ℤ := -(mk : ℤ) * 3000 * Qz ^ 6 * (Qz + Pz) * dropDenZ
  zLeB 0 osNum && zLeB lhs rhs && natLtB mk 65536
/-- Recursive shell list check parameterized by `sNum`. -/
def checkShellListGen (sNum K P Q : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], A, mLast =>
      natLeB A 20000000 && checkShellExpZGen sNum K P Q A mLast
  | (R, mk) :: rest, A, mLast =>
      natLtB 0 R && natLeB A R && natLeB R 20000000 &&
        checkShellExpZGen sNum K P Q A mk && checkShellListGen sNum K P Q rest R mLast
/-- Finite Cauchy segment check (`[K + 1, K + L]`) parameterized by `sNum`. -/
def checkSegFiniteGen (sNum K L P Q mLast mNeg seg_num : ℕ) (shells : List (ℕ × ℕ)) : Bool :=
  checkShellListGen sNum K P Q shells 0 mLast &&
  checkNegExpZ K P Q mNeg &&
  (let sum_nat := evalShellSum shells 0 mLast + 40000000 * powExp200Fast 16 mNeg
   let g_den := P * (Q + P) ^ (L - 1); let g_num := (Q + P) ^ L - Q ^ L
   natLeB (2 * (L * 80000001 * 10000 * g_den + sum_nat * g_num))
     (seg_num * 80000001 * 1000000 * g_den))
/-- Geometric tail Cauchy segment check (`[K + 1, kapteynTruncD]`) parameterized by `sNum`. -/
def checkSegTailGen (sNum K L P Q mLast mNeg seg_num : ℕ) (shells : List (ℕ × ℕ)) : Bool :=
  checkShellListGen sNum K P Q shells 0 mLast &&
  checkNegExpZ K P Q mNeg &&
  (let sum_nat := evalShellSum shells 0 mLast + 40000000 * powExp200Fast 16 mNeg
   natLeB (2 * (L * 80000001 * 10000 * P + sum_nat * (Q + P)))
     (seg_num * 80000001 * 1000000 * P))
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
end
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
open PhotochemistrySolution.GQSP PhotochemistrySolution.TightWalkCauchyA
  PhotochemistrySolution.TightWalkCauchyB PhotochemistrySolution.TightWalkCauchy
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (zLeB zLeB_eq_true natLeB
    natLeB_eq_true natLtB natLtB_eq_true)
theorem shell_exp_of_checkZGen {sNum K P Q A mk : ℕ} {s : ℝ} (_hP : 0 < P) (hQ : 0 < Q)
    (hs : s ≤ (sNum : ℝ) / 10000) (hchk : checkShellExpZGen sNum K P Q A mk = true) : mk <
    65536 ∧ -(((K + 1 : ℕ) : ℝ) * logLb6 ((P : ℝ) / (Q : ℝ))) + (s / 2) *
    ((((Q + P : ℕ) : ℝ) / (Q : ℝ)) - ((Q : ℝ) / ((Q + P : ℕ) : ℝ))) *
    (1 - shellDrop A) ≤ -(mk : ℝ) / 200 := by
  simp only [checkShellExpZGen, Bool.and_eq_true, zLeB_eq_true, natLtB_eq_true] at hchk
  rcases hchk with ⟨⟨hos, hineq⟩, hmk⟩
  have hQ0 : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hden0 : (0 : ℝ) < (dropDenZ : ℝ) := by norm_num [dropDenZ, d0ShellZ]
  have hrr : (((Q + P : ℕ) : ℝ) / (Q : ℝ)) - ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) =
      (2 * (P : ℝ) * (Q : ℝ) + (P : ℝ) ^ 2) / ((Q : ℝ) * ((Q + P : ℕ) : ℝ)) := by
    push_cast; field_simp [hQ0.ne', (by positivity : ((Q + P : ℕ) : ℝ) ≠ 0)]; ring
  refine ⟨hmk, (add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by linarith : s / 2 ≤ ((sNum : ℝ) / 10000) / 2) (by rw [hrr]; positivity))
    (oneSubShellDrop_eq A ▸ div_nonneg (by exact_mod_cast hos) hden0.le))).trans ?_⟩
  have hineqR := (Int.cast_le (R := ℝ)).mpr hineq
  push_cast at hineqR; rw [logLb6_rat_eq hQ, hrr, oneSubShellDrop_eq, ← sub_nonpos]
  refine nonpos_of_mul_nonpos_left ?_
      (by positivity : (0 : ℝ) < 600000 * (Q : ℝ) ^ 6 * ((Q : ℝ) + (P : ℝ)) * (dropDenZ : ℝ))
  push_cast; field_simp [hQ0.ne', (by positivity : (Q : ℝ) + (P : ℝ) ≠ 0), hden0.ne'];
      linarith
theorem sum_shellUpperFn_le_gen {sNum K P Q : ℕ} (shells : List (ℕ × ℕ)) (A mLast : ℕ)
    (hchk : checkShellListGen sNum K P Q shells A mLast = true) : (∑ j ∈ Finset.range 80000001,
    shellUpperFn shells A mLast j) ≤ (evalShellSum shells A mLast : ℝ) / 10 ^ 24 := by
  induction shells generalizing A with
  | nil =>
      simp only [checkShellListGen, Bool.and_eq_true, natLeB_eq_true] at hchk;
          unfold shellUpperFn evalShellSum
      have hs := sum_ite_le_mul_card (M := 80000001) (fun j ↦ A ≤ distCenter j ∧ j < 40000001)
        (by positivity : 0 ≤ (powExp200Fast 16 mLast : ℝ) / 10 ^ 24) (card_outer_le hchk.1)
      push_cast; linarith
  | cons hd rest ih =>
      rcases hd with ⟨R, mk⟩
      simp only [checkShellListGen, Bool.and_eq_true, natLtB_eq_true, natLeB_eq_true] at hchk
      rcases hchk with ⟨⟨⟨⟨hR0, hAR⟩, hR20⟩, _⟩, hrest⟩
      unfold shellUpperFn evalShellSum; rw [Finset.sum_add_distrib]
      have hs1 :=
          sum_ite_le_mul_card (M := 80000001) (fun j ↦ A ≤ distCenter j ∧ distCenter j < R ∧ j <
          40000001)
        (by positivity : 0 ≤ (powExp200Fast 16 mk : ℝ) / 10 ^ 24) (card_annulus_le hR0 hAR hR20)
      push_cast; linarith [ih R hrest]
theorem r_inv_pow_and_log_le {K P Q : ℕ} (hQ : 0 < Q) :
    0 ≤ ((Q + P : ℕ) : ℝ) / (Q : ℝ) - (Q : ℝ) / ((Q + P : ℕ) : ℝ) ∧
      ((K + 1 : ℕ) : ℝ) * logLb6 ((P : ℝ) / (Q : ℝ)) ≤ ((K + 1 : ℕ) : ℝ) *
          Real.log (((Q + P : ℕ) : ℝ) / (Q : ℝ)) ∧
      ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ (K + 1) = Real.exp (-(((K + 1 : ℕ) : ℝ) *
          Real.log (((Q + P : ℕ) : ℝ) / (Q : ℝ)))) := by
  have hQ0 : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hQP0 : (0 : ℝ) < ((Q + P : ℕ) : ℝ) := by positivity
  have hlog : logLb6 ((P : ℝ) / (Q : ℝ)) ≤ Real.log (((Q + P : ℕ) : ℝ) / (Q : ℝ)) :=
    (show ((Q + P : ℕ) : ℝ) / (Q : ℝ) = 1 + (P : ℝ) /
        (Q : ℝ) by push_cast; field_simp [hQ0.ne']) ▸ logLb6_le_log (by positivity)
  refine ⟨sub_nonneg.mpr ((div_le_div_iff₀ hQP0 hQ0).mpr
      (by exact_mod_cast Nat.mul_self_le_mul_self (Nat.le_add_right Q P))),
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (K + 1)), ?_⟩
  rw [← inv_div ((Q + P : ℕ) : ℝ) (Q : ℝ), inv_pow, ← Real.exp_log (pow_pos (div_pos hQP0 hQ0)
      (K + 1)), Real.log_pow, ← Real.exp_neg]
theorem circle_pt_one_le_gen {sNum K P Q A mk j : ℕ} {s : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hs0 : 0 ≤ s)
    (hs : s ≤ (sNum : ℝ) / 10000) (hA20 : A ≤ 20000000) (hj : j < 40000001) (hAd : A ≤ distCenter j)
    (hchk : checkShellExpZGen sNum K P Q A mk = true) : (((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ (K + 1)) *
    Real.exp ((s / 2) * ((((Q + P : ℕ) : ℝ) / (Q : ℝ)) - ((Q : ℝ) / ((Q + P : ℕ) : ℝ))) *
    Real.sin (2 * Real.pi * (j : ℝ) / 80000001)) ≤ (powExp200Fast 16 mk : ℝ) / 10 ^ 24 := by
  obtain ⟨hr_sub_nn, hmul_log, hpow_log⟩ := r_inv_pow_and_log_le (K := K) (P := P) hQ
  have hsinA : Real.sin (2 * Real.pi * (j : ℝ) / 80000001) ≤ 1 - shellDrop A := by
    rcases A.eq_zero_or_pos with rfl | hApos
    · simpa [shellDrop] using Real.sin_le_one (2 * Real.pi * (j : ℝ) / 80000001)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hApos.ne'
      simpa only [shellDrop, show max (0 : ℝ) (4 * ((k + 1 : ℕ) : ℝ) - 1) = 4 * ((k + 1 : ℕ) : ℝ) -
          1 by
        push_cast; exact max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) k])] using
        sin_upper_shell_le hj hA20 ((le_distCenter_iff hA20).mp hAd)
  obtain ⟨hmk16, hexp_le⟩ := shell_exp_of_checkZGen hP hQ hs hchk
  rw [hpow_log, ← Real.exp_add]
  refine (Real.exp_le_exp.mpr ?_).trans (exp_neg_div200_le_powExp200Fast 16 mk hmk16)
  linarith [hmul_log, hexp_le,
      mul_le_mul_of_nonneg_left hsinA (mul_nonneg (div_nonneg hs0 zero_le_two) hr_sub_nn)]
theorem circle_pt_le_shellUpperFn_gen {sNum K P Q : ℕ} {s : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hs0 : 0 ≤ s) (hs : s ≤ (sNum : ℝ) / 10000) (shells : List (ℕ × ℕ)) (A mLast j : ℕ)
    (hchk : checkShellListGen sNum K P Q shells A mLast = true) (hj : j < 40000001)
    (hAd : A ≤ distCenter j) : (((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ (K + 1)) * Real.exp ((s / 2) *
    ((((Q + P : ℕ) : ℝ) / (Q : ℝ)) - ((Q : ℝ) / ((Q + P : ℕ) : ℝ))) * Real.sin (2 * Real.pi *
    (j : ℝ) / 80000001)) ≤ shellUpperFn shells A mLast j := by
  induction shells generalizing A with
  | nil =>
      simp only [checkShellListGen, Bool.and_eq_true, natLeB_eq_true] at hchk
      simpa only [shellUpperFn, hAd, hj, and_self,
          ↓reduceIte] using circle_pt_one_le_gen hP hQ hs0 hs hchk.1 hj hAd hchk.2
  | cons hd rest ih =>
      rcases hd with ⟨R, mk⟩
      simp only [checkShellListGen, Bool.and_eq_true, natLtB_eq_true, natLeB_eq_true] at hchk
      rcases hchk with ⟨⟨⟨⟨_, hAR⟩, hR20⟩, hmkChk⟩, hrest⟩; unfold shellUpperFn
      by_cases hltR : distCenter j < R
      · simp only [hAd, hltR, hj, and_self, ↓reduceIte]
        linarith [circle_pt_one_le_gen hP hQ hs0 hs (hAR.trans hR20) hj hAd hmkChk,
            shellUpperFn_nonneg rest R mLast j]
      · simpa only [hltR, false_and, and_false, ↓reduceIte, zero_add] using ih R hrest (by omega)
theorem circle_avg_shells_le_gen {sNum K P Q mLast mNeg : ℕ} {shells : List (ℕ × ℕ)} {s : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hs0 : 0 ≤ s) (hs : s ≤ (sNum : ℝ) / 10000)
    (hshells : checkShellListGen sNum K P Q shells 0 mLast = true)
    (hneg : checkNegExpZ K P Q mNeg = true) :
    let r : ℝ := ((Q + P : ℕ) : ℝ) / (Q : ℝ); let r_inv : ℝ := (Q : ℝ) / ((Q + P : ℕ) : ℝ)
    (1 / (80000001 : ℝ)) * ∑ j ∈ Finset.range 80000001,
      r_inv ^ (K + 1) * Real.exp ((s / 2) * (r - r_inv) * Real.sin (2 * Real.pi * (j : ℝ) /
          80000001)) ≤
    ((evalShellSum shells 0 mLast + 40000000 * powExp200Fast 16 mNeg : ℕ) : ℝ) /
      (80000001 * (10 ^ 24 : ℝ)) := by
  intro r r_inv
  obtain ⟨hr_sub_nn, hmul_log, hpow_log⟩ := r_inv_pow_and_log_le (K := K) (P := P) hQ
  obtain ⟨hmN16, hmN_le⟩ := neg_exp_of_checkZ hQ hneg
  have hs1 := Finset.sum_le_sum fun j (hj : j ∈ Finset.range 80000001) ↦ show r_inv ^ (K + 1) *
      Real.exp ((s / 2) * (r - r_inv) * Real.sin (2 * Real.pi * (j : ℝ) / 80000001)) ≤
      shellUpperFn shells 0 mLast j + (if 40000001 ≤ j then (powExp200Fast 16 mNeg : ℝ) /
          10 ^ 24 else 0) by
    by_cases hhalf : 40000001 ≤ j
    · simp only [hhalf, ↓reduceIte]; dsimp only [r, r_inv]; rw [hpow_log, ← Real.exp_add]
      have hj1 : (40000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hhalf
      have hj2 : (j : ℝ) ≤ 80000000 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hnonpos :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (div_nonneg hs0 zero_le_two) hr_sub_nn)
        (sin_le_zero_of_mem_Icc_pi (φ := 2 * Real.pi * (j : ℝ) / 80000001)
          ((le_div_iff₀ (by norm_num : (0 : ℝ) < 80000001)).mpr
              (by nlinarith only [Real.pi_pos, hj1]))
          ((div_le_iff₀ (by norm_num : (0 : ℝ) < 80000001)).mpr
              (by nlinarith only [Real.pi_pos, hj2])))
      exact ((Real.exp_le_exp.mpr (by linarith only [hmul_log, hnonpos, hmN_le])).trans
        (exp_neg_div200_le_powExp200Fast 16 mNeg hmN16)).trans
            (by linarith [shellUpperFn_nonneg shells 0 mLast j])
    · simpa only [hhalf, ↓reduceIte, add_zero] using
        circle_pt_le_shellUpperFn_gen hP hQ hs0 hs shells 0 mLast j hshells (by omega)
            (Nat.zero_le _)
  rw [Finset.sum_add_distrib] at hs1
  have hsN := sum_ite_le_mul_card (M := 80000001) (fun j ↦ 40000001 ≤ j)
    (by positivity : 0 ≤ (powExp200Fast 16 mNeg : ℝ) / 10 ^ 24) (C := 40000000)
    (by simpa using card_filter_ge_nat 80000001 40000001 (by norm_num))
  exact (mul_le_mul_of_nonneg_left (hs1.trans (show _ ≤
      ((evalShellSum shells 0 mLast + 40000000 * powExp200Fast 16 mNeg : ℕ) : ℝ) / 10 ^ 24 by
    push_cast; linarith [sum_shellUpperFn_le_gen shells 0 mLast hshells, hsN]))
        (by positivity)).trans_eq (by ring)

theorem cauchy_seg_core_le_gen {sNum K L E P Q mLast mNeg : ℕ} {shells : List (ℕ × ℕ)} {s : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hKL : K + L ≤ kapteynTruncD)
    (hs0 : 0 ≤ s) (hs : s ≤ (sNum : ℝ) / 10000)
    (hs_arg : ∀ z_norm : ℝ,
      z_norm ≤ s * (((((Q + P : ℕ) : ℝ) / (Q : ℝ) + (Q : ℝ) / ((Q + P : ℕ) : ℝ)) / 2)) →
      5 * z_norm ≤ E)
    (hEN : E + 60 ≤ kapteynTruncD + 1)
    (hshells : checkShellListGen sNum K P Q shells 0 mLast = true)
    (hneg : checkNegExpZ K P Q mNeg = true) :
    let sum_nat := evalShellSum shells 0 mLast + 40000000 * powExp200Fast 16 mNeg;
    let S_avg : ℝ := (sum_nat : ℝ) / (80000001 * (10 ^ 24 : ℝ));
    let r_inv : ℝ := (Q : ℝ) / ((Q + P : ℕ) : ℝ)
    ∑ n ∈ Finset.Icc (K + 1) (K + L),
      ‖jacobiAngerTruncCoeff kapteynTruncD s n‖ ≤
    2 * ((L : ℝ) * ((1 : ℝ) / (10 ^ 20 : ℝ)) + S_avg * ∑ t ∈ Finset.range L, r_inv ^ t) := by
  intro sum_nat S_avg r_inv
  let D : ℕ := kapteynTruncD
  let r : ℝ := ((Q + P : ℕ) : ℝ) / (Q : ℝ)
  have hQP0 : (0 : ℝ) < ((Q + P : ℕ) : ℝ) := by positivity
  have hr_pos : 0 < r := div_pos hQP0 (Nat.cast_pos.mpr hQ)
  have hr_inv_eq : r⁻¹ = r_inv := inv_div _ _
  let M : ℕ := 2 * D + 1
  have hM_val : M = 80000001 := by norm_num [M, D, kapteynTruncD]
  let w : ℕ → ℂ := fun j ↦ (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I / (M : ℂ)) ^ j
  have hw_eq (j : ℕ) : w j = (r : ℂ) * Complex.exp (((2 * Real.pi * j / M : ℝ) : ℂ) * Complex.I)
      := by
    dsimp only [w]; rw [← Complex.exp_nat_mul]; congr 2; push_cast; ring
  have hw_norm (j : ℕ) : ‖w j‖ = r := by
    rw [hw_eq j, norm_mul, Complex.norm_of_nonneg hr_pos.le, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hw_norm_inv (j : ℕ) : ‖(w j)⁻¹‖ = r_inv := by rw [norm_inv, hw_norm j, hr_inv_eq]
  have h5norm (j : ℕ) : 5 * ‖-Complex.I * (s : ℂ) * ((w j + (w j)⁻¹) / 2)‖ ≤ E := hs_arg _ <| by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_of_nonneg hs0, norm_div,
        RCLike.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      ((norm_add_le _ _).trans_eq (by rw [hw_norm j, hw_norm_inv j])) zero_le_two) hs0
  have hre_exact (j : ℕ) : ‖Complex.exp (-Complex.I * (s : ℂ) * ((w j + (w j)⁻¹) / 2))‖ =
      Real.exp ((s / 2) * (r - r_inv) * Real.sin (2 * Real.pi * (j : ℝ) / (M : ℝ))) := by
    rw [hw_eq j, Complex.norm_exp]; congr 1
    set φ : ℝ := 2 * Real.pi * (j : ℝ) / (M : ℝ)
    have h2 : Complex.exp (-(φ : ℂ) * Complex.I) = (Real.cos φ : ℂ) - (Real.sin φ : ℂ) *
        Complex.I := by
      rw [show -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]; push_cast; ring
    rw [mul_inv, ← Complex.exp_neg, ← neg_mul, ← Complex.ofReal_inv, hr_inv_eq,
        Complex.exp_ofReal_mul_I φ, h2, div_eq_mul_inv]
    simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_im,
        Complex.add_im,
      Complex.sub_im, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im,
      show ((2 : ℂ)⁻¹).re = 1 / 2 by norm_num, show ((2 : ℂ)⁻¹).im = 0 by norm_num]; ring
  let S1 (m : ℕ) : ℝ := ∑ j ∈ Finset.range m,
    r_inv ^ (K + 1) * Real.exp ((s / 2) * (r - r_inv) * Real.sin (2 * Real.pi * (j : ℝ) / (m : ℝ)))
  have havg_K1 : (1 / (M : ℝ)) * S1 M ≤ S_avg :=
      hM_val ▸ circle_avg_shells_le_gen hP hQ hs0 hs hshells hneg
  have hpointwise (t : ℕ) (ht : t ∈ Finset.range L) :
      ‖jacobiAngerTruncCoeff D s (K + 1 + t)‖ ≤ 2 * ((1 : ℝ) / (10 ^ 20 : ℝ) + r_inv ^ t * S_avg)
          := by
    have hk1 : K + 1 + t = (K + t) + 1 := by omega
    rw [hk1, show jacobiAngerTruncCoeff D s ((K + t) + 1) = 2 * jacobiAngerLaurentCoeff D s ((K +
        t) + 1)
        by simp [jacobiAngerLaurentCoeff], ← hk1, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
      jacobiAngerLaurentCoeff_eq_discrete_cauchy D s hr_pos (Finset.mem_Icc.mpr
        ⟨by omega, by have := Finset.mem_range.mp ht; dsimp [D]; omega⟩),
      norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hM_pos : (0 : ℝ) < (M : ℝ) := by rw [hM_val]; norm_num
    refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_)
      (div_nonneg zero_le_one hM_pos.le)).trans ((show (1 / (M : ℝ)) *
        ((M : ℝ) * ((1 : ℝ) / (10 ^ 20 : ℝ)) + r_inv ^ t * S1 M) =
        (1 : ℝ) / (10 ^ 20 : ℝ) + r_inv ^ t * ((1 / (M : ℝ)) *
            S1 M) by field_simp [hM_pos.ne']).le.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left havg_K1 (by positivity))))) zero_le_two
    rw [show (M : ℝ) * ((1 : ℝ) / (10 ^ 20 : ℝ)) + r_inv ^ t * S1 M = ∑ j ∈ Finset.range M,
        ((1 : ℝ) / (10 ^ 20 : ℝ) + r_inv ^ t * (r_inv ^ (K + 1) * Real.exp ((s / 2) * (r - r_inv) *
          Real.sin (2 * Real.pi * (j : ℝ) / (M : ℝ))))) by
      simp only [S1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    set z := -Complex.I * (s : ℂ) * ((w j + (w j)⁻¹) / 2)
    rw [← sub_add_cancel (expTaylorC D z) (Complex.exp z), add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_pow, hw_norm_inv j]
      have hp := mul_le_mul_of_nonneg_right
        (Real.pow_div_factorial_le_exp (4 * ‖z‖) (by positivity) (D + 1)) (Real.exp_pos ‖z‖).le
      rw [mul_pow, ← Real.exp_add, show 4 * ‖z‖ + ‖z‖ = 5 * ‖z‖ by ring] at hp
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity)
        ((div_le_one hQP0).mpr (Nat.cast_le.mpr (Nat.le_add_right Q P)))) (norm_nonneg _)).trans
        ((mul_one _).le.trans ((norm_expTaylorC_sub_exp_le D z).trans ((show _ ≤
            Real.exp (5 * ‖z‖) / (4 : ℝ) ^ (D + 1) from
          (le_div_iff₀ (by positivity)).mpr ((le_of_eq (by ring)).trans hp)).trans
              (exp_div_four_pow_le (h5norm j) hEN))))
    · rw [norm_mul, norm_pow, hw_norm_inv j, pow_add, hre_exact j]; exact le_of_eq (by ring)
  rw [show Finset.Icc (K + 1) (K + L) = Finset.image (fun t ↦ K + 1 + t) (Finset.range L) by
      ext x; simpa only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range] using
        ⟨fun _ ↦ ⟨x - (K + 1), by omega, by omega⟩, fun ⟨_, _, _⟩ ↦ ⟨by omega, by omega⟩⟩,
    Finset.sum_image (fun _ _ _ _ h ↦ by omega)]
  exact (Finset.sum_le_sum hpointwise).trans_eq
    (by rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, ← Finset.sum_mul, mul_comm _ S_avg])
theorem geom_sum_r_inv_mul {P Q : ℕ} (L : ℕ) (hQP0 : (0 : ℝ) < ((Q + P : ℕ) : ℝ)) :
    ((P : ℝ) / ((Q + P : ℕ) : ℝ)) * ∑ t ∈ Finset.range L, ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ t = 1 -
        ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ L := by
  rw [← show 1 - (Q : ℝ) / ((Q + P : ℕ) : ℝ) = (P : ℝ) /
      ((Q + P : ℕ) : ℝ) by field_simp [hQP0.ne']; push_cast; ring]
  linarith [mul_geom_sum ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) L]
theorem seg_bound_of_natLe {L sum_nat g_num g_den seg_num : ℕ} {g_val : ℝ} (hd : 0 < g_den)
    (hg : g_val ≤ (g_num : ℝ) / (g_den : ℝ))
    (hnat : 2 * (L * 80000001 * 10000 * g_den + sum_nat * g_num) ≤ seg_num * 80000001 * 1000000 *
        g_den) :
    2 * ((L : ℝ) * ((1 : ℝ) / (10 ^ 20 : ℝ)) + ((sum_nat : ℝ) / (80000001 * (10 ^ 24 : ℝ))) *
        g_val) ≤ (seg_num : ℝ) / 10 ^ 18 := by
  have hd0 : (0 : ℝ) < (g_den : ℝ) := Nat.cast_pos.mpr hd
  have hr : ((2 * (L * 80000001 * 10000 * g_den + sum_nat * g_num) : ℕ) : ℝ) ≤
      ((seg_num * 80000001 * 1000000 * g_den : ℕ) : ℝ) := Nat.cast_le.mpr hnat
  push_cast at hr
  refine (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hg
      (by positivity))) zero_le_two).trans
    (le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 80000001 * (10 ^ 24 : ℝ) * (g_den : ℝ)))
  linarith [show (2 * ((L : ℝ) * ((1 : ℝ) / (10 ^ 20 : ℝ)) + ((sum_nat : ℝ) /
      (80000001 * (10 ^ 24 : ℝ))) * ((g_num : ℝ) / (g_den : ℝ)))) *
      (80000001 * (10 ^ 24 : ℝ) * (g_den : ℝ)) =
      2 * ((L : ℝ) * 80000001 * 10000 * (g_den : ℝ) + (sum_nat : ℝ) *
          (g_num : ℝ)) by field_simp [hd0.ne']; ring,
    show ((seg_num : ℝ) / 10 ^ 18) * (80000001 * (10 ^ 24 : ℝ) * (g_den : ℝ)) = (seg_num : ℝ) *
        80000001 * 1000000 * (g_den : ℝ) by ring]
theorem cauchy_seg_finite_le_gen {sNum K L E P Q mLast mNeg seg_num : ℕ} {shells : List (ℕ × ℕ)}
    {s : ℝ} (hL : 1 ≤ L) (hP : 0 < P) (hQ : 0 < Q) (hKL : K + L ≤ kapteynTruncD) (hs0 : 0 ≤ s)
    (hs : s ≤ (sNum : ℝ) / 10000) (hs_arg : ∀ z_norm : ℝ, z_norm ≤ s *
    (((((Q + P : ℕ) : ℝ) / (Q : ℝ) + (Q : ℝ) / ((Q + P : ℕ) : ℝ)) / 2)) → 5 * z_norm ≤ E)
    (hEN : E + 60 ≤ kapteynTruncD + 1)
    (hchk : checkSegFiniteGen sNum K L P Q mLast mNeg seg_num shells = true) : ∑ n ∈ Finset.Icc (K +
    1) (K + L), ‖jacobiAngerTruncCoeff kapteynTruncD s n‖ ≤ (seg_num : ℝ) / 10 ^ 18 := by
  simp only [checkSegFiniteGen, Bool.and_eq_true, natLeB_eq_true] at hchk
  rcases hchk with ⟨⟨hshells, hneg⟩, hnat⟩
  have hcore := cauchy_seg_core_le_gen hP hQ hKL hs0 hs hs_arg hEN hshells hneg
  dsimp only at hcore
  have hQP0 : (0 : ℝ) < ((Q + P : ℕ) : ℝ) := by positivity
  have hg_den : 0 < P * (Q + P) ^ (L - 1) := mul_pos hP (pow_pos (by omega) (L - 1))
  refine hcore.trans (seg_bound_of_natLe hg_den (le_of_eq ?_) hnat)
  rw [eq_div_iff (Nat.cast_pos.mpr hg_den).ne', Nat.cast_mul,
    Nat.cast_sub (Nat.pow_le_pow_left (Nat.le_add_right Q P) L), Nat.cast_pow, Nat.cast_pow,
        Nat.cast_pow,
    show (∑ t ∈ Finset.range L, ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ t) *
        ((P : ℝ) * ((Q + P : ℕ) : ℝ) ^ (L - 1)) =
      (((P : ℝ) / ((Q + P : ℕ) : ℝ)) * ∑ t ∈ Finset.range L, ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ t) *
        (((Q + P : ℕ) : ℝ) ^ (L - 1) * ((Q + P : ℕ) : ℝ)) by field_simp [hQP0.ne'], ← pow_succ,
    Nat.sub_add_cancel hL, geom_sum_r_inv_mul L hQP0, div_pow, sub_mul, one_mul,
        div_mul_cancel₀ _ (pow_ne_zero L hQP0.ne')]
theorem cauchy_seg_tail_le_gen {sNum K L E P Q mLast mNeg seg_num : ℕ} {shells : List (ℕ × ℕ)}
    {s : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hKL : K + L = kapteynTruncD) (hs0 : 0 ≤ s)
    (hs : s ≤ (sNum : ℝ) / 10000) (hs_arg : ∀ z_norm : ℝ, z_norm ≤ s *
    (((((Q + P : ℕ) : ℝ) / (Q : ℝ) + (Q : ℝ) / ((Q + P : ℕ) : ℝ)) / 2)) → 5 * z_norm ≤ E)
    (hEN : E + 60 ≤ kapteynTruncD + 1)
    (hchk : checkSegTailGen sNum K L P Q mLast mNeg seg_num shells = true) : ∑ n ∈ Finset.Icc (K +
    1) kapteynTruncD, ‖jacobiAngerTruncCoeff kapteynTruncD s n‖ ≤ (seg_num : ℝ) / 10 ^ 18 := by
  simp only [checkSegTailGen, Bool.and_eq_true, natLeB_eq_true] at hchk
  rcases hchk with ⟨⟨hshells, hneg⟩, hnat⟩
  have hcore := cauchy_seg_core_le_gen hP hQ hKL.le hs0 hs hs_arg hEN hshells hneg
  dsimp only at hcore; rw [hKL] at hcore
  have hQP0 : (0 : ℝ) < ((Q + P : ℕ) : ℝ) := by positivity
  refine hcore.trans (seg_bound_of_natLe hP ((le_div_iff₀ (Nat.cast_pos.mpr hP)).mpr ?_) hnat)
  have hmul : ((P : ℝ) / ((Q + P : ℕ) : ℝ)) * ∑ t ∈ Finset.range L,
      ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ t ≤ 1 := by
    linarith [geom_sum_r_inv_mul L hQP0, show (0 : ℝ) ≤
        ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ L by positivity]
  linarith [mul_le_mul_of_nonneg_right hmul hQP0.le,
    show (((P : ℝ) / ((Q + P : ℕ) : ℝ)) * ∑ t ∈ Finset.range L, ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ t) *
        ((Q + P : ℕ) : ℝ) =
      (∑ t ∈ Finset.range L, ((Q : ℝ) / ((Q + P : ℕ) : ℝ)) ^ t) * (P : ℝ) by field_simp [hQP0.ne']]
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkCauchy54
end
end


noncomputable section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.KinB
open scoped Matrix.Norms.L2Operator Circuit.Notation Fin.CommRing
open Operator QProg Matrix Qubit WithLp Circuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
def AndBracketProg.onRegister {M n : ℕ} (r : QRegister M n) : AndBracketProg M → AndBracketProg n
  | .id => .id
  | .prim c => .prim (c.onRegister r)
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc)
        (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
        (body.onRegister r)
@[simp] theorem AndBracketProg.toCircuit_onRegister {M n : ℕ} (r : QRegister M n)
    (p : AndBracketProg M) :
    (p.onRegister r).toCircuit = p.toCircuit.onRegister r := by
  induction p with
  | id | prim _ => rfl
  | seq _ _ ih₁ ih₂ =>
        simp only [AndBracketProg.onRegister, AndBracketProg.toCircuit, Circuit.onRegister, ih₁,
        ih₂]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a _ ih =>
      simp only [AndBracketProg.onRegister, AndBracketProg.toCircuit, Circuit.onRegister, ih,
          Circuit.TOFF,
        show r.compose (QRegister.triple c₁ c₂ anc h₁₂ h₁a h₂a) = QRegister.triple (r c₁) (r c₂)
            (r anc) (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a)
            (r.wires.injective.ne h₂a) by ext i; fin_cases i <;> rfl]
@[simp] theorem AndBracketProg.numTempAnd_onRegister {M n : ℕ} (r : QRegister M n)
    (p : AndBracketProg M) :
    (p.onRegister r).numTempAnd = p.numTempAnd := by
  induction p with
  | id | prim _ => rfl
  | seq _ _ ih₁ ih₂ => simp only [AndBracketProg.onRegister, AndBracketProg.numTempAnd, ih₁, ih₂]
  | tempAnd _ _ _ _ _ _ _ ih => simp only [AndBracketProg.onRegister, AndBracketProg.numTempAnd, ih]
theorem AndBracketProg.IsCliffordPrim.onRegister {M n : ℕ} (r : QRegister M n)
    {p : AndBracketProg M} (hp : p.IsCliffordPrim) : (p.onRegister r).IsCliffordPrim := by
  induction p with
  | id => trivial
  | prim c =>
        exact ⟨(Circuit.count_onRegister .T r c).trans hp.1,
        (Circuit.count_onRegister .TOFF r c).trans hp.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact ih hp
theorem embedMatrix_diagonal_mulVec_ket {M n : ℕ} (r : QRegister M n)
    (d : Fin (2 ^ M) → ℂ) (β : BitAssignment n) :
    (r.embedMatrix (Matrix.diagonal d)).mulVec (ket β) =
      d (r.extractIndex ((basisBitsEquiv n).symm β)) • ket β := by
  let idx := (basisBitsEquiv n).symm β
  change r.embedMatrix (Matrix.diagonal d) *ᵥ basisState idx =
      d (r.extractIndex idx) • basisState idx
  funext outIdx
  rw [r.embedMatrix_mulVec_apply, Finset.sum_eq_single (r.extractIndex outIdx) (fun _ _ hb ↦ by
      rw [Matrix.diagonal_apply_ne _ hb.symm, zero_mul]) (fun hm ↦ (hm (Finset.mem_univ _)).elim),
    show r.basisSplitEquiv.symm (r.extractIndex outIdx, (r.basisSplitEquiv outIdx).2) =
      outIdx from r.basisSplitEquiv.symm_apply_apply outIdx,
    Matrix.diagonal_apply_eq, Pi.smul_apply, smul_eq_mul]
  by_cases hout : outIdx = idx <;> simp [hout, basisState]
theorem cleanProj_image_eq_embedMatrix {M n : ℕ} (r : QRegister M n) (S : Finset (Wire M)) :
    cleanProj (S.image r.wires) = r.embedMatrix (cleanProj S) := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [cleanProj_mulVec_ket, cleanProj, embedMatrix_diagonal_mulVec_ket]
  simp only [Finset.forall_mem_image, fun u ↦ ((QRegExt.basisBits_extractIdx r) _ u).trans
    (congrFun ((basisBitsEquiv n).apply_symm_apply β) (r u))]
  split_ifs <;> first | exact (one_smul ℂ _).symm | exact (zero_smul ℂ _).symm
def ValidCleanBracket {M : ℕ} (S : Finset (Wire M)) : AndBracketProg M → Prop
  | .id => True
  | .prim c => cleanProj S * (c.eval.1 * cleanProj S) = c.eval.1 * cleanProj S
  | .seq p₁ p₂ => ValidCleanBracket S p₁ ∧ ValidCleanBracket S p₂
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      anc ∈ S ∧
      ValidCleanBracket (S.erase anc) body ∧
      body.toCircuit.eval.1 * andInvProj c₁ c₂ anc =
        andInvProj c₁ c₂ anc * body.toCircuit.eval.1 ∧
      cleanProj S *
          (((AndBracketProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit).eval.1 * cleanProj S) =
        ((AndBracketProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit).eval.1 * cleanProj S
theorem ValidCleanBracket.realizesOnClean_onRegister {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] (v : Var) (r : QRegister M n) {S : Finset (Wire M)}
    {p : AndBracketProg M} (hp : ValidCleanBracket S p) :
    AndBracketProg.RealizesOnClean v (S.image r.wires) (p.onRegister r) := by
  induction p generalizing S with
  | id => exact AndBracketProg.RealizesOnClean.id v _
  | prim c =>
      apply AndBracketProg.RealizesOnClean.prim
      rw [cleanProj_image_eq_embedMatrix, Circuit.eval_onRegister, QRegister.embedUnitary_val,
          ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
      exact congrArg r.embedMatrix hp
  | seq _ _ ih₁ ih₂ => exact AndBracketProg.RealizesOnClean.seq (ih₁ hp.1) (ih₂ hp.2)
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      rcases hp with ⟨hanc, hbody, hcomm, hpresS⟩
      have himg_erase : (S.image r.wires).erase (r anc) = (S.erase anc).image r.wires := by
        ext w
        simp only [Finset.mem_erase, Finset.mem_image]
        exact ⟨fun ⟨hne, u, hu, hru⟩ ↦ ⟨u, ⟨fun h ↦ hne (hru ▸ congrArg r.wires h), hu⟩, hru⟩,
            fun ⟨u, ⟨hne, hu⟩, hru⟩ ↦ ⟨fun h ↦ hne (r.wires.injective (hru.trans h)), u, hu, hru⟩⟩
      apply AndBracketProg.RealizesOnClean.tempAnd (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)
          (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
          (Finset.mem_image_of_mem r.wires hanc)
      · exact himg_erase ▸ ih hbody
      · have hand : andInvProj (r c₁) (r c₂) (r anc) = r.embedMatrix (andInvProj c₁ c₂ anc) :=
          matrix_ext_ket fun β ↦ by
            rw [andInvProj_mulVec_ket, andInvProj, embedMatrix_diagonal_mulVec_ket]
            simp only [fun u ↦ ((QRegExt.basisBits_extractIdx r) _ u).trans
              (congrFun ((basisBitsEquiv n).apply_symm_apply β) (r u))]
            split_ifs <;> first | exact (one_smul ℂ _).symm | exact (zero_smul ℂ _).symm
        rw [AndBracketProg.toCircuit_onRegister, Circuit.eval_onRegister,
          QRegister.embedUnitary_val, hand, ← QRegister.embedMatrix_mul,
          ← QRegister.embedMatrix_mul]
        exact congrArg r.embedMatrix hcomm
      · have htc := AndBracketProg.toCircuit_onRegister r (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body)
        dsimp only [AndBracketProg.onRegister] at htc
        rw [htc, cleanProj_image_eq_embedMatrix, Circuit.eval_onRegister,
            QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
        exact congrArg r.embedMatrix hpresS
theorem cleanProj_range_eq_basisOutcomeProjector_zero {w n : ℕ} (sub : QRegister w n) :
    cleanProj (Finset.univ.image sub.wires) = sub.basisOutcomeProjector 0 := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [cleanProj_mulVec_ket, SelectRefl.ket_basisOutcomeProjector_zero sub β]
  simp only [Finset.forall_mem_image, Finset.mem_univ, forall_true_left]
theorem cleanWorkStep_of_realizesOnClean {Var : Type} [Fintype Var] [DecidableEq Var] {n w : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rWork : QRegister w n) (p : AndBracketProg n)
    (hp : AndBracketProg.RealizesOnClean v (Finset.univ.image rWork.wires) p)
    (hcomm : p.toCircuit.eval.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 *
    p.toCircuit.eval.1) : CleanWorkStep rWork p.toCircuit.eval (p.toDyn v) := by
  refine ⟨hcomm, fun M ↦ ?_⟩
  have hconst (q : AndBracketProg n) (M : Observable (Fin (2 ^ n))) :
      ∃ N : Observable (Fin (2 ^ n)), wp (q.toDyn v).compile (fun _ ↦ M) = fun _ ↦ N := by
    induction q generalizing M with
    | id => exact ⟨M, rfl⟩
    | prim c => exact ⟨qAssign_obs_map c.eval M, wp_circuit_constObservable c M⟩
    | seq p₁ p₂ ih₁ ih₂ =>
        rcases ih₂ M with ⟨N₂, h₂⟩
        rcases ih₁ N₂ with ⟨N₁, h₁⟩
        exact ⟨N₁, (congrArg (wp (p₁.toDyn v).compile) h₂).trans h₁⟩
    | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
        let u := andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a
        let N_u := wp u.compile (fun _ ↦ M) (fun _ ↦ (0 : ℤ))
        have hu : wp u.compile (fun _ ↦ M) = fun _ ↦ N_u := funext fun _ ↦ Subtype.ext <| by
          dsimp only [u, N_u, andUncomputeDyn]
          rw [DynCircExt.gad_wp_andUncompute_apply_assertion,
            DynCircExt.gad_wp_andUncompute_apply_assertion]
        rcases ih N_u with ⟨N_b, hb⟩
        change ∃ N, wp (DynamicCircuit.circuit _).compile
          (wp (body.toDyn v).compile (wp u.compile (fun _ ↦ M))) = fun _ ↦ N
        rw [hu, hb]
        exact ⟨_, wp_circuit_constObservable _ N_b⟩
  rcases hconst p M with ⟨N, hN⟩
  have h := hp.2.2 (fun _ ↦ M) (fun _ _ ↦ rfl) (fun _ ↦ (0 : ℤ))
  have hs : star p.toCircuit.eval.1 = p.toCircuit.eval.1ᴴ := rfl
  rw [cleanProj_range_eq_basisOutcomeProjector_zero rWork, hN] at h
  exact ⟨N, hN, by simpa [wpQAssignCompat, hs, Matrix.conjTranspose_conjTranspose] using h.symm⟩
inductive ComputeProg (M : ℕ) where
  | id : ComputeProg M
  | x (w : Wire M) : ComputeProg M
  | cnot (c t : Wire M) (h : c ≠ t) : ComputeProg M
  | andGate (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : ComputeProg M
  | seq (p₁ p₂ : ComputeProg M) : ComputeProg M
namespace ComputeProg
def wrap {M : ℕ} : ComputeProg M → AndBracketProg M → AndBracketProg M
  | .id, mid => mid
  | .x w, mid => .seq (.prim (.X w)) (.seq mid (.prim (.X w)))
  | .cnot c t h, mid => .seq (.prim (.CNOT c t h)) (.seq mid (.prim (.CNOT c t h)))
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a, mid => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a mid
  | .seq p₁ p₂, mid => p₁.wrap (p₂.wrap mid)
def numAnd {M : ℕ} : ComputeProg M → ℕ
  | .id => 0
  | .x _ => 0
  | .cnot _ _ _ => 0
  | .andGate _ _ _ _ _ _ => 1
  | .seq p₁ p₂ => p₁.numAnd + p₂.numAnd
@[simp] theorem wrap_numTempAnd {M : ℕ} (p : ComputeProg M) (mid : AndBracketProg M) :
    (p.wrap mid).numTempAnd = p.numAnd + mid.numTempAnd := by
  induction p generalizing mid with
  | id | x _ | cnot _ _ _ | andGate _ _ _ _ _ _ => simp [wrap, numAnd, AndBracketProg.numTempAnd]
  | seq _ _ ih₁ ih₂ => simp only [wrap, numAnd, ih₁, ih₂, Nat.add_assoc]
theorem wrap_isCliffordPrim {M : ℕ} (p : ComputeProg M) {mid : AndBracketProg M}
    (hmid : mid.IsCliffordPrim) : (p.wrap mid).IsCliffordPrim := by
  induction p generalizing mid with
  | id | andGate _ _ _ _ _ _ => exact hmid
  | x _ | cnot _ _ _ => exact ⟨⟨rfl, rfl⟩, hmid, ⟨rfl, rfl⟩⟩
  | seq _ _ ih₁ ih₂ => exact ih₁ (ih₂ hmid)
def fwdBits {M : ℕ} : ComputeProg M → BitAssignment M → BitAssignment M
  | .id, β => β
  | .x w, β => Function.update β w (β w + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .andGate c₁ c₂ anc _ _ _, β => Function.update β anc (β anc + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.fwdBits (p₁.fwdBits β)
def DisjointFrom {M : ℕ} (T : Finset (Wire M)) : ComputeProg M → Prop
  | .id => True
  | .x w => w ∉ T
  | .cnot c t _ => c ∉ T ∧ t ∉ T
  | .andGate c₁ c₂ anc _ _ _ => c₁ ∉ T ∧ c₂ ∉ T ∧ anc ∉ T
  | .seq p₁ p₂ => DisjointFrom T p₁ ∧ DisjointFrom T p₂
theorem ket_wrap_computeProg {M : ℕ} (T : Finset (Wire M)) (p : ComputeProg M)
    (mid : AndBracketProg M) (midOut : BitAssignment M → BitAssignment M) (hp : p.DisjointFrom T)
    (hmid : ∀ β : BitAssignment M, mid.toCircuit.eval.1.mulVec (ket β) = ket (midOut β))
    (hout : ∀ (β : BitAssignment M) (w : Wire M), w ∉ T → midOut β w = β w) (β : BitAssignment M) :
    ((p.wrap mid).toCircuit).eval.1.mulVec (ket β) =
    ket (fun w ↦ if w ∈ T then midOut (p.fwdBits β) w else β w) := by
  have hupd : ∀ {γ : BitAssignment M} {mOut : BitAssignment M → BitAssignment M}
      (htOut : ∀ δ w, w ∉ T → mOut δ w = δ w) (u : Wire M) (hu : u ∉ T) (d d' : ZMod 2), d' = d →
      Function.update (mOut (Function.update γ u (γ u + d))) u (mOut (Function.update γ u (γ u +
          d)) u + d') = fun w ↦ if w ∈ T then mOut (Function.update γ u (γ u + d)) w else γ w := by
    intro γ mOut htOut u hu d d' hd
    funext w
    change _ = if w ∈ T then mOut (Function.update γ u (γ u + d)) w else γ w
    rcases eq_or_ne w u with rfl | hne
    · rw [Function.update_self, ite_eq_right hu, htOut _ w hu, Function.update_self, hd, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
    · by_cases hw : w ∈ T <;> simp [hw, Function.update_of_ne hne, htOut]
  induction p generalizing mid midOut β with
  | id =>
      rw [wrap, hmid β]
      exact congrArg ket (funext fun w ↦ by by_cases hw : w ∈ T <;> simp [hw, fwdBits, hout])
  | x u =>
      simp only [wrap, AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul,
          ← Matrix.mulVec_mulVec, ket_X, hmid]
      exact congrArg ket (hupd hout u hp 1 1 rfl)
  | cnot c t hct =>
      simp only [wrap, AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul,
          ← Matrix.mulVec_mulVec, ket_CNOT, hmid]
      exact congrArg ket (hupd hout t hp.2 (β c) _ ((hout _ c hp.1).trans (Function.update_of_ne hct
          _ _)))
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      simp only [wrap, AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul,
          ← Matrix.mulVec_mulVec, ket_TOFF, hmid]
      exact congrArg ket (hupd hout anc hp.2.2 (β c₁ *
          β c₂) _ (congrArg₂ HMul.hMul ((hout _ c₁ hp.1).trans (Function.update_of_ne h₁a _ _))
          ((hout _ c₂ hp.2.1).trans (Function.update_of_ne h₂a _ _))))
  | seq p₁ p₂ ih₁ ih₂ =>
      let mid₂Out : BitAssignment M → BitAssignment M := fun γ w ↦
          if w ∈ T then midOut (p₂.fwdBits γ) w else γ w
      rw [wrap, ih₁ (p₂.wrap mid) mid₂Out hp.1 (fun γ ↦ ih₂ mid midOut hp.2 hmid hout γ)
          (fun _ _ hw ↦ ite_eq_right hw) β]
      exact congrArg ket (funext fun w ↦ by by_cases hw : w ∈ T <;> simp [hw, fwdBits, mid₂Out])
def finalClean {M : ℕ} (S : Finset (Wire M)) : ComputeProg M → Finset (Wire M)
  | .id => S
  | .x _ => S
  | .cnot _ _ _ => S
  | .andGate _ _ anc _ _ _ => S.erase anc
  | .seq p₁ p₂ => p₂.finalClean (p₁.finalClean S)
def ValidProg {M : ℕ} (T S : Finset (Wire M)) : ComputeProg M → Prop
  | .id => True
  | .x w => w ∉ T ∧ w ∉ S
  | .cnot c t _ => c ∉ T ∧ t ∉ T ∧ (t ∉ S ∨ c ∈ S)
  | .andGate c₁ c₂ anc _ _ _ => c₁ ∉ T ∧ c₂ ∉ T ∧ anc ∉ T ∧ anc ∈ S
  | .seq p₁ p₂ => ValidProg T S p₁ ∧ ValidProg T (p₁.finalClean S) p₂
theorem disjointFrom_of_validProg {M : ℕ} {T S : Finset (Wire M)} {p : ComputeProg M}
    (hp : p.ValidProg T S) : p.DisjointFrom T := by
  induction p generalizing S with
  | id => trivial
  | x _ => exact hp.1
  | cnot _ _ _ => exact ⟨hp.1, hp.2.1⟩
  | andGate _ _ _ _ _ _ => exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
end ComputeProg
end QuantumComputation.Specs.PhotochemistrySolution.KinB
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse

open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Stage1ZeroNEremSpec
  PhotochemistrySolution.ScreenFermatCore
theorem card_decodeFermatCell_split (u1 h1 h2 : ℕ) (s : ZeroNEremSector) :
    ((Finset.univ : Finset (Fin 1306588000)).filter (fun u ↦ decodeFermatCell u1 h1 h2 u.val =
    s)).card = ((Finset.univ : Finset (Fin (172032 * 4096))).filter (fun u ↦
    decodeFermatCell u1 h1 h2 u.val = s)).card +
    ((Finset.univ : Finset (Fin (90112 * 4096))).filter (fun u ↦
    decodeFermatCell u1 h1 h2 (704643072 + u.val) = s)).card +
    ((Finset.univ : Finset (Fin (3145728 * 64))).filter (fun u ↦
    decodeFermatCell u1 h1 h2 (1073741824 + u.val) = s)).card +
    ((Finset.univ : Finset (Fin 31519584)).filter (fun u ↦ decodeFermatCell u1 h1 h2 (1275068416 +
    u.val) = s)).card := by
  have s1 :=
      card_fin_add_filter (M := 172032 * 4096) (N := 601944928)
      (fun x ↦ decodeFermatCell u1 h1 h2 x = s)
  have s2 :=
      card_fin_add_filter (M := 90112 * 4096) (N := 232846176)
      (fun x ↦ decodeFermatCell u1 h1 h2 (704643072 + x) = s)
  have s3 :=
      card_fin_add_filter (M := 3145728 * 64) (N := 31519584)
      (fun x ↦ decodeFermatCell u1 h1 h2 (1073741824 + x) = s)
  simp only [(fun _ ↦ by omega : ∀ x : ℕ, 704643072 + (90112 * 4096 + x) = 1073741824 + x)] at s2
  simp only [(fun _ ↦ by omega : ∀ x : ℕ, 1073741824 + (3145728 * 64 + x) = 1275068416 + x)] at s3
  rw [Nat.add_assoc, Nat.add_assoc]
  exact s1.trans (congrArg₂ HAdd.hAdd rfl (s2.trans (congrArg₂ HAdd.hAdd rfl s3)))
theorem sum_enSlab_eq (u1 : ℕ) (s : ZeroNEremSector) : (∑ h1 : Fin 3, ∑ h2 : Fin 3,
    ((Finset.univ : Finset (Fin (3145728 * 64))).filter (fun u ↦
    decodeFermatCell u1 h1.val h2.val (1073741824 + u.val) = s)).card) = foldSum 3 fun h2 ↦
    foldSum 192 fun z1 ↦
    cond (eqSec (enCellFermat u1 h2 z1).1 s) (enCellFermat u1 h2 z1).2 0 +
    cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s)
    (3145728 - (enCellFermat u1 h2 z1).2) 0 := by
  rw [Finset.sum_comm, ← sum_fin_eq_foldSum 3]
  refine Finset.sum_congr rfl fun h2 _ ↦ ?_
  rw [← sum_h1_fin64]
  refine Finset.sum_congr rfl fun h1 _ ↦ ?_
  simp only [(fun r : Fin 64 ↦ by omega : ∀ r : Fin 64, (h1.val * 64 + r.val) / 64 = h1.val)]
  rw [← card_fin_div_lt_of_mod (M := 3145728) (B := 64) (Nat.succ_pos _)
      (fun r ↦ (enCellFermat u1 h2.val (h1.val * 64 + r)).1) (.kin (mkFin234 (47 + u1))
      (mkFin3 h1.val)) s
    (fun r ↦ (enCellFermat u1 h2.val (h1.val * 64 + r)).2) (fun _ _ ↦ by
      dsimp only [enCellFermat, tENFermat]
      exact cond_snd_le (cond_le (by omega) (cond_le (by omega) (by omega))) (by omega))]
  refine congrArg Finset.card (Finset.ext fun u ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hu := u.isLt
  have hb1 : Nat.blt (1073741824 + u.val) 704643072 = false := Bool.eq_false_iff.mpr fun h ↦
      absurd (Nat.blt_eq.mp h) (by omega)
  have hb2 : Nat.blt (1073741824 + u.val) 1073741824 = false := Bool.eq_false_iff.mpr fun h ↦
      absurd (Nat.blt_eq.mp h) (by omega)
  have hb3 : Nat.blt (1073741824 + u.val) 1275068416 = true := Nat.blt_eq.mpr (by omega)
  unfold decodeFermatCell
  simp only [hb1, hb2, hb3, Bool.cond_false, Bool.cond_true,
      (by omega : (1073741824 + u.val) % 64 = u.val % 64),
      (by omega : 1073741824 + u.val - 1073741824 = u.val)]
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end

section
set_option exponentiation.threshold 8192
section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectBase
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation Fin.CommRing
open Operator Matrix Qubit WithLp
theorem sequence_drop_ofFn_of_ge_local {n m : ℕ} (c : Fin m → Circuit n) {r : ℕ}
    (hr : m ≤ r) : Circuit.sequence ((List.ofFn c).drop r) = Circuit.identity := by
  have hnil : (List.ofFn c).drop r = [] := by rw [List.drop_eq_nil_iff, List.length_ofFn]; exact hr
  rw [hnil]; rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectBase
end
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase


section
namespace QuantumComputation.Specs.PhotochemistrySolution
open scoped Matrix.Norms.L2Operator Circuit.Notation
open Operator Matrix Qubit WithLp Circuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
noncomputable abbrev ketState {n : ℕ} (β : Wire n → ZMod 2) : StateVector n :=
    basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_symm_ket {q : ℕ} (β : Wire q → ZMod 2) :
    basisBits q ((basisBitsEquiv q).symm β) = β :=
  (basisBitsEquiv q).apply_symm_apply β
def regTail {n k : ℕ} (r : QRegister (k + 1) n) : QRegister k n where
  wires := ⟨fun i ↦ r i.succ, fun _ _ h ↦ Fin.succ_inj.mp (r.wires.injective h)⟩
@[simp] theorem regTail_apply {n k : ℕ} (r : QRegister (k + 1) n) (i : Fin k) :
    regTail r i = r i.succ := rfl
def regVal {n : ℕ} : ∀ (k : ℕ), QRegister k n → (Wire n → ZMod 2) → ℕ
  | 0, _, _ => 0
  | k + 1, r, β => (β (r 0)).val + 2 * regVal k (regTail r) β
theorem regVal_basisBits {n k : ℕ} (r : QRegister k n)
    (j : Fin (2 ^ n)) : regVal k r (basisBits n j) = (r.extractIndex j).val := by
  have hsum {m : ℕ} (s : QRegister m n) (β : Wire n → ZMod 2) :
      regVal m s β = ∑ i : Fin m, (β (s i)).val * 2 ^ i.val := by
    induction m with
    | zero => simp [regVal]
    | succ m ih =>
        rw [regVal, ih (regTail s), Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ', regTail_apply]
        exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
  rw [hsum, ← sum_basisBits_mul_two_pow k (r.extractIndex j)]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [QRegExt.basisBits_extractIdx]
theorem ketState_eq_tensorState_single {n b : ℕ} (r : QRegister b n) (y : Fin (2 ^ b))
    (env : r.Environment → ZMod 2) : ketState (basisBits n (r.basisSplitEquiv.symm (y, env))) =
    r.tensorState (basisState y) (Pi.single env 1) := by
  have hk : ketState (basisBits n (r.basisSplitEquiv.symm (y, env))) =
      basisState (r.basisSplitEquiv.symm (y, env)) :=
      congrArg basisState ((basisBitsEquiv n).symm_apply_apply _); rw [hk]; funext idx; unfold
      QRegister.tensorState basisState
  by_cases h : idx = r.basisSplitEquiv.symm (y, env)
  · subst h;
    have hext : r.extractIndex (r.basisSplitEquiv.symm (y, env)) = y :=
        congrArg Prod.fst (r.basisSplitEquiv.apply_symm_apply (y, env)); rw [Pi.single_eq_same,
        hext, r.basisSplitEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h]
    by_cases hy : r.extractIndex idx = y
    · rw [hy, Pi.single_eq_same, one_mul]
      have henv : (r.basisSplitEquiv idx).2 ≠ env := by
        intro heq; apply h; apply r.basisSplitEquiv.injective;
        rw [r.basisSplitEquiv.apply_symm_apply]; exact Prod.ext hy heq
      rw [Pi.single_eq_of_ne henv]
    · rw [Pi.single_eq_of_ne hy, zero_mul]
theorem tensorState_single_eq_sum {n b : ℕ} (r : QRegister b n) (φ : Fin (2 ^ b) → ℂ)
    (env : r.Environment → ZMod 2) : r.tensorState φ (Pi.single env 1) = ∑ y : Fin (2 ^ b),
    φ y • ketState (basisBits n (r.basisSplitEquiv.symm (y, env))) := by
  funext idx
  rw [Finset.sum_apply]
  unfold QRegister.tensorState
  by_cases henv : (r.basisSplitEquiv idx).2 = env
  · rw [henv, Pi.single_eq_same, mul_one,
      Finset.sum_eq_single (r.extractIndex idx) (fun y _ hy ↦ ?_)
          (fun h ↦ absurd (Finset.mem_univ _) h)]
    · simp [ketState_eq_tensorState_single, QRegister.tensorState, basisState, henv]
    · simp [ketState_eq_tensorState_single, QRegister.tensorState, basisState, Ne.symm hy]
  · simp [ketState_eq_tensorState_single, QRegister.tensorState, henv]
theorem eq_basisBits_basisSplitEquiv_symm {n b : ℕ} (r : QRegister b n) (y y' : Fin (2 ^ b))
    (env : r.Environment → ZMod 2) (β' : Wire n → ZMod 2)
    (hpres : ∀ w : Wire n, w ∉ Set.range r.wires → β' w = basisBits n (r.basisSplitEquiv.symm (y,
    env)) w) (hval : regVal b r β' = y'.val) : β' = basisBits n (r.basisSplitEquiv.symm (y', env))
    := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    have h2 : r.extractIndex ((basisBitsEquiv n).symm β') = y' :=
        Fin.ext
        (by rw [← regVal_basisBits r ((basisBitsEquiv n).symm β'), basisBits_symm_ket β', hval])
    rw [← QRegExt.basisBits_extractIdx r (r.basisSplitEquiv.symm (y', env)) i,
      show r.extractIndex (r.basisSplitEquiv.symm (y', env)) =
          y' from congrArg Prod.fst (r.basisSplitEquiv.apply_symm_apply (y', env)),
      ← h2, QRegExt.basisBits_extractIdx, basisBits_symm_ket]
  · rw [hpres w hw]
    exact congrFun ((congrArg Prod.snd (r.basisSplitEquiv.apply_symm_apply (y,
        env))).trans (congrArg Prod.snd (r.basisSplitEquiv.apply_symm_apply (y', env))).symm)
        ⟨w, hw⟩
theorem exp_two_pi_I_mod_div_two_pow (b m : ℕ) : Complex.exp (2 * Real.pi * Complex.I *
    (((m % 2 ^ b : ℕ) : ℝ) / (2 ^ b : ℝ))) = Complex.exp (2 * Real.pi * Complex.I *
    ((m : ℝ) / (2 ^ b : ℝ))) := by
  have hm : (m : ℂ) = 2 ^ b * (m / 2 ^ b : ℕ) + (m % 2 ^ b : ℕ) := by
    exact_mod_cast (Nat.div_add_mod m (2 ^ b)).symm
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((m : ℝ) / (2 ^ b : ℝ)) : ℂ) =
      (m / 2 ^ b : ℕ) * (2 * Real.pi * Complex.I) +
        2 * Real.pi * Complex.I * (((m % 2 ^ b : ℕ) : ℝ) / (2 ^ b : ℝ)) by
    push_cast
    field_simp [pow_ne_zero b (two_ne_zero : (2 : ℂ) ≠ 0)]
    rw [hm], Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, _root_.one_pow,
        one_mul]
theorem phaseGradientState_apply_main (b : ℕ) (y : Fin (2 ^ b)) : phaseGradientState b y =
    (1 / Real.sqrt (2 ^ b) : ℂ) * Complex.exp (-2 * Real.pi * Complex.I *
    ((y.val : ℝ) / (2 ^ b : ℝ))) := by
  simpa using PgBase.phaseGradientState_apply b y
theorem phaseGradientState_sub_shift_main (b : ℕ) (a y : Fin (2 ^ b)) : phaseGradientState b (y -
    a) = Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) / (2 ^ b : ℝ))) *
    phaseGradientState b y := by
  have h2 : (2 : ℂ) ^ b ≠ 0 := pow_ne_zero b two_ne_zero
  rw [phaseGradientState_apply_main, phaseGradientState_apply_main, mul_left_comm,
      ← Complex.exp_add]
  congr 1
  by_cases h : a.val ≤ y.val
  · congr 1
    rw [Fin.sub_val_of_le h, Nat.cast_sub h]
    push_cast
    field_simp [h2]
    ring
  · have hval : (y - a).val = 2 ^ b - a.val + y.val := by
      rw [Fin.sub_def]
      exact Nat.mod_eq_of_lt (by omega)
    rw [show -2 * (Real.pi : ℂ) * Complex.I * (((y - a).val : ℝ) / (2 ^ b : ℝ)) =
        (2 * Real.pi * Complex.I * ((a.val : ℝ) / (2 ^ b : ℝ)) +
          -2 * Real.pi * Complex.I * ((y.val : ℝ) / (2 ^ b : ℝ))) + -(2 * Real.pi * Complex.I) by
      rw [hval, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt a.isLt)]
      push_cast
      field_simp [h2]
      ring, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
end QuantumComputation.Specs.PhotochemistrySolution
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectArithSymSem
open scoped Circuit.Notation Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.SelectRefl
theorem regVal_congr {b d : ℕ} (r : QRegister b d) (β₁ β₂ : BitAssignment d)
    (h : ∀ i : Fin b, β₁ (r i) = β₂ (r i)) : regVal b r β₁ = regVal b r β₂ := by
  induction b with
  | zero => rfl
  | succ b ih => rw [regVal, regVal, h 0, ih (regTail r) (fun i ↦ h i.succ)]
end QuantumComputation.Specs.PhotochemistrySolution.SelectArithSymSem
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastRouterEval
open Operator QProg DynamicCircuit Matrix PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
theorem regVal_congr {d : ℕ} : ∀ {k : ℕ} (r : QRegister k d) (β₁ β₂ : BitAssignment d),
    (∀ i : Fin k, β₁ (r i) = β₂ (r i)) → regVal k r β₁ = regVal k r β₂ :=
  fun r β₁ β₂ h ↦ PhotochemistrySolution.SelectArithSymSem.regVal_congr r β₁ β₂ h
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastRouterEval
end
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
open scoped Circuit.Notation Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix Circuit Qubit QFT
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.QubitizationWalkSem
open PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
open PhotochemistrySolution.QubitizationKapteyn PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
open PhotochemistrySolution.SelectArithSymSem PhotochemistrySolution.SelectFastRouterEval
  PhotochemistrySolution.SelectDataBuilder
open PhotochemistrySolution.SelectFastRouterCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding ket ket_CNOT ket_TOFF ket_X
  matrix_ext_ket
def CommCleanBracket {M : ℕ} (S : Finset (Wire M)) : AndBracketProg M → Prop
  | .id => True
  | .prim c => c.eval.1 * cleanProj S = cleanProj S * c.eval.1
  | .seq p₁ p₂ => CommCleanBracket S p₁ ∧ CommCleanBracket S p₂
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      anc ∈ S ∧
      CommCleanBracket (S.erase anc) body ∧
      body.toCircuit.eval.1 * andInvProj c₁ c₂ anc =
        andInvProj c₁ c₂ anc * body.toCircuit.eval.1 ∧
      ((AndBracketProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit).eval.1 * cleanProj S =
        cleanProj S * ((AndBracketProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).toCircuit).eval.1

theorem cleanProj_mul_self {M : ℕ} (S : Finset (Wire M)) : cleanProj S * cleanProj S =
    cleanProj S := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  split_ifs with h
  · rw [cleanProj_mulVec_ket, ite_eq_left h]
  · rw [Matrix.mulVec_zero]
theorem unitary_inv_comm {d : ℕ} (U : Unitary (2 ^ d)) (Q : Operator (2 ^ d))
    (hcomm : U.1 * Q = Q * U.1) : U⁻¹.1 * Q = Q * U⁻¹.1 := by
  calc U⁻¹.1 * Q = U⁻¹.1 * (Q * (U.1 * U⁻¹.1)) := by
          rw [show U.1 * U⁻¹.1 = 1 from congrArg Subtype.val (mul_inv_cancel U), mul_one]
    _ = (U⁻¹.1 * U.1) * (Q * U⁻¹.1) := by
      rw [← Matrix.mul_assoc Q, ← hcomm, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Q * U⁻¹.1 := by
      rw [show U⁻¹.1 * U.1 = 1 from congrArg Subtype.val (inv_mul_cancel U), one_mul]

def zGateCirc {M : ℕ} (w : Wire M) : Circuit M := .seq (.H w) (.seq (.X w) (.H w))
theorem ket_zGateCirc {M : ℕ} (w : Wire M) (β : BitAssignment M) :
    (zGateCirc w).eval.1.mulVec (ket β) = QubitizationWalkSem.bitSign (β w) • ket β := by
  simp only [zGateCirc, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ket_H_apply w β,
    Matrix.mulVec_smul, Matrix.mulVec_add, PhotochemistrySolution.SelectSymDyn.ket_X_apply w,
    Function.update_self, Function.update_idem, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl,
        ket_H_apply w]
  have hsq : sqrtHalf ^ 2 = 1 / 2 := (pow_two sqrtHalf).trans sqrtHalf_mul_sqrtHalf
  have hup := Function.update_eq_self w β
  rcases bit_cases (β w) with hw | hw <;> rw [hw] at hup ⊢ <;> ext idx <;>
    simp only [hup, PhotochemistrySolution.QubitizationWalkSem.bitSign_zero,
      PhotochemistrySolution.QubitizationWalkSem.bitSign_one, Pi.add_apply, Pi.smul_apply] <;>
    ring_nf <;> rw [hsq] <;> ring

def EvalPhasePerm {M : ℕ} (p : AndBracketProg M) (ph : BitAssignment M → ZMod 2)
    (f : BitAssignment M → BitAssignment M) : Prop :=
    ∀ β : BitAssignment M, p.toCircuit.eval.1.mulVec (KinB.ket β) =
    QubitizationWalkSem.bitSign (ph β) • KinB.ket (f β)
theorem EvalPhasePerm.id {M : ℕ} : EvalPhasePerm (.id : AndBracketProg M) (fun _ ↦ 0) (fun β ↦ β) :=
    fun β ↦ by
  rw [show (AndBracketProg.id : AndBracketProg M).toCircuit.eval.1 = 1 from rfl,
    Matrix.one_mulVec, PhotochemistrySolution.QubitizationWalkSem.bitSign_zero, one_smul]
theorem EvalPhasePerm.seq {M : ℕ} {p₁ p₂ : AndBracketProg M} {ph₁ ph₂ : BitAssignment M → ZMod 2}
    {f₁ f₂ : BitAssignment M → BitAssignment M}
    (h₁ : EvalPhasePerm p₁ ph₁ f₁) (h₂ : EvalPhasePerm p₂ ph₂ f₂) : EvalPhasePerm (.seq p₁ p₂)
        (fun β ↦ ph₁ β + ph₂ (f₁ β)) (fun β ↦ f₂ (f₁ β)) := fun β ↦ by
  simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    h₁ β, Matrix.mulVec_smul, h₂ (f₁ β), smul_smul, QubitizationWalkSem.bitSign_add]
theorem EvalPhasePerm.cz {M : ℕ} (c₁ c₂ : Wire M)
    (h : c₁ ≠ c₂) : EvalPhasePerm (.prim (czCircuit c₁ c₂ h)) (fun β ↦ β c₁ * β c₂) (fun β ↦ β) :=
    czCircuit_mulVec_ket c₁ c₂ h
theorem EvalPhasePerm.cnot {M : ℕ} (c t : Wire M) (h : c ≠ t) :
    EvalPhasePerm (.prim (Circuit.CNOT c t h)) (fun _ ↦ 0) (fun β ↦ Function.update β t (β t + β c))
        := fun β ↦ by
  simpa only [AndBracketProg.toCircuit, QubitizationWalkSem.bitSign_zero, one_smul]
    using PhotochemistrySolution.KinB.ket_CNOT c t h β
theorem EvalPhasePerm.tempAnd {M : ℕ}
    (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : AndBracketProg M) (ph : BitAssignment M → ZMod 2)
        (f : BitAssignment M → BitAssignment M)
    (hb : EvalPhasePerm body ph f) :
    let toff := fun γ : BitAssignment M ↦ Function.update γ anc (γ anc + γ c₁ * γ c₂)
    EvalPhasePerm (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) (fun β ↦ ph (toff β))
        (fun β ↦ toff (f (toff β))) := fun β ↦ by
  simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, PhotochemistrySolution.KinB.ket_TOFF, hb _, Matrix.mulVec_smul]
theorem EvalPhasePerm.comm_cleanProj_of_fix {M : ℕ} {p : AndBracketProg M}
    {ph : BitAssignment M → ZMod 2} {f : BitAssignment M → BitAssignment M}
    (hp : EvalPhasePerm p ph f) (S : Finset (Wire M)) (hfix : ∀ (β : BitAssignment M)
    (w : Wire M), w ∈ S → f β w = β w) : p.toCircuit.eval.1 * cleanProj S = cleanProj S *
    p.toCircuit.eval.1 :=
  matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket, hp β,
      Matrix.mulVec_smul, cleanProj_mulVec_ket]
    by_cases hS : ∀ w ∈ S, β w = 0
    · rw [ite_eq_left hS, hp β, ite_eq_left fun w hw ↦ (hfix β w hw).trans (hS w hw)]
    · rw [ite_eq_right hS, Matrix.mulVec_zero,
        ite_eq_right fun h ↦ hS fun w hw ↦ (hfix β w hw).symm.trans (h w hw), smul_zero]
theorem EvalPhasePerm.comm_andInvProj_of_fix {M : ℕ} {p : AndBracketProg M}
    {ph : BitAssignment M → ZMod 2} {f : BitAssignment M → BitAssignment M}
    (hp : EvalPhasePerm p ph f) (c₁ c₂ anc : Wire M) (hfix : ∀ β : BitAssignment M, f β c₁ = β c₁ ∧
    f β c₂ = β c₂ ∧ f β anc = β anc) : p.toCircuit.eval.1 * andInvProj c₁ c₂ anc =
    andInvProj c₁ c₂ anc * p.toCircuit.eval.1 :=
  matrix_ext_ket fun β ↦ by
    obtain ⟨h1, h2, ha⟩ := hfix β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, andInvProj_mulVec_ket, hp β,
      Matrix.mulVec_smul, andInvProj_mulVec_ket, ha, h1, h2]
    by_cases h : β anc = β c₁ * β c₂
    · rw [ite_eq_left h, hp β, ite_eq_left h]
    · rw [ite_eq_right h, Matrix.mulVec_zero, ite_eq_right h, smul_zero]

def gidneyFullAddPhase {M : ℕ} :
    ∀ (k : ℕ) (rA rB : QRegister (k + 1) M) (rCarry : QRegister k M) (cIn : Wire M),
      rA.DisjointWires rB →
      rA.DisjointWires rCarry →
      rB.DisjointWires rCarry →
      cIn ∉ Set.range rA.wires →
      cIn ∉ Set.range rB.wires →
      cIn ∉ Set.range rCarry.wires →
      AndBracketProg M
  | 0, rA, rB, _, cIn, hAB, _, _, hcA, hcB, _ =>
      have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
      have hca : cIn ≠ rA 0 := fun e ↦ hcA ⟨0, e.symm⟩
      have hcb : cIn ≠ rB 0 := fun e ↦ hcB ⟨0, e.symm⟩
      .seq (.prim (zGateCirc cIn))
        (.seq (.prim (.CNOT cIn (rA 0) hca))
          (.seq (.prim (.CNOT cIn (rB 0) hcb))
            (.seq (.prim (czCircuit (rA 0) (rB 0) hab))
              (.seq (.prim (.CNOT (rA 0) (rB 0) hab))
                (.seq (.prim (.CNOT cIn (rA 0) hca))
                  (.prim (.CNOT cIn (rB 0) hcb)))))))
  | k + 1, rA, rB, rCarry, cIn, hAB, hAC, hBC, hcA, hcB, hcC =>
      have hab : rA 0 ≠ rB 0 := hAB.ne 0 0; have hac : rA 0 ≠ rCarry 0 := hAC.ne 0 0;
      have hbc : rB 0 ≠ rCarry 0 := hBC.ne 0 0
      have hca : cIn ≠ rA 0 := fun e ↦ hcA ⟨0, e.symm⟩
      have hcb : cIn ≠ rB 0 := fun e ↦ hcB ⟨0, e.symm⟩
      have hcc : cIn ≠ rCarry 0 := fun e ↦ hcC ⟨0, e.symm⟩
      .seq (.prim (.CNOT cIn (rA 0) hca))
        (.seq (.prim (.CNOT cIn (rB 0) hcb))
          (.seq (.tempAnd (rA 0) (rB 0) (rCarry 0) hab hac hbc
            (.seq (.prim (.CNOT cIn (rCarry 0) hcc))
              (.seq (gidneyFullAddPhase k (PhotochemistrySolution.regTail rA)
                  (PhotochemistrySolution.regTail rB)
                  (PhotochemistrySolution.regTail rCarry) (rCarry 0)
                  (QRegister.disjoint_iff.mpr fun i j e ↦ hAB.ne i.succ j.succ e)
                  (QRegister.disjoint_iff.mpr fun i j e ↦ hAC.ne i.succ j.succ e)
                  (QRegister.disjoint_iff.mpr fun i j e ↦ hBC.ne i.succ j.succ e)
                  (fun ⟨i, e⟩ ↦ hAC.ne i.succ 0 e)
                  (fun ⟨i, e⟩ ↦ hBC.ne i.succ 0 e)
                  (fun ⟨i, e⟩ ↦ Fin.succ_ne_zero i (rCarry.wires.injective e)))
                (.prim (.CNOT cIn (rCarry 0) hcc)))))
            (.seq (.prim (.CNOT (rA 0) (rB 0) hab))
              (.seq (.prim (.CNOT cIn (rA 0) hca))
                (.prim (.CNOT cIn (rB 0) hcb))))))

def gidneyAddPhase {M : ℕ} :
    ∀ (w : ℕ) (rA rB : QRegister (w + 1) M) (rCarry : QRegister w M),
      rA.DisjointWires rB →
      rA.DisjointWires rCarry →
      rB.DisjointWires rCarry →
      AndBracketProg M
  | 0, rA, rB, _, hAB, _, _ =>
      have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
      .seq (.prim (czCircuit (rA 0) (rB 0) hab)) (.prim (.CNOT (rA 0) (rB 0) hab))
  | k + 1, rA, rB, rCarry, hAB, hAC, hBC =>
      have hab : rA 0 ≠ rB 0 := hAB.ne 0 0; have hac : rA 0 ≠ rCarry 0 := hAC.ne 0 0;
      have hbc : rB 0 ≠ rCarry 0 := hBC.ne 0 0
      .seq (.tempAnd (rA 0) (rB 0) (rCarry 0) hab hac hbc
        (gidneyFullAddPhase k (PhotochemistrySolution.regTail rA)
            (PhotochemistrySolution.regTail rB)
          (PhotochemistrySolution.regTail rCarry) (rCarry 0)
          (QRegister.disjoint_iff.mpr fun i j e ↦ hAB.ne i.succ j.succ e)
          (QRegister.disjoint_iff.mpr fun i j e ↦ hAC.ne i.succ j.succ e)
          (QRegister.disjoint_iff.mpr fun i j e ↦ hBC.ne i.succ j.succ e)
          (fun ⟨i, e⟩ ↦ hAC.ne i.succ 0 e)
          (fun ⟨i, e⟩ ↦ hBC.ne i.succ 0 e)
          (fun ⟨i, e⟩ ↦ Fin.succ_ne_zero i (rCarry.wires.injective e))))
        (.prim (.CNOT (rA 0) (rB 0) hab))

theorem hcnot_comm_clean {M : ℕ} (T : Finset (Wire M)) (c t : Wire M) (h : c ≠ t)
    (ht : t ∉ T) : (Circuit.CNOT c t h).eval.1 * cleanProj T = cleanProj T *
    (Circuit.CNOT c t h).eval.1 :=
  EvalPhasePerm.comm_cleanProj_of_fix (EvalPhasePerm.cnot c t h) T
    fun _ _ hw ↦ by rw [Function.update_of_ne (fun e ↦ ht (by rwa [← e]))]

theorem gidney_full_bit_step (a b cIn : ZMod 2) : cIn + (a + cIn) * (b + cIn) =
    (((a.val + b.val + cIn.val) / 2 : ℕ) : ZMod 2) ∧ (((b + cIn) + (a + cIn)) + cIn).val =
    (a.val + b.val + cIn.val) % 2 ∧ (a + cIn) + cIn = a := by
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases cIn with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩

def withDeltaStack {M : ℕ} (wCtrl : Wire M) :
    ∀ (k : ℕ) (rSrc rDst : QRegister k M),
      wCtrl ∉ Set.range rSrc.wires →
      wCtrl ∉ Set.range rDst.wires →
      rSrc.DisjointWires rDst →
      AndBracketProg M → AndBracketProg M
  | 0, _, _, _, _, _, body => body
  | k + 1, rSrc, rDst, hcS, hcD, hSD, body =>
      .tempAnd wCtrl (rSrc 0) (rDst 0)
        (fun e ↦ hcS ⟨0, e.symm⟩) (fun e ↦ hcD ⟨0, e.symm⟩) (hSD.ne 0 0)
        (withDeltaStack wCtrl k (PhotochemistrySolution.regTail rSrc)
            (PhotochemistrySolution.regTail rDst)
          (fun ⟨i, e⟩ ↦ hcS ⟨i.succ, e⟩)
          (fun ⟨i, e⟩ ↦ hcD ⟨i.succ, e⟩)
          (QRegister.disjoint_iff.mpr fun i j e ↦ hSD.ne i.succ j.succ e)
          body)

def qftSrcReg {M : ℕ} (rP : QRegister 8 M) (w : ℕ) (hw : w ≤ 6) : QRegister (w + 1) M :=
  ⟨⟨fun j ↦ rP ⟨7 - j.val, by omega⟩, fun i j e ↦ by
      have hi := rP.wires.injective e;
      have hv := congrArg Fin.val hi; change 7 - i.val = 7 - j.val at hv
      (apply Fin.ext; omega)⟩⟩

theorem _qft_w_le6 (ℓ : Fin 8) : 6 - ℓ.val ≤ 6 := Nat.sub_le _ _

theorem _qft_dst_le7 (ℓ : Fin 8) : 0 + (6 - ℓ.val + 1) ≤ 7 := by omega

theorem _qft_cat_le8 (ℓ : Fin 8) (hℓ : ℓ.val < 7) : ℓ.val + (6 - ℓ.val + 1) ≤ 8 := by omega

def polyGidneyInnerBracket {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (_hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (ℓ : Fin 8) : AndBracketProg M :=
  if hℓ : ℓ.val < 7 then
    let w := 6 - ℓ.val; let rSrc := qftSrcReg rP w (_qft_w_le6 ℓ);
    let rDst := rDelta.slice 0 (w + 1) (_qft_dst_le7 ℓ);
    let rB := rCat.slice ℓ.val (w + 1) (_qft_cat_le8 ℓ hℓ);
    let rC := rCarry.slice 0 w ((Nat.zero_add _).trans_le (_qft_w_le6 ℓ))
    withDeltaStack (rP ℓ) (w + 1) rSrc rDst
      (fun ⟨j, e⟩ ↦ by
        have hv := congrArg Fin.val (rP.wires.injective e)
        change 7 - j.val = ℓ.val at hv; omega)
      (fun ⟨j, e⟩ ↦ hPDelta.ne ℓ ⟨0 + j.val, by omega⟩ e.symm)
      (QRegister.disjoint_iff.mpr fun i j e ↦ hPDelta.ne ⟨7 - i.val, by omega⟩
          ⟨0 + j.val, by omega⟩ e)
      (gidneyAddPhase w rDst rB rC
        (QRegister.disjoint_iff.mpr fun i j e ↦ hDCat.ne ⟨0 + i.val, by omega⟩
            ⟨ℓ.val + j.val, by omega⟩ e)
        (QRegister.disjoint_iff.mpr fun i j e ↦ hDCarry.ne ⟨0 + i.val, by omega⟩
            ⟨0 + j.val, by omega⟩ e)
        (QRegister.disjoint_iff.mpr fun i j e ↦ hCatCarry.ne ⟨ℓ.val + i.val, by omega⟩
            ⟨0 + j.val, by omega⟩ e))
  else .id

def polySwapWire2Circ {M : ℕ} (a b : Wire M) (hab : a ≠ b) : Circuit M :=
    .seq (.CNOT a b hab) (.seq (.CNOT b a hab.symm) (.CNOT a b hab))
def polySwapAll8Circ {M : ℕ} (rP : QRegister 8 M) : Circuit M :=
    .seq (polySwapWire2Circ (rP 0) (rP 7) (rP.wires.injective.ne (fun h ↦ nomatch h)))
    (.seq (polySwapWire2Circ (rP 1) (rP 6) (rP.wires.injective.ne (fun h ↦ nomatch h)))
    (.seq (polySwapWire2Circ (rP 2) (rP 5) (rP.wires.injective.ne (fun h ↦ nomatch h)))
    (polySwapWire2Circ (rP 3) (rP 4) (rP.wires.injective.ne (fun h ↦ nomatch h)))))
theorem ket_polySwapWire2Circ {M : ℕ} (a b : Wire M) (hab : a ≠ b) (γ : BitAssignment M) :
    (polySwapWire2Circ a b hab).eval.1.mulVec (ket γ) =
    ket (Function.update (Function.update γ a (γ b)) b (γ a)) := by
  simp only [polySwapWire2Circ, Circuit.eval_seq, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, PhotochemistrySolution.KinB.ket_CNOT]
  refine congrArg ket (funext fun u ↦ ?_)
  by_cases ha : u = a
  · subst u
    simp [hab, hab.symm, ← add_assoc, add_comm (γ b) (γ a), CharTwo.add_self_eq_zero]
  · by_cases hb : u = b
    · subst u
      rcases bit_cases (γ a) with h1 | h1 <;> rcases bit_cases (γ b) with h2 | h2 <;>
        simp [hab, hab.symm, h1, h2, CharTwo.add_self_eq_zero]
    · simp [ha, hb]
theorem regVal_lt_two_pow_local {M : ℕ} :
    ∀ (W : ℕ) (r : QRegister W M) (δ : BitAssignment M),
      PhotochemistrySolution.regVal W r δ < 2 ^ W
  | 0, _, _ => Nat.zero_lt_one
  | W + 1, r, δ => by
      have := ZMod.val_lt (δ (r 0))
      have := regVal_lt_two_pow_local W (PhotochemistrySolution.regTail r) δ
      rw [PhotochemistrySolution.regVal, pow_succ']
      omega
theorem regVal_eq_of_wires_eq_qft8 {M : ℕ} :
    ∀ {w₁ w₂ : ℕ} (_ : w₁ = w₂) (r₁ : QRegister w₁ M) (r₂ : QRegister w₂ M) (δ : BitAssignment M),
      (∀ (i : Fin w₁) (j : Fin w₂), i.val = j.val → r₁ i = r₂ j) →
      PhotochemistrySolution.regVal w₁ r₁ δ = PhotochemistrySolution.regVal w₂ r₂ δ
  | 0, 0, _, _, _, _, _ => rfl
  | _ + 1, _ + 1, rfl, r₁, r₂, δ, h =>
      congrArg₂ (fun x y ↦ x + 2 * y) (congrArg (fun u ↦ (δ u).val) (h 0 0 rfl))
        (regVal_eq_of_wires_eq_qft8 rfl (PhotochemistrySolution.regTail r₁)
            (PhotochemistrySolution.regTail r₂) δ
          fun i j hij ↦ h i.succ j.succ (congrArg (· + 1) hij))
theorem basisOutcomeProjector_zero_idem {d k : ℕ} (R : QRegister k d) : R.basisOutcomeProjector 0 *
    R.basisOutcomeProjector 0 = R.basisOutcomeProjector 0 := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  split_ifs with h0
  · rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left h0]
  · rw [Matrix.mulVec_zero]

def _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.AndBracketProg.reverse {M : ℕ} :
    AndBracketProg M → AndBracketProg M
  | .id => .id
  | .prim c => .prim c
  | .seq p₁ p₂ => .seq (reverse p₂) (reverse p₁)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (reverse body)

@[simp] theorem AndBracketProg.numTempAnd_reverse {M : ℕ} (p : AndBracketProg M) :
    p.reverse.numTempAnd = p.numTempAnd := by
  induction p <;> simp only [AndBracketProg.reverse, AndBracketProg.numTempAnd, *, Nat.add_comm]

@[simp] theorem AndBracketProg.onRegister_reverse {M n : ℕ} (r : QRegister M n)
    (p : AndBracketProg M) :
    p.reverse.onRegister r = (p.onRegister r).reverse := by
  induction p <;> simp only [AndBracketProg.reverse, AndBracketProg.onRegister, *]

theorem CommCleanBracket.comm_cleanProj {M : ℕ} {S : Finset (Wire M)} {p : AndBracketProg M}
    (hp : CommCleanBracket S p) :
    p.toCircuit.eval.1 * cleanProj S = cleanProj S * p.toCircuit.eval.1 := by
  induction p with
  | id => simp [AndBracketProg.toCircuit]
  | prim _ => exact hp
  | seq _ _ ih₁ ih₂ =>
      simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hp.1, ← Matrix.mul_assoc, ih₂ hp.2, Matrix.mul_assoc]
  | tempAnd _ _ _ _ _ _ _ _ => exact hp.2.2.2

@[simp] theorem gidneyFullAddPhase_numTempAnd {M : ℕ} :
    ∀ (k : ℕ) (rA rB : QRegister (k + 1) M) (rCarry : QRegister k M) (cIn : Wire M)
      (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry)
      (hcA : cIn ∉ Set.range rA.wires) (hcB : cIn ∉ Set.range rB.wires)
      (hcC : cIn ∉ Set.range rCarry.wires),
      (gidneyFullAddPhase k rA rB rCarry cIn hAB hAC hBC hcA hcB hcC).numTempAnd = k
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | k + 1, _, _, _, _, _, _, _, _, _, _ => by
      simp only [gidneyFullAddPhase, AndBracketProg.numTempAnd, gidneyFullAddPhase_numTempAnd k]
      omega

@[simp] theorem gidneyAddPhase_numTempAnd {M : ℕ} :
    ∀ (w : ℕ) (rA rB : QRegister (w + 1) M) (rCarry : QRegister w M)
      (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry),
      (gidneyAddPhase w rA rB rCarry hAB hAC hBC).numTempAnd = w
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, rA, rB, rCarry, hAB, hAC, hBC => by
      simp only [gidneyAddPhase, AndBracketProg.numTempAnd, gidneyFullAddPhase_numTempAnd]; omega
@[simp] theorem withDeltaStack_numTempAnd {M : ℕ} (wCtrl : Wire M) :
    ∀ (k : ℕ) (rSrc rDst : QRegister k M)
      (hcS : wCtrl ∉ Set.range rSrc.wires)
      (hcD : wCtrl ∉ Set.range rDst.wires)
      (hSD : rSrc.DisjointWires rDst)
      (body : AndBracketProg M),
      (withDeltaStack wCtrl k rSrc rDst hcS hcD hSD body).numTempAnd = k + body.numTempAnd
  | 0, _, _, _, _, _, _ => by simp [withDeltaStack]
  | k + 1, _, _, _, _, _, _ => by
      simp only [withDeltaStack, AndBracketProg.numTempAnd, withDeltaStack_numTempAnd wCtrl k]
      omega

@[simp] theorem polyGidneyInnerBracket_numTempAnd {M : ℕ}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (ℓ : Fin 8) :
    (polyGidneyInnerBracket rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry
        ℓ).numTempAnd =
      if ℓ.val < 7 then (7 - ℓ.val) + (6 - ℓ.val) else 0 := by
  unfold polyGidneyInnerBracket
  split_ifs with hℓ
  · rw [withDeltaStack_numTempAnd, gidneyAddPhase_numTempAnd]; omega
  · rfl

theorem regVal_slice_split_local {M : ℕ} :
    ∀ (a b : ℕ) (r : QRegister (a + b) M) (δ : BitAssignment M),
      PhotochemistrySolution.regVal (a + b) r δ =
        PhotochemistrySolution.regVal a (r.slice 0 a (by omega)) δ +
          2 ^ a * PhotochemistrySolution.regVal b (r.slice a b (by omega)) δ
  | a, b, r, δ => by
      have hsum : ∀ {W : ℕ} (q : QRegister W M),
          PhotochemistrySolution.regVal W q δ = ∑ k : Fin W, 2 ^ k.val * (δ (q k)).val := by
        intro W
        induction W with
        | zero => exact fun _ ↦ rfl
        | succ W ih =>
            intro q
            simp only [PhotochemistrySolution.regVal, ih (PhotochemistrySolution.regTail q),
                Fin.sum_univ_succ,
              Finset.mul_sum, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ',
              PhotochemistrySolution.regTail_apply]
            exact congrArg ((δ (q 0)).val + ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
      simp only [hsum, Fin.sum_univ_add, Finset.mul_sum,
        Fin.val_castAdd, Fin.val_natAdd, pow_add, mul_assoc]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun i _ ↦ by
          rw [show r (Fin.castAdd b i) = (r.slice 0 a _) i from
            congrArg r.wires (Fin.ext (Nat.zero_add _).symm)])
        (Finset.sum_congr rfl fun _ _ ↦ rfl)
theorem disjoint_rP_clean13 {M : ℕ} (rP : QRegister 8 M)
    (rDelta : QRegister 7 M) (rCarry : QRegister 6 M) (rClean13 : QRegister 13 M)
    (hPDelta : rP.DisjointWires rDelta) (hPCarry : rP.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    rP.DisjointWires rClean13 :=
  QRegister.disjoint_iff.mpr fun i j hij ↦
    if hj : j.val < 7 then hPDelta.ne i ⟨j.val, hj⟩ (hij.trans (hSubD ⟨j.val, hj⟩))
    else hPCarry.ne i ⟨j.val - 7, by have := j.isLt; omega⟩ (hij.trans
      ((congrArg rClean13.wires (Fin.ext (by have := j.isLt; dsimp; omega))).trans (hSubC ⟨j.val -
          7, by have := j.isLt; omega⟩)))

theorem disjoint_rCat_clean13 {M : ℕ} (rCat : QRegister 8 M)
    (rDelta : QRegister 7 M) (rCarry : QRegister 6 M) (rClean13 : QRegister 13 M)
    (hDCat : rDelta.DisjointWires rCat) (hCatCarry : rCat.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    rCat.DisjointWires rClean13 :=
  disjoint_rP_clean13 rCat rDelta rCarry rClean13
    (QRegister.disjoint_iff.mpr fun i j e ↦ hDCat.ne j i e.symm) hCatCarry hSubD hSubC
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
end


section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
open scoped Circuit.Notation Matrix.Norms.L2Operator Polynomial
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate WithLp Polynomial
  ComplexConjugate PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.QubitizationCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.OvBidir
variable {Var : Type}
set_option exponentiation.threshold 8192 in
theorem hAncCompact (scrW : ℕ) : 100 ≤ ancWOfScr scrW := by unfold ancWOfScr; omega
set_option exponentiation.threshold 8192 in
theorem locQGen_hAncCompact_eq (scrW : ℕ) : locQGen (hAncCompact scrW) = locQCompactGen scrW := by
  apply Fin.ext;
  change systemQubits_frozen + (ancWOfScr scrW - 1) = systemQubits_frozen + (34 + scrW + 70)
  unfold ancWOfScr; omega
set_option exponentiation.threshold 8192 in
theorem projOneQGen_hAncCompact_eq (scrW : ℕ) : projOneQGen (hAncCompact scrW) =
    projOneQCompactGen scrW := by
  unfold projOneQGen projOneQCompactGen projOneQPoly; rw [locQGen_hAncCompact_eq scrW]; rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
end
end

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.GQSP
  QuantumComputation.Specs.PhotochemistrySolution.OvBidir
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectKapteynScreened
open scoped Polynomial
open Operator Polynomial ComplexConjugate
  PhotochemistrySolution.JacobiAngerTightWalk PhotochemistrySolution.DiagShiftSpecBridge
theorem twist_scaledTruncLaurentPoly_gen {K D : ℕ} (ε : ℝ) (hK : Odd K)
    (s δ : ℝ) : twist (scaledPoly ε δ (truncLaurentPoly K D s)) = -conjRev (2 * K)
    (scaledPoly ε δ (truncLaurentPoly K D s)) := by
  unfold scaledPoly truncLaurentPoly;
  rw [twist_mul, twist_C, conjRev_C_mul, Complex.conj_ofReal,
      twist_laurentPoly hK (conj_jacobiAngerLaurentCoeff D s), mul_neg]
end QuantumComputation.Specs.PhotochemistrySolution.SelectKapteynScreened

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectEulerRot32
set_option exponentiation.threshold 8192
open Operator QProg DynamicCircuit Circuit Qubit PhotochemistrySolution.QubitizationTop
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
theorem phaseTurn_map_comm_mixedSignal {ι : Type*} [Fintype ι] [DecidableEq ι] (θ : ℝ)
    (U : Matrix ι ι ℂ) (b : Bool) : (phaseTurn θ).map (algebraMap ℂ (Matrix ι ι ℂ)) *
    mixedSignal U b = mixedSignal U b * (phaseTurn θ).map (algebraMap ℂ (Matrix ι ι ℂ)) := by
  rw [phaseTurn_eq]
  cases b <;> {
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [mixedSignal, Matrix.mul_apply, Algebra.commutes] }
theorem comm_phaseTurn_sigOp {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Matrix (Fin 2)
    (Fin 2) ℂ →ₐ[ℂ] Matrix ι ι ℂ) {U : Matrix ι ι ℂ} (hU : U ∈ qubitCommutant e)
    (hU' : Uᴴ ∈ qubitCommutant e) (θ : ℝ) (b : Bool) : e (phaseTurn θ) * sigOp e U b = sigOp e U b *
    e (phaseTurn θ) := by
  unfold sigOp;
  rw [← blockOp_map_algebraMap e (phaseTurn θ),
      ← blockOp_mul e (map_algebraMap_entries_mem e (phaseTurn θ)),
      phaseTurn_map_comm_mixedSignal θ U b, blockOp_mul e (mixedSignal_entries_mem e hU hU' b),
      blockOp_map_algebraMap e (phaseTurn θ)]
end QuantumComputation.Specs.PhotochemistrySolution.SelectEulerRot32

namespace QuantumComputation.Specs.PhotochemistrySolution.Pyth32Su2
set_option exponentiation.threshold 512
open scoped Polynomial
open Polynomial ComplexConjugate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectEulerRot32 (comm_phaseTurn_sigOp)
noncomputable def su2Diag (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-((θ : ℂ) * Complex.I)), 0; 0, Complex.exp ((θ : ℂ) * Complex.I)]
theorem su2Diag_neg (θ : ℝ) :
    su2Diag (-θ) = !![Complex.exp ((θ : ℂ) * Complex.I), 0;
                      0, Complex.exp (-((θ : ℂ) * Complex.I))] := by
  unfold su2Diag; ext i j : 1
  fin_cases i <;> fin_cases j <;> simp
theorem su2Diag_neg_mul_self (θ : ℝ) : su2Diag (-θ) * su2Diag θ = 1 := by
  have h1 : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
  have h2 : Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [mul_comm]; exact h1
  rw [su2Diag_neg]; ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [su2Diag, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
end QuantumComputation.Specs.PhotochemistrySolution.Pyth32Su2
end

section
set_option exponentiation.threshold 8192
noncomputable section PhaseGradientSec
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectBase
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation
open Operator Matrix Qubit WithLp
theorem circuit_approx_plusPhase (c : Circuit 1) (hc1 : (CircExt.isOneQubitCircuit c) = true)
    (s : CyclotomicState) (hs : ((CircExt.evalCyclotomic c)).toOdd = s)
    (m j : ℕ) (hk : s.k = 2 * m + 1) (cα sα c₀ εc s₀ εs δ : ℝ)
    (hδ : 0 ≤ δ) (hα : cα ^ 2 + sα ^ 2 = 1)
    (hc : |Real.cos (2 * Real.pi / (2 : ℝ) ^ j) - c₀| ≤ εc)
    (hs_sin : |Real.sin (2 * Real.pi / (2 : ℝ) ^ j) - s₀| ≤ εs)
    (h_num :
      (|((s.u.a : ℝ) / (2 : ℝ) ^ m - cα) +
          ((s.u.b - s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid| +
        |((s.u.b - s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad) ^ 2 +
      (|((s.u.c : ℝ) / (2 : ℝ) ^ m - sα) +
          ((s.u.b + s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid| +
        |((s.u.b + s.u.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad) ^ 2 +
      (|(s.v.a : ℝ) / (2 : ℝ) ^ m +
          ((s.v.b - s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid +
          (-cα) * c₀ + (-sα) * s₀| +
        |((s.v.b - s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad +
        |(-cα)| * εc + |(-sα)| * εs) ^ 2 +
      (|(s.v.c : ℝ) / (2 : ℝ) ^ m +
          ((s.v.b + s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1) * sqrtTwoMid +
          (-sα) * c₀ + cα * s₀| +
        |((s.v.b + s.v.d : ℤ) : ℝ) / (2 : ℝ) ^ (m + 1)| * sqrtTwoRad +
        |(-sα)| * εc + |cα| * εs) ^ 2 ≤
      2 * δ ^ 2) :
    ∃ α : ℝ, ‖WithLp.toLp 2 (c.eval.1 *ᵥ basisState 0 -
      Complex.exp (α * Complex.I) •
        (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ j) (basisBits 1 i 0)))‖ ≤ δ := by
  rw [CircExt.evalCyclotomic_toStateVector c hc1, ← CyclotomicState.toOdd_toStateVector, hs]
  exact cyclotomicState_approx_plusPhase s m j hk cα sα c₀ εc s₀ εs δ hδ hα hc hs_sin h_num
noncomputable def concretePhaseErr (j : ℕ) : ℝ :=
    if j = 1 ∨ j = 2 then 0 else if j = 3 then 1 / 10 ^ 17 else if j = 6 ∨ j = 8 ∨ j = 11 ∨ j = 12 ∨
    j = 16 then 3 / 10 ^ 6 else if j ≤ 18 then 3 / 500000 else (3 / 2 : ℝ) * Real.pi / (2 : ℝ) ^ j
theorem concretePhaseErr_nonneg (j : ℕ) : 0 ≤ concretePhaseErr j := by
  unfold concretePhaseErr
  split_ifs <;> positivity
theorem concretePhaseState_approx_tight_1 : ∃ α : ℝ,
    ‖WithLp.toLp 2 ((concretePhaseState 1).eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 1)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErr 1 :=
  circuit_approx_plusPhase (concretePhaseState 1) rfl concretePhaseCyclotomicState1 rfl 0 1 rfl
    1 0 (-1) 0 0 0 (concretePhaseErr 1) (by unfold concretePhaseErr; norm_num) (by norm_num)
    cos_two_pi_div_two_pow_one_approx sin_two_pi_div_two_pow_one_approx
    (by unfold concretePhaseCyclotomicState1 concretePhaseErr sqrtTwoMid sqrtTwoRad; norm_num)
theorem concretePhaseState_approx_tight_2 : ∃ α : ℝ,
    ‖WithLp.toLp 2 ((concretePhaseState 2).eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 2)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErr 2 :=
  circuit_approx_plusPhase (concretePhaseState 2) rfl concretePhaseCyclotomicState2 rfl 0 2 rfl
    1 0 0 0 1 0 (concretePhaseErr 2) (by unfold concretePhaseErr; norm_num) (by norm_num)
    cos_two_pi_div_two_pow_two_approx sin_two_pi_div_two_pow_two_approx
    (by unfold concretePhaseCyclotomicState2 concretePhaseErr sqrtTwoMid sqrtTwoRad; norm_num)
theorem concretePhaseState_approx_tight_3 : ∃ α : ℝ,
    ‖WithLp.toLp 2 ((concretePhaseState 3).eval.1 *ᵥ basisState 0 - Complex.exp (α *
    Complex.I) • (fun i : Fin (2 ^ 1) ↦ QFT.plusPhase (-(1 : ℝ) / (2 : ℝ) ^ 3)
    (basisBits 1 i 0)))‖ ≤ concretePhaseErr 3 :=
  circuit_approx_plusPhase (concretePhaseState 3) rfl concretePhaseCyclotomicState3 rfl 0 3 rfl
    1 0 (sqrtTwoMid / 2) (sqrtTwoRad / 2) (sqrtTwoMid / 2) (sqrtTwoRad / 2)
    (concretePhaseErr 3) (by unfold concretePhaseErr; norm_num) (by norm_num)
    cos_two_pi_div_two_pow_three_approx sin_two_pi_div_two_pow_three_approx
    (by unfold concretePhaseCyclotomicState3 concretePhaseErr sqrtTwoMid sqrtTwoRad; norm_num)
end QuantumComputation.Specs.PhotochemistrySolution.SelectBase
end PhaseGradientSec

noncomputable section
open scoped Matrix.Norms.L2Operator
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationProgram
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationTop
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.QubitizationCore
  QuantumComputation.Specs.PhotochemistrySolution.SelectSymDyn
  QuantumComputation.Specs.PhotochemistrySolution.BucketRouterCircuit
  QuantumComputation.Specs.PhotochemistrySolution.OvBidir
  QuantumComputation.Specs.PhotochemistrySolution.GQSP
open QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
  QuantumComputation.Specs.PhotochemistrySolution.SelectEulerRot32
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ThreeSpec
open PhotochemistrySolution.DiagShiftSpecBridge
theorem approximatesTimeEvolution_of_O1_O2_O3_walk {Var : Type} [Fintype Var] [DecidableEq Var]
    {ancW n : ℕ} [NeZero (2 ^ n)] {hAnc : 100 ≤ ancW} {rSys : QRegister systemQubits_frozen n}
        {rAnc : QRegister ancW n}
    {hdisj : rSys.DisjointWires rAnc} {tSel : ℕ} {ε_walk : ℝ}
        (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
    (W : Unitary (2 ^ (systemQubits_frozen + ancW)))
    (hwalk : ApproximatesTimeEvolution (k := systemQubits_frozen)
        (m := ancW) D.aImpl (D.α * evolutionTime_frozen) ε_walk 1 W)
    (htot : ε_walk + (D.α * evolutionTime_frozen) * D.εBlock ≤ 0.01) :
    ApproximatesTimeEvolution (k := systemQubits_frozen)
        (m := ancW) hamiltonian_frozen evolutionTime_frozen 0.01 1 W :=
  approximatesTimeEvolution_of_rescaled_blockEncoding hamiltonian_conjTranspose
    D.aImpl_herm D.α_pos (by unfold evolutionTime_frozen; positivity) W hwalk D.aImpl_approx htot
end QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ThreeSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectLcu70Rot32
open scoped Polynomial
open WithLp Polynomial ComplexConjugate PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationKapteyn PhotochemistrySolution.DiagShiftSpecBridge
theorem sum_basisBits_mul_two_pow_32_rot32only (b : ℕ) (z : Fin (2 ^ b)) : ∑ i : Fin b,
    (basisBits b z i).val * 2 ^ i.val = z.val := by
  simp_rw [SelectFastRouterCore.basisBits_val_eq];
  rw [SelectFastRouterCore.sum_bit_mul_pow_eq_mod, Nat.mod_eq_of_lt z.isLt]

theorem opNorm_le_of_mulVec_pgL2Norm_32_rot32only {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ ψ : I → ℂ, pgL2Norm (A *ᵥ ψ) ≤ c * pgL2Norm ψ) :
    ‖A‖ ≤ c := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).opNorm_le_bound hc fun ψ ↦ h ψ.ofLp

theorem vecMulVec_single_zero_eq_pgColZero_32_rot32only {d : ℕ} [NeZero d]
    (u : Fin d → ℂ) : Matrix.vecMulVec u (Pi.single (0 : Fin d) 1) = pgColZeroMatrix u := by
  ext i j; by_cases hj : j = 0;
  · { subst hj; simp [Matrix.vecMulVec_apply, pgColZeroMatrix, Pi.single_eq_same] };
  · { have hjv : j.val ≠ 0 := fun h ↦ hj (Fin.ext h); simp [Matrix.vecMulVec_apply, pgColZeroMatrix,
        Pi.single_eq_of_ne hj, hjv] }

theorem pgColZero_mul_diag_single_zero_32_rot32only {d : ℕ} [NeZero d]
    (u : Fin d → ℂ) : pgColZeroMatrix u * Matrix.diagonal (Pi.single (0 : Fin d) 1) =
    pgColZeroMatrix u := by
  ext i j; by_cases hj : j = 0;
  · { subst hj; simp [Matrix.mul_diagonal, pgColZeroMatrix, Pi.single_eq_same] };
  · { have hjv : j.val ≠ 0 := fun h ↦ hj (Fin.ext h); simp [Matrix.mul_diagonal, pgColZeroMatrix,
        Pi.single_eq_of_ne hj, hjv] }

theorem embedMatrix_diag_single_zero_32_rot32only {N b : ℕ} (r : QRegister b N) :
    r.embedMatrix (Matrix.diagonal (Pi.single (0 : Fin (2 ^ b)) 1)) =
    r.basisOutcomeProjector 0 := by
  have hc : Matrix.diagonal (Pi.single (0 : Fin (2 ^ b)) 1) = compProj 0 :=
      (by ext i j; by_cases h1 : i = 0; · { subst h1; by_cases h2 : j =
                                              0;
                                              · { subst h2; rfl };
                                                    · simp [Matrix.diagonal_apply, compProj,
                                                          Matrix.single_apply] };
                                                    · simp [Matrix.diagonal_apply, compProj, h1,
                                                          Ne.symm h1]); rw [hc]; rfl

theorem pgL2Norm_gradZeroEnv_le_32_rot32only {N b : ℕ} (r : QRegister b N) (ψ : Fin (2 ^ N) → ℂ) :
    pgL2Norm (gradZeroEnv r ψ) ≤ pgL2Norm ψ := by
  have heq : pgL2Norm (gradZeroEnv r ψ) = pgL2Norm ((r.basisOutcomeProjector 0) *ᵥ ψ) :=
      (by rw [basisOutcomeProjector_mulVec_eq_tensorState_local r 0 ψ]; change pgL2Norm (gradZeroEnv
            r ψ) = pgL2Norm (r.tensorState (basisState 0)
            (gradZeroEnv r ψ)); rw [pgL2Norm_tensorState, pgL2Norm_basisState,
            one_mul]); rw [heq]; have hsq : pgL2Norm ((r.basisOutcomeProjector 0) *ᵥ ψ) ^ 2 ≤
                                   pgL2Norm ψ ^ 2 :=
                                   (by rw [pgL2Norm_sq, pgL2Norm_sq]; gcongr with idx
                                       rw [r.basisOutcomeProjector_mulVec]; split_ifs <;>
                                         simp); nlinarith [pgL2Norm_nonneg ((r.basisOutcomeProjector
                                         0) *ᵥ ψ), pgL2Norm_nonneg ψ]
end QuantumComputation.Specs.PhotochemistrySolution.SelectLcu70Rot32
end

noncomputable section
open Operator QProg DynamicCircuit Matrix Circuit Qubit
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64GqspWalk
open scoped Matrix.Norms.L2Operator Polynomial
open PrimitiveGate WithLp Polynomial ComplexConjugate
  PhotochemistrySolution.GQSP
open PhotochemistrySolution.OvBidir PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationProgram
open PhotochemistrySolution.QubitizationTop PhotochemistrySolution.QubitizationKapteyn
  PhotochemistrySolution.SelectCompactAnc
open PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.DiagShiftSpecBridge
  PhotochemistrySolution.SelectEulerRot32
open PhotochemistrySolution.JacobiAngerTightWalk
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectKapteynScreened hiding
  twist_scaledTruncLaurentPoly_gen
theorem walk_corner_screened_poly {N S : ℕ} (rSysL : QRegister S N)
    (P₀' e00 Plcu Pscr S_op Uex : Operator (2 ^ N)) (aImpl : Operator (2 ^ S))
    (hP0_idem : P₀' * P₀' = P₀') (hPlcu_herm : Plcuᴴ = Plcu) (hPlcu_idem : Plcu * Plcu = Plcu)
    (hPscr_herm : Pscrᴴ = Pscr) (hPscr_idem : Pscr * Pscr = Pscr)
    (hcomm_ls : Pscr * Plcu = Plcu * Pscr) (hP0_e00_r : P₀' * e00 = P₀')
    (hP0_e00_l : e00 * P₀' = P₀') (hP0_lcu_r : P₀' * Plcu = P₀') (hP0_lcu_l : Plcu * P₀' = P₀')
    (hP0_scr_r : P₀' * Pscr = P₀') (hP0_scr_l : Pscr * P₀' = P₀') (hS_sq : S_op * S_op = 1)
    (hS_herm : S_opᴴ = S_op) (hS_scr : S_op * Pscr = Pscr * S_op)
    (hblock : Plcu * S_op * Plcu * Pscr = rSysL.embedMatrix aImpl * Plcu * Pscr)
    (haImpl_herm : aImplᴴ = aImpl) (hcomm_sys_lcu : rSysL.embedMatrix aImpl * Plcu = Plcu *
    rSysL.embedMatrix aImpl) (hcomm_sys_scr : rSysL.embedMatrix aImpl * Pscr = Pscr *
    rSysL.embedMatrix aImpl) (hcomm_sys_P0 : ∀ X : Operator (2 ^ S), rSysL.embedMatrix X * P₀' =
    P₀' * rSysL.embedMatrix X) {d D_trunc : ℕ} {ε_cheb s δ : ℝ}
    (hcor : e00 * Uex * e00 = e00 * ((reflectionMatrix Plcu * S_op)ᴴ ^ d *
    aeval (reflectionMatrix Plcu * S_op)
    (GQSP.scaledPoly ε_cheb δ (GQSP.truncLaurentPoly d D_trunc s)))) : P₀' * Uex * P₀' =
    ((1 / (1 + ε_cheb + δ) : ℝ) : ℂ) • (rSysL.embedMatrix (GQSP.truncChebApprox d D_trunc aImpl s) *
    P₀') := by
  have hPjoint_herm : (Plcu * Pscr)ᴴ = Plcu * Pscr := by
    rw [Matrix.conjTranspose_mul, hPscr_herm, hPlcu_herm, hcomm_ls]
  have hPjoint_idem : (Plcu * Pscr) * (Plcu * Pscr) = Plcu * Pscr := by
    rw [show (Plcu * Pscr) * (Plcu * Pscr) = Plcu * (Pscr * Plcu) * Pscr by simp only [mul_assoc],
        hcomm_ls]
    simp only [mul_assoc, ← mul_assoc Plcu Plcu, hPlcu_idem, hPscr_idem]
  have hR_comm (P : Operator (2 ^ N)) (hP : P * Pscr = Pscr * P) : reflectionMatrix P * Pscr =
      Pscr * reflectionMatrix P := by
    unfold reflectionMatrix
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hP]
  have hc_joint : Commute (reflectionMatrix (Plcu * Pscr) * S_op) Pscr :=
      Commute.mul_left (hR_comm (Plcu * Pscr) (by simp only [mul_assoc, hcomm_ls.symm])) hS_scr
  have hcomm_adj {W : Operator (2 ^ N)} (hW : Commute W Pscr) : Commute Wᴴ Pscr := by
    simpa only [commute_iff_eq, Matrix.conjTranspose_mul,
        hPscr_herm] using (congrArg Matrix.conjTranspose hW.eq).symm
  have hpow_scr (k : ℕ) : (reflectionMatrix Plcu * S_op) ^ k * Pscr =
      (reflectionMatrix (Plcu * Pscr) * S_op) ^ k * Pscr := by
    induction k with
    | zero => simp only [pow_zero, one_mul]
    | succ k ih =>
      have hRscr : reflectionMatrix Plcu * S_op * Pscr = (reflectionMatrix (Plcu * Pscr) * S_op) *
          Pscr := by
        unfold reflectionMatrix
        simp only [sub_mul, smul_mul_assoc, one_mul, mul_assoc, hS_scr, ← mul_assoc Pscr Pscr,
            hPscr_idem]
      rw [pow_succ, pow_succ, mul_assoc ((reflectionMatrix Plcu * S_op) ^ k), hRscr, hc_joint.eq,
        ← mul_assoc ((reflectionMatrix Plcu * S_op) ^ k), ih,
            mul_assoc ((reflectionMatrix (Plcu * Pscr) * S_op) ^ k), ← hc_joint.eq, ← mul_assoc]
  have hpow_adj_scr (k : ℕ) : (reflectionMatrix Plcu * S_op)ᴴ ^ k * Pscr =
      (reflectionMatrix (Plcu * Pscr) * S_op)ᴴ ^ k * Pscr := by
    have hadj := congrArg Matrix.conjTranspose (hpow_scr k)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow,
        Matrix.conjTranspose_pow, hPscr_herm,
      ← ((hcomm_adj (Commute.mul_left (hR_comm Plcu hcomm_ls.symm) hS_scr)).pow_left k).eq,
      ← ((hcomm_adj hc_joint).pow_left k).eq] at hadj
    exact hadj
  set targetP := GQSP.scaledPoly ε_cheb δ (GQSP.truncLaurentPoly d D_trunc s)
  have haeval_scr : ((reflectionMatrix Plcu * S_op)ᴴ ^ d * aeval (reflectionMatrix Plcu *
      S_op) targetP) * Pscr = ((reflectionMatrix (Plcu * Pscr) * S_op)ᴴ ^ d *
      aeval (reflectionMatrix (Plcu * Pscr) * S_op) targetP) * Pscr := by
    have hp (P : ℂ[X]) : aeval (reflectionMatrix Plcu * S_op) P * Pscr =
        aeval (reflectionMatrix (Plcu * Pscr) * S_op) P * Pscr := by
      induction P using Polynomial.induction_on' with
      | add p q ihp ihq => simp only [map_add, add_mul, ihp, ihq]
      | monomial k a =>
            simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, one_mul, smul_mul_assoc,
            hpow_scr k]
    have hcomm_p (P : ℂ[X]) : Pscr * aeval (reflectionMatrix (Plcu * Pscr) * S_op) P =
        aeval (reflectionMatrix (Plcu * Pscr) * S_op) P * Pscr := by
      induction P using Polynomial.induction_on' with
      | add p q ihp ihq => simp only [map_add, mul_add, add_mul, ihp, ihq]
      | monomial k a =>
            simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, one_mul, mul_smul_comm,
            smul_mul_assoc, (hc_joint.pow_left k).eq]
    rw [mul_assoc, hp, ← hcomm_p, ← mul_assoc, hpow_adj_scr, mul_assoc, hcomm_p, mul_assoc]
  have hblk_joint : (Plcu * Pscr) * S_op * (Plcu * Pscr) = rSysL.embedMatrix aImpl * (Plcu * Pscr)
      := by
    calc (Plcu * Pscr) * S_op * (Plcu * Pscr) = Plcu * (S_op * (Pscr * Plcu) * Pscr) := by
            simp only [mul_assoc, ← hS_scr]
      _ = (Plcu * S_op * Plcu * Pscr) * Pscr := by simp only [hcomm_ls, mul_assoc]
      _ = rSysL.embedMatrix aImpl * (Plcu * Pscr) := by
        rw [hblock, mul_assoc, hPscr_idem, mul_assoc]
  have hproj_walk :=
      poly_proj_walk_scaledTruncPoly_gen d D_trunc hPjoint_herm hPjoint_idem hS_sq hS_herm
      hblk_joint (by rw [← rSysL.embedMatrix_conjTranspose, haImpl_herm])
      (Commute.mul_right hcomm_sys_lcu hcomm_sys_scr) ε_cheb s δ
  have hP0_jl : (Plcu * Pscr) * P₀' = P₀' := by rw [mul_assoc, hP0_scr_l, hP0_lcu_l]
  have hP0_jr : P₀' * (Plcu * Pscr) = P₀' := by rw [← mul_assoc, hP0_lcu_r, hP0_scr_r]
  calc P₀' * Uex * P₀' = P₀' * (e00 * Uex * e00) * P₀' := by
          simp only [mul_assoc, hP0_e00_l]; simp only [← mul_assoc, hP0_e00_r]
    _ = P₀' * (((reflectionMatrix Plcu * S_op)ᴴ ^ d * aeval (reflectionMatrix Plcu *
                                                            S_op) targetP) * Pscr) *
                                                            P₀' := by
      rw [hcor]; simp only [← mul_assoc, hP0_e00_r]; simp only [mul_assoc, hP0_scr_l]
    _ = P₀' * ((Plcu * Pscr) * ((reflectionMatrix (Plcu * Pscr) * S_op)ᴴ ^ d *
        aeval (reflectionMatrix (Plcu * Pscr) * S_op) targetP) * (Plcu * Pscr)) * P₀' := by
      rw [haeval_scr];
      set Wk :=
          (reflectionMatrix (Plcu * Pscr) * S_op)ᴴ ^ d * aeval (reflectionMatrix (Plcu * Pscr) *
          S_op) targetP
      calc P₀' * (Wk * Pscr) * P₀' = P₀' * (Wk * (Pscr * P₀')) := by simp only [mul_assoc]
        _ = (P₀' * (Plcu * Pscr)) * (Wk * ((Plcu * Pscr) * P₀')) := by
          rw [hP0_scr_l, hP0_jr, hP0_jl]
        _ = P₀' * ((Plcu * Pscr) * Wk * (Plcu * Pscr)) * P₀' := by simp only [mul_assoc]
    _ =
        ((1 /
        (1 + ε_cheb + δ) : ℝ) : ℂ) • (rSysL.embedMatrix (GQSP.truncChebApprox d D_trunc aImpl s) *
        P₀') := by
      rw [hproj_walk, mul_smul_comm, smul_mul_assoc,
          ← embedMatrix_truncChebApprox rSysL d D_trunc aImpl s]
      exact congrArg (_ • ·) (by
        rw [mul_assoc P₀', mul_assoc (rSysL.embedMatrix _), hP0_jl, ← mul_assoc,
          ← hcomm_sys_P0 _, mul_assoc, hP0_idem])
end QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64GqspWalk

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
open PhotochemistrySolution.SelectRefl
theorem CleanWorkStep.of_subreg {Var : Type} [Fintype Var] [DecidableEq Var] {n wSub wSuper : ℕ}
    [NeZero (2 ^ n)] (rSub : QRegister wSub n) (rSuper : QRegister wSuper n)
    (hSub : ∀ i : Fin wSub, ∃ j : Fin wSuper, rSub i = rSuper j) (U : Unitary (2 ^ n))
    (c : DynamicCircuit Var n) (hcomm : U.1 * rSuper.basisOutcomeProjector 0 =
    rSuper.basisOutcomeProjector 0 * U.1) (hStep : CleanWorkStep rSub U c) :
    CleanWorkStep rSuper U c := by
  have habs_right : rSub.basisOutcomeProjector 0 * rSuper.basisOutcomeProjector 0 =
      rSuper.basisOutcomeProjector 0 := by
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
    split_ifs with h0
    · rw [SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left fun i ↦
          by obtain ⟨j, hj⟩ := hSub i; rw [hj]; exact h0 j]
    · rw [Matrix.mulVec_zero]
  have habs_left : rSuper.basisOutcomeProjector 0 * rSub.basisOutcomeProjector 0 =
      rSuper.basisOutcomeProjector 0 := by
    simpa only [Matrix.conjTranspose_mul, rSub.basisOutcomeProjector_conjTranspose 0,
      rSuper.basisOutcomeProjector_conjTranspose 0] using
      congrArg Matrix.conjTranspose habs_right
  refine ⟨hcomm, fun M ↦ ?_⟩
  obtain ⟨N, hwp, hmat⟩ := hStep.2 M
  have wrap (X : Operator (2 ^ n)) :
      rSuper.basisOutcomeProjector 0 * (rSub.basisOutcomeProjector 0 * X *
          rSub.basisOutcomeProjector 0) *
        rSuper.basisOutcomeProjector 0 = rSuper.basisOutcomeProjector 0 * X *
            rSuper.basisOutcomeProjector 0 := by
    simp only [Matrix.mul_assoc, habs_right]
    rw [← Matrix.mul_assoc (rSuper.basisOutcomeProjector 0) (rSub.basisOutcomeProjector 0),
        habs_left]
  exact ⟨N, hwp, (wrap _).symm.trans
    ((congrArg (fun Y ↦ rSuper.basisOutcomeProjector 0 * Y *
        rSuper.basisOutcomeProjector 0) hmat).trans (wrap _))⟩
noncomputable def spliceUnitaryMat {d : ℕ} (U₁ U₂ : Unitary (2 ^ d)) (P : Operator (2 ^ d)) :
    Operator (2 ^ d) := U₁.1 * P + U₂.1 * (1 - P)
noncomputable def spliceUnitary {d : ℕ} (U₁ U₂ : Unitary (2 ^ d)) (P : Operator (2 ^ d))
    (hP_herm : Pᴴ = P) (hP_idem : P * P = P) (hcomm₁ : U₁.1 * P = P * U₁.1)
    (hcomm₂ : U₂.1 * P = P * U₂.1) : Unitary (2 ^ d) :=
  { val := spliceUnitaryMat U₁ U₂ P
    property := by
      rw [Matrix.mem_unitaryGroup_iff];
      change spliceUnitaryMat U₁ U₂ P * (spliceUnitaryMat U₁ U₂ P)ᴴ = 1;
      let Q := (1 : Operator (2 ^ d)) - P
      have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
      have hPQ : P * Q = 0 := by simp [Q, mul_sub, hP_idem]
      have hQP : Q * P = 0 := by simp [Q, sub_mul, hP_idem]
      have hQ_idem : Q * Q = Q := by
        calc Q * Q = Q - Q * P := by simp [Q, mul_sub]
          _ = Q := by rw [hQP, sub_zero]
      have hcommQ : U₂.1 * Q = Q * U₂.1 := by simp [Q, mul_sub, sub_mul, hcomm₂]
      have hu₁ : U₁.1 * U₁.1ᴴ = 1 := congrArg Subtype.val (mul_inv_cancel U₁);
      have hu₂ : U₂.1 * U₂.1ᴴ = 1 :=
          congrArg Subtype.val (mul_inv_cancel U₂); change (U₁.1 * P + U₂.1 * Q) *
          (U₁.1 * P + U₂.1 * Q)ᴴ = 1
      have hM_herm : (U₁.1 * P + U₂.1 * Q)ᴴ = P * U₁.1ᴴ + Q * U₂.1ᴴ := by
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hP_herm, hQ_herm]
      rw [hM_herm]
      calc (U₁.1 * P + U₂.1 * Q) * (P * U₁.1ᴴ + Q * U₂.1ᴴ)
          = (U₁.1 * (P * P) * U₁.1ᴴ + U₂.1 * (Q * P) * U₁.1ᴴ) +
              (U₁.1 * (P * Q) * U₂.1ᴴ + U₂.1 * (Q * Q) * U₂.1ᴴ) := by
              simp only [mul_add, add_mul, Matrix.mul_assoc]
        _ = (U₁.1 * P) * U₁.1ᴴ + (U₂.1 * Q) * U₂.1ᴴ := by rw [hP_idem, hPQ, hQP, hQ_idem]; simp
        _ = P * (U₁.1 * U₁.1ᴴ) + Q * (U₂.1 * U₂.1ᴴ) := by
          rw [hcomm₁, hcommQ]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hu₁, hu₂, mul_one, mul_one]; simp [Q] }

theorem spliceUnitary_mul_proj {d : ℕ} (U₁ U₂ : Unitary (2 ^ d)) (P : Operator (2 ^ d))
    (hP_herm : Pᴴ = P) (hP_idem : P * P = P) (hcomm₁ : U₁.1 * P = P * U₁.1)
    (hcomm₂ : U₂.1 * P = P * U₂.1) : (spliceUnitary U₁ U₂ P hP_herm hP_idem hcomm₁ hcomm₂).1 * P =
    U₁.1 * P := by
  change (U₁.1 * P + U₂.1 * (1 - P)) * P = U₁.1 * P
  rw [add_mul, Matrix.mul_assoc, hP_idem, Matrix.mul_assoc, sub_mul, one_mul, hP_idem, sub_self,
      mul_zero, add_zero]
theorem spliceUnitary_mul_comm_proj {d : ℕ} (U₁ U₂ : Unitary (2 ^ d)) (P R : Operator (2 ^ d))
    (hP_herm : Pᴴ = P) (hP_idem : P * P = P) (hcomm₁ : U₁.1 * P = P * U₁.1)
    (hcomm₂ : U₂.1 * P = P * U₂.1) (hPR : P * R = R * P) (heq_on_PR : (U₁.1 * R) * P = (U₂.1 * R) *
    P) : (spliceUnitary U₁ U₂ P hP_herm hP_idem hcomm₁ hcomm₂).1 * R = U₂.1 * R := by
  change (U₁.1 * P + U₂.1 * (1 - P)) * R = U₂.1 * R
  have hQR : (1 - P) * R = R * (1 - P) := by simp [sub_mul, mul_sub, hPR]
  rw [add_mul, Matrix.mul_assoc U₁.1 P R, hPR, ← Matrix.mul_assoc U₁.1 R P, heq_on_PR,
      Matrix.mul_assoc U₂.1 (1 - P) R, hQR, ← Matrix.mul_assoc U₂.1 R (1 - P), ← mul_add]
  simp
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectBase
open scoped Matrix.Norms.L2Operator ComplexOrder Circuit.Notation Fin.CommRing
open Operator Matrix Qubit WithLp
theorem l2Norm_stateToFactor (ψ : Fin (2 ^ 1) → ℂ) : pgL2Norm (stateToFactor ψ) = pgL2Norm ψ := by
  rw [pgL2Norm_eq_sqrt, pgL2Norm_eq_sqrt, sum_zmod_two_local, sum_fin_two_pow_one]; rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectBase
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.TightWalkPhaseGrad
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate WithLp ComplexConjugate
  PhotochemistrySolution.GQSP PhotochemistrySolution.OvBidir PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectCompactRot34
  PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectCsa64GqspWalk
  PhotochemistrySolution.SelectLcu70Rot32
open scoped Matrix.Norms.L2Operator
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
theorem norm_conj_prep_eps_sub_le_phaseGrad {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (P B : Unitary (2 ^ m))
    (V P_g P₀ M : Operator (2 ^ m)) (hPV : ‖P.1 * P_g - V‖ ≤ ε) (hP0 : ‖P₀‖ ≤ 1) (hM : ‖M‖ ≤ 1)
    (hPg0 : P_g * P₀ = P₀) (hBM : B.1 * (V * P₀) = V * (M * P₀)) (hMPg0 : (P_g * M) * P₀ = M * P₀) :
    ‖((P⁻¹ * (B * P)).1 - M) * P₀‖ ≤ 2 * ε := by
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  set E : Operator (2 ^ m) := P.1 * P_g - V
  have hinv_mul : P⁻¹.1 * P.1 = 1 := congrArg Subtype.val (inv_mul_cancel P);
  have hPinv_norm : ‖P⁻¹.1‖ ≤ 1 := QubitizationTop.norm_unitary_le_one P⁻¹;
  have hB_norm : ‖B.1‖ ≤ 1 := QubitizationTop.norm_unitary_le_one B
  have hPP0 : P.1 * P₀ = E * P₀ + V * P₀ := by
    calc P.1 * P₀ = P.1 * (P_g * P₀) := by rw [hPg0]
      _ = (E + V) * P₀ := by dsimp only [E]; rw [sub_add_cancel, mul_assoc]
      _ = E * P₀ + V * P₀ := add_mul E V P₀
  have hsecond : P⁻¹.1 * (V * (M * P₀)) - M * P₀ = -(P⁻¹.1 * (E * (M * P₀))) := by
    calc P⁻¹.1 * (V * (M * P₀)) - M * P₀
        = P⁻¹.1 * (V * (M * P₀)) - (P_g * M) * P₀ := by rw [hMPg0]
      _ = P⁻¹.1 * (V * (M * P₀)) - ((P⁻¹.1 * P.1) * P_g) * (M * P₀) := by
        rw [hinv_mul, one_mul, mul_assoc]
      _ = -(P⁻¹.1 * (E * (M * P₀))) := by
          dsimp only [E]; simp only [sub_mul, mul_sub, mul_assoc]
          abel
  have hdecomp : ((P⁻¹ * (B * P)).1 - M) * P₀ = P⁻¹.1 * (B.1 * (E * P₀)) - P⁻¹.1 * (E * (M * P₀))
      := by
    rw [sub_mul]; change P⁻¹.1 * (B.1 * P.1) * P₀ - M * P₀ = _;
    rw [mul_assoc P⁻¹.1, mul_assoc B.1, hPP0, mul_add B.1, hBM, mul_add P⁻¹.1, add_sub_assoc,
        hsecond, sub_eq_add_neg]
  have ht1 : ‖P⁻¹.1 * (B.1 * (E * P₀))‖ ≤ ε := by
    have he0 : ‖E * P₀‖ ≤ ε :=
        (norm_mul_le E P₀).trans ((mul_le_mul hPV hP0 (norm_nonneg P₀) hε).trans (mul_one ε).le);
        have hbe0 : ‖B.1 * (E * P₀)‖ ≤ ε :=
        (norm_mul_le B.1 (E *
        P₀)).trans ((mul_le_mul hB_norm he0 (norm_nonneg _) zero_le_one).trans (one_mul ε).le);
        exact (norm_mul_le P⁻¹.1 _).trans ((mul_le_mul hPinv_norm hbe0 (norm_nonneg _)
        zero_le_one).trans (one_mul ε).le)
  have ht2 : ‖P⁻¹.1 * (E * (M * P₀))‖ ≤ ε := by
    have hm0 : ‖M * P₀‖ ≤ 1 :=
        (norm_mul_le M P₀).trans ((mul_le_mul hM hP0 (norm_nonneg P₀) zero_le_one).trans
        (one_mul 1).le); have hem0 : ‖E * (M * P₀)‖ ≤ ε :=
                           (norm_mul_le E (M *
                           P₀)).trans ((mul_le_mul hPV hm0 (norm_nonneg _) hε).trans
                           (mul_one ε).le); exact (norm_mul_le P⁻¹.1 _).trans
                           ((mul_le_mul hPinv_norm hem0 (norm_nonneg _) zero_le_one).trans
                           (one_mul ε).le)
  rw [hdecomp]
  exact (norm_sub_le _ _).trans ((add_le_add ht1 ht2).trans_eq (by ring))
end QuantumComputation.Specs.PhotochemistrySolution.TightWalkPhaseGrad
end

noncomputable section
open QProg QuantumComputation.Specs.PhotochemistrySolution
section
set_option exponentiation.threshold 8192
open scoped Circuit.Notation Matrix.Norms.L2Operator
open Operator DynamicCircuit Matrix Circuit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationCore
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationProgram
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.QubitizationTop
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
open Qubit QFT PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.QubitizationKapteyn
  PhotochemistrySolution.SelectApprox PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectSandwich
open PhotochemistrySolution.SelectArithSymSem PhotochemistrySolution.SelectFastRouterEval
  PhotochemistrySolution.SelectDataBuilder PhotochemistrySolution.SelectFastRouterCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding ket ket_CNOT ket_TOFF ket_X
  matrix_ext_ket
def _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.AndBracketProg.IsSelfInvPrim
    {M : ℕ} :
    AndBracketProg M → Prop
  | .id => True
  | .prim c => c.eval * c.eval = 1
  | .seq p₁ p₂ => IsSelfInvPrim p₁ ∧ IsSelfInvPrim p₂
  | .tempAnd _ _ _ _ _ _ body => IsSelfInvPrim body

theorem eval_TOFF_mul_self {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) : (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval *
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      KinB.ket_TOFF, Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]

theorem AndBracketProg.eval_reverse_eq_inv {M : ℕ} {p : AndBracketProg M} (hp : p.IsSelfInvPrim) :
    p.reverse.toCircuit.eval = (p.toCircuit.eval)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  induction p with
  | id => simp [AndBracketProg.reverse, AndBracketProg.toCircuit]
  | prim _ => exact hp
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [AndBracketProg.reverse, AndBracketProg.toCircuit, Circuit.eval_seq]
      rw [mul_assoc, ← mul_assoc p₁.toCircuit.eval, ih₁ hp.1, one_mul, ih₂ hp.2]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      have hT := eval_TOFF_mul_self c₁ c₂ anc h₁₂ h₁a h₂a
      simp only [AndBracketProg.reverse, AndBracketProg.toCircuit, Circuit.eval_seq]
      rw [show ∀ a b c : Unitary (2 ^ M), a * b * a * (a * c * a) = a * (b * (a * a) * c) * a
        from fun _ _ _ ↦ by simp only [mul_assoc], hT, mul_one, ih hp, mul_one, hT]

noncomputable abbrev catState8Mat : Operator (2 ^ 8) :=
    Matrix.vecMulVec (PgBase.phaseGradientState 8) (star (PgBase.phaseGradientState 8))
theorem CommCleanBracket.valid {M : ℕ} {S : Finset (Wire M)} {p : AndBracketProg M}
    (hp : CommCleanBracket S p) : ValidCleanBracket S p := by
  induction p generalizing S with
  | id => trivial
  | prim c =>
      exact (Matrix.mul_assoc (cleanProj S) c.eval.1 _).symm.trans
        (by rw [← hp, Matrix.mul_assoc, cleanProj_mul_self])
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
  | tempAnd _ _ _ _ _ _ _ ih =>
      exact ⟨hp.1, ih hp.2.1, hp.2.2.1, by
        rw [← Matrix.mul_assoc, ← hp.2.2.2, Matrix.mul_assoc, cleanProj_mul_self]⟩
theorem CommCleanBracket.reverse {M : ℕ} {S : Finset (Wire M)} {p : AndBracketProg M}
    (hself : p.IsSelfInvPrim) (hp : CommCleanBracket S p) : CommCleanBracket S p.reverse := by
  induction p generalizing S with
  | id => trivial
  | prim _ => exact hp
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hself.2 hp.2, ih₁ hself.1 hp.1⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      exact ⟨hp.1, ih hself hp.2.1,
        AndBracketProg.eval_reverse_eq_inv (p := body) hself ▸ unitary_inv_comm _ _ hp.2.2.1,
        AndBracketProg.eval_reverse_eq_inv (p := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) hself ▸
          unitary_inv_comm _ _ hp.2.2.2⟩

theorem cleanWorkStep_onRegister_of_commClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n w : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister M n) (rSub : QRegister w M)
    (p : AndBracketProg M) (hcomm : CommCleanBracket (Finset.univ.image rSub.wires) p) :
    CleanWorkStep (rTot.compose rSub) (rTot.embedUnitary p.toCircuit.eval)
    ((p.onRegister rTot).toDyn v) := by
  have himg : (Finset.univ.image rSub.wires).image rTot.wires =
      Finset.univ.image (rTot.compose rSub).wires := by simp [Finset.image_image]
  have hev : (p.onRegister rTot).toCircuit.eval = rTot.embedUnitary p.toCircuit.eval := by
    rw [AndBracketProg.toCircuit_onRegister, Circuit.eval_onRegister]
  refine hev ▸ cleanWorkStep_of_realizesOnClean v (rTot.compose rSub) (p.onRegister rTot)
    (himg ▸ ValidCleanBracket.realizesOnClean_onRegister v rTot hcomm.valid) (by
      rw [hev, QRegister.embedUnitary_val, ← cleanProj_range_eq_basisOutcomeProjector_zero,
        ← himg, cleanProj_image_eq_embedMatrix, ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul]
      exact congrArg rTot.embedMatrix hcomm.comm_cleanProj)
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
open scoped Polynomial
open WithLp Polynomial ComplexConjugate PhotochemistrySolution.BucketRouterCircuit
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectFastQft8Gidney
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding ket ket_CNOT ket_TOFF ket_X
  matrix_ext_ket writeReg writeReg_apply_of_not_mem
variable {Var : Type}
inductive ClassicalBracketProg (M : ℕ) where
  | id : ClassicalBracketProg M
  | x (u : Wire M) : ClassicalBracketProg M
  | cnot (c t : Wire M) (h : c ≠ t) : ClassicalBracketProg M
  | seq (p₁ p₂ : ClassicalBracketProg M) : ClassicalBracketProg M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : ClassicalBracketProg M) : ClassicalBracketProg M
namespace ClassicalBracketProg
def toBracket {M : ℕ} : ClassicalBracketProg M → AndBracketProg M
  | .id => .id
  | .x u => .prim (.X u)
  | .cnot c tgt h => .prim (.CNOT c tgt h)
  | .seq p₁ p₂ => .seq p₁.toBracket p₂.toBracket
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body.toBracket
def numTempAnd {M : ℕ} : ClassicalBracketProg M → ℕ
  | .id => 0
  | .x _ => 0
  | .cnot _ _ _ => 0
  | .seq p₁ p₂ => p₁.numTempAnd + p₂.numTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.numTempAnd
@[simp] theorem toBracket_numTempAnd {M : ℕ} (p : ClassicalBracketProg M) :
    p.toBracket.numTempAnd = p.numTempAnd := by
  induction p <;> simp [toBracket, numTempAnd, AndBracketProg.numTempAnd, *]
theorem toBracket_isSelfInvPrim {M : ℕ} (p : ClassicalBracketProg M) :
    p.toBracket.IsSelfInvPrim := by
  induction p <;> simp only [toBracket, AndBracketProg.IsSelfInvPrim,
    SelectSymDyn.eval_X_mul_self, SelectSymDyn.eval_CNOT_mul_self, and_self, *]
def evalBits {M : ℕ} : ClassicalBracketProg M → BitAssignment M → BitAssignment M
  | .id, β => β
  | .x u, β => Function.update β u (β u + 1)
  | .cnot c tgt _, β => Function.update β tgt (β tgt + β c)
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂); let β₂ := body.evalBits β₁
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)
theorem toBracket_ket {M : ℕ} (p : ClassicalBracketProg M) (β : BitAssignment M) :
    p.toBracket.toCircuit.eval.1.mulVec (KinB.ket β) = KinB.ket (p.evalBits β) := by
  induction p generalizing β <;> simp only [toBracket, AndBracketProg.toCircuit,
    Circuit.eval_identity, Circuit.eval_seq, Submonoid.coe_one, Submonoid.coe_mul,
        Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, evalBits, PhotochemistrySolution.KinB.ket_X,
    PhotochemistrySolution.KinB.ket_CNOT, PhotochemistrySolution.KinB.ket_TOFF, *]
end ClassicalBracketProg
def _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.ComputeProg.wrapCB {M : ℕ} :
    ComputeProg M → ClassicalBracketProg M → ClassicalBracketProg M
  | .id, mid => mid
  | .x w, mid => .seq (.x w) (.seq mid (.x w))
  | .cnot c tgt h, mid => .seq (.cnot c tgt h) (.seq mid (.cnot c tgt h))
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a, mid => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a mid
  | .seq p₁ p₂, mid => p₁.wrapCB (p₂.wrapCB mid)
@[simp] theorem
    _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.ComputeProg.wrapCB_toBracket {M : ℕ}
    (p : ComputeProg M) (mid : ClassicalBracketProg M) :
    (p.wrapCB mid).toBracket = p.wrap mid.toBracket := by
  induction p generalizing mid <;>
    simp [ComputeProg.wrapCB, ComputeProg.wrap, ClassicalBracketProg.toBracket, *]
@[simp] theorem
    _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.ComputeProg.wrapCB_numTempAnd
    {M : ℕ}
    (p : ComputeProg M) (mid : ClassicalBracketProg M) :
    (p.wrapCB mid).numTempAnd = p.numAnd + mid.numTempAnd := by
  rw [← ClassicalBracketProg.toBracket_numTempAnd, ComputeProg.wrapCB_toBracket,
      ComputeProg.wrap_numTempAnd, ClassicalBracketProg.toBracket_numTempAnd]
theorem _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.ComputeProg.wrapCB_evalBits
    {M : ℕ} (Tout : Finset (Wire M)) (p : ComputeProg M) (mid : ClassicalBracketProg M)
    (hp : p.DisjointFrom Tout) (hout : ∀ (β : BitAssignment M) (w : Wire M), w ∉ Tout →
    mid.evalBits β w = β w) (β : BitAssignment M) : (p.wrapCB mid).evalBits β = fun w ↦
    if w ∈ Tout then mid.evalBits (p.fwdBits β) w else β w := by
  have hket :=
      ComputeProg.ket_wrap_computeProg Tout p mid.toBracket mid.evalBits hp mid.toBracket_ket hout β
  rw [← ComputeProg.wrapCB_toBracket, ClassicalBracketProg.toBracket_ket] at hket
  by_contra hne
  have h1 := congrFun hket ((basisBitsEquiv M).symm ((p.wrapCB mid).evalBits β))
  simp [PhotochemistrySolution.KinB.ket, basisState, 
    (basisBitsEquiv M).symm.injective.eq_iff, hne] at h1
theorem commCleanBracket_wrap {M : ℕ} (T S : Finset (Wire M)) (hTS : Disjoint T S)
    (p : ComputeProg M) (mid : AndBracketProg M) (midOut : BitAssignment M → BitAssignment M)
    (hp : p.ValidProg T S) (hmid_comm : CommCleanBracket (p.finalClean S) mid)
    (hmid_ket : ∀ β : BitAssignment M, mid.toCircuit.eval.1.mulVec (KinB.ket β) =
    KinB.ket (midOut β)) (hout : ∀ (β : BitAssignment M) (w : Wire M), w ∉ T → midOut β w = β w) :
    CommCleanBracket S (p.wrap mid) := by
  have hket_comm (S' : Finset (Wire M)) (U : Operator (2 ^ M))
      (f : BitAssignment M → BitAssignment M)
      (hU : ∀ β, U.mulVec (KinB.ket β) = KinB.ket (f β))
      (hiff : ∀ β, (∀ w ∈ S', f β w = 0) ↔ ∀ w ∈ S', β w = 0) : U * cleanProj S' = cleanProj S' *
          U :=
    PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket, hU β,
        cleanProj_mulVec_ket]
      exact if hS : ∀ w ∈ S', β w =
          0 then by rw [ite_eq_left hS, ite_eq_left ((hiff β).mpr hS), hU β]
      else by rw [ite_eq_right hS, ite_eq_right (mt (hiff β).mp hS), Matrix.mulVec_zero]
  have hEqOn {S' : Finset (Wire M)} {f g : BitAssignment M} (h : ∀ w ∈ S', f w = g w) :
      (∀ w ∈ S', f w = 0) ↔ ∀ w ∈ S', g w = 0 := forall₂_congr fun w hw ↦ by rw [h w hw]
  induction p generalizing S mid midOut with
  | id => exact hmid_comm
  | x u =>
      have hx := hket_comm S _ _ (PhotochemistrySolution.KinB.ket_X u) fun _ ↦
        hEqOn fun w hw ↦ Function.update_of_ne (fun (e : w = u) ↦ hp.2 (e ▸ hw)) _ _
      exact ⟨hx, hmid_comm, hx⟩
  | cnot c t hct =>
      have hc := hket_comm S _ _ (PhotochemistrySolution.KinB.ket_CNOT c t hct) fun β ↦
        hp.2.2.elim
          (fun htS ↦ hEqOn fun w hw ↦ Function.update_of_ne (fun (e : w = t) ↦ htS (e ▸ hw)) _ _)
          fun hcS ↦ ⟨fun h ↦ by
              have hc0 : β c = 0 := by simpa [Function.update_of_ne hct] using h c hcS
              simpa [hc0, Function.update_eq_self] using h,
            fun h ↦ by simpa [h c hcS, Function.update_eq_self] using h⟩
      exact ⟨hc, hmid_comm, hc⟩
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      refine ⟨hp.2.2.2, hmid_comm, PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_,
        hket_comm S _ _ (ComputeProg.ket_wrap_computeProg T (.andGate c₁ c₂ anc h₁₂ h₁a h₂a)
          mid midOut ⟨hp.1, hp.2.1, hp.2.2.1⟩ hmid_ket hout) fun _ ↦
          hEqOn fun _ hw ↦ ite_eq_right (Finset.disjoint_right.mp hTS hw)⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmid_ket β, andInvProj_mulVec_ket,
        andInvProj_mulVec_ket, hout β anc hp.2.2.1, hout β c₁ hp.1, hout β c₂ hp.2.1]
      split_ifs with hinv <;> simp [hmid_ket β]
  | seq p₁ p₂ ih₁ ih₂ =>
      have hsub (p₀ : ComputeProg M) : ∀ S', p₀.finalClean S' ⊆ S' := by
        induction p₀ with
        | seq _ _ h₁ h₂ => exact fun S' ↦ (h₂ _).trans (h₁ S')
        | andGate _ _ a _ _ _ => exact Finset.erase_subset a
        | _ => exact fun _ ↦ Finset.Subset.rfl
      exact ih₁ S hTS (p₂.wrap mid) (fun γ w ↦ if w ∈ T then midOut (p₂.fwdBits γ) w else γ w)
        hp.1 (ih₂ _ (Disjoint.mono_right (hsub p₁ S) hTS) mid midOut hp.2 hmid_comm hmid_ket hout)
        (ComputeProg.ket_wrap_computeProg T p₂ mid midOut
          (ComputeProg.disjointFrom_of_validProg hp.2) hmid_ket hout) fun _ _ hw ↦ ite_eq_right hw
def tempAndCnot {M : ℕ} (c₁ c₂ anc t : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hat : anc ≠ t) : ClassicalBracketProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (.cnot anc t hat)
@[simp] theorem tempAndCnot_numTempAnd {M : ℕ} (c₁ c₂ anc t : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ t) :
    (tempAndCnot c₁ c₂ anc t h₁₂ h₁a h₂a hat).numTempAnd = 1 := rfl
theorem tempAndCnot_evalBits {M : ℕ} (c₁ c₂ anc t : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (hat : anc ≠ t) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (β : BitAssignment M) :
    (tempAndCnot c₁ c₂ anc t h₁₂ h₁a h₂a hat).evalBits β = Function.update β t (β t +
    (β anc + β c₁ * β c₂)) := by
  dsimp only [tempAndCnot, ClassicalBracketProg.evalBits]
  simp only [Function.update_self, Function.update_of_ne hat, Function.update_of_ne hat.symm,
    Function.update_of_ne h₁t, Function.update_of_ne h₁a, Function.update_of_ne h₂t,
    Function.update_of_ne h₂a, add_assoc, CharTwo.add_self_eq_zero, add_zero,
    Function.update_comm hat.symm, Function.update_idem, Function.update_eq_self]
theorem tempAndCnot_commCleanBracket {M : ℕ} (S : Finset (Wire M)) (c₁ c₂ anc t : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ t) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (hancS : anc ∈ S)
    (htS : t ∉ S) : CommCleanBracket S (tempAndCnot c₁ c₂ anc t h₁₂ h₁a h₂a hat).toBracket := by
  refine ⟨hancS, hcnot_comm_clean (S.erase anc) anc t hat (htS ∘ Finset.mem_of_mem_erase),
    EvalPhasePerm.comm_andInvProj_of_fix (EvalPhasePerm.cnot anc t hat) c₁ c₂ anc fun _ ↦
      ⟨Function.update_of_ne h₁t _ _, Function.update_of_ne h₂t _ _, Function.update_of_ne hat _ _⟩,
    EvalPhasePerm.comm_cleanProj_of_fix (ph := fun _ ↦ 0)
      (f := fun β ↦ Function.update β t (β t + (β anc + β c₁ * β c₂))) (fun β ↦ by
        rw [PhotochemistrySolution.QubitizationWalkSem.bitSign_zero, one_smul]
        exact ((tempAndCnot c₁ c₂ anc t h₁₂ h₁a h₂a hat).toBracket_ket β).trans
          (congrArg _ (tempAndCnot_evalBits c₁ c₂ anc t h₁₂ h₁a h₂a hat h₁t h₂t β)))
      S fun _ w hw ↦ Function.update_of_ne (fun (e : w = t) ↦ htS (e ▸ hw)) _ _⟩
end QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags

namespace QuantumComputation.Specs.PhotochemistrySolution.FastQft8Semantics
open Qubit PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding
  basisBitsEquiv_symm_basisBits basisBits_basisBitsEquiv_symm
theorem embedMatrix_mulVec_ket_diag {M n : ℕ} (r : QRegister M n) (A : Matrix (Fin (2 ^ M))
    (Fin (2 ^ M)) ℂ) (ψ : BitAssignment M → ℂ) (hA : ∀ γ : BitAssignment M, A.mulVec (KinB.ket γ) =
    ψ γ • KinB.ket γ) (β : BitAssignment n) : (r.embedMatrix A).mulVec (KinB.ket β) =
    ψ (fun i ↦ β (r i)) • KinB.ket β := by
  have hentry (l j : Fin (2 ^ M)) : A l j = if l = j then ψ (basisBits M j) else 0 := by
    simpa [PhotochemistrySolution.KinB.ket, basisState, Pi.single_apply] using
      congrFun (hA (basisBits M j)) l
  rw [PhotochemistrySolution.KinB.embedMatrix_mulVec_ket,
    Finset.sum_eq_single (PhotochemistrySolution.KinB.localIdx r β)
      (fun l _ hl ↦ by rw [hentry, ite_eq_right hl, zero_smul])
          (fun h ↦ absurd (Finset.mem_univ _) h),
    hentry, ite_eq_left rfl, show PhotochemistrySolution.KinB.writeReg β r
        (basisBits M (PhotochemistrySolution.KinB.localIdx r β)) = β by
      simp only [KinB.writeReg, show KinB.localIdx r β =
        r.extractIndex ((basisBitsEquiv n).symm β) by simp [QRegister.extractIndex],
        basisBitsEquiv_symm_basisBits, r.replaceIndex_extractIndex, basisBits_basisBitsEquiv_symm],
    basisBits_basisBitsEquiv_symm]
end QuantumComputation.Specs.PhotochemistrySolution.FastQft8Semantics
end

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
open Operator DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding ket ket_CNOT ket_TOFF ket_X
  matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags (ClassicalBracketProg
    tempAndCnot tempAndCnot_evalBits tempAndCnot_commCleanBracket commCleanBracket_wrap)
theorem mod_lt_succ (n k : ℕ) : k % (n + 1) < n + 1 := Nat.mod_lt k (Nat.succ_pos n)
def finMod (n k : ℕ) : Fin (n + 1) := ⟨k % (n + 1), mod_lt_succ n k⟩
def safeCnotCP {M : ℕ} (c t : Wire M) : ComputeProg M := if h : c = t then .id else .cnot c t h
def safeAndGateCP {M : ℕ} (c₁ c₂ anc : Wire M) : ComputeProg M :=
    if h12 : c₁ = c₂ then .id else if h1a : c₁ = anc then .id else if h2a : c₂ =
    anc then .id else .andGate c₁ c₂ anc h12 h1a h2a
def safeCnotCB {M : ℕ} (c t : Wire M) : ClassicalBracketProg M :=
    if h : c = t then .id else .cnot c t h
def safeTempAndCnotCB {M : ℕ} (c₁ c₂ anc t : Wire M) : ClassicalBracketProg M :=
    if h12 : c₁ = c₂ then .id else if h1a : c₁ = anc then .id else if h2a : c₂ =
    anc then .id else if hat : anc = t then .id else tempAndCnot c₁ c₂ anc t h12 h1a h2a hat
def clearBit (m i : ℕ) : ℕ := if m.testBit i then m ^^^ (2 ^ i) else m
theorem testBit_clearBit (m i j : ℕ) : (clearBit m i).testBit j = (m.testBit j && decide (j ≠ i))
    := by
  unfold clearBit
  rcases eq_or_ne i j with rfl | hij
  · split_ifs with hm <;> simp [hm, Nat.testBit_xor]
  · split_ifs with hm <;> simp [hij, hij.symm, Nat.testBit_xor]
def maskFinset (M m : ℕ) : Finset (Wire M) := Finset.univ.filter (fun w : Wire M ↦ m.testBit w.val)
theorem _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.fast_maskFinset_iff
    {A M : ℕ} (f : Fin A → Fin M) (m : ℕ) : Finset.univ.image f = maskFinset M m ↔
    _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.rangeMaskFin f A =
    Nat.land m (Nat.sub (Nat.shiftLeft 1 M) 1) := by
  have hMask (k : ℕ) : (Nat.land m (Nat.sub (Nat.shiftLeft 1 M) 1)).testBit k =
      (decide (k < M) && m.testBit k) := by
    change (m &&& ((1 <<< M) - 1)).testBit k = _
    rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
  refine ⟨fun heq ↦ Nat.eq_of_testBit_eq fun k ↦ ?_, fun heq ↦ Finset.ext fun w ↦ ?_⟩
  · rw [hMask]
    by_cases hkM : k < M
    · have hw := Finset.ext_iff.mp heq ⟨k, hkM⟩
      simp only [maskFinset, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter] at hw
      rw [decide_eq_true hkM, Bool.true_and, Bool.eq_iff_iff,
        _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.testBit_rangeMaskFin_iff f
            A k le_rfl]
      exact ⟨fun ⟨j, _, hj⟩ ↦ hw.mp ⟨j, Fin.ext hj⟩,
        fun hm ↦ (hw.mpr hm).elim fun j hj ↦ ⟨j, j.isLt, congrArg Fin.val hj⟩⟩
    · simp only [hkM, decide_false, Bool.false_and, Bool.eq_false_iff]
      exact fun ht ↦
          ((RangeMask.testBit_rangeMaskFin_iff f A k le_rfl).mp ht).elim
        fun j ⟨_, hj⟩ ↦ hkM (hj ▸ (f j).isLt)
  · have hb :
        (RangeMask.rangeMaskFin f A).testBit w.val = m.testBit w.val := by
      simpa [w.isLt] using (congrArg (·.testBit w.val) heq).trans (hMask w.val)
    simp only [maskFinset, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, ← hb,
      _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.testBit_rangeMaskFin_iff f A
          w.val le_rfl]
    exact ⟨fun ⟨j, hj⟩ ↦ ⟨j, j.isLt, congrArg Fin.val hj⟩, fun ⟨j, _, hj⟩ ↦ ⟨j, Fin.ext hj⟩⟩
theorem _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.fast_maskFinset_fw_iff
    {A M : ℕ} (f : Fin A → Wire M) (m : ℕ) : Finset.univ.image f = maskFinset M m ↔
    _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.rangeMaskFin f A =
    Nat.land m (Nat.sub (Nat.shiftLeft 1 M) 1) :=
    _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.fast_maskFinset_iff f m
@[simp] theorem mem_maskFinset {M m : ℕ} {w : Wire M} : w ∈ maskFinset M m ↔ m.testBit w.val =
    true := by simp [maskFinset]
theorem maskFinset_zero (M : ℕ) : maskFinset M 0 = ∅ := by ext w; simp
theorem maskFinset_two_pow {M : ℕ} (u : Wire M) : maskFinset M (2 ^ u.val) = {u} := by
  ext w; simp only [mem_maskFinset, Finset.mem_singleton, Nat.testBit_two_pow, decide_eq_true_eq];
  exact ⟨fun h ↦ Fin.ext h.symm, fun h ↦ congrArg Fin.val h.symm⟩
theorem maskFinset_lor {M : ℕ} (m₁ m₂ : ℕ) : maskFinset M (m₁ ||| m₂) =
    maskFinset M m₁ ∪ maskFinset M m₂ := by ext w; simp
theorem maskFinset_clearBit {M : ℕ} (m : ℕ) (anc : Wire M) : maskFinset M (clearBit m anc.val) =
    (maskFinset M m).erase anc := by
  ext w;
  simp only [mem_maskFinset, Finset.mem_erase, testBit_clearBit, Bool.and_eq_true,
      decide_eq_true_eq]; exact ⟨fun ⟨h1, h2⟩ ↦ ⟨fun e ↦ h2 (congrArg Fin.val e), h1⟩,
      fun ⟨h2, h1⟩ ↦ ⟨h1, fun e ↦ h2 (Fin.ext e)⟩⟩
theorem disjoint_maskFinset_of_land_eq_zero {M m₁ m₂ : ℕ} (h : (m₁ &&& m₂) = 0) :
    Disjoint (maskFinset M m₁) (maskFinset M m₂) := by
  rw [Finset.disjoint_left]; intro w hw1 hw2; rw [mem_maskFinset] at hw1 hw2
  have hland : (m₁ &&& m₂).testBit w.val = true := by rw [Nat.testBit_land, hw1, hw2]; rfl
  rw [h, Nat.zero_testBit] at hland; exact Bool.noConfusion hland
inductive StructuredCB (M : ℕ) where
  | id
  | x (u : Wire M)
  | cnot (c t : Wire M)
  | seq (p₁ p₂ : StructuredCB M)
  | tempAndCnot (c₁ c₂ anc t : Wire M)
  | wrap (p : ComputeProg M) (mid : StructuredCB M)
namespace StructuredCB
def toCB {M : ℕ} : StructuredCB M → ClassicalBracketProg M
  | .id =>
        .id | .x u => .x u | .cnot c t => safeCnotCB c t | .seq p₁ p₂ =>
                                                             .seq p₁.toCB p₂.toCB
                                                             | .tempAndCnot c₁ c₂ anc t =>
                                                             safeTempAndCnotCB c₁ c₂ anc t
                                                             | .wrap p mid => p.wrapCB mid.toCB
def numTempAnd {M : ℕ} : StructuredCB M → ℕ
  | .id | .x _ | .cnot _ _ => 0 | .seq p₁ p₂ =>
                                    p₁.numTempAnd +
                                    p₂.numTempAnd | .wrap p mid => p.numAnd + mid.numTempAnd
  | .tempAndCnot c₁ c₂ anc t =>
        if c₁ = c₂ then 0 else if c₁ = anc then 0 else if c₂ = anc then 0 else if anc =
        t then 0 else 1
@[simp] theorem toCB_numTempAnd {M : ℕ} (b : StructuredCB M) : b.toCB.numTempAnd =
    b.numTempAnd := by
  induction b with
  | id | x _ => rfl | cnot _ _ =>
                        dsimp only [toCB, numTempAnd, safeCnotCB]; split_ifs <;>
                        rfl | seq _ _ ih₁ ih₂ =>
                                simp [toCB, numTempAnd, ClassicalBracketProg.numTempAnd, ih₁, ih₂]
  | tempAndCnot _ _ _ _ =>
        dsimp only [toCB, numTempAnd, safeTempAndCnotCB]; split_ifs <;>
        rfl | wrap _ _ ih => simp [toCB, numTempAnd, ComputeProg.wrapCB_numTempAnd, ih]
def modTargets {M : ℕ} : StructuredCB M → Finset (Wire M)
  | .id =>
        ∅ | .x u => {u} | .cnot c t =>
                            if c =
                            t then ∅ else {t} | .seq p₁ p₂ =>
                                                  p₁.modTargets ∪ p₂.modTargets
                                                  | .wrap _ mid => mid.modTargets
  | .tempAndCnot c₁ c₂ anc t =>
        if c₁ = c₂ then ∅ else if c₁ = anc then ∅ else if c₂ = anc then ∅ else if anc =
        t then ∅ else {t}
def modMask {M : ℕ} : StructuredCB M → ℕ
  | .id =>
        0 | .x u => 2 ^ u.val | .cnot c t =>
                                  if c =
                                  t then 0 else 2 ^ t.val
                                  | .seq p₁ p₂ =>
                                  p₁.modMask ||| p₂.modMask | .wrap _ mid => mid.modMask
  | .tempAndCnot c₁ c₂ anc t =>
        if c₁ = c₂ then 0 else if c₁ = anc then 0 else if c₂ = anc then 0 else if anc =
        t then 0 else 2 ^ t.val
theorem modTargets_eq_maskFinset {M : ℕ} (b : StructuredCB M) : b.modTargets =
    maskFinset M b.modMask := by
  induction b <;> dsimp only [modTargets, modMask] <;> (try split_ifs) <;>
    simp [maskFinset_zero, maskFinset_two_pow, maskFinset_lor, *]
def finalCleanMask {M : ℕ} (sMask : ℕ) : ComputeProg M → ℕ
  | .id | .x _ | .cnot _ _ _ => sMask | .andGate _ _ anc _ _ _ =>
                                          clearBit sMask anc.val
                                          | .seq p₁ p₂ =>
                                          finalCleanMask (finalCleanMask sMask p₁) p₂
theorem maskFinset_finalCleanMask {M : ℕ} (sMask : ℕ) (p : ComputeProg M) :
    maskFinset M (finalCleanMask sMask p) = p.finalClean (maskFinset M sMask) := by
  induction p generalizing sMask with
    | id
    | x _
    | cnot _ _ _ => rfl
    | andGate _ _ anc _ _ _ => exact maskFinset_clearBit sMask anc
    | seq _ _ ih₁ ih₂ => dsimp only [finalCleanMask, ComputeProg.finalClean]; rw [ih₂, ih₁]
def validProgMask {M : ℕ} (tMask sMask : ℕ) : ComputeProg M → Bool
  | .id =>
        true | .x w =>
                 !tMask.testBit w.val &&
                 !sMask.testBit w.val | .cnot c t _ =>
                                          !tMask.testBit c.val && !tMask.testBit t.val &&
                                          (!sMask.testBit t.val || sMask.testBit c.val)
  | .andGate c₁ c₂ anc _ _ _ =>
        !tMask.testBit c₁.val && !tMask.testBit c₂.val && !tMask.testBit anc.val &&
        sMask.testBit anc.val | .seq p₁ p₂ =>
                                  validProgMask tMask sMask p₁ &&
                                  validProgMask tMask (finalCleanMask sMask p₁) p₂
theorem validProg_of_validProgMask {M tMask sMask : ℕ} {p : ComputeProg M}
    (h : validProgMask tMask sMask p = true) : p.ValidProg (maskFinset M tMask) (maskFinset M sMask)
    := by
  induction p generalizing sMask <;>
    simp_all [validProgMask, ComputeProg.ValidProg, ← maskFinset_finalCleanMask]
def validCleanMask {M : ℕ} (sMask : ℕ) : StructuredCB M → Bool
  | .id =>
        true | .x u => !sMask.testBit u.val | .cnot c t =>
                                                decide (c = t) ||
                                                !sMask.testBit t.val
                                                | .seq p₁ p₂ =>
                                                p₁.validCleanMask sMask && p₂.validCleanMask sMask
  | .tempAndCnot c₁ c₂ anc t =>
        if c₁ = c₂ then true else if c₁ = anc then true else if c₂ = anc then true else if anc =
        t then true else sMask.testBit anc.val && !sMask.testBit t.val && decide (c₁ ≠ t) &&
        decide (c₂ ≠ t)
  | .wrap p mid =>
        let tMask :=
        mid.modMask; decide ((tMask &&& sMask) = 0) && validProgMask tMask sMask p &&
        mid.validCleanMask (finalCleanMask sMask p)
def evalS {M : ℕ} : StructuredCB M → BitAssignment M → BitAssignment M
  | .id, β => β | .x u, β => Function.update β u (β u + 1) | .cnot c t, β =>
        if c = t then β else Function.update β t (β t + β c) | .seq p₁ p₂, β =>
        p₂.evalS (p₁.evalS β)
  | .tempAndCnot c₁ c₂ anc t, β =>
        if c₁ = c₂ then β else if c₁ = anc then β else if c₂ = anc then β else if anc =
        t then β else Function.update β t (β t + (β anc + β c₁ * β c₂))
  | .wrap p mid, β =>
        let γ := mid.evalS (p.fwdBits β); fun w ↦ if w ∈ mid.modTargets then γ w else β w
theorem evalS_outside_modTargets {M : ℕ} (b : StructuredCB M) (β : BitAssignment M) {w : Wire M}
    (hw : w ∉ b.modTargets) : b.evalS β w = β w := by
  induction b generalizing β <;> dsimp only [evalS, modTargets] at hw ⊢ <;>
    (try split_ifs at hw ⊢) <;> simp_all
theorem toCB_evalBits_eq_evalS {M sMask : ℕ} {b : StructuredCB M}
    (hb : b.validCleanMask sMask = true) (β : BitAssignment M) : b.toCB.evalBits β = b.evalS β := by
  induction b generalizing sMask β with
  | id | x _ => rfl | cnot _ _ => dsimp only [toCB, evalS, safeCnotCB]; split_ifs <;> rfl
  | seq _ _ ih₁ ih₂ => obtain ⟨h1, h2⟩ :=
        Bool.and_eq_true_iff.mp hb; dsimp only [toCB, evalS,
        ClassicalBracketProg.evalBits]; rw [ih₁ h1 β, ih₂ h2]
  | tempAndCnot c₁ c₂ anc t =>
      dsimp only [toCB, evalS, validCleanMask, safeTempAndCnotCB] at hb ⊢;
      split_ifs at hb ⊢ with h12 h1a h2a hat <;> [rfl; rfl; rfl; rfl;
        (simp only [Bool.and_eq_true,
            decide_eq_true_eq] at hb; exact tempAndCnot_evalBits c₁ c₂ anc t h12 h1a h2a hat hb.1.2
            hb.2 β)]
  | wrap p mid ih =>
      obtain ⟨⟨_, hpM⟩, hmM⟩ := (Bool.and_eq_true_iff.mp hb).imp_left Bool.and_eq_true_iff.mp;
      have hp : p.DisjointFrom mid.modTargets :=
          ComputeProg.disjointFrom_of_validProg (modTargets_eq_maskFinset mid ▸
          validProg_of_validProgMask hpM)
      have hout : ∀ η w, w ∉ mid.modTargets → mid.toCB.evalBits η w = η w := fun η w hw ↦ by
        rw [ih hmM η]; exact evalS_outside_modTargets mid η hw
      rw [toCB, ComputeProg.wrapCB_evalBits mid.modTargets p mid.toCB hp hout β];
      dsimp only [evalS]; funext w; rw [ih hmM (p.fwdBits β)]
theorem toCB_evalBits_outside {M sMask : ℕ} {b : StructuredCB M}
    (hb : b.validCleanMask sMask = true) (β : BitAssignment M) {w : Wire M}
    (hw : w ∉ b.modTargets) : b.toCB.evalBits β w = β w :=
    (congrFun (toCB_evalBits_eq_evalS hb β) w).trans (evalS_outside_modTargets b β hw)
theorem comm_cleanProj_fixes {M : ℕ} (S : Finset (Wire M)) (p : ClassicalBracketProg M)
    (hS : ∀ β, ∀ w ∈ S, p.evalBits β w = β w) : p.toBracket.toCircuit.eval.1 * cleanProj S =
    cleanProj S * p.toBracket.toCircuit.eval.1 := by
  apply KinB.matrix_ext_ket; intro β;
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket, p.toBracket_ket β,
      cleanProj_mulVec_ket]
  have hiff : (∀ w ∈ S, p.evalBits β w = 0) ↔ (∀ w ∈ S, β w = 0) :=
      ⟨fun h w hw ↦ (hS β w hw).symm.trans (h w hw), fun h w hw ↦ (hS β w hw).trans (h w hw)⟩
  by_cases h0 : ∀ w ∈ S, β w = 0 <;> [rw [ite_eq_left h0, ite_eq_left (hiff.mpr h0),
      p.toBracket_ket β]; rw [ite_eq_right h0, ite_eq_right (mt hiff.mp h0), Matrix.mulVec_zero]]
theorem commCleanBracket_of_validCleanMask {M sMask : ℕ} {b : StructuredCB M}
    (h : b.validCleanMask sMask = true) :
    CommCleanBracket (maskFinset M sMask) b.toCB.toBracket := by
  induction b generalizing sMask with
  | id => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ (Bool.and_eq_true_iff.mp h).1, ih₂ (Bool.and_eq_true_iff.mp h).2⟩
  | x u =>
      exact comm_cleanProj_fixes _ (.x u) fun _ w hw ↦ Function.update_of_ne
        (fun (e : w = u) ↦ Bool.eq_false_iff.mp ((Bool.not_eq_true' _).mp h)
            (mem_maskFinset.mp (e ▸ hw))) _ _
  | cnot c t =>
      dsimp only [toCB, safeCnotCB, validCleanMask] at h ⊢
      split_ifs with hct
      · trivial
      · have ht : (!sMask.testBit t.val) = true := by simpa [hct] using h
        exact comm_cleanProj_fixes _ (.cnot c t hct) fun _ w hw ↦ Function.update_of_ne
          (fun (e : w = t) ↦ Bool.eq_false_iff.mp ((Bool.not_eq_true' _).mp ht)
              (mem_maskFinset.mp (e ▸ hw))) _ _
  | tempAndCnot c₁ c₂ anc t =>
      dsimp only [toCB, safeTempAndCnotCB, validCleanMask] at h ⊢
      split_ifs at h ⊢ with h12 h1a h2a hat <;> try trivial
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      exact tempAndCnot_commCleanBracket _ c₁ c₂ anc t h12 h1a h2a hat h.1.2 h.2
        (mem_maskFinset.mpr h.1.1.1) (mem_maskFinset.not.mpr (Bool.eq_false_iff.mp h.1.1.2))
  | wrap p mid ih =>
      obtain ⟨⟨hdM, hpM⟩, hmM⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
      simpa only [toCB, ComputeProg.wrapCB_toBracket] using commCleanBracket_wrap mid.modTargets
        (maskFinset M sMask) (modTargets_eq_maskFinset mid ▸
          disjoint_maskFinset_of_land_eq_zero (of_decide_eq_true hdM)) p mid.toCB.toBracket
        mid.toCB.evalBits (modTargets_eq_maskFinset mid ▸ validProg_of_validProgMask hpM)
        (maskFinset_finalCleanMask sMask p ▸ ih hmM) mid.toCB.toBracket_ket
        fun γ _ hw ↦ toCB_evalBits_outside hmM γ hw
end StructuredCB
def cpOfList {M : ℕ} (xs : List (ComputeProg M)) : ComputeProg M := xs.foldr .seq .id
def scbOfList {M : ℕ} (xs : List (StructuredCB M)) : StructuredCB M := xs.foldr .seq .id
end QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB

section
set_option exponentiation.threshold 8192
open Operator DynamicCircuit Matrix Circuit QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectWalkerDecode
open Qubit PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
def maskToBits (M m : ℕ) : BitAssignment M := fun w ↦ if m.testBit w.val then 1 else 0
def flipBit (m i : ℕ) : ℕ := m ^^^ (2 ^ i)
def evalMaskCP {M : ℕ} : ComputeProg M → ℕ → ℕ
  | .id, m => m | .x u, m => flipBit m u.val | .cnot c t _, m =>
        if m.testBit c.val then flipBit m t.val else m
  | .andGate c₁ c₂ anc _ _ _, m =>
        if m.testBit c₁.val && m.testBit c₂.val then flipBit m anc.val else m | .seq p₁ p₂,
        m => evalMaskCP p₂ (evalMaskCP p₁ m)
theorem maskToBits_flip {M m : ℕ} (u : Wire M)
    (b : Bool) : maskToBits M (if b then flipBit m u.val else m) =
    Function.update (maskToBits M m) u (maskToBits M m u + if b then 1 else 0) := by
  funext w; by_cases h : w = u
  · subst h; rw [Function.update_self]; dsimp only [maskToBits, flipBit];
    cases b <;> cases hm : m.testBit w.val <;>
        simp [hm, Nat.testBit_xor, Nat.testBit_two_pow_self, CharTwo.add_self_eq_zero]
  · rw [Function.update_of_ne h]; dsimp only [maskToBits, flipBit];
    cases b <;> simp [Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Fin.val_ne_of_ne (Ne.symm h))]
theorem maskToBits_evalMaskCP {M : ℕ} (p : ComputeProg M)
    (m : ℕ) : maskToBits M (evalMaskCP p m) = p.fwdBits (maskToBits M m) := by
  induction p generalizing m with
  | id =>
        rfl | x u => exact maskToBits_flip u true | cnot c t _ =>
                                                      exact maskToBits_flip t (m.testBit c.val)
                                                      | seq _ _ ih₁ ih₂ =>
                                                      dsimp only [evalMaskCP,
                                                      ComputeProg.fwdBits]; rw [ih₂, ih₁]
  | andGate c₁ c₂ anc _ _ _ =>
        dsimp only [evalMaskCP,
        ComputeProg.fwdBits]; rw [maskToBits_flip anc (m.testBit c₁.val &&
        m.testBit c₂.val)]; congr 2; dsimp only [maskToBits]; cases m.testBit c₁.val <;>
        cases m.testBit c₂.val <;> rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectWalkerDecode

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectGidneyFast
open scoped Circuit.Notation Matrix.Norms.L2Operator
open Qubit PhotochemistrySolution.KinB PhotochemistrySolution.QubitizationCore
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.QubitizationKapteyn
  PhotochemistrySolution.SelectRefl
open PhotochemistrySolution.SelectSandwich
def czGateCircuit {M : ℕ} (a b : Wire M) (h : a ≠ b) : Circuit M :=
  Circuit.H b ;;ᶜ Circuit.CNOT a b h ;;ᶜ Circuit.H b
theorem czGateCircuit_isCliffordPrim {M : ℕ} (a b : Wire M)
    (h : a ≠ b) : (AndBracketProg.prim (czGateCircuit a b h)).IsCliffordPrim := by
  simp [AndBracketProg.IsCliffordPrim, czGateCircuit, Circuit.count_seq, Circuit.H, Circuit.CNOT]
def finSeqProg {M : ℕ} : (k : ℕ) → (Fin k → ComputeProg M) → ComputeProg M
  | 0, _ => .id
  | k + 1, f => .seq (finSeqProg k (fun i ↦ f i.castSucc)) (f (Fin.last k))
theorem finSeqProg_numAnd_le {M : ℕ} :
    ∀ (k c : ℕ) (f : Fin k → ComputeProg M),
      (∀ i, (f i).numAnd ≤ c) → (finSeqProg k f).numAnd ≤ k * c
  | 0, _, _, _ => Nat.zero_le _
  | k + 1, c, f, h => by
      simpa only [finSeqProg, ComputeProg.numAnd, Nat.succ_mul] using
        Nat.add_le_add (finSeqProg_numAnd_le k c _ fun i ↦ h i.castSucc) (h (Fin.last k))
def andChainProg {M : ℕ} :
    ∀ (k : ℕ) (rIn : Fin (k + 1) → Wire M) (rClean : Fin k → Wire M),
      (∀ i j, rIn i ≠ rClean j) → (∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂) →
      (∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂) →
      ComputeProg M
  | 0, _, _, _, _, _ => .id
  | 1, rIn, rClean, hIC, _, hIn =>
      .andGate (rIn 0) (rIn 1) (rClean 0) (hIn 0 1 (fun h ↦ nomatch h)) (hIC 0 0) (hIC 1 0)
  | k + 2, rIn, rClean, hIC, hCC, hIn =>
      .seq
        (andChainProg (k + 1) (fun i ↦ rIn i.castSucc) (fun j ↦ rClean j.castSucc)
          (fun i j ↦ hIC i.castSucc j.castSucc)
          (fun j₁ j₂ h ↦ hCC j₁.castSucc j₂.castSucc (Fin.castSucc_injective (k + 1) |>.ne h))
          (fun i₁ i₂ h ↦ hIn i₁.castSucc i₂.castSucc (Fin.castSucc_injective (k + 2) |>.ne h)))
        (.andGate (rClean (Fin.castSucc (Fin.last k))) (rIn (Fin.last (k + 2)))
            (rClean (Fin.last (k + 1)))
          (fun h ↦ hIC (Fin.last (k + 2)) (Fin.castSucc (Fin.last k)) h.symm)
          (hCC (Fin.castSucc (Fin.last k)) (Fin.last (k + 1))
            (by intro h; have hv := congrArg Fin.val h; change k = k + 1 at hv; omega))
          (hIC (Fin.last (k + 2)) (Fin.last (k + 1))))
theorem andChainProg_numAnd {M : ℕ} :
    ∀ (k : ℕ) (rIn : Fin (k + 1) → Wire M) (rClean : Fin k → Wire M)
      (hIC : ∀ i j, rIn i ≠ rClean j)
      (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂)
      (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂),
      (andChainProg k rIn rClean hIC hCC hIn).numAnd = k
  | 0, _, _, _, _, _ => rfl
  | 1, _, _, _, _, _ => rfl
  | k + 2, rIn, rClean, hIC, hCC, hIn => by
      dsimp only [andChainProg, ComputeProg.numAnd]; rw [andChainProg_numAnd (k + 1)]
theorem andChainProg_fwdBits_other {M : ℕ} :
    ∀ (k : ℕ) (rIn : Fin (k + 1) → Wire M) (rClean : Fin k → Wire M)
      (hIC : ∀ i j, rIn i ≠ rClean j)
      (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂)
      (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂)
      (β : BitAssignment M) (w : Wire M), (∀ j, w ≠ rClean j) →
      (andChainProg k rIn rClean hIC hCC hIn).fwdBits β w = β w
  | 0, _, _, _, _, _, _, _, _ => rfl
  | 1, _, rClean, _, _, _, β, w, hw => by
      dsimp only [andChainProg, ComputeProg.fwdBits]; exact Function.update_of_ne (hw 0) _ _
  | k + 2, rIn, rClean, hIC, hCC, hIn, β, w, hw => by
      dsimp only [andChainProg, ComputeProg.fwdBits];
      rw [Function.update_of_ne (hw (Fin.last (k + 1)))]
      exact andChainProg_fwdBits_other (k + 1) _ _ _ _ _ β w (fun j ↦ hw j.castSucc)
theorem andChainProg_fwdBits_last {M : ℕ} :
    ∀ (k : ℕ) (rIn : Fin (k + 2) → Wire M) (rClean : Fin (k + 1) → Wire M)
      (hIC : ∀ i j, rIn i ≠ rClean j)
      (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂)
      (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂)
      (β : BitAssignment M), (∀ j, β (rClean j) = 0) →
      (andChainProg (k + 1) rIn rClean hIC hCC hIn).fwdBits β (rClean (Fin.last k)) =
        ∏ i : Fin (k + 2), β (rIn i)
  | 0, _, _, _, _, _, _, hClean0 => by
      dsimp only [andChainProg, ComputeProg.fwdBits]
      rw [show Fin.last 0 = 0 from rfl, Function.update_self, hClean0 0, zero_add,
        Fin.prod_univ_two]
  | k + 1, rIn, rClean, hIC, hCC, hIn, β, hClean0 => by
      dsimp only [andChainProg, ComputeProg.fwdBits]
      rw [Function.update_self,
        andChainProg_fwdBits_other (k + 1) _ _ _ _ _ β (rClean (Fin.last (k + 1)))
          (fun j ↦ hCC _ _ (Fin.ne_of_gt (Fin.castSucc_lt_last j))),
        hClean0 (Fin.last (k + 1)), zero_add,
        andChainProg_fwdBits_last k _ _ _ _ _ β (fun j ↦ hClean0 j.castSucc),
        andChainProg_fwdBits_other (k + 1) _ _ _ _ _ β (rIn (Fin.last (k + 2)))
          (fun j ↦ hIC _ j.castSucc)]
      exact (Fin.prod_univ_castSucc fun i : Fin (k + 3) ↦ β (rIn i)).symm
theorem andChainProg_finalClean_mem_of_ne {M : ℕ} :
    ∀ (k : ℕ) (wSet : Finset (Wire M))
      (rIn : Fin (k + 1) → Wire M) (rClean : Fin k → Wire M)
      (hIC : ∀ i j, rIn i ≠ rClean j)
      (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂)
      (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂)
      (w : Wire M), w ∈ wSet → (∀ j, w ≠ rClean j) →
      w ∈ (andChainProg k rIn rClean hIC hCC hIn).finalClean wSet
  | 0, _, _, _, _, _, _, _, hw, _ => hw
  | 1, _, _, _, _, _, _, _, hw, hne => Finset.mem_erase.mpr ⟨hne 0, hw⟩
  | k + 2, wSet, _, _, _, _, _, w, hw, hne =>
      Finset.mem_erase.mpr ⟨hne (Fin.last (k + 1)),
        andChainProg_finalClean_mem_of_ne (k + 1) wSet _ _ _ _ _ w hw fun j ↦ hne j.castSucc⟩
theorem andChainProg_validProg_exact {M : ℕ} :
    ∀ (k : ℕ) (tSet wSet : Finset (Wire M))
      (rIn : Fin (k + 1) → Wire M) (rClean : Fin k → Wire M)
      (hIC : ∀ i j, rIn i ≠ rClean j)
      (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂)
      (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂),
      (∀ i, rIn i ∉ tSet) → (∀ j, rClean j ∉ tSet) → (∀ j, rClean j ∈ wSet) →
      (andChainProg k rIn rClean hIC hCC hIn).ValidProg tSet wSet
  | 0, _, _, _, _, _, _, _, _, _, _ => trivial
  | 1, _, _, _, _, _, _, _, hInT, hCleanT, hCleanS => ⟨hInT 0, hInT 1, hCleanT 0, hCleanS 0⟩
  | k + 2, tSet, wSet, _, rClean, _, hCC, _, hInT, hCleanT, hCleanS =>
      ⟨andChainProg_validProg_exact (k + 1) tSet wSet _ _ _ _ _
          (fun i ↦ hInT i.castSucc) (fun j ↦ hCleanT j.castSucc) (fun j ↦ hCleanS j.castSucc),
        hCleanT (Fin.castSucc (Fin.last k)), hInT (Fin.last (k + 2)), hCleanT (Fin.last (k + 1)),
        andChainProg_finalClean_mem_of_ne (k + 1) wSet _ _ _ _ _
          (rClean (Fin.last (k + 1))) (hCleanS (Fin.last (k + 1)))
          fun j ↦ hCC _ _ (Fin.ne_of_gt (Fin.castSucc_lt_last j))⟩
def norChainReflProg {M : ℕ} (m : ℕ) (rLcu : Fin (m + 2) → Wire M) (rClean : Fin (m + 1) → Wire M)
    (hIC : ∀ i j, rLcu i ≠ rClean j) (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂)
    (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rLcu i₁ ≠ rLcu i₂) : ComputeProg M :=
    .seq (finSeqProg (m + 2) (fun i ↦ .x (rLcu i))) (andChainProg (m + 1) rLcu rClean hIC hCC hIn)
theorem norChainReflProg_numAnd {M : ℕ} (m : ℕ) (rLcu : Fin (m + 2) → Wire M)
    (rClean : Fin (m + 1) → Wire M) (hIC : ∀ i j, rLcu i ≠ rClean j)
    (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂) (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rLcu i₁ ≠ rLcu i₂) :
    (norChainReflProg m rLcu rClean hIC hCC hIn).numAnd = m + 1 := by
  simpa [norChainReflProg, ComputeProg.numAnd, andChainProg_numAnd] using
    Nat.eq_zero_of_le_zero (finSeqProg_numAnd_le (m + 2) 0 _ fun _ ↦ le_rfl)
theorem count_toDyn_onRegister_eq {Var : Type} {M n : ℕ} (v : Var) (r : QRegister M n)
    {p : AndBracketProg M} (hp : p.IsCliffordPrim) : ((p.onRegister r).toDyn v).count .T = 4 *
    p.numTempAnd := by
  rw [AndBracketProg.count_toDyn_t v (hp.onRegister r), AndBracketProg.numTempAnd_onRegister]
end QuantumComputation.Specs.PhotochemistrySolution.SelectGidneyFast

namespace QuantumComputation.Specs.PhotochemistrySolution.TargetBScr
open scoped Matrix.Norms.L2Operator
open PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.KinB
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationProgram
open PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectApprox PhotochemistrySolution.SelectDataBuilder
  PhotochemistrySolution.SelectGidneyFast
abbrev IsPhaseDiag {M : ℕ} (U : Operator (2 ^ M)) (φ : BitAssignment M → ZMod 2) : Prop :=
    ∀ β : BitAssignment M, U.mulVec (DynCircExt.ket β) =
    QubitizationWalkSem.bitSign (φ β) • DynCircExt.ket β
theorem IsPhaseDiag.preserves_cleanProj {M : ℕ} {U : Operator (2 ^ M)}
    {φ : BitAssignment M → ZMod 2} (h : IsPhaseDiag U φ) (S : Finset (Wire M)) : cleanProj S *
    (U * cleanProj S) = U * cleanProj S :=
  DynCircExt.matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
    exact if hS : ∀ w ∈ S, β w =
        0 then by rw [ite_eq_left hS, h β, Matrix.mulVec_smul, cleanProj_mulVec_ket, ite_eq_left hS]
      else by rw [ite_eq_right hS, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem IsPhaseDiag.comm_andInvProj {M : ℕ} {U : Operator (2 ^ M)} {φ : BitAssignment M → ZMod 2}
    (h : IsPhaseDiag U φ) (c₁ c₂ anc : Wire M) : U * andInvProj c₁ c₂ anc = andInvProj c₁ c₂ anc *
    U :=
  DynCircExt.matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h β, Matrix.mulVec_smul,
        andInvProj_mulVec_ket]
    split_ifs <;> simp [h β]
theorem IsPhaseDiag.comm_basisOutcomeProjector_zero {M m : ℕ} {U : Operator (2 ^ M)}
    {φ : BitAssignment M → ZMod 2} (h : IsPhaseDiag U φ) (r : QRegister m M) : U *
    r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * U :=
  DynCircExt.matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h β, Matrix.mulVec_smul,
      PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    split_ifs <;> simp [h β]
theorem IsPhaseDiag.wrap_computeProg {M : ℕ} (p : ComputeProg M) {mid : AndBracketProg M}
    {φ : BitAssignment M → ZMod 2} (hmid : IsPhaseDiag mid.toCircuit.eval.1 φ) :
    IsPhaseDiag ((p.wrap mid).toCircuit).eval.1 (fun β ↦ φ (p.fwdBits β)) := by
  have hinv (β : BitAssignment M) (u : Wire M) (v : ZMod 2) :
      Function.update (Function.update β u (β u + v)) u (Function.update β u (β u + v) u + v) =
          β := by
    simp [Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, Function.update_eq_self]
  induction p generalizing mid φ with
  | id => exact hmid
  | seq _ _ ih₁ ih₂ => exact ih₁ (ih₂ hmid)
  | x _ => exact fun β ↦ by simp only [ComputeProg.wrap, ComputeProg.fwdBits,
      AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      DynCircExt.ket_X, hmid _, Matrix.mulVec_smul, hinv]
  | cnot _ _ hct => exact fun β ↦ by simp only [ComputeProg.wrap, ComputeProg.fwdBits,
      AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      DynCircExt.ket_CNOT, hmid _, Matrix.mulVec_smul, Function.update_of_ne hct, hinv]
  | andGate _ _ _ _ h₁a h₂a => exact fun β ↦ by simp only [ComputeProg.wrap, ComputeProg.fwdBits,
      AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      DynCircExt.ket_TOFF, hmid _, Matrix.mulVec_smul, Function.update_of_ne h₁a,
      Function.update_of_ne h₂a, hinv]
theorem validCleanBracket_wrap_phase {M : ℕ} (p : ComputeProg M) (S : Finset (Wire M))
    {mid : AndBracketProg M} {φ : BitAssignment M → ZMod 2} (hp : p.ValidProg ∅ S)
    (hmid_valid : ValidCleanBracket (p.finalClean S) mid)
    (hmid_diag : IsPhaseDiag mid.toCircuit.eval.1 φ) : ValidCleanBracket S (p.wrap mid) := by
  have hpres (S' : Finset (Wire M)) (U : Operator (2 ^ M)) (f : BitAssignment M → BitAssignment M)
      (hU : ∀ β, U.mulVec (DynCircExt.ket β) = DynCircExt.ket (f β))
      (hS' : ∀ β, (∀ w ∈ S', β w = 0) → ∀ w ∈ S', f β w = 0) :
      cleanProj S' * (U * cleanProj S') = U * cleanProj S' :=
    DynCircExt.matrix_ext_ket fun β ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
      exact if h0 : ∀ w ∈ S', β w = 0 then by
        rw [ite_eq_left h0, hU β, cleanProj_mulVec_ket, ite_eq_left (hS' β h0)]
      else by rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  induction p generalizing S mid φ with
  | id => exact hmid_valid
  | x u =>
      have hx := hpres S _ _ (DynCircExt.ket_X u) fun β h0 w hw ↦ by
        simpa [Function.update_of_ne fun (h : w = u) ↦ hp.2 (h ▸ hw)] using h0 w hw
      exact ⟨hx, hmid_valid, hx⟩
  | cnot c t hct =>
      have hc := hpres S _ _ (DynCircExt.ket_CNOT c t hct) fun β h0 ↦
        hp.2.2.elim (fun htS w hw ↦
            by simpa [Function.update_of_ne fun e : w = t ↦ htS (e ▸ hw)] using h0 w hw)
          fun hcS ↦ by simpa [h0 c hcS, Function.update_eq_self] using h0
      exact ⟨hc, hmid_valid, hc⟩
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      exact ⟨hp.2.2.2, hmid_valid, hmid_diag.comm_andInvProj c₁ c₂ anc,
        (hmid_diag.wrap_computeProg (.andGate c₁ c₂ anc h₁₂ h₁a h₂a)).preserves_cleanProj S⟩
  | seq p₁ p₂ ih₁ ih₂ =>
      exact ih₁ S hp.1 (ih₂ (p₁.finalClean S) hp.2 hmid_valid hmid_diag)
        (hmid_diag.wrap_computeProg p₂)
theorem finSeqProg_x_finalClean {M : ℕ} :
    ∀ (k : ℕ) (S : Finset (Wire M)) (f : Fin k → Wire M),
      (finSeqProg k (fun i ↦ .x (f i))).finalClean S = S
  | 0, _, _ => rfl
  | k + 1, S, f => finSeqProg_x_finalClean k S fun i ↦ f i.castSucc
theorem finSeqProg_x_validProg {M : ℕ} :
    ∀ (k : ℕ) (S : Finset (Wire M)) (f : Fin k → Wire M),
      (∀ i, f i ∉ S) → (finSeqProg k (fun i ↦ .x (f i))).ValidProg ∅ S
  | 0, _, _, _ => trivial
  | k + 1, S, _, hf =>
      ⟨finSeqProg_x_validProg k S _ fun i ↦ hf i.castSucc, Finset.notMem_empty _,
        (finSeqProg_x_finalClean k S _).symm ▸ hf (Fin.last k)⟩
theorem finSeqProg_x_fwdBits {M : ℕ} :
    ∀ (k : ℕ) (f : Fin k → Wire M), Function.Injective f →
      ∀ (β : BitAssignment M),
        (∀ i : Fin k, (finSeqProg k (fun j ↦ .x (f j))).fwdBits β (f i) = β (f i) + 1) ∧
        (∀ w : Wire M, (∀ i : Fin k, w ≠ f i) →
          (finSeqProg k (fun j ↦ .x (f j))).fwdBits β w = β w)
  | 0, _, _, _ => ⟨fun i ↦ i.elim0, fun _ _ ↦ rfl⟩
  | k + 1, f, hinj, β => by
      obtain ⟨ih₁, ih₂⟩ := finSeqProg_x_fwdBits k (fun j ↦ f j.castSucc)
        (fun _ _ h ↦ Fin.castSucc_inj.mp (hinj h)) β
      dsimp only [finSeqProg, ComputeProg.fwdBits]
      exact ⟨Fin.lastCases
          ((Function.update_self _ _ _).trans (congrArg (· + 1)
            (ih₂ _ fun j ↦ hinj.ne (Fin.castSucc_lt_last j).ne.symm)))
          (fun j ↦ (Function.update_of_ne
            (hinj.ne (Fin.castSucc_lt_last j).ne) _ _).trans (ih₁ j)),
        fun w hw ↦ (Function.update_of_ne (hw (Fin.last k)) _ _).trans
          (ih₂ w fun j ↦ hw j.castSucc)⟩
theorem bitSign_mul_eq {a b : ZMod 2} : QubitizationWalkSem.bitSign a *
    QubitizationWalkSem.bitSign b = QubitizationWalkSem.bitSign (a + b) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [QubitizationWalkSem.bitSign, show (1 : ZMod 2) + 1 = 0 by decide]
theorem prod_bit_add_one_eq_ite {k : ℕ} (g : Fin k → ZMod 2) : (∏ i : Fin k, (g i + 1)) = if ∀ i :
    Fin k, g i = 0 then (1 : ZMod 2) else 0 := by
  if hall : ∀ i : Fin k, g i = 0 then simp [hall]
  else obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
       simpa [hall, Finset.prod_eq_zero_iff] using
         ⟨i₀, by rw [(bit_cases (g i₀)).resolve_left hi₀, CharTwo.add_self_eq_zero]⟩
theorem IsPhaseDiag.seq_right {M : ℕ} {b₁ b₂ : AndBracketProg M} {φ₁ φ₂ : BitAssignment M → ZMod 2}
    (h₁ : IsPhaseDiag b₁.toCircuit.eval.1 φ₁) (h₂ : IsPhaseDiag b₂.toCircuit.eval.1 φ₂) :
    IsPhaseDiag (b₁.seq b₂).toCircuit.eval.1 (fun β ↦ φ₂ β + φ₁ β) := by
  intro β; change (b₂.toCircuit.eval.1 * b₁.toCircuit.eval.1).mulVec (DynCircExt.ket β) = _;
  rw [← Matrix.mulVec_mulVec, h₁ β, Matrix.mulVec_smul, h₂ β, smul_smul, bitSign_mul_eq, add_comm]
theorem norChainReflBracket_isPhaseDiag {M : ℕ} (m : ℕ) (q : Wire M) (rIn : Fin (m + 2) → Wire M)
    (rClean : Fin (m + 1) → Wire M) (hIC : ∀ i j, rIn i ≠ rClean j)
    (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂) (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂)
    (hq_ne : q ≠ rClean (Fin.last m)) (hinj : Function.Injective rIn) (hqC : ∀ j, q ≠ rClean j)
    (hqI : ∀ i, q ≠ rIn i) :
    IsPhaseDiag (AndBracketProg.seq ((norChainReflProg m rIn rClean hIC hCC hIn).wrap
    (AndBracketProg.prim (czGateCircuit q (rClean (Fin.last m)) hq_ne)))
    (AndBracketProg.prim (Circuit.Z q))).toCircuit.eval.1 (fun β ↦ β q + β q *
    ((norChainReflProg m rIn rClean hIC hCC hIn).fwdBits β (rClean (Fin.last m)))) := by
  intro β
  have hcz :
      IsPhaseDiag (AndBracketProg.prim (czGateCircuit q (rClean (Fin.last m))
      hq_ne)).toCircuit.eval.1 (fun γ ↦ γ q * γ (rClean (Fin.last m))) := fun γ ↦
      czCircuit_mulVec_ket q (rClean (Fin.last m)) hq_ne γ
  have hz : IsPhaseDiag (AndBracketProg.prim (Circuit.Z q)).toCircuit.eval.1 (fun γ ↦ γ q) :=
      fun γ ↦ SelectSymDynInstance.ket_Z_apply q γ
  have hq_pres : (norChainReflProg m rIn rClean hIC hCC hIn).fwdBits β q = β q := by
    dsimp only [norChainReflProg, ComputeProg.fwdBits];
    rw [andChainProg_fwdBits_other (m + 1) rIn rClean hIC hCC hIn _ q hqC];
    exact (finSeqProg_x_fwdBits (m + 2) rIn hinj β).2 q hqI
  have h :=
      ((hcz.wrap_computeProg (norChainReflProg m rIn rClean hIC hCC hIn)).seq_right hz) β; dsimp
      only at h; rw [hq_pres] at h; exact h
theorem norChainReflBracket_valid {M : ℕ} (m : ℕ) (S : Finset (Wire M)) (q : Wire M)
    (rIn : Fin (m + 2) → Wire M) (rClean : Fin (m + 1) → Wire M) (hIC : ∀ i j, rIn i ≠ rClean j)
    (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂) (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rIn i₁ ≠ rIn i₂)
    (hq_ne : q ≠ rClean (Fin.last m)) (hlcu_not_S : ∀ i, rIn i ∉ S)
    (hclean_mem_S : ∀ j, rClean j ∈ S) :
    ValidCleanBracket S (AndBracketProg.seq ((norChainReflProg m rIn rClean hIC hCC hIn).wrap
    (AndBracketProg.prim (czGateCircuit q (rClean (Fin.last m)) hq_ne)))
    (AndBracketProg.prim (Circuit.Z q))) := by
  have hcz :
      IsPhaseDiag (AndBracketProg.prim (czGateCircuit q (rClean (Fin.last m))
      hq_ne)).toCircuit.eval.1 (fun γ ↦ γ q * γ (rClean (Fin.last m))) := fun γ ↦
      czCircuit_mulVec_ket q (rClean (Fin.last m)) hq_ne γ
  have hz : IsPhaseDiag (AndBracketProg.prim (Circuit.Z q)).toCircuit.eval.1 (fun γ ↦ γ q) :=
      fun γ ↦ SelectSymDynInstance.ket_Z_apply q γ
  have hvalid_nor : (norChainReflProg m rIn rClean hIC hCC hIn).ValidProg ∅ S := by
    dsimp only [norChainReflProg, ComputeProg.ValidProg];
    refine ⟨finSeqProg_x_validProg (m + 2) S rIn hlcu_not_S, ?_⟩;
    rw [finSeqProg_x_finalClean (m + 2) S rIn]
    exact andChainProg_validProg_exact (m + 1) ∅ S rIn rClean hIC hCC hIn (fun _ ↦
        Finset.notMem_empty _) (fun _ ↦ Finset.notMem_empty _) hclean_mem_S
  exact ⟨validCleanBracket_wrap_phase (norChainReflProg m rIn rClean hIC hCC hIn) S hvalid_nor
      (hcz.preserves_cleanProj _) hcz, hz.preserves_cleanProj S⟩
theorem norChainReflBracket_mul_clean_eq {M m w : ℕ} (q : Wire M) (rLcuReg : QRegister (m + 2) M)
    (rScrReg : QRegister w M) (rClean : Fin (m + 1) → Wire M) (hIC : ∀ i j, rLcuReg i ≠ rClean j)
    (hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClean j₁ ≠ rClean j₂) (hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rLcuReg i₁ ≠
    rLcuReg i₂) (hq_ne : q ≠ rClean (Fin.last m)) (hqC : ∀ j, q ≠ rClean j)
    (hqI : ∀ i, q ≠ rLcuReg i) (hCleanZero : ∀ (β : BitAssignment M), (∀ j, β (rScrReg j) = 0) →
    ∀ j, β (rClean j) = 0) :
    (AndBracketProg.seq ((norChainReflProg m rLcuReg.wires rClean hIC hCC hIn).wrap
    (AndBracketProg.prim (czGateCircuit q (rClean (Fin.last m)) hq_ne)))
    (AndBracketProg.prim (Circuit.Z q))).toCircuit.eval.1 * rScrReg.basisOutcomeProjector 0 =
    (1 - (2 : ℂ) • ((QRegister.singleton q).basisOutcomeProjector 1 *
    (1 - rLcuReg.basisOutcomeProjector 0))) * rScrReg.basisOutcomeProjector 0 := by
  refine DynCircExt.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hs : ∀ j, β (rScrReg j) = 0
  · have hx := finSeqProg_x_fwdBits (m + 2) rLcuReg.wires rLcuReg.wires.injective β
    rw [ite_eq_left hs, norChainReflBracket_isPhaseDiag m q rLcuReg.wires rClean hIC hCC hIn
      hq_ne rLcuReg.wires.injective hqC hqI β, reflMat_mulVec_ket q rLcuReg β]
    have htop :
        (norChainReflProg m rLcuReg.wires rClean hIC hCC hIn).fwdBits β (rClean (Fin.last m)) = _ :=
      (andChainProg_fwdBits_last m rLcuReg.wires rClean hIC hCC hIn _ fun j ↦
        (hx.2 (rClean j) fun i h ↦ hIC i j h.symm).trans (hCleanZero β hs j)).trans
        (Finset.prod_congr rfl fun i _ ↦ hx.1 i)
    dsimp only; rw [htop, prod_bit_add_one_eq_ite]
    by_cases hl : ∀ i : Fin (m + 2), β (rLcuReg i) = 0 <;> rcases bit_cases (β q) with hq | hq <;>
      simp [hl, hq, CharTwo.add_self_eq_zero]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
end QuantumComputation.Specs.PhotochemistrySolution.TargetBScr

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectStructKinComp
open Qubit PhotochemistrySolution.KinB PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SelectCompactAnc
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
def checkKinSCBFast {M : ℕ} (sMask : ℕ) : StructuredCB M → ℕ × ℕ × Bool
  | .id =>
        (0, 0,
        true) | .x u =>
                  (0, 2 ^ u.val,
                  !sMask.testBit u.val) | .cnot c t =>
                                            if c = t then (0, 0, true) else (0, 2 ^ t.val,
                                            !sMask.testBit t.val)
  | .seq p₁ p₂ => let r₁ := checkKinSCBFast sMask p₁;
    let r₂ := checkKinSCBFast sMask p₂; (r₁.1 + r₂.1, r₁.2.1 ||| r₂.2.1, r₁.2.2 && r₂.2.2)
  | .tempAndCnot c₁ c₂ anc t =>
        if c₁ = c₂ then (0, 0, true) else if c₁ = anc then (0, 0, true) else if c₂ = anc then (0, 0,
        true) else if anc = t then (0, 0, true) else (1, 2 ^ t.val, sMask.testBit anc.val &&
        !sMask.testBit t.val && decide (c₁ ≠ t) && decide (c₂ ≠ t))
  | .wrap p mid =>
        let r :=
        checkKinSCBFast (StructuredCB.finalCleanMask sMask p) mid; (p.numAnd + r.1, r.2.1,
        decide ((r.2.1 &&& sMask) = 0) && StructuredCB.validProgMask r.2.1 sMask p && r.2.2)
theorem checkKinSCBFast_eq {M : ℕ} (b : StructuredCB M) (sMask : ℕ) : checkKinSCBFast sMask b =
    (b.numTempAnd, b.modMask, b.validCleanMask sMask) := by
  induction b generalizing sMask with
  | id | x _ => rfl | cnot _ _ =>
                        dsimp only [checkKinSCBFast, StructuredCB.numTempAnd, StructuredCB.modMask,
                        StructuredCB.validCleanMask]; split_ifs with h <;> simp [h]
  | seq _ _ ih₁ ih₂ =>
        simp only [checkKinSCBFast, ih₁, ih₂, StructuredCB.numTempAnd, StructuredCB.modMask,
        StructuredCB.validCleanMask]
  | tempAndCnot _ _ _ _ =>
        dsimp only [checkKinSCBFast, StructuredCB.numTempAnd, StructuredCB.modMask,
        StructuredCB.validCleanMask]; split_ifs <;> rfl
  | wrap _ _ ih =>
        simp only [checkKinSCBFast, ih, StructuredCB.numTempAnd, StructuredCB.modMask,
        StructuredCB.validCleanMask]
theorem of_checkKinSCBFast {M n m s : ℕ} {b : StructuredCB M}
    (h : checkKinSCBFast s b = (n, m, true)) : b.numTempAnd = n ∧ b.modMask = m ∧
    b.validCleanMask s = true := by
  rw [checkKinSCBFast_eq] at h; injection h with h1 h2; injection h2 with h2 h3; exact ⟨h1, h2, h3⟩
end QuantumComputation.Specs.PhotochemistrySolution.SelectStructKinComp

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectQft8CatLocal
open scoped Circuit.Notation
open Qubit QFT PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectDataBuilder PhotochemistrySolution.SelectFastQft8Gidney
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem eval_H_eq_embedMatrix8_noSym {M : ℕ} (rP : QRegister 8 M)
    (ℓ : Fin 8) : (Circuit.H (rP ℓ)).eval.1 = rP.embedMatrix (hadamardAt 8 ℓ).1 := by
  have hcomp : rP.compose (QRegister.singleton ℓ) = QRegister.singleton (rP ℓ) := by ext i : 1; rfl
  have hmat : PrimitiveGate.H.eval.1 = (hadamardUnitary (q := 1)).1 := by
    ext i j; change ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1]) i j = hadamardMatrix 1 i j
    rw [show (Real.sqrt (1 / 2) : ℝ) = 1 / Real.sqrt 2 by rw [one_div, Real.sqrt_inv, one_div]]
    fin_cases i <;> fin_cases j <;> simp [hadamardMatrix, dotProduct, Complex.real_smul, pow_one,
        show basisBits 1 1 0 = 1 from rfl]
  change (Circuit.single .H (rP ℓ)).eval.1 = rP.embedMatrix (hadamardAt 8 ℓ).1
  rw [Circuit.eval_single, QRegister.embedUnitary_val, hmat, ← hcomp, rP.embedMatrix_compose]; rfl
theorem eval_polySwapAll8Circ_eq_swapAllUnitary_noSym {M : ℕ} (rP : QRegister 8 M) :
    (polySwapAll8Circ rP).eval.1 = rP.embedMatrix (QFT.swapAllUnitary 8).1 := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  let idx := (basisBitsEquiv M).symm β;
  have hidx : basisBits M idx = β := (basisBitsEquiv M).apply_symm_apply β;
  have hk : KinB.ket β = Pi.single idx 1 := rfl
  have hrhs : (rP.embedMatrix (QFT.swapAllUnitary 8).1).mulVec (KinB.ket β) =
      KinB.ket (basisBits M (rP.replaceIndex idx (bitRevEquiv 8 (rP.extractIndex idx)))) := by
    have hperm : (QFT.swapAllUnitary 8).1.mulVec (Pi.single (rP.extractIndex idx) 1) =
        Pi.single (bitRevEquiv 8 (rP.extractIndex idx)) 1 :=
        KineticStep.swapAllUnitary_mulVec_basisState 8 (rP.extractIndex idx); rw [hk,
        rP.embedMatrix_mulVec_single_factors, hperm,
        QRegister.tensorState_single_replaceIndex]; exact congrArg basisState
        ((basisBitsEquiv M).symm_apply_apply _).symm
  simp only [polySwapAll8Circ, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ket_polySwapWire2Circ, hrhs]
  congr 1; ext w; by_cases hw : w ∈ Set.range rP.wires
  · obtain ⟨i, rfl⟩ :=
        hw; rw [QRegExt.basisBits_replaceIdx_apply, basisBits_bitRevEquiv_coe,
        (QRegExt.basisBits_extractIdx rP), hidx]; fin_cases i <;> simp [rP.wires.injective.eq_iff,
            Fin.rev]
  · rw [QRegExt.basisBits_replaceIdx_of_not_mem _ _ _ _ hw,
        hidx]; have hne : ∀ k : Fin 8, w ≠ rP k := fun k h ↦
                 hw ⟨k, h.symm⟩; simp [Function.update_of_ne, hne 0, hne 1, hne 2, hne 3, hne 4,
                 hne 5, hne 6, hne 7]
theorem localOnQft16_add_proj_noSym {M : ℕ} (rP rCat : QRegister 8 M) (rClean13 : QRegister 13 M)
    {A B : Operator (2 ^ M)} (hA : LocalOnQft16 rP rCat A) (hB : LocalOnQft16 rP rCat B) :
    LocalOnQft16 rP rCat (A * rClean13.basisOutcomeProjector 0 + B *
        (1 - rClean13.basisOutcomeProjector 0)) := fun α G hG ↦ by
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  split_ifs
  · simpa only [sub_self, Matrix.mulVec_zero, add_zero] using hA α G hG
  · simpa only [Matrix.mulVec_zero, zero_add, sub_zero] using hB α G hG
end QuantumComputation.Specs.PhotochemistrySolution.SelectQft8CatLocal

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectQft8CatKick
open scoped Circuit.Notation
open Qubit QFT PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectDataBuilder PhotochemistrySolution.SelectFastQft8Gidney
open PhotochemistrySolution.SelectQft8CatLocal
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem mul_cat_clean13_eq_of_mulVec_noSym {M : ℕ} (rCat : QRegister 8 M)
    (rClean13 : QRegister 13 M) (hCatClean : rCat.DisjointWires rClean13) (A B : Operator (2 ^ M))
    (h : ∀ env : rCat.Environment → ZMod 2,
    (∀ i : Fin 13, basisBits M (rCat.basisSplitEquiv.symm (0, env)) (rClean13 i) = 0) →
    A.mulVec (rCat.tensorState (PgBase.phaseGradientState 8) (Pi.single env 1)) =
    B.mulVec (rCat.tensorState (PgBase.phaseGradientState 8) (Pi.single env 1))) : A *
    (rCat.embedMatrix catState8Mat * rClean13.basisOutcomeProjector 0) = B *
    (rCat.embedMatrix catState8Mat * rClean13.basisOutcomeProjector 0) := by
  refine Matrix.ext_of_mulVec_single fun inIdx ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  let y₀ := rCat.extractIndex inIdx
  let env := (rCat.basisSplitEquiv inIdx).2
  have hket : Pi.single inIdx (1 : ℂ) = DynCircExt.ket (basisBits M inIdx) :=
    congrArg basisState ((basisBitsEquiv M).symm_apply_apply inIdx).symm
  have hout (i : Fin 13) :
      basisBits M inIdx (rClean13 i) = basisBits M (rCat.basisSplitEquiv.symm (0, env)) (rClean13 i)
          :=
    congrFun (congrArg Prod.snd (rCat.basisSplitEquiv.apply_symm_apply (0, env))).symm
      ⟨rClean13 i, fun ⟨b, hb⟩ ↦ hCatClean.ne b i hb⟩
  rw [hket, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hc : ∀ i : Fin 13, basisBits M (rCat.basisSplitEquiv.symm (0, env)) (rClean13 i) = 0
  · rw [ite_eq_left (fun i ↦ (hout i).trans (hc i)), ← hket,
      show Pi.single inIdx (1 : ℂ) = rCat.tensorState (Pi.single y₀ 1) (Pi.single env 1) from
        funext fun k ↦ by
          dsimp only [QRegister.tensorState]
          exact if hk : k = inIdx then by subst hk; simp [y₀, env]
            else if h1 : rCat.extractIndex k = y₀ then by
              simp [hk, h1, show (rCat.basisSplitEquiv k).2 ≠ env from
                fun h2 ↦ hk (rCat.basisSplitEquiv.injective (Prod.ext h1 h2))]
            else by simp [Pi.single_apply, hk, h1],
      rCat.embedMatrix_mulVec_tensorState, show catState8Mat.mulVec (Pi.single y₀ 1) =
        star (PgBase.phaseGradientState 8 y₀) • PgBase.phaseGradientState 8 from funext fun y ↦ by
          simp [catState8Mat, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply,
              mul_comm],
      QRegister.tensorState_smul_left, Matrix.mulVec_smul, Matrix.mulVec_smul, h env hc]
  · rw [ite_eq_right (fun h' ↦ hc fun i ↦ (hout i).symm.trans (h' i)),
      Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
end QuantumComputation.Specs.PhotochemistrySolution.SelectQft8CatKick

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3
open Qubit QFT PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectDataBuilder
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket
theorem qft8Stg3_bnds (scrW off : ℕ) (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) : 1 ≤ scrW ∧ (34 + off) +
    7 ≤ ancWOfScr scrW ∧ (41 + off) + 6 ≤ ancWOfScr scrW ∧ (34 + off) + 13 ≤ ancWOfScr scrW ∧
    (47 + off) + 8 ≤ ancWOfScr scrW := by unfold ancWOfScr; omega
abbrev qft8Stg3Delta7 (scrW off : ℕ) (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) :
    QRegister 7 (totDimCompactGen scrW) :=
    (locAncCompactGen scrW).slice (34 + off) 7 (qft8Stg3_bnds scrW off hoff).2.1
abbrev qft8Stg3Carry6 (scrW off : ℕ) (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) :
    QRegister 6 (totDimCompactGen scrW) :=
    (locAncCompactGen scrW).slice (41 + off) 6 (qft8Stg3_bnds scrW off hoff).2.2.1
abbrev qft8Stg3Clean13 (scrW off : ℕ) (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) :
    QRegister 13 (totDimCompactGen scrW) :=
    (locAncCompactGen scrW).slice (34 + off) 13 (qft8Stg3_bnds scrW off hoff).2.2.2.1
def Qft8Stg3ValidP (scrW off : ℕ) (rP : QRegister 8 (totDimCompactGen scrW)) : Prop :=
    ∀ k : Fin 8, ∃ p : Fin (ancWOfScr scrW), rP k = locAncCompactGen scrW p ∧ 35 ≤ p.val ∧ p.val <
    34 + off
theorem qft8Stg3_rP_disj_cat8 {scrW off : ℕ} {rP : QRegister 8 (totDimCompactGen scrW)}
    (hP : Qft8Stg3ValidP scrW off rP) : rP.DisjointWires (locCat8SharedCompactGen scrW) :=
    QRegister.disjoint_iff.mpr fun k c h ↦ by
  obtain ⟨p, hp, _, _⟩ := hP k;
  have hv :=
      congrArg Fin.val ((locAncCompactGen scrW).wires.injective (hp.symm.trans h)); change p.val =
      0 + (26 + c.val) at hv; omega
theorem qft8Stg3_rP_disj_delta7 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW)
    {rP : QRegister 8 (totDimCompactGen scrW)} (hP : Qft8Stg3ValidP scrW off rP) :
    rP.DisjointWires (qft8Stg3Delta7 scrW off hoff) := QRegister.disjoint_iff.mpr fun k i h ↦ by
  obtain ⟨p, hp, _, _⟩ := hP k;
  have hv :=
      congrArg Fin.val ((locAncCompactGen scrW).wires.injective (hp.symm.trans h)); change p.val =
      (34 + off) + i.val at hv; omega
theorem qft8Stg3_rP_disj_carry6 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW)
    {rP : QRegister 8 (totDimCompactGen scrW)} (hP : Qft8Stg3ValidP scrW off rP) :
    rP.DisjointWires (qft8Stg3Carry6 scrW off hoff) := QRegister.disjoint_iff.mpr fun k i h ↦ by
  obtain ⟨p, hp, _, _⟩ := hP k;
  have hv :=
      congrArg Fin.val ((locAncCompactGen scrW).wires.injective (hp.symm.trans h)); change p.val =
      (41 + off) + i.val at hv; omega
theorem qft8Stg3_delta7_disj_cat8 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) :
    (qft8Stg3Delta7 scrW off hoff).DisjointWires (locCat8SharedCompactGen scrW) :=
    QRegister.disjoint_iff.mpr fun i c h ↦ by
  have hv :=
      congrArg Fin.val ((locAncCompactGen scrW).wires.injective h); change (34 + off) + i.val = 0 +
      (26 + c.val) at hv; omega
theorem qft8Stg3_delta7_disj_carry6 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) :
    (qft8Stg3Delta7 scrW off hoff).DisjointWires (qft8Stg3Carry6 scrW off hoff) :=
    QRegister.disjoint_iff.mpr fun i j h ↦ by
  have hv :=
      congrArg Fin.val ((locAncCompactGen scrW).wires.injective h); change (34 + off) + i.val =
      (41 + off) + j.val at hv; omega
theorem qft8Stg3_cat8_disj_carry6 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) :
    (locCat8SharedCompactGen scrW).DisjointWires (qft8Stg3Carry6 scrW off hoff) :=
    QRegister.disjoint_iff.mpr fun c j h ↦ by
  have hv :=
      congrArg Fin.val ((locAncCompactGen scrW).wires.injective h); change 0 + (26 + c.val) =
      (41 + off) + j.val at hv; omega
theorem qft8Stg3_clean13_sub_delta7 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW)
    (i : Fin 7) : qft8Stg3Clean13 scrW off hoff ⟨i.val, by omega⟩ =
    qft8Stg3Delta7 scrW off hoff i := rfl
theorem qft8Stg3_clean13_sub_carry6 {scrW off : ℕ} (hoff : 1 ≤ off ∧ off + 21 ≤ scrW)
    (i : Fin 6) : qft8Stg3Clean13 scrW off hoff ⟨7 + i.val, by omega⟩ =
    qft8Stg3Carry6 scrW off hoff i :=
    congrArg (locAncCompactGen scrW).wires
    (Fin.ext (by change (34 + off) + (7 + i.val) = (41 + off) + i.val; omega))
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
noncomputable abbrev qft8Stg3IdealU (scrW : ℕ) (rP : QRegister 8 (totDimCompactGen scrW)) :
    Unitary (2 ^ totDimCompactGen scrW) := rP.embedUnitary qftGridUnitary
end QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3
end

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectKinThreshCore
open Operator DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
theorem fwdBits_safeAnd {M : ℕ} {c₁ c₂ a : Wire M} (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ a) (h2a : c₂ ≠ a)
    (γ : BitAssignment M) : (safeAndGateCP c₁ c₂ a).fwdBits γ = Function.update γ a (γ a + γ c₁ *
    γ c₂)
    := by
  dsimp only [safeAndGateCP]; rw [dite_eq_right h12, dite_eq_right h1a, dite_eq_right h2a]; rfl
end QuantumComputation.Specs.PhotochemistrySolution.SelectKinThreshCore

namespace QuantumComputation.Specs.PhotochemistrySolution.StrictNatMask
set_option exponentiation.threshold 512
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
/-- Force `x : ℕ`. -/
def strictNat {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  match x with | 0 => k 0 | n + 1 => k (n + 1)
@[simp] theorem strictNat_eq {α : Type} (x : ℕ) (k : ℕ → α) : strictNat x k = k x := by
  cases x <;> rfl
end QuantumComputation.Specs.PhotochemistrySolution.StrictNatMask
end

noncomputable section

open QuantumComputation.Specs.PhotochemistrySolution.SelectWalkerDecode
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Init
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem um_sa {N M : ℕ} (m : Fin N → Wire M) (hinj : Function.Injective m) (u : Wire N)
    (v0 v1 : ZMod 2) (hv : v0 = v1) (β : BitAssignment M) (w : Wire M) :
    Function.update β (m u) v0 w =
      if h : ∃ q : Fin N, m q = w then Function.update (fun q ↦
          β (m q)) u v1 h.choose else β w := by
  split_ifs with h
  · rcases eq_or_ne h.choose u with hqu | hqu
    · simpa only [← hqu, h.choose_spec, Function.update_self] using hv
    · simpa only [Function.update_of_ne fun e ↦ hqu (hinj (h.choose_spec.trans e)),
        Function.update_of_ne hqu] using (congrArg β h.choose_spec).symm
  · exact Function.update_of_ne (fun e ↦ h ⟨u, e.symm⟩) _ _
theorem mba_sa (n q : ℕ) (v : Fin n) : maskToBits n q v = (((q / 2 ^ v.val) % 2 : ℕ) : ZMod 2)
    := by
  change (if ((1 &&& (q >>> v.val)) != 0) then (1 : ZMod 2) else 0) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  rcases (by omega : (q / 2 ^ v.val) % 2 = 0 ∨ (q / 2 ^ v.val) % 2 = 1) with h | h <;> simp [h]
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Init
end

noncomputable section
open Operator QProg DynamicCircuit Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
  QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Init
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectKinThreshCore
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.StrictNatMask (strictNat strictNat_eq)
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
abbrev w304 (i : ℕ) : Wire 304 := finMod 303 i
def mapCP {N M : ℕ} (m : Fin N → Wire M) : ComputeProg N → ComputeProg M
  | .id => .id
  | .x u => .x (m u)
  | .cnot c t _ => safeCnotCP (m c) (m t)
  | .andGate c₁ c₂ a _ _ _ => safeAndGateCP (m c₁) (m c₂) (m a)
  | .seq p₁ p₂ => .seq (mapCP m p₁) (mapCP m p₂)
theorem mapCP_fwd {N M : ℕ} (m : Fin N → Wire M) (hinj : Function.Injective m) :
    ∀ (p : ComputeProg N) (β : BitAssignment M) (w : Wire M),
      (mapCP m p).fwdBits β w = if h : ∃ u : Fin N, m u = w then p.fwdBits (fun q ↦
          β (m q)) h.choose else β w
  | .id, _, w => by
      dsimp only [mapCP, ComputeProg.fwdBits]
      exact if h : ∃ u : Fin N, m u = w then by rw [dite_eq_left h, h.choose_spec]
        else by rw [dite_eq_right h]
  | .x u, β, w => um_sa m hinj u _ _ rfl β w
  | .cnot c t hct, β, w => by
      simpa [mapCP, ComputeProg.fwdBits, safeCnotCP, hinj.ne hct] using um_sa m hinj t _ _ rfl β w
  | .andGate c₁ c₂ a h12 h1a h2a, β, w => by
      simpa only [mapCP, ComputeProg.fwdBits,
        fwdBits_safeAnd (hinj.ne h12) (hinj.ne h1a) (hinj.ne h2a)] using um_sa m hinj a _ _ rfl β w
  | .seq p₁ p₂, β, w => by
      have hp : (fun q ↦ (mapCP m p₁).fwdBits β (m q)) = p₁.fwdBits (fun q ↦ β (m q)) :=
        funext fun q ↦ let hq : ∃ v, m v = m q := ⟨q, rfl⟩
          (mapCP_fwd m hinj p₁ β _).trans
            ((dite_eq_left hq).trans (congrArg _ (hinj hq.choose_spec)))
      dsimp only [mapCP, ComputeProg.fwdBits]
      exact if h : ∃ u : Fin N, m u = w then by
          rw [mapCP_fwd m hinj p₂, dite_eq_left h, dite_eq_left h, hp]
        else by
          rw [mapCP_fwd m hinj p₂, dite_eq_right h, dite_eq_right h,
            mapCP_fwd m hinj p₁, dite_eq_right h]
theorem mapCP_fwd_apply {N M : ℕ} (m : Fin N → Wire M) (hinj : Function.Injective m)
    (p : ComputeProg N)
    (β : BitAssignment M) (u : Fin N) : (mapCP m p).fwdBits β (m u) = p.fwdBits (fun q ↦
        β (m q)) u :=
  let hu : ∃ q : Fin N, m q = m u := ⟨u, rfl⟩
  (mapCP_fwd m hinj p β (m u)).trans ((dite_eq_left hu).trans (congrArg (p.fwdBits _)
      (hinj hu.choose_spec)))
theorem mapCP_fwd_outside {N M : ℕ} (m : Fin N → Wire M) (hinj : Function.Injective m)
    (p : ComputeProg N)
    (β : BitAssignment M) (w : Wire M) (hw : ∀ u : Fin N, m u ≠ w) : (mapCP m p).fwdBits β w =
        β w :=
  (mapCP_fwd m hinj p β w).trans (dite_eq_right fun ⟨u, e⟩ ↦ hw u e)
def decGateN (Npred c : ℕ) : ComputeProg (Npred + 1) :=
    if c % 4 = 1 then .x (finMod Npred (c / 4)) else if c % 4 =
    2 then safeCnotCP (finMod Npred ((c / 4) % 32)) (finMod Npred ((c / 128) % 32)) else if c % 4 =
    3 then safeAndGateCP (finMod Npred ((c / 4) % 32)) (finMod Npred ((c / 128) % 32))
    (finMod Npred (c / 4096)) else .id
def pLo13 : ComputeProg 13 :=
    cpOfList ([ 17, 21, 25, 29, 33283, 514, 162, 674, 37511, 1186, 162, 646, 294, 806, 41739, 1318,
    294, 778, 426, 938, 45967, 1450, 426, 910, 49811].map (decGateN 12))
def pHi13 : ComputeProg 13 :=
    cpOfList ([ 13, 17, 21, 25, 34, 546, 37379, 1186, 34, 514, 166, 678, 41607, 1318, 166, 646, 298,
    810, 45835, 1450, 298, 778, 430, 942, 50063, 1582, 430, 910, 13, 49].map (decGateN 12))
def pHiUnx13 : ComputeProg 13 :=
    cpOfList ([ 49, 13, 910, 942, 778, 810, 646, 678, 514, 546, 17, 21, 25, 13].map (decGateN 12))
def pLoUnx12 : ComputeProg 12 :=
    cpOfList ([ 910, 938, 778, 806, 646, 674, 514, 17, 21, 25, 29].map (decGateN 11))
def embLo25 (u : Fin 13) : Wire 25 :=
    finMod 24 ([0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24].getD u.val 0)
def embHi25 (u : Fin 13) : Wire 25 :=
    finMod 24 ([4, 5, 6, 7, 12, 13, 14, 15, 19, 20, 21, 22, 23].getD u.val 0)
def embHiUnx24 (u : Fin 13) : Wire 24 :=
    finMod 23 ([4, 5, 6, 7, 12, 13, 14, 15, 19, 20, 21, 22, 23].getD u.val 0)
def embLoUnx24 (u : Fin 12) : Wire 24 :=
    finMod 23 ([0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19].getD u.val 0)
def pAxis25 : ComputeProg 25 := .seq (mapCP embLo25 pLo13) (mapCP embHi25 pHi13)
def pAxisUnx24 : ComputeProg 24 := .seq (mapCP embHiUnx24 pHiUnx13) (mapCP embLoUnx24 pLoUnx12)
def axMap25 (ax : Fin 3) (u : Fin 25) : Wire 304 :=
    if u.val < 8 then w304 (8 * ax.val + u.val) else if u.val < 16 then w304 (24 + 8 * ax.val +
    (u.val - 8)) else w304 (50 + 9 * ax.val + (u.val - 16))
def axMap24 (ax : Fin 3) (u : Fin 24) : Wire 304 :=
    axMap25 ax ⟨u.val, Nat.lt_trans u.isLt (Nat.lt_succ_self 24)⟩
def pPre304 : ComputeProg 304 :=
    cpOfList [mapCP (axMap25 0) pAxis25, mapCP (axMap25 1) pAxis25, mapCP (axMap25 2) pAxis25]
def byteOfBits (f : Fin 8 → ZMod 2) : Fin 256 := ⟨finBitsVal f, finBitsVal_lt f⟩
def nibVal (f : Fin 4 → ZMod 2) : ℕ := (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val
def tcNib (f : Fin 4 → ZMod 2) : ℤ := if (f 3).val = 1 then (nibVal f : ℤ) - 16 else (nibVal f : ℤ)
theorem mask9_of_bits (f : Fin 9 → ZMod 2) :
    let m := (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val + 16 * (f 4).val + 32 *
      (f 5).val + 64 * (f 6).val + 128 * (f 7).val + 256 * (f 8).val
    m < 512 ∧ ∀ u : Fin 13, maskToBits 13 m u = (if h : u.val < 9 then f ⟨u.val,
      h⟩ else 0) := by
  intro m
  have _ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := ⟨ZMod.val_lt (f 0), ZMod.val_lt (f 1),
    ZMod.val_lt (f 2), ZMod.val_lt (f 3), ZMod.val_lt (f 4), ZMod.val_lt (f 5),
    ZMod.val_lt (f 6), ZMod.val_lt (f 7), ZMod.val_lt (f 8)⟩
  have hz {b : ZMod 2} {k : ℕ} (hk : k = b.val) : (k : ZMod 2) = b := hk ▸ b.natCast_zmod_val
  refine ⟨by dsimp only [m]; omega, fun u ↦ (mba_sa 13 m u).trans ?_⟩
  fin_cases u <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, 
    Nat.reducePow, Nat.reduceLT, ↓reduceDIte] <;>
    exact hz (by simp only [m, ZMod.val_zero]; omega)
def mn_sa (q : ℕ) (sh : ℕ) : ℕ :=
    ((q / sh) % 2) + 2 * ((q / (2 * sh)) % 2) + 4 * ((q / (4 * sh)) % 2) + 8 * ((q / (8 * sh)) % 2)
def mt_sa (q : ℕ) (sh : ℕ) : ℤ :=
    if (q / (8 * sh)) % 2 = 1 then (mn_sa q sh : ℤ) - 16 else (mn_sa q sh : ℤ)
def es_sa {M : ℕ} : ComputeProg M → ℕ → ℕ
  | .seq p₁ p₂, m => strictNat (es_sa p₁ m) (es_sa p₂)
  | g, m => evalMaskCP g m
theorem ese_sa {M : ℕ} : ∀ (p : ComputeProg M) (m : ℕ),
    es_sa p m = evalMaskCP p m
  | .seq p₁ p₂, m =>
      (strictNat_eq (es_sa p₁ m) (es_sa p₂)).trans
        ((congrArg _ (ese_sa p₁ m)).trans (ese_sa p₂ _))
  | .id, _ | .x _, _ | .cnot _ _ _, _ | .andGate _ _ _ _ _ _, _ => rfl
theorem mne_sa (q : ℕ) (_hq : q < 8192) :
    nibVal (fun k ↦ maskToBits 13 q ⟨k.val, by omega⟩) = mn_sa q 1 ∧
    nibVal (fun k ↦ maskToBits 13 q ⟨4 + k.val, by omega⟩) = mn_sa q 16 ∧
    tcNib (fun k ↦ maskToBits 13 q ⟨k.val, by omega⟩) = mt_sa q 1 ∧
    tcNib (fun k ↦ maskToBits 13 q ⟨4 + k.val, by omega⟩) = mt_sa q 16 := by
  have hv (v : Fin 13) : (maskToBits 13 q v).val = (q / 2 ^ v.val) % 2 :=
    mba_sa 13 q v ▸ ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))
  simp [tcNib, nibVal, mt_sa, mn_sa, hv, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
theorem alf_sa : ∀ m : Fin 256,
    strictNat (es_sa pLo13 m.val) (fun o ↦
    strictNat (es_sa pLoUnx12 (o % 4096)) (fun u ↦
      decide (o < 8192 ∧ o % 16 = m.val % 16 ∧
    mn_sa o 16 + 16 * ((o / 2048) % 2) = 15 + mn_sa m.val 1 - mn_sa m.val 16 ∧
    (o / 4096) % 2 = ((o / 16) % 2) * ((o / 32) % 2) ∧
    u < 4096 ∧ u % 256 = m.val))) = true := by decide +kernel
theorem ahf_sa : ∀ m : Fin 512,
    strictNat (es_sa pHi13 m.val) (fun o ↦
    strictNat (es_sa pHiUnx13 o) (fun u ↦
      decide (o < 8192 ∧ o % 16 = m.val % 16 ∧
    (mn_sa o 16 : ℤ) + 16 * (1 - ((o / 4096) % 2 : ℤ)) =
      15 + mt_sa m.val 1 - mt_sa m.val 16 + ((m.val / 256) % 2 : ℤ) ∧
    (o / 256) % 2 = (m.val / 256) % 2 ∧
    u < 8192 ∧ u % 512 = m.val))) = true := by decide +kernel

theorem atc_sa : ∀ m : Fin 256,
    let f : Fin 8 → ZMod 2 := fun k ↦ maskToBits 8 m.val k;
    twosComplement_frozen (byteOfBits f) = (nibVal (fun k ↦ f ⟨k.val, by omega⟩) : ℤ) + 16 * tcNib
      (fun k ↦ f ⟨4 + k.val, by omega⟩) := by decide +kernel

theorem axis_micro_certs :
    (∀ m : Fin 256,
      let g := maskToBits 13 m.val;
      let o := pLo13.fwdBits g;
      (∀ k : Fin 4, o ⟨k.val, by omega⟩ = g ⟨k.val, by omega⟩) ∧
      nibVal (fun k ↦ o ⟨4 + k.val, by omega⟩) + 16 * (o ⟨11, by decide⟩).val =
    15 + nibVal (fun k ↦ g ⟨k.val, by omega⟩) - nibVal (fun k ↦ g ⟨4 + k.val, by omega⟩) ∧
      o ⟨12, by decide⟩ = o ⟨4, by decide⟩ * o ⟨5, by decide⟩ ∧
      ∀ q : Fin 8,
    (pLoUnx12.fwdBits (fun u : Fin 12 ↦ o ⟨u.val, by omega⟩)) ⟨q.val, by omega⟩ =
      g ⟨q.val, by omega⟩) ∧
    (∀ m : Fin 512,
      let g := maskToBits 13 m.val;
      let o := pHi13.fwdBits g;
      (∀ k : Fin 4, o ⟨k.val, by omega⟩ = g ⟨k.val, by omega⟩) ∧
      (nibVal (fun k ↦ o ⟨4 + k.val, by omega⟩) : ℤ) + 16 * (1 - (o ⟨12, by decide⟩).val) =
    15 + tcNib (fun k ↦ g ⟨k.val, by omega⟩) - tcNib (fun k ↦ g ⟨4 + k.val, by omega⟩) +
      (g ⟨8, by decide⟩).val ∧
      o ⟨8, by decide⟩ = g ⟨8, by decide⟩ ∧
      ∀ q : Fin 9, (pHiUnx13.fwdBits o) ⟨q.val, by omega⟩ = g ⟨q.val, by omega⟩) ∧
    (∀ m : Fin 256,
      let f : Fin 8 → ZMod 2 := fun k ↦ maskToBits 8 m.val k;
      twosComplement_frozen (byteOfBits f) =
    (nibVal (fun k ↦ f ⟨k.val, by omega⟩) : ℤ) + 16 * tcNib (fun k ↦
      f ⟨4 + k.val, by omega⟩)) := by
  have hv2 (x : ℕ) : (((x % 2 : ℕ) : ZMod 2)).val = x % 2 :=
    ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))
  refine ⟨fun m ↦ ?_, fun m ↦ ?_, atc_sa⟩
  · obtain ⟨ho_lt, ho_mod, ho_add, ho_and, _, hu_mod⟩ :=
      (by simpa [strictNat_eq, ese_sa, decide_eq_true_eq] using alf_sa m : _)
    dsimp only
    rw [← maskToBits_evalMaskCP pLo13 m.val]
    set o := evalMaskCP pLo13 m.val
    have hpull12 : (fun u : Fin 12 ↦ maskToBits 13 o ⟨u.val, by omega⟩) =
        maskToBits 12 (o % 4096) := funext fun u ↦ by
      rw [mba_sa, mba_sa]; fin_cases u <;> exact congrArg Nat.cast (by dsimp; omega)
    refine ⟨fun k ↦ ?_, ?_, ?_, fun q ↦ ?_⟩
    · rw [mba_sa, mba_sa]; fin_cases k <;> exact congrArg Nat.cast (by dsimp; omega)
    · rwa [(mne_sa o ho_lt).2.1, (mne_sa m.val (by omega)).1, (mne_sa m.val (by omega)).2.1,
        mba_sa, hv2]
    · simpa only [mba_sa, Nat.reducePow, ← Nat.cast_mul] using congrArg Nat.cast ho_and
    · rw [hpull12, ← maskToBits_evalMaskCP pLoUnx12 (o % 4096), mba_sa, mba_sa]
      fin_cases q <;> exact congrArg Nat.cast (by dsimp; omega)
  · obtain ⟨ho_lt, ho_mod, ho_add, ho_c3, _, hu_mod⟩ :=
      (by simpa [strictNat_eq, ese_sa, decide_eq_true_eq] using ahf_sa m : _)
    dsimp only
    rw [← maskToBits_evalMaskCP pHi13 m.val]
    set o := evalMaskCP pHi13 m.val
    refine ⟨fun k ↦ ?_, ?_, ?_, fun q ↦ ?_⟩
    · rw [mba_sa, mba_sa]; fin_cases k <;> exact congrArg Nat.cast (by dsimp; omega)
    · rwa [(mne_sa o ho_lt).2.1, (mne_sa m.val (by omega)).2.2.1, (mne_sa m.val (by omega)).2.2.2,
        mba_sa, mba_sa, hv2, hv2]
    · simpa only [mba_sa, Nat.reducePow] using congrArg (Nat.cast (R := ZMod 2)) ho_c3
    · rw [← maskToBits_evalMaskCP pHiUnx13 o, mba_sa, mba_sa]
      fin_cases q <;> exact congrArg Nat.cast (by dsimp; omega)
theorem tc_byte_split (f : Fin 8 → ZMod 2) :
    twosComplement_frozen (byteOfBits f) =
      (nibVal (fun k ↦ f ⟨k.val, by omega⟩) : ℤ) + 16 * tcNib (fun k ↦
        f ⟨4 + k.val, by omega⟩) := by
  have hm := mask9_of_bits (fun j : Fin 9 ↦ if h : j.val < 8 then f ⟨j.val, h⟩ else 0)
  have heq : (fun k : Fin 8 ↦ maskToBits 8 (byteOfBits f).val k) = f := by
    funext k; have hk := hm.2 ⟨k.val, by omega⟩
    have hv : (byteOfBits f).val = (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val + 16 *
        (f 4).val + 32 * (f 5).val + 64 * (f 6).val + 128 * (f 7).val := by
      dsimp only [byteOfBits, finBitsVal];
      change (f 0).val + 2 * ((f 1).val + 2 * ((f 2).val + 2 * ((f 3).val + 2 * ((f 4).val + 2 *
          ((f 5).val + 2 * ((f 6).val + 2 * ((f 7).val + 2 * 0))))))) = _; ring
    dsimp only [maskToBits] at hk ⊢; have hk9 : k.val < 9 := by omega
    rw [hv]; simpa [k.isLt, hk9] using hk
  simpa only [heq] using axis_micro_certs.2.2 (byteOfBits f)

abbrev DToken := ℕ × List ℕ × Bool
def axTokens (ax : ℕ) : List DToken :=
  let u := fun k : ℕ => 24 + 8 * ax + k; let cb := 57 + 9 * ax; let p01 := 58 + 9 * ax;
  [(0, [u 0], true), (2, [p01], false), (8, [cb], true)] ++
  ((List.range 6).map fun k => (k + 2, [u (k + 2)], false)) ++
  ((List.range 8).map fun k => (k + 8, [u k, cb], false)) ++
  (((List.range 8).flatMap fun i => ((List.range 8).map fun j => (i, j))).filterMap fun ij =>
    if ij.1 < ij.2 /\ ¬ (ij.1 = 0 /\ ij.2 = 1) then some (ij.1 + ij.2, [u ij.1, u ij.2],
        true) else none)
def initTokens : List DToken :=
    axTokens 0 ++ axTokens 1 ++ axTokens 2 ++ [(2, [], true), (16, [], true), (17, [], true)]
def splitTok : ℕ -> List DToken -> DToken × List DToken
  | _, [] => ((0, [], false), [])
  | 0, x :: xs => (x, xs)
  | n + 1, x :: xs => let r := splitTok n xs; (r.1, x :: r.2)
def xorTokCP (target : ℕ) (tok : DToken) : ComputeProg 304 :=
    .seq (if tok.2.2 then .x (w304 target) else .id)
    (cpOfList (tok.2.1.map fun s => safeCnotCP (w304 s) (w304 target)))
def stepDadda (pool : List DToken) (c : ℕ) : List DToken × ComputeProg 304 :=
  let tag := c % 4;
  if tag = 0 then
    let k0 := (c / 4) % 256; let wOut := c / 1024; let (t0, p1) := splitTok k0 pool;
    (p1 ++ [(t0.1, [wOut], false)], xorTokCP wOut t0)
  else if tag = 1 then
    let k0 := (c / 4) % 256; let k1 := (c / 1024) % 256; let k2 := (c / 262144) % 256;
    let wC := c / 67108864;
    let (t0, p1) := splitTok k0 pool; let (t1, p2) := splitTok k1 p1;
    let (t2, p3) := splitTok k2 p2;
    let wS := t0.2.1.headD 0;
    (p3 ++ [(t0.1, [wS], false), (t0.1 + 1, [wC], false)],
      cpOfList [xorTokCP wS t2, xorTokCP 49 t1, xorTokCP 49 t2, safeAndGateCP (w304 wS) (w304 49)
          (w304 wC),
                xorTokCP 49 t2, xorTokCP 49 t1, xorTokCP wC t2, xorTokCP wS t1])
  else if tag = 2 then
    let k0 := (c / 4) % 256; let k1 := (c / 1024) % 256; let wC := c / 262144;
    let (t0, p1) := splitTok k0 pool; let (t1, p2) := splitTok k1 p1; let wS := t0.2.1.headD 0;
    (p2 ++ [(t0.1, [wS], false), (t0.1 + 1, [wC], false)],
      cpOfList [xorTokCP 49 t1, safeAndGateCP (w304 wS) (w304 49) (w304 wC),
                safeCnotCP (w304 49) (w304 wS), xorTokCP 49 t1])
  else
    let k0 := (c / 4) % 256; let k1 := (c / 1024) % 256;
    let (t0, p1) := splitTok k0 pool; let (t1, p2) := splitTok k1 p1; let wS := t0.2.1.headD 0;
    (p2 ++ [(17, [wS], false)], xorTokCP wS t1)
def runDaddaList : List DToken -> List ℕ -> List DToken × ComputeProg 304
  | pool, [] => (pool, .id)
  | pool, c :: cs =>
        let r1 := stepDadda pool c; let r2 := runDaddaList r1.1 cs; (r2.1, .seq r1.2 r2.2)
def d2WireList : List ℕ :=
    [77, 78, 76, 83, 90, 92, 101, 113, 125, 137, 149, 161, 180, 187, 192, 197, 203, 206]
def d2Wire (k : Fin 18) : Wire 304 := w304 (d2WireList.getD k.val 0)
def tokBit (t : DToken) (γ : BitAssignment 304) : ZMod 2 :=
    (if t.2.2 then 1 else 0) + t.2.1.foldr (fun s acc => γ (w304 s) + acc) 0
def poolSum (pool : List DToken) (γ : BitAssignment 304) : ℕ :=
    pool.foldr (fun t acc => (tokBit t γ).val * 2 ^ t.1 + acc) 0
def isDaddaOwned (w : ℕ) : Bool :=
  (w == 58 || w == 67 || w == 76 || 77 <= w) && w < 207
def inNatList : ℕ -> List ℕ -> Bool
  | _, [] => false
  | x, y :: ys => (x == y) || inNatList x ys
def tokAvoid (forb : List ℕ) (t : DToken) : Bool := t.2.1.all fun s => s < 304 && !inNatList s forb
def daddaInv (pool : List DToken) (cm : List ℕ) (γ0 γ : BitAssignment 304) : Prop :=
    γ (w304 49) = 0 /\ (∀ u : Wire 304, isDaddaOwned u.val = false -> u.val ≠ 49 -> γ u =
    γ0 u) /\ (∀ a : ℕ, inNatList a cm = true -> a < 304 /\ γ (w304 a) =
    0) /\ poolSum pool γ % 262144 = poolSum initTokens γ0 % 262144
def wfDaddaStep (pool : List DToken) (cm : List ℕ) (c : ℕ) : Option (List ℕ) :=
  let tag := c % 4;
  if tag = 0 then
    let k0 := (c / 4) % 256; let wOut := c / 1024; let (t0, p1) := splitTok k0 pool;
    if k0 < pool.length && isDaddaOwned wOut && inNatList wOut cm &&
       tokAvoid [wOut] t0 && p1.all (tokAvoid [wOut]) then some (cm.filter (· != wOut)) else none
  else if tag = 1 then
    let k0 := (c / 4) % 256; let k1 := (c / 1024) % 256; let k2 := (c / 262144) % 256;
    let wC := c / 67108864;
    let (t0, p1) := splitTok k0 pool; let (t1, p2) := splitTok k1 p1;
    let (t2, p3) := splitTok k2 p2;
    let wS := t0.2.1.headD 0;
    if k0 < pool.length && k1 < p1.length && k2 < p2.length &&
       t0.2.1 == [wS] && !t0.2.2 && t1.1 == t0.1 && t2.1 == t0.1 &&
       isDaddaOwned wS && isDaddaOwned wC && wS != wC && !inNatList wS cm && inNatList wC cm &&
       tokAvoid [wS, wC, 49] t1 && tokAvoid [wS, wC, 49] t2 && p3.all (tokAvoid [wS, wC, 49])
    then some (cm.filter (· != wC)) else none
  else if tag = 2 then
    let k0 := (c / 4) % 256; let k1 := (c / 1024) % 256; let wC := c / 262144;
    let (t0, p1) := splitTok k0 pool; let (t1, p2) := splitTok k1 p1; let wS := t0.2.1.headD 0;
    if k0 < pool.length && k1 < p1.length &&
       t0.2.1 == [wS] && !t0.2.2 && t1.1 == t0.1 &&
       isDaddaOwned wS && isDaddaOwned wC && wS != wC && !inNatList wS cm && inNatList wC cm &&
       tokAvoid [wS, wC, 49] t1 && p2.all (tokAvoid [wS, wC, 49])
    then some (cm.filter (· != wC)) else none
  else
    let k0 := (c / 4) % 256; let k1 := (c / 1024) % 256;
    let (t0, p1) := splitTok k0 pool; let (t1, p2) := splitTok k1 p1; let wS := t0.2.1.headD 0;
    if k0 < pool.length && k1 < p1.length &&
       t0.1 == 17 && t0.2.1 == [wS] && !t0.2.2 && t1.1 == 17 &&
       isDaddaOwned wS && !inNatList wS cm && tokAvoid [wS, 49] t1 && p2.all (tokAvoid [wS, 49])
    then some cm else none

theorem poolSum_append (a b : List DToken) (γ : BitAssignment 304) : poolSum (a ++ b) γ =
    poolSum a γ + poolSum b γ := by
  induction a with
  | nil => simp [poolSum]
  | cons _ _ ih =>
    simpa only [poolSum, List.cons_append, List.foldr_cons, add_assoc] using congrArg (_ + ·) ih
theorem splitTok_sum : ∀ (pool : List DToken) (k : ℕ), k < pool.length → ∀ (γ : BitAssignment 304),
    poolSum pool γ = (tokBit (splitTok k pool).1 γ).val * 2 ^ (splitTok k pool).1.1 +
      poolSum (splitTok k pool).2 γ /\ (splitTok k pool).2.length = pool.length - 1
  | [], _, hk, _ => nomatch hk
  | _ :: _, 0, _, _ => by simp [splitTok, poolSum]
  | _ :: xs, n + 1, hk, γ => by
      obtain ⟨h1, h2⟩ := splitTok_sum xs n (Nat.lt_of_succ_lt_succ hk) γ
      simp only [poolSum, splitTok, List.foldr_cons, List.length_cons] at hk h1 h2 ⊢
      exact ⟨by omega, by omega⟩
theorem w304_ne_of_ne {a b : ℕ} (ha : a < 304) (hb : b < 304) (hne : a ≠ b)
    : w304 a ≠ w304 b := fun e ↦ hne (by
    simpa only [w304, finMod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using congrArg Fin.val e)
theorem foldr_w304_update (target : ℕ) (ht : target < 304) (ws : List ℕ) (hav : ws.all
  (fun s ↦ s < 304 && decide (s ≠ target)) = true) (γ : BitAssignment 304) (v : ZMod 2) :
    ws.foldr (fun s acc ↦ Function.update γ (w304 target) v (w304 s) + acc) 0 = ws.foldr
      (fun s acc ↦ γ (w304 s) + acc) 0 := by
  induction ws with
  | nil => rfl
  | cons r rs ihr =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hav
    simp only [List.foldr, Function.update_of_ne (w304_ne_of_ne hav.1.1 ht hav.1.2), ihr hav.2]
theorem xorList_fwd (target : ℕ) (ht : target < 304) (ws : List ℕ) (hav : ws.all
  (fun s => s < 304 && decide (s ≠ target)) = true) (γ : BitAssignment 304) :
    (cpOfList (ws.map fun s => safeCnotCP (w304 s) (w304 target))).fwdBits γ = Function.update γ
      (w304 target) (γ (w304 target) + ws.foldr (fun s acc => γ (w304 s) + acc) 0) := by
  induction ws generalizing γ with
  | nil => simp [cpOfList, ComputeProg.fwdBits]
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hav
    change (cpOfList (ss.map fun r => safeCnotCP (w304 r) (w304 target))).fwdBits
      ((safeCnotCP (w304 s) (w304 target)).fwdBits γ) = _
    rw [ih hav.2, show (safeCnotCP (w304 s) (w304 target)).fwdBits γ =
        Function.update γ (w304 target) (γ (w304 target) + γ (w304 s)) by
      simp only [safeCnotCP, w304_ne_of_ne hav.1.1 ht hav.1.2, ↓reduceDIte, ComputeProg.fwdBits],
      foldr_w304_update target ht ss hav.2, Function.update_idem, Function.update_self]
    exact congrArg (Function.update γ (w304 target)) (by dsimp only [List.foldr]; abel)
theorem xorTokCP_fwd (target : ℕ) (ht : target < 304) (tok : DToken) (hav : tok.2.1.all
  (fun s => s < 304 && decide (s ≠ target)) = true) (γ : BitAssignment 304) :
    (xorTokCP target tok).fwdBits γ =
      Function.update γ (w304 target) (γ (w304 target) + tokBit tok γ) := by
  rcases tok with ⟨b, ws, inv⟩
  dsimp only [xorTokCP, ComputeProg.fwdBits] at hav ⊢
  cases inv <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ComputeProg.fwdBits, xorList_fwd target ht ws hav,
      foldr_w304_update target ht ws hav, Function.update_idem, Function.update_self, tokBit] <;>
    exact congrArg (Function.update γ (w304 target)) (by abel)
theorem tokAvoid_imp (forb : List ℕ) (target : ℕ) (ht : inNatList target forb = true)
    (t : DToken) (h : tokAvoid forb t = true) :
    t.2.1.all (fun s => s < 304 && decide (s ≠ target)) = true := by
  simp only [tokAvoid, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at h ⊢
  exact fun s hs ↦ ⟨(h s hs).1, fun e ↦ Bool.noConfusion ((e ▸ ht).symm.trans (h s hs).2)⟩
theorem tokBit_congr (forb : List ℕ) (t : DToken) (h : tokAvoid forb t = true)
    (γ γ' : BitAssignment 304) (heq : ∀ u : Wire 304, inNatList u.val forb = false -> γ' u = γ u) :
    tokBit t γ' = tokBit t γ := by
  rcases t with ⟨b, ws, inv⟩
  dsimp only [tokBit]; congr 1; dsimp only [tokAvoid] at h
  induction ws with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h;
    have hw : (w304 s).val = s :=
        Nat.mod_eq_of_lt h.1.1; dsimp only [List.foldr]; rw [heq (w304 s) (hw.symm ▸ h.1.2), ih h.2]
theorem poolSum_congr (forb : List ℕ) (ps : List DToken) (h : ps.all (tokAvoid forb) = true)
    (γ γ' : BitAssignment 304) (heq : ∀ u : Wire 304, inNatList u.val forb = false -> γ' u = γ u) :
    poolSum ps γ' = poolSum ps γ := by
  induction ps with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h; dsimp only [poolSum, List.foldr];
    rw [tokBit_congr forb t h.1 γ γ' heq]; exact congrArg _ (ih h.2)
theorem inNatList_filter : ∀ (cm : List ℕ) (a w0 : ℕ),
    inNatList a (cm.filter (· != w0)) = true → inNatList a cm = true /\ a ≠ w0
  | [], _, _, h => Bool.noConfusion h
  | x :: xs, a, w0, h => by
    rw [List.filter] at h
    rcases hx : (x != w0) with _ | _
    · rw [hx] at h
      obtain ⟨h1, h2⟩ := inNatList_filter xs a w0 h
      exact ⟨by simp [inNatList, h1], h2⟩
    · rw [hx] at h
      simp only [inNatList, Bool.or_eq_true, beq_iff_eq] at h ⊢
      exact h.elim (fun e ↦ ⟨Or.inl e, fun e' ↦ by simp [← e, e', bne] at hx⟩)
        fun hr ↦ (inNatList_filter xs a w0 hr).imp Or.inr id
theorem owned_facts (w : ℕ) (h : isDaddaOwned w = true) : w < 304 /\ w ≠ 49 := by
  simp only [isDaddaOwned, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega
theorem upd_outside_forb (forb : List ℕ) (w0 : ℕ) (hw0 : w0 < 304) (hin : inNatList w0 forb = true)
    (γ δ : BitAssignment 304) (val : ZMod 2) (heq : ∀ u : Wire 304, inNatList u.val forb =
    false -> δ u = γ u) : ∀ u : Wire 304, inNatList u.val forb =
    false -> Function.update δ (w304 w0) val u = γ u := by
  refine fun u hu ↦ (Function.update_of_ne (fun e : u = w304 w0 ↦ ?_) val δ).trans (heq u hu)
  simp [e, w304, finMod, Nat.mod_eq_of_lt hw0, hin] at hu
theorem nonown_notIn3 (wS wC : ℕ) (hwS : isDaddaOwned wS = true) (hwC : isDaddaOwned wC = true)
    (u : Wire 304) (hu : isDaddaOwned u.val = false) (hu49 : u.val ≠ 49) : inNatList u.val [wS, wC,
    49] = false := by
  simp only [inNatList, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨fun e => Bool.noConfusion ((e ▸ hu).symm.trans hwS),
    fun e => Bool.noConfusion ((e ▸ hu).symm.trans hwC), hu49, trivial⟩
theorem clean_step3 (cm : List ℕ) (wS wC : ℕ) (hwS_not : inNatList wS cm = false)
    (γ δ : BitAssignment 304) (v49 : δ (w304 49) = 0) (hcl : ∀ a : ℕ, inNatList a cm = true -> a <
    304 /\ γ (w304 a) = 0) (hf : ∀ u : Wire 304, inNatList u.val [wS, wC, 49] = false -> δ u =
    γ u) : ∀ a : ℕ, inNatList a (cm.filter (· != wC)) = true -> a < 304 /\ δ (w304 a) = 0 := by
  intro a ha
  obtain ⟨hacm, hneC⟩ := inNatList_filter cm a wC ha
  refine ⟨(hcl a hacm).1,
    if ha49 : a = 49 then ha49 ▸ v49 else (hf (w304 a) ?_).trans (hcl a hacm).2⟩
  simp [w304, finMod, Nat.mod_eq_of_lt (hcl a hacm).1, inNatList, hneC, ha49,
    show a ≠ wS from fun e ↦ Bool.noConfusion ((e ▸ hacm).symm.trans hwS_not)]
theorem tokBit_single (t : DToken) (w : ℕ) (hw : t.2.1 = [w]) (hi : t.2.2 = false)
    (γ : BitAssignment 304) : tokBit t γ = γ (w304 w) := by simp [tokBit, hw, hi]
theorem zmod2_fa_alg (x y z : ZMod 2) : (0 + y + z + z + y : ZMod 2) = 0 /\ (x + z + y : ZMod 2) =
    x + y + z /\ (0 + (x + z) * (0 + y + z) + z : ZMod 2) = (x + z) * (y + z) + z /\ x.val + y.val +
    z.val = (x + y + z).val + 2 * ((x + z) * (y + z) + z).val := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
theorem zmod2_ha_alg (x y : ZMod 2) : (0 + y + y : ZMod 2) = 0 /\ (0 + x * (0 + y) : ZMod 2) = x *
    y /\ (x + (0 + y) : ZMod 2) = x + y /\ x.val + y.val = (x + y).val + 2 * (x * y).val := by
  fin_cases x <;> fin_cases y <;> decide
theorem zmod2_x17_mod (x y : ZMod 2) : (x + y).val * 2 ^ 17 % 262144 = (x.val * 2 ^ 17 +
  y.val * 2 ^ 17) % 262144 := by fin_cases x <;> fin_cases y <;> decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
end
end


noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate ComplexConjugate
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
  PhotochemistrySolution.SelectDataBuilder PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.DiagShiftSpecBridge
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectCompactRot34
  PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.OvBidir
  PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectGidneyFast
  PhotochemistrySolution.TargetBScr PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SelectCsa64GqspWalk PhotochemistrySolution.SelectCsa64ThreeSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open scoped Matrix.Norms.L2Operator
theorem compose_basisOutcomeProjector_zero {M n w : ℕ} (rComp : QRegister M n)
    (rSub : QRegister w M) : (rComp.compose rSub).basisOutcomeProjector 0 =
    rComp.embedMatrix (rSub.basisOutcomeProjector 0) := rComp.embedMatrix_compose rSub (compProj 0)
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr zGateCirc czCircuit
def SubspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (R_in R_out : Operator (2 ^ n)) (p : DynamicCircuit Var n) : Prop :=
    ∀ M : Observable (Fin (2 ^ n)), ∃ N : Observable (Fin (2 ^ n)), wp p.compile (fun _ ↦ M) =
    (fun _ ↦ N) ∧ R_outᴴ * M.1.1 * R_out = R_inᴴ * N.1.1 * R_in
theorem SubspaceStep.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R₀ R₁ R₂ : Operator (2 ^ n)} {p₁ p₂ : DynamicCircuit Var n} (h₁ : SubspaceStep R₀ R₁ p₁)
    (h₂ : SubspaceStep R₁ R₂ p₂) : SubspaceStep R₀ R₂ (.seq p₁ p₂) := fun M ↦
    let ⟨N₂, hw₂, hm₂⟩ :=
    h₂ M; let ⟨N₁, hw₁, hm₁⟩ :=
            h₁ N₂; ⟨N₁, by change wp p₁.compile (wp p₂.compile (fun _ ↦ M)) = _; rw [hw₂, hw₁],
            hm₂.trans hm₁⟩
theorem SubspaceStep.of_clean {Var : Type} [Fintype Var] [DecidableEq Var] {n w : ℕ}
    [NeZero (2 ^ n)] {rWork : QRegister w n} {U : Unitary (2 ^ n)} {p : DynamicCircuit Var n}
    {R : Operator (2 ^ n)} (h : CleanWorkStep rWork U p) (hc : rWork.basisOutcomeProjector 0 * R =
    R) : SubspaceStep R (U.1 * R) p := fun M ↦
    let ⟨N, hw, hm⟩ :=
    h.2 M; have hc' : Rᴴ * rWork.basisOutcomeProjector 0 = Rᴴ :=
             (by simpa only [Matrix.conjTranspose_mul,
                   rWork.basisOutcomeProjector_conjTranspose 0] using congrArg Matrix.conjTranspose
                   hc);
                   have h1 : (U.1 * R)ᴴ * M.1.1 * (U.1 * R) = Rᴴ * (rWork.basisOutcomeProjector 0 *
                   (U.1ᴴ * M.1.1 * U.1) * rWork.basisOutcomeProjector 0) * R :=
                   (by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]; rw [hc,
                         ← Matrix.mul_assoc Rᴴ (rWork.basisOutcomeProjector 0),
                         hc']);
                         have h2 : Rᴴ * (rWork.basisOutcomeProjector 0 * N.1.1 *
                         rWork.basisOutcomeProjector 0) * R = Rᴴ * N.1.1 * R :=
                         (by simp only [Matrix.mul_assoc]; rw [hc,
                               ← Matrix.mul_assoc Rᴴ (rWork.basisOutcomeProjector 0),
                               hc']); ⟨N, hw,
                               h1.trans ((congrArg (fun X ↦ Rᴴ * X * R) hm).trans h2)⟩
noncomputable def stepCB {w N : ℕ} (r : QRegister w N) (f : BitAssignment w → BitAssignment w)
    (δ : BitAssignment N) : BitAssignment N := DynCircExt.writeReg δ r (f (fun k ↦ δ (r k)))
attribute [local irreducible] QRegister.basisOutcomeProjector projOneQCompactGen
theorem proj_absorb_gen {w₁ w₂ n : ℕ} (r₁ : QRegister w₁ n) (r₂ : QRegister w₂ n)
    (hsub : ∀ j : Fin w₂, ∃ i : Fin w₁, r₂ j = r₁ i) : r₂.basisOutcomeProjector 0 *
    r₁.basisOutcomeProjector 0 =
    r₁.basisOutcomeProjector 0 := by refine KinB.matrix_ext_ket fun β ↦
                                       ?_; rw [← Matrix.mulVec_mulVec,
                                       SelectRefl.ket_basisOutcomeProjector_zero]; exact if h0 :
                                       ∀ i : Fin w₁, β (r₁ i) =
                                       0 then
                                       by rw [ite_eq_left h0,
                                            SelectRefl.ket_basisOutcomeProjector_zero,
                                            ite_eq_left fun j ↦
                                            let ⟨i, hi⟩ :=
                                            hsub j; hi ▸ h0 i] else
                                            by rw [ite_eq_right h0, Matrix.mulVec_zero]
end QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate ComplexConjugate
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
  PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.SelectCsa64ThreeSpec
  PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.DiagShiftSpecBridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
theorem unembedReg_inj {a M N : ℕ} (r : QRegister a N) (hr : ∀ i : Fin a, (r i).val < M) :
    Function.Injective (fun i : Fin a ↦ (⟨(r i).val, hr i⟩ : Wire M)) :=
  fun _ _ h ↦ r.wires.injective (Fin.ext (Fin.mk.inj h))
abbrev unembedReg {a M N : ℕ} (r : QRegister a N) (hr : ∀ i : Fin a, (r i).val < M) :
    QRegister a M where
  wires := { toFun := fun i ↦ ⟨(r i).val, hr i⟩, inj' := unembedReg_inj r hr }
def AllWiresLtCirc (M : ℕ) {N : ℕ} : Circuit N → Prop
  | .identity => True
  | .gate _ r => ∀ i, (r i).val < M
  | .seq c₁ c₂ => AllWiresLtCirc M c₁ ∧ AllWiresLtCirc M c₂
def AllWiresLtDyn (M : ℕ) {Var : Type} {N : ℕ} : DynamicCircuit Var N → Prop
  | .circuit c => AllWiresLtCirc M c
  | .measure _ r => ∀ i, (r i).val < M
  | @DynamicCircuit.qIf _ _ _ _ tb fb => AllWiresLtDyn M tb ∧ AllWiresLtDyn M fb
  | .seq p₁ p₂ => AllWiresLtDyn M p₁ ∧ AllWiresLtDyn M p₂
def unembedCirc (M : ℕ) {N : ℕ} : Circuit N → Circuit M
  | .identity => .identity
  | .gate g r => if hr : ∀ i, (r i).val < M then .gate g (unembedReg r hr) else .identity
  | .seq c₁ c₂ => .seq (unembedCirc M c₁) (unembedCirc M c₂)
def unembedDyn (M : ℕ) {Var : Type} {N : ℕ} : DynamicCircuit Var N → DynamicCircuit Var M
  | .circuit c => .circuit (unembedCirc M c)
  | .measure v r =>
        if hr : ∀ i, (r i).val < M then .measure v (unembedReg r hr) else .circuit .identity
  | @DynamicCircuit.qIf _ _ cond inst tb fb =>
        @DynamicCircuit.qIf _ _ cond inst (unembedDyn M tb) (unembedDyn M fb)
  | .seq p₁ p₂ => .seq (unembedDyn M p₁) (unembedDyn M p₂)
theorem unembedCirc_count_le (M : ℕ) {N a : ℕ} (g : PrimitiveGate a)
    (c : Circuit N) : (unembedCirc M c).count g ≤ c.count g := by
  induction c with
  | identity => exact le_rfl
  | gate _ _ => dsimp only [unembedCirc]; split_ifs <;> simp [Circuit.count]
  | seq _ _ ih₁ ih₂ => exact Nat.add_le_add ih₁ ih₂
theorem unembedDyn_count_le (M : ℕ) {Var : Type} {N a : ℕ} (g : PrimitiveGate a)
    (p : DynamicCircuit Var N) : (unembedDyn M p).count g ≤ p.count g := by
  induction p with
  | circuit c => simpa [unembedDyn, DynamicCircuit.count] using unembedCirc_count_le M g c
  | measure _ _ => unfold unembedDyn; split_ifs <;> simp [DynamicCircuit.count, Circuit.count]
  | qIf _ _ _ iht ihf => simpa [unembedDyn, DynamicCircuit.count] using max_le_max iht ihf
  | seq _ _ ih₁ ih₂ => simpa [unembedDyn, DynamicCircuit.count] using Nat.add_le_add ih₁ ih₂
theorem zero_add_le_of_le {M N : ℕ} (hMN : M ≤ N) : 0 + M ≤ N := (Nat.zero_add M).symm ▸ hMN
theorem block0_compose_unembedReg {a M N : ℕ} (hMN : M ≤ N) (r : QRegister a N)
    (hr : ∀ i : Fin a, (r i).val < M) :
    (QRegister.block 0 M (zero_add_le_of_le hMN)).compose (unembedReg r hr) = r := by
  ext i; exact Nat.zero_add _
theorem onRegister_unembedCirc_eq {M N : ℕ} (hMN : M ≤ N) (c : Circuit N)
    (hc : AllWiresLtCirc M c) :
    (unembedCirc M c).onRegister (QRegister.block 0 M (zero_add_le_of_le hMN)) = c := by
  induction c with
  | identity => rfl
  | gate _ r =>
      have hr : ∀ i, (r i).val < M := hc
      rw [unembedCirc, dite_eq_left hr, Circuit.onRegister, block0_compose_unembedReg hMN r hr]
  | seq _ _ ih₁ ih₂ => exact congrArg₂ Circuit.seq (ih₁ hc.1) (ih₂ hc.2)
theorem onRegister_unembedDyn_eq {Var : Type} {M N : ℕ} (hMN : M ≤ N) (p : DynamicCircuit Var N)
    (hp : AllWiresLtDyn M p) :
    DynCircExt.onRegister (QRegister.block 0 M (zero_add_le_of_le hMN)) (unembedDyn M p) = p := by
  induction p with
  | circuit c => exact congrArg DynamicCircuit.circuit (onRegister_unembedCirc_eq hMN c hp)
  | measure _ r =>
      have hr : ∀ i, (r i).val < M := hp
      rw [unembedDyn, dite_eq_left hr, DynCircExt.onRegister,
        block0_compose_unembedReg hMN r hr]
  | qIf cond _ _ iht ihf => exact congrArg₂ (DynamicCircuit.qIf cond) (iht hp.1) (ihf hp.2)
  | seq _ _ ih₁ ih₂ => exact congrArg₂ DynamicCircuit.seq (ih₁ hp.1) (ih₂ hp.2)
theorem embedMatrix_posSemidef {k n : ℕ} (r : QRegister k n) {B : Operator (2 ^ k)}
    (hB : B.PosSemidef) : (r.embedMatrix B).PosSemidef := by
  unfold QRegister.embedMatrix;
  have h1 : (1 : Matrix (r.Environment → ZMod 2) (r.Environment → ZMod 2) ℂ).PosSemidef :=
      Matrix.PosSemidef.one; exact (Matrix.PosSemidef.kronecker hB h1).submatrix ⇑r.basisSplitEquiv
theorem embedObservable_herm {k n : ℕ} (r : QRegister k n) (M : Observable (Fin (2 ^ k))) :
    (r.embedMatrix M.1.mat).IsHermitian := by
  change (r.embedMatrix M.1.mat)ᴴ = r.embedMatrix M.1.mat; rw [← r.embedMatrix_conjTranspose];
  exact congrArg r.embedMatrix M.1.prop
theorem embedObservable_mem {k n : ℕ} (r : QRegister k n) (M : Observable (Fin (2 ^ k))) : 0 ≤
    (⟨r.embedMatrix M.1.mat, embedObservable_herm r M⟩ : HermitianMat (Fin (2 ^ n)) ℂ) ∧
    (⟨r.embedMatrix M.1.mat, embedObservable_herm r M⟩ : HermitianMat (Fin (2 ^ n)) ℂ) ≤ 1 := by
  constructor
  · exact HermitianMat.zero_le_iff.mpr (embedMatrix_posSemidef r (HermitianMat.zero_le_iff.mp
        M.2.1))
  · apply HermitianMat.le_iff.mpr; change (1 - r.embedMatrix M.1.mat).PosSemidef
    have hsub : (1 : Operator (2 ^ n)) - r.embedMatrix M.1.mat =
        r.embedMatrix ((1 : Operator (2 ^ k)) - M.1.mat) := by
      rw [← r.embedMatrix_one, PhotochemistrySolution.embedMatrix_sub]
    rw [hsub]; exact embedMatrix_posSemidef r (HermitianMat.le_iff.mp M.2.2)
noncomputable def embedObservable {k n : ℕ} (r : QRegister k n) (M : Observable (Fin (2 ^ k))) :
    Observable (Fin (2 ^ n)) :=
    ⟨⟨r.embedMatrix M.1.mat, embedObservable_herm r M⟩, embedObservable_mem r M⟩
@[simp] theorem embedObservable_mat {k n : ℕ} (r : QRegister k n) (M : Observable (Fin (2 ^ k))) :
    (embedObservable r M).1.mat = r.embedMatrix M.1.mat := rfl
noncomputable def embedAssertion {Var : Type} [Fintype Var] {k n : ℕ} (r : QRegister k n)
    (Θ : CQAssertion (Store Var) (2 ^ k)) : CQAssertion (Store Var) (2 ^ n) := fun σ ↦
    embedObservable r (Θ σ)
theorem herm_finset_sum_mat {d : ℕ} {ι : Type} (s : Finset ι) (f : ι → HermitianMat (Fin d) ℂ) :
    (∑ i ∈ s, f i).mat = ∑ i ∈ s, (f i).mat := map_sum (AddSubmonoid.subtype _) f s
theorem compose_basisOutcomeProjector_any {a b n : ℕ} (r₁ : QRegister b n) (r₂ : QRegister a b)
    (o : Fin (2 ^ a)) : (r₁.compose r₂).basisOutcomeProjector o =
    r₁.embedMatrix (r₂.basisOutcomeProjector o) := by
  rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
      QRegister.embedMatrix_compose]
theorem compose_basisOutcomeProjector_zero {a b n : ℕ} (r₁ : QRegister b n) (r₂ : QRegister a b) :
    (r₁.compose r₂).basisOutcomeProjector 0 = r₁.embedMatrix (r₂.basisOutcomeProjector 0) :=
    compose_basisOutcomeProjector_any r₁ r₂ 0
theorem extractIndex_eq_zero_iff_basisBits_eq_zero {k n : ℕ} (r : QRegister k n)
    (j : Fin (2 ^ n)) : r.extractIndex j = 0 ↔ ∀ i : Fin k, basisBits n j (r i) = 0 := by
  constructor
  · intro h i; rw [← (QRegExt.basisBits_extractIdx r), h, basisBits_div_mod]; norm_num
  · intro h; apply (basisBitsEquiv k).injective; funext i;
    change basisBits k (r.extractIndex j) i = basisBits k 0 i;
    rw [(QRegExt.basisBits_extractIdx r), h i, basisBits_div_mod]; norm_num
theorem wp_onRegister_embedAssertion {Var : Type} [Fintype Var] [DecidableEq Var] {k n : ℕ}
    (r : QRegister k n) (p : DynamicCircuit Var k) (Θ : CQAssertion (Store Var) (2 ^ k)) :
    wp (DynCircExt.onRegister r p).compile (embedAssertion r Θ) =
        embedAssertion r (wp p.compile Θ) := by
  induction p generalizing Θ with
  | circuit c =>
      refine funext fun σ ↦ Subtype.ext (HermitianMat.ext ?_)
      simp only [DynCircExt.onRegister, DynCircExt.compile_circuit_loc,
          wp_circuit_compile_loc, wpQAssignCompat, QhlAux.qAssign_obs_map_val,
          HermitianMat.conj_apply_mat, Circuit.eval_onRegister, QRegister.embedUnitary_val,
          embedAssertion, embedObservable_mat, Matrix.conjTranspose_conjTranspose,
          ← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul]
  | measure v q =>
      refine funext fun σ ↦ Subtype.ext (HermitianMat.ext ?_)
      simp only [DynCircExt.onRegister, DynamicCircuit.compile_measure, QProg.measureRegister,
          wp_qMeasure_apply, CQAssertion.subst_apply, embedAssertion, embedObservable_mat]
      dsimp [qMeasure_obs_map]; rw [herm_finset_sum_mat, herm_finset_sum_mat, r.embedMatrix_sum];
      apply Finset.sum_congr rfl; intro o _;
      simp only [qMeasure_outcome_herm_eq_conj, HermitianMat.conj_apply_mat,
          CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply,
          compose_basisOutcomeProjector_any, ← r.embedMatrix_conjTranspose,
          QRegister.basisOutcomeProjector_conjTranspose, embedObservable_mat,
          r.embedMatrix_mul]
  | qIf cond tb fb iht ihf =>
      funext σ
      simp only [DynCircExt.onRegister, DynamicCircuit.compile_qIf, wp_qIf, embedAssertion]
      by_cases h : cond σ <;> simp [h, iht, ihf, embedAssertion]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynCircExt.onRegister, DynamicCircuit.compile_seq, wp_qSeq, ih₂, ih₁]
theorem wp_onRegister_le_of_comm {Var : Type} [Finite Var] [DecidableEq Var] {k n : ℕ}
    (r : QRegister k n) (p : DynamicCircuit Var k) (M : Observable (Fin (2 ^ n)))
    (hcomm : ∀ A : Operator (2 ^ k), r.embedMatrix A * M.1.mat = M.1.mat * r.embedMatrix A) :
    wp (DynCircExt.onRegister r p).compile (fun _ ↦ M) ≤ (fun _ ↦ M) := by
  let _ : Fintype Var := Fintype.ofFinite Var
  induction p with
  | circuit c =>
      intro σ
      change wp ((c.onRegister r).compile) (fun _ ↦ M) σ ≤ M
      rw [wp_circuit_compile_loc]
      refine le_of_eq (Subtype.ext (HermitianMat.ext ?_))
      have hu : c.eval.1ᴴ * c.eval.1 = 1 := by simpa [Matrix.star_eq_conjTranspose] using c.eval.2.1
      change (HermitianMat.conj ((c.onRegister r).eval).1.conjTranspose M.1).mat = M.1.mat
      rw [Circuit.eval_onRegister, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
        QRegister.embedUnitary_val, ← r.embedMatrix_conjTranspose, Matrix.mul_assoc,
        ← hcomm c.eval.1, ← Matrix.mul_assoc, ← r.embedMatrix_mul,
        hu, r.embedMatrix_one, Matrix.one_mul]
  | measure v q =>
      refine fun σ ↦ le_of_eq (Subtype.ext (HermitianMat.ext ?_))
      simp only [DynCircExt.onRegister, DynamicCircuit.compile_measure,
        QProg.measureRegister, wp_qMeasure_apply, CQAssertion.subst_apply]
      dsimp [qMeasure_obs_map]
      have ht (o : Fin 2) :
          (qMeasure_outcome_herm (((r.compose q).computationalBasisMeasurement : Measurement (2 ^ n)
              (2 ^ 1)).1 o) M.1).mat =
          r.embedMatrix (q.basisOutcomeProjector o) * M.1.mat := by
        simp only [qMeasure_outcome_herm_eq_conj, HermitianMat.conj_apply_mat,
            CompleteMeasurement.toMeasurement_coe,
          QRegister.computationalBasisMeasurement_apply, compose_basisOutcomeProjector_any,
              ← r.embedMatrix_conjTranspose,
          QRegister.basisOutcomeProjector_conjTranspose]
        rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, ← r.embedMatrix_mul,
          q.basisOutcomeProjector_mul_self]
      have hsum : (∑ i : Fin 2, q.basisOutcomeProjector i) = 1 := q.sum_basisOutcomeProjector
      rw [herm_finset_sum_mat, Finset.sum_congr rfl fun o _ ↦ ht o, ← Finset.sum_mul,
        ← r.embedMatrix_sum, hsum, r.embedMatrix_one, Matrix.one_mul]
  | qIf cond tb fb iht ihf =>
      intro σ
      simp only [DynCircExt.onRegister, DynamicCircuit.compile_qIf, wp_qIf]
      split_ifs
      · exact iht σ
      · exact ihf σ
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynCircExt.onRegister, DynamicCircuit.compile_seq, wp_qSeq]
      exact (wp_mono (DynCircExt.onRegister r p₁).compile ih₂).trans ih₁
theorem star_dotProduct_tensorState_single {k n : ℕ} (r : QRegister k n)
    (e₀ : r.Environment → ZMod 2) (u v : Fin (2 ^ k) → ℂ) :
    star (r.tensorState u (Pi.single e₀ 1)) ⬝ᵥ r.tensorState v (Pi.single e₀ 1) = star u ⬝ᵥ v := by
  unfold dotProduct
  rw [← r.basisSplitEquiv.symm.sum_comp (fun g ↦ star (r.tensorState u (Pi.single e₀ 1)) g *
      r.tensorState v (Pi.single e₀ 1) g), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single e₀]
  · simp [QRegister.tensorState, ← r.basisSplitEquiv_apply_fst]
  · exact fun _ _ hne ↦ by simp [QRegister.tensorState, Pi.single_eq_of_ne hne]
  · exact fun hmem ↦ (hmem (Finset.mem_univ e₀)).elim
theorem inner_euclidean_tensorState_single {k n : ℕ} (r : QRegister k n)
    (e₀ : r.Environment → ZMod 2) (u v : Fin (2 ^ k) → ℂ) :
    @inner ℂ (EuclideanSpace ℂ (Fin (2 ^ n))) _ (WithLp.toLp 2 (r.tensorState u (Pi.single e₀ 1)))
    (WithLp.toLp 2 (r.tensorState v (Pi.single e₀ 1))) =
    @inner ℂ (EuclideanSpace ℂ (Fin (2 ^ k))) _ (WithLp.toLp 2 u) (WithLp.toLp 2 v) :=
    by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct];
  change (r.tensorState v (Pi.single e₀ 1)) ⬝ᵥ star (r.tensorState u (Pi.single e₀ 1)) =
      v ⬝ᵥ star u; rw [dotProduct_comm, star_dotProduct_tensorState_single r e₀ u v,
      dotProduct_comm]
theorem norm_euclidean_tensorState_single {k n : ℕ} (r : QRegister k n)
    (e₀ : r.Environment → ZMod 2) (u : Fin (2 ^ k) → ℂ) :
    ‖(WithLp.toLp 2 (r.tensorState u (Pi.single e₀ 1)) : EuclideanSpace ℂ (Fin (2 ^ n)))‖ =
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin (2 ^ k)))‖ := by
  have hsq :
      ‖(WithLp.toLp 2 (r.tensorState u (Pi.single e₀ 1)) : EuclideanSpace ℂ (Fin (2 ^ n)))‖ ^ 2 =
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin (2 ^ k)))‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ,
        inner_euclidean_tensorState_single r e₀ u u]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
theorem dirtyObservable_herm {k n : ℕ} (r : QRegister k n) :
    (1 - r.basisOutcomeProjector 0).IsHermitian := by
  change (1 - r.basisOutcomeProjector 0)ᴴ = 1 - r.basisOutcomeProjector 0;
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, r.basisOutcomeProjector_conjTranspose]
theorem dirtyObservable_mem {k n : ℕ} (r : QRegister k n) : 0 ≤ (⟨1 - r.basisOutcomeProjector 0,
    dirtyObservable_herm r⟩ : HermitianMat (Fin (2 ^ n)) ℂ) ∧ (⟨1 - r.basisOutcomeProjector 0,
    dirtyObservable_herm r⟩ : HermitianMat (Fin (2 ^ n)) ℂ) ≤ 1 := by
  refine ⟨HermitianMat.zero_le_iff.mpr (Matrix.le_iff.mp (r.basisOutcomeProjector_le_one 0)),
      HermitianMat.le_iff.mpr ?_⟩
  change ((1 : Operator (2 ^ n)) - (1 - r.basisOutcomeProjector 0)).PosSemidef
  simpa [sub_sub_cancel, r.basisOutcomeProjector_conjTranspose,
      r.basisOutcomeProjector_mul_self] using Matrix.posSemidef_conjTranspose_mul_self
      (r.basisOutcomeProjector 0)
noncomputable def dirtyObservable {k n : ℕ} (r : QRegister k n) : Observable (Fin (2 ^ n)) :=
    ⟨⟨1 - r.basisOutcomeProjector 0, dirtyObservable_herm r⟩, dirtyObservable_mem r⟩
@[simp] theorem dirtyObservable_mat {k n : ℕ} (r : QRegister k n) :
    (dirtyObservable r).1.mat = 1 - r.basisOutcomeProjector 0 := rfl
end QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas

protected theorem QuantumComputation.Specs.PhotochemistrySolution.QRegExt.embedMatrix_sub {k n :
    ℕ} (r : QRegister k n) (A B : Operator (2 ^ k)) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B :=
    QuantumComputation.Specs.PhotochemistrySolution.embedMatrix_sub r A B
end

noncomputable section
open Operator QProg Matrix
section
open DynamicCircuit Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ThreeSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open ComplexConjugate PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
  PhotochemistrySolution.DiagShiftSpecBridge
/--
Specification of a partition of `ancW` ancilla slots into `ancW'` live slots (`keepIdx`)
and `kIdle` untouched slots (`idleIdx`).
-/
structure AncillaPartition (ancW ancW' kIdle : ℕ) where
  keepIdx : QRegister ancW' ancW
  idleIdx : QRegister kIdle ancW
  disj : keepIdx.DisjointWires idleIdx
  cover : ∀ j : Fin ancW, j ∈ Set.range keepIdx.wires ∨ j ∈ Set.range idleIdx.wires
  invIdx : Fin ancW → Sum (Fin ancW') (Fin kIdle)
  inv_left_keep : ∀ i : Fin ancW', invIdx (keepIdx i) = Sum.inl i
  inv_left_idle : ∀ l : Fin kIdle, invIdx (idleIdx l) = Sum.inr l
  inv_right : ∀ j : Fin ancW, Sum.elim (fun i ↦ keepIdx i) (fun l ↦ idleIdx l) (invIdx j) = j
theorem assembleAnc_inj {ancW ancW' kIdle m : ℕ} (part : AncillaPartition ancW ancW' kIdle)
    (rKeep : QRegister ancW' m) (rIdle : QRegister kIdle m) (hdisjKI : rKeep.DisjointWires rIdle) :
    Function.Injective (fun j ↦ Sum.elim (fun i ↦ rKeep i) (fun l ↦ rIdle l) (part.invIdx j)) := by
  intro a b h
  cases ha : part.invIdx a <;> cases hb : part.invIdx b <;> dsimp only at h <;> rw [ha, hb] at h
  · rw [← part.inv_right a, ← part.inv_right b, ha, hb, rKeep.wires.injective h]
  · exact (QRegister.disjoint_iff.mp hdisjKI _ _ h).elim
  · exact (QRegister.disjoint_iff.mp hdisjKI _ _ h.symm).elim
  · rw [← part.inv_right a, ← part.inv_right b, ha, hb, rIdle.wires.injective h]
/--
Assemble a full `ancW`-wire ancilla register from disjoint `rKeep : QRegister ancW' m`
and `rIdle : QRegister kIdle m` using `part : AncillaPartition ancW ancW' kIdle`.
-/
abbrev assembleAnc {ancW ancW' kIdle m : ℕ} (part : AncillaPartition ancW ancW' kIdle)
    (rKeep : QRegister ancW' m) (rIdle : QRegister kIdle m)
    (hdisjKI : rKeep.DisjointWires rIdle) : QRegister ancW m where
  wires :=
    { toFun := fun j ↦ Sum.elim (fun i ↦ rKeep i) (fun l ↦ rIdle l) (part.invIdx j)
      inj' := assembleAnc_inj part rKeep rIdle hdisjKI }
@[simp] theorem assembleAnc_compose_keep {ancW ancW' kIdle m : ℕ}
    (part : AncillaPartition ancW ancW' kIdle)
    (rKeep : QRegister ancW' m) (rIdle : QRegister kIdle m)
    (hdisjKI : rKeep.DisjointWires rIdle) :
    (assembleAnc part rKeep rIdle hdisjKI).compose part.keepIdx = rKeep := by
  apply congrArg QRegister.mk; apply Function.Embedding.ext; intro i; apply Fin.ext
  change Fin.val (Sum.elim (fun i ↦ rKeep i) (fun l ↦ rIdle l) (part.invIdx (part.keepIdx i))) = _
  rw [part.inv_left_keep i]; rfl
@[simp] theorem assembleAnc_compose_idle {ancW ancW' kIdle m : ℕ}
    (part : AncillaPartition ancW ancW' kIdle)
    (rKeep : QRegister ancW' m) (rIdle : QRegister kIdle m)
    (hdisjKI : rKeep.DisjointWires rIdle) :
    (assembleAnc part rKeep rIdle hdisjKI).compose part.idleIdx = rIdle := by
  apply congrArg QRegister.mk; apply Function.Embedding.ext; intro l; apply Fin.ext
  change Fin.val (Sum.elim (fun i ↦ rKeep i) (fun l ↦ rIdle l) (part.invIdx (part.idleIdx l))) = _
  rw [part.inv_left_idle l]; rfl
theorem assembleAnc_disjoint_left {sysW ancW ancW' kIdle m : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) (rSys : QRegister sysW m) (rKeep : QRegister ancW' m)
    (rIdle : QRegister kIdle m) (hSK : rSys.DisjointWires rKeep) (hSI : rSys.DisjointWires rIdle)
    (hKI : rKeep.DisjointWires rIdle) : rSys.DisjointWires (assembleAnc part rKeep rIdle hKI) := by
  rw [QRegister.disjoint_iff]; intro i j h
  change rSys i = Sum.elim (fun i ↦ rKeep i) (fun l ↦ rIdle l) (part.invIdx j) at h
  cases hj : part.invIdx j <;> rw [hj] at h
  · exact QRegister.disjoint_iff.mp hSK i _ h
  · exact QRegister.disjoint_iff.mp hSI i _ h
theorem assembleAnc_basisOutcomeProjector_zero {ancW ancW' kIdle m : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) (rKeep : QRegister ancW' m)
    (rIdle : QRegister kIdle m) (hKI : rKeep.DisjointWires rIdle) :
    (assembleAnc part rKeep rIdle hKI).basisOutcomeProjector 0 = rKeep.basisOutcomeProjector 0 *
    rIdle.basisOutcomeProjector 0 := by
  let rA := assembleAnc part rKeep rIdle hKI
  rw [rA.basisOutcomeProjector_eq_diagonal, rKeep.basisOutcomeProjector_eq_diagonal,
    rIdle.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext global
  have hiff : rA.extractIndex global = 0 ↔ rKeep.extractIndex global = 0 ∧
      rIdle.extractIndex global = 0 := by
    simp only [extractIndex_eq_zero_iff_basisBits_eq_zero]
    refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun l ↦ ?_⟩, fun ⟨hk, hi⟩ j ↦ ?_⟩
    · simpa [rA, assembleAnc, part.inv_left_keep i] using h (part.keepIdx i)
    · simpa [rA, assembleAnc, part.inv_left_idle l] using h (part.idleIdx l)
    · change basisBits m global (Sum.elim (fun i ↦ rKeep i) (fun l ↦ rIdle l) (part.invIdx j)) = 0
      cases part.invIdx j <;> simp [hk, hi]
  by_cases hK : rKeep.extractIndex global = 0 <;> by_cases hI : rIdle.extractIndex global = 0 <;>
    simp [hiff, hK, hI]
theorem zero_add_le_add_right (a b : ℕ) : 0 + a ≤ a + b :=
    (Nat.zero_add a).symm ▸ Nat.le_add_right a b
theorem amb_disj_phantom {w n kIdle : ℕ} (r : QRegister w n) :
    ((QRegister.block 0 n (zero_add_le_add_right n kIdle)).compose r).DisjointWires (QRegister.block
    n kIdle le_rfl)
    := by
  rw [QRegister.disjoint_iff]; intro i j h;
  have hv := congrArg Fin.val h; change 0 + (r i).val = n + j.val at hv;
  have hi : (r i).val < n := (r i).isLt; omega
/-- Generic unembedded program on `sysW` system wires and `ancW'` live ancilla wires. -/
abbrev unembedProgram {sysW ancW ancW' kIdle : ℕ} (part : AncillaPartition ancW ancW' kIdle)
    (P_big : ∀ {Var : Type} {m : ℕ}, Var → QRegister sysW m → QRegister ancW m →
    DynamicCircuit Var m) {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister sysW n)
    (rAncSmall : QRegister ancW' n) : DynamicCircuit Var n :=
  let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
  let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl
  unembedDyn n (P_big v (rAmb.compose rSys)
    (assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall)))
/--
Exact spacetime cost preservation (`TOFF = 0` and `(sysW + ancW') * T ≤ cost` ) with zero `decide` .
-/
theorem unembedProgram_const_cost {sysW ancW ancW' kIdle T_max cost : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) (P_big : ∀ {Var : Type}
    {m : ℕ}, Var → QRegister sysW m → QRegister ancW m → DynamicCircuit Var m)
    (hBigCost : ∀ {Var : Type} {m : ℕ} (v : Var) (rS : QRegister sysW m) (rA : QRegister ancW m),
    (P_big v rS rA).count PrimitiveGate.TOFF = 0 ∧ (P_big v rS rA).count PrimitiveGate.T ≤ T_max)
    (hCost : (sysW + ancW') * T_max ≤ cost) {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister sysW n)
    (rAncSmall : QRegister ancW' n) :
    (unembedProgram part P_big v rSys rAncSmall).count PrimitiveGate.TOFF = 0 ∧ (sysW + ancW') *
    (unembedProgram part P_big v rSys rAncSmall).count PrimitiveGate.T ≤ cost := by
  let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
  let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl;
  let rS := rAmb.compose rSys;
  let rA :=
      assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall); obtain
      ⟨hToff, hT⟩ :=
      hBigCost v rS rA;
      have h0 : (unembedProgram part P_big v rSys rAncSmall).count PrimitiveGate.TOFF ≤ 0 :=
      (unembedDyn_count_le n PrimitiveGate.TOFF (P_big v rS rA)).trans (le_of_eq hToff);
      have h1 : (unembedProgram part P_big v rSys rAncSmall).count PrimitiveGate.T ≤ T_max :=
      (unembedDyn_count_le n PrimitiveGate.T (P_big v rS rA)).trans hT; exact
      ⟨Nat.eq_zero_of_le_zero h0, (Nat.mul_le_mul_left (sysW + ancW') h1).trans hCost⟩
abbrev sysCanon (sysW ancW : ℕ) : QRegister sysW (sysW + ancW) :=
    QRegister.block 0 sysW (zero_add_le_add_right sysW ancW)
abbrev ancCanon (sysW ancW : ℕ) : QRegister ancW (sysW + ancW) := QRegister.block sysW ancW le_rfl
theorem sysCanon_disj_keep {sysW ancW ancW' kIdle : ℕ} (part : AncillaPartition ancW ancW' kIdle) :
    (sysCanon sysW ancW).DisjointWires ((ancCanon sysW ancW).compose part.keepIdx) := by
  rw [QRegister.disjoint_iff]; intro i j h;
  have hv := congrArg Fin.val h; change 0 + i.val = sysW + (part.keepIdx j).val at hv;
  have hi : i.val < sysW := i.isLt; omega
abbrev rLiveCanon (sysW : ℕ) {ancW ancW' kIdle : ℕ} (part : AncillaPartition ancW ancW' kIdle) :
    QRegister (sysW + ancW') (sysW + ancW) :=
    (sysCanon sysW ancW).concat ((ancCanon sysW ancW).compose part.keepIdx)
    (sysCanon_disj_keep part)
abbrev rIdleCanon (sysW : ℕ) {ancW ancW' kIdle : ℕ} (part : AncillaPartition ancW ancW' kIdle) :
    QRegister kIdle (sysW + ancW) := (ancCanon sysW ancW).compose part.idleIdx
theorem rLiveCanon_disj_idle {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) :
    (rLiveCanon sysW part).DisjointWires (rIdleCanon sysW part) := by
  rw [QRegister.disjoint_iff]; intro q l h
  by_cases hq : q.val < sysW
  · have hq_eq : q = Fin.castAdd ancW' ⟨q.val, hq⟩ := rfl; rw [hq_eq] at h;
    have hleft : (rLiveCanon sysW part) (Fin.castAdd ancW' ⟨q.val, hq⟩) = sysCanon sysW ancW ⟨q.val,
        hq⟩ :=
        QRegister.concat_apply_left (sysCanon sysW ancW) ((ancCanon sysW ancW).compose part.keepIdx)
        (sysCanon_disj_keep part)
        ⟨q.val,
        hq⟩; rw [hleft] at h; have hv :=
                                congrArg Fin.val h; change 0 + q.val = sysW +
                                (part.idleIdx l).val at hv; omega
  · let j : Fin ancW' := ⟨q.val - sysW, by omega⟩
    have hq_eq : q = Fin.natAdd sysW j := Fin.ext (by dsimp [j]; omega)
    have hright : (rLiveCanon sysW part) (Fin.natAdd sysW j) =
        ((ancCanon sysW ancW).compose part.keepIdx) j :=
        QRegister.concat_apply_right (sysCanon sysW ancW)
        ((ancCanon sysW ancW).compose part.keepIdx) (sysCanon_disj_keep part) j; rw [hq_eq,
        hright] at h; have hinj :=
                        (ancCanon sysW ancW).wires.injective h; exact QRegister.disjoint_iff.mp
                        part.disj j l hinj
theorem ancCanon_keep_disj_idle {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) :
    ((ancCanon sysW ancW).compose part.keepIdx).DisjointWires (rIdleCanon sysW part) := by
  rw [QRegister.disjoint_iff]; intro i l h;
  exact QRegister.disjoint_iff.mp part.disj i l ((ancCanon sysW ancW).wires.injective h)
theorem assembleAnc_canon_eq {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) :
    assembleAnc part ((ancCanon sysW ancW).compose part.keepIdx) (rIdleCanon sysW part)
    (ancCanon_keep_disj_idle part) = ancCanon sysW ancW := by
  apply congrArg QRegister.mk; apply Function.Embedding.ext; intro j; apply Fin.ext
  change Fin.val (Sum.elim (fun i ↦ ((ancCanon sysW ancW).compose part.keepIdx) i)
      (fun l ↦ (rIdleCanon sysW part) l) (part.invIdx j)) = (ancCanon sysW ancW j).val
  have hr := part.inv_right j
  cases hj : part.invIdx j <;> rw [hj] at hr <;>
    exact congrArg (fun x ↦ (ancCanon sysW ancW x).val) hr
theorem env_eq_zero_iff_idle_zero {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) (global : Fin (2 ^ (sysW + ancW))) :
    ((rLiveCanon sysW part).basisSplitEquiv global).2 = 0 ↔
    (rIdleCanon sysW part).extractIndex global = 0 := by
  rw [extractIndex_eq_zero_iff_basisBits_eq_zero]
  refine ⟨fun h l ↦ ?_, fun h ↦ ?_⟩
  · simpa [QRegister.basisSplitEquiv_apply_snd] using congrFun h ⟨(rIdleCanon sysW part) l, fun
      ⟨q, hq⟩ ↦ QRegister.disjoint_iff.mp (rLiveCanon_disj_idle part) q l hq⟩
  · funext ⟨q, hq⟩
    simp only [QRegister.basisSplitEquiv_apply_snd, Pi.zero_apply]
    by_cases hlt : q.val < sysW
    · exact (hq ⟨Fin.castAdd ancW' ⟨q.val, hlt⟩, (QRegister.concat_apply_left _ _ _ ⟨q.val,
        hlt⟩).trans (Fin.ext (Nat.zero_add q.val))⟩).elim
    · let a : Fin ancW := ⟨q.val - sysW, by omega⟩
      have hqa : q = ancCanon sysW ancW a := Fin.ext (by
        dsimp [ancCanon, QRegister.block, Fin.natAddEmb, Fin.natAdd, DFunLike.coe,
            -Function.Embedding.toFun_eq_coe, a]
        omega)
      rcases part.cover a with ⟨i, hi⟩ | ⟨l, hl⟩
      · exact (hq ⟨Fin.natAdd sysW i, (QRegister.concat_apply_right _ _ _ i).trans
          ((congrArg (ancCanon sysW ancW) hi).trans hqa.symm)⟩).elim
      · rw [hqa, ← hl]
        exact h l
noncomputable abbrev sliceIdleZero {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) (w : Fin (2 ^ (sysW + ancW)) → ℂ) :
    Fin (2 ^ (sysW + ancW')) → ℂ := fun loc ↦
    w ((rLiveCanon sysW part).basisSplitEquiv.symm (loc, 0))
theorem tensorState_sliceIdleZero {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) {w : Fin (2 ^ (sysW + ancW)) → ℂ}
    (hw : ((rIdleCanon sysW part).basisOutcomeProjector 0).mulVec w = w) :
    (rLiveCanon sysW part).tensorState (sliceIdleZero part w) (Pi.single 0 1) = w := by
  funext global; dsimp [QRegister.tensorState, sliceIdleZero]
  by_cases henv : ((rLiveCanon sysW part).basisSplitEquiv global).2 = 0
  · rw [henv, Pi.single_eq_same, mul_one]
    have hsym :
        (rLiveCanon sysW part).basisSplitEquiv.symm ((rLiveCanon sysW part).extractIndex global,
        0) =
        global := by
      apply (rLiveCanon sysW part).basisSplitEquiv.injective; rw [Equiv.apply_symm_apply];
      exact Prod.ext rfl henv.symm
    rw [hsym]
  · rw [Pi.single_eq_of_ne henv, mul_zero];
    have hne : (rIdleCanon sysW part).extractIndex global ≠ 0 :=
        mt (env_eq_zero_iff_idle_zero part global).mpr henv; have hw0 := congrFun hw global
    rw [(rIdleCanon sysW part).basisOutcomeProjector_mulVec, ite_eq_right_iff.mpr fun h ↦
        absurd h hne] at hw0
    exact hw0
theorem tensorState_cleanSmall_is_ancCanon_clean {sysW ancW ancW' kIdle : ℕ}
    (part : AncillaPartition ancW ancW' kIdle) {j : Fin (2 ^ (sysW + ancW'))}
    (hj : (QRegister.block sysW ancW' le_rfl).extractIndex j = 0) :
    ((ancCanon sysW ancW).basisOutcomeProjector 0).mulVec ((rLiveCanon sysW part).tensorState
    (Pi.single j 1) (Pi.single 0 1)) = (rLiveCanon sysW part).tensorState (Pi.single j 1)
    (Pi.single 0 1) := by
  let g₀ := (rLiveCanon sysW part).basisSplitEquiv.symm (j, 0)
  have h1 : (rLiveCanon sysW part).extractIndex g₀ = j := by
    rw [← (rLiveCanon sysW part).basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have h2 : ((rLiveCanon sysW part).basisSplitEquiv g₀).2 = 0 := by rw [Equiv.apply_symm_apply]
  have hg₀_eq : (rLiveCanon sysW part).tensorState (Pi.single j 1)
      (Pi.single 0 1) = Pi.single g₀ 1 :=
    by simpa only [h1, h2] using (rLiveCanon sysW part).tensorState_single_factors g₀
  rw [hg₀_eq, (ancCanon sysW ancW).basisOutcomeProjector_mulVec_single]
  have hzero : (ancCanon sysW ancW).extractIndex g₀ = 0 := by
    rw [extractIndex_eq_zero_iff_basisBits_eq_zero]
    intro a
    rcases part.cover a with ⟨i, rfl⟩ | ⟨l, rfl⟩
    · have hb :=
          (extractIndex_eq_zero_iff_basisBits_eq_zero (QRegister.block sysW ancW' le_rfl) j).mp hj i
      rw [← h1, (QRegExt.basisBits_extractIdx (rLiveCanon sysW part))] at hb
      change basisBits (sysW + ancW) g₀ ((rLiveCanon sysW part) (Fin.natAdd sysW i)) = 0 at hb
      rwa [QRegister.concat_apply_right (sysCanon sysW ancW)
          ((ancCanon sysW ancW).compose part.keepIdx) (sysCanon_disj_keep part) i] at hb
    · exact (extractIndex_eq_zero_iff_basisBits_eq_zero (rIdleCanon sysW part) g₀).mp
          ((env_eq_zero_iff_idle_zero part g₀).mp h2) l
  simp [hzero]

/--
Compositional wire-range bound for ANY `[irreducible]` circuit `c : Circuit K` embedded via
`onRegister` (`O(K)` wire checks, zero AST unfolding.).
-/
theorem allWiresLtCirc_onRegister {K M M' : ℕ} (c : Circuit K) (emb : QRegister K M)
    (hlt : ∀ w : Fin K, (emb w).val < M') : AllWiresLtCirc M' (c.onRegister emb) := by
  induction c with
  | identity => trivial
  | gate _ r => intro i; exact hlt (r i)
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
end QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas

namespace QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open PhotochemistrySolution.QubitizationTop PhotochemistrySolution.OvBidir
  PhotochemistrySolution.SelectGidneyFast PhotochemistrySolution.QubitizationProgram
  PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.QubitizationWalkSem
open PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectLcu70Rot32
  PhotochemistrySolution.UnembedIdleAncillas
theorem assembleAnc_val_lt_of_not_idle {ancW ancW' kIdle n : ℕ}
    (part : AncillaPartition ancW ancW' kIdle)
    (rAncSmall : QRegister ancW' n)
    (j : Fin ancW)
    (hNotIdle : ∀ l : Fin kIdle, part.idleIdx l ≠ j) :
    let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle);
    let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl
    (assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall) j).val <
        n := by
  intro rAmb rPhantom
  rcases part.cover j with ⟨i, rfl⟩ | ⟨l, hl⟩
  · have hk := congrArg (fun r : QRegister ancW' _ ↦ r i)
      (assembleAnc_compose_keep part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall))
    change (assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall)
        (part.keepIdx i)).val < n
    rw [show assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall)
        (part.keepIdx i) = (rAmb.compose rAncSmall) i from hk]
    change 0 + (rAncSmall i).val < n; omega
  · exact absurd hl (hNotIdle l)
theorem allWiresLtCirc_inverse {M N : ℕ} {c : Circuit N} (hc : AllWiresLtCirc M c) :
    AllWiresLtCirc M c.inverse := by
  induction c with
  | identity => trivial
  | gate g r =>
      have hr : ∀ i, (r i).val < M := hc
      cases g <;> simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence, AllWiresLtCirc, hr]
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hc.2, ih₁ hc.1⟩
theorem allWiresLtDyn_foldFinDyn {Var : Type} {N M m : ℕ} {body : Fin m → DynamicCircuit Var N}
    (hb : ∀ i : Fin m, AllWiresLtDyn M (body i)) : AllWiresLtDyn M (foldFinDyn body) := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨ih fun i ↦ hb i.castSucc, hb (Fin.last m)⟩
theorem allWiresLtCirc_single {N M : ℕ} {g : PrimitiveGate 1} {w : Wire N}
    (hw : w.val < M) : AllWiresLtCirc M (.gate g (QRegister.singleton w)) :=
  fun i ↦ by have hi : i = 0 := Subsingleton.elim i 0; subst hi; exact hw
theorem allWiresLtCirc_pair {N M : ℕ} {c t : Wire N} {h : c ≠ t} (hc : c.val < M)
    (ht : t.val < M) : AllWiresLtCirc M (Circuit.CNOT c t h) :=
  fun i ↦ by fin_cases i <;> assumption
def CircWires {K : ℕ} (P : Wire K → Prop) : Circuit K → Prop
  | .identity => True
  | .gate _ r => ∀ i, P (r i)
  | .seq c₁ c₂ => CircWires P c₁ ∧ CircWires P c₂
/-- Structural wire-support predicate on `AndBracketProg K`. -/
def AndBracketWires {K : ℕ} (P : Wire K → Prop) : AndBracketProg K → Prop
  | .id => True
  | .prim c => CircWires P c
  | .seq p₁ p₂ => AndBracketWires P p₁ ∧ AndBracketWires P p₂
  | .tempAnd c₁ c₂ a _ _ _ body => P c₁ ∧ P c₂ ∧ P a ∧ AndBracketWires P body
/-- Structural wire-support predicate on `ComputeProg K`. -/
def ComputeProgWires {K : ℕ} (P : Wire K → Prop) : ComputeProg K → Prop
  | .id => True
  | .x u => P u
  | .cnot c tgt _ => P c ∧ P tgt
  | .andGate c₁ c₂ a _ _ _ => P c₁ ∧ P c₂ ∧ P a
  | .seq p₁ p₂ => ComputeProgWires P p₁ ∧ ComputeProgWires P p₂
theorem allWiresLtDyn_of_andBracketWires {Var : Type} {K N M : ℕ} (v : Var) (r : QRegister K N)
    (P : Wire K → Prop) (hP : ∀ w : Wire K, P w → (r w).val < M) :
    ∀ {p : AndBracketProg K}, AndBracketWires P p → AllWiresLtDyn M ((p.onRegister r).toDyn v)
  | .id, _ => trivial
  | .prim c, hc => by
      change AllWiresLtCirc M (c.onRegister r)
      induction c with
      | identity => trivial
      | gate _ reg => exact fun i ↦ hP (reg i) (hc i)
      | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨allWiresLtDyn_of_andBracketWires v r P hP h₁,
      allWiresLtDyn_of_andBracketWires v r P hP h₂⟩
  | .tempAnd c₁ c₂ a _ _ _ _, ⟨hc₁, hc₂, haP, hb⟩ => by
      have h₁ := hP c₁ hc₁; have h₂ := hP c₂ hc₂; have ha := hP a haP
      have ha1 {g : PrimitiveGate 1} : AllWiresLtCirc M (.gate g (QRegister.singleton
        (r a))) := allWiresLtCirc_single ha
      have hc2 {g : PrimitiveGate 1} : AllWiresLtCirc M (.gate g (QRegister.singleton
        (r c₂))) := allWiresLtCirc_single h₂
      exact ⟨⟨ha1, ha1, allWiresLtCirc_pair h₂ ha, allWiresLtCirc_inverse ha1,
        allWiresLtCirc_pair h₁ ha, ha1, allWiresLtCirc_pair h₂ ha, allWiresLtCirc_inverse ha1,
          allWiresLtCirc_pair h₁ ha, ha1, ha1⟩,
        allWiresLtDyn_of_andBracketWires v r P hP hb, ⟨ha1, fun i ↦ Subsingleton.elim i 0 ▸ ha,
          ⟨ha1, ⟨hc2, allWiresLtCirc_pair h₁ h₂, hc2⟩⟩, trivial⟩⟩
theorem andBracketWires_wrap {K : ℕ} {P : Wire K → Prop} : ∀ {p : ComputeProg K}
    {mid : AndBracketProg K}, ComputeProgWires P p → AndBracketWires P mid → AndBracketWires P
    (p.wrap mid)
  | .id, _, _, hmid => hmid
  | .x _u, _, hu, hmid => ⟨fun i ↦ Subsingleton.elim i 0 ▸ hu, hmid,
      fun i ↦ Subsingleton.elim i 0 ▸ hu⟩
  | .cnot _ _ _, _, ⟨hc, ht⟩, hmid =>
      ⟨fun | ⟨0, _⟩ => hc | ⟨1, _⟩ => ht, hmid,
       fun | ⟨0, _⟩ => hc | ⟨1, _⟩ => ht⟩
  | .andGate _ _ _ _ _ _, _, ⟨h₁, h₂, ha⟩, hmid => ⟨h₁, h₂, ha, hmid⟩
  | .seq p₁ p₂, mid, ⟨h₁, h₂⟩, hmid => @andBracketWires_wrap K P p₁ (p₂.wrap mid) h₁
      (@andBracketWires_wrap K P p₂ mid h₂ hmid)
end QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
end

namespace QuantumComputation.Specs.PhotochemistrySolution.ProviderCoreFused
open Circuit Qubit PrimitiveGate DynamicCircuit PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.UnembedIdleAncillas
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
abbrev scrWLayoutFused : ℕ := 1577
abbrev dLayoutFused : ℕ := totDimCompactGen scrWLayoutFused
theorem hSys5616_fused : systemQubits_frozen = 5616 := rfl
theorem ancWOfScr_layoutFused : ancWOfScr scrWLayoutFused = 1682 := rfl
/--
Active wires in `dLayout = 7298` when keeping `wIn` inner workspace wires (`6083 .. 6082 + wIn`).
-/
def ActiveLayoutFusedOf (wIn : ℕ) (w : Wire dLayoutFused) : Prop :=
    w.val < 5616 ∨ (5618 ≤ w.val ∧ w.val ≤ 5649) ∨ (5680 ≤ w.val ∧ w.val ≤ 5712) ∨ (5715 ≤ w.val ∧
    w.val < 6083 + wIn) ∨ 7215 ≤ w.val
end QuantumComputation.Specs.PhotochemistrySolution.ProviderCoreFused

namespace QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge
open scoped Matrix.Norms.L2Operator
open DynamicCircuit Circuit Qubit PrimitiveGate ComplexConjugate
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectSandwich
  PhotochemistrySolution.SelectDataBuilder
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.DiagShiftSpecBridge PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCompactRot34
open PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.OvBidir
  PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectGidneyFast
  PhotochemistrySolution.TargetBScr PhotochemistrySolution.SelectStructuredCB
open PhotochemistrySolution.SelectCsa64GqspWalk PhotochemistrySolution.SelectCsa64ThreeSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] systemQubits_frozen
theorem hScrBlockL {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) :
    34 + scrL ≤ ancWOfScr scrW := by unfold ancWOfScr; omega
theorem hLcuBlockL {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) :
    (34 + scrL) + (m + 2) ≤ ancWOfScr scrW := by unfold ancWOfScr; omega
abbrev scrSubLGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) :
    QRegister scrL (ancWOfScr scrW) := QRegister.block 34 scrL (hScrBlockL hp)
abbrev lcuSubLGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) : QRegister (m + 2)
    (ancWOfScr scrW) := QRegister.block (34 + scrL) (m + 2) (hLcuBlockL hp)
abbrev rScrLGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) :
    QRegister scrL (totDimCompactGen scrW) := (locAncCompactGen scrW).compose (scrSubLGen hp)
abbrev rLcuLGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) : QRegister (m + 2)
    (totDimCompactGen scrW) := (locAncCompactGen scrW).compose (lcuSubLGen hp)
theorem lcu_scr_ne_L {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (i : Fin (m + 2)) (j : Fin scrL) : lcuSubLGen hp i ≠ scrSubLGen hp j := fun h ↦ by
  have hv := congrArg Fin.val h; rw [block_apply_val, block_apply_val] at hv; omega
theorem lcu_idx_L {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) (h65 : 65 ≤ scrL)
    (i : Fin (m + 2)) : 34 ≤ (lcuSubLGen hp i).val ∧ ((lcuSubLGen hp i).val < 64 ∨ 99 ≤
    (lcuSubLGen hp i).val) ∧ (lcuSubLGen hp i).val ≠ ancWOfScr scrW - 1 := by
  rw [block_apply_val]; refine ⟨by omega, Or.inr (by omega), ?_⟩; unfold ancWOfScr; omega
theorem scr_idx_L {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) (j : Fin scrL) : 34 ≤
    (scrSubLGen hp j).val ∧ (scrSubLGen hp j).val ≠ ancWOfScr scrW - 1 := by
  rw [block_apply_val]; refine ⟨by omega, ?_⟩; unfold ancWOfScr; omega
theorem scr_rot34_L {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) (h65 : 65 ≤ scrL)
    (t : Fin (ancWOfScr scrW)) (ht : 64 ≤ t.val ∧ t.val < 99) :
    t ∈ Set.range (scrSubLGen hp).wires :=
  ⟨⟨t.val - 34, by omega⟩,
      Fin.ext (by rw [block_apply_val]; change 34 + (t.val - 34) = t.val; omega)⟩
theorem locQ_ne_rLcuLGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) (i : Fin (m + 2)) :
    locQCompactGen scrW ≠ rLcuLGen hp i := fun h ↦ by
  have hv := congrArg Fin.val ((locAncCompactGen scrW).wires.injective h)
  change 34 + scrW + 70 = (lcuSubLGen hp i).val at hv; rw [block_apply_val] at hv; omega
/-- Polymorphic LCU reflection unitary on `m + 2` coin qubits inside `totDimCompactGen scrW`. -/
noncomputable abbrev reflULGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) :
    Unitary (2 ^ (totDimCompactGen scrW)) :=
    reflU_sym (locQCompactGen scrW) (rLcuLGen hp) (locQ_ne_rLcuLGen hp)
theorem reflULGen_eq {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) :
    (reflULGen hp).1 =
      1 - (2 : ℂ) • (projOneQCompactGen scrW * (1 - lcuProjCompactGen scrW (lcuSubLGen hp))) := rfl
theorem reflHInLGen {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) (i₁ i₂ : Fin (m + 2))
    (h : i₁ ≠ i₂) : rLcuLGen hp i₁ ≠ rLcuLGen hp i₂ := fun hi ↦ h ((rLcuLGen hp).wires.injective hi)
attribute [local irreducible] SelectCompactAnc.ancWOfScr QRegister.embedUnitary QRegister.concat
    reflULGen
theorem cselU_cat_shared {scrW : ℕ} {S cselU : LocalUnitary (totDimCompactGen scrW)}
    (h : cselU.u.1 * cat8SharedProjCompactGen scrW = (1 - projOneQCompactGen scrW * (1 - S.u.1)) *
    cat8SharedProjCompactGen scrW) : cselU.u.1 * cat8SharedProjGen (hAncCompact scrW) =
    (1 - projOneQGen (hAncCompact scrW) * (1 - S.u.1)) * cat8SharedProjGen (hAncCompact scrW) := by
  rw [projOneQGen_hAncCompact_eq scrW]; exact h
theorem reflU_eq_shared {scrW scrL m : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70) : (reflULGen hp).1 =
    1 - (2 : ℂ) • (projOneQGen (hAncCompact scrW) * (1 - lcuProjGen (lcuSubLGen hp))) := by
  rw [projOneQGen_hAncCompact_eq scrW]; exact reflULGen_eq hp
theorem hT_csel_add_reflL {a b c tSel : ℕ} (h1 : a + 4 * b ≤ tSel) (h2 : c = 4 * b) : a + c ≤
    tSel := by omega
end QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self ket_H_apply sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
variable {Var : Type}
/--
Predicate asserting that `U : Unitary (2 ^ n)` commutes with every elementary circuit and
measurement outcome projector inside `p : DynamicCircuit Var n`.
-/
def CommutesWithDyn {Var : Type} {n : ℕ} (U : Unitary (2 ^ n)) : DynamicCircuit Var n → Prop
  | .circuit c => c.eval.1 * U.1 = U.1 * c.eval.1
  | .measure _ r => ∀ o : Fin 2, r.basisOutcomeProjector o * U.1 = U.1 * r.basisOutcomeProjector o
  | @DynamicCircuit.qIf _ _ _ _ t f => CommutesWithDyn U t ∧ CommutesWithDyn U f
  | .seq p₁ p₂ => CommutesWithDyn U p₁ ∧ CommutesWithDyn U p₂
theorem unitary_comm_inv_of_comm {N : ℕ} (U : Unitary N) (A : Matrix (Fin N) (Fin N) ℂ)
    (h : A * U.1 = U.1 * A) : A * (U⁻¹).1 = (U⁻¹).1 * A := by
  have hL : (U⁻¹).1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
  have hR : U.1 * (U⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel U)
  have hU : U.1 * (A * (U⁻¹).1) = U.1 * ((U⁻¹).1 * A) := by
    rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, hR, Matrix.mul_one, ← Matrix.mul_assoc, hR,
      Matrix.one_mul]
  simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using congrArg ((U⁻¹).1 * ·) hU
theorem commutesWithDyn_inv {Var : Type} {n : ℕ} (U : Unitary (2 ^ n)) :
    ∀ {p : DynamicCircuit Var n}, CommutesWithDyn U p → CommutesWithDyn U⁻¹ p := by
  intro p h; induction p with
  | circuit _ => exact unitary_comm_inv_of_comm U _ h
  | measure _ _ => exact fun o ↦ unitary_comm_inv_of_comm U _ (h o)
  | qIf _ _ _ iht ihf => exact ⟨iht h.1, ihf h.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
theorem commutesWithDyn_mul {Var : Type} {n : ℕ} (U₁ U₂ : Unitary (2 ^ n)) : ∀
    {p : DynamicCircuit Var n}, CommutesWithDyn U₁ p → CommutesWithDyn U₂ p → CommutesWithDyn
    (U₁ * U₂) p := by
  intro p h₁ h₂
  induction p with
  | circuit _ => dsimp only [CommutesWithDyn, Submonoid.coe_mul]
                 rw [← Matrix.mul_assoc, h₁, Matrix.mul_assoc, h₂, ← Matrix.mul_assoc]
  | measure _ _ => intro o
                   dsimp only [Submonoid.coe_mul]
                   rw [← Matrix.mul_assoc, h₁ o, Matrix.mul_assoc, h₂ o, ← Matrix.mul_assoc]
  | qIf _ _ _ iht ihf => exact ⟨iht h₁.1 h₂.1, ihf h₁.2 h₂.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h₁.1 h₂.1, ih₂ h₁.2 h₂.2⟩
theorem obs_ext_mat {N : ℕ} {A B : Observable (Fin N)} (h : A.1.1 = B.1.1) : A = B := by
  apply Subtype.ext; apply Subtype.ext; exact h
theorem wp_qAssign_obs_map_comm {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    (U : Unitary (2 ^ n)) :
    ∀ (p : DynamicCircuit Var n), CommutesWithDyn U p →
    ∀ (Q : CQAssertion (Store Var) (2 ^ n)),
      wp p.compile (fun σ ↦ qAssign_obs_map U (Q σ)) =
        fun σ ↦ qAssign_obs_map U (wp p.compile Q σ) := by
  let _ : Fintype Var := Fintype.ofFinite Var
  have hConj {A X : Operator (2 ^ n)} (hc : A * U.1 = U.1 * A) : Aᴴ * (U.1ᴴ * X * U.1) * A = U.1ᴴ *
      (Aᴴ * X * A) * U.1 := by
    have hcH : U.1ᴴ * Aᴴ = Aᴴ * U.1ᴴ := by
      simpa only [conjTranspose_mul] using congrArg conjTranspose hc
    calc Aᴴ * (U.1ᴴ * X * U.1) * A = (Aᴴ * U.1ᴴ) * X * (U.1 * A) := by simp only [Matrix.mul_assoc]
      _ = (U.1ᴴ * Aᴴ) * X * (A * U.1) := by rw [hcH, hc]
      _ = U.1ᴴ * (Aᴴ * X * A) * U.1 := by simp only [Matrix.mul_assoc]
  intro p hcomm Q
  induction p generalizing Q with
  | circuit c =>
      refine funext fun σ ↦ ?_
      change wp c.compile _ σ = qAssign_obs_map U (wp c.compile Q σ)
      rw [congrFun (wp_circuit_compile_loc c _) σ, congrFun (wp_circuit_compile_loc c Q) σ]
      refine obs_ext_mat ?_
      simp only [wpQAssignCompat, qAssign_obs_map_mat]
      exact @hConj c.eval.1 (Q σ).1.1 hcomm
  | measure v r =>
      have hM (F : Fin (2 ^ 1) → Observable (Fin (2 ^ n))) :
          (qMeasure_obs_map (r.computationalBasisMeasurement : Measurement (2 ^ n) (2 ^ 1)) F).1.1 =
          (r.basisOutcomeProjector 0)ᴴ * (F 0).1.1 * r.basisOutcomeProjector 0 +
          (r.basisOutcomeProjector 1)ᴴ * (F 1).1.1 * r.basisOutcomeProjector 1 := by
        have hc : (qMeasure_obs_map (r.computationalBasisMeasurement : Measurement (2 ^ n)
            (2 ^ 1)) F).1 =
            (F 0).1.conj ((r.basisOutcomeProjector 0)ᴴ) +
              (F 1).1.conj ((r.basisOutcomeProjector 1)ᴴ) := by
          rw [qMeasure_obs_map_coe]
          change ∑ o : Fin 2, _ = _
          rw [Fin.sum_univ_two]
          simp [qMeasure_outcome_herm_eq_conj, CompleteMeasurement.toMeasurement_coe,
              QRegister.computationalBasisMeasurement_apply]
        have hm := congrArg HermitianMat.mat hc
        rw [HermitianMat.mat_add, conj_apply_mat, conj_apply_mat,
          conjTranspose_conjTranspose, conjTranspose_conjTranspose] at hm
        exact hm
      refine funext fun σ ↦ ?_
      let Q' : CQAssertion (Store Var) (2 ^ n) := fun σ' ↦ qAssign_obs_map U (Q σ')
      have hw (R) : wp (DynamicCircuit.measure v r).compile R σ =
          qMeasure_obs_map (r.computationalBasisMeasurement : Measurement (2 ^ n) (2 ^ 1))
              (fun o ↦ R (σ.subst v ↑o.1)) :=
        wp_qMeasure_apply (r.computationalBasisMeasurement : Measurement (2 ^ n) (2 ^ 1)) v R σ
      change wp (DynamicCircuit.measure v r).compile Q' σ =
        qAssign_obs_map U (wp (DynamicCircuit.measure v r).compile Q σ)
      rw [hw Q', hw Q]
      refine obs_ext_mat ?_
      rw [qAssign_obs_map_mat, hM, hM, Matrix.mul_add, Matrix.add_mul]
      simp only [Q', qAssign_obs_map_mat]
      rw [hConj (hcomm 0), hConj (hcomm 1)]
  | qIf cond t f iht ihf =>
      funext σ; dsimp only [DynamicCircuit.compile_qIf, wp]; split_ifs
      · exact congrFun (iht hcomm.1 Q) σ
      · exact congrFun (ihf hcomm.2 Q) σ
  | seq p₁ p₂ ih₁ ih₂ =>
      rw [wp_seq_compile, ih₂ hcomm.2 Q, ih₁ hcomm.1, ← wp_seq_compile]
/--
Universal left-multiplication congruence for `SubspaceStep` under any commuting unitary `U`
(applies seamlessly to both static circuits AND dynamic MBU Stage-4 / `pKin` programs.).
-/
theorem subspaceStep_mul_left_of_commutesWithDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (U : Unitary (2 ^ n)) {p : DynamicCircuit Var n}
    (hcomm : CommutesWithDyn U p) {R₁ R₂ : Operator (2 ^
    n)} (hp : SubspaceStep (Var := Var) R₁ R₂ p) : SubspaceStep (Var := Var) (U.1 * R₁)
      (U.1 * R₂) p := fun M ↦ by
  have hUU : U.1 * U.1ᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using U.2.2
  have hUUL (X : Operator (2 ^ n)) : U.1 * (U.1ᴴ * X) = X := by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hUHL (X : Operator (2 ^ n)) : U.1ᴴ * (U.1 * X) = X := by
    rw [← Matrix.mul_assoc, show U.1ᴴ * U.1 = 1 by simpa [Matrix.star_eq_conjTranspose] using U.2.1,
        Matrix.one_mul]
  have hinv_mat : (U⁻¹).1 = U.1ᴴ := by
    have hL : (U⁻¹).1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
    rw [← Matrix.mul_one (U⁻¹).1, ← hUU, ← Matrix.mul_assoc, hL, Matrix.one_mul]
  rcases hp (qAssign_obs_map U M) with ⟨N, hwpN, hmatN⟩
  refine ⟨qAssign_obs_map U⁻¹ N, ?_, ?_⟩
  · have hcancel : (fun _ : Store Var ↦ qAssign_obs_map U⁻¹ (qAssign_obs_map U M)) = (fun _ ↦ M) :=
        funext fun _ ↦
      obs_ext_mat
          (by simp only [qAssign_obs_map_mat, hinv_mat, conjTranspose_conjTranspose,
                Matrix.mul_assoc, hUU, Matrix.mul_one, hUUL])
    rw [← hcancel, wp_qAssign_obs_map_comm U⁻¹ p (commutesWithDyn_inv U hcomm), hwpN]
  · rw [qAssign_obs_map_mat] at hmatN
    simpa only [qAssign_obs_map_mat, hinv_mat, conjTranspose_conjTranspose, conjTranspose_mul,
        Matrix.mul_assoc, hUHL] using
      (by simpa only [Matrix.mul_assoc] using hmatN : R₂ᴴ * (U.1ᴴ * (M.1.1 * (U.1 * R₂))) = R₁ᴴ *
            (N.1.1 * R₁))
/-- Specification/circuit helper `zResetFixupDyn`. -/
def zResetFixupDyn (v : Var) {n : ℕ} (q : Wire n) (cFix : Circuit n) : DynamicCircuit Var n :=
  .seq (.measure v (QRegister.singleton q))
    (.qIf (fun σ ↦ σ v = 1) (.circuit (Circuit.X q ;;ᶜ cFix)) .identity)
@[simp] theorem count_zResetFixupDyn_t (v : Var) {n : ℕ} (q : Wire n) (cFix : Circuit n) :
    (zResetFixupDyn v q cFix).count .T = cFix.count .T := by
  simp [zResetFixupDyn, DynamicCircuit.count]
@[simp] theorem count_zResetFixupDyn_toff (v : Var) {n : ℕ} (q : Wire n) (cFix : Circuit n) :
    (zResetFixupDyn v q cFix).count .TOFF = cFix.count .TOFF := by
  simp [zResetFixupDyn, DynamicCircuit.count]
theorem subspaceStep_of_circuit [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (R : Operator (2 ^ n)) (c : Circuit n) :
    SubspaceStep (Var := Var) R (c.eval.1 * R) (.circuit c) := fun M ↦
  ⟨qAssign_obs_map c.eval M, wp_circuit_constObservable c M, by
    rw [qAssign_obs_map_mat]; simp only [conjTranspose_mul, Matrix.mul_assoc]⟩
theorem subspaceStep_congr_out [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R_in R₁ R₂ : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (hp : SubspaceStep (Var := Var) R_in R₁ p) (heq : R₁ = R₂) :
    SubspaceStep (Var := Var) R_in R₂ p := heq ▸ hp
theorem subspaceStep_congr_in [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R₁ R₂ R_out : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (heq : R₁ = R₂) (hp : SubspaceStep (Var := Var) R₂ R_out p) :
    SubspaceStep (Var := Var) R₁ R_out p := heq ▸ hp
end QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep

namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
open Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
theorem subspaceStep_seq_u {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {A B C : Operator (2 ^ n)} {c1 c2 : DynamicCircuit Var n} (h1 : SubspaceStep A B c1)
    (h2 : SubspaceStep B C c2) :
    SubspaceStep A C (.seq c1 c2) := h1.seq h2
end QuantumComputation.Specs.PhotochemistrySolution.CoulombFast

section
open DynamicCircuit Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.FastQft8
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectQft8GidneyStg3
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (czCircuit bitSign
    bitSign_zero bitSign_add)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires
    AndBracketWires)
-- primitives (part 0: DiagZProg & wire footprint) for 34-AND QFT8
/-- Diagonal Clifford `Z` / `CZ` program for zero-`T` phase corrections (`+128` mod `256`). -/
inductive DiagZProg (M : ℕ) where
  | id : DiagZProg M
  | z (u : Wire M) : DiagZProg M
  | cz (a b : Wire M) (h : a ≠ b) : DiagZProg M
  | seq (p₁ p₂ : DiagZProg M) : DiagZProg M
namespace DiagZProg

/-- Lowering of a `DiagZProg` into `AndBracketProg`. -/
def toBracket {M : ℕ} : DiagZProg M → AndBracketProg M
  | .id => .id
  | .z u => .prim (zGateCirc u)
  | .cz a b h => .prim (czCircuit a b h)
  | .seq p₁ p₂ => .seq p₁.toBracket p₂.toBracket
/-- Parity phase bit in `ZMod 2` accumulated on basis assignment `β`. -/
def phaseBit {M : ℕ} : DiagZProg M → BitAssignment M → ZMod 2
  | .id, _ => 0
  | .z u, β => β u
  | .cz a b _, β => β a * β b
  | .seq p₁ p₂, β => p₁.phaseBit β + p₂.phaseBit β
/-- Wire-support predicate on `DiagZProg`. -/
def wires {M : ℕ} (P : Wire M → Prop) : DiagZProg M → Prop
  | .id => True
  | .z u => P u
  | .cz a b _ => P a ∧ P b
  | .seq p₁ p₂ => wires P p₁ ∧ wires P p₂
@[simp] theorem numTempAnd_toBracket {M : ℕ} (p : DiagZProg M) : p.toBracket.numTempAnd = 0 := by
  induction p <;> simp [toBracket, AndBracketProg.numTempAnd, *]
end DiagZProg

/-- Wire-support predicate on `ClassicalBracketProg`. -/
def CBPDisj {M : ℕ} (P : Wire M → Prop) : ClassicalBracketProg M → Prop
  | .id => True
  | .x u => P u
  | .cnot c t _ => P c ∧ P t
  | .seq p₁ p₂ => CBPDisj P p₁ ∧ CBPDisj P p₂
  | .tempAnd c₁ c₂ a _ _ _ body => P c₁ ∧ P c₂ ∧ P a ∧ CBPDisj P body
theorem cbpDisj_andBracketWires {M : ℕ} {P : Wire M → Prop} (p : ClassicalBracketProg M)
    (hp : CBPDisj P p) : AndBracketWires P p.toBracket := by
  induction p with
  | id => trivial
  | x _ => exact fun ⟨0, _⟩ ↦ hp
  | cnot _ _ _ => exact fun | ⟨0, _⟩ => hp.1 | ⟨1, _⟩ => hp.2
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact ⟨hp.1, hp.2.1, hp.2.2.1, ih hp.2.2.2⟩
theorem andBracketWires_reverse {M : ℕ} {P : Wire M → Prop} (p : AndBracketProg M)
    (hp : AndBracketWires P p) : AndBracketWires P p.reverse := by
  induction p with
  | id => trivial
  | prim _ => exact hp
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hp.2, ih₁ hp.1⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact ⟨hp.1, hp.2.1, hp.2.2.1, ih hp.2.2.2⟩

-- full adder spec for 34-AND QFT8 (-120 T/step at +0 Q)
theorem cbpDisj_evalBits {M : ℕ} {P : Wire M → Prop} (p : ClassicalBracketProg M)
    (hp : CBPDisj P p) : ∀ {β₁ β₂ : BitAssignment M}, (∀ w, P w → β₁ w = β₂ w) →
    (∀ w, P w → p.evalBits β₁ w = p.evalBits β₂ w) ∧ (∀ w, ¬ P w → p.evalBits β₁ w = β₁ w) := by
  have hupd {β₁ β₂ : BitAssignment M} {u : Wire M} {v₁ v₂ : ZMod 2} (hu : P u) (hv : v₁ = v₂)
      (hEq : ∀ w, P w → β₁ w = β₂ w) :
      (∀ w, P w → Function.update β₁ u v₁ w = Function.update β₂ u v₂ w) ∧ (∀ w, ¬ P w →
        Function.update β₁ u v₁ w = β₁ w) :=
    ⟨fun w hw ↦ if hwu : w = u then by simp [hwu, hv] else by simp [Function.update_of_ne hwu,
      hEq w hw], fun w hnw ↦ Function.update_of_ne (fun e : w = u ↦ hnw (Eq.mp
        (congrArg P e.symm) hu)) _ _⟩
  induction p with
  | id => exact fun {_ _} hEq ↦ ⟨hEq, fun _ _ ↦ rfl⟩
  | x u => exact fun {_ _} hEq ↦ hupd hp (congrArg (· + 1) (hEq u hp)) hEq
  | cnot c t _ => exact fun {_ _} hEq ↦ hupd hp.2 (congrArg₂ (· + ·) (hEq t hp.2)
      (hEq c hp.1)) hEq
  | seq _ _ ih₁ ih₂ =>
      intro _ _ hEq
      obtain ⟨e₁, f₁⟩ := ih₁ hp.1 hEq
      obtain ⟨e₂, f₂⟩ := ih₂ hp.2 e₁
      exact ⟨e₂, fun w hnw ↦ (f₂ w hnw).trans (f₁ w hnw)⟩
  | tempAnd c₁ c₂ a _ _ _ _ ih =>
      intro _ _ hEq
      obtain ⟨h₁, h₂, ha, hb⟩ := hp
      obtain ⟨t₁, f₁⟩ := hupd ha (congrArg₂ (· + ·) (hEq a ha) (congrArg₂ (· * ·) (hEq c₁ h₁)
        (hEq c₂ h₂))) hEq
      obtain ⟨eB, fB⟩ := ih hb t₁
      obtain ⟨t₂, f₂⟩ := hupd ha (congrArg₂ (· + ·) (eB a ha) (congrArg₂ (· * ·) (eB c₁ h₁)
        (eB c₂ h₂))) eB
      exact ⟨t₂, fun w hnw ↦ (f₂ w hnw).trans ((fB w hnw).trans (f₁ w hnw))⟩
theorem cbpDisj_commClean {M : ℕ} (S : Finset (Wire M)) (p : ClassicalBracketProg M)
    (h0 : p.numTempAnd = 0) (hp : CBPDisj (fun u ↦ u ∉ S) p) : CommCleanBracket S p.toBracket := by
  induction p with
  | id => trivial
  | x u =>
      exact EvalPhasePerm.comm_cleanProj_of_fix (p := .prim (.X u)) (ph := fun _ ↦ 0)
        (f := fun β ↦ Function.update β u (β u + 1)) (fun β ↦ by
          rw [bitSign_zero, one_smul]
          exact PhotochemistrySolution.KinB.ket_X u β)
        S (fun _ w hw ↦ Function.update_of_ne (fun e ↦ by subst e; exact hp hw) _ _)
  | cnot c t h => exact hcnot_comm_clean S c t h hp.2
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ (Nat.eq_zero_of_add_eq_zero_right h0) hp.1, ih₂
      (Nat.eq_zero_of_add_eq_zero_left h0) hp.2⟩
  | tempAnd _ _ _ _ _ _ _ _ => dsimp [ClassicalBracketProg.numTempAnd] at h0
                               omega

-- bracket definition (-120 T/step at +0 Q)
theorem fin8_ne {i j : Fin 8} (h : decide (i ≠ j) = true) : i ≠ j := of_decide_eq_true h
theorem slice07_le8 : 0 + 7 ≤ 8 := by omega
end QuantumComputation.Specs.PhotochemistrySolution.FastQft8
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.FastQft8
open Operator QProg DynamicCircuit Matrix Circuit Qubit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (bitSign bitSign_zero bitSign_add)
-- T-count, self-inverse Clifford, and wire footprint
-- CatShiftSpec algebra for 34-AND QFT8 (-120 T/step at +0 Q)
/--
Forward and reverse `CleanWorkStep` on `rTot.compose rClean13` plus clean-projector
commutation for an `AndBracketProg`.
-/
def CleanStepPair13 {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister M n) (rClean13 : QRegister 13 M) (p : AndBracketProg M) : Prop :=
    p.IsSelfInvPrim ∧ p.toCircuit.eval.1 * cleanProj (Finset.univ.image rClean13.wires) =
    cleanProj (Finset.univ.image rClean13.wires) * p.toCircuit.eval.1 ∧
    CleanWorkStep (rTot.compose rClean13) (rTot.embedUnitary p.toCircuit.eval)
    ((p.onRegister rTot).toDyn v) ∧ CleanWorkStep (rTot.compose rClean13)
    ((rTot.embedUnitary p.toCircuit.eval)⁻¹) ((p.reverse.onRegister rTot).toDyn v)
theorem CleanStepPair13.id {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister M n) (rClean13 : QRegister 13 M) :
    CleanStepPair13 v rTot rClean13 .id := by
  have hs := cleanWorkStep_onRegister_of_commClean v rTot rClean13 .id trivial
  refine ⟨trivial, by simp [AndBracketProg.toCircuit], hs, ?_⟩
  have h1 : (rTot.embedUnitary AndBracketProg.id.toCircuit.eval)⁻¹ =
      rTot.embedUnitary AndBracketProg.id.toCircuit.eval := by
    change (rTot.embedUnitary (1 : Unitary (2 ^ M)))⁻¹ = rTot.embedUnitary 1;
    rw [rTot.embedUnitary_one, inv_one]
  rw [h1]; exact hs
theorem CleanStepPair13.seq {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    {v : Var} {rTot : QRegister M n} {rClean13 : QRegister 13 M} {p₁ p₂ : AndBracketProg M}
    (h₁ : CleanStepPair13 v rTot rClean13 p₁) (h₂ : CleanStepPair13 v rTot rClean13 p₂) :
    CleanStepPair13 v rTot rClean13 (.seq p₁ p₂) := by
  obtain ⟨⟨hs₁, hc₁, hf₁, hr₁⟩, ⟨hs₂, hc₂, hf₂, hr₂⟩⟩ := And.intro h₁ h₂
  refine ⟨⟨hs₁, hs₂⟩, ?_, ?_, ?_⟩
  · simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
    rw [Matrix.mul_assoc, hc₁, ← Matrix.mul_assoc, hc₂, Matrix.mul_assoc]
  · simpa only [AndBracketProg.toCircuit, AndBracketProg.onRegister, AndBracketProg.toDyn,
      Circuit.eval_seq, rTot.embedUnitary_mul] using CleanWorkStep.seq hf₁ hf₂
  · simpa only [AndBracketProg.toCircuit, AndBracketProg.reverse, AndBracketProg.onRegister,
      AndBracketProg.toDyn, Circuit.eval_seq, rTot.embedUnitary_mul, _root_.mul_inv_rev] using
      CleanWorkStep.seq hr₂ hr₁
/-- Signed-phase-gradient action on `rCat 0..6` (mod/div `128`) under clean predicate `cleanP`. -/
def CatShiftOn {M : ℕ} (rCat : QRegister 8 M) (cleanP : BitAssignment M → Prop)
    (Δ : BitAssignment M → ℕ) (p : AndBracketProg M) : Prop :=
  ∃ (ph : BitAssignment M → ZMod 2) (f : BitAssignment M → BitAssignment M),
    EvalPhasePerm p ph f ∧
    (∀ (β : BitAssignment M) (u : Wire M),
      (∀ j : Fin 7, u ≠ rCat ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 7)⟩) →
        f β u = β u) ∧
    (∀ β : BitAssignment M, cleanP β →
      PhotochemistrySolution.regVal 7 (rCat.slice 0 7 slice07_le8) (f β) =
        (PhotochemistrySolution.regVal 7 (rCat.slice 0 7 slice07_le8) β + Δ β) % 128 ∧
      ph β =
        (((PhotochemistrySolution.regVal 7 (rCat.slice 0 7 slice07_le8) β + Δ β) /
            128 : ℕ) : ZMod 2))
/-- Signed-phase-gradient action under `rClean13 = 0`. -/
abbrev CatShiftSpec {M : ℕ} (rCat : QRegister 8 M) (rClean13 : QRegister 13 M)
    (Δ : BitAssignment M → ℕ) (p : AndBracketProg M) : Prop :=
    CatShiftOn rCat (fun β ↦ ∀ j : Fin 13, β (rClean13 j) = 0) Δ p
theorem CatShiftOn.comm_cleanProj {M : ℕ} {rCat : QRegister 8 M}
    {cleanP : BitAssignment M → Prop} {Δ : BitAssignment M → ℕ} {p : AndBracketProg M}
    (h : CatShiftOn rCat cleanP Δ p) (S : Finset (Wire M))
    (hDisj : ∀ w ∈ S, ∀ j : Fin 7, w ≠ rCat ⟨j.val, by omega⟩) :
    p.toCircuit.eval.1 * cleanProj S = cleanProj S * p.toCircuit.eval.1 := by
  obtain ⟨ph, f, hev, hout, _⟩ := h
  exact EvalPhasePerm.comm_cleanProj_of_fix hev S fun β w hw ↦ hout β w (hDisj w hw)
theorem CatShiftSpec.seq {M : ℕ} {rCat : QRegister 8 M} {rClean13 : QRegister 13 M}
    (hCatClean : rCat.DisjointWires rClean13)
    {Δ₁ Δ₂ : BitAssignment M → ℕ} {p₁ p₂ : AndBracketProg M}
    (h₁ : CatShiftSpec rCat rClean13 Δ₁ p₁)
    (h₂ : CatShiftSpec rCat rClean13 Δ₂ p₂)
    (hInv₂ : ∀ γ₁ γ₂ : BitAssignment M,
      (∀ u, (∀ j : Fin 7, u ≠ rCat ⟨j.val, by omega⟩) → γ₁ u = γ₂ u) → Δ₂ γ₁ = Δ₂ γ₂) :
    CatShiftSpec rCat rClean13 (fun β ↦ Δ₁ β + Δ₂ β) (.seq p₁ p₂) := by
  obtain ⟨ph₁, f₁, hev₁, hout₁, hv₁⟩ := h₁; obtain ⟨ph₂, f₂, hev₂, hout₂, hv₂⟩ := h₂
  refine ⟨fun β ↦ ph₁ β + ph₂ (f₁ β), fun β ↦ f₂ (f₁ β), EvalPhasePerm.seq hev₁ hev₂, fun β u hu ↦
      (hout₂ (f₁ β) u hu).trans (hout₁ β u hu), fun β h0 ↦ ?_⟩
  dsimp only
  obtain ⟨hs₁, hp₁⟩ := hv₁ β h0
  obtain ⟨hs₂, hp₂⟩ := hv₂ (f₁ β) fun j ↦
    (hout₁ β (rClean13 j) fun c e ↦ hCatClean.ne ⟨c.val, by omega⟩ j e.symm).trans (h0 j)
  rw [hInv₂ (f₁ β) β (hout₁ β), hs₁] at hs₂ hp₂
  exact ⟨hs₂.trans (by omega),
    by simpa only [hp₁, hp₂, ← Nat.cast_add] using congrArg Nat.cast (by omega)⟩
end QuantumComputation.Specs.PhotochemistrySolution.FastQft8
end

end ScopedLocalHelpers
end
