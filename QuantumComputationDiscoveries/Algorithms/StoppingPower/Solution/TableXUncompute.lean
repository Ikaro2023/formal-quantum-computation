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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SingleAnchorPauliCap
set_option Elab.async false

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModTableXUncompute
@[expose] public section
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators
noncomputable def diagSignUnitary {k : ℕ} (phase : Fin (2 ^ k) → Bool) : Unitary (2 ^ k) :=
  ⟨Matrix.diagonal fun x ↦ if phase x then (-1 : ℂ) else 1, by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    by_cases h : phase x = true
    · simp [h]
    · simp [h]⟩
@[simp] theorem diagSignUnitary_false {k : ℕ} :
    diagSignUnitary (k := k) (fun _ ↦ false) = 1 := by
  apply Subtype.ext
  simp [diagSignUnitary]
theorem embedUnitary_diagSignUnitary_mulVec_single {n k : ℕ}
    (r : QRegister k n) (phase : Fin (2 ^ k) → Bool) (g : Fin (2 ^ n)) :
    (r.embedUnitary (diagSignUnitary phase)).1.mulVec (Pi.single g 1) =
      (if phase (r.extractIndex g) then (-1 : ℂ) else 1) • Pi.single g 1 := by
  funext i
  rw [QRegister.embedUnitary_val, diagSignUnitary, r.embedMatrix_diagonal_mulVec]
  by_cases hig : i = g
  · simp [hig]
  · simp [Pi.single_eq_of_ne hig]
def f2Parity (b : ℕ) (f : Fin b → Bool) (v : Fin (2 ^ b)) : Bool :=
  (List.finRange b).foldr (fun i acc ↦ xor (f i && decide (basisBits b v i ≠ 0)) acc) false
theorem sign_f2Parity_eq_prod (b : ℕ) (f : Fin b → Bool) (v : Fin (2 ^ b)) :
    (if f2Parity b f v then (-1 : ℂ) else 1) =
      ∏ i : Fin b, if f i && decide (basisBits b v i ≠ 0) then (-1 : ℂ) else 1 := by
  have hx (x y : Bool) : (if xor x y then (-1 : ℂ) else 1) =
      (if x then (-1 : ℂ) else 1) * (if y then (-1 : ℂ) else 1) := by
    match x, y with | false, _ => simp | true, false => norm_num | true, true => norm_num
  have haux (l : List (Fin b)) (p : Fin b → Bool) :
      (if l.foldr (fun i acc ↦ xor (p i) acc) false then (-1 : ℂ) else 1) =
        (l.map fun i ↦ if p i then (-1 : ℂ) else 1).prod := by
    induction l with
    | nil => simp
    | cons _ _ ih => rw [List.foldr_cons, List.map_cons, List.prod_cons, hx, ih]
  rw [f2Parity, haux, Fin.prod_univ_def]
@[simp] theorem f2Parity_zero (b : ℕ) (f : Fin b → Bool) : f2Parity b f 0 = false := by
  have h0 (i : Fin b) : basisBits b 0 i = 0 := by simp [-Nat.reducePow, basisBits_eq_div_mod]
  simp only [f2Parity, h0, ne_eq, not_true_eq_false, decide_false, Bool.and_false, Bool.false_xor]
  induction List.finRange b with
  | nil => rfl
  | cons _ _ ih => exact ih
noncomputable def setTableOp {n k b : ℕ} (rData : QRegister k n) (rMeas : QRegister b n)
    (tbl : Fin (2 ^ k) → Fin (2 ^ b)) : Operator (2 ^ n) := Matrix.of fun i h ↦ if i =
    rMeas.replaceIndex h (tbl (rData.extractIndex h)) then 1 else 0
theorem setTableOp_mulVec_single {n k b : ℕ} (rData : QRegister k n) (rMeas : QRegister b n)
    (tbl : Fin (2 ^ k) → Fin (2 ^ b)) (h : Fin (2 ^ n)) : (setTableOp rData rMeas tbl).mulVec
    (Pi.single h 1) = Pi.single (rMeas.replaceIndex h (tbl (rData.extractIndex h))) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  by_cases hi : i = rMeas.replaceIndex h (tbl (rData.extractIndex h))
  · simp [setTableOp, hi]
  · simp [setTableOp, hi]
private theorem lemHex31f {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ g : Fin d, A.mulVec (Pi.single g 1) = B.mulVec (Pi.single g 1)) : A = B := by
  ext i g
  have hgi := congrFun (h g) i
  simp only [Matrix.mulVec_single_one] at hgi
  exact hgi
theorem tableXReset_mul_setTableOp_mul_zeroMeas {n k b : ℕ} (rData : QRegister k n)
    (rMeas : QRegister b n) (tbl : Fin (2 ^ k) → Fin (2 ^ b)) (f : Fin b → Bool) :
    (rData.embedUnitary (diagSignUnitary (fun x ↦ f2Parity b f (tbl x)))).1 *
    DynCircuitExt.xResetKraus rMeas f * setTableOp rData rMeas tbl *
    rMeas.basisOutcomeProjector 0 = (((√(1 / 2)) ^ b : ℝ) : ℂ) • rMeas.basisOutcomeProjector 0
    := by
  apply lemHex31f
  intro g
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    rMeas.basisOutcomeProjector_mulVec_single, Matrix.smul_mulVec,
    rMeas.basisOutcomeProjector_mulVec_single]
  by_cases hg0 : rMeas.extractIndex g = 0
  · simp only [hg0, ↓reduceIte]
    rw [setTableOp_mulVec_single]
    let g' := rMeas.replaceIndex g (tbl (rData.extractIndex g))
    have hRep : rMeas.replaceIndex g' 0 = g := by
      apply rMeas.basisSplitEquiv.injective
      rw [rMeas.basisSplitEquiv_replaceIndex, rMeas.basisSplitEquiv_replaceIndex]
      exact Prod.ext (by simp [QRegister.basisSplitEquiv_apply_fst, hg0]) rfl
    change (rData.embedUnitary (diagSignUnitary (fun x ↦ f2Parity b f (tbl x)))).1.mulVec
      ((DynCircuitExt.xResetKraus rMeas f).mulVec (Pi.single g' 1)) = _
    rw [DynCircuitExt.xResetKraus_mulVec_single, rMeas.extractIndex_replaceIndex, hRep,
      ← sign_f2Parity_eq_prod, Matrix.mulVec_smul, embedUnitary_diagSignUnitary_mulVec_single,
      smul_smul]
    refine congrArg₂ (· • ·) ?_ rfl
    cases f2Parity b f (tbl (rData.extractIndex g))
    · simp
    · simp
  · simp [hg0]
namespace DynCircuitExt
open _root_.DynamicCircuit
section UniversalTableUncompute
variable {Var : Type} [Fintype Var] [DecidableEq Var] {n k b m : ℕ} [NeZero (2 ^ n)]
theorem realizesCleanTableXUncompute (v : Var) (rData : QRegister k n) (rMeas : QRegister b n)
    (rScr : QRegister m n) (hDM : rData.DisjointWires rMeas) (hDS : rData.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr) (tbl : Fin (2 ^ k) → Fin (2 ^ b)) {uComp : Unitary
    (2 ^ (k + b))} {uTarget : Unitary (2 ^ k)} {dPre : DynamicCircuit Var n} {cont : (Fin b →
    Bool) → DynamicCircuit Var n} (hPre : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rData.concat rMeas hDM) rScr uComp dPre) (hComp : ((rData.concat rMeas hDM).embedUnitary
    uComp).1 * (rMeas.concat rScr hMS).basisOutcomeProjector 0 = setTableOp rData rMeas tbl *
    (rData.embedUnitary uTarget).1 * (rMeas.concat rScr hMS).basisOutcomeProjector 0) (hCont :
    ∀ f : Fin b → Bool, RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMeas.concat rScr hMS)
    (diagSignUnitary (fun x ↦ f2Parity b f (tbl x))) (cont f)) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMeas.concat rScr hMS) uTarget
    (DynamicCircuit.seq dPre (measureXResetAndBranch v b rMeas cont)) := by
  let Pm : Operator (2 ^ n) := rMeas.basisOutcomeProjector 0
  let Pw : Operator (2 ^ n) := (rMeas.concat rScr hMS).basisOutcomeProjector 0
  have hPm_Pw : Pm * Pw = Pw := by
    rw [show Pw = Pm * rScr.basisOutcomeProjector 0 from
      QRegExt.concat_basisOutcomeProjector_zero rMeas rScr hMS,
      ← Matrix.mul_assoc, rMeas.basisOutcomeProjector_mul_self 0]
  have hComm : (rData.embedUnitary uTarget).1 * Pm = Pm * (rData.embedUnitary uTarget).1 :=
    rData.embedMatrix_comm_of_disjoint rMeas hDM uTarget.1 (compProj 0)
  apply realizesEmbeddedUnitaryWithCleanWorkspace_measureXReset_uniform
    v rData rMeas rScr hDM hDS hMS hPre hCont
  intro f
  let UT : Operator (2 ^ n) := (rData.embedUnitary uTarget).1
  have hComm_pw : UT * Pw = Pm * (UT * Pw) := by
    calc UT * Pw = UT * (Pm * Pw) := congrArg (UT * ·) hPm_Pw.symm
      _ = Pm * (UT * Pw) := by rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc]
  change ((rData.embedUnitary (diagSignUnitary (fun x ↦ f2Parity b f (tbl x)))).1 *
    xResetKraus rMeas f * ((rData.concat rMeas hDM).embedUnitary uComp).1) * Pw =
    (((√(1 / 2)) ^ b : ℝ) : ℂ) • (UT * Pw)
  rw [Matrix.mul_assoc _ ((rData.concat rMeas hDM).embedUnitary uComp).1 Pw, hComp,
    Matrix.mul_assoc (setTableOp rData rMeas tbl) UT Pw, hComm_pw,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    tableXReset_mul_setTableOp_mul_zeroMeas rData rMeas tbl f,
    Matrix.smul_mul, ← hComm_pw]
end UniversalTableUncompute
end DynCircuitExt
end
end ModTableXUncompute

section ModTempAndBlocks
@[expose] public section
open Operator Matrix QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
section BasisKet
variable {n : ℕ}
noncomputable abbrev basisKet (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_basisBitsEquiv_symm_eq {q : ℕ} (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits_eq {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j := (basisBitsEquiv q).symm_apply_apply j
theorem pi_single_eq_basisKet (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = basisKet (basisBits n g) := by
  simp [basisKet, basisState]
theorem matrix_ext_basisKet {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (basisKet β) = B.mulVec (basisKet β)) : A = B :=
  MeasureBranchHadamardSem.matrix_ext_ket h
@[simp] theorem evolve_X_basisKet (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (basisKet β) = basisKet (Function.update β q (β q + 1)) :=
  MeasureBranchHadamardSem.ket_X q β
@[simp] theorem evolve_CNOT_basisKet (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (basisKet β) =
      basisKet (Function.update β t (β t + β c)) :=
  MeasureBranchHadamardSem.ket_CNOT c t h β
@[simp]
theorem evolve_TOFF_basisKet (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (basisKet β) =
    basisKet (Function.update β t (β t + β c₁ * β c₂)) :=
  MeasureBranchHadamardSem.ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t β
@[simp]
theorem basisOutcomeProjector_zero_mulVec_basisKet (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (basisKet β) =
      if β q = 0 then basisKet β else 0 :=
  MeasureBranchHadamardSem.ket_projector_zero q β
theorem register_basisOutcomeProjector_zero_mulVec_basisKet {m : ℕ} (r : QRegister m n)
    (β : BitAssignment n) : (r.basisOutcomeProjector 0).mulVec (basisKet β) =
      if ∀ i : Fin m, β (r i) = 0 then basisKet β else 0 := by
  rw [basisKet, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  simp only [QRegExt.extractIndex_eq_zero_iff, basisBits_basisBitsEquiv_symm_eq]
end BasisKet
namespace QRegExt
open _root_.QRegister
variable {n k m : ℕ}
theorem disjointWires_iff_disjoint_image (r : QRegister k n) (s : QRegister m n) :
    r.DisjointWires s ↔ Disjoint r.image s.image := by
  rw [disjoint_iff, Finset.disjoint_left]
  exact ⟨fun h _ hr hs ↦ by
    rcases (mem_image _ _).mp hr, (mem_image _ _).mp hs with ⟨⟨i, rfl⟩, ⟨j, hj⟩⟩
    exact h i j hj.symm, fun h i j hij ↦
    h ((mem_image r _).mpr ⟨i, rfl⟩) ((mem_image s _).mpr ⟨j, hij.symm⟩)⟩
@[simp] theorem image_concat (r : QRegister k n) (s : QRegister m n) (h : r.DisjointWires s) :
    (r.concat s h).image = r.image ∪ s.image := by
  ext q
  simp only [mem_image, Finset.mem_union]
  exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ Fin.addCases (fun a ↦ Or.inl ⟨a, by simp⟩)
    (fun b ↦ Or.inr ⟨b, by simp⟩) i, fun hq ↦ hq.elim
    (fun ⟨i, hi⟩ ↦ ⟨Fin.castAdd m i, by simp [hi]⟩)
    (fun ⟨j, hj⟩ ↦ ⟨Fin.natAdd k j, by simp [hj]⟩)⟩
@[simp] theorem basisOutcomeProjector_zero_of_zero (r : QRegister 0 n) :
    r.basisOutcomeProjector 0 = 1 := by
  rw [basisOutcomeProjector_eq_diagonal, ← Matrix.diagonal_one]
  congr 1
theorem image_head_tail (r : QRegister (m + 1) n) :
    r.image = insert (r 0) (r.slice 1 m (by omega)).image := by
  ext q
  simp only [mem_image, Finset.mem_insert, slice_apply]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩
    exact Fin.cases (Or.inl rfl)
      (fun j ↦ Or.inr ⟨j, congrArg r (Fin.ext (by simp [Nat.add_comm]))⟩) i
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨⟨1 + j.val, by omega⟩, rfl⟩
theorem head_not_mem_tail_image (r : QRegister (m + 1) n) :
    r 0 ∉ (r.slice 1 m (by omega)).image := by
  rintro h
  rcases (mem_image _ _).mp h with ⟨j, hj⟩
  have hval := congrArg Fin.val (r.wires.injective hj)
  dsimp [slice_apply] at hval
  omega
end QRegExt
@[simp] theorem restrictAssertionToZeroAncilla_of_zero {Var : Type} {n : ℕ}
    (M : CQAssertionCompat Var (2 ^ n)) (r : QRegister 0 n) :
    CQAssertion.restrictToZeroAncilla M r = M := by
  funext σ
  apply Subtype.ext
  simp [CQAssertion.restrictToZeroAncilla_coe]
theorem restrictAssertionToZeroAncilla_head_tail {Var : Type} {n m : ℕ}
    (M : CQAssertionCompat Var (2 ^ n)) (r : QRegister (m +
      1) n) : CQAssertion.restrictToZeroAncilla M
    r = CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla M
      (QRegister.singleton (r 0))) (r.slice 1 m (by omega)) := by
  have hsplit : r.basisOutcomeProjector 0 =
      (QRegister.singleton (r 0)).basisOutcomeProjector 0 *
      (r.slice 1 m (by omega)).basisOutcomeProjector 0 := by
    simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    have hiff : r.extractIndex g = 0 ↔ (QRegister.singleton (r 0)).extractIndex g = 0 ∧
        (r.slice 1 m (by omega)).extractIndex g = 0 := by
      simp only [QRegExt.extractIndex_eq_zero_iff, QRegister.singleton_apply,
        QRegister.slice_apply]
      refine ⟨fun h ↦ ⟨fun _ ↦ h 0, fun j ↦ h ⟨1 + j.val, by omega⟩⟩,
        fun ⟨h0, ht⟩ i ↦ Fin.cases (h0 0)
          (fun j ↦ (Fin.ext (Nat.add_comm 1 j.val) :
            (⟨1 + j.val, by omega⟩ : Fin (m + 1)) = j.succ) ▸ ht j) i⟩
    by_cases h1 : (QRegister.singleton (r 0)).extractIndex g = 0
    · simp [hiff, h1]
    · simp [hiff, h1]
  refine funext fun σ ↦ Subtype.ext ?_
  simp only [CQAssertion.restrictToZeroAncilla_coe, conj_conj, hsplit,
    QRegExt.basisOutcomeProjector_comm (QRegister.singleton (r 0)) 0 _ 0]
section DisjointSupport
variable {Var : Type} [Fintype Var] {n m : ℕ}
theorem CircuitExt.eval_comm_basisOutcomeProjector_of_disjoint_support (c : Circuit n)
    (r : QRegister m n) (hdisj : Disjoint c.support r.image) (o : Fin (2 ^ m)) : c.eval.1 *
    r.basisOutcomeProjector o = r.basisOutcomeProjector o * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g rg =>
      exact QRegister.embedMatrix_comm_of_disjoint rg r
        ((QRegExt.disjointWires_iff_disjoint_image rg r).mpr hdisj) g.eval.1 (compProj o)
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]
theorem restrictToZeroAncilla_wp_qAssign_comm_of_disjoint (c : Circuit n)
    (r : QRegister m n) (hdisj : Disjoint c.support r.image) (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ) r = wpQAssignCompat c.eval
    (CQAssertion.restrictToZeroAncilla Θ r) := funext fun σ ↦ Subtype.ext <| by
  have hadj :
      r.basisOutcomeProjector 0 * c.eval.1ᴴ = c.eval.1ᴴ * r.basisOutcomeProjector 0 := by
    simpa only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      congrArg conjTranspose ((CircuitExt.eval_comm_basisOutcomeProjector_of_disjoint_support c) r
        hdisj 0)
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  change (Θ σ).1.conj (r.basisOutcomeProjector 0 * c.eval.1ᴴ) =
    (Θ σ).1.conj (c.eval.1ᴴ * r.basisOutcomeProjector 0)
  rw [hadj]
end DisjointSupport
section ClassicalPerm
variable {n : ℕ}
def ClassicalPerm (c : Circuit n) (f : BitAssignment n → BitAssignment n) : Prop :=
  ∀ β : BitAssignment n, c.eval.1.mulVec (basisKet β) = basisKet (f β)
theorem ClassicalPerm.identity : ClassicalPerm (Circuit.identity : Circuit n) id := fun β ↦ by
  rw [Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec]
  rfl
theorem ClassicalPerm.X (q : Wire n) : ClassicalPerm (Circuit.X q)
    (fun β ↦ Function.update β q (β q + 1)) := evolve_X_basisKet q
theorem ClassicalPerm.CNOT (c t : Wire n) (h : c ≠ t) : ClassicalPerm (Circuit.CNOT c t h)
    (fun β ↦ Function.update β t (β t + β c)) := evolve_CNOT_basisKet c t h
theorem ClassicalPerm.TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    ClassicalPerm (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t)
      (fun β ↦ Function.update β t (β t + β c₁ * β c₂)) :=
  evolve_TOFF_basisKet c₁ c₂ t h₁₂ h₁t h₂t
theorem ClassicalPerm.seq {c₁ c₂ : Circuit n} {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : ClassicalPerm c₁ f₁) (h₂ : ClassicalPerm c₂ f₂) :
    ClassicalPerm (c₁ ;;ᶜ c₂) (f₂ ∘ f₁) := fun β ↦ by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁ β, Function.comp_apply,
    h₂ (f₁ β)]
theorem toffoli_conj_preserves_zero_ancilla_of_classicalPerm (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (c_body : Circuit n)
    (f_body : BitAssignment n → BitAssignment n) (hperm : ClassicalPerm c_body f_body)
    (hc₁ : ∀ β, f_body β c₁ = β c₁) (hc₂ : ∀ β, f_body β c₂ = β c₂)
    (hanc : ∀ β, f_body β anc = β anc) :
    let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
    P₀ * (T_anc * c_body.eval.1 * T_anc * P₀) = T_anc * c_body.eval.1 * T_anc * P₀ := by
  intro P₀ T_anc
  refine matrix_ext_basisKet fun β ↦ ?_
  dsimp only [P₀, T_anc]
  simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases hβ : β anc = 0
  · simp only [hβ, ↓reduceIte, evolve_TOFF_basisKet, zero_add]
    let β₁ := Function.update β anc (β c₁ * β c₂)
    rw [hperm β₁, evolve_TOFF_basisKet, basisOutcomeProjector_zero_mulVec_basisKet]
    have hzero : f_body β₁ anc + f_body β₁ c₁ * f_body β₁ c₂ = 0 := by
      rw [hanc β₁, hc₁ β₁, hc₂ β₁]
      simp [β₁, Function.update_of_ne h₁a, Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
    simp [Function.update_self, hzero]
  · simp [hβ]
end ClassicalPerm
structure TempAndStep (n : ℕ) where
  pre : Circuit n
  c₁ : Wire n
  c₂ : Wire n
  anc : Wire n
  h₁₂ : c₁ ≠ c₂
  h₁a : c₁ ≠ anc
  h₂a : c₂ ≠ anc
  midPre : Circuit n
  midPost : Circuit n
  post : Circuit n
namespace TempAndStep
variable {Var : Type} {n : ℕ}
def wrapCircuit (s : TempAndStep n) (c : Circuit n) : Circuit n :=
  s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ
    (s.midPre ;;ᶜ c ;;ᶜ s.midPost) ;;ᶜ
    Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.post
def wrapDynamic (v : Var) (s : TempAndStep n) (inner : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  .seq (.circuit s.pre) (.seq (.seq (.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a)
    (.seq (.seq (.circuit s.midPre) (.seq inner (.circuit s.midPost)))
      (.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂))) (.circuit s.post))
def IsCliffordWrapper (s : TempAndStep n) : Prop := s.pre.count .TOFF = 0 ∧ s.pre.count .T = 0
    ∧ s.midPre.count .TOFF = 0 ∧ s.midPre.count .T = 0 ∧ s.midPost.count .TOFF = 0 ∧
    s.midPost.count .T = 0 ∧ s.post.count .TOFF = 0 ∧ s.post.count .T = 0
theorem count_wrapDynamic_toff (v : Var) (s : TempAndStep n) (inner : DynamicCircuit Var n)
    (hs : s.IsCliffordWrapper) : (s.wrapDynamic v inner).count .TOFF = inner.count .TOFF := by
  rcases hs with ⟨h1, _, h2, _, h3, _, h4, _⟩
  simp [wrapDynamic, DynamicCircuit.count_andCompute_toff,
    DynamicCircuit.count_andUncompute_toff, h1, h2, h3, h4]
theorem count_wrapDynamic_t (v : Var) (s : TempAndStep n) (inner : DynamicCircuit Var n)
    (hs : s.IsCliffordWrapper) : (s.wrapDynamic v inner).count .T = 4 + inner.count .T := by
  rcases hs with ⟨_, h1, _, h2, _, h3, _, h4⟩
  simp [wrapDynamic, DynamicCircuit.count_andCompute_t, DynamicCircuit.count_andUncompute_t,
    h1, h2, h3, h4]
theorem restrictToZeroAncilla_wp_wrapDynamic_head_tail [Fintype Var] [DecidableEq Var]
    [NeZero (2 ^ n)] {m : ℕ} (v : Var) (s : TempAndStep n) (inner : DynamicCircuit Var n)
    (c_inner : Circuit n) (rTotal : QRegister (m + 1) n) (hanc : s.anc = rTotal 0)
    (hpre_anc : s.anc ∉ s.pre.support) (hpre_rest : Disjoint s.pre.support (rTotal.slice 1 m
      (by omega)).image) (hc₁_rest : s.c₁ ∉ (rTotal.slice 1 m (by omega)).image)
    (hc₂_rest : s.c₂ ∉ (rTotal.slice 1 m (by omega)).image) (hmidPre_rest : Disjoint
      s.midPre.support (rTotal.slice 1 m (by omega)).image)
    (hc_body : let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1
      P₀ * (T_anc * (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost).eval.1 * T_anc * P₀) =
        T_anc * (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost).eval.1 * T_anc * P₀)
    (h_inner : ∀ Ψ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      CQAssertion.restrictToZeroAncilla (wp inner.compile Ψ) (rTotal.slice 1 m (by omega)) =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c_inner.eval Ψ) (rTotal.slice 1 m
        (by
          omega))) (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) =
      Θ σ) : CQAssertion.restrictToZeroAncilla (wp (s.wrapDynamic v inner).compile Θ) rTotal =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat (s.wrapCircuit c_inner).eval Θ) rTotal :=
  by
  let rRest := rTotal.slice 1 m (by omega)
  have hpre_total : Disjoint s.pre.support rTotal.image := by
    rw [QRegExt.image_head_tail, ← hanc, Finset.disjoint_insert_right]
    exact ⟨hpre_anc, hpre_rest⟩
  have hand_rest :
      Disjoint (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).support rRest.image := by
    rw [Circuit.support_andCompute]
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hc₁_rest, hc₂_rest, hanc ▸ (QRegExt.head_not_mem_tail_image rTotal)⟩
  let Θ₁ := wpQAssignCompat s.post.eval Θ
  let Ψ := wpQAssignCompat s.midPost.eval
    (wp (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile Θ₁)
  let c_body := s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost
  let middle : DynamicCircuit Var n := .seq (.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a)
    (.seq (.seq (.circuit s.midPre) (.seq inner (.circuit s.midPost)))
      (.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂))
  rw [show wp (s.wrapDynamic v inner).compile Θ =
        wpQAssignCompat s.pre.eval (wp middle.compile Θ₁) by simp [wrapDynamic, middle, Θ₁],
    show wpQAssignCompat (s.wrapCircuit c_inner).eval Θ = wpQAssignCompat s.pre.eval
        (wpQAssignCompat (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ c_body ;;ᶜ
          Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval Θ₁) by
      simp only [wrapCircuit, c_body, Θ₁, Circuit.eval_seq, wpQAssignCompat_comp, mul_assoc],
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre rTotal hpre_total,
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre rTotal hpre_total]
  congr 1
  rw [restrictAssertionToZeroAncilla_head_tail _ rTotal,
    restrictAssertionToZeroAncilla_head_tail _ rTotal, ← hanc,
    restrictAssertionToZeroAncilla_comm _ (QRegister.singleton s.anc) rRest,
    show wp middle.compile Θ₁ = wpQAssignCompat (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a
        s.h₂a).eval (wpQAssignCompat s.midPre.eval (wp inner.compile Ψ)) by
      simp [middle, Ψ, DynamicCircuit.andCompute],
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint _ rRest hand_rest,
    restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.midPre rRest hmidPre_rest,
    h_inner Ψ (fun σ val ↦ by dsimp only [Ψ, wpQAssignCompat]
                              rw [DynamicCircuit.wp_andUncompute_update_self]),
    ← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint s.midPre rRest hmidPre_rest,
    ← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint _ rRest hand_rest,
    show wpQAssignCompat (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).eval
        (wpQAssignCompat s.midPre.eval (wpQAssignCompat c_inner.eval Ψ)) =
          wp (DynamicCircuit.seq (.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a) (DynamicCircuit.seq
            (.circuit c_body) (.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂))).compile Θ₁ by
      simp [c_body, Ψ, DynamicCircuit.andCompute, wpQAssignCompat_comp],
    restrictAssertionToZeroAncilla_comm _ rRest (QRegister.singleton s.anc),
    DynCircuitExt.restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq_compat
      v s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a c_body hc_body Θ₁
      (fun σ val ↦ congrArg (qAssignObsMap s.post.eval) (hΘ σ val))]
def wrapCircuitList : List (TempAndStep n) → Circuit n → Circuit n
  | [], core => core
  | s :: rest, core => s.wrapCircuit (wrapCircuitList rest core)
def wrapDynamicList (v : Var) :
    List (TempAndStep n) → DynamicCircuit Var n → DynamicCircuit Var n
  | [], core => core
  | s :: rest, core => s.wrapDynamic v (wrapDynamicList v rest core)
theorem count_wrapDynamicList_toff (v : Var) (steps : List (TempAndStep n))
    (core : DynamicCircuit Var n) (hsteps : ∀ s ∈ steps, s.IsCliffordWrapper) :
    (wrapDynamicList v steps core).count .TOFF = core.count .TOFF := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      rw [wrapDynamicList, count_wrapDynamic_toff v s _ (hsteps s (by simp)),
        ih fun s' hs' ↦ hsteps s' (by simp [hs'])]
theorem count_wrapDynamicList_t (v : Var) (steps : List (TempAndStep n))
    (core : DynamicCircuit Var n) (hsteps : ∀ s ∈ steps, s.IsCliffordWrapper) :
    (wrapDynamicList v steps core).count .T = 4 * steps.length + core.count .T := by
  induction steps with
  | nil => simp [wrapDynamicList]
  | cons s rest ih =>
      rw [wrapDynamicList, count_wrapDynamic_t v s _ (hsteps s (by simp)),
        ih fun s' hs' ↦ hsteps s' (by simp [hs']), List.length_cons]
      omega
end TempAndStep
end
end ModTempAndBlocks

section ModGidneyTempAndAdder
@[expose] public section
open Operator Matrix QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
section RegVal
def bitsVal {q : ℕ} (γ : BitAssignment q) : ℕ := ∑ i : Fin q, (γ i).val * 2 ^ i.val
def regVal {q n : ℕ} (r : QRegister q n) (β : BitAssignment n) : ℕ :=
  bitsVal (fun i ↦ β (r i))
theorem zmod2_val_le_one (b : ZMod 2) : b.val ≤ 1 := Nat.le_of_lt_succ (ZMod.val_lt b)
private lemma bitsVal_succ {m : ℕ} (g : Fin (m + 1) → ZMod 2) :
    bitsVal g = (g 0).val + 2 * bitsVal (fun j : Fin m ↦ g j.succ) := by
  unfold bitsVal
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, _root_.pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fin.val_succ, pow_succ]
  ring
theorem bitsVal_lt_two_pow {q : ℕ} (γ : BitAssignment q) : bitsVal γ < 2 ^ q := by
  induction q with
  | zero => simp [bitsVal]
  | succ q ih =>
      have h0 := zmod2_val_le_one (γ 0)
      have hlt := ih (fun i ↦ γ i.succ)
      rw [bitsVal_succ, pow_succ]
      omega
theorem regVal_lt_two_pow {q n : ℕ} (r : QRegister q n) (β : BitAssignment n) : regVal r β < 2
    ^ q := bitsVal_lt_two_pow (fun i ↦ β (r i))
theorem sum_div_two_pow_mod_two_mul_two_pow (q m : ℕ) (hm : m < 2 ^ q) :
    (∑ i : Fin q, (m / 2 ^ i.val % 2) * 2 ^ i.val) = m := by
  induction q generalizing m with
  | zero => simp [show m = 0 by simpa using hm]
  | succ q ih =>
      rw [Fin.sum_univ_succ, show (∑ i : Fin q, (m / 2 ^ i.succ.val % 2) * 2 ^ i.succ.val) =
          2 * ∑ i : Fin q, ((m / 2) / 2 ^ i.val % 2) * 2 ^ i.val by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
        ring, ih (m / 2) (by rw [pow_succ'] at hm
                             omega)]
      simp only [Fin.val_zero, _root_.pow_zero, Nat.div_one, mul_one]
      omega
@[simp] theorem bitsVal_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    bitsVal (basisBits q j) = j.val := by
  unfold bitsVal
  simp only [show ∀ i : Fin q, (basisBits q j i).val = j.val / 2 ^ i.val % 2 from fun i ↦ by
    rw [basisBits_eq_div_mod]
    exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide))]
  exact sum_div_two_pow_mod_two_mul_two_pow q j.val j.isLt
@[simp] theorem bitsVal_eq_symm_val {q : ℕ} (γ : BitAssignment q) :
    bitsVal γ = ((basisBitsEquiv q).symm γ).val := by
  simpa using bitsVal_basisBits ((basisBitsEquiv q).symm γ)
theorem regVal_eq_extractIndex_val {q n : ℕ} (r : QRegister q n) (β : BitAssignment n) :
    regVal r β = (r.extractIndex ((basisBitsEquiv n).symm β)).val := by
  simp [regVal, QRegister.extractIndex, bitsVal_eq_symm_val]
theorem regVal_head_tail {q n : ℕ} (r : QRegister (q + 1) n) (β : BitAssignment n) :
    regVal r β = (β (r 0)).val + 2 * regVal (r.slice 1 q (by omega)) β := by
  unfold regVal
  rw [bitsVal_succ (fun i ↦ β (r i))]
  refine congrArg ((β (r 0)).val + 2 * ·) (congrArg bitsVal (funext fun i ↦ ?_))
  rw [QRegister.slice_apply]
  exact congrArg (fun j ↦ β (r j)) (Fin.ext (Nat.add_comm i.val 1))
theorem regVal_congr {q n : ℕ} (r : QRegister q n) {β₁ β₂ : BitAssignment n}
    (h : ∀ i : Fin q, β₁ (r i) = β₂ (r i)) : regVal r β₁ = regVal r β₂ := by
  unfold regVal bitsVal
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp only
  rw [h i]
theorem add_two_mul_mod (s₀ X p : ℕ) (hs₀ : s₀ < 2) :
    s₀ + 2 * (X % p) = (s₀ + 2 * X) % (2 * p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have hlt : s₀ + 2 * (X % p) < 2 * p := by
      have := Nat.mod_lt X hp
      omega
    rw [show s₀ + 2 * X = (s₀ + 2 * (X % p)) + (2 * p) * (X / p) by
      linarith [Nat.div_add_mod X p], Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
end RegVal
section LocalClassicalPerm
variable {n : ℕ}
structure LocalClassicalPerm (S : Finset (Wire n)) (c : Circuit n)
    (f : BitAssignment n → BitAssignment n) : Prop where
  perm : ClassicalPerm c f
  support_sub : c.support ⊆ S
  preserves_outside : ∀ β w, w ∉ S → f β w = β w
  depends_on : ∀ β₁ β₂, (∀ w ∈ S, β₁ w = β₂ w) → ∀ w ∈ S, f β₁ w = f β₂ w
namespace LocalClassicalPerm
theorem mono {S₁ S₂ : Finset (Wire n)} {c : Circuit n} {f : BitAssignment n → BitAssignment n}
    (h : LocalClassicalPerm S₁ c f) (hsub : S₁ ⊆ S₂) : LocalClassicalPerm S₂ c f where
  perm := h.perm
  support_sub := h.support_sub.trans hsub
  preserves_outside β w hw := h.preserves_outside β w (fun hw₁ ↦ hw (hsub hw₁))
  depends_on β₁ β₂ hβ w hw₂ := by
    by_cases hw₁ : w ∈ S₁
    · exact h.depends_on β₁ β₂ (fun u hu ↦ hβ u (hsub hu)) w hw₁
    · rw [h.preserves_outside β₁ w hw₁, h.preserves_outside β₂ w hw₁, hβ w hw₂]
theorem identity (S : Finset (Wire n)) :
    LocalClassicalPerm S (Circuit.identity : Circuit n) id :=
  ⟨ClassicalPerm.identity, by simp, fun _ _ _ ↦ rfl, fun _ _ h w hw ↦ h w hw⟩
theorem CNOT {S : Finset (Wire n)} (c t : Wire n) (h : c ≠ t) (hc : c ∈ S) (ht : t ∈ S) :
    LocalClassicalPerm S (Circuit.CNOT c t h) (fun β ↦ Function.update β t (β t + β c)) where
  perm := ClassicalPerm.CNOT c t h
  support_sub q hq := by
    simp only [Circuit.support_gate, QRegister.image_pair, Finset.mem_insert,
      Finset.mem_singleton] at hq
    exact hq.elim (fun e ↦ e ▸ hc) (fun e ↦ e ▸ ht)
  preserves_outside β w hw := Function.update_of_ne (fun h' : w = t ↦ hw (h' ▸ ht)) _ _
  depends_on β₁ β₂ hβ w hw := by
    by_cases hwt : w = t
    · simp [hwt, hβ t ht, hβ c hc]
    · simp [Function.update_of_ne hwt, hβ w hw]
theorem seq {S : Finset (Wire n)} {c₁ c₂ : Circuit n}
    {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : LocalClassicalPerm S c₁ f₁) (h₂ : LocalClassicalPerm S c₂ f₂) :
    LocalClassicalPerm S (c₁ ;;ᶜ c₂) (f₂ ∘ f₁) :=
  ⟨h₁.perm.seq h₂.perm, Circuit.support_seq c₁ c₂ ▸ Finset.union_subset h₁.support_sub
    h₂.support_sub, fun β w hw ↦ by
      rw [Function.comp_apply, h₂.preserves_outside _ w hw, h₁.preserves_outside β w hw],
    fun β₁ β₂ hβ w hw ↦ h₂.depends_on _ _ (fun u hu ↦ h₁.depends_on β₁ β₂ hβ u hu) w hw⟩
@[simp] theorem zmod2_add_self (a : ZMod 2) : a + a = 0 :=
  (by decide : ∀ x : ZMod 2, x + x = 0) a
@[simp] theorem zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a :=
  (by decide : ∀ x y : ZMod 2, x + y + y = x) a b
@[simp] theorem cnot_self_cancel (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    let f := fun γ : BitAssignment n ↦ Function.update γ t (γ t + γ c)
    f (f β) = β := funext fun w ↦ by
  by_cases hwt : w = t
  · simp [hwt, Function.update_of_ne h]
  · simp [Function.update_of_ne hwt]
theorem comp_self_inv₂ {α : Type*} (f₁ f₂ : α → α)
    (h₁ : ∀ x, f₁ (f₁ x) = x) (h₂ : ∀ x, f₂ (f₂ x) = x) (x : α) :
    (f₁ ∘ f₂) ((f₂ ∘ f₁) x) = x := by simp only [Function.comp_apply, h₂, h₁]
theorem comp_self_inv₃ {α : Type*} (f₁ f₂ f₃ : α → α)
    (h₁ : ∀ x, f₁ (f₁ x) = x) (h₂ : ∀ x, f₂ (f₂ x) = x) (h₃ : ∀ x, f₃ (f₃ x) = x) (x : α) :
    ((f₁ ∘ f₂) ∘ f₃) (((f₃ ∘ f₂) ∘ f₁) x) = x := by
  simp only [Function.comp_apply, h₃, h₂, h₁]
end LocalClassicalPerm
open LocalClassicalPerm
structure SymTempAndStep (n : ℕ) extends TempAndStep n where
  S : Finset (Wire n)
  f_pre : BitAssignment n → BitAssignment n
  f_midPre : BitAssignment n → BitAssignment n
  f_midPost : BitAssignment n → BitAssignment n
  f_post : BitAssignment n → BitAssignment n
  clifford : toTempAndStep.IsCliffordWrapper
  local_pre : LocalClassicalPerm S pre f_pre
  local_post : LocalClassicalPerm S post f_post
  local_midPre : LocalClassicalPerm S midPre f_midPre
  local_midPost : LocalClassicalPerm S midPost f_midPost
  post_pre_id : ∀ β, f_post (f_pre β) = β
  midPost_midPre_id : ∀ β, f_midPost (f_midPre β) = β
  c₁_mem : c₁ ∈ S
  c₂_mem : c₂ ∈ S
  anc_mem : anc ∈ S
  anc_not_mem_pre : anc ∉ pre.support
namespace SymTempAndStep
variable {Var : Type} {n : ℕ}
def stepFwd (s : SymTempAndStep n) (β : BitAssignment n) : BitAssignment n :=
  let β₁ := s.f_pre β
  let β₂ := Function.update β₁ s.anc (β₁ s.anc + β₁ s.c₁ * β₁ s.c₂)
  s.f_midPre β₂
theorem stepFwd_outside (s : SymTempAndStep n) (β : BitAssignment n) {w : Wire n} (hw : w ∉ s.S) :
    s.stepFwd β w = β w := by
  unfold stepFwd
  have hw_anc : w ≠ s.anc := fun h ↦ hw (h ▸ s.anc_mem)
  rw [s.local_midPre.preserves_outside _ w hw, Function.update_of_ne hw_anc,
    s.local_pre.preserves_outside _ w hw]
theorem body_and_wrap_eq (s : SymTempAndStep n) {M : Finset (Wire n)}
    (hdisj : Disjoint s.S M) (f_inner : BitAssignment n → BitAssignment n)
    (h_inner_out : ∀ β w, w ∉ M → f_inner β w = β w) :
    let f_toff : BitAssignment n → BitAssignment n :=
      fun γ ↦ Function.update γ s.anc (γ s.anc + γ s.c₁ * γ s.c₂)
    let f_body := s.f_midPost ∘ f_inner ∘ s.f_midPre
    (∀ β w, w ∈ s.S → f_body β w = β w) ∧
    (∀ β, s.f_post (f_toff (f_body (f_toff (s.f_pre β)))) =
      fun w ↦ if w ∈ M then f_inner (s.stepFwd β) w else β w) := by
  intro f_toff f_body
  have hbody_S : ∀ β w, w ∈ s.S → f_body β w = β w := fun β w hw ↦ by
    dsimp only [f_body, Function.comp_apply]
    have hagree : ∀ u ∈ s.S, f_inner (s.f_midPre β) u = s.f_midPre β u :=
      fun u hu ↦ h_inner_out _ u (Finset.disjoint_left.mp hdisj hu)
    rw [s.local_midPost.depends_on _ _ hagree w hw, s.midPost_midPre_id β]
  refine ⟨hbody_S, fun β ↦ funext fun w ↦ ?_⟩
  let β₂ := f_toff (s.f_pre β)
  have htoff_S : ∀ u ∈ s.S, f_toff (f_body β₂) u = s.f_pre β u := fun u hu ↦ by
    dsimp only [f_toff]
    by_cases hua : u = s.anc
    · subst hua
      simp only [Function.update_self, hbody_S β₂ s.anc s.anc_mem,
        hbody_S β₂ s.c₁ s.c₁_mem, hbody_S β₂ s.c₂ s.c₂_mem, β₂, f_toff,
        Function.update_of_ne s.h₁a, Function.update_of_ne s.h₂a, zmod2_add_cancel_right]
    · simp only [Function.update_of_ne hua, hbody_S β₂ u hu, β₂, f_toff]
  by_cases hwS : w ∈ s.S
  · simp only [Finset.disjoint_left.mp hdisj hwS, ↓reduceIte]
    rw [s.local_post.depends_on _ _ htoff_S w hwS, s.post_pre_id β]
  · have hwa : w ≠ s.anc := fun h ↦ hwS (h ▸ s.anc_mem)
    rw [s.local_post.preserves_outside _ w hwS]
    dsimp only [f_toff, f_body, Function.comp_apply]
    rw [Function.update_of_ne hwa, s.local_midPost.preserves_outside _ w hwS]
    by_cases hwM : w ∈ M
    · simp only [hwM, ↓reduceIte]
      rfl
    · simp only [hwM, ↓reduceIte]
      rw [h_inner_out _ w hwM, s.local_midPre.preserves_outside _ w hwS,
        Function.update_of_ne hwa, s.local_pre.preserves_outside _ w hwS]
theorem wrap_correct [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (v : Var) (s : SymTempAndStep n) {M : Finset (Wire n)} (hdisj_SM : Disjoint s.S M)
    (inner : DynamicCircuit Var n) (c_inner : Circuit n)
    (f_inner : BitAssignment n → BitAssignment n) (rTotal : QRegister (m + 1) n)
    (hanc : s.anc = rTotal 0) (hdisj_S_rest : Disjoint s.S (rTotal.slice 1 m (by omega)).image)
    (h_inner_perm : ClassicalPerm c_inner f_inner) (h_inner_out : ∀ β w, w ∉ M → f_inner β w =
    β w) (h_inner_wp : ∀ Ψ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) =
    Ψ σ) → CQAssertion.restrictToZeroAncilla (wp inner.compile Ψ) (rTotal.slice 1 m (by omega)) =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c_inner.eval Ψ)
      (rTotal.slice 1 m (by omega))) :
    let f_wrap : BitAssignment n → BitAssignment n :=
      fun β w ↦ if w ∈ M then f_inner (s.stepFwd β) w else β w
    ClassicalPerm (s.toTempAndStep.wrapCircuit c_inner) f_wrap ∧
    (∀ β w, w ∉ M → f_wrap β w = β w) ∧ (∀ Θ : CQAssertionCompat Var (2 ^ n),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) → CQAssertion.restrictToZeroAncilla
        (wp (s.toTempAndStep.wrapDynamic v inner).compile Θ) rTotal =
        CQAssertion.restrictToZeroAncilla
          (wpQAssignCompat (s.toTempAndStep.wrapCircuit c_inner).eval Θ) rTotal) := by
  intro f_wrap
  obtain ⟨hbody_S, hf_eq⟩ := s.body_and_wrap_eq hdisj_SM f_inner h_inner_out
  have hbody_perm := s.local_midPre.perm.seq (h_inner_perm.seq s.local_midPost.perm)
  have hc_body := toffoli_conj_preserves_zero_ancilla_of_classicalPerm
    s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost) _ hbody_perm
    (fun β ↦ hbody_S β s.c₁ s.c₁_mem) (fun β ↦ hbody_S β s.c₂ s.c₂_mem)
    (fun β ↦ hbody_S β s.anc s.anc_mem)
  have htoff_perm := ClassicalPerm.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a
  refine ⟨fun β ↦ ?_, fun β w hwM ↦ by simp [f_wrap, hwM], fun Θ hΘ ↦ ?_⟩
  · have hseq := s.local_pre.perm.seq
      (htoff_perm.seq (hbody_perm.seq (htoff_perm.seq s.local_post.perm)))
    rw [show s.toTempAndStep.wrapCircuit c_inner = s.pre ;;ᶜ
        (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ
          ((s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost) ;;ᶜ
            (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.post))) by
      simp [TempAndStep.wrapCircuit], hseq β]
    exact congrArg basisKet (hf_eq β)
  · exact TempAndStep.restrictToZeroAncilla_wp_wrapDynamic_head_tail
      v s.toTempAndStep inner c_inner rTotal hanc s.anc_not_mem_pre
      (Finset.disjoint_of_subset_left s.local_pre.support_sub hdisj_S_rest)
      (Finset.disjoint_left.mp hdisj_S_rest s.c₁_mem)
      (Finset.disjoint_left.mp hdisj_S_rest s.c₂_mem)
      (Finset.disjoint_of_subset_left s.local_midPre.support_sub hdisj_S_rest)
      hc_body h_inner_wp Θ hΘ
end SymTempAndStep
section AtomicSteps
variable {n : ℕ}
def fullAdderSymStep (a b c anc : Wire n) (hab : a ≠ b) (hac : a ≠ c) (ha_anc : a ≠ anc)
    (hbc : b ≠ c) (hb_anc : b ≠ anc) (hc_anc : c ≠ anc) : SymTempAndStep n :=
  let S : Finset (Wire n) := {a, b, c, anc}
  let hc_a := LocalClassicalPerm.CNOT (S := S) c a hac.symm (by simp [S]) (by simp [S])
  let hc_b := LocalClassicalPerm.CNOT (S := S) c b hbc.symm (by simp [S]) (by simp [S])
  let hb_a := LocalClassicalPerm.CNOT (S := S) b a hab.symm (by simp [S]) (by simp [S])
  let hc_anc_p := LocalClassicalPerm.CNOT (S := S) c anc hc_anc (by simp [S]) (by simp [S])
  { pre := Circuit.CNOT c a hac.symm ;;ᶜ Circuit.CNOT c b hbc.symm
    c₁ := a, c₂ := b, anc := anc, h₁₂ := hab, h₁a := ha_anc, h₂a := hb_anc
    midPre := Circuit.CNOT c b hbc.symm ;;ᶜ (Circuit.CNOT b a hab.symm ;;ᶜ
      Circuit.CNOT c anc hc_anc)
    midPost := Circuit.CNOT c anc hc_anc ;;ᶜ (Circuit.CNOT b a hab.symm ;;ᶜ
      Circuit.CNOT c b hbc.symm)
    post := Circuit.CNOT c b hbc.symm ;;ᶜ Circuit.CNOT c a hac.symm
    S := S, f_pre := _, f_midPre := _, f_midPost := _, f_post := _
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := hc_a.seq hc_b, local_post := hc_b.seq hc_a
    local_midPre := hc_b.seq (hb_a.seq hc_anc_p)
    local_midPost := hc_anc_p.seq (hb_a.seq hc_b)
    post_pre_id := LocalClassicalPerm.comp_self_inv₂ _ _
      (LocalClassicalPerm.cnot_self_cancel c a hac.symm)
      (LocalClassicalPerm.cnot_self_cancel c b hbc.symm)
    midPost_midPre_id := LocalClassicalPerm.comp_self_inv₃ _ _ _
      (LocalClassicalPerm.cnot_self_cancel c b hbc.symm)
      (LocalClassicalPerm.cnot_self_cancel b a hab.symm)
      (LocalClassicalPerm.cnot_self_cancel c anc hc_anc)
    c₁_mem := by simp [S], c₂_mem := by simp [S], anc_mem := by simp [S]
    anc_not_mem_pre := by
      simp [Circuit.support_seq, Circuit.support_gate, QRegister.image_pair,
        ha_anc.symm, hb_anc.symm, hc_anc.symm] }
theorem fullAdderSymStep_stepFwd (a b c anc : Wire n) (hab : a ≠ b) (hac : a ≠ c)
    (ha_anc : a ≠ anc) (hbc : b ≠ c) (hb_anc : b ≠ anc) (hc_anc : c ≠ anc)
    (β : BitAssignment n) (hβ_anc : β anc = 0) : (fullAdderSymStep a b c anc hab hac ha_anc
    hbc hb_anc hc_anc).stepFwd β = Function.update (Function.update β a (β a + β b + β c)) anc
    (β c + (β a + β c) * (β b + β c)) := by
  funext w
  dsimp only [SymTempAndStep.stepFwd, fullAdderSymStep, Function.comp_apply]
  by_cases hw_anc : w = anc
  · subst hw_anc
    simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hab.symm,
      Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm,
      Function.update_of_ne ha_anc, Function.update_of_ne ha_anc.symm,
      Function.update_of_ne hb_anc, Function.update_of_ne hb_anc.symm,
      Function.update_of_ne hc_anc, hβ_anc]
    ring
  · by_cases hwa : w = a
    · subst hwa
      simp only [Function.update_self, Function.update_of_ne hw_anc, Function.update_of_ne hab,
        Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
        Function.update_of_ne hbc.symm,
        Function.update_of_ne hb_anc, Function.update_of_ne hc_anc]
      rw [LocalClassicalPerm.zmod2_add_cancel_right, add_right_comm]
    · by_cases hwb : w = b
      · subst hwb
        simp [Function.update_of_ne hw_anc, Function.update_of_ne hwa,
          Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm,
          Function.update_of_ne hc_anc]
      · simp [Function.update_of_ne hw_anc, Function.update_of_ne hwa,
          Function.update_of_ne hwb, Function.update_of_ne hc_anc]
def halfAdderSymStep (a b anc : Wire n)
    (hab : a ≠ b) (ha_anc : a ≠ anc) (hb_anc : b ≠ anc) : SymTempAndStep n :=
  let S : Finset (Wire n) := {a, b, anc}
  let hb_a := LocalClassicalPerm.CNOT (S := S) b a hab.symm (by simp [S]) (by simp [S])
  { pre := Circuit.identity, c₁ := a, c₂ := b, anc := anc
    h₁₂ := hab, h₁a := ha_anc, h₂a := hb_anc
    midPre := Circuit.CNOT b a hab.symm, midPost := Circuit.CNOT b a hab.symm
    post := Circuit.identity, S := S, f_pre := id, f_midPre := _, f_midPost := _, f_post := id
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := LocalClassicalPerm.identity S, local_post := LocalClassicalPerm.identity S
    local_midPre := hb_a, local_midPost := hb_a
    post_pre_id _ := rfl, midPost_midPre_id β := cnot_self_cancel b a hab.symm β
    c₁_mem := by simp [S], c₂_mem := by simp [S], anc_mem := by simp [S]
    anc_not_mem_pre := by simp }
theorem halfAdderSymStep_stepFwd (a b anc : Wire n) (hab : a ≠ b) (ha_anc : a ≠ anc)
    (hb_anc : b ≠ anc) (β : BitAssignment n) (hβ_anc : β anc = 0) :
    (halfAdderSymStep a b anc hab ha_anc hb_anc).stepFwd β = Function.update
    (Function.update β a (β a + β b)) anc (β a * β b) := by
  funext w
  dsimp only [halfAdderSymStep, SymTempAndStep.stepFwd, id]
  by_cases hwa : w = a
  · subst hwa
    simp [Function.update_of_ne ha_anc, Function.update_of_ne hb_anc]
  · by_cases hw_anc : w = anc
    · subst hw_anc
      simp [Function.update_of_ne ha_anc.symm, hβ_anc]
    · simp [Function.update_of_ne hwa, Function.update_of_ne hw_anc]
def andWithMidSymStep (S : Finset (Wire n)) (a b anc : Wire n) (hab : a ≠ b) (ha_anc : a ≠ anc)
    (hb_anc : b ≠ anc) (haS : a ∈ S) (hbS : b ∈ S) (hancS : anc ∈ S)
    (midExtra midExtraRev : Circuit n) (f_extra f_extraRev : BitAssignment n → BitAssignment n)
    (h_extra_cliff : midExtra.count .TOFF = 0 ∧ midExtra.count .T = 0 ∧
      midExtraRev.count .TOFF = 0 ∧ midExtraRev.count .T = 0)
    (h_local_extra : LocalClassicalPerm S midExtra f_extra)
    (h_local_extraRev : LocalClassicalPerm S midExtraRev f_extraRev)
    (h_extra_id : ∀ β, f_extraRev (f_extra β) = β) : SymTempAndStep n :=
  { pre := Circuit.identity, c₁ := a, c₂ := b, anc := anc
    h₁₂ := hab, h₁a := ha_anc, h₂a := hb_anc, midPre := midExtra, midPost := midExtraRev
    post := Circuit.identity, S := S, f_pre := id, f_midPre := f_extra, f_midPost := f_extraRev
    f_post := id
    clifford := by
      rcases h_extra_cliff with ⟨h1, h2, h3, h4⟩
      simp [TempAndStep.IsCliffordWrapper, h1, h2, h3, h4]
    local_pre := LocalClassicalPerm.identity S, local_post := LocalClassicalPerm.identity S
    local_midPre := h_local_extra, local_midPost := h_local_extraRev
    post_pre_id _ := rfl, midPost_midPre_id := h_extra_id
    c₁_mem := haS, c₂_mem := hbS, anc_mem := hancS, anc_not_mem_pre := by simp }
end AtomicSteps
theorem zmod2_full_adder_val (a b c : ZMod 2) :
    (a + b + c).val + 2 * (c + (a + c) * (b + c)).val = a.val + b.val + c.val := by
  revert a b c; decide
theorem zmod2_half_adder_val (a b : ZMod 2) :
    (a + b).val + 2 * (a * b).val = a.val + b.val := by
  revert a b; decide
section GidneyAdder
variable {Var : Type} {n : ℕ}
def gidneyRippleStep (u₀ t₀ c_in c₀ : Wire n) (hut : u₀ ≠ t₀) (huc : u₀ ≠ c₀)
    (htc : t₀ ≠ c₀) (hcin_u : c_in ≠ u₀) (hcin_t : c_in ≠ t₀)
    (hcin_c : c_in ≠ c₀) : TempAndStep n :=
  { pre := Circuit.CNOT c_in u₀ hcin_u ;;ᶜ Circuit.CNOT c_in t₀ hcin_t,
    c₁ := u₀, c₂ := t₀, anc := c₀, h₁₂ := hut, h₁a := huc, h₂a := htc,
    midPre := Circuit.CNOT c_in u₀ hcin_u ;;ᶜ Circuit.CNOT c_in c₀ hcin_c,
    midPost := Circuit.CNOT c_in c₀ hcin_c ;;ᶜ Circuit.CNOT c_in u₀ hcin_u,
    post := Circuit.CNOT c_in u₀ hcin_u ;;ᶜ Circuit.CNOT u₀ t₀ hut }
theorem gidneyRippleStep_isClifford (u₀ t₀ c_in c₀ : Wire n) (hut : u₀ ≠ t₀) (huc : u₀ ≠ c₀)
    (htc : t₀ ≠ c₀) (hcin_u : c_in ≠ u₀) (hcin_t : c_in ≠ t₀) (hcin_c : c_in ≠ c₀) :
    (gidneyRippleStep u₀ t₀ c_in c₀ hut huc htc hcin_u hcin_t hcin_c).IsCliffordWrapper := by
  simp [gidneyRippleStep, TempAndStep.IsCliffordWrapper]
def gidneyHalfStep (u₀ t₀ c₀ : Wire n) (hut : u₀ ≠ t₀) (huc : u₀ ≠ c₀)
    (htc : t₀ ≠ c₀) : TempAndStep n :=
  { pre := Circuit.identity, c₁ := u₀, c₂ := t₀, anc := c₀, h₁₂ := hut, h₁a := huc, h₂a := htc,
    midPre := Circuit.identity, midPost := Circuit.identity, post := Circuit.CNOT u₀ t₀ hut }
theorem gidneyHalfStep_isClifford (u₀ t₀ c₀ : Wire n) (hut : u₀ ≠ t₀) (huc : u₀ ≠ c₀)
    (htc : t₀ ≠ c₀) : (gidneyHalfStep u₀ t₀ c₀ hut huc htc).IsCliffordWrapper := by
  simp [gidneyHalfStep, TempAndStep.IsCliffordWrapper]
def gidneyAdderAuxCircuit : (k : ℕ) → (uWires : Fin (k + 1) → Wire n) →
    (rT : QRegister (k + 1) n) → (rC : QRegister k n) → (c_in : Wire n) →
    (hu_T : ∀ j, uWires j ∉ rT.image) → (hu_C : ∀ j, uWires j ∉ rC.image) →
    (hdisj_TC : rT.DisjointWires rC) → (hcin_u : ∀ j, c_in ≠ uWires j) →
    (hcin_T : c_in ∉ rT.image) → (hcin_C : c_in ∉ rC.image) → Circuit n
  | 0, uWires, rT, _, c_in, hu_T, _, _, _, hcin_T, _ =>
      Circuit.CNOT c_in (rT 0) (rT.ne_apply_of_not_mem_image c_in hcin_T 0) ;;ᶜ
        Circuit.CNOT (uWires 0) (rT 0) (rT.ne_apply_of_not_mem_image _ (hu_T 0) 0)
  | k + 1, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      (gidneyRippleStep (uWires 0) (rT 0) c_in (rC 0)
        (rT.ne_apply_of_not_mem_image _ (hu_T 0) 0) (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0)
        (hdisj_TC.ne 0 0) (hcin_u 0) (rT.ne_apply_of_not_mem_image _ hcin_T 0)
        (rC.ne_apply_of_not_mem_image _ hcin_C 0)).wrapCircuit
        (gidneyAdderAuxCircuit k (fun j ↦ uWires j.succ) (rT.slice 1 (k + 1) (by omega))
          (rC.slice 1 k (by omega)) (rC 0)
          (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj))
          (fun j hj ↦ hu_C j.succ (rC.image_compose_subset _ hj))
          ((hdisj_TC.compose_left _).compose_right _)
          (fun j h ↦ hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩))
          (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj))
          (QRegExt.head_not_mem_tail_image rC))
def gidneyAdderAuxDyn (v : Var) : (k : ℕ) → (uWires : Fin (k + 1) → Wire n) →
    (rT : QRegister (k + 1) n) → (rC : QRegister k n) → (c_in : Wire n) →
    (hu_T : ∀ j, uWires j ∉ rT.image) → (hu_C : ∀ j, uWires j ∉ rC.image) →
    (hdisj_TC : rT.DisjointWires rC) → (hcin_u : ∀ j, c_in ≠ uWires j) →
    (hcin_T : c_in ∉ rT.image) → (hcin_C : c_in ∉ rC.image) → DynamicCircuit Var n
  | 0, uWires, rT, _, c_in, hu_T, _, _, _, hcin_T, _ =>
      .circuit (Circuit.CNOT c_in (rT 0) (rT.ne_apply_of_not_mem_image c_in hcin_T 0) ;;ᶜ
        Circuit.CNOT (uWires 0) (rT 0) (rT.ne_apply_of_not_mem_image _ (hu_T 0) 0))
  | k + 1, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      (gidneyRippleStep (uWires 0) (rT 0) c_in (rC 0)
        (rT.ne_apply_of_not_mem_image _ (hu_T 0) 0) (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0)
        (hdisj_TC.ne 0 0) (hcin_u 0) (rT.ne_apply_of_not_mem_image _ hcin_T 0)
        (rC.ne_apply_of_not_mem_image _ hcin_C 0)).wrapDynamic v
        (gidneyAdderAuxDyn v k (fun j ↦ uWires j.succ) (rT.slice 1 (k + 1) (by omega))
          (rC.slice 1 k (by omega)) (rC 0)
          (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj))
          (fun j hj ↦ hu_C j.succ (rC.image_compose_subset _ hj))
          ((hdisj_TC.compose_left _).compose_right _)
          (fun j h ↦ hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩))
          (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj))
          (QRegExt.head_not_mem_tail_image rC))
theorem count_gidneyAdderAuxDyn_toff (v : Var) (k : ℕ) (uWires : Fin (k + 1) → Wire n)
    (rT : QRegister (k + 1) n) (rC : QRegister k n) (c_in : Wire n) (hu_T : ∀ j, uWires j ∉
    rT.image) (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j,
    c_in ≠ uWires j) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    (gidneyAdderAuxDyn v k uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count
      .TOFF = 0 := by
  induction k generalizing c_in with
  | zero => simp [gidneyAdderAuxDyn]
  | succ k ih =>
      rw [gidneyAdderAuxDyn, TempAndStep.count_wrapDynamic_toff _ _ _
        (gidneyRippleStep_isClifford ..)]
      exact ih ..
theorem count_gidneyAdderAuxDyn_t (v : Var) (k : ℕ) (uWires : Fin (k + 1) → Wire n)
    (rT : QRegister (k + 1) n) (rC : QRegister k n) (c_in : Wire n) (hu_T : ∀ j, uWires j ∉
    rT.image) (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j,
    c_in ≠ uWires j) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    (gidneyAdderAuxDyn v k uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count
      .T = 4 * k := by
  induction k generalizing c_in with
  | zero => simp [gidneyAdderAuxDyn]
  | succ k ih =>
      rw [gidneyAdderAuxDyn, TempAndStep.count_wrapDynamic_t _ _ _
        (gidneyRippleStep_isClifford ..), ih]
      omega
theorem gidneyAdderAux_correct [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (k : ℕ) (uWires : Fin (k + 1) → Wire n) (rT : QRegister (k + 1) n) (rC : QRegister k n)
    (c_in : Wire n) (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : ∃ f : BitAssignment n →
    BitAssignment n, ClassicalPerm (gidneyAdderAuxCircuit k uWires rT rC c_in hu_T hu_C
    hdisj_TC hcin_u hcin_T hcin_C) f ∧ (∀ β w, w ∉ rT.image → f β w = β w) ∧ (∀ β, (∀ i : Fin
    k, β (rC i) = 0) → regVal rT (f β) = (regVal rT β + bitsVal (fun j ↦ β (uWires j)) + (β
    c_in).val) % 2 ^ (k + 1)) ∧ (∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ (Function.update σ
    v val) = Θ σ) → CQAssertion.restrictToZeroAncilla (wp (gidneyAdderAuxDyn v k uWires rT rC
    c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).compile Θ) rC =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat (gidneyAdderAuxCircuit k uWires rT rC c_in
    hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).eval Θ) rC) := by
  induction k generalizing c_in with
  | zero =>
      have hcin_t0 : c_in ≠ rT 0 := rT.ne_apply_of_not_mem_image c_in hcin_T 0
      have hu_t0 : uWires 0 ≠ rT 0 := rT.ne_apply_of_not_mem_image (uWires 0) (hu_T 0) 0
      have hp := (ClassicalPerm.CNOT c_in (rT 0) hcin_t0).seq
        (ClassicalPerm.CNOT (uWires 0) (rT 0) hu_t0)
      refine ⟨_, hp, fun β w hw ↦ ?_, fun β _ ↦ ?_, fun Θ _ ↦ ?_⟩
      · have hwt : w ≠ rT 0 := rT.ne_apply_of_not_mem_image w hw 0
        simp [Function.comp_apply, Function.update_of_ne hwt]
      · have h0_slice (γ : BitAssignment n) : regVal (rT.slice 1 0 (by omega)) γ = 0 := by
          simp [regVal, bitsVal]
        rw [regVal_head_tail, regVal_head_tail, h0_slice, h0_slice]
        simp only [Function.comp_apply, Function.update_self, Function.update_of_ne hu_t0,
          bitsVal, mul_zero, add_zero]
        exact (by decide : ∀ a b c : ZMod 2,
          (a + c + b).val = (a.val + b.val * 1 + c.val) % 2) (β (rT 0)) (β (uWires 0)) (β c_in)
      · rw [gidneyAdderAuxDyn, gidneyAdderAuxCircuit, DynamicCircuit.compile_circuit,
          DynCircuitExt.wp_circuit_compile_compat]
  | succ k ih =>
      let rT_rest := rT.slice 1 (k + 1) (by omega)
      let rC_rest := rC.slice 1 k (by omega)
      have hut : uWires 0 ≠ rT 0 := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      have huc : uWires 0 ≠ rC 0 := rC.ne_apply_of_not_mem_image _ (hu_C 0) 0
      have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
      have hcin_t : c_in ≠ rT 0 := rT.ne_apply_of_not_mem_image _ hcin_T 0
      have hcin_c : c_in ≠ rC 0 := rC.ne_apply_of_not_mem_image _ hcin_C 0
      have hu_T_rest (j : Fin (k + 1)) : uWires j.succ ∉ rT_rest.image :=
        fun hj ↦ hu_T j.succ (rT.image_compose_subset _ hj)
      have hu_C_rest (j : Fin (k + 1)) : uWires j.succ ∉ rC_rest.image :=
        fun hj ↦ hu_C j.succ (rC.image_compose_subset _ hj)
      have hdisj_TC_rest : rT_rest.DisjointWires rC_rest :=
        (hdisj_TC.compose_left _).compose_right _
      have hc0_u (j : Fin (k + 1)) : rC 0 ≠ uWires j.succ :=
        fun h ↦ hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩)
      have hc0_T_rest : rC 0 ∉ rT_rest.image :=
        fun hj ↦ hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj)
      have hc0_C_rest : rC 0 ∉ rC_rest.image := (QRegExt.head_not_mem_tail_image rC)
      have ht0_T_rest : rT 0 ∉ rT_rest.image := (QRegExt.head_not_mem_tail_image rT)
      have hu0_T_rest : uWires 0 ∉ rT_rest.image :=
        fun hj ↦ hu_T 0 (rT.image_compose_subset _ hj)
      have hcin_T_rest : c_in ∉ rT_rest.image :=
        fun hj ↦ hcin_T (rT.image_compose_subset _ hj)
      obtain ⟨f_rest, hperm_rest, hout_rest, hval_rest, hwp_rest⟩ :=
        ih (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
          hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
      let s_step := gidneyRippleStep (uWires 0) (rT 0) c_in (rC 0)
        hut huc htc (hcin_u 0) hcin_t hcin_c
      let c_inner := gidneyAdderAuxCircuit k (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
        hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
      let d_inner := gidneyAdderAuxDyn v k (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
        hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
      let S_pre : Finset (Wire n) := {c_in, uWires 0, rT 0}
      let S_mid : Finset (Wire n) := {c_in, uWires 0, rC 0}
      let fc_u := fun γ : BitAssignment n ↦ Function.update γ (uWires 0) (γ (uWires 0) + γ c_in)
      let fc_t := fun γ : BitAssignment n ↦ Function.update γ (rT 0) (γ (rT 0) + γ c_in)
      let fc_c := fun γ : BitAssignment n ↦ Function.update γ (rC 0) (γ (rC 0) + γ c_in)
      let fu_t := fun γ : BitAssignment n ↦ Function.update γ (rT 0) (γ (rT 0) + γ (uWires 0))
      let f_toff := fun γ : BitAssignment n ↦
        Function.update γ (rC 0) (γ (rC 0) + γ (uWires 0) * γ (rT 0))
      let f_pre := fc_t ∘ fc_u
      let f_midPre := fc_c ∘ fc_u
      let f_midPost := fc_u ∘ fc_c
      let f_post := fu_t ∘ fc_u
      let f_body := f_midPost ∘ f_rest ∘ f_midPre
      let f_total := f_post ∘ f_toff ∘ f_body ∘ f_toff ∘ f_pre
      have hlp_pre : LocalClassicalPerm S_pre s_step.pre f_pre :=
        (LocalClassicalPerm.CNOT c_in (uWires 0) (hcin_u 0) (by simp [S_pre])
          (by simp [S_pre])).seq
          (LocalClassicalPerm.CNOT c_in (rT 0) hcin_t (by simp [S_pre]) (by simp [S_pre]))
      have hlp_midPre : LocalClassicalPerm S_mid s_step.midPre f_midPre :=
        (LocalClassicalPerm.CNOT c_in (uWires 0) (hcin_u 0) (by simp [S_mid])
          (by simp [S_mid])).seq
          (LocalClassicalPerm.CNOT c_in (rC 0) hcin_c (by simp [S_mid]) (by simp [S_mid]))
      have hlp_midPost : LocalClassicalPerm S_mid s_step.midPost f_midPost :=
        (LocalClassicalPerm.CNOT c_in (rC 0) hcin_c (by simp [S_mid]) (by simp [S_mid])).seq
          (LocalClassicalPerm.CNOT c_in (uWires 0) (hcin_u 0) (by simp [S_mid]) (by simp [S_mid]))
      have hpost_perm : ClassicalPerm s_step.post f_post :=
        (ClassicalPerm.CNOT c_in (uWires 0) (hcin_u 0)).seq
          (ClassicalPerm.CNOT (uWires 0) (rT 0) hut)
      have hmid_inv (γ : BitAssignment n) : f_midPost (f_midPre γ) = γ :=
        comp_self_inv₂ fc_u fc_c (cnot_self_cancel c_in (uWires 0) (hcin_u 0))
          (cnot_self_cancel c_in (rC 0) hcin_c) γ
      have hS_mid_T : Disjoint S_mid rT_rest.image := by
        simp [S_mid, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
          hcin_T_rest, hu0_T_rest, hc0_T_rest]
      have hbody_out (γ : BitAssignment n) {w : Wire n} (hw : w ∉ rT_rest.image) :
          f_body γ w = γ w := by
        dsimp only [f_body, Function.comp_apply]
        by_cases hwS : w ∈ S_mid
        · rw [hlp_midPost.depends_on _ _
            (fun u hu ↦ hout_rest _ u (Finset.disjoint_left.mp hS_mid_T hu)) w hwS, hmid_inv]
        · rw [hlp_midPost.preserves_outside _ w hwS, hout_rest _ w hw,
            hlp_midPre.preserves_outside _ w hwS]
      have htb_out (γ : BitAssignment n) {w : Wire n} (hw : w ∉ rT_rest.image) :
          f_toff (f_body (f_toff γ)) w = γ w := by
        let γ₁ := f_toff γ
        change f_toff (f_body γ₁) w = γ w
        by_cases hwc : w = rC 0
        · subst hwc
          simp [f_toff, γ₁, hbody_out γ₁ hc0_T_rest, hbody_out γ₁ hu0_T_rest,
            hbody_out γ₁ ht0_T_rest, Function.update_of_ne huc, Function.update_of_ne htc]
        · simp [f_toff, γ₁, Function.update_of_ne hwc, hbody_out γ₁ hw]
      have hbody_perm := hlp_midPre.perm.seq (hperm_rest.seq hlp_midPost.perm)
      have hc_body := toffoli_conj_preserves_zero_ancilla_of_classicalPerm
        (uWires 0) (rT 0) (rC 0) hut huc htc (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost)
        f_body hbody_perm (fun β ↦ hbody_out β hu0_T_rest) (fun β ↦ hbody_out β ht0_T_rest)
        (fun β ↦ hbody_out β hc0_T_rest)
      have htoff_p := ClassicalPerm.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc
      have htotal_perm : ClassicalPerm (gidneyAdderAuxCircuit (k + 1) uWires rT rC c_in hu_T
          hu_C hdisj_TC hcin_u hcin_T hcin_C) f_total := fun β ↦ by
        rw [gidneyAdderAuxCircuit, show s_step.wrapCircuit c_inner =
            s_step.pre ;;ᶜ (Circuit.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc ;;ᶜ
              ((s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost) ;;ᶜ
                (Circuit.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc ;;ᶜ s_step.post))) by
          simp [s_step, gidneyRippleStep, TempAndStep.wrapCircuit]]
        exact (hlp_pre.perm.seq (htoff_p.seq (hbody_perm.seq (htoff_p.seq hpost_perm)))) β
      refine ⟨f_total, htotal_perm, fun β w hw ↦ ?_, fun β hβ_C ↦ ?_, fun Θ hΘ ↦ ?_⟩
      · have hwt0 : w ≠ rT 0 := rT.ne_apply_of_not_mem_image w hw 0
        have hw_rest : w ∉ rT_rest.image := fun hj ↦ hw (rT.image_compose_subset _ hj)
        let β₁ := f_pre β
        change fu_t (fc_u (f_toff (f_body (f_toff β₁)))) w = β w
        by_cases hwu : w = uWires 0
        · subst hwu
          dsimp only [fu_t, fc_u]
          rw [Function.update_of_ne hut, Function.update_self, htb_out β₁ hu0_T_rest,
            htb_out β₁ hcin_T_rest]
          dsimp only [β₁, f_pre, fc_t, fc_u, Function.comp_apply]
          rw [Function.update_of_ne hut, Function.update_self, Function.update_of_ne hcin_t,
            Function.update_of_ne (hcin_u 0), zmod2_add_cancel_right]
        · dsimp only [fu_t, fc_u]
          rw [Function.update_of_ne hwt0, Function.update_of_ne hwu, htb_out β₁ hw_rest]
          dsimp only [β₁, f_pre, fc_t, fc_u, Function.comp_apply]
          rw [Function.update_of_ne hwt0, Function.update_of_ne hwu]
      · let β_mid := f_midPre (f_toff (f_pre β))
        have hβ_mid_c0 : β_mid (rC 0) =
            β c_in + (β (uWires 0) + β c_in) * (β (rT 0) + β c_in) := by
          simp only [β_mid, f_midPre, f_toff, f_pre, fc_c, fc_t, fc_u, Function.comp_apply,
            Function.update_self, Function.update_of_ne huc.symm, Function.update_of_ne htc.symm,
            Function.update_of_ne huc, Function.update_of_ne hut, Function.update_of_ne hut.symm,
            Function.update_of_ne (hcin_u 0), Function.update_of_ne hcin_t,
            Function.update_of_ne hcin_c, hβ_C 0]
          ring
        have hβ_mid_out {w : Wire n} (hwt : w ≠ rT 0) (hwc : w ≠ rC 0) : β_mid w = β w := by
          dsimp only [β_mid, f_midPre, f_toff, f_pre, fc_c, fc_t, fc_u, Function.comp_apply]
          by_cases hwu : w = uWires 0
          · subst hwu
            simp [Function.update_of_ne huc, Function.update_of_ne hut,
              Function.update_of_ne hcin_c, Function.update_of_ne hcin_t,
              Function.update_of_ne (hcin_u 0)]
          · simp [Function.update_of_ne hwc, Function.update_of_ne hwt, Function.update_of_ne hwu]
        have htotal_t0 : f_total β (rT 0) = β (uWires 0) + β (rT 0) + β c_in := by
          let β₁ := f_pre β
          change fu_t (fc_u (f_toff (f_body (f_toff β₁)))) (rT 0) = _
          dsimp only [fu_t, fc_u]
          rw [Function.update_self, Function.update_of_ne hut.symm, Function.update_self,
            htb_out β₁ ht0_T_rest, htb_out β₁ hu0_T_rest, htb_out β₁ hcin_T_rest]
          dsimp only [β₁, f_pre, fc_t, fc_u, Function.comp_apply]
          rw [Function.update_self, Function.update_of_ne hut.symm,
            Function.update_of_ne (hcin_u 0), Function.update_of_ne hut, Function.update_self,
            Function.update_of_ne hcin_t, Function.update_of_ne (hcin_u 0)]
          exact (by decide : ∀ u t c : ZMod 2, (t + c) + ((u + c) + c) = u + t + c)
            (β (uWires 0)) (β (rT 0)) (β c_in)
        have htotal_T_rest (i : Fin (k + 1)) :
            f_total β (rT_rest i) = f_rest β_mid (rT_rest i) := by
          have hi := (rT_rest.mem_image _).mpr ⟨i, rfl⟩
          simp [f_total, f_post, fu_t, fc_u, f_toff, f_body, f_midPost, fc_c, β_mid,
            Function.comp_apply,
            Function.update_of_ne (fun h : rT_rest i = rT 0 ↦ ht0_T_rest (h ▸ hi)),
            Function.update_of_ne (fun h : rT_rest i = uWires 0 ↦ hu0_T_rest (h ▸ hi)),
            Function.update_of_ne (fun h : rT_rest i = rC 0 ↦ hc0_T_rest (h ▸ hi))]
        have hβ_mid_T_rest (i : Fin (k + 1)) : β_mid (rT_rest i) = β (rT_rest i) := by
          have hi := (rT_rest.mem_image _).mpr ⟨i, rfl⟩
          exact hβ_mid_out (fun h ↦ ht0_T_rest (h ▸ hi)) (fun h ↦ hc0_T_rest (h ▸ hi))
        have hβ_mid_C_rest (i : Fin k) : β_mid (rC_rest i) = 0 := by
          have hi := (rC_rest.mem_image _).mpr ⟨i, rfl⟩
          rw [hβ_mid_out
            (fun h ↦ hdisj_TC.apply_not_mem_right 0 (rC.image_compose_subset _ (h ▸ hi)))
            (fun h ↦ hc0_C_rest (h ▸ hi))]
          exact hβ_C ⟨1 + i.val, by omega⟩
        have hubits : bitsVal (fun j : Fin (k + 1) ↦ β_mid (uWires j.succ)) =
            bitsVal (fun j : Fin (k + 1) ↦ β (uWires j.succ)) :=
          congrArg bitsVal (funext fun j ↦ hβ_mid_out
            (rT.ne_apply_of_not_mem_image _ (hu_T j.succ) 0)
            (rC.ne_apply_of_not_mem_image _ (hu_C j.succ) 0))
        rw [regVal_head_tail rT (f_total β), regVal_congr rT_rest htotal_T_rest,
          hval_rest β_mid hβ_mid_C_rest, regVal_congr rT_rest hβ_mid_T_rest,
          htotal_t0, hβ_mid_c0, hubits, regVal_head_tail rT β,
          bitsVal_succ (fun j : Fin (k + 2) ↦ β (uWires j)),
          add_two_mul_mod _ _ (2 ^ (k + 1)) (ZMod.val_lt _), ← pow_succ']
        congr 1
        linarith [zmod2_full_adder_val (β (uWires 0)) (β (rT 0)) (β c_in)]
      · rw [gidneyAdderAuxDyn, gidneyAdderAuxCircuit]
        have hcin_Cr : c_in ∉ rC_rest.image := fun hj ↦ hcin_C (rC.image_compose_subset _ hj)
        have hc1_rest : uWires 0 ∉ rC_rest.image := fun hj ↦ hu_C 0 (rC.image_compose_subset _ hj)
        have hc2_rest : rT 0 ∉ rC_rest.image :=
          fun hj ↦ hdisj_TC.apply_not_mem_right 0 (rC.image_compose_subset _ hj)
        have hpre_anc : rC 0 ∉ s_step.pre.support := fun h ↦ by
          simpa [S_pre, hcin_c.symm, huc.symm, htc.symm] using hlp_pre.support_sub h
        have hpre_rest : Disjoint s_step.pre.support rC_rest.image :=
          Finset.disjoint_of_subset_left hlp_pre.support_sub (by
            simp [S_pre, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
              hcin_Cr, hc1_rest, hc2_rest])
        have hmidPre_rest : Disjoint s_step.midPre.support rC_rest.image :=
          Finset.disjoint_of_subset_left hlp_midPre.support_sub (by
            simp [S_mid, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
              hcin_Cr, hc1_rest, hc0_C_rest])
        exact TempAndStep.restrictToZeroAncilla_wp_wrapDynamic_head_tail
          v s_step d_inner c_inner rC rfl hpre_anc hpre_rest hc1_rest hc2_rest hmidPre_rest
          hc_body hwp_rest Θ hΘ
def gidneyAdderCircuit (k : ℕ) (uWires : Fin (k + 2) → Wire n) (rT : QRegister (k + 2) n)
    (rC : QRegister (k + 1) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) : Circuit n :=
  (gidneyHalfStep (uWires 0) (rT 0) (rC 0) (rT.ne_apply_of_not_mem_image _ (hu_T 0) 0)
    (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0) (hdisj_TC.ne 0 0)).wrapCircuit
    (gidneyAdderAuxCircuit k (fun j ↦ uWires j.succ) (rT.slice 1 (k + 1) (by omega))
      (rC.slice 1 k (by omega)) (rC 0)
      (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj))
      (fun j hj ↦ hu_C j.succ (rC.image_compose_subset _ hj))
      ((hdisj_TC.compose_left _).compose_right _)
      (fun j h ↦ hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩))
      (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj))
      (QRegExt.head_not_mem_tail_image rC))
def gidneyAdderDyn (v : Var) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 1) n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) : DynamicCircuit Var n :=
  (gidneyHalfStep (uWires 0) (rT 0) (rC 0) (rT.ne_apply_of_not_mem_image _ (hu_T 0) 0)
    (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0) (hdisj_TC.ne 0 0)).wrapDynamic v
    (gidneyAdderAuxDyn v k (fun j ↦ uWires j.succ) (rT.slice 1 (k + 1) (by omega))
      (rC.slice 1 k (by omega)) (rC 0)
      (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj))
      (fun j hj ↦ hu_C j.succ (rC.image_compose_subset _ hj))
      ((hdisj_TC.compose_left _).compose_right _)
      (fun j h ↦ hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩))
      (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj))
      (QRegExt.head_not_mem_tail_image rC))
theorem count_gidneyAdderDyn_toff (v : Var) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 1) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) :
    (gidneyAdderDyn v k uWires rT rC hu_T hu_C hdisj_TC).count .TOFF = 0 := by
  rw [gidneyAdderDyn, TempAndStep.count_wrapDynamic_toff _ _ _ (gidneyHalfStep_isClifford ..)]
  exact count_gidneyAdderAuxDyn_toff ..
theorem count_gidneyAdderDyn_t (v : Var) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 1) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) :
    (gidneyAdderDyn v k uWires rT rC hu_T hu_C hdisj_TC).count .T = 4 * (k + 1) := by
  rw [gidneyAdderDyn, TempAndStep.count_wrapDynamic_t _ _ _ (gidneyHalfStep_isClifford ..),
    count_gidneyAdderAuxDyn_t]
  omega
theorem gidneyAdder_correct [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var) (k : ℕ)
    (uWires : Fin (k + 2) → Wire n) (rT : QRegister (k + 2) n) (rC : QRegister (k + 1) n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) : ∃ f : BitAssignment n → BitAssignment n, ClassicalPerm
    (gidneyAdderCircuit k uWires rT rC hu_T hu_C hdisj_TC) f ∧
    (∀ β w, w ∉ rT.image → f β w = β w) ∧ (∀ β, (∀ i : Fin (k + 1), β (rC i) = 0) → regVal rT
    (f β) = (regVal rT β + bitsVal (fun j ↦ β (uWires j))) % 2 ^ (k + 2)) ∧ (∀ Θ : CQAssertionCompat
    Var (2 ^ n), (∀ σ val, Θ (Function.update σ v val) = Θ σ) → CQAssertion.restrictToZeroAncilla
    (wp (gidneyAdderDyn v k uWires rT rC hu_T hu_C hdisj_TC).compile Θ) rC =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat (gidneyAdderCircuit k uWires rT rC hu_T
    hu_C hdisj_TC).eval Θ) rC) := by
  let rT_rest := rT.slice 1 (k + 1) (by omega)
  let rC_rest := rC.slice 1 k (by omega)
  have hut : uWires 0 ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0
  have huc : uWires 0 ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ (hu_C 0) 0
  have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
  have hc0_T_rest : rC 0 ∉ rT_rest.image :=
    fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj)
  have hc0_C_rest : rC 0 ∉ rC_rest.image := QRegExt.head_not_mem_tail_image rC
  have ht0_T_rest : rT 0 ∉ rT_rest.image := QRegExt.head_not_mem_tail_image rT
  have hu0_T_rest : uWires 0 ∉ rT_rest.image :=
    fun hj ↦ hu_T 0 (QRegister.image_compose_subset rT _ hj)
  have hu_T_rest : ∀ j : Fin (k + 1), uWires j.succ ∉ rT_rest.image :=
    fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj)
  have hu_C_rest : ∀ j : Fin (k + 1), uWires j.succ ∉ rC_rest.image :=
    fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj)
  have hdisj_TC_rest : rT_rest.DisjointWires rC_rest :=
    (hdisj_TC.compose_left _).compose_right _
  have hc0_u : ∀ j : Fin (k + 1), rC 0 ≠ uWires j.succ :=
    fun j h ↦ hu_C j.succ (QRegister.mem_image rC (uWires j.succ) |>.mpr ⟨0, h⟩)
  obtain ⟨f_rest, hperm_rest, hout_rest, hval_rest, hwp_rest⟩ :=
    gidneyAdderAux_correct v k (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
      hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
  let s_step := gidneyHalfStep (uWires 0) (rT 0) (rC 0) hut huc htc
  let c_inner := gidneyAdderAuxCircuit k (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
    hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
  let d_inner := gidneyAdderAuxDyn v k (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
    hu_T_rest hu_C_rest hdisj_TC_rest hc0_u hc0_T_rest hc0_C_rest
  have hbody_perm : ClassicalPerm (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost) f_rest :=
    ClassicalPerm.identity.seq (hperm_rest.seq ClassicalPerm.identity)
  have hc_body := toffoli_conj_preserves_zero_ancilla_of_classicalPerm
    (uWires 0) (rT 0) (rC 0) hut huc htc (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost)
    f_rest hbody_perm (fun β ↦ hout_rest β (uWires 0) hu0_T_rest)
    (fun β ↦ hout_rest β (rT 0) ht0_T_rest)
    (fun β ↦ hout_rest β (rC 0) hc0_T_rest)
  let f_toff := fun β : BitAssignment n ↦
    Function.update β (rC 0) (β (rC 0) + β (uWires 0) * β (rT 0))
  let f_post := fun β : BitAssignment n ↦ Function.update β (rT 0) (β (rT 0) + β (uWires 0))
  let f_total := f_post ∘ f_toff ∘ f_rest ∘ f_toff
  have htoff_p := ClassicalPerm.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc
  have htotal_perm : ClassicalPerm (gidneyAdderCircuit k uWires rT rC hu_T hu_C hdisj_TC)
      f_total := fun β ↦ by
    rw [gidneyAdderCircuit, show s_step.wrapCircuit c_inner =
        s_step.pre ;;ᶜ (Circuit.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc ;;ᶜ
          ((s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost) ;;ᶜ
            (Circuit.TOFF (uWires 0) (rT 0) (rC 0) hut huc htc ;;ᶜ s_step.post))) by
      simp [s_step, gidneyHalfStep, TempAndStep.wrapCircuit]]
    exact (ClassicalPerm.identity.seq
      (htoff_p.seq (hbody_perm.seq (htoff_p.seq (ClassicalPerm.CNOT (uWires 0) (rT 0) hut))))) β
  refine ⟨f_total, htotal_perm, fun β w hw ↦ ?_, fun β hβ_C ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · have hwt0 : w ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT w hw 0
    have hw_rest : w ∉ rT_rest.image := fun hj ↦ hw (QRegister.image_compose_subset rT _ hj)
    dsimp only [f_total, f_post, f_toff, Function.comp_apply]
    by_cases hwc : w = rC 0
    · subst hwc
      simp [Function.update_of_ne htc.symm, Function.update_of_ne huc,
        Function.update_of_ne htc, hout_rest _ (rC 0) hc0_T_rest,
        hout_rest _ (uWires 0) hu0_T_rest, hout_rest _ (rT 0) ht0_T_rest]
    · simp [Function.update_of_ne hwt0, Function.update_of_ne hwc, hout_rest _ w hw_rest]
  · let β_mid := f_toff β
    have htotal_T : ∀ i : Fin (k + 1), f_total β (rT_rest i) = f_rest β_mid (rT_rest i) :=
      fun i ↦ by
        have hi := (rT_rest.mem_image _).mpr ⟨i, rfl⟩
        dsimp only [f_total, f_post, f_toff, Function.comp_apply, β_mid]
        simp [Function.update_of_ne (show rT_rest i ≠ rT 0 from fun h ↦ ht0_T_rest (h ▸ hi)),
          Function.update_of_ne (show rT_rest i ≠ rC 0 from fun h ↦ hc0_T_rest (h ▸ hi))]
    have hmid_T : ∀ i : Fin (k + 1), β_mid (rT_rest i) = β (rT_rest i) := fun i ↦
      Function.update_of_ne
        (fun h : rT_rest i = rC 0 ↦ hc0_T_rest (h ▸ (rT_rest.mem_image _).mpr ⟨i, rfl⟩)) _ _
    rw [regVal_head_tail rT (f_total β), regVal_congr rT_rest htotal_T,
      hval_rest β_mid fun i ↦ by
        rw [show β_mid (rC_rest i) = β (rC_rest i) from Function.update_of_ne
          (fun h : rC_rest i = rC 0 ↦ hc0_C_rest (h ▸ (rC_rest.mem_image _).mpr ⟨i, rfl⟩)) _ _]
        exact hβ_C ⟨1 + i.val, by omega⟩,
      regVal_congr rT_rest hmid_T,
      show f_total β (rT 0) = β (uWires 0) + β (rT 0) by
        simp [f_total, f_post, f_toff, Function.comp_apply, Function.update_of_ne htc,
          Function.update_of_ne huc, hout_rest _ (rT 0) ht0_T_rest,
          hout_rest _ (uWires 0) hu0_T_rest, add_comm],
      show β_mid (rC 0) = β (uWires 0) * β (rT 0) by simp [β_mid, f_toff, hβ_C 0],
      show bitsVal (fun j : Fin (k + 1) ↦ β_mid (uWires j.succ)) =
          bitsVal (fun j : Fin (k + 1) ↦ β (uWires j.succ)) from
        congrArg bitsVal (funext fun j ↦
          Function.update_of_ne (rC.ne_apply_of_not_mem_image _ (hu_C j.succ) 0) _ _),
      regVal_head_tail rT β, bitsVal_succ (fun j : Fin (k + 2) ↦ β (uWires j)),
      add_two_mul_mod _ _ (2 ^ (k + 1)) (ZMod.val_lt _), ← pow_succ']
    congr 1
    linarith [zmod2_half_adder_val (β (uWires 0)) (β (rT 0))]
  · rw [gidneyAdderDyn, gidneyAdderCircuit]
    exact TempAndStep.restrictToZeroAncilla_wp_wrapDynamic_head_tail
      v s_step d_inner c_inner rC rfl (by simp [s_step, gidneyHalfStep])
      (by simp [s_step, gidneyHalfStep])
      (fun hj ↦ hu_C 0 (rC.image_compose_subset _ hj))
      (fun hj ↦ hdisj_TC.apply_not_mem_right 0 (rC.image_compose_subset _ hj))
      (by simp [s_step, gidneyHalfStep]) hc_body hwp_rest Θ hΘ
end GidneyAdder
end LocalClassicalPerm
end
end ModGidneyTempAndAdder

section ModCanonRank7Circuit
@[expose] public section
set_option maxRecDepth 8192
namespace CanonRank7Circuit
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
open OctahedralOrbit Dyadic128CoulombMath
variable {Var : Type} {n : ℕ}
theorem ket_eq_basisKet (β : BitAssignment n) : ket β = basisKet β := rfl
theorem slice_image_subset {m a l : ℕ} (r : QRegister m n) (h : a + l ≤ m) :
    (r.slice a l h).image ⊆ r.image := r.image_compose_subset _
theorem bitsVal_add_one {k : ℕ} (γ : BitAssignment k) :
    bitsVal (fun i ↦ γ i + 1) + bitsVal γ = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ m ih =>
      have hhead := (by decide : ∀ b : ZMod 2, (b + 1).val + b.val = 1) (γ 0)
      have ih_m := ih (fun i ↦ γ i.succ)
      have hpow := Nat.one_le_two_pow (n := m)
      rw [bitsVal_succ (fun i ↦ γ i + 1), bitsVal_succ γ, pow_succ]
      omega
def copyXorRegCircuit : {k : ℕ} → (rSrc rDst : QRegister k n) → rSrc.DisjointWires rDst → Circuit n
  | 0, _, _, _ => .identity
  | m + 1, rSrc, rDst, hSD =>
      copyXorRegCircuit (regInit rSrc) (regInit rDst) (disjoint_regInit_both hSD) ;;ᶜ
      Circuit.CNOT (rSrc (Fin.last m)) (rDst (Fin.last m)) (hSD.ne (Fin.last m) (Fin.last m))
@[simp] theorem count_copyXorRegCircuit_toff {k : ℕ} (rSrc rDst : QRegister k n)
    (hSD : rSrc.DisjointWires rDst) :
    (copyXorRegCircuit rSrc rDst hSD).count PrimitiveGate.TOFF = 0 := by
  induction k with
  | zero => rfl
  | succ _ ih =>
      rw [copyXorRegCircuit, Circuit.count_seq, ih]
      simp [Circuit.CNOT]
@[simp] theorem count_copyXorRegCircuit_t {k : ℕ} (rSrc rDst : QRegister k n)
    (hSD : rSrc.DisjointWires rDst) :
    (copyXorRegCircuit rSrc rDst hSD).count PrimitiveGate.T = 0 := by
  induction k with
  | zero => rfl
  | succ _ ih =>
      rw [copyXorRegCircuit, Circuit.count_seq, ih]
      simp [Circuit.CNOT]
theorem copyXorRegCircuit_classicalPerm {k : ℕ} (rSrc rDst : QRegister k n)
    (hSD : rSrc.DisjointWires rDst) : ClassicalPerm (copyXorRegCircuit rSrc rDst hSD)
    (fun β ↦ writeReg β rDst (fun i ↦ β (rDst i) + β (rSrc i))) := fun β ↦ by
  induction k with
  | zero =>
      simp only [copyXorRegCircuit, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      rw [← ket_eq_basisKet, writeReg_zero]
  | succ m ih =>
      dsimp only [copyXorRegCircuit]
      rw [← ket_eq_basisKet, eval_seq_mulVec]
      change _ = ket _
      rw [ket_eq_basisKet, ih (regInit rSrc) (regInit rDst) (disjoint_regInit_both hSD),
        ← ket_eq_basisKet, ket_CNOT]
      have hsrc := writeReg_apply_of_not_mem β (regInit rDst)
        (fun i ↦ β ((regInit rDst) i) + β ((regInit rSrc) i)) (rSrc (Fin.last m))
        (fun ⟨i, hi⟩ ↦ hSD.ne (Fin.last m) i.castSucc hi.symm)
      have hdst := writeReg_apply_of_not_mem β (regInit rDst)
        (fun i ↦ β ((regInit rDst) i) + β ((regInit rSrc) i)) (rDst (Fin.last m))
        (last_not_mem_range_regInit rDst)
      simp only [regInit_apply] at hsrc hdst ⊢
      rw [hsrc, hdst, ← writeReg_castSucc β rDst (fun j ↦ β (rDst j) + β (rSrc j))]
private theorem count_inv (c : Circuit n) :
    c.inverse.count .TOFF = c.count .TOFF ∧ c.inverse.count .T = c.count .T := by
  induction c with
  | identity => exact ⟨rfl, rfl⟩
  | gate g r =>
      cases g
      all_goals simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
  | seq c₁ c₂ ih₁ ih₂ =>
      exact ⟨by simp [Circuit.inverse, ih₁.1, ih₂.1, add_comm],
        by simp [Circuit.inverse, ih₁.2, ih₂.2, add_comm]⟩
@[simp] theorem count_inverse_toff (c : Circuit n) :
    c.inverse.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := (count_inv c).1
@[simp] theorem count_inverse_t (c : Circuit n) :
    c.inverse.count PrimitiveGate.T = c.count PrimitiveGate.T := (count_inv c).2
def fineCoordOfReg21 (rD21 : QRegister 21 n) (β : BitAssignment n) : FineCoord128 :=
  fun w ↦ ⟨regVal (rD21.slice (7 * w.val) 7 (by omega)) β,
    regVal_lt_two_pow (rD21.slice (7 * w.val) 7 (by omega)) β⟩
end CanonRank7Circuit
end
end ModCanonRank7Circuit

section ModDyadicQft64Circuit
@[expose] public section
namespace DyadicQft64
open Real Operator Matrix QProg HermitianMat LocalClassicalPerm
open KaratsubaQft64Matrix
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
local infixr:67 " ;;ᵈ " => DynamicCircuit.seq
section PhasePermEngine
variable {Var : Type} {n : ℕ}
noncomputable def dyadicTurn (B : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (k : ℂ) / (2 ^ B : ℂ))
@[simp] theorem dyadicTurn_zero (B : ℕ) : dyadicTurn B 0 = 1 := by simp [dyadicTurn]
theorem dyadicTurn_add (B : ℕ) (a b : ℤ) :
    dyadicTurn B a * dyadicTurn B b = dyadicTurn B (a + b) := by
  unfold dyadicTurn
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem star_dyadicTurn (B : ℕ) (k : ℤ) : star (dyadicTurn B k) = dyadicTurn B (-k) := by
  unfold dyadicTurn
  rw [RCLike.star_def, ← Complex.exp_conj]
  congr 1
  simp only [div_eq_mul_inv, map_mul, map_inv₀, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, map_intCast, Int.cast_neg]
  ring
theorem star_dyadicTurn_mul_self (B : ℕ) (k : ℤ) :
    star (dyadicTurn B k) * dyadicTurn B k = 1 := by
  rw [star_dyadicTurn, dyadicTurn_add, neg_add_cancel, dyadicTurn_zero]
theorem dyadicTurn_eq_omega128 (k : ℤ) : dyadicTurn 7 k = omega128 k := by
  unfold dyadicTurn
  rw [omega128_def]
  congr 1
  ring
theorem dyadicTurn_add_period (B : ℕ) (a m : ℤ) :
    dyadicTurn B (a + m * (2 ^ B : ℤ)) = dyadicTurn B a := by
  unfold dyadicTurn
  have hne : ((2 : ℂ) ^ B) ≠ 0 := pow_ne_zero B (by norm_num)
  rw [show 2 * π * Complex.I * ((a + m * (2 ^ B : ℤ) : ℤ) : ℂ) / (2 ^ B : ℂ) =
      2 * π * Complex.I * (a : ℂ) / (2 ^ B : ℂ) + (m : ℂ) * (2 * π * Complex.I) by
    push_cast
    field_simp [hne], Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem dyadicTurn_eq_of_emod_eq (B : ℕ) {a b : ℤ} (h : a % (2 ^ B : ℤ) = b % (2 ^ B : ℤ)) :
    dyadicTurn B a = dyadicTurn B b := by
  calc dyadicTurn B a
      = dyadicTurn B (a % (2 ^ B : ℤ) + (a / (2 ^ B : ℤ)) * (2 ^ B : ℤ)) :=
          congrArg (dyadicTurn B) (by linarith [Int.emod_add_mul_ediv a (2 ^ B : ℤ)])
    _ = dyadicTurn B (b % (2 ^ B : ℤ)) := by rw [dyadicTurn_add_period, h]
    _ = dyadicTurn B (b % (2 ^ B : ℤ) + (b / (2 ^ B : ℤ)) * (2 ^ B : ℤ)) :=
          (dyadicTurn_add_period B _ _).symm
    _ = dyadicTurn B b :=
          congrArg (dyadicTurn B) (by linarith [Int.emod_add_mul_ediv b (2 ^ B : ℤ)])
structure PhasePerm (M : Finset (Wire n)) (c : Circuit n)
    (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n) : Prop where
  evolve : ∀ β : BitAssignment n, c.eval.1.mulVec (basisKet β) = φ β • basisKet (f β)
  outside : ∀ β w, w ∉ M → f β w = β w
namespace PhasePerm
alias eval_ket := evolve
alias preserves_outside := outside
theorem identity (M : Finset (Wire n)) :
    PhasePerm M (Circuit.identity : Circuit n) (fun _ ↦ 1) id :=
  ⟨fun β ↦ by rw [ClassicalPerm.identity β, one_smul], fun _ _ _ ↦ rfl⟩
theorem mono {M₁ M₂ : Finset (Wire n)} {c : Circuit n} {φ : BitAssignment n → ℂ}
    {f : BitAssignment n → BitAssignment n} (h : PhasePerm M₁ c φ f) (hsub : M₁ ⊆ M₂) :
    PhasePerm M₂ c φ f := ⟨h.evolve, fun β w hw ↦ h.outside β w (fun hm ↦ hw (hsub hm))⟩
theorem of_classicalPerm {M : Finset (Wire n)} {c : Circuit n}
    {f : BitAssignment n → BitAssignment n} (hp : ClassicalPerm c f)
    (hout : ∀ β w, w ∉ M → f β w = β w) : PhasePerm M c (fun _ ↦ 1) f :=
  ⟨fun β ↦ by simp [hp β], hout⟩
theorem seq {M : Finset (Wire n)} {c₁ c₂ : Circuit n} {φ₁ φ₂ : BitAssignment n → ℂ}
    {f₁ f₂ : BitAssignment n → BitAssignment n} (h₁ : PhasePerm M c₁ φ₁ f₁)
    (h₂ : PhasePerm M c₂ φ₂ f₂) :
    PhasePerm M (c₁ ;;ᶜ c₂) (fun β ↦ φ₁ β * φ₂ (f₁ β)) (f₂ ∘ f₁) :=
  ⟨fun β ↦ by
    rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h₁.evolve β,
      Matrix.mulVec_smul, Function.comp_apply, h₂.evolve (f₁ β), smul_smul],
   fun β w hw ↦ by rw [Function.comp_apply, h₂.outside (f₁ β) w hw, h₁.outside β w hw]⟩
theorem congr_phase {M : Finset (Wire n)} {c : Circuit n} {φ₁ φ₂ : BitAssignment n → ℂ}
    {f : BitAssignment n → BitAssignment n} (h : PhasePerm M c φ₁ f) (hφ : ∀ β, φ₁ β = φ₂ β) :
    PhasePerm M c φ₂ f := ⟨fun β ↦ hφ β ▸ h.evolve β, h.outside⟩
private theorem phasePerm_diag1 (g : PrimitiveGate 1) (q : Wire n) (k : ℤ)
    (hg00 : g.eval.1 0 0 = 1) (hg10 : g.eval.1 1 0 = 0)
    (hg01 : g.eval.1 0 1 = 0) (hg11 : g.eval.1 1 1 = dyadicTurn 7 k) :
    PhasePerm (∅ : Finset (Wire n)) (Circuit.gate g (QRegister.singleton q))
      (fun β ↦ dyadicTurn 7 (k * (β q).val)) id where
  outside _ _ _ := rfl
  evolve β := by
    let r := QRegister.singleton q
    let idx := (basisBitsEquiv n).symm β
    have hcol : g.eval.1.mulVec (Pi.single (r.extractIndex idx) 1) =
        dyadicTurn 7 (k * (β q).val) • Pi.single (r.extractIndex idx) 1 := by
      have hext : r.extractIndex idx = if β q = 0 then 0 else 1 := by
        simpa [r, idx, QRegister.extractIndex] using
          (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) =
            if b = 0 then 0 else 1) (β q)
      by_cases hq : β q = 0
      · rw [hext, ite_eq_left hq, hq]
        funext i
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, hg00]
        · simp [Matrix.mulVec, dotProduct, hg10]
      · have hq1 : β q = 1 := ((by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (β q)).resolve_left hq
        rw [hext, ite_eq_right hq, hq1]
        funext i
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, hg01]
        · simp [Matrix.mulVec, dotProduct, hg11]
    rw [Circuit.eval_gate, QRegister.embedUnitary_val, basisKet, basisState,
      r.embedMatrix_mulVec_single_factors, hcol, r.tensorState_smul_left,
      r.tensorState_single_replaceIndex, r.replaceIndex_extractIndex]
    rfl
theorem gateZ (q : Wire n) : PhasePerm (∅ : Finset (Wire n)) (Circuit.Z q)
    (fun β ↦ dyadicTurn 7 (64 * (β q).val)) id :=
  phasePerm_diag1 .Z q 64 rfl rfl rfl (by
    unfold dyadicTurn
    rw [show 2 * π * Complex.I * ((64 : ℤ) : ℂ) / (2 ^ 7 : ℂ) = π * Complex.I by
      push_cast
      ring, Complex.exp_pi_mul_I]
    rfl)
theorem gateS (q : Wire n) : PhasePerm (∅ : Finset (Wire n)) (Circuit.S q)
    (fun β ↦ dyadicTurn 7 (32 * (β q).val)) id :=
  phasePerm_diag1 .S q 32 rfl rfl rfl (by
    unfold dyadicTurn
    rw [show 2 * π * Complex.I * ((32 : ℤ) : ℂ) / (2 ^ 7 : ℂ) =
        ((π / 2 : ℝ) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp)
theorem gateSDag (q : Wire n) : PhasePerm (∅ : Finset (Wire n)) ((Circuit.S q).inverse)
    (fun β ↦ dyadicTurn 7 (-32 * (β q).val)) id := by
  rw [show (Circuit.S q).inverse = Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity) from rfl]
  refine ((gateS q).seq ((gateZ q).seq (identity ∅))).congr_phase fun β ↦ ?_
  simp only [id_eq, mul_one, dyadicTurn_add]
  exact dyadicTurn_eq_of_emod_eq 7 ((by decide : ∀ b : ZMod 2,
    (32 * (b.val : ℤ) + 64 * (b.val : ℤ)) % (2 ^ 7 : ℤ) =
      (-32 * (b.val : ℤ)) % (2 ^ 7 : ℤ)) (β q))
theorem gateT (q : Wire n) : PhasePerm (∅ : Finset (Wire n)) (Circuit.T q)
    (fun β ↦ dyadicTurn 7 (16 * (β q).val)) id :=
  phasePerm_diag1 .T q 16 rfl rfl rfl (by
    unfold dyadicTurn
    rw [show 2 * π * Complex.I * ((16 : ℤ) : ℂ) / (2 ^ 7 : ℂ) =
        ((π / 4 : ℝ) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    change (1 + Complex.I) / √2 = _
    push_cast
    field_simp [h2]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    ring)
theorem gateTDag (q : Wire n) : PhasePerm (∅ : Finset (Wire n)) ((Circuit.T q).inverse)
    (fun β ↦ dyadicTurn 7 (-16 * (β q).val)) id := by
  rw [show (Circuit.T q).inverse =
      Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity)) from rfl]
  refine ((gateT q).seq ((gateS q).seq ((gateZ q).seq (identity ∅)))).congr_phase fun β ↦ ?_
  simp only [id_eq, mul_one, dyadicTurn_add]
  exact dyadicTurn_eq_of_emod_eq 7 ((by decide : ∀ b : ZMod 2,
    (16 * (b.val : ℤ) + (32 * (b.val : ℤ) + 64 * (b.val : ℤ))) % (2 ^ 7 : ℤ) =
      (-16 * (b.val : ℤ)) % (2 ^ 7 : ℤ)) (β q))
end PhasePerm
def cliffordCZ (c t : Wire n) (h : c ≠ t) : Circuit n :=
  Circuit.S c ;;ᶜ Circuit.S t ;;ᶜ Circuit.CNOT c t h ;;ᶜ
    (Circuit.S t).inverse ;;ᶜ Circuit.CNOT c t h
@[simp] theorem count_cliffordCZ_toff (c t : Wire n) (h : c ≠ t) :
    (cliffordCZ c t h).count .TOFF = 0 := rfl
@[simp] theorem count_cliffordCZ_t (c t : Wire n) (h : c ≠ t) :
    (cliffordCZ c t h).count .T = 0 := rfl
private theorem phasePerm_cnot_sandwich (c t : Wire n) (h : c ≠ t)
    (g₁ g₂ g₃ : Circuit n) (k₁ k₂ : ℤ)
    (h₁ : PhasePerm ∅ g₁ (fun β ↦ dyadicTurn 7 (k₁ * (β c).val)) id)
    (h₂ : PhasePerm ∅ g₂ (fun β ↦ dyadicTurn 7 (k₁ * (β t).val)) id)
    (h₃ : PhasePerm ∅ g₃ (fun β ↦ dyadicTurn 7 (-k₁ * (β t).val)) id)
    (hbit : ∀ a b : ZMod 2,
      k₁ * (a.val : ℤ) + (k₁ * (b.val : ℤ) + (-k₁) * ((b + a).val : ℤ)) =
        k₂ * ((a.val : ℤ) * (b.val : ℤ))) :
    PhasePerm (∅ : Finset (Wire n))
      (g₁ ;;ᶜ g₂ ;;ᶜ Circuit.CNOT c t h ;;ᶜ g₃ ;;ᶜ Circuit.CNOT c t h)
      (fun β ↦ dyadicTurn 7 (k₂ * ((β c).val * (β t).val))) id := by
  let fc : BitAssignment n → BitAssignment n := fun γ ↦ Function.update γ t (γ t + γ c)
  have hfc : ∀ β, fc (fc β) = β := cnot_self_cancel c t h
  have hcnot : PhasePerm {t} (Circuit.CNOT c t h) (fun _ ↦ 1) fc :=
    PhasePerm.of_classicalPerm (ClassicalPerm.CNOT c t h) fun _ _ hw ↦
      Function.update_of_ne (by simpa using hw) _ _
  have hseq := (h₁.mono (Finset.empty_subset _)).seq
    ((h₂.mono (Finset.empty_subset _)).seq (hcnot.seq
      ((h₃.mono (Finset.empty_subset _)).seq hcnot)))
  refine { evolve := fun β ↦ ?_, outside := fun _ _ _ ↦ rfl }
  have hev := hseq.evolve β
  change (g₁ ;;ᶜ g₂ ;;ᶜ Circuit.CNOT c t h ;;ᶜ g₃ ;;ᶜ Circuit.CNOT c t h).eval.1.mulVec
    (basisKet β) = _ at hev
  rw [hev]
  dsimp only [Function.comp_apply, id_eq]
  rw [hfc β]
  congr 1
  dsimp only [fc]
  simp only [one_mul, mul_one, Function.update_self, dyadicTurn_add]
  exact congrArg (dyadicTurn 7) (by exact_mod_cast hbit (β c) (β t))
theorem phasePerm_cliffordCZ (c t : Wire n) (h : c ≠ t) : PhasePerm (∅ : Finset (Wire n))
    (cliffordCZ c t h) (fun β ↦ dyadicTurn 7 (64 * ((β c).val * (β t).val))) id :=
  phasePerm_cnot_sandwich c t h _ _ _ 32 64 (PhasePerm.gateS c) (PhasePerm.gateS t)
    (PhasePerm.gateSDag t) (by decide)
theorem symTempAndStep_wrap_phasePerm_correct [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {m : ℕ} (v : Var) (s : SymTempAndStep n) {M : Finset (Wire n)} (hdisj_SM : Disjoint s.S M)
    (inner : DynamicCircuit Var n) (c_inner : Circuit n) (φ_inner : BitAssignment n → ℂ)
    (f_inner : BitAssignment n → BitAssignment n) (rTotal : QRegister (m + 1) n)
    (hanc : s.anc = rTotal 0) (hdisj_S_rest : Disjoint s.S (rTotal.slice 1 m (by omega)).image)
    (h_inner : PhasePerm M c_inner φ_inner f_inner) (h_inner_wp : ∀ Ψ : CQAssertionCompat Var
    (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) → CQAssertion.restrictToZeroAncilla
      (wp inner.compile Ψ) (rTotal.slice 1 m (by omega)) = CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat c_inner.eval Ψ) (rTotal.slice 1 m (by omega))) :
    let f_wrap : BitAssignment n → BitAssignment n :=
      fun β w ↦ if w ∈ M then f_inner (s.stepFwd β) w else β w
    PhasePerm M (s.toTempAndStep.wrapCircuit c_inner) (fun β ↦ φ_inner (s.stepFwd β)) f_wrap ∧
    (∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      CQAssertion.restrictToZeroAncilla
        (wp (s.toTempAndStep.wrapDynamic v inner).compile Θ) rTotal =
        CQAssertion.restrictToZeroAncilla
          (wpQAssignCompat (s.toTempAndStep.wrapCircuit c_inner).eval Θ) rTotal) := by
  intro f_wrap
  obtain ⟨hbody_S, hf_eq⟩ := s.body_and_wrap_eq hdisj_SM f_inner h_inner.outside
  dsimp only [Function.comp_apply] at hbody_S
  let of_cp {c : Circuit n} {f : BitAssignment n → BitAssignment n}
      (h : ClassicalPerm c f) : PhasePerm (Finset.univ : Finset (Wire n)) c (fun _ ↦ 1) f :=
    PhasePerm.of_classicalPerm h fun _ _ hw ↦ absurd (Finset.mem_univ _) hw
  have htoff_p := of_cp (ClassicalPerm.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a)
  have hb_seq := (of_cp s.local_midPre.perm).seq
    ((h_inner.mono (Finset.subset_univ _)).seq (of_cp s.local_midPost.perm))
  have hc_body :
      let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1
      P₀ * (T_anc * (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost).eval.1 * T_anc * P₀) =
        T_anc * (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost).eval.1 * T_anc * P₀ := by
    intro P₀ T_anc
    refine matrix_ext_basisKet fun β ↦ ?_
    dsimp only [P₀, T_anc]
    simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_mulVec_basisKet]
    by_cases h0 : β s.anc = 0
    · simp only [h0, ↓reduceIte, evolve_TOFF_basisKet, hb_seq.evolve,
        Matrix.mulVec_smul, one_mul, mul_one, Function.comp_apply]
      let β₁ := Function.update β s.anc (0 + β s.c₁ * β s.c₂)
      have hzero : s.f_midPost (f_inner (s.f_midPre β₁)) s.anc +
          s.f_midPost (f_inner (s.f_midPre β₁)) s.c₁ *
            s.f_midPost (f_inner (s.f_midPre β₁)) s.c₂ = 0 := by
        rw [hbody_S β₁ s.anc s.anc_mem, hbody_S β₁ s.c₁ s.c₁_mem, hbody_S β₁ s.c₂ s.c₂_mem]
        simp only [β₁, Function.update_self, Function.update_of_ne s.h₁a,
          Function.update_of_ne s.h₂a]
        exact (by decide : ∀ x : ZMod 2, (0 + x) + x = 0) _
      rw [hzero, basisOutcomeProjector_zero_mulVec_basisKet]
      simp
    · simp [h0]
  refine ⟨{ evolve := fun β ↦ ?_, outside := fun β w hw ↦ by simp [f_wrap, hw] }, fun Θ hΘ ↦ ?_⟩
  · have hseq := (of_cp s.local_pre.perm).seq
      (htoff_p.seq (hb_seq.seq (htoff_p.seq (of_cp s.local_post.perm))))
    rw [show s.toTempAndStep.wrapCircuit c_inner = s.pre ;;ᶜ
        (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ
          ((s.midPre ;;ᶜ (c_inner ;;ᶜ s.midPost)) ;;ᶜ
            (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.post))) by
      simp [TempAndStep.wrapCircuit], hseq.evolve β]
    dsimp only [Function.comp_apply]
    simp only [one_mul, mul_one]
    exact congrArg (φ_inner (s.stepFwd β) • basisKet ·) (hf_eq β)
  · exact TempAndStep.restrictToZeroAncilla_wp_wrapDynamic_head_tail
      v s.toTempAndStep inner c_inner rTotal hanc s.anc_not_mem_pre
      (Finset.disjoint_of_subset_left s.local_pre.support_sub hdisj_S_rest)
      (Finset.disjoint_left.mp hdisj_S_rest s.c₁_mem)
      (Finset.disjoint_left.mp hdisj_S_rest s.c₂_mem)
      (Finset.disjoint_of_subset_left s.local_midPre.support_sub hdisj_S_rest)
      hc_body h_inner_wp Θ hΘ
def andSymStep (a b anc : Wire n) (hab : a ≠ b) (ha_anc : a ≠ anc)
    (hb_anc : b ≠ anc) : SymTempAndStep n :=
  andWithMidSymStep {a, b, anc} a b anc hab ha_anc hb_anc (by simp) (by simp) (by simp)
    Circuit.identity Circuit.identity id id ⟨rfl, rfl, rfl, rfl⟩
    (LocalClassicalPerm.identity _) (LocalClassicalPerm.identity _) fun _ ↦ rfl
theorem andSymStep_stepFwd (a b anc : Wire n) (hab : a ≠ b) (ha_anc : a ≠ anc)
    (hb_anc : b ≠ anc) (β : BitAssignment n) (hβ_anc : β anc = 0) :
    (andSymStep a b anc hab ha_anc hb_anc).stepFwd β = Function.update β anc (β a * β b) :=
  funext fun w ↦ by
    dsimp only [andSymStep, andWithMidSymStep, SymTempAndStep.stepFwd, id]
    by_cases hw : w = anc
    · simp [hw, hβ_anc]
    · simp [Function.update_of_ne hw]
def symWrapDynList (v : Var) (L : List (SymTempAndStep n)) (core : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  TempAndStep.wrapDynamicList v (L.map SymTempAndStep.toTempAndStep) core
def symWrapCircuitList (L : List (SymTempAndStep n)) (core : Circuit n) : Circuit n :=
  TempAndStep.wrapCircuitList (L.map SymTempAndStep.toTempAndStep) core
def symStepFwdList : List (SymTempAndStep n) → BitAssignment n → BitAssignment n
  | [], β => β
  | s :: rest, β => symStepFwdList rest (s.stepFwd β)
@[simp] theorem symStepFwdList_nil (β : BitAssignment n) :
    symStepFwdList ([] : List (SymTempAndStep n)) β = β := rfl
@[simp] theorem symStepFwdList_cons (s : SymTempAndStep n) (rest : List (SymTempAndStep n))
    (β : BitAssignment n) :
    symStepFwdList (s :: rest) β = symStepFwdList rest (s.stepFwd β) := rfl
theorem symStepFwdList_append (L₁ L₂ : List (SymTempAndStep n)) (β : BitAssignment n) :
    symStepFwdList (L₁ ++ L₂) β = symStepFwdList L₂ (symStepFwdList L₁ β) := by
  induction L₁ generalizing β with
  | nil => rfl
  | cons s _ ih => exact ih (s.stepFwd β)
def ValidSymStepList (M : Finset (Wire n)) {m_anc : ℕ} (rAnc : QRegister m_anc n) :
    ℕ → List (SymTempAndStep n) → Prop
  | _, [] => True
  | offset, s :: rest => ∃ hlt : offset < m_anc, s.anc = rAnc ⟨offset, hlt⟩ ∧
      Disjoint s.S M ∧ (∀ j : Fin m_anc, offset < j.val → rAnc j ∉ s.S) ∧
      ValidSymStepList M rAnc (offset + 1) rest
theorem validSymStepList_append (M : Finset (Wire n)) {m_anc : ℕ} (rAnc : QRegister m_anc n)
    (offset : ℕ) (L₁ L₂ : List (SymTempAndStep n)) : ValidSymStepList M rAnc offset (L₁ ++ L₂) ↔
      ValidSymStepList M rAnc offset L₁ ∧ ValidSymStepList M rAnc (offset + L₁.length) L₂ := by
  induction L₁ generalizing offset with
  | nil => simp [ValidSymStepList]
  | cons s rest ih =>
      simp only [List.cons_append, ValidSymStepList, List.length_cons,
        show offset + (rest.length + 1) = (offset + 1) + rest.length by omega, ih (offset + 1)]
      exact ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ ↦ ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩,
        fun ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ ↦ ⟨h1, h2, h3, h4, h5, h6⟩⟩
private lemma slice_restrict_congr {A B : CQAssertionCompat Var (2 ^ n)}
    {m_anc : ℕ} (rAnc : QRegister m_anc n) {o₁ l₁ o₂ l₂ : ℕ} (ho : o₁ = o₂) (hl : l₁ = l₂)
    {h₁ : o₁ + l₁ ≤ m_anc} {h₂ : o₂ + l₂ ≤ m_anc}
    (heq : CQAssertion.restrictToZeroAncilla A (rAnc.slice o₂ l₂ h₂) =
      CQAssertion.restrictToZeroAncilla B (rAnc.slice o₂ l₂ h₂)) :
    CQAssertion.restrictToZeroAncilla A (rAnc.slice o₁ l₁ h₁) =
      CQAssertion.restrictToZeroAncilla B (rAnc.slice o₁ l₁ h₁) := by
  subst ho
  subst hl
  exact heq
theorem symWrapDynList_phasePerm_correct [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {m_anc : ℕ} (v : Var) (M : Finset (Wire n)) (rAnc : QRegister m_anc n) (offset k_in : ℕ)
    (steps : List (SymTempAndStep n)) (hvalid : ValidSymStepList M rAnc offset steps)
    (hfit : offset + steps.length + k_in ≤ m_anc) (inner : DynamicCircuit Var n)
    (c_inner : Circuit n) (φ_inner : BitAssignment n → ℂ)
    (f_inner : BitAssignment n → BitAssignment n)
    (h_inner : PhasePerm M c_inner φ_inner f_inner) (h_inner_wp : ∀ Ψ : CQAssertionCompat Var (2 ^
    n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) → CQAssertion.restrictToZeroAncilla (wp
    inner.compile Ψ) (rAnc.slice (offset + steps.length) k_in hfit) =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c_inner.eval Ψ) (rAnc.slice (offset +
    steps.length) k_in hfit)) : ∃ f_total : BitAssignment n → BitAssignment n, PhasePerm M
    (symWrapCircuitList steps c_inner) (fun β ↦ φ_inner (symStepFwdList steps β)) f_total ∧
    (∀ β, ∀ w ∈ M, f_total β w = f_inner (symStepFwdList steps β) w) ∧ (∀ Θ : CQAssertionCompat Var
    (2 ^ n), (∀ σ val, Θ (Function.update σ v val) = Θ σ) → CQAssertion.restrictToZeroAncilla (wp
    (symWrapDynList v steps inner).compile Θ) (rAnc.slice offset (steps.length + k_in)
    (by omega)) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat (symWrapCircuitList steps
    c_inner).eval Θ) (rAnc.slice offset (steps.length + k_in) (by omega))) := by
  induction steps generalizing offset with
  | nil =>
      refine ⟨f_inner, h_inner, fun _ _ _ ↦ rfl, fun Θ hΘ ↦ ?_⟩
      have hwp0 : CQAssertion.restrictToZeroAncilla (wp (symWrapDynList v [] inner).compile Θ)
          (rAnc.slice (offset + ([] : List (SymTempAndStep n)).length) k_in hfit) =
        CQAssertion.restrictToZeroAncilla (wpQAssignCompat (symWrapCircuitList [] c_inner).eval Θ)
          (rAnc.slice (offset + ([] : List (SymTempAndStep n)).length) k_in hfit) := by
        simpa [symWrapDynList, symWrapCircuitList, TempAndStep.wrapDynamicList,
          TempAndStep.wrapCircuitList] using h_inner_wp Θ hΘ
      exact slice_restrict_congr rAnc rfl (Nat.zero_add k_in) hwp0
  | cons s rest ih =>
      rcases hvalid with ⟨hbound, hanc_s, hdisj_SM, hlat_s, hvalid_rest⟩
      have hfit' : (offset + 1) + rest.length + k_in ≤ m_anc := by
        simp only [List.length_cons] at hfit
        omega
      have ho' : (offset + 1) + rest.length = offset + (s :: rest).length := by
        simp only [List.length_cons]
        omega
      obtain ⟨f_rest, hperm_rest, hM_rest, hwp_rest⟩ := ih (offset + 1) hvalid_rest hfit'
        fun Ψ hΨ ↦ slice_restrict_congr rAnc ho' rfl (h_inner_wp Ψ hΨ)
      let m_sub : ℕ := rest.length + k_in
      let rSub : QRegister (m_sub + 1) n := rAnc.slice offset (m_sub + 1) (by omega)
      have hslice_eq : rSub.slice 1 m_sub (by omega) =
          rAnc.slice (offset + 1) m_sub (by omega) := by
        ext idx
        refine congrArg Fin.val ?_
        simp only [rSub, QRegister.slice_apply]
        exact congrArg rAnc (Fin.ext (by
          simp
          omega))
      have hanc0 : s.anc = rSub 0 := by
        rw [hanc_s]
        dsimp only [rSub]
        rw [QRegister.slice_apply]
        congr 1
      have hdisj_rest : Disjoint s.S (rSub.slice 1 m_sub (by omega)).image := by
        rw [hslice_eq, Finset.disjoint_right]
        rintro w hw
        rcases (QRegister.mem_image _ w).mp hw with ⟨idx, rfl⟩
        exact hlat_s ⟨(offset + 1) + idx.val, by omega⟩
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _))
      have hstep := symTempAndStep_wrap_phasePerm_correct v s hdisj_SM
        (symWrapDynList v rest inner) (symWrapCircuitList rest c_inner)
        (fun γ ↦ φ_inner (symStepFwdList rest γ)) f_rest rSub hanc0 hdisj_rest
        hperm_rest (fun Ψ hΨ ↦ hslice_eq ▸ hwp_rest Ψ hΨ)
      refine ⟨fun β w ↦ if w ∈ M then f_rest (s.stepFwd β) w else β w, hstep.1,
        fun β w hwM ↦ by simp [hwM, hM_rest (s.stepFwd β) w hwM, symStepFwdList_cons],
        fun Θ hΘ ↦ slice_restrict_congr rAnc rfl (by
          simp only [m_sub, List.length_cons]
          omega) (hstep.2 Θ hΘ)⟩
theorem count_symWrapDynList_toff (v : Var) (steps : List (SymTempAndStep n))
    (inner : DynamicCircuit Var n) :
    (symWrapDynList v steps inner).count .TOFF = inner.count .TOFF :=
  TempAndStep.count_wrapDynamicList_toff v _ inner fun _ hs ↦ by
    rcases List.mem_map.mp hs with ⟨s, _, rfl⟩
    exact s.clifford
theorem count_symWrapDynList_t (v : Var) (steps : List (SymTempAndStep n))
    (inner : DynamicCircuit Var n) :
    (symWrapDynList v steps inner).count .T = 4 * steps.length + inner.count .T := by
  simpa [symWrapDynList] using
    (TempAndStep.count_wrapDynamicList_t v (steps.map SymTempAndStep.toTempAndStep) inner
      fun _ hs ↦ by
        rcases List.mem_map.mp hs with ⟨s, _, rfl⟩
        exact s.clifford)
end PhasePermEngine
section CleanWorkspaceAndCatalystEngine
variable {Var : Type} {n : ℕ}
theorem basisOutcomeProjector_zero_mul_of_image_subset {m₁ m₂ : ℕ} (rWork : QRegister m₁ n)
    (rSub : QRegister m₂ n) (hsub : rSub.image ⊆ rWork.image) : rWork.basisOutcomeProjector 0
    * rSub.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 := by
  rw [rWork.basisOutcomeProjector_eq_diagonal, rSub.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  by_cases h₁ : rWork.extractIndex g = 0
  · have h₂ : rSub.extractIndex g = 0 := ((QRegExt.extractIndex_eq_zero_iff rSub) g).mpr fun j ↦ by
      obtain ⟨i, hi⟩ := (rWork.mem_image _).mp (hsub ((rSub.mem_image _).mpr ⟨j, rfl⟩))
      exact hi ▸ ((QRegExt.extractIndex_eq_zero_iff rWork) g).mp h₁ i
    simp [h₁, h₂]
  · simp [h₁]
theorem restrictAssertionToZeroAncilla_eq_of_image_subset {m₁ m₂ : ℕ}
    (rWork : QRegister m₁ n) (rSub : QRegister m₂ n) (hsub : rSub.image ⊆ rWork.image)
    {A B : CQAssertionCompat Var (2 ^ n)} (h : CQAssertion.restrictToZeroAncilla A rSub =
    CQAssertion.restrictToZeroAncilla B rSub) : CQAssertion.restrictToZeroAncilla A rWork =
    CQAssertion.restrictToZeroAncilla B rWork := by
  have habsorb (M : CQAssertionCompat Var (2 ^ n)) :
      CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla M rSub) rWork =
        CQAssertion.restrictToZeroAncilla M rWork := funext fun σ ↦ Subtype.ext <| by
    simp only [CQAssertion.restrictToZeroAncilla_coe, HermitianMat.conj_conj,
      basisOutcomeProjector_zero_mul_of_image_subset rWork rSub hsub]
  rw [← habsorb A, h, habsorb B]
private theorem wp_andUncompute_const [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (M : Observable (Fin (2 ^ n))) :
    ∃ M' : Observable (Fin (2 ^ n)),
      wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (fun _ ↦ M) = fun _ ↦ M' := by
  refine ⟨wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (fun _ ↦ M) 0, ?_⟩
  funext σ
  apply Subtype.ext
  let F := Circuit.andUncomputeFixup c₁ c₂ anc h₁₂
  let U := Circuit.H anc
  have hmeas (τ : Store Var) : (wp (.qSeq (QProg.measureRegister v (QRegister.singleton anc))
      (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip)) (fun _ ↦ M) τ).1 = M.1.conj
      ((QRegister.singleton anc).basisOutcomeProjector 0)ᴴ + (M.1.conj F.eval.1ᴴ).conj
      ((QRegister.singleton anc).basisOutcomeProjector 1)ᴴ := by
    simp only [wp_qSeq, wp_qIf, wp_skip, QProg.measureRegister,
      wp_qMeasure, CQAssertion.qMeasure_coe]
    change ∑ o : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp [Matrix.star_eq_conjTranspose,
      QRegister.computationalBasisMeasurement_apply,
      F]
  have hU (A : CQAssertionCompat Var (2 ^ n)) : wp U.compile A = CQAssertion.qAssign U.eval A :=
    DynamicCircuit.wp_circuit_compile U A
  change (wp U.compile (wp (.qSeq (QProg.measureRegister v (QRegister.singleton anc))
    (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip)) (fun _ ↦ M)) σ).1 =
    (wp U.compile (wp (.qSeq (QProg.measureRegister v (QRegister.singleton anc))
    (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip))
    (fun _ ↦ M)) 0).1
  rw [hU]
  simp only [CQAssertion.qAssign_apply, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, hmeas σ, hmeas 0]
theorem TempAndStep.wp_wrapDynamic_const [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (s : TempAndStep n) (inner : DynamicCircuit Var n) (h_inner : ∀ M : Observable
    (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp inner.compile (fun _ ↦ M) = fun _ ↦ M')
    (M : Observable (Fin (2 ^ n))) : ∃ M' : Observable (Fin (2 ^ n)),
      wp (s.wrapDynamic v inner).compile
    (fun _ ↦ M) = fun _ ↦ M' := by
  obtain ⟨M_unc, hM_unc⟩ :=
    wp_andUncompute_const v s.c₁ s.c₂ s.anc s.h₁₂ (qAssignObsMap s.post.eval M)
  obtain ⟨M_in, hM_in⟩ := h_inner (qAssignObsMap s.midPost.eval M_unc)
  refine ⟨qAssignObsMap s.pre.eval (qAssignObsMap (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a
    s.h₂a).eval (qAssignObsMap s.midPre.eval M_in)), ?_⟩
  simp only [
    TempAndStep.wrapDynamic,
    DynamicCircuit.andCompute,
    DynamicCircuit.compile_seq,
    DynamicCircuit.compile_circuit,
    wp_qSeq,
    DynamicCircuit.wp_circuit_compile,
    CQAssertion.qAssign_const,
    hM_unc,
    hM_in]
theorem symWrapDynList_wp_const [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (steps : List (SymTempAndStep n)) (inner : DynamicCircuit Var n) (h_inner : ∀ M :
    Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp inner.compile (fun _ ↦
      M) = fun _ ↦ M')
    (M : Observable (Fin (2 ^ n))) : ∃ M' : Observable (Fin (2 ^ n)), wp
    (symWrapDynList v steps inner).compile (fun _ ↦ M) = fun _ ↦ M' := by
  induction steps generalizing M with
  | nil => exact h_inner M
  | cons s rest ih => exact TempAndStep.wp_wrapDynamic_const v s.toTempAndStep _ ih M
theorem realizesEmbeddedUnitaryWithCleanWorkspace_of_kets [Fintype Var] [DecidableEq Var]
    [NeZero (2 ^ n)] {k m : ℕ} (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (d : DynamicCircuit Var n) (c : Circuit n) (hconst : ∀ M :
    Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦ M) = fun _ ↦
      M') (hwp
    : ∀ M : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla (wp d.compile (fun _ ↦ M))
    rWork = CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval (fun _ ↦ M)) rWork) (hkets
    : ∀ β : BitAssignment n, (∀ j : Fin m, β (rWork j) = 0) → c.eval.1.mulVec (basisKet β) =
    (rAct.embedUnitary u).1.mulVec (basisKet β)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d := by
  let P₀ := rWork.basisOutcomeProjector 0
  have hmat : c.eval.1 * P₀ = (rAct.embedUnitary u).1 * P₀ := matrix_ext_basisKet fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with hz
    · exact hkets β hz
    · simp
  have hadj : P₀ * c.eval.1ᴴ = P₀ * (rAct.embedUnitary u).1ᴴ := by
    simpa only [P₀, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      congrArg conjTranspose hmat
  intro M
  obtain ⟨M', hM'⟩ := hconst M
  refine ⟨M', hM', ?_⟩
  have h_s1 : P₀ * M'.1.1 * P₀ = P₀ * c.eval.1ᴴ * M.1.1 * c.eval.1 * P₀ := by
    have h_eq := congrArg (fun F ↦ (F (0 : Store Var)).1.1) (hwp M)
    rw [hM'] at h_eq
    dsimp only [P₀]
    simpa [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using h_eq
  calc P₀ * M'.1.1 * P₀
      = (P₀ * c.eval.1ᴴ) * M.1.1 * (c.eval.1 * P₀) := by
          rw [h_s1]
          simp only [Matrix.mul_assoc]
    _ = P₀ * ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * P₀ := by
          rw [hadj, hmat]
          simp only [Matrix.mul_assoc]
noncomputable def dyadicDiagUnitary (k B : ℕ) (e : BitAssignment k → ℤ) : Unitary (2 ^ k) :=
  ⟨Matrix.diagonal fun x : Fin (2 ^ k) ↦ dyadicTurn B (e (basisBits k x)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_dyadicTurn_mul_self B _)⟩
theorem dyadicDiagUnitary_inv (k B : ℕ) (e : BitAssignment k → ℤ) :
    (dyadicDiagUnitary k B e)⁻¹ = dyadicDiagUnitary k B (fun γ ↦ -e γ) := by
  apply inv_eq_of_mul_eq_one_left
  ext i j
  simp only [Submonoid.coe_mul, dyadicDiagUnitary, Matrix.diagonal_mul_diagonal,
    OneMemClass.coe_one, ← Matrix.diagonal_one]
  by_cases hij : i = j
  · subst hij
    simp [dyadicTurn_add]
  · simp [hij]
theorem embedUnitary_dyadicDiagUnitary_mulVec_basisKet {k : ℕ}
    (rAct : QRegister k n) (B : ℕ) (e : BitAssignment k → ℤ) (β : BitAssignment n) :
    (rAct.embedUnitary (dyadicDiagUnitary k B e)).1.mulVec (basisKet β) =
      dyadicTurn B (e (fun i ↦ β (rAct i))) • basisKet β := funext fun g ↦ by
  rw [QRegister.embedUnitary_val, dyadicDiagUnitary, rAct.embedMatrix_diagonal_mulVec]
  by_cases hg : g = (basisBitsEquiv n).symm β
  · subst hg
    rw [show basisBits k (rAct.extractIndex ((basisBitsEquiv n).symm β)) = fun i ↦ β (rAct i)
      from funext fun i ↦ by simp [-Nat.reducePow, QRegister.basisBits_extractIndex]]
    rfl
  · simp [basisKet, basisState, Pi.single_eq_of_ne hg]
def splitSysCatEquiv (kSys B : ℕ) : Fin (2 ^ (kSys + B)) ≃ BitAssignment kSys × Fin (2 ^ B) :=
  (basisBitsEquiv (kSys + B)).trans
    { toFun := fun f ↦
        (fun i ↦ f (Fin.castAdd B i), (basisBitsEquiv B).symm (fun j ↦ f (Fin.natAdd kSys j)))
      invFun := fun p ↦ Fin.addCases p.1 (basisBits B p.2)
      left_inv := fun _ ↦ funext (Fin.addCases (fun _ ↦ by simp) (fun _ ↦ by simp))
      right_inv := fun ⟨_, _⟩ ↦ Prod.ext (funext fun _ ↦ by simp) (by simp) }
lemma mod_add_sub_cancel (M : ℕ) (hM : 0 < M) (m s : ℕ) (hm : m < M) :
    ((m + s) % M + (M - s % M)) % M = m := by
  have hs : s % M < M := Nat.mod_lt s hM
  rw [Nat.mod_add_mod, show m + s + (M - s % M) = m + M * (s / M + 1) by
    linarith [Nat.div_add_mod s M, Nat.add_sub_of_le (le_of_lt hs), mul_add M (s / M) 1,
      mul_one M], Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]
def catModAddMidPerm (kSys B : ℕ) (shift : BitAssignment kSys → ℕ) :
    Equiv.Perm (BitAssignment kSys × Fin (2 ^ B)) where
  toFun p := (p.1, ⟨(p.2.val + shift p.1) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩)
  invFun p :=
    (p.1, ⟨(p.2.val + (2 ^ B - shift p.1 % 2 ^ B)) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩)
  left_inv := fun ⟨γ, m⟩ ↦ Prod.ext rfl <| Fin.ext <|
    mod_add_sub_cancel (2 ^ B) (by positivity) m.val (shift γ) m.isLt
  right_inv := fun ⟨γ, m⟩ ↦ Prod.ext rfl <| Fin.ext <| by
    dsimp only
    have hs : shift γ % 2 ^ B < 2 ^ B := Nat.mod_lt _ (by positivity)
    calc ((m.val + (2 ^ B - shift γ % 2 ^ B)) % 2 ^ B + shift γ) % 2 ^ B
        = (m.val + (2 ^ B - shift γ % 2 ^ B) + shift γ % 2 ^ B) % 2 ^ B := by
            rw [Nat.mod_add_mod, Nat.add_mod_mod]
      _ = (m.val + 2 ^ B) % 2 ^ B := by
            rw [Nat.add_assoc, Nat.sub_add_cancel (le_of_lt hs)]
      _ = m.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]
def catModAddPerm (kSys B : ℕ) (shift : BitAssignment kSys → ℕ) :
    Equiv.Perm (Fin (2 ^ (kSys + B))) :=
  (splitSysCatEquiv kSys B).trans <|
    (catModAddMidPerm kSys B shift).trans (splitSysCatEquiv kSys B).symm
noncomputable def catModAddUnitary (kSys B : ℕ) (shift : BitAssignment kSys → ℕ) : Unitary
    (2 ^ (kSys + B)) := permutationUnitary (catModAddPerm kSys B shift)
theorem catModAddUnitary_mulVec_basisKet {kSys B : ℕ} (rSys : QRegister kSys n)
    (rCat : QRegister B n) (hdisj : rSys.DisjointWires rCat) (shift : BitAssignment kSys → ℕ)
    (f : BitAssignment n → BitAssignment n) (β : BitAssignment n)
    (hout : ∀ w, w ∉ rCat.image → f β w = β w) (hval : regVal rCat (f β) = (regVal rCat β +
    shift (fun i ↦ β (rSys i))) % 2 ^ B) : basisKet (f β) = ((rSys.concat rCat
    hdisj).embedUnitary (catModAddUnitary kSys B shift)).1.mulVec (basisKet β) := by
  let rSC := rSys.concat rCat hdisj
  let idx₀ := (basisBitsEquiv n).symm β
  have hext_sys : (splitSysCatEquiv kSys B (rSC.extractIndex idx₀)).1 = fun i ↦ β (rSys i) :=
    funext fun i ↦ by
      change basisBits (kSys + B) (rSC.extractIndex idx₀) (Fin.castAdd B i) = β (rSys i)
      simp [rSC, idx₀]
  have hext_cat_fin : (splitSysCatEquiv kSys B (rSC.extractIndex idx₀)).2 =
      (basisBitsEquiv B).symm (fun i ↦ β (rCat i)) := by
    change (basisBitsEquiv B).symm (fun j ↦ basisBits (kSys + B) (rSC.extractIndex idx₀)
      (Fin.natAdd kSys j)) = (basisBitsEquiv B).symm (fun i ↦ β (rCat i))
    congr 1
    funext j
    simp [rSC, idx₀]
  have hext_cat : (splitSysCatEquiv kSys B (rSC.extractIndex idx₀)).2.val = regVal rCat β := by
    rw [hext_cat_fin, regVal, bitsVal_eq_symm_val]
  rw [QRegister.embedUnitary_val, catModAddUnitary, basisKet, basisKet, basisState, basisState,
    rSC.embedMatrix_mulVec_single_factors, permutationUnitary_mulVec_single,
    rSC.tensorState_single_replaceIndex]
  congr 1
  apply (basisBitsEquiv n).injective
  funext w
  rw [Equiv.apply_symm_apply]
  change f β w =
    basisBits n (rSC.replaceIndex idx₀ (catModAddPerm kSys B shift (rSC.extractIndex idx₀))) w
  have hcat_eq : catModAddPerm kSys B shift (rSC.extractIndex idx₀) =
      (splitSysCatEquiv kSys B).symm (fun i ↦ β (rSys i), ⟨regVal rCat (f β),
      regVal_lt_two_pow rCat (f β)⟩) := by
    simp only [catModAddPerm, Equiv.trans_apply]
    congr 1
    ext
    · dsimp only [catModAddMidPerm, Equiv.coe_fn_mk]
      exact congrFun hext_sys _
    · simp only [catModAddMidPerm, Equiv.coe_fn_mk, hext_sys, hext_cat, hval]
  by_cases hwSC : w ∈ Set.range rSC.wires
  · rcases hwSC with ⟨idx, rfl⟩
    rw [rSC.basisBits_replaceIndex_apply, hcat_eq]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left, hout (rSys i) (hdisj.apply_not_mem_right i)]
      simp [splitSysCatEquiv]
    · rw [QRegister.concat_apply_right]
      have hbits : basisBits B ⟨regVal rCat (f β), regVal_lt_two_pow rCat (f β)⟩ =
          fun t ↦ f β (rCat t) := by
        apply (basisBitsEquiv B).symm.injective
        ext
        simp [regVal, bitsVal_eq_symm_val]
      simp [splitSysCatEquiv, hbits]
  · rw [rSC.basisBits_replaceIndex_of_not_mem idx₀ _ w hwSC, hout w fun hmem ↦ by
      rcases (rCat.mem_image w).mp hmem with ⟨j, rfl⟩
      exact hwSC ⟨Fin.natAdd kSys j, QRegister.concat_apply_right rSys rCat hdisj j⟩]
    simp [idx₀]
noncomputable def phaseGradKet (b : ℕ) : Fin (2 ^ b) → ℂ := fun m ↦
  ((2 : ℝ) ^ (-(b : ℝ) / 2) : ℂ) * Complex.exp (-(2 * π * Complex.I * (m.val : ℂ)) / 2 ^ b)
theorem phaseGradKet_eq_norm_mul_dyadicTurn (b : ℕ) (m : Fin (2 ^ b)) :
    phaseGradKet b m = ((2 : ℝ) ^ (-(b : ℝ) / 2) : ℂ) * dyadicTurn b (-(m.val : ℤ)) := by
  unfold phaseGradKet dyadicTurn
  congr 2
  push_cast
  ring
def IntertwinesCatOp {N : ℕ} (U_cat P_Cat0 M_cat M_eff : Operator N) : Prop :=
  M_cat * U_cat * P_Cat0 = U_cat * M_eff * P_Cat0 ∧ M_eff * U_cat = U_cat * M_eff ∧
    M_eff * P_Cat0 = P_Cat0 * M_eff
theorem IntertwinesCatOp.one {N : ℕ} (U_cat P_Cat0 : Operator N) :
    IntertwinesCatOp U_cat P_Cat0 1 1 := ⟨by simp, by simp, by simp⟩
theorem IntertwinesCatOp.refl_of_comm {N : ℕ} {U_cat P_Cat0 M : Operator N}
    (hU : M * U_cat = U_cat * M) (hP : M * P_Cat0 = P_Cat0 * M) :
    IntertwinesCatOp U_cat P_Cat0 M M := ⟨by rw [hU], hU, hP⟩
theorem IntertwinesCatOp.mul {N : ℕ} {U_cat P_Cat0 A_cat A_eff B_cat B_eff : Operator N}
    (hA : IntertwinesCatOp U_cat P_Cat0 A_cat A_eff)
    (hB : IntertwinesCatOp U_cat P_Cat0 B_cat B_eff) :
    IntertwinesCatOp U_cat P_Cat0 (A_cat * B_cat) (A_eff * B_eff) :=
  ⟨by calc (A_cat * B_cat) * U_cat * P_Cat0
        _ = A_cat * (B_cat * U_cat * P_Cat0) := by simp only [Matrix.mul_assoc]
        _ = A_cat * (U_cat * B_eff * P_Cat0) := by rw [hB.1]
        _ = A_cat * U_cat * (P_Cat0 * B_eff) := by
            rw [← hB.2.2]
            simp only [Matrix.mul_assoc]
        _ = (A_cat * U_cat * P_Cat0) * B_eff := by simp only [Matrix.mul_assoc]
        _ = (U_cat * A_eff * P_Cat0) * B_eff := by rw [hA.1]
        _ = U_cat * A_eff * (P_Cat0 * B_eff) := by simp only [Matrix.mul_assoc]
        _ = U_cat * A_eff * (B_eff * P_Cat0) := by rw [← hB.2.2]
        _ = U_cat * (A_eff * B_eff) * P_Cat0 := by simp only [Matrix.mul_assoc],
   by rw [Matrix.mul_assoc, hB.2.1, ← Matrix.mul_assoc, hA.2.1, Matrix.mul_assoc],
   by rw [Matrix.mul_assoc, hB.2.2, ← Matrix.mul_assoc, hA.2.2, Matrix.mul_assoc]⟩
theorem IntertwinesCatOp.unitary_star {N : ℕ} {U_cat P_Cat0 : Operator N}
    (hP_sa : star P_Cat0 = P_Cat0) (B_cat B_eff : Unitary N)
    (h : IntertwinesCatOp U_cat P_Cat0 B_cat.1 B_eff.1) : IntertwinesCatOp U_cat P_Cat0
    (star B_cat.1) (star B_eff.1) := by
  have hP_comm : star B_eff.1 * P_Cat0 = P_Cat0 * star B_eff.1 := by
    simpa only [star_mul, hP_sa] using (congrArg star h.2.2).symm
  have hU_comm : star B_eff.1 * U_cat = U_cat * star B_eff.1 := by
    calc star B_eff.1 * U_cat
      _ = star B_eff.1 * U_cat * (B_eff.1 * star B_eff.1) := by rw [B_eff.2.2, Matrix.mul_one]
      _ = star B_eff.1 * (U_cat * B_eff.1) * star B_eff.1 := by simp only [Matrix.mul_assoc]
      _ = star B_eff.1 * (B_eff.1 * U_cat) * star B_eff.1 := by rw [← h.2.1]
      _ = (star B_eff.1 * B_eff.1) * U_cat * star B_eff.1 := by simp only [Matrix.mul_assoc]
      _ = U_cat * star B_eff.1 := by rw [B_eff.2.1, Matrix.one_mul]
  refine ⟨?_, hU_comm, hP_comm⟩
  calc star B_cat.1 * U_cat * P_Cat0
    _ = star B_cat.1 * U_cat * (B_eff.1 * star B_eff.1) * P_Cat0 := by
        rw [B_eff.2.2, Matrix.mul_one]
    _ = star B_cat.1 * U_cat * B_eff.1 * (star B_eff.1 * P_Cat0) := by
        simp only [Matrix.mul_assoc]
    _ = star B_cat.1 * U_cat * B_eff.1 * (P_Cat0 * star B_eff.1) := by rw [hP_comm]
    _ = star B_cat.1 * (U_cat * B_eff.1 * P_Cat0) * star B_eff.1 := by
        simp only [Matrix.mul_assoc]
    _ = star B_cat.1 * (B_cat.1 * U_cat * P_Cat0) * star B_eff.1 := by rw [← h.1]
    _ = (star B_cat.1 * B_cat.1) * U_cat * P_Cat0 * star B_eff.1 := by
        simp only [Matrix.mul_assoc]
    _ = U_cat * (P_Cat0 * star B_eff.1) := by rw [B_cat.2.1, Matrix.one_mul, Matrix.mul_assoc]
    _ = U_cat * (star B_eff.1 * P_Cat0) := by rw [← hP_comm]
    _ = U_cat * star B_eff.1 * P_Cat0 := by rw [Matrix.mul_assoc]
theorem catModAddUnitary_intertwinesCat [NeZero (2 ^ n)] {kSys B : ℕ}
    (rSys : QRegister kSys n) (rCat : QRegister B n) (hdisj : rSys.DisjointWires rCat)
    (U_cat_B : Unitary (2 ^ B)) (hcol0 : U_cat_B.1.mulVec (Pi.single 0 1) = phaseGradKet B)
    (shift : BitAssignment kSys → ℕ) : IntertwinesCatOp (rCat.embedUnitary U_cat_B).1
    (rCat.basisOutcomeProjector 0) ((rSys.concat rCat hdisj).embedUnitary (catModAddUnitary
    kSys B shift)).1 (rSys.embedUnitary (dyadicDiagUnitary kSys B (fun γ ↦ (shift γ : ℤ)))).1 :=
  ⟨by
    apply matrix_ext_basisKet
    intro β
    simp only [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with hzero
    · let idx₀ := (basisBitsEquiv n).symm β
      let γ : BitAssignment kSys := fun i ↦ β (rSys i)
      have hext0 : rCat.extractIndex idx₀ = 0 :=
        (QRegExt.extractIndex_eq_zero_iff rCat idx₀).mpr fun j ↦ by simp [idx₀, hzero j]
      have hprep : (rCat.embedUnitary U_cat_B).1.mulVec (basisKet β) = ∑ m : Fin (2 ^ B),
          phaseGradKet B m • basisKet (basisBits n (rCat.replaceIndex idx₀ m)) := by
        have hexpand : phaseGradKet B =
            ∑ m : Fin (2 ^ B), phaseGradKet B m • Pi.single m (1 : ℂ) := funext fun x ↦ by
          rw [Finset.sum_apply, Finset.sum_eq_single x]
          · simp
          · exact fun m _ hmx ↦ by simp [Pi.single_eq_of_ne hmx.symm]
          · exact fun hx ↦ absurd (Finset.mem_univ x) hx
        conv_lhs =>
          rw [QRegister.embedUnitary_val, basisKet, basisState,
            rCat.embedMatrix_mulVec_single_factors, hext0, hcol0, hexpand,
            rCat.tensorState_sum_left]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [rCat.tensorState_smul_left, rCat.tensorState_single_replaceIndex]
        simp only [basisKet, basisState, basisBitsEquiv_symm_basisBits_eq, idx₀]
      have hstep (m : Fin (2 ^ B)) : ((rSys.concat rCat hdisj).embedUnitary
          (catModAddUnitary kSys B shift)).1.mulVec
            (basisKet (basisBits n (rCat.replaceIndex idx₀ m))) =
          basisKet (basisBits n (rCat.replaceIndex idx₀
            ⟨(m.val + shift γ) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩)) := by
        symm
        let m' : Fin (2 ^ B) := ⟨(m.val + shift γ) % 2 ^ B, Nat.mod_lt _ (by positivity)⟩
        have hval_r (x : Fin (2 ^ B)) :
            regVal rCat (basisBits n (rCat.replaceIndex idx₀ x)) = x.val := by
          rw [regVal, show (fun j ↦ basisBits n (rCat.replaceIndex idx₀ x) (rCat j)) =
              basisBits B x from funext (rCat.basisBits_replaceIndex_apply idx₀ x),
            bitsVal_basisBits]
        apply catModAddUnitary_mulVec_basisKet rSys rCat hdisj shift
          (fun _ ↦ basisBits n (rCat.replaceIndex idx₀ m'))
          (basisBits n (rCat.replaceIndex idx₀ m))
        · intro w hw
          have hnot : w ∉ Set.range rCat.wires :=
            fun ⟨j, hj⟩ ↦ hw ((QRegister.mem_image rCat w).mpr ⟨j, hj⟩)
          simp [rCat.basisBits_replaceIndex_of_not_mem idx₀ _ w hnot]
        · rw [hval_r m', hval_r m, show (fun i ↦ basisBits n (rCat.replaceIndex idx₀ m)
              (rSys i)) = γ from funext fun i ↦ by
            rw [rCat.basisBits_replaceIndex_of_not_mem idx₀ m (rSys i)
              (fun ⟨j, hj⟩ ↦ hdisj.ne i j hj.symm)]
            simp [γ, idx₀]]
      rw [embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul, hprep,
        Matrix.mulVec_sum, Finset.smul_sum]
      simp_rw [Matrix.mulVec_smul, hstep, smul_smul]
      let M := catModAddMidPerm 0 B (fun _ ↦ shift γ)
      let e : Equiv.Perm (Fin (2 ^ B)) :=
        { toFun := fun m ↦ (M (0, m)).2
          invFun := fun k ↦ (M.symm (0, k)).2
          left_inv := fun m ↦ congrArg Prod.snd (M.symm_apply_apply (0, m))
          right_inv := fun k ↦ congrArg Prod.snd (M.apply_symm_apply (0, k)) }
      rw [← e.symm.sum_comp]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hek : e (e.symm k) = k := e.apply_symm_apply k
      change phaseGradKet B (e.symm k) •
          basisKet (basisBits n (rCat.replaceIndex idx₀ (e (e.symm k)))) =
        (dyadicTurn B (shift γ : ℤ) * phaseGradKet B k) •
          basisKet (basisBits n (rCat.replaceIndex idx₀ k))
      rw [hek]
      congr 1
      rw [phaseGradKet_eq_norm_mul_dyadicTurn B (e.symm k),
        phaseGradKet_eq_norm_mul_dyadicTurn B k, ← mul_assoc,
        mul_comm (dyadicTurn B (shift γ : ℤ)), mul_assoc, dyadicTurn_add]
      congr 1
      have hmod_nat : ((e.symm k).val + shift γ) % 2 ^ B = k.val := congrArg Fin.val hek
      have hdiv := Nat.div_add_mod ((e.symm k).val + shift γ) (2 ^ B)
      rw [hmod_nat] at hdiv
      have hcast : ((2 ^ B : ℤ) * (((e.symm k).val + shift γ) / 2 ^ B : ℕ)) + (k.val : ℤ) =
          ((e.symm k).val : ℤ) + (shift γ : ℤ) := by exact_mod_cast hdiv
      rw [show (-(e.symm k).val : ℤ) = ((shift γ : ℤ) + -(k.val : ℤ)) +
          (-((((e.symm k).val + shift γ) / 2 ^ B : ℕ) : ℤ)) * (2 ^ B : ℤ) by
        linear_combination hcast, dyadicTurn_add_period]
    · simp,
   rSys.embedMatrix_comm_of_disjoint rCat hdisj _ _,
   rSys.embedMatrix_comm_of_disjoint rCat hdisj _ (compProj 0)⟩
theorem regVal_split_slice {B s k_hi : ℕ} (r : QRegister B n) (hs : s + k_hi = B)
    (γ : BitAssignment n) : regVal r γ = regVal (r.slice 0 s (by omega)) γ + 2 ^ s * regVal
    (r.slice s k_hi (by omega)) γ := by
  subst hs
  unfold regVal bitsVal
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hw : r (finSumFinEquiv (@Sum.inl (Fin s) (Fin k_hi) i)) =
        (r.slice 0 s (by omega)) i := by
      rw [QRegister.slice_apply]
      exact congrArg r (Fin.ext (by simp))
    dsimp only [Function.comp_apply]
    rw [hw]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hw : r (finSumFinEquiv (@Sum.inr (Fin s) (Fin k_hi) j)) =
        (r.slice s k_hi (by omega)) j := by
      rw [QRegister.slice_apply]
      exact congrArg r (Fin.ext rfl)
    dsimp only [Function.comp_apply]
    rw [hw]
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, pow_add]
    ring
def xAllCircuit : {q : ℕ} → QRegister q n → Circuit n
  | 0, _ => Circuit.identity
  | q + 1, r => Circuit.X (r 0) ;;ᶜ xAllCircuit (r.slice 1 q (by omega))
@[simp] theorem count_xAllCircuit_toff {q : ℕ} (r : QRegister q n) :
    (xAllCircuit r).count .TOFF = 0 := by
  induction q with | zero => simp [xAllCircuit] | succ _ ih => simp [xAllCircuit, ih]
@[simp] theorem count_xAllCircuit_t {q : ℕ} (r : QRegister q n) :
    (xAllCircuit r).count .T = 0 := by
  induction q with | zero => simp [xAllCircuit] | succ _ ih => simp [xAllCircuit, ih]
def flipRegBits {q : ℕ} (r : QRegister q n) (β : BitAssignment n) : BitAssignment n :=
  fun w ↦ if w ∈ r.image then β w + 1 else β w
theorem flipRegBits_outside {q : ℕ} (r : QRegister q n) (β : BitAssignment n) {w : Wire n}
    (hw : w ∉ r.image) : flipRegBits r β w = β w := by simp [flipRegBits, hw]
theorem flipRegBits_self_inv {q : ℕ} (r : QRegister q n) (β : BitAssignment n) :
    flipRegBits r (flipRegBits r β) = β := funext fun w ↦ by
  by_cases hw : w ∈ r.image
  · simp [flipRegBits, hw, zmod2_add_cancel_right]
  · simp [flipRegBits, hw]
theorem classicalPerm_xAllCircuit {q : ℕ} (r : QRegister q n) :
    ClassicalPerm (xAllCircuit r) (flipRegBits r) := by
  induction q with
  | zero =>
      intro β
      rw [show flipRegBits r β = β from funext fun w ↦ by simp [flipRegBits, QRegister.mem_image]]
      exact ClassicalPerm.identity β
  | succ q ih =>
      let r_tail := r.slice 1 q (by omega)
      have h0_not_tail : r 0 ∉ r_tail.image := QRegExt.head_not_mem_tail_image r
      have hseq := (ClassicalPerm.X (r 0)).seq (ih r_tail)
      intro β
      rw [xAllCircuit, hseq β]
      congr 1
      funext w
      simp only [Function.comp_apply, flipRegBits, QRegExt.image_head_tail r, Finset.mem_insert]
      by_cases hw0 : w = r 0
      · simp [hw0, h0_not_tail]
      · simp [r_tail, hw0]
theorem regVal_flipRegBits {q : ℕ} (r : QRegister q n) (β : BitAssignment n) :
    regVal r (flipRegBits r β) = 2 ^ q - 1 - regVal r β := by
  induction q with
  | zero => simp [regVal, bitsVal]
  | succ q ih =>
      let r_tail := r.slice 1 q (by omega)
      have h0_mem : r 0 ∈ r.image := (QRegister.mem_image r _).mpr ⟨0, rfl⟩
      have htail_eq : regVal r_tail (flipRegBits r β) = regVal r_tail (flipRegBits r_tail β) :=
        regVal_congr r_tail fun i ↦ by
          have hi := (QRegister.mem_image r_tail _).mpr ⟨i, rfl⟩
          simp [flipRegBits, hi, QRegister.image_compose_subset r _ hi]
      have hb0_flip := (by decide : ∀ b : ZMod 2, (b + 1).val = 1 - b.val) (β (r 0))
      have hb0 := zmod2_val_le_one (β (r 0))
      have hlt_tail := regVal_lt_two_pow r_tail β
      rw [regVal_head_tail r (flipRegBits r β), regVal_head_tail r β,
        show flipRegBits r β (r 0) = β (r 0) + 1 by simp [flipRegBits, h0_mem],
        hb0_flip, show regVal (r.slice 1 q (by omega)) (flipRegBits r β) =
          2 ^ q - 1 - regVal r_tail β from htail_eq.trans (ih r_tail), pow_succ]
      dsimp only [r_tail] at hlt_tail ⊢
      omega
theorem restrictAssertionToZeroAncilla_mat_eq [NeZero (2 ^ n)]
    {m : ℕ} {A B : CQAssertionCompat Var (2 ^ n)} {rWork : QRegister m n}
    (h : CQAssertion.restrictToZeroAncilla A rWork = CQAssertion.restrictToZeroAncilla B rWork)
    (σ : Store Var) :
    rWork.basisOutcomeProjector 0 * (A σ).1.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * (B σ).1.1 * rWork.basisOutcomeProjector 0 := by
  simpa [CQAssertion.restrictToZeroAncilla_coe] using congrArg (fun F ↦ (F σ).1.1) h
theorem restrictAssertionToZeroAncilla_eq_of_mat_eq
    [NeZero (2 ^ n)] {m : ℕ} {A B : CQAssertionCompat Var (2 ^ n)} {rWork : QRegister m n}
    (h : ∀ σ : Store Var, rWork.basisOutcomeProjector 0 * (A σ).1.1 *
      rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * (B σ).1.1 * rWork.basisOutcomeProjector 0) :
    CQAssertion.restrictToZeroAncilla A rWork = CQAssertion.restrictToZeroAncilla B rWork :=
  funext fun σ ↦ Subtype.ext <| Subtype.ext <| by
    simpa [CQAssertion.restrictToZeroAncilla_coe] using h σ
private theorem restrict_wpQAssign_of_phasePerm
    [Fintype Var] [NeZero (2 ^ n)] {m : ℕ}
    {rWork : QRegister m n} {M : Finset (Wire n)} {c : Circuit n}
    {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hc : PhasePerm M c φ f) (hdisj : Disjoint M rWork.image) {A B : CQAssertionCompat Var (2 ^ n)}
    (hab : CQAssertion.restrictToZeroAncilla A rWork = CQAssertion.restrictToZeroAncilla B rWork) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval A) rWork =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval B) rWork := by
  let P₀ := rWork.basisOutcomeProjector 0
  let U := c.eval.1
  have hkeep : U * P₀ = P₀ * U * P₀ := matrix_ext_basisKet fun β ↦ by
    dsimp only [P₀, U]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with hzero
    · have hf_zero : ∀ j : Fin m, f β (rWork j) = 0 := fun j ↦ by
        rw [hc.preserves_outside β (rWork j) (Finset.disjoint_right.mp hdisj
          ((QRegister.mem_image rWork _).mpr ⟨j, rfl⟩))]
        exact hzero j
      rw [hc.eval_ket β, Matrix.mulVec_smul,
        register_basisOutcomeProjector_zero_mulVec_basisKet]
      simp [hf_zero]
    · simp
  have hkeep_adj : P₀ * Uᴴ = P₀ * Uᴴ * P₀ := by
    simpa only [P₀, U, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
      Matrix.mul_assoc] using congrArg conjTranspose hkeep
  have hsand (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      P₀ * (Uᴴ * X * U) * P₀ = P₀ * Uᴴ * (P₀ * X * P₀) * U * P₀ := by
    calc P₀ * (Uᴴ * X * U) * P₀ = (P₀ * Uᴴ) * X * (U * P₀) := by simp only [Matrix.mul_assoc]
      _ = P₀ * Uᴴ * (P₀ * X * P₀) * U * P₀ := by
            conv_lhs => rw [hkeep, hkeep_adj]
            simp only [Matrix.mul_assoc]
  apply restrictAssertionToZeroAncilla_eq_of_mat_eq
  intro σ
  have hσ := restrictAssertionToZeroAncilla_mat_eq hab σ
  have hw (C : CQAssertionCompat Var (2 ^ n)) :
      (wpQAssignCompat c.eval C σ).1.1 = Uᴴ * (C σ).1.1 * U := by
    simp [U, wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [hw A, hw B, hsand, hsand, hσ]
theorem restrictAssertionToZeroAncilla_seq_unitary_sandwich
    [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ} (rWork : QRegister m n)
    (M₁ : Finset (Wire n)) (c₁ : Circuit n) (φ₁ : BitAssignment n → ℂ)
    (f₁ : BitAssignment n → BitAssignment n) (hc₁ : PhasePerm M₁ c₁ φ₁ f₁)
    (hdisj₁ : Disjoint M₁ rWork.image) (d : DynamicCircuit Var n) (c₂ c₃ : Circuit n)
    (Θ : CQAssertionCompat Var (2 ^ n))
    (hd : CQAssertion.restrictToZeroAncilla (wp d.compile (wpQAssignCompat c₃.eval Θ)) rWork =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c₂.eval
        (wpQAssignCompat c₃.eval Θ)) rWork) :
    CQAssertion.restrictToZeroAncilla (wp (.circuit c₁ ;;ᵈ d ;;ᵈ .circuit c₃).compile Θ) rWork =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat (c₁ ;;ᶜ c₂ ;;ᶜ c₃).eval Θ) rWork := by
  simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
    DynCircuitExt.wp_circuit_compile_compat, Circuit.eval_seq, ← wpQAssignCompat_comp]
  exact restrict_wpQAssign_of_phasePerm hc₁ hdisj₁ hd
structure CleanPhasePerm [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (rWork : QRegister m n) (M : Finset (Wire n)) (d : DynamicCircuit Var n) (c : Circuit n)
    (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n) : Prop where
  phasePerm : PhasePerm M c φ f
  wp_const : ∀ Q : Observable (Fin (2 ^ n)), ∃ Q', wp d.compile (fun _ ↦ Q) = fun _ ↦ Q'
  wp_obs : ∀ Q : Observable (Fin (2 ^ n)), CQAssertion.restrictToZeroAncilla (wp d.compile (fun _ ↦
    Q))
    rWork = CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval (fun _ ↦ Q)) rWork
namespace CleanPhasePerm
theorem mono_work_and_set [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m₁ m₂ : ℕ}
    {rSub : QRegister m₁ n} {rWork : QRegister m₂ n} {M₁ M₂ : Finset (Wire n)}
    {d : DynamicCircuit Var n} {c : Circuit n} {φ : BitAssignment n → ℂ}
    {f : BitAssignment n → BitAssignment n} (h : CleanPhasePerm rSub M₁ d c φ f)
    (hsub : rSub.image ⊆ rWork.image) (hM : M₁ ⊆ M₂) : CleanPhasePerm rWork M₂ d c φ f :=
  ⟨h.phasePerm.mono hM, h.wp_const,
    fun Q ↦ restrictAssertionToZeroAncilla_eq_of_image_subset rWork rSub hsub (h.wp_obs Q)⟩
theorem seq [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    {rWork : QRegister m n} {M₁ M₂ : Finset (Wire n)}
    {d₁ d₂ : DynamicCircuit Var n} {c₁ c₂ : Circuit n}
    {φ₁ φ₂ : BitAssignment n → ℂ} {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : CleanPhasePerm rWork M₁ d₁ c₁ φ₁ f₁)
    (hdisj₁ : Disjoint M₁ rWork.image)
    (h₂ : CleanPhasePerm rWork M₂ d₂ c₂ φ₂ f₂) :
    CleanPhasePerm rWork (M₁ ∪ M₂) (d₁ ;;ᵈ d₂) (c₁ ;;ᶜ c₂)
      (fun β ↦ φ₁ β * φ₂ (f₁ β)) (f₂ ∘ f₁) where
  phasePerm :=
    (h₁.phasePerm.mono Finset.subset_union_left).seq
      (h₂.phasePerm.mono Finset.subset_union_right)
  wp_const Q := by
    obtain ⟨Q₂, hQ₂⟩ := h₂.wp_const Q
    obtain ⟨Q₁, hQ₁⟩ := h₁.wp_const Q₂
    exact ⟨Q₁, by simpa only [DynamicCircuit.compile_seq, wp_qSeq, hQ₂] using hQ₁⟩
  wp_obs Q := by
    obtain ⟨Q₂, hQ₂⟩ := h₂.wp_const Q
    rw [DynamicCircuit.compile_seq, wp, hQ₂, h₁.wp_obs Q₂,
      Circuit.eval_seq, ← wpQAssignCompat_comp]
    exact restrict_wpQAssign_of_phasePerm h₁.phasePerm hdisj₁ (hQ₂ ▸ h₂.wp_obs Q)
theorem realizes [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {k m : ℕ}
    {rAct : QRegister k n} {rWork : QRegister m n} {M : Finset (Wire n)}
    {d : DynamicCircuit Var n} {c : Circuit n} {φ : BitAssignment n → ℂ}
    {f : BitAssignment n → BitAssignment n} (h : CleanPhasePerm rWork M d c φ f)
    (u : Unitary (2 ^ k)) (hkets : ∀ β : BitAssignment n, (∀ j : Fin m, β (rWork j) = 0) → φ β
    • basisKet (f β) = (rAct.embedUnitary u).1.mulVec (basisKet β)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d :=
  realizesEmbeddedUnitaryWithCleanWorkspace_of_kets rAct rWork u d c
    h.wp_const h.wp_obs fun β hz ↦ (h.phasePerm.eval_ket β).trans (hkets β hz)
end CleanPhasePerm
def wireListSum (ws : List (Wire n)) (β : BitAssignment n) : ℕ :=
  (ws.map fun w ↦ (β w).val).sum
@[simp] theorem wireListSum_nil (β : BitAssignment n) :
    wireListSum ([] : List (Wire n)) β = 0 := rfl
@[simp] theorem wireListSum_cons (w : Wire n) (ws : List (Wire n)) (β : BitAssignment n) :
    wireListSum (w :: ws) β = (β w).val + wireListSum ws β := rfl
theorem wireListSum_append (ws₁ ws₂ : List (Wire n)) (β : BitAssignment n) :
    wireListSum (ws₁ ++ ws₂) β = wireListSum ws₁ β + wireListSum ws₂ β := by
  simp [wireListSum, List.map_append, List.sum_append]
def optBitVal : Option (Wire n) → BitAssignment n → ℕ | none, _ => 0 | some w, β => (β w).val
def optWireOrZero (wZero : Wire n) : Option (Wire n) → Wire n | none => wZero | some w => w
@[simp] theorem optWireOrZero_val (wZero : Wire n) (ow : Option (Wire n)) (β : BitAssignment n)
    (hzero : β wZero = 0) : (β (optWireOrZero wZero ow)).val = optBitVal ow β := by
  cases ow
  · simp [optWireOrZero, optBitVal, hzero]
  · rfl
def tList : List (Wire n) → Circuit n | [] => .identity | w :: ws => Circuit.T w ;;ᶜ tList ws
def tDagList : List (Wire n) → Circuit n
  | [] => .identity | w :: ws => (Circuit.T w).inverse ;;ᶜ tDagList ws
def sList : List (Wire n) → Circuit n | [] => .identity | w :: ws => Circuit.S w ;;ᶜ sList ws
def sDagList : List (Wire n) → Circuit n
  | [] => .identity | w :: ws => (Circuit.S w).inverse ;;ᶜ sDagList ws
def zList : List (Wire n) → Circuit n | [] => .identity | w :: ws => Circuit.Z w ;;ᶜ zList ws
@[simp] theorem count_tList_toff (ws : List (Wire n)) : (tList ws).count .TOFF = 0 := by
  induction ws with | nil => rfl | cons _ _ ih => simpa [tList] using ih
@[simp] theorem count_tList_t (ws : List (Wire n)) : (tList ws).count .T = ws.length := by
  induction ws with | nil => rfl | cons _ _ ih => simp [tList, ih, Nat.add_comm]
@[simp] theorem count_tDagList_toff (ws : List (Wire n)) : (tDagList ws).count .TOFF = 0 := by
  induction ws with
  | nil => rfl | cons _ _ ih => simpa [tDagList, Circuit.inverseGate, Circuit.sequence] using ih
@[simp] theorem count_tDagList_t (ws : List (Wire n)) : (tDagList ws).count .T = ws.length := by
  induction ws with
  | nil => rfl
  | cons _ _ ih => simp [tDagList, Circuit.inverseGate, Circuit.sequence, ih, Nat.add_comm]
@[simp] theorem count_sList_toff (ws : List (Wire n)) : (sList ws).count .TOFF = 0 := by
  induction ws with | nil => rfl | cons _ _ ih => simpa [sList] using ih
@[simp] theorem count_sList_t (ws : List (Wire n)) : (sList ws).count .T = 0 := by
  induction ws with | nil => rfl | cons _ _ ih => simpa [sList] using ih
@[simp] theorem count_sDagList_toff (ws : List (Wire n)) : (sDagList ws).count .TOFF = 0 := by
  induction ws with
  | nil => rfl | cons _ _ ih => simpa [sDagList, Circuit.inverseGate, Circuit.sequence] using ih
@[simp] theorem count_sDagList_t (ws : List (Wire n)) : (sDagList ws).count .T = 0 := by
  induction ws with
  | nil => rfl | cons _ _ ih => simpa [sDagList, Circuit.inverseGate, Circuit.sequence] using ih
@[simp] theorem count_zList_toff (ws : List (Wire n)) : (zList ws).count .TOFF = 0 := by
  induction ws with | nil => rfl | cons _ _ ih => simpa [zList] using ih
@[simp] theorem count_zList_t (ws : List (Wire n)) : (zList ws).count .T = 0 := by
  induction ws with | nil => rfl | cons _ _ ih => simpa [zList] using ih
private theorem phasePerm_gateList (g : Wire n → Circuit n) (k : ℤ)
    (hg : ∀ w, PhasePerm ∅ (g w) (fun β ↦ dyadicTurn 7 (k * (β w).val)) id)
    (cL : List (Wire n) → Circuit n) (h0 : cL [] = Circuit.identity)
    (hc : ∀ w ws, cL (w :: ws) = g w ;;ᶜ cL ws) (ws : List (Wire n)) :
    PhasePerm ∅ (cL ws) (fun β ↦ dyadicTurn 7 (k * (wireListSum ws β : ℤ))) id := by
  induction ws with
  | nil =>
      rw [h0]
      exact PhasePerm.congr_phase (PhasePerm.identity ∅) fun _ ↦ by simp [dyadicTurn_zero]
  | cons w ws ih =>
      rw [hc]
      refine PhasePerm.congr_phase (PhasePerm.mono ((hg w).seq ih) (by simp)) fun β ↦ ?_
      dsimp only [id, wireListSum_cons]
      rw [dyadicTurn_add]
      refine congrArg (dyadicTurn 7) ?_
      push_cast
      ring
theorem phasePerm_tList (ws : List (Wire n)) :
    PhasePerm ∅ (tList ws) (fun β ↦ dyadicTurn 7 (16 * (wireListSum ws β : ℤ))) id :=
  phasePerm_gateList Circuit.T 16 PhasePerm.gateT tList rfl (fun _ _ ↦ rfl) ws
theorem phasePerm_tDagList (ws : List (Wire n)) :
    PhasePerm ∅ (tDagList ws) (fun β ↦ dyadicTurn 7 (-16 * (wireListSum ws β : ℤ))) id :=
  phasePerm_gateList (fun w ↦ (Circuit.T w).inverse) (-16) PhasePerm.gateTDag tDagList
    rfl (fun _ _ ↦ rfl) ws
theorem phasePerm_sList (ws : List (Wire n)) :
    PhasePerm ∅ (sList ws) (fun β ↦ dyadicTurn 7 (32 * (wireListSum ws β : ℤ))) id :=
  phasePerm_gateList Circuit.S 32 PhasePerm.gateS sList rfl (fun _ _ ↦ rfl) ws
theorem phasePerm_sDagList (ws : List (Wire n)) :
    PhasePerm ∅ (sDagList ws) (fun β ↦ dyadicTurn 7 (-32 * (wireListSum ws β : ℤ))) id :=
  phasePerm_gateList (fun w ↦ (Circuit.S w).inverse) (-32) PhasePerm.gateSDag sDagList
    rfl (fun _ _ ↦ rfl) ws
theorem phasePerm_zList (ws : List (Wire n)) :
    PhasePerm ∅ (zList ws) (fun β ↦ dyadicTurn 7 (64 * (wireListSum ws β : ℤ))) id :=
  phasePerm_gateList Circuit.Z 64 PhasePerm.gateZ zList rfl (fun _ _ ↦ rfl) ws
structure BucketOut (n : ℕ) where
  sumWire : Option (Wire n)
  carries : List (Wire n)
  steps : List (SymTempAndStep n)
theorem mem_cons3_of_mem_cons {α : Type*} {a b c x : α} {rest : List α}
    (hx : x ∈ a :: rest) : x ∈ a :: b :: c :: rest :=
  (List.mem_cons.mp hx).elim (fun e ↦ e ▸ List.mem_cons_self) fun h ↦
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
def reduceBucketAux {m_anc : ℕ} (rAnc : QRegister m_anc n) : (fuel : ℕ) →
    (B : List (Wire n)) → (offset : ℕ) → (hfuel : B.length ≤ fuel) →
    (hfit : offset + B.length / 2 ≤ m_anc) → (hnodup : B.Nodup) →
    (hanc_disj : ∀ x ∈ B, ∀ k, offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩) → BucketOut n
  | 0, B, _, hfuel, _, _, _ => match B, hfuel with | [], _ => ⟨none, [], []⟩
  | _ + 1, [], _, _, _, _, _ => ⟨none, [], []⟩
  | _ + 1, [a], _, _, _, _, _ => ⟨some a, [], []⟩
  | _ + 1, [a, b], offset, _, hfit, hnodup, hanc_disj =>
      have hlt0 : offset < m_anc := by
        simp only [List.length_cons, List.length_nil] at hfit
        omega
      let anc0 := rAnc ⟨offset, hlt0⟩
      ⟨some a, [anc0], [halfAdderSymStep a b anc0
        (fun h ↦ (List.nodup_cons.mp hnodup).1 (by simp [h]))
        (hanc_disj a (by simp) offset (le_refl _) hlt0)
        (hanc_disj b (by simp) offset (le_refl _) hlt0)]⟩
  | fuel + 1, a :: b :: c :: rest, offset, hfuel, hfit, hnodup, hanc_disj =>
      have hcons1 := List.nodup_cons.mp hnodup
      have hcons2 := List.nodup_cons.mp hcons1.2
      have hlt0 : offset < m_anc := by
        simp only [List.length_cons] at hfit
        omega
      let anc0 := rAnc ⟨offset, hlt0⟩
      let step0 := fullAdderSymStep a b c anc0 (fun h ↦ hcons1.1 (by simp [h]))
        (fun h ↦ hcons1.1 (by simp [h])) (hanc_disj a (by simp) offset (le_refl _) hlt0)
        (fun h ↦ hcons2.1 (by simp [h])) (hanc_disj b (by simp) offset (le_refl _) hlt0)
        (hanc_disj c (by simp) offset (le_refl _) hlt0)
      let sub := reduceBucketAux rAnc fuel (a :: rest) (offset + 1)
        (by simp only [List.length_cons] at hfuel ⊢
            omega)
        (by simp only [List.length_cons] at hfit ⊢
            omega)
        (List.nodup_cons.mpr ⟨fun hx ↦ hcons1.1 (by simp [hx]),
          (List.nodup_cons.mp hcons2.2).2⟩)
        (fun x hx k hk hkm ↦ hanc_disj x (mem_cons3_of_mem_cons hx) k (by omega) hkm)
      ⟨sub.sumWire, anc0 :: sub.carries, step0 :: sub.steps⟩
def reduceBucket {m_anc : ℕ} (rAnc : QRegister m_anc n) (B : List (Wire n)) (offset : ℕ)
    (hfit : offset + B.length / 2 ≤ m_anc) (hnodup : B.Nodup) (hanc_disj : ∀ x ∈ B, ∀ k,
    offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩) : BucketOut n :=
  reduceBucketAux rAnc B.length B offset (le_refl _) hfit hnodup hanc_disj
theorem symStepFwdList_outside (steps : List (SymTempAndStep n)) (β : BitAssignment n)
    (w : Wire n) (hw : ∀ s ∈ steps, w ∉ s.S) : symStepFwdList steps β w = β w := by
  induction steps generalizing β with
  | nil => rfl
  | cons s _ ih =>
      rw [symStepFwdList, ih _ fun s' hs' ↦ hw s' (by simp [hs']),
        s.stepFwd_outside β (hw s (by simp))]
private lemma step0_valid {m_anc : ℕ} (M : Finset (Wire n)) (rAnc : QRegister m_anc n)
    (hdisj_anc_M : Disjoint rAnc.image M) (B : List (Wire n)) (offset : ℕ)
    (hlt0 : offset < m_anc)
    (hanc_disj : ∀ x ∈ B, ∀ k, offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩)
    (hB_M : ∀ x ∈ B, x ∉ M) (s : SymTempAndStep n)
    (hS : ∀ q ∈ s.S, q ∈ B ∨ q = rAnc ⟨offset, hlt0⟩) :
    Disjoint s.S M ∧ ∀ j : Fin m_anc, offset < j.val → rAnc j ∉ s.S := by
  refine ⟨Finset.disjoint_left.mpr fun q hq ↦ ?_, fun j hj hmem ↦ ?_⟩
  · rcases hS q hq with hqB | rfl
    · exact hB_M q hqB
    · exact Finset.disjoint_left.mp hdisj_anc_M ((QRegister.mem_image rAnc _).mpr ⟨_, rfl⟩)
  · rcases hS (rAnc j) hmem with hjB | heq
    · exact hanc_disj _ hjB j.val (by omega) j.isLt rfl
    · have hv := congrArg Fin.val (rAnc.wires.injective heq)
      dsimp at hv
      omega
theorem reduceBucketAux_spec {m_anc : ℕ} (M : Finset (Wire n)) (rAnc : QRegister m_anc n)
    (hdisj_anc_M : Disjoint rAnc.image M) (fuel : ℕ) (B : List (Wire n)) (offset : ℕ)
    (hfuel : B.length ≤ fuel) (hfit : offset + B.length / 2 ≤ m_anc) (hnodup : B.Nodup)
    (hanc_disj : ∀ x ∈ B, ∀ k, offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩)
    (hB_M : ∀ x ∈ B, x ∉ M) :
    let out := reduceBucketAux rAnc fuel B offset hfuel hfit hnodup hanc_disj
    out.steps.length = B.length / 2 ∧ out.carries.length = B.length / 2 ∧ out.carries.Nodup ∧
    (∀ c ∈ out.carries, ∃ k, ∃ hk : k < m_anc,
      offset ≤ k ∧ k < offset + B.length / 2 ∧ c = rAnc ⟨k, hk⟩) ∧
    (∀ w, out.sumWire = some w → w ∈ B) ∧ ValidSymStepList M rAnc offset out.steps ∧
    (∀ s ∈ out.steps, ∀ w ∈ s.S, w ∈ B ∨ w ∈ out.carries) ∧
    (∀ β : BitAssignment n, (∀ k, offset ≤ k → (hk : k < m_anc) → β (rAnc ⟨k, hk⟩) = 0) →
      optBitVal out.sumWire (symStepFwdList out.steps β) +
        2 * wireListSum out.carries (symStepFwdList out.steps β) = wireListSum B β) := by
  induction fuel generalizing B offset with
  | zero =>
      cases B with
      | nil => simp [reduceBucketAux, ValidSymStepList, optBitVal, wireListSum]
      | cons _ _ => simp at hfuel
  | succ fuel ih =>
      match B with
      | [] => simp [reduceBucketAux, ValidSymStepList, optBitVal, wireListSum]
      | [a] => simp [reduceBucketAux, ValidSymStepList, optBitVal, wireListSum]
      | [a, b] =>
          have hlt0 : offset < m_anc := by
            simp at hfit
            omega
          let anc0 := rAnc ⟨offset, hlt0⟩
          have hab : a ≠ b := fun h ↦ (List.nodup_cons.mp hnodup).1 (by simp [h])
          have ha_anc : a ≠ anc0 := hanc_disj a (by simp) offset (le_refl _) hlt0
          have hb_anc : b ≠ anc0 := hanc_disj b (by simp) offset (le_refl _) hlt0
          let step0 := halfAdderSymStep a b anc0 hab ha_anc hb_anc
          have hS0 : ∀ q ∈ step0.S, q ∈ [a, b] ∨ q = anc0 := fun q hq ↦ by
            change q ∈ ({a, b, anc0} : Finset (Wire n)) at hq
            simpa [or_assoc] using hq
          obtain ⟨hdisj_SM, hlat⟩ :=
            step0_valid M rAnc hdisj_anc_M [a, b] offset hlt0 hanc_disj hB_M step0 hS0
          have hdef_ab :
              reduceBucketAux rAnc (fuel + 1) [a, b] offset hfuel hfit hnodup hanc_disj =
                ⟨some a, [anc0], [step0]⟩ := rfl
          dsimp only
          rw [hdef_ab]
          refine ⟨by simp, by simp, by simp, ?_, by simp, ⟨hlt0, rfl, hdisj_SM, hlat, trivial⟩,
            ?_, fun β hzero ↦ ?_⟩
          · rintro c hc
            simp only [List.mem_singleton] at hc
            exact ⟨offset, hlt0, le_refl _, by simp, hc⟩
          · rintro s hs q hq
            simp only [List.mem_singleton] at hs
            subst hs
            simpa [List.mem_singleton] using hS0 q hq
          · have h0 := hzero offset (le_refl _) hlt0
            simp only [symStepFwdList, step0,
              halfAdderSymStep_stepFwd a b anc0 hab ha_anc hb_anc β h0,
              optBitVal, wireListSum_cons, wireListSum_nil, add_zero, Function.update_self,
              Function.update_of_ne ha_anc]
            exact zmod2_half_adder_val (β a) (β b)
      | a :: b :: c :: rest =>
          have hcons1 := List.nodup_cons.mp hnodup
          have hcons2 := List.nodup_cons.mp hcons1.2
          have hcons3 := List.nodup_cons.mp hcons2.2
          have hab : a ≠ b := fun h ↦ hcons1.1 (by simp [h])
          have hac : a ≠ c := fun h ↦ hcons1.1 (by simp [h])
          have hbc : b ≠ c := fun h ↦ hcons2.1 (by simp [h])
          have hlt0 : offset < m_anc := by
            simp only [List.length_cons] at hfit
            omega
          let anc0 := rAnc ⟨offset, hlt0⟩
          have ha_anc : a ≠ anc0 := hanc_disj a (by simp) offset (le_refl _) hlt0
          have hb_anc : b ≠ anc0 := hanc_disj b (by simp) offset (le_refl _) hlt0
          have hc_anc : c ≠ anc0 := hanc_disj c (by simp) offset (le_refl _) hlt0
          let step0 := fullAdderSymStep a b c anc0 hab hac ha_anc hbc hb_anc hc_anc
          have hfuel' : (a :: rest).length ≤ fuel := by
            simp only [List.length_cons] at hfuel ⊢
            omega
          have hfit' : (offset + 1) + (a :: rest).length / 2 ≤ m_anc := by
            simp only [List.length_cons] at hfit ⊢
            omega
          have hnodup' : (a :: rest).Nodup :=
            List.nodup_cons.mpr ⟨fun hx ↦ hcons1.1 (by simp [hx]), hcons3.2⟩
          have hanc_disj' : ∀ x ∈ a :: rest, ∀ k, offset + 1 ≤ k → (hk : k < m_anc) →
              x ≠ rAnc ⟨k, hk⟩ :=
            fun x hx k hk hkm ↦ hanc_disj x (mem_cons3_of_mem_cons hx) k (by omega) hkm
          obtain ⟨hlen_s, hlen_c, hnodup_c, hmem_c, hsum_in, hvalid_sub, hS_sub, hval_sub⟩ :=
            ih (a :: rest) (offset + 1) hfuel' hfit' hnodup' hanc_disj'
              (fun x hx ↦ hB_M x (mem_cons3_of_mem_cons hx))
          let sub := reduceBucketAux rAnc fuel (a :: rest) (offset + 1) hfuel' hfit' hnodup'
            hanc_disj'
          have hdef_abc :
              reduceBucketAux rAnc (fuel + 1) (a :: b :: c :: rest) offset hfuel hfit hnodup
                hanc_disj = ⟨sub.sumWire, anc0 :: sub.carries, step0 :: sub.steps⟩ := rfl
          dsimp only
          rw [hdef_abc]
          have hhalf_eq : 1 + (a :: rest).length / 2 = (a :: b :: c :: rest).length / 2 := by
            simp only [List.length_cons]
            omega
          have hanc0_not_c : anc0 ∉ sub.carries := fun hmem ↦ by
            rcases hmem_c anc0 hmem with ⟨k, hk, hk_ge, _, heq⟩
            have hv := congrArg Fin.val (rAnc.wires.injective heq)
            dsimp at hv
            omega
          have hS0 : ∀ q ∈ step0.S, q ∈ a :: b :: c :: rest ∨ q = anc0 := fun q hq ↦ by
            simp only [step0, fullAdderSymStep, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            all_goals simp
          obtain ⟨hdisj_SM, hlat⟩ := step0_valid M rAnc hdisj_anc_M (a :: b :: c :: rest)
            offset hlt0 hanc_disj hB_M step0 hS0
          refine ⟨by rw [List.length_cons,
              show sub.steps.length = (a :: rest).length / 2 from hlen_s,
              Nat.add_comm, hhalf_eq],
            by rw [List.length_cons,
              show sub.carries.length = (a :: rest).length / 2 from hlen_c,
              Nat.add_comm, hhalf_eq],
            List.nodup_cons.mpr ⟨hanc0_not_c, hnodup_c⟩, ?_,
            fun q hq ↦ mem_cons3_of_mem_cons (hsum_in q hq),
            ⟨hlt0, rfl, hdisj_SM, hlat, hvalid_sub⟩, ?_, fun β hzero ↦ ?_⟩
          · rintro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact ⟨offset, hlt0, le_refl _, by omega, rfl⟩
            · rcases hmem_c x hx' with ⟨k, hk, hk_ge, hk_lt, rfl⟩
              exact ⟨k, hk, by omega, by omega, rfl⟩
          · rintro s hs q hq
            rcases List.mem_cons.mp hs with rfl | hs'
            · exact (hS0 q hq).imp_right fun h ↦ by simp [h]
            · exact (hS_sub s hs' q hq).imp mem_cons3_of_mem_cons (List.mem_cons_of_mem _)
          · let β₁ := step0.stepFwd β
            have hstep0_eq :=
              fullAdderSymStep_stepFwd a b c anc0 hab hac ha_anc hbc hb_anc hc_anc
                β (hzero offset (le_refl _) hlt0)
            have hzero₁ : ∀ k, offset + 1 ≤ k → (hk : k < m_anc) → β₁ (rAnc ⟨k, hk⟩) = 0 :=
              fun k hk hkm ↦ by
                have hne_anc0 : rAnc ⟨k, hkm⟩ ≠ anc0 := fun heq ↦ by
                  have hv := congrArg Fin.val (rAnc.wires.injective heq)
                  dsimp at hv
                  omega
                rw [show β₁ = _ from hstep0_eq, Function.update_of_ne hne_anc0,
                  Function.update_of_ne (hanc_disj a (by simp) k (by omega) hkm).symm]
                exact hzero k (by omega) hkm
            have hrest_eq : wireListSum rest β₁ = wireListSum rest β :=
              congrArg List.sum <| List.map_congr_left fun x hx ↦ congrArg ZMod.val <| by
                rw [show β₁ = _ from hstep0_eq,
                  Function.update_of_ne (hanc_disj x (by simp [hx]) offset (le_refl _) hlt0),
                  Function.update_of_ne (fun h ↦ hcons1.1 (by simp [← h, hx]))]
            have hanc0_out : symStepFwdList sub.steps β₁ anc0 = β₁ anc0 :=
              symStepFwdList_outside sub.steps β₁ anc0 fun s hs hmem ↦
                (hS_sub s hs anc0 hmem).elim
                  (fun hB ↦
                    hanc_disj anc0 (mem_cons3_of_mem_cons hB) offset (le_refl _) hlt0 rfl)
                  hanc0_not_c
            have hih_val := hval_sub β₁ hzero₁
            simp only [wireListSum_cons, hrest_eq] at hih_val ⊢
            have ha₁ : β₁ a = β a + β b + β c := by
              rw [show β₁ = _ from hstep0_eq, Function.update_of_ne ha_anc,
                Function.update_self]
            have hanc₁ : β₁ anc0 = β c + (β a + β c) * (β b + β c) := by
              rw [show β₁ = _ from hstep0_eq, Function.update_self]
            rw [ha₁] at hih_val
            simp only [symStepFwdList]
            change optBitVal sub.sumWire (symStepFwdList sub.steps β₁) +
              2 * ((symStepFwdList sub.steps β₁ anc0).val +
                wireListSum sub.carries (symStepFwdList sub.steps β₁)) = _
            rw [hanc0_out, hanc₁]
            linarith [zmod2_full_adder_val (β a) (β b) (β c)]
theorem reduceBucket_spec {m_anc : ℕ} (M : Finset (Wire n)) (rAnc : QRegister m_anc n)
    (hdisj_anc_M : Disjoint rAnc.image M) (B : List (Wire n)) (offset : ℕ)
    (hfit : offset + B.length / 2 ≤ m_anc) (hnodup : B.Nodup)
    (hanc_disj : ∀ x ∈ B, ∀ k, offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩)
    (hB_M : ∀ x ∈ B, x ∉ M) :
    let out := reduceBucket rAnc B offset hfit hnodup hanc_disj
    out.steps.length = B.length / 2 ∧ out.carries.length = B.length / 2 ∧ out.carries.Nodup ∧
    (∀ c ∈ out.carries, ∃ k, ∃ hk : k < m_anc,
      offset ≤ k ∧ k < offset + B.length / 2 ∧ c = rAnc ⟨k, hk⟩) ∧
    (∀ w, out.sumWire = some w → w ∈ B) ∧ ValidSymStepList M rAnc offset out.steps ∧
    (∀ s ∈ out.steps, ∀ w ∈ s.S, w ∈ B ∨ w ∈ out.carries) ∧
    (∀ β : BitAssignment n, (∀ k, offset ≤ k → (hk : k < m_anc) → β (rAnc ⟨k, hk⟩) = 0) →
      optBitVal out.sumWire (symStepFwdList out.steps β) +
        2 * wireListSum out.carries (symStepFwdList out.steps β) = wireListSum B β) :=
  reduceBucketAux_spec M rAnc hdisj_anc_M B.length B offset (le_refl _) hfit hnodup hanc_disj
    hB_M
def compressStepsCount : List (List (Wire n)) → ℕ → ℕ
  | [], _ => 0
  | B :: rest, inCarryLen =>
      let s := (B.length + inCarryLen) / 2
      s + compressStepsCount rest s
def weightedBucketsVal : List (List (Wire n)) → BitAssignment n → ℕ
  | [], _ => 0
  | B :: rest, β => wireListSum B β + 2 * weightedBucketsVal rest β
def weightedOptWiresVal : List (Option (Wire n)) → BitAssignment n → ℕ
  | [], _ => 0
  | ow :: rest, β => optBitVal ow β + 2 * weightedOptWiresVal rest β
structure CompressOut (n : ℕ) where
  sumWires : List (Option (Wire n))
  carries : List (Wire n)
  steps : List (SymTempAndStep n)
def compressBucketsAux {m_anc : ℕ} (rAnc : QRegister m_anc n) :
    (buckets : List (List (Wire n))) → (inCarries : List (Wire n)) → (offset : ℕ) →
    (hfit : offset + compressStepsCount buckets inCarries.length ≤ m_anc) → (hB_nodup : ∀ B ∈
      buckets, B.Nodup) → (hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) →
    (hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rAnc.image) → (hin_nodup : inCarries.Nodup) →
    (hin_anc : ∀ c ∈ inCarries, ∃ k, ∃ hk : k < m_anc, k < offset ∧ c = rAnc ⟨k, hk⟩) →
    CompressOut n
  | [], inCarries, _, _, _, _, _, _, _ => ⟨[], inCarries, []⟩
  | B :: rest, inCarries, offset, hfit, hB_nodup, hB_disj, hB_anc, hin_nodup, hin_anc =>
      let fullB := B ++ inCarries
      have hfit1 : offset + fullB.length / 2 ≤ m_anc := by
        simp only [fullB, List.length_append, compressStepsCount] at hfit ⊢
        omega
      have hfull_nodup : fullB.Nodup := List.nodup_append.mpr ⟨hB_nodup B (by simp), hin_nodup,
        fun x hxB _ hy heq ↦ by
          rcases hin_anc x (heq ▸ hy) with ⟨k, hk, _, rfl⟩
          exact hB_anc B (by simp) _ hxB ((rAnc.mem_image _).mpr ⟨⟨k, hk⟩, rfl⟩)⟩
      have hfull_anc_disj :
          ∀ x ∈ fullB, ∀ k, offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩ :=
        fun x hx k hk_ge hkm heq ↦ (List.mem_append.mp hx).elim
          (fun hxB ↦ hB_anc B (by simp) _ (heq ▸ hxB) ((rAnc.mem_image _).mpr ⟨⟨k, hkm⟩, rfl⟩))
          fun hxc ↦ by
            rcases hin_anc x hxc with ⟨k₀, hk₀, hk₀_lt, rfl⟩
            have hv := congrArg Fin.val (rAnc.wires.injective heq)
            dsimp at hv
            omega
      let r1 := reduceBucket rAnc fullB offset hfit1 hfull_nodup hfull_anc_disj
      have hr1 := reduceBucket_spec ∅ rAnc (by simp) fullB offset hfit1 hfull_nodup
        hfull_anc_disj (by simp)
      let rRest := compressBucketsAux rAnc rest r1.carries (offset + fullB.length / 2)
        (by rw [show r1.carries.length = (B.length + inCarries.length) / 2 by
              simpa [fullB, List.length_append] using hr1.2.1]
            simpa [fullB, List.length_append, compressStepsCount, add_assoc] using hfit)
        (fun B' hB' ↦ hB_nodup B' (by simp [hB'])) (List.pairwise_cons.mp hB_disj).2
        (fun B' hB' ↦ hB_anc B' (by simp [hB'])) hr1.2.2.1 fun c hc ↦
          let ⟨k, hk, _, hk_lt, heq⟩ := hr1.2.2.2.1 c hc
          ⟨k, hk, hk_lt, heq⟩
      ⟨r1.sumWire :: rRest.sumWires, rRest.carries, r1.steps ++ rRest.steps⟩
def compressBuckets {m_anc : ℕ} (rAnc : QRegister m_anc n) (buckets : List (List (Wire n)))
    (offset : ℕ) (hfit : offset + compressStepsCount buckets 0 ≤ m_anc) (hB_nodup : ∀ B ∈
    buckets, B.Nodup) (hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂)
    (hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rAnc.image) : CompressOut n :=
  compressBucketsAux rAnc buckets [] offset hfit hB_nodup hB_disj hB_anc List.nodup_nil
    fun _ h ↦ by simp at h
theorem compressBucketsAux_spec {m_anc : ℕ} (M : Finset (Wire n)) (rAnc : QRegister m_anc n)
    (hdisj_anc_M : Disjoint rAnc.image M) (buckets : List (List (Wire n)))
    (inCarries : List (Wire n)) (offset : ℕ)
    (hfit : offset + compressStepsCount buckets inCarries.length ≤ m_anc)
    (hB_nodup : ∀ B ∈ buckets, B.Nodup)
    (hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂)
    (hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rAnc.image)
    (hB_M : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ M) (hin_nodup : inCarries.Nodup)
    (hin_anc : ∀ c ∈ inCarries, ∃ k, ∃ hk : k < m_anc, k < offset ∧ c = rAnc ⟨k, hk⟩) :
    let out := compressBucketsAux rAnc buckets inCarries offset hfit hB_nodup hB_disj hB_anc
      hin_nodup hin_anc
    let totalSteps := compressStepsCount buckets inCarries.length
    out.sumWires.length = buckets.length ∧ out.steps.length = totalSteps ∧ out.carries.Nodup ∧
    (∀ c ∈ out.carries, ∃ k, ∃ hk : k < m_anc, k < offset + totalSteps ∧ c = rAnc ⟨k, hk⟩) ∧
    (∀ ow ∈ out.sumWires, ∀ w, ow = some w → w ∈ inCarries ∨ (∃ B ∈ buckets, w ∈ B) ∨
      ∃ k, ∃ hk : k < m_anc, offset ≤ k ∧ k < offset + totalSteps ∧ w = rAnc ⟨k, hk⟩) ∧
    ValidSymStepList M rAnc offset out.steps ∧
    (∀ s ∈ out.steps, ∀ w ∈ s.S, w ∈ inCarries ∨ (∃ B ∈ buckets, w ∈ B) ∨
      ∃ k, ∃ hk : k < m_anc, offset ≤ k ∧ k < offset + totalSteps ∧ w = rAnc ⟨k, hk⟩) ∧
    (∀ β : BitAssignment n, (∀ k, offset ≤ k → (hk : k < m_anc) → β (rAnc ⟨k, hk⟩) = 0) →
      weightedOptWiresVal out.sumWires (symStepFwdList out.steps β) +
        2 ^ buckets.length * wireListSum out.carries (symStepFwdList out.steps β) =
      weightedBucketsVal buckets β + wireListSum inCarries β) := by
  induction buckets generalizing inCarries offset with
  | nil =>
      refine ⟨rfl, rfl, hin_nodup, fun c hc ↦ ?_, by simp [compressBucketsAux], trivial,
        by simp [compressBucketsAux], fun β _ ↦ by
          simp [compressBucketsAux, weightedOptWiresVal, weightedBucketsVal]⟩
      rcases hin_anc c hc with ⟨k, hk, hk_lt, rfl⟩
      exact ⟨k, hk, by simpa [compressStepsCount] using hk_lt, rfl⟩
  | cons B rest ih =>
      let fullB := B ++ inCarries
      have hfit1 : offset + fullB.length / 2 ≤ m_anc := by
        simp only [fullB, List.length_append, compressStepsCount] at hfit ⊢
        omega
      have hfull_nodup : fullB.Nodup := List.nodup_append.mpr ⟨hB_nodup B (by simp), hin_nodup,
        fun x hxB _ hy heq ↦ by
          rcases hin_anc x (heq ▸ hy) with ⟨k, hk, _, rfl⟩
          exact hB_anc B (by simp) _ hxB ((QRegister.mem_image rAnc _).mpr ⟨⟨k, hk⟩, rfl⟩)⟩
      have hfull_anc_disj :
          ∀ x ∈ fullB, ∀ k, offset ≤ k → (hk : k < m_anc) → x ≠ rAnc ⟨k, hk⟩ :=
        fun x hx k hk_ge hkm heq ↦ by
          rcases List.mem_append.mp hx with hxB | hxc
          · exact hB_anc B (by simp) _ (heq ▸ hxB) ((QRegister.mem_image rAnc _).mpr ⟨_, rfl⟩)
          · rcases hin_anc x hxc with ⟨k₀, hk₀, hk₀_lt, rfl⟩
            have hv := congrArg Fin.val (rAnc.wires.injective heq)
            dsimp at hv
            omega
      have hfull_M : ∀ x ∈ fullB, x ∉ M := fun x hx ↦
        (List.mem_append.mp hx).elim (hB_M B (by simp) x) fun hxc ↦ by
          rcases hin_anc x hxc with ⟨_, _, _, rfl⟩
          exact Finset.disjoint_left.mp hdisj_anc_M ((QRegister.mem_image rAnc _).mpr ⟨_, rfl⟩)
      let r1 := reduceBucket rAnc fullB offset hfit1 hfull_nodup hfull_anc_disj
      have hr1 := reduceBucket_spec M rAnc hdisj_anc_M fullB offset hfit1 hfull_nodup
        hfull_anc_disj hfull_M
      have hlen_c : r1.carries.length = (B.length + inCarries.length) / 2 := by
        simpa [fullB, List.length_append] using hr1.2.1
      have hfit_rest :
          (offset + fullB.length / 2) + compressStepsCount rest r1.carries.length ≤ m_anc := by
        rw [hlen_c]
        simpa [fullB, List.length_append, compressStepsCount, add_assoc] using hfit
      have hin_anc' : ∀ c ∈ r1.carries, ∃ k, ∃ hk : k < m_anc,
          k < offset + fullB.length / 2 ∧ c = rAnc ⟨k, hk⟩ := fun c hc ↦ by
        rcases hr1.2.2.2.1 c hc with ⟨k, hk, _, hk_lt, rfl⟩
        exact ⟨k, hk, hk_lt, rfl⟩
      have hpair := List.pairwise_cons.mp hB_disj
      obtain ⟨hlen_sw, hlen_st, hnodup_c, hmem_c, hmem_sw, hvalid_rest, hS_rest, hval_rest⟩ :=
        ih r1.carries (offset + fullB.length / 2) hfit_rest
          (fun B' hB' ↦ hB_nodup B' (by simp [hB'])) hpair.2
          (fun B' hB' ↦ hB_anc B' (by simp [hB'])) (fun B' hB' ↦ hB_M B' (by simp [hB']))
          hr1.2.2.1 hin_anc'
      let rRest := compressBucketsAux rAnc rest r1.carries (offset + fullB.length / 2) hfit_rest
        (fun B' hB' ↦ hB_nodup B' (by simp [hB'])) hpair.2
        (fun B' hB' ↦ hB_anc B' (by simp [hB'])) hr1.2.2.1 hin_anc'
      have htot_eq : fullB.length / 2 + compressStepsCount rest r1.carries.length =
          compressStepsCount (B :: rest) inCarries.length := by
        simp [fullB, List.length_append, compressStepsCount, hlen_c]
      have hdef_out : compressBucketsAux rAnc (B :: rest) inCarries offset hfit hB_nodup
          hB_disj hB_anc hin_nodup hin_anc =
          ⟨r1.sumWire :: rRest.sumWires, rRest.carries, r1.steps ++ rRest.steps⟩ := rfl
      have hlift_sub {w : Wire n}
          (h : w ∈ r1.carries ∨ (∃ B' ∈ rest, w ∈ B') ∨
            ∃ k, ∃ hk : k < m_anc, offset + fullB.length / 2 ≤ k ∧
              k < (offset + fullB.length / 2) + compressStepsCount rest r1.carries.length ∧
              w = rAnc ⟨k, hk⟩) :
          w ∈ inCarries ∨ (∃ B' ∈ B :: rest, w ∈ B') ∨
            ∃ k, ∃ hk : k < m_anc, offset ≤ k ∧
              k < offset + compressStepsCount (B :: rest) inCarries.length ∧
              w = rAnc ⟨k, hk⟩ := by
        rcases h with hwc | ⟨B', hB', hwB'⟩ | ⟨k, hk, hk_ge, hk_lt, rfl⟩
        · rcases hr1.2.2.2.1 w hwc with ⟨k, hk, hk_ge, hk_lt, rfl⟩
          exact Or.inr (Or.inr ⟨k, hk, hk_ge, by
            rw [← htot_eq]
            omega, rfl⟩)
        · exact Or.inr (Or.inl ⟨B', by simp [hB'], hwB'⟩)
        · exact Or.inr (Or.inr ⟨k, hk, by omega, by
            rw [← htot_eq]
            omega, rfl⟩)
      refine ⟨by rw [hdef_out, List.length_cons, List.length_cons,
          show rRest.sumWires.length = rest.length from hlen_sw],
        by rw [hdef_out, List.length_append, hr1.1, hlen_st, htot_eq], hnodup_c,
        fun c hc ↦ ?_, fun ow how w hsome ↦ ?_,
        by rw [hdef_out, validSymStepList_append, hr1.1]
           exact ⟨hr1.2.2.2.2.2.1, hvalid_rest⟩,
        fun s hs w hw ↦ ?_, fun β hzero ↦ ?_⟩
      · rcases hmem_c c hc with ⟨k, hk, hk_lt, rfl⟩
        exact ⟨k, hk, by
          rw [← htot_eq]
          omega, rfl⟩
      · rcases List.mem_cons.mp (hdef_out ▸ how) with rfl | how
        · exact (List.mem_append.mp (hr1.2.2.2.2.1 w hsome)).elim
            (fun hwB ↦ Or.inr (Or.inl ⟨B, by simp, hwB⟩)) Or.inl
        · exact hlift_sub (hmem_sw ow how w hsome)
      · rcases List.mem_append.mp (hdef_out ▸ hs) with hs1 | hs2
        · rcases hr1.2.2.2.2.2.2.1 s hs1 w hw with h_in_B | h_in_c
          · exact (List.mem_append.mp h_in_B).elim
              (fun hwB ↦ Or.inr (Or.inl ⟨B, by simp, hwB⟩)) Or.inl
          · exact hlift_sub (Or.inl h_in_c)
        · exact hlift_sub (hS_rest s hs2 w hw)
      · let β₁ := symStepFwdList r1.steps β
        have hr1_out {x : Wire n} {s : SymTempAndStep n} (hs : s ∈ r1.steps) (hx : x ∈ s.S) :
            x ∈ B ∨ ∃ k₀, ∃ hk₀ : k₀ < m_anc, k₀ < offset + fullB.length / 2 ∧
              x = rAnc ⟨k₀, hk₀⟩ := by
          rcases hr1.2.2.2.2.2.2.1 s hs x hx with h_in_B | h_in_c
          · exact (List.mem_append.mp h_in_B).elim Or.inl fun hxc ↦
              let ⟨k₀, hk₀, _, heq⟩ := hin_anc x hxc
              Or.inr ⟨k₀, hk₀, by omega, heq⟩
          · exact Or.inr (hin_anc' x h_in_c)
        have hzero₁ : ∀ k, offset + fullB.length / 2 ≤ k → (hk : k < m_anc) →
            β₁ (rAnc ⟨k, hk⟩) = 0 := fun k hk_ge hkm ↦ by
          dsimp only [β₁]
          rw [symStepFwdList_outside r1.steps β _ fun s hs hmem ↦ by
            rcases hr1_out hs hmem with hxB | ⟨k₀, hk₀, hk₀_lt, heq⟩
            · exact hB_anc B (by simp) _ hxB ((rAnc.mem_image _).mpr ⟨_, rfl⟩)
            · have hv := congrArg Fin.val (rAnc.wires.injective heq)
              dsimp at hv
              omega]
          exact hzero k (by omega) hkm
        have hb_eq : ∀ B' ∈ rest, wireListSum B' β₁ = wireListSum B' β := fun B' hB' ↦
          congrArg List.sum <| List.map_congr_left fun x hx ↦ congrArg ZMod.val <|
            symStepFwdList_outside r1.steps β x fun s hs hmem ↦ by
              rcases hr1_out hs hmem with hxB | ⟨_, _, _, rfl⟩
              · exact hpair.1 B' hB' x hxB hx
              · exact hB_anc B' (by simp [hB']) _ hx ((rAnc.mem_image _).mpr ⟨_, rfl⟩)
        have hrest_eq : weightedBucketsVal rest β₁ = weightedBucketsVal rest β := by
          clear * - hb_eq
          induction rest with
          | nil => rfl
          | cons B' rs ihr =>
              simp only [weightedBucketsVal, hb_eq B' (by simp),
                ihr fun B'' hB'' ↦ hb_eq B'' (by simp [hB''])]
        have hsum0_preserve :
            optBitVal r1.sumWire (symStepFwdList rRest.steps β₁) = optBitVal r1.sumWire β₁ := by
          cases hsw : r1.sumWire with
          | none => rfl
          | some w0 =>
              refine congrArg ZMod.val (symStepFwdList_outside rRest.steps β₁ w0 fun s hs hmem ↦ ?_)
              have hw0_fb := hr1.2.2.2.2.1 w0 hsw
              rcases hS_rest s hs w0 hmem with hwc2 | ⟨B', hB', hwB'⟩ | ⟨k₂, hk₂, _, _, rfl⟩
              · rcases hr1.2.2.2.1 w0 hwc2 with ⟨k₂, hk₂, hk₂_ge, _, rfl⟩
                exact hfull_anc_disj _ hw0_fb k₂ hk₂_ge hk₂ rfl
              · rcases List.mem_append.mp hw0_fb with hwB0 | hwc0
                · exact hpair.1 B' hB' w0 hwB0 hwB'
                · rcases hin_anc w0 hwc0 with ⟨_, _, _, rfl⟩
                  exact hB_anc B' (by simp [hB']) _ hwB' ((rAnc.mem_image _).mpr ⟨_, rfl⟩)
              · exact hfull_anc_disj _ hw0_fb k₂ (by omega) hk₂ rfl
        have hr1_val : optBitVal r1.sumWire β₁ + 2 * wireListSum r1.carries β₁ =
            wireListSum B β + wireListSum inCarries β := by
          simpa only [β₁, fullB, wireListSum_append] using hr1.2.2.2.2.2.2.2 β hzero
        have hih_val := hval_rest β₁ hzero₁
        rw [hdef_out]
        simp only [weightedOptWiresVal, weightedBucketsVal, List.length_cons,
          symStepFwdList_append r1.steps rRest.steps β, pow_succ', mul_assoc]
        linarith [hih_val, hrest_eq, hr1_val, hsum0_preserve]
theorem compressBuckets_spec {m_anc : ℕ} (M : Finset (Wire n)) (rAnc : QRegister m_anc n)
    (hdisj_anc_M : Disjoint rAnc.image M) (buckets : List (List (Wire n))) (offset : ℕ)
    (hfit : offset + compressStepsCount buckets 0 ≤ m_anc) (hB_nodup : ∀ B ∈ buckets, B.Nodup)
    (hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) (hB_anc : ∀ B ∈ buckets, ∀ x ∈ B,
      x ∉ rAnc.image) (hB_M : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ M) :
    let out := compressBuckets rAnc buckets offset hfit hB_nodup hB_disj hB_anc
    let totalSteps := compressStepsCount buckets 0
    out.sumWires.length = buckets.length ∧ out.steps.length = totalSteps ∧ out.carries.Nodup ∧
    (∀ c ∈ out.carries, ∃ k, ∃ hk : k < m_anc, k < offset + totalSteps ∧ c = rAnc ⟨k, hk⟩) ∧
    (∀ ow ∈ out.sumWires, ∀ w, ow = some w → (∃ B ∈ buckets, w ∈ B) ∨ ∃ k, ∃ hk : k < m_anc,
      offset ≤ k ∧ k < offset + totalSteps ∧ w = rAnc ⟨k, hk⟩) ∧ ValidSymStepList M rAnc offset
      out.steps ∧ (∀ s ∈ out.steps, ∀ w ∈ s.S, (∃ B ∈ buckets, w ∈ B) ∨ ∃ k, ∃ hk : k < m_anc,
      offset ≤ k ∧ k < offset + totalSteps ∧ w = rAnc ⟨k, hk⟩) ∧ (∀ β : BitAssignment n,
      (∀ k, offset ≤ k → (hk : k < m_anc) → β (rAnc ⟨k, hk⟩) = 0) → weightedOptWiresVal
      out.sumWires (symStepFwdList out.steps β) + 2 ^ buckets.length * wireListSum out.carries
      (symStepFwdList out.steps β) = weightedBucketsVal buckets β) := by
  have h := compressBucketsAux_spec M rAnc hdisj_anc_M buckets [] offset hfit
    hB_nodup hB_disj hB_anc hB_M List.nodup_nil (fun _ h ↦ by simp at h)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun ow how w hsome ↦ (h.2.2.2.2.1 ow how w hsome).elim (by simp) id,
    h.2.2.2.2.2.1, fun s hs w hw ↦ (h.2.2.2.2.2.2.1 s hs w hw).elim (by simp) id,
    fun β hzero ↦ by simpa [compressBuckets, wireListSum] using h.2.2.2.2.2.2.2 β hzero⟩
end CleanWorkspaceAndCatalystEngine
end DyadicQft64
end
end ModDyadicQft64Circuit

section ModDyadicQft64Engine
@[expose] public section
namespace DyadicQft64Engine
open Real Operator Matrix QProg HermitianMat
open KaratsubaQft64Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
noncomputable def phaseGradKet (b : ℕ) : Fin (2 ^ b) → ℂ := fun m ↦
  ((2 : ℝ) ^ (-(b : ℝ) / 2) : ℂ) * Complex.exp (-(2 * π * Complex.I * (m.val : ℂ)) / 2 ^ b)
noncomputable def turnPow2 (B : ℕ) (k : ℤ) : ℂ := DyadicQft64.dyadicTurn B k
@[simp] theorem turnPow2_zero (B : ℕ) : turnPow2 B 0 = 1 := DyadicQft64.dyadicTurn_zero B
theorem turnPow2_add (B : ℕ) (a b : ℤ) :
    turnPow2 B (a + b) = turnPow2 B a * turnPow2 B b := (DyadicQft64.dyadicTurn_add B a b).symm
theorem star_turnPow2_mul_self (B : ℕ) (k : ℤ) : star (turnPow2 B k) * turnPow2 B k = 1 :=
  DyadicQft64.star_dyadicTurn_mul_self B k
theorem turnPow2_add_period (B : ℕ) (a q : ℤ) :
    turnPow2 B (a + q * (2 ^ B : ℤ)) = turnPow2 B a := DyadicQft64.dyadicTurn_add_period B a q
theorem turnPow2_scale_pow (a b : ℕ) (k : ℤ) :
    turnPow2 (a + b) ((2 ^ a : ℤ) * k) = turnPow2 b k := by
  unfold turnPow2 DyadicQft64.dyadicTurn
  congr 1
  have hne : ((2 : ℂ) ^ a) ≠ 0 := pow_ne_zero a (by norm_num)
  rw [pow_add]
  push_cast
  field_simp [hne]
def sysCatEquiv (kSys B : ℕ) : Fin (2 ^ (kSys + B)) ≃ BitAssignment kSys × Fin (2 ^ B) :=
  DyadicQft64.splitSysCatEquiv kSys B
@[simp] theorem basisBits_sysCatEquiv_symm (kSys B : ℕ) (γ : BitAssignment kSys)
    (m : Fin (2 ^ B)) : basisBits (kSys + B) ((sysCatEquiv kSys B).symm (γ, m)) =
      Fin.addCases γ (basisBits B m) := funext <| Fin.addCases
  (fun i ↦ by
    rw [Fin.addCases_left]
    exact congrFun (congrArg Prod.fst ((sysCatEquiv kSys B).apply_symm_apply (γ, m))) i)
  (fun j ↦ by
    rw [Fin.addCases_right]
    exact congrFun ((basisBitsEquiv B).symm_apply_eq.mp
      (congrArg Prod.snd ((sysCatEquiv kSys B).apply_symm_apply (γ, m)))) j)
noncomputable def preDiag6 (b : Fin 2) : Unitary 64 :=
  ⟨Matrix.diagonal fun u : Fin 64 ↦ omega128 (karatsubaInExp128 b u), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_mul_omega128_self _)⟩
noncomputable def wireHadamard6 (m : Fin 6) : Unitary 64 :=
  (QRegister.singleton m : QRegister 1 6).embedUnitary Qubit.H
noncomputable def bit5Flip6 : Unitary 64 :=
  (QRegister.singleton (5 : Fin 6) : QRegister 1 6).embedUnitary Qubit.X
def stageRowExp128 (m : Fin 6) (w : Fin 64) : ℤ :=
  ∑ r ∈ Finset.filter (fun r : Fin 6 ↦ r.val < m.val) Finset.univ,
    ((2 ^ (5 - m.val + r.val) : ℕ) : ℤ) * (bitXor (bit6 w m) (bit6 w r) : ℤ)
noncomputable def stageDiag6 (m : Fin 6) : Unitary 64 :=
  ⟨Matrix.diagonal fun w : Fin 64 ↦ omega128 (stageRowExp128 m w), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ star_mul_omega128_self _)⟩
private lemma lemHex330 (m : Fin 6) (z w : Fin 64) : (wireHadamard6 m).1 z w = if ∀ r : Fin 6, r ≠
    m → bit6 z r = bit6 w r then (1 / (√2 : ℂ)) * omega128
    (64 * ((bit6 z m * bit6 w m : ℕ) : ℤ)) else 0 := by
  let reg : QRegister 1 6 := QRegister.singleton m
  have hb6 (a : Fin 64) (r : Fin 6) : (basisBits 6 a r).val = bit6 a r := by
    rw [basisBits_eq_div_mod]
    exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
  have hbit_iff : (reg.basisSplitEquiv z).2 = (reg.basisSplitEquiv w).2 ↔
      ∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r := by
    rw [reg.basisSplit_environment_eq_iff]
    refine ⟨fun h r hr ↦ ?_, fun h r hr ↦ ?_⟩
    · have hnot : r ∉ Set.range reg.wires := fun ⟨_, hi⟩ ↦ hr hi.symm
      simpa only [hb6] using congrArg ZMod.val (h r hnot)
    · apply ZMod.val_injective
      simpa only [hb6] using h r fun e ↦ hr ⟨0, e.symm⟩
  have hext_bit (a : Fin 64) : (reg.extractIndex a).val = bit6 a m := by
    have hfin : ∀ x : Fin 2, x.val = (basisBits 1 x 0).val := by decide
    rw [hfin, reg.basisBits_extractIndex]
    exact hb6 a m
  rw [wireHadamard6, QRegister.embedUnitary_val, reg.embedMatrix_apply]
  by_cases h : (reg.basisSplitEquiv z).2 = (reg.basisSplitEquiv w).2
  · rw [ite_eq_left h, ite_eq_left (hbit_iff.mp h), ← hext_bit z, ← hext_bit w]
    have ho64 : omega128 64 = -1 := by
      rw [omega128_def, show 2 * π * ((64 : ℤ) : ℂ) * Complex.I / 128 = π * Complex.I by
        push_cast
        ring, Complex.exp_pi_mul_I]
    generalize reg.extractIndex z = ez, reg.extractIndex w = ew
    fin_cases ez
    · fin_cases ew
      · simp [Qubit.H]
      · simp [Qubit.H]
    · fin_cases ew
      · simp [Qubit.H]
      · simp [Qubit.H, ho64]
  · simp [h, mt hbit_iff.mpr h]
private lemma lemHex331 {a b : Fin 64} (h : ∀ r : Fin 6, bit6 a r = bit6 b r) : a = b := by
  apply Fin.ext
  have ha := fin64_val_eq_bits a
  have hb := fin64_val_eq_bits b
  simp only [h] at ha
  linarith
private theorem lemHex332 (u : Fin 64) (kf : Fin 6) (Φ : Fin 64 → ℤ) (hΦ : ∀ w₁ w₂ : Fin 64, (∀ r
    : Fin 6, kf.val < r.val → bit6 w₁ r = bit6 w₂ r) → Φ w₁ = Φ w₂) (c : ℂ) : ((stageDiag6 kf
    * wireHadamard6 kf).1.mulVec fun w ↦ if ∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6
    u r then c * omega128 (Φ w) else 0) = fun z ↦ if ∀ r : Fin 6, r.val < kf.val → bit6 z r =
    bit6 u r then (c * (1 / (√2 : ℂ))) * omega128 (Φ z + (64 * ((bit6 z kf : ℤ) * (bit6 u kf :
    ℤ)) + ∑ r ∈ Finset.filter (fun r : Fin 6 ↦ r.val < kf.val) Finset.univ, ((2 ^ (5 - kf.val
    + r.val) : ℕ) : ℤ) * (bitXor (bit6 z kf) (bit6 u r) : ℤ))) else 0 := by
  let ψ_in : Fin 64 → ℂ := fun w ↦
    if ∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6 u r then c * omega128 (Φ w) else 0
  funext z
  change ((stageDiag6 kf * wireHadamard6 kf).1.mulVec ψ_in) z = _
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  change (Matrix.diagonal (fun w ↦ omega128 (stageRowExp128 kf w))).mulVec
      ((wireHadamard6 kf).1.mulVec ψ_in) z = _
  rw [Matrix.mulVec_diagonal, Matrix.mulVec, dotProduct]
  let bitsPre (r : Fin 6) : ZMod 2 := if r = kf then basisBits 6 u kf else basisBits 6 z r
  let wPre : Fin 64 := (basisBitsEquiv 6).symm bitsPre
  have hwPre_bit (r : Fin 6) : bit6 wPre r = if r = kf then bit6 u kf else bit6 z r := by
    have hb : basisBits 6 wPre r = bitsPre r :=
      congrFun ((basisBitsEquiv 6).apply_symm_apply bitsPre) r
    by_cases hrk : r = kf
    · subst hrk
      simpa [-Nat.reducePow, bitsPre, basisBits_eq_div_mod, bit6,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using congrArg ZMod.val hb
    · simpa [-Nat.reducePow, bitsPre, hrk, basisBits_eq_div_mod, bit6,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using congrArg ZMod.val hb
  have hwPre_hi : ∀ r : Fin 6, r ≠ kf → bit6 z r = bit6 wPre r := fun r hr ↦ by
    simp [hwPre_bit, hr]
  rw [Finset.sum_eq_single wPre (fun w _ hne ↦ by
    rw [lemHex330]
    by_cases hw_ag : ∀ r : Fin 6, r ≠ kf → bit6 z r = bit6 w r
    · have hnot : ¬(∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6 u r) := fun hw_low ↦
        hne (lemHex331 fun r ↦ by
          by_cases hrk : r = kf
          · simp [hrk, hwPre_bit, hw_low kf (Nat.lt_succ_self _)]
          · simp [hwPre_bit, hrk, (hw_ag r hrk).symm])
      rw [ite_eq_left hw_ag]
      dsimp only [ψ_in]
      rw [ite_eq_right hnot, mul_zero]
    · rw [ite_eq_right hw_ag, zero_mul]) (fun hm ↦ absurd (Finset.mem_univ _) hm),
    lemHex330, ite_eq_left hwPre_hi]
  by_cases hz_low : ∀ r : Fin 6, r.val < kf.val → bit6 z r = bit6 u r
  · have hwPre_low : ∀ r : Fin 6, r.val < kf.val + 1 → bit6 wPre r = bit6 u r := fun r hr ↦ by
      by_cases hrk : r = kf
      · simp [hwPre_bit, hrk]
      · simp [hwPre_bit, hrk, hz_low r (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hr)
          (fun e ↦ hrk (Fin.ext e)))]
    have hΦ_eq : Φ wPre = Φ z :=
      hΦ wPre z fun r hr ↦ (hwPre_hi r (fun e ↦ Nat.ne_of_gt hr (congrArg Fin.val e))).symm
    have hrow_eq : stageRowExp128 kf z =
        ∑ r ∈ Finset.filter (fun r : Fin 6 ↦ r.val < kf.val) Finset.univ,
          ((2 ^ (5 - kf.val + r.val) : ℕ) : ℤ) * (bitXor (bit6 z kf) (bit6 u r) : ℤ) :=
      Finset.sum_congr rfl fun r hr ↦ by rw [hz_low r (Finset.mem_filter.mp hr).2]
    dsimp only [ψ_in]
    rw [ite_eq_left hwPre_low, ite_eq_left hz_low, hΦ_eq,
      show bit6 wPre kf = bit6 u kf by simp [hwPre_bit], hrow_eq, omega128_add, omega128_add]
    push_cast
    ring
  · have hnot : ¬(∀ r : Fin 6, r.val < kf.val + 1 → bit6 wPre r = bit6 u r) := fun h ↦
      hz_low fun r hr ↦ by
        simpa [hwPre_bit, show r ≠ kf from fun e ↦ Nat.ne_of_lt hr (congrArg Fin.val e)] using
          h r (Nat.lt_succ_of_lt hr)
    dsimp only [ψ_in]
    rw [ite_eq_right hnot, ite_eq_right hz_low, mul_zero, mul_zero]
theorem sixStageKaratsuba64_eq_rawUnitary (b : Fin 2) : (wireHadamard6 0 * (stageDiag6 1 *
    wireHadamard6 1) * (stageDiag6 2 * wireHadamard6 2) * (stageDiag6 3 * wireHadamard6 3) *
    (stageDiag6 4 * wireHadamard6 4) * (stageDiag6 5 * wireHadamard6 5) * preDiag6 b).1 =
    karatsubaRawUnitary128 b := by
  ext z u
  have hcol (A : Matrix (Fin 64) (Fin 64) ℂ) : A z u = (A.mulVec (Pi.single u 1)) z := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine (hcol _).trans ?_
  let termExp (k : Fin 6) (w : Fin 64) : ℤ := 64 * ((bit6 w k : ℤ) * (bit6 u k : ℤ)) +
    ∑ r ∈ Finset.filter (fun r : Fin 6 ↦ r.val < k.val) Finset.univ,
      ((2 ^ (5 - k.val + r.val) : ℕ) : ℤ) * (bitXor (bit6 w k) (bit6 u r) : ℤ)
  let Φ (m : ℕ) (w : Fin 64) : ℤ := karatsubaInExp128 b u +
    ∑ k ∈ Finset.filter (fun k : Fin 6 ↦ m ≤ k.val) Finset.univ, termExp k w
  let vec (m : ℕ) : Fin 64 → ℂ := fun w ↦
    if ∀ r : Fin 6, r.val < m → bit6 w r = bit6 u r then
      ((1 / (√2 : ℂ)) ^ (6 - m)) * omega128 (Φ m w) else 0
  have hpre : (preDiag6 b).1.mulVec (Pi.single u 1) = vec 6 := by
    funext w
    dsimp only [preDiag6, vec, Φ]
    rw [Matrix.diagonal_mulVec_single,
      show Finset.filter (fun k : Fin 6 ↦ 6 ≤ k.val) Finset.univ = ∅ from
        Finset.filter_eq_empty_iff.mpr fun k _ ↦ by omega]
    by_cases hwu : w = u
    · subst hwu
      simp
    · simp [hwu, show ¬(∀ r : Fin 6, bit6 w r = bit6 u r) from fun h ↦ hwu (lemHex331 h)]
  have h0_diag : stageDiag6 0 = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [stageDiag6, stageRowExp128]
    · simp [stageDiag6, hij]
  have hstep (kf : Fin 6) :
      (stageDiag6 kf * wireHadamard6 kf).1.mulVec (vec (kf.val + 1)) = vec kf.val := by
    have hΦ_dep : ∀ w₁ w₂ : Fin 64,
        (∀ r : Fin 6, kf.val < r.val → bit6 w₁ r = bit6 w₂ r) →
        Φ (kf.val + 1) w₁ = Φ (kf.val + 1) w₂ := fun w₁ w₂ h ↦ by
      dsimp only [Φ]
      refine congrArg (karatsubaInExp128 b u + ·) (Finset.sum_congr rfl fun k hk ↦ ?_)
      dsimp only [termExp]
      rw [h k (Nat.lt_of_succ_le (Finset.mem_filter.mp hk).2)]
    rw [lemHex332 u kf (Φ (kf.val + 1)) hΦ_dep ((1 / (√2 : ℂ)) ^ (6 - (kf.val + 1)))]
    funext w
    dsimp only [vec]
    have hpow : (1 / (√2 : ℂ)) ^ (6 - (kf.val + 1)) * (1 / (√2 : ℂ)) =
        (1 / (√2 : ℂ)) ^ (6 - kf.val) := by
      rw [← pow_succ, show 6 - (kf.val + 1) + 1 = 6 - kf.val by omega]
    have hsum : Φ (kf.val + 1) w + termExp kf w = Φ kf.val w := by
      dsimp only [Φ]
      have hset : Finset.filter (fun k : Fin 6 ↦ kf.val ≤ k.val) Finset.univ =
          insert kf (Finset.filter (fun k : Fin 6 ↦ kf.val + 1 ≤ k.val) Finset.univ) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      ring
    rw [hpow]
    exact if_congr Iff.rfl (congrArg _ (congrArg omega128 hsum)) rfl
  have hprod : (wireHadamard6 0 * (stageDiag6 1 * wireHadamard6 1) * (stageDiag6 2 *
      wireHadamard6 2) * (stageDiag6 3 * wireHadamard6 3) * (stageDiag6 4 * wireHadamard6 4) *
      (stageDiag6 5 * wireHadamard6 5) * preDiag6 b).1.mulVec (Pi.single u 1) =
      (stageDiag6 0 * wireHadamard6 0).1.mulVec ((stageDiag6 1 * wireHadamard6 1).1.mulVec
      ((stageDiag6 2 * wireHadamard6 2).1.mulVec ((stageDiag6 3 * wireHadamard6 3).1.mulVec
      ((stageDiag6 4 * wireHadamard6 4).1.mulVec ((stageDiag6 5 * wireHadamard6 5).1.mulVec
      ((preDiag6 b).1.mulVec (Pi.single u 1))))))) := by
    rw [h0_diag, one_mul]
    simp only [Submonoid.coe_mul, mul_assoc, Matrix.mulVec_mulVec]
  have hs (k : Fin 6) (m m' : ℕ) (hm : k.val + 1 = m) (hm' : k.val = m') :
      (stageDiag6 k * wireHadamard6 k).1.mulVec (vec m) = vec m' := hm ▸ hm' ▸ hstep k
  rw [hprod, hpre, hs 5 6 5 (by decide) (by decide), hs 4 5 4 (by decide) (by decide),
    hs 3 4 3 (by decide) (by decide), hs 2 3 2 (by decide) (by decide),
    hs 1 2 1 (by decide) (by decide), hs 0 1 0 (by decide) (by decide)]
  dsimp only [vec]
  rw [ite_eq_left (fun r hr ↦ absurd hr (Nat.not_lt_zero _))]
  have hnorm : (1 / (√2 : ℂ)) ^ 6 = 1 / (√64 : ℂ) := by
    have hs2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [sq]
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [show (√64 : ℝ) = 8 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)],
      _root_.one_div_pow, show ((√2 : ℝ) : ℂ) ^ 6 = (((√2 : ℝ) : ℂ) ^ 2) ^ 3 by ring, hs2]
    push_cast
    norm_num
  rw [hnorm]
  dsimp only [karatsubaRawUnitary128, Matrix.of_apply, Φ, termExp]
  congr 2
  rw [show Finset.filter (fun k : Fin 6 ↦ 0 ≤ k.val) Finset.univ = Finset.univ by simp,
    Fin.sum_univ_six,
    show Finset.filter (fun r : Fin 6 ↦ r.val < (0 : Fin 6).val) Finset.univ = ∅ by decide,
    show Finset.filter (fun r : Fin 6 ↦ r.val < (1 : Fin 6).val) Finset.univ = {0} by decide,
    show Finset.filter (fun r : Fin 6 ↦ r.val < (2 : Fin 6).val) Finset.univ = {0, 1} by decide,
    show Finset.filter (fun r : Fin 6 ↦ r.val < (3 : Fin 6).val) Finset.univ = {0, 1, 2} by decide,
    show Finset.filter (fun r : Fin 6 ↦ r.val < (4 : Fin 6).val) Finset.univ =
      {0, 1, 2, 3} by decide,
    show Finset.filter (fun r : Fin 6 ↦ r.val < (5 : Fin 6).val) Finset.univ =
      {0, 1, 2, 3, 4} by decide]
  simp only [Finset.sum_singleton, Finset.sum_empty, Fin.isValue]
  unfold karatsubaStageExp128
  norm_num
  ring
theorem bit5Flip6_mulVec_single (u : Fin 64) :
    bit5Flip6.1.mulVec (Pi.single u 1) = Pi.single (xor32 u) 1 := by
  let reg : QRegister 1 6 := QRegister.singleton 5
  have hcol : Qubit.X.1.mulVec (Pi.single (reg.extractIndex u) 1) =
      Pi.single (1 - reg.extractIndex u) 1 := by
    rcases (by omega : (reg.extractIndex u).val = 0 ∨ (reg.extractIndex u).val = 1) with h0 | h1
    · have he : reg.extractIndex u = 0 := Fin.ext h0
      rw [he]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Qubit.X]
    · have he : reg.extractIndex u = 1 := Fin.ext h1
      rw [he]; funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Qubit.X]
  rw [bit5Flip6, QRegister.embedUnitary_val, reg.embedMatrix_mulVec_single_factors, hcol,
    reg.tensorState_single_replaceIndex]
  congr 1
  clear hcol
  revert u
  decide
theorem sixStageKaratsuba64_offset_eq_offsetUnitary (b : Fin 2) : (wireHadamard6 0 *
    (stageDiag6 1 * wireHadamard6 1) * (stageDiag6 2 * wireHadamard6 2) * (stageDiag6 3 *
    wireHadamard6 3) * (stageDiag6 4 * wireHadamard6 4) * (stageDiag6 5 * wireHadamard6 5) *
    preDiag6 b * bit5Flip6).1 = karatsubaOffsetUnitary128 b := by
  ext z u
  have hcol := congrFun (show ((wireHadamard6 0 * (stageDiag6 1 * wireHadamard6 1) *
      (stageDiag6 2 * wireHadamard6 2) * (stageDiag6 3 * wireHadamard6 3) *
      (stageDiag6 4 * wireHadamard6 4) * (stageDiag6 5 * wireHadamard6 5) *
      preDiag6 b * bit5Flip6).1).mulVec (Pi.single u 1) = _ by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, bit5Flip6_mulVec_single,
      sixStageKaratsuba64_eq_rawUnitary b]) z
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, karatsubaOffsetUnitary128] using hcol
def parallelBit5FlipAxes {n M_ax : ℕ} (rAxes : Fin M_ax → QRegister 6 n) : Circuit n :=
  Circuit.sequence (List.ofFn fun a : Fin M_ax ↦ Circuit.X (rAxes a 5))
@[simp] theorem count_parallelBit5FlipAxes_toff {n M_ax : ℕ}
    (rAxes : Fin M_ax → QRegister 6 n) : (parallelBit5FlipAxes rAxes).count .TOFF = 0 := by
  simp [parallelBit5FlipAxes, List.sum_ofFn]
@[simp] theorem count_parallelBit5FlipAxes_t {n M_ax : ℕ}
    (rAxes : Fin M_ax → QRegister 6 n) : (parallelBit5FlipAxes rAxes).count .T = 0 := by
  simp [parallelBit5FlipAxes, List.sum_ofFn]
end DyadicQft64Engine
end
end ModDyadicQft64Engine

section ModFullSysPrepare6Slot
@[expose] public section
namespace FullSysPrepare6Slot
section ConfigFullSysPrepare6Slot
open Operator Matrix QProg HermitianMat _root_.QRegister QRegExt _root_.DynamicCircuit DynCircuitExt
  LocalClassicalPerm
open SymTempAndStep SpecsAux SpecsAux.SpecMirror
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
def fullSysCoinIdx (k : Fin 6) : Fin 8 := if k = 0 then 4 else if k = 1 then 5 else if k = 2
    then 0 else if k = 3 then 6 else if k = 4 then 1 else 7
section GidneyComparatorAndEncoder
variable {Var : Type} {n : ℕ}
def xorCoin3Bits (rCoin3 : QRegister 3 n) (cBit : ZMod 2) (mask : Fin 3 → ZMod 2)
    (β : BitAssignment n) : BitAssignment n := Function.update (Function.update
    (Function.update β (rCoin3 0) (β (rCoin3 0) + cBit * mask 0)) (rCoin3 1) (β (rCoin3 1) +
    cBit * mask 1)) (rCoin3 2) (β (rCoin3 2) + cBit * mask 2)
@[simp] theorem xorCoin3Bits_apply_reg (rCoin3 : QRegister 3 n) (cBit : ZMod 2)
    (mask : Fin 3 → ZMod 2) (β : BitAssignment n) (j : Fin 3) :
    xorCoin3Bits rCoin3 cBit mask β (rCoin3 j) = β (rCoin3 j) + cBit * mask j := by
  fin_cases j
  · simp [xorCoin3Bits]
  · simp [xorCoin3Bits]
  · simp [xorCoin3Bits]
private def rTailAux {b N : ℕ} (r : QRegister (b + 1) N) : QRegister b N :=
  ⟨fun i ↦ r i.succ, fun _ _ h ↦ Fin.succ_injective _ (r.wires.injective h)⟩
private theorem hadamardAll_zero {N : ℕ} (r : QRegister 0 N) :
    (PhaseGradCatalystCore.hadamardAll r).eval.1 = 1 := by
  unfold PhaseGradCatalystCore.hadamardAll
  rw [List.ofFn_zero]
  rfl
private theorem hadamardAll_succ {b N : ℕ} (r : QRegister (b + 1) N) :
    (PhaseGradCatalystCore.hadamardAll r).eval.1 =
      (PhaseGradCatalystCore.hadamardAll (rTailAux r)).eval.1 * (Circuit.H (r 0)).eval.1 := by
  unfold PhaseGradCatalystCore.hadamardAll
  rw [List.ofFn_succ]
  simp only [Circuit.sequence, Circuit.eval_seq, Submonoid.coe_mul]
  rfl
private theorem lemHex333 {b k N : ℕ} (r : QRegister b N) (rOther : QRegister k N)
    (hdisj : r.DisjointWires rOther) (A : Operator (2 ^ k)) :
    (PhaseGradCatalystCore.hadamardAll r).eval.1 * rOther.embedMatrix A = rOther.embedMatrix A
    * (PhaseGradCatalystCore.hadamardAll r).eval.1 := by
  induction b with
  | zero => simp [hadamardAll_zero r]
  | succ b ih =>
      have hdisj_tail : (rTailAux r).DisjointWires rOther :=
        QRegister.disjoint_iff.mpr fun i j ↦ hdisj.ne i.succ j
      have hdisj_q0 : (QRegister.singleton (r 0)).DisjointWires rOther :=
        QRegister.disjoint_iff.mpr fun i j ↦ Fin.cases (hdisj.ne 0 j) (fun x ↦ x.elim0) i
      have h1q : (Circuit.H (r 0)).eval.1 * rOther.embedMatrix A =
          rOther.embedMatrix A * (Circuit.H (r 0)).eval.1 := by
        simpa only [Circuit.eval_single, PrimitiveGate.eval, QRegister.embedUnitary_val] using
          (QRegister.singleton (r 0)).embedMatrix_comm_of_disjoint rOther hdisj_q0 Qubit.H.1 A
      rw [hadamardAll_succ r, Matrix.mul_assoc, h1q, ← Matrix.mul_assoc,
        ih (rTailAux r) hdisj_tail, Matrix.mul_assoc]
theorem hadamardAll_eval_self_adj {b k : ℕ} (r : QRegister b k) :
    (PhaseGradCatalystCore.hadamardAll r).eval.1ᴴ =
      (PhaseGradCatalystCore.hadamardAll r).eval.1 := by
  induction b with
  | zero => simp [hadamardAll_zero r]
  | succ b ih =>
      have hH_sa : (Circuit.H (r 0)).eval.1ᴴ = (Circuit.H (r 0)).eval.1 := by
        have hloc : Qubit.H.1ᴴ = Qubit.H.1 := by
          ext i j
          fin_cases i
          · fin_cases j
            · simp [Qubit.H]
            · simp [Qubit.H]
          · fin_cases j
            · simp [Qubit.H]
            · simp [Qubit.H]
        change ((QRegister.singleton (r 0)).embedMatrix Qubit.H.1)ᴴ =
          (QRegister.singleton (r 0)).embedMatrix Qubit.H.1
        rw [← QRegister.embedMatrix_conjTranspose, hloc]
      have hdisj : (rTailAux r).DisjointWires (QRegister.singleton (r 0)) :=
        QRegister.disjoint_iff.mpr fun i j ↦ Fin.cases
          (fun h ↦ Fin.succ_ne_zero i (r.wires.injective h)) (fun x ↦ x.elim0) j
      have hcomm : (PhaseGradCatalystCore.hadamardAll (rTailAux r)).eval.1 *
          (Circuit.H (r 0)).eval.1 =
          (Circuit.H (r 0)).eval.1 * (PhaseGradCatalystCore.hadamardAll (rTailAux r)).eval.1 :=
        lemHex333 (rTailAux r) (QRegister.singleton (r 0)) hdisj Qubit.H.1
      rw [hadamardAll_succ r, Matrix.conjTranspose_mul, hH_sa, ih (rTailAux r), hcomm]
@[simp] theorem hadamardAll_eval_inv {b k : ℕ} (r : QRegister b k) :
    (PhaseGradCatalystCore.hadamardAll r).eval⁻¹ =
      (PhaseGradCatalystCore.hadamardAll r).eval := by
  ext i j
  change (PhaseGradCatalystCore.hadamardAll r).eval.1ᴴ i j = _
  rw [hadamardAll_eval_self_adj]
end GidneyComparatorAndEncoder
section LcuTopBlockAndJunction
private theorem lemHex334 (x : Fin 2) : compProj 0 * Qubit.H.1ᴴ * compProj x * Qubit.H.1 *
    compProj 0 = (2 : ℂ)⁻¹ • compProj 0 := by
  fin_cases x <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [compProj, Qubit.H, Matrix.mul_apply, Fin.sum_univ_two]
private theorem lemHex335 {N : ℕ} (q : Wire N) (x : Fin 2) :
    (QRegister.singleton q).basisOutcomeProjector 0 * (Circuit.H q).eval.1ᴴ *
      (QRegister.singleton q).basisOutcomeProjector x * (Circuit.H q).eval.1 *
      (QRegister.singleton q).basisOutcomeProjector 0 =
      (2 : ℂ)⁻¹ • (QRegister.singleton q).basisOutcomeProjector 0 := by
  simp only [Circuit.eval_single, PrimitiveGate.eval, QRegister.embedUnitary_val,
    QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_conjTranspose,
    ← QRegister.embedMatrix_mul]
  rw [lemHex334, QRegister.embedMatrix_smul]
private theorem lemHex336 {N : ℕ} (P0 Q0 A B Pu Qu : Operator N) (hQ0A' : Q0 * Aᴴ = Aᴴ * Q0)
    (hB'Pu : Bᴴ * Pu = Pu * Bᴴ) (hQ0Pu : Q0 * Pu = Pu * Q0) (hBA : B * A = A * B)
    (hQuA : Qu * A = A * Qu) (hBP0 : B * P0 = P0 * B) (hB'A : Bᴴ * A = A * Bᴴ)
    (hQuP0 : Qu * P0 = P0 * Qu) (hQ0A : Q0 * A = A * Q0) (hB'P0 : Bᴴ * P0 = P0 * Bᴴ)
    (hQ0P0 : Q0 * P0 = P0 * Q0) : (P0 * Q0) * (B * A)ᴴ * (Pu * Qu) * (B * A) * (P0 * Q0) =
    (P0 * Aᴴ * Pu * A * P0) * (Q0 * Bᴴ * Qu * B * Q0) := by
  rw [Matrix.conjTranspose_mul]
  calc (P0 * Q0) * (Aᴴ * Bᴴ) * (Pu * Qu) * (B * A) * (P0 * Q0)
    _ = P0 * (Q0 * Aᴴ) * (Bᴴ * Pu) * Qu * (B * A) * P0 * Q0 := by simp only [Matrix.mul_assoc]
    _ = P0 * Aᴴ * (Q0 * Pu) * Bᴴ * Qu * (A * B) * P0 * Q0 := by
        rw [hQ0A', hB'Pu, hBA]
        simp only [Matrix.mul_assoc]
    _ = P0 * Aᴴ * Pu * Q0 * Bᴴ * (Qu * A) * (B * P0) * Q0 := by
        rw [hQ0Pu]
        simp only [Matrix.mul_assoc]
    _ = P0 * Aᴴ * Pu * Q0 * (Bᴴ * A) * (Qu * P0) * B * Q0 := by
        rw [hQuA, hBP0]
        simp only [Matrix.mul_assoc]
    _ = P0 * Aᴴ * Pu * (Q0 * A) * (Bᴴ * P0) * Qu * B * Q0 := by
        rw [hB'A, hQuP0]
        simp only [Matrix.mul_assoc]
    _ = P0 * Aᴴ * Pu * A * (Q0 * P0) * Bᴴ * Qu * B * Q0 := by
        rw [hQ0A, hB'P0]
        simp only [Matrix.mul_assoc]
    _ = (P0 * Aᴴ * Pu * A * P0) * (Q0 * Bᴴ * Qu * B * Q0) := by
        rw [hQ0P0]
        simp only [Matrix.mul_assoc]
theorem hadamardAll_proj_zero_conj {b N : ℕ} (r : QRegister b N) (u : Fin (2 ^ b)) :
    r.basisOutcomeProjector 0 * (PhaseGradCatalystCore.hadamardAll r).eval.1ᴴ *
    r.basisOutcomeProjector u * (PhaseGradCatalystCore.hadamardAll r).eval.1 *
    r.basisOutcomeProjector 0 = ((2 : ℂ)⁻¹ ^ b) • r.basisOutcomeProjector 0 := by
  induction b with
  | zero =>
      rw [show u = 0 from Fin.ext (by omega), (QRegExt.basisOutcomeProjector_zero_of_zero r),
        hadamardAll_zero r]
      simp
  | succ b ih =>
      let r1 := QRegister.singleton (r 0)
      have hdisj : r1.DisjointWires (rTailAux r) :=
        QRegister.disjoint_iff.mpr fun i j ↦ Fin.cases
          (fun h ↦ Fin.succ_ne_zero j (r.wires.injective h.symm)) (fun x ↦ x.elim0) i
      have hbeq {q : ℕ} {y z : Fin (2 ^ q)} :
          y = z ↔ ∀ i, basisBits q y i = basisBits q z i :=
        ⟨fun h _ ↦ h ▸ rfl, fun h ↦ (basisBitsEquiv q).injective (funext h)⟩
      let splitIdx (x : Fin (2 ^ (b + 1))) : Fin (2 ^ 1) × Fin (2 ^ b) :=
        ((basisBitsEquiv 1).symm (fun _ ↦ basisBits (b + 1) x 0),
         (basisBitsEquiv b).symm (fun i ↦ basisBits (b + 1) x i.succ))
      have hproj_split (x : Fin (2 ^ (b + 1))) : r.basisOutcomeProjector x =
          r1.basisOutcomeProjector (splitIdx x).1 *
          (rTailAux r).basisOutcomeProjector (splitIdx x).2 := by
        simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
        refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
        have hiff : r.extractIndex g = x ↔
            r1.extractIndex g = (splitIdx x).1 ∧ (rTailAux r).extractIndex g = (splitIdx x).2 := by
          rw [hbeq, hbeq, hbeq]
          simp only [r1, rTailAux, splitIdx, QRegister.basisBits_extractIndex,
            basisBits_basisBitsEquiv_symm_eq, QRegister.singleton_apply]
          exact ⟨fun h ↦ ⟨fun _ ↦ h 0, fun i ↦ h i.succ⟩,
            fun ⟨h1, h2⟩ idx ↦ Fin.cases (h1 0) h2 idx⟩
        by_cases h1 : r1.extractIndex g = (splitIdx x).1
        · simp [hiff, h1]
        · simp [hiff, h1]
      have hb0 {q : ℕ} (i : Fin q) : basisBits q 0 i = 0 := by
        simp [-Nat.reducePow, basisBits_eq_div_mod]
      have hsplit0 : splitIdx 0 = (0, 0) :=
        Prod.ext
          (hbeq.mpr fun i ↦ by
            dsimp only [splitIdx]
            rw [basisBits_basisBitsEquiv_symm_eq, hb0, hb0])
          (hbeq.mpr fun i ↦ by
            dsimp only [splitIdx]
            rw [basisBits_basisBitsEquiv_symm_eq, hb0, hb0])
      have hcW (M : Operator 2) (w : Fin (2 ^ b)) :=
        (r1.embedMatrix_comm_of_disjoint (rTailAux r) hdisj M (compProj w)).symm
      have hcB (M : Operator 2) := lemHex333 (rTailAux r) r1 (QRegister.disjoint_comm.mp hdisj) M
      have hcB' (M : Operator 2) :
          (PhaseGradCatalystCore.hadamardAll (rTailAux r)).eval.1ᴴ * r1.embedMatrix M =
            r1.embedMatrix M * (PhaseGradCatalystCore.hadamardAll (rTailAux r)).eval.1ᴴ := by
        rw [hadamardAll_eval_self_adj]
        exact hcB M
      have hA : (Circuit.H (r 0)).eval.1 = r1.embedMatrix Qubit.H.1 := rfl
      have hA' : (Circuit.H (r 0)).eval.1ᴴ = r1.embedMatrix Qubit.H.1ᴴ := by
        rw [hA, QRegister.embedMatrix_conjTranspose]
      rw [hproj_split 0, hsplit0, hproj_split u, hadamardAll_succ r]
      dsimp only
      rw [lemHex336 (r1.basisOutcomeProjector 0) ((rTailAux r).basisOutcomeProjector 0)
          (Circuit.H (r 0)).eval.1 (PhaseGradCatalystCore.hadamardAll (rTailAux r)).eval.1
          (r1.basisOutcomeProjector (splitIdx u).1)
          ((rTailAux r).basisOutcomeProjector (splitIdx u).2)
          (by
            rw [hA']
            exact hcW Qubit.H.1ᴴ 0)
          (hcB' (compProj (splitIdx u).1))
          (hcW (compProj (splitIdx u).1) 0)
          (by
            rw [hA]
            exact hcB Qubit.H.1)
          (by
            rw [hA]
            exact hcW Qubit.H.1 (splitIdx u).2)
          (hcB (compProj 0))
          (by
            rw [hA]
            exact hcB' Qubit.H.1)
          (hcW (compProj 0) (splitIdx u).2)
          (by
            rw [hA]
            exact hcW Qubit.H.1 0)
          (hcB' (compProj 0))
          (hcW (compProj 0) 0),
        lemHex335 (r 0) (splitIdx u).1, ih (rTailAux r) (splitIdx u).2,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring
noncomputable def coinSelOutcome {mSel : ℕ} (rCoin3Sel : QRegister 3 mSel) (c : Fin 8) :
    Fin (2 ^ mSel) :=
  (basisBitsEquiv mSel).symm (xorCoin3Bits rCoin3Sel 1 (basisBits 3 c) (fun _ ↦ 0))
@[simp] theorem basisBits_coinSelOutcome_coin {mSel : ℕ} (rCoin3Sel : QRegister 3 mSel)
    (c : Fin 8) (j : Fin 3) :
    basisBits mSel (coinSelOutcome rCoin3Sel c) (rCoin3Sel j) = basisBits 3 c j := by
  simp [coinSelOutcome]
theorem basisBits_coinSelOutcome_outside {mSel : ℕ} (rCoin3Sel : QRegister 3 mSel) (c : Fin 8)
    {w : Wire mSel} (hw : w ∉ rCoin3Sel.image) :
    basisBits mSel (coinSelOutcome rCoin3Sel c) w = 0 := by
  simp [coinSelOutcome, xorCoin3Bits,
    Function.update_of_ne fun h ↦ hw ((rCoin3Sel.mem_image _).mpr ⟨0, h.symm⟩),
    Function.update_of_ne fun h ↦ hw ((rCoin3Sel.mem_image _).mpr ⟨1, h.symm⟩),
    Function.update_of_ne fun h ↦ hw ((rCoin3Sel.mem_image _).mpr ⟨2, h.symm⟩)]
end LcuTopBlockAndJunction
section ConcreteFullSysInstances
local instance (priority := 1000000) instNeZeroTwoPowPrep6 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
end ConcreteFullSysInstances
end ConfigFullSysPrepare6Slot
end FullSysPrepare6Slot
end
end ModFullSysPrepare6Slot

end QuantumComputation.Specs.StoppingPowerSolution
