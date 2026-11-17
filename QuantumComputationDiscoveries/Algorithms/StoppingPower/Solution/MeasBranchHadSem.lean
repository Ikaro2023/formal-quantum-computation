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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CleanAncillaComb

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModOctahedralOrbitUnfold
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace OctahedralOrbit
theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := InPlaceFullAddSlice.bit_cases b
end OctahedralOrbit
namespace DynCircuitExt
open _root_.DynamicCircuit
variable {Var : Type} {n : ℕ}
theorem circuit_eval_comm_basisOutcomeProjector_of_not_mem_support {m : ℕ} (c : Circuit n)
    (rAnc : QRegister m n) (o : Fin (2 ^ m)) (hc : ∀ i : Fin m, rAnc i ∉ c.support) : c.eval.1
    * rAnc.basisOutcomeProjector o = rAnc.basisOutcomeProjector o * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g r =>
      have hdisj : r.DisjointWires rAnc := QRegister.disjoint_iff.mpr fun i j hij ↦
        hc j (by rw [Circuit.support_gate, QRegister.mem_image]; exact ⟨i, hij⟩)
      rw [Circuit.eval_gate, QRegister.embedUnitary_val]
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r) rAnc hdisj g.eval.1 o
  | seq c₁ c₂ ih₁ ih₂ =>
      rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
        ih₁ fun i h ↦ hc i (Finset.mem_union_left _ h), ← Matrix.mul_assoc,
        ih₂ fun i h ↦ hc i (Finset.mem_union_right _ h), Matrix.mul_assoc]
theorem wp_qAssign_restrictAssertionToZeroAncilla_comm [Fintype Var] {m : ℕ}
    (U : Unitary (2 ^ n)) (rAnc : QRegister m n) (hcomm : U.1 * rAnc.basisOutcomeProjector 0 =
    rAnc.basisOutcomeProjector 0 * U.1) (Θ : CQAssertionCompat Var (2 ^ n)) : wpQAssignCompat U
    (CQAssertion.restrictToZeroAncilla Θ rAnc) = CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat U Θ) rAnc := by
  funext σ
  apply Subtype.ext
  have hadj : U.1ᴴ * rAnc.basisOutcomeProjector 0 = rAnc.basisOutcomeProjector 0 * U.1ᴴ := by
    simpa only [conjTranspose_mul, rAnc.basisOutcomeProjector_conjTranspose 0] using
      (congrArg conjTranspose hcomm).symm
  simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, CQAssertion.restrictToZeroAncilla_coe, conj_conj, hadj]
end DynCircuitExt
namespace OctahedralOrbit
variable {n : ℕ}
noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j := (basisBitsEquiv q).symm_apply_apply j
theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by simp [ket, basisState]
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := InPlaceFullAddSlice.matrix_ext_ket h
noncomputable def writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]
theorem writeReg_apply_of_not_mem {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
      simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
theorem writeReg_eq_update {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rcases eq_or_ne i i₀ with rfl | hi
    · simp
    · rw [writeReg_apply_reg, Function.update_of_ne (r.wires.injective.ne hi), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne fun h ↦ hw ⟨i₀, h.symm⟩]
noncomputable abbrev localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
  (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {k : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors,
    show r.extractIndex ((basisBitsEquiv n).symm β) = localIdx r β by simp [QRegister.extractIndex],
    show A.mulVec (Pi.single (localIdx r β) 1) =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • Pi.single l 1
      from funext fun x ↦ by simp [Matrix.mulVec, dotProduct, Pi.single_apply],
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]
theorem singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) = A 0
    (if β q = 0 then 0 else 1) • ket (Function.update β q 0) + A 1 (if β q = 0 then 0 else 1)
    • ket (Function.update β q 1) := by
  have hloc : localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 :=
    (by decide : ∀ b : ZMod 2,
      ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1) (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [embedMatrix_mulVec_ket, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) :=
  InPlaceFullAddSlice.eval_seq_mulVec c₁ c₂ ψ
theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) :=
  InPlaceFullAddSlice.ket_X q β
theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) :=
  InPlaceFullAddSlice.ket_CNOT c t h β
theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) = ket
    (Function.update β t (β t + β c₁ * β c₂)) :=
  InPlaceFullAddSlice.ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t β
theorem ket_projector (q : Wire n) (o : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (ket β) =
      if β q = (o.val : ZMod 2) then ket β else 0 := InPlaceFullAddSlice.ket_projector q o β
theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 := InPlaceFullAddSlice.ket_projector_zero q β
end OctahedralOrbit
end
end ModOctahedralOrbitUnfold

section ModMeasureBranchHadamardSem
@[expose] public section
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace MeasureBranchHadamardSem
section BasisKetAndProjectors
variable {n : ℕ}
noncomputable def ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
def bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
noncomputable def sqrtHalf : ℂ := (√(1 / 2) : ℝ)
theorem sqrtHalf_mul_sqrtHalf : (sqrtHalf : ℂ) * sqrtHalf = 1 / 2 := by
  rw [sqrtHalf, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num
theorem star_sqrtHalf : star (sqrtHalf : ℂ) = sqrtHalf := Complex.conj_ofReal _
theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := InPlaceFullAddSlice.bit_cases b
theorem bitSign_mul_self (b : ZMod 2) : bitSign b * bitSign b = 1 := by
  rcases bit_cases b with rfl | rfl <;> simp [bitSign]
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B :=
  InPlaceFullAddSlice.matrix_ext_ket h
theorem mul_mulVec (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (v : Fin (2 ^ n) → ℂ) :
    (A * B).mulVec v = A.mulVec (B.mulVec v) := (Matrix.mulVec_mulVec v A B).symm
theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) :=
  InPlaceFullAddSlice.eval_seq_mulVec c₁ c₂ ψ
theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) :=
  InPlaceFullAddSlice.ket_X q β
theorem ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β :=
  InPlaceFullAddSlice.ket_Z q β
theorem ket_H (q : Wire n) (β : BitAssignment n) : (Circuit.H q).eval.1.mulVec (ket β) =
    sqrtHalf • (ket (Function.update β q 0) + bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((√(1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec (OctahedralOrbit.ket β) = _
  rw [OctahedralOrbit.singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;>
    simp [ket, hb, bitSign, sqrtHalf, smul_add, Complex.real_smul]
theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) :=
  InPlaceFullAddSlice.ket_CNOT c t h β
theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) = ket
    (Function.update β t (β t + β c₁ * β c₂)) :=
  InPlaceFullAddSlice.ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t β
theorem ket_projector (q : Wire n) (o : Fin (2 ^ 1)) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (ket β) =
      if β q = (o.val : ZMod 2) then ket β else 0 := InPlaceFullAddSlice.ket_projector q o β
theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 := InPlaceFullAddSlice.ket_projector_zero q β
theorem ket_projector_one (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) =
      if β q = 1 then ket β else 0 := by simpa using ket_projector q 1 β
noncomputable def projZeroAll : (k : ℕ) → (Fin k → Wire n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0, _ => 1
  | k + 1, scr =>
      (QRegister.singleton (scr 0)).basisOutcomeProjector 0 * projZeroAll k (fun i => scr i.succ)
theorem projZeroAll_eq_inPlace :
    ∀ (k : ℕ) (scr : Fin k → Wire n), projZeroAll k scr = InPlaceFullAddSlice.projZeroAll k scr
  | 0, _ => rfl
  | k + 1, scr => by
      simp only [projZeroAll, InPlaceFullAddSlice.projZeroAll, projZeroAll_eq_inPlace]
theorem ket_projZeroAll : ∀ (k : ℕ) (scr : Fin k → Wire n) (β : BitAssignment n),
    (projZeroAll k scr).mulVec (ket β) =
      if ∀ j : Fin k, β (scr j) = 0 then ket β else 0 := fun k scr β => by
  rw [projZeroAll_eq_inPlace]
  exact InPlaceFullAddSlice.ket_projZeroAll k scr β
theorem basisOutcomeProjector_comm_projZeroAll (w : Wire n) (o : Fin (2 ^ 1)) (k : ℕ)
    (scr : Fin k → Wire n) : (QRegister.singleton w).basisOutcomeProjector o * projZeroAll k
    scr = projZeroAll k scr * (QRegister.singleton w).basisOutcomeProjector o := by
  rw [projZeroAll_eq_inPlace]
  exact InPlaceFullAddSlice.basisOutcomeProjector_comm_projZeroAll w o k scr
theorem projZeroAll_conjTranspose :
    ∀ (k : ℕ) (scr : Fin k → Wire n), (projZeroAll k scr)ᴴ = projZeroAll k scr := fun k scr => by
  rw [projZeroAll_eq_inPlace]
  exact InPlaceFullAddSlice.projZeroAll_conjTranspose k scr
theorem projZeroAll_mul_self (k : ℕ) (scr : Fin k → Wire n) :
    projZeroAll k scr * projZeroAll k scr = projZeroAll k scr := by
  refine matrix_ext_ket fun β => ?_
  by_cases hs : ∀ j : Fin k, β (scr j) = 0 <;> simp [mul_mulVec, ket_projZeroAll, hs]
theorem projZeroAll_comm :
    ∀ (k₁ k₂ : ℕ) (s₁ : Fin k₁ → Wire n) (s₂ : Fin k₂ → Wire n),
      projZeroAll k₁ s₁ * projZeroAll k₂ s₂ = projZeroAll k₂ s₂ * projZeroAll k₁ s₁
  | 0, _, _, _ => by simp [projZeroAll]
  | k₁ + 1, k₂, s₁, s₂ => by
      rw [projZeroAll, Matrix.mul_assoc, projZeroAll_comm k₁ k₂ _ s₂, ← Matrix.mul_assoc,
        basisOutcomeProjector_comm_projZeroAll, Matrix.mul_assoc]
theorem toffoli_eval_sq (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval * (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval = 1 :=
  InPlaceFullAddSlice.toffoli_eval_sq c₁ c₂ t h₁₂ h₁t h₂t
theorem projZeroAll_eq_basisOutcomeProjector_zero {m : ℕ} (rWork : QRegister m n) :
    projZeroAll m rWork.wires = rWork.basisOutcomeProjector 0 := by
  rw [projZeroAll_eq_inPlace]
  exact InPlaceFullAddSlice.projZeroAll_eq_basisOutcomeProjector_zero rWork
end BasisKetAndProjectors
section CleanUnitaryAlgebra
variable {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
def RealizesCleanUnitary (v : Var) (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (c : DynamicCircuit Var n) (U : Unitary (2 ^ n)) : Prop := (∀ (Ψ : CQAssertionCompat Var (2 ^
    n)), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) → ∀ σ val, wp c.compile Ψ
    (Function.update σ v val) = wp c.compile Ψ σ) ∧ (∀ (Θ : CQAssertionCompat Var (2 ^ n)), (∀ σ
    val, Θ (Function.update σ v val) = Θ σ) → ∀ σ : Store Var, ((wp c.compile Θ σ).1).conj
    P_scr = ((wpQAssignCompat U Θ σ).1).conj P_scr)
theorem RealizesCleanUnitary.identity (v : Var) (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    RealizesCleanUnitary v P_scr .identity (1 : Unitary (2 ^ n)) :=
  InPlaceFullAddSlice.RealizesCleanUnitary.identity v P_scr
theorem RealizesCleanUnitary.circuit (v : Var) (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (c : Circuit n) : RealizesCleanUnitary v P_scr (.circuit c) c.eval :=
  InPlaceFullAddSlice.RealizesCleanUnitary.circuit v P_scr c
theorem RealizesCleanUnitary.congr_unitary {v : Var}
    {P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {c : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ n)} (hP : P_scrᴴ = P_scr) (hc : RealizesCleanUnitary v P_scr c U₁)
    (heq : U₁.1 * P_scr = U₂.1 * P_scr) : RealizesCleanUnitary v P_scr c U₂ :=
  InPlaceFullAddSlice.RealizesCleanUnitary.congr_unitary (U₂ := U₂) hP hc heq
theorem RealizesCleanUnitary.mono_proj {v : Var}
    {P_small P_big : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {c : DynamicCircuit Var n}
    {U : Unitary (2 ^ n)} (hPs : P_smallᴴ = P_small) (hPb : P_bigᴴ = P_big)
    (hsub : P_small * P_big = P_big) (hc : RealizesCleanUnitary v P_small c U) :
    RealizesCleanUnitary v P_big c U :=
  InPlaceFullAddSlice.RealizesCleanUnitary.mono_proj hPs hPb hsub hc
theorem RealizesCleanUnitary.seq {v : Var} {P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP : P_scrᴴ = P_scr)
    (h₁ : RealizesCleanUnitary v P_scr c₁ U₁) (h₂ : RealizesCleanUnitary v P_scr c₂ U₂)
    (hclean : P_scr * (U₁.1 * P_scr) = U₁.1 * P_scr) : RealizesCleanUnitary v P_scr
    (.seq c₁ c₂) (U₂ * U₁) :=
  InPlaceFullAddSlice.RealizesCleanUnitary.seq hP h₁ h₂ hclean
theorem RealizesCleanUnitary.withTempAnd_projZeroAll (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (k : ℕ) (scr : Fin k → Wire n)
    (hdisj : ∀ j : Fin k, anc ≠ scr j) (body : DynamicCircuit Var n)
    (U_body U_clean : Unitary (2 ^ n))
    (hbody : RealizesCleanUnitary v (projZeroAll k scr) body U_body) (hket_eq : ∀ β :
    BitAssignment n, β anc = 0 → (∀ j : Fin k, β (scr j) = 0) → (Circuit.TOFF c₁ c₂ anc h₁₂
    h₁a h₂a).eval.1.mulVec (U_body.1.mulVec (ket (Function.update β anc (β c₁ * β c₂)))) =
    U_clean.1.mulVec (ket β)) (hket_clean : ∀ β : BitAssignment n, β anc = 0 → (∀ j : Fin k, β
    (scr j) = 0) → ((QRegister.singleton anc).basisOutcomeProjector 0).mulVec
    (U_clean.1.mulVec (ket β)) = U_clean.1.mulVec (ket β)) : RealizesCleanUnitary v
    (projZeroAll (k + 1) (Fin.cons anc scr)) (.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a
    h₂a) (.seq body (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))) U_clean := by
  rw [projZeroAll_eq_inPlace] at hbody ⊢
  exact InPlaceFullAddSlice.RealizesCleanUnitary.withTempAnd_projZeroAll
    v c₁ c₂ anc h₁₂ h₁a h₂a k scr hdisj body U_body U_clean hbody hket_eq hket_clean
end CleanUnitaryAlgebra
section SequentialMeasurement
def measureAndBranchSeq {Var : Type} {n : ℕ} (v : Var) :
    (m : ℕ) → (Fin m → QRegister 1 n) → ((Fin m → Bool) → DynamicCircuit Var n) →
      DynamicCircuit Var n
  | 0, _, k => k Fin.elim0
  | m + 1, qs, k =>
      .seq (.measure v (qs 0))
        (dynQIfVar v
          (measureAndBranchSeq v m (fun i => qs i.succ) (fun rest => k (Fin.cons true rest)))
          (measureAndBranchSeq v m (fun i => qs i.succ) (fun rest => k (Fin.cons false rest))))
theorem measureAndBranchSeq_count_le {Var : Type} {n a : ℕ} (v : Var) (g : PrimitiveGate a)
    (c : ℕ) : ∀ (m : ℕ) (qs : Fin m → QRegister 1 n) (k : (Fin m → Bool) → DynamicCircuit Var n),
      (∀ outcome, (k outcome).count g ≤ c) → (measureAndBranchSeq v m qs k).count g ≤ c
  | 0, _, k, hk => hk Fin.elim0
  | m + 1, _, k, hk => by
      simp only [measureAndBranchSeq, DynamicCircuit.count, zero_add, max_le_iff]
      exact ⟨measureAndBranchSeq_count_le v g c m _ _ (fun _ => hk _),
        measureAndBranchSeq_count_le v g c m _ _ (fun _ => hk _)⟩
theorem measureAndBranchSeq_count_eq_zero {Var : Type} {n a : ℕ} (v : Var) (g : PrimitiveGate a)
    (m : ℕ) (qs : Fin m → QRegister 1 n) (k : (Fin m → Bool) → DynamicCircuit Var n)
    (hk : ∀ outcome, (k outcome).count g = 0) : (measureAndBranchSeq v m qs k).count g = 0 :=
  Nat.eq_zero_of_le_zero (measureAndBranchSeq_count_le v g 0 m qs k (fun o => le_of_eq (hk o)))
noncomputable def projOutcomeAll {n : ℕ} :
    (m : ℕ) → (Fin m → Wire n) → (Fin m → Bool) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0, _, _ => 1
  | m + 1, qs, g =>
      projOutcomeAll m (fun i => qs i.succ) (fun i => g i.succ) *
        (QRegister.singleton (qs 0)).basisOutcomeProjector (if g 0 then 1 else 0)
noncomputable def branchKrausUnitary {n : ℕ} :
    (m : ℕ) → (Fin m → Wire n) → ((Fin m → Bool) → Unitary (2 ^ n)) →
      (Fin m → Bool) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0, _, U_fix, g => (U_fix g).1
  | m + 1, qs, U_fix, g =>
      branchKrausUnitary m (fun i => qs i.succ)
        (fun rest => U_fix (Fin.cons (g 0) rest)) (fun i => g i.succ) *
        (QRegister.singleton (qs 0)).basisOutcomeProjector (if g 0 then 1 else 0)
theorem branchKrausUnitary_eq_mul_projOutcomeAll {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (U_fix : (Fin m → Bool) → Unitary (2 ^ n)) (g : Fin m → Bool),
      branchKrausUnitary m qs U_fix g = (U_fix g).1 * projOutcomeAll m qs g
  | 0, _, U_fix, g => (Matrix.mul_one (U_fix g).1).symm
  | m + 1, qs, U_fix, g => by
      have hg : (Fin.cons (g 0) fun i => g i.succ) = g := Fin.cons_self_tail g
      simp only [branchKrausUnitary, projOutcomeAll, branchKrausUnitary_eq_mul_projOutcomeAll,
        hg, Matrix.mul_assoc]
theorem wp_measureAndBranchSeq_update_self {Var : Type} [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) :
    ∀ (m : ℕ) (qs : Fin m → QRegister 1 n) (fixup : (Fin m → Bool) → DynamicCircuit Var n),
      (∀ g (Ψ : CQAssertionCompat Var (2 ^ n)),
        (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
        ∀ σ val, wp (fixup g).compile Ψ (Function.update σ v val) = wp (fixup g).compile Ψ σ) →
      ∀ (Ψ : CQAssertionCompat Var (2 ^ n)),
        (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
        ∀ (σ : Store Var) (val : ℤ),
          wp (measureAndBranchSeq v m qs fixup).compile Ψ (Function.update σ v val) =
            wp (measureAndBranchSeq v m qs fixup).compile Ψ σ
  | 0, _, fixup, hfix, Ψ, hΨ, σ, val => hfix Fin.elim0 Ψ hΨ σ val
  | m + 1, qs, fixup, _, Ψ, _, σ, val => by
      have hsubst (val' : ℤ) :
          Store.subst (Function.update σ v val) v val' = Store.subst σ v val' :=
        funext fun y => by by_cases hy : y = v <;> simp [Store.subst, hy]
      apply Subtype.ext
      simp only [measureAndBranchSeq, compile_seq, compile_measure, QProg.measureRegister,
        wp_qSeq, wp_qMeasure_apply, qMeasure_obs_map_coe, CQAssertionCompat.subst_apply, hsubst]
theorem wp_measureAndBranchSeq_dynamic {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hP_herm : P_scrᴴ = P_scr)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    ∀ (m : ℕ) (qs : Fin m → Wire n)
      (fixup : (Fin m → Bool) → DynamicCircuit Var n)
      (U_fix : (Fin m → Bool) → Unitary (2 ^ n)),
      (∀ (r : Fin m) (o : Fin (2 ^ 1)),
        (QRegister.singleton (qs r)).basisOutcomeProjector o * P_scr =
          P_scr * (QRegister.singleton (qs r)).basisOutcomeProjector o) →
      (∀ g, RealizesCleanUnitary v P_scr (fixup g) (U_fix g)) →
      ∀ (σ : Store Var),
        ((wp (measureAndBranchSeq v m (fun r => QRegister.singleton (qs r)) fixup).compile
            Θ σ).1).conj P_scr =
          ∑ g : Fin m → Bool,
            ((Θ σ).1.conj (branchKrausUnitary m qs U_fix g)ᴴ).conj P_scr
  | 0, _, fixup, U_fix, _, hfix, σ => by
      have huniv : (@Finset.univ (Fin 0 → Bool) _) = {Fin.elim0} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨Finset.mem_univ _, fun g _ => Subsingleton.elim g Fin.elim0⟩
      rw [huniv, Finset.sum_singleton]
      simpa [measureAndBranchSeq, branchKrausUnitary, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        (hfix Fin.elim0).2 Θ hΘ σ
  | m + 1, qs, fixup, U_fix, hcomm, hfix, σ => by
      have hsubst0 : σ.subst v 0 = Function.update σ v 0 :=
        funext fun _ => by simp [Store.subst, Function.update]
      have hsubst1 : σ.subst v 1 = Function.update σ v 1 :=
        funext fun _ => by simp [Store.subst, Function.update]
      have ih (b : Bool) :
          ((wp (measureAndBranchSeq v m (fun i => QRegister.singleton (qs i.succ))
              (fun rest => fixup (Fin.cons b rest))).compile
            Θ (Function.update σ v (if b then 1 else 0))).1).conj P_scr =
          ∑ rest : Fin m → Bool,
            ((Θ σ).1.conj (branchKrausUnitary m (fun i => qs i.succ)
              (fun rest => U_fix (Fin.cons b rest)) rest)ᴴ).conj P_scr := by
        simpa only [hΘ] using wp_measureAndBranchSeq_dynamic v P_scr hP_herm Θ hΘ m
          (fun i => qs i.succ) (fun rest => fixup (Fin.cons b rest))
          (fun rest => U_fix (Fin.cons b rest)) (fun r o => hcomm r.succ o)
          (fun rest => hfix (Fin.cons b rest)) (Function.update σ v (if b then 1 else 0))
      let P (b : Bool) := (QRegister.singleton (qs 0)).basisOutcomeProjector (if b then 1 else 0)
      have hP_adj (b : Bool) : P_scr * (P b)ᴴ = (P b)ᴴ * P_scr := by
        rw [QRegister.basisOutcomeProjector_conjTranspose]
        exact (hcomm 0 _).symm
      have hmeas : (wp (measureAndBranchSeq v (m + 1) (fun r => QRegister.singleton (qs r))
          fixup).compile Θ σ).1 = (wp (measureAndBranchSeq v m (fun i => QRegister.singleton
          (qs i.succ)) (fun rest => fixup (Fin.cons false rest))).compile Θ (Function.update σ
          v 0)).1.conj (P false)ᴴ + (wp (measureAndBranchSeq v m (fun i => QRegister.singleton
          (qs i.succ)) (fun rest => fixup (Fin.cons true rest))).compile Θ (Function.update σ v
          1)).1.conj (P true)ᴴ := by
        simp only [measureAndBranchSeq, compile_seq, compile_measure, compile_qIf, wp_qSeq,
          wp_qIf, QProg.measureRegister, wp_qMeasure_apply, qMeasure_obs_map_coe,
          CQAssertionCompat.subst_apply]
        change ∑ o : Fin 2, _ = _
        rw [Fin.sum_univ_two]
        simp [qMeasure_outcome_herm_eq_conj, hsubst0, hsubst1,
          QRegister.computationalBasisMeasurement_apply, P]
      have htail (b : Bool) (rest : Fin m → Bool) :
          (((Θ σ).1.conj (branchKrausUnitary m (fun i => qs i.succ)
            (fun r => U_fix (Fin.cons b r)) rest)ᴴ).conj P_scr).conj (P b)ᴴ =
          ((Θ σ).1.conj (branchKrausUnitary (m + 1) qs U_fix (Fin.cons b rest))ᴴ).conj P_scr := by
        simp only [branchKrausUnitary, Fin.cons_zero, Fin.cons_succ, conjTranspose_mul,
          conj_conj, P]
        change (Θ σ).1.conj ((P b)ᴴ * (P_scr * _)) = (Θ σ).1.conj (P_scr * ((P b)ᴴ * _))
        rw [← Matrix.mul_assoc, ← hP_adj b, Matrix.mul_assoc]
      rw [hmeas, map_add, conj_conj, conj_conj, hP_adj false, hP_adj true, ← conj_conj,
        ← conj_conj, show Function.update σ v 0 = Function.update σ v (if false then 1 else 0)
          from rfl, show Function.update σ v 1 = Function.update σ v (if true then 1 else 0)
          from rfl, ih false, ih true, map_sum, map_sum]
      simp only [htail]
      rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
        Fintype.sum_bool, add_comm]
      rfl
attribute [irreducible] measureAndBranchSeq
end SequentialMeasurement
section HadamardSyndromeUncompute
def hadamardAll {n : ℕ} : (m : ℕ) → (Fin m → Wire n) → Circuit n
  | 0, _ => .identity
  | m + 1, qs => Circuit.H (qs 0) ;;ᶜ hadamardAll m (fun i => qs i.succ)
@[simp] theorem count_hadamardAll_t {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n), (hadamardAll m qs).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, qs => by simp [hadamardAll, count_hadamardAll_t]
@[simp] theorem count_hadamardAll_toff {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n), (hadamardAll m qs).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, qs => by simp [hadamardAll, count_hadamardAll_toff]
def xReset {n : ℕ} : (m : ℕ) → (Fin m → Wire n) → (Fin m → Bool) → Circuit n
  | 0, _, _ => .identity
  | m + 1, qs, g =>
      (if g 0 then Circuit.X (qs 0) else .identity) ;;ᶜ
        xReset m (fun i => qs i.succ) (fun i => g i.succ)
@[simp] theorem count_xReset_t {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool), (xReset m qs g).count PrimitiveGate.T = 0
  | 0, _, _ => rfl
  | m + 1, qs, g => by
      simp only [xReset, Circuit.count_seq, count_xReset_t]
      split <;> simp
@[simp] theorem count_xReset_toff {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool), (xReset m qs g).count PrimitiveGate.TOFF = 0
  | 0, _, _ => rfl
  | m + 1, qs, g => by
      simp only [xReset, Circuit.count_seq, count_xReset_toff]
      split <;> simp
def zeroSynd {n : ℕ} : (m : ℕ) → (Fin m → Wire n) → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, qs, β => zeroSynd m (fun i => qs i.succ) (Function.update β (qs 0) 0)
def writeSynd {n : ℕ} :
    (m : ℕ) → (Fin m → Wire n) → (Fin m → Bool) → BitAssignment n → BitAssignment n
  | 0, _, _, β => β
  | m + 1, qs, y, β =>
      writeSynd m (fun i => qs i.succ) (fun i => y i.succ)
        (Function.update β (qs 0) (if y 0 then 1 else 0))
def syndSign {n : ℕ} : (m : ℕ) → (Fin m → Wire n) → (Fin m → Bool) → BitAssignment n → ℂ
  | 0, _, _, _ => 1
  | m + 1, qs, g, β =>
      (if g 0 then bitSign (β (qs 0)) else 1) *
        syndSign m (fun i => qs i.succ) (fun i => g i.succ) β
theorem writeSynd_apply_of_not_mem {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (y : Fin m → Bool) (β : BitAssignment n) (w : Wire n),
      (∀ r : Fin m, w ≠ qs r) → writeSynd m qs y β w = β w
  | 0, _, _, _, _, _ => rfl
  | m + 1, qs, y, β, w, hw => by
      rw [writeSynd, writeSynd_apply_of_not_mem m (fun i => qs i.succ) _ _ w (fun r => hw r.succ),
        Function.update_of_ne (hw 0)]
theorem zeroSynd_eq_writeSynd {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (β : BitAssignment n),
      zeroSynd m qs β = writeSynd m qs (fun _ => false) β
  | 0, _, _ => rfl
  | m + 1, qs, β => by
      simp only [zeroSynd, writeSynd, Bool.false_eq_true, ↓reduceIte]
      exact zeroSynd_eq_writeSynd m _ _
theorem zeroSynd_apply_mem {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n), Function.Injective qs →
      ∀ (β : BitAssignment n) (r : Fin m), zeroSynd m qs β (qs r) = 0
  | 0, _, _, _, r => Fin.elim0 r
  | m + 1, qs, hqs, β, r => by
      cases r using Fin.cases with
      | zero =>
          rw [zeroSynd, zeroSynd_eq_writeSynd, writeSynd_apply_of_not_mem m _ _ _ (qs 0)
            (fun i h => Fin.succ_ne_zero i (hqs h.symm)), Function.update_self]
      | succ j =>
          exact zeroSynd_apply_mem m (fun i => qs i.succ)
            (fun _ _ h => Fin.succ_injective _ (hqs h)) (Function.update β (qs 0) 0) j
theorem zeroSynd_writeSynd_of_zero {n : ℕ} (m : ℕ) (qs : Fin m → Wire n)
    (hqs : Function.Injective qs) (y : Fin m → Bool) (β : BitAssignment n)
    (hzero : ∀ r : Fin m, β (qs r) = 0) : zeroSynd m qs (writeSynd m qs y β) = β := by
  funext w
  by_cases hw : ∃ r : Fin m, w = qs r
  · obtain ⟨r, rfl⟩ := hw
    rw [zeroSynd_apply_mem m qs hqs, hzero r]
  · rw [zeroSynd_eq_writeSynd, writeSynd_apply_of_not_mem m qs _ _ w (fun r h => hw ⟨r, h⟩),
      writeSynd_apply_of_not_mem m qs y β w (fun r h => hw ⟨r, h⟩)]
theorem syndSign_congr_of_eq_on {n : ℕ} : ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool)
    (β₁ β₂ : BitAssignment n),
      (∀ r, β₁ (qs r) = β₂ (qs r)) → syndSign m qs g β₁ = syndSign m qs g β₂
  | 0, _, _, _, _, _ => rfl
  | m + 1, qs, g, β₁, β₂, heq => by
      simp only [syndSign, heq 0, syndSign_congr_of_eq_on m _ _ β₁ β₂ fun r => heq r.succ]
theorem syndSign_mul_self {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool) (β : BitAssignment n),
      syndSign m qs g β * syndSign m qs g β = 1
  | 0, _, _, _ => by simp [syndSign]
  | m + 1, qs, g, β => by
      have h0 : (if g 0 then bitSign (β (qs 0)) else (1 : ℂ)) *
          (if g 0 then bitSign (β (qs 0)) else 1) = 1 := by cases g 0 <;> simp [bitSign_mul_self]
      rw [syndSign, mul_mul_mul_comm, h0, one_mul]
      exact syndSign_mul_self m (fun i => qs i.succ) (fun i => g i.succ) β
theorem embed_comm {n : ℕ} {u v : Wire n} (h : u ≠ v) (A B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) :
    (QRegister.singleton u).embedMatrix A * (QRegister.singleton v).embedMatrix B =
      (QRegister.singleton v).embedMatrix B * (QRegister.singleton u).embedMatrix A :=
  QRegister.embedMatrix_comm_of_disjoint _ _ (QRegister.disjoint_iff.mpr fun _ _ => h) A B
theorem comm_projZeroAll {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ∀ (k : ℕ) (scr : Fin k → Wire n),
      (∀ (j : Fin k) (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ),
        M * (QRegister.singleton (scr j)).embedMatrix B =
          (QRegister.singleton (scr j)).embedMatrix B * M) →
      M * projZeroAll k scr = projZeroAll k scr * M
  | 0, _, _ => by simp [projZeroAll]
  | k + 1, scr, hM => by
      rw [projZeroAll, QRegister.basisOutcomeProjector, ← Matrix.mul_assoc, hM 0 _,
        Matrix.mul_assoc, comm_projZeroAll M k _ fun j => hM j.succ, ← Matrix.mul_assoc]
theorem comm_projOutcomeAll {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool),
      (∀ (i : Fin m) (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ),
        M * (QRegister.singleton (qs i)).embedMatrix B =
          (QRegister.singleton (qs i)).embedMatrix B * M) →
      M * projOutcomeAll m qs g = projOutcomeAll m qs g * M
  | 0, _, _, _ => by simp [projOutcomeAll]
  | m + 1, qs, g, hM => by
      rw [projOutcomeAll, QRegister.basisOutcomeProjector, ← Matrix.mul_assoc,
        comm_projOutcomeAll M m _ _ fun i => hM i.succ, Matrix.mul_assoc, hM 0 _,
        ← Matrix.mul_assoc]
theorem comm_hadamardAll {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ∀ (m : ℕ) (qs : Fin m → Wire n),
      (∀ (i : Fin m) (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ),
        M * (QRegister.singleton (qs i)).embedMatrix B =
          (QRegister.singleton (qs i)).embedMatrix B * M) →
      M * (hadamardAll m qs).eval.1 = (hadamardAll m qs).eval.1 * M
  | 0, _, _ => by simp [hadamardAll]
  | m + 1, qs, hM => by
      simp only [hadamardAll, Circuit.eval_seq, Submonoid.coe_mul, Circuit.eval_single,
        QRegister.embedUnitary_val]
      rw [← Matrix.mul_assoc, comm_hadamardAll M m _ fun i => hM i.succ,
        Matrix.mul_assoc, hM 0 _, ← Matrix.mul_assoc]
theorem comm_xReset {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool),
      (∀ (i : Fin m) (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ),
        M * (QRegister.singleton (qs i)).embedMatrix B =
          (QRegister.singleton (qs i)).embedMatrix B * M) →
      M * (xReset m qs g).eval.1 = (xReset m qs g).eval.1 * M
  | 0, _, _, _ => by simp [xReset]
  | m + 1, qs, g, hM => by
      have h0 : M * (if g 0 then Circuit.X (qs 0) else .identity).eval.1 =
          (if g 0 then Circuit.X (qs 0) else .identity).eval.1 * M := by
        cases g 0
        · simp
        · simp only [↓reduceIte, Circuit.eval_single, QRegister.embedUnitary_val, hM 0]
      simp only [xReset, Circuit.eval_seq, Submonoid.coe_mul]
      rw [← Matrix.mul_assoc, comm_xReset M m _ _ fun i => hM i.succ,
        Matrix.mul_assoc, h0, ← Matrix.mul_assoc]
theorem ket_xReset_projOutcome_hadamardAll {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n), Function.Injective qs →
      ∀ (g : Fin m → Bool) (β : BitAssignment n),
        ((xReset m qs g).eval.1 * projOutcomeAll m qs g * (hadamardAll m qs).eval.1).mulVec
            (ket β) = ((sqrtHalf : ℂ) ^ m * syndSign m qs g β) • ket (zeroSynd m qs β)
  | 0, _, _, _, β => by simp [xReset, projOutcomeAll, hadamardAll, syndSign, zeroSynd]
  | m + 1, qs, hqs, g, β => by
      have hdisj0 : ∀ i : Fin m, qs 0 ≠ qs i.succ := fun i h => Fin.succ_ne_zero i (hqs h.symm)
      let X₀ := (if g 0 then Circuit.X (qs 0) else .identity).eval.1
      let P₀ := (QRegister.singleton (qs 0)).basisOutcomeProjector (if g 0 then 1 else 0)
      let H₀ := (Circuit.H (qs 0)).eval.1
      let X_rest := (xReset m (fun i => qs i.succ) (fun i => g i.succ)).eval.1
      let P_rest := projOutcomeAll m (fun i => qs i.succ) (fun i => g i.succ)
      let H_rest := (hadamardAll m (fun i => qs i.succ)).eval.1
      have hc1 : X₀ * P_rest = P_rest * X₀ := by
        dsimp only [X₀]
        cases g 0
        · simp
        · simp only [↓reduceIte, Circuit.eval_single, QRegister.embedUnitary_val]
          exact comm_projOutcomeAll _ m _ _ fun i B => embed_comm (hdisj0 i) _ B
      have hc2 : (X₀ * P₀) * H_rest = H_rest * (X₀ * P₀) := by
        have emb : X₀ * P₀ = (QRegister.singleton (qs 0)).embedMatrix
            ((if g 0 then PrimitiveGate.x.eval.1 else 1) * compProj (if g 0 then 1 else 0)) := by
          dsimp only [X₀, P₀]
          cases g 0
          · simp [QRegister.basisOutcomeProjector]
          · simp only [↓reduceIte, QRegister.embedMatrix_mul]
            rw [Circuit.eval_single, QRegister.embedUnitary_val, QRegister.basisOutcomeProjector]
        rw [emb]
        exact comm_hadamardAll _ m _ fun i B => embed_comm (hdisj0 i) _ B
      have hfact : (xReset (m + 1) qs g).eval.1 * projOutcomeAll (m + 1) qs g *
          (hadamardAll (m + 1) qs).eval.1 = (X_rest * P_rest * H_rest) * (X₀ * P₀ * H₀) := by
        change (X_rest * X₀) * (P_rest * P₀) * (H_rest * H₀) = _
        calc (X_rest * X₀) * (P_rest * P₀) * (H_rest * H₀)
            = X_rest * (X₀ * P_rest) * P₀ * (H_rest * H₀) := by simp only [Matrix.mul_assoc]
          _ = X_rest * P_rest * ((X₀ * P₀) * H_rest) * H₀ := by
                rw [hc1]
                simp only [Matrix.mul_assoc]
          _ = (X_rest * P_rest * H_rest) * (X₀ * P₀ * H₀) := by
                rw [hc2]
                simp only [Matrix.mul_assoc]
      have h0 : (X₀ * P₀ * H₀).mulVec (ket β) =
          (sqrtHalf * if g 0 then bitSign (β (qs 0)) else 1) •
            ket (Function.update β (qs 0) 0) := by
        have hadd : (1 : ZMod 2) + 1 = 0 := rfl
        dsimp only [X₀, P₀, H₀]
        cases g 0
        · simp only [Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mul, mul_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
            ket_projector_zero, Function.update_self, one_ne_zero, smul_zero, add_zero, mul_one]
        · simp only [↓reduceIte, mul_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
            ket_projector_one, Function.update_self, zero_ne_one, Matrix.mulVec_zero, zero_add,
            ket_X, hadd, Function.update_idem, smul_smul]
      rw [hfact, mul_mulVec, h0, Matrix.mulVec_smul,
        ket_xReset_projOutcome_hadamardAll m (fun i => qs i.succ)
          (fun _ _ h => Fin.succ_injective _ (hqs h)) (fun i => g i.succ)
          (Function.update β (qs 0) 0),
        smul_smul, zeroSynd,
        syndSign_congr_of_eq_on m _ _ _ _ (fun i => Function.update_of_ne (hdisj0 i).symm _ _),
        syndSign, pow_succ]
      congr 1
      ring
theorem RealizesCleanUnitary.streamingSyndromeUncompute {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (m k : ℕ) (qs : Fin m → Wire n)
    (hqs : Function.Injective qs) (scr : Fin k → Wire n)
    (hdisj : ∀ (r : Fin m) (j : Fin k), qs r ≠ scr j) (cBody : DynamicCircuit Var n)
    (U_body U_target : Unitary (2 ^ n)) (fixupPhase : (Fin m → Bool) → DynamicCircuit Var n)
    (U_phase : (Fin m → Bool) → Unitary (2 ^ n)) (syndOf : BitAssignment n → (Fin m → Bool))
    (phaseOf : BitAssignment n → ℂ)
    (hBody : RealizesCleanUnitary v (projZeroAll k scr) cBody U_body) (hFix : ∀ g,
    RealizesCleanUnitary v (projZeroAll k scr) (fixupPhase g) (U_phase g)) (hBody_ket : ∀ β :
    BitAssignment n, (∀ r : Fin m, β (qs r) = 0) → (∀ j : Fin k, β (scr j) = 0) →
    U_body.1.mulVec (ket β) = phaseOf β • ket (writeSynd m qs (syndOf β) β)) (hPhase_ket : ∀
    (g : Fin m → Bool) (β : BitAssignment n), (∀ r : Fin m, β (qs r) = 0) → (∀ j : Fin k, β
    (scr j) = 0) → (U_phase g).1.mulVec (ket β) = syndSign m qs g (writeSynd m qs (syndOf β)
    β) • ket β) (hTarget_ket : ∀ β : BitAssignment n, (∀ r : Fin m, β (qs r) = 0) → (∀ j : Fin
    k, β (scr j) = 0) → U_target.1.mulVec (ket β) = phaseOf β • ket β) : RealizesCleanUnitary
    v (projZeroAll m qs * projZeroAll k scr) (.seq cBody (.seq (.circuit (hadamardAll m qs))
    (measureAndBranchSeq v m (fun r => QRegister.singleton (qs r)) (fun g => .seq (.circuit
    (xReset m qs g)) (fixupPhase g))))) U_target := by
  let P_scr := projZeroAll k scr
  let P_all := projZeroAll m qs * P_scr
  let branchProg : (Fin m → Bool) → DynamicCircuit Var n :=
    fun g => .seq (.circuit (xReset m qs g)) (fixupPhase g)
  let cUncomp : DynamicCircuit Var n := .seq (.circuit (hadamardAll m qs))
      (measureAndBranchSeq v m (fun r => QRegister.singleton (qs r)) branchProg)
  have hPs_herm : P_scrᴴ = P_scr := projZeroAll_conjTranspose k scr
  have hPall_herm : P_allᴴ = P_all := by
    rw [conjTranspose_mul, projZeroAll_conjTranspose, projZeroAll_conjTranspose]
    exact projZeroAll_comm k m scr qs
  have hPscr_elem (r : Fin m) (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) :
      P_scr * (QRegister.singleton (qs r)).embedMatrix B =
        (QRegister.singleton (qs r)).embedMatrix B * P_scr :=
    (comm_projZeroAll _ k scr fun j C => embed_comm (hdisj r j) B C).symm
  have hBranch (g : Fin m → Bool) :
      RealizesCleanUnitary v P_scr (branchProg g) (U_phase g * (xReset m qs g).eval) := by
    refine RealizesCleanUnitary.seq hPs_herm
      (RealizesCleanUnitary.circuit v P_scr (xReset m qs g)) (hFix g) ?_
    rw [← Matrix.mul_assoc, comm_xReset P_scr m qs g hPscr_elem,
      Matrix.mul_assoc, projZeroAll_mul_self]
  have hUncomp_inv (Ψ : CQAssertionCompat Var (2 ^ n))
      (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) (σ : Store Var) (val : ℤ) :
      wp cUncomp.compile Ψ (Function.update σ v val) = wp cUncomp.compile Ψ σ := by
    simp only [cUncomp, compile_seq, wp_qSeq]
    exact (RealizesCleanUnitary.circuit v P_scr (hadamardAll m qs)).1 _
      (wp_measureAndBranchSeq_update_self v m _ branchProg (fun g => (hBranch g).1) Ψ hΨ) σ val
  have hPscr_Pall : P_all * P_scr = P_all := by
    dsimp [P_all, P_scr]
    rw [Matrix.mul_assoc, projZeroAll_mul_self]
  have hBody_clean_adj : P_all * U_body.1ᴴ * P_scr = P_all * U_body.1ᴴ := by
    have hBody_clean_scr : P_scr * (U_body.1 * P_all) = U_body.1 * P_all := by
      refine matrix_ext_ket fun β => ?_
      simp only [P_all, P_scr, mul_mulVec, ket_projZeroAll]
      by_cases hs : ∀ j : Fin k, β (scr j) = 0
      · simp only [hs, imp_true_iff, ↓reduceIte, ket_projZeroAll]
        by_cases hy : ∀ r : Fin m, β (qs r) = 0
        · have hpres (j : Fin k) : (writeSynd m qs (syndOf β) β) (scr j) = 0 := by
            rw [writeSynd_apply_of_not_mem m qs _ β (scr j) (fun r => (hdisj r j).symm)]
            exact hs j
          simp only [hy, imp_true_iff, ↓reduceIte, hBody_ket β hy hs, Matrix.mulVec_smul,
            ket_projZeroAll, hpres]
        · simp only [hy, ↓reduceIte, Matrix.mulVec_zero]
      · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
    simpa [conjTranspose_mul, hPs_herm, hPall_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hBody_clean_scr
  refine ⟨fun Ψ hΨ σ val => ?_, fun Θ hΘ σ => ?_⟩
  · simp only [compile_seq, wp_qSeq]
    exact hBody.1 (wp cUncomp.compile Ψ) (hUncomp_inv Ψ hΨ) σ val
  · have hstep1 : ((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_all =
        (((wp cUncomp.compile Θ σ).1).conj P_scr).conj (P_all * U_body.1ᴴ) := by
      calc ((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_all
          = (((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_scr).conj P_all := by
              rw [conj_conj, hPscr_Pall]
        _ = (((wpQAssignCompat U_body (wp cUncomp.compile Θ) σ).1).conj P_scr).conj P_all := by
              rw [hBody.2 (wp cUncomp.compile Θ) (hUncomp_inv Θ hΘ) σ]
        _ = (((wp cUncomp.compile Θ σ).1).conj P_scr).conj (P_all * U_body.1ᴴ) := by
              simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
                Matrix.star_eq_conjTranspose, conj_conj]
              rw [← Matrix.mul_assoc P_all P_scr U_body.1ᴴ, hPscr_Pall, hBody_clean_adj]
    have hstep2 : ((wp cUncomp.compile Θ σ).1).conj P_scr = ∑ g : Fin m → Bool, ((Θ σ).1.conj
        (branchKrausUnitary m qs (fun g => U_phase g * (xReset m qs g).eval) g * (hadamardAll
        m qs).eval.1)ᴴ).conj P_scr := by
      have hH_adj : P_scr * (hadamardAll m qs).eval.1ᴴ =
          (hadamardAll m qs).eval.1ᴴ * P_scr := by
        simpa [P_scr, conjTranspose_mul, hPs_herm] using
          congrArg conjTranspose (comm_hadamardAll P_scr m qs hPscr_elem).symm
      simp only [cUncomp, compile_seq, compile_circuit, wp_qSeq, wp_circuit_compile_compat,
        wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, conj_conj, hH_adj]
      rw [← conj_conj, wp_measureAndBranchSeq_dynamic v P_scr hPs_herm Θ hΘ m qs branchProg
        (fun g => U_phase g * (xReset m qs g).eval)
        (fun r o => basisOutcomeProjector_comm_projZeroAll (qs r) o k scr) hBranch σ, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [conj_conj, ← hH_adj, conj_conj, Matrix.mul_assoc, ← conjTranspose_mul]
    have hterm (g : Fin m → Bool) :
        ((((Θ σ).1.conj (branchKrausUnitary m qs (fun g =>
          U_phase g * (xReset m qs g).eval) g * (hadamardAll m qs).eval.1)ᴴ).conj P_scr).conj
          (P_all * U_body.1ᴴ)) = ((Θ σ).1.conj (U_target.1 * P_all)ᴴ).conj
          (((sqrtHalf : ℂ) ^ m) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := by
      have hk : branchKrausUnitary m qs (fun g => U_phase g * (xReset m qs g).eval) g *
          (hadamardAll m qs).eval.1 * U_body.1 * P_all = ((sqrtHalf : ℂ) ^ m) •
          (U_target.1 * P_all) := by
        refine matrix_ext_ket fun β => ?_
        rw [branchKrausUnitary_eq_mul_projOutcomeAll, Submonoid.coe_mul]
        by_cases hscr : ∀ j : Fin k, β (scr j) = 0
        · by_cases hsynd : ∀ r : Fin m, β (qs r) = 0
          · have hP : P_all.mulVec (ket β) = ket β := by
              simp only [P_all, P_scr, mul_mulVec, ket_projZeroAll, hscr, hsynd,
                imp_true_iff, ↓reduceIte]
            rw [show (U_phase g).1 * (xReset m qs g).eval.1 * projOutcomeAll m qs g *
                  (hadamardAll m qs).eval.1 * U_body.1 * P_all =
                (U_phase g).1 * (((xReset m qs g).eval.1 * projOutcomeAll m qs g *
                  (hadamardAll m qs).eval.1) * (U_body.1 * P_all)) by simp only [Matrix.mul_assoc],
              mul_mulVec (U_phase g).1, mul_mulVec _ (U_body.1 * P_all), mul_mulVec U_body.1 P_all,
              hP, hBody_ket β hsynd hscr, Matrix.mulVec_smul,
              ket_xReset_projOutcome_hadamardAll m qs hqs g,
              zeroSynd_writeSynd_of_zero m qs hqs (syndOf β) β hsynd, smul_smul,
              Matrix.mulVec_smul, hPhase_ket g β hsynd hscr, smul_smul,
              Matrix.smul_mulVec, mul_mulVec U_target.1 P_all, hP, hTarget_ket β hsynd hscr,
              smul_smul]
            congr 1
            linear_combination (sqrtHalf : ℂ) ^ m * phaseOf β *
              syndSign_mul_self m qs g (writeSynd m qs (syndOf β) β)
          · simp only [P_all, P_scr, Matrix.smul_mulVec, mul_mulVec, ket_projZeroAll, hscr, hsynd,
              imp_true_iff, ↓reduceIte, Matrix.mulVec_zero, smul_zero]
        · simp only [P_all, P_scr, Matrix.smul_mulVec, mul_mulVec, ket_projZeroAll, hscr,
            ↓reduceIte, Matrix.mulVec_zero, smul_zero]
      rw [conj_conj, conj_conj, conj_conj, show P_all * U_body.1ᴴ * P_scr *
          (branchKrausUnitary m qs (fun g => U_phase g * (xReset m qs g).eval) g *
            (hadamardAll m qs).eval.1)ᴴ =
          (branchKrausUnitary m qs (fun g => U_phase g * (xReset m qs g).eval) g *
            (hadamardAll m qs).eval.1 * U_body.1 * P_all)ᴴ by
          rw [hBody_clean_adj]
          simp only [conjTranspose_mul, hPall_herm, Matrix.mul_assoc],
        hk, conjTranspose_smul, star_pow, star_sqrtHalf, Matrix.smul_mul, Matrix.one_mul]
    change ((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_all =
      ((wpQAssignCompat U_target Θ σ).1).conj P_all
    rw [hstep1, hstep2, map_sum]
    simp_rw [hterm, conj_conj, Matrix.smul_mul, Matrix.one_mul, conjTranspose_mul, hPall_herm]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    have hhalf : ((2 ^ m : ℕ) : ℂ) * ((sqrtHalf : ℂ) ^ m * (sqrtHalf : ℂ) ^ m) = 1 := by
      rw [← mul_pow, sqrtHalf_mul_sqrtHalf, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      norm_num
    have hsum_mat : ∀ (s : Finset (Fin m → Bool)) (H : HermitianMat (Fin (2 ^ n)) ℂ),
        (∑ _ ∈ s, H).mat = (s.card : ℂ) • H.mat := fun s H =>
      Finset.induction_on s (by simp) fun a s ha ih => by
        have h1 : (∑ _ ∈ insert a s, H).mat = H.mat + (∑ _ ∈ s, H).mat :=
          congrArg HermitianMat.mat (Finset.sum_insert ha)
        rw [h1, ih, show (insert a s).card = s.card + 1 by simp [ha],
          Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]
    ext1
    rw [hsum_mat, show ((Finset.univ : Finset (Fin m → Bool)).card : ℂ) = ((2 ^ m : ℕ) : ℂ) by simp,
      HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
      conjTranspose_smul, star_pow, star_sqrtHalf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hhalf, one_smul]
end HadamardSyndromeUncompute
end MeasureBranchHadamardSem
end
end ModMeasureBranchHadamardSem

section ModDyadic128CoulombMath
@[expose] public section
set_option maxRecDepth 8192
namespace Dyadic128CoulombMath
open Real SpecsAux SpecsAux.SpecMirror
open scoped BigOperators
abbrev orbitCount47905 : ℕ := 47905
abbrev SubGridCoord64 : Type := Fin 3 → Fin 64
abbrev FineCoord128 : Type := Fin 3 → Fin 128
structure CanonicalTriple65 where
  u : Fin 65
  v : Fin 65
  w : Fin 65
  uv : u ≤ v
  vw : v ≤ w
  deriving DecidableEq
def canonicalEmbed128 (t : CanonicalTriple65) : FineCoord128
  | ⟨0, _⟩ => ⟨t.u.val, by omega⟩
  | ⟨1, _⟩ => ⟨t.v.val, by omega⟩
  | ⟨2, _⟩ => ⟨t.w.val, by omega⟩
def foldMag128 (x : Fin 128) : Fin 65 := ⟨min x.val (128 - x.val), by omega⟩
@[simp] theorem foldMag128_zero : foldMag128 0 = 0 := rfl
@[simp] theorem foldMag128_nyquist : foldMag128 ⟨64, by omega⟩ = ⟨64, by omega⟩ := rfl
theorem foldMag128_mod_two (x : Fin 128) : (foldMag128 x).val % 2 = x.val % 2 := by
  dsimp [foldMag128]
  omega
def sortTriple {α : Type*} [LinearOrder α] (f : Fin 3 → α) : Fin 3 → α :=
  let a0 := min (f 0) (f 1)
  let b0 := max (f 0) (f 1)
  let c1 := max b0 (f 2)
  let b1 := min b0 (f 2)
  let a2 := min a0 b1
  let b2 := max a0 b1
  ![a2, b2, c1]
theorem exists_perm_sortTriple {α : Type*} [LinearOrder α] (f : Fin 3 → α) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ w, sortTriple f w = f (σ w) := by
  have mkStep (i j k : Fin 3) (hik : i ≠ k) (hjk : j ≠ k) (g : Fin 3 → α) :
      ∃ τ : Equiv.Perm (Fin 3),
        g (τ i) = min (g i) (g j) ∧ g (τ j) = max (g i) (g j) ∧ g (τ k) = g k := by
    by_cases h : g i ≤ g j
    · exact ⟨1, (min_eq_left h).symm, (max_eq_right h).symm, rfl⟩
    · exact ⟨Equiv.swap i j, by rw [Equiv.swap_apply_left, min_eq_right (le_of_not_ge h)],
        by rw [Equiv.swap_apply_right, max_eq_left (le_of_not_ge h)],
        by rw [Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]⟩
  rcases mkStep 0 1 2 (by decide) (by decide) f with ⟨σ₁, h1a, h1b, h1c⟩
  rcases mkStep 1 2 0 (by decide) (by decide) (fun x ↦ f (σ₁ x)) with ⟨σ₂, h2a, h2b, h2c⟩
  rcases mkStep 0 1 2 (by decide) (by decide) (fun x ↦ f (σ₁ (σ₂ x))) with ⟨σ₃, h3a, h3b, h3c⟩
  have h0 : sortTriple f 0 = f ((σ₁ * σ₂ * σ₃) 0) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h3a, h2c, h2a, h1a, h1b, h1c]
    rfl
  have h1 : sortTriple f 1 = f ((σ₁ * σ₂ * σ₃) 1) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h3b, h2c, h2a, h1a, h1b, h1c]
    rfl
  have h2 : sortTriple f 2 = f ((σ₁ * σ₂ * σ₃) 2) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h3c, h2b, h1b, h1c]
    rfl
  refine ⟨σ₁ * σ₂ * σ₃, fun w ↦ ?_⟩
  fin_cases w
  · exact h0
  · exact h1
  · exact h2
theorem sortTriple_mono {α : Type*} [LinearOrder α] (f : Fin 3 → α) :
    sortTriple f 0 ≤ sortTriple f 1 ∧ sortTriple f 1 ≤ sortTriple f 2 := by
  dsimp [sortTriple]
  exact ⟨min_le_max, max_le (min_le_max.trans (le_max_left _ _))
    ((min_le_left _ _).trans (le_max_left _ _))⟩
def canonTriple128 (d : FineCoord128) : CanonicalTriple65 :=
  let s := sortTriple (fun w ↦ foldMag128 (d w))
  have hm := sortTriple_mono (fun w ↦ foldMag128 (d w))
  ⟨s 0, s 1, s 2, hm.1, hm.2⟩
@[simp] theorem canonTriple128_canonicalEmbed128 (c : CanonicalTriple65) :
    canonTriple128 (canonicalEmbed128 c) = c := by
  have hf : (fun w ↦ foldMag128 (canonicalEmbed128 c w)) = ![c.u, c.v, c.w] :=
    funext fun w ↦ by
      fin_cases w <;> exact Fin.ext (by dsimp [foldMag128, canonicalEmbed128]; omega)
  cases c with
  | mk u v w uv vw =>
    simp only [canonTriple128, hf]
    dsimp [sortTriple]
    simp only [min_eq_left uv, max_eq_right uv, min_eq_left vw, max_eq_right vw]
def triNum (n : ℕ) : ℕ := n * (n + 1) / 2
def tetNum (n : ℕ) : ℕ := n * (n + 1) * (n + 2) / 6
theorem two_mul_triNum (n : ℕ) : 2 * triNum n = n * (n + 1) := by
  dsimp [triNum]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have : (k + k) * (k + k + 1) = 2 * (k * (2 * k + 1)) := by ring
    omega
  · have : (2 * k + 1) * (2 * k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) := by ring
    omega
theorem triNum_succ (n : ℕ) : triNum (n + 1) = triNum n + (n + 1) := by
  linarith [two_mul_triNum (n + 1), two_mul_triNum n]
theorem six_mul_tetNum (n : ℕ) : 6 * tetNum n = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [tetNum] at ih ⊢
    have hdiff : (k + 1) * (k + 2) * (k + 3) = k * (k + 1) * (k + 2) + 3 * ((k + 1) * (k + 2)) := by
      ring
    rw [hdiff, ← two_mul_triNum (k + 1),
      show (k * (k + 1) * (k + 2) + 3 * (2 * triNum (k + 1))) / 6 =
        k * (k + 1) * (k + 2) / 6 + triNum (k + 1) by omega]
    omega
theorem tetNum_succ (n : ℕ) : tetNum (n + 1) = tetNum n + triNum (n + 1) := by
  linarith [six_mul_tetNum (n + 1), six_mul_tetNum n, two_mul_triNum (n + 1)]
def tetRankPoly (u v w : ℕ) : ℕ := tetNum w + triNum v + u
theorem tetNum_mono {a b : ℕ} (hab : a ≤ b) : tetNum a ≤ tetNum b :=
  Nat.div_le_div_right (Nat.mul_le_mul (Nat.mul_le_mul hab (by omega)) (by omega))
theorem triNum_mono {a b : ℕ} (hab : a ≤ b) : triNum a ≤ triNum b :=
  Nat.div_le_div_right (Nat.mul_le_mul hab (by omega))
theorem tetRankPoly_lt_tetNum_succ {u v w : ℕ} (huv : u ≤ v) (hvw : v ≤ w) :
    tetRankPoly u v w < tetNum (w + 1) := by
  have h1 := triNum_succ v
  have h2 : triNum (v + 1) ≤ triNum (w + 1) := triNum_mono (by omega)
  have h3 := tetNum_succ w
  dsimp [tetRankPoly]
  omega
def findUpper (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, r => if f (k + 1) ≤ r then k + 1 else findUpper f k r
theorem findUpper_spec (f : ℕ → ℕ) (hf0 : f 0 = 0) :
    ∀ k r, r < f (k + 1) →
      findUpper f k r ≤ k ∧ f (findUpper f k r) ≤ r ∧ r < f (findUpper f k r + 1)
  | 0, _, hr => ⟨le_rfl, hf0.le.trans (Nat.zero_le _), hr⟩
  | k + 1, r, hr => by
    dsimp [findUpper]
    split_ifs with hle
    · exact ⟨le_rfl, hle, hr⟩
    · rcases findUpper_spec f hf0 k r (by omega) with ⟨_, h2, h3⟩
      exact ⟨by omega, h2, h3⟩
theorem findUpper_eq (f : ℕ → ℕ) {y x r : ℕ} (hmono : ∀ {a b}, a ≤ b → f a ≤ f b)
    (hy1 : f y ≤ r) (hy2 : r < f (y + 1)) (hx1 : f x ≤ r) (hx2 : r < f (x + 1)) : y = x := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd (hmono (by omega : y + 1 ≤ x)) (by omega)
  · exact absurd (hmono (by omega : x + 1 ≤ y)) (by omega)
theorem unrank_bounds {r w v : ℕ} (hr : r < orbitCount47905) (hw_def : w = findUpper tetNum 64 r)
    (hv_def : v = findUpper triNum w (r - tetNum w)) :
    w ≤ 64 ∧ tetNum w ≤ r ∧ v ≤ w ∧ triNum v ≤ r - tetNum w ∧ r - tetNum w - triNum v ≤ v := by
  subst hw_def hv_def
  have hlt65 : r < tetNum 65 := by
    change r < 47905 at hr
    have h65 : tetNum 65 = 47905 := by decide
    omega
  have hw := findUpper_spec tetNum rfl 64 r hlt65
  have hs1 := tetNum_succ (findUpper tetNum 64 r)
  have hv := findUpper_spec triNum rfl (findUpper tetNum 64 r) (r - tetNum (findUpper tetNum 64 r))
    (by omega)
  have hs2 :=
    triNum_succ (findUpper triNum (findUpper tetNum 64 r) (r - tetNum (findUpper tetNum 64 r)))
  exact ⟨hw.1, hw.2.1, hv.1, hv.2.1, by omega⟩
def tetUnrank65 (idx : Fin orbitCount47905) : CanonicalTriple65 :=
  let w := findUpper tetNum 64 idx.val
  let rem := idx.val - tetNum w
  let v := findUpper triNum w rem
  let u := rem - triNum v
  have hb := unrank_bounds idx.isLt (w := w) (v := v) rfl rfl
  ⟨⟨u, by dsimp [u, rem]; omega⟩, ⟨v, by omega⟩, ⟨w, by omega⟩, hb.2.2.2.2, hb.2.2.1⟩
def tetRank65 : CanonicalTriple65 ≃ Fin orbitCount47905 where
  toFun t := ⟨tetRankPoly t.u.val t.v.val t.w.val, by
    have h1 := tetRankPoly_lt_tetNum_succ t.uv t.vw
    have h2 : tetNum (t.w.val + 1) ≤ tetNum 65 := tetNum_mono (by omega)
    have h65 : tetNum 65 = 47905 := by decide
    change tetRankPoly t.u.val t.v.val t.w.val < 47905
    omega⟩
  invFun := tetUnrank65
  left_inv t := by
    set r := tetRankPoly t.u.val t.v.val t.w.val
    have hlt65 : r < tetNum 65 :=
      lt_of_lt_of_le (tetRankPoly_lt_tetNum_succ t.uv t.vw) (tetNum_mono (by omega))
    have hw := findUpper_spec tetNum rfl 64 r hlt65
    have hw_eq : findUpper tetNum 64 r = t.w.val :=
      findUpper_eq tetNum tetNum_mono hw.2.1 hw.2.2
        (by dsimp [r, tetRankPoly]; omega) (tetRankPoly_lt_tetNum_succ t.uv t.vw)
    set rem := r - tetNum (findUpper tetNum 64 r)
    have hrem_eq : rem = triNum t.v.val + t.u.val := by
      dsimp only [rem]
      rw [hw_eq]
      dsimp [r, tetRankPoly]
      omega
    have htri_lt : triNum t.v.val + t.u.val < triNum (t.v.val + 1) := by
      rw [triNum_succ]
      have := t.uv
      omega
    have hrem_lt : rem < triNum (findUpper tetNum 64 r + 1) := by
      rw [hw_eq, hrem_eq]
      exact lt_of_lt_of_le htri_lt (triNum_mono (by have := t.vw; omega))
    have hv := findUpper_spec triNum rfl (findUpper tetNum 64 r) rem hrem_lt
    have hv_eq : findUpper triNum (findUpper tetNum 64 r) rem = t.v.val :=
      findUpper_eq triNum triNum_mono hv.2.1 hv.2.2 (by rw [hrem_eq]; omega) (by rwa [hrem_eq])
    have hu_eq : rem - triNum (findUpper triNum (findUpper tetNum 64 r) rem) = t.u.val := by
      rw [hv_eq, hrem_eq]
      omega
    cases t with
    | mk u v w uv vw =>
      dsimp [tetUnrank65] at *
      congr 1
      · exact Fin.ext hu_eq
      · exact Fin.ext hv_eq
      · exact Fin.ext hw_eq
  right_inv idx := by
    ext
    have hb := unrank_bounds idx.isLt rfl rfl
    dsimp [tetUnrank65, tetRankPoly]
    omega
def momentumTransferBox62 : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 ↦ Finset.Icc (-62 : ℤ) 62)
theorem mem_momentumTransferBox62 {ν : Fin 3 → ℤ} :
    ν ∈ momentumTransferBox62 ↔ ∀ w, -62 ≤ ν w ∧ ν w ≤ 62 := by
  simp [momentumTransferBox62, Fintype.mem_piFinset, Finset.mem_Icc]
attribute [irreducible] momentumTransferBox62
noncomputable def w128Dual (d : FineCoord128) : ℝ := ∑ ν ∈ momentumTransferBox62,
    coulombKernel ν * Real.cos (2 * π * (∑ w : Fin 3, (ν w : ℝ) * (d w).val) / 128)
noncomputable def w128Orbit (idx : Fin orbitCount47905) : ℝ :=
  let t := tetRank65.symm idx
  let m : Fin 3 → ℕ := ![t.u.val, t.v.val, t.w.val]
  ∑ ν ∈ momentumTransferBox62,
    coulombKernel ν * ∏ w : Fin 3, Real.cos (2 * π * (ν w : ℝ) * (m w : ℝ) / 128)
theorem w128Dual_eq_orbit (d : FineCoord128) :
    w128Dual d = w128Orbit (tetRank65 (canonTriple128 d)) := by
  have hprod : w128Dual d = ∑ ν ∈ momentumTransferBox62,
      coulombKernel ν * ∏ w : Fin 3, Real.cos (2 * π * (ν w : ℝ) * (d w).val / 128) := by
    let c : Fin 3 → ℤ → ℝ := fun w n ↦ Real.cos (2 * π * (n : ℝ) * (d w).val / 128)
    let s : Fin 3 → ℤ → ℝ := fun w n ↦ Real.sin (2 * π * (n : ℝ) * (d w).val / 128)
    have hs_odd (w : Fin 3) (n : ℤ) : s w (-n) = -s w n := by
      dsimp [s]
      rw [show 2 * π * ((-n : ℤ) : ℝ) * (d w).val / 128 =
          -(2 * π * (n : ℝ) * (d w).val / 128) by push_cast; ring, Real.sin_neg]
    have hcos_expand (ν : Fin 3 → ℤ) :
        Real.cos (2 * π * (∑ w : Fin 3, (ν w : ℝ) * (d w).val) / 128) =
          c 0 (ν 0) * c 1 (ν 1) * c 2 (ν 2) - s 0 (ν 0) * s 1 (ν 1) * c 2 (ν 2) -
          s 0 (ν 0) * c 1 (ν 1) * s 2 (ν 2) - c 0 (ν 0) * s 1 (ν 1) * s 2 (ν 2) := by
      rw [show 2 * π * (∑ w : Fin 3, (ν w : ℝ) * (d w).val) / 128 =
          (2 * π * (ν 0 : ℝ) * (d 0).val / 128 + 2 * π * (ν 1 : ℝ) * (d 1).val / 128) +
            2 * π * (ν 2 : ℝ) * (d 2).val / 128 by rw [Fin.sum_univ_three]; ring,
        Real.cos_add, Real.cos_add, Real.sin_add]
      dsimp [c, s]
      ring
    have kill_axis (ax : Fin 3) (g : (Fin 3 → ℤ) → ℝ)
        (hg : ∀ ν, g (Function.update ν ax (-ν ax)) = -g ν) :
        (∑ ν ∈ momentumTransferBox62, coulombKernel ν * g ν) = 0 := by
      let f : (Fin 3 → ℤ) → (Fin 3 → ℤ) := fun ν ↦ Function.update ν ax (-ν ax)
      have hf_inv (ν : Fin 3 → ℤ) : f (f ν) = ν :=
        funext fun w ↦ by by_cases hw : w = ax <;> simp [f, hw]
      have hf_mem (ν : Fin 3 → ℤ) (hν : ν ∈ momentumTransferBox62) :
          f ν ∈ momentumTransferBox62 := by
        rw [mem_momentumTransferBox62] at hν ⊢
        intro w
        by_cases hw : w = ax
        · rw [hw]
          simp only [f, Function.update_self]
          exact ⟨by linarith [(hν ax).2], by linarith [(hν ax).1]⟩
        · simpa [f, hw] using hν w
      have hk (ν : Fin 3 → ℤ) : coulombKernel (f ν) = coulombKernel ν := by
        dsimp [coulombKernel, waveNumberSq, waveVector, dotProduct]
        congr 2
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        by_cases hw : w = ax
        · subst hw
          simp [f]
          ring
        · simp [f, hw]
      have hbij : (∑ ν ∈ momentumTransferBox62, coulombKernel ν * g ν) =
          ∑ ν ∈ momentumTransferBox62, -(coulombKernel ν * g ν) :=
        Finset.sum_bij (fun ν _ ↦ f ν) hf_mem
          (fun a _ b _ hab ↦ by rw [← hf_inv a, ← hf_inv b, hab])
          (fun b hb ↦ ⟨f b, hf_mem b hb, hf_inv b⟩)
          (fun ν _ ↦ by rw [hk ν, hg ν, mul_neg, neg_neg])
      rw [Finset.sum_neg_distrib] at hbij
      linarith
    unfold w128Dual
    simp only [hcos_expand, sub_eq_add_neg, mul_add, mul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib,
      kill_axis 0 (fun ν ↦ s 0 (ν 0) * s 1 (ν 1) * c 2 (ν 2)) (fun ν ↦ by simp [hs_odd 0]),
      kill_axis 0 (fun ν ↦ s 0 (ν 0) * c 1 (ν 1) * s 2 (ν 2)) (fun ν ↦ by simp [hs_odd 0]),
      kill_axis 1 (fun ν ↦ c 0 (ν 0) * s 1 (ν 1) * s 2 (ν 2)) (fun ν ↦ by simp [hs_odd 1]),
      neg_zero, add_zero]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    rw [Fin.prod_univ_three]
  rw [hprod]
  unfold w128Orbit
  rw [Equiv.symm_apply_apply]
  dsimp only
  rcases exists_perm_sortTriple (fun w ↦ foldMag128 (d w)) with ⟨σ, hσ⟩
  have hm (w : Fin 3) : (![((canonTriple128 d).u.val), ((canonTriple128 d).v.val),
      ((canonTriple128 d).w.val)] : Fin 3 → ℕ) w = (foldMag128 (d (σ w))).val := by
    fin_cases w
    · exact congrArg Fin.val (hσ 0)
    · exact congrArg Fin.val (hσ 1)
    · exact congrArg Fin.val (hσ 2)
  refine Finset.sum_bij (fun ν _ ↦ ν ∘ σ)
    (fun ν hν ↦ mem_momentumTransferBox62.mpr fun w ↦ mem_momentumTransferBox62.mp hν (σ w))
    (fun a _ b _ hab ↦ funext fun w ↦ by simpa using congrFun hab (σ.symm w))
    (fun b hb ↦ ⟨b ∘ σ.symm,
      mem_momentumTransferBox62.mpr fun w ↦ mem_momentumTransferBox62.mp hb (σ.symm w),
      funext fun w ↦ by simp⟩)
    fun ν _ ↦ ?_
  have hk_perm : coulombKernel (ν ∘ σ) = coulombKernel ν := by
    dsimp [coulombKernel, waveNumberSq, waveVector, dotProduct]
    congr 2
    exact Equiv.sum_comp σ (fun w ↦ 2 * π * (ν w : ℝ) / cellVolume ^ (1 / 3 : ℝ) *
      (2 * π * (ν w : ℝ) / cellVolume ^ (1 / 3 : ℝ)))
  rw [hk_perm, ← Equiv.prod_comp σ (fun w ↦ Real.cos (2 * π * (ν w : ℝ) * (d w).val / 128))]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  dsimp only [Function.comp_apply]
  rw [hm w]
  by_cases hx : (d (σ w)).val ≤ 128 - (d (σ w)).val
  · rw [show (foldMag128 (d (σ w))).val = (d (σ w)).val from min_eq_left hx]
  · rw [show (foldMag128 (d (σ w))).val = 128 - (d (σ w)).val from min_eq_right (by omega),
      Nat.cast_sub (by omega : (d (σ w)).val ≤ 128),
      show 2 * π * (ν (σ w) : ℝ) * ((128 : ℕ) - ((d (σ w)).val : ℝ)) / 128 =
        -(2 * π * (ν (σ w) : ℝ) * ((d (σ w)).val : ℝ) / 128) + (ν (σ w) : ℝ) * (2 * π) by
        push_cast; ring,
      Real.cos_add_int_mul_two_pi, Real.cos_neg]
noncomputable def subGridWeight128 (d : FineCoord128) : Fin 4 :=
  ⟨(d 0).val % 2 + (d 1).val % 2 + (d 2).val % 2, by omega⟩
def tripleParityWeight (t : CanonicalTriple65) : Fin 4 :=
  ⟨t.u.val % 2 + t.v.val % 2 + t.w.val % 2, by omega⟩
noncomputable def orbitParityWeight (idx : Fin orbitCount47905) : Fin 4 :=
  tripleParityWeight (tetRank65.symm idx)
theorem subGridWeight128_eq_orbit (d : FineCoord128) :
    subGridWeight128 d = orbitParityWeight (tetRank65 (canonTriple128 d)) := by
  unfold orbitParityWeight subGridWeight128 tripleParityWeight canonTriple128
  rw [tetRank65.symm_apply_apply]
  ext
  dsimp only
  rcases exists_perm_sortTriple (fun w ↦ foldMag128 (d w)) with ⟨σ, hσ⟩
  rw [hσ 0, hσ 1, hσ 2]
  have hsum : (∑ w : Fin 3, (foldMag128 (d (σ w))).val % 2) = ∑ w : Fin 3, (d w).val % 2 := by
    rw [Equiv.sum_comp σ (fun w ↦ (foldMag128 (d w)).val % 2)]
    exact Finset.sum_congr rfl fun w _ ↦ foldMag128_mod_two (d w)
  simpa only [Fin.sum_univ_three, Nat.add_assoc] using hsum.symm
noncomputable def canonicalNormSq65 (t : CanonicalTriple65) : ℕ :=
  t.u.val ^ 2 + t.v.val ^ 2 + t.w.val ^ 2
end Dyadic128CoulombMath
end
end ModDyadic128CoulombMath

end QuantumComputation.Specs.StoppingPowerSolution
