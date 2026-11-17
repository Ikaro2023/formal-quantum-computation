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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CoreSpecDefs

@[expose] public section
set_option exponentiation.threshold 64
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModCleanAncillaCombinators
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

/-- Compatibility alias for `basisBitsEquiv`. -/
abbrev basisBitsEquiv := basisBits
@[simp] theorem basisBits_zero_at (q : ℕ) (i : Fin q) : basisBits q 0 i = 0 := by
  simp [-Nat.reducePow, basisBits_eq_div_mod]
namespace QRegExt
open _root_.QRegister
variable {n k m : ℕ}
theorem extractIndex_eq_zero_iff (r : QRegister k n) (global : Fin (2 ^ n)) :
    r.extractIndex global = 0 ↔ ∀ i : Fin k, basisBits n global (r i) = 0 := by
  rw [← (basisBitsEquiv k).apply_eq_iff_eq, funext_iff]
  simp only [basisBitsEquiv, basisBits_extractIndex, basisBits_zero_at]
theorem extractIndex_concat_eq_zero_iff (r₁ : QRegister k n) (r₂ : QRegister m n)
    (hdisj : r₁.DisjointWires r₂) (global : Fin (2 ^ n)) : (r₁.concat r₂ hdisj).extractIndex
    global = 0 ↔ r₁.extractIndex global = 0 ∧ r₂.extractIndex global = 0 := by
  simp only [extractIndex_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa only [concat_apply_left] using h (Fin.castAdd m i)
    · simpa only [concat_apply_right] using h (Fin.natAdd k j)
  · rintro ⟨h₁, h₂⟩ idx
    refine Fin.addCases (m := k) (n := m)
      (motive := fun idx ↦ basisBits n global ((r₁.concat r₂ hdisj) idx) = 0)
      (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simpa only [concat_apply_left] using h₁ i
    · simpa only [concat_apply_right] using h₂ j
theorem basisOutcomeProjector_concat_zero (r₁ : QRegister k n) (r₂ : QRegister m n)
    (hdisj : r₁.DisjointWires r₂) : (r₁.concat r₂ hdisj).basisOutcomeProjector 0 =
    r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 := by
  rw [basisOutcomeProjector_eq_diagonal, basisOutcomeProjector_eq_diagonal,
    basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext global
  simp only [extractIndex_concat_eq_zero_iff]
  by_cases h₁ : r₁.extractIndex global = 0 <;>
    by_cases h₂ : r₂.extractIndex global = 0 <;> simp [h₁, h₂]
theorem basisOutcomeProjector_comm (r₁ : QRegister k n) (o₁ : Fin (2 ^ k))
    (r₂ : QRegister m n) (o₂ : Fin (2 ^ m)) :
    r₁.basisOutcomeProjector o₁ * r₂.basisOutcomeProjector o₂ =
      r₂.basisOutcomeProjector o₂ * r₁.basisOutcomeProjector o₁ := by
  rw [basisOutcomeProjector_eq_diagonal, basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
end QRegExt
section CleanAncillaCombinators
variable {Var : Type} [Fintype Var] {n k m : ℕ}
omit [Fintype Var] in
@[simp] theorem CQAssertionExt.restrictToBasisOutcomes_coe (M : CQAssertionCompat Var (2 ^ n))
    (register : QRegister k n) (outcomes : Finset (Fin (2 ^ k))) (σ : Store Var) :
    (CQAssertion.restrictToBasisOutcomes M register outcomes σ).1 = (M σ).1.conj
    (register.basisOutcomesProjector outcomes) := rfl
omit [Fintype Var] in
theorem restrictAssertionToZeroAncilla_comm
    (M : CQAssertionCompat Var (2 ^ n)) (r₁ : QRegister k n) (r₂ : QRegister m n) :
    CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla M r₁) r₂ =
      CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla M r₂) r₁ := by
  funext σ
  apply Subtype.ext
  simp only [CQAssertion.restrictToZeroAncilla_coe, conj_conj,
    QRegExt.basisOutcomeProjector_comm]
omit [Fintype Var] in
theorem restrictAssertionToZeroAncilla_concat (M : CQAssertionCompat Var (2 ^ n))
    (r₁ : QRegister k n) (r₂ : QRegister m n) (hdisj : r₁.DisjointWires r₂) :
    CQAssertion.restrictToZeroAncilla M (r₁.concat r₂ hdisj) = CQAssertion.restrictToZeroAncilla
    (CQAssertion.restrictToZeroAncilla M r₁) r₂ := by
  funext σ
  apply Subtype.ext
  simp only [CQAssertion.restrictToZeroAncilla_coe, conj_conj,
    QRegExt.basisOutcomeProjector_concat_zero, QRegExt.basisOutcomeProjector_comm]
end CleanAncillaCombinators
namespace DynCircuitExt
open _root_.DynamicCircuit
variable {Var : Type} {n k a : ℕ}
noncomputable def onRegister (placement : QRegister k n) : DynamicCircuit Var k →
    DynamicCircuit Var n :=
  dynMapSameVar (fun c ↦ .circuit (c.onRegister placement)) (fun v r ↦
    .measure v (placement.compose r))
@[simp] theorem onRegister_identity (placement : QRegister k n) :
    onRegister (Var := Var) placement .identity = .identity := rfl
@[simp] theorem onRegister_circuit (placement : QRegister k n) (c : Circuit k) :
    onRegister (Var := Var) placement (.circuit c) = .circuit (c.onRegister placement) := rfl
@[simp] theorem onRegister_measure (placement : QRegister k n) (v : Var) (r : QRegister 1 k) :
    onRegister placement (.measure v r) = .measure v (placement.compose r) := rfl
@[simp] theorem onRegister_dynQIfVar (placement : QRegister k n) (v : Var)
    (t f : DynamicCircuit Var k) : onRegister placement (dynQIfVar v t f) = dynQIfVar v
    (onRegister placement t) (onRegister placement f) := rfl
@[simp] theorem onRegister_seq (placement : QRegister k n) (p₁ p₂ : DynamicCircuit Var k) :
    onRegister placement (.seq p₁ p₂) =
      .seq (onRegister placement p₁) (onRegister placement p₂) := rfl
end DynCircuitExt
end
end ModCleanAncillaCombinators

section ModCleanAncillaDynamicSeq
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder
namespace QRegExt
open _root_.QRegister
variable {n k m : ℕ}
theorem embedMatrix_comm_basisOutcomeProjector_of_disjoint (rAct : QRegister k n)
    (rWork : QRegister m n) (hdisj : rAct.DisjointWires rWork)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (o : Fin (2 ^ m)) : rAct.embedMatrix A *
    rWork.basisOutcomeProjector o = rWork.basisOutcomeProjector o * rAct.embedMatrix A := by
  ext i j
  rw [basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hAgree : (rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv j).2
  · have hOutside : rAct.AgreeOutside i j := (rAct.basisSplit_environment_eq_iff i j).mp hAgree
    have hEqIdx : rWork.extractIndex i = rWork.extractIndex j := by
      rw [← (basisBitsEquiv m).apply_eq_iff_eq]
      funext idx
      simp only [basisBitsEquiv, basisBits_extractIndex]
      exact hOutside (rWork idx) (fun hmem ↦ Set.disjoint_left.mp hdisj hmem ⟨idx, rfl⟩)
    rw [hEqIdx, mul_comm]
  · simp [embedMatrix_apply, hAgree]
theorem basisOutcomeProjector_zero_mul_compose_zero {m₁ : ℕ} (rWork : QRegister m n)
    (sel : QRegister m₁ m) : rWork.basisOutcomeProjector 0 *
    (rWork.compose sel).basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 := by
  rw [basisOutcomeProjector_eq_diagonal, basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext g
  by_cases h : rWork.extractIndex g = 0
  · have hSub : (rWork.compose sel).extractIndex g = 0 := by
      rw [extractIndex_compose, h, ← (basisBitsEquiv m₁).apply_eq_iff_eq]
      funext idx
      change basisBits m₁ (sel.extractIndex 0) idx = basisBits m₁ 0 idx
      rw [basisBits_extractIndex]
      simp [-Nat.reducePow, basisBits_eq_div_mod]
    simp [h, hSub]
  · simp [h]
theorem compose_zero_mul_basisOutcomeProjector_zero {m₁ : ℕ} (rWork : QRegister m n)
    (sel : QRegister m₁ m) : (rWork.compose sel).basisOutcomeProjector 0 *
    rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 :=
  (basisOutcomeProjector_comm (rWork.compose sel) 0 rWork 0).trans
    ((QRegExt.basisOutcomeProjector_zero_mul_compose_zero rWork) sel)
end QRegExt
namespace DynCircuitExt
open _root_.DynamicCircuit
variable {Var : Type} {n k m a : ℕ}
def sequenceList : List (DynamicCircuit Var n) → DynamicCircuit Var n
  | [] => .identity
  | p :: ps => .seq p (sequenceList ps)
@[simp]
theorem sequenceList_nil : sequenceList ([] : List (DynamicCircuit Var n)) = .identity := rfl
@[simp]
theorem sequenceList_cons (p : DynamicCircuit Var n) (ps : List (DynamicCircuit Var n)) :
    sequenceList (p :: ps) = .seq p (sequenceList ps) := rfl
@[simp] theorem count_sequenceList (g : PrimitiveGate a) (ps : List (DynamicCircuit Var n)) :
    (sequenceList ps).count g = (ps.map (count g)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]
def RealizesEmbeddedUnitaryWithCleanWorkspace [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (rAct : QRegister k n) (rWork : QRegister m n) (u : Unitary (2 ^ k))
    (d : DynamicCircuit Var n) : Prop :=
      ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧ rWork.basisOutcomeProjector 0 * M'.1.1 *
    rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 *
    ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * rWork.basisOutcomeProjector
    0
section CleanWorkspaceComposition
variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
theorem realizesEmbeddedUnitaryWithCleanWorkspace_identity
    (rAct : QRegister k n) (rWork : QRegister m n) :
    RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rAct rWork 1 .identity := by
  intro M
  refine ⟨M, rfl, ?_⟩
  simp
theorem realizesEmbeddedUnitaryWithCleanWorkspace_circuit
    (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (c : Circuit n)
    (hc : c.eval = rAct.embedUnitary u) :
    RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rAct rWork u (.circuit c) := by
  intro M
  refine ⟨qAssignObsMap (rAct.embedUnitary u) M, ?_, ?_⟩
  · funext σ
    rw [compile_circuit, wp_circuit_compile_compat, hc]
    rfl
  · simp [qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
theorem RealizesEmbeddedUnitaryWithCleanWorkspace.widenWorkspace
    {m₁ : ℕ} {rAct : QRegister k n} {rWork : QRegister m n} {sel : QRegister m₁ m}
    {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace rAct (rWork.compose sel) u d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  have hL := (QRegExt.basisOutcomeProjector_zero_mul_compose_zero rWork) sel
  have hR := (QRegExt.compose_zero_mul_basisOutcomeProjector_zero rWork) sel
  have hwrap (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      rWork.basisOutcomeProjector 0 * X * rWork.basisOutcomeProjector 0 =
        rWork.basisOutcomeProjector 0 * ((rWork.compose sel).basisOutcomeProjector 0 * X *
          (rWork.compose sel).basisOutcomeProjector 0) * rWork.basisOutcomeProjector 0 := by
    calc rWork.basisOutcomeProjector 0 * X * rWork.basisOutcomeProjector 0
      _ = (rWork.basisOutcomeProjector 0 * (rWork.compose sel).basisOutcomeProjector 0) * X *
            ((rWork.compose sel).basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) := by
          rw [hL, hR]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hwrap M'.1.1, hproj, ← hwrap]
theorem RealizesEmbeddedUnitaryWithCleanWorkspace.widenActive
    {k₁ : ℕ} {rAct : QRegister k n} {sel : QRegister k₁ k} {rWork : QRegister m n}
    {u : Unitary (2 ^ k₁)} {d : DynamicCircuit Var n}
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace (rAct.compose sel) rWork u d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (sel.embedUnitary u) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  rw [← QRegister.embedUnitary_compose]
  exact hproj
theorem RealizesEmbeddedUnitaryWithCleanWorkspace.seq
    {rAct : QRegister k n} {rWork : QRegister m n} (hdisj : rAct.DisjointWires rWork)
    {u₁ u₂ : Unitary (2 ^ k)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u₁ d₁)
    (h₂ : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u₂ d₂) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (u₂ * u₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, ?_⟩
  · simp only [compile_seq, wp_qSeq, hwp₂, hwp₁]
  · let P := rWork.basisOutcomeProjector 0
    let U₁ := (rAct.embedUnitary u₁).1
    let U₂ := (rAct.embedUnitary u₂).1
    have hComm : U₁ * P = P * U₁ :=
      (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hdisj u₁.1 0
    have hCommStar : U₁ᴴ * P = P * U₁ᴴ := by
      have h := (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hdisj u₁.1ᴴ
        0
      rw [QRegister.embedMatrix_conjTranspose] at h
      exact h
    have hMul : (rAct.embedUnitary (u₂ * u₁)).1 = U₂ * U₁ := by
      simp [U₁, U₂]
    rw [hMul]
    change P * M₁.1.1 * P = P * ((U₂ * U₁)ᴴ * M.1.1 * (U₂ * U₁)) * P
    calc
      P * M₁.1.1 * P = P * (U₁ᴴ * M₂.1.1 * U₁) * P := hproj₁
      _ = (P * U₁ᴴ) * M₂.1.1 * (U₁ * P) := by simp only [Matrix.mul_assoc]
      _ = U₁ᴴ * (P * M₂.1.1 * P) * U₁ := by rw [← hCommStar, hComm]; simp only [Matrix.mul_assoc]
      _ = U₁ᴴ * (P * (U₂ᴴ * M.1.1 * U₂) * P) * U₁ := by rw [hproj₂]
      _ = (U₁ᴴ * P) * U₂ᴴ * M.1.1 * U₂ * (P * U₁) := by simp only [Matrix.mul_assoc]
      _ = P * ((U₂ * U₁)ᴴ * M.1.1 * (U₂ * U₁)) * P := by
        rw [hCommStar, ← hComm]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem RealizesEmbeddedUnitaryWithCleanWorkspace.replicate {rAct : QRegister k n}
    {rWork : QRegister m n} (hdisj : rAct.DisjointWires rWork) {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d)
    (R : ℕ) : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (u ^ R)
    (sequenceList (List.replicate R d)) := by
  induction R with
  | zero =>
      simpa using realizesEmbeddedUnitaryWithCleanWorkspace_identity (Var := Var) rAct rWork
  | succ R ih =>
      rw [List.replicate_succ, sequenceList_cons, pow_succ]
      exact hd.seq hdisj ih
end CleanWorkspaceComposition
end DynCircuitExt
end
end ModCleanAncillaDynamicSeq

section ModDyadicSubgridToeplitz128
@[expose] public section
namespace SpecsAux.DyadicSubgridToeplitz128
open Real Operator Matrix SpecsAux.SpecMirror
open scoped Matrix BigOperators
abbrev NyqGrid3D64 : Type := Fin 3 → Fin 64
abbrev NyqParity3D : Type := Fin 3 → Fin 2
abbrev NyqFine3D128 : Type := Fin 3 → Fin 128
def nyq128Join1D (yb : Fin 64 × Fin 2) : Fin 128 :=
  ⟨2 * yb.1.val + yb.2.val, by omega⟩
def nyq128Split1D (x : Fin 128) : Fin 64 × Fin 2 :=
  (⟨x.val / 2, by omega⟩,⟨x.val % 2, by omega⟩)
def nyq128Equiv1D : Fin 64 × Fin 2 ≃ Fin 128 where
  toFun := nyq128Join1D
  invFun := nyq128Split1D
  left_inv := fun ⟨y, b⟩ ↦ by ext <;> dsimp [nyq128Join1D, nyq128Split1D] <;> omega
  right_inv := fun x ↦ by ext; dsimp [nyq128Join1D, nyq128Split1D]; omega
def nyq128Join3D (yb : NyqGrid3D64 × NyqParity3D) : NyqFine3D128 :=
  fun w ↦ nyq128Equiv1D (yb.1 w, yb.2 w)
def nyq128Split3D (x : NyqFine3D128) : NyqGrid3D64 × NyqParity3D :=
  (fun w ↦ (nyq128Equiv1D.symm (x w)).1, fun w ↦ (nyq128Equiv1D.symm (x w)).2)
def nyq128Equiv3D : NyqGrid3D64 × NyqParity3D ≃ NyqFine3D128 where
  toFun := nyq128Join3D
  invFun := nyq128Split3D
  left_inv := fun ⟨y, b⟩ ↦ by ext w <;> simp [nyq128Join3D, nyq128Split3D]
  right_inv := fun x ↦ by ext w; exact congrArg Fin.val (nyq128Equiv1D.apply_symm_apply (x w))
@[simp] lemma nyq128Equiv3D_val (y : NyqGrid3D64) (b : NyqParity3D) (w : Fin 3) :
    (nyq128Equiv3D (y, b) w).val = 2 * (y w).val + (b w).val := rfl
lemma sum_nyqSubGrid64_eq_fine128 (F : NyqFine3D128 → ℂ) :
    (∑ b : NyqParity3D, ∑ y : NyqGrid3D64, F (nyq128Equiv3D (y, b))) = ∑ x : NyqFine3D128, F x := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact Equiv.sum_comp nyq128Equiv3D F
def fin3TupleEquiv (α : Type*) : (α × α × α) ≃ (Fin 3 → α) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun f := (f 0, f 1, f 2)
  left_inv p := by rcases p with ⟨a, b, c⟩; rfl
  right_inv f := by ext i; fin_cases i <;> rfl
lemma sum_fin3_prod {α : Type*} [Fintype α] (g : Fin 3 → α → ℂ) :
    (∑ x : Fin 3 → α, ∏ w : Fin 3, g w (x w)) = ∏ w : Fin 3, ∑ a : α, g w a := by
  rw [← Equiv.sum_comp (fin3TupleEquiv α), Fin.prod_univ_three]
  have h : ∀ p : α × α × α,
      ∏ w : Fin 3, g w (fin3TupleEquiv α p w) = g 0 p.1 * g 1 p.2.1 * g 2 p.2.2 :=
    fun p ↦ by rw [Fin.prod_univ_three]; rfl
  simp only [h, Fintype.sum_prod_type, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
def anchorParity1D (b₀ : Fin 2) (d : Fin 128) : Fin 2 :=
  ⟨(b₀.val + d.val) % 2, by omega⟩
def anchorParity3D (b₀ : NyqParity3D) (d : NyqFine3D128) : NyqParity3D :=
  fun w ↦ anchorParity1D (b₀ w) (d w)
def anchorSubTarget1D (y₀ : Fin 64) (b₀ : Fin 2) (d : Fin 128) : Fin 64 × Fin 2 :=
  nyq128Equiv1D.symm ⟨(2 * y₀.val + b₀.val + 128 - d.val) % 128, by omega⟩
theorem anchorSubTarget1D_fst_eq_borrow (y₀ : Fin 64) (b₀ : Fin 2) (d : Fin 128) :
    (anchorSubTarget1D y₀ b₀ d).1 =
      ⟨(y₀.val + 64 - d.val / 2 - (1 - b₀.val) * (d.val % 2)) % 64, by omega⟩ := by
  fin_cases b₀ <;> (ext; dsimp [anchorSubTarget1D, nyq128Equiv1D, nyq128Split1D]; omega)
def anchorSubTarget3D (y₀ : NyqGrid3D64) (b₀ : NyqParity3D) (d : NyqFine3D128) : NyqGrid3D64 ×
    NyqParity3D := (fun w ↦ (anchorSubTarget1D (y₀ w) (b₀ w) (d w)).1, anchorParity3D b₀ d)
@[simp] lemma nyq128Equiv3D_anchorSubTarget3D_val (y₀ : NyqGrid3D64) (b₀ : NyqParity3D)
    (d : NyqFine3D128) (w : Fin 3) : (nyq128Equiv3D (anchorSubTarget3D y₀ b₀ d) w).val =
    (2 * (y₀ w).val + (b₀ w).val + 128 - (d w).val) % 128 := by
  dsimp [anchorSubTarget3D, anchorParity3D, anchorSubTarget1D, anchorParity1D,
    nyq128Equiv3D, nyq128Join3D, nyq128Equiv1D, nyq128Join1D, nyq128Split1D]
  omega
def InMomGrid1D (p : ℤ) : Prop := -31 ≤ p ∧ p ≤ 31
def InMomGrid3D (p : Fin 3 → ℤ) : Prop := ∀ w, InMomGrid1D (p w)
def openBox1D62 : Finset ℤ := Finset.Icc (-62) 62
def openBox3D62 : Finset (Fin 3 → ℤ) :=
  (openBox1D62 ×ˢ (openBox1D62 ×ˢ openBox1D62)).map (fin3TupleEquiv ℤ).toEmbedding
lemma mem_openBox3D62_iff (ν : Fin 3 → ℤ) : ν ∈ openBox3D62 ↔ ∀ w, -62 ≤ ν w ∧ ν w ≤ 62 := by
  simp only [openBox3D62, openBox1D62, Finset.mem_map_equiv, Finset.mem_product, Finset.mem_Icc,
    fin3TupleEquiv, Equiv.coe_fn_symm_mk]
  exact ⟨fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption, fun h ↦ ⟨h 0, h 1, h 2⟩⟩
attribute [irreducible] openBox3D62
lemma sub_mem_openBox3D62 {p q : Fin 3 → ℤ} (hp : InMomGrid3D p) (hq : InMomGrid3D q) :
    p - q ∈ openBox3D62 := by
  rw [mem_openBox3D62_iff]
  intro w
  have hp' := hp w
  have hq' := hq w
  dsimp [InMomGrid1D] at hp' hq'
  change -62 ≤ p w - q w ∧ p w - q w ≤ 62
  omega
lemma inMomGrid3D_electron_of_state (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons) :
    InMomGrid3D (momentum x (.electron i)) := by
  intro w
  dsimp [InMomGrid1D, momentum, signMagnitude, componentBits, electronBits]
  set s := x.val / 2 ^ bitOffset (.electron i) w / 32 % 2
  set m := x.val / 2 ^ bitOffset (.electron i) w % 32
  have hs : s = 0 ∨ s = 1 := by omega
  have hm : m ≤ 31 := by omega
  rcases hs with h | h <;> rw [h] <;> simp <;> omega
def shiftedFin64ToInt (u : Fin 64) : ℤ := (u.val : ℤ) - 32
def shiftedMom3D (p : NyqGrid3D64) : Fin 3 → ℤ := fun w ↦ shiftedFin64ToInt (p w)
noncomputable def omega128 (d : ℤ) : ℂ := Complex.exp (2 * π * (d : ℂ) * Complex.I / 128)
@[simp] lemma omega128_zero : omega128 0 = 1 := by simp [omega128]
lemma omega128_add (a b : ℤ) : omega128 (a + b) = omega128 a * omega128 b := by
  unfold omega128
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma star_omega128 (d : ℤ) : star (omega128 d) = omega128 (-d) := by
  unfold omega128
  rw [RCLike.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat,
    Int.cast_neg]
  ring
lemma omega128_pow (d : ℤ) (n : ℕ) : (omega128 d) ^ n = omega128 (d * (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← omega128_add]
      congr 1; push_cast; ring
lemma omega128_mul_128 (k : ℤ) : omega128 (k * 128) = 1 := by
  unfold omega128
  exact Complex.exp_eq_one_iff.mpr ⟨k, by push_cast; ring⟩
lemma omega128_pow_128 (d : ℤ) : (omega128 d) ^ 128 = 1 := by
  rw [omega128_pow]
  exact omega128_mul_128 d
lemma omega128_periodic_emod (ν m : ℤ) : omega128 (ν * (m % 128)) = omega128 (ν * m) := by
  set q := m / 128
  set r := m % 128
  have hm : m = r + 128 * q := by omega
  have hmul : ν * m = ν * r + (ν * q) * 128 := by rw [hm]; ring
  rw [hmul, omega128_add, omega128_mul_128, mul_one]
lemma omega128_ne_one_of_abs_lt {d : ℤ} (hd0 : d ≠ 0) (hd1 : -128 < d) (hd2 : d < 128) :
    omega128 d ≠ 1 := by
  intro h
  rcases Complex.exp_eq_one_iff.mp h with ⟨k, hk⟩
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2piI : (2 : ℂ) * π * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hmul : (2 * (π : ℂ) * Complex.I) * ((d : ℂ) - 128 * (k : ℂ)) = 0 := by
    calc (2 * (π : ℂ) * Complex.I) * ((d : ℂ) - 128 * (k : ℂ))
      _ = 128 * (2 * π * (d : ℂ) * Complex.I / 128 - (k : ℂ) * (2 * π * Complex.I)) := by ring
      _ = 128 * 0 := by rw [sub_eq_zero.mpr hk]
      _ = 0 := by ring
  have hsub : (d : ℂ) = ((128 * k : ℤ) : ℂ) := by
    push_cast
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left h2piI)
  have hd_int : d = 128 * k := Int.cast_injective hsub
  omega
private lemma lemHex0 (r : ℂ) (n : ℕ) : (1 - r) * ∑ k ∈ Finset.range n, r ^ k = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
theorem sum_omega128_of_abs_lt {d : ℤ} (hd1 : -128 < d) (hd2 : d < 128) :
    (∑ x : Fin 128, omega128 (d * (x.val : ℤ))) = if d = 0 then 128 else 0 := by
  by_cases hd0 : d = 0
  · subst hd0; simp
  · simp only [hd0, ↓reduceIte]
    have hconv : (∑ x : Fin 128, omega128 (d * (x.val : ℤ))) =
        ∑ k ∈ Finset.range 128, (omega128 d) ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ omega128 (d * (k : ℤ))) 128]
      exact Finset.sum_congr rfl fun k _ ↦ (omega128_pow d k).symm
    rw [hconv]
    have hne : 1 - omega128 d ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (omega128_ne_one_of_abs_lt hd0 hd1 hd2))
    have hprod : (1 - omega128 d) * ∑ k ∈ Finset.range 128, (omega128 d) ^ k = 0 := by
      rw [lemHex0, omega128_pow_128, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left hne
noncomputable def nyquist128Char3D (ν : Fin 3 → ℤ) (x : NyqFine3D128) : ℂ :=
  ∏ w : Fin 3, omega128 (ν w * ((x w).val : ℤ))
lemma nyquist128Char3D_add_left (μ ν : Fin 3 → ℤ) (x : NyqFine3D128) :
    nyquist128Char3D (μ + ν) x = nyquist128Char3D μ x * nyquist128Char3D ν x := by
  unfold nyquist128Char3D
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [← omega128_add]
  congr 1; simp [add_mul]
lemma star_nyquist128Char3D (ν : Fin 3 → ℤ) (x : NyqFine3D128) :
    star (nyquist128Char3D ν x) = nyquist128Char3D (-ν) x := by
  unfold nyquist128Char3D
  rw [RCLike.star_def, map_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [← RCLike.star_def, star_omega128]
  congr 1; simp
lemma star_nyquist128Char3D_mul (ν μ : Fin 3 → ℤ) (x : NyqFine3D128) :
    star (nyquist128Char3D ν x) * nyquist128Char3D μ x = nyquist128Char3D (μ - ν) x := by
  rw [star_nyquist128Char3D, ← nyquist128Char3D_add_left]
  congr 1; ext w; simp [sub_eq_add_neg, add_comm]
lemma nyquist128Char3D_anchorSubTarget3D (ν : Fin 3 → ℤ) (y₀ : NyqGrid3D64) (b₀ : NyqParity3D)
    (d : NyqFine3D128) : nyquist128Char3D ν (nyq128Equiv3D (anchorSubTarget3D y₀ b₀ d)) =
    nyquist128Char3D ν (nyq128Equiv3D (y₀, b₀)) * nyquist128Char3D (-ν) d := by
  unfold nyquist128Char3D
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [nyq128Equiv3D_anchorSubTarget3D_val, nyq128Equiv3D_val]
  have hcast : (((2 * (y₀ w).val + (b₀ w).val + 128 - (d w).val) % 128 : ℕ) : ℤ) =
      ((2 * ((y₀ w).val : ℤ) + ((b₀ w).val : ℤ)) - ((d w).val : ℤ)) % 128 := by
    have hd : (d w).val < 128 := (d w).isLt
    omega
  rw [hcast, omega128_periodic_emod, ← omega128_add]
  congr 1; simp; ring
private lemma prod_ite_fin3 {α : Type*} [DecidableEq α] (f g : Fin 3 → α) (c : ℂ) :
    (∏ w : Fin 3, if f w = g w then c else 0) = if f = g then c ^ 3 else 0 := by
  by_cases h : f = g
  · subst h
    simp [pow_three]
  · simp only [h, ↓reduceIte, Fin.prod_univ_three]
    by_cases h0 : f 0 = g 0
    · by_cases h1 : f 1 = g 1
      · have h2 : f 2 ≠ g 2 := fun h2 ↦ h (funext fun | 0 => h0 | 1 => h1 | 2 => h2)
        simp [h0, h1, h2]
      · simp [h1]
    · simp [h0]
theorem sum_nyquist128Char3D_of_abs_lt {δ : Fin 3 → ℤ}
    (h1 : ∀ w, -128 < δ w) (h2 : ∀ w, δ w < 128) :
    (∑ x : NyqFine3D128, nyquist128Char3D δ x) = if δ = 0 then (128 ^ 3 : ℂ) else 0 := by
  unfold nyquist128Char3D
  rw [sum_fin3_prod (fun w (a : Fin 128) ↦ omega128 (δ w * (a.val : ℤ)))]
  simp_rw [fun w ↦ sum_omega128_of_abs_lt (h1 w) (h2 w)]
  simpa only [Pi.zero_apply] using prod_ite_fin3 δ 0 128
theorem sum_nyquist128Char3D_of_mem_openBox3D62 {μ ν : Fin 3 → ℤ}
    (hμ : μ ∈ openBox3D62) (hν : ν ∈ openBox3D62) :
    (∑ x : NyqFine3D128, nyquist128Char3D (μ - ν) x) = if μ = ν then (128 ^ 3 : ℂ) else 0 := by
  rw [mem_openBox3D62_iff] at hμ hν
  rw [sum_nyquist128Char3D_of_abs_lt
    (fun w ↦ by have := hμ w; have := hν w; change -128 < μ w - ν w; omega)
    (fun w ↦ by have := hμ w; have := hν w; change μ w - ν w < 128; omega)]
  simp only [sub_eq_zero]
noncomputable def subGridElem64_1D (b : Fin 2) (y : Fin 64) (p : ℤ) : ℂ :=
  (1 / (√64 : ℂ)) * omega128 (-p * (2 * (y.val : ℤ) + (b.val : ℤ)))
lemma star_subGridElem64_1D_mul (b : Fin 2) (y : Fin 64) (p q : ℤ) :
    star (subGridElem64_1D b y p) * subGridElem64_1D b y q =
      (1 / 64 : ℂ) * omega128 ((p - q) * (2 * (y.val : ℤ) + (b.val : ℤ))) := by
  unfold subGridElem64_1D
  rw [star_mul', star_omega128]
  have hstar_sqrt : star (1 / (√64 : ℂ)) = 1 / (√64 : ℂ) := by
    simp [RCLike.star_def, Complex.conj_ofReal]
  have hsq : ((√64 : ℝ) : ℂ) * ((√64 : ℝ) : ℂ) = 64 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 64)
  rw [hstar_sqrt, mul_mul_mul_comm, ← omega128_add]
  congr 1
  · rw [one_div_mul_one_div, hsq]
  · congr 1; ring
noncomputable def subGridElem64_3D (b : NyqParity3D) (y : NyqGrid3D64) (p : Fin 3 → ℤ) : ℂ :=
  ∏ w : Fin 3, subGridElem64_1D (b w) (y w) (p w)
lemma star_subGridElem64_3D_mul (b : NyqParity3D) (y : NyqGrid3D64) (p q : Fin 3 → ℤ) :
    star (subGridElem64_3D b y p) * subGridElem64_3D b y q =
      (1 / (64 ^ 3 : ℂ)) * nyquist128Char3D (p - q) (nyq128Equiv3D (y, b)) := by
  unfold subGridElem64_3D nyquist128Char3D
  rw [RCLike.star_def, map_prod, ← Finset.prod_mul_distrib]
  simp only [← RCLike.star_def, star_subGridElem64_1D_mul, nyq128Equiv3D_val, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1; norm_num
noncomputable def subGridUnitary64 (b : NyqParity3D) : Matrix NyqGrid3D64 NyqGrid3D64 ℂ :=
  Matrix.of fun y p ↦ subGridElem64_3D b y (shiftedMom3D p)
private lemma sum_fin64_geom {ζ : ℂ} (hne : ζ ≠ 1) (hpow : ζ ^ 64 = 1) :
    (∑ y : Fin 64, ζ ^ y.val) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ ζ ^ k) 64]
  have hprod : (1 - ζ) * ∑ k ∈ Finset.range 64, ζ ^ k = 0 := by
    rw [lemHex0, hpow, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne.symm)
private lemma lemHex1 (b : Fin 2) (u v : Fin 64) : (∑ y : Fin 64, (1 / 64 : ℂ) * omega128
    ((shiftedFin64ToInt u - shiftedFin64ToInt v) * (2 * (y.val : ℤ) + (b.val : ℤ)))) = if u =
    v then 1 else 0 := by
  set δ : ℤ := shiftedFin64ToInt u - shiftedFin64ToInt v
  by_cases huv : u = v
  · subst huv
    simp [δ]
  · simp only [huv, ↓reduceIte]
    have hδ0 : 2 * δ ≠ 0 := fun h ↦ huv (Fin.ext (by
      dsimp [δ, shiftedFin64ToInt] at h
      omega))
    have hpow : (omega128 (2 * δ)) ^ 64 = 1 := by
      rw [omega128_pow, show (2 * δ) * ((64 : ℕ) : ℤ) = δ * 128 by
        push_cast
        ring, omega128_mul_128]
    have hgeom := sum_fin64_geom (omega128_ne_one_of_abs_lt hδ0
      (by
        dsimp [δ, shiftedFin64ToInt]
        omega)
      (by
        dsimp [δ, shiftedFin64ToInt]
        omega)) hpow
    have hfactor (y : Fin 64) : (1 / 64 : ℂ) * omega128 (δ * (2 * (y.val : ℤ) + (b.val : ℤ))) =
        ((1 / 64 : ℂ) * omega128 (δ * (b.val : ℤ))) * (omega128 (2 * δ)) ^ y.val := by
      rw [omega128_pow, mul_assoc, ← omega128_add]
      exact congrArg ((1 / 64 : ℂ) * omega128 ·) (by ring)
    simp_rw [hfactor, ← Finset.mul_sum, hgeom, mul_zero]
theorem conjTranspose_mul_subGridUnitary64 (b : NyqParity3D) :
    (subGridUnitary64 b)ᴴ * subGridUnitary64 b = 1 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm (y : NyqGrid3D64) : (subGridUnitary64 b)ᴴ p y * subGridUnitary64 b y q =
      ∏ w : Fin 3, (1 / 64 : ℂ) * omega128 ((shiftedFin64ToInt (p w) - shiftedFin64ToInt (q w)) *
        (2 * ((y w).val : ℤ) + ((b w).val : ℤ))) := by
    simp only [Matrix.conjTranspose_apply, subGridUnitary64, Matrix.of_apply, subGridElem64_3D]
    rw [RCLike.star_def, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ ↦ by
      rw [← RCLike.star_def, star_subGridElem64_1D_mul]
      rfl
  simp_rw [hterm]
  rw [sum_fin3_prod (fun w (a : Fin 64) ↦ (1 / 64 : ℂ) *
    omega128 ((shiftedFin64ToInt (p w) - shiftedFin64ToInt (q w)) * (2 * (a.val : ℤ) +
      ((b w).val : ℤ))))]
  simp_rw [lemHex1]
  simpa only [one_pow] using prod_ite_fin3 p q 1
private lemma lemHex2 (b : Fin 2) (y₁ y₂ : Fin 64) : (∑ u : Fin 64, subGridElem64_1D b y₁
    (shiftedFin64ToInt u) * star (subGridElem64_1D b y₂ (shiftedFin64ToInt u))) = if y₁ = y₂
    then 1 else 0 := by
  have h1d (u : Fin 64) : subGridElem64_1D b y₁ (shiftedFin64ToInt u) *
      star (subGridElem64_1D b y₂ (shiftedFin64ToInt u)) =
      (1 / 64 : ℂ) * omega128 (-2 * ((y₁.val : ℤ) - (y₂.val : ℤ)) * ((u.val : ℤ) - 32)) := by
    unfold subGridElem64_1D shiftedFin64ToInt
    have hs : star (1 / (√64 : ℂ)) = 1 / (√64 : ℂ) := by simp [RCLike.star_def, Complex.conj_ofReal]
    have hsq : ((√64 : ℝ) : ℂ) * ((√64 : ℝ) : ℂ) = 64 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 64)
    rw [star_mul', star_omega128, hs, mul_mul_mul_comm, one_div_mul_one_div, hsq, ← omega128_add]
    exact congrArg ((1 / 64 : ℂ) * omega128 ·) (by ring)
  simp_rw [h1d]
  by_cases hy : y₁ = y₂
  · subst hy
    simp
  · simp only [hy, ↓reduceIte]
    set δ : ℤ := -2 * ((y₁.val : ℤ) - (y₂.val : ℤ))
    have hδ0 : δ ≠ 0 := fun h ↦ hy (Fin.ext (by
      dsimp [δ] at h
      omega))
    have hpow : (omega128 δ) ^ 64 = 1 := by
      rw [omega128_pow, show δ * ((64 : ℕ) : ℤ) = (-((y₁.val : ℤ) - (y₂.val : ℤ))) * 128 by
        dsimp [δ]
        ring, omega128_mul_128]
    have hgeom := sum_fin64_geom (omega128_ne_one_of_abs_lt hδ0
      (by
        dsimp [δ]
        omega)
      (by
        dsimp [δ]
        omega)) hpow
    have hfactor (u : Fin 64) : (1 / 64 : ℂ) * omega128 (δ * ((u.val : ℤ) - 32)) =
        ((1 / 64 : ℂ) * omega128 (-32 * δ)) * (omega128 δ) ^ u.val := by
      rw [omega128_pow, mul_assoc (1 / 64 : ℂ), ← omega128_add]
      exact congrArg ((1 / 64 : ℂ) * omega128 ·) (by ring)
    simp_rw [hfactor, ← Finset.mul_sum, hgeom, mul_zero]
theorem subGridUnitary64_mul_conjTranspose (b : NyqParity3D) :
    subGridUnitary64 b * (subGridUnitary64 b)ᴴ = 1 := by
  ext y₁ y₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm (u : NyqGrid3D64) : subGridUnitary64 b y₁ u * (subGridUnitary64 b)ᴴ u y₂ =
      ∏ w : Fin 3, subGridElem64_1D (b w) (y₁ w) (shiftedFin64ToInt (u w)) *
        star (subGridElem64_1D (b w) (y₂ w) (shiftedFin64ToInt (u w))) := by
    simp only [Matrix.conjTranspose_apply, subGridUnitary64, Matrix.of_apply, subGridElem64_3D,
      shiftedMom3D]
    rw [RCLike.star_def, map_prod, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [sum_fin3_prod (fun w (a : Fin 64) ↦
    subGridElem64_1D (b w) (y₁ w) (shiftedFin64ToInt a) *
      star (subGridElem64_1D (b w) (y₂ w) (shiftedFin64ToInt a)))]
  simp_rw [lemHex2]
  simpa only [one_pow] using prod_ite_fin3 y₁ y₂ 1
noncomputable def dualWeight128Fine (K : (Fin 3 → ℤ) → ℂ) (x : NyqFine3D128) : ℂ :=
  ∑ ν ∈ openBox3D62, K ν * star (nyquist128Char3D ν x)
noncomputable def dualWeight128 (K : (Fin 3 → ℤ) → ℂ) (b : NyqParity3D) (y : NyqGrid3D64) : ℂ :=
  dualWeight128Fine K (nyq128Equiv3D (y, b))
noncomputable def subGridAvgToeplitz128 (K : (Fin 3 → ℤ) → ℂ) (p q : Fin 3 → ℤ) : ℂ :=
  (1 / 8 : ℂ) * ∑ b : NyqParity3D, ∑ y : NyqGrid3D64,
    star (subGridElem64_3D b y p) * dualWeight128 K b y * subGridElem64_3D b y q
private lemma sum_dualWeight128Fine_orth (K : (Fin 3 → ℤ) → ℂ) {μ : Fin 3 → ℤ}
    (hμ : μ ∈ openBox3D62) :
    (∑ x : NyqFine3D128, dualWeight128Fine K x * nyquist128Char3D μ x) =
      (128 ^ 3 : ℂ) * K μ := by
  unfold dualWeight128Fine
  simp only [Finset.sum_mul, mul_assoc, star_nyquist128Char3D_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun ν hν ↦
    congrArg (K ν * ·) (sum_nyquist128Char3D_of_mem_openBox3D62 hμ hν)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hμ, ↓reduceIte]
  ring
theorem subGridAvgToeplitz128_eq_openBox (K : (Fin 3 → ℤ) → ℂ) {p q : Fin 3 → ℤ}
    (hp : InMomGrid3D p) (hq : InMomGrid3D q) : subGridAvgToeplitz128 K p q = K (p - q) := by
  unfold subGridAvgToeplitz128 dualWeight128
  have hterm (b : NyqParity3D) (y : NyqGrid3D64) :
      star (subGridElem64_3D b y p) * dualWeight128Fine K (nyq128Equiv3D (y, b)) *
          subGridElem64_3D b y q =
        (1 / (64 ^ 3 : ℂ)) * (dualWeight128Fine K (nyq128Equiv3D (y, b)) *
          nyquist128Char3D (p - q) (nyq128Equiv3D (y, b))) := by
    rw [mul_right_comm, star_subGridElem64_3D_mul]
    ring
  simp only [hterm, ← Finset.mul_sum]
  rw [sum_nyqSubGrid64_eq_fine128 (fun x ↦ dualWeight128Fine K x * nyquist128Char3D (p - q) x),
    sum_dualWeight128Fine_orth K (sub_mem_openBox3D62 hp hq)]
  ring
lemma stepNumberSq_neg (ν : Fin 3 → ℤ) : waveNumberSq (-ν) = waveNumberSq ν := by
  unfold waveNumberSq waveVector dotProduct
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp; ring
lemma coulombKernel_neg (ν : Fin 3 → ℤ) : coulombKernel (-ν) = coulombKernel ν := by
  unfold coulombKernel; rw [stepNumberSq_neg]
lemma neg_mem_openBox3D62_iff (ν : Fin 3 → ℤ) : -ν ∈ openBox3D62 ↔ ν ∈ openBox3D62 := by
  simp only [mem_openBox3D62_iff, Pi.neg_apply]; exact forall_congr' fun w ↦ by omega
theorem star_dualWeight128Fine_of_even_real {K : (Fin 3 → ℤ) → ℝ} (hEven : ∀ ν, K (-ν) = K ν)
    (x : NyqFine3D128) : star (dualWeight128Fine (fun ν ↦ (K ν : ℂ)) x) = dualWeight128Fine
    (fun ν ↦ (K ν : ℂ)) x := by
  unfold dualWeight128Fine
  rw [star_sum]
  have hterm : ∀ ν : Fin 3 → ℤ,
      star ((K ν : ℂ) * star (nyquist128Char3D ν x)) =
        (K (-ν) : ℂ) * star (nyquist128Char3D (-ν) x) := fun ν ↦ by
    rw [star_mul', RCLike.star_def, Complex.conj_ofReal, ← RCLike.star_def, star_star,
      ← star_nyquist128Char3D, star_star, hEven ν]
  simp_rw [hterm]
  refine Finset.sum_nbij (-·) (fun ν hν ↦ (neg_mem_openBox3D62_iff ν).mpr hν)
    (fun _ _ _ _ h ↦ neg_injective h) ?_ (fun _ _ ↦ rfl)
  intro ν hν; exact ⟨-ν, (neg_mem_openBox3D62_iff ν).mpr hν, neg_neg ν⟩
noncomputable def coulombDual128Real (x : NyqFine3D128) : ℝ :=
  (dualWeight128Fine (fun ν ↦ (coulombKernel ν : ℂ)) x).re
theorem ofReal_coulombDual128Real (x : NyqFine3D128) :
    (coulombDual128Real x : ℂ) = dualWeight128Fine (fun ν ↦ (coulombKernel ν : ℂ)) x := by
  have h := star_dualWeight128Fine_of_even_real coulombKernel_neg x
  rw [RCLike.star_def] at h
  exact Complex.conj_eq_iff_re.mp h
noncomputable def oneElectronPhase (R : Fin 3 → ℝ) (p : Fin 3 → ℤ) : ℂ :=
  Complex.exp (-(waveVector p ⬝ᵥ R) * Complex.I)
lemma oneElectronPhase_mul_star (R : Fin 3 → ℝ) (p q : Fin 3 → ℤ) :
    oneElectronPhase R p * star (oneElectronPhase R q) = oneElectronPhase R (p - q) := by
  have hsub : waveVector (p - q) ⬝ᵥ R = waveVector p ⬝ᵥ R - waveVector q ⬝ᵥ R := by
    have hw : waveVector (p - q) = waveVector p - waveVector q := by
      funext w; simp only [waveVector, Pi.sub_apply, Int.cast_sub]; ring
    rw [hw, sub_dotProduct]
  have hstar : star (oneElectronPhase R q) = Complex.exp ((waveVector q ⬝ᵥ R) * Complex.I) := by
    unfold oneElectronPhase
    rw [RCLike.star_def, ← Complex.exp_conj]
    congr 1; simp [Complex.conj_ofReal]
  rw [hstar, oneElectronPhase, oneElectronPhase, ← Complex.exp_add, hsub]
  congr 1; push_cast; ring
def kHead128 (K128 : NyqFine3D128 → ℝ) (kCut : NyqParity3D → ℝ) (x : NyqFine3D128) : ℝ :=
  max (K128 x - kCut (nyq128Equiv3D.symm x).2) 0
def kTail128 (K128 : NyqFine3D128 → ℝ) (kCut : NyqParity3D → ℝ) (x : NyqFine3D128) : ℝ :=
  min (K128 x) (kCut (nyq128Equiv3D.symm x).2)
noncomputable def kTailShifted128 (K128 : NyqFine3D128 → ℝ) (kCut kMin : NyqParity3D → ℝ)
    (x : NyqFine3D128) : ℝ :=
  let b := (nyq128Equiv3D.symm x).2
  kTail128 K128 kCut x - (kCut b + kMin b) / 2
theorem kHead128_add_kTail128 (K128 : NyqFine3D128 → ℝ) (kCut : NyqParity3D → ℝ)
    (x : NyqFine3D128) : kHead128 K128 kCut x + kTail128 K128 kCut x = K128 x := by
  dsimp [kHead128, kTail128]
  rcases le_total (kCut (nyq128Equiv3D.symm x).2) (K128 x) with hle | hle
  · rw [max_eq_left (by linarith), min_eq_right hle]; ring
  · rw [max_eq_right (by linarith), min_eq_left hle]; ring
noncomputable def singleAnchorPairSubElem128 (W : NyqFine3D128 → ℂ) (pᵢ qᵢ pⱼ qⱼ : Fin 3 → ℤ)
    : ℂ := (1 / 64 : ℂ) * ∑ b₀ : NyqParity3D, ∑ d : NyqFine3D128, W d * ∑ y₀ : NyqGrid3D64,
    (star (subGridElem64_3D b₀ y₀ pᵢ) * subGridElem64_3D b₀ y₀ qᵢ) * (star (subGridElem64_3D
    (anchorSubTarget3D y₀ b₀ d).2 (anchorSubTarget3D y₀ b₀ d).1 pⱼ) * subGridElem64_3D
    (anchorSubTarget3D y₀ b₀ d).2 (anchorSubTarget3D y₀ b₀ d).1 qⱼ)
theorem singleAnchorPairSubElem128_dualWeight128_eq (K : (Fin 3 → ℤ) → ℂ)
    {pᵢ qᵢ pⱼ qⱼ : Fin 3 → ℤ} (hpᵢ : InMomGrid3D pᵢ) (hqᵢ : InMomGrid3D qᵢ)
    (hpⱼ : InMomGrid3D pⱼ) (hqⱼ : InMomGrid3D qⱼ) : singleAnchorPairSubElem128
    (dualWeight128Fine K) pᵢ qᵢ pⱼ qⱼ = if pᵢ + pⱼ = qᵢ + qⱼ then K (pᵢ - qᵢ) else 0 := by
  unfold singleAnchorPairSubElem128
  have inner_eq (b₀ : NyqParity3D) (d : NyqFine3D128) (y₀ : NyqGrid3D64) :
      (star (subGridElem64_3D b₀ y₀ pᵢ) * subGridElem64_3D b₀ y₀ qᵢ) *
        (star (subGridElem64_3D (anchorSubTarget3D y₀ b₀ d).2 (anchorSubTarget3D y₀ b₀ d).1 pⱼ) *
          subGridElem64_3D (anchorSubTarget3D y₀ b₀ d).2 (anchorSubTarget3D y₀ b₀ d).1 qⱼ) =
      (1 / (64 ^ 6 : ℂ)) *
        nyquist128Char3D (pᵢ - qᵢ + (pⱼ - qⱼ)) (nyq128Equiv3D (y₀, b₀)) *
        nyquist128Char3D (-(pⱼ - qⱼ)) d := by
    rw [star_subGridElem64_3D_mul, star_subGridElem64_3D_mul, Prod.mk.eta,
      nyquist128Char3D_anchorSubTarget3D, nyquist128Char3D_add_left]
    ring
  simp_rw [inner_eq]
  have factor_b (b₀ : NyqParity3D) :
      (∑ d : NyqFine3D128, dualWeight128Fine K d * ∑ y₀ : NyqGrid3D64,
        (1 / (64 ^ 6 : ℂ)) * nyquist128Char3D (pᵢ - qᵢ + (pⱼ - qⱼ)) (nyq128Equiv3D (y₀, b₀)) *
          nyquist128Char3D (-(pⱼ - qⱼ)) d) =
      (1 / (64 ^ 6 : ℂ)) * (∑ y₀ : NyqGrid3D64,
        nyquist128Char3D (pᵢ - qᵢ + (pⱼ - qⱼ)) (nyq128Equiv3D (y₀, b₀))) *
        (∑ d : NyqFine3D128, dualWeight128Fine K d * nyquist128Char3D (-(pⱼ - qⱼ)) d) := by
    have h1 (d : NyqFine3D128) : dualWeight128Fine K d *
        (∑ y₀ : NyqGrid3D64, (1 / (64 ^ 6 : ℂ)) *
          nyquist128Char3D (pᵢ - qᵢ + (pⱼ - qⱼ)) (nyq128Equiv3D (y₀, b₀)) *
          nyquist128Char3D (-(pⱼ - qⱼ)) d) =
        ((1 / (64 ^ 6 : ℂ)) * ∑ y₀ : NyqGrid3D64,
          nyquist128Char3D (pᵢ - qᵢ + (pⱼ - qⱼ)) (nyq128Equiv3D (y₀, b₀))) *
          (dualWeight128Fine K d * nyquist128Char3D (-(pⱼ - qⱼ)) d) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    simp_rw [h1, ← Finset.mul_sum]
  simp_rw [factor_b, ← Finset.sum_mul, ← Finset.mul_sum, sum_nyqSubGrid64_eq_fine128]
  rw [sum_nyquist128Char3D_of_abs_lt (δ := pᵢ - qᵢ + (pⱼ - qⱼ))
    (fun w ↦ by
      have h1 := hpᵢ w
      have h2 := hqᵢ w
      have h3 := hpⱼ w
      have h4 := hqⱼ w
      dsimp [InMomGrid1D] at *
      simp
      omega)
    (fun w ↦ by
      have h1 := hpᵢ w
      have h2 := hqᵢ w
      have h3 := hpⱼ w
      have h4 := hqⱼ w
      dsimp [InMomGrid1D] at *
      simp
      omega)]
  by_cases hcons : pᵢ + pⱼ = qᵢ + qⱼ
  · have hz : pᵢ - qᵢ + (pⱼ - qⱼ) = 0 := funext fun w ↦ by
      have hw := congrFun hcons w
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hw ⊢
      omega
    have hneg : -(pⱼ - qⱼ) = pᵢ - qᵢ := funext fun w ↦ by
      have hw := congrFun hcons w
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at hw ⊢
      omega
    rw [ite_eq_left hz, ite_eq_left hcons, hneg,
      sum_dualWeight128Fine_orth K (sub_mem_openBox3D62 hpᵢ hqᵢ)]
    ring
  · have hnz : pᵢ - qᵢ + (pⱼ - qⱼ) ≠ 0 := fun hz ↦ hcons (funext fun w ↦ by
      have hw := congrFun hz w
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hw ⊢
      omega)
    simp [hcons, hnz]
open Classical in
noncomputable def uEnManyBody (c : Configuration) : Operator (2 ^ systemQubits) := Matrix.of
    fun x y ↦ if IsGridState x ∧ IsGridState y then ∑ i : Fin numElectrons, if ∀ b ≠
    Particle.electron i, momentum x b = momentum y b then -(structureFactor c (momentum x
    (.electron i) - momentum y (.electron i)) * (coulombKernel (momentum x (.electron i) -
    momentum y (.electron i)) : ℂ)) else 0 else 0
open Classical in
noncomputable def vEeManyBody : Operator (2 ^ systemQubits) := Matrix.of fun x y ↦ if
    IsGridState x ∧ IsGridState y then ∑ i : Fin numElectrons, ∑ j : Fin numElectrons, if i ≠
    j ∧ (∀ d, d ≠ Particle.electron i → d ≠ Particle.electron j → momentum x d = momentum y d)
    ∧ momentum x (.electron i) + momentum x (.electron j) = momentum y (.electron i) +
    momentum y (.electron j) then (coulombKernel (momentum x (.electron i) - momentum y
    (.electron i)) : ℂ) / 2 else 0 else 0
end SpecsAux.DyadicSubgridToeplitz128
end
end ModDyadicSubgridToeplitz128

section ModDyadicSubgridToeplitz512AndShift
@[expose] public section
namespace SpecsAux.DyadicSubgridToeplitz512AndShift
open Real Operator Matrix SpecsAux.SpecMirror
open scoped Matrix BigOperators
abbrev NyqGrid3D256 : Type := Fin 3 → Fin 256
abbrev NyqFine3D512 : Type := Fin 3 → Fin 512
def nyq512ProjEquiv3D : NyqGrid3D256 × (Fin 3 → Fin 2) ≃ NyqFine3D512 where
  toFun p w := ⟨2 * (p.1 w).val + (p.2 w).val, by omega⟩
  invFun x := (fun w ↦ ⟨(x w).val / 2, by omega⟩, fun w ↦ ⟨(x w).val % 2, by omega⟩)
  left_inv := fun ⟨y, b⟩ ↦ by ext w <;> dsimp <;> omega
  right_inv := fun x ↦ by ext w; dsimp; omega
lemma sum_nyqProj256_eq_fine512 (F : NyqFine3D512 → ℂ) : (∑ b : Fin 3 → Fin 2, ∑ y :
    NyqGrid3D256, F (nyq512ProjEquiv3D (y, b))) = ∑ x : NyqFine3D512, F x := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact Equiv.sum_comp nyq512ProjEquiv3D F
lemma sum_fin3_prod512 {α : Type*} [Fintype α] (g : Fin 3 → α → ℂ) :
    (∑ x : Fin 3 → α, ∏ w : Fin 3, g w (x w)) = ∏ w : Fin 3, ∑ a : α, g w a :=
  DyadicSubgridToeplitz128.sum_fin3_prod g
noncomputable def omega512 (d : ℤ) : ℂ := Complex.exp (2 * π * (d : ℂ) * Complex.I / 512)
@[simp] lemma omega512_zero : omega512 0 = 1 := by simp [omega512]
lemma omega512_add (a b : ℤ) : omega512 (a + b) = omega512 a * omega512 b := by
  unfold omega512; rw [← Complex.exp_add]; congr 1; push_cast; ring
lemma star_omega512 (d : ℤ) : star (omega512 d) = omega512 (-d) := by
  unfold omega512
  rw [RCLike.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat,
    Int.cast_neg]
  ring
lemma omega512_pow (d : ℤ) (n : ℕ) : (omega512 d) ^ n = omega512 (d * (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← omega512_add]; congr 1; push_cast; ring
lemma omega512_mul_512 (k : ℤ) : omega512 (k * 512) = 1 :=
  Complex.exp_eq_one_iff.mpr ⟨k, by push_cast; ring⟩
lemma omega512_periodic_emod (ν m : ℤ) : omega512 (ν * (m % 512)) = omega512 (ν * m) := by
  set q := m / 512
  set r := m % 512
  have hm : m = r + 512 * q := by omega
  have hmul : ν * m = ν * r + (ν * q) * 512 := by rw [hm]; ring
  rw [hmul, omega512_add, omega512_mul_512, mul_one]
lemma omega512_ne_one_of_abs_lt {d : ℤ} (hd0 : d ≠ 0) (hd1 : -512 < d) (hd2 : d < 512) :
    omega512 d ≠ 1 := by
  intro h
  rcases Complex.exp_eq_one_iff.mp h with ⟨k, hk⟩
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2piI : (2 : ℂ) * π * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hmul : (2 * (π : ℂ) * Complex.I) * ((d : ℂ) - 512 * (k : ℂ)) = 0 := by
    calc (2 * (π : ℂ) * Complex.I) * ((d : ℂ) - 512 * (k : ℂ))
      _ = 512 * (2 * π * (d : ℂ) * Complex.I / 512 - (k : ℂ) * (2 * π * Complex.I)) := by ring
      _ = 512 * 0 := by rw [sub_eq_zero.mpr hk]
      _ = 0 := by ring
  have hsub : (d : ℂ) = ((512 * k : ℤ) : ℂ) := by
    push_cast
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left h2piI)
  have hd_int : d = 512 * k := Int.cast_injective hsub
  omega
private lemma lemHex3 (r : ℂ) (n : ℕ) : (1 - r) * ∑ k ∈ Finset.range n, r ^ k = 1 - r ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
theorem sum_omega512_of_abs_lt {d : ℤ} (hd1 : -512 < d) (hd2 : d < 512) :
    (∑ x : Fin 512, omega512 (d * (x.val : ℤ))) = if d = 0 then 512 else 0 := by
  by_cases hd0 : d = 0
  · subst hd0; simp
  · simp only [hd0, ↓reduceIte]
    have hconv : (∑ x : Fin 512, omega512 (d * (x.val : ℤ))) =
        ∑ k ∈ Finset.range 512, (omega512 d) ^ k := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ omega512 (d * (k : ℤ))) 512]
      exact Finset.sum_congr rfl fun k _ ↦ (omega512_pow d k).symm
    rw [hconv]
    have hne : 1 - omega512 d ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (omega512_ne_one_of_abs_lt hd0 hd1 hd2))
    have h512 : d * ((512 : ℕ) : ℤ) = d * 512 := by push_cast; ring
    have hprod : (1 - omega512 d) * ∑ k ∈ Finset.range 512, (omega512 d) ^ k = 0 := by
      rw [lemHex3, omega512_pow, h512, omega512_mul_512, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left hne
noncomputable def nyquist512Char3D (ν : Fin 3 → ℤ) (x : NyqFine3D512) : ℂ :=
  ∏ w : Fin 3, omega512 (ν w * ((x w).val : ℤ))
lemma nyquist512Char3D_add_left (μ ν : Fin 3 → ℤ) (x : NyqFine3D512) :
    nyquist512Char3D (μ + ν) x = nyquist512Char3D μ x * nyquist512Char3D ν x := by
  unfold nyquist512Char3D
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [← omega512_add]; congr 1; simp [add_mul]
theorem sum_nyquist512Char3D_of_abs_lt {δ : Fin 3 → ℤ}
    (h1 : ∀ w, -512 < δ w) (h2 : ∀ w, δ w < 512) :
    (∑ x : NyqFine3D512, nyquist512Char3D δ x) = if δ = 0 then (512 ^ 3 : ℂ) else 0 := by
  unfold nyquist512Char3D
  rw [sum_fin3_prod512 (fun w (a : Fin 512) ↦ omega512 (δ w * (a.val : ℤ)))]
  simp_rw [fun w ↦ sum_omega512_of_abs_lt (h1 w) (h2 w)]
  simpa only [Pi.zero_apply] using DyadicSubgridToeplitz128.prod_ite_fin3 δ 0 512
def InProjMomGrid3D (p : Fin 3 → ℤ) : Prop := ∀ w, -127 ≤ p w ∧ p w ≤ 127
def InElecMomGrid3D (p : Fin 3 → ℤ) : Prop := ∀ w, -31 ≤ p w ∧ p w ≤ 31
lemma inProjMomGrid3D_of_state (x : Fin (2 ^ systemQubits)) :
    InProjMomGrid3D (momentum x .projectile) := by
  intro w
  dsimp [momentum, signMagnitude, componentBits, projectileBits]
  set s := x.val / 2 ^ bitOffset .projectile w / 128 % 2
  set m := x.val / 2 ^ bitOffset .projectile w % 128
  have hs : s = 0 ∨ s = 1 := by omega
  have hm : m ≤ 127 := by omega
  rcases hs with h | h <;> rw [h] <;> simp <;> omega
noncomputable def projSubGridElem256_3D (b : Fin 3 → Fin 2) (y : NyqGrid3D256)
    (p : Fin 3 → ℤ) : ℂ :=
  ∏ w : Fin 3, (1 / (√256 : ℂ)) * omega512 (-p w * (2 * ((y w).val : ℤ) + ((b w).val : ℤ)))
lemma star_projSubGridElem256_3D_mul (b : Fin 3 → Fin 2) (y : NyqGrid3D256) (p q : Fin 3 → ℤ) :
    star (projSubGridElem256_3D b y p) * projSubGridElem256_3D b y q =
      (1 / (256 ^ 3 : ℂ)) * nyquist512Char3D (p - q) (nyq512ProjEquiv3D (y, b)) := by
  unfold projSubGridElem256_3D nyquist512Char3D
  rw [RCLike.star_def, map_prod, ← Finset.prod_mul_distrib]
  have h1d : ∀ w : Fin 3,
      star ((1 / (√256 : ℂ)) * omega512 (-p w * (2 * ((y w).val : ℤ) + ((b w).val : ℤ)))) *
        ((1 / (√256 : ℂ)) * omega512 (-q w * (2 * ((y w).val : ℤ) + ((b w).val : ℤ)))) =
      (1 / 256 : ℂ) * omega512 ((p w - q w) * (((nyq512ProjEquiv3D (y, b) w).val : ℤ))) :=
    fun w ↦ by
      rw [star_mul', star_omega512]
      have hs : star (1 / (√256 : ℂ)) = 1 / (√256 : ℂ) := by
        simp [RCLike.star_def, Complex.conj_ofReal]
      have hsq : ((√256 : ℝ) : ℂ) * ((√256 : ℝ) : ℂ) = 256 := by
        exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 256)
      rw [hs, mul_mul_mul_comm, ← omega512_add]
      congr 1
      · rw [one_div_mul_one_div, hsq]
      · dsimp [nyq512ProjEquiv3D]; congr 1; ring
  simp only [← RCLike.star_def, h1d]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1; norm_num
end SpecsAux.DyadicSubgridToeplitz512AndShift
end
end ModDyadicSubgridToeplitz512AndShift

section ModFullScaleBESector
@[expose] public section
namespace FullScaleBESectorAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
end FullScaleBESectorAlt
namespace SpecsAux
open Operator Matrix SpecsAux.SpecMirror
namespace FullScaleBESector
open scoped Matrix.Norms.L2Operator
def AgreesOnFermionicSector (spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons))
    (A B : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) (ε : ℝ) : Prop :=
  let P := SpecsAux.SpecMirror.fermionicProjector spinUp
  A * P = P * A ∧ ‖P * (A - B) * P‖ ≤ ε
theorem agreesOnFermionicSector_trans {spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons)}
    {A B C : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)} {ε₁ ε₂ : ℝ}
    (h₁ : AgreesOnFermionicSector spinUp A B ε₁) (h₂ : AgreesOnFermionicSector spinUp B C ε₂)
    : AgreesOnFermionicSector spinUp A C (ε₁ + ε₂) := by
  refine ⟨h₁.1, ?_⟩
  let P := SpecsAux.SpecMirror.fermionicProjector spinUp
  have hsplit : P * (A - C) * P = P * (A - B) * P + P * (B - C) * P := by
    dsimp only [P]
    noncomm_ring
  calc ‖P * (A - C) * P‖
      = ‖P * (A - B) * P + P * (B - C) * P‖ := by rw [hsplit]
    _ ≤ ‖P * (A - B) * P‖ + ‖P * (B - C) * P‖ := norm_add_le _ _
    _ ≤ ε₁ + ε₂ := add_le_add h₁.2 h₂.2
def IsQubitizedBlockEncodingUnitary {k m : ℕ} (α : ℝ) (A : Operator (2 ^ k))
    (U : Unitary (2 ^ (k + m))) : Prop :=
  let P := (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector 0
  let sysA := (QRegister.block 0 k (by omega) : QRegister k (k + m)).embedMatrix A
  0 < α ∧ U.1ᴴ = U.1 ∧ P * U.1 * P = (α : ℂ)⁻¹ • (P * sysA * P)
noncomputable def phaseGradientState (b : ℕ) : Fin (2 ^ b) → ℂ :=
  fun k ↦ (Real.sqrt (2 ^ b) : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * k.val) / 2 ^ b)
theorem extractIndex_eq_zero_iff {k n : ℕ} (r : QRegister k n) (global : Fin (2 ^ n)) :
    r.extractIndex global = 0 ↔ ∀ i : Fin k, basisBits n global (r i) = 0 :=
  (QRegExt.extractIndex_eq_zero_iff r) global
noncomputable def zeroEnvIdx {k m : ℕ} (x : Fin (2 ^ k)) : Fin (2 ^ (k + m)) :=
  ((QRegister.block 0 k (by omega) : QRegister k (k + m)).basisSplitEquiv).symm (x, fun _ ↦ 0)
theorem block_high_not_mem_block_low {k m : ℕ} (j : Fin m) :
    (QRegister.block k m le_rfl : QRegister m (k + m)) j ∉
      Set.range (QRegister.block 0 k (by omega) : QRegister k (k + m)).wires := by
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  have hilt : i.val < k := i.isLt
  simp [FullScaleBESectorAlt.qreg_block_apply] at hval
  omega
theorem block_high_extractIndex_of_env_zero {k m : ℕ} (g : Fin (2 ^ (k + m))) (henv :
    ((QRegister.block 0 k (by omega) : QRegister k (k + m)).basisSplitEquiv g).2 = fun _ ↦ 0)
    : (QRegister.block k m le_rfl : QRegister m (k + m)).extractIndex g = 0 := by
  let rSys : QRegister k (k + m) := QRegister.block 0 k (by omega)
  let rBlock : QRegister m (k + m) := QRegister.block k m le_rfl
  rw [extractIndex_eq_zero_iff]
  intro j
  have hnot := block_high_not_mem_block_low (k := k) j
  have hsnd := congrFun henv ⟨rBlock j, hnot⟩
  rwa [QRegister.basisSplitEquiv_apply_snd] at hsnd
theorem block_high_extractIndex_zeroEnvIdx {k m : ℕ} (x : Fin (2 ^ k)) :
    (QRegister.block k m le_rfl : QRegister m (k + m)).extractIndex
      (zeroEnvIdx (m := m) x) = 0 := by
  apply block_high_extractIndex_of_env_zero
  unfold zeroEnvIdx
  rw [Equiv.apply_symm_apply]
theorem sandwich_zero_embedMatrix_apply {k m : ℕ} (M : Operator (2 ^ k)) (x y : Fin (2 ^ k)) :
    let rSys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let rBlock : QRegister m (k + m) := QRegister.block k m le_rfl
    let P₀ := rBlock.basisOutcomeProjector 0
    (P₀ * rSys.embedMatrix M * P₀) (zeroEnvIdx (m := m) x) (zeroEnvIdx (m := m) y) = M x y := by
  intro rSys rBlock P₀
  have hx0 : rBlock.extractIndex (zeroEnvIdx (m := m) x) = 0 :=
    block_high_extractIndex_zeroEnvIdx x
  have hy0 : rBlock.extractIndex (zeroEnvIdx (m := m) y) = 0 :=
    block_high_extractIndex_zeroEnvIdx y
  have hfst_x : rSys.extractIndex (zeroEnvIdx (m := m) x) = x := by
    unfold zeroEnvIdx
    rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have hfst_y : rSys.extractIndex (zeroEnvIdx (m := m) y) = y := by
    unfold zeroEnvIdx
    rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have hsnd_eq : (rSys.basisSplitEquiv (zeroEnvIdx (m := m) x)).2 =
      (rSys.basisSplitEquiv (zeroEnvIdx (m := m) y)).2 := by
    unfold zeroEnvIdx
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [P₀, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul,
    Matrix.mul_diagonal, hx0, hy0, ↓reduceIte, one_mul, mul_one,
    QRegister.embedMatrix_apply, hsnd_eq, hfst_x, hfst_y]
theorem embedMatrix_sandwich_zero_inj {k m : ℕ} (A B : Operator (2 ^ k))
    (h :
      let rSys : QRegister k (k + m) := QRegister.block 0 k (by omega)
      let rBlock : QRegister m (k + m) := QRegister.block k m le_rfl
      let P₀ := rBlock.basisOutcomeProjector 0
      P₀ * rSys.embedMatrix A * P₀ = P₀ * rSys.embedMatrix B * P₀) :
    A = B := by
  ext x y
  have hxy := congrFun (congrFun h (zeroEnvIdx (m := m) x)) (zeroEnvIdx (m := m) y)
  rwa [sandwich_zero_embedMatrix_apply, sandwich_zero_embedMatrix_apply] at hxy
theorem isHermitian_of_isQubitizedBlockEncodingUnitary {k m : ℕ} {α E₀ : ℝ}
    {Heff : Operator (2 ^ k)} {U_BE : Unitary (2 ^ (k + m))} (hBE :
    IsQubitizedBlockEncodingUnitary α (Heff - (E₀ : ℂ) • (1 : Operator (2 ^ k))) U_BE) :
    Heff.IsHermitian := by
  let rSys : QRegister k (k + m) := QRegister.block 0 k (by omega)
  let rBlock : QRegister m (k + m) := QRegister.block k m le_rfl
  let P₀ := rBlock.basisOutcomeProjector 0
  let A : Operator (2 ^ k) := Heff - (E₀ : ℂ) • (1 : Operator (2 ^ k))
  rcases hBE with ⟨hα, hU_sa, hP_eq⟩
  have hα_ne : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hP0_sa : P₀ᴴ = P₀ := rBlock.basisOutcomeProjector_conjTranspose 0
  have hM_eq : P₀ * rSys.embedMatrix A * P₀ = (α : ℂ) • (P₀ * U_BE.1 * P₀) := by
    calc P₀ * rSys.embedMatrix A * P₀
      _ = ((α : ℂ) * (α : ℂ)⁻¹) • (P₀ * rSys.embedMatrix A * P₀) := by
          rw [mul_inv_cancel₀ hα_ne, one_smul]
      _ = (α : ℂ) • ((α : ℂ)⁻¹ • (P₀ * rSys.embedMatrix A * P₀)) := (smul_smul _ _ _).symm
      _ = (α : ℂ) • (P₀ * U_BE.1 * P₀) := by rw [← hP_eq]
  have hM_sa : (P₀ * rSys.embedMatrix A * P₀)ᴴ = P₀ * rSys.embedMatrix A * P₀ := by
    rw [hM_eq, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      conjTranspose_mul, conjTranspose_mul, hP0_sa, hU_sa, Matrix.mul_assoc]
  have hM_lhs : (P₀ * rSys.embedMatrix A * P₀)ᴴ = P₀ * rSys.embedMatrix Aᴴ * P₀ := by
    rw [conjTranspose_mul, conjTranspose_mul, hP0_sa, ← rSys.embedMatrix_conjTranspose,
      Matrix.mul_assoc]
  have hA_sa : Aᴴ = A := embedMatrix_sandwich_zero_inj Aᴴ A (hM_lhs.symm.trans hM_sa)
  have hHeff_eq : Heff = A + (E₀ : ℂ) • (1 : Operator (2 ^ k)) := (sub_add_cancel Heff _).symm
  rw [Matrix.IsHermitian, hHeff_eq, conjTranspose_add, hA_sa, conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, conjTranspose_one]
end FullScaleBESector
end SpecsAux
end
end ModFullScaleBESector

section ModGidneyPointEq
@[expose] public section
open Operator Matrix QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace DynCircuitExt
open _root_.DynamicCircuit
variable {Var : Type} {n : ℕ}
def withTempAnd (v : Var) (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (body : DynamicCircuit Var n) :
    DynamicCircuit Var n := .seq (andCompute control₁ control₂ ancilla h₁a h₂a)
    (.seq body (andUncompute v control₁ control₂ ancilla h₁₂))
@[simp] theorem count_withTempAnd_t (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (body : DynamicCircuit Var n) :
    (withTempAnd v control₁ control₂ ancilla h₁₂ h₁a h₂a body).count PrimitiveGate.T =
      body.count PrimitiveGate.T + 4 := by
  simp only [withTempAnd, count, count_andCompute_t, count_andUncompute_t, add_zero]
  omega
@[simp] theorem count_withTempAnd_toff (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (body : DynamicCircuit Var n) :
    (withTempAnd v control₁ control₂ ancilla h₁₂ h₁a h₂a body).count PrimitiveGate.TOFF =
      body.count PrimitiveGate.TOFF := by
  simp [withTempAnd]
def czCircuit (control target : Wire n) (hct : control ≠ target) : Circuit n :=
  Circuit.H target ;;ᶜ Circuit.CNOT control target hct ;;ᶜ Circuit.H target
@[simp] theorem count_czCircuit_t (control target : Wire n) (hct : control ≠ target) :
    (czCircuit control target hct).count PrimitiveGate.T = 0 := by
  simp [czCircuit]
@[simp] theorem count_czCircuit_toff (control target : Wire n) (hct : control ≠ target) :
    (czCircuit control target hct).count PrimitiveGate.TOFF = 0 := by
  simp [czCircuit]
def xMask : (d : ℕ) → (Fin d → Wire n) → (Fin d → Bool) → Circuit n
  | 0, _, _ => .identity
  | d + 1, xs, pat =>
      (if pat 0 then .identity else Circuit.X (xs 0)) ;;ᶜ
        xMask d (fun i => xs i.succ) (fun i => pat i.succ)
@[simp] theorem count_xMask_t :
    ∀ (d : ℕ) (xs : Fin d → Wire n) (pat : Fin d → Bool),
      (xMask d xs pat).count PrimitiveGate.T = 0
  | 0, _, _ => rfl
  | d + 1, xs, pat => by
      simp only [xMask, Circuit.count_seq, count_xMask_t]
      split <;> simp
@[simp] theorem count_xMask_toff :
    ∀ (d : ℕ) (xs : Fin d → Wire n) (pat : Fin d → Bool),
      (xMask d xs pat).count PrimitiveGate.TOFF = 0
  | 0, _, _ => rfl
  | d + 1, xs, pat => by
      simp only [xMask, Circuit.count_seq, count_xMask_toff]
      split <;> simp
def toffChainCircuit :
    (k : ℕ) → (acc : Wire n) → (ctrls : Fin k → Wire n) → (scratches : Fin k → Wire n) →
    (hacc_c : ∀ i, acc ≠ ctrls i) →
    (hacc_s : ∀ i, acc ≠ scratches i) →
    (hc_s : ∀ i j, ctrls i ≠ scratches j) →
    (hs_inj : Function.Injective scratches) →
    (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → Circuit n) →
    Circuit n
  | 0, acc, _, _, _, _, _, _, leaf => leaf acc (Or.inl rfl)
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf =>
      let t₀ := Circuit.TOFF acc (ctrls 0) (scratches 0) (hacc_c 0) (hacc_s 0) (hc_s 0 0)
      t₀ ;;ᶜ
        toffChainCircuit k (scratches 0)
          (fun i => ctrls i.succ)
          (fun i => scratches i.succ)
          (fun i => (hc_s i.succ 0).symm)
          (fun i => fun h => Fin.succ_ne_zero i (hs_inj h).symm)
          (fun i j => hc_s i.succ j.succ)
          (hs_inj.comp (Fin.succ_injective _))
          (fun w hw => leaf w (by
            rcases hw with rfl | ⟨i, rfl⟩
            · exact Or.inr ⟨0, rfl⟩
            · exact Or.inr ⟨i.succ, rfl⟩)) ;;ᶜ
        t₀
def withAndChain (v : Var) :
    (k : ℕ) → (acc : Wire n) → (ctrls : Fin k → Wire n) → (scratches : Fin k → Wire n) →
    (hacc_c : ∀ i, acc ≠ ctrls i) →
    (hacc_s : ∀ i, acc ≠ scratches i) →
    (hc_s : ∀ i j, ctrls i ≠ scratches j) →
    (hs_inj : Function.Injective scratches) →
    (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → DynamicCircuit Var n) →
    DynamicCircuit Var n
  | 0, acc, _, _, _, _, _, _, leaf => leaf acc (Or.inl rfl)
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf =>
      withTempAnd v acc (ctrls 0) (scratches 0)
        (hacc_c 0) (hacc_s 0) (hc_s 0 0)
        (withAndChain v k (scratches 0)
          (fun i => ctrls i.succ)
          (fun i => scratches i.succ)
          (fun i => (hc_s i.succ 0).symm)
          (fun i => fun h => Fin.succ_ne_zero i (hs_inj h).symm)
          (fun i j => hc_s i.succ j.succ)
          (hs_inj.comp (Fin.succ_injective _))
          (fun w hw => leaf w (by
            rcases hw with rfl | ⟨i, rfl⟩
            · exact Or.inr ⟨0, rfl⟩
            · exact Or.inr ⟨i.succ, rfl⟩)))
theorem count_withAndChain_toff_eq_zero (v : Var) :
    ∀ (k : ℕ) (acc : Wire n) (ctrls : Fin k → Wire n) (scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → DynamicCircuit Var n),
      (∀ w hw, (leaf w hw).count PrimitiveGate.TOFF = 0) →
      (withAndChain v k acc ctrls scratches hacc_c hacc_s hc_s hs_inj leaf).count
        PrimitiveGate.TOFF = 0
  | 0, acc, _, _, _, _, _, _, leaf, h0 => h0 acc (Or.inl rfl)
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf, h0 => by
      unfold withAndChain
      rw [count_withTempAnd_toff]
      exact count_withAndChain_toff_eq_zero v k (scratches 0)
        (fun i => ctrls i.succ) (fun i => scratches i.succ)
        (fun i => (hc_s i.succ 0).symm)
        (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
        (fun i j => hc_s i.succ j.succ)
        (hs_inj.comp (Fin.succ_injective _))
        (fun w hw => leaf w (by
          rcases hw with rfl | ⟨i, rfl⟩
          · exact Or.inr ⟨0, rfl⟩
          · exact Or.inr ⟨i.succ, rfl⟩))
        (fun w hw => h0 w _)
section KetAlgebra
noncomputable def gket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
abbrev gbitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
noncomputable def gsqrtHalf : ℂ := (√(1 / 2) : ℝ)
theorem gsqrtHalf_mul_self : gsqrtHalf * gsqrtHalf = 1 / 2 := by
  dsimp [gsqrtHalf]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring
theorem gsqrtHalf_sq : gsqrtHalf ^ 2 = 1 / 2 := by
  linear_combination gsqrtHalf_mul_self
theorem gbit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
@[simp] private theorem lemHex4 (β : BitAssignment n) : basisBits n ((basisBitsEquiv n).symm β) =
    β := (basisBitsEquiv n).apply_symm_apply β
@[simp] private theorem lemHex5 (g : Fin (2 ^ n)) : (basisBitsEquiv n).symm (basisBits n g) = g :=
    (basisBitsEquiv n).symm_apply_apply g
theorem gsingle_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = gket (basisBits n g) := by
  simp [gket, basisState]
theorem gmatrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (gket β) = B.mulVec (gket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits n j)) i
  simpa [← gsingle_eq_ket, Matrix.mulVec_single_one] using this
private noncomputable def lemHex6 {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
private theorem lemHex7 {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : lemHex6 β r γ (r i) = γ i := by
  simp [lemHex6, QRegister.basisBits_replaceIndex_apply]
private theorem lemHex8 {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (w : Wire n) (hw : w ∉ Set.range r.wires) : lemHex6 β r γ w = β w := by
  simp [lemHex6, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
private theorem lemHex9 {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    lemHex6 β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [lemHex7]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h => hi (r.wires.injective h)), hγ i hi]
  · rw [lemHex8 _ _ _ _ hw, Function.update_of_ne]
    exact fun h => hw ⟨i₀, h.symm⟩
private noncomputable abbrev lemHexa {k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin
    (2 ^ k) := (basisBitsEquiv k).symm (fun i => β (r i))
private theorem lemHexb {k : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) : (r.embedMatrix A).mulVec (gket β) = ∑ l : Fin (2 ^ k), A l
    (lemHexa r β) • gket (lemHex6 β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBitsEquiv n).symm β) = lemHexa r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [gket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [lemHex6, gket, basisState]
private theorem lemHexc {k : ℕ} (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) : (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (gket β) = gket
    (lemHex6 β r (basisBits k (σ.symm (lemHexa r β)))) := by
  rw [lemHexb, Finset.sum_eq_single (σ.symm (lemHexa r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ lemHexa r β := fun h => hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp
private theorem lemHexd (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ) (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (gket β) = A 0 (if β q = 0 then 0 else 1) •
    gket (Function.update β q 0) + A 1 (if β q = 0 then 0 else 1) • gket
    (Function.update β q 1) := by
  have hloc : lemHexa (QRegister.singleton q) β = if β q = 0 then 0 else 1 :=
    (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ => b) : Fin 2) =
      if b = 0 then 0 else 1) (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ => b) :
      lemHex6 β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [lemHex9 _ _ _ 0 (fun i hi => absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [lemHexb, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
theorem geval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl
theorem gket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (gket β) = gket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0,1; 1,0]).mulVec _ = _
  rw [lemHexd]
  rcases gbit_cases (β q) with hb | hb <;> simp [hb, CharTwo.add_self_eq_zero]
theorem gket_H (q : Wire n) (β : BitAssignment n) : (Circuit.H q).eval.1.mulVec (gket β) =
    gsqrtHalf • (gket (Function.update β q 0) + gbitSign (β q) • gket (Function.update β q 1))
    := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((√(1 / 2) : ℝ) • !![(1 : ℂ), 1; 1,-1])).mulVec _ = _
  rw [lemHexd]
  rcases gbit_cases (β q) with hb | hb <;> simp [hb, gsqrtHalf, smul_add, Complex.real_smul]
theorem gket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (gket β) = gket (Function.update β t (β t + β c)) := by
  rw[Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val, lemHexc]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBitsEquiv 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [lemHexa, hloc, lemHex9 _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi
theorem gket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (gket β) = gket
    (Function.update β t (β t + β c₁ * β c₂)) := by
  rw[Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val, lemHexc]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBitsEquiv 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [lemHexa, hloc, lemHex9 _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi
theorem gket_projector (q : Wire n) (o : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (gket β) =
      if β q = (o.val : ZMod 2) then gket β else 0 := by
  rw [gket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ (b : ZMod 2) (o : Fin 2),
      (((basisBitsEquiv 1).symm (fun _ => b) : Fin 2) = o ↔ b = (o.val : ZMod 2)) := by decide
  have hext : (QRegister.singleton q).extractIndex ((basisBitsEquiv n).symm β) =
      (basisBitsEquiv 1).symm (fun _ => β q) := by simp [QRegister.extractIndex]
  rw [hext]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((h _ _).1 h1) h2
  · exact absurd ((h _ _).2 h2) h1
  · rfl
theorem gtoffoli_eval_mul_self (control₁ control₂ target : Wire n) (h₁₂ : control₁ ≠ control₂)
    (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval *
    (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval = 1 := by
  apply Subtype.ext
  apply gmatrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    gket_TOFF, Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
    Function.update_idem]
  have hadd : β target + β control₁ * β control₂ + β control₁ * β control₂ = β target := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]
theorem gket_czCircuit (control target : Wire n) (hct : control ≠ target) (β : BitAssignment n) :
    (czCircuit control target hct).eval.1.mulVec (gket β) =
      gbitSign (β control * β target) • gket β := by
  rw [czCircuit]
  simp only [geval_seq_mulVec, gket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
    gket_CNOT, Function.update_self, Function.update_of_ne hct, Function.update_idem, zero_add]
  have hcombine (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) : gsqrtHalf • (gsqrtHalf • (ψ₀ +
      gbitSign c₁ • ψ₁) + gbitSign c₂ • (gsqrtHalf • (ψ₀ + gbitSign (1 + c₁) • ψ₁))) =
      gbitSign (c₁ * c₂) • (if c₂ = 0 then ψ₀ else ψ₁) := by
    rcases gbit_cases c₁ with rfl | rfl <;>
      rcases gbit_cases c₂ with rfl | rfl <;>
      simp only [gbitSign, CharTwo.add_self_eq_zero, add_zero, mul_zero, mul_one,
        one_ne_zero, ↓reduceIte, smul_add, smul_smul] <;>
      match_scalars <;>
      first
        | ring1
        | (ring_nf; simp only [gsqrtHalf_sq]; ring1)
  rw [hcombine (β control) (β target)]
  have e := Function.update_eq_self target β
  rcases gbit_cases (β target) with h₂ | h₂ <;> rw [h₂] at e ⊢ <;> simp [e]
noncomputable def xMaskBits (d : ℕ) (xs : Fin d → Wire n) (pat : Fin d → Bool)
    (β : BitAssignment n) : BitAssignment n :=
  fun w => if h : ∃ i, xs i = w then
    let i := Classical.choose h
    if pat i then β w else β w + 1
  else β w
theorem xMaskBits_outside (d : ℕ) (xs : Fin d → Wire n) (pat : Fin d → Bool)
    (β : BitAssignment n) (w : Wire n) (hw : ∀ i, xs i ≠ w) :
    xMaskBits d xs pat β w = β w := by
  have hno : ¬ ∃ i, xs i = w := fun ⟨i, hi⟩ => hw i hi
  simp [xMaskBits, hno]
theorem xMaskBits_apply_inj (d : ℕ) (xs : Fin d → Wire n) (hxs_inj : Function.Injective xs)
    (pat : Fin d → Bool) (β : BitAssignment n) (i : Fin d) :
    xMaskBits d xs pat β (xs i) = if pat i then β (xs i) else β (xs i) + 1 := by
  have hex : ∃ j, xs j = xs i := ⟨i, rfl⟩
  have hchoose : Classical.choose hex = i := hxs_inj (Classical.choose_spec hex)
  simp [xMaskBits, hex, hchoose]
theorem gket_xMask :
    ∀ (d : ℕ) (xs : Fin d → Wire n) (_hxs_inj : Function.Injective xs)
      (pat : Fin d → Bool) (β : BitAssignment n),
      (xMask d xs pat).eval.1.mulVec (gket β) = gket (xMaskBits d xs pat β)
  | 0, _, _, _, _ => by
      simp only [xMask, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      rfl
  | d + 1, xs, hxs_inj, pat, β => by
      simp only [xMask, geval_seq_mulVec]
      have hstep : ((if pat 0 then (Circuit.identity : Circuit n) else
        Circuit.X (xs 0)).eval.1.mulVec (gket β)) =
          gket (if pat 0 then β else Function.update β (xs 0) (β (xs 0) + 1)) := by
        cases h : pat 0
        · simpa [h] using gket_X (xs 0) β
        · simp
      have hinj_tail : Function.Injective (fun i : Fin d => xs i.succ) :=
        fun _ _ h => Fin.succ_injective _ (hxs_inj h)
      rw [hstep, gket_xMask d (fun i => xs i.succ) hinj_tail]
      apply congrArg gket
      funext w
      by_cases hw : ∃ i : Fin (d + 1), xs i = w
      · obtain ⟨i, rfl⟩ := hw
        rw [xMaskBits_apply_inj (d + 1) xs hxs_inj pat β i]
        refine Fin.cases ?_ (fun j => ?_) i
        · have hno : ∀ k : Fin d, xs k.succ ≠ xs 0 :=
            fun k hk => Fin.succ_ne_zero k (hxs_inj hk)
          rw [xMaskBits_outside d (fun k => xs k.succ) (fun k => pat k.succ) _ (xs 0) hno]
          cases pat 0 <;> simp
        · have hne0 : xs j.succ ≠ xs 0 := fun h => Fin.succ_ne_zero j (hxs_inj h)
          rw [xMaskBits_apply_inj d (fun k => xs k.succ) hinj_tail (fun k => pat k.succ) _ j]
          cases pat 0
          · simp [Function.update_of_ne hne0]
          · simp
      · have hno' : ∀ k : Fin d, xs k.succ ≠ w := fun k hk => hw ⟨k.succ, hk⟩
        have hne0 : w ≠ xs 0 := fun h => hw ⟨0, h.symm⟩
        rw [xMaskBits_outside (d + 1) xs pat β w (fun i hi => hw ⟨i, hi⟩),
            xMaskBits_outside d (fun k => xs k.succ) (fun k => pat k.succ) _ w hno']
        cases pat 0
        · simp [Function.update_of_ne hne0]
        · simp
theorem xMaskBits_involutive (d : ℕ) (xs : Fin d → Wire n) (pat : Fin d → Bool)
    (β : BitAssignment n) : xMaskBits d xs pat (xMaskBits d xs pat β) = β := by
  funext w
  by_cases hw : ∃ i, xs i = w
  · simp only [xMaskBits, hw, ↓reduceDIte]
    split
    · rfl
    · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · simp [xMaskBits, hw]
end KetAlgebra
section ChainSemantics
theorem toffChainCircuit_mulVec_ket :
    ∀ (k : ℕ) (acc : Wire n) (ctrls : Fin k → Wire n) (scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → Circuit n)
      (φ : ZMod 2 → BitAssignment n → ℂ)
      (upd : ZMod 2 → BitAssignment n → BitAssignment n),
      (∀ top htop (γ : BitAssignment n),
        (leaf top htop).eval.1.mulVec (gket γ) = φ (γ top) γ • gket (upd (γ top) γ)) →
      (∀ b γ, upd b γ acc = γ acc) →
      (∀ b γ i, upd b γ (ctrls i) = γ (ctrls i)) →
      (∀ b γ i, upd b γ (scratches i) = γ (scratches i)) →
      (∀ b w v₀ γ, (∃ i, scratches i = w) → φ b (Function.update γ w v₀) = φ b γ) →
      (∀ b w v₀ γ, (∃ i, scratches i = w) →
        upd b (Function.update γ w v₀) = Function.update (upd b γ) w v₀) →
      ∀ (β : BitAssignment n),(∀ i, β (scratches i) = 0) →
        (toffChainCircuit k acc ctrls scratches hacc_c hacc_s hc_s hs_inj leaf).eval.1.mulVec
            (gket β) =
          φ (β acc * ∏ i : Fin k, β (ctrls i)) β •
            gket (upd (β acc * ∏ i : Fin k, β (ctrls i)) β)
  | 0, acc, _, _, _, _, _, _, leaf, φ, upd, hleaf, _, _, _, _, _, β, _ => by
      simpa [toffChainCircuit] using hleaf acc (Or.inl rfl) β
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf, φ, upd,
      hleaf, hupd_acc, hupd_c, hupd_s, hφ_scr, hupd_scr_comm, β, hclean => by
      simp only [toffChainCircuit, geval_seq_mulVec]
      let b₀ : ZMod 2 := β acc * β (ctrls 0)
      let β₁ : BitAssignment n := Function.update β (scratches 0) b₀
      have ht1 : (Circuit.TOFF acc (ctrls 0) (scratches 0) (hacc_c 0) (hacc_s 0) (hc_s 0
        0)).eval.1.mulVec
          (gket β) = gket β₁ := by
        rw [gket_TOFF, hclean 0, zero_add]
      rw [ht1]
      have hclean₁ : ∀ i : Fin k, β₁ (scratches i.succ) = 0 := by
        intro i
        have hne : scratches i.succ ≠ scratches 0 := fun h => Fin.succ_ne_zero i (hs_inj h)
        simp [β₁, Function.update_of_ne hne, hclean i.succ]
      have ih := toffChainCircuit_mulVec_ket k (scratches 0)
        (fun i => ctrls i.succ) (fun i => scratches i.succ)
        (fun i => (hc_s i.succ 0).symm)
        (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
        (fun i j => hc_s i.succ j.succ)
        (hs_inj.comp (Fin.succ_injective _))
        (fun w hw => leaf w (by
          rcases hw with rfl | ⟨i, rfl⟩
          · exact Or.inr ⟨0, rfl⟩
          · exact Or.inr ⟨i.succ, rfl⟩))
        φ upd
        (fun top htop γ => hleaf top _ γ)
        (fun b γ => hupd_s b γ 0)
        (fun b γ i => hupd_c b γ i.succ)
        (fun b γ i => hupd_s b γ i.succ)
        (fun b w v₀ γ ⟨i, hi⟩ => hφ_scr b w v₀ γ ⟨i.succ, hi⟩)
        (fun b w v₀ γ ⟨i, hi⟩ => hupd_scr_comm b w v₀ γ ⟨i.succ, hi⟩)
        β₁ hclean₁
      rw [ih, Matrix.mulVec_smul]
      have hprod_eq : β₁ (scratches 0) * (∏ i : Fin k, β₁ (ctrls i.succ)) = β acc * ∏ i : Fin
          (k + 1), β (ctrls i) := by
        have hc_eq : ∀ i : Fin k, β₁ (ctrls i.succ) = β (ctrls i.succ) := fun i =>
          Function.update_of_ne (hc_s i.succ 0) _ _
        simp only [β₁, b₀, Function.update_self, hc_eq, Fin.prod_univ_succ]
        ring
      rw [hprod_eq]
      let P := β acc * ∏ i : Fin (k + 1), β (ctrls i)
      have hφ_eq : φ P β₁ = φ P β := hφ_scr P (scratches 0) b₀ β ⟨0, rfl⟩
      have hupd_eq : upd P β₁ = Function.update (upd P β) (scratches 0) b₀ :=
        hupd_scr_comm P (scratches 0) b₀ β ⟨0, rfl⟩
      rw [hφ_eq, hupd_eq, gket_TOFF]
      congr 2
      have hacc_after : Function.update (upd P β) (scratches 0) b₀ acc = β acc := by
        rw [Function.update_of_ne (hacc_s 0), hupd_acc]
      have hc0_after : Function.update (upd P β) (scratches 0) b₀ (ctrls 0) = β (ctrls 0) := by
        rw [Function.update_of_ne (hc_s 0 0), hupd_c]
      rw [Function.update_self, hacc_after, hc0_after, Function.update_idem]
      have hcancel : b₀ + β acc * β (ctrls 0) = β (scratches 0) := by
        dsimp [b₀]
        rw [CharTwo.add_self_eq_zero, hclean 0]
      rw [hcancel]
      funext w
      dsimp only [P] at *
      by_cases hw : w = scratches 0
      · subst hw; rw [Function.update_self]; exact (hupd_s _ β 0).symm
      · exact Function.update_of_ne hw _ _
theorem toffChainCircuit_preserves_wire :
    ∀ (k : ℕ) (acc : Wire n) (ctrls : Fin k → Wire n) (scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → Circuit n)
      (φ : ZMod 2 → BitAssignment n → ℂ)
      (upd : ZMod 2 → BitAssignment n → BitAssignment n),
      (∀ top htop (γ : BitAssignment n),
        (leaf top htop).eval.1.mulVec (gket γ) = φ (γ top) γ • gket (upd (γ top) γ)) →
      (∀ (q : Wire n),(∀ i, q ≠ scratches i) → (∀ b γ, upd b γ q = γ q) →
        ∀ (o : Fin 2),
          (QRegister.singleton q).basisOutcomeProjector o *
              (toffChainCircuit k acc ctrls scratches hacc_c hacc_s hc_s hs_inj leaf).eval.1 =
            (toffChainCircuit k acc ctrls scratches hacc_c hacc_s hc_s hs_inj leaf).eval.1 *
              (QRegister.singleton q).basisOutcomeProjector o)
  | 0, acc, _, _, _, _, _, _, leaf, φ, upd, hleaf, q, _, hupd_q, o => by
      apply gmatrix_ext_ket; intro β
      by_cases hb : β q = (o.val : ZMod 2)
      · simp only [toffChainCircuit, ← Matrix.mulVec_mulVec, hleaf, Matrix.mulVec_smul,
          gket_projector, hupd_q, hb, ↓reduceIte]
      · simp only [toffChainCircuit, ← Matrix.mulVec_mulVec, hleaf, Matrix.mulVec_smul,
          gket_projector, hupd_q, hb, ↓reduceIte, Matrix.mulVec_zero, smul_zero]
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf, φ, upd,
      hleaf, q, hq_scr, hupd_q, o => by
      simp only [toffChainCircuit, Circuit.eval_seq, Submonoid.coe_mul]
      set Pq := (QRegister.singleton q).basisOutcomeProjector o
      set T₀ := (Circuit.TOFF acc (ctrls 0) (scratches 0) (hacc_c 0) (hacc_s 0) (hc_s 0 0)).eval.1
      set subLeaf : (w : Wire n) → (w = scratches 0 ∨ ∃ i : Fin k,
        w = scratches i.succ) → Circuit n :=
        fun w hw => leaf w (by
          rcases hw with rfl | ⟨i, rfl⟩
          · exact Or.inr ⟨0, rfl⟩
          · exact Or.inr ⟨i.succ, rfl⟩)
      set M := (toffChainCircuit k (scratches 0) (fun i => ctrls i.succ) (fun i => scratches i.succ)
        (fun i => (hc_s i.succ 0).symm)
        (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
        (fun i j => hc_s i.succ j.succ)
        (hs_inj.comp (Fin.succ_injective _))
        subLeaf).eval.1
      have hT₀ : Pq * T₀ = T₀ * Pq := by
        apply gmatrix_ext_ket; intro β
        by_cases hb : β q = (o.val : ZMod 2)
        · simp only [Pq, T₀, ← Matrix.mulVec_mulVec, gket_TOFF, gket_projector,
            Function.update_of_ne (hq_scr 0), hb, ↓reduceIte]
        · simp only [Pq, T₀, ← Matrix.mulVec_mulVec, gket_TOFF, gket_projector,
            Function.update_of_ne (hq_scr 0), hb, ↓reduceIte, Matrix.mulVec_zero]
      have hsub : Pq * M = M * Pq := toffChainCircuit_preserves_wire k (scratches 0)
          (fun i => ctrls i.succ) (fun i => scratches i.succ) (fun i => (hc_s i.succ 0).symm)
          (fun i h => Fin.succ_ne_zero i (hs_inj h).symm) (fun i j => hc_s i.succ j.succ)
          (hs_inj.comp (Fin.succ_injective _)) subLeaf φ upd (fun top htop γ => hleaf top _ γ)
          q (fun i => hq_scr i.succ) hupd_q o
      calc
        Pq * (T₀ * M * T₀)
            = (Pq * T₀) * M * T₀ := by
              rw [← Matrix.mul_assoc Pq (T₀ * M) T₀, ← Matrix.mul_assoc Pq T₀ M]
        _ = T₀ * (Pq * M) * T₀ := by
              rw [hT₀, Matrix.mul_assoc T₀ Pq M]
        _ = T₀ * M * (Pq * T₀) := by
              rw [hsub, ← Matrix.mul_assoc T₀ M Pq, Matrix.mul_assoc (T₀ * M) Pq T₀]
        _ = (T₀ * M * T₀) * Pq := by
              rw [hT₀, ← Matrix.mul_assoc (T₀ * M) T₀ Pq]
private theorem lemHexe (c₁ c₂ : Wire n) (o₁ o₂ : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton c₁).basisOutcomeProjector o₁ *
      (QRegister.singleton c₂).basisOutcomeProjector o₂).mulVec (gket β) =
      if β c₁ = (o₁.val : ZMod 2) ∧ β c₂ = (o₂.val : ZMod 2) then gket β else 0 := by
  by_cases h2 : β c₂ = (o₂.val : ZMod 2)
  · simp only [← Matrix.mulVec_mulVec, gket_projector, h2, ↓reduceIte, and_true]
  · simp only [← Matrix.mulVec_mulVec, gket_projector, h2, ↓reduceIte, Matrix.mulVec_zero,
      and_false]
private theorem lemHexf (c₁ c₂ anc : Wire n) (o₁ o₂ oa : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton c₁).basisOutcomeProjector o₁ * (QRegister.singleton
    c₂).basisOutcomeProjector o₂ * (QRegister.singleton anc).basisOutcomeProjector oa).mulVec
    (gket β) = if (β c₁ = (o₁.val : ZMod 2) ∧ β c₂ = (o₂.val : ZMod 2)) ∧ β anc =
    (oa.val : ZMod 2) then gket β else 0 := by
  rw [← Matrix.mulVec_mulVec, gket_projector]
  by_cases h3 : β anc = (oa.val : ZMod 2)
  · simp only [h3, ↓reduceIte, and_true]
    exact lemHexe c₁ c₂ o₁ o₂ β
  · simp only [h3, ↓reduceIte, Matrix.mulVec_zero, and_false]
theorem toffoli_conj_clean_of_preserves_three
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hc₁ : ∀ o : Fin 2,
      (QRegister.singleton c₁).basisOutcomeProjector o * U =
        U * (QRegister.singleton c₁).basisOutcomeProjector o)
    (hc₂ : ∀ o : Fin 2,
      (QRegister.singleton c₂).basisOutcomeProjector o * U =
        U * (QRegister.singleton c₂).basisOutcomeProjector o)
    (hanc : ∀ o : Fin 2,
      (QRegister.singleton anc).basisOutcomeProjector o * U =
        U * (QRegister.singleton anc).basisOutcomeProjector o) :
    let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
    P₀ * (T_anc * U * T_anc * P₀) = T_anc * U * T_anc * P₀ := by
  dsimp only
  set P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  set T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
  set Pc₁ := fun o : Fin 2 => (QRegister.singleton c₁).basisOutcomeProjector o
  set Pc₂ := fun o : Fin 2 => (QRegister.singleton c₂).basisOutcomeProjector o
  set Pa := fun o : Fin 2 => (QRegister.singleton anc).basisOutcomeProjector o
  have hsum : Pc₁ 0 * Pc₂ 0 + Pc₁ 0 * Pc₂ 1 + Pc₁ 1 * Pc₂ 0 + Pc₁ 1 * Pc₂ 1 = 1 := by
    apply gmatrix_ext_ket; intro β
    simp only [Pc₁, Pc₂, Matrix.add_mulVec, lemHexe]
    rcases gbit_cases (β c₁) with h1 | h1 <;> rcases gbit_cases (β c₂) with h2 | h2 <;>
      (rw [h1, h2]; simp)
  have hcond_eq : ∀ (o₁ o₂ : Fin 2) (b₁ b₂ ba : ZMod 2),
      ((b₁ = (o₁.val : ZMod 2) ∧ b₂ = (o₂.val : ZMod 2)) ∧
        ba + b₁ * b₂ = ((if o₁ = 1 ∧ o₂ = 1 then (1 : Fin 2) else 0).val : ZMod 2)) ↔
      ((b₁ = (o₁.val : ZMod 2) ∧ b₂ = (o₂.val : ZMod 2)) ∧
        ba = ((0 : Fin 2).val : ZMod 2)) := by decide
  have hzero : ∀ (o₁ o₂ : Fin 2), ((if o₁ = 1 ∧ o₂ = 1 then (1 : Fin 2) else 0).val : ZMod 2) +
      (o₁.val : ZMod 2) * (o₂.val : ZMod 2) = ((0 : Fin 2).val : ZMod 2) := by decide
  have hbranch (o₁ o₂ : Fin 2) : T_anc * (Pc₁ o₁ * Pc₂ o₂ * P₀) =
      (Pc₁ o₁ * Pc₂ o₂ * Pa (if o₁ = 1 ∧ o₂ = 1 then 1 else 0)) * T_anc ∧ P₀ * T_anc *
      (Pc₁ o₁ * Pc₂ o₂ * Pa (if o₁ = 1 ∧ o₂ = 1 then 1 else 0)) = T_anc *
      (Pc₁ o₁ * Pc₂ o₂ * Pa (if o₁ = 1 ∧ o₂ = 1 then 1 else 0)) := by
    set out : Fin 2 := if o₁ = 1 ∧ o₂ = 1 then 1 else 0
    constructor
    · apply gmatrix_ext_ket
      intro β
      conv_lhs => rw [← Matrix.mulVec_mulVec]
      conv_rhs => rw [← Matrix.mulVec_mulVec]
      dsimp only [Pc₁, Pc₂, Pa, P₀, T_anc, out]
      rw [lemHexf, gket_TOFF, lemHexf,
        Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
        if_congr (hcond_eq o₁ o₂ (β c₁) (β c₂) (β anc)) rfl rfl]
      split_ifs
      · exact gket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
      · exact Matrix.mulVec_zero _
    · apply gmatrix_ext_ket
      intro β
      conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      conv_rhs => rw [← Matrix.mulVec_mulVec]
      dsimp only [Pc₁, Pc₂, Pa, P₀, T_anc]
      rw [lemHexf]
      by_cases hc : (β c₁ = (o₁.val : ZMod 2) ∧ β c₂ = (o₂.val : ZMod 2)) ∧ β anc =
        (out.val : ZMod 2)
      · rcases hc with ⟨⟨hc1, hc2⟩, ha⟩
        simp only [hc1, hc2, ha, and_self, ↓reduceIte, gket_TOFF, gket_projector,
          Function.update_self]
        exact ite_eq_left (hzero o₁ o₂)
      · simp only [hc, ↓reduceIte, Matrix.mulVec_zero]
  have hterm (o₁ o₂ : Fin 2) : P₀ * (T_anc * U * T_anc * (Pc₁ o₁ * Pc₂ o₂ * P₀)) = T_anc * U *
      T_anc * (Pc₁ o₁ * Pc₂ o₂ * P₀) := by
    obtain ⟨hb1, hb2⟩ := hbranch o₁ o₂
    set out : Fin 2 := if o₁ = 1 ∧ o₂ = 1 then 1 else 0
    set P₃ := Pc₁ o₁ * Pc₂ o₂ * Pa out
    have hUcomm : U * P₃ = P₃ * U := by
      simp only [P₃, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U (Pc₁ o₁), ← hc₁ o₁, Matrix.mul_assoc (Pc₁ o₁) U,
        ← Matrix.mul_assoc U (Pc₂ o₂), ← hc₂ o₂, Matrix.mul_assoc (Pc₂ o₂) U, ← hanc out]
    calc P₀ * (T_anc * U * T_anc * (Pc₁ o₁ * Pc₂ o₂ * P₀))
      _ = P₀ * T_anc * U * (T_anc * (Pc₁ o₁ * Pc₂ o₂ * P₀)) := by simp only [Matrix.mul_assoc]
      _ = P₀ * T_anc * (U * P₃) * T_anc := by
          rw [hb1, ← Matrix.mul_assoc (P₀ * T_anc * U) P₃ T_anc, Matrix.mul_assoc (P₀ * T_anc) U P₃]
      _ = (P₀ * T_anc * P₃) * U * T_anc := by rw [hUcomm, ← Matrix.mul_assoc (P₀ * T_anc) P₃ U]
      _ = T_anc * U * (P₃ * T_anc) := by
          rw [hb2, Matrix.mul_assoc T_anc P₃ U, ← hUcomm, ← Matrix.mul_assoc T_anc U P₃,
            Matrix.mul_assoc (T_anc * U) P₃ T_anc]
      _ = T_anc * U * T_anc * (Pc₁ o₁ * Pc₂ o₂ * P₀) := by
          rw [← hb1, ← Matrix.mul_assoc (T_anc * U) T_anc]
  have expand_rhs : T_anc * U * T_anc * P₀ = T_anc * U * T_anc * (Pc₁ 0 * Pc₂ 0 * P₀) + T_anc
      * U * T_anc * (Pc₁ 0 * Pc₂ 1 * P₀) + T_anc * U * T_anc * (Pc₁ 1 * Pc₂ 0 * P₀) + T_anc *
      U * T_anc * (Pc₁ 1 * Pc₂ 1 * P₀) := by
    have hp : P₀ = Pc₁ 0 * Pc₂ 0 * P₀ + Pc₁ 0 * Pc₂ 1 * P₀ + Pc₁ 1 * Pc₂ 0 * P₀ + Pc₁ 1 * Pc₂
        1 * P₀ := by
      calc P₀ = (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * P₀ := (Matrix.one_mul P₀).symm
        _ = _ := by rw [← hsum]; simp only [Matrix.add_mul, Matrix.mul_assoc]
    simpa only [Matrix.mul_add] using congrArg (fun M => T_anc * U * T_anc * M) hp
  rw [expand_rhs, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
    hterm 0 0, hterm 0 1, hterm 1 0, hterm 1 1]
end ChainSemantics
section QHL
variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
theorem restrictToZeroAncilla_wp_withTempAnd_of_update_eq
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (body : DynamicCircuit Var n) (U_body : Unitary (2 ^ n))
    (Θ : CQAssertionCompat Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (hbody_eq :
      wp body.compile (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ) =
        wpQAssignCompat U_body (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ))
    (hc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
      P₀ * (T_anc * U_body.1 * T_anc * P₀) = T_anc * U_body.1 * T_anc * P₀) :
    CQAssertion.restrictToZeroAncilla
      (wp (withTempAnd v control₁ control₂ ancilla h₁₂ h₁a h₂a body).compile Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat
        ((Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval * U_body *
          (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval) Θ)
      (QRegister.singleton ancilla) := by
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
  let V := T_anc * U_body * T_anc
  have hT_sq : T_anc * T_anc = 1 :=
    gtoffoli_eval_mul_self control₁ control₂ ancilla h₁₂ h₁a h₂a
  have hU_eq : U_body * T_anc = T_anc * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
  have hV_P₀ : P₀ * (V.1 * P₀) = V.1 * P₀ := hc
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hV_restrict (Ψ : CQAssertionCompat Var (2 ^ n)) : CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat V (CQAssertion.restrictToZeroAncilla Ψ (QRegister.singleton ancilla)))
      (QRegister.singleton ancilla) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat V Ψ)
      (QRegister.singleton ancilla) := by
    funext σ
    apply Subtype.ext
    have hadj : P₀ * V.1ᴴ * P₀ = P₀ * V.1ᴴ := by
      have h := congrArg conjTranspose hV_P₀
      simpa [P₀, conjTranspose_mul, hP₀_herm, ← Matrix.mul_assoc] using h
    simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc, hadj]
  change CQAssertion.restrictToZeroAncilla
    (wp (.qSeq (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile
      (.qSeq body.compile (andUncompute v control₁ control₂ ancilla h₁₂).compile)) Θ)
    (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat V Θ) (QRegister.singleton ancilla)
  rw [restrictToZeroAncilla_wp_andCompute_seq_compat control₁ control₂ ancilla h₁₂ h₁a h₂a]
  change CQAssertion.restrictToZeroAncilla (wpQAssignCompat T_anc (wp body.compile (wp
    (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ))) (QRegister.singleton ancilla)
    = _
  rw [hbody_eq, wpQAssignCompat_comp, hU_eq, ← wpQAssignCompat_comp, ← hV_restrict,
    restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
      v control₁ control₂ ancilla h₁₂ h₁a h₂a Θ hΘ,
    hV_restrict]
noncomputable def restrictZeroWires : List (Wire n) → CQAssertionCompat Var (2 ^ n) →
    CQAssertionCompat Var (2 ^ n)
  | [], Θ => Θ
  | w :: ws, Θ => CQAssertion.restrictToZeroAncilla (restrictZeroWires ws Θ) (QRegister.singleton w)
omit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] in
theorem restrictZero_singleton_comm (w₁ w₂ : Wire n) (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton w₂))
    (QRegister.singleton w₁) = CQAssertion.restrictToZeroAncilla
    (CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton w₁)) (QRegister.singleton w₂) :=
  restrictAssertionToZeroAncilla_comm Θ (QRegister.singleton w₂) (QRegister.singleton w₁)
omit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] in
theorem restrictZeroWires_comm_singleton (w₀ : Wire n) :
    ∀ (ws : List (Wire n)) (Θ : CQAssertionCompat Var (2 ^ n)),
      CQAssertion.restrictToZeroAncilla (restrictZeroWires ws Θ) (QRegister.singleton w₀) =
        restrictZeroWires ws (CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton w₀))
  | [], _ => rfl
  | w :: ws, Θ => by
      simp only [restrictZeroWires]
      rw [restrictZero_singleton_comm, restrictZeroWires_comm_singleton w₀ ws]
omit [NeZero (2 ^ n)] in
private theorem lemHex11 (w : Wire n) :
    ∀ (c : Circuit n), w ∉ c.support →
      (QRegister.singleton w).basisOutcomeProjector 0 * c.eval.1 =
        c.eval.1 * (QRegister.singleton w).basisOutcomeProjector 0
  | .identity, _ => by simp
  | .gate g r, hnw => by
      have hdisj : r.DisjointWires (QRegister.singleton w) :=
        QRegister.disjoint_iff.mpr fun i _ ↦ (r.ne_apply_of_not_mem_image w hnw i).symm
      exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint r)
        (QRegister.singleton w) hdisj g.eval.1 0).symm
  | .seq c₁ c₂, hnw => by
      simp only [Circuit.support_seq, Finset.mem_union, not_or] at hnw
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [← Matrix.mul_assoc, lemHex11 w c₂ hnw.2, Matrix.mul_assoc, lemHex11 w c₁ hnw.1,
        ← Matrix.mul_assoc]
omit [DecidableEq Var] [NeZero (2 ^ n)] in
theorem restrictZeroWires_wp_qAssign_comm (c : Circuit n) :
    ∀ (ws : List (Wire n)),
      (∀ w ∈ ws, w ∉ c.support) →
      ∀ (Θ : CQAssertionCompat Var (2 ^ n)),
        restrictZeroWires ws (wpQAssignCompat c.eval Θ) =
          wpQAssignCompat c.eval (restrictZeroWires ws Θ)
  | [], _, _ => rfl
  | w :: ws, hdisj, Θ => by
      simp only [restrictZeroWires]
      rw [restrictZeroWires_wp_qAssign_comm c ws (fun u hu => hdisj u (List.mem_cons_of_mem w hu))]
      funext σ; apply Subtype.ext
      have hcomm : (QRegister.singleton w).basisOutcomeProjector 0 * c.eval.1ᴴ =
          c.eval.1ᴴ * (QRegister.singleton w).basisOutcomeProjector 0 := by
        have hadj := congrArg conjTranspose (lemHex11 w c (hdisj w (List.mem_cons_self ..)))
        simpa [QRegister.basisOutcomeProjector_conjTranspose] using hadj.symm
      simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hcomm]
def wireList : (k : ℕ) → (Fin k → Wire n) → List (Wire n)
  | 0, _ => []
  | k + 1, f => f 0 :: wireList k (fun i => f i.succ)
omit [NeZero (2 ^ n)] in
theorem mem_wireList_iff {k : ℕ} {f : Fin k → Wire n} {w : Wire n} :
    w ∈ wireList k f ↔ ∃ i : Fin k, f i = w := by
  induction k with
  | zero =>
      simp only [wireList, List.not_mem_nil, false_iff]
      exact fun ⟨i, _⟩ => Fin.elim0 i
  | succ k ih =>
      simp only [wireList, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨i.succ, rfl⟩
      · rintro ⟨i, rfl⟩
        exact Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
omit [NeZero (2 ^ n)] in
theorem not_mem_support_xMask :
    ∀ (d : ℕ) (xs : Fin d → Wire n) (pat : Fin d → Bool) (w : Wire n),
      (∀ i, xs i ≠ w) → w ∉ (xMask d xs pat).support
  | 0, _, _, _, _ => by simp [xMask]
  | d + 1, xs, pat, w, hw => by
      simp only [xMask, Circuit.support_seq, Finset.mem_union, not_or]
      refine ⟨?_,
        not_mem_support_xMask d (fun i => xs i.succ) (fun i => pat i.succ) w (fun i => hw i.succ)⟩
      by_cases hp : pat 0 <;> simp [hp, (hw 0).symm]
omit [Fintype Var] in
theorem wp_withAndChain_update_self [Finite Var] (v : Var) :
    ∀ (k : ℕ) (acc : Wire n) (ctrls : Fin k → Wire n) (scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → Circuit n)
      (Θ : CQAssertionCompat Var (2 ^ n)),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ (σ : Store Var) (val : ℤ),
        wp (withAndChain v k acc ctrls scratches hacc_c hacc_s hc_s hs_inj
            (fun w hw => .circuit (leaf w hw))).compile Θ (Function.update σ v val) =
          wp (withAndChain v k acc ctrls scratches hacc_c hacc_s hc_s hs_inj
            (fun w hw => .circuit (leaf w hw))).compile Θ σ
  | 0, acc, _, _, _, _, _, _, leaf, Θ, hΘ, σ, val => by
      cases nonempty_fintype Var
      simp [withAndChain, compile_circuit, hΘ]
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf, Θ, _, σ, val => by
      cases nonempty_fintype Var
      let Ψ := wp (andUncompute v acc (ctrls 0) (scratches 0) (hacc_c 0)).compile Θ
      have hΨ : ∀ σ' val', Ψ (Function.update σ' v val') = Ψ σ' :=
        fun σ' val' =>
          wp_andUncompute_update_self v acc (ctrls 0) (scratches 0) (hacc_c 0) Θ σ' val'
      have ih := wp_withAndChain_update_self v k (scratches 0)
        (fun i => ctrls i.succ) (fun i => scratches i.succ)
        (fun i => (hc_s i.succ 0).symm)
        (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
        (fun i j => hc_s i.succ j.succ)
        (hs_inj.comp (Fin.succ_injective _))
        (fun w hw => leaf w (by
          rcases hw with rfl | ⟨i, rfl⟩
          · exact Or.inr ⟨0, rfl⟩
          · exact Or.inr ⟨i.succ, rfl⟩))
        Ψ hΨ σ val
      simp only [withAndChain, withTempAnd, andCompute, compile_seq, compile_circuit, wp_qSeq,
        wp_circuit_compile_compat, wpQAssignCompat]
      exact congrArg (qAssignObsMap _) ih
theorem restrictZeroWires_wp_withAndChain (v : Var) :
    ∀ (k : ℕ) (acc : Wire n) (ctrls : Fin k → Wire n) (scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → Circuit n)
      (φ : ZMod 2 → BitAssignment n → ℂ)
      (upd : ZMod 2 → BitAssignment n → BitAssignment n),
      (∀ top htop (γ : BitAssignment n),
        (leaf top htop).eval.1.mulVec (gket γ) = φ (γ top) γ • gket (upd (γ top) γ)) →
      (∀ b γ, upd b γ acc = γ acc) →
      (∀ b γ i, upd b γ (ctrls i) = γ (ctrls i)) →
      (∀ b γ i, upd b γ (scratches i) = γ (scratches i)) →
      ∀ (Θ : CQAssertionCompat Var (2 ^ n)),
        (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
        restrictZeroWires (wireList k scratches)
          (wp (withAndChain v k acc ctrls scratches hacc_c hacc_s hc_s hs_inj
            (fun w hw => .circuit (leaf w hw))).compile Θ) =
        restrictZeroWires (wireList k scratches)
          (wpQAssignCompat
            (toffChainCircuit k acc ctrls scratches hacc_c hacc_s hc_s hs_inj leaf).eval Θ)
  | 0, acc, _, _, _, _, _, _, leaf, _, _, _, _, _, _, Θ, _ => by
      simp[wireList, restrictZeroWires, withAndChain, toffChainCircuit, compile_circuit]
  | k + 1, acc, ctrls, scratches, hacc_c, hacc_s, hc_s, hs_inj, leaf, φ, upd,
      hleaf, hupd_acc, hupd_c, hupd_s, Θ, hΘ => by
      let s₀ := scratches 0
      let tail := wireList k (fun i => scratches i.succ)
      let cAnd := Circuit.andCompute acc (ctrls 0) s₀ (hacc_s 0) (hc_s 0 0)
      let cToff := Circuit.TOFF acc (ctrls 0) s₀ (hacc_c 0) (hacc_s 0) (hc_s 0 0)
      let hs_tail : Function.Injective (fun i : Fin k => scratches i.succ) :=
        hs_inj.comp (Fin.succ_injective _)
      let subLeaf : (w : Wire n) → (w = s₀ ∨ ∃ i : Fin k, w = scratches i.succ) → Circuit n :=
        fun w hw => leaf w (hw.elim (fun h => Or.inr ⟨0, h⟩) (fun ⟨i, h⟩ => Or.inr ⟨i.succ, h⟩))
      let innerDyn : DynamicCircuit Var n := withAndChain v k s₀ (fun i => ctrls i.succ)
        (fun i => scratches i.succ) (fun i => (hc_s i.succ 0).symm)
        (fun i h => Fin.succ_ne_zero i (hs_inj h).symm) (fun i j => hc_s i.succ j.succ) hs_tail
        (fun w hw => DynamicCircuit.circuit (subLeaf w hw))
      let innerRef := toffChainCircuit k s₀ (fun i => ctrls i.succ) (fun i => scratches i.succ)
        (fun i => (hc_s i.succ 0).symm) (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
        (fun i j => hc_s i.succ j.succ) hs_tail subLeaf
      let Ψ := wp (andUncompute v acc (ctrls 0) s₀ (hacc_c 0)).compile Θ
      have hΨ : ∀ σ' val', Ψ (Function.update σ' v val') = Ψ σ' :=
        wp_andUncompute_update_self v acc (ctrls 0) s₀ (hacc_c 0) Θ
      have hdisj_and : ∀ w ∈ tail, w ∉ cAnd.support := fun w hw => by
        obtain ⟨i, rfl⟩ := mem_wireList_iff.mp hw
        rw [Circuit.support_andCompute]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(hacc_s i.succ).symm, (hc_s 0 i.succ).symm, fun h => Fin.succ_ne_zero i (hs_inj h)⟩
      have ih := restrictZeroWires_wp_withAndChain v k s₀ (fun i => ctrls i.succ)
        (fun i => scratches i.succ) (fun i => (hc_s i.succ 0).symm)
        (fun i h => Fin.succ_ne_zero i (hs_inj h).symm) (fun i j => hc_s i.succ j.succ)
        hs_tail subLeaf φ upd (fun top _ γ => hleaf top _ γ) (fun b γ => hupd_s b γ 0)
        (fun b γ i => hupd_c b γ i.succ) (fun b γ i => hupd_s b γ i.succ) Ψ hΨ
      have hpres (q : Wire n) (hq : ∀ i : Fin k, q ≠ scratches i.succ)
          (hu : ∀ b γ, upd b γ q = γ q) :=
        toffChainCircuit_preserves_wire k s₀ (fun i => ctrls i.succ) (fun i => scratches i.succ)
          (fun i => (hc_s i.succ 0).symm) (fun i h => Fin.succ_ne_zero i (hs_inj h).symm)
          (fun i j => hc_s i.succ j.succ) hs_tail subLeaf φ upd (fun top _ γ =>
            hleaf top _ γ) q hq hu
      have hconj := restrictToZeroAncilla_wp_withTempAnd_of_update_eq
        v acc (ctrls 0) s₀ (hacc_c 0) (hacc_s 0) (hc_s 0 0) (DynamicCircuit.circuit innerRef)
          innerRef.eval Θ hΘ
        (by simp [compile_circuit])
        (toffoli_conj_clean_of_preserves_three acc (ctrls 0) s₀ (hacc_c 0) (hacc_s 0) (hc_s 0 0)
          innerRef.eval.1 (hpres acc (fun i => hacc_s i.succ) hupd_acc)
          (hpres (ctrls 0) (fun i => hc_s 0 i.succ) (fun b γ => hupd_c b γ 0))
          (hpres s₀ (fun i h => Fin.succ_ne_zero i (hs_inj h).symm) (fun b γ => hupd_s b γ 0)))
      have hfold (d : DynamicCircuit Var n) : wpQAssignCompat cAnd.eval (wp d.compile Ψ) =
          wp (withTempAnd v acc (ctrls 0) s₀ (hacc_c 0) (hacc_s 0) (hc_s 0 0) d).compile Θ := by
        simp [cAnd, Ψ, withTempAnd, andCompute, compile_seq, compile_circuit]
      have heval_eq : (toffChainCircuit (k + 1) acc ctrls scratches hacc_c hacc_s hc_s hs_inj
          leaf).eval = cToff.eval * innerRef.eval * cToff.eval := by
        simp only [toffChainCircuit, Circuit.eval_seq, mul_assoc]
        rfl
      simp only [wireList, restrictZeroWires, withAndChain]
      have hc : wpQAssignCompat innerRef.eval Ψ = wp (DynamicCircuit.circuit innerRef).compile Ψ :=
        by
        simp [compile_circuit]
      rw [← hfold innerDyn, restrictZeroWires_wp_qAssign_comm cAnd tail hdisj_and, ih,
        ← restrictZeroWires_wp_qAssign_comm cAnd tail hdisj_and, hc,
        hfold (DynamicCircuit.circuit innerRef), restrictZeroWires_comm_singleton, hconj,
          ← heval_eq,
        ← restrictZeroWires_comm_singleton]
end QHL
end DynCircuitExt
end
end ModGidneyPointEq

section ModHeavyHeadAndProjectile128
@[expose] public section
namespace HeavyHeadAndProjectile128
abbrev SubGridParity3 : Type := Fin 3 → Bool
abbrev FineCoord128 : Type := Fin 3 → Fin 128
end HeavyHeadAndProjectile128
end
end ModHeavyHeadAndProjectile128

section ModInPlaceFullAddSlice
@[expose] public section
namespace InPlaceFullAddSliceAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end InPlaceFullAddSliceAlt
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace InPlaceFullAddSlice
section BasisKetAndProjectors
variable {n : ℕ}
noncomputable def ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
def bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1
@[simp] private theorem lemHex12 {q : ℕ} (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β
@[simp] private theorem lemHex13 {q : ℕ} (j : Fin (2 ^ q)) : (basisBitsEquiv q).symm
    (basisBits q j) = j := (basisBitsEquiv q).symm_apply_apply j
theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
private theorem lemHex14 (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket, basisState]
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have hcol := congrFun (h (basisBits n j)) i
  simpa [← lemHex14, Matrix.mulVec_single_one] using hcol
private theorem lemHex15 (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (v : Fin (2 ^ n) → ℂ) :
    (A * B).mulVec v = A.mulVec (B.mulVec v) := (Matrix.mulVec_mulVec v A B).symm
theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl
private noncomputable def lemHex16 {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] private theorem lemHex17 {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : lemHex16 β r γ (r i) = γ i := by
  simp [lemHex16, QRegister.basisBits_replaceIndex_apply]
private theorem lemHex18 {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (w : Wire n) (hw : w ∉ Set.range r.wires) : lemHex16 β r γ w = β w := by
  simp [lemHex16, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
private theorem lemHex19 {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    lemHex16 β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [lemHex17]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h => hi (r.wires.injective h)), hγ i hi]
  · rw [lemHex18 _ _ _ _ hw,
      Function.update_of_ne (fun h => hw ⟨i₀, h.symm⟩)]
private noncomputable abbrev lemHex1a {k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin
    (2 ^ k) := (basisBitsEquiv k).symm (fun i => β (r i))
private theorem lemHex1b {k : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) : (r.embedMatrix A).mulVec (ket β) = ∑ l : Fin (2 ^ k), A l
    (lemHex1a r β) • ket (lemHex16 β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBitsEquiv n).symm β) = lemHex1a r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [lemHex16, ket, basisState]
private theorem lemHex1c {k : ℕ} (r : QRegister k n) (perm : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) : (r.embedMatrix (Equiv.Perm.permMatrix ℂ perm)).mulVec (ket β) = ket
    (lemHex16 β r (basisBits k (perm.symm (lemHex1a r β)))) := by
  rw [lemHex1b, Finset.sum_eq_single (perm.symm (lemHex1a r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have hne : perm l ≠ lemHex1a r β := fun h => hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne]
  · simp
private theorem lemHex1d (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ) (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) = A 0 (if β q = 0 then 0 else 1) •
    ket (Function.update β q 0) + A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1)
    := by
  have hloc : lemHex1a (QRegister.singleton q) β = if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBitsEquiv 1).symm (fun _ => b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ => b) :
      lemHex16 β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [lemHex19 _ _ _ 0 (fun i hi => absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [lemHex1b, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0,1; 1,0]).mulVec _ = _
  rw [lemHex1d]
  have hadd : (1 : ZMod 2) + 1 = 0 := rfl
  rcases bit_cases (β q) with hb | hb <;> simp [hb, hadd]
theorem ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1,0; 0,-1]).mulVec _ = _
  rw [lemHex1d]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e, bitSign]
theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw[Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val, lemHex1c]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBitsEquiv 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [lemHex1a, hloc, lemHex19 _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi
theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) = ket
    (Function.update β t (β t + β c₁ * β c₂)) := by
  rw[Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val, lemHex1c]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBitsEquiv 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [lemHex1a, hloc, lemHex19 _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi
theorem ket_projector (q : Wire n) (o : Fin (2 ^ 1)) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (ket β) =
      if β q = (o.val : ZMod 2) then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ (b : ZMod 2) (o : Fin (2 ^ 1)),
      (((basisBitsEquiv 1).symm (fun _ => b) : Fin (2 ^ 1)) = o ↔ b = (o.val : ZMod 2)) := by
    decide
  have hext : (QRegister.singleton q).extractIndex ((basisBitsEquiv n).symm β) =
      (basisBitsEquiv 1).symm (fun _ => β q) := by
    simp [QRegister.extractIndex]
  simp only [hext]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((h _ _).1 h1) h2
  · exact absurd ((h _ _).2 h2) h1
  · rfl
theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 := by
  simpa using ket_projector q 0 β
noncomputable def projZeroAll : (k : ℕ) → (Fin k → Wire n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | 0, _ => 1
  | k + 1, scr =>
      (QRegister.singleton (scr 0)).basisOutcomeProjector 0 *
        projZeroAll k (fun i => scr i.succ)
theorem ket_projZeroAll :
    ∀ (k : ℕ) (scr : Fin k → Wire n) (β : BitAssignment n),
      (projZeroAll k scr).mulVec (ket β) =
        if ∀ j : Fin k, β (scr j) = 0 then ket β else 0
  | 0, _, β => by simp [projZeroAll]
  | k + 1, scr, β => by
      simp only [projZeroAll, lemHex15, ket_projZeroAll]
      by_cases htail : ∀ j : Fin k, β (scr j.succ) = 0
      · simp only [htail, imp_true_iff, ↓reduceIte, ket_projector_zero]
        by_cases h0 : β (scr 0) = 0
        · have hall : ∀ j : Fin (k + 1), β (scr j) = 0 := Fin.cases h0 htail
          simp only [h0, hall, imp_true_iff, ↓reduceIte]
        · have hnot : ¬ ∀ j : Fin (k + 1), β (scr j) = 0 := fun h => h0 (h 0)
          simp only [h0, hnot, ↓reduceIte]
      · have hnot : ¬ ∀ j : Fin (k + 1), β (scr j) = 0 := fun h => htail (fun j => h j.succ)
        simp only [htail, hnot, ↓reduceIte, Matrix.mulVec_zero]
theorem basisOutcomeProjector_comm_projZeroAll (w : Wire n) (o : Fin (2 ^ 1)) (k : ℕ)
    (scr : Fin k → Wire n) : (QRegister.singleton w).basisOutcomeProjector o * projZeroAll k
    scr = projZeroAll k scr * (QRegister.singleton w).basisOutcomeProjector o := by
  apply matrix_ext_ket
  intro β
  simp only [lemHex15, ket_projector, ket_projZeroAll]
  by_cases hw : β w = (o.val : ZMod 2) <;> by_cases hs : ∀ j : Fin k, β (scr j) = 0
  · simp only [hw, hs, imp_true_iff, ↓reduceIte, ket_projector, ket_projZeroAll]
  · simp only [hw, hs, ↓reduceIte, ket_projZeroAll, Matrix.mulVec_zero]
  · simp only [hw, hs, imp_true_iff, ↓reduceIte, ket_projector, Matrix.mulVec_zero]
  · simp only [hw, hs, ↓reduceIte, Matrix.mulVec_zero]
theorem projZeroAll_conjTranspose :
    ∀ (k : ℕ) (scr : Fin k → Wire n),(projZeroAll k scr)ᴴ = projZeroAll k scr
  | 0, _ => conjTranspose_one
  | k + 1, scr => by
      simp only [projZeroAll, conjTranspose_mul, projZeroAll_conjTranspose,
        QRegister.basisOutcomeProjector_conjTranspose]
      exact (basisOutcomeProjector_comm_projZeroAll (scr 0) 0 k (fun i => scr i.succ)).symm
theorem toffoli_comm_projZeroAll (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (k : ℕ) (scr : Fin k → Wire n) (hdisj : ∀ j : Fin k, anc ≠ scr j) :
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * projZeroAll k scr = projZeroAll k scr *
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 := by
  apply matrix_ext_ket
  intro β
  have hpres : (∀ j : Fin k, (Function.update β anc (β anc + β c₁ * β c₂)) (scr j) = 0) ↔
      (∀ j : Fin k, β (scr j) = 0) := by
    refine ⟨fun h j => ?_, fun h j => ?_⟩
    · have hj := h j; rwa [Function.update_of_ne (hdisj j).symm] at hj
    · rw [Function.update_of_ne (hdisj j).symm]; exact h j
  by_cases hs : ∀ j : Fin k, β (scr j) = 0
  · simp only [lemHex15, ket_TOFF, ket_projZeroAll, hs, hpres.mpr hs, imp_true_iff, ↓reduceIte]
  · simp only [lemHex15, ket_TOFF, ket_projZeroAll, hs, mt hpres.mp hs, ↓reduceIte,
      Matrix.mulVec_zero]
theorem toffoli_eval_sq (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval * (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, lemHex15, Matrix.one_mulVec,
    ket_TOFF, Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
    Function.update_idem]
  have hadd : β t + β c₁ * β c₂ + β c₁ * β c₂ = β t := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]
theorem projZeroAll_eq_basisOutcomeProjector_zero {m : ℕ} (rWork : QRegister m n) :
    projZeroAll m rWork.wires = rWork.basisOutcomeProjector 0 := by
  apply matrix_ext_ket
  intro β
  have hzero : rWork.extractIndex ((basisBitsEquiv n).symm β) = 0 ↔
      ∀ j : Fin m, β (rWork j) = 0 := by
    simp only [(QRegExt.extractIndex_eq_zero_iff rWork), lemHex12]
  rw [ket_projZeroAll, ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  by_cases h : ∀ j : Fin m, β (rWork j) = 0
  · simp only [h, imp_true_iff, hzero.mpr h, ↓reduceIte]
  · simp only [h, mt hzero.mp h, ↓reduceIte]
end BasisKetAndProjectors
section CleanUnitaryAlgebra
variable {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
def RealizesCleanUnitary (v : Var) (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (c : DynamicCircuit Var n) (U : Unitary (2 ^ n)) : Prop := (∀ (Ψ : CQAssertionCompat Var (2 ^
    n)), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) → ∀ σ val, wp c.compile Ψ
    (Function.update σ v val) = wp c.compile Ψ σ) ∧ (∀ (Θ : CQAssertionCompat Var (2 ^ n)), (∀ σ
    val, Θ (Function.update σ v val) = Θ σ) → ∀ σ : Store Var, ((wp c.compile Θ σ).1).conj
    P_scr = ((wpQAssignCompat U Θ σ).1).conj P_scr)
theorem RealizesCleanUnitary.identity (v : Var) (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    : RealizesCleanUnitary v P_scr .identity (1 : Unitary (2 ^ n)) := by
  refine ⟨fun Ψ hΨ σ val => hΨ σ val, fun Θ _ σ => ?_⟩
  simp [wpQAssignCompat]
theorem RealizesCleanUnitary.circuit (v : Var) (P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (c : Circuit n) : RealizesCleanUnitary v P_scr (.circuit c) c.eval := by
  refine ⟨fun Ψ hΨ σ val => ?_, fun Θ _ σ => ?_⟩
  · simp [DynamicCircuit.compile_circuit, wpQAssignCompat, hΨ σ val]
  · simp [DynamicCircuit.compile_circuit]
theorem RealizesCleanUnitary.congr_unitary {v : Var}
    {P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {c : DynamicCircuit Var n}
    {U₁ U₂ : Unitary (2 ^ n)} (hP : P_scrᴴ = P_scr) (hc : RealizesCleanUnitary v P_scr c U₁)
    (heq : U₁.1 * P_scr = U₂.1 * P_scr) : RealizesCleanUnitary v P_scr c U₂ := by
  refine ⟨hc.1, fun Θ hΘ σ => ?_⟩
  rw [hc.2 Θ hΘ σ]
  have hadj : P_scr * U₁.1ᴴ = P_scr * U₂.1ᴴ := by
    have h := congrArg conjTranspose heq
    simpa [conjTranspose_mul, hP] using h
  simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, conj_conj, hadj]
theorem RealizesCleanUnitary.mono_proj {v : Var}
    {P_small P_big : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {c : DynamicCircuit Var n}
    {U : Unitary (2 ^ n)} (hPs : P_smallᴴ = P_small) (hPb : P_bigᴴ = P_big)
    (hsub : P_small * P_big = P_big) (hc : RealizesCleanUnitary v P_small c U) :
    RealizesCleanUnitary v P_big c U := by
  refine ⟨hc.1, fun Θ hΘ σ => ?_⟩
  have hleft : P_big * P_small = P_big := by
    have h := congrArg conjTranspose hsub
    simpa [conjTranspose_mul, hPs, hPb] using h
  calc
    ((wp c.compile Θ σ).1).conj P_big
      = (((wp c.compile Θ σ).1).conj P_small).conj P_big := by rw [conj_conj, hleft]
    _ = (((wpQAssignCompat U Θ σ).1).conj P_small).conj P_big := by rw [hc.2 Θ hΘ σ]
    _ = ((wpQAssignCompat U Θ σ).1).conj P_big := by rw [conj_conj, hleft]
private theorem rcu_seq_asym {v : Var} {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : RealizesCleanUnitary v P₁ c₁ U₁) (h₂ : RealizesCleanUnitary v P₂ c₂ U₂)
    (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) : RealizesCleanUnitary v P₁ (.seq c₁ c₂) (U₂ * U₁) := by
  refine ⟨fun Ψ hΨ σ val => ?_, fun Θ hΘ σ => ?_⟩
  · simp only [compile_seq, wp_qSeq]
    exact h₁.1 (wp c₂.compile Ψ) (h₂.1 Ψ hΨ) σ val
  · have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
      simpa [conjTranspose_mul, hP₁, hP₂, ← Matrix.mul_assoc] using congrArg conjTranspose hclean
    simp only [compile_seq, wp_qSeq]
    rw [h₁.2 (wp c₂.compile Θ) (h₂.1 Θ hΘ) σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [← hadj, ← conj_conj, h₂.2 Θ hΘ σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj, Submonoid.coe_mul, conjTranspose_mul]
    rw [← Matrix.mul_assoc (P₁ * U₁.1ᴴ) P₂ U₂.1ᴴ, hadj, Matrix.mul_assoc]
theorem RealizesCleanUnitary.seq {v : Var} {P_scr : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP : P_scrᴴ = P_scr)
    (h₁ : RealizesCleanUnitary v P_scr c₁ U₁) (h₂ : RealizesCleanUnitary v P_scr c₂ U₂)
    (hclean : P_scr * (U₁.1 * P_scr) = U₁.1 * P_scr) : RealizesCleanUnitary v P_scr
    (.seq c₁ c₂) (U₂ * U₁) :=
  rcu_seq_asym hP hP h₁ h₂ hclean
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
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let P_rest := projZeroAll k scr
  let P_all := projZeroAll (k + 1) (Fin.cons anc scr)
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let V := T_anc * U_body * T_anc
  have hP_all_def : P_all = P₀ * P_rest := rfl
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hPr_herm : P_restᴴ = P_rest := projZeroAll_conjTranspose k scr
  have hcomm_P : P₀ * P_rest = P_rest * P₀ :=
    basisOutcomeProjector_comm_projZeroAll anc 0 k scr
  have hcomm_T : T_anc.1 * P_rest = P_rest * T_anc.1 :=
    toffoli_comm_projZeroAll c₁ c₂ anc h₁₂ h₁a h₂a k scr hdisj
  have hcomm_T_adj : P_rest * T_anc.1ᴴ = T_anc.1ᴴ * P_rest := by
    have h := congrArg conjTranspose hcomm_T
    simpa [conjTranspose_mul, hPr_herm] using h
  have hV_eq_clean : V.1 * P_all = U_clean.1 * P_all := by
    apply matrix_ext_ket
    intro β
    change (T_anc.1 * U_body.1 * T_anc.1 * (P₀ * projZeroAll k scr)).mulVec (ket β) =
      (U_clean.1 * (P₀ * projZeroAll k scr)).mulVec (ket β)
    simp only [lemHex15, ket_projZeroAll]
    by_cases hscr : ∀ j : Fin k, β (scr j) = 0
    · simp only [hscr, imp_true_iff, ↓reduceIte, P₀, ket_projector_zero]
      by_cases hanc : β anc = 0
      · simp only [hanc, ↓reduceIte, T_anc, ket_TOFF, zero_add]
        exact hket_eq β hanc hscr
      · simp only [hanc, ↓reduceIte, Matrix.mulVec_zero]
    · simp only [hscr, ↓reduceIte, Matrix.mulVec_zero]
  have hU_clean_P₀ : P₀ * (U_clean.1 * P_all) = U_clean.1 * P_all := by
    apply matrix_ext_ket
    intro β
    change (P₀ * (U_clean.1 * (P₀ * projZeroAll k scr))).mulVec (ket β) =
      (U_clean.1 * (P₀ * projZeroAll k scr)).mulVec (ket β)
    simp only [lemHex15, ket_projZeroAll]
    by_cases hscr : ∀ j : Fin k, β (scr j) = 0
    · simp only [hscr, imp_true_iff, ↓reduceIte]
      by_cases hanc : β anc = 0
      · have hp : P₀.mulVec (ket β) = ket β := by
          simp only [P₀, ket_projector_zero, hanc, ↓reduceIte]
        rw [hp]
        exact hket_clean β hanc hscr
      · have hp : P₀.mulVec (ket β) = 0 := by
          simp only [P₀, ket_projector_zero, hanc, ↓reduceIte]
        rw [hp, Matrix.mulVec_zero, Matrix.mulVec_zero]
    · simp only [hscr, ↓reduceIte, Matrix.mulVec_zero]
  have hclean_adj : P_all * U_clean.1ᴴ * P₀ = P_all * U_clean.1ᴴ := by
    have hPall_herm : P_allᴴ = P_all := projZeroAll_conjTranspose (k + 1) (Fin.cons anc scr)
    have h := congrArg conjTranspose hU_clean_P₀
    simpa [conjTranspose_mul, hP₀_herm, hPall_herm, ← Matrix.mul_assoc] using h
  have hT_sq : T_anc * T_anc = 1 := toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a
  have hU_eq : U_body * T_anc = T_anc * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
  refine ⟨fun Ψ _ σ val => ?_, fun Θ hΘ σ => ?_⟩
  · simp only [andCompute, compile_seq, compile_circuit, wp_qSeq, wp_circuit_compile_compat,
    wpQAssignCompat]
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
          P₀ =
        ((wpQAssignCompat T_anc (wp body.compile Ψ) σ).1).conj P₀ := by
      have h := congrFun
        (restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a
          (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile) Θ) σ
      exact congrArg Subtype.val h
    have hstep_uncomp : ((wpQAssignCompat T_anc Ψ σ).1).conj P₀ = (Θ σ).1.conj P₀ := by
      have h := congrFun
        (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
          v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ) σ
      exact congrArg Subtype.val h
    have hPall_eq : P_all = P_rest * P₀ := by
      rw [hP_all_def]
      exact hcomm_P
    change ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
        (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)) Θ σ).1).conj
      P_all = ((wpQAssignCompat U_clean Θ σ).1).conj P_all
    rw [hPall_eq, ← conj_conj, hstep1]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    have hswap1 : P_rest * (P₀ * T_anc.1ᴴ) = (P₀ * T_anc.1ᴴ) * P_rest := by
      rw [← Matrix.mul_assoc, ← hcomm_P, Matrix.mul_assoc, hcomm_T_adj, ← Matrix.mul_assoc]
    rw [hswap1, ← conj_conj, hbody.2 Ψ hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    have hprod_adj :
        (P₀ * T_anc.1ᴴ) * (P_rest * U_body.1ᴴ) = (P_all * U_clean.1ᴴ * P₀) * T_anc.1ᴴ := by
      have h1 : (P₀ * T_anc.1ᴴ) * (P_rest * U_body.1ᴴ) = P_all * (U_body * T_anc).1ᴴ := by
        rw [hPall_eq, Submonoid.coe_mul, conjTranspose_mul,
          ← Matrix.mul_assoc (P₀ * T_anc.1ᴴ) P_rest, ← hswap1]
        simp only [Matrix.mul_assoc]
      have h2 : P_all * V.1ᴴ = P_all * U_clean.1ᴴ := by
        simpa [P_all, conjTranspose_mul, projZeroAll_conjTranspose (k + 1) (Fin.cons anc scr)] using
          congrArg conjTranspose hV_eq_clean
      rw [h1, hU_eq, Submonoid.coe_mul, conjTranspose_mul, ← Matrix.mul_assoc, h2, hclean_adj]
    rw [hprod_adj, Matrix.mul_assoc (P_all * U_clean.1ᴴ) P₀ T_anc.1ᴴ, ← conj_conj]
    have hmid : (Ψ σ).1.conj (P₀ * T_anc.1ᴴ) = (Θ σ).1.conj P₀ := by
      simpa [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, conj_conj] using hstep_uncomp
    rw [hmid, conj_conj, hclean_adj, hPall_eq]
end CleanUnitaryAlgebra
def PreservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (d : DynamicCircuit Var n) : Prop :=
  ∀ (M : Observable (Fin (2 ^ n))), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ =>
    M) = fun _ => M'
theorem PreservesStoreConst.circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (c : Circuit n) : PreservesStoreConst (Var := Var) (.circuit c) := fun M =>
  ⟨qAssignObsMap c.eval M, by
    funext σ
    simp [DynamicCircuit.compile_circuit, wpQAssignCompat]⟩
theorem PreservesStoreConst.identity {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} :
    PreservesStoreConst (Var := Var) (n := n) .identity := fun M => ⟨M, rfl⟩
theorem PreservesStoreConst.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {d₁ d₂ : DynamicCircuit Var n} (h₁ : PreservesStoreConst d₁) (h₂ : PreservesStoreConst d₂)
    : PreservesStoreConst (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hM₂⟩ := h₂ M
  obtain ⟨M₁, hM₁⟩ := h₁ M₂
  exact ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp_qSeq, hM₂, hM₁]⟩
theorem PreservesStoreConst.andUncompute {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) :
    PreservesStoreConst (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) := by
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have hinner : PreservesStoreConst (.seq (.measure v (QRegister.singleton anc)) (dynQIfVar v
      (.circuit (Circuit.andUncomputeFixup c₁ c₂ anc h₁₂)) .identity)) := by
    intro M
    let σ₀ : Store Var := fun _ => 0
    let inner : DynamicCircuit Var n := .seq (.measure v (QRegister.singleton anc)) (dynQIfVar
        v (.circuit (Circuit.andUncomputeFixup c₁ c₂ anc h₁₂)) .identity)
    refine ⟨wp inner.compile (fun _ => M) σ₀, ?_⟩
    funext σ
    simp only [inner, DynamicCircuit.compile_seq, DynamicCircuit.compile_measure,
      DynamicCircuit.compile_qIf, DynamicCircuit.compile_circuit, QProg.measureRegister, wp_qSeq,
      wp_qIf, wp_qMeasure_apply, CQAssertionCompat.subst_apply]
    congr 1; funext o
    simp [Store.subst, wpQAssignCompat]
  exact PreservesStoreConst.seq (PreservesStoreConst.circuit (Circuit.H anc)) hinner
@[simp] lemma lemHex1e : (1 : ZMod 2).val = 1 := rfl
theorem wire_ne_of_lt {M : ℕ} {a b : Wire M} (h : a.val < b.val) : a ≠ b :=
  fun heq ↦ absurd (congrArg Fin.val heq) (Nat.ne_of_lt h)
theorem wire_ne_of_gt {M : ℕ} {a b : Wire M} (h : b.val < a.val) : a ≠ b :=
  (wire_ne_of_lt h).symm
theorem mul_mulVec_prog {n : ℕ} (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (v : Fin (2 ^ n) → ℂ) : (A * B).mulVec v = A.mulVec (B.mulVec v) :=
  (Matrix.mulVec_mulVec v A B).symm
noncomputable def writeRegProg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeRegProg_apply_reg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeRegProg β r γ (r i) = γ i := by
  simp [writeRegProg, QRegister.basisBits_replaceIndex_apply]
theorem writeRegProg_apply_of_not_mem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeRegProg β r γ w = β w := by
  simp [writeRegProg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
noncomputable abbrev localIdxProg {k n : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin
    (2 ^ k) := (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket_prog {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdxProg r β) • ket (writeRegProg β r (basisBits k l)) := by
  simpa only [lemHex16, writeRegProg] using lemHex1b r A β
inductive CliffProg (M : ℕ) where
  | nil : CliffProg M
  | x (q : Wire M) : CliffProg M
  | cnot (c t : Wire M) (h : c ≠ t) : CliffProg M
  | seq (c₁ c₂ : CliffProg M) : CliffProg M
namespace CliffProg
def eval {M : ℕ} : CliffProg M → BitAssignment M → BitAssignment M
  | .nil, β => β
  | .x q, β => Function.update β q (β q + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .seq c₁ c₂, β => c₂.eval (c₁.eval β)
def inv {M : ℕ} : CliffProg M → CliffProg M
  | .nil => .nil
  | .x q => .x q
  | .cnot c t h => .cnot c t h
  | .seq c₁ c₂ => .seq c₂.inv c₁.inv
def toCircuit {M : ℕ} : CliffProg M → Circuit M
  | .nil => .identity
  | .x q => Circuit.X q
  | .cnot c t h => Circuit.CNOT c t h
  | .seq c₁ c₂ => c₁.toCircuit ;;ᶜ c₂.toCircuit
def onRegister {M n : ℕ} (r : QRegister M n) : CliffProg M → CliffProg n
  | .nil => .nil
  | .x q => .x (r q)
  | .cnot c t h => .cnot (r c) (r t) (r.wires.injective.ne h)
  | .seq c₁ c₂ => .seq (c₁.onRegister r) (c₂.onRegister r)
def SupportsBelow {M : ℕ} (bound : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x q => q.val < bound
  | .cnot c t _ => c.val < bound ∧ t.val < bound
  | .seq c₁ c₂ => c₁.SupportsBelow bound ∧ c₂.SupportsBelow bound
@[simp]
theorem toCircuit_count_toff {M : ℕ} : ∀ c : CliffProg M, c.toCircuit.count PrimitiveGate.TOFF = 0
  | .nil => by simp [toCircuit]
  | .x _ => by simp [toCircuit]
  | .cnot _ _ _ => by simp [toCircuit]
  | .seq c₁ c₂ => by simp [toCircuit, toCircuit_count_toff]
@[simp]
theorem toCircuit_count_t {M : ℕ} : ∀ c : CliffProg M, c.toCircuit.count PrimitiveGate.T = 0
  | .nil => by simp [toCircuit]
  | .x _ => by simp [toCircuit]
  | .cnot _ _ _ => by simp [toCircuit]
  | .seq c₁ c₂ => by simp [toCircuit, toCircuit_count_t]
theorem toCircuit_eval_ket {M : ℕ} :
    ∀ (c : CliffProg M) (β : BitAssignment M),
      c.toCircuit.eval.1.mulVec (ket β) = ket (c.eval β)
  | .nil, _ => by simp [toCircuit, eval]
  | .x q, β => by rw [toCircuit, eval, ket_X]
  | .cnot c t h, β => by rw [toCircuit, eval, ket_CNOT]
  | .seq c₁ c₂, β => by
      rw [toCircuit, eval, eval_seq_mulVec, toCircuit_eval_ket c₁, toCircuit_eval_ket c₂]
theorem onRegister_toCircuit_eval {M n : ℕ} (r : QRegister M n) :
    ∀ c : CliffProg M, ((c.onRegister r).toCircuit).eval = (c.toCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toCircuit]
  | .x q => by
      simp only [onRegister, toCircuit, Circuit.X, Circuit.single, Circuit.onRegister]
      congr 2
  | .cnot c t h => by
      simp only [onRegister, toCircuit, Circuit.CNOT, Circuit.onRegister]
      congr 2; apply InPlaceFullAddSliceAlt.qreg_ext; intro i; fin_cases i <;> rfl
  | .seq c₁ c₂ => by simp [onRegister, toCircuit, Circuit.eval_seq, onRegister_toCircuit_eval]
theorem inv_eval {M : ℕ} : ∀ (c : CliffProg M) (β : BitAssignment M), c.inv.eval (c.eval β) = β
  | .nil, _ => rfl
  | .x q, β => by
      funext w
      by_cases hw : w = q
      · subst hw
        have h11 : (1 + 1 : ZMod 2) = 0 := rfl
        simp [inv, eval, add_assoc, h11]
      · simp [inv, eval, Function.update_of_ne hw]
  | .cnot c t h, β => by
      funext w
      by_cases hw : w = t
      · subst hw
        simp [inv, eval, Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero]
      · simp [inv, eval, Function.update_of_ne hw]
  | .seq c₁ c₂, β => by simp [inv, eval, inv_eval]
theorem eval_outside {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound →
      ∀ (β : BitAssignment M) (w : Wire M), bound ≤ w.val → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x q, hq, β, w, hw =>
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le hq hw)) _ _
  | .cnot _ t _, ⟨_, ht⟩, β, w, hw =>
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le ht hw)) _ _
  | .seq c₁ c₂, ⟨h₁, h₂⟩, β, w, hw => by
      simp only [eval]
      rw [eval_outside c₂ h₂ _ w hw, eval_outside c₁ h₁ _ w hw]
end CliffProg
inductive TempPhaseProg (m : ℕ) where
  | nil : TempPhaseProg m
  | cliff (c : CliffProg m) : TempPhaseProg m
  | z (q : Wire m) : TempPhaseProg m
  | seq (p₁ p₂ : TempPhaseProg m) : TempPhaseProg m
  | tempAnd (c₁ c₂ anc : Wire m) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : TempPhaseProg m) : TempPhaseProg m
namespace TempPhaseProg
def cnot {m : ℕ} (c t : Wire m) (h : c ≠ t) : TempPhaseProg m := .cliff (.cnot c t h)
def evalBits {m : ℕ} : TempPhaseProg m → BitAssignment m → BitAssignment m
  | .nil, β => β
  | .cliff c, β => c.eval β
  | .z _, β => β
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      let β₂ := body.evalBits β₁
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)
def evalSign {m : ℕ} : TempPhaseProg m → BitAssignment m → ZMod 2
  | .nil, _ => 0
  | .cliff _, _ => 0
  | .z q, β => β q
  | .seq p₁ p₂, β => p₁.evalSign β + p₂.evalSign (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      body.evalSign (Function.update β anc (β anc + β c₁ * β c₂))
def countTempAnd {m : ℕ} : TempPhaseProg m → ℕ
  | .nil => 0
  | .cliff _ => 0
  | .z _ => 0
  | .seq p₁ p₂ => p₁.countTempAnd + p₂.countTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.countTempAnd
def toToffCircuit {m : ℕ} : TempPhaseProg m → Circuit m
  | .nil => .identity
  | .cliff c => c.toCircuit
  | .z q => Circuit.Z q
  | .seq p₁ p₂ => p₁.toToffCircuit ;;ᶜ p₂.toToffCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toToffCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
def onRegister {m n : ℕ} (r : QRegister m n) : TempPhaseProg m → TempPhaseProg n
  | .nil => .nil
  | .cliff c => .cliff (c.onRegister r)
  | .z q => .z (r q)
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc)
        (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
        (body.onRegister r)
def toDyn {Var : Type} {n : ℕ} (v : Var) : TempPhaseProg n → DynamicCircuit Var n
  | .nil => .circuit .identity
  | .cliff c => .circuit c.toCircuit
  | .z q => .circuit (Circuit.Z q)
  | .seq p₁ p₂ => .seq (p₁.toDyn v) (p₂.toDyn v)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq (body.toDyn v) (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
@[simp] theorem onRegister_countTempAnd {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempPhaseProg m, (p.onRegister r).countTempAnd = p.countTempAnd
  | .nil => rfl
  | .cliff _ => rfl
  | .z _ => rfl
  | .seq p₁ p₂ => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
  | .tempAnd _ _ _ _ _ _ body => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
@[simp] theorem toDyn_count_toff {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempPhaseProg n, (p.toDyn v).count PrimitiveGate.TOFF = 0
  | .nil => by simp [toDyn]
  | .cliff _ => by simp [toDyn]
  | .z _ => by simp [toDyn]
  | .seq p₁ p₂ => by simp [toDyn, toDyn_count_toff]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [toDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, toDyn_count_toff]
@[simp] theorem toDyn_count_t {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempPhaseProg n, (p.toDyn v).count PrimitiveGate.T = 4 * p.countTempAnd
  | .nil => by simp [toDyn, countTempAnd]
  | .cliff _ => by simp [toDyn, countTempAnd]
  | .z _ => by simp [toDyn, countTempAnd]
  | .seq p₁ p₂ => by
      simp [toDyn, countTempAnd, toDyn_count_t]
      ring
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [toDyn, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, countTempAnd, toDyn_count_t]
      ring
theorem bitSign_eq_neg_one_pow (b : ZMod 2) : bitSign b = (-1 : ℂ) ^ b.val := by
  rcases bit_cases b with rfl | rfl <;> norm_num [bitSign]
theorem neg_one_pow_zmod2_mul (a b : ZMod 2) :
    ((-1 : ℂ) ^ a.val) * ((-1 : ℂ) ^ b.val) = (-1 : ℂ) ^ (a + b).val := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · have h11 : (1 + 1 : ZMod 2) = 0 := rfl
    rw [h11]
    norm_num
theorem toToffCircuit_eval_ket {m : ℕ} :
    ∀ (p : TempPhaseProg m) (β : BitAssignment m),
      (p.toToffCircuit).eval.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (p.evalSign β).val) • ket (p.evalBits β)
  | .nil, β => by simp [toToffCircuit, evalSign, evalBits]
  | .cliff c, β => by rw [toToffCircuit, evalSign, evalBits, c.toCircuit_eval_ket]; simp
  | .z q, β => by rw [toToffCircuit, evalSign, evalBits, ket_Z, bitSign_eq_neg_one_pow]
  | .seq p₁ p₂, β => by
      rw[toToffCircuit, eval_seq_mulVec, toToffCircuit_eval_ket p₁, Matrix.mulVec_smul,
          toToffCircuit_eval_ket p₂, smul_smul, neg_one_pow_zmod2_mul]
      rfl
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, β => by
      rw [toToffCircuit, eval_seq_mulVec, eval_seq_mulVec,
        ket_TOFF, toToffCircuit_eval_ket body, Matrix.mulVec_smul, ket_TOFF]
      rfl
theorem onRegister_toToffCircuit_eval {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempPhaseProg m,
      ((p.onRegister r).toToffCircuit).eval = (p.toToffCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toToffCircuit]
  | .cliff c => by simp [onRegister, toToffCircuit, c.onRegister_toCircuit_eval]
  | .z q => by
      simp only [onRegister, toToffCircuit, Circuit.Z, Circuit.single, Circuit.onRegister]
      congr 2
  | .seq p₁ p₂ => by
      simp [onRegister, toToffCircuit, Circuit.eval_seq, onRegister_toToffCircuit_eval]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      have htoff : (Circuit.TOFF (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)
          (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)).eval =
          ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).onRegister r).eval := by
        simp only [Circuit.TOFF, Circuit.onRegister]
        congr 2; apply InPlaceFullAddSliceAlt.qreg_ext; intro i; fin_cases i <;> rfl
      simp [onRegister, toToffCircuit, Circuit.eval_seq, htoff,
        onRegister_toToffCircuit_eval r body]
end TempPhaseProg
def cleanRem (M rem : ℕ) (β : BitAssignment M) : Prop :=
  ∀ w : Wire M, M - rem ≤ w.val → β w = 0
def tailScr {M n : ℕ} (rComb : QRegister M n) (rem : ℕ) (h : rem ≤ M) : Fin rem → Wire n :=
  fun j ↦ rComb ⟨(M - rem) + j.val, by omega⟩
theorem tailScr_succ {M n : ℕ} (rComb : QRegister M n) (rem' : ℕ) (h : rem' + 1 ≤ M) :
    tailScr rComb (rem' + 1) h =
      Fin.cons (rComb ⟨M - (rem' + 1), by omega⟩) (tailScr rComb rem' (by omega)) := by
  funext j
  cases j using Fin.cases with
  | zero => simp only [Fin.cons_zero, tailScr, Fin.val_zero, add_zero]
  | succ i =>
      simp only [Fin.cons_succ, tailScr, Fin.val_succ]
      congr 1; ext; dsimp; omega
theorem projZeroAll_tailScr_sub {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M) (hle : rem₁ ≤ rem₂) : projZeroAll rem₁
    (tailScr rComb rem₁ h₁) * projZeroAll rem₂ (tailScr rComb rem₂ h₂) = projZeroAll rem₂
    (tailScr rComb rem₂ h₂) := by
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz₂ : ∀ j : Fin rem₂, β (tailScr rComb rem₂ h₂ j) = 0
  · have hz₁ : ∀ i : Fin rem₁, β (tailScr rComb rem₁ h₁ i) = 0 := by
      intro i
      have heq : tailScr rComb rem₁ h₁ i =
          tailScr rComb rem₂ h₂ ⟨(M - rem₁) - (M - rem₂) + i.val, by omega⟩ := by
        dsimp [tailScr]; congr 1; ext; dsimp; omega
      rw [heq]
      exact hz₂ _
    simp [hz₁, hz₂, ket_projZeroAll]
  · simp [hz₂]
def ValidCleanRem (M : ℕ) : ℕ → TempPhaseProg M → Prop
  | _, .nil => True
  | _, .cliff _ => True
  | _, .z _ => True
  | rem, .seq p₁ p₂ =>
      ∃ remMid : ℕ, remMid ≤ M ∧
        ValidCleanRem M rem p₁ ∧ ValidCleanRem M remMid p₂ ∧
        (∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remMid (p₁.evalBits β))
  | rem, .tempAnd c₁ c₂ anc _ _ _ body =>
      M - rem ≤ anc.val ∧
        let rem' := M - (anc.val + 1)
        ValidCleanRem M rem' body ∧
          (∀ β₁ : BitAssignment M, cleanRem M rem' β₁ →
            body.evalBits β₁ c₁ = β₁ c₁ ∧
              body.evalBits β₁ c₂ = β₁ c₂ ∧
              body.evalBits β₁ anc = β₁ anc)
theorem eval_onRegister_prog_ket {M n : ℕ} (rComb : QRegister M n)
    (p : TempPhaseProg M) (β : BitAssignment n) :
    let γ : BitAssignment M := fun idx ↦ β (rComb idx)
    ((p.onRegister rComb).toToffCircuit).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (p.evalSign γ).val) • ket (writeRegProg β rComb (p.evalBits γ)) := by
  intro γ
  rw [p.onRegister_toToffCircuit_eval rComb, Circuit.eval_onRegister,
    QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
  have hloc : localIdxProg rComb β = (basisBitsEquiv M).symm γ := rfl
  rw [hloc]
  have hcol : ∀ l : Fin (2 ^ M), (p.toToffCircuit).eval.1 l ((basisBitsEquiv M).symm γ) = if l
      = (basisBitsEquiv M).symm (p.evalBits γ) then ((-1 : ℂ) ^ (p.evalSign γ).val) else 0
      := by
    intro l
    have hk := congrFun (p.toToffCircuit_eval_ket γ) l
    simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using hk
  simp_rw [hcol, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hbb : basisBits M ((basisBitsEquiv M).symm (p.evalBits γ)) = p.evalBits γ :=
    (basisBitsEquiv M).apply_symm_apply _
  rw [hbb]
theorem RealizesCleanUnitary_seq_asym {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : RealizesCleanUnitary v P₁ c₁ U₁) (h₂ : RealizesCleanUnitary v P₂ c₂ U₂)
    (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) : RealizesCleanUnitary v P₁ (.seq c₁ c₂) (U₂ * U₁) :=
  rcu_seq_asym hP₁ hP₂ h₁ h₂ hclean
theorem realizes_of_validCleanRem
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (p : TempPhaseProg M) (rem : ℕ) (hrem : rem ≤ M),
      ValidCleanRem M rem p →
      RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
        ((p.onRegister rComb).toDyn v) (((p.onRegister rComb).toToffCircuit).eval)
  | .nil, rem, hrem, _ => RealizesCleanUnitary.circuit v _ _
  | .cliff _, rem, hrem, _ => RealizesCleanUnitary.circuit v _ _
  | .z _, rem, hrem, _ => RealizesCleanUnitary.circuit v _ _
  | .seq p₁ p₂, rem, hrem, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ => by
      let P₁ := projZeroAll rem (tailScr rComb rem hrem)
      let P₂ := projZeroAll remMid (tailScr rComb remMid hmid)
      have hP₁ : P₁ᴴ = P₁ := projZeroAll_conjTranspose rem _
      have hP₂ : P₂ᴴ = P₂ := projZeroAll_conjTranspose remMid _
      have ih₁ := realizes_of_validCleanRem v rComb p₁ rem hrem hv₁
      have ih₂ := realizes_of_validCleanRem v rComb p₂ remMid hmid hv₂
      have hclean : P₂ * (((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁) =
          ((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁ := by
        apply matrix_ext_ket
        intro β
        simp only [P₁, P₂, mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0
        · simp only [hz, imp_true_iff, ↓reduceIte, eval_onRegister_prog_ket,
            Matrix.mulVec_smul, ket_projZeroAll]
          have hγ : cleanRem M rem (fun idx ↦ β (rComb idx)) := by
            intro w hw
            have hj : w = ⟨(M - rem) + (w.val - (M - rem)), by omega⟩ := by
              ext; dsimp; omega
            rw [hj]
            exact hz ⟨w.val - (M - rem), by omega⟩
          have hout : ∀ j : Fin remMid, writeRegProg β rComb
              (p₁.evalBits (fun idx ↦ β (rComb idx))) (tailScr rComb remMid hmid j) = 0 := by
            intro j
            dsimp [tailScr]
            rw [writeRegProg_apply_reg]
            exact hpres _ hγ ⟨(M - remMid) + j.val, by omega⟩ (by dsimp; omega)
          simp only [hout, imp_true_iff, ↓reduceIte]
        · simp only [hz, ↓reduceIte, Matrix.mulVec_zero]
      have hseq := RealizesCleanUnitary_seq_asym hP₁ hP₂ ih₁ ih₂ hclean
      have heq : (p₂.onRegister rComb).toToffCircuit.eval *
          (p₁.onRegister rComb).toToffCircuit.eval =
          ((TempPhaseProg.seq p₁ p₂).onRegister rComb).toToffCircuit.eval := by
        simp [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      simpa [TempPhaseProg.onRegister, TempPhaseProg.toDyn, heq] using hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, rem, hrem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      have hrem1 : rem' + 1 ≤ M := by omega
      have hrem_le : rem' + 1 ≤ rem := by omega
      have ihBody := realizes_of_validCleanRem v rComb body rem' hrem' hvBody
      have hanc_eq : anc = ⟨M - (rem' + 1), by omega⟩ := by
        ext; dsimp [rem']; omega
      have hdisj : ∀ j : Fin rem', rComb anc ≠ tailScr rComb rem' hrem' j := by
        intro j h
        have hinj := congrArg Fin.val (rComb.wires.injective h)
        dsimp [tailScr, rem'] at hinj
        omega
      let U_body := ((body.onRegister rComb).toToffCircuit).eval
      let U_clean :=
        (((TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toToffCircuit).eval
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        rem' (tailScr rComb rem' hrem') hdisj
        ((body.onRegister rComb).toDyn v) U_body U_clean ihBody
        (by
          intro β hanc0 _
          simp only [U_clean, U_body, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
            eval_seq_mulVec, ket_TOFF, hanc0, zero_add])
        (by
          intro β hanc0 hscr0
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          have hγ_anc : γ anc = 0 := hanc0
          let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
          have hγ₁_clean : cleanRem M rem' β₁ := by
            intro w hw
            have hw_ne : w ≠ anc := wire_ne_of_gt (by dsimp [rem'] at hw; omega)
            dsimp only [β₁]
            rw [Function.update_of_ne hw_ne]
            have hj : w = ⟨(M - rem') + (w.val - (M - rem')), by omega⟩ := by
              ext; dsimp; omega
            rw [hj]
            exact hscr0 ⟨w.val - (M - rem'), by omega⟩
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hγ₁_clean
          have hfinal_anc :
              (TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).evalBits γ anc = 0 := by
            dsimp only [TempPhaseProg.evalBits]
            change Function.update (body.evalBits β₁) anc
              (body.evalBits β₁ anc + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, hγ_anc, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [show U_clean.1.mulVec (ket β) = _ from
              eval_onRegister_prog_ket rComb
                (TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) β,
            Matrix.mulVec_smul, ket_projector_zero]
          rw [writeRegProg_apply_reg, hfinal_anc]
          simp)
      have hscr_eq : projZeroAll (rem' + 1) (Fin.cons (rComb anc) (tailScr rComb rem' hrem'))
          = projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1) := by
        rw [hanc_eq, ← tailScr_succ rComb rem' hrem1]
      have hstep' : RealizesCleanUnitary v
          (projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1))
          (((TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toDyn v) U_clean :=
            by
        simpa [TempPhaseProg.onRegister, TempPhaseProg.toDyn, hscr_eq] using hstep
      exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (rem' + 1) _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hrem1 hrem hrem_le)
        hstep'
theorem PreservesStoreConst_toDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) : ∀ p : TempPhaseProg n, PreservesStoreConst (p.toDyn v)
  | .nil => PreservesStoreConst.circuit _
  | .cliff _ => PreservesStoreConst.circuit _
  | .z _ => PreservesStoreConst.circuit _
  | .seq p₁ p₂ =>
      PreservesStoreConst.seq (PreservesStoreConst_toDyn v p₁) (PreservesStoreConst_toDyn v p₂)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ body =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq (PreservesStoreConst_toDyn v body)
          (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂))
structure ScopedBlock (M rem : ℕ) (setup : BitAssignment M → BitAssignment M)
    (body : TempPhaseProg M) (p : TempPhaseProg M) : Prop where
  valid : ValidCleanRem M rem p
  bits : ∀ β : BitAssignment M, cleanRem M rem β → p.evalBits β = β
  sign : ∀ β : BitAssignment M, cleanRem M rem β → p.evalSign β = body.evalSign (setup β)
theorem ScopedBlock.trans {M rem₁ rem₂ : ℕ}
    {s₁ s₂ : BitAssignment M → BitAssignment M}
    {leaf mid outer : TempPhaseProg M}
    (hOuter : ScopedBlock M rem₁ s₁ mid outer)
    (hInner : ScopedBlock M rem₂ s₂ leaf mid)
    (hClean : ∀ β, cleanRem M rem₁ β → cleanRem M rem₂ (s₁ β)) :
    ScopedBlock M rem₁ (s₂ ∘ s₁) leaf outer where
  valid := hOuter.valid
  bits := hOuter.bits
  sign β hβ := by
    rw [hOuter.sign β hβ, hInner.sign (s₁ β) (hClean β hβ), Function.comp_apply]
def withCliffAlloc {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) : TempPhaseProg M :=
  .seq (.cliff c) (.seq body (.cliff c.inv))
@[simp]
theorem withCliffAlloc_countTempAnd {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) :
    (withCliffAlloc c body).countTempAnd = body.countTempAnd := by
  simp [withCliffAlloc, TempPhaseProg.countTempAnd]
theorem ScopedBlock.withCliffAlloc_block {M rem remIn : ℕ}
    (hremIn : remIn ≤ M) (hle : remIn ≤ rem)
    (c : CliffProg M) (hc : c.SupportsBelow (M - remIn))
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M remIn sBody leaf body) :
    ScopedBlock M rem (sBody ∘ c.eval) leaf (withCliffAlloc c body) where
  valid := by
    refine ⟨remIn, hremIn, trivial, ?_, fun β hβ w hw ↦ ?_⟩
    · refine ⟨0, Nat.zero_le M, hBody.valid, trivial, fun _ _ w hw ↦ absurd hw (by omega)⟩
    · rw [TempPhaseProg.evalBits, c.eval_outside hc β w hw]
      exact hβ w (by omega)
  bits β hβ := by
    have hc_clean : cleanRem M remIn (c.eval β) := fun w hw ↦ by
      rw [c.eval_outside hc β w hw]
      exact hβ w (by omega)
    simp only [withCliffAlloc, TempPhaseProg.evalBits, hBody.bits (c.eval β) hc_clean, c.inv_eval]
  sign β hβ := by
    have hc_clean : cleanRem M remIn (c.eval β) := fun w hw ↦ by
      rw [c.eval_outside hc β w hw]
      exact hβ w (by omega)
    simp [withCliffAlloc, TempPhaseProg.evalSign, TempPhaseProg.evalBits,
      hBody.sign (c.eval β) hc_clean, Function.comp_apply]
def withTempBit {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : TempPhaseProg M) : TempPhaseProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body
@[simp] theorem withTempBit_countTempAnd {M : ℕ} (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : TempPhaseProg M) :
    (withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body).countTempAnd = 1 + body.countTempAnd := rfl
theorem ScopedBlock.withTempBit_block {M : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < pos) (hc₂ : c₂.val < pos)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (pos + 1)) sBody leaf body) : ScopedBlock M (M - pos)
    (fun β ↦ sBody (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂))) leaf (withTempBit c₁ c₂
    ⟨pos, hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) body) := by
  have h1a : c₁ ≠ ⟨pos, hpos⟩ := wire_ne_of_lt hc₁
  have h2a : c₂ ≠ ⟨pos, hpos⟩ := wire_ne_of_lt hc₂
  have hcl (β : BitAssignment M) (hβ : cleanRem M (M - pos) β) :
      cleanRem M (M - (pos + 1)) (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)) := fun w hw ↦ by
    rw [Function.update_of_ne (wire_ne_of_gt (by
      dsimp
      omega))]
    exact hβ w (by omega)
  refine ⟨⟨by
      dsimp
      omega, hBody.valid, fun β₁ hβ₁ ↦ by
      rw [hBody.bits β₁ hβ₁]
      exact ⟨rfl, rfl, rfl⟩⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · have hanc0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (by
      dsimp
      omega)
    simp only [withTempBit, TempPhaseProg.evalBits, hanc0, zero_add, hBody.bits _ (hcl β hβ)]
    funext w
    by_cases hw : w = ⟨pos, hpos⟩
    · subst hw
      simp [Function.update_self, Function.update_of_ne h1a, Function.update_of_ne h2a,
        CharTwo.add_self_eq_zero, hanc0]
    · simp [Function.update_of_ne hw]
  · have hanc0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (by
      dsimp
      omega)
    simp only [withTempBit, TempPhaseProg.evalSign, hanc0, zero_add]
    exact hBody.sign _ (hcl β hβ)
def withInPlaceFullAdd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b c : Wire M) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < cur) (hb : b.val < cur) (hc : c.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let coutWire : Wire M := ⟨cur, hcur⟩
  let cPre : CliffProg M := .seq (.cnot a b hab) (.cnot a c hac)
  let cInner : CliffProg M :=
    .seq (.cnot a coutWire (wire_ne_of_lt (by dsimp [coutWire]; omega)))
      (.seq (.cnot a c hac) (.cnot c b hbc.symm))
  withCliffAlloc cPre
    (withTempBit b c coutWire hbc
      (wire_ne_of_lt (by dsimp [coutWire]; omega))
      (wire_ne_of_lt (by dsimp [coutWire]; omega))
      (withCliffAlloc cInner body))
@[simp] theorem withInPlaceFullAdd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b c : Wire M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < cur)
    (hb : b.val < cur) (hc : c.val < cur) (body : TempPhaseProg M) : (withInPlaceFullAdd cur
    hcur a b c hab hac hbc ha hb hc body).countTempAnd = 1 + body.countTempAnd := by
  simp [withInPlaceFullAdd]
def inPlaceFullAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b c : Wire M)
    (β : BitAssignment M) : BitAssignment M := Function.update
    (Function.update β b (β a + β b + β c)) ⟨cur, hcur⟩ ((β b + β a) * (β c + β a) + β a)
theorem inPlaceFullAdd_val_eq (x y z : ZMod 2) :
    (x + y + z).val + 2 * ((y + x) * (z + x) + x).val = x.val + y.val + z.val := by
  revert x y z; decide
theorem fullAdd_temp_eq_inPlaceFullAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b c : Wire M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a.val < cur) (hb : b.val < cur) (hc : c.val < cur) (β : BitAssignment M) :
    let cPre : CliffProg M := .seq (.cnot a b hab) (.cnot a c hac)
    let cInner : CliffProg M :=
      .seq (.cnot a ⟨cur, hcur⟩ (wire_ne_of_lt ha))
        (.seq (.cnot a c hac) (.cnot c b hbc.symm))
    cInner.eval (Function.update (cPre.eval β) ⟨cur, hcur⟩
      ((cPre.eval β) b * (cPre.eval β) c)) = inPlaceFullAddSetup cur hcur a b c β := by
  have hacout : a ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt ha
  have hbcout : b ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt hb
  have hccout : c ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt hc
  dsimp only [CliffProg.eval, inPlaceFullAddSetup]
  funext w
  by_cases hw_co : w = (⟨cur, hcur⟩ : Wire M)
  · subst hw_co
    simp only [Function.update_self, Function.update_of_ne hbcout.symm,
      Function.update_of_ne hccout.symm, Function.update_of_ne hacout,
      Function.update_of_ne hbc, Function.update_of_ne hac,
      Function.update_of_ne hab, Function.update_of_ne hbc.symm]
  · by_cases hw_b : w = b
    · subst hw_b
      simp only [Function.update_self, Function.update_of_ne hw_co,
        Function.update_of_ne hbc, Function.update_of_ne hbc.symm,
        Function.update_of_ne hccout,
        Function.update_of_ne hacout, Function.update_of_ne hac, Function.update_of_ne hab,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
      ring
    · by_cases hw_c : w = c
      · subst hw_c
        simp only [Function.update_self, Function.update_of_ne hw_co,
          Function.update_of_ne hw_b,
          Function.update_of_ne hacout, Function.update_of_ne hac, Function.update_of_ne hab,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · simp only [Function.update_of_ne hw_co, Function.update_of_ne hw_b,
          Function.update_of_ne hw_c]
theorem ScopedBlock.withInPlaceFullAdd_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b c : Wire M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < cur)
    (hb : b.val < cur) (hc : c.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ inPlaceFullAddSetup cur hcur a b c) leaf
    (withInPlaceFullAdd cur hcur a b c hab hac hbc ha hb hc body) := by
  let remIn := M - (cur + 1)
  let cPre : CliffProg M := .seq (.cnot a b hab) (.cnot a c hac)
  let cInner : CliffProg M :=
    .seq (.cnot a ⟨cur, hcur⟩ (wire_ne_of_lt ha))
      (.seq (.cnot a c hac) (.cnot c b hbc.symm))
  have hri : remIn ≤ M := by omega
  have h1 := ScopedBlock.withCliffAlloc_block hri le_rfl cInner
    ⟨⟨by omega, by
      dsimp [remIn]
      omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur b c hbc hb hc h1
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl cPre ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withInPlaceFullAdd]
  rw [h3.sign β hβ]
  exact congrArg (leaf.evalSign ∘ sBody)
    (fullAdd_temp_eq_inPlaceFullAddSetup cur hcur a b c hab hac hbc ha hb hc β)
end InPlaceFullAddSlice
end
end ModInPlaceFullAddSlice

section ModInPlaceStepEngine
@[expose] public section
namespace InPlaceStepEngine
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open InPlaceFullAddSlice
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
def withInPlaceHalfAdd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (body : TempPhaseProg M) : TempPhaseProg M :=
  let coutWire : Wire M := ⟨cur, hcur⟩
  withTempBit a b coutWire hab
    (wire_ne_of_lt ha) (wire_ne_of_lt hb)
    (withCliffAlloc (.cnot a b hab) body)
@[simp] theorem withInPlaceHalfAdd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) :
    (withInPlaceHalfAdd cur hcur a b hab ha hb body).countTempAnd = 1 + body.countTempAnd := by
  simp [withInPlaceHalfAdd]
def inPlaceHalfAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M)
    (β : BitAssignment M) : BitAssignment M := Function.update
    (Function.update β b (β a + β b)) ⟨cur, hcur⟩ (β a * β b)
theorem cnot_temp_eq_inPlaceHalfAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M)
    (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur) (β : BitAssignment M) :
    (CliffProg.cnot a b hab).eval (Function.update β ⟨cur, hcur⟩ (β a * β b)) =
    inPlaceHalfAddSetup cur hcur a b β := by
  have hacout : a ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt ha
  have hbcout : b ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt hb
  dsimp only [CliffProg.eval, inPlaceHalfAddSetup]
  funext w
  by_cases hw_co : w = (⟨cur, hcur⟩ : Wire M)
  · subst hw_co
    rw [Function.update_of_ne hbcout.symm, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hw_co]
    by_cases hw_b : w = b
    · subst hw_b
      rw [Function.update_self, Function.update_of_ne hbcout, Function.update_of_ne hacout,
        Function.update_self]
      ring
    · rw [Function.update_of_ne hw_b, Function.update_of_ne hw_co, Function.update_of_ne hw_b]
theorem ScopedBlock.withInPlaceHalfAdd_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ inPlaceHalfAddSetup cur hcur a b) leaf
      (withInPlaceHalfAdd cur hcur a b hab ha hb body) := by
  let remIn := M - (cur + 1)
  have h1 : ScopedBlock M remIn (sBody ∘ (CliffProg.cnot a b hab).eval) leaf
      (withCliffAlloc (.cnot a b hab) body) :=
    ScopedBlock.withCliffAlloc_block (by dsimp [remIn]; omega) le_rfl (.cnot a b hab)
      ⟨by dsimp [remIn]; omega, by dsimp [remIn]; omega⟩ hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur a b hab ha hb h1
  refine ⟨h2.valid, h2.bits, fun β hβ ↦ ?_⟩
  dsimp only [withInPlaceHalfAdd]
  rw [h2.sign β hβ]
  dsimp only [Function.comp_apply]
  rw [cnot_temp_eq_inPlaceHalfAddSetup cur hcur a b hab ha hb β]
structure TargetBlock (M targetEnd rem : ℕ)
    (fTarget : BitAssignment M → BitAssignment M)
    (sTarget : BitAssignment M → ZMod 2)
    (p : TempPhaseProg M) : Prop where
  valid : ValidCleanRem M rem p
  bits : ∀ β : BitAssignment M, cleanRem M rem β → ∀ w : Wire M,
    p.evalBits β w = if w.val < targetEnd then fTarget β w else β w
  sign : ∀ β : BitAssignment M, cleanRem M rem β → p.evalSign β = sTarget β
def cliffInRange {M : ℕ} (lo hi : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x w => lo ≤ w.val ∧ w.val < hi
  | .cnot c t _ => (lo ≤ c.val ∧ c.val < hi) ∧ (lo ≤ t.val ∧ t.val < hi)
  | .seq p₁ p₂ => cliffInRange lo hi p₁ ∧ cliffInRange lo hi p₂
theorem cliffInRange_eval_out {M lo hi : ℕ} {c : CliffProg M} (hc : cliffInRange lo hi c)
    (β : BitAssignment M) (w : Wire M) (hw : w.val < lo ∨ hi ≤ w.val) : c.eval β w = β w := by
  induction c generalizing β with
  | nil => rfl
  | x u =>
      have hne : w ≠ u := fun h ↦ by
        subst h
        rcases hw with hw | hw <;>
          [exact absurd hc.1 (not_le_of_gt hw); exact absurd hc.2 (not_lt_of_ge hw)]
      simp [CliffProg.eval, Function.update_of_ne hne]
  | cnot u v huv =>
      have hne : w ≠ v := fun h ↦ by
        subst h
        rcases hw with hw | hw <;>
          [exact absurd hc.2.1 (not_le_of_gt hw); exact absurd hc.2.2 (not_lt_of_ge hw)]
      simp [CliffProg.eval, Function.update_of_ne hne]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [CliffProg.eval]
      rw [ih₂ hc.2 (p₁.eval β), ih₁ hc.1 β]
theorem cliffInRange_eval_congr {M lo hi : ℕ} {c : CliffProg M} (hc : cliffInRange lo hi c)
    {β₁ β₂ : BitAssignment M} (hEq : ∀ w : Wire M, lo ≤ w.val → w.val < hi → β₁ w = β₂ w) :
    ∀ w : Wire M, lo ≤ w.val → w.val < hi → c.eval β₁ w = c.eval β₂ w := by
  induction c generalizing β₁ β₂ with
  | nil => exact fun w hlo hhi ↦ hEq w hlo hhi
  | x u =>
      intro w hlo hhi
      by_cases hw : w = u
      · subst u; simp [CliffProg.eval, hEq w hc.1 hc.2]
      · simp [CliffProg.eval, Function.update_of_ne hw, hEq w hlo hhi]
  | cnot u v huv =>
      intro w hlo hhi
      by_cases hw : w = v
      · subst v
        simp [CliffProg.eval, hEq w hc.2.1 hc.2.2, hEq u hc.1.1 hc.1.2]
      · simp [CliffProg.eval, Function.update_of_ne hw, hEq w hlo hhi]
  | seq p₁ p₂ ih₁ ih₂ =>
      intro w hlo hhi
      exact ih₂ hc.2 (ih₁ hc.1 hEq) w hlo hhi
theorem cliffInRange_inv {M lo hi : ℕ} {c : CliffProg M} (hc : cliffInRange lo hi c) :
    cliffInRange lo hi c.inv := by
  induction c with
  | nil => trivial
  | x _ => exact hc
  | cnot _ _ _ => exact hc
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hc.2, ih₁ hc.1⟩
theorem cliff_inv_eval_cancel {M : ℕ} (c : CliffProg M) (β : BitAssignment M) :
    c.inv.eval (c.eval β) = β :=
  c.inv_eval β
theorem TargetBlock.withCliffAlloc_block {M targetEnd rem remIn : ℕ} (hremIn : remIn ≤ M)
    (hle : remIn ≤ rem) (htarget : targetEnd ≤ M - remIn) (c : CliffProg M)
    (hc : cliffInRange targetEnd (M - remIn) c) {fBody : BitAssignment M → BitAssignment M}
    {sBody : BitAssignment M → ZMod 2} {body : TempPhaseProg M}
    (hBody : TargetBlock M targetEnd remIn fBody sBody body) : TargetBlock M targetEnd rem
    (fun β ↦ fBody (c.eval β)) (fun β ↦ sBody (c.eval β)) (withCliffAlloc c body) := by
  have hcinv := cliffInRange_inv hc
  have hCleanFwd : ∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remIn (c.eval β) := by
    intro β hβ w hw
    rw [cliffInRange_eval_out hc β w (Or.inr hw)]
    exact hβ w (by omega)
  refine ⟨⟨remIn, hremIn, trivial, ⟨remIn, hremIn, hBody.valid, trivial, ?_⟩, hCleanFwd⟩, ?_, ?_⟩
  · intro β₁ hβ₁ w hw
    rw [hBody.bits β₁ hβ₁ w]
    split_ifs with hlt
    · omega
    · exact hβ₁ w hw
  · intro β hβ w
    have hclean₁ : cleanRem M remIn (c.eval β) := hCleanFwd β hβ
    dsimp only [withCliffAlloc, TempPhaseProg.evalBits]
    by_cases hlt : w.val < targetEnd
    · rw [cliffInRange_eval_out hcinv _ w (Or.inl hlt), hBody.bits (c.eval β) hclean₁ w]
      simp only [hlt, ↓reduceIte]
    · simp only [hlt, ↓reduceIte]
      by_cases hhi : M - remIn ≤ w.val
      · rw [cliffInRange_eval_out hcinv _ w (Or.inr hhi), hBody.bits (c.eval β) hclean₁ w]
        simp only [hlt, ↓reduceIte]
        exact cliffInRange_eval_out hc β w (Or.inr hhi)
      · have hcongr := cliffInRange_eval_congr hcinv
          (β₁ := body.evalBits (c.eval β)) (β₂ := c.eval β)
          (fun u hlo _ ↦ by
            have hu : ¬(u.val < targetEnd) := by omega
            rw [hBody.bits (c.eval β) hclean₁ u]
            simp only [hu, ↓reduceIte])
          w (by omega) (by omega)
        rw [hcongr, cliff_inv_eval_cancel]
  · intro β hβ
    simp only [withCliffAlloc, TempPhaseProg.evalSign, zero_add, add_zero]
    exact hBody.sign (c.eval β) (hCleanFwd β hβ)
theorem TargetBlock.withTempBit_block {M targetEnd : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M)
    (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂) (hc₁_lo : targetEnd ≤ c₁.val)
    (hc₂_lo : targetEnd ≤ c₂.val) (hc₁ : c₁.val < pos) (hc₂ : c₂.val < pos)
    {fBody : BitAssignment M → BitAssignment M} {sBody : BitAssignment M → ZMod 2}
    {body : TempPhaseProg M}
    (hBody : TargetBlock M targetEnd (M - (pos + 1)) fBody sBody body) : TargetBlock M
    targetEnd (M - pos) (fun β ↦ fBody (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)))
    (fun β ↦ sBody (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂))) (withTempBit c₁ c₂ ⟨pos,
    hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) body) := by
  have h1a : c₁ ≠ (⟨pos, hpos⟩ : Wire M) := wire_ne_of_lt hc₁
  have h2a : c₂ ≠ (⟨pos, hpos⟩ : Wire M) := wire_ne_of_lt hc₂
  have hpv : (⟨pos, hpos⟩ : Wire M).val = pos := rfl
  have hfix (β₁ : BitAssignment M) (hβ₁ : cleanRem M (M - (pos + 1)) β₁) (u : Wire M)
      (hu : ¬(u.val < targetEnd)) : body.evalBits β₁ u = β₁ u := by
    rw [hBody.bits β₁ hβ₁ u, ite_eq_right hu]
  have hcl (β : BitAssignment M) (hβ : cleanRem M (M - pos) β) :
      cleanRem M (M - (pos + 1)) (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)) := fun u hu ↦ by
    rw [Function.update_of_ne (wire_ne_of_gt (by omega))]
    exact hβ u (by omega)
  refine ⟨⟨by omega, hBody.valid, fun β₁ hβ₁ ↦ ⟨hfix β₁ hβ₁ c₁ (by omega),
    hfix β₁ hβ₁ c₂ (by omega), hfix β₁ hβ₁ ⟨pos, hpos⟩ (by omega)⟩⟩,
    fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
  · have hanc0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (by omega)
    dsimp only [withTempBit, TempPhaseProg.evalBits]
    rw [hanc0, zero_add]
    by_cases hw : w = (⟨pos, hpos⟩ : Wire M)
    · subst hw
      rw [Function.update_self, hfix _ (hcl β hβ) ⟨pos, hpos⟩ (by omega),
        hfix _ (hcl β hβ) c₁ (by omega), hfix _ (hcl β hβ) c₂ (by omega)]
      simp [show ¬(pos < targetEnd) by omega, Function.update_self, Function.update_of_ne h1a,
        Function.update_of_ne h2a, CharTwo.add_self_eq_zero, hanc0]
    · rw [Function.update_of_ne hw, hBody.bits _ (hcl β hβ) w]
      split_ifs
      · rfl
      · exact Function.update_of_ne hw _ _
  · have hanc0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (by omega)
    simp only [withTempBit, TempPhaseProg.evalSign, hanc0, zero_add]
    exact hBody.sign _ (hcl β hβ)
theorem TargetBlock.withInPlaceFullAdd_block {M targetEnd : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b c : Wire M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha_lo : targetEnd ≤ a.val)
    (hb_lo : targetEnd ≤ b.val) (hc_lo : targetEnd ≤ c.val) (ha : a.val < cur)
    (hb : b.val < cur) (hc : c.val < cur) {fBody : BitAssignment M → BitAssignment M}
    {sBody : BitAssignment M → ZMod 2} {body : TempPhaseProg M}
    (hBody : TargetBlock M targetEnd (M - (cur + 1)) fBody sBody body) : TargetBlock M
    targetEnd (M - cur) (fun β ↦ fBody (inPlaceFullAddSetup cur hcur a b c β))
    (fun β ↦ sBody (inPlaceFullAddSetup cur hcur a b c β))
    (withInPlaceFullAdd cur hcur a b c hab hac hbc ha hb hc body) := by
  let remIn := M - (cur + 1)
  have hcv : (⟨cur, hcur⟩ : Wire M).val = cur := rfl
  let cPre : CliffProg M := .seq (.cnot a b hab) (.cnot a c hac)
  let cInner : CliffProg M :=
    .seq (.cnot a ⟨cur, hcur⟩ (wire_ne_of_lt ha))
      (.seq (.cnot a c hac) (.cnot c b hbc.symm))
  have h1 := TargetBlock.withCliffAlloc_block (M := M) (targetEnd := targetEnd)
    (rem := remIn) (remIn := remIn) (by omega) le_rfl (by omega) cInner
    ⟨⟨⟨ha_lo, by omega⟩, ⟨by omega, by omega⟩⟩,
      ⟨⟨ha_lo, by omega⟩, ⟨hc_lo, by omega⟩⟩,
      ⟨⟨hc_lo, by omega⟩, ⟨hb_lo, by omega⟩⟩⟩ hBody
  have h2 := TargetBlock.withTempBit_block (M := M) (targetEnd := targetEnd)
    cur hcur b c hbc hb_lo hc_lo hb hc h1
  have h3 := TargetBlock.withCliffAlloc_block (M := M) (targetEnd := targetEnd)
    (rem := M - cur) (remIn := M - cur) (by omega) le_rfl (by omega) cPre
    ⟨⟨⟨ha_lo, by omega⟩, ⟨hb_lo, by omega⟩⟩, ⟨⟨ha_lo, by omega⟩, ⟨hc_lo, by omega⟩⟩⟩ h2
  have hEq := fullAdd_temp_eq_inPlaceFullAddSetup cur hcur a b c hab hac hbc ha hb hc
  refine ⟨h3.valid, fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
  · dsimp only [withInPlaceFullAdd]
    rw [h3.bits β hβ w, hEq β]
  · dsimp only [withInPlaceFullAdd]
    rw [h3.sign β hβ, hEq β]
theorem TargetBlock.withInPlaceHalfAdd_block {M targetEnd : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha_lo : targetEnd ≤ a.val) (hb_lo : targetEnd ≤ b.val)
    (ha : a.val < cur) (hb : b.val < cur) {fBody : BitAssignment M → BitAssignment M}
    {sBody : BitAssignment M → ZMod 2} {body : TempPhaseProg M}
    (hBody : TargetBlock M targetEnd (M - (cur + 1)) fBody sBody body) : TargetBlock M
    targetEnd (M - cur) (fun β ↦ fBody (inPlaceHalfAddSetup cur hcur a b β))
    (fun β ↦ sBody (inPlaceHalfAddSetup cur hcur a b β))
    (withInPlaceHalfAdd cur hcur a b hab ha hb body) := by
  let remIn := M - (cur + 1)
  have h1 := TargetBlock.withCliffAlloc_block (M := M) (targetEnd := targetEnd)
    (rem := remIn) (remIn := remIn) (by dsimp [remIn]; omega) le_rfl (by dsimp [remIn]; omega)
    (.cnot a b hab) ⟨⟨ha_lo, by dsimp [remIn]; omega⟩,⟨hb_lo, by dsimp [remIn]; omega⟩⟩ hBody
  have h2 := TargetBlock.withTempBit_block (M := M) (targetEnd := targetEnd)
    cur hcur a b hab ha_lo hb_lo ha hb h1
  refine ⟨h2.valid, fun β hβ w ↦ ?_, fun β hβ ↦ ?_⟩
  · dsimp only [withInPlaceHalfAdd]
    rw [h2.bits β hβ w, cnot_temp_eq_inPlaceHalfAddSetup cur hcur a b hab ha hb β]
  · dsimp only [withInPlaceHalfAdd]
    rw [h2.sign β hβ, cnot_temp_eq_inPlaceHalfAddSetup cur hcur a b hab ha hb β]
def listGet : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => listGet xs i
def listSet : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: listSet xs i v
theorem listSet_length : ∀ (L : List ℕ) (i v : ℕ),(listSet L i v).length = L.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, v => congrArg Nat.succ (listSet_length xs i v)
theorem listGet_listSet : ∀ (L : List ℕ) (i j v : ℕ), i < L.length →
    listGet (listSet L i v) j = if j = i then v else listGet L j
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0,0, _, _ => rfl
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1,0, _, _ => rfl
  | _ :: xs, i + 1, j + 1, v, h => by
      have ih := listGet_listSet xs i j v (Nat.lt_of_succ_lt_succ h)
      simpa [listSet, listGet] using ih
inductive InPlaceStep where
  | fa (a b c : ℕ)
  | ha (a b : ℕ)
  deriving DecidableEq, Repr
def InPlaceStep.validAt (cur : ℕ) : InPlaceStep → Bool
  | .fa a b c =>
      decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c) &&
        decide (a < cur) && decide (b < cur) && decide (c < cur)
  | .ha a b =>
      decide (a ≠ b) && decide (a < cur) && decide (b < cur)
theorem InPlaceStep.validAt_fa_iff {cur a b c : ℕ} : InPlaceStep.validAt cur (.fa a b c) =
    true ↔ (((a ≠ b ∧ a ≠ c) ∧ b ≠ c) ∧ a < cur ∧ b < cur) ∧ c < cur := by
  simp only [InPlaceStep.validAt, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
theorem InPlaceStep.validAt_ha_iff {cur a b : ℕ} : InPlaceStep.validAt cur (.ha a b) = true ↔
    (a ≠ b ∧ a < cur) ∧ b < cur := by
  simp only [InPlaceStep.validAt, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
def InPlaceStep.above (targetEnd : ℕ) : InPlaceStep → Bool
  | .fa a b c => decide (targetEnd ≤ a) && decide (targetEnd ≤ b) && decide (targetEnd ≤ c)
  | .ha a b => decide (targetEnd ≤ a) && decide (targetEnd ≤ b)
def validInPlaceSteps : ℕ → List InPlaceStep → Bool
  | _, [] => true
  | cur, s :: rest => s.validAt cur && validInPlaceSteps (cur + 1) rest
def stepsAbove (targetEnd : ℕ) : List InPlaceStep → Bool
  | [] => true
  | s :: rest => s.above targetEnd && stepsAbove targetEnd rest
def withInPlaceSteps {M : ℕ} (cur : ℕ) (steps : List InPlaceStep)
    (hbound : cur + steps.length ≤ M) (hvalid : validInPlaceSteps cur steps = true)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  match steps with
  | [] => body
  | .fa a b c :: rest =>
      have hv : InPlaceStep.validAt cur (.fa a b c) = true ∧
          validInPlaceSteps (cur + 1) rest = true := by
        simpa [validInPlaceSteps] using hvalid
      have hv' := InPlaceStep.validAt_fa_iff.mp hv.1
      have hcur1 : cur + 1 ≤ M := by simp at hbound; omega
      withInPlaceFullAdd cur hcur1 ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
        (fun h ↦ hv'.1.1.1.1 (congrArg Fin.val h))
        (fun h ↦ hv'.1.1.1.2 (congrArg Fin.val h))
        (fun h ↦ hv'.1.1.2 (congrArg Fin.val h))
        hv'.1.2.1 hv'.1.2.2 hv'.2
        (withInPlaceSteps (cur + 1) rest (by simp at hbound; omega) hv.2 body)
  | .ha a b :: rest =>
      have hv : InPlaceStep.validAt cur (.ha a b) = true ∧
          validInPlaceSteps (cur + 1) rest = true := by
        simpa [validInPlaceSteps] using hvalid
      have hv' := InPlaceStep.validAt_ha_iff.mp hv.1
      have hcur1 : cur + 1 ≤ M := by simp at hbound; omega
      withInPlaceHalfAdd cur hcur1 ⟨a, by omega⟩ ⟨b, by omega⟩
        (fun h ↦ hv'.1.1 (congrArg Fin.val h))
        hv'.1.2 hv'.2
        (withInPlaceSteps (cur + 1) rest (by simp at hbound; omega) hv.2 body)
@[simp] theorem withInPlaceSteps_countTempAnd {M : ℕ} (cur : ℕ) (steps : List InPlaceStep)
    (hbound : cur + steps.length ≤ M) (hvalid : validInPlaceSteps cur steps = true)
    (body : TempPhaseProg M) : (withInPlaceSteps cur steps hbound hvalid body).countTempAnd =
    steps.length + body.countTempAnd := by
  induction steps generalizing cur with
  | nil => simp [withInPlaceSteps]
  | cons s rest ih =>
      cases s <;> (simp [withInPlaceSteps, ih]; omega)
def InPlaceStep.evalOne {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (s : InPlaceStep) (hvalid : s.validAt cur = true) (β : BitAssignment M) : BitAssignment M :=
  match s with
  | .fa a b c =>
      have hv' := InPlaceStep.validAt_fa_iff.mp hvalid
      inPlaceFullAddSetup cur hcur ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ β
  | .ha a b =>
      have hv' := InPlaceStep.validAt_ha_iff.mp hvalid
      inPlaceHalfAddSetup cur hcur ⟨a, by omega⟩ ⟨b, by omega⟩ β
def evalInPlaceSteps {M : ℕ} (cur : ℕ) (steps : List InPlaceStep)
    (hbound : cur + steps.length ≤ M) (hvalid : validInPlaceSteps cur steps = true)
    (β : BitAssignment M) : BitAssignment M :=
  match steps with
  | [] => β
  | s :: rest =>
      have hv : s.validAt cur = true ∧ validInPlaceSteps (cur + 1) rest = true := by
        simpa [validInPlaceSteps] using hvalid
      have hcur1 : cur + 1 ≤ M := by simp at hbound; omega
      evalInPlaceSteps (cur + 1) rest (by simp at hbound; omega) hv.2
        (s.evalOne cur hcur1 hv.1 β)
theorem ScopedBlock.withInPlaceSteps_block {M : ℕ} (cur : ℕ) (steps : List InPlaceStep)
    (hbound : cur + steps.length ≤ M) (hvalid : validInPlaceSteps cur steps = true)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + steps.length)) sBody leaf body) :
    ScopedBlock M (M - cur) (fun β ↦ sBody (evalInPlaceSteps cur steps hbound hvalid β)) leaf
      (withInPlaceSteps cur steps hbound hvalid body) := by
  induction steps generalizing cur with
  | nil =>
      simpa [withInPlaceSteps, evalInPlaceSteps] using hBody
  | cons s rest ih =>
      cases s with
      | fa a b c =>
          have hv : InPlaceStep.validAt cur (.fa a b c) = true ∧
              validInPlaceSteps (cur + 1) rest = true := by
            simpa [validInPlaceSteps] using hvalid
          have hv' := InPlaceStep.validAt_fa_iff.mp hv.1
          have hBody' : ScopedBlock M (M - ((cur + 1) + rest.length)) sBody leaf body := by
            simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hBody
          have hRest := ih (cur + 1) (by simp at hbound; omega) hv.2 hBody'
          exact ScopedBlock.withInPlaceFullAdd_block cur (by simp at hbound; omega)
            _ _ _ _ _ _ hv'.1.2.1 hv'.1.2.2 hv'.2 hRest
      | ha a b =>
          have hv : InPlaceStep.validAt cur (.ha a b) = true ∧
              validInPlaceSteps (cur + 1) rest = true := by
            simpa [validInPlaceSteps] using hvalid
          have hv' := InPlaceStep.validAt_ha_iff.mp hv.1
          have hBody' : ScopedBlock M (M - ((cur + 1) + rest.length)) sBody leaf body := by
            simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hBody
          have hRest := ih (cur + 1) (by simp at hbound; omega) hv.2 hBody'
          exact ScopedBlock.withInPlaceHalfAdd_block cur (by simp at hbound; omega)
            _ _ _ hv'.1.2 hv'.2 hRest
theorem TargetBlock.withInPlaceSteps_block {M targetEnd : ℕ} (cur : ℕ)
    (steps : List InPlaceStep) (hbound : cur + steps.length ≤ M)
    (hvalid : validInPlaceSteps cur steps = true) (habove : stepsAbove targetEnd steps = true)
    {fBody : BitAssignment M → BitAssignment M} {sBody : BitAssignment M → ZMod 2}
    {body : TempPhaseProg M} (hBody : TargetBlock M targetEnd (M - (cur + steps.length)) fBody
    sBody body) : TargetBlock M targetEnd (M - cur)
    (fun β ↦ fBody (evalInPlaceSteps cur steps hbound hvalid β))
    (fun β ↦ sBody (evalInPlaceSteps cur steps hbound hvalid β))
    (withInPlaceSteps cur steps hbound hvalid body) := by
  induction steps generalizing cur with
  | nil =>
      simpa [withInPlaceSteps, evalInPlaceSteps] using hBody
  | cons s rest ih =>
      have hab : s.above targetEnd = true ∧ stepsAbove targetEnd rest = true := by
        simpa [stepsAbove] using habove
      cases s with
      | fa a b c =>
          have hv : InPlaceStep.validAt cur (.fa a b c) = true ∧
              validInPlaceSteps (cur + 1) rest = true := by
            simpa [validInPlaceSteps] using hvalid
          have hv' := InPlaceStep.validAt_fa_iff.mp hv.1
          have hlo : (targetEnd ≤ a ∧ targetEnd ≤ b) ∧ targetEnd ≤ c := by
            simpa [InPlaceStep.above, Bool.and_eq_true, decide_eq_true_eq] using hab.1
          have hBody' : TargetBlock M targetEnd (M - ((cur + 1) + rest.length)) fBody sBody body :=
            by
            simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hBody
          have hRest := ih (cur + 1) (by simp at hbound; omega) hv.2 hab.2 hBody'
          exact TargetBlock.withInPlaceFullAdd_block cur (by simp at hbound; omega)
            _ _ _ _ _ _ hlo.1.1 hlo.1.2 hlo.2 hv'.1.2.1 hv'.1.2.2 hv'.2 hRest
      | ha a b =>
          have hv : InPlaceStep.validAt cur (.ha a b) = true ∧
              validInPlaceSteps (cur + 1) rest = true := by
            simpa [validInPlaceSteps] using hvalid
          have hv' := InPlaceStep.validAt_ha_iff.mp hv.1
          have hlo : targetEnd ≤ a ∧ targetEnd ≤ b := by
            simpa [InPlaceStep.above, Bool.and_eq_true, decide_eq_true_eq] using hab.1
          have hBody' : TargetBlock M targetEnd (M - ((cur + 1) + rest.length)) fBody sBody body :=
            by
            simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hBody
          have hRest := ih (cur + 1) (by simp at hbound; omega) hv.2 hab.2 hBody'
          exact TargetBlock.withInPlaceHalfAdd_block cur (by simp at hbound; omega)
            _ _ _ hlo.1 hlo.2 hv'.1.2 hv'.2 hRest
def wSum {M : ℕ} (L : List ℕ) (β : BitAssignment M) : ℕ :=
  ∑ q : Wire M, listGet L q.val * (β q).val
def stepWeightList (cur : ℕ) (L : List ℕ) : InPlaceStep → Option (List ℕ)
  | .fa a b c =>
      let wa := listGet L a
      if listGet L cur == 0 && wa > 0 && listGet L b == wa && listGet L c == wa then
        some (listSet (listSet (listSet (listSet L a 0) c 0) b wa) cur (2 * wa))
      else none
  | .ha a b =>
      let wa := listGet L a
      if listGet L cur == 0 && wa > 0 && listGet L b == wa then
        some (listSet (listSet (listSet L a 0) b wa) cur (2 * wa))
      else none
def strictNat : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      match strictNat n with
      | 0 => 1
      | k + 1 => k + 2
theorem strictNat_eq : ∀ n : ℕ, strictNat n = n
  | 0 => rfl
  | n + 1 => by
      dsimp [strictNat]
      rw [strictNat_eq n]
      cases n <;> rfl
def forceList : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
      match strictNat x, forceList xs with
      | 0, [] => 0 :: []
      | 0, y :: ys => 0 :: y :: ys
      | k + 1, [] => (k + 1) :: []
      | k + 1, y :: ys => (k + 1) :: y :: ys
theorem forceList_eq : ∀ L : List ℕ, forceList L = L
  | [] => rfl
  | x :: xs => by
      dsimp [forceList]
      rw [strictNat_eq x, forceList_eq xs]
      cases x <;> cases xs <;> rfl
theorem match_forceList_apply {α : Type*} (f : List ℕ → α) (L' : List ℕ) :
    (match forceList L' with | [] => f [] | h :: t => f (h :: t)) = f L' := by
  rw [forceList_eq L']
  cases L' <;> rfl
theorem match_forceList_id (L' : List ℕ) :
    (match forceList L' with | [] => [] | h :: t => h :: t) = L' :=
  match_forceList_apply id L'
def runWeightList : ℕ → List InPlaceStep → List ℕ → Option (List ℕ)
  | _, [], L => some L
  | cur, s :: rest, L =>
      match stepWeightList cur L s with
      | none => none
      | some L' =>
          match forceList L' with
          | [] => runWeightList (cur + 1) rest []
          | h :: t => runWeightList (cur + 1) rest (h :: t)
theorem sum_four_distinct {α : Type*} [Fintype α] (f g : α → ℕ) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h4 : f a + f b + f c + f d = g a + g b + g c + g d)
    (hrest : ∀ q : α, q ≠ a → q ≠ b → q ≠ c → q ≠ d → f q = g q) : (∑ q : α, f q) = ∑ q : α, g
    q := by
  classical
  let S : Finset α := {a, b, c, d}
  have hS (h : α → ℕ) : (∑ q ∈ S, h q) = h a + h b + h c + h d := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, hab, hac, had, hbc, hbd, hcd,
      or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
    omega
  have hF : (∑ q ∈ Sᶜ, f q) = ∑ q ∈ Sᶜ, g q := by
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    simp only [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    exact hrest q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
  rw [← Finset.sum_add_sum_compl S f, ← Finset.sum_add_sum_compl S g, hS f, hS g, h4, hF]
theorem sum_three_distinct {α : Type*} [Fintype α] (f g : α → ℕ) (a b d : α)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (h3 : f a + f b + f d = g a + g b + g d)
    (hrest : ∀ q : α, q ≠ a → q ≠ b → q ≠ d → f q = g q) : (∑ q : α, f q) = ∑ q : α, g q := by
  classical
  let S : Finset α := {a, b, d}
  have hS (h : α → ℕ) : (∑ q ∈ S, h q) = h a + h b + h d := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, hab, had, hbd,
      or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
    omega
  have hF : (∑ q ∈ Sᶜ, f q) = ∑ q ∈ Sᶜ, g q := by
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    simp only [S, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    exact hrest q hq.1 hq.2.1 hq.2.2
  rw [← Finset.sum_add_sum_compl S f, ← Finset.sum_add_sum_compl S g, hS f, hS g, h3, hF]
theorem inPlaceHalfAdd_val_eq (x y : ZMod 2) :
    (x + y).val + 2 * (x * y).val = x.val + y.val := by
  revert x y; decide
theorem stepWeightList_preserves_wSum {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (L L' : List ℕ)
    (hlen : L.length = M) (s : InPlaceStep) (hvalid : s.validAt cur = true)
    (hstep : stepWeightList cur L s = some L') : L'.length = M ∧ ∀ β : BitAssignment M, wSum
    L' (s.evalOne cur hcur hvalid β) = wSum L β := by
  cases s with
  | fa a b c =>
      rcases InPlaceStep.validAt_fa_iff.mp hvalid with ⟨⟨⟨⟨hab, hac⟩, hbc⟩, ha, hb⟩, hc⟩
      dsimp only [stepWeightList] at hstep
      split at hstep
      · rename_i hcond
        injection hstep with hL'
        subst hL'
        set L₁ :=
          listSet (listSet (listSet (listSet L a 0) c 0) b (listGet L a)) cur (2 * listGet L a)
        refine ⟨by simp only [L₁, listSet_length, hlen], fun β ↦ ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, gt_iff_lt] at hcond
        rcases hcond with ⟨⟨⟨hcur0, _⟩, hwb⟩, hwc⟩
        let aw : Wire M := ⟨a, lt_trans ha hcur⟩
        let bw : Wire M := ⟨b, lt_trans hb hcur⟩
        let cw : Wire M := ⟨c, lt_trans hc hcur⟩
        let auxAux : Wire M := ⟨cur, hcur⟩
        have hg (j : ℕ) : listGet L₁ j = if j = cur then 2 * listGet L a else if j = b then
            listGet L a else if j = c then 0 else if j = a then 0 else listGet L j := by
          simp only [L₁, listGet_listSet, listSet_length, hlen, lt_trans ha hcur,
            lt_trans hb hcur, lt_trans hc hcur, show cur < M from hcur]
        dsimp only [InPlaceStep.evalOne, wSum]
        apply sum_four_distinct _ _ aw bw cw auxAux (fun h ↦ hab (congrArg Fin.val h))
          (fun h ↦ hac (congrArg Fin.val h)) (wire_ne_of_lt ha) (fun h ↦ hbc (congrArg Fin.val h))
          (wire_ne_of_lt hb) (wire_ne_of_lt hc)
        · have hba : inPlaceFullAddSetup cur hcur aw bw cw β bw = β aw + β bw + β cw := by
            dsimp only [inPlaceFullAddSetup]
            rw [Function.update_of_ne (wire_ne_of_lt hb : bw ≠ ⟨cur, hcur⟩), Function.update_self]
          have hda : inPlaceFullAddSetup cur hcur aw bw cw β auxAux =
              (β bw + β aw) * (β cw + β aw) + β aw := by
            dsimp only [inPlaceFullAddSetup, auxAux]
            rw [Function.update_self]
          change listGet L₁ a * _ + listGet L₁ b *
            (inPlaceFullAddSetup cur hcur aw bw cw β bw).val +
            listGet L₁ c * _ + listGet L₁ cur * (inPlaceFullAddSetup cur hcur aw bw cw β auxAux).val
              =
            listGet L a * (β aw).val + listGet L b * (β bw).val +
              listGet L c * (β cw).val + listGet L cur * (β auxAux).val
          simp only [hg, Nat.ne_of_lt ha, Nat.ne_of_lt hb, Nat.ne_of_lt hc, hab, hac, Ne.symm hbc,
            ↓reduceIte, zero_mul, zero_add, add_zero, hba, hda, hwb, hwc, hcur0]
          calc listGet L a * (β aw + β bw + β cw).val +
                2 * listGet L a * ((β bw + β aw) * (β cw + β aw) + β aw).val
            _ = listGet L a * ((β aw + β bw + β cw).val +
                  2 * ((β bw + β aw) * (β cw + β aw) + β aw).val) := by ring
            _ = listGet L a * ((β aw).val + (β bw).val + (β cw).val) := by
                  rw [inPlaceFullAdd_val_eq]
            _ = _ := by ring
        · intro q hqa hqb hqc hqd
          simp only [hg q.val, show q.val ≠ cur from fun h ↦ hqd (Fin.ext h),
            show q.val ≠ b from fun h ↦ hqb (Fin.ext h),
            show q.val ≠ c from fun h ↦ hqc (Fin.ext h),
            show q.val ≠ a from fun h ↦ hqa (Fin.ext h), ↓reduceIte, inPlaceFullAddSetup,
            Function.update_of_ne (show q ≠ ⟨cur, hcur⟩ from hqd),
            Function.update_of_ne (show q ≠ ⟨b, lt_trans hb hcur⟩ from hqb)]
      · contradiction
  | ha a b =>
      rcases InPlaceStep.validAt_ha_iff.mp hvalid with ⟨⟨hab, ha⟩, hb⟩
      dsimp only [stepWeightList] at hstep
      split at hstep
      · rename_i hcond
        injection hstep with hL'
        subst hL'
        set L₁ := listSet (listSet (listSet L a 0) b (listGet L a)) cur (2 * listGet L a)
        refine ⟨by simp only [L₁, listSet_length, hlen], fun β ↦ ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq, gt_iff_lt] at hcond
        rcases hcond with ⟨⟨hcur0, _⟩, hwb⟩
        let aw : Wire M := ⟨a, lt_trans ha hcur⟩
        let bw : Wire M := ⟨b, lt_trans hb hcur⟩
        let auxAux : Wire M := ⟨cur, hcur⟩
        have hg (j : ℕ) : listGet L₁ j = if j = cur then 2 * listGet L a else if j = b then
            listGet L a else if j = a then 0 else listGet L j := by
          simp only [L₁, listGet_listSet, listSet_length, hlen, lt_trans ha hcur,
            lt_trans hb hcur, show cur < M from hcur]
        dsimp only [InPlaceStep.evalOne, wSum]
        apply sum_three_distinct _ _ aw bw auxAux (fun h ↦ hab (congrArg Fin.val h))
          (wire_ne_of_lt ha) (wire_ne_of_lt hb)
        · have hba : inPlaceHalfAddSetup cur hcur aw bw β bw = β aw + β bw := by
            dsimp only [inPlaceHalfAddSetup]
            rw [Function.update_of_ne (wire_ne_of_lt hb : bw ≠ ⟨cur, hcur⟩), Function.update_self]
          have hda : inPlaceHalfAddSetup cur hcur aw bw β auxAux = β aw * β bw := by
            dsimp only [inPlaceHalfAddSetup, auxAux]
            rw [Function.update_self]
          change listGet L₁ a * _ + listGet L₁ b * (inPlaceHalfAddSetup cur hcur aw bw β bw).val +
            listGet L₁ cur * (inPlaceHalfAddSetup cur hcur aw bw β auxAux).val =
            listGet L a * (β aw).val + listGet L b * (β bw).val + listGet L cur * (β auxAux).val
          simp only [hg, Nat.ne_of_lt ha, Nat.ne_of_lt hb, hab, ↓reduceIte, zero_mul, zero_add,
            hba, hda, hwb, hcur0]
          calc listGet L a * (β aw + β bw).val + 2 * listGet L a * (β aw * β bw).val
            _ = listGet L a * ((β aw + β bw).val + 2 * (β aw * β bw).val) := by ring
            _ = listGet L a * ((β aw).val + (β bw).val) := by rw [inPlaceHalfAdd_val_eq]
            _ = _ := by ring
        · intro q hqa hqb hqd
          simp only [hg q.val, show q.val ≠ cur from fun h ↦ hqd (Fin.ext h),
            show q.val ≠ b from fun h ↦ hqb (Fin.ext h),
            show q.val ≠ a from fun h ↦ hqa (Fin.ext h), ↓reduceIte, inPlaceHalfAddSetup,
            Function.update_of_ne (show q ≠ ⟨cur, hcur⟩ from hqd),
            Function.update_of_ne (show q ≠ ⟨b, lt_trans hb hcur⟩ from hqb)]
      · contradiction
theorem runWeightList_preserves_wSum {M : ℕ} (cur : ℕ) (steps : List InPlaceStep)
    (hbound : cur + steps.length ≤ M) (hvalid : validInPlaceSteps cur steps = true)
    (L L_out : List ℕ) (hlen : L.length = M) (hrun : runWeightList cur steps L = some L_out)
    (β : BitAssignment M) : wSum L_out (evalInPlaceSteps cur steps hbound hvalid β) = wSum L β
    := by
  induction steps generalizing cur L β with
  | nil =>
      injection hrun with hL
      subst hL
      rfl
  | cons s rest ih =>
      have hv : s.validAt cur = true ∧ validInPlaceSteps (cur + 1) rest = true := by
        simpa [validInPlaceSteps] using hvalid
      dsimp only [runWeightList] at hrun
      cases hs : stepWeightList cur L s with
      | none => rw [hs] at hrun; contradiction
      | some L' =>
          rw [hs] at hrun
          dsimp only at hrun
          rw [match_forceList_apply (runWeightList (cur + 1) rest) L'] at hrun
          have hcur1 : cur + 1 ≤ M := by simp at hbound; omega
          obtain ⟨hlen', hstep_eq⟩ := stepWeightList_preserves_wSum cur hcur1 L L' hlen s hv.1 hs
          dsimp only [evalInPlaceSteps]
          rw [ih (cur + 1) (by simp at hbound; omega) hv.2 L' hlen' hrun]
          exact hstep_eq β
def embedPopWire {N S M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hbound : cur + S ≤ M) (u : Wire (N + S)) : Wire M :=
  if h : u.val < N then inWires ⟨u.val, h⟩ else ⟨cur + (u.val - N), by omega⟩
theorem embedPopWire_lt {N S M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hLt : ∀ i : Fin N, (inWires i).val < cur) (hbound : cur + S ≤ M) (u : Wire (N + S)) :
    (embedPopWire cur inWires hbound u).val < cur + S := by
  have hu := u.isLt
  dsimp [embedPopWire]
  split_ifs with h
  · have := hLt ⟨u.val, h⟩; omega
  · dsimp; omega
theorem embedPopWire_ge_of_above {N S M targetEnd : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hGe : ∀ i : Fin N, targetEnd ≤ (inWires i).val) (hCurGe : targetEnd ≤ cur)
    (hbound : cur + S ≤ M) (u : Wire (N + S)) : targetEnd ≤
    (embedPopWire cur inWires hbound u).val := by
  dsimp [embedPopWire]
  split_ifs with h
  · exact hGe ⟨u.val, h⟩
  · dsimp; omega
theorem embedPopWire_injective {N S M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hInj : Function.Injective inWires) (hLt : ∀ i : Fin N, (inWires i).val < cur)
    (hbound : cur + S ≤ M) : Function.Injective (embedPopWire cur inWires hbound) := by
  intro u₁ u₂ heq
  dsimp [embedPopWire] at heq
  split_ifs at heq with h₁ h₂ h₃
  · have hi := hInj heq
    exact Fin.ext (by simpa using congrArg Fin.val hi)
  · exfalso; have := hLt ⟨u₁.val, h₁⟩; have hv := congrArg Fin.val heq; dsimp at hv; omega
  · exfalso; have := hLt ⟨u₂.val, h₃⟩; have hv := congrArg Fin.val heq; dsimp at hv; omega
  · have hv := congrArg Fin.val heq; dsimp at hv; exact Fin.ext (by omega)
def mapPopIdx {N M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M) (v : ℕ) : ℕ :=
  if h : v < N then (inWires ⟨v, h⟩).val else cur + (v - N)
def InPlaceStep.remap {N M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M) : InPlaceStep → InPlaceStep
  | .fa a b c => .fa (mapPopIdx cur inWires a) (mapPopIdx cur inWires b) (mapPopIdx cur inWires c)
  | .ha a b => .ha (mapPopIdx cur inWires a) (mapPopIdx cur inWires b)
def remapSteps {N M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M) : List InPlaceStep → List InPlaceStep
  | [] => []
  | s :: rest => s.remap cur inWires :: remapSteps cur inWires rest
@[simp] theorem remapSteps_length {N M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (steps : List InPlaceStep) : (remapSteps cur inWires steps).length = steps.length := by
  induction steps <;> simp [remapSteps, *]
theorem mapPopIdx_lt_step {N M : ℕ} (cur t : ℕ) (inWires : Fin N → Wire M)
    (hLt : ∀ i : Fin N, (inWires i).val < cur) {v : ℕ} (hv : v < N + t) :
    mapPopIdx cur inWires v < cur + t := by
  dsimp [mapPopIdx]
  split_ifs with h
  · have := hLt ⟨v, h⟩; omega
  · omega
theorem mapPopIdx_ne {N M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hInj : Function.Injective inWires) (hLt : ∀ i : Fin N, (inWires i).val < cur) {v₁ v₂ : ℕ}
    (hne : v₁ ≠ v₂) : mapPopIdx cur inWires v₁ ≠ mapPopIdx cur inWires v₂ := by
  dsimp [mapPopIdx]
  split_ifs with h₁ h₂ h₃
  · intro heq
    have hi := hInj (Fin.ext heq)
    exact hne (by simpa using congrArg Fin.val hi)
  · have := hLt ⟨v₁, h₁⟩; omega
  · have := hLt ⟨v₂, h₃⟩; omega
  · omega
theorem remapSteps_valid_aux {N M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hInj : Function.Injective inWires) (hLt : ∀ i : Fin N, (inWires i).val < cur) :
    ∀ (t : ℕ) (steps : List InPlaceStep),
      validInPlaceSteps (N + t) steps = true →
      validInPlaceSteps (cur + t) (remapSteps cur inWires steps) = true
  | _, [], _ => rfl
  | t, s :: rest, hvalid => by
      have hv : s.validAt (N + t) = true ∧ validInPlaceSteps (N + t + 1) rest = true := by
        simpa [validInPlaceSteps] using hvalid
      have hs' : (s.remap cur inWires).validAt (cur + t) = true := by
        cases s with
        | fa a b c =>
            rcases InPlaceStep.validAt_fa_iff.mp hv.1 with ⟨⟨⟨⟨hab, hac⟩, hbc⟩, ha, hb⟩, hc⟩
            simp[InPlaceStep.remap, InPlaceStep.validAt,
                mapPopIdx_ne cur inWires hInj hLt hab, mapPopIdx_ne cur inWires hInj hLt hac,
                mapPopIdx_ne cur inWires hInj hLt hbc, mapPopIdx_lt_step cur t inWires hLt ha,
                mapPopIdx_lt_step cur t inWires hLt hb,
                mapPopIdx_lt_step cur t inWires hLt hc]
        | ha a b =>
            rcases InPlaceStep.validAt_ha_iff.mp hv.1 with ⟨⟨hab, ha⟩, hb⟩
            simp[InPlaceStep.remap, InPlaceStep.validAt,
                mapPopIdx_ne cur inWires hInj hLt hab, mapPopIdx_lt_step cur t inWires hLt ha,
                mapPopIdx_lt_step cur t inWires hLt hb]
      have hrest' := remapSteps_valid_aux cur inWires hInj hLt (t + 1) rest
        (by simpa [Nat.add_assoc] using hv.2)
      simp only [remapSteps, validInPlaceSteps, hs', Bool.true_and]
      simpa [Nat.add_assoc] using hrest'
theorem remapSteps_above {N M targetEnd : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hGe : ∀ i : Fin N, targetEnd ≤ (inWires i).val) (hCurGe : targetEnd ≤ cur) :
    ∀ (steps : List InPlaceStep), stepsAbove targetEnd (remapSteps cur inWires steps) = true
  | [] => rfl
  | s :: rest => by
      have hm : ∀ v : ℕ, targetEnd ≤ mapPopIdx cur inWires v := fun v ↦ by
        dsimp [mapPopIdx]; split_ifs with h
        · exact hGe ⟨v, h⟩
        · omega
      cases s <;> simp [remapSteps, stepsAbove, InPlaceStep.remap, InPlaceStep.above, hm,
        remapSteps_above cur inWires hGe hCurGe rest]
theorem evalInPlaceSteps_remap_sim {N S M : ℕ} (cur : ℕ) (inWires : Fin N → Wire M)
    (hInj : Function.Injective inWires) (hLt : ∀ i : Fin N, (inWires i).val < cur)
    (hbound : cur + S ≤ M) :
    ∀ (t : ℕ) (steps : List InPlaceStep) (ht : t + steps.length = S)
      (hv₀ : validInPlaceSteps (N + t) steps = true)
      (β : BitAssignment M),
      let φ := embedPopWire cur inWires hbound
      let hvM := remapSteps_valid_aux cur inWires hInj hLt t steps hv₀
      let hb₀ : (N + t) + steps.length ≤ N + S := by omega
      let hbM : (cur + t) + (remapSteps cur inWires steps).length ≤ M := by simp; omega
      ((evalInPlaceSteps (cur + t) (remapSteps cur inWires steps) hbM hvM β) ∘ φ =
          evalInPlaceSteps (N + t) steps hb₀ hv₀ (β ∘ φ)) ∧
        (∀ w : Wire M, (∀ u : Wire (N + S), w ≠ φ u) →
          evalInPlaceSteps (cur + t) (remapSteps cur inWires steps) hbM hvM β w = β w)
  | t, [], ht, hv₀, β => ⟨rfl, fun _ _ ↦ rfl⟩
  | t, s :: rest, ht, hv₀, β => by
      let φ := embedPopWire cur inWires hbound
      have hφ_inj : Function.Injective φ := embedPopWire_injective cur inWires hInj hLt hbound
      have hφ_eq : ∀ (v : ℕ) (hv : v < N + S),(φ ⟨v, hv⟩).val = mapPopIdx cur inWires v := by
        intro v hv; dsimp [φ, embedPopWire, mapPopIdx]; split_ifs <;> rfl
      have hv_split : s.validAt (N + t) = true ∧ validInPlaceSteps (N + t + 1) rest = true := by
        simpa [validInPlaceSteps] using hv₀
      have hcur0 : (N + t) + 1 ≤ N + S := by simp at ht; omega
      have hcurM : (cur + t) + 1 ≤ M := by simp at ht; omega
      have hdu : φ ⟨N + t, hcur0⟩ = ⟨cur + t, hcurM⟩ := by
        apply Fin.ext
        have hd_val : (φ ⟨N + t, hcur0⟩).val = mapPopIdx cur inWires (N + t) := hφ_eq (N + t) hcur0
        dsimp [mapPopIdx] at hd_val
        rw [dite_eq_right_iff.mpr (fun h ↦ absurd h (by omega))] at hd_val
        dsimp
        omega
      have hStep (bu : Wire (N + S)) (vb vd : ZMod 2) :
          let β' := Function.update (Function.update β (φ bu) vb) ⟨cur + t, hcurM⟩ vd
          (β' ∘ φ = Function.update (Function.update (β ∘ φ) bu vb) ⟨N + t, hcur0⟩ vd) ∧
            (∀ w : Wire M, (∀ u : Wire (N + S), w ≠ φ u) → β' w = β w) := by
        refine ⟨funext fun u ↦ ?_, fun w hw ↦ ?_⟩
        · dsimp only [Function.comp_apply]
          rw [← hdu]
          by_cases hu_d : u = (⟨N + t, hcur0⟩ : Wire (N + S))
          · subst hu_d
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (hφ_inj.ne hu_d), Function.update_of_ne hu_d]
            by_cases hu_b : u = bu
            · subst hu_b
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne (hφ_inj.ne hu_b), Function.update_of_ne hu_b]
              rfl
        · rw [← hdu, Function.update_of_ne (hw ⟨N + t, hcur0⟩), Function.update_of_ne (hw bu)]
      have hWire (v : ℕ) (hv : v < N + t) :
          (⟨mapPopIdx cur inWires v, by have := mapPopIdx_lt_step cur t inWires hLt hv; omega⟩ :
            Wire M) = φ ⟨v, by omega⟩ :=
        Fin.ext (hφ_eq v (by omega)).symm
      cases s with
      | fa a b c =>
          rcases InPlaceStep.validAt_fa_iff.mp hv_split.1 with ⟨⟨⟨⟨_, _⟩, _⟩, ha, hb⟩, hc⟩
          rcases hStep ⟨b, by omega⟩
            (β (φ ⟨a, by omega⟩) + β (φ ⟨b, by omega⟩) + β (φ ⟨c, by omega⟩))
            ((β (φ ⟨b, by omega⟩) + β (φ ⟨a, by omega⟩)) *
              (β (φ ⟨c, by omega⟩) + β (φ ⟨a, by omega⟩)) + β (φ ⟨a, by omega⟩)) with
            ⟨hcomm1, hout1⟩
          let β' := inPlaceFullAddSetup (cur + t) hcurM
            (φ ⟨a, by omega⟩) (φ ⟨b, by omega⟩) (φ ⟨c, by omega⟩) β
          have ih := evalInPlaceSteps_remap_sim cur inWires hInj hLt hbound (t + 1) rest
            (by simp at ht; omega) (by simpa [Nat.add_assoc] using hv_split.2) β'
          refine ⟨?_, fun w hw ↦ ?_⟩
          · dsimp only [remapSteps, evalInPlaceSteps, InPlaceStep.evalOne, InPlaceStep.remap]
            simp only [hWire a ha, hWire b hb, hWire c hc]
            have h1 := ih.1
            rw [show β' ∘ φ = inPlaceFullAddSetup (N + t) hcur0 ⟨a, by omega⟩ ⟨b, by omega⟩
                ⟨c, by omega⟩ (β ∘ φ) from hcomm1] at h1
            convert h1 using 3
          · dsimp only [remapSteps, evalInPlaceSteps, InPlaceStep.evalOne, InPlaceStep.remap]
            simp only [hWire a ha, hWire b hb, hWire c hc]
            exact (by convert ih.2 w hw using 2 :
              evalInPlaceSteps (cur + t + 1) _ _ _ β' w = β' w).trans (hout1 w hw)
      | ha a b =>
          rcases InPlaceStep.validAt_ha_iff.mp hv_split.1 with ⟨⟨_, ha⟩, hb⟩
          rcases hStep ⟨b, by omega⟩ (β (φ ⟨a, by omega⟩) + β (φ ⟨b, by omega⟩))
            (β (φ ⟨a, by omega⟩) * β (φ ⟨b, by omega⟩)) with ⟨hcomm1, hout1⟩
          let β' := inPlaceHalfAddSetup (cur + t) hcurM (φ ⟨a, by omega⟩) (φ ⟨b, by omega⟩) β
          have ih := evalInPlaceSteps_remap_sim cur inWires hInj hLt hbound (t + 1) rest
            (by simp at ht; omega) (by simpa [Nat.add_assoc] using hv_split.2) β'
          refine ⟨?_, fun w hw ↦ ?_⟩
          · dsimp only [remapSteps, evalInPlaceSteps, InPlaceStep.evalOne, InPlaceStep.remap]
            simp only [hWire a ha, hWire b hb]
            have h1 := ih.1
            rw [show β' ∘ φ = inPlaceHalfAddSetup (N + t) hcur0 ⟨a, by omega⟩ ⟨b, by omega⟩
                (β ∘ φ) from hcomm1] at h1
            convert h1 using 3
          · dsimp only [remapSteps, evalInPlaceSteps, InPlaceStep.evalOne, InPlaceStep.remap]
            simp only [hWire a ha, hWire b hb]
            exact (by convert ih.2 w hw using 2 :
              evalInPlaceSteps (cur + t + 1) _ _ _ β' w = β' w).trans (hout1 w hw)
def addWeightAt {M₀ : ℕ} (L : List ℕ) (w : Wire M₀) (wt : ℕ) : List ℕ :=
  listSet L w.val (listGet L w.val + wt)
theorem addWeightAt_length {M₀ : ℕ} (L : List ℕ) (w : Wire M₀) (wt : ℕ) :
    (addWeightAt L w wt).length = L.length := listSet_length L w.val (listGet L w.val + wt)
theorem wSum_addWeightAt {M₀ : ℕ} (L : List ℕ) (hL : L.length = M₀) (w : Wire M₀) (wt : ℕ)
    (β₀ : BitAssignment M₀) : wSum (addWeightAt L w wt) β₀ = wSum L β₀ + wt * (β₀ w).val := by
  unfold wSum addWeightAt
  have hw : w.val < L.length := by omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w)]
  have hself : listGet (listSet L w.val (listGet L w.val + wt)) w.val = listGet L w.val + wt := by
    rw [listGet_listSet L w.val w.val _ hw]; simp
  have hrest : ∑ q ∈ Finset.univ.erase w, listGet (listSet L w.val (listGet L w.val + wt))
      q.val * (β₀ q).val = ∑ q ∈ Finset.univ.erase w, listGet L q.val * (β₀ q).val := by
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    have hne : q.val ≠ w.val := fun h ↦ (Finset.mem_erase.mp hq).1 (Fin.ext h)
    rw [listGet_listSet L w.val q.val _ hw]
    simp [hne]
  rw [hself, hrest]
  ring
def expectedOutWeightsAux {M₀ K : ℕ} (outWires : Fin K → Wire M₀) :
    (k : ℕ) → k ≤ K → List ℕ
  | 0, _ => List.replicate M₀ 0
  | k + 1, hk =>
      match forceList (addWeightAt (expectedOutWeightsAux outWires k (Nat.le_of_succ_le hk))
          (outWires ⟨k, hk⟩) (2 ^ k)) with
      | [] => []
      | h :: t => h :: t
def expectedOutWeights {M₀ K : ℕ} (outWires : Fin K → Wire M₀) : List ℕ :=
  expectedOutWeightsAux outWires K (le_refl K)
theorem expectedOutWeightsAux_length {M₀ K : ℕ} (outWires : Fin K → Wire M₀) :
    ∀ (k : ℕ) (hk : k ≤ K),(expectedOutWeightsAux outWires k hk).length = M₀
  | 0, _ => List.length_replicate
  | k + 1, hk => by
      dsimp only [expectedOutWeightsAux]
      rw [match_forceList_id]
      exact (addWeightAt_length _ _ _).trans (expectedOutWeightsAux_length outWires k
        (Nat.le_of_succ_le hk))
theorem listGet_replicate_zero : ∀ (n j : ℕ), listGet (List.replicate n 0) j = 0
  | 0, _ => rfl
  | _ + 1,0 => rfl
  | n + 1, j + 1 => listGet_replicate_zero n j
theorem wSum_expectedOutWeightsAux {M₀ K : ℕ} (outWires : Fin K → Wire M₀) (β₀ : BitAssignment M₀) :
    ∀ (k : ℕ) (hk : k ≤ K),
      wSum (expectedOutWeightsAux outWires k hk) β₀ =
        ∑ j : Fin k, 2 ^ j.val * (β₀ (outWires ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)).val
  | 0, _ => by
      unfold expectedOutWeightsAux wSum
      simp [listGet_replicate_zero]
  | k + 1, hk => by
      dsimp only [expectedOutWeightsAux]
      rw [match_forceList_id,
          wSum_addWeightAt _ (expectedOutWeightsAux_length outWires k (Nat.le_of_succ_le hk)),
          wSum_expectedOutWeightsAux outWires β₀ k (Nat.le_of_succ_le hk),
          Fin.sum_univ_castSucc]
      rfl
theorem wSum_expectedOutWeights {M₀ K : ℕ} (outWires : Fin K → Wire M₀) (β₀ : BitAssignment M₀) :
    wSum (expectedOutWeights outWires) β₀ = ∑ k : Fin K, 2 ^ k.val * (β₀ (outWires k)).val :=
  wSum_expectedOutWeightsAux outWires β₀ K (le_refl K)
end InPlaceStepEngine
end
end ModInPlaceStepEngine

section ModInt01ToffoliSubst
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder
namespace ToffoliSubst
variable {Var : Type} {n k m : ℕ}
theorem triple_eq_self (r : QRegister 3 n) (h₀₁ : r 0 ≠ r 1) (h₀₂ : r 0 ≠ r 2)
    (h₁₂ : r 1 ≠ r 2) : QRegister.triple (r 0) (r 1) (r 2) h₀₁ h₀₂ h₁₂ = r := by
  ext i
  fin_cases i <;> rfl
def substGate (v : Var) (ancilla : Wire n) :
    {a : ℕ} → PrimitiveGate a → QRegister a n → DynamicCircuit Var n
  | 3, .toffoli, r =>
      have h₀₁ : r 0 ≠ r 1 := fun h ↦ by cases r.wires.injective h
      if h : r 0 ≠ ancilla ∧ r 1 ≠ ancilla ∧ r 2 ≠ ancilla then
        DynamicCircuit.jonesToffoli v (r 0) (r 1) (r 2) ancilla h₀₁ h.1 h.2.1 h.2.2
      else
        .identity
  | 1, .x, r => .circuit (.gate .x r)
  | 1, .y, r => .circuit (.gate .y r)
  | 1, .z, r => .circuit (.gate .z r)
  | 1, .h, r => .circuit (.gate .h r)
  | 1, .s, r => .circuit (.gate .s r)
  | 1, .t, r => .circuit (.gate .t r)
  | 2, .cnot, r => .circuit (.gate .cnot r)
  | 2, .swap, r => .circuit (.gate .swap r)
def substCircuit (v : Var) (ancilla : Wire n) : Circuit n → DynamicCircuit Var n
  | .identity => .identity
  | .gate g r => substGate v ancilla g r
  | .seq c₁ c₂ => .seq (substCircuit v ancilla c₁) (substCircuit v ancilla c₂)
@[simp] theorem count_substGate_toff (v : Var) (ancilla : Wire n)
    {a : ℕ} (g : PrimitiveGate a) (r : QRegister a n) :
    (substGate v ancilla g r).count PrimitiveGate.TOFF = 0 := by
  cases g with
  | toffoli =>
      dsimp only [substGate]
      split_ifs <;> simp
  | _ => rfl
@[simp] theorem count_substCircuit_toff (v : Var) (ancilla : Wire n) (c : Circuit n) :
    (substCircuit v ancilla c).count PrimitiveGate.TOFF = 0 := by
  induction c with
  | identity => rfl
  | gate g r => exact count_substGate_toff v ancilla g r
  | seq c₁ c₂ ih₁ ih₂ => simp [substCircuit, ih₁, ih₂]
theorem eval_comm_basisOutcomeProjector_of_not_mem_support
    (c : Circuit n) (ancilla : Wire n) (hanc : ancilla ∉ c.support) (o : Fin 2) :
    c.eval.1 * (QRegister.singleton ancilla).basisOutcomeProjector o =
      (QRegister.singleton ancilla).basisOutcomeProjector o * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g r =>
      have hdisj : r.DisjointWires (QRegister.singleton ancilla) :=
        QRegister.disjoint_iff.mpr fun i _ ↦ (r.ne_apply_of_not_mem_image ancilla hanc i).symm
      simpa only [Circuit.eval_gate, QRegister.embedUnitary_val,
        QRegister.basisOutcomeProjector] using
        r.embedMatrix_comm_of_disjoint (QRegister.singleton ancilla) hdisj g.eval.1 (compProj o)
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.mem_union, not_or] at hanc
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hanc.1, ← Matrix.mul_assoc, ih₂ hanc.2, Matrix.mul_assoc]
section QHL
variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
omit [DecidableEq Var] [NeZero (2 ^ n)] in
theorem restrictToZeroAncilla_wp_qAssign_restrict_eq_of_not_mem_support
    (c : Circuit n) (ancilla : Wire n) (hanc : ancilla ∉ c.support)
    (Θ : CQAssertionCompat Var (2 ^ n)) : CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval
    (CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton ancilla)))
    (QRegister.singleton ancilla) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ)
    (QRegister.singleton ancilla) := by
  funext σ
  apply Subtype.ext
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hP₀_idem : P₀ * P₀ = P₀ := QRegister.basisOutcomeProjector_mul_self _ 0
  have hcomm : c.eval.1 * P₀ = P₀ * c.eval.1 :=
    eval_comm_basisOutcomeProjector_of_not_mem_support c ancilla hanc 0
  have hadj : P₀ * c.eval.1ᴴ * P₀ = P₀ * c.eval.1ᴴ := by
    have h := congrArg conjTranspose hcomm
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
    calc P₀ * c.eval.1ᴴ * P₀ = P₀ * (c.eval.1ᴴ * P₀) := by rw [Matrix.mul_assoc]
      _ = P₀ * (P₀ * c.eval.1ᴴ) := by rw [← h]
      _ = (P₀ * P₀) * c.eval.1ᴴ := by rw [← Matrix.mul_assoc]
      _ = P₀ * c.eval.1ᴴ := by rw [hP₀_idem]
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, HermitianMat.conj_conj]
  rw [← Matrix.mul_assoc, hadj]
omit [Fintype Var] in
theorem wp_substGate_update_eq [Finite Var] (v : Var) (ancilla : Wire n) {a : ℕ}
    (g : PrimitiveGate a) (r : QRegister a n) (Θ : CQAssertionCompat Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) (σ : Store Var) (val : ℤ) : wp
    (substGate v ancilla g r).compile Θ (Function.update σ v val) = wp
    (substGate v ancilla g r).compile Θ σ := by
  cases g with
  | toffoli =>
      dsimp only [substGate]
      split_ifs with h
      · exact DynamicCircuit.wp_jonesToffoli_update_self v (r 0) (r 1) (r 2) ancilla _
          h.1 h.2.1 h.2.2 Θ σ val
      · simpa using hΘ σ val
  | _ =>
      cases nonempty_fintype Var
      simp only [substGate, DynamicCircuit.compile_circuit,
        DynCircuitExt.wp_circuit_compile_compat,
        wpQAssignCompat, hΘ σ val]
omit [Fintype Var] in
theorem wp_substCircuit_update_eq [Finite Var] (v : Var) (ancilla : Wire n) (c : Circuit n)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) : ∀ σ val,
    wp (substCircuit v ancilla c).compile Θ (Function.update σ v val) = wp
    (substCircuit v ancilla c).compile Θ σ := by
  induction c generalizing Θ with
  | identity =>
      intro σ val
      simpa [substCircuit] using hΘ σ val
  | gate g r =>
      intro σ val
      exact wp_substGate_update_eq v ancilla g r Θ hΘ σ val
  | seq c₁ c₂ ih₁ ih₂ =>
      intro σ val
      simp only [substCircuit, DynamicCircuit.compile_seq, wp_qSeq]
      exact ih₁ (wp (substCircuit v ancilla c₂).compile Θ) (ih₂ Θ hΘ) σ val
theorem restrictToZeroAncilla_wp_substGate_of_not_mem (v : Var) (ancilla : Wire n)
    {a : ℕ} (g : PrimitiveGate a) (r : QRegister a n) (hanc : ancilla ∉ r.image)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla (wp (substGate v ancilla g r).compile Θ)
    (QRegister.singleton ancilla) = CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat (Circuit.gate g r).eval Θ) (QRegister.singleton ancilla) := by
  cases g with
  | toffoli =>
      have h₀₁ : r 0 ≠ r 1 := fun h ↦ by cases r.wires.injective h
      have h₀₂ : r 0 ≠ r 2 := fun h ↦ by cases r.wires.injective h
      have h₁₂ : r 1 ≠ r 2 := fun h ↦ by cases r.wires.injective h
      have h₀a : r 0 ≠ ancilla := (r.ne_apply_of_not_mem_image ancilla hanc 0).symm
      have h₁a : r 1 ≠ ancilla := (r.ne_apply_of_not_mem_image ancilla hanc 1).symm
      have h₂a : r 2 ≠ ancilla := (r.ne_apply_of_not_mem_image ancilla hanc 2).symm
      have hcond : r 0 ≠ ancilla ∧ r 1 ≠ ancilla ∧ r 2 ≠ ancilla := ⟨h₀a, h₁a, h₂a⟩
      have hgate : Circuit.gate PrimitiveGate.toffoli r =
          Circuit.TOFF (r 0) (r 1) (r 2) h₀₁ h₀₂ h₁₂ := by
        simp [Circuit.TOFF, compat_primGate_TOFF_eq, triple_eq_self r h₀₁ h₀₂ h₁₂]
      rw [hgate]
      dsimp only [substGate]
      rw [dite_eq_left_of_eq_true (eq_true hcond)]
      exact DynCircuitExt.restrictToZeroAncilla_wp_jonesToffoli_of_update_eq_compat
        v (r 0) (r 1) (r 2) ancilla h₀₁ h₀₂ h₁₂ h₀a h₁a h₂a Θ hΘ
  | _ => rfl
theorem restrictToZeroAncilla_wp_substCircuit_of_not_mem_support (v : Var)
    (ancilla : Wire n) (c : Circuit n) (hanc : ancilla ∉ c.support)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla (wp (substCircuit v ancilla c).compile Θ)
    (QRegister.singleton ancilla) = CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ)
    (QRegister.singleton ancilla) := by
  induction c generalizing Θ with
  | identity =>
      funext σ
      apply Subtype.ext
      simp [substCircuit]
  | gate g r =>
      exact restrictToZeroAncilla_wp_substGate_of_not_mem v ancilla g r hanc Θ hΘ
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.mem_union, not_or] at hanc
      simp only [substCircuit, DynamicCircuit.compile_seq, wp_qSeq, Circuit.eval_seq]
      have h₂_upd : ∀ σ val, wp (substCircuit v ancilla c₂).compile Θ
          (Function.update σ v val) = wp (substCircuit v ancilla c₂).compile Θ σ :=
          wp_substCircuit_update_eq v ancilla c₂ Θ hΘ
      rw [ih₁ hanc.1 (wp (substCircuit v ancilla c₂).compile Θ) h₂_upd,
        ← restrictToZeroAncilla_wp_qAssign_restrict_eq_of_not_mem_support
            c₁ ancilla hanc.1,
        ih₂ hanc.2 Θ hΘ,
        restrictToZeroAncilla_wp_qAssign_restrict_eq_of_not_mem_support
            c₁ ancilla hanc.1,
        wpQAssignCompat_comp]
end QHL
end ToffoliSubst
end
end ModInt01ToffoliSubst

section ModKaratsubaQft64Matrix
@[expose] public section
namespace KaratsubaQft64Matrix
open Real Operator Matrix
open scoped Matrix BigOperators
noncomputable def omega512 (k : ℤ) : ℂ := Complex.exp (2 * π * (k : ℂ) * Complex.I / 512)
noncomputable def omega128 (k : ℤ) : ℂ := Complex.exp (2 * π * (k : ℂ) * Complex.I / 512 * 4)
lemma omega128_def (k : ℤ) :
    omega128 k = Complex.exp (2 * π * (k : ℂ) * Complex.I / 128) := by
  unfold omega128
  congr 1; ring
@[simp] lemma omega128_zero : omega128 0 = 1 := by
  simp [omega128]
lemma omega512_four_mul (k : ℤ) : omega512 (4 * k) = omega128 k := by
  unfold omega512 omega128
  congr 1; push_cast; ring
lemma omega512_add (a b : ℤ) : omega512 (a + b) = omega512 a * omega512 b := by
  unfold omega512
  rw [← Complex.exp_add]
  congr 1; push_cast; ring
lemma omega128_add (a b : ℤ) : omega128 (a + b) = omega128 a * omega128 b := by
  unfold omega128
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma star_omega512 (k : ℤ) : star (omega512 k) = omega512 (-k) := by
  unfold omega512
  rw [RCLike.star_def, ← Complex.exp_conj]
  congr 1
  simp only [div_eq_mul_inv, map_mul, map_inv₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_intCast, Int.cast_neg]
  ring
lemma star_omega128 (k : ℤ) : star (omega128 k) = omega128 (-k) := by
  rw [← omega512_four_mul, star_omega512, ← omega512_four_mul]
  congr 1; ring
lemma star_mul_omega128_self (k : ℤ) : star (omega128 k) * omega128 k = 1 := by
  rw [star_omega128, ← omega128_add, neg_add_cancel, omega128_zero]
lemma omega512_mul_512 (q : ℤ) : omega512 (512 * q) = 1 := by
  unfold omega512
  exact Complex.exp_eq_one_iff.mpr ⟨q, by push_cast; ring⟩
lemma omega512_add_mul_512 (a q : ℤ) : omega512 (a + 512 * q) = omega512 a := by
  rw [omega512_add, omega512_mul_512, mul_one]
def bit6 (u : Fin 64) (r : Fin 6) : ℕ := (u.val / 2 ^ r.val) % 2
lemma bit6_zero_or_one (u : Fin 64) (r : Fin 6) : bit6 u r = 0 ∨ bit6 u r = 1 := by
  unfold bit6; omega
private lemma lemHex1f : ∀ u : Fin 64, u.val = bit6 u 0 + 2 * bit6 u 1 + 4 * bit6 u 2 + 8 * bit6 u
    3 + 16 * bit6 u 4 + 32 * bit6 u 5 := by
  decide
private lemma lemHex20 : ∀ u : Fin 64, u.val % 32 = bit6 u 0 + 2 * bit6 u 1 + 4 * bit6 u 2 + 8 *
    bit6 u 3 + 16 * bit6 u 4 := by
  decide
private lemma lemHex21 : ∀ u : Fin 64, u.val / 32 = bit6 u 5 := by
  decide
lemma fin64_val_eq_bits (u : Fin 64) : (u.val : ℤ) = (bit6 u 0 : ℤ) + 2 * (bit6 u 1 : ℤ) + 4 *
    (bit6 u 2 : ℤ) + 8 * (bit6 u 3 : ℤ) + 16 * (bit6 u 4 : ℤ) + 32 * (bit6 u 5 : ℤ) := by
  exact_mod_cast lemHex1f u
lemma fin64_mod32_eq_bits (u : Fin 64) : ((u.val % 32 : ℕ) : ℤ) = (bit6 u 0 : ℤ) + 2 *
    (bit6 u 1 : ℤ) + 4 * (bit6 u 2 : ℤ) + 8 * (bit6 u 3 : ℤ) + 16 * (bit6 u 4 : ℤ) := by
  exact_mod_cast lemHex20 u
lemma fin64_div32_eq_bit5 (u : Fin 64) : ((u.val / 32 : ℕ) : ℤ) = (bit6 u 5 : ℤ) := by
  exact_mod_cast lemHex21 u
def twosComp6Int (u : Fin 64) : ℤ := ((u.val % 32 : ℕ) : ℤ) - 32 * ((u.val / 32 : ℕ) : ℤ)
def shiftedFin64ToInt (u : Fin 64) : ℤ := (u.val : ℤ) - 32
def xor32 (u : Fin 64) : Fin 64 :=
  ⟨(u.val + 32) % 64, by omega⟩
theorem twosComp6Int_xor32 : ∀ u : Fin 64, twosComp6Int (xor32 u) = shiftedFin64ToInt u := by
  decide
def bitRev6 (z : Fin 64) : Fin 64 :=
  ⟨32 * bit6 z 0 + 16 * bit6 z 1 + 8 * bit6 z 2 + 4 * bit6 z 3 + 2 * bit6 z 4 + bit6 z 5, by
    have h0 := bit6_zero_or_one z 0
    have h1 := bit6_zero_or_one z 1
    have h2 := bit6_zero_or_one z 2
    have h3 := bit6_zero_or_one z 3
    have h4 := bit6_zero_or_one z 4
    have h5 := bit6_zero_or_one z 5
    omega⟩
lemma bitRev6_involutive : Function.Involutive bitRev6 := by
  intro z; revert z; decide
def bitRev6Equiv : Fin 64 ≃ Fin 64 := bitRev6_involutive.toPerm
@[simp] lemma bitRev6Equiv_apply (z : Fin 64) : bitRev6Equiv z = bitRev6 z := rfl
def bitXor (a c : ℕ) : ℕ := (a + c) % 2
lemma bitXor_eq_sub_two_mul {a c : ℕ} (ha : a = 0 ∨ a = 1) (hc : c = 0 ∨ c = 1) :
    (bitXor a c : ℤ) = (a : ℤ) + (c : ℤ) - 2 * (a : ℤ) * (c : ℤ) := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num [bitXor]
def karatsubaInExp512 (b8 : Fin 8) (u : Fin 64) : ℤ := -128 * ((bit6 u 0 : ℤ) + (bit6 u 1 : ℤ)
    + (bit6 u 2 : ℤ) + (bit6 u 3 : ℤ) + (bit6 u 4 : ℤ)) + (4 - (b8.val : ℤ)) *
    ((u.val % 32 : ℕ) : ℤ) + 32 * (b8.val : ℤ) * (bit6 u 5 : ℤ)
def karatsubaInExp128 (b : Fin 2) (u : Fin 64) : ℤ := -32 * ((bit6 u 0 : ℤ) + (bit6 u 1 : ℤ) +
    (bit6 u 2 : ℤ) + (bit6 u 3 : ℤ) + (bit6 u 4 : ℤ)) + (1 - (b.val : ℤ)) *
    ((u.val % 32 : ℕ) : ℤ) + 32 * (b.val : ℤ) * (bit6 u 5 : ℤ)
lemma karatsubaInExp512_four_mul (b : Fin 2) (u : Fin 64) :
    karatsubaInExp512 ⟨4 * b.val, by omega⟩ u = 4 * karatsubaInExp128 b u := by
  unfold karatsubaInExp512 karatsubaInExp128
  dsimp only
  push_cast
  ring
def karatsubaStageExp128 (z u : Fin 64) : ℤ := 64 * ((bit6 z 0 * bit6 u 0 : ℤ) + (bit6 z 1 *
    bit6 u 1 : ℤ) + (bit6 z 2 * bit6 u 2 : ℤ) + (bit6 z 3 * bit6 u 3 : ℤ) + (bit6 z 4 * bit6 u
    4 : ℤ) + (bit6 z 5 * bit6 u 5 : ℤ)) + (16 * (bitXor (bit6 z 1) (bit6 u 0) : ℤ) + (8 *
    (bitXor (bit6 z 2) (bit6 u 0) : ℤ) + 16 * (bitXor (bit6 z 2) (bit6 u 1) : ℤ)) + (4 *
    (bitXor (bit6 z 3) (bit6 u 0) : ℤ) + 8 * (bitXor (bit6 z 3) (bit6 u 1) : ℤ) + 16 * (bitXor
    (bit6 z 3) (bit6 u 2) : ℤ)) + (2 * (bitXor (bit6 z 4) (bit6 u 0) : ℤ) + 4 * (bitXor (bit6
    z 4) (bit6 u 1) : ℤ) + 8 * (bitXor (bit6 z 4) (bit6 u 2) : ℤ) + 16 * (bitXor (bit6 z 4)
    (bit6 u 3) : ℤ)) + (1 * (bitXor (bit6 z 5) (bit6 u 0) : ℤ) + 2 * (bitXor (bit6 z 5) (bit6
    u 1) : ℤ) + 4 * (bitXor (bit6 z 5) (bit6 u 2) : ℤ) + 8 * (bitXor (bit6 z 5) (bit6 u 3) :
    ℤ) + 16 * (bitXor (bit6 z 5) (bit6 u 4) : ℤ)))
def karatsubaOutExp128 (z : Fin 64) : ℤ := 16 * (bit6 z 1 : ℤ) + 24 * (bit6 z 2 : ℤ) + 28 *
    (bit6 z 3 : ℤ) + 30 * (bit6 z 4 : ℤ) + 31 * (bit6 z 5 : ℤ)
noncomputable def karatsubaOutPhase64 (y : Fin 64) : ℂ :=
  omega128 (karatsubaOutExp128 (bitRev6 y))
theorem karatsubaExp512_sub_target_eq_mul_512 (b8 : Fin 8) (z u : Fin 64) : ∃ q : ℤ,
    karatsubaInExp512 b8 u + 4 * karatsubaStageExp128 z u = 4 * karatsubaOutExp128 z -
    twosComp6Int u * (8 * ((bitRev6 z).val : ℤ) + (b8.val : ℤ)) + 512 * q := by
  have hxor (i j : Fin 6) :
      (bitXor (bit6 z i) (bit6 u j) : ℤ) =
        (bit6 z i : ℤ) + (bit6 u j : ℤ) - 2 * (bit6 z i : ℤ) * (bit6 u j : ℤ) :=
    bitXor_eq_sub_two_mul (bit6_zero_or_one z i) (bit6_zero_or_one u j)
  refine ⟨((bit6 z 0 : ℤ) * (bit6 u 0 : ℤ) + (bit6 z 0 : ℤ) * (bit6 u 1 : ℤ) +
      2 * ((bit6 z 0 : ℤ) * (bit6 u 2 : ℤ)) + 4 * ((bit6 z 0 : ℤ) * (bit6 u 3 : ℤ)) +
      8 * ((bit6 z 0 : ℤ) * (bit6 u 4 : ℤ)) - 16 * ((bit6 z 0 : ℤ) * (bit6 u 5 : ℤ))) +
    ((bit6 z 1 : ℤ) * (bit6 u 1 : ℤ) + (bit6 z 1 : ℤ) * (bit6 u 2 : ℤ) +
      2 * ((bit6 z 1 : ℤ) * (bit6 u 3 : ℤ)) + 4 * ((bit6 z 1 : ℤ) * (bit6 u 4 : ℤ)) -
      8 * ((bit6 z 1 : ℤ) * (bit6 u 5 : ℤ))) +
    ((bit6 z 2 : ℤ) * (bit6 u 2 : ℤ) + (bit6 z 2 : ℤ) * (bit6 u 3 : ℤ) +
      2 * ((bit6 z 2 : ℤ) * (bit6 u 4 : ℤ)) - 4 * ((bit6 z 2 : ℤ) * (bit6 u 5 : ℤ))) +
    ((bit6 z 3 : ℤ) * (bit6 u 3 : ℤ) + (bit6 z 3 : ℤ) * (bit6 u 4 : ℤ) -
      2 * ((bit6 z 3 : ℤ) * (bit6 u 5 : ℤ))) +
    ((bit6 z 4 : ℤ) * (bit6 u 4 : ℤ) - (bit6 z 4 : ℤ) * (bit6 u 5 : ℤ)), ?_⟩
  unfold karatsubaInExp512 karatsubaStageExp128 karatsubaOutExp128 twosComp6Int bitRev6
  rw [fin64_mod32_eq_bits, fin64_div32_eq_bit5]
  simp only [hxor]
  push_cast
  ring
theorem omega512_karatsuba_eq (b8 : Fin 8) (z u : Fin 64) : omega512
    (karatsubaInExp512 b8 u + 4 * karatsubaStageExp128 z u) = karatsubaOutPhase64 (bitRev6 z)
    * omega512 (-twosComp6Int u * (8 * ((bitRev6 z).val : ℤ) + (b8.val : ℤ))) := by
  rcases karatsubaExp512_sub_target_eq_mul_512 b8 z u with ⟨q, hq⟩
  rw [hq, omega512_add_mul_512]
  have hsub :
      4 * karatsubaOutExp128 z -
          twosComp6Int u * (8 * ((bitRev6 z).val : ℤ) + (b8.val : ℤ)) =
        4 * karatsubaOutExp128 z +
          (-twosComp6Int u * (8 * ((bitRev6 z).val : ℤ) + (b8.val : ℤ))) := by ring
  rw [hsub, omega512_add, omega512_four_mul]
  unfold karatsubaOutPhase64
  rw [bitRev6_involutive z]
theorem omega128_karatsuba_eq (b : Fin 2) (z u : Fin 64) : omega128
    (karatsubaInExp128 b u + karatsubaStageExp128 z u) = karatsubaOutPhase64 (bitRev6 z) *
    omega128 (-twosComp6Int u * (2 * ((bitRev6 z).val : ℤ) + (b.val : ℤ))) := by
  have h := omega512_karatsuba_eq ⟨4 * b.val, by omega⟩ z u
  have hlhs :
      karatsubaInExp512 ⟨4 * b.val, by omega⟩ u + 4 * karatsubaStageExp128 z u =
        4 * (karatsubaInExp128 b u + karatsubaStageExp128 z u) := by
    rw [karatsubaInExp512_four_mul]; ring
  have hrhs : -twosComp6Int u * (8 * ((bitRev6 z).val : ℤ) + (4 * b.val : ℕ)) = 4 *
      (-twosComp6Int u * (2 * ((bitRev6 z).val : ℤ) + (b.val : ℤ))) := by
    push_cast; ring
  rw [hlhs, omega512_four_mul] at h
  dsimp only at h
  rw [hrhs, omega512_four_mul] at h
  exact h
noncomputable def subGridElem128 (b : Fin 2) (y : Fin 64) (p : ℤ) : ℂ :=
  (1 / (√64 : ℂ)) * omega128 (-p * (2 * (y.val : ℤ) + (b.val : ℤ)))
noncomputable def subGridUnitary128 (b : Fin 2) : Matrix (Fin 64) (Fin 64) ℂ :=
  Matrix.of fun y u ↦ subGridElem128 b y (shiftedFin64ToInt u)
noncomputable def karatsubaRawUnitary128 (b : Fin 2) : Matrix (Fin 64) (Fin 64) ℂ := Matrix.of
    fun z u ↦ (1 / (√64 : ℂ)) * omega128 (karatsubaInExp128 b u + karatsubaStageExp128 z u)
noncomputable def karatsubaOffsetUnitary128 (b : Fin 2) : Matrix (Fin 64) (Fin 64) ℂ :=
  Matrix.of fun z u ↦ karatsubaRawUnitary128 b z (xor32 u)
theorem karatsubaRawUnitary128_apply (b : Fin 2) (z u : Fin 64) : karatsubaRawUnitary128 b z u
    = karatsubaOutPhase64 (bitRev6 z) * subGridElem128 b (bitRev6 z) (twosComp6Int u) := by
  dsimp [karatsubaRawUnitary128, subGridElem128]
  rw [omega128_karatsuba_eq]
  ring
theorem karatsubaOffsetUnitary128_apply (b : Fin 2) (z u : Fin 64) :
    karatsubaOffsetUnitary128 b z u =
      karatsubaOutPhase64 (bitRev6Equiv z) * subGridUnitary128 b (bitRev6Equiv z) u := by
  dsimp [karatsubaOffsetUnitary128, subGridUnitary128]
  rw [karatsubaRawUnitary128_apply, twosComp6Int_xor32]
end KaratsubaQft64Matrix
end
end ModKaratsubaQft64Matrix

section ModLiteralKineticAndMidpoint128
@[expose] public section
namespace LiteralKineticAndMidpoint128
open Operator Matrix Real SpecsAux.SpecMirror
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open Classical in
noncomputable abbrev gridProjector : Operator (2 ^ systemQubits) :=
  Matrix.diagonal fun x ↦ if IsGridState x then 1 else 0
def intNormSq (p : Fin 3 → ℤ) : ℕ := (p 0).natAbs ^ 2 + (p 1).natAbs ^ 2 + (p 2).natAbs ^ 2
theorem l2_opNorm_diagonal_le {d : ℕ} (f : Fin d → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x, ‖f x‖ ≤ B) : ‖Matrix.diagonal f‖ ≤ B := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hB).mpr hf
open Classical in
noncomputable abbrev electronKineticOp : Operator (2 ^ systemQubits) := Matrix.diagonal fun x
    ↦ if IsGridState x then ((∑ i : Fin numElectrons, waveNumberSq (momentum x (.electron i))
    / 2 : ℝ) : ℂ) else 0
noncomputable abbrev elecQuadCenterOffset : ℝ := ∑ _i : Fin numElectrons, (∑ _w : Fin 3, (2 *
    π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 * (((2 : ℝ) ^ (electronBits - 1) - 1) ^ 2 / 2)) / 2
theorem pi_le_3141592654 : π ≤ 3141592654 / 1000000000 := by
  linarith [Real.pi_lt_d20]
theorem cellVolume_rpow_third_ge_1342516031 :
    (1342516031 / 100000000 : ℝ) ≤ cellVolume ^ (1 / 3 : ℝ) := by
  have h1 : (1342516031 / 100000000 : ℝ) ^ 3 ≤ cellVolume := by
    unfold cellVolume
    norm_num
  have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / 3)
  have h3 : ((1342516031 / 100000000 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 1342516031 / 100000000 := by
    rw [show ((1342516031 / 100000000 : ℝ) ^ 3) =
        (1342516031 / 100000000 : ℝ) ^ (3 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  linarith
noncomputable abbrev gridKappa : ℝ := 2 * π / cellVolume ^ (1 / 3 : ℝ)
noncomputable abbrev gridKappaRatHi : ℝ :=
  2 * (3141592654 / 1000000000) / (1342516031 / 100000000)
theorem gridKappa_nonneg : 0 ≤ gridKappa := by
  unfold gridKappa
  positivity
theorem kappaSqHalf_nonneg : 0 ≤ (2 * π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2 := by
  positivity
theorem gridKappa_le_ratHi : gridKappa ≤ gridKappaRatHi := by
  unfold gridKappa gridKappaRatHi
  have hpi : 2 * π ≤ 2 * (3141592654 / 1000000000 : ℝ) := by linarith [pi_le_3141592654]
  have hvol := cellVolume_rpow_third_ge_1342516031
  have h1 : 2 * π / cellVolume ^ (1 / 3 : ℝ) ≤ (2 * (3141592654 / 1000000000 : ℝ)) /
      cellVolume ^ (1 / 3 : ℝ) := div_le_div_of_nonneg_right hpi (by positivity)
  have h2 : (2 * (3141592654 / 1000000000 : ℝ)) / cellVolume ^ (1 / 3 : ℝ) ≤
      (2 * (3141592654 / 1000000000 : ℝ)) / (1342516031 / 100000000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hvol
  exact le_trans h1 h2
theorem kappaSqHalf_le_ratHi : gridKappa ^ 2 / 2 ≤ gridKappaRatHi ^ 2 / 2 := by
  have h0 : 0 ≤ gridKappa := gridKappa_nonneg
  have hle : gridKappa ≤ gridKappaRatHi := gridKappa_le_ratHi
  have hsq : gridKappa ^ 2 ≤ gridKappaRatHi ^ 2 := sq_le_sq' (by linarith) hle
  exact div_le_div_of_nonneg_right hsq (by positivity)
theorem momentum_electron_natAbs_le_31 (x : Fin (2 ^ systemQubits)) (i : Fin numElectrons)
    (w : Fin 3) : (momentum x (.electron i) w).natAbs ≤ 31 := by
  rw [momentum, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
    Int.natAbs_natCast]
  have hlt : (signMagnitude x (.electron i) w).2 < 32 := by
    dsimp [signMagnitude, componentBits, electronBits]
    exact Nat.mod_lt _ (by norm_num)
  omega
theorem elecQuadCenterOffset_eq :
    elecQuadCenterOffset = ((2 * π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) * 314247 := by
  unfold elecQuadCenterOffset
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, numElectrons, electronBits,
    nsmul_eq_mul]
  ring
theorem sum_electron_stepNumberSq_div_two_eq (x : Fin (2 ^ systemQubits)) :
    (∑ i : Fin numElectrons, waveNumberSq (momentum x (.electron i)) / 2) =
      ((2 * π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
        ((∑ i : Fin numElectrons, intNormSq (momentum x (.electron i)) : ℕ) : ℝ) := by
  have hsq_int (z : ℤ) : (z : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 := by
    cases z with
    | ofNat n => simp
    | negSucc n =>
        simp only [Int.cast_negSucc, Int.natAbs_negSucc]
        push_cast
        ring
  have hitem (i : Fin numElectrons) : waveNumberSq (momentum x (.electron i)) / 2 =
      ((2 * π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
      (intNormSq (momentum x (.electron i)) : ℝ) := by
    calc waveNumberSq (momentum x (.electron i)) / 2
      _ = ((2 * π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
            ((momentum x (.electron i) 0 : ℝ) ^ 2 +
              (momentum x (.electron i) 1 : ℝ) ^ 2 +
              (momentum x (.electron i) 2 : ℝ) ^ 2) := by
            dsimp [waveNumberSq, waveVector, dotProduct]
            rw [Fin.sum_univ_three]
            ring
      _ = ((2 * π / cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
            (intNormSq (momentum x (.electron i)) : ℝ) := by
            dsimp [intNormSq]
            push_cast
            rw [hsq_int, hsq_int, hsq_int]
  simp_rw [hitem, ← Finset.mul_sum]
  push_cast
  rfl
open Classical in
theorem electronKineticOp_sub_offset_eq_diagonal (E₀ : ℝ) : electronKineticOp - (E₀ : ℂ) •
    gridProjector = Matrix.diagonal fun x ↦ if IsGridState x then (((∑ i : Fin numElectrons,
    waveNumberSq (momentum x (.electron i)) / 2) - E₀ : ℝ) : ℂ) else 0 := by
  ext x y
  simp only [electronKineticOp, gridProjector, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : IsGridState x
    · simp only [hx, ↓reduceIte]; push_cast; ring
    · simp [hx]
  · simp [hxy]
noncomputable abbrev lambdaSlot0TeHi : ℝ := 3441613 / 100
theorem momentum_projectile_natAbs_le_127 (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    (momentum x .projectile w).natAbs ≤ 127 := by
  rw [momentum, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
    Int.natAbs_natCast]
  have hlt : (signMagnitude x .projectile w).2 < 128 := by
    dsimp [signMagnitude, componentBits, projectileBits]
    exact Nat.mod_lt _ (by norm_num)
  omega
theorem abs_momentum_projectile_le_127 (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    |(momentum x .projectile w : ℝ)| ≤ 127 := by
  have hnat : ((momentum x .projectile w).natAbs : ℝ) ≤ 127 := by
    exact_mod_cast momentum_projectile_natAbs_le_127 x w
  have habs_eq : |(momentum x .projectile w : ℝ)| = ((momentum x .projectile w).natAbs : ℝ) := by
    cases momentum x .projectile w with
    | ofNat n =>
        change |((n : ℕ) : ℝ)| = (n : ℝ)
        exact abs_of_nonneg (Nat.cast_nonneg n)
    | negSucc n =>
        simp only [Int.cast_negSucc, Int.natAbs_negSucc, abs_neg]
        rw [abs_of_nonneg (by positivity)]
  linarith
noncomputable def projectileKineticOp (c : Configuration) : Operator (2 ^ systemQubits) :=
  open Classical in
  Matrix.diagonal fun x ↦
    if IsGridState x then
      ((waveNumberSq (momentum x .projectile - c.projectileMomentum) /
        (2 * projectileMass) : ℝ) : ℂ)
    else 0
theorem electronKineticOp_eq_matrixOf :
    electronKineticOp =
      open Classical in
      Matrix.of fun x y ↦
        if IsGridState x ∧ IsGridState y then
          if x = y then
            ((∑ i : Fin numElectrons, waveNumberSq (momentum x (.electron i)) / 2 : ℝ) : ℂ)
          else 0
        else 0 := by
  classical
  ext x y
  simp only [electronKineticOp, Matrix.diagonal_apply, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : IsGridState x <;> simp [hx]
  · simp [hxy]
theorem projectileKineticOp_eq_matrixOf (c : Configuration) :
    projectileKineticOp c =
      open Classical in
      Matrix.of fun x y ↦
        if IsGridState x ∧ IsGridState y then
          if x = y then
            ((waveNumberSq (momentum x .projectile - c.projectileMomentum) /
              (2 * projectileMass) : ℝ) : ℂ)
          else 0
        else 0 := by
  classical
  ext x y
  simp only [projectileKineticOp, Matrix.diagonal_apply, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : IsGridState x <;> simp [hx]
  · simp [hxy]
noncomputable def projMidpointOffset (c : Configuration) : ℝ :=
  ((48387 / 2 : ℝ) * (gridKappa ^ 2 / 2) + waveNumberSq c.projectileMomentum / 2) / projectileMass
noncomputable def projLiteralPrepWeight (c : Configuration) : ℝ :=
  ((48387 / 2 : ℝ) * (gridKappa ^ 2 / 2) +
    127 * gridKappa * ∑ w : Fin 3, |waveVector c.projectileMomentum w|) / projectileMass
noncomputable abbrev lambdaSlot1TpHi : ℝ := 414968 / 1000
theorem stepVector_sub (a b : Fin 3 → ℤ) (w : Fin 3) :
    waveVector (a - b) w = waveVector a w - waveVector b w := by
  dsimp [waveVector]
  push_cast
  ring
theorem stepNumberSq_sub_eq (a b : Fin 3 → ℤ) : waveNumberSq (a - b) = waveNumberSq a - 2 * ∑
    w : Fin 3, waveVector a w * waveVector b w + waveNumberSq b := by
  dsimp [waveNumberSq, dotProduct]
  simp only [stepVector_sub, Fin.sum_univ_three]
  ring
theorem sum_abs_stepVector_projectileMomentum_le (c : Configuration) :
    (∑ w : Fin 3, |waveVector c.projectileMomentum w|) ≤ 50880725 / 1000 := by
  have hm : waveNumberSq c.projectileMomentum ≤ 29376 ^ 2 := c.momentum_le
  dsimp [waveNumberSq, dotProduct] at hm
  rw [Fin.sum_univ_three] at hm ⊢
  set a := |waveVector c.projectileMomentum 0|
  set b := |waveVector c.projectileMomentum 1|
  set d := |waveVector c.projectileMomentum 2|
  have ha0 : 0 ≤ a := abs_nonneg _
  have hb0 : 0 ≤ b := abs_nonneg _
  have hd0 : 0 ≤ d := abs_nonneg _
  have hsq : a ^ 2 + b ^ 2 + d ^ 2 ≤ 29376 ^ 2 := by
    nlinarith [hm, sq_abs (waveVector c.projectileMomentum 0),
      sq_abs (waveVector c.projectileMomentum 1),
      sq_abs (waveVector c.projectileMomentum 2)]
  have hcs : (a + b + d) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - d), sq_nonneg (d - a)]
  have hcap : (a + b + d) ^ 2 ≤ (50880725 / 1000 : ℝ) ^ 2 := by
    linarith [show (3 : ℝ) * (29376 ^ 2 : ℝ) ≤ (50880725 / 1000 : ℝ) ^ 2 by norm_num]
  nlinarith
theorem projLiteralPrepWeight_le_414968_div_1000 (c : Configuration) :
    projLiteralPrepWeight c ≤ lambdaSlot1TpHi := by
  unfold projLiteralPrepWeight lambdaSlot1TpHi
  have hk_le : gridKappa ≤ gridKappaRatHi := gridKappa_le_ratHi
  have hk0 : 0 ≤ gridKappa := gridKappa_nonneg
  have hksq_le : gridKappa ^ 2 / 2 ≤ gridKappaRatHi ^ 2 / 2 := kappaSqHalf_le_ratHi
  have hsum_le : (∑ w : Fin 3, |waveVector c.projectileMomentum w|) ≤ 50880725 / 1000 :=
    sum_abs_stepVector_projectileMomentum_le c
  have hsum0 : 0 ≤ ∑ w : Fin 3, |waveVector c.projectileMomentum w| :=
    Finset.sum_nonneg fun w _ ↦ abs_nonneg _
  have hlin : 127 * gridKappa * (∑ w : Fin 3, |waveVector c.projectileMomentum w|) ≤
      127 * gridKappaRatHi * (50880725 / 1000) := by
    have h1 : gridKappa * (∑ w : Fin 3, |waveVector c.projectileMomentum w|) ≤
        gridKappaRatHi * (50880725 / 1000) :=
      mul_le_mul hk_le hsum_le hsum0 (by unfold gridKappaRatHi; positivity)
    linarith
  have hnum : (48387 / 2 : ℝ) * (gridKappa ^ 2 / 2) +
      127 * gridKappa * (∑ w : Fin 3, |waveVector c.projectileMomentum w|) ≤
      (48387 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2) + 127 * gridKappaRatHi * (50880725 / 1000) := by
    linarith
  have hdiv : ((48387 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2) +
      127 * gridKappaRatHi * (50880725 / 1000)) / projectileMass ≤ 414968 / 1000 := by
    unfold gridKappaRatHi projectileMass
    norm_num
  exact le_trans (div_le_div_of_nonneg_right hnum (by unfold projectileMass; positivity)) hdiv
end LiteralKineticAndMidpoint128
end
end ModLiteralKineticAndMidpoint128

section ModMeasureAndBranchClean
@[expose] public section
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators
namespace QRegExt
open _root_.QRegister
variable {n k m : ℕ}
theorem concat_basisOutcomeProjector_zero (r : QRegister k n) (s : QRegister m n)
    (h : r.DisjointWires s) : (r.concat s h).basisOutcomeProjector 0 = r.basisOutcomeProjector
    0 * s.basisOutcomeProjector 0 :=
  basisOutcomeProjector_concat_zero r s h
end QRegExt
namespace DynCircuitExt
open _root_.DynamicCircuit
variable {Var : Type} {n k m b a : ℕ}
noncomputable def wireZProj (q : QRegister 1 n) (bit : Bool) : Operator (2 ^ n) :=
  q.basisOutcomeProjector (if bit then 1 else 0)
noncomputable def wireXResetKraus (q : QRegister 1 n) (bit : Bool) : Operator (2 ^ n) := if
    bit then (Circuit.X (q 0)).eval.1 * q.basisOutcomeProjector 1 * (Circuit.H (q 0)).eval.1
    else q.basisOutcomeProjector 0 * (Circuit.H (q 0)).eval.1
noncomputable def xResetKraus :
    {b : ℕ} → QRegister b n → (Fin b → Bool) → Operator (2 ^ n)
  | 0, _, _ => 1
  | b + 1, r, f =>
      xResetKraus (r.slice 1 b (by omega)) (Fin.tail f) *
        wireXResetKraus (r.slice 0 1 (by omega)) (f 0)
def measureXResetAndBranch (v : Var) :
    (b : ℕ) → QRegister b n → ((Fin b → Bool) → DynamicCircuit Var n) → DynamicCircuit Var n
  | 0, _, cont => cont finZeroElim
  | b + 1, r, cont =>
      let q := r.slice 0 1 (by omega)
      .seq (.circuit (.H (q 0)))
        (.seq (.measure v q)
          (dynQIfVar v
            (.seq (.circuit (.X (q 0)))
              (measureXResetAndBranch v b (r.slice 1 b (by omega))
                (fun g ↦ cont (Fin.cons true g))))
            (measureXResetAndBranch v b (r.slice 1 b (by omega))
              (fun g ↦ cont (Fin.cons false g)))))
private theorem lemHex22 (w : Wire n) : (Circuit.H w).count .T = 0 := by
  simp [Circuit.count]
private theorem lemHex23 (w : Wire n) : (Circuit.X w).count .T = 0 := by
  simp [Circuit.count]
private theorem lemHex24 (w : Wire n) : (Circuit.H w).count .TOFF = 0 := by
  simp [Circuit.count]
private theorem lemHex25 (w : Wire n) : (Circuit.X w).count .TOFF = 0 := by
  simp [Circuit.count]
theorem count_measureXResetAndBranch_T_le (v : Var) :
    ∀ (b : ℕ) (r : QRegister b n) (cont : (Fin b → Bool) → DynamicCircuit Var n) (B : ℕ),
      (∀ f, (cont f).count .T ≤ B) →
      (measureXResetAndBranch v b r cont).count .T ≤ B
  | 0, _, cont, B, hB => hB finZeroElim
  | b + 1, r, cont, B, hB => by
      have h1 := count_measureXResetAndBranch_T_le v b (r.slice 1 b (by omega))
        (fun g' ↦ cont (Fin.cons true g')) B (fun g' ↦ hB _)
      have h0 := count_measureXResetAndBranch_T_le v b (r.slice 1 b (by omega))
        (fun g' ↦ cont (Fin.cons false g')) B (fun g' ↦ hB _)
      simp only [measureXResetAndBranch, DynamicCircuit.count, lemHex22, lemHex23]
      omega
theorem count_measureXResetAndBranch_TOFF_le (v : Var) :
    ∀ (b : ℕ) (r : QRegister b n) (cont : (Fin b → Bool) → DynamicCircuit Var n) (B : ℕ),
      (∀ f, (cont f).count .TOFF ≤ B) →
      (measureXResetAndBranch v b r cont).count .TOFF ≤ B
  | 0, _, cont, B, hB => hB finZeroElim
  | b + 1, r, cont, B, hB => by
      have h1 := count_measureXResetAndBranch_TOFF_le v b (r.slice 1 b (by omega))
        (fun g' ↦ cont (Fin.cons true g')) B (fun g' ↦ hB _)
      have h0 := count_measureXResetAndBranch_TOFF_le v b (r.slice 1 b (by omega))
        (fun g' ↦ cont (Fin.cons false g')) B (fun g' ↦ hB _)
      simp only [measureXResetAndBranch, DynamicCircuit.count, lemHex24, lemHex25]
      omega
section StoreClosedWP
variable [Finite Var] [DecidableEq Var] [NeZero (2 ^ n)]
omit [Finite Var] in
private theorem lemHex26 (v : Var) (q : QRegister 1 n) {dTrue dFalse : DynamicCircuit Var n}
    {M MTrue MFalse : Observable (Fin (2 ^ n))}
    (hTrue : wp dTrue.compile (fun _ ↦ M) = (fun _ ↦ MTrue))
    (hFalse : wp dFalse.compile (fun _ ↦ M) = (fun _ ↦ MFalse)) : ∃ MOut : Observable (Fin (2 ^ n)),
    wp (DynamicCircuit.seq (.measure v q) (dynQIfVar v dTrue dFalse)).compile (fun _ ↦ M) =
    (fun _ ↦ MOut) ∧ MOut.1.1 = (wireZProj q false)ᴴ * MFalse.1.1 * wireZProj q false +
    (wireZProj q true)ᴴ * MTrue.1.1 * wireZProj q true := by
  let A : Fin (2 ^ 1) → Observable (Fin (2 ^ n)) := fun o ↦ if o.val = 0 then MFalse else MTrue
  refine ⟨qMeasure_obs_map q.computationalBasisMeasurement A, ?_, ?_⟩
  · funext σ
    simp only [compile_seq, compile_measure, compile_qIf, QProg.measureRegister, wp_qSeq, wp_qIf,
      wp_qMeasure_apply, CQAssertionCompat.subst_apply, Store.subst_eq_update, Function.update_self,
      hTrue, hFalse]
    congr 1
    funext o
    fin_cases o <;> simp [A]
  · have h1 : (qMeasure_obs_map q.computationalBasisMeasurement A).1 =
        (MFalse.1.conj (wireZProj q false)ᴴ) + (MTrue.1.conj (wireZProj q true)ᴴ) := by
      rw [qMeasure_obs_map_coe]
      change ∑ o : Fin 2, _ = _
      rw [Fin.sum_univ_two]
      simp [qMeasure_outcome_herm_eq_conj, QRegister.computationalBasisMeasurement_apply,
        wireZProj, A]
    have h2 := congrArg HermitianMat.mat h1
    change (qMeasure_obs_map q.computationalBasisMeasurement A).1.1 =
      (wireZProj q false)ᴴ * MFalse.1.1 * ((wireZProj q false)ᴴ)ᴴ +
        (wireZProj q true)ᴴ * MTrue.1.1 * ((wireZProj q true)ᴴ)ᴴ at h2
    simpa only [Matrix.conjTranspose_conjTranspose] using h2
theorem wp_measureXResetAndBranch_const (v : Var) :
    ∀ (b : ℕ) (r : QRegister b n) (cont : (Fin b → Bool) → DynamicCircuit Var n)
      (M : Observable (Fin (2 ^ n))) (MCont : (Fin b → Bool) → Observable (Fin (2 ^ n))),
      (∀ f, wp (cont f).compile (fun _ ↦ M) = (fun _ ↦ MCont f)) →
      ∃ MOut : Observable (Fin (2 ^ n)),
        wp (measureXResetAndBranch v b r cont).compile (fun _ ↦ M) = (fun _ ↦ MOut) ∧
        MOut.1.1 = ∑ f : Fin b → Bool, (xResetKraus r f)ᴴ * (MCont f).1.1 * xResetKraus r f
  | 0, r, cont, M, MCont, hCont => by
      refine ⟨MCont finZeroElim, hCont finZeroElim, ?_⟩
      let MC : (Fin 0 → Bool) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := fun f ↦ (MCont f).1.1
      change MC finZeroElim = ∑ f : Fin 0 → Bool, (xResetKraus r f)ᴴ * MC f * xResetKraus r f
      have huniv : (Finset.univ : Finset (Fin 0 → Bool)) = {finZeroElim} := by
        ext f
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim f finZeroElim
      rw [huniv, Finset.sum_singleton]
      simp [xResetKraus]
  | b + 1, r, cont, M, MCont, hCont => by
      cases nonempty_fintype Var
      let q := r.slice 0 1 (by omega)
      obtain ⟨M1, h1_wp, h1_mat⟩ := wp_measureXResetAndBranch_const v b (r.slice 1 b (by omega))
        (fun g ↦ cont (Fin.cons true g)) M (fun g ↦ MCont (Fin.cons true g)) (fun g ↦ hCont _)
      obtain ⟨M0, h0_wp, h0_mat⟩ := wp_measureXResetAndBranch_const v b (r.slice 1 b (by omega))
        (fun g ↦ cont (Fin.cons false g)) M (fun g ↦ MCont (Fin.cons false g)) (fun g ↦ hCont _)
      let M1X : Observable (Fin (2 ^ n)) := qAssignObsMap (Circuit.X (q 0)).eval M1
      have h1X_wp : wp (DynamicCircuit.seq (.circuit (.X (q 0)))
          (measureXResetAndBranch v b (r.slice 1 b (by omega))
            (fun g ↦ cont (Fin.cons true g)))).compile (fun _ ↦ M) = (fun _ ↦ M1X) := by
        funext σ
        simp only [compile_seq, compile_circuit, wp_qSeq, h1_wp, wp_circuit_compile_compat,
          wpQAssignCompat, M1X]
      obtain ⟨MMid, hMid_wp, hMid_mat⟩ := lemHex26 v q h1X_wp h0_wp
      let MOut : Observable (Fin (2 ^ n)) := qAssignObsMap (Circuit.H (q 0)).eval MMid
      refine ⟨MOut, ?_, ?_⟩
      · funext σ
        simp only [measureXResetAndBranch, compile_seq, compile_circuit, wp_qSeq,
          wp_circuit_compile_compat, wpQAssignCompat, MOut]
        exact congrArg (qAssignObsMap (Circuit.H (q 0)).eval) (congrFun hMid_wp σ)
      · have hM1X : M1X.1.1 = (Circuit.X (q 0)).eval.1ᴴ * M1.1.1 * (Circuit.X (q 0)).eval.1 := by
          simp [M1X, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
        have hMOut : MOut.1.1 = (Circuit.H (q 0)).eval.1ᴴ * MMid.1.1 * (Circuit.H (q 0)).eval.1 :=
          by
          simp [MOut, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
        rw [hMOut, hMid_mat, hM1X, h0_mat, h1_mat]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul]
        let e : Bool × (Fin b → Bool) ≃ (Fin (b + 1) → Bool) :=
          Fin.consEquiv (fun _ : Fin (b + 1) ↦ Bool)
        rw [← e.sum_comp (fun f ↦ (xResetKraus r f)ᴴ * (MCont f).1.1 * xResetKraus r f),
          Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
        refine congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun g _ ↦ ?_)
          (Finset.sum_congr rfl fun g _ ↦ ?_)
        · simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, xResetKraus, wireXResetKraus, wireZProj,
            ite_true, Fin.cons_zero, Fin.tail_cons,
            Matrix.conjTranspose_mul, Matrix.mul_assoc, q]
        · simp only [e, Fin.consEquiv, Equiv.coe_fn_mk, xResetKraus, wireXResetKraus, wireZProj,
          Bool.false_eq_true, ite_false, Fin.cons_zero, Fin.tail_cons, Matrix.conjTranspose_mul,
          Matrix.mul_assoc, q]
end StoreClosedWP
attribute [irreducible] measureXResetAndBranch
theorem sum_sqrt_half_pow_sq (b : ℕ) :
    (∑ _f : Fin b → Bool, ((√(1 / 2)) ^ b : ℝ) ^ 2) = 1 := by
  have hsq : (((√(1 / 2)) ^ b : ℝ) ^ 2) = (1 / 2 : ℝ) ^ b := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  simp only [hsq, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num
private theorem lemHex27 (q : QRegister 1 n) : QRegister.singleton (q 0) = q := by
  ext i
  fin_cases i
  rfl
noncomputable def localXResetMat (bit : Bool) : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := if bit
    then Qubit.X.1 * compProj (1 : Fin (2 ^ 1)) * Qubit.H.1 else compProj (0 : Fin (2 ^ 1)) *
    Qubit.H.1
theorem wireXResetKraus_eq_embedMatrix (q : QRegister 1 n) (bit : Bool) :
    wireXResetKraus q bit = q.embedMatrix (localXResetMat bit) := by
  have hq : QRegister.singleton (q 0) = q := lemHex27 q
  by_cases h : bit
  · simp only [wireXResetKraus, localXResetMat, h, ite_true, Circuit.X, Circuit.H,
      Circuit.single, Circuit.eval_gate, compat_primGate_X_eq, compat_primGate_H_eq,
        PrimitiveGate.eval,
      hq, QRegister.embedUnitary_val, QRegister.basisOutcomeProjector]
    rw [← q.embedMatrix_mul, ← q.embedMatrix_mul]
  · simp only [wireXResetKraus, localXResetMat, h, Bool.false_eq_true, ite_false, Circuit.H,
      Circuit.single, Circuit.eval_gate, compat_primGate_H_eq, PrimitiveGate.eval,
      hq, QRegister.embedUnitary_val, QRegister.basisOutcomeProjector]
    rw [← q.embedMatrix_mul]
theorem wireXResetKraus_comm_basisOutcomeProjector (q : QRegister 1 n) (rScr : QRegister m n)
    (hdisj : q.DisjointWires rScr) (bit : Bool) (o : Fin (2 ^ m)) : wireXResetKraus q bit *
    rScr.basisOutcomeProjector o = rScr.basisOutcomeProjector o * wireXResetKraus q bit := by
  rw [wireXResetKraus_eq_embedMatrix]
  exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint q rScr hdisj _ o
private theorem lemHex28 {offset width : ℕ} (r : QRegister b n) (rScr : QRegister m n)
    (h : offset + width ≤ b) (hdisj : r.DisjointWires rScr) :
    (r.slice offset width h).DisjointWires rScr := by
  rw [QRegister.disjoint_iff] at hdisj ⊢
  intro i j heq
  exact hdisj ⟨offset + i.val, by omega⟩ j heq
theorem xResetKraus_comm_basisOutcomeProjector :
    ∀ (b : ℕ) (r : QRegister b n) (rScr : QRegister m n),
      r.DisjointWires rScr →
      ∀ (f : Fin b → Bool) (o : Fin (2 ^ m)),
        xResetKraus r f * rScr.basisOutcomeProjector o =
          rScr.basisOutcomeProjector o * xResetKraus r f
  | 0, _, _, _, _, _ => by simp [xResetKraus]
  | b + 1, r, rScr, hdisj, f, o => by
      simp only [xResetKraus]
      have h0 := wireXResetKraus_comm_basisOutcomeProjector (r.slice 0 1 (by omega)) rScr
        (lemHex28 r rScr _ hdisj) (f 0) o
      have h1 := xResetKraus_comm_basisOutcomeProjector b (r.slice 1 b (by omega)) rScr
        (lemHex28 r rScr _ hdisj) (Fin.tail f) o
      rw [Matrix.mul_assoc, h0, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
private theorem lemHex29 (bit : Bool) :
    compProj (0 : Fin (2 ^ 1)) * localXResetMat bit = localXResetMat bit := by
  cases bit
  · have h0 : compProj (0 : Fin 2) * compProj (0 : Fin 2) = compProj (0 : Fin 2) := by
      ext i j
      simp only [compProj, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp
    change compProj (0 : Fin 2) * (compProj (0 : Fin 2) * Qubit.H.1) =
      compProj (0 : Fin 2) * Qubit.H.1
    rw [← Matrix.mul_assoc, h0]
  · have h1 : compProj (0 : Fin 2) * Qubit.X.1 * compProj (1 : Fin 2) =
        Qubit.X.1 * compProj (1 : Fin 2) := by
      ext i j
      simp only [compProj, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp
    change compProj (0 : Fin 2) * (Qubit.X.1 * compProj (1 : Fin 2) * Qubit.H.1) =
      Qubit.X.1 * compProj (1 : Fin 2) * Qubit.H.1
    calc
      compProj (0 : Fin 2) * (Qubit.X.1 * compProj (1 : Fin 2) * Qubit.H.1)
          = (compProj (0 : Fin 2) * Qubit.X.1 * compProj (1 : Fin 2)) * Qubit.H.1 := by
            simp only [Matrix.mul_assoc]
      _ = Qubit.X.1 * compProj (1 : Fin 2) * Qubit.H.1 := by rw [h1]
private theorem lemHex2a (r : QRegister (b + 1) n) : r.basisOutcomeProjector 0 =
    (r.slice 0 1 (by omega)).basisOutcomeProjector 0 *
    (r.slice 1 b (by omega)).basisOutcomeProjector 0 := by
  have hd : (r.slice 0 1 (by omega)).DisjointWires (r.slice 1 b (by omega)) :=
    r.slice_disjoint_of_le 0 1 1 b (by omega) (by omega) (by omega)
  rw [← QRegExt.basisOutcomeProjector_concat_zero _ _ hd,
    QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
  congr 1
  funext g
  have hiff : r.extractIndex g = 0 ↔
      ((r.slice 0 1 (by omega)).concat (r.slice 1 b (by omega)) hd).extractIndex g = 0 := by
    simp only [QRegExt.extractIndex_eq_zero_iff]
    refine ⟨fun hall idx ↦ ?_, fun hall idx ↦ ?_⟩
    · rcases finSumFinEquiv.surjective idx with ⟨i | j, rfl⟩
      · simpa only [finSumFinEquiv_apply_left, QRegister.concat_apply_left, QRegister.slice_apply]
          using hall ⟨0 + i.val, by omega⟩
      · simpa only [finSumFinEquiv_apply_right, QRegister.concat_apply_right, QRegister.slice_apply]
          using hall ⟨1 + j.val, by omega⟩
    · by_cases h0 : idx.val = 0
      · have hk := hall (Fin.castAdd b (0 : Fin 1))
        rw [QRegister.concat_apply_left, QRegister.slice_apply] at hk
        exact (congrArg (fun j ↦ basisBits n g (r.wires j)) (Fin.ext (by
          dsimp
          omega))).trans hk
      · have hk := hall (Fin.natAdd 1 ⟨idx.val - 1, by omega⟩)
        rw [QRegister.concat_apply_right, QRegister.slice_apply] at hk
        simpa only [show (⟨1 + (idx.val - 1), by omega⟩ : Fin (b + 1)) = idx from
          Fin.ext (by
            change 1 + (idx.val - 1) = idx.val
            omega)] using hk
  simp [hiff]
theorem basisOutcomeProjector_zero_mul_xResetKraus :
    ∀ (b : ℕ) (r : QRegister b n) (f : Fin b → Bool),
      r.basisOutcomeProjector 0 * xResetKraus r f = xResetKraus r f
  | 0, r, f => by
      have h0 : r.basisOutcomeProjector 0 = 1 := by
        rw [QRegister.basisOutcomeProjector_eq_diagonal]
        ext i j
        have hsub : Subsingleton (Fin (2 ^ 0)) := by
          change Subsingleton (Fin 1)
          infer_instance
        by_cases hij : i = j
        · subst hij; simp [Subsingleton.elim (r.extractIndex i) 0]
        · simp [hij]
      simp [xResetKraus, h0]
  | b + 1, r, f => by
      let q := r.slice 0 1 (by omega)
      let tail := r.slice 1 b (by omega)
      have hd : q.DisjointWires tail :=
        r.slice_disjoint_of_le 0 1 1 b (by omega) (by omega) (by omega)
      have hcomm : q.basisOutcomeProjector 0 * xResetKraus tail (Fin.tail f) =
          xResetKraus tail (Fin.tail f) * q.basisOutcomeProjector 0 :=
        (xResetKraus_comm_basisOutcomeProjector b tail q hd.symm (Fin.tail f) 0).symm
      have hq0 : q.basisOutcomeProjector 0 * wireXResetKraus q (f 0) = wireXResetKraus q (f 0) := by
        rw [QRegister.basisOutcomeProjector, wireXResetKraus_eq_embedMatrix,
          ← q.embedMatrix_mul, lemHex29]
      calc
        r.basisOutcomeProjector 0 * xResetKraus r f
            = (q.basisOutcomeProjector 0 * tail.basisOutcomeProjector 0) *
                (xResetKraus tail (Fin.tail f) * wireXResetKraus q (f 0)) := by
              rw [lemHex2a]
              rfl
        _ = q.basisOutcomeProjector 0 *
              (tail.basisOutcomeProjector 0 * xResetKraus tail (Fin.tail f)) *
              wireXResetKraus q (f 0) := by simp only [Matrix.mul_assoc]
        _ = (q.basisOutcomeProjector 0 * xResetKraus tail (Fin.tail f)) *
              wireXResetKraus q (f 0) := by
              rw [basisOutcomeProjector_zero_mul_xResetKraus b tail (Fin.tail f)]
        _ = xResetKraus tail (Fin.tail f) *
              (q.basisOutcomeProjector 0 * wireXResetKraus q (f 0)) := by
              rw [hcomm, Matrix.mul_assoc]
        _ = xResetKraus r f := by
              rw [hq0]
              rfl
private theorem lemHex2b : ((√2 : ℂ)⁻¹) = ((√(1 / 2) : ℝ) : ℂ) := by
  have h : (√2 : ℝ)⁻¹ = √(1 / 2) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, one_div]
  exact_mod_cast h
theorem localXResetMat_mulVec_single (bit : Bool) (c : Fin (2 ^ 1)) :
    (localXResetMat bit).mulVec (Pi.single c 1) = ((((√(1 / 2) : ℝ) : ℂ) * if bit && decide
    (basisBits 1 c 0 ≠ 0) then (-1 : ℂ) else 1)) • Pi.single (0 : Fin (2 ^ 1)) 1 := by
  rw [← lemHex2b]
  have hb0 : basisBits 1 (0 : Fin 2) 0 = 0 := by decide
  have hb1 : basisBits 1 (1 : Fin 2) 0 = 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  cases bit <;>
  · ext i
    simp only [localXResetMat, compProj, Qubit.X, Qubit.H, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul]
    fin_cases c <;> fin_cases i <;>
      simp [hb0, hb1, h10, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
private theorem lemHex2c (r : QRegister (b + 1) n) (g : Fin (2 ^ n)) :
    (r.slice 1 b (by omega)).replaceIndex
      ((r.slice 0 1 (by omega)).replaceIndex g 0) 0 = r.replaceIndex g 0 := by
  let q := r.slice 0 1 (by omega)
  let tail := r.slice 1 b (by omega)
  let g₁ := q.replaceIndex g 0
  let g₂ := tail.replaceIndex g₁ 0
  have hin {w₀ : ℕ} (sub : QRegister w₀ n) (g₀ : Fin (2 ^ n)) (i : Fin w₀) :
      basisBits n (sub.replaceIndex g₀ 0) (sub i) = 0 := by
    rw [← sub.basisBits_extractIndex, sub.extractIndex_replaceIndex, basisBits_zero_at]
  have hout {w₀ : ℕ} (sub : QRegister w₀ n) (g₀ : Fin (2 ^ n)) (w : Wire n)
      (hw : w ∉ Set.range sub.wires) :
      basisBits n (sub.replaceIndex g₀ 0) w = basisBits n g₀ w :=
    ((sub.basisSplit_environment_eq_iff _ _).mp (by rw [sub.basisSplitEquiv_replaceIndex])) w hw
  have hbits (w : Wire n) :
      basisBits n g₂ w = if w ∈ Set.range r.wires then 0 else basisBits n g w := by
    by_cases htail : w ∈ Set.range tail.wires
    · rcases htail with ⟨j, rfl⟩
      simp [g₂, hin tail g₁ j,
        show tail.wires j ∈ Set.range r.wires from ⟨⟨1 + j.val, by omega⟩, rfl⟩]
    · rw [show g₂ = tail.replaceIndex g₁ 0 from rfl, hout tail g₁ w htail]
      by_cases hhead : w ∈ Set.range q.wires
      · rcases hhead with ⟨i, rfl⟩
        simp [g₁, hin q g i,
          show q.wires i ∈ Set.range r.wires from ⟨⟨0 + i.val, by omega⟩, rfl⟩]
      · have hnotr : w ∉ Set.range r.wires := by
          rintro ⟨idx, rfl⟩
          by_cases h0 : idx.val = 0
          · exact hhead ⟨0, congrArg r (Fin.ext (by simp [h0]))⟩
          · exact htail ⟨⟨idx.val - 1, by omega⟩, congrArg r (Fin.ext (by
              change 1 + (idx.val - 1) = idx.val
              omega))⟩
        simp [g₁, hout q g w hhead, hnotr]
  refine (r.replaceIndex_eq_of_extractIndex_eq_of_agreeOutside g g₂ 0 ?_ ?_).symm
  · exact ((QRegExt.extractIndex_eq_zero_iff r) g₂).mpr fun idx ↦ by simp [hbits (r idx)]
  · intro w hw
    simp [hbits w, hw]
theorem xResetKraus_mulVec_single :
    ∀ (b : ℕ) (r : QRegister b n) (f : Fin b → Bool) (g : Fin (2 ^ n)),
      (xResetKraus r f).mulVec (Pi.single g 1) =
        ((((√(1 / 2)) ^ b : ℝ) : ℂ) *
          ∏ i : Fin b,
            if f i && decide (basisBits b (r.extractIndex g) i ≠ 0) then (-1 : ℂ) else 1) •
          Pi.single (r.replaceIndex g 0) 1
  | 0, r, f, g => by
      have hsub : Subsingleton (Fin (2 ^ 0)) := by
        change Subsingleton (Fin 1)
        infer_instance
      have hrep : r.replaceIndex g 0 = g := by
        apply r.replaceIndex_eq_of_extractIndex_eq_of_agreeOutside g g 0
        · exact Subsingleton.elim _ _
        · intro _ _; rfl
      rw [xResetKraus, Matrix.one_mulVec, hrep]
      simp
  | b + 1, r, f, g => by
      let q := r.slice 0 1 (by omega)
      let tail := r.slice 1 b (by omega)
      have hhead_vec : (wireXResetKraus q (f 0)).mulVec (Pi.single g 1) = ((((√(1 / 2) : ℝ) :
          ℂ) * if f 0 && decide (basisBits (b + 1) (r.extractIndex g) 0 ≠ 0) then (-1 : ℂ)
          else 1)) • Pi.single (q.replaceIndex g 0) 1 := by
        have hbit0 : basisBits 1 (q.extractIndex g) 0 = basisBits (b + 1) (r.extractIndex g) 0 := by
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
          rfl
        rw [wireXResetKraus_eq_embedMatrix, q.embedMatrix_mulVec_single_factors,
          localXResetMat_mulVec_single, hbit0, q.tensorState_smul_left,
          q.tensorState_single_replaceIndex]
      have htail_bits : ∀ i : Fin b, basisBits b (tail.extractIndex (q.replaceIndex g 0)) i =
          basisBits (b + 1) (r.extractIndex g) i.succ := by
        intro i
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        have hnotq : tail i ∉ Set.range q.wires := by
          rintro ⟨j, hj⟩
          have hd : q.DisjointWires tail :=
            r.slice_disjoint_of_le 0 1 1 b (by omega) (by omega) (by omega)
          exact hd.ne j i hj
        have henv : (q.basisSplitEquiv (q.replaceIndex g 0)).2 = (q.basisSplitEquiv g).2 := by
          rw [q.basisSplitEquiv_replaceIndex]
        have hout := ((q.basisSplit_environment_eq_iff (q.replaceIndex g 0) g).mp henv)
          (tail i) hnotq
        rw [hout]
        exact congrArg (basisBits n g) (congrArg r (Fin.ext (by dsimp; omega)))
      have hih := xResetKraus_mulVec_single b tail (Fin.tail f) (q.replaceIndex g 0)
      have hrep_ht : tail.replaceIndex (q.replaceIndex g 0) 0 = r.replaceIndex g 0 := lemHex2c r g
      change (xResetKraus tail (Fin.tail f) * wireXResetKraus q (f 0)).mulVec (Pi.single g 1) = _
      rw [← Matrix.mulVec_mulVec, hhead_vec, Matrix.mulVec_smul, hih, hrep_ht, smul_smul]
      refine congrArg₂ (· • ·) ?_ rfl
      rw [Fin.prod_univ_succ, pow_succ (√(1 / 2) : ℝ) b]
      push_cast
      have hprod : (∏ i : Fin b, if Fin.tail f i && decide (basisBits b (tail.extractIndex
          (q.replaceIndex g 0)) i ≠ 0) then (-1 : ℂ) else 1) = (∏ i : Fin b, if f i.succ &&
          decide (basisBits (b + 1) (r.extractIndex g) i.succ ≠ 0) then (-1 : ℂ) else 1) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        exact congrArg (fun x ↦ if f i.succ && decide (x ≠ 0) then (-1 : ℂ) else 1) (htail_bits i)
      rw [hprod]
      ring
section CleanWorkspaceBridges
variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
theorem realizesEmbeddedUnitaryWithCleanWorkspace_measureXReset (v : Var)
    (rData : QRegister k n) (rMeas : QRegister b n) (rScr : QRegister m n)
    (hDM : rData.DisjointWires rMeas) (hDS : rData.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr) {uComp : Unitary (2 ^ (k + b))}
    {uTarget : Unitary (2 ^ k)} {uFix : (Fin b → Bool) → Unitary (2 ^ k)}
    {dPre : DynamicCircuit Var n} {cont : (Fin b → Bool) → DynamicCircuit Var n}
    (w : (Fin b → Bool) → ℝ) (hw : (∑ f : Fin b → Bool, (w f) ^ 2) = 1) (hPre :
    RealizesEmbeddedUnitaryWithCleanWorkspace (rData.concat rMeas hDM) rScr uComp dPre) (hCont
    : ∀ f : Fin b → Bool, RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMeas.concat rScr
    hMS) (uFix f) (cont f)) (hBranch : ∀ f : Fin b → Bool, ((rData.embedUnitary (uFix f)).1 *
    xResetKraus rMeas f * ((rData.concat rMeas hDM).embedUnitary uComp).1) * (rMeas.concat
    rScr hMS).basisOutcomeProjector 0 = ((w f : ℂ) • ((rData.embedUnitary uTarget).1 *
    (rMeas.concat rScr hMS).basisOutcomeProjector 0))) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMeas.concat rScr hMS) uTarget
    (DynamicCircuit.seq dPre (measureXResetAndBranch v b rMeas cont)) := by
  have hAS : (rData.concat rMeas hDM).DisjointWires rScr := by
    rw [QRegister.disjoint_iff]
    intro i j heq
    rcases finSumFinEquiv.surjective i with ⟨id | im, rfl⟩
    · simp only [finSumFinEquiv_apply_left, QRegister.concat_apply_left] at heq
      exact hDS.ne id j heq
    · simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right] at heq
      exact hMS.ne im j heq
  intro M
  choose MCont hCont_wp hCont_proj using fun f ↦ hCont f M
  obtain ⟨MMid, hMid_wp, hMid_mat⟩ :=
    wp_measureXResetAndBranch_const v b rMeas cont M MCont hCont_wp
  obtain ⟨M', hPre_wp, hPre_proj⟩ := hPre MMid
  refine ⟨M', ?_, ?_⟩
  · funext σ
    simp only [compile_seq, wp_qSeq, hMid_wp, hPre_wp]
  · let Pm := rMeas.basisOutcomeProjector 0
    let Ps := rScr.basisOutcomeProjector 0
    let Pw := (rMeas.concat rScr hMS).basisOutcomeProjector 0
    have hPw : Pw = Pm * Ps := QRegExt.basisOutcomeProjector_concat_zero rMeas rScr hMS
    have hPs_self : Ps * Ps = Ps := QRegister.basisOutcomeProjector_mul_self rScr 0
    have hPw_adj : Pwᴴ = Pw := QRegister.basisOutcomeProjector_conjTranspose _ 0
    have hcomm_ms : Pm * Ps = Ps * Pm := QRegExt.basisOutcomeProjector_comm rMeas 0 rScr 0
    let UC := ((rData.concat rMeas hDM).embedUnitary uComp).1
    let UT := (rData.embedUnitary uTarget).1
    have hUC_comm : UC * Ps = Ps * UC :=
      QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ rScr hAS uComp.1 0
    have hOuter : Pw * M'.1.1 * Pw = Pw * (UCᴴ * MMid.1.1 * UC) * Pw := by
      have hwrap (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
          Pw * X * Pw = Pm * (Ps * X * Ps) * Pm := by
        calc Pw * X * Pw = (Pm * Ps) * X * (Ps * Pm) :=
              congrArg₂ (· * ·) (congrArg (· * X) hPw) (hPw.trans hcomm_ms)
          _ = Pm * (Ps * X * Ps) * Pm := by simp only [Matrix.mul_assoc]
      rw [hwrap, hPre_proj, ← hwrap]
    have hTerm (f : Fin b → Bool) :
        Pw * (UCᴴ * ((xResetKraus rMeas f)ᴴ * (MCont f).1.1 * xResetKraus rMeas f) * UC) * Pw =
          (((w f : ℝ) ^ 2 : ℝ) : ℂ) • (Pw * (UTᴴ * M.1.1 * UT) * Pw) := by
      let Kf := xResetKraus rMeas f
      let Uf := (rData.embedUnitary (uFix f)).1
      have hClean : Pw * (Kf * UC * Pw) = Kf * UC * Pw := by
        calc Pw * (Kf * UC * Pw)
          _ = Pm * (Ps * Kf) * UC * (Pm * Ps) := by
                rw [hPw]
                simp only [Matrix.mul_assoc]
          _ = (Pm * Kf) * (Ps * UC) * (Pm * Ps) := by
                rw [(xResetKraus_comm_basisOutcomeProjector b rMeas rScr hMS f 0).symm]
                simp only [Matrix.mul_assoc]
                rfl
          _ = Kf * (UC * Ps) * (Pm * Ps) := by
                rw [basisOutcomeProjector_zero_mul_xResetKraus b rMeas f, ← hUC_comm]
          _ = Kf * UC * (Pm * (Ps * Ps)) := by
                have hps : (Ps * Pm) * Ps = Pm * (Ps * Ps) := by
                  rw [← hcomm_ms, Matrix.mul_assoc]
                simpa only [Matrix.mul_assoc] using congrArg (Kf * UC * ·) hps
          _ = Kf * UC * Pw := by rw [hPs_self, ← hPw]
      have hClean_adj : Pw * UCᴴ * Kfᴴ * Pw = Pw * UCᴴ * Kfᴴ := by
        simpa only [Matrix.conjTranspose_mul, hPw_adj, Matrix.mul_assoc] using
          congrArg conjTranspose hClean
      have hProd : Uf * Pw * Kf * UC * Pw = (w f : ℂ) • (UT * Pw) := by
        calc Uf * Pw * Kf * UC * Pw = Uf * (Pw * (Kf * UC * Pw)) := by simp only [Matrix.mul_assoc]
          _ = (Uf * Kf * UC) * Pw := by
                rw [hClean]
                simp only [Matrix.mul_assoc]
          _ = (w f : ℂ) • (UT * Pw) := hBranch f
      have hstar : star (w f : ℂ) = (w f : ℂ) := Complex.conj_ofReal (w f)
      have hProd_adj : Pw * UCᴴ * Kfᴴ * Pw * Ufᴴ = (w f : ℂ) • (Pw * UTᴴ) := by
        simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
          hstar, hPw_adj, Matrix.mul_assoc] using congrArg conjTranspose hProd
      calc Pw * (UCᴴ * (Kfᴴ * (MCont f).1.1 * Kf) * UC) * Pw
        _ = (Pw * UCᴴ * Kfᴴ) * (MCont f).1.1 * (Kf * UC * Pw) := by simp only [Matrix.mul_assoc]
        _ = (Pw * UCᴴ * Kfᴴ * Pw) * (MCont f).1.1 * (Pw * (Kf * UC * Pw)) :=
              congrArg₂ (· * ·) (congrArg₂ (· * ·) hClean_adj.symm rfl) hClean.symm
        _ = (Pw * UCᴴ * Kfᴴ) * (Pw * (MCont f).1.1 * Pw) * (Kf * UC * Pw) := by
              simp only [Matrix.mul_assoc]
        _ = (Pw * UCᴴ * Kfᴴ) * (Pw * (Ufᴴ * M.1.1 * Uf) * Pw) * (Kf * UC * Pw) := by
              rw [hCont_proj f]
        _ = (Pw * UCᴴ * Kfᴴ * Pw * Ufᴴ) * M.1.1 * (Uf * Pw * Kf * UC * Pw) := by
              simp only [Matrix.mul_assoc]
        _ = ((w f : ℂ) • (Pw * UTᴴ)) * M.1.1 * ((w f : ℂ) • (UT * Pw)) := by rw [hProd_adj, hProd]
        _ = (((w f : ℝ) ^ 2 : ℝ) : ℂ) • (Pw * (UTᴴ * M.1.1 * UT) * Pw) := by
              simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
              congr 1
              push_cast
              ring
    rw [hOuter, hMid_mat]
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_congr rfl fun f _ ↦ hTerm f, ← Finset.sum_smul,
      show (∑ f : Fin b → Bool, (((w f : ℝ) ^ 2 : ℝ) : ℂ)) = 1 from by exact_mod_cast hw,
      one_smul]
theorem realizesEmbeddedUnitaryWithCleanWorkspace_measureXReset_uniform (v : Var)
    (rData : QRegister k n) (rMeas : QRegister b n) (rScr : QRegister m n)
    (hDM : rData.DisjointWires rMeas) (hDS : rData.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr) {uComp : Unitary (2 ^ (k + b))}
    {uTarget : Unitary (2 ^ k)} {uFix : (Fin b → Bool) → Unitary (2 ^ k)}
    {dPre : DynamicCircuit Var n} {cont : (Fin b → Bool) → DynamicCircuit Var n} (hPre :
    RealizesEmbeddedUnitaryWithCleanWorkspace (rData.concat rMeas hDM) rScr uComp dPre) (hCont
    : ∀ f : Fin b → Bool, RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMeas.concat rScr
    hMS) (uFix f) (cont f)) (hBranch : ∀ f : Fin b → Bool, ((rData.embedUnitary (uFix f)).1 *
    xResetKraus rMeas f * ((rData.concat rMeas hDM).embedUnitary uComp).1) * (rMeas.concat
    rScr hMS).basisOutcomeProjector 0 = ((((√(1 / 2)) ^ b : ℝ) : ℂ) • ((rData.embedUnitary
    uTarget).1 * (rMeas.concat rScr hMS).basisOutcomeProjector 0))) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMeas.concat rScr hMS) uTarget
    (DynamicCircuit.seq dPre (measureXResetAndBranch v b rMeas cont)) :=
    realizesEmbeddedUnitaryWithCleanWorkspace_measureXReset v rData rMeas rScr hDM hDS hMS
    (fun _ ↦ (√(1 / 2)) ^ b) (sum_sqrt_half_pow_sq b) hPre hCont hBranch
end CleanWorkspaceBridges
end DynCircuitExt
end
end ModMeasureAndBranchClean

end QuantumComputation.Specs.StoppingPowerSolution
