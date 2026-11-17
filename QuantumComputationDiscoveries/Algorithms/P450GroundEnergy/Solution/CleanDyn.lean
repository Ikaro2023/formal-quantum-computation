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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputation.QuantumHoareLogic.CleanAncilla

/-!
# Clean-Ancilla `DynamicCircuit` Composition & Top-Level Bridge

Provides register relocation (`DynamicCircuit.onRegister`), list/iteration combinators
(`DynamicCircuit.sequence`, `DynamicCircuit.replicate`), the compositional clean-ancilla weakest
precondition equality predicate `CleanRealizes`, Toffoli-to-Jones-Toffoli lowering
(`substToffoliWithAncilla`), Gidney temporary-AND compute/middle/uncompute sandwiches
(`CleanRealizes.andSandwich`), and top-level program relocation (`topProg`).
-/

@[expose] public section

open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

namespace QRegister

/-- Computable decidability of `QRegister.DisjointWires` via pairwise wire inequality. -/
instance instDecidableDisjointWires {n k m : ℕ} (r : QRegister k n) (s : QRegister m n) :
    Decidable (r.DisjointWires s) :=
  decidable_of_iff' (∀ i j, r i ≠ s j) QRegister.disjoint_iff

theorem disjointWires_of_image_subset_right {n k m₁ m₂ : ℕ}
    {r : QRegister k n} {s₁ : QRegister m₁ n} {s₂ : QRegister m₂ n}
    (hdisj : r.DisjointWires s₂) (hsub : s₁.image ⊆ s₂.image) :
    r.DisjointWires s₁ := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have hmem : s₁ j ∈ s₂.image := hsub (QRegister.mem_image s₁ (s₁ j) |>.mpr ⟨j, rfl⟩)
  obtain ⟨j₂, hj₂⟩ := QRegister.mem_image s₂ (s₁ j) |>.mp hmem
  exact hdisj.ne i j₂ (heq.trans hj₂.symm)

theorem image_concat {n k m : ℕ} (r : QRegister k n) (s : QRegister m n)
    (h : r.DisjointWires s) :
    (r.concat s h).image = r.image ∪ s.image := by
  ext q
  simp only [QRegister.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨idx, rfl⟩
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
    · exact Or.inl ⟨i, by simp⟩
    · exact Or.inr ⟨j, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, QRegister.concat_apply_left r s h i⟩
    · exact ⟨Fin.natAdd k j, QRegister.concat_apply_right r s h j⟩

theorem disjointWires_concat_right {n k m₁ m₂ : ℕ}
    {r : QRegister k n} {s₁ : QRegister m₁ n} {s₂ : QRegister m₂ n}
    (hs : s₁.DisjointWires s₂) (h₁ : r.DisjointWires s₁) (h₂ : r.DisjointWires s₂) :
    r.DisjointWires (s₁.concat s₂ hs) := by
  rw [QRegister.disjoint_iff]
  intro i idx
  obtain ⟨j₁ | j₂, rfl⟩ := finSumFinEquiv.surjective idx
  · simpa using h₁.ne i j₁
  · simpa using h₂.ne i j₂

theorem disjointWires_concat_left {n k₁ k₂ m : ℕ}
    {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n} {s : QRegister m n}
    (hr : r₁.DisjointWires r₂) (h₁ : r₁.DisjointWires s) (h₂ : r₂.DisjointWires s) :
    (r₁.concat r₂ hr).DisjointWires s :=
  QRegister.disjoint_comm.mp
    (disjointWires_concat_right hr (QRegister.disjoint_comm.mp h₁) (QRegister.disjoint_comm.mp h₂))

end QRegister

namespace DynamicCircuit

variable {Var : Type}

/-- Relocate an `m`-wire dynamic circuit onto an ordered `m`-wire register inside `n` wires. -/
def onRegister {m n : ℕ} (placement : QRegister m n) :
    DynamicCircuit Var m → DynamicCircuit Var n :=
  DynamicCircuit.qcFold
    (fun c ↦ .circuit (c.onRegister placement))
    (fun v r ↦ .measure v (placement.compose r))
    DynamicCircuit.qcRawQIf
    .seq

@[simp]
theorem onRegister_circuit {m n : ℕ} (placement : QRegister m n) (c : Circuit m) :
    (DynamicCircuit.circuit c : DynamicCircuit Var m).onRegister placement =
      .circuit (c.onRegister placement) :=
  DynamicCircuit.qcFold_circuit _ _ _ _ c

@[simp]
theorem onRegister_identity {m n : ℕ} (placement : QRegister m n) :
    (identity : DynamicCircuit Var m).onRegister placement = .identity :=
  onRegister_circuit placement .identity

@[simp]
theorem onRegister_measure {m n : ℕ} (placement : QRegister m n) (v : Var) (r : QRegister 1 m) :
    (DynamicCircuit.measure v r).onRegister placement = .measure v (placement.compose r) :=
  DynamicCircuit.qcFold_measure _ _ _ _ v r

@[simp]
theorem onRegister_qIf {m n : ℕ} (placement : QRegister m n) (cond : QCRawGuard Var)
    (t f : DynamicCircuit Var m) :
    (DynamicCircuit.qcRawQIf cond t f).onRegister placement =
      DynamicCircuit.qcRawQIf cond (t.onRegister placement) (f.onRegister placement) :=
  DynamicCircuit.qcFold_qIf _ _ _ _ cond t f

@[simp]
theorem onRegister_seq {m n : ℕ} (placement : QRegister m n)
    (p₁ p₂ : DynamicCircuit Var m) :
    (DynamicCircuit.seq p₁ p₂).onRegister placement =
      .seq (p₁.onRegister placement) (p₂.onRegister placement) :=
  DynamicCircuit.qcFold_seq _ _ _ _ p₁ p₂

@[simp]
theorem onRegister_whole {n : ℕ} (p : DynamicCircuit Var n) :
    p.onRegister (QRegister.whole n) = p := by
  induction p using DynamicCircuit.qcInd <;> simp_all

@[simp]
theorem onRegister_compose {ℓ m n : ℕ} (outer : QRegister m n) (inner : QRegister ℓ m)
    (p : DynamicCircuit Var ℓ) :
    (p.onRegister inner).onRegister outer = p.onRegister (outer.compose inner) := by
  induction p using DynamicCircuit.qcInd <;> simp_all

/-- Relocating an `m`-wire dynamic circuit onto `placement` preserves every primitive gate count. -/
@[simp]
theorem count_onRegister {m n a : ℕ} (g : PrimitiveGate a) (placement : QRegister m n)
    (p : DynamicCircuit Var m) :
    (p.onRegister placement).count g = p.count g := by
  induction p using DynamicCircuit.qcInd with
  | circuit c => simp
  | measure _ _ => simp
  | qIf _ t f iht ihf => simp [iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ => simp [ih₁, ih₂]

theorem circuit_support_onRegister_subset {m n : ℕ} (placement : QRegister m n)
    (c : Circuit m) :
    (c.onRegister placement).support ⊆ placement.image := by
  induction c with
  | identity => simp
  | gate _ r => exact QRegister.image_compose_subset placement r
  | seq c₁ c₂ ih₁ ih₂ => exact Finset.union_subset ih₁ ih₂

/-- Syntactic support of `p.onRegister placement` lies inside `placement.image`. -/
theorem support_onRegister_subset {m n : ℕ} (placement : QRegister m n)
    (p : DynamicCircuit Var m) :
    (p.onRegister placement).support ⊆ placement.image := by
  induction p using DynamicCircuit.qcInd with
  | circuit c => simpa using circuit_support_onRegister_subset placement c
  | measure _ r => simpa using QRegister.image_compose_subset placement r
  | qIf _ _ _ iht ihf => simpa using Finset.union_subset iht ihf
  | seq _ _ ih₁ ih₂ => simpa using Finset.union_subset ih₁ ih₂

end DynamicCircuit

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn
open QuantumComputation.Specs QuantumComputation.Specs.P450

/-! ## Forward Observable Embedding & Environment-Isometry Pullback for `wp_onRegister` -/

theorem embedMatrix_sub {m n : ℕ} (r : QRegister m n)
    (A B : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  ext i j
  simp only [QRegister.embedMatrix_apply, Matrix.sub_apply]
  split_ifs <;> ring

theorem embedMatrix_posSemidef {m n : ℕ} (r : QRegister m n)
    {A : Operator (2 ^ m)} (hA : A.PosSemidef) :
    (r.embedMatrix A).PosSemidef := by
  unfold QRegister.embedMatrix
  have h1 : (1 : Matrix (r.Environment → ZMod 2) (r.Environment → ZMod 2) ℂ).PosSemidef :=
    Matrix.PosSemidef.one
  exact (Matrix.PosSemidef.kronecker hA h1).submatrix ⇑r.basisSplitEquiv

theorem embedObservable_herm {m n : ℕ} (r : QRegister m n) (M : Observable (Fin (2 ^ m))) :
    (r.embedMatrix M.1.mat).IsHermitian := by
  change (r.embedMatrix M.1.mat)ᴴ = r.embedMatrix M.1.mat
  rw [← r.embedMatrix_conjTranspose]
  exact congrArg r.embedMatrix M.1.prop

theorem embedObservable_mem {m n : ℕ} (r : QRegister m n) (M : Observable (Fin (2 ^ m))) :
    0 ≤ (⟨r.embedMatrix M.1.mat, embedObservable_herm r M⟩ : HermitianMat (Fin (2 ^ n)) ℂ) ∧
      (⟨r.embedMatrix M.1.mat, embedObservable_herm r M⟩ : HermitianMat (Fin (2 ^ n)) ℂ) ≤ 1 := by
  constructor
  · exact HermitianMat.zero_le_iff.mpr
      (embedMatrix_posSemidef r (HermitianMat.zero_le_iff.mp M.2.1))
  · apply HermitianMat.le_iff.mpr
    change (1 - r.embedMatrix M.1.mat).PosSemidef
    rw [← r.embedMatrix_one, ← embedMatrix_sub]
    exact embedMatrix_posSemidef r (HermitianMat.le_iff.mp M.2.2)

/-- Embed an `m`-qubit observable into an `n`-qubit system via `r.embedMatrix`. -/
noncomputable def embedObservable {m n : ℕ} (r : QRegister m n)
    (M : Observable (Fin (2 ^ m))) : Observable (Fin (2 ^ n)) :=
  ⟨⟨r.embedMatrix M.1.mat, embedObservable_herm r M⟩, embedObservable_mem r M⟩

@[simp]
theorem embedObservable_mat {m n : ℕ} (r : QRegister m n) (M : Observable (Fin (2 ^ m))) :
    (embedObservable r M).1.mat = r.embedMatrix M.1.mat := rfl

@[simp]
theorem compose_basisOutcomeProjector {a b n : ℕ}
    (r₁ : QRegister b n) (r₂ : QRegister a b) (o : Fin (2 ^ a)) :
    (r₁.compose r₂).basisOutcomeProjector o = r₁.embedMatrix (r₂.basisOutcomeProjector o) := by
  rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
    QRegister.embedMatrix_compose]

private theorem wp_measure_coe {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (q : QRegister 1 n) (A : QCAssertion Var (2 ^ n))
    (σ : Store Var) :
    (wp (DynamicCircuit.measure v q).compile A σ).1 =
      ∑ o : Fin 2,
        (A (Store.subst σ v (Int.ofNat o.val))).1.conj (q.basisOutcomeProjector o)ᴴ := by
  have := Fintype.ofFinite Var
  rw [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
    qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe]
  simp [qc_qMeasure_outcome_herm_eq_conj]

/-- Partial-isometry matrix fixing environment state `φ` around `placement : QRegister m N`. -/
noncomputable def envIso {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ) :
    Matrix (Fin (2 ^ N)) (Fin (2 ^ m)) ℂ :=
  fun g x ↦ placement.tensorState (Pi.single x 1) φ g

private theorem envIso_mulVec_single {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ) (x : Fin (2 ^ m)) :
    (envIso placement φ).mulVec (Pi.single x 1) = placement.tensorState (Pi.single x 1) φ := by
  funext g
  simp [envIso]

private theorem envIso_mulVec {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ) (v : Fin (2 ^ m) → ℂ) :
    (envIso placement φ).mulVec v = placement.tensorState v φ := by
  funext g
  simp only [Matrix.mulVec, dotProduct, envIso, QRegister.tensorState, Pi.single_apply]
  have hsum :
      (∑ x : Fin (2 ^ m),
        ((if placement.extractIndex g = x then (1 : ℂ) else 0) *
          φ (placement.basisSplitEquiv g).2) * v x) =
      ∑ x : Fin (2 ^ m),
        if placement.extractIndex g = x then v x * φ (placement.basisSplitEquiv g).2 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : placement.extractIndex g = x <;> simp [hx, mul_comm]
  rw [hsum, Finset.sum_ite_eq]
  simp

theorem embedMatrix_mul_envIso {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    placement.embedMatrix K * envIso placement φ = envIso placement φ * K := by
  ext g x
  have h : ((placement.embedMatrix K * envIso placement φ).mulVec (Pi.single x 1)) g =
      ((envIso placement φ * K).mulVec (Pi.single x 1)) g := by
    rw [← Matrix.mulVec_mulVec, envIso_mulVec_single, placement.embedMatrix_mulVec_tensorState,
      ← Matrix.mulVec_mulVec, envIso_mulVec]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem envIso_conjTranspose_mul_self {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ) :
    (envIso placement φ)ᴴ * envIso placement φ =
      (∑ e, (Complex.normSq (φ e) : ℂ)) • (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, envIso, QRegister.tensorState,
    Pi.single_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  let f : Fin (2 ^ N) → ℂ := fun g ↦
    star ((if placement.extractIndex g = x then (1 : ℂ) else 0) *
        φ (placement.basisSplitEquiv g).2) *
      ((if placement.extractIndex g = y then (1 : ℂ) else 0) *
        φ (placement.basisSplitEquiv g).2)
  change ∑ g, f g = _
  rw [← placement.basisSplitEquiv.symm.sum_comp f, Fintype.sum_prod_type]
  have hf (z : Fin (2 ^ m)) (e : placement.Environment → ZMod 2) :
      f (placement.basisSplitEquiv.symm (z, e)) =
        (if z = x ∧ z = y then (1 : ℂ) else 0) * (Complex.normSq (φ e) : ℂ) := by
    have hz : placement.extractIndex (placement.basisSplitEquiv.symm (z, e)) = z := by
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    have he : (placement.basisSplitEquiv (placement.basisSplitEquiv.symm (z, e))).2 = e := by
      rw [Equiv.apply_symm_apply]
    simp only [f, hz, he]
    rcases eq_or_ne z x with rfl | hzx
    · by_cases hzy : z = y <;> simp [hzy, Complex.mul_conj, mul_comm]
    · simp [hzx]
  simp_rw [hf, ← Finset.mul_sum]
  by_cases hxy : x = y
  · subst hxy
    simp [mul_comm]
  · have hzero (z : Fin (2 ^ m)) : (if z = x ∧ z = y then (1 : ℂ) else 0) = 0 := by
      by_cases hzx : z = x <;> simp [hzx, hxy]
    simp [hzero, hxy]

theorem envIso_conj_le_one {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1) :
    (envIso placement φ)ᴴ * ((envIso placement φ)ᴴ)ᴴ ≤ 1 := by
  rw [conjTranspose_conjTranspose, envIso_conjTranspose_mul_self]
  change ((1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) -
    ((∑ e, (Complex.normSq (φ e) : ℂ)) • 1)).PosSemidef
  have hsub : (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) -
      (∑ e, (Complex.normSq (φ e) : ℂ)) • 1 =
      Matrix.diagonal (fun _ ↦ ((1 - ∑ e, Complex.normSq (φ e) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hsub, Matrix.posSemidef_diagonal_iff]
  intro _
  rw [Complex.nonneg_iff]
  exact ⟨by simp [sub_nonneg.mpr hφ], by simp⟩

/-- Pull back a global `N`-qubit observable to `m` qubits via `(envIso placement φ)ᴴ`. -/
noncomputable def pullbackObs {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1)
    (M : Observable (Fin (2 ^ N))) : Observable (Fin (2 ^ m)) :=
  ⟨M.1.conj (envIso placement φ)ᴴ, M.1.conj_nonneg _ M.2.1,
    (HermitianMat.conj_mono M.2.2).trans
      (HermitianMat.conj_one_le_one (envIso placement φ)ᴴ (envIso_conj_le_one placement φ hφ))⟩

@[simp]
theorem pullbackObs_coe {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1)
    (M : Observable (Fin (2 ^ N))) :
    (pullbackObs placement φ hφ M).1 = M.1.conj (envIso placement φ)ᴴ := rfl

/-- Pull back a global `QCAssertion` branchwise to `m` qubits via `pullbackObs`. -/
noncomputable def pullbackAssertion {Var : Type} [Fintype Var] {m N : ℕ}
    (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1)
    (Θ : QCAssertion Var (2 ^ N)) : QCAssertion Var (2 ^ m) :=
  fun σ ↦ pullbackObs placement φ hφ (Θ σ)

private theorem conjTranspose_embedMatrix_mul {m N : ℕ} (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (K : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    (envIso placement φ)ᴴ * (placement.embedMatrix K)ᴴ =
      Kᴴ * (envIso placement φ)ᴴ := by
  have h := congrArg conjTranspose (embedMatrix_mul_envIso placement φ K)
  simpa only [conjTranspose_mul] using h

/-- Exact `wp` pullback through `DynamicCircuit.onRegister` for any subnormalized environment
`φ`. -/
theorem pullbackAssertion_wp_onRegister {Var : Type} [Fintype Var] [DecidableEq Var]
    {m N : ℕ} [NeZero (2 ^ m)] [NeZero (2 ^ N)]
    (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1)
    (p : DynamicCircuit Var m) (Θ : QCAssertion Var (2 ^ N)) :
    pullbackAssertion placement φ hφ (wp (p.onRegister placement).compile Θ) =
      wp p.compile (pullbackAssertion placement φ hφ Θ) := by
  induction p using DynamicCircuit.qcInd generalizing Θ with
  | circuit c =>
      funext σ
      apply Subtype.ext
      simp only [pullbackAssertion, pullbackObs_coe,
        DynamicCircuit.onRegister_circuit, DynamicCircuit.compile_circuit,
        DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, Circuit.eval_onRegister,
        QRegister.embedUnitary_val, conj_conj, conjTranspose_embedMatrix_mul]
  | measure v q =>
      funext σ
      apply Subtype.ext
      simp only [DynamicCircuit.onRegister_measure, pullbackAssertion, pullbackObs_coe,
        wp_measure_coe, map_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [conj_conj, conj_conj, compose_basisOutcomeProjector, conjTranspose_embedMatrix_mul]
  | qIf cond tb fb iht ihf =>
      funext σ
      simp only [DynamicCircuit.onRegister_qIf, DynamicCircuit.compile_qcRawQIf, wp_qcRawQIf,
        pullbackAssertion]
      by_cases h : cond.holds σ <;> simp [h, ← iht, ← ihf, pullbackAssertion]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.onRegister_seq, DynamicCircuit.compile_seq, wp_qSeq]
      rw [ih₁, ih₂]

theorem pullbackAssertion_restrict {Var : Type} [Fintype Var] {m N s : ℕ}
    (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1)
    (rScr : QRegister s m) (Θ : QCAssertion Var (2 ^ N)) :
    pullbackAssertion placement φ hφ
        (restrictAssertionToZeroAncilla Θ (placement.compose rScr)) =
      restrictAssertionToZeroAncilla (pullbackAssertion placement φ hφ Θ) rScr := by
  funext σ
  apply Subtype.ext
  have hcomm := conjTranspose_embedMatrix_mul placement φ (rScr.basisOutcomeProjector 0)
  rw [← placement.embedMatrix_conjTranspose,
    QRegister.basisOutcomeProjector_conjTranspose] at hcomm
  simp only [pullbackAssertion, pullbackObs_coe, restrictAssertionToZeroAncilla_coe,
    conj_conj, compose_basisOutcomeProjector, hcomm]

theorem pullbackAssertion_wp_qAssign {Var : Type} [Fintype Var] {m N k : ℕ}
    (placement : QRegister m N)
    (φ : (placement.Environment → ZMod 2) → ℂ)
    (hφ : ∑ e, Complex.normSq (φ e) ≤ 1)
    (rAct : QRegister k m) (U : Unitary (2 ^ k)) (Θ : QCAssertion Var (2 ^ N)) :
    pullbackAssertion placement φ hφ
        (qcWpQAssign ((placement.compose rAct).embedUnitary U) Θ) =
      qcWpQAssign (rAct.embedUnitary U) (pullbackAssertion placement φ hφ Θ) := by
  funext σ
  apply Subtype.ext
  have hcomm := conjTranspose_embedMatrix_mul placement φ (rAct.embedUnitary U).1
  have hemb : ((placement.compose rAct).embedUnitary U).1 =
      placement.embedMatrix (rAct.embedUnitary U).1 := by
    rw [QRegister.embedUnitary_compose]; rfl
  simp only [pullbackAssertion, pullbackObs_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hemb, hcomm]

private theorem envIso_apply_single_env {m N : ℕ} (placement : QRegister m N)
    (e : placement.Environment → ZMod 2) (g : Fin (2 ^ N)) (x : Fin (2 ^ m)) :
    envIso placement (Pi.single e 1) g x =
      if g = placement.basisSplitEquiv.symm (x, e) then 1 else 0 := by
  have hf := congrFun (placement.tensorState_single_factors
    (placement.basisSplitEquiv.symm (x, e))) g
  have hx : placement.extractIndex (placement.basisSplitEquiv.symm (x, e)) = x := by
    rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have he : (placement.basisSplitEquiv (placement.basisSplitEquiv.symm (x, e))).2 = e := by
    rw [Equiv.apply_symm_apply]
  rw [hx, he] at hf
  simpa only [envIso, Pi.single_apply, eq_comm] using hf

private theorem envIso_conj_single_apply {m N : ℕ} (placement : QRegister m N)
    (D : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ)
    (e₁ e₂ : placement.Environment → ZMod 2) (x₁ x₂ : Fin (2 ^ m)) :
    ((envIso placement (Pi.single e₁ 1))ᴴ * D * envIso placement (Pi.single e₂ 1)) x₁ x₂ =
      D (placement.basisSplitEquiv.symm (x₁, e₁)) (placement.basisSplitEquiv.symm (x₂, e₂)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, envIso_apply_single_env]
  simp

private theorem normSq_single_le_one {α : Type*} [Fintype α] [DecidableEq α] (e : α) :
    ∑ a : α, Complex.normSq ((Pi.single e (1 : ℂ) : α → ℂ) a) ≤ 1 := by
  have h : (∑ a : α, Complex.normSq ((Pi.single e (1 : ℂ) : α → ℂ) a)) = 1 := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro a _ ha; simp [ha]
    · simp
  linarith

private theorem normSq_half_pair_le_one {α : Type*} [Fintype α] [DecidableEq α]
    {e₁ e₂ : α} (hne : e₁ ≠ e₂) (c : ℂ) (hc : Complex.normSq c = 1) :
    ∑ a : α, Complex.normSq
      (((1 / 2 : ℂ) • (Pi.single e₁ (1 : ℂ) + c • Pi.single e₂ (1 : ℂ)) : α → ℂ) a) ≤ 1 := by
  let v : α → ℂ := (1 / 2 : ℂ) • (Pi.single e₁ (1 : ℂ) + c • Pi.single e₂ (1 : ℂ))
  change ∑ a : α, Complex.normSq (v a) ≤ 1
  have h : (∑ a : α, Complex.normSq (v a)) = 1 / 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₁)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ e₂⟩)]
    have hrest : ∑ a ∈ (Finset.univ.erase e₁).erase e₂, Complex.normSq (v a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have ha₂ : a ≠ e₂ := (Finset.mem_erase.mp ha).1
      have ha₁ : a ≠ e₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
      simp [v, ha₁, ha₂]
    have hv₁ : v e₁ = 1 / 2 := by simp [v, hne]
    have hv₂ : v e₂ = (1 / 2 : ℂ) * c := by simp [v, hne.symm]
    rw [hrest, add_zero, hv₁, hv₂]
    simp [hc]
    norm_num
  linarith

private theorem envIso_add {m N : ℕ} (placement : QRegister m N)
    (φ₁ φ₂ : (placement.Environment → ZMod 2) → ℂ) :
    envIso placement (φ₁ + φ₂) = envIso placement φ₁ + envIso placement φ₂ := by
  ext g x
  simp [envIso, QRegister.tensorState, mul_add]

private theorem envIso_smul {m N : ℕ} (placement : QRegister m N) (c : ℂ)
    (φ : (placement.Environment → ZMod 2) → ℂ) :
    envIso placement (c • φ) = c • envIso placement φ := by
  ext g x
  simp [envIso, QRegister.tensorState, mul_left_comm]

/-- Polarization: two `QCAssertion`s on `N` qubits agree iff all their `pullbackAssertion`s
agree. -/
theorem cqAssertion_eq_of_pullbackAssertion_eq {Var : Type} [Fintype Var] {m N : ℕ}
    (placement : QRegister m N) (Θ₁ Θ₂ : QCAssertion Var (2 ^ N))
    (h : ∀ (φ : (placement.Environment → ZMod 2) → ℂ) (hφ : ∑ e, Complex.normSq (φ e) ≤ 1),
      pullbackAssertion placement φ hφ Θ₁ = pullbackAssertion placement φ hφ Θ₂) :
    Θ₁ = Θ₂ := by
  classical
  funext σ
  apply Subtype.ext; ext1
  ext g₁ g₂
  let D : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ := (Θ₁ σ).1.mat - (Θ₂ σ).1.mat
  suffices hD : D g₁ g₂ = 0 from sub_eq_zero.mp hD
  have hzero : ∀ (φ : (placement.Environment → ZMod 2) → ℂ),
      ∑ e, Complex.normSq (φ e) ≤ 1 →
      (envIso placement φ)ᴴ * D * envIso placement φ = 0 := by
    intro φ hφ
    have hσ := congrArg (fun A : QCAssertion Var (2 ^ m) ↦ (A σ).1.mat) (h φ hφ)
    simp only [pullbackAssertion, pullbackObs_coe, conj_apply_mat,
      conjTranspose_conjTranspose] at hσ
    dsimp [D]
    rw [Matrix.mul_sub, Matrix.sub_mul, hσ, sub_self]
  obtain ⟨⟨x₁, e₁⟩, hg₁⟩ := placement.basisSplitEquiv.symm.surjective g₁
  obtain ⟨⟨x₂, e₂⟩, hg₂⟩ := placement.basisSplitEquiv.symm.surjective g₂
  subst hg₁ hg₂
  have hdiag (e : placement.Environment → ZMod 2) :
      (envIso placement (Pi.single e 1))ᴴ * D * envIso placement (Pi.single e 1) = 0 :=
    hzero (Pi.single e 1) (normSq_single_le_one e)
  by_cases he : e₁ = e₂
  · subst he
    rw [← envIso_conj_single_apply placement D e₁ e₁ x₁ x₂, hdiag e₁, Matrix.zero_apply]
  · let E₁ := envIso placement (Pi.single e₁ 1)
    let E₂ := envIso placement (Pi.single e₂ 1)
    have hpair (c : ℂ) (hc : Complex.normSq c = 1) :
        c • (E₁ᴴ * D * E₂) + star c • (E₂ᴴ * D * E₁) = 0 := by
      have hp := hzero ((1 / 2 : ℂ) • (Pi.single e₁ 1 + c • Pi.single e₂ 1))
        (normSq_half_pair_le_one he c hc)
      rw [envIso_smul, envIso_add, envIso_smul] at hp
      have hexp :
          ((1 / 2 : ℂ) • (E₁ + c • E₂))ᴴ * D * ((1 / 2 : ℂ) • (E₁ + c • E₂)) =
            (1 / 4 : ℂ) • (E₁ᴴ * D * E₁ + star c • (c • (E₂ᴴ * D * E₂)) +
              (c • (E₁ᴴ * D * E₂) + star c • (E₂ᴴ * D * E₁))) := by
        simp only [conjTranspose_smul, conjTranspose_add, star_mul, star_div₀, star_one, star_ofNat,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, smul_add, smul_smul]
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hexp, hdiag e₁, hdiag e₂, smul_zero, smul_zero, add_zero, zero_add] at hp
      have h4 := congrArg ((4 : ℂ) • ·) hp
      simpa [smul_smul] using h4
    have h1 := congrArg (fun M ↦ M x₁ x₂) (hpair 1 (by simp))
    have hI := congrArg (fun M ↦ M x₁ x₂) (hpair Complex.I (by simp))
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
      star_one, Complex.star_def, Complex.conj_I] at h1 hI
    have hentry : (E₁ᴴ * D * E₂) x₁ x₂ = 0 := by
      have hcalc : (E₁ᴴ * D * E₂) x₁ x₂ =
          (1 / 2 : ℂ) * (1 * (E₁ᴴ * D * E₂) x₁ x₂ + 1 * (E₂ᴴ * D * E₁) x₁ x₂) -
            (Complex.I / 2) * (Complex.I * (E₁ᴴ * D * E₂) x₁ x₂ +
              -Complex.I * (E₂ᴴ * D * E₁) x₁ x₂) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [hcalc, h1, hI]
      ring
    rwa [← envIso_conj_single_apply placement D e₁ e₂ x₁ x₂]

/-! ## `CleanRealizes` & Automatic Postcondition-Restriction Lemma -/

/-- Exact clean-ancilla weakest-precondition realization predicate for `DynamicCircuit`:
1. `P` contains zero `.TOFF` gates.
2. `wp P.compile` preserves `v`-update invariance of assertions.
3. On `v`-invariant assertions, restricting `wp P.compile Θ` to `|0^s⟩` on `rScr` equals
   restricting `wp_qAssign (rAct.embedUnitary U) Θ` to `|0^s⟩` on `rScr`.
4. Restricting the postcondition `Θ` to `|0^s⟩` on `rScr` leaves the `rScr`-restricted `wp`
   unchanged for all assertions `Θ`. -/
def CleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    restrictAssertionToZeroAncilla (wp P.compile Θ) rScr =
      restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr) ∧
  (∀ Θ : QCAssertion Var (2 ^ N),
    restrictAssertionToZeroAncilla (wp P.compile (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr)

/-- Positive ℝ-linear lift of `wp p.compile` to unrestricted `HermitianMat` families. -/
private noncomputable def wpHerm {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} :
    DynamicCircuit Var n →
    (Store Var → HermitianMat (Fin (2 ^ n)) ℂ) →
    (Store Var → HermitianMat (Fin (2 ^ n)) ℂ) :=
  DynamicCircuit.qcRec
    (fun c A σ ↦ (A σ).conj c.eval.1ᴴ)
    (fun x r A σ ↦
      ∑ o : Fin 2, (A (Store.subst σ x (Int.ofNat o.val))).conj (r.basisOutcomeProjector o)ᴴ)
    (fun b _ _ iht ihf A σ ↦ if b.holds σ then iht A σ else ihf A σ)
    (fun _ _ ih₁ ih₂ A σ ↦ ih₁ (ih₂ A) σ)

@[simp]
private theorem wpHerm_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (c : Circuit n) (A : Store Var → HermitianMat (Fin (2 ^ n)) ℂ) (σ : Store Var) :
    wpHerm (.circuit c) A σ = (A σ).conj c.eval.1ᴴ := rfl

@[simp]
private theorem wpHerm_measure {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (x : Var) (r : QRegister 1 n) (A : Store Var → HermitianMat (Fin (2 ^ n)) ℂ)
    (σ : Store Var) :
    wpHerm (.measure x r) A σ =
      ∑ o : Fin 2,
        (A (Store.subst σ x (Int.ofNat o.val))).conj (r.basisOutcomeProjector o)ᴴ := rfl

@[simp]
private theorem wpHerm_qIf {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (b : QCRawGuard Var) (t f : DynamicCircuit Var n)
    (A : Store Var → HermitianMat (Fin (2 ^ n)) ℂ) (σ : Store Var) :
    wpHerm (DynamicCircuit.qcRawQIf b t f) A σ =
      if b.holds σ then wpHerm t A σ else wpHerm f A σ := rfl

@[simp]
private theorem wpHerm_seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (p₁ p₂ : DynamicCircuit Var n) (A : Store Var → HermitianMat (Fin (2 ^ n)) ℂ)
    (σ : Store Var) :
    wpHerm (.seq p₁ p₂) A σ = wpHerm p₁ (wpHerm p₂ A) σ := rfl

private theorem wpHerm_eq_wp {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (p : DynamicCircuit Var n) (Θ : QCAssertion Var (2 ^ n)) :
    wpHerm p (fun σ ↦ (Θ σ).1) = fun σ ↦ (wp p.compile Θ σ).1 := by
  induction p using DynamicCircuit.qcInd generalizing Θ with
  | circuit c =>
      funext σ
      simp [qcWpQAssign, qcQAssignObsMap, Matrix.star_eq_conjTranspose]
  | measure x r =>
      funext σ
      rw [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
        qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe]
      simp [qc_qMeasure_outcome_herm_eq_conj]
  | qIf b t f iht ihf =>
      funext σ
      by_cases hb : b.holds σ <;> simp [hb, congrFun (iht Θ) σ, congrFun (ihf Θ) σ]
  | seq p₁ p₂ ih₁ ih₂ =>
      funext σ
      change wpHerm p₁ (wpHerm p₂ (fun σ' ↦ (Θ σ').1)) σ =
        (wp p₁.compile (wp p₂.compile Θ) σ).1
      rw [ih₂, ih₁]

private theorem wpHerm_add {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (p : DynamicCircuit Var n) (A B : Store Var → HermitianMat (Fin (2 ^ n)) ℂ) :
    wpHerm p (A + B) = wpHerm p A + wpHerm p B := by
  induction p using DynamicCircuit.qcInd generalizing A B with
  | circuit c => funext σ; simp [map_add]
  | measure x r => funext σ; simp [map_add, Finset.sum_add_distrib]
  | qIf b t f iht ihf =>
      funext σ
      by_cases hb : b.holds σ <;> simp [hb, congrFun (iht A B) σ, congrFun (ihf A B) σ]
  | seq p₁ p₂ ih₁ ih₂ => funext σ; simp [ih₂, ih₁]

private theorem herm_conj_add {d : ℕ} (B : Operator d)
    (H₁ H₂ : HermitianMat (Fin d) ℂ) :
    (H₁ + H₂).conj B = H₁.conj B + H₂.conj B := by
  ext1
  simp only [HermitianMat.mat_add, conj_apply_mat]
  rw [Matrix.mul_add, Matrix.add_mul]

private theorem herm_conj_sub {d : ℕ} (B : Operator d)
    (H₁ H₂ : HermitianMat (Fin d) ℂ) :
    (H₁ - H₂).conj B = H₁.conj B - H₂.conj B := by
  ext1
  simp only [HermitianMat.mat_sub, conj_apply_mat]
  rw [Matrix.mul_sub, Matrix.sub_mul]

private theorem herm_conj_smul {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℂ) (c : ℝ)
    (H : HermitianMat (Fin d₂) ℂ) :
    (c • H).conj B = c • H.conj B := by
  ext1
  simp only [HermitianMat.mat_smul, conj_apply_mat, Matrix.mul_smul, Matrix.smul_mul]

private theorem wpHerm_smul {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (p : DynamicCircuit Var n) (c : ℝ) (A : Store Var → HermitianMat (Fin (2 ^ n)) ℂ) :
    wpHerm p (c • A) = c • wpHerm p A := by
  induction p using DynamicCircuit.qcInd generalizing A with
  | circuit circ => funext σ; simp [herm_conj_smul]
  | measure x r =>
      funext σ
      simp only [wpHerm_measure, Pi.smul_apply, herm_conj_smul, Finset.smul_sum]
  | qIf b t f iht ihf =>
      funext σ
      by_cases hb : b.holds σ <;> simp [hb, congrFun (iht A) σ, congrFun (ihf A) σ]
  | seq p₁ p₂ ih₁ ih₂ => funext σ; simp [ih₂, ih₁]

private theorem wpHerm_sub {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (p : DynamicCircuit Var n) (A B : Store Var → HermitianMat (Fin (2 ^ n)) ℂ) :
    wpHerm p (A - B) = wpHerm p A - wpHerm p B := by
  rw [sub_eq_add_neg, wpHerm_add, ← neg_one_smul ℝ B, wpHerm_smul, neg_one_smul, ← sub_eq_add_neg]

private theorem wpHerm_mono {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (p : DynamicCircuit Var n) {A B : Store Var → HermitianMat (Fin (2 ^ n)) ℂ}
    (h : A ≤ B) : wpHerm p A ≤ wpHerm p B := by
  induction p using DynamicCircuit.qcInd generalizing A B with
  | circuit c => intro σ; exact HermitianMat.conj_mono (h σ)
  | measure x r =>
      intro σ
      exact Finset.sum_le_sum fun o _ ↦ HermitianMat.conj_mono (h _)
  | qIf b t f iht ihf =>
      intro σ
      by_cases hb : b.holds σ <;> simp [hb, iht h σ, ihf h σ]
  | seq p₁ p₂ ih₁ ih₂ => exact ih₁ (ih₂ h)

private theorem herm_eq_zero_of_forall_pos_smul_bounds {d : ℕ}
    (D W : HermitianMat (Fin d) ℂ)
    (h : ∀ t : ℝ, 0 < t → -(t ^ 2 • W) ≤ D ∧ D ≤ t ^ 2 • W) :
    D = 0 := by
  have hnonneg_eps : ∀ ε : ℝ, 0 < ε → -(ε • W) ≤ D ∧ D ≤ ε • W := by
    intro ε hε
    have hsq : (√ε) ^ 2 = ε := Real.sq_sqrt hε.le
    simpa only [hsq] using h (√ε) (Real.sqrt_pos.mpr hε)
  have hpsd_of_sign : ∀ S : HermitianMat (Fin d) ℂ,
      (∀ ε : ℝ, 0 < ε → 0 ≤ S + ε • W) → 0 ≤ S := by
    intro S hS
    rw [HermitianMat.zero_le_iff]
    refine ⟨S.2, fun x ↦ ?_⟩
    let q (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
      x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * M i j * xj
    have hstep : ∀ ε : ℝ, 0 < ε → 0 ≤ q S.mat + (ε : ℂ) * q W.mat := by
      intro ε hε
      have hp : 0 ≤ q (S + ε • W).mat := (HermitianMat.zero_le_iff.mp (hS ε hε)).2 x
      have hlin : q (S + ε • W).mat = q S.mat + (ε : ℂ) * q W.mat := by
        simp only [q, Finsupp.sum, HermitianMat.mat_add, HermitianMat.mat_smul,
          Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _
        ring
      rwa [hlin] at hp
    have h1 := Complex.nonneg_iff.mp (hstep 1 one_pos)
    have h2 := Complex.nonneg_iff.mp (hstep 2 two_pos)
    have himS : (q S.mat).im = 0 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero] at h1 h2
      linarith
    have hreS : 0 ≤ (q S.mat).re := by
      by_contra hlt
      push Not at hlt
      set s := (q S.mat).re
      set w := (q W.mat).re
      by_cases hw : w ≤ 0
      · have h1re := h1.1
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, one_mul] at h1re
        linarith
      · push Not at hw
        have hεpos : 0 < (-s) / (2 * w) := div_pos (neg_pos.mpr hlt) (by linarith)
        have hε := (Complex.nonneg_iff.mp (hstep ((-s) / (2 * w)) hεpos)).1
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero] at hε
        have hmul : (-s) / (2 * w) * w = -s / 2 := by field_simp
        linarith
    exact Complex.nonneg_iff.mpr ⟨hreS, himS.symm⟩
  have hD_nonneg : 0 ≤ D := hpsd_of_sign D fun ε hε ↦
    calc (0 : HermitianMat (Fin d) ℂ) = -(ε • W) + ε • W := (neg_add_cancel _).symm
      _ ≤ D + ε • W := add_le_add (hnonneg_eps ε hε).1 le_rfl
  have hnegD_nonneg : 0 ≤ -D := hpsd_of_sign (-D) fun ε hε ↦
    calc (0 : HermitianMat (Fin d) ℂ) = -D + D := (neg_add_cancel _).symm
      _ ≤ -D + ε • W := add_le_add le_rfl (hnonneg_eps ε hε).2
  exact le_antisymm (neg_nonneg.mp hnegD_nonneg) hD_nonneg

private theorem obs_sub_conj_bounds {n m : ℕ} (rScr : QRegister m n)
    (M : Observable (Fin (2 ^ n))) (t : ℝ) (ht : 0 < t) :
    -(t ^ 2 • (1 : HermitianMat (Fin (2 ^ n)) ℂ) +
        (2 + t⁻¹ ^ 2) • (1 - rScr.cleanObservable.1)) ≤
      M.1 - M.1.conj (rScr.basisOutcomeProjector 0) ∧
    M.1 - M.1.conj (rScr.basisOutcomeProjector 0) ≤
      t ^ 2 • (1 : HermitianMat (Fin (2 ^ n)) ℂ) +
        (1 + t⁻¹ ^ 2) • (1 - rScr.cleanObservable.1) := by
  let P := rScr.basisOutcomeProjector 0
  let Q_herm : HermitianMat (Fin (2 ^ n)) ℂ := 1 - rScr.cleanObservable.1
  let Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := 1 - P
  have hP_herm : Pᴴ = P := rScr.basisOutcomeProjector_conjTranspose 0
  have hP_idem : P * P = P := rScr.basisOutcomeProjector_mul_self 0
  have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
  have hPQ_sum : P + Q = 1 := by simp [Q]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hclean_mat : rScr.cleanObservable.1.mat = P := by simp [QRegister.cleanObservable, P]
  have hconjP_le : M.1.conj P ≤ 1 :=
    (HermitianMat.conj_mono M.2.2).trans
      ((by ext1; simp [conj_apply_mat, hclean_mat, hP_herm, hP_idem] :
        (1 : HermitianMat (Fin (2 ^ n)) ℂ).conj P = rScr.cleanObservable.1).le.trans
        rScr.cleanObservable.2.2)
  have hQ_conj_one : (1 : HermitianMat (Fin (2 ^ n)) ℂ).conj Q = Q_herm := by
    ext1
    simp only [conj_apply_mat, HermitianMat.mat_one, Matrix.mul_one, hQ_herm, Q, Q_herm,
      HermitianMat.mat_sub, hclean_mat]
    rw [sub_mul, one_mul, mul_sub, mul_one, hP_idem]
    abel
  have hconjQ_le : M.1.conj Q ≤ Q_herm :=
    (HermitianMat.conj_mono M.2.2).trans hQ_conj_one.le
  have hdecomp : M.1.mat =
      P * M.1.mat * P + P * M.1.mat * Q + Q * M.1.mat * P + Q * M.1.mat * Q := by
    calc M.1.mat = (P + Q) * M.1.mat * (P + Q) := by rw [hPQ_sum, one_mul, mul_one]
      _ = P * M.1.mat * P + P * M.1.mat * Q + Q * M.1.mat * P + Q * M.1.mat * Q := by
          simp only [Matrix.add_mul, Matrix.mul_add]
          abel
  have hti : (t : ℂ) * (t⁻¹ : ℂ) = 1 := mul_inv_cancel₀ ht_ne
  have hit : (t⁻¹ : ℂ) * (t : ℂ) = 1 := inv_mul_cancel₀ ht_ne
  have hub_mid : M.1 - M.1.conj P ≤ t ^ 2 • M.1.conj P + (1 + t⁻¹ ^ 2) • M.1.conj Q := by
    suffices hdiff : 0 ≤ (t ^ 2 • M.1.conj P + (1 + t⁻¹ ^ 2) • M.1.conj Q) - (M.1 - M.1.conj P)
      from sub_nonneg.mp hdiff
    have heq : (t ^ 2 • M.1.conj P + (1 + t⁻¹ ^ 2) • M.1.conj Q) - (M.1 - M.1.conj P) =
        M.1.conj ((t : ℂ) • P - (t⁻¹ : ℂ) • Q) := by
      ext1
      simp only [HermitianMat.mat_sub, HermitianMat.mat_add, HermitianMat.mat_smul,
        conj_apply_mat, conjTranspose_sub, conjTranspose_smul, hP_herm, hQ_herm,
        Complex.star_def, star_inv₀, Complex.conj_ofReal,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
      ext i j
      have hd := congrFun (congrFun hdecomp i) j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one,
        Complex.ofReal_inv] at hd ⊢
      linear_combination -hd + (P * M.1.mat * Q) i j * hti + (Q * M.1.mat * P) i j * hit
    rw [heq]
    exact M.1.conj_nonneg _ M.2.1
  have hlb_mid : -(t ^ 2 • M.1.conj P + (2 + t⁻¹ ^ 2) • M.1.conj Q) ≤ M.1 - M.1.conj P := by
    suffices hdiff : 0 ≤ (t ^ 2 • M.1.conj P + (2 + t⁻¹ ^ 2) • M.1.conj Q) + (M.1 - M.1.conj P) by
      exact neg_le_iff_add_nonneg'.mpr hdiff
    have heq : (t ^ 2 • M.1.conj P + (2 + t⁻¹ ^ 2) • M.1.conj Q) + (M.1 - M.1.conj P) =
        M.1.conj ((t : ℂ) • P + (t⁻¹ : ℂ) • Q) + (3 : ℝ) • M.1.conj Q := by
      ext1
      simp only [HermitianMat.mat_sub, HermitianMat.mat_add, HermitianMat.mat_smul,
        conj_apply_mat, conjTranspose_add, conjTranspose_smul, hP_herm, hQ_herm,
        Complex.star_def, star_inv₀, Complex.conj_ofReal,
        Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      ext i j
      have hd := congrFun (congrFun hdecomp i) j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_ofNat,
        Complex.ofReal_inv] at hd ⊢
      linear_combination hd - (P * M.1.mat * Q) i j * hti - (Q * M.1.mat * P) i j * hit
    rw [heq]
    exact add_nonneg (M.1.conj_nonneg _ M.2.1)
      (smul_nonneg (by positivity) (M.1.conj_nonneg _ M.2.1))
  have ht2_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have h1t_nonneg : 0 ≤ 1 + t⁻¹ ^ 2 := by positivity
  have h2t_nonneg : 0 ≤ 2 + t⁻¹ ^ 2 := by positivity
  refine ⟨?_, hub_mid.trans (add_le_add (smul_le_smul_of_nonneg_left hconjP_le ht2_nonneg)
    (smul_le_smul_of_nonneg_left hconjQ_le h1t_nonneg))⟩
  exact (neg_le_neg (add_le_add (smul_le_smul_of_nonneg_left hconjP_le ht2_nonneg)
    (smul_le_smul_of_nonneg_left hconjQ_le h2t_nonneg))).trans hlb_mid

/-- Automatic derivation of `CleanRealizes` Conjunct 4 (for ALL assertions `Θ`, even those
depending on `v`) from store-independent clean-ancilla `wp` agreement and
`rAct.DisjointWires rScr`. -/
theorem restrictAssertionToZeroAncilla_wp_restrict_eq_of_clean
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k s : ℕ} [NeZero (2 ^ n)]
    (rAct : QRegister k n) (rScr : QRegister s n) (hdisj : rAct.DisjointWires rScr)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var n)
    (hclean : ∀ M : Observable (Fin (2 ^ n)),
      restrictAssertionToZeroAncilla (wp P.compile (fun _ ↦ M)) rScr =
        restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) (fun _ ↦ M)) rScr)
    (Θ : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla (wp P.compile (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr := by
  funext σ
  apply Subtype.ext
  let P₀ := rScr.basisOutcomeProjector 0
  let Q_obs : Observable (Fin (2 ^ n)) :=
    ⟨1 - rScr.cleanObservable.1, sub_nonneg.mpr rScr.cleanObservable.2.2,
      sub_le_self 1 rScr.cleanObservable.2.1⟩
  have hQ_zero : (wpHerm P (fun _ ↦ Q_obs.1) σ).conj P₀ = 0 := by
    have hwpQ := congrArg (fun A ↦ (A σ).1) (hclean Q_obs)
    dsimp only [restrictAssertionToZeroAncilla_coe] at hwpQ
    rw [← congrFun (wpHerm_eq_wp P (fun _ ↦ Q_obs)) σ] at hwpQ
    rw [hwpQ]
    ext1
    have hP₀_herm : P₀ᴴ = P₀ := rScr.basisOutcomeProjector_conjTranspose 0
    have hP₀_idem : P₀ * P₀ = P₀ := rScr.basisOutcomeProjector_mul_self 0
    have hclean_mat : rScr.cleanObservable.1.mat = P₀ := by simp [QRegister.cleanObservable, P₀]
    have hcomm : (rAct.embedUnitary U).1 * P₀ = P₀ * (rAct.embedUnitary U).1 :=
      rAct.embedMatrix_comm_of_disjoint rScr hdisj U.1 (compProj 0)
    have hcommH : P₀ * (rAct.embedUnitary U).1ᴴ = (rAct.embedUnitary U).1ᴴ * P₀ := by
      have h := congrArg conjTranspose hcomm
      simpa only [conjTranspose_mul, hP₀_herm] using h
    simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_apply_mat, Q_obs, HermitianMat.mat_sub,
      HermitianMat.mat_one, hclean_mat, QRegister.basisOutcomeProjector_conjTranspose,
      conjTranspose_conjTranspose, HermitianMat.mat_zero]
    calc P₀ * ((rAct.embedUnitary U).1ᴴ * (1 - P₀) * (rAct.embedUnitary U).1) * P₀
      _ = (P₀ * (rAct.embedUnitary U).1ᴴ) * (1 - P₀) * ((rAct.embedUnitary U).1 * P₀) := by
          simp only [Matrix.mul_assoc]
      _ = (rAct.embedUnitary U).1ᴴ * (P₀ * (1 - P₀) * P₀) * (rAct.embedUnitary U).1 := by
          rw [hcommH, hcomm]; simp only [Matrix.mul_assoc]
      _ = 0 := by
          have hmid : P₀ * (1 - P₀) * P₀ = 0 := by
            rw [mul_sub, mul_one, hP₀_idem, sub_self, zero_mul]
          rw [hmid, mul_zero, zero_mul]
  let A : Store Var → HermitianMat (Fin (2 ^ n)) ℂ := fun σ' ↦ (Θ σ').1
  let B : Store Var → HermitianMat (Fin (2 ^ n)) ℂ := fun σ' ↦ (Θ σ').1.conj P₀
  let oneFam : Store Var → HermitianMat (Fin (2 ^ n)) ℂ := fun _ ↦ 1
  let QFam : Store Var → HermitianMat (Fin (2 ^ n)) ℂ := fun _ ↦ Q_obs.1
  let W : HermitianMat (Fin (2 ^ n)) ℂ := (wpHerm P oneFam σ).conj P₀
  let D : HermitianMat (Fin (2 ^ n)) ℂ := (wpHerm P A σ).conj P₀ - (wpHerm P B σ).conj P₀
  have hD_zero : D = 0 := by
    refine herm_eq_zero_of_forall_pos_smul_bounds D W fun t ht ↦ ?_
    have hb := fun σ' ↦ obs_sub_conj_bounds rScr (Θ σ') t ht
    have hle_ub : A - B ≤ t ^ 2 • oneFam + (1 + t⁻¹ ^ 2) • QFam := fun σ' ↦ (hb σ').2
    have hle_lb : -(t ^ 2 • oneFam + (2 + t⁻¹ ^ 2) • QFam) ≤ A - B := fun σ' ↦ (hb σ').1
    have hub : (wpHerm P (A - B) σ).conj P₀ ≤
        (wpHerm P (t ^ 2 • oneFam + (1 + t⁻¹ ^ 2) • QFam) σ).conj P₀ :=
      HermitianMat.conj_mono (wpHerm_mono P hle_ub σ)
    have hlb : (wpHerm P (-(t ^ 2 • oneFam + (2 + t⁻¹ ^ 2) • QFam)) σ).conj P₀ ≤
        (wpHerm P (A - B) σ).conj P₀ :=
      HermitianMat.conj_mono (wpHerm_mono P hle_lb σ)
    rw [wpHerm_sub, Pi.sub_apply, herm_conj_sub] at hub hlb
    rw [wpHerm_add, wpHerm_smul, wpHerm_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      herm_conj_add, herm_conj_smul, herm_conj_smul, hQ_zero, smul_zero, add_zero] at hub
    have hneg_fam : -(t ^ 2 • oneFam + (2 + t⁻¹ ^ 2) • QFam) =
        (-1 : ℝ) • (t ^ 2 • oneFam + (2 + t⁻¹ ^ 2) • QFam) := (neg_one_smul ℝ _).symm
    rw [hneg_fam, wpHerm_smul, wpHerm_add, wpHerm_smul, wpHerm_smul,
      Pi.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      herm_conj_smul, herm_conj_add, herm_conj_smul, herm_conj_smul,
      hQ_zero, smul_zero, add_zero, neg_one_smul] at hlb
    exact ⟨hlb, hub⟩
  have hEq : (wpHerm P B σ).conj P₀ = (wpHerm P A σ).conj P₀ :=
    (sub_eq_zero.mp hD_zero).symm
  have hA := congrFun (wpHerm_eq_wp P Θ) σ
  have hB := congrFun (wpHerm_eq_wp P (restrictAssertionToZeroAncilla Θ rScr)) σ
  dsimp [A, B] at hEq
  simpa only [restrictAssertionToZeroAncilla_coe, ← hA, ← hB] using hEq

/-! ## Core `CleanRealizes` Constructors & Combinators -/

/-- Smart constructor for `CleanRealizes` when `rAct.DisjointWires rScr`: Conjunct 4 is derived
automatically from Conjunct 3 via `restrictAssertionToZeroAncilla_wp_restrict_eq_of_clean`. -/
theorem CleanRealizes.mk_of_disjoint {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (hdisj : rAct.DisjointWires rScr)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N)
    (htoff : P.count PrimitiveGate.TOFF = 0)
    (hupd : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ)
    (hwp : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      restrictAssertionToZeroAncilla (wp P.compile Θ) rScr =
        restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr) :
    CleanRealizes v rAct rScr U P :=
  ⟨htoff, hupd, hwp,
    restrictAssertionToZeroAncilla_wp_restrict_eq_of_clean rAct rScr hdisj U P
      (fun M ↦ hwp (fun _ ↦ M) (fun _ _ ↦ rfl))⟩

theorem CleanRealizes.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U₁ U₂ : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v rAct rScr U₁ P) (hU : U₁ = U₂) :
    CleanRealizes v rAct rScr U₂ P :=
  hU ▸ h

/-- `DynamicCircuit.identity` realizes `1` on any `(rAct, rScr)`. -/
theorem CleanRealizes.identity {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N) :
    CleanRealizes v rAct rScr 1 .identity := by
  refine ⟨rfl, fun Θ hΘ σ val ↦ hΘ σ val, fun Θ _ ↦ ?_, fun Θ ↦ ?_⟩
  · funext σ; apply Subtype.ext
    simp [qcWpQAssign, qcQAssignObsMap]
  · funext σ; apply Subtype.ext
    simp [conj_conj, rScr.basisOutcomeProjector_mul_self 0]

/-- Any `.TOFF`-free `Circuit k` placed onto `rAct` (disjoint from `rScr`) satisfies
`CleanRealizes`. -/
theorem CleanRealizes.circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (hdisj : rAct.DisjointWires rScr) (c : Circuit k)
    (htoff : c.count PrimitiveGate.TOFF = 0) :
    CleanRealizes v rAct rScr c.eval (.circuit (c.onRegister rAct)) := by
  refine CleanRealizes.mk_of_disjoint v rAct rScr hdisj c.eval (.circuit (c.onRegister rAct))
    (by simp [htoff])
    (fun Θ hΘ σ val ↦ by simp [qcWpQAssign, hΘ σ val])
    (fun Θ _ ↦ by simp)

/-- Sequential composition of `CleanRealizes` circuits realizes `U₂ * U₁` (note circuit execution
order `P₁` then `P₂` corresponds to matrix product `U₂ * U₁`). -/
theorem CleanRealizes.seq {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U₁ U₂ : Unitary (2 ^ k)} {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : CleanRealizes v rAct rScr U₁ P₁) (h₂ : CleanRealizes v rAct rScr U₂ P₂) :
    CleanRealizes v rAct rScr (U₂ * U₁) (.seq P₁ P₂) := by
  refine ⟨by simp [h₁.1, h₂.1], fun Θ hΘ σ val ↦ h₁.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ) σ val,
    fun Θ hΘ ↦ ?_, fun Θ ↦ ?_⟩
  · change restrictAssertionToZeroAncilla (wp P₁.compile (wp P₂.compile Θ)) rScr = _
    have hU₂_inv : ∀ σ val,
        qcWpQAssign (rAct.embedUnitary U₂) Θ (Function.update σ v val) =
          qcWpQAssign (rAct.embedUnitary U₂) Θ σ := by
      intro σ val; simp [qcWpQAssign, hΘ σ val]
    rw [← h₁.2.2.2 (wp P₂.compile Θ), h₂.2.2.1 Θ hΘ,
      h₁.2.2.2 (qcWpQAssign (rAct.embedUnitary U₂) Θ),
      h₁.2.2.1 (qcWpQAssign (rAct.embedUnitary U₂) Θ) hU₂_inv,
      qc_wp_qAssign_comp, ← rAct.embedUnitary_mul]
  · change restrictAssertionToZeroAncilla
        (wp P₁.compile (wp P₂.compile (restrictAssertionToZeroAncilla Θ rScr))) rScr =
      restrictAssertionToZeroAncilla (wp P₁.compile (wp P₂.compile Θ)) rScr
    rw [← h₁.2.2.2, h₂.2.2.2 Θ, h₁.2.2.2]

/-- Full-space register relocation of `CleanRealizes` along any `placement : QRegister m N`. -/
theorem CleanRealizes.onRegister {Var : Type} [Fintype Var] [DecidableEq Var]
    {m N k s : ℕ} [NeZero (2 ^ m)] [NeZero (2 ^ N)]
    (placement : QRegister m N)
    {v : Var} {rAct : QRegister k m} {rScr : QRegister s m}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var m}
    (h : CleanRealizes v rAct rScr U P) :
    CleanRealizes v (placement.compose rAct) (placement.compose rScr) U
      (P.onRegister placement) := by
  refine ⟨by simp [h.1], ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    have heq : wp (P.onRegister placement).compile Θ =
        fun σ' ↦ wp (P.onRegister placement).compile Θ (Function.update σ' v val) := by
      refine cqAssertion_eq_of_pullbackAssertion_eq placement _ _ fun φ hφ ↦ ?_
      have hφ_inv : ∀ σ' val',
          pullbackAssertion placement φ hφ Θ (Function.update σ' v val') =
            pullbackAssertion placement φ hφ Θ σ' := by
        intro σ' val'; simp [pullbackAssertion, hΘ σ' val']
      funext σ'
      have hstep := congrFun (pullbackAssertion_wp_onRegister placement φ hφ P Θ)
      rw [hstep σ']
      change _ = pullbackObs placement φ hφ
        (wp (P.onRegister placement).compile Θ (Function.update σ' v val))
      rw [show pullbackObs placement φ hφ
          (wp (P.onRegister placement).compile Θ (Function.update σ' v val)) =
        pullbackAssertion placement φ hφ (wp (P.onRegister placement).compile Θ)
          (Function.update σ' v val) from rfl]
      rw [hstep (Function.update σ' v val), h.2.1 _ hφ_inv σ' val]
    exact (congrFun heq σ).symm
  · intro Θ hΘ
    refine cqAssertion_eq_of_pullbackAssertion_eq placement _ _ fun φ hφ ↦ ?_
    have hφ_inv : ∀ σ' val',
        pullbackAssertion placement φ hφ Θ (Function.update σ' v val') =
          pullbackAssertion placement φ hφ Θ σ' := by
      intro σ' val'; simp [pullbackAssertion, hΘ σ' val']
    rw [pullbackAssertion_restrict, pullbackAssertion_wp_onRegister, h.2.2.1 _ hφ_inv,
      pullbackAssertion_restrict, pullbackAssertion_wp_qAssign]
  · intro Θ
    refine cqAssertion_eq_of_pullbackAssertion_eq placement _ _ fun φ hφ ↦ ?_
    rw [pullbackAssertion_restrict, pullbackAssertion_wp_onRegister,
      pullbackAssertion_restrict, h.2.2.2,
      pullbackAssertion_restrict, pullbackAssertion_wp_onRegister]

/-! ## Sub-Register & Extended-Scratch Lifting -/

theorem extractIndex_eq_zero_iff_basisBits_eq_zero {k n : ℕ} (r : QRegister k n)
    (j : Fin (2 ^ n)) :
    r.extractIndex j = 0 ↔ ∀ i : Fin k, basisBits n j (r i) = 0 := by
  constructor
  · intro h i
    rw [← r.basisBits_extractIndex, h, basisBits_eq_div_mod]
    norm_num
  · intro h
    apply (basisBits k).injective
    funext i
    rw [r.basisBits_extractIndex, h i, basisBits_eq_div_mod]
    norm_num

theorem basisOutcomeProjector_zero_mul_of_image_subset {n s₁ s₂ : ℕ}
    {rScr₁ : QRegister s₁ n} {rScr₂ : QRegister s₂ n}
    (hsub : rScr₁.image ⊆ rScr₂.image) :
    rScr₁.basisOutcomeProjector 0 * rScr₂.basisOutcomeProjector 0 =
      rScr₂.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext g
  by_cases h₂ : rScr₂.extractIndex g = 0
  · have h₁ : rScr₁.extractIndex g = 0 := by
      rw [extractIndex_eq_zero_iff_basisBits_eq_zero] at h₂ ⊢
      intro i
      have hmem : rScr₁ i ∈ rScr₂.image := hsub (QRegister.mem_image rScr₁ _ |>.mpr ⟨i, rfl⟩)
      obtain ⟨j, hj⟩ := QRegister.mem_image rScr₂ _ |>.mp hmem
      rw [← hj]
      exact h₂ j
    simp [h₁, h₂]
  · simp [h₂]

theorem restrictAssertionToZeroAncilla_absorb {Var : Type} {n s₁ s₂ : ℕ}
    {rScr₁ : QRegister s₁ n} {rScr₂ : QRegister s₂ n}
    (hsub : rScr₁.image ⊆ rScr₂.image) (A : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla A rScr₁) rScr₂ =
      restrictAssertionToZeroAncilla A rScr₂ := by
  funext σ; apply Subtype.ext
  have hmul : rScr₂.basisOutcomeProjector 0 * rScr₁.basisOutcomeProjector 0 =
      rScr₂.basisOutcomeProjector 0 := by
    have h := congrArg conjTranspose (basisOutcomeProjector_zero_mul_of_image_subset hsub)
    simpa only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
  simp only [restrictAssertionToZeroAncilla_coe, conj_conj, hmul]

/-- Lift `CleanRealizes` from a sub-register `rAct.compose subAct` and a sub-scratch register
`rScr₁` (`rScr₁.image ⊆ rScr₂.image`, in any wire order!) to `(rAct, rScr₂)`. -/
theorem CleanRealizes.subregister {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k₀ k s₁ s₂ : ℕ} [NeZero (2 ^ N)]
    {v : Var} {rAct : QRegister k N} {subAct : QRegister k₀ k}
    {rScr₁ : QRegister s₁ N} {rScr₂ : QRegister s₂ N}
    {U₀ : Unitary (2 ^ k₀)} {P : DynamicCircuit Var N}
    (hdisj : rAct.DisjointWires rScr₂) (hsub : rScr₁.image ⊆ rScr₂.image)
    (h : CleanRealizes v (rAct.compose subAct) rScr₁ U₀ P) :
    CleanRealizes v rAct rScr₂ (subAct.embedUnitary U₀) P := by
  refine CleanRealizes.mk_of_disjoint v rAct rScr₂ hdisj (subAct.embedUnitary U₀) P h.1 h.2.1
    fun Θ hΘ ↦ ?_
  rw [← restrictAssertionToZeroAncilla_absorb hsub (wp P.compile Θ), h.2.2.1 Θ hΘ,
    restrictAssertionToZeroAncilla_absorb hsub, ← QRegister.embedUnitary_compose]

/-- Special case of `CleanRealizes.subregister` extending or reordering only the scratch register
(`rScr₁.image ⊆ rScr₂.image`). -/
theorem CleanRealizes.extend_scr {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₁ s₂ : ℕ} [NeZero (2 ^ N)]
    {v : Var} {rAct : QRegister k N} {rScr₁ : QRegister s₁ N} {rScr₂ : QRegister s₂ N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hdisj : rAct.DisjointWires rScr₂) (hsub : rScr₁.image ⊆ rScr₂.image)
    (h : CleanRealizes v rAct rScr₁ U P) :
    CleanRealizes v rAct rScr₂ U P := by
  have h' : CleanRealizes v (rAct.compose (QRegister.whole k)) rScr₁ U P := by simpa using h
  simpa using h'.subregister hdisj hsub

/-! ## Toffoli-to-Jones-Toffoli Lowering (`substToffoliWithAncilla`) -/

private theorem triple_eq_self {n : ℕ} (r : QRegister 3 n)
    (h₀₁ : r 0 ≠ r 1) (h₀₂ : r 0 ≠ r 2) (h₁₂ : r 1 ≠ r 2) :
    QRegister.triple (r 0) (r 1) (r 2) h₀₁ h₀₂ h₁₂ = r := by
  ext i; fin_cases i <;> rfl

/-- Lower one primitive gate by replacing `.toffoli` with `DynamicCircuit.jonesToffoli` using clean
wire `ancilla` and scratch measurement variable `v`. -/
def substGate {Var : Type} {n : ℕ} (v : Var) (ancilla : Wire n) :
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

/-- Lower every `.toffoli` gate in `c : Circuit n` to `jonesToffoli` on reusable clean wire
`ancilla`. -/
def substCircuit {Var : Type} {n : ℕ} (v : Var) (ancilla : Wire n) :
    Circuit n → DynamicCircuit Var n
  | .identity => .identity
  | .gate g r => substGate v ancilla g r
  | .seq c₁ c₂ => .seq (substCircuit v ancilla c₁) (substCircuit v ancilla c₂)

/-- Relocate `c : Circuit k` onto `rAct : QRegister k N` and lower every `.toffoli` gate to
`jonesToffoli` using reusable clean wire `anc : Wire N`. -/
def substToffoliWithAncilla {Var : Type} {N k : ℕ}
    (v : Var) (rAct : QRegister k N) (anc : Wire N) (c : Circuit k) :
    DynamicCircuit Var N :=
  substCircuit v anc (c.onRegister rAct)

@[simp]
theorem count_substGate_toff {Var : Type} {n : ℕ} (v : Var) (ancilla : Wire n)
    {a : ℕ} (g : PrimitiveGate a) (r : QRegister a n) :
    (substGate v ancilla g r).count PrimitiveGate.TOFF = 0 := by
  cases g with
  | toffoli => dsimp only [substGate]; split_ifs <;> simp
  | _ => rfl

@[simp]
theorem count_substCircuit_toff {Var : Type} {n : ℕ} (v : Var) (ancilla : Wire n) (c : Circuit n) :
    (substCircuit v ancilla c).count PrimitiveGate.TOFF = 0 := by
  induction c with
  | identity => rfl
  | gate g r => exact count_substGate_toff v ancilla g r
  | seq _ _ ih₁ ih₂ => simp [substCircuit, ih₁, ih₂]

@[simp]
theorem count_substToffoliWithAncilla_toff {Var : Type} {N k : ℕ}
    (v : Var) (rAct : QRegister k N) (anc : Wire N) (c : Circuit k) :
    (substToffoliWithAncilla v rAct anc c).count PrimitiveGate.TOFF = 0 :=
  count_substCircuit_toff v anc (c.onRegister rAct)

theorem count_substCircuit_t_eq_of_not_mem_support {Var : Type} {n : ℕ}
    (v : Var) (ancilla : Wire n) (c : Circuit n) (hanc : ancilla ∉ c.support) :
    (substCircuit v ancilla c).count PrimitiveGate.T =
      c.count .T + 4 * c.count .TOFF := by
  induction c with
  | identity => simp [substCircuit]
  | gate g r =>
      dsimp only [substCircuit]
      cases g with
      | toffoli =>
          have hcond : r 0 ≠ ancilla ∧ r 1 ≠ ancilla ∧ r 2 ≠ ancilla :=
            ⟨(r.ne_apply_of_not_mem_image ancilla hanc 0).symm,
              (r.ne_apply_of_not_mem_image ancilla hanc 1).symm,
              (r.ne_apply_of_not_mem_image ancilla hanc 2).symm⟩
          simp [substGate, hcond]
      | _ => simp [substGate]
  | seq _ _ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.mem_union, not_or] at hanc
      simp only [substCircuit, DynamicCircuit.count, Circuit.count_seq, ih₁ hanc.1, ih₂ hanc.2]
      omega

theorem count_substToffoliWithAncilla_t {Var : Type} {N k : ℕ}
    (v : Var) (rAct : QRegister k N) (anc : Wire N)
    (hdisj : rAct.DisjointWires (QRegister.singleton anc)) (c : Circuit k) :
    (substToffoliWithAncilla v rAct anc c).count PrimitiveGate.T =
      c.count .T + 4 * c.count .TOFF := by
  have hnot : anc ∉ (c.onRegister rAct).support := fun hmem ↦ by
    have himg := DynamicCircuit.circuit_support_onRegister_subset rAct c hmem
    obtain ⟨i, hi⟩ := QRegister.mem_image rAct anc |>.mp himg
    exact hdisj.ne i 0 hi
  rw [substToffoliWithAncilla]
  simpa using count_substCircuit_t_eq_of_not_mem_support v anc (c.onRegister rAct) hnot

private theorem cleanRealizes_substGate_singleton {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k a : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (anc : Wire N)
    (hdisj : rAct.DisjointWires (QRegister.singleton anc))
    (g : PrimitiveGate a) (r : QRegister a k) :
    CleanRealizes v rAct (QRegister.singleton anc) (Circuit.gate g r).eval
      (substGate v anc g (rAct.compose r)) := by
  let r' := rAct.compose r
  refine CleanRealizes.mk_of_disjoint v rAct (QRegister.singleton anc) hdisj
    (Circuit.gate g r).eval (substGate v anc g r') (count_substGate_toff v anc g r') ?_ ?_
  · intro Θ hΘ σ val
    cases g with
    | toffoli =>
        dsimp only [substGate]
        split_ifs with h
        · exact DynamicCircuit.wp_jonesToffoli_update_self v (r' 0) (r' 1) (r' 2) anc _
            h.1 h.2.1 h.2.2 Θ σ val
        · simpa [wp] using hΘ σ val
    | _ =>
        simp [substGate, qcWpQAssign, hΘ σ val]
  · intro Θ hΘ
    have hemb : rAct.embedUnitary (Circuit.gate g r).eval = (Circuit.gate g r').eval := by
      simp [r', QRegister.embedUnitary_compose]
    rw [hemb]
    cases g with
    | toffoli =>
        have h₀₁ : r' 0 ≠ r' 1 := fun h ↦ by cases r'.wires.injective h
        have h₀₂ : r' 0 ≠ r' 2 := fun h ↦ by cases r'.wires.injective h
        have h₁₂ : r' 1 ≠ r' 2 := fun h ↦ by cases r'.wires.injective h
        have hcond : r' 0 ≠ anc ∧ r' 1 ≠ anc ∧ r' 2 ≠ anc :=
          ⟨hdisj.ne (r 0) 0, hdisj.ne (r 1) 0, hdisj.ne (r 2) 0⟩
        have htoff_eq : (Circuit.TOFF (r' 0) (r' 1) (r' 2) h₀₁ h₀₂ h₁₂).eval =
            (Circuit.gate .toffoli r').eval := by
          dsimp [Circuit.TOFF]
          rw [triple_eq_self r' h₀₁ h₀₂ h₁₂]
        dsimp only [substGate]
        split_ifs with hc
        · rw [← htoff_eq]
          exact DynamicCircuit.qc_wp_jonesToffoli_of_update_eq
            v (r' 0) (r' 1) (r' 2) anc h₀₁ h₀₂ h₁₂ hc.1 hc.2.1 hc.2.2 Θ hΘ
        · exact False.elim (hc hcond)
    | _ => simp [substGate]

/-- `substToffoliWithAncilla` realizes `c.eval` on `rAct` using a single clean wire `anc`. -/
theorem cleanRealizes_substToffoliWithAncilla_singleton
    {Var : Type} [Fintype Var] [DecidableEq Var] {N k : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (anc : Wire N)
    (hdisj : rAct.DisjointWires (QRegister.singleton anc)) (c : Circuit k) :
    CleanRealizes v rAct (QRegister.singleton anc) c.eval
      (substToffoliWithAncilla v rAct anc c) := by
  induction c with
  | identity => simpa [substToffoliWithAncilla, substCircuit] using
      CleanRealizes.identity v rAct (QRegister.singleton anc)
  | gate g r =>
      exact cleanRealizes_substGate_singleton v rAct anc hdisj g r
  | seq c₁ c₂ ih₁ ih₂ =>
      simpa only [substToffoliWithAncilla, Circuit.onRegister_seq, substCircuit, Circuit.eval_seq]
        using ih₁.seq ih₂

/-- `substToffoliWithAncilla` realizes `c.eval` on `rAct` using any clean scratch wire `rScr j` of a
disjoint scratch register `rScr`. -/
theorem cleanRealizes_substToffoliWithAncilla
    {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (hdisj : rAct.DisjointWires rScr) (j : Fin s) (c : Circuit k) :
    CleanRealizes v rAct rScr c.eval (substToffoliWithAncilla v rAct (rScr j) c) := by
  have hsub : (QRegister.singleton (rScr j)).image ⊆ rScr.image := by
    simp [Finset.singleton_subset_iff, QRegister.mem_image]
  have hdisj₁ : rAct.DisjointWires (QRegister.singleton (rScr j)) :=
    QRegister.disjointWires_of_image_subset_right hdisj hsub
  exact (cleanRealizes_substToffoliWithAncilla_singleton v rAct (rScr j) hdisj₁ c).extend_scr
    hdisj hsub

/-! ## Gidney Temporary-AND Sandwich (`andSandwichProg` & `CleanRealizes.andSandwich`) -/

/-- Gidney temporary-AND compute / middle `DynamicCircuit` / measurement-assisted uncompute
sandwich (`4 + mid.count .T` `T` gates, `0` `TOFF` gates when `mid` is `.TOFF`-free). -/
def andSandwichProg {Var : Type} {N : ℕ}
    (v : Var) (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (mid : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
    (.seq mid (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))

@[simp]
theorem count_andSandwichProg_toff {Var : Type} {N : ℕ}
    (v : Var) (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (mid : DynamicCircuit Var N) :
    (andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a mid).count PrimitiveGate.TOFF =
      mid.count PrimitiveGate.TOFF := by
  simp [andSandwichProg]

@[simp]
theorem count_andSandwichProg_t {Var : Type} {N : ℕ}
    (v : Var) (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (mid : DynamicCircuit Var N) :
    (andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a mid).count PrimitiveGate.T =
      4 + mid.count PrimitiveGate.T := by
  simp [andSandwichProg]

private theorem restrict_concat {Var : Type} {N s₁ s₂ : ℕ}
    (r₁ : QRegister s₁ N) (r₂ : QRegister s₂ N) (h₁₂ : r₁.DisjointWires r₂)
    (A : QCAssertion Var (2 ^ N)) :
    restrictAssertionToZeroAncilla A (r₁.concat r₂ h₁₂) =
      restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla A r₁) r₂ := by
  funext σ; apply Subtype.ext
  have hproj : (r₁.concat r₂ h₁₂).basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext g
    have heq : (r₁.concat r₂ h₁₂).extractIndex g = 0 ↔
        r₂.extractIndex g = 0 ∧ r₁.extractIndex g = 0 := by
      simp only [extractIndex_eq_zero_iff_basisBits_eq_zero]
      constructor
      · intro h
        refine ⟨fun j ↦ ?_, fun i ↦ ?_⟩
        · simpa using h (Fin.natAdd s₁ j)
        · simpa using h (Fin.castAdd s₂ i)
      · rintro ⟨h₂, h₁⟩ idx
        obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
        · simpa using h₁ i
        · simpa using h₂ j
    by_cases h₂ : r₂.extractIndex g = 0 <;> by_cases h₁ : r₁.extractIndex g = 0 <;>
      simp [heq, h₁, h₂]
  simp only [restrictAssertionToZeroAncilla_coe, conj_conj, hproj]

private theorem restrict_wp_qAssign_comm_of_comm {Var : Type} [Fintype Var] {N s : ℕ}
    (W : Unitary (2 ^ N)) (r : QRegister s N)
    (hcomm : W.1 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * W.1)
    (A : QCAssertion Var (2 ^ N)) :
    restrictAssertionToZeroAncilla (qcWpQAssign W (restrictAssertionToZeroAncilla A r)) r =
      restrictAssertionToZeroAncilla (qcWpQAssign W A) r := by
  funext σ; apply Subtype.ext
  let P₀ := r.basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := r.basisOutcomeProjector_conjTranspose 0
  have hP₀_idem : P₀ * P₀ = P₀ := r.basisOutcomeProjector_mul_self 0
  have hadj : P₀ * W.1ᴴ * P₀ = P₀ * W.1ᴴ := by
    have h := congrArg conjTranspose hcomm
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
    calc P₀ * W.1ᴴ * P₀ = P₀ * (W.1ᴴ * P₀) := by rw [Matrix.mul_assoc]
      _ = P₀ * (P₀ * W.1ᴴ) := by rw [← h]
      _ = (P₀ * P₀) * W.1ᴴ := by rw [← Matrix.mul_assoc]
      _ = P₀ * W.1ᴴ := by rw [hP₀_idem]
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [← Matrix.mul_assoc, hadj]

/-- Compositional `CleanRealizes` rule for Gidney temporary-AND sandwiches
`andCompute c₁ c₂ anc ;; mid ;; andUncompute v c₁ c₂ anc`, where `mid` is ANY `CleanRealizes`
dynamic circuit (including nested `andSandwich`es or `substToffoliWithAncilla`s) acting on
`rAct.concat (QRegister.singleton anc) hActAnc` with inner clean scratch `rScrMid`. -/
theorem CleanRealizes.andSandwich {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N)
    (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hActAnc : rAct.DisjointWires (QRegister.singleton anc))
    (rScrMid : QRegister s N)
    (hAncMid : (QRegister.singleton anc).DisjointWires rScrMid)
    (hActMid : rAct.DisjointWires rScrMid)
    (hc₁Mid : c₁ ∉ rScrMid.image) (hc₂Mid : c₂ ∉ rScrMid.image)
    (U_mid : Unitary (2 ^ (k + 1))) (U_act : Unitary (2 ^ k))
    (mid : DynamicCircuit Var N)
    (hmid : CleanRealizes v (rAct.concat (QRegister.singleton anc) hActAnc) rScrMid U_mid mid)
    (hU :
      let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      T_anc.1 * ((rAct.concat (QRegister.singleton anc) hActAnc).embedUnitary U_mid).1 *
        T_anc.1 * P₀ = (rAct.embedUnitary U_act).1 * P₀) :
    CleanRealizes v rAct ((QRegister.singleton anc).concat rScrMid hAncMid) U_act
      (andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a mid) := by
  let rAnc1 := QRegister.singleton anc
  let rScr := rAnc1.concat rScrMid hAncMid
  let rActExt := rAct.concat rAnc1 hActAnc
  have hdisj : rAct.DisjointWires rScr :=
    QRegister.disjointWires_concat_right hAncMid hActAnc hActMid
  refine CleanRealizes.mk_of_disjoint v rAct rScr hdisj U_act
    (andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a mid)
    (by simp [hmid.1]) ?_ ?_
  · intro Θ _ σ val
    have huncomp_inv : ∀ σ' val',
        wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ (Function.update σ' v val') =
          wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ σ' :=
      fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' val'
    have hmid_inv := hmid.2.1 _ huncomp_inv σ val
    dsimp [andSandwichProg]
    simp [DynamicCircuit.andCompute, qcWpQAssign, hmid_inv]
  · intro Θ hΘ
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
    let W_mid := rActExt.embedUnitary U_mid
    let V := T_anc * W_mid * T_anc
    let U_uncomp := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
    have huncomp_inv : ∀ σ' val', U_uncomp (Function.update σ' v val') = U_uncomp σ' :=
      fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' val'
    have hT_mid_disj : (QRegister.triple c₁ c₂ anc h₁₂ h₁a h₂a).DisjointWires rScrMid := by
      rw [QRegister.disjoint_iff]
      intro i j
      fin_cases i
      · exact rScrMid.ne_apply_of_not_mem_image c₁ hc₁Mid j
      · exact rScrMid.ne_apply_of_not_mem_image c₂ hc₂Mid j
      · exact hAncMid.ne 0 j
    have hT_comm_mid : T_anc.1 * rScrMid.basisOutcomeProjector 0 =
        rScrMid.basisOutcomeProjector 0 * T_anc.1 :=
      (QRegister.triple c₁ c₂ anc h₁₂ h₁a h₂a).embedMatrix_comm_of_disjoint rScrMid hT_mid_disj
        PrimitiveGate.toffoli.eval.1 (compProj 0)
    have hT_sq : T_anc * T_anc = 1 := by
      dsimp [T_anc, Circuit.TOFF, Circuit.eval]
      rw [← QRegister.embedUnitary_mul]
      simp [PrimitiveGate.eval, PrimitiveGate.toffoliUnitary]
    have hTW_eq : W_mid * T_anc = T_anc * V := by
      dsimp [V]; rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
    have hAct_comm_anc : (rAct.embedUnitary U_act).1 * rAnc1.basisOutcomeProjector 0 =
        rAnc1.basisOutcomeProjector 0 * (rAct.embedUnitary U_act).1 :=
      rAct.embedMatrix_comm_of_disjoint rAnc1 hActAnc U_act.1 (compProj 0)
    have hV_P₀ : rAnc1.basisOutcomeProjector 0 * (V.1 * rAnc1.basisOutcomeProjector 0) =
        V.1 * rAnc1.basisOutcomeProjector 0 := by
      have hU' : V.1 * rAnc1.basisOutcomeProjector 0 =
          (rAct.embedUnitary U_act).1 * rAnc1.basisOutcomeProjector 0 := hU
      rw [hU', hAct_comm_anc, ← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]
    have hV_restrict (Ψ : QCAssertion Var (2 ^ N)) :
        restrictAssertionToZeroAncilla (qcWpQAssign V (restrictAssertionToZeroAncilla Ψ rAnc1))
          rAnc1 =
        restrictAssertionToZeroAncilla (qcWpQAssign V Ψ) rAnc1 := by
      funext σ'; apply Subtype.ext
      have hadj : rAnc1.basisOutcomeProjector 0 * V.1ᴴ * rAnc1.basisOutcomeProjector 0 =
          rAnc1.basisOutcomeProjector 0 * V.1ᴴ := by
        have h := congrArg conjTranspose hV_P₀
        simpa [conjTranspose_mul, rAnc1.basisOutcomeProjector_conjTranspose 0,
          ← Matrix.mul_assoc] using h
      simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
      rw [← Matrix.mul_assoc, hadj]
    have hswap (A : QCAssertion Var (2 ^ N)) :
        restrictAssertionToZeroAncilla A rScr =
          restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla A rScrMid) rAnc1 := by
      rw [restrict_concat rAnc1 rScrMid hAncMid]
      funext σ'; apply Subtype.ext
      have hcomm : rScrMid.basisOutcomeProjector 0 * rAnc1.basisOutcomeProjector 0 =
          rAnc1.basisOutcomeProjector 0 * rScrMid.basisOutcomeProjector 0 :=
        QRegister.embedMatrix_comm_of_disjoint rScrMid rAnc1 (QRegister.disjoint_comm.mp hAncMid)
          (compProj 0) (compProj 0)
      simp only [restrictAssertionToZeroAncilla_coe, conj_conj, hcomm]
    change restrictAssertionToZeroAncilla
      (wp (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
        (wp mid.compile U_uncomp)) rScr = _
    rw [restrict_concat rAnc1 rScrMid hAncMid,
      DynamicCircuit.qc_wp_andCompute c₁ c₂ anc h₁₂ h₁a h₂a,
      ← restrict_concat rAnc1 rScrMid hAncMid, hswap,
      ← restrict_wp_qAssign_comm_of_comm T_anc rScrMid hT_comm_mid,
      hmid.2.2.1 U_uncomp huncomp_inv,
      restrict_wp_qAssign_comm_of_comm T_anc rScrMid hT_comm_mid,
      ← hswap, qc_wp_qAssign_comp, hTW_eq, ← qc_wp_qAssign_comp,
      restrict_concat rAnc1 rScrMid hAncMid,
      ← hV_restrict,
      DynamicCircuit.qc_wp_toffoli_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ,
      hV_restrict, ← restrict_concat rAnc1 rScrMid hAncMid]
    funext σ'; apply Subtype.ext
    have hadj : rAnc1.basisOutcomeProjector 0 * V.1ᴴ =
        rAnc1.basisOutcomeProjector 0 * (rAct.embedUnitary U_act).1ᴴ := by
      have hU' : V.1 * rAnc1.basisOutcomeProjector 0 =
          (rAct.embedUnitary U_act).1 * rAnc1.basisOutcomeProjector 0 := hU
      have h := congrArg conjTranspose hU'
      simpa only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
    have hproj : rScr.basisOutcomeProjector 0 =
        rScrMid.basisOutcomeProjector 0 * rAnc1.basisOutcomeProjector 0 := by
      rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
        QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext g
      have heq : rScr.extractIndex g = 0 ↔
          rScrMid.extractIndex g = 0 ∧ rAnc1.extractIndex g = 0 := by
        dsimp only [rScr]
        simp only [extractIndex_eq_zero_iff_basisBits_eq_zero]
        refine ⟨fun h ↦ ⟨fun j ↦ by simpa using h (Fin.natAdd 1 j),
            fun i ↦ by simpa using h (Fin.castAdd s i)⟩,
          fun ⟨h₂, h₁⟩ idx ↦ ?_⟩
        obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
        · simpa using h₁ i
        · simpa using h₂ j
      by_cases h₂ : rScrMid.extractIndex g = 0 <;> by_cases h₁ : rAnc1.extractIndex g = 0 <;>
        simp [heq, h₁, h₂]
    simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [hproj, Matrix.mul_assoc, hadj, ← Matrix.mul_assoc]

/-- Local `(k + 1)`-qubit specialization of `CleanRealizes.andSandwich` when `c₁ = rAct i₁` and
`c₂ = rAct i₂`. -/
theorem CleanRealizes.andSandwich_local {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (i₁ i₂ : Fin k) (hi₁₂ : i₁ ≠ i₂)
    (anc : Wire N) (hActAnc : rAct.DisjointWires (QRegister.singleton anc))
    (rScrMid : QRegister s N)
    (hAncMid : (QRegister.singleton anc).DisjointWires rScrMid)
    (hActMid : rAct.DisjointWires rScrMid)
    (U_mid : Unitary (2 ^ (k + 1))) (U_act : Unitary (2 ^ k))
    (mid : DynamicCircuit Var N)
    (hmid : CleanRealizes v (rAct.concat (QRegister.singleton anc) hActAnc) rScrMid U_mid mid)
    (hU_loc :
      let anc_loc : Wire (k + 1) := Fin.natAdd k 0
      let c₁_loc : Wire (k + 1) := Fin.castAdd 1 i₁
      let c₂_loc : Wire (k + 1) := Fin.castAdd 1 i₂
      let h₁₂_loc : c₁_loc ≠ c₂_loc := (Fin.castAdd_injective k 1).ne hi₁₂
      let h₁a_loc : c₁_loc ≠ anc_loc := by intro h; simp [c₁_loc, anc_loc, Fin.ext_iff] at h; omega
      let h₂a_loc : c₂_loc ≠ anc_loc := by intro h; simp [c₂_loc, anc_loc, Fin.ext_iff] at h; omega
      let P₀_loc := (QRegister.singleton anc_loc).basisOutcomeProjector 0
      let T_loc := (Circuit.TOFF c₁_loc c₂_loc anc_loc h₁₂_loc h₁a_loc h₂a_loc).eval
      let rAct_sub : QRegister k (k + 1) := .block 0 k (by omega)
      T_loc.1 * U_mid.1 * T_loc.1 * P₀_loc = (rAct_sub.embedUnitary U_act).1 * P₀_loc) :
    CleanRealizes v rAct ((QRegister.singleton anc).concat rScrMid hAncMid) U_act
      (andSandwichProg v (rAct i₁) (rAct i₂) anc
        (rAct.wires.injective.ne hi₁₂) (hActAnc.ne i₁ 0) (hActAnc.ne i₂ 0) mid) := by
  let rActExt := rAct.concat (QRegister.singleton anc) hActAnc
  let anc_loc : Wire (k + 1) := Fin.natAdd k 0
  let c₁_loc : Wire (k + 1) := Fin.castAdd 1 i₁
  let c₂_loc : Wire (k + 1) := Fin.castAdd 1 i₂
  have h₁₂_loc : c₁_loc ≠ c₂_loc := (Fin.castAdd_injective k 1).ne hi₁₂
  have h₁a_loc : c₁_loc ≠ anc_loc := by intro h; simp [c₁_loc, anc_loc, Fin.ext_iff] at h; omega
  have h₂a_loc : c₂_loc ≠ anc_loc := by intro h; simp [c₂_loc, anc_loc, Fin.ext_iff] at h; omega
  have h₁₂ : rAct i₁ ≠ rAct i₂ := rAct.wires.injective.ne hi₁₂
  have h₁a : rAct i₁ ≠ anc := hActAnc.ne i₁ 0
  have h₂a : rAct i₂ ≠ anc := hActAnc.ne i₂ 0
  refine CleanRealizes.andSandwich v rAct (rAct i₁) (rAct i₂) anc h₁₂ h₁a h₂a
    hActAnc rScrMid hAncMid hActMid
    (hActMid.apply_not_mem_right i₁) (hActMid.apply_not_mem_right i₂)
    U_mid U_act mid hmid ?_
  have hP₀ : (QRegister.singleton anc).basisOutcomeProjector 0 =
      rActExt.embedMatrix ((QRegister.singleton anc_loc).basisOutcomeProjector 0) := by
    have hcomp : rActExt.compose (QRegister.singleton anc_loc) = QRegister.singleton anc := by
      ext j; fin_cases j; simp [rActExt, anc_loc]
    rw [← hcomp, compose_basisOutcomeProjector]
  have hT : (Circuit.TOFF (rAct i₁) (rAct i₂) anc h₁₂ h₁a h₂a).eval =
      rActExt.embedUnitary (Circuit.TOFF c₁_loc c₂_loc anc_loc h₁₂_loc h₁a_loc h₂a_loc).eval := by
    have hcomp : rActExt.compose (QRegister.triple c₁_loc c₂_loc anc_loc h₁₂_loc h₁a_loc h₂a_loc) =
        QRegister.triple (rAct i₁) (rAct i₂) anc h₁₂ h₁a h₂a := by
      ext j; fin_cases j <;> simp [rActExt, c₁_loc, c₂_loc, anc_loc]
    dsimp [Circuit.TOFF]
    rw [← hcomp, QRegister.embedUnitary_compose]
  have hAct : rAct.embedUnitary U_act =
      rActExt.embedUnitary ((QRegister.block 0 k (by omega)).embedUnitary U_act) := by
    have hcomp : rActExt.compose (QRegister.block 0 k (by omega)) = rAct := by
      ext j
      have hj : QRegister.block 0 k (by omega : 0 + k ≤ k + 1) j = Fin.castAdd 1 j := by
        ext; simp
      simp [rActExt, hj]
    rw [← QRegister.embedUnitary_compose, hcomp]
  dsimp only
  rw [hP₀, hT, hAct]
  dsimp only [rActExt, c₁_loc, c₂_loc, anc_loc]
  simp only [QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul]
  have hU_loc' :
      (Circuit.TOFF (Fin.castAdd 1 i₁) (Fin.castAdd 1 i₂) (Fin.natAdd k 0)
          h₁₂_loc h₁a_loc h₂a_loc).eval.1 * U_mid.1 *
        (Circuit.TOFF (Fin.castAdd 1 i₁) (Fin.castAdd 1 i₂) (Fin.natAdd k 0)
          h₁₂_loc h₁a_loc h₂a_loc).eval.1 *
        (QRegister.singleton (Fin.natAdd k 0)).basisOutcomeProjector 0 =
      ((QRegister.block 0 k (by omega)).embedMatrix U_act.1) *
        (QRegister.singleton (Fin.natAdd k 0)).basisOutcomeProjector 0 := hU_loc
  exact congrArg (rAct.concat (QRegister.singleton anc) hActAnc).embedMatrix hU_loc'

/-! ## Top-Level Program Packaging, `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` & Born
Marginalization -/

/-- Relocate a local `(k + m)`-wire `DynamicCircuit` onto `(rSys, rAnc)` when disjoint, falling back
to `.identity` otherwise so gate-count bounds hold unconditionally without `hdisj`. -/
def topProg {Var : Type} {k m n : ℕ}
    (P_loc : DynamicCircuit Var (k + m))
    (rSys : QRegister k n) (rAnc : QRegister m n) : DynamicCircuit Var n :=
  if hdisj : rSys.DisjointWires rAnc then
    P_loc.onRegister (rSys.concat rAnc hdisj)
  else
    .identity

theorem topProg_of_disjoint {Var : Type} {k m n : ℕ}
    (P_loc : DynamicCircuit Var (k + m))
    (rSys : QRegister k n) (rAnc : QRegister m n) (hdisj : rSys.DisjointWires rAnc) :
    topProg P_loc rSys rAnc = P_loc.onRegister (rSys.concat rAnc hdisj) := by
  simp [topProg, hdisj]

theorem count_topProg_toff {Var : Type} {k m n : ℕ}
    (P_loc : DynamicCircuit Var (k + m))
    (rSys : QRegister k n) (rAnc : QRegister m n)
    (htoff : P_loc.count PrimitiveGate.TOFF = 0) :
    (topProg P_loc rSys rAnc).count PrimitiveGate.TOFF = 0 := by
  by_cases hdisj : rSys.DisjointWires rAnc <;> simp [topProg, hdisj, htoff]

theorem count_topProg_t_le {Var : Type} {k m n : ℕ}
    (P_loc : DynamicCircuit Var (k + m))
    (rSys : QRegister k n) (rAnc : QRegister m n) :
    (topProg P_loc rSys rAnc).count PrimitiveGate.T ≤ P_loc.count PrimitiveGate.T := by
  by_cases hdisj : rSys.DisjointWires rAnc <;> simp [topProg, hdisj]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

export CleanDyn (
  embedObservable envIso pullbackObs pullbackAssertion pullbackAssertion_wp_onRegister
  cqAssertion_eq_of_pullbackAssertion_eq CleanRealizes
  restrictAssertionToZeroAncilla_wp_restrict_eq_of_clean substGate substCircuit
  substToffoliWithAncilla count_substToffoliWithAncilla_toff count_substToffoliWithAncilla_t
  cleanRealizes_substToffoliWithAncilla_singleton cleanRealizes_substToffoliWithAncilla
  andSandwichProg count_andSandwichProg_toff count_andSandwichProg_t topProg topProg_of_disjoint
  count_topProg_toff count_topProg_t_le
)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
