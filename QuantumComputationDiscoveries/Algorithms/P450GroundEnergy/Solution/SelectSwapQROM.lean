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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.Circuits.Toffoli
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs

/-!
# Parametric SelectSwap QROM and Measurement-Based Uncomputation

Provides Toffoli-free (`PrimitiveGate.TOFF` count `0`), single-classical-variable (`v : Var`)
dynamic circuits for quantum read-only memory (QROM) loading and measurement-based unloading,
following Low, Kliuchnikov, and Schaeffer (arXiv:1812.00954, 2018), Babbush et al.
(Phys. Rev. X 8, 041015, 2018), and Berry et al. (Quantum 3, 208, 2019):

- `CleanRealizes`: 4-conjunct clean-ancilla specification contract for single-variable dynamic
  circuits (`TOFF = 0`, `v`-store invariance, clean-ancilla `wp` equivalence, and clean-ancilla
  postcondition restoration).
- `unaryIterDyn` and `unaryQromLoadDyn`: MSB-first pruned unary iteration over `[0, B)` using
  Cody Jones' 4-`T` `andCompute` and `0-T` `andUncompute`, exact on all `2^k` basis states.
- `selectSwapLoadDyn`: parametric `λ = 2^s` forward SelectSwap QROM loading `2^s` `W`-bit words
  into a staging buffer and routing the selected word into slot `0` via a `(2^s - 1) * W` Fredkin
  swap network.
- `selectSwapPhaseFixupDyn`: `1`-bit phase fixup using algebraic normal form (ANF) over `ZMod 2`,
  requiring `2^s - s - 1` temporary-AND computations on the low `s` index bits plus pruned unary
  iteration on the high `k` index bits.
- `measureXResetAndBranch`, `qromXMeasUnloadDyn`, `chunkedXMeasUnloadDyn`,
  `selectSwapCleanLoadDyn`, and `selectSwapSandwichDyn`: `0-T` X-basis measurement and reset of
  loaded table or staging registers followed by `1`-bit phase fixup, using only classical variable
  `v` and `0` phase-accumulator qubits.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-!
## Section 1: Clean-Ancilla Specification Contract and Basis-Ket Helpers
-/

/-- Four-conjunct clean-ancilla realization contract for a dynamic circuit `P` using only scratch
classical variable `v : Var` and clean quantum scratch register `rScr`. -/
abbrev CleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ} [NeZero (2 ^ N)]
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

/-- Orthogonal projector onto computational-basis states whose bits on wire set `S` are all `0`. -/
noncomputable def zeroProjOn {N : ℕ} (S : Finset (Wire N)) : Operator (2 ^ N) :=
  Matrix.diagonal fun g ↦ if ∀ w ∈ S, basisBits N g w = 0 then 1 else 0

@[simp]
theorem zeroProjOn_empty {N : ℕ} : zeroProjOn (∅ : Finset (Wire N)) = 1 := by
  simp [zeroProjOn]

@[simp]
theorem zeroProjOn_conjTranspose {N : ℕ} (S : Finset (Wire N)) :
    (zeroProjOn S)ᴴ = zeroProjOn S := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ∀ w ∈ S, basisBits N i w = 0 <;> simp [zeroProjOn, h]
  · simp [zeroProjOn, hij, Ne.symm hij]

@[simp]
theorem zeroProjOn_mul_union {N : ℕ} (S₁ S₂ : Finset (Wire N)) :
    zeroProjOn S₁ * zeroProjOn S₂ = zeroProjOn (S₁ ∪ S₂) := by
  simp only [zeroProjOn, Matrix.diagonal_mul_diagonal]
  congr 1
  funext g
  have hiff : ((∀ w ∈ S₁, basisBits N g w = 0) ∧ (∀ w ∈ S₂, basisBits N g w = 0)) ↔
      (∀ w ∈ S₁ ∪ S₂, basisBits N g w = 0) := by
    constructor
    · rintro ⟨h₁, h₂⟩ w hw
      rcases Finset.mem_union.mp hw with hw₁ | hw₂
      · exact h₁ w hw₁
      · exact h₂ w hw₂
    · intro hu
      exact ⟨fun w hw ↦ hu w (Finset.mem_union_left S₂ hw),
        fun w hw ↦ hu w (Finset.mem_union_right S₁ hw)⟩
  by_cases h₁ : ∀ w ∈ S₁, basisBits N g w = 0 <;>
    by_cases h₂ : ∀ w ∈ S₂, basisBits N g w = 0
  · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_left (hiff.mp ⟨h₁, h₂⟩), mul_one]
  · have hu : ¬∀ w ∈ S₁ ∪ S₂, basisBits N g w = 0 := fun h ↦ h₂ (hiff.mpr h).2
    rw [ite_eq_left h₁, ite_eq_right h₂, ite_eq_right hu, mul_zero]
  · have hu : ¬∀ w ∈ S₁ ∪ S₂, basisBits N g w = 0 := fun h ↦ h₁ (hiff.mpr h).1
    rw [ite_eq_right h₁, ite_eq_right hu, zero_mul]
  · have hu : ¬∀ w ∈ S₁ ∪ S₂, basisBits N g w = 0 := fun h ↦ h₁ (hiff.mpr h).1
    rw [ite_eq_right h₁, ite_eq_right hu, zero_mul]

theorem zeroProjOn_mul_self {N : ℕ} (S : Finset (Wire N)) :
    zeroProjOn S * zeroProjOn S = zeroProjOn S := by
  rw [zeroProjOn_mul_union, Finset.union_idempotent]

theorem zeroProjOn_comm {N : ℕ} (S₁ S₂ : Finset (Wire N)) :
    zeroProjOn S₁ * zeroProjOn S₂ = zeroProjOn S₂ * zeroProjOn S₁ := by
  rw [zeroProjOn_mul_union, zeroProjOn_mul_union, Finset.union_comm]

theorem basisOutcomeProjector_zero_eq_zeroProjOn {N m : ℕ} (r : QRegister m N) :
    r.basisOutcomeProjector 0 = zeroProjOn r.image := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, zeroProjOn]
  congr 1
  funext g
  have hiff : r.extractIndex g = 0 ↔ ∀ w ∈ r.image, basisBits N g w = 0 := by
    constructor
    · intro h0 w hw
      rw [QRegister.mem_image] at hw
      obtain ⟨i, rfl⟩ := hw
      have hi : basisBits m (r.extractIndex g) i = 0 := by
        rw [h0, basisBits_eq_div_mod]
        simp
      simpa only [QRegister.basisBits_extractIndex] using hi
    · intro hall
      apply (basisBits m).injective
      funext i
      have hmem : r i ∈ r.image := (QRegister.mem_image r (r i)).mpr ⟨i, rfl⟩
      rw [QRegister.basisBits_extractIndex, hall (r i) hmem, basisBits_eq_div_mod]
      simp
  by_cases h : r.extractIndex g = 0
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]

/-- Restrict a classical-quantum assertion `M` branchwise onto `zeroProjOn S`. -/
noncomputable def restrictZeroSet {Var : Type} [Fintype Var] {N : ℕ}
    (M : QCAssertion Var (2 ^ N)) (S : Finset (Wire N)) : QCAssertion Var (2 ^ N) :=
  fun σ ↦ ⟨HermitianMat.conj (zeroProjOn S) (M σ).1, by
    constructor
    · exact (M σ).1.conj_nonneg (zeroProjOn S) (M σ).2.1
    · apply (HermitianMat.conj_mono (M σ).2.2).trans
      apply HermitianMat.le_iff.mpr
      change (1 - (1 : HermitianMat (Fin (2 ^ N)) ℂ).conj (zeroProjOn S)).mat.PosSemidef
      simp only [HermitianMat.mat_sub, HermitianMat.mat_one, conj_apply_mat,
        Matrix.mul_one, zeroProjOn_conjTranspose, zeroProjOn_mul_self]
      rw [zeroProjOn, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
      intro g
      by_cases h : ∀ w ∈ S, basisBits N g w = 0
      · rw [ite_eq_left h]; simp
      · rw [ite_eq_right h]; simp⟩

@[simp]
theorem restrictZeroSet_coe {Var : Type} [Fintype Var] {N : ℕ}
    (M : QCAssertion Var (2 ^ N)) (S : Finset (Wire N)) (σ : Store Var) :
    (restrictZeroSet M S σ).1 = (M σ).1.conj (zeroProjOn S) := rfl

theorem restrictAssertionToZeroAncilla_eq_restrictZeroSet {Var : Type} [Fintype Var] {N m : ℕ}
    (M : QCAssertion Var (2 ^ N)) (r : QRegister m N) :
    restrictAssertionToZeroAncilla M r = restrictZeroSet M r.image := by
  funext σ
  apply Subtype.ext
  simp [restrictZeroSet_coe, basisOutcomeProjector_zero_eq_zeroProjOn]

theorem restrictZeroSet_union {Var : Type} [Fintype Var] {N : ℕ}
    (M : QCAssertion Var (2 ^ N)) (S₁ S₂ : Finset (Wire N)) :
    restrictZeroSet (restrictZeroSet M S₁) S₂ = restrictZeroSet M (S₁ ∪ S₂) := by
  funext σ
  apply Subtype.ext
  simp only [restrictZeroSet_coe, conj_conj, zeroProjOn_comm S₂ S₁, zeroProjOn_mul_union]

theorem restrictZeroSet_idem {Var : Type} [Fintype Var] {N : ℕ}
    (M : QCAssertion Var (2 ^ N)) (S : Finset (Wire N)) :
    restrictZeroSet (restrictZeroSet M S) S = restrictZeroSet M S := by
  rw [restrictZeroSet_union, Finset.union_idempotent]

theorem restrictZeroSet_insert {Var : Type} [Fintype Var] {N : ℕ}
    (M : QCAssertion Var (2 ^ N)) (w : Wire N) (S : Finset (Wire N)) :
    restrictZeroSet M (insert w S) =
      restrictZeroSet (restrictAssertionToZeroAncilla M (QRegister.singleton w)) S := by
  rw [restrictAssertionToZeroAncilla_eq_restrictZeroSet, QRegister.image_singleton,
    restrictZeroSet_union, Finset.singleton_union]

theorem restrictZeroSet_insert_outer {Var : Type} [Fintype Var] {N : ℕ}
    (M : QCAssertion Var (2 ^ N)) (w : Wire N) (S : Finset (Wire N)) :
    restrictZeroSet M (insert w S) =
      restrictAssertionToZeroAncilla (restrictZeroSet M S) (QRegister.singleton w) := by
  rw [restrictAssertionToZeroAncilla_eq_restrictZeroSet, QRegister.image_singleton,
    restrictZeroSet_union, Finset.union_singleton]

/-- Ambient-unitary version of `CleanRealizes` indexed by a `Finset` of clean scratch wires. -/
def CleanRealizesSet {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (S : Finset (Wire N)) (U : Unitary (2 ^ N)) (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    restrictZeroSet (wp P.compile Θ) S = restrictZeroSet (qcWpQAssign U Θ) S) ∧
  (∀ Θ : QCAssertion Var (2 ^ N),
    restrictZeroSet (wp P.compile (restrictZeroSet Θ S)) S = restrictZeroSet (wp P.compile Θ) S)

theorem cleanRealizes_iff_set {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    [NeZero (2 ^ N)] (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (U : Unitary (2 ^ k)) (P : DynamicCircuit Var N) :
    CleanRealizes v rAct rScr U P ↔
      CleanRealizesSet v rScr.image (rAct.embedUnitary U) P := by
  simp only [CleanRealizes, CleanRealizesSet, restrictAssertionToZeroAncilla_eq_restrictZeroSet]

theorem CleanRealizesSet.identity {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N)) :
    CleanRealizesSet v S 1 (.identity : DynamicCircuit Var N) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    exact hΘ σ val
  · intro Θ _
    funext σ
    apply Subtype.ext
    simp [qcWpQAssign]
  · intro Θ
    simpa [wp] using restrictZeroSet_idem Θ S

theorem CleanRealizesSet.seq {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)} {U₁ U₂ : Unitary (2 ^ N)}
    {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : CleanRealizesSet v S U₁ P₁) (h₂ : CleanRealizesSet v S U₂ P₂) :
    CleanRealizesSet v S (U₂ * U₁) (.seq P₁ P₂) := by
  refine ⟨by simp [h₁.1, h₂.1], ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    change wp P₁.compile (wp P₂.compile Θ) (Function.update σ v val) =
      wp P₁.compile (wp P₂.compile Θ) σ
    exact h₁.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ) σ val
  · intro Θ hΘ
    change restrictZeroSet (wp P₁.compile (wp P₂.compile Θ)) S =
      restrictZeroSet (qcWpQAssign (U₂ * U₁) Θ) S
    rw [← h₁.2.2.2 (wp P₂.compile Θ), h₂.2.2.1 Θ hΘ, h₁.2.2.2 (qcWpQAssign U₂ Θ),
      h₁.2.2.1 (qcWpQAssign U₂ Θ) (fun σ val ↦ by simp [qcWpQAssign, hΘ σ val]), qc_wp_qAssign_comp]
  · intro Θ
    change restrictZeroSet (wp P₁.compile (wp P₂.compile (restrictZeroSet Θ S))) S =
      restrictZeroSet (wp P₁.compile (wp P₂.compile Θ)) S
    rw [← h₁.2.2.2 (wp P₂.compile (restrictZeroSet Θ S)), h₂.2.2.2 Θ, h₁.2.2.2 (wp P₂.compile Θ)]

theorem CleanRealizes.seq {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    [NeZero (2 ^ N)] {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U₁ U₂ : Unitary (2 ^ k)} {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : CleanRealizes v rAct rScr U₁ P₁) (h₂ : CleanRealizes v rAct rScr U₂ P₂) :
    CleanRealizes v rAct rScr (U₂ * U₁) (.seq P₁ P₂) := by
  rw [cleanRealizes_iff_set, QRegister.embedUnitary_mul]
  exact ((cleanRealizes_iff_set v rAct rScr U₁ P₁).mp h₁).seq
    ((cleanRealizes_iff_set v rAct rScr U₂ P₂).mp h₂)

/-!
### Computational-Basis Ket Calculus
-/

/-- Global `N`-qubit computational-basis ket indexed by bit assignment `β : BitAssignment N`. -/
noncomputable abbrev ket {N : ℕ} (β : BitAssignment N) : Fin (2 ^ N) → ℂ :=
  basisState ((basisBits N).symm β)

theorem basisBits_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

theorem symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem single_eq_ket {N : ℕ} (g : Fin (2 ^ N)) :
    (Pi.single g 1 : Fin (2 ^ N) → ℂ) = ket (basisBits N g) := by
  simp [ket, basisState]

theorem matrix_ext_ket {N : ℕ} {A B : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (h : ∀ β : BitAssignment N, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits N j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

theorem zeroProjOn_mulVec_ket {N : ℕ} (S : Finset (Wire N)) (β : BitAssignment N) :
    (zeroProjOn S).mulVec (ket β) = if ∀ w ∈ S, β w = 0 then ket β else 0 := by
  funext i
  rw [zeroProjOn, Matrix.mulVec_diagonal]
  by_cases hi : i = (basisBits N).symm β
  · subst hi
    simp only [ket, basisState, Pi.single_eq_same, basisBits_symm, mul_one]
    by_cases h : ∀ w ∈ S, β w = 0
    · rw [ite_eq_left h, ite_eq_left h, Pi.single_eq_same]
    · rw [ite_eq_right h, ite_eq_right h]; rfl
  · simp only [ket, basisState, Pi.single_eq_of_ne hi, mul_zero]
    by_cases h : ∀ w ∈ S, β w = 0
    · rw [ite_eq_left h, Pi.single_eq_of_ne hi]
    · rw [ite_eq_right h]; rfl

theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem disjoint_image_of_disjointWires {N k m : ℕ} {r₁ : QRegister k N} {r₂ : QRegister m N}
    (h : r₁.DisjointWires r₂) : Disjoint r₁.image r₂.image := by
  rw [Finset.disjoint_left]
  intro w hw₁ hw₂
  obtain ⟨i, rfl⟩ := (QRegister.mem_image r₁ w).mp hw₁
  obtain ⟨j, hj⟩ := (QRegister.mem_image r₂ _).mp hw₂
  exact h.ne i j hj.symm

theorem singleton_projector_zero_mulVec_ket {N : ℕ} (w : Wire N) (β : BitAssignment N) :
    ((QRegister.singleton w).basisOutcomeProjector 0).mulVec (ket β) =
      if β w = 0 then ket β else 0 := by
  rw [basisOutcomeProjector_zero_eq_zeroProjOn, QRegister.image_singleton, zeroProjOn_mulVec_ket]
  simp

theorem singleton_projector_one_mulVec_ket {N : ℕ} (w : Wire N) (β : BitAssignment N) :
    ((QRegister.singleton w).basisOutcomeProjector 1).mulVec (ket β) =
      if β w = 1 then ket β else 0 := by
  have hext : (QRegister.singleton w).extractIndex ((basisBits N).symm β) =
      if β w = 1 then 1 else 0 := by
    apply (basisBits 1).injective
    funext i
    rw [QRegister.basisBits_extractIndex, basisBits_symm, QRegister.singleton_apply]
    fin_cases i
    rcases bit_cases (β w) with hb | hb <;> (rw [hb]; decide)
  simpa only [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single, hext] using
    (by split_ifs <;> simp_all :
      (if (if β w = 1 then (1 : Fin 2) else 0) = 1 then ket β else 0) =
        if β w = 1 then ket β else 0)

theorem CleanRealizesSet.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)} {U₁ U₂ : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N}
    (h : CleanRealizesSet v S U₁ P)
    (hEq : ∀ β : BitAssignment N, (∀ w ∈ S, β w = 0) →
      U₁.1.mulVec (ket β) = U₂.1.mulVec (ket β)) :
    CleanRealizesSet v S U₂ P := by
  have hMat : U₁.1 * zeroProjOn S = U₂.1 * zeroProjOn S := by
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
    by_cases hβ : ∀ w ∈ S, β w = 0
    · rw [ite_eq_left hβ, hEq β hβ]
    · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hAdj : zeroProjOn S * U₁.1ᴴ = zeroProjOn S * U₂.1ᴴ := by
    have h' := congrArg conjTranspose hMat
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro Θ hΘ
  rw [h.2.2.1 Θ hΘ]
  funext σ
  apply Subtype.ext
  simp only [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [hAdj]

/-- Lift a Toffoli-free static `Circuit N` whose unitary maps `zeroProjOn S` into itself. -/
theorem CleanRealizesSet.ofCircuit {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N)) (c : Circuit N)
    (hToff : c.count PrimitiveGate.TOFF = 0)
    (hPres : ∀ β : BitAssignment N, (∀ w ∈ S, β w = 0) →
      (zeroProjOn S).mulVec (c.eval.1.mulVec (ket β)) = c.eval.1.mulVec (ket β)) :
    CleanRealizesSet v S c.eval (.circuit c) := by
  have hMat : zeroProjOn S * c.eval.1 * zeroProjOn S = c.eval.1 * zeroProjOn S := by
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
    by_cases hβ : ∀ w ∈ S, β w = 0
    · rw [ite_eq_left hβ]
      simpa only [zeroProjOn_mulVec_ket] using hPres β hβ
    · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hAdj : zeroProjOn S * c.eval.1ᴴ * zeroProjOn S = zeroProjOn S * c.eval.1ᴴ := by
    have h' := congrArg conjTranspose hMat
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose, ← Matrix.mul_assoc] using h'
  refine ⟨hToff, ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    simp [qcWpQAssign, hΘ σ val]
  · intro Θ _
    simp
  · intro Θ
    funext σ
    apply Subtype.ext
    simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
      restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc, hAdj]

/-!
### Frame Commutation with Disjoint Clean-Wire Projectors
-/

private theorem circuit_comm_zeroProjOn {N : ℕ} (c : Circuit N) (S : Finset (Wire N))
    (hDisj : Disjoint c.support S) :
    c.eval.1 * zeroProjOn S = zeroProjOn S * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g r =>
    ext i j
    simp only [Circuit.eval_gate, QRegister.embedUnitary_val, zeroProjOn,
      Matrix.mul_diagonal, Matrix.diagonal_mul, QRegister.embedMatrix_apply_of_agreeOutside]
    by_cases hAg : r.AgreeOutside i j
    · have hSame : (∀ w ∈ S, basisBits N i w = 0) ↔ (∀ w ∈ S, basisBits N j w = 0) := by
        refine ⟨fun hi w hw ↦ ?_, fun hj w hw ↦ ?_⟩
        · have hwNot : w ∉ Set.range r.wires := by
            rintro ⟨idx, rfl⟩
            exact Finset.disjoint_left.mp hDisj ((QRegister.mem_image r (r idx)).mpr ⟨idx, rfl⟩) hw
          rw [← hAg w hwNot]
          exact hi w hw
        · have hwNot : w ∉ Set.range r.wires := by
            rintro ⟨idx, rfl⟩
            exact Finset.disjoint_left.mp hDisj ((QRegister.mem_image r (r idx)).mpr ⟨idx, rfl⟩) hw
          rw [hAg w hwNot]
          exact hj w hw
      by_cases hi : ∀ w ∈ S, basisBits N i w = 0
      · rw [ite_eq_left hAg, ite_eq_left hi, ite_eq_left (hSame.mp hi)]; ring
      · rw [ite_eq_left hAg, ite_eq_right hi, ite_eq_right (mt hSame.mpr hi)]; ring
    · rw [ite_eq_right hAg]; ring
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Circuit.support_seq, Finset.disjoint_union_left] at hDisj
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    rw [Matrix.mul_assoc, ih₁ hDisj.1, ← Matrix.mul_assoc, ih₂ hDisj.2, Matrix.mul_assoc]

private theorem measure_comm_zeroProjOn {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] (v : Var) (w : Wire N) (S : Finset (Wire N))
    (Θ : QCAssertion Var (2 ^ N)) :
    wp (DynamicCircuit.measure v (QRegister.singleton w)).compile (restrictZeroSet Θ S) =
      restrictZeroSet (wp (DynamicCircuit.measure v (QRegister.singleton w)).compile Θ) S := by
  funext σ
  apply Subtype.ext
  change (wp (QProg.measureRegister v (QRegister.singleton w)) (restrictZeroSet Θ S) σ).1 =
    (restrictZeroSet (wp (QProg.measureRegister v (QRegister.singleton w)) Θ) S σ).1
  simp only [qc_wp_qMeasure', QProg.measureRegister, qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe,
    QCAssertion.subst_apply, restrictZeroSet_coe, map_sum, qc_qMeasure_outcome_herm_eq_conj,
    CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply, conj_conj]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  have hcomm : zeroProjOn S * ((QRegister.singleton w).basisOutcomeProjector o)ᴴ =
      ((QRegister.singleton w).basisOutcomeProjector o)ᴴ * zeroProjOn S := by
    rw [QRegister.basisOutcomeProjector_conjTranspose, QRegister.basisOutcomeProjector_eq_diagonal,
      zeroProjOn, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext g
    ring
  rw [hcomm]

/-- A dynamic circuit whose syntactic support is disjoint from `S` commutes unconditionally with
`restrictZeroSet _ S` inside `wp`. -/
theorem wp_restrictZeroSet_of_disjoint {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] (P : DynamicCircuit Var N) (S : Finset (Wire N))
    (hDisj : Disjoint P.support S) (Θ : QCAssertion Var (2 ^ N)) :
    wp P.compile (restrictZeroSet Θ S) = restrictZeroSet (wp P.compile Θ) S := by
  induction P using DynamicCircuit.qcInd generalizing Θ with
  | circuit c =>
    funext σ
    apply Subtype.ext
    have hcomm := circuit_comm_zeroProjOn c S hDisj
    have hadj : (c.eval.1)ᴴ * zeroProjOn S = zeroProjOn S * (c.eval.1)ᴴ := by
      have h' := congrArg conjTranspose hcomm
      simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'.symm
    simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
      restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [hadj]
  | measure v r =>
    have hr : r = QRegister.singleton (r 0) := by
      ext i
      fin_cases i
      rfl
    rw [hr]
    exact measure_comm_zeroProjOn v (r 0) S Θ
  | qIf cond t f iht ihf =>
    simp only [DynamicCircuit.support_qcRawQIf, Finset.disjoint_union_left] at hDisj
    funext σ
    apply Subtype.ext
    change (if cond.holds σ then wp t.compile (restrictZeroSet Θ S) σ
        else wp f.compile (restrictZeroSet Θ S) σ).1 =
      ((if cond.holds σ then wp t.compile Θ σ else wp f.compile Θ σ).1).conj (zeroProjOn S)
    split_ifs
    · exact congrArg Subtype.val (congrFun (iht hDisj.1 Θ) σ)
    · exact congrArg Subtype.val (congrFun (ihf hDisj.2 Θ) σ)
  | seq p₁ p₂ ih₁ ih₂ =>
    simp only [DynamicCircuit.support_seq, Finset.disjoint_union_left] at hDisj
    change wp p₁.compile (wp p₂.compile (restrictZeroSet Θ S)) =
      restrictZeroSet (wp p₁.compile (wp p₂.compile Θ)) S
    rw [ih₂ hDisj.2 Θ, ih₁ hDisj.1 (wp p₂.compile Θ)]

theorem CleanRealizesSet.extend {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S₁ S₂ : Finset (Wire N)} {U : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N}
    (h : CleanRealizesSet v S₁ U P) (hSub : S₁ ⊆ S₂)
    (hDisjP : Disjoint P.support (S₂ \ S₁)) :
    CleanRealizesSet v S₂ U P := by
  have hUnion : S₁ ∪ (S₂ \ S₁) = S₂ := Finset.union_sdiff_of_subset hSub
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro Θ hΘ
    rw [← hUnion, ← restrictZeroSet_union, ← restrictZeroSet_union, h.2.2.1 Θ hΘ]
  · intro Θ
    let D := S₂ \ S₁
    have hDUnion : D ∪ S₁ = S₂ := (Finset.union_comm D S₁).trans hUnion
    calc restrictZeroSet (wp P.compile (restrictZeroSet Θ S₂)) S₂
        = restrictZeroSet (restrictZeroSet
            (wp P.compile (restrictZeroSet (restrictZeroSet Θ S₁) D)) D) S₁ := by
          rw [restrictZeroSet_union Θ S₁ D, hUnion,
            restrictZeroSet_union _ D S₁, hDUnion]
      _ = restrictZeroSet (restrictZeroSet
            (wp P.compile (restrictZeroSet Θ S₁)) S₁) D := by
          rw [wp_restrictZeroSet_of_disjoint P D hDisjP (restrictZeroSet Θ S₁),
            restrictZeroSet_idem, restrictZeroSet_union, hDUnion, ← hUnion,
            ← restrictZeroSet_union]
      _ = restrictZeroSet (wp P.compile Θ) S₂ := by
          rw [h.2.2.2 Θ, restrictZeroSet_union, hUnion]

/-!
### Primitive Gate Ket Evaluation Helpers
-/

private noncomputable def writeReg {N k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) : BitAssignment N :=
  basisBits N (r.replaceIndex ((basisBits N).symm β) ((basisBits k).symm γ))

@[simp]
private theorem writeReg_apply_reg {N k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

private theorem writeReg_apply_of_not_mem {N k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (w : Wire N) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

private theorem writeReg_eq_update {N k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne]
    exact fun h ↦ hw ⟨i₀, h.symm⟩

private noncomputable abbrev localIdx {N k : ℕ} (r : QRegister k N) (β : BitAssignment N) :
    Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

private theorem embedMatrix_mulVec_ket {N k : ℕ} (r : QRegister k N)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment N) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits N).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

private theorem embedMatrix_permMatrix_mulVec_ket {N k : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment N) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

private theorem singleton_embedMatrix_mulVec_ket {N : ℕ} (q : Wire N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment N) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hloc : localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [embedMatrix_mulVec_ket, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]

/-- Sign `(-1)^b` for a `ZMod 2` bit `b`. -/
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- Real-valued `1 / √2` lifted to `ℂ`. -/
noncomputable def sqrtHalf : ℂ := ((√(1 / 2) : ℝ) : ℂ)

@[simp]
theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> simp [bitSign]

theorem bitSign_mul_self (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  rcases bit_cases a with rfl | rfl <;> simp [bitSign]

@[simp]
theorem star_bitSign (a : ZMod 2) : star (bitSign a) = bitSign a := by
  rcases bit_cases a with rfl | rfl <;> simp [bitSign]

theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  dsimp [sqrtHalf]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

@[simp]
theorem star_sqrtHalf : star sqrtHalf = sqrtHalf := by
  dsimp [sqrtHalf]
  exact Complex.conj_ofReal _

theorem ket_identity {N : ℕ} (β : BitAssignment N) :
    (Circuit.identity : Circuit N).eval.1.mulVec (ket β) = ket β := by
  simp only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]

theorem eval_seq_mulVec {N : ℕ} (c₁ c₂ : Circuit N) (ψ : Fin (2 ^ N) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

theorem ket_X {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb]

theorem ket_Z {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem ket_H {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      sqrtHalf • (ket (Function.update β q 0) +
        bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((√(1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, sqrtHalf, smul_add, Complex.real_smul]

theorem ket_CNOT {N : ℕ} (c t : Wire N) (h : c ≠ t) (β : BitAssignment N) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi

theorem ket_TOFF {N : ℕ} (c₁ c₂ t : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment N) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      ket (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBits 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi

/-!
### Temporary-AND Sandwich (`andSandwichDyn`) and `jonesToffoli` Clean-Set Theorems
-/

/-- Compute `c₁ ∧ c₂` into clean `anc` (`4 T`), run dynamic `body`, and uncompute `anc` (`0 T`). -/
def andSandwichDyn {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
    (.seq body (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))

@[simp]
theorem count_andSandwichDyn_toff {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : DynamicCircuit Var N) :
    (andSandwichDyn v c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.TOFF =
      body.count PrimitiveGate.TOFF := by
  simp [andSandwichDyn]

@[simp]
theorem count_andSandwichDyn_t {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : DynamicCircuit Var N) :
    (andSandwichDyn v c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.T =
      4 + body.count PrimitiveGate.T := by
  simp [andSandwichDyn]

/-- `andSandwichDyn` realizes `TOFF c₁ c₂ anc * U_body * TOFF c₁ c₂ anc` on clean set `S` whenever
`anc ∈ S`, `c₁, c₂ ∉ S`, `body` realizes `U_body` on `S.erase anc`, and the conjugated unitary
preserves `|0⟩` on `anc`. -/
theorem CleanRealizesSet.andSandwich {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)} {c₁ c₂ anc : Wire N}
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hAnc : anc ∈ S) (hc₁ : c₁ ∉ S) (hc₂ : c₂ ∉ S)
    {U_body : Unitary (2 ^ N)} {body : DynamicCircuit Var N}
    (hBody : CleanRealizesSet v (S.erase anc) U_body body)
    (hPresAnc : ∀ β : BitAssignment N, (∀ w ∈ S, β w = 0) →
      let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      ((QRegister.singleton anc).basisOutcomeProjector 0).mulVec
        ((T_anc * U_body * T_anc).1.mulVec (ket β)) =
      (T_anc * U_body * T_anc).1.mulVec (ket β)) :
    CleanRealizesSet v S
      ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval * U_body *
        (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval)
      (andSandwichDyn v c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  let S' := S.erase anc
  have hS_eq : insert anc S' = S := Finset.insert_erase hAnc
  let T_c := Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
  let T_anc := T_c.eval
  let V := T_anc * U_body * T_anc
  have hDisj3 : Disjoint ({c₁, c₂, anc} : Finset (Wire N)) S' := by
    rw [Finset.disjoint_left]
    intro w hw hmem
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hc₁ (Finset.mem_of_mem_erase hmem)
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hc₂ (Finset.mem_of_mem_erase hmem)
      · rw [Finset.mem_singleton.mp hw] at hmem
        exact Finset.notMem_erase anc S hmem
  have hDisjCompute :
      Disjoint (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).support S' := by
    simpa only [DynamicCircuit.support_andCompute] using hDisj3
  have hDisjUncomp : Disjoint (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).support S' := by
    simpa only [DynamicCircuit.support_andUncompute] using hDisj3
  have hDisjToff : Disjoint T_c.support S' := by
    simpa only [T_c, Circuit.support_toffoli] using hDisj3
  have hToff_comm (Ψ : QCAssertion Var (2 ^ N)) :
      qcWpQAssign T_anc (restrictZeroSet Ψ S') = restrictZeroSet (qcWpQAssign T_anc Ψ) S' := by
    simpa only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile] using
      wp_restrictZeroSet_of_disjoint (.circuit T_c) S' hDisjToff Ψ
  have hT_sq : T_anc * T_anc = 1 := by
    apply Subtype.ext
    apply matrix_ext_ket
    intro β
    simp only [T_anc, T_c, Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec,
      Matrix.one_mulVec, ket_TOFF, Function.update_self, Function.update_of_ne h₁a,
      Function.update_of_ne h₂a, Function.update_idem]
    have hadd : β anc + β c₁ * β c₂ + β c₁ * β c₂ = β anc := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hadd, Function.update_eq_self]
  have hU_eq : U_body * T_anc = T_anc * V := by
    dsimp only [V]
    rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
  have hV_anc (Ψ : QCAssertion Var (2 ^ N)) :
      restrictZeroSet
        (qcWpQAssign V (restrictAssertionToZeroAncilla Ψ (QRegister.singleton anc))) S =
      restrictZeroSet (qcWpQAssign V Ψ) S := by
    let P_anc := (QRegister.singleton anc).basisOutcomeProjector 0
    have hMat : P_anc * V.1 * zeroProjOn S = V.1 * zeroProjOn S := by
      apply matrix_ext_ket
      intro β
      simp only [← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
      by_cases hβ : ∀ w ∈ S, β w = 0
      · rw [ite_eq_left hβ]
        exact hPresAnc β hβ
      · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
    have hAdj : zeroProjOn S * V.1ᴴ * P_anc = zeroProjOn S * V.1ᴴ := by
      have h' := congrArg conjTranspose hMat
      dsimp only [P_anc] at h' ⊢
      simpa only [conjTranspose_mul, zeroProjOn_conjTranspose,
        QRegister.basisOutcomeProjector_conjTranspose, ← Matrix.mul_assoc] using h'
    funext σ
    apply Subtype.ext
    simp only [restrictZeroSet_coe, restrictAssertionToZeroAncilla_coe, qcWpQAssign,
      qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conj_conj]
    rw [← Matrix.mul_assoc, hAdj]
  refine ⟨by simp [hBody.1], ?_, ?_, ?_⟩
  · intro Θ _ σ val
    change wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile
        (wp body.compile (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ))
        (Function.update σ v val) =
      wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile
        (wp body.compile (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ)) σ
    have hUn : ∀ σ' val',
        wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ (Function.update σ' v val') =
          wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ σ' :=
      fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' val'
    have hBd := hBody.2.1 _ hUn
    simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, hBd σ val]
  · intro Θ hΘ
    rw [← hS_eq, restrictZeroSet_insert]
    change restrictZeroSet
      (restrictAssertionToZeroAncilla
        (wp (.qSeq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile
          (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)) Θ)
        (QRegister.singleton anc)) S' = _
    rw [DynamicCircuit.qc_wp_andCompute_seq c₁ c₂ anc h₁₂ h₁a h₂a]
    rw [← restrictZeroSet_insert, hS_eq, ← hS_eq, restrictZeroSet_insert_outer]
    change restrictAssertionToZeroAncilla
      (restrictZeroSet
        (qcWpQAssign T_anc
          (wp body.compile (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ))) S')
      (QRegister.singleton anc) = _
    rw [← hToff_comm,
      hBody.2.2.1 (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ)
        (fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' val'),
      hToff_comm, ← restrictZeroSet_insert_outer, hS_eq, qc_wp_qAssign_comp, hU_eq,
      ← qc_wp_qAssign_comp, ← hV_anc,
      DynamicCircuit.qc_wp_toffoli_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ,
      hV_anc]
  · intro Θ
    let Q := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
    have hStep1 : wp (andSandwichDyn v c₁ c₂ anc h₁₂ h₁a h₂a body).compile (restrictZeroSet Θ S) =
        wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile
          (wp body.compile (restrictZeroSet Q S')) := by
      change wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile
        (wp body.compile
          (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (restrictZeroSet Θ S))) = _
      rw [← hS_eq, restrictZeroSet_insert Θ anc S',
        wp_restrictZeroSet_of_disjoint (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) S'
          hDisjUncomp (restrictAssertionToZeroAncilla Θ (QRegister.singleton anc)),
        DynamicCircuit.wp_andUncompute_clean_post v c₁ c₂ anc h₁₂ h₁a h₂a Θ]
    have hStep2 : wp (andSandwichDyn v c₁ c₂ anc h₁₂ h₁a h₂a body).compile Θ =
        wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile (wp body.compile Q) := rfl
    have hInner : restrictZeroSet
        (wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile
          (wp body.compile (restrictZeroSet Q S'))) S' =
      restrictZeroSet
        (wp (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a).compile (wp body.compile Q)) S' := by
      rw [← wp_restrictZeroSet_of_disjoint (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a) S'
        hDisjCompute,
        ← wp_restrictZeroSet_of_disjoint (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a) S'
        hDisjCompute,
        hBody.2.2.2 Q]
    rw [hStep1, hStep2, ← hS_eq, restrictZeroSet_insert_outer _ anc S',
      restrictZeroSet_insert_outer _ anc S', hInner]

/-- `jonesToffoli` realizes `Circuit.TOFF c₁ c₂ target` on any clean wire set `S` containing
`anc` and excluding `c₁, c₂, target`. -/
theorem CleanRealizesSet.jonesToffoli {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N)) (c₁ c₂ target anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ target) (h₂t : c₂ ≠ target)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hta : target ≠ anc)
    (hAnc : anc ∈ S) (hc₁ : c₁ ∉ S) (hc₂ : c₂ ∉ S) (ht : target ∉ S) :
    CleanRealizesSet v S (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).eval
      (DynamicCircuit.jonesToffoli v c₁ c₂ target anc h₁₂ h₁a h₂a hta) := by
  let S' := S.erase anc
  have hDisjJ : Disjoint (DynamicCircuit.jonesToffoli (Var := Var) v c₁ c₂ target anc
      h₁₂ h₁a h₂a hta).support S' := by
    rw [DynamicCircuit.support_jonesToffoli, Finset.disjoint_left]
    intro w hw hmem
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hc₁ (Finset.mem_of_mem_erase hmem)
    · rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hc₂ (Finset.mem_of_mem_erase hmem)
      · rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ht (Finset.mem_of_mem_erase hmem)
        · rw [Finset.mem_singleton.mp hw] at hmem
          exact Finset.notMem_erase anc S hmem
  have hBase : CleanRealizesSet v {anc} (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).eval
      (DynamicCircuit.jonesToffoli v c₁ c₂ target anc h₁₂ h₁a h₂a hta) := by
    have hSing (Ψ : QCAssertion Var (2 ^ N)) :
        restrictZeroSet Ψ {anc} = restrictAssertionToZeroAncilla Ψ (QRegister.singleton anc) := by
      rw [restrictAssertionToZeroAncilla_eq_restrictZeroSet, QRegister.image_singleton]
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro Θ _ σ val
      exact DynamicCircuit.wp_jonesToffoli_update_self v c₁ c₂ target anc h₁₂ h₁a h₂a hta Θ σ val
    · intro Θ hΘ
      rw [hSing, hSing]
      exact DynamicCircuit.qc_wp_jonesToffoli_of_update_eq
        v c₁ c₂ target anc h₁₂ h₁t h₂t h₁a h₂a hta Θ hΘ
    · intro Θ
      rw [hSing Θ, DynamicCircuit.wp_jonesToffoli_clean_post v c₁ c₂ target anc h₁₂ h₁a h₂a hta]
  have hSub : ({anc} : Finset (Wire N)) ⊆ S := Finset.singleton_subset_iff.mpr hAnc
  have hDiff : S \ {anc} = S' := Finset.sdiff_singleton_eq_erase anc S
  exact hBase.extend hSub (by rwa [hDiff])

/-!
## Section 2: Target QROM/Phase Unitaries, Pruned Unary Iteration, and Pure Unary QROM
-/

/-- Bit-assignment update that XORs `word : Fin W → Bool` into `rOut : QRegister W N`. -/
noncomputable def xorRegBits {N W : ℕ} (β : BitAssignment N) (rOut : QRegister W N)
    (word : Fin W → Bool) : BitAssignment N :=
  fun q ↦
    if h : ∃ j : Fin W, rOut j = q then
      β q + if word (Classical.choose h) then 1 else 0
    else
      β q

@[simp]
theorem xorRegBits_apply_reg {N W : ℕ} (β : BitAssignment N) (rOut : QRegister W N)
    (word : Fin W → Bool) (j : Fin W) :
    xorRegBits β rOut word (rOut j) = β (rOut j) + if word j then 1 else 0 := by
  have hex : ∃ k : Fin W, rOut k = rOut j := ⟨j, rfl⟩
  simp only [xorRegBits, hex, ↓reduceDIte]
  have hchoose : Classical.choose hex = j := rOut.wires.injective (Classical.choose_spec hex)
  rw [hchoose]

theorem xorRegBits_apply_of_not_mem {N W : ℕ} (β : BitAssignment N) (rOut : QRegister W N)
    (word : Fin W → Bool) (q : Wire N) (hq : q ∉ rOut.image) :
    xorRegBits β rOut word q = β q := by
  have hne : ¬∃ j : Fin W, rOut j = q := fun hex ↦ hq ((QRegister.mem_image rOut q).mpr hex)
  simp [xorRegBits, hne, ↓reduceDIte]

@[simp]
theorem xorRegBits_false {N W : ℕ} (β : BitAssignment N) (rOut : QRegister W N) :
    xorRegBits β rOut (fun _ ↦ false) = β := by
  funext q
  by_cases hq : q ∈ rOut.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut q).mp hq
    simp
  · exact xorRegBits_apply_of_not_mem β rOut _ q hq

@[simp]
theorem xorRegBits_idem {N W : ℕ} (β : BitAssignment N) (rOut : QRegister W N)
    (word : Fin W → Bool) :
    xorRegBits (xorRegBits β rOut word) rOut word = β := by
  funext q
  by_cases hq : q ∈ rOut.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut q).mp hq
    simp only [xorRegBits_apply_reg]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [xorRegBits_apply_of_not_mem _ rOut _ q hq, xorRegBits_apply_of_not_mem _ rOut _ q hq]

/-- Bit-level involution on `BitAssignment (nIdx + W)` XORing `T[idx]` (for `idx < L`) into the
`W` output bits. -/
noncomputable def xorLoadBits (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool))
    (γ : BitAssignment (nIdx + W)) : BitAssignment (nIdx + W) := fun k ↦
  let idx := (basisBits nIdx).symm (fun i ↦ γ (Fin.castAdd W i))
  match finSumFinEquiv.symm k with
  | Sum.inl _ => γ k
  | Sum.inr j => γ k + if decide (idx.val < L ∧ T idx.val j) then 1 else 0

theorem xorLoadBits_involutive (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool)) :
    Function.Involutive (xorLoadBits nIdx W L T) := by
  intro γ
  have hIdx : (basisBits nIdx).symm (fun i ↦ xorLoadBits nIdx W L T γ (Fin.castAdd W i)) =
      (basisBits nIdx).symm (fun i ↦ γ (Fin.castAdd W i)) := by
    congr 1
    funext i
    simp [xorLoadBits]
  funext k
  let γ₁ := xorLoadBits nIdx W L T γ
  have hIdx₁ : (basisBits nIdx).symm (fun i ↦ γ₁ (Fin.castAdd W i)) =
      (basisBits nIdx).symm (fun i ↦ γ (Fin.castAdd W i)) := hIdx
  change (match finSumFinEquiv.symm k with
    | Sum.inl _ => γ₁ k
    | Sum.inr j =>
      γ₁ k + if decide (((basisBits nIdx).symm (fun i ↦ γ₁ (Fin.castAdd W i))).val < L ∧
        T ((basisBits nIdx).symm (fun i ↦ γ₁ (Fin.castAdd W i))).val j) then 1 else 0) = γ k
  rw [hIdx₁]
  dsimp only [γ₁, xorLoadBits]
  rcases finSumFinEquiv.symm k with i | j
  · rfl
  · dsimp only
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Involution on `Fin (2 ^ (nIdx + W))` XORing `T[idx]` (for `idx < L`) into the `W` output
bits. -/
noncomputable def xorLoadPerm (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool)) :
    Equiv.Perm (Fin (2 ^ (nIdx + W))) :=
  (basisBits (nIdx + W)).trans
    ((Equiv.mk (xorLoadBits nIdx W L T) (xorLoadBits nIdx W L T)
        (xorLoadBits_involutive nIdx W L T) (xorLoadBits_involutive nIdx W L T)).trans
      (basisBits (nIdx + W)).symm)

@[simp]
theorem xorLoadPerm_symm (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool)) :
    (xorLoadPerm nIdx W L T).symm = xorLoadPerm nIdx W L T := by
  ext x
  rfl

@[simp]
theorem xorLoadPerm_apply_apply (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool))
    (x : Fin (2 ^ (nIdx + W))) :
    xorLoadPerm nIdx W L T (xorLoadPerm nIdx W L T x) = x := by
  simp only [xorLoadPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  change (basisBits (nIdx + W)).symm
    (xorLoadBits nIdx W L T (xorLoadBits nIdx W L T (basisBits (nIdx + W) x))) = x
  rw [xorLoadBits_involutive, Equiv.symm_apply_apply]

/-- Unitary `|idx⟩ |y⟩ ↦ |idx⟩ |y ⊕ (if idx < L then T[idx] else 0)⟩` on `(nIdx + W)` qubits. -/
noncomputable def xorLoadUnitary (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool)) :
    Unitary (2 ^ (nIdx + W)) :=
  Operator.permutationUnitary (xorLoadPerm nIdx W L T)

@[simp]
theorem xorLoadUnitary_mul_self (nIdx W L : ℕ) (T : ℕ → (Fin W → Bool)) :
    xorLoadUnitary nIdx W L T * xorLoadUnitary nIdx W L T = 1 := by
  apply Subtype.ext
  have hsq : (xorLoadPerm nIdx W L T)⁻¹ * (xorLoadPerm nIdx W L T)⁻¹ = 1 := by
    ext x
    simp [Equiv.Perm.inv_def]
  simp only [xorLoadUnitary, Operator.permutationUnitary, Submonoid.coe_mul, Submonoid.coe_one,
    ← Matrix.permMatrix_mul, hsq, Matrix.permMatrix_one]

theorem embed_xorLoadUnitary_mulVec_ket {N nIdx W L : ℕ}
    (rIdx : QRegister nIdx N) (rOut : QRegister W N) (hDisj : rIdx.DisjointWires rOut)
    (T : ℕ → (Fin W → Bool)) (β : BitAssignment N) :
    let idx := (basisBits nIdx).symm (fun i ↦ β (rIdx i))
    ((rIdx.concat rOut hDisj).embedUnitary (xorLoadUnitary nIdx W L T)).1.mulVec (ket β) =
      ket (xorRegBits β rOut (fun j ↦ decide (idx.val < L ∧ T idx.val j))) := by
  intro idx
  rw [QRegister.embedUnitary_val, xorLoadUnitary, Operator.permutationUnitary,
    embedMatrix_permMatrix_mulVec_ket]
  congr 1
  let rComb := rIdx.concat rOut hDisj
  have hIdxEq : (basisBits nIdx).symm (fun i ↦ β (rComb (Fin.castAdd W i))) = idx := by
    congr 1
    funext i
    simp [rComb]
  funext q
  by_cases hq : q ∈ Set.range rComb.wires
  · obtain ⟨k, rfl⟩ := hq
    rw [writeReg_apply_reg]
    have hInvSymm : ((xorLoadPerm nIdx W L T)⁻¹).symm (localIdx rComb β) =
        (xorLoadPerm nIdx W L T) (localIdx rComb β) := rfl
    rw [hInvSymm]
    have hbits : basisBits (nIdx + W) (xorLoadPerm nIdx W L T (localIdx rComb β)) k =
        match finSumFinEquiv.symm k with
        | Sum.inl _ => β (rComb k)
        | Sum.inr j => β (rComb k) + if decide (idx.val < L ∧ T idx.val j) then 1 else 0 := by
      have happ : basisBits (nIdx + W) (xorLoadPerm nIdx W L T (localIdx rComb β)) =
          xorLoadBits nIdx W L T (fun i ↦ β (rComb i)) := by
        simp only [xorLoadPerm, localIdx, Equiv.trans_apply, Equiv.apply_symm_apply]
        rfl
      rw [happ]
      dsimp only [xorLoadBits]
      rw [hIdxEq]
    rw [hbits]
    rcases hsum : finSumFinEquiv.symm k with i | j
    · have hk : k = Fin.castAdd W i := by
        simpa using congrArg finSumFinEquiv hsum
      subst hk
      have hnotOut : rComb (Fin.castAdd W i) ∉ rOut.image := by
        rw [QRegister.concat_apply_left]
        exact hDisj.apply_not_mem_right i
      rw [xorRegBits_apply_of_not_mem _ rOut _ _ hnotOut]
    · have hk : k = Fin.natAdd nIdx j := by
        simpa using congrArg finSumFinEquiv hsum
      subst hk
      simp [rComb, xorRegBits_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hq, xorRegBits_apply_of_not_mem]
    intro hmem
    obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut q).mp hmem
    exact hq ⟨Fin.natAdd nIdx j, QRegister.concat_apply_right rIdx rOut hDisj j⟩

/-- Diagonal `1`-bit phase unitary `|idx⟩ ↦ (-1)^{if idx < L then P[idx] else 0} |idx⟩`. -/
noncomputable def diagPhaseUnitary (nIdx L : ℕ) (P : ℕ → Bool) : Unitary (2 ^ nIdx) :=
  ⟨Matrix.diagonal (fun idx : Fin (2 ^ nIdx) ↦
      if idx.val < L ∧ P idx.val then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : i.val < L ∧ P i.val <;> simp [h]
    · simp [hij]⟩

@[simp]
theorem diagPhaseUnitary_mul_self (nIdx L : ℕ) (P : ℕ → Bool) :
    diagPhaseUnitary nIdx L P * diagPhaseUnitary nIdx L P = 1 := by
  apply Subtype.ext
  simp only [diagPhaseUnitary, Submonoid.coe_mul, Submonoid.coe_one, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i.val < L ∧ P i.val <;> simp [h]
  · simp [hij]

theorem embed_diagPhaseUnitary_mulVec_ket {N nIdx L : ℕ}
    (rIdx : QRegister nIdx N) (P : ℕ → Bool) (β : BitAssignment N) :
    let idx := (basisBits nIdx).symm (fun i ↦ β (rIdx i))
    (rIdx.embedUnitary (diagPhaseUnitary nIdx L P)).1.mulVec (ket β) =
      (if idx.val < L ∧ P idx.val then (-1 : ℂ) else 1) • ket β := by
  intro idx
  funext g
  rw [QRegister.embedUnitary_val, diagPhaseUnitary, QRegister.embedMatrix_diagonal_mulVec]
  by_cases hg : g = (basisBits N).symm β
  · subst hg
    have hext : rIdx.extractIndex ((basisBits N).symm β) = idx := by
      simp [QRegister.extractIndex, idx]
    simp [ket, basisState, hext]
  · simp [ket, basisState, Pi.single_eq_of_ne hg]

/-!
### Binary Index Splitting Lemmas
-/

theorem localIdx_succ_val {N k : ℕ} (rHi : QRegister (k + 1) N) (β : BitAssignment N) :
    let rLo := rHi.subregister (Fin.castLEEmb (Nat.le_succ k))
    let wMsb := rHi ⟨k, Nat.lt_succ_self k⟩
    ((basisBits (k + 1)).symm (fun i ↦ β (rHi i))).val =
      2 ^ k * (if β wMsb = 1 then 1 else 0) +
        ((basisBits k).symm (fun i ↦ β (rLo i))).val := by
  intro rLo wMsb
  let b : ℕ := if β wMsb = 1 then 1 else 0
  let qLo := (basisBits k).symm (fun i ↦ β (rLo i))
  have hb : b ≤ 1 := by dsimp [b]; split_ifs <;> omega
  have hlt : 2 ^ k * b + qLo.val < 2 ^ (k + 1) := by
    have := qLo.isLt
    rw [pow_succ]
    nlinarith
  let j : Fin (2 ^ (k + 1)) := ⟨2 ^ k * b + qLo.val, hlt⟩
  suffices hEq : (basisBits (k + 1)).symm (fun i ↦ β (rHi i)) = j from
    congrArg Fin.val hEq
  apply (basisBits (k + 1)).injective
  funext i
  rw [Equiv.apply_symm_apply, basisBits_eq_div_mod]
  by_cases hi : i.val < k
  · have hrLo : β (rLo ⟨i.val, hi⟩) = β (rHi i) := rfl
    have hqBit : β (rLo ⟨i.val, hi⟩) = ((qLo.val / 2 ^ i.val % 2 : ℕ) : ZMod 2) := by
      have := congrFun (basisBits_symm (fun m ↦ β (rLo m))) ⟨i.val, hi⟩
      rw [← this, basisBits_eq_div_mod]
    rw [← hrLo, hqBit]
    congr 1
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1 - i.val) * 2 ^ i.val := by
      rw [mul_assoc, ← pow_add, ← pow_succ']
      congr 1
      omega
    have hjval : j.val = qLo.val + (2 * (2 ^ (k - 1 - i.val) * b)) * 2 ^ i.val := by
      calc j.val
          = 2 ^ k * b + qLo.val := rfl
        _ = (2 * 2 ^ (k - 1 - i.val) * 2 ^ i.val) * b + qLo.val := congrArg (· * b + qLo.val) hpow
        _ = qLo.val + (2 * (2 ^ (k - 1 - i.val) * b)) * 2 ^ i.val := by ring
    have hmod (a c : ℕ) : (a + 2 * c) % 2 = a % 2 := by omega
    rw [hjval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i.val), hmod]
  · have hik : i.val = k := by omega
    have hi_eq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hik
    subst hi_eq
    have hjdiv : j.val / 2 ^ k = b := by
      have hjval : j.val = qLo.val + b * 2 ^ k := by dsimp [j]; ring
      rw [hjval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt qLo.isLt,
        zero_add]
    rw [hjdiv]
    rcases bit_cases (β wMsb) with h0 | h1
    · simp [b, wMsb, h0]
    · simp [b, wMsb, h1]

theorem localIdx_split_add {N s k : ℕ} (rIdx : QRegister (s + k) N) (β : BitAssignment N) :
    let rOff := rIdx.slice 0 s (by omega)
    let rHi := rIdx.slice s k (by omega)
    ((basisBits (s + k)).symm (fun i ↦ β (rIdx i))).val =
      2 ^ s * ((basisBits k).symm (fun i ↦ β (rHi i))).val +
        ((basisBits s).symm (fun i ↦ β (rOff i))).val := by
  intro rOff rHi
  let q := (basisBits k).symm (fun i ↦ β (rHi i))
  let r := (basisBits s).symm (fun i ↦ β (rOff i))
  have hlt : 2 ^ s * q.val + r.val < 2 ^ (s + k) := by
    have := q.isLt
    have := r.isLt
    rw [pow_add]
    nlinarith
  let j : Fin (2 ^ (s + k)) := ⟨2 ^ s * q.val + r.val, hlt⟩
  suffices hEq : (basisBits (s + k)).symm (fun i ↦ β (rIdx i)) = j from
    congrArg Fin.val hEq
  apply (basisBits (s + k)).injective
  funext i
  rw [Equiv.apply_symm_apply, basisBits_eq_div_mod]
  by_cases hi : i.val < s
  · have hrOff : β (rOff ⟨i.val, hi⟩) = β (rIdx i) := by
      congr 1
      dsimp only [rOff]
      rw [QRegister.slice_apply]
      congr 1
      ext
      simp
    have hrBit : β (rOff ⟨i.val, hi⟩) = ((r.val / 2 ^ i.val % 2 : ℕ) : ZMod 2) := by
      have := congrFun (basisBits_symm (fun m ↦ β (rOff m))) ⟨i.val, hi⟩
      rw [← this, basisBits_eq_div_mod]
    rw [← hrOff, hrBit]
    congr 1
    have hpow : 2 ^ s = 2 * 2 ^ (s - 1 - i.val) * 2 ^ i.val := by
      rw [mul_assoc, ← pow_add, ← pow_succ']
      congr 1
      omega
    have hjval : j.val = r.val + (2 * (2 ^ (s - 1 - i.val) * q.val)) * 2 ^ i.val := by
      calc j.val
          = 2 ^ s * q.val + r.val := rfl
        _ = (2 * 2 ^ (s - 1 - i.val) * 2 ^ i.val) * q.val + r.val :=
            congrArg (· * q.val + r.val) hpow
        _ = r.val + (2 * (2 ^ (s - 1 - i.val) * q.val)) * 2 ^ i.val := by ring
    have hmod (a c : ℕ) : (a + 2 * c) % 2 = a % 2 := by omega
    rw [hjval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i.val), hmod]
  · let m : Fin k := ⟨i.val - s, by omega⟩
    have hrHi : β (rHi m) = β (rIdx i) := by
      congr 1
      dsimp only [rHi]
      rw [QRegister.slice_apply]
      congr 1
      ext
      dsimp only [m]
      omega
    have hqBit : β (rHi m) = ((q.val / 2 ^ m.val % 2 : ℕ) : ZMod 2) := by
      have := congrFun (basisBits_symm (fun t ↦ β (rHi t))) m
      rw [← this, basisBits_eq_div_mod]
    rw [← hrHi, hqBit]
    congr 1
    have hi_add : i.val = s + m.val := by dsimp [m]; omega
    have hjdiv : j.val / 2 ^ s = q.val := by
      have hjval : j.val = r.val + q.val * 2 ^ s := by dsimp [j]; ring
      rw [hjval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt r.isLt, zero_add]
    rw [hi_add, pow_add 2 s m.val, ← Nat.div_div_eq_div_mul, hjdiv]

/-!
### Pruned MSB-First Unary Iteration (`unaryIterGatedDyn` and `unaryIterDyn`)
-/

/-!
### Pure Unary QROM (`s = 0`, `unaryQromLoadDyn`)
-/

/-!
### Power-of-Two Swap Network (`swapTreePow2Dyn`) and Slot Routing Map
-/

/-!
### Forward SelectSwap QROM (`selectSwapLoadDyn` and `selectSwapLoadReuseSpineDyn`)
-/

/-!
## Section 4: ANF `1`-Bit Phase Fixup (`selectSwapPhaseFixupDyn`)
-/

/-- Controlled-`Z` (`CZ`) gate decomposed as `H w₂ ;; CNOT w₁ w₂ ;; H w₂` (`0 T`, `0 TOFF`). -/
def czCircuit {N : ℕ} (w₁ w₂ : Wire N) (h : w₁ ≠ w₂) : Circuit N :=
  .seq (Circuit.H w₂) (.seq (Circuit.CNOT w₁ w₂ h) (Circuit.H w₂))

@[simp]
theorem count_czCircuit_toff {N : ℕ} (w₁ w₂ : Wire N) (h : w₁ ≠ w₂) :
    (czCircuit w₁ w₂ h).count PrimitiveGate.TOFF = 0 := by
  simp [czCircuit, Circuit.H, Circuit.single]

@[simp]
theorem count_czCircuit_t {N : ℕ} (w₁ w₂ : Wire N) (h : w₁ ≠ w₂) :
    (czCircuit w₁ w₂ h).count PrimitiveGate.T = 0 := by
  simp [czCircuit, Circuit.H, Circuit.single]

theorem ket_czCircuit {N : ℕ} (w₁ w₂ : Wire N) (h : w₁ ≠ w₂) (β : BitAssignment N) :
    (czCircuit w₁ w₂ h).eval.1.mulVec (ket β) = bitSign (β w₁ * β w₂) • ket β := by
  simp only [czCircuit, eval_seq_mulVec]
  rw [ket_H]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT, Function.update_self,
    Function.update_of_ne h, Function.update_idem, zero_add, ket_H, smul_add, smul_smul]
  have hupd (b : ZMod 2) (hb : β w₂ = b) : Function.update β w₂ b = β := by
    rw [← hb]
    exact Function.update_eq_self w₂ β
  have hbs0 : bitSign 0 = 1 := rfl
  have hbs1 : bitSign 1 = -1 := rfl
  rcases bit_cases (β w₁) with h1 | h1 <;> rcases bit_cases (β w₂) with h2 | h2
  · rw [h1, h2, hupd 0 h2, mul_zero, add_zero, hbs0, hbs1]
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rw [sq, sqrtHalf_mul_sqrtHalf]
    ring
  · rw [h1, h2, hupd 1 h2, zero_mul, add_zero, hbs0, hbs1]
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rw [sq, sqrtHalf_mul_sqrtHalf]
    ring
  · rw [h1, h2, hupd 0 h2, mul_zero, one_add_one_zmod2, hbs0, hbs1]
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rw [sq, sqrtHalf_mul_sqrtHalf]
    ring
  · rw [h1, h2, hupd 1 h2, mul_one, one_add_one_zmod2, hbs0, hbs1]
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rw [sq, sqrtHalf_mul_sqrtHalf]
    ring

/-- Applies `czCircuit wCtrl (r j)` for each `j : Fin M` with `mask j = 1` (`0 T`, `0 TOFF`). -/
def czMaskCircuit {N : ℕ} (wCtrl : Wire N) :
    (M : ℕ) → (r : QRegister M N) → (∀ j : Fin M, wCtrl ≠ r j) → (Fin M → ZMod 2) → Circuit N
  | 0, _, _, _ => .identity
  | M + 1, r, hne, mask =>
      let iLast : Fin (M + 1) := ⟨M, Nat.lt_succ_self M⟩
      let emb := Fin.castLEEmb (Nat.le_succ M)
      .seq
        (if mask iLast = 1 then czCircuit wCtrl (r iLast) (hne iLast) else .identity)
        (czMaskCircuit wCtrl M (r.subregister emb)
          (show ∀ j : Fin M, wCtrl ≠ (r.subregister emb) j from
            fun j ↦ hne (Fin.castLE (Nat.le_succ M) j))
          (fun j ↦ mask (Fin.castLE (Nat.le_succ M) j)))

@[simp]
theorem count_czMaskCircuit_toff {N M : ℕ} (wCtrl : Wire N) (r : QRegister M N)
    (hne : ∀ j : Fin M, wCtrl ≠ r j) (mask : Fin M → ZMod 2) :
    (czMaskCircuit wCtrl M r hne mask).count PrimitiveGate.TOFF = 0 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [czMaskCircuit, Circuit.count_seq]
    refine Nat.add_eq_zero_iff.mpr ⟨?_, ih _ _ _⟩
    split_ifs <;> simp

@[simp]
theorem count_czMaskCircuit_t {N M : ℕ} (wCtrl : Wire N) (r : QRegister M N)
    (hne : ∀ j : Fin M, wCtrl ≠ r j) (mask : Fin M → ZMod 2) :
    (czMaskCircuit wCtrl M r hne mask).count PrimitiveGate.T = 0 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [czMaskCircuit, Circuit.count_seq]
    refine Nat.add_eq_zero_iff.mpr ⟨?_, ih _ _ _⟩
    split_ifs <;> simp

theorem ket_czMaskCircuit {N M : ℕ} (wCtrl : Wire N) (r : QRegister M N)
    (hne : ∀ j : Fin M, wCtrl ≠ r j) (mask : Fin M → ZMod 2) (β : BitAssignment N) :
    (czMaskCircuit wCtrl M r hne mask).eval.1.mulVec (ket β) =
      bitSign (β wCtrl * ∑ j : Fin M, mask j * β (r j)) • ket β := by
  induction M with
  | zero =>
    rw [czMaskCircuit, ket_identity]
    simp [bitSign]
  | succ M ih =>
    let iLast : Fin (M + 1) := ⟨M, Nat.lt_succ_self M⟩
    let rLo := r.subregister (Fin.castLEEmb (Nat.le_succ M))
    let maskLo : Fin M → ZMod 2 := fun j ↦ mask (Fin.castLE (Nat.le_succ M) j)
    have hFirst :
        (if mask iLast = 1 then czCircuit wCtrl (r iLast) (hne iLast) else .identity).eval.1.mulVec
          (ket β) = bitSign (β wCtrl * (mask iLast * β (r iLast))) • ket β := by
      rcases bit_cases (mask iLast) with h0 | h1
      · rw [h0, ite_eq_right (by decide : (0 : ZMod 2) ≠ 1), ket_identity, zero_mul, mul_zero]
        simp [bitSign]
      · rw [h1, ite_eq_left rfl, ket_czCircuit, one_mul]
    simp only [czMaskCircuit, eval_seq_mulVec]
    rw [hFirst, Matrix.mulVec_smul, ih rLo _ maskLo, smul_smul, ← bitSign_add]
    congr 2
    rw [Fin.sum_univ_castSucc, mul_add, add_comm]
    rfl

/-!
### Algebraic Normal Form (Möbius Transform over `ZMod 2`) and Monomial Sandwiches
-/

/-- Evaluates the `m`-th multilinear monomial (`m : Fin (2 ^ s)`) on `x : Fin s → ZMod 2`. -/
def monoEval : (s : ℕ) → (Fin s → ZMod 2) → Fin (2 ^ s) → ZMod 2
  | 0, _, _ => 1
  | s + 1, x, m =>
      let xLo : Fin s → ZMod 2 := fun i ↦ x (Fin.castLE (Nat.le_succ s) i)
      let xMsb : ZMod 2 := x ⟨s, Nat.lt_succ_self s⟩
      if hm : m.val < 2 ^ s then
        monoEval s xLo ⟨m.val, hm⟩
      else
        xMsb * monoEval s xLo
          ⟨m.val - 2 ^ s, by
            have hm2 : m.val < 2 * 2 ^ s := by simpa [pow_succ'] using m.isLt
            omega⟩

theorem monoEval_zero (s : ℕ) (x : Fin s → ZMod 2) :
    monoEval s x ⟨0, Nat.two_pow_pos s⟩ = 1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h0 : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
    simp only [monoEval, h0, ↓reduceDIte]
    exact ih _

/-- Recursive binary Möbius transform computing the ANF coefficients of `f : Fin (2 ^ s) →
ZMod 2`. -/
def anfCoeffs : (s : ℕ) → (Fin (2 ^ s) → ZMod 2) → Fin (2 ^ s) → ZMod 2
  | 0, f, _ => f ⟨0, by simp⟩
  | s + 1, f, m =>
      let f₀ : Fin (2 ^ s) → ZMod 2 :=
        fun u ↦ f ⟨u.val, by have := u.isLt; rw [pow_succ']; omega⟩
      let f₁ : Fin (2 ^ s) → ZMod 2 :=
        fun u ↦ f₀ u + f ⟨2 ^ s + u.val, by have := u.isLt; rw [pow_succ']; omega⟩
      if hm : m.val < 2 ^ s then
        anfCoeffs s f₀ ⟨m.val, hm⟩
      else
        anfCoeffs s f₁
          ⟨m.val - 2 ^ s, by
            have hm2 : m.val < 2 * 2 ^ s := by simpa [pow_succ'] using m.isLt
            omega⟩

theorem sum_anfCoeffs_mul_monoEval (s : ℕ) (f : Fin (2 ^ s) → ZMod 2) (x : Fin s → ZMod 2) :
    ∑ m : Fin (2 ^ s), anfCoeffs s f m * monoEval s x m = f ((basisBits s).symm x) := by
  induction s with
  | zero =>
    change ∑ m : Fin 1, anfCoeffs 0 f m * monoEval 0 x m = f ((basisBits 0).symm x)
    rw [Fin.sum_univ_one]
    simp only [anfCoeffs, monoEval, mul_one]
    congr 1
  | succ s ih =>
    let xLo : Fin s → ZMod 2 := fun i ↦ x (Fin.castLE (Nat.le_succ s) i)
    let xMsb : ZMod 2 := x ⟨s, Nat.lt_succ_self s⟩
    let f₀ : Fin (2 ^ s) → ZMod 2 :=
      fun u ↦ f ⟨u.val, by have := u.isLt; rw [pow_succ']; omega⟩
    let f₁ : Fin (2 ^ s) → ZMod 2 :=
      fun u ↦ f₀ u + f ⟨2 ^ s + u.val, by have := u.isLt; rw [pow_succ']; omega⟩
    have hpow : 2 ^ s + 2 ^ s = 2 ^ (s + 1) := by rw [pow_succ']; ring
    let e : Fin (2 ^ s) ⊕ Fin (2 ^ s) ≃ Fin (2 ^ (s + 1)) :=
      finSumFinEquiv.trans (finCongr hpow)
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    have hSumLo : (∑ u : Fin (2 ^ s),
        anfCoeffs (s + 1) f (e (Sum.inl u)) * monoEval (s + 1) x (e (Sum.inl u))) =
        f₀ ((basisBits s).symm xLo) := by
      rw [← ih f₀ xLo]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      have heVal : (e (Sum.inl u)).val = u.val := by simp [e]
      have huLt : (e (Sum.inl u)).val < 2 ^ s := by rw [heVal]; exact u.isLt
      have huFin : (⟨(e (Sum.inl u)).val, huLt⟩ : Fin (2 ^ s)) = u := Fin.ext heVal
      simp only [anfCoeffs, monoEval, huLt, ↓reduceDIte, huFin]
      rfl
    have hSumHi : (∑ u : Fin (2 ^ s),
        anfCoeffs (s + 1) f (e (Sum.inr u)) * monoEval (s + 1) x (e (Sum.inr u))) =
        xMsb * f₁ ((basisBits s).symm xLo) := by
      rw [← ih f₁ xLo, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      have heVal : (e (Sum.inr u)).val = 2 ^ s + u.val := by simp [e, add_comm]
      have huNotLt : ¬((e (Sum.inr u)).val < 2 ^ s) := by omega
      have huSub : (e (Sum.inr u)).val - 2 ^ s = u.val := by omega
      have huFin : (⟨(e (Sum.inr u)).val - 2 ^ s, by
          have hm2 : (e (Sum.inr u)).val < 2 * 2 ^ s := by
            simpa [pow_succ'] using (e (Sum.inr u)).isLt
          omega⟩ : Fin (2 ^ s)) = u := Fin.ext huSub
      simp only [anfCoeffs, monoEval, huNotLt, ↓reduceDIte, huFin]
      dsimp only [f₁, f₀, xMsb, xLo]
      ring
    rw [hSumLo, hSumHi]
    let rLo := (basisBits s).symm xLo
    let r := (basisBits (s + 1)).symm x
    have hrSplit : r.val = 2 ^ s * (if xMsb = 1 then 1 else 0) + rLo.val := by
      simpa [r, rLo, xLo, xMsb] using localIdx_succ_val (QRegister.whole (s + 1)) x
    rcases bit_cases xMsb with hm0 | hm1
    · have hrEq : r = ⟨rLo.val, by have := rLo.isLt; rw [pow_succ']; omega⟩ := by
        apply Fin.ext
        dsimp
        rw [hrSplit, hm0]
        simp
      change f₀ rLo + xMsb * f₁ rLo = f r
      rw [hm0, zero_mul, add_zero, hrEq]
    · have hrEq : r = ⟨2 ^ s + rLo.val, by have := rLo.isLt; rw [pow_succ']; omega⟩ := by
        apply Fin.ext
        dsimp
        rw [hrSplit, hm1]
        simp
      change f₀ rLo + xMsb * (f₀ rLo + f ⟨2 ^ s + rLo.val, _⟩) = f r
      rw [hm1, one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add, hrEq]

/-- Number of non-linear (`deg ≥ 2`) monomial scratch wires for an `s`-bit ANF phase fixup:
equals `2 ^ s - s - 1`. -/
def anfScratchWidth : ℕ → ℕ
  | 0 => 0
  | s + 1 => anfScratchWidth s + (2 ^ s - 1)

/-- Bundled construction of the `(2 ^ s - 1)`-wire non-empty monomial register together with its
wire-image bound inside `rOff.image ∪ rMono.image`. -/
def allMonoRegAux {N : ℕ} :
    (s : ℕ) → (rOff : QRegister s N) → (rMono : QRegister (anfScratchWidth s) N) →
    rOff.DisjointWires rMono →
    { r : QRegister (2 ^ s - 1) N // r.image ⊆ rOff.image ∪ rMono.image }
  | 0, _, _, _ =>
      ⟨⟨⟨Fin.elim0, fun a ↦ a.elim0⟩⟩, by
        intro q hq
        obtain ⟨i, _⟩ := (QRegister.mem_image _ q).mp hq
        exact i.elim0⟩
  | s + 1, rOff, rMono, hDisj =>
      let iMsb : Fin (s + 1) := ⟨s, Nat.lt_succ_self s⟩
      let emb := Fin.castLEEmb (Nat.le_succ s)
      let hLo : 0 + anfScratchWidth s ≤ anfScratchWidth (s + 1) := by simp [anfScratchWidth]
      let hHi : anfScratchWidth s + (2 ^ s - 1) ≤ anfScratchWidth (s + 1) := by
        simp [anfScratchWidth]
      let rOffLo := rOff.subregister emb
      let rMonoLo := rMono.slice 0 (anfScratchWidth s) hLo
      let rMonoHi := rMono.slice (anfScratchWidth s) (2 ^ s - 1) hHi
      let hDisjLo : rOffLo.DisjointWires rMonoLo :=
        (hDisj.compose_left ⟨emb⟩).compose_right (QRegister.block 0 (anfScratchWidth s) hLo)
      let sub := allMonoRegAux s rOffLo rMonoLo hDisjLo
      let f : Fin (2 ^ (s + 1) - 1) → Wire N := fun u ↦
        if hu : u.val < 2 ^ s - 1 then
          sub.1 ⟨u.val, hu⟩
        else if _ : u.val = 2 ^ s - 1 then
          rOff iMsb
        else
          rMonoHi ⟨u.val - 2 ^ s, by
            have hu2 : u.val < 2 * 2 ^ s - 1 := by simpa only [pow_succ'] using u.isLt
            have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
            omega⟩
      have hSubMem (i : Fin (2 ^ s - 1)) : sub.1 i ∈ rOffLo.image ∪ rMonoLo.image :=
        sub.2 ((QRegister.mem_image sub.1 (sub.1 i)).mpr ⟨i, rfl⟩)
      have hMsbNotLo : rOff iMsb ∉ rOffLo.image ∪ rMonoLo.image := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hO | hM
        · obtain ⟨j, hj⟩ := (QRegister.mem_image rOffLo _).mp hO
          have := congrArg Fin.val (rOff.wires.injective hj)
          dsimp [iMsb, emb] at this
          omega
        · obtain ⟨j, hj⟩ := (QRegister.mem_image rMonoLo _).mp hM
          exact hDisj.ne iMsb _ hj.symm
      have hHiNotLo (j : Fin (2 ^ s - 1)) : rMonoHi j ∉ rOffLo.image ∪ rMonoLo.image := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hO | hM
        · obtain ⟨k, hk⟩ := (QRegister.mem_image rOffLo _).mp hO
          exact hDisj.ne _ _ hk
        · obtain ⟨k, hk⟩ := (QRegister.mem_image rMonoLo _).mp hM
          exact (rMono.slice_disjoint_of_le 0 (anfScratchWidth s)
            (anfScratchWidth s) (2 ^ s - 1) hLo hHi (by omega)).ne k j hk
      have hMsbNeHi (j : Fin (2 ^ s - 1)) : rOff iMsb ≠ rMonoHi j :=
        hDisj.ne iMsb _
      have hInj : Function.Injective f := by
        intro u₁ u₂ hEq
        dsimp only [f] at hEq
        by_cases h1 : u₁.val < 2 ^ s - 1
        · rw [dite_eq_left h1] at hEq
          by_cases h2 : u₂.val < 2 ^ s - 1
          · rw [dite_eq_left h2] at hEq
            have hval := congrArg Fin.val (sub.1.wires.injective hEq)
            dsimp only at hval
            exact Fin.ext hval
          · rw [dite_eq_right h2] at hEq
            by_cases h2e : u₂.val = 2 ^ s - 1
            · rw [dite_eq_left h2e] at hEq
              exact absurd (hEq ▸ hSubMem ⟨u₁.val, h1⟩) hMsbNotLo
            · rw [dite_eq_right h2e] at hEq
              exact absurd (hEq ▸ hSubMem ⟨u₁.val, h1⟩) (hHiNotLo _)
        · rw [dite_eq_right h1] at hEq
          by_cases h1e : u₁.val = 2 ^ s - 1
          · rw [dite_eq_left h1e] at hEq
            by_cases h2 : u₂.val < 2 ^ s - 1
            · rw [dite_eq_left h2] at hEq
              exact absurd (hEq.symm ▸ hSubMem ⟨u₂.val, h2⟩) hMsbNotLo
            · rw [dite_eq_right h2] at hEq
              by_cases h2e : u₂.val = 2 ^ s - 1
              · exact Fin.ext (by omega)
              · rw [dite_eq_right h2e] at hEq
                exact absurd hEq (hMsbNeHi _)
          · rw [dite_eq_right h1e] at hEq
            by_cases h2 : u₂.val < 2 ^ s - 1
            · rw [dite_eq_left h2] at hEq
              exact absurd (hEq.symm ▸ hSubMem ⟨u₂.val, h2⟩) (hHiNotLo _)
            · rw [dite_eq_right h2] at hEq
              by_cases h2e : u₂.val = 2 ^ s - 1
              · rw [dite_eq_left h2e] at hEq
                exact absurd hEq.symm (hMsbNeHi _)
              · rw [dite_eq_right h2e] at hEq
                have hSub := congrArg Fin.val (rMonoHi.wires.injective hEq)
                dsimp only at hSub
                have : 2 ^ s ≤ u₁.val := by omega
                have : 2 ^ s ≤ u₂.val := by omega
                exact Fin.ext (by omega)
      ⟨⟨⟨f, hInj⟩⟩, by
        intro q hq
        obtain ⟨u, rfl⟩ := (QRegister.mem_image ⟨⟨f, hInj⟩⟩ q).mp hq
        change f u ∈ rOff.image ∪ rMono.image
        dsimp only [f]
        split_ifs with h1 h1e
        · exact (Finset.union_subset_union (rOff.image_compose_subset _)
            (rMono.image_compose_subset _)) (hSubMem ⟨u.val, h1⟩)
        · exact Finset.mem_union_left _ ((QRegister.mem_image rOff _).mpr ⟨iMsb, rfl⟩)
        · exact Finset.mem_union_right _
            ((rMono.image_compose_subset _) ((QRegister.mem_image rMonoHi _).mpr ⟨_, rfl⟩))⟩

/-- Ordered register of all `2 ^ s - 1` non-empty monomial wires built from `rOff` (`s` wires)
and `rMono` (`anfScratchWidth s` wires): index `u : Fin (2 ^ s - 1)` corresponds to mask
`u.val + 1`. -/
def allMonoReg {N : ℕ} (s : ℕ) (rOff : QRegister s N) (rMono : QRegister (anfScratchWidth s) N)
    (hDisj : rOff.DisjointWires rMono) : QRegister (2 ^ s - 1) N :=
  (allMonoRegAux s rOff rMono hDisj).1

theorem allMonoReg_image_subset {N s : ℕ} (rOff : QRegister s N)
    (rMono : QRegister (anfScratchWidth s) N) (hDisj : rOff.DisjointWires rMono) :
    (allMonoReg s rOff rMono hDisj).image ⊆ rOff.image ∪ rMono.image :=
  (allMonoRegAux s rOff rMono hDisj).2

theorem allMonoReg_apply_lt {N s : ℕ} (rOff : QRegister (s + 1) N)
    (rMono : QRegister (anfScratchWidth (s + 1)) N) (hDisj : rOff.DisjointWires rMono)
    (u : Fin (2 ^ (s + 1) - 1)) (hu : u.val < 2 ^ s - 1) :
    let emb := Fin.castLEEmb (Nat.le_succ s)
    let hLo : 0 + anfScratchWidth s ≤ anfScratchWidth (s + 1) := by simp [anfScratchWidth]
    allMonoReg (s + 1) rOff rMono hDisj u =
      allMonoReg s (rOff.subregister emb) (rMono.slice 0 (anfScratchWidth s) hLo)
        ((hDisj.compose_left ⟨emb⟩).compose_right (QRegister.block 0 (anfScratchWidth s) hLo))
        ⟨u.val, hu⟩ := by
  dsimp only [allMonoReg, allMonoRegAux]
  exact dite_eq_left hu

theorem allMonoReg_apply_eq {N s : ℕ} (rOff : QRegister (s + 1) N)
    (rMono : QRegister (anfScratchWidth (s + 1)) N) (hDisj : rOff.DisjointWires rMono)
    (u : Fin (2 ^ (s + 1) - 1)) (hu : u.val = 2 ^ s - 1) :
    allMonoReg (s + 1) rOff rMono hDisj u = rOff ⟨s, Nat.lt_succ_self s⟩ := by
  have hnot : ¬(u.val < 2 ^ s - 1) := by omega
  dsimp only [allMonoReg, allMonoRegAux]
  exact (dite_eq_right hnot).trans (dite_eq_left hu)

theorem allMonoReg_apply_ge {N s : ℕ} (rOff : QRegister (s + 1) N)
    (rMono : QRegister (anfScratchWidth (s + 1)) N) (hDisj : rOff.DisjointWires rMono)
    (u : Fin (2 ^ (s + 1) - 1)) (hu : 2 ^ s ≤ u.val) :
    let hHi : anfScratchWidth s + (2 ^ s - 1) ≤ anfScratchWidth (s + 1) := by
      simp [anfScratchWidth]
    allMonoReg (s + 1) rOff rMono hDisj u =
      rMono.slice (anfScratchWidth s) (2 ^ s - 1) hHi
        ⟨u.val - 2 ^ s, by
          have hu2 : u.val < 2 * 2 ^ s - 1 := by simpa only [pow_succ'] using u.isLt
          have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
          omega⟩ := by
  have hnot1 : ¬(u.val < 2 ^ s - 1) := by omega
  have hnot2 : u.val ≠ 2 ^ s - 1 := by omega
  dsimp only [allMonoReg, allMonoRegAux]
  exact (dite_eq_right hnot1).trans (dite_eq_right hnot2)

/-- Bit-assignment update that XORs `β wCtrl * β (rSrc j)` into each `rDst j`. -/
noncomputable def xorAndRegBits {N M : ℕ} (β : BitAssignment N) (wCtrl : Wire N)
    (rSrc rDst : QRegister M N) : BitAssignment N :=
  fun q ↦
    if h : ∃ j : Fin M, rDst j = q then
      β q + β wCtrl * β (rSrc (Classical.choose h))
    else
      β q

@[simp]
theorem xorAndRegBits_apply_dst {N M : ℕ} (β : BitAssignment N) (wCtrl : Wire N)
    (rSrc rDst : QRegister M N) (j : Fin M) :
    xorAndRegBits β wCtrl rSrc rDst (rDst j) = β (rDst j) + β wCtrl * β (rSrc j) := by
  have hex : ∃ k : Fin M, rDst k = rDst j := ⟨j, rfl⟩
  simp only [xorAndRegBits, hex, ↓reduceDIte]
  have hchoose : Classical.choose hex = j := rDst.wires.injective (Classical.choose_spec hex)
  rw [hchoose]

theorem xorAndRegBits_apply_of_not_mem {N M : ℕ} (β : BitAssignment N) (wCtrl : Wire N)
    (rSrc rDst : QRegister M N) (q : Wire N) (hq : q ∉ rDst.image) :
    xorAndRegBits β wCtrl rSrc rDst q = β q := by
  have hne : ¬∃ j : Fin M, rDst j = q := fun hex ↦ hq ((QRegister.mem_image rDst q).mpr hex)
  simp [xorAndRegBits, hne]

/-- Nested `M`-wire temporary-AND sandwich computing `wCtrl ∧ rSrc j` into clean `rDst j` (`4 * M`
`T` gates), running `body`, and uncomputing `rDst` in `0` `T` gates. -/
def regAndWithWireSandwichDyn {Var : Type} {N : ℕ} (v : Var) (wCtrl : Wire N) :
    (M : ℕ) → (rSrc rDst : QRegister M N) →
    (∀ j : Fin M, wCtrl ≠ rSrc j) →
    (∀ j : Fin M, wCtrl ≠ rDst j) →
    rSrc.DisjointWires rDst →
    DynamicCircuit Var N → DynamicCircuit Var N
  | 0, _, _, _, _, _, body => body
  | M + 1, rSrc, rDst, hCtrlSrc, hCtrlDst, hSrcDst, body =>
      let iLast : Fin (M + 1) := ⟨M, Nat.lt_succ_self M⟩
      let emb := Fin.castLEEmb (Nat.le_succ M)
      andSandwichDyn v wCtrl (rSrc iLast) (rDst iLast)
        (hCtrlSrc iLast) (hCtrlDst iLast) (hSrcDst.ne iLast iLast)
        (regAndWithWireSandwichDyn v wCtrl M (rSrc.subregister emb) (rDst.subregister emb)
          (show ∀ j : Fin M, wCtrl ≠ (rSrc.subregister emb) j from
            fun j ↦ hCtrlSrc (Fin.castLE (Nat.le_succ M) j))
          (show ∀ j : Fin M, wCtrl ≠ (rDst.subregister emb) j from
            fun j ↦ hCtrlDst (Fin.castLE (Nat.le_succ M) j))
          ((hSrcDst.compose_left ⟨emb⟩).compose_right ⟨emb⟩)
          body)

@[simp]
theorem count_regAndWithWireSandwichDyn_toff {Var : Type} {N M : ℕ} (v : Var) (wCtrl : Wire N)
    (rSrc rDst : QRegister M N) (hCtrlSrc : ∀ j : Fin M, wCtrl ≠ rSrc j)
    (hCtrlDst : ∀ j : Fin M, wCtrl ≠ rDst j) (hSrcDst : rSrc.DisjointWires rDst)
    (body : DynamicCircuit Var N) :
    (regAndWithWireSandwichDyn v wCtrl M rSrc rDst hCtrlSrc hCtrlDst hSrcDst body).count
      PrimitiveGate.TOFF = body.count PrimitiveGate.TOFF := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [regAndWithWireSandwichDyn, count_andSandwichDyn_toff]
    exact ih _ _ _ _ _

@[simp]
theorem count_regAndWithWireSandwichDyn_t {Var : Type} {N M : ℕ} (v : Var) (wCtrl : Wire N)
    (rSrc rDst : QRegister M N) (hCtrlSrc : ∀ j : Fin M, wCtrl ≠ rSrc j)
    (hCtrlDst : ∀ j : Fin M, wCtrl ≠ rDst j) (hSrcDst : rSrc.DisjointWires rDst)
    (body : DynamicCircuit Var N) :
    (regAndWithWireSandwichDyn v wCtrl M rSrc rDst hCtrlSrc hCtrlDst hSrcDst body).count
      PrimitiveGate.T = 4 * M + body.count PrimitiveGate.T := by
  induction M with
  | zero => simp [regAndWithWireSandwichDyn]
  | succ M ih =>
    simp only [regAndWithWireSandwichDyn, count_andSandwichDyn_t, ih]
    ring

theorem cleanRealizesSet_regAndWithWireSandwichDyn_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {N M : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N)) (wCtrl : Wire N)
    (rSrc rDst : QRegister M N)
    (hCtrlSrc : ∀ j : Fin M, wCtrl ≠ rSrc j)
    (hCtrlDst : ∀ j : Fin M, wCtrl ≠ rDst j)
    (hSrcDst : rSrc.DisjointWires rDst)
    (hDstSubS : rDst.image ⊆ S)
    (hCtrlNotS : wCtrl ∉ S)
    (hDisjSrcS : Disjoint rSrc.image S)
    {U_body : Unitary (2 ^ N)} {body : DynamicCircuit Var N} {φ : BitAssignment N → ℂ}
    (hBody : CleanRealizesSet v (S \ rDst.image) U_body body)
    (hBodyKet : ∀ β : BitAssignment N, (∀ x ∈ S \ rDst.image, β x = 0) →
      U_body.1.mulVec (ket β) = φ β • ket β) :
    ∃ U : Unitary (2 ^ N),
      CleanRealizesSet v S U
        (regAndWithWireSandwichDyn v wCtrl M rSrc rDst hCtrlSrc hCtrlDst hSrcDst body) ∧
      ∀ β : BitAssignment N, (∀ x ∈ S, β x = 0) →
        U.1.mulVec (ket β) = φ (xorAndRegBits β wCtrl rSrc rDst) • ket β := by
  induction M generalizing S with
  | zero =>
    have hDstEmpty : rDst.image = ∅ := by
      ext q
      simp only [Finset.notMem_empty, iff_false]
      intro hmem
      obtain ⟨j, _⟩ := (QRegister.mem_image rDst q).mp hmem
      exact j.elim0
    rw [hDstEmpty, Finset.sdiff_empty] at hBody hBodyKet
    refine ⟨U_body, hBody, ?_⟩
    intro β hβ
    have hEq : xorAndRegBits β wCtrl rSrc rDst = β := by
      funext q
      apply xorAndRegBits_apply_of_not_mem
      rw [hDstEmpty]
      exact Finset.notMem_empty q
    rw [hBodyKet β hβ, hEq]
  | succ M ih =>
    let iLast : Fin (M + 1) := ⟨M, Nat.lt_succ_self M⟩
    let emb := Fin.castLEEmb (Nat.le_succ M)
    let wAnc := rDst iLast
    let rSrcLo := rSrc.subregister emb
    let rDstLo := rDst.subregister emb
    have hAncInS : wAnc ∈ S := hDstSubS ((QRegister.mem_image rDst wAnc).mpr ⟨iLast, rfl⟩)
    have hSrcNotS : rSrc iLast ∉ S :=
      Finset.disjoint_left.mp hDisjSrcS ((QRegister.mem_image rSrc _).mpr ⟨iLast, rfl⟩)
    have hAncNotLo : wAnc ∉ rDstLo.image := by
      intro hmem
      obtain ⟨j, hj⟩ := (QRegister.mem_image rDstLo wAnc).mp hmem
      have := congrArg Fin.val (rDst.wires.injective hj)
      dsimp [iLast, emb] at this
      omega
    have hDstImg : rDst.image = insert wAnc rDstLo.image := by
      ext q
      simp only [Finset.mem_insert, QRegister.mem_image]
      constructor
      · rintro ⟨j, rfl⟩
        by_cases hj : j.val < M
        · exact Or.inr ⟨⟨j.val, hj⟩, rfl⟩
        · have hjEq : j = iLast := Fin.ext (by dsimp [iLast]; omega)
          exact Or.inl (congrArg rDst hjEq)
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨iLast, rfl⟩
        · exact ⟨Fin.castLE (Nat.le_succ M) j, rfl⟩
    let S' := S.erase wAnc
    have hDstLoSubS' : rDstLo.image ⊆ S' := by
      intro q hq
      exact Finset.mem_erase.mpr ⟨fun hEq ↦ hAncNotLo (hEq ▸ hq),
        hDstSubS ((rDst.image_compose_subset _) hq)⟩
    have hCtrlNotS' : wCtrl ∉ S' := fun h ↦ hCtrlNotS (Finset.mem_of_mem_erase h)
    have hDisjSrcLoS' : Disjoint rSrcLo.image S' :=
      Disjoint.mono (rSrc.image_compose_subset _) (Finset.erase_subset wAnc S) hDisjSrcS
    have hSdiffEq : S' \ rDstLo.image = S \ rDst.image := by
      ext q
      simp [S', hDstImg, and_comm, and_assoc]
    have hBody' : CleanRealizesSet v (S' \ rDstLo.image) U_body body := by
      rwa [hSdiffEq]
    have hBodyKet' : ∀ β : BitAssignment N, (∀ x ∈ S' \ rDstLo.image, β x = 0) →
        U_body.1.mulVec (ket β) = φ β • ket β := by
      intro β hβ
      exact hBodyKet β (by rwa [← hSdiffEq])
    obtain ⟨U_lo, hLo, hkLo⟩ := ih S' rSrcLo rDstLo
      (fun j ↦ hCtrlSrc (Fin.castLE (Nat.le_succ M) j))
      (fun j ↦ hCtrlDst (Fin.castLE (Nat.le_succ M) j))
      ((hSrcDst.compose_left ⟨emb⟩).compose_right ⟨emb⟩)
      hDstLoSubS' hCtrlNotS' hDisjSrcLoS' hBody' hBodyKet'
    let T_anc := (Circuit.TOFF wCtrl (rSrc iLast) wAnc
      (hCtrlSrc iLast) (hCtrlDst iLast) (hSrcDst.ne iLast iLast)).eval
    have hSandKet : ∀ β : BitAssignment N, (∀ x ∈ S, β x = 0) →
        (T_anc * U_lo * T_anc).1.mulVec (ket β) =
          φ (xorAndRegBits β wCtrl rSrc rDst) • ket β := by
      intro β hβ
      have hβAnc : β wAnc = 0 := hβ wAnc hAncInS
      let β₁ := Function.update β wAnc (β wCtrl * β (rSrc iLast))
      have hβ₁S' : ∀ x ∈ S', β₁ x = 0 := by
        intro x hx
        dsimp only [β₁]
        rw [Function.update_of_ne (Finset.mem_erase.mp hx).1, hβ x (Finset.mem_of_mem_erase hx)]
      simp only [T_anc, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [ket_TOFF, hβAnc, zero_add]
      change (Circuit.TOFF wCtrl (rSrc iLast) wAnc
        (hCtrlSrc iLast) (hCtrlDst iLast) (hSrcDst.ne iLast iLast)).eval.1.mulVec
          (U_lo.1.mulVec (ket β₁)) = _
      rw [hkLo β₁ hβ₁S', Matrix.mulVec_smul, ket_TOFF]
      have hRest : Function.update β₁ wAnc (β₁ wAnc + β₁ wCtrl * β₁ (rSrc iLast)) = β := by
        dsimp only [β₁]
        rw [Function.update_self, Function.update_of_ne (hCtrlDst iLast),
          Function.update_of_ne (hSrcDst.ne iLast iLast), CharTwo.add_self_eq_zero,
          Function.update_idem, ← hβAnc, Function.update_eq_self]
      have hArgEq : xorAndRegBits β₁ wCtrl rSrcLo rDstLo = xorAndRegBits β wCtrl rSrc rDst := by
        funext q
        by_cases hq : q ∈ rDst.image
        · rw [hDstImg] at hq
          rcases Finset.mem_insert.mp hq with rfl | hqLo
          · rw [xorAndRegBits_apply_of_not_mem _ _ _ _ _ hAncNotLo, xorAndRegBits_apply_dst,
              hβAnc, zero_add]
            exact Function.update_self wAnc _ β
          · obtain ⟨j, rfl⟩ := (QRegister.mem_image rDstLo q).mp hqLo
            have hne : rDstLo j ≠ wAnc := fun h ↦ hAncNotLo (h ▸ hqLo)
            have hneSrc : rSrcLo j ≠ wAnc := hSrcDst.ne (Fin.castLE (Nat.le_succ M) j) iLast
            change xorAndRegBits β₁ wCtrl rSrcLo rDstLo (rDstLo j) =
              xorAndRegBits β wCtrl rSrc rDst (rDst (Fin.castLE (Nat.le_succ M) j))
            rw [xorAndRegBits_apply_dst, xorAndRegBits_apply_dst]
            dsimp only [β₁]
            rw [Function.update_of_ne hne, Function.update_of_ne (hCtrlDst iLast),
              Function.update_of_ne hneSrc]
            rfl
        · have hnotLo : q ∉ rDstLo.image := fun hmem ↦ hq ((rDst.image_compose_subset _) hmem)
          have hne : q ≠ wAnc := fun hEq ↦ hq (hEq ▸ (hDstImg ▸ Finset.mem_insert_self _ _))
          rw [xorAndRegBits_apply_of_not_mem _ _ _ _ _ hnotLo,
            xorAndRegBits_apply_of_not_mem _ _ _ _ _ hq]
          exact Function.update_of_ne hne _ _
      rw [hRest, hArgEq]
    refine ⟨T_anc * U_lo * T_anc, ?_, hSandKet⟩
    refine CleanRealizesSet.andSandwich (hCtrlSrc iLast) (hCtrlDst iLast)
      (hSrcDst.ne iLast iLast) hAncInS hCtrlNotS hSrcNotS hLo ?_
    intro β hβ
    change ((QRegister.singleton wAnc).basisOutcomeProjector 0).mulVec
      ((T_anc * U_lo * T_anc).1.mulVec (ket β)) = _
    rw [hSandKet β hβ, Matrix.mulVec_smul, singleton_projector_zero_mulVec_ket,
      ite_eq_left (hβ wAnc hAncInS)]

/-- Recursive temporary-AND sandwich computing all `2 ^ s - s - 1` non-linear multilinear monomials
of `rOff` into clean `rMono`, running `body`, and uncomputing `rMono` in `0` `T` gates. -/
def monoSandwichDyn {Var : Type} {N : ℕ} (v : Var) :
    (s : ℕ) → (rOff : QRegister s N) → (rMono : QRegister (anfScratchWidth s) N) →
    rOff.DisjointWires rMono → DynamicCircuit Var N → DynamicCircuit Var N
  | 0, _, _, _, body => body
  | s + 1, rOff, rMono, hDisj, body =>
      let iMsb : Fin (s + 1) := ⟨s, Nat.lt_succ_self s⟩
      let emb := Fin.castLEEmb (Nat.le_succ s)
      let hLo : 0 + anfScratchWidth s ≤ anfScratchWidth (s + 1) := by simp [anfScratchWidth]
      let hHi : anfScratchWidth s + (2 ^ s - 1) ≤ anfScratchWidth (s + 1) := by
        simp [anfScratchWidth]
      let rOffLo := rOff.subregister emb
      let rMonoLo := rMono.slice 0 (anfScratchWidth s) hLo
      let rMonoHi := rMono.slice (anfScratchWidth s) (2 ^ s - 1) hHi
      let hDisjLo : rOffLo.DisjointWires rMonoLo :=
        (hDisj.compose_left ⟨emb⟩).compose_right (QRegister.block 0 (anfScratchWidth s) hLo)
      let rAllLo := allMonoReg s rOffLo rMonoLo hDisjLo
      have hAllSub := allMonoReg_image_subset rOffLo rMonoLo hDisjLo
      have hMsbAll : ∀ j : Fin (2 ^ s - 1), rOff iMsb ≠ rAllLo j := by
        intro j hEq
        have hmem := hAllSub ((QRegister.mem_image rAllLo _).mpr ⟨j, rfl⟩)
        rw [← hEq] at hmem
        rcases Finset.mem_union.mp hmem with hO | hM
        · obtain ⟨k, hk⟩ := (QRegister.mem_image rOffLo _).mp hO
          have := congrArg Fin.val (rOff.wires.injective hk)
          dsimp [iMsb, emb] at this
          omega
        · obtain ⟨k, hk⟩ := (QRegister.mem_image rMonoLo _).mp hM
          exact hDisj.ne iMsb _ hk.symm
      have hMsbHi : ∀ j : Fin (2 ^ s - 1), rOff iMsb ≠ rMonoHi j :=
        fun _ ↦ hDisj.ne iMsb _
      have hAllHi : rAllLo.DisjointWires rMonoHi := by
        rw [QRegister.disjoint_iff]
        intro j k hEq
        have hmem := hAllSub ((QRegister.mem_image rAllLo _).mpr ⟨j, rfl⟩)
        rw [hEq] at hmem
        rcases Finset.mem_union.mp hmem with hO | hM
        · obtain ⟨m, hm⟩ := (QRegister.mem_image rOffLo _).mp hO
          exact hDisj.ne _ _ hm
        · obtain ⟨m, hm⟩ := (QRegister.mem_image rMonoLo _).mp hM
          exact (rMono.slice_disjoint_of_le 0 (anfScratchWidth s)
            (anfScratchWidth s) (2 ^ s - 1) hLo hHi (by omega)).ne m k hm
      monoSandwichDyn v s rOffLo rMonoLo hDisjLo
        (regAndWithWireSandwichDyn v (rOff iMsb) (2 ^ s - 1) rAllLo rMonoHi
          hMsbAll (show ∀ j : Fin (2 ^ s - 1), rOff iMsb ≠ rMonoHi j from hMsbHi) hAllHi body)

@[simp]
theorem count_monoSandwichDyn_toff {Var : Type} {N s : ℕ} (v : Var)
    (rOff : QRegister s N) (rMono : QRegister (anfScratchWidth s) N)
    (hDisj : rOff.DisjointWires rMono) (body : DynamicCircuit Var N) :
    (monoSandwichDyn v s rOff rMono hDisj body).count PrimitiveGate.TOFF =
      body.count PrimitiveGate.TOFF := by
  induction s generalizing body with
  | zero => rfl
  | succ s ih =>
    simp only [monoSandwichDyn]
    rw [ih, count_regAndWithWireSandwichDyn_toff]

@[simp]
theorem count_monoSandwichDyn_t {Var : Type} {N s : ℕ} (v : Var)
    (rOff : QRegister s N) (rMono : QRegister (anfScratchWidth s) N)
    (hDisj : rOff.DisjointWires rMono) (body : DynamicCircuit Var N) :
    (monoSandwichDyn v s rOff rMono hDisj body).count PrimitiveGate.T =
      4 * anfScratchWidth s + body.count PrimitiveGate.T := by
  induction s generalizing body with
  | zero => simp [monoSandwichDyn, anfScratchWidth]
  | succ s ih =>
    simp only [monoSandwichDyn]
    rw [ih, count_regAndWithWireSandwichDyn_t]
    simp only [anfScratchWidth]
    ring

theorem cleanRealizesSet_monoSandwichDyn_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (rOff : QRegister s N) (rMono : QRegister (anfScratchWidth s) N)
    (hDisj : rOff.DisjointWires rMono)
    (hMonoSubS : rMono.image ⊆ S) (hDisjOffS : Disjoint rOff.image S)
    {U_body : Unitary (2 ^ N)} {body : DynamicCircuit Var N} {φ : BitAssignment N → ℂ}
    (hBody : CleanRealizesSet v (S \ rMono.image) U_body body)
    (hBodyKet : ∀ β : BitAssignment N, (∀ x ∈ S \ rMono.image, β x = 0) →
      U_body.1.mulVec (ket β) = φ β • ket β) :
    ∃ (U : Unitary (2 ^ N)) (pop : BitAssignment N → BitAssignment N),
      CleanRealizesSet v S U (monoSandwichDyn v s rOff rMono hDisj body) ∧
      ∀ β : BitAssignment N, (∀ x ∈ S, β x = 0) →
        U.1.mulVec (ket β) = φ (pop β) • ket β ∧
        (∀ w, w ∉ rMono.image → pop β w = β w) ∧
        (∀ u : Fin (2 ^ s - 1),
          pop β (allMonoReg s rOff rMono hDisj u) =
            monoEval s (fun i ↦ β (rOff i))
              ⟨u.val + 1, by have := u.isLt; have := Nat.one_le_two_pow (n := s); omega⟩) := by
  induction s generalizing S body U_body φ with
  | zero =>
    have hMonoEmpty : rMono.image = ∅ := by
      ext q
      simp only [Finset.notMem_empty, iff_false]
      intro hmem
      obtain ⟨j, _⟩ := (QRegister.mem_image rMono q).mp hmem
      exact j.elim0
    rw [hMonoEmpty, Finset.sdiff_empty] at hBody hBodyKet
    refine ⟨U_body, id, hBody, ?_⟩
    intro β hβ
    refine ⟨hBodyKet β hβ, fun _ _ ↦ rfl, fun u ↦ u.elim0⟩
  | succ s ih =>
    let iMsb : Fin (s + 1) := ⟨s, Nat.lt_succ_self s⟩
    let emb := Fin.castLEEmb (Nat.le_succ s)
    let hLo : 0 + anfScratchWidth s ≤ anfScratchWidth (s + 1) := by simp [anfScratchWidth]
    let hHi : anfScratchWidth s + (2 ^ s - 1) ≤ anfScratchWidth (s + 1) := by
      simp [anfScratchWidth]
    let rOffLo := rOff.subregister emb
    let rMonoLo := rMono.slice 0 (anfScratchWidth s) hLo
    let rMonoHi := rMono.slice (anfScratchWidth s) (2 ^ s - 1) hHi
    let hDisjLo : rOffLo.DisjointWires rMonoLo :=
      (hDisj.compose_left ⟨emb⟩).compose_right (QRegister.block 0 (anfScratchWidth s) hLo)
    let rAllLo := allMonoReg s rOffLo rMonoLo hDisjLo
    have hAllSub := allMonoReg_image_subset rOffLo rMonoLo hDisjLo
    have hLoHiDisj : Disjoint rMonoLo.image rMonoHi.image :=
      disjoint_image_of_disjointWires
        (rMono.slice_disjoint_of_le 0 (anfScratchWidth s)
          (anfScratchWidth s) (2 ^ s - 1) hLo hHi (by omega))
    have hMonoImg : rMono.image = rMonoLo.image ∪ rMonoHi.image := by
      apply Finset.Subset.antisymm
      · intro q hq
        obtain ⟨k, rfl⟩ := (QRegister.mem_image rMono q).mp hq
        by_cases hk : k.val < anfScratchWidth s
        · refine Finset.mem_union_left _
            ((QRegister.mem_image rMonoLo _).mpr ⟨⟨k.val, hk⟩, ?_⟩)
          dsimp [rMonoLo]
          congr 1
          apply Fin.ext
          simp
        · have hkHi : k.val - anfScratchWidth s < 2 ^ s - 1 := by
            have := k.isLt
            simp only [anfScratchWidth] at this
            omega
          refine Finset.mem_union_right _
            ((QRegister.mem_image rMonoHi _).mpr ⟨⟨k.val - anfScratchWidth s, hkHi⟩, ?_⟩)
          dsimp [rMonoHi]
          congr 1
          apply Fin.ext
          dsimp
          omega
      · exact Finset.union_subset (rMono.image_compose_subset _) (rMono.image_compose_subset _)
    let S_hi := S \ rMonoLo.image
    have hMonoHiSub : rMonoHi.image ⊆ S_hi := by
      intro q hq
      exact Finset.mem_sdiff.mpr ⟨hMonoSubS ((rMono.image_compose_subset _) hq),
        Finset.disjoint_right.mp hLoHiDisj hq⟩
    have hMsbNotSHi : rOff iMsb ∉ S_hi :=
      fun h ↦ Finset.disjoint_left.mp hDisjOffS
        ((QRegister.mem_image rOff _).mpr ⟨iMsb, rfl⟩) (Finset.mem_sdiff.mp h).1
    have hDisjAllSHi : Disjoint rAllLo.image S_hi := by
      refine Disjoint.mono_left hAllSub (Finset.disjoint_union_left.mpr ⟨?_, ?_⟩)
      · exact Disjoint.mono (rOff.image_compose_subset _) Finset.sdiff_subset hDisjOffS
      · rw [Finset.disjoint_left]
        intro x hx hxs
        exact (Finset.mem_sdiff.mp hxs).2 hx
    have hSdiffEq : S_hi \ rMonoHi.image = S \ rMono.image := by
      ext q
      simp [S_hi, hMonoImg, and_assoc]
    have hBodyHi : CleanRealizesSet v (S_hi \ rMonoHi.image) U_body body := by
      rwa [hSdiffEq]
    have hBodyKetHi : ∀ β : BitAssignment N, (∀ x ∈ S_hi \ rMonoHi.image, β x = 0) →
        U_body.1.mulVec (ket β) = φ β • ket β := by
      intro β hβ
      exact hBodyKet β (by rwa [← hSdiffEq])
    obtain ⟨U_mid, hMid, hkMid⟩ :=
      cleanRealizesSet_regAndWithWireSandwichDyn_diag v S_hi (rOff iMsb) rAllLo rMonoHi
        _ _ _ hMonoHiSub hMsbNotSHi hDisjAllSHi hBodyHi hBodyKetHi
    have hMonoLoSubS : rMonoLo.image ⊆ S := (rMono.image_compose_subset _).trans hMonoSubS
    have hDisjOffLoS : Disjoint rOffLo.image S :=
      Disjoint.mono_left (rOff.image_compose_subset _) hDisjOffS
    obtain ⟨U_full, pop_lo, hFull, hkFull⟩ :=
      ih S rOffLo rMonoLo hDisjLo hMonoLoSubS hDisjOffLoS hMid hkMid
    refine ⟨U_full, fun β ↦ xorAndRegBits (pop_lo β) (rOff iMsb) rAllLo rMonoHi, hFull, ?_⟩
    intro β hβ
    obtain ⟨hKetEq, hOutLo, hAllLoEq⟩ := hkFull β hβ
    refine ⟨hKetEq, ?_, ?_⟩
    · intro w hw
      have hwNotHi : w ∉ rMonoHi.image :=
        fun h ↦ hw (hMonoImg ▸ Finset.mem_union_right _ h)
      have hwNotLo : w ∉ rMonoLo.image :=
        fun h ↦ hw (hMonoImg ▸ Finset.mem_union_left _ h)
      dsimp only
      rw [xorAndRegBits_apply_of_not_mem _ _ _ _ _ hwNotHi, hOutLo w hwNotLo]
    · intro u
      have hMsbNotMono : rOff iMsb ∉ rMono.image := hDisj.apply_not_mem_right iMsb
      have hMsbNotLo : rOff iMsb ∉ rMonoLo.image :=
        fun h ↦ hMsbNotMono ((rMono.image_compose_subset _) h)
      have hMsbNotHi : rOff iMsb ∉ rMonoHi.image :=
        fun h ↦ hMsbNotMono ((rMono.image_compose_subset _) h)
      by_cases hu : u.val < 2 ^ s - 1
      · rw [allMonoReg_apply_lt rOff rMono hDisj u hu]
        have hNotHi : rAllLo ⟨u.val, hu⟩ ∉ rMonoHi.image := by
          intro hmem
          have hmemA := hAllSub ((QRegister.mem_image rAllLo _).mpr ⟨⟨u.val, hu⟩, rfl⟩)
          rcases Finset.mem_union.mp hmemA with hO | hM
          · obtain ⟨k, hk⟩ := (QRegister.mem_image rOffLo _).mp hO
            exact hDisj.apply_not_mem_right (Fin.castLE (Nat.le_succ s) k)
              (hk ▸ (rMono.image_compose_subset _) hmem)
          · exact Finset.disjoint_left.mp hLoHiDisj hM hmem
        change xorAndRegBits (pop_lo β) (rOff iMsb) rAllLo rMonoHi (rAllLo ⟨u.val, hu⟩) = _
        rw [xorAndRegBits_apply_of_not_mem _ _ _ _ _ hNotHi, hAllLoEq ⟨u.val, hu⟩]
        have hu1Lt : u.val + 1 < 2 ^ s := by omega
        simp only [monoEval, hu1Lt, ↓reduceDIte]
        rfl
      · by_cases huEq : u.val = 2 ^ s - 1
        · rw [allMonoReg_apply_eq rOff rMono hDisj u huEq]
          change xorAndRegBits (pop_lo β) (rOff iMsb) rAllLo rMonoHi (rOff iMsb) = _
          rw [xorAndRegBits_apply_of_not_mem _ _ _ _ _ hMsbNotHi, hOutLo _ hMsbNotLo]
          have hu1Eq : u.val + 1 = 2 ^ s := by
            have := Nat.one_le_two_pow (n := s)
            omega
          have hu1NotLt : ¬(u.val + 1 < 2 ^ s) := by omega
          have hu1Sub : u.val + 1 - 2 ^ s = 0 := by omega
          have hFin0 : (⟨u.val + 1 - 2 ^ s, by
              have hm2 : u.val + 1 < 2 * 2 ^ s := by omega
              omega⟩ : Fin (2 ^ s)) = ⟨0, Nat.two_pow_pos s⟩ := Fin.ext hu1Sub
          simp only [monoEval, hu1NotLt, ↓reduceDIte, hFin0, monoEval_zero, mul_one]
          rfl
        · have huGe : 2 ^ s ≤ u.val := by omega
          rw [allMonoReg_apply_ge rOff rMono hDisj u huGe]
          let t : Fin (2 ^ s - 1) := ⟨u.val - 2 ^ s, by
            have hu2 : u.val < 2 * 2 ^ s - 1 := by simpa only [pow_succ'] using u.isLt
            have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
            omega⟩
          change xorAndRegBits (pop_lo β) (rOff iMsb) rAllLo rMonoHi (rMonoHi t) = _
          rw [xorAndRegBits_apply_dst]
          have htNotLo : rMonoHi t ∉ rMonoLo.image :=
            Finset.disjoint_right.mp hLoHiDisj ((QRegister.mem_image rMonoHi _).mpr ⟨t, rfl⟩)
          have htInS : rMonoHi t ∈ S :=
            hMonoSubS
              ((rMono.image_compose_subset _) ((QRegister.mem_image rMonoHi _).mpr ⟨t, rfl⟩))
          rw [hOutLo (rMonoHi t) htNotLo, hβ (rMonoHi t) htInS, zero_add,
            hOutLo (rOff iMsb) hMsbNotLo, hAllLoEq t]
          have hu1NotLt : ¬(u.val + 1 < 2 ^ s) := by omega
          have hu1Sub : u.val + 1 - 2 ^ s = t.val + 1 := by dsimp [t]; omega
          have hFinEq : (⟨u.val + 1 - 2 ^ s, by
              have hu2 : u.val < 2 * 2 ^ s - 1 := by simpa only [pow_succ'] using u.isLt
              omega⟩ : Fin (2 ^ s)) =
              ⟨t.val + 1, by have := t.isLt; have := Nat.one_le_two_pow (n := s); omega⟩ :=
            Fin.ext hu1Sub
          simp only [monoEval, hu1NotLt, ↓reduceDIte, hFinEq]
          rfl

/-!
### Complete `1`-Bit ANF Phase Fixup (`selectSwapPhaseFixupDyn`)
-/

/-- The `2 ^ s`-entry `ZMod 2` phase block `q` of Boolean phase table `P` (bounded by `L`). -/
def blockPhaseFn (s L : ℕ) (P : ℕ → Bool) (q : ℕ) (r : Fin (2 ^ s)) : ZMod 2 :=
  if decide (2 ^ s * q + r.val < L) && P (2 ^ s * q + r.val) then 1 else 0

private theorem wp_qAssign_one {Var : Type} [Fintype Var] {N : ℕ}
    (Θ : QCAssertion Var (2 ^ N)) :
    qcWpQAssign (1 : Unitary (2 ^ N)) Θ = Θ := by
  funext σ
  apply Subtype.ext
  simp [qcWpQAssign]

/-- Four-conjunct specification for a dynamic circuit `P` that uncomputes `W_load` on measured
wires `M_set ⊆ S` into residual unitary `U_rem` using only classical variable `v : Var`, leaving
all wires in `S` clean (`|0⟩`). -/
def CleanUnloadsSet {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (S M_set : Finset (Wire N)) (W_load U_rem : Unitary (2 ^ N))
    (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    restrictZeroSet (qcWpQAssign W_load (wp P.compile Θ)) S =
      restrictZeroSet (qcWpQAssign U_rem Θ) S) ∧
  (∀ Θ : QCAssertion Var (2 ^ N),
    restrictZeroSet (wp P.compile (restrictZeroSet Θ S)) (S \ M_set) =
      restrictZeroSet (wp P.compile Θ) (S \ M_set))

theorem CleanUnloadsSet.of_cleanRealizesSet {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)} {U : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (h : CleanRealizesSet v S U P) :
    CleanUnloadsSet v S ∅ 1 U P := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro Θ hΘ
    rw [wp_qAssign_one]
    exact h.2.2.1 Θ hΘ
  · intro Θ
    simpa only [Finset.sdiff_empty] using h.2.2.2 Θ

theorem CleanUnloadsSet.congr_load {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S M_set : Finset (Wire N)} {W₁ W₂ U_rem : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (h : CleanUnloadsSet v S M_set W₁ U_rem P)
    (hEq : ∀ β : BitAssignment N, (∀ w ∈ S, β w = 0) →
      W₁.1.mulVec (ket β) = W₂.1.mulVec (ket β)) :
    CleanUnloadsSet v S M_set W₂ U_rem P := by
  have hMat : W₁.1 * zeroProjOn S = W₂.1 * zeroProjOn S := by
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
    by_cases hβ : ∀ w ∈ S, β w = 0
    · rw [ite_eq_left hβ, hEq β hβ]
    · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hAdj : zeroProjOn S * W₁.1ᴴ = zeroProjOn S * W₂.1ᴴ := by
    have h' := congrArg conjTranspose hMat
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro Θ hΘ
  rw [← h.2.2.1 Θ hΘ]
  funext σ
  apply Subtype.ext
  simp only [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [hAdj]

/-- Sequential composition of two unload stages: `P₁` unloads `W₁` on `M₁` while `M₂` still holds
the output of `W₂`, and `P₂` then unloads `W₂` on `M₂`. -/
theorem CleanUnloadsSet.seq {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S M₁ M₂ : Finset (Wire N)} {W₁ W₂ U_rem : Unitary (2 ^ N)}
    {P₁ P₂ : DynamicCircuit Var N}
    (hM₂ : M₂ ⊆ S)
    (h₁ : CleanUnloadsSet v (S \ M₂) M₁ W₁ 1 P₁)
    (h₂ : CleanUnloadsSet v S M₂ W₂ U_rem P₂)
    (hW₂Comm : W₂.1 * zeroProjOn (S \ M₂) = zeroProjOn (S \ M₂) * W₂.1) :
    CleanUnloadsSet v S (M₁ ∪ M₂) (W₁ * W₂) U_rem (.seq P₁ P₂) := by
  have hUnion : (S \ M₂) ∪ M₂ = S := by
    ext x
    by_cases hx : x ∈ M₂
    · simp [hx, hM₂ hx]
    · simp [hx]
  have hAdj : zeroProjOn (S \ M₂) * W₂.1ᴴ = W₂.1ᴴ * zeroProjOn (S \ M₂) := by
    have h' := congrArg conjTranspose hW₂Comm
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'
  have hCommPsi (Ψ : QCAssertion Var (2 ^ N)) :
      restrictZeroSet (qcWpQAssign W₂ Ψ) (S \ M₂) = qcWpQAssign W₂ (restrictZeroSet Ψ (S \ M₂)) :=
        by
    funext σ
    apply Subtype.ext
    simp only [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [hAdj]
  refine ⟨by simp [h₁.1, h₂.1], ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    change wp P₁.compile (wp P₂.compile Θ) (Function.update σ v val) =
      wp P₁.compile (wp P₂.compile Θ) σ
    exact h₁.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ) σ val
  · intro Θ hΘ
    change restrictZeroSet (qcWpQAssign (W₁ * W₂) (wp P₁.compile (wp P₂.compile Θ))) S =
      restrictZeroSet (qcWpQAssign U_rem Θ) S
    rw [← qc_wp_qAssign_comp, ← hUnion, ← restrictZeroSet_union, hCommPsi,
      h₁.2.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ), wp_qAssign_one, ← hCommPsi,
      restrictZeroSet_union, hUnion, h₂.2.2.1 Θ hΘ]
  · intro Θ
    have hSdiff : (S \ M₂) \ M₁ = S \ (M₁ ∪ M₂) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    change restrictZeroSet (wp P₁.compile (wp P₂.compile (restrictZeroSet Θ S)))
        (S \ (M₁ ∪ M₂)) =
      restrictZeroSet (wp P₁.compile (wp P₂.compile Θ)) (S \ (M₁ ∪ M₂))
    rw [← hSdiff, ← h₁.2.2.2 (wp P₂.compile (restrictZeroSet Θ S)),
      h₂.2.2.2 Θ, h₁.2.2.2 (wp P₂.compile Θ)]

/-!
### Single-Wire and Multi-Wire `0-T` X-Basis Measurement with Reset
-/

/-- Measures wire `w` in the X basis into `v`, resets `w` to `|0⟩` if the outcome was `1`, and
branches to continuation `k₁` (outcome `1`) or `k₀` (outcome `0`). -/
def measureXReset1AndBranch {Var : Type} {N : ℕ} (v : Var) (w : Wire N)
    (k₀ k₁ : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (.circuit (Circuit.H w))
    (.seq (.measure v (QRegister.singleton w))
      (qcQIf (fun σ ↦ σ v) (.seq (.circuit (Circuit.X w)) k₁) k₀))

@[simp]
theorem count_measureXReset1AndBranch_toff {Var : Type} {N : ℕ} (v : Var) (w : Wire N)
    (k₀ k₁ : DynamicCircuit Var N) :
    (measureXReset1AndBranch v w k₀ k₁).count PrimitiveGate.TOFF =
      max (k₁.count PrimitiveGate.TOFF) (k₀.count PrimitiveGate.TOFF) := by
  simp [measureXReset1AndBranch, Circuit.H, Circuit.X, Circuit.single]

@[simp]
theorem count_measureXReset1AndBranch_t {Var : Type} {N : ℕ} (v : Var) (w : Wire N)
    (k₀ k₁ : DynamicCircuit Var N) :
    (measureXReset1AndBranch v w k₀ k₁).count PrimitiveGate.T =
      max (k₁.count PrimitiveGate.T) (k₀.count PrimitiveGate.T) := by
  simp [measureXReset1AndBranch, Circuit.H, Circuit.X, Circuit.single]

private theorem wp_measureXReset1AndBranch_apply {Var : Type} [Finite Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (w : Wire N) (k₀ k₁ : DynamicCircuit Var N)
    (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    let P₀ := (QRegister.singleton w).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton w).basisOutcomeProjector 1
    let L₀ := P₀ * (Circuit.H w).eval.1
    let L₁ := (Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1
    (wp (measureXReset1AndBranch v w k₀ k₁).compile Θ σ).1 =
      (wp k₀.compile Θ (Function.update σ v 0)).1.conj L₀ᴴ +
        (wp k₁.compile Θ (Function.update σ v 1)).1.conj L₁ᴴ := by
  have := Fintype.ofFinite Var
  intro P₀ P₁ L₀ L₁
  let U := Circuit.H w
  let Xw := Circuit.X w
  have hmeas_apply :
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton w))
          (qcQIf (fun σ'' ↦ σ'' v) (.qSeq Xw.compile k₁.compile) k₀.compile)) Θ σ).1 =
        (wp k₀.compile Θ (Function.update σ v 0)).1.conj P₀ᴴ +
          ((wp k₁.compile Θ (Function.update σ v 1)).1.conj Xw.eval.1ᴴ).conj P₁ᴴ := by
    have hsubst0 : σ.subst v 0 = Function.update σ v 0 := by
      funext y; simp [Store.subst, Function.update]
    have hsubst1 : σ.subst v 1 = Function.update σ v 1 := by
      funext y; simp [Store.subst, Function.update]
    simp only [wp_qSeq, wp_qIf, qc_wp_qMeasure', QProg.measureRegister, qc_wp_qMeasure_apply,
      qc_qMeasure_obs_map_coe,
      QCAssertion.subst_apply]
    change ∑ o : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp [qc_qMeasure_outcome_herm_eq_conj, hsubst0, hsubst1,
      qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, QRegister.computationalBasisMeasurement_apply, P₀, P₁, Xw]
  change (wp U.compile
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton w))
        (qcQIf (fun σ'' ↦ σ'' v) (.qSeq Xw.compile k₁.compile) k₀.compile)) Θ) σ).1 = _
  rw [DynamicCircuit.qc_wp_circuit_compile]
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]
  rw [hmeas_apply, map_add, conj_conj, conj_conj, conj_conj]
  dsimp only [L₀, L₁, U, Xw]
  simp only [Matrix.mul_assoc, conjTranspose_mul]

/-- One-wire inductive step for Berry et al. X-basis measurement unloading: measuring `w` in the
X basis, resetting `w` to `|0⟩`, and branching between `B₀` (residual `U₀`) and `B₁` (residual
`U₀ * D_w`) cancels the 1-bit XOR `W_w` while sliding disjoint `W_lo` into both branches. -/
theorem CleanUnloadsSet.measureXReset1 {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S M_lo : Finset (Wire N)} {w : Wire N}
    {W_lo W_w U₀ D_w : Unitary (2 ^ N)} {B₀ B₁ : DynamicCircuit Var N}
    (hwS : w ∈ S) (hwNotM : w ∉ M_lo)
    (hB₀ : CleanUnloadsSet v S M_lo W_lo U₀ B₀)
    (hB₁ : CleanUnloadsSet v S M_lo W_lo (U₀ * D_w) B₁)
    {bitFn : BitAssignment N → Bool} {g : BitAssignment N → BitAssignment N}
    (hWloKet : ∀ β : BitAssignment N, W_lo.1.mulVec (ket β) = ket (g β))
    (hgSame : ∀ β : BitAssignment N, g β w = β w)
    (hgUpd : ∀ (β : BitAssignment N) (val : ZMod 2),
      g (Function.update β w val) = Function.update (g β) w val)
    (hWwKet : ∀ β : BitAssignment N,
      W_w.1.mulVec (ket β) = ket (Function.update β w (β w + if bitFn β then 1 else 0)))
    (hDwKet : ∀ β : BitAssignment N, (∀ x ∈ S, β x = 0) →
      D_w.1.mulVec (ket β) = (if bitFn β then (-1 : ℂ) else 1) • ket β)
    (hDwSq : D_w * D_w = 1)
    (hDwComm : D_w.1 * zeroProjOn S = zeroProjOn S * D_w.1) :
    CleanUnloadsSet v S (insert w M_lo) (W_lo * W_w) U₀
      (measureXReset1AndBranch v w B₀ B₁) := by
  let P₀ := (QRegister.singleton w).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton w).basisOutcomeProjector 1
  let L₀ := P₀ * (Circuit.H w).eval.1
  let L₁ := (Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1
  have hCommH : (Circuit.H w).eval.1 * W_lo.1 = W_lo.1 * (Circuit.H w).eval.1 := by
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec]
    rw [hWloKet, ket_H, hgSame, ← hgUpd, ← hgUpd, ket_H,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hWloKet, hWloKet]
  have hCommX : (Circuit.X w).eval.1 * W_lo.1 = W_lo.1 * (Circuit.X w).eval.1 := by
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec]
    rw [hWloKet, ket_X, hgSame, ← hgUpd, ket_X, hWloKet]
  have hCommP₀ : P₀ * W_lo.1 = W_lo.1 * P₀ := by
    apply matrix_ext_ket
    intro β
    simp only [P₀, ← Matrix.mulVec_mulVec]
    rw [hWloKet, singleton_projector_zero_mulVec_ket, hgSame, singleton_projector_zero_mulVec_ket]
    by_cases hw0 : β w = 0
    · rw [ite_eq_left hw0, ite_eq_left hw0, hWloKet]
    · rw [ite_eq_right hw0, ite_eq_right hw0, Matrix.mulVec_zero]
  have hCommP₁ : P₁ * W_lo.1 = W_lo.1 * P₁ := by
    apply matrix_ext_ket
    intro β
    simp only [P₁, ← Matrix.mulVec_mulVec]
    rw [hWloKet, singleton_projector_one_mulVec_ket, hgSame, singleton_projector_one_mulVec_ket]
    by_cases hw1 : β w = 1
    · rw [ite_eq_left hw1, ite_eq_left hw1, hWloKet]
    · rw [ite_eq_right hw1, ite_eq_right hw1, Matrix.mulVec_zero]
  have hL₀Wlo : W_lo.1ᴴ * L₀ᴴ = L₀ᴴ * W_lo.1ᴴ := by
    have h : L₀ * W_lo.1 = W_lo.1 * L₀ := by
      dsimp only [L₀]
      rw [Matrix.mul_assoc, hCommH, ← Matrix.mul_assoc, hCommP₀, Matrix.mul_assoc]
    simpa only [conjTranspose_mul] using congrArg conjTranspose h
  have hL₁Wlo : W_lo.1ᴴ * L₁ᴴ = L₁ᴴ * W_lo.1ᴴ := by
    have h : L₁ * W_lo.1 = W_lo.1 * L₁ := by
      dsimp only [L₁]
      calc (Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1 * W_lo.1
          = (Circuit.X w).eval.1 * P₁ * ((Circuit.H w).eval.1 * W_lo.1) := by
              simp only [Matrix.mul_assoc]
        _ = (Circuit.X w).eval.1 * (P₁ * W_lo.1) * (Circuit.H w).eval.1 := by
              rw [hCommH]; simp only [Matrix.mul_assoc]
        _ = ((Circuit.X w).eval.1 * W_lo.1) * P₁ * (Circuit.H w).eval.1 := by
              rw [hCommP₁]; simp only [Matrix.mul_assoc]
        _ = W_lo.1 * ((Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1) := by
              rw [hCommX]; simp only [Matrix.mul_assoc]
    simpa only [conjTranspose_mul] using congrArg conjTranspose h
  have hKraus0 : L₀ * W_w.1 * zeroProjOn S = sqrtHalf • zeroProjOn S := by
    apply matrix_ext_ket
    intro β
    simp only [L₀, P₀, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, zeroProjOn_mulVec_ket]
    by_cases hβ : ∀ x ∈ S, β x = 0
    · have hβw : β w = 0 := hβ w hwS
      rw [ite_eq_left hβ, hWwKet, hβw, zero_add, ket_H,
        Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
        Function.update_idem, Function.update_idem, Function.update_self,
        singleton_projector_zero_mulVec_ket, singleton_projector_zero_mulVec_ket]
      have hupd0 : Function.update β w 0 = β := by rw [← hβw]; exact Function.update_eq_self w β
      have hupd1 : Function.update β w 1 w ≠ 0 := by simp
      rw [hupd0, ite_eq_left hβw, ite_eq_right hupd1, smul_zero, add_zero]
    · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  have hKraus1 : L₁ * W_w.1 * zeroProjOn S = sqrtHalf • (zeroProjOn S * D_w.1) := by
    rw [← hDwComm]
    apply matrix_ext_ket
    intro β
    simp only [L₁, P₁, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, zeroProjOn_mulVec_ket]
    by_cases hβ : ∀ x ∈ S, β x = 0
    · have hβw : β w = 0 := hβ w hwS
      have h01 : ((0 : ZMod 2) = 1) = False := by decide
      have hupd0 : Function.update β w 0 = β := by rw [← hβw]; exact Function.update_eq_self w β
      rw [ite_eq_left hβ, hWwKet, hβw, zero_add, ket_H]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Function.update_idem,
        singleton_projector_one_mulVec_ket, Function.update_self, h01, ↓reduceIte,
        zero_add, ket_X, one_add_one_zmod2]
      rw [hupd0, hDwKet β hβ]
      cases bitFn β <;> simp [bitSign]
    · simp only [ite_eq_right hβ, Matrix.mulVec_zero, smul_zero]
  have hKraus0Adj : zeroProjOn S * W_w.1ᴴ * L₀ᴴ = sqrtHalf • zeroProjOn S := by
    have h' := congrArg conjTranspose hKraus0
    simpa only [conjTranspose_mul, conjTranspose_smul, star_sqrtHalf,
      zeroProjOn_conjTranspose, ← Matrix.mul_assoc] using h'
  have hKraus1Adj : zeroProjOn S * W_w.1ᴴ * L₁ᴴ = sqrtHalf • (D_w.1ᴴ * zeroProjOn S) := by
    have h' := congrArg conjTranspose hKraus1
    simpa only [conjTranspose_mul, conjTranspose_smul, star_sqrtHalf,
      zeroProjOn_conjTranspose, ← Matrix.mul_assoc] using h'
  have hDwAdjComm : D_w.1ᴴ * zeroProjOn S = zeroProjOn S * D_w.1ᴴ := by
    have h' := congrArg conjTranspose hDwComm.symm
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'
  have hDwAdjSq : D_w.1ᴴ * D_w.1ᴴ = 1 := by
    have h' := congrArg (fun u : Unitary (2 ^ N) ↦ u.1ᴴ) hDwSq
    simpa only [Submonoid.coe_mul, Submonoid.coe_one, conjTranspose_mul,
      conjTranspose_one] using h'
  refine ⟨by simp [hB₀.1, hB₁.1], ?_, ?_, ?_⟩
  · intro Θ _ σ val
    apply Subtype.ext
    rw [wp_measureXReset1AndBranch_apply, wp_measureXReset1AndBranch_apply,
      Function.update_idem, Function.update_idem]
  · intro Θ hΘ
    rw [← qc_wp_qAssign_comp]
    funext σ
    apply Subtype.ext
    have hStepLo :
        (qcWpQAssign W_lo (wp (measureXReset1AndBranch v w B₀ B₁).compile Θ) σ).1 =
          (qcWpQAssign W_lo (wp B₀.compile Θ) (Function.update σ v 0)).1.conj L₀ᴴ +
            (qcWpQAssign W_lo (wp B₁.compile Θ) (Function.update σ v 1)).1.conj L₁ᴴ := by
      simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose]
      rw [wp_measureXReset1AndBranch_apply, map_add, conj_conj, conj_conj, hL₀Wlo, hL₁Wlo,
        ← conj_conj, ← conj_conj]
    have h0Eq :
        (restrictZeroSet (qcWpQAssign W_lo (wp B₀.compile Θ)) S (Function.update σ v 0)).1 =
          (Θ σ).1.conj (zeroProjOn S * U₀.1ᴴ) := by
      rw [hB₀.2.2.1 Θ hΘ]
      simp [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hΘ σ 0]
    have h1Eq :
        (restrictZeroSet (qcWpQAssign W_lo (wp B₁.compile Θ)) S (Function.update σ v 1)).1 =
          (Θ σ).1.conj (zeroProjOn S * (U₀ * D_w).1ᴴ) := by
      rw [hB₁.2.2.1 Θ hΘ]
      simp [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hΘ σ 1]
    ext1
    have hLhsExpand :
        (restrictZeroSet (qcWpQAssign W_w
          (qcWpQAssign W_lo (wp (measureXReset1AndBranch v w B₀ B₁).compile Θ))) S σ).1 =
        (qcWpQAssign W_lo (wp B₀.compile Θ) (Function.update σ v 0)).1.conj
          (sqrtHalf • zeroProjOn S) +
        (qcWpQAssign W_lo (wp B₁.compile Θ) (Function.update σ v 1)).1.conj
          (sqrtHalf • (D_w.1ᴴ * zeroProjOn S)) := by
      have hOuter (Ψ : QCAssertion Var (2 ^ N)) :
          (restrictZeroSet (qcWpQAssign W_w Ψ) S σ).1 =
            ((Ψ σ).1.conj W_w.1ᴴ).conj (zeroProjOn S) := by
        simp [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
          Unitary.coe_star, Matrix.star_eq_conjTranspose]
      rw [hOuter, hStepLo, map_add, map_add, conj_conj, conj_conj, conj_conj, conj_conj,
        hKraus0Adj, hKraus1Adj]
    have hTerm0 :
        ((qcWpQAssign W_lo (wp B₀.compile Θ) (Function.update σ v 0)).1.conj
          (sqrtHalf • zeroProjOn S)).mat =
        (1 / 2 : ℂ) • ((Θ σ).1.conj (zeroProjOn S * U₀.1ᴴ)).mat := by
      have h0Mat := congrArg HermitianMat.mat h0Eq
      simp only [restrictZeroSet_coe, conj_apply_mat, conjTranspose_smul, star_sqrtHalf,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrtHalf_mul_sqrtHalf] at h0Mat ⊢
      rw [h0Mat]
    have hTerm1 :
        ((qcWpQAssign W_lo (wp B₁.compile Θ) (Function.update σ v 1)).1.conj
          (sqrtHalf • (D_w.1ᴴ * zeroProjOn S))).mat =
        (1 / 2 : ℂ) • ((Θ σ).1.conj (zeroProjOn S * U₀.1ᴴ)).mat := by
      have hCollapse : D_w.1ᴴ * (zeroProjOn S * (U₀ * D_w).1ᴴ) = zeroProjOn S * U₀.1ᴴ := by
        simp only [Submonoid.coe_mul, conjTranspose_mul]
        calc D_w.1ᴴ * (zeroProjOn S * (D_w.1ᴴ * U₀.1ᴴ))
            = (D_w.1ᴴ * zeroProjOn S) * D_w.1ᴴ * U₀.1ᴴ := by simp only [Matrix.mul_assoc]
          _ = zeroProjOn S * (D_w.1ᴴ * D_w.1ᴴ) * U₀.1ᴴ := by
              rw [hDwAdjComm, Matrix.mul_assoc (zeroProjOn S)]
          _ = zeroProjOn S * U₀.1ᴴ := by rw [hDwAdjSq, Matrix.mul_one]
      have h1Conj :
          ((qcWpQAssign W_lo (wp B₁.compile Θ) (Function.update σ v 1)).1.conj
            (D_w.1ᴴ * zeroProjOn S)).mat =
          ((Θ σ).1.conj (zeroProjOn S * U₀.1ᴴ)).mat := by
        have h' := congrArg (fun H : HermitianMat (Fin (2 ^ N)) ℂ ↦ (H.conj D_w.1ᴴ).mat) h1Eq
        dsimp only [restrictZeroSet_coe] at h'
        rw [conj_conj, conj_conj, hCollapse] at h'
        exact h'
      simp only [conj_apply_mat, conjTranspose_smul, star_sqrtHalf,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrtHalf_mul_sqrtHalf] at h1Conj ⊢
      rw [h1Conj]
    have hRhsMat :
        (restrictZeroSet (qcWpQAssign U₀ Θ) S σ).1.mat =
          ((Θ σ).1.conj (zeroProjOn S * U₀.1ᴴ)).mat := by
      simp [restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [congrArg HermitianMat.mat hLhsExpand, HermitianMat.mat_add, hTerm0, hTerm1,
      ← add_smul, hRhsMat]
    norm_num
  · intro Θ
    let S_rem := S \ M_lo
    let S_out := S \ insert w M_lo
    have hL₀Post : zeroProjOn S_out * L₀ᴴ = L₀ᴴ * zeroProjOn S_rem := by
      have h : L₀ * zeroProjOn S_out = zeroProjOn S_rem * L₀ := by
        apply matrix_ext_ket
        intro β
        simp only [L₀, P₀, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
        by_cases hOut : ∀ x ∈ S_out, β x = 0
        · rw [ite_eq_left hOut, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
            singleton_projector_zero_mulVec_ket, singleton_projector_zero_mulVec_ket]
          have hupd0 : Function.update β w 0 w = 0 := Function.update_self w 0 β
          have hupd1 : Function.update β w 1 w ≠ 0 := by simp
          rw [ite_eq_left hupd0, ite_eq_right hupd1, smul_zero, add_zero,
            Matrix.mulVec_smul, zeroProjOn_mulVec_ket]
          have hRem : ∀ x ∈ S_rem, Function.update β w 0 x = 0 := by
            intro x hx
            by_cases hxw : x = w
            · subst hxw; simp
            · rw [Function.update_of_ne hxw]
              exact hOut x (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
                fun hmem ↦ (Finset.mem_insert.mp hmem).elim hxw (Finset.mem_sdiff.mp hx).2⟩)
          rw [ite_eq_left hRem]
        · have hupd0 : Function.update β w 0 w = 0 := Function.update_self w 0 β
          have hupd1 : Function.update β w 1 w ≠ 0 := by simp
          rw [ite_eq_right hOut, ket_H]
          simp only [Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_add,
            singleton_projector_zero_mulVec_ket, hupd0, ↓reduceIte, ite_eq_right hupd1,
            smul_zero, add_zero, zeroProjOn_mulVec_ket]
          have hNotRem : ¬(∀ x ∈ S_rem, Function.update β w 0 x = 0) := by
            intro hRem
            apply hOut
            intro x hx
            have hxw : x ≠ w :=
              fun hEq ↦ (Finset.mem_sdiff.mp hx).2 (hEq ▸ Finset.mem_insert_self w M_lo)
            have hxRem : x ∈ S_rem := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
              fun hm ↦ (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hm)⟩
            simpa [Function.update_of_ne hxw] using hRem x hxRem
          rw [ite_eq_right hNotRem, smul_zero]
      have h' := congrArg conjTranspose h
      simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'
    have hL₁Post : zeroProjOn S_out * L₁ᴴ = L₁ᴴ * zeroProjOn S_rem := by
      have h : L₁ * zeroProjOn S_out = zeroProjOn S_rem * L₁ := by
        apply matrix_ext_ket
        intro β
        simp only [L₁, P₁, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
        by_cases hOut : ∀ x ∈ S_out, β x = 0
        · have h01 : ((0 : ZMod 2) = 1) = False := by decide
          rw [ite_eq_left hOut, ket_H]
          simp only [Matrix.mulVec_smul, Matrix.mulVec_add, singleton_projector_one_mulVec_ket,
            Function.update_self, h01, ↓reduceIte, zero_add,
            ket_X, one_add_one_zmod2, Function.update_idem, zeroProjOn_mulVec_ket]
          have hRem : ∀ x ∈ S_rem, Function.update β w 0 x = 0 := by
            intro x hx
            by_cases hxw : x = w
            · subst hxw; simp
            · rw [Function.update_of_ne hxw]
              exact hOut x (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
                fun hmem ↦ (Finset.mem_insert.mp hmem).elim hxw (Finset.mem_sdiff.mp hx).2⟩)
          rw [ite_eq_left hRem]
        · have h01 : ((0 : ZMod 2) = 1) = False := by decide
          rw [ite_eq_right hOut, ket_H]
          simp only [Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_add,
            singleton_projector_one_mulVec_ket, Function.update_self, h01, ↓reduceIte,
            zero_add, ket_X, one_add_one_zmod2, Function.update_idem, zeroProjOn_mulVec_ket]
          have hNotRem : ¬(∀ x ∈ S_rem, Function.update β w 0 x = 0) := by
            intro hRem
            apply hOut
            intro x hx
            have hxw : x ≠ w :=
              fun hEq ↦ (Finset.mem_sdiff.mp hx).2 (hEq ▸ Finset.mem_insert_self w M_lo)
            have hxRem : x ∈ S_rem := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
              fun hm ↦ (Finset.mem_sdiff.mp hx).2 (Finset.mem_insert_of_mem hm)⟩
            simpa [Function.update_of_ne hxw] using hRem x hxRem
          rw [ite_eq_right hNotRem, smul_zero, smul_zero]
      have h' := congrArg conjTranspose h
      simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using h'
    funext σ
    apply Subtype.ext
    simp only [restrictZeroSet_coe]
    rw [wp_measureXReset1AndBranch_apply, wp_measureXReset1AndBranch_apply,
      map_add, map_add, conj_conj, conj_conj, conj_conj, conj_conj,
      hL₀Post, hL₁Post, ← conj_conj, ← conj_conj, ← conj_conj, ← conj_conj]
    have h0 := congrArg (fun M : QCAssertion Var (2 ^ N) ↦ (M (Function.update σ v 0)).1)
      (hB₀.2.2.2 Θ)
    have h1 := congrArg (fun M : QCAssertion Var (2 ^ N) ↦ (M (Function.update σ v 1)).1)
      (hB₁.2.2.2 Θ)
    dsimp only [restrictZeroSet_coe, S_rem] at h0 h1 ⊢
    rw [h0, h1]

/-- Outcome-dependent `1`-bit phase table `⨁_{j < b} (bit_j(m) ∧ T[idx]_j)` for Berry et al.
X-basis measurement unloading of `b` qubits. -/
def parityPhaseTable : (b : ℕ) → (ℕ → (Fin b → Bool)) → Fin (2 ^ b) → ℕ → Bool
  | 0, _, _, _ => false
  | b + 1, T, m, idx =>
      let T_lo : ℕ → (Fin b → Bool) := fun q j ↦ T q (Fin.castLE (Nat.le_succ b) j)
      let iLast : Fin (b + 1) := ⟨b, Nat.lt_succ_self b⟩
      if hm : m.val < 2 ^ b then
        parityPhaseTable b T_lo ⟨m.val, hm⟩ idx
      else
        xor (T idx iLast)
          (parityPhaseTable b T_lo
            ⟨m.val - 2 ^ b, by
              have hm2 : m.val < 2 * 2 ^ b := by simpa [pow_succ'] using m.isLt
              omega⟩
            idx)

private theorem diagPhaseUnitary_false (nIdx L : ℕ) :
    diagPhaseUnitary nIdx L (fun _ ↦ false) = 1 := by
  apply Subtype.ext
  ext i j
  by_cases hij : i = j
  · subst hij; simp [diagPhaseUnitary]
  · simp [diagPhaseUnitary, hij]

private theorem diagPhaseUnitary_xor (nIdx L : ℕ) (P₁ P₂ : ℕ → Bool) :
    diagPhaseUnitary nIdx L (fun idx ↦ xor (P₁ idx) (P₂ idx)) =
      diagPhaseUnitary nIdx L P₁ * diagPhaseUnitary nIdx L P₂ := by
  apply Subtype.ext
  simp only [diagPhaseUnitary, Submonoid.coe_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext idx
  by_cases hL : idx.val < L
  · simp only [hL, true_and]
    cases P₁ idx.val <;> cases P₂ idx.val <;> simp
  · simp [hL]

private theorem embed_diagPhaseUnitary_comm_zeroProjOn {N nIdx L : ℕ}
    (rIdx : QRegister nIdx N) (P : ℕ → Bool) (S : Finset (Wire N)) :
    (rIdx.embedUnitary (diagPhaseUnitary nIdx L P)).1 * zeroProjOn S =
      zeroProjOn S * (rIdx.embedUnitary (diagPhaseUnitary nIdx L P)).1 := by
  apply matrix_ext_ket
  intro β
  simp only [← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
  by_cases hβ : ∀ w ∈ S, β w = 0
  · rw [ite_eq_left hβ, embed_diagPhaseUnitary_mulVec_ket, Matrix.mulVec_smul,
      zeroProjOn_mulVec_ket, ite_eq_left hβ]
  · rw [ite_eq_right hβ, Matrix.mulVec_zero, embed_diagPhaseUnitary_mulVec_ket,
      Matrix.mulVec_smul, zeroProjOn_mulVec_ket, ite_eq_right hβ, smul_zero]

private theorem embed_xorLoadUnitary_zero_width {N nIdx L : ℕ}
    (rIdx : QRegister nIdx N) (rOut : QRegister 0 N) (hDisj : rIdx.DisjointWires rOut)
    (T : ℕ → (Fin 0 → Bool)) :
    (rIdx.concat rOut hDisj).embedUnitary (xorLoadUnitary nIdx 0 L T) = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_one, Matrix.one_mulVec]
  rw [embed_xorLoadUnitary_mulVec_ket]
  congr 1

private theorem embed_xorLoadUnitary_split {N nIdx W₁ W₂ W : ℕ} (L : ℕ) (hW : W₁ + W₂ = W)
    (rIdx : QRegister nIdx N) (rOut : QRegister W N) (hDisj : rIdx.DisjointWires rOut)
    (T : ℕ → (Fin W → Bool)) :
    let h₁ : 0 + W₁ ≤ W := by omega
    let h₂ : W₁ + W₂ ≤ W := by omega
    let r₁ := rOut.slice 0 W₁ h₁
    let r₂ := rOut.slice W₁ W₂ h₂
    let T₁ : ℕ → (Fin W₁ → Bool) := fun idx j ↦ T idx ⟨j.val, by omega⟩
    let T₂ : ℕ → (Fin W₂ → Bool) := fun idx j ↦ T idx ⟨W₁ + j.val, by omega⟩
    (rIdx.concat rOut hDisj).embedUnitary (xorLoadUnitary nIdx W L T) =
      ((rIdx.concat r₁ (hDisj.compose_right (QRegister.block 0 W₁ h₁))).embedUnitary
        (xorLoadUnitary nIdx W₁ L T₁)) *
      ((rIdx.concat r₂ (hDisj.compose_right (QRegister.block W₁ W₂ h₂))).embedUnitary
        (xorLoadUnitary nIdx W₂ L T₂)) := by
  intro h₁ h₂ r₁ r₂ T₁ T₂
  have hDisj₁₂ : Disjoint r₁.image r₂.image :=
    disjoint_image_of_disjointWires (rOut.slice_disjoint_of_le 0 W₁ W₁ W₂ h₁ h₂ (by omega))
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [embed_xorLoadUnitary_mulVec_ket, embed_xorLoadUnitary_mulVec_ket,
    embed_xorLoadUnitary_mulVec_ket]
  let idx := (basisBits nIdx).symm (fun i ↦ β (rIdx i))
  have hIdxEq : (basisBits nIdx).symm (fun i ↦
      xorRegBits β r₂ (fun j ↦ decide (idx.val < L ∧ T₂ idx.val j)) (rIdx i)) = idx := by
    congr 1
    funext i
    apply xorRegBits_apply_of_not_mem
    exact (hDisj.compose_right (QRegister.block W₁ W₂ h₂)).apply_not_mem_right i
  change ket (xorRegBits β rOut (fun j ↦ decide (idx.val < L ∧ T idx.val j))) =
    ket (xorRegBits (xorRegBits β r₂ (fun j ↦ decide (idx.val < L ∧ T₂ idx.val j))) r₁
      (fun j ↦ decide (((basisBits nIdx).symm (fun i ↦
        xorRegBits β r₂ (fun j ↦ decide (idx.val < L ∧ T₂ idx.val j)) (rIdx i))).val < L ∧
        T₁ ((basisBits nIdx).symm (fun i ↦
          xorRegBits β r₂ (fun j ↦ decide (idx.val < L ∧ T₂ idx.val j)) (rIdx i))).val j)))
  rw [hIdxEq]
  congr 1
  funext q
  by_cases hq : q ∈ rOut.image
  · obtain ⟨p, rfl⟩ := (QRegister.mem_image rOut q).mp hq
    by_cases hp : p.val < W₁
    · let j₁ : Fin W₁ := ⟨p.val, hp⟩
      have hr₁ : r₁ j₁ = rOut p := by
        dsimp only [r₁, j₁]
        rw [QRegister.slice_apply]
        congr 1
        exact Fin.ext (Nat.zero_add p.val)
      have hNot₂ : rOut p ∉ r₂.image :=
        hr₁ ▸ Finset.disjoint_left.mp hDisj₁₂ ((QRegister.mem_image r₁ _).mpr ⟨j₁, rfl⟩)
      rw [← hr₁, xorRegBits_apply_reg, xorRegBits_apply_of_not_mem _ r₂ _ _ (hr₁ ▸ hNot₂),
        hr₁, xorRegBits_apply_reg]
    · let j₂ : Fin W₂ := ⟨p.val - W₁, by omega⟩
      have hr₂ : r₂ j₂ = rOut p := by
        dsimp only [r₂, j₂]
        rw [QRegister.slice_apply]
        congr 1
        exact Fin.ext (by dsimp [j₂]; omega)
      have hNot₁ : rOut p ∉ r₁.image :=
        hr₂ ▸ Finset.disjoint_right.mp hDisj₁₂ ((QRegister.mem_image r₂ _).mpr ⟨j₂, rfl⟩)
      rw [xorRegBits_apply_of_not_mem _ r₁ _ _ hNot₁, ← hr₂, xorRegBits_apply_reg,
        hr₂, xorRegBits_apply_reg]
      have hjEq : (⟨W₁ + j₂.val, by omega⟩ : Fin W) = p := Fin.ext (by dsimp [j₂]; omega)
      simp only [T₂, hjEq]
  · have hNot₁ : q ∉ r₁.image := fun hm ↦ hq ((rOut.image_compose_subset _) hm)
    have hNot₂ : q ∉ r₂.image := fun hm ↦ hq ((rOut.image_compose_subset _) hm)
    rw [xorRegBits_apply_of_not_mem _ rOut _ q hq,
      xorRegBits_apply_of_not_mem _ r₁ _ q hNot₁,
      xorRegBits_apply_of_not_mem _ r₂ _ q hNot₂]

/-- Multi-wire X-basis measurement with reset (`0 T` + leaf `T`, `0 TOFF`) using a single classical
variable `v : Var`, branching on the `b`-bit measurement outcome `m : Fin (2 ^ b)` to `k m`. -/
def measureXResetAndBranch {Var : Type} {N : ℕ} (v : Var) :
    (b : ℕ) → QRegister b N → (Fin (2 ^ b) → DynamicCircuit Var N) → DynamicCircuit Var N
  | 0, _, k => k ⟨0, by simp⟩
  | b + 1, rMeas, k =>
      let iLast : Fin (b + 1) := ⟨b, Nat.lt_succ_self b⟩
      let rLo := rMeas.subregister (Fin.castLEEmb (Nat.le_succ b))
      measureXReset1AndBranch v (rMeas iLast)
        (measureXResetAndBranch v b rLo
          (fun mLo ↦ k ⟨mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩))
        (measureXResetAndBranch v b rLo
          (fun mLo ↦ k ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩))

theorem count_measureXResetAndBranch_toff {Var : Type} {N : ℕ} (v : Var)
    (b : ℕ) (rMeas : QRegister b N) (k : Fin (2 ^ b) → DynamicCircuit Var N)
    (hk : ∀ m : Fin (2 ^ b), (k m).count PrimitiveGate.TOFF = 0) :
    (measureXResetAndBranch v b rMeas k).count PrimitiveGate.TOFF = 0 := by
  induction b with
  | zero => exact hk _
  | succ b ih =>
    simp only [measureXResetAndBranch, count_measureXReset1AndBranch_toff]
    rw [ih _ _ (fun mLo ↦ hk _), ih _ _ (fun mLo ↦ hk _), max_self]

theorem count_measureXResetAndBranch_t_eq {Var : Type} {N : ℕ} (v : Var)
    (b C : ℕ) (rMeas : QRegister b N) (k : Fin (2 ^ b) → DynamicCircuit Var N)
    (hk : ∀ m : Fin (2 ^ b), (k m).count PrimitiveGate.T = C) :
    (measureXResetAndBranch v b rMeas k).count PrimitiveGate.T = C := by
  induction b with
  | zero => exact hk _
  | succ b ih =>
    simp only [measureXResetAndBranch, count_measureXReset1AndBranch_t]
    rw [ih _ _ (fun mLo ↦ hk _), ih _ _ (fun mLo ↦ hk _), max_self]

/-- Structural `O(b)` correctness proof for `measureXResetAndBranch`: if leaf `k m` realizes
`U_base * rIdx.embedUnitary (diagPhaseUnitary nIdx L (parityPhaseTable b T m))` on clean set `S`
(`rMeas.image ⊆ S`), then `measureXResetAndBranch v b rMeas k` unloads `xorLoadUnitary nIdx b L T`
into residual unitary `U_base` while leaving all of `S` clean (`|0⟩`). -/
theorem cleanUnloadsSet_measureXResetAndBranch {Var : Type} [Fintype Var] [DecidableEq Var]
    {N nIdx : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (b L : ℕ) (T : ℕ → (Fin b → Bool))
    (rIdx : QRegister nIdx N) (rMeas : QRegister b N)
    (hIdxMeas : rIdx.DisjointWires rMeas)
    (hMeasSubS : rMeas.image ⊆ S)
    (U_base : Unitary (2 ^ N))
    (k : Fin (2 ^ b) → DynamicCircuit Var N)
    (hk : ∀ m : Fin (2 ^ b),
      CleanRealizesSet v S
        (U_base * rIdx.embedUnitary (diagPhaseUnitary nIdx L (parityPhaseTable b T m)))
        (k m)) :
    CleanUnloadsSet v S rMeas.image
      ((rIdx.concat rMeas hIdxMeas).embedUnitary (xorLoadUnitary nIdx b L T))
      U_base
      (measureXResetAndBranch v b rMeas k) := by
  induction b generalizing U_base with
  | zero =>
    have hImgEmpty : rMeas.image = ∅ := by
      ext q
      simp only [Finset.notMem_empty, iff_false]
      intro hmem
      obtain ⟨j, _⟩ := (QRegister.mem_image rMeas q).mp hmem
      exact Fin.elim0 j
    have hLeaf0 := hk ⟨0, by simp⟩
    have hP0 : parityPhaseTable 0 T ⟨0, by simp⟩ = fun _ ↦ false := rfl
    rw [hP0, diagPhaseUnitary_false, QRegister.embedUnitary_one, mul_one] at hLeaf0
    rw [embed_xorLoadUnitary_zero_width rIdx rMeas hIdxMeas T, hImgEmpty]
    exact CleanUnloadsSet.of_cleanRealizesSet hLeaf0
  | succ b ih =>
    let iLast : Fin (b + 1) := ⟨b, Nat.lt_succ_self b⟩
    let w := rMeas iLast
    let emb := Fin.castLEEmb (Nat.le_succ b)
    let rLo := rMeas.subregister emb
    let T_lo : ℕ → (Fin b → Bool) := fun idx j ↦ T idx (Fin.castLE (Nat.le_succ b) j)
    let T_last : ℕ → (Fin 1 → Bool) := fun idx _ ↦ T idx iLast
    let P_last : ℕ → Bool := fun idx ↦ T idx iLast
    let D_last := rIdx.embedUnitary (diagPhaseUnitary nIdx L P_last)
    let k₀ : Fin (2 ^ b) → DynamicCircuit Var N :=
      fun mLo ↦ k ⟨mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩
    let k₁ : Fin (2 ^ b) → DynamicCircuit Var N :=
      fun mLo ↦ k ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩
    have hLoSubS : rLo.image ⊆ S := (rMeas.image_compose_subset _).trans hMeasSubS
    have hwS : w ∈ S := hMeasSubS ((QRegister.mem_image rMeas w).mpr ⟨iLast, rfl⟩)
    have hwNotLo : w ∉ rLo.image := by
      intro hmem
      obtain ⟨j, hj⟩ := (QRegister.mem_image rLo w).mp hmem
      have hEq : Fin.castLE (Nat.le_succ b) j = iLast := rMeas.wires.injective hj
      have := congrArg Fin.val hEq
      exact Nat.ne_of_lt j.isLt this
    have hImgEq : insert w rLo.image = rMeas.image := by
      ext q
      constructor
      · intro hmem
        rcases Finset.mem_insert.mp hmem with rfl | hLo
        · exact (QRegister.mem_image rMeas w).mpr ⟨iLast, rfl⟩
        · exact (rMeas.image_compose_subset _) hLo
      · intro hmem
        obtain ⟨j, rfl⟩ := (QRegister.mem_image rMeas q).mp hmem
        by_cases hj : j.val < b
        · exact Finset.mem_insert_of_mem
            ((QRegister.mem_image rLo _).mpr ⟨⟨j.val, hj⟩, congrArg rMeas (Fin.ext rfl)⟩)
        · have hjEq : j = iLast := Fin.ext (by dsimp [iLast]; omega)
          subst hjEq
          exact Finset.mem_insert_self w rLo.image
    have hIdxLo : rIdx.DisjointWires rLo := hIdxMeas.compose_right ⟨emb⟩
    have hIdxSing : rIdx.DisjointWires (QRegister.singleton w) := by
      rw [QRegister.disjoint_iff]
      intro i j
      fin_cases j
      exact hIdxMeas.ne i iLast
    have hk₀ : ∀ mLo : Fin (2 ^ b),
        CleanRealizesSet v S
          (U_base * rIdx.embedUnitary (diagPhaseUnitary nIdx L (parityPhaseTable b T_lo mLo)))
          (k₀ mLo) := by
      intro mLo
      have hPar : parityPhaseTable (b + 1) T
          ⟨mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩ =
          parityPhaseTable b T_lo mLo := by
        funext idx
        dsimp only [parityPhaseTable]
        exact dite_eq_left mLo.isLt
      simpa only [k₀, hPar] using hk ⟨mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩
    have hk₁ : ∀ mLo : Fin (2 ^ b),
        CleanRealizesSet v S
          ((U_base * D_last) *
            rIdx.embedUnitary (diagPhaseUnitary nIdx L (parityPhaseTable b T_lo mLo)))
          (k₁ mLo) := by
      intro mLo
      have hNotLt : ¬(2 ^ b + mLo.val < 2 ^ b) := by omega
      have hSub : 2 ^ b + mLo.val - 2 ^ b = mLo.val := by omega
      have hPar : parityPhaseTable (b + 1) T
          ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩ =
          fun idx ↦ xor (P_last idx) (parityPhaseTable b T_lo mLo idx) := by
        funext idx
        dsimp only [parityPhaseTable]
        rw [dite_eq_right hNotLt]
        have hFinEq : (⟨2 ^ b + mLo.val - 2 ^ b, by
            have hm2 : 2 ^ b + mLo.val < 2 * 2 ^ b := by have := mLo.isLt; omega
            omega⟩ : Fin (2 ^ b)) = mLo := Fin.ext hSub
        rw [hFinEq]
      have hLeaf := hk ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩
      rw [hPar, diagPhaseUnitary_xor, QRegister.embedUnitary_mul, ← mul_assoc] at hLeaf
      exact hLeaf
    have hB₀ := ih T_lo rLo hIdxLo hLoSubS U_base k₀ hk₀
    have hB₁ := ih T_lo rLo hIdxLo hLoSubS (U_base * D_last) k₁ hk₁
    let W_lo := (rIdx.concat rLo hIdxLo).embedUnitary (xorLoadUnitary nIdx b L T_lo)
    let W_w := (rIdx.concat (QRegister.singleton w) hIdxSing).embedUnitary
      (xorLoadUnitary nIdx 1 L T_last)
    have hStep := CleanUnloadsSet.measureXReset1 (W_w := W_w) hwS hwNotLo hB₀ hB₁
      (bitFn := fun β ↦ decide (((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
        P_last ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val))
      (g := fun β ↦ xorRegBits β rLo (fun j ↦
        decide (((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
          T_lo ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val j)))
      (fun β ↦ embed_xorLoadUnitary_mulVec_ket rIdx rLo hIdxLo T_lo β)
      (fun β ↦ xorRegBits_apply_of_not_mem β rLo _ w hwNotLo)
      (fun β val ↦ by
        have hIdxUpd : (basisBits nIdx).symm (fun i ↦ Function.update β w val (rIdx i)) =
            (basisBits nIdx).symm (fun i ↦ β (rIdx i)) := by
          congr 1
          funext i
          exact Function.update_of_ne (hIdxMeas.ne i iLast) val β
        rw [hIdxUpd]
        funext x
        by_cases hx : x = w
        · subst hx
          rw [xorRegBits_apply_of_not_mem _ rLo _ _ hwNotLo, Function.update_self,
            Function.update_self]
        · by_cases hxLo : x ∈ rLo.image
          · obtain ⟨j, rfl⟩ := (QRegister.mem_image rLo x).mp hxLo
            rw [xorRegBits_apply_reg, Function.update_of_ne hx, Function.update_of_ne hx,
              xorRegBits_apply_reg]
          · rw [xorRegBits_apply_of_not_mem _ rLo _ _ hxLo, Function.update_of_ne hx,
              Function.update_of_ne hx, xorRegBits_apply_of_not_mem _ rLo _ _ hxLo])
      (fun β ↦ by
        dsimp only [W_w]
        rw [embed_xorLoadUnitary_mulVec_ket]
        congr 1
        funext x
        by_cases hx : x = w
        · subst hx
          change xorRegBits β (QRegister.singleton w) _ (QRegister.singleton w 0) = _
          rw [xorRegBits_apply_reg, QRegister.singleton_apply, Function.update_self]
        · have hxNot : x ∉ (QRegister.singleton w).image := by simp [hx]
          rw [xorRegBits_apply_of_not_mem _ _ _ x hxNot, Function.update_of_ne hx])
      (fun β _ ↦ by
        dsimp only [D_last]
        rw [embed_diagPhaseUnitary_mulVec_ket]
        congr 1
        by_cases hcond : ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
            P_last ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val <;> simp [hcond])
      (by
        dsimp only [D_last]
        rw [← QRegister.embedUnitary_mul, diagPhaseUnitary_mul_self, QRegister.embedUnitary_one])
      (embed_diagPhaseUnitary_comm_zeroProjOn rIdx P_last S)
    rw [hImgEq] at hStep
    have hSplit := embed_xorLoadUnitary_split L (rfl : b + 1 = b + 1)
      rIdx rMeas hIdxMeas T
    dsimp only at hSplit
    have hr₁Eq : rMeas.slice 0 b (by omega) = rLo := by
      ext j
      exact congrArg Fin.val (congrArg rMeas (Fin.ext (Nat.zero_add j.val)))
    have hr₂Eq : rMeas.slice b 1 (by omega) = QRegister.singleton w := by
      ext j
      fin_cases j
      exact congrArg Fin.val (congrArg rMeas (Fin.ext (Nat.add_zero b)))
    refine hStep.congr_load ?_
    intro β _
    rw [hSplit]
    simp only [W_w, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      embed_xorLoadUnitary_mulVec_ket]
    have hIdx1 : (basisBits nIdx).symm (fun i ↦
        xorRegBits β (QRegister.singleton w) (fun j ↦
          decide (((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
            T_last ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val j)) (rIdx i)) =
        (basisBits nIdx).symm (fun i ↦ β (rIdx i)) := by
      congr 1
      funext i
      exact xorRegBits_apply_of_not_mem _ _ _ _ (hIdxSing.apply_not_mem_right i)
    have hIdx2 : (basisBits nIdx).symm (fun i ↦
        xorRegBits β (rMeas.slice b 1 (by omega)) (fun j ↦
          decide (((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
            T ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val ⟨b + j.val, by omega⟩))
          (rIdx i)) =
        (basisBits nIdx).symm (fun i ↦ β (rIdx i)) := by
      congr 1
      funext i
      exact xorRegBits_apply_of_not_mem _ _ _ _
        ((hIdxMeas.compose_right (QRegister.block b 1 (by omega))).apply_not_mem_right i)
    rw [hIdx1, hIdx2]
    congr 1
    have hInnerEq :
        xorRegBits β (QRegister.singleton w) (fun j ↦
          decide (((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
            T_last ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val j)) =
        xorRegBits β (rMeas.slice b 1 (by omega)) (fun j ↦
          decide (((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val < L ∧
            T ((basisBits nIdx).symm (fun i ↦ β (rIdx i))).val ⟨b + j.val, by omega⟩)) := by
      rw [hr₂Eq]
      congr 1
      funext j
      fin_cases j
      have hiEq : (⟨b + 0, by omega⟩ : Fin (b + 1)) = iLast := Fin.ext (Nat.add_zero b)
      dsimp only [T_last]
      rw [hiEq]
    rw [hInnerEq, hr₁Eq]
    rfl

attribute [irreducible] measureXResetAndBranch

/-!
### Single-Shot and Chunked `0-T` X-Measurement QROM Unload
-/

/-!
### SelectSwap Sandwich (`selectSwapSandwichDyn`) and Clean Load (`selectSwapCleanLoadDyn`)
-/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
