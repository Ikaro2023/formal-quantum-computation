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

public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.Circuits.Toffoli
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs

/-!
# Asymmetric `4*(L-1) T` One-Hot Unary Iteration & `16`-Bit QPE Step-Equality Controller

Implements measurement-uncomputed unary-iteration primitives for `P450GroundEnergy` with `0`
primitive `TOFF` gates:
- `withUnaryOneHotDyn` and `withUnaryOneHotEnabledDyn`: Babbush et al. (Phys. Rev. X 8, 041015,
  2018) in-place binary-splitting one-hot range decoder computing `hot[i] = [idx == i]` (`idx < L`)
  in `4 * (L - 1)` `T` gates (`L - 1` `DynamicCircuit.andCompute` gadgets, `0` extra tree scratch
  wires) and uncomputing `rHot` cleanly back to `|0^L⟩` in `0` `T` gates via
  `DynamicCircuit.andUncompute`.
- Group-factored DFTHC (`L = 9`, `L = 29`, `9 × 29`), one-body (`L = 58`), `SelectSwap` (`L = 80`),
  and full `319`-row address decoders with exact `T`-gate counts and `CleanRealizes` contracts.
- `unaryRangeLoopDyn` and `qpeUnaryStepLoopDyn`: streaming binary-tree unary-iteration controller
  maintaining a clean step-equality wire `eq_j = [m == j]` across `j = 1 .. M` on `16`-bit `m` at
  amortized `4 T` per step and returning all `16` tree ancillas cleanly to `|0^16⟩`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

namespace GroupUnary

open Operator Matrix QProg HermitianMat Circuit
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

local instance instNeZeroTwoPowLocal (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-!
## Part 1: Clean-Subspace Weakest-Precondition Engine & `CleanRealizes`
-/

/-- Clean-ancilla `wp`-equality contract matching `CleanDyn.CleanRealizes` and
`CleanDyn.CleanRealizes` definitionally (`rfl`). -/
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

/-- Computational-basis ket `|β⟩` in `ℂ^(2^N)`. -/
noncomputable abbrev ket {N : ℕ} (β : BitAssignment N) : Fin (2 ^ N) → ℂ :=
  basisState ((basisBits N).symm β)

private theorem basisBits_symm_ket {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

private theorem symm_basisBits {q : ℕ} (g : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q g) = g :=
  (basisBits q).symm_apply_apply g

/-- Overwrite the bits of `β` on register `r` with `γ`, leaving all other wires unchanged. -/
noncomputable def writeReg {k N : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) : BitAssignment N :=
  basisBits N (r.replaceIndex ((basisBits N).symm β) ((basisBits k).symm γ))

@[simp]
theorem writeReg_apply_reg {k N : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

theorem writeReg_apply_of_not_mem {k N : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (w : Wire N) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

private theorem writeReg_eq_update {k N : ℕ} (β : BitAssignment N) (r : QRegister k N)
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

private theorem embedMatrix_mulVec_ket {k N : ℕ} (r : QRegister k N)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment N) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k),
        A l ((basisBits k).symm (fun i ↦ β (r i))) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits N).symm β) =
      (basisBits k).symm (fun i ↦ β (r i)) := by
    dsimp [QRegister.extractIndex]
    congr 1; funext i
    exact congrFun (basisBits_symm_ket β) (r i)
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

private theorem embedMatrix_permMatrix_mulVec_ket {k N : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment N) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
      ket (writeReg β r (basisBits k (σ.symm ((basisBits k).symm (fun i ↦ β (r i)))))) := by
  rw [embedMatrix_mulVec_ket,
    Finset.sum_eq_single (σ.symm ((basisBits k).symm (fun i ↦ β (r i))))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ (basisBits k).symm (fun i ↦ β (r i)) :=
      fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

private theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

private theorem add_self_zmod2 (b : ZMod 2) : b + b = 0 := by
  rcases bit_cases b with rfl | rfl <;> rfl

private theorem ket_X {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [embedMatrix_mulVec_ket]
  have hloc : ((basisBits 1).symm (fun _ ↦ β ((QRegister.singleton q) 0)) : Fin 2) =
      if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  have hfun : (fun i : Fin 1 ↦ β ((QRegister.singleton q) i)) =
      (fun _ ↦ β ((QRegister.singleton q) 0)) := funext fun _ ↦ rfl
  rw [hfun, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]

private theorem ket_CNOT {N : ℕ} (c t : Wire N) (h : c ≠ t) (β : BitAssignment N) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [hloc, writeReg_eq_update _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi

private theorem ket_TOFF {N : ℕ} (c₁ c₂ t : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment N) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      ket (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBits 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [hloc, writeReg_eq_update _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi

/-- Orthogonal projector onto computational-basis states satisfying `S`. -/
noncomputable def predProj {N : ℕ} (S : BitAssignment N → Bool) : Operator (2 ^ N) :=
  Matrix.diagonal fun i : Fin (2 ^ N) ↦ if S (basisBits N i) then (1 : ℂ) else 0

theorem predProj_conjTranspose {N : ℕ} (S : BitAssignment N → Bool) :
    (predProj S)ᴴ = predProj S := by
  ext i j
  simp only [predProj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : j = i
  · subst hij
    by_cases hS : S (basisBits N j) = true <;> simp [hS]
  · have hji : i ≠ j := Ne.symm hij
    simp [hij, hji]

theorem predProj_mul {N : ℕ} (S₁ S₂ : BitAssignment N → Bool) :
    predProj S₁ * predProj S₂ = predProj (fun β ↦ S₁ β && S₂ β) := by
  dsimp [predProj]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h₁ : S₁ (basisBits N i) = true <;>
    by_cases h₂ : S₂ (basisBits N i) = true <;>
    simp [h₁, h₂]

theorem predProj_idem {N : ℕ} (S : BitAssignment N → Bool) :
    predProj S * predProj S = predProj S := by
  rw [predProj_mul]
  simp

theorem predProj_comm {N : ℕ} (S₁ S₂ : BitAssignment N → Bool) :
    predProj S₁ * predProj S₂ = predProj S₂ * predProj S₁ := by
  rw [predProj_mul, predProj_mul]
  congr 1
  funext β
  exact Bool.and_comm (S₁ β) (S₂ β)

theorem one_sub_predProj {N : ℕ} (S : BitAssignment N → Bool) :
    1 - predProj S = predProj (fun β ↦ !S β) := by
  ext i j
  simp only [predProj, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hS : S (basisBits N i) = true <;> simp [hS]
  · simp [hij]

theorem predProj_conj_le_one {N : ℕ} (S : BitAssignment N → Bool) :
    HermitianMat.conj (predProj S) (1 : HermitianMat (Fin (2 ^ N)) ℂ) ≤ 1 := by
  have hsum :
      HermitianMat.conj (predProj S) (1 : HermitianMat (Fin (2 ^ N)) ℂ) +
        HermitianMat.conj (predProj (fun β ↦ !S β)) (1 : HermitianMat (Fin (2 ^ N)) ℂ) = 1 := by
    apply Subtype.ext
    change (predProj S * 1 * (predProj S)ᴴ) +
      (predProj (fun β ↦ !S β) * 1 * (predProj (fun β ↦ !S β))ᴴ) = 1
    rw [Matrix.mul_one, Matrix.mul_one, predProj_conjTranspose, predProj_conjTranspose,
      predProj_idem, predProj_idem, ← one_sub_predProj, add_sub_cancel]
  have hnonneg :
      0 ≤ HermitianMat.conj (predProj (fun β ↦ !S β)) (1 : HermitianMat (Fin (2 ^ N)) ℂ) :=
    HermitianMat.conj_nonneg (predProj (fun β ↦ !S β)) zero_le_one
  exact le_of_add_le_of_nonneg_left hsum.le hnonneg

/-- Restrict an assertion branchwise onto the computational-basis subspace `S`. -/
noncomputable def restrictPred {Var : Type} [Fintype Var] {N : ℕ}
    (S : BitAssignment N → Bool) (Θ : QCAssertion Var (2 ^ N)) : QCAssertion Var (2 ^ N) :=
  fun σ ↦ ⟨(Θ σ).1.conj (predProj S),
    ⟨(Θ σ).1.conj_nonneg (predProj S) (Θ σ).2.1,
      (HermitianMat.conj_mono (Θ σ).2.2).trans (predProj_conj_le_one S)⟩⟩

@[simp]
theorem restrictPred_coe {Var : Type} [Fintype Var] {N : ℕ}
    (S : BitAssignment N → Bool) (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    (restrictPred S Θ σ).1 = (Θ σ).1.conj (predProj S) := rfl

/-- Store-independent observable projecting onto computational-basis states satisfying `S`. -/
noncomputable def constPredObs {Var : Type} [Fintype Var] {N : ℕ}
    (S : BitAssignment N → Bool) : QCAssertion Var (2 ^ N) :=
  restrictPred S (fun _ ↦ 1)

/-!
### Wire-Basis Preservation & Commutation with Computational-Basis Projectors
-/

/-!
### Finite-Kraus Decomposition & Projector Absorption on `DynamicCircuit`
-/

private noncomputable def krausBranches {Var : Type} [DecidableEq Var] {N : ℕ} :
    DynamicCircuit Var N → Store Var → List (Operator (2 ^ N) × Store Var) :=
  DynamicCircuit.qcRec
    (fun c σ ↦ [(c.eval.1, σ)])
    (fun v r σ ↦
      [(r.basisOutcomeProjector 0, Function.update σ v 0),
       (r.basisOutcomeProjector 1, Function.update σ v 1)])
    (fun cond _ _ iht ihf σ ↦ if cond.holds σ then iht σ else ihf σ)
    (fun _ _ ih₁ ih₂ σ ↦
      (ih₁ σ).flatMap fun b₁ ↦
        (ih₂ b₁.2).map fun b₂ ↦ (b₂.1 * b₁.1, b₂.2))

@[simp]
private theorem krausBranches_circuit {Var : Type} [DecidableEq Var] {N : ℕ}
    (c : Circuit N) (σ : Store Var) :
    krausBranches (.circuit c) σ = [(c.eval.1, σ)] := rfl

@[simp]
private theorem krausBranches_measure {Var : Type} [DecidableEq Var] {N : ℕ}
    (v : Var) (r : QRegister 1 N) (σ : Store Var) :
    krausBranches (.measure v r) σ =
      [(r.basisOutcomeProjector 0, Function.update σ v 0),
       (r.basisOutcomeProjector 1, Function.update σ v 1)] := rfl

@[simp]
private theorem krausBranches_qIf {Var : Type} [DecidableEq Var] {N : ℕ}
    (cond : QCRawGuard Var) (t f : DynamicCircuit Var N) (σ : Store Var) :
    krausBranches (DynamicCircuit.qcRawQIf cond t f) σ =
      if cond.holds σ then krausBranches t σ else krausBranches f σ := rfl

@[simp]
private theorem krausBranches_seq {Var : Type} [DecidableEq Var] {N : ℕ}
    (p₁ p₂ : DynamicCircuit Var N) (σ : Store Var) :
    krausBranches (.seq p₁ p₂) σ =
      (krausBranches p₁ σ).flatMap fun b₁ ↦
        (krausBranches p₂ b₁.2).map fun b₂ ↦ (b₂.1 * b₁.1, b₂.2) := rfl

private theorem conj_list_sum {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (xs : List (HermitianMat (Fin d) ℂ)) :
    xs.sum.conj B = (xs.map fun x ↦ x.conj B).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [map_add, ih]

private theorem list_sum_flatMap {α β : Type*} [AddCommMonoid β]
    (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem wp_compile_eq_krausBranches {Var : Type} [Finite Var] [DecidableEq Var] {N : ℕ}
    (P : DynamicCircuit Var N) (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    (wp P.compile Θ σ).1 =
      ((krausBranches P σ).map fun b ↦ (Θ b.2).1.conj b.1ᴴ).sum := by
  cases nonempty_fintype Var
  induction P using DynamicCircuit.qcInd generalizing Θ σ with
  | circuit c =>
      simp [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose]
  | measure v r =>
      have hsubst0 : σ.subst v 0 = Function.update σ v 0 := by
        funext y; simp [Store.subst, Function.update]
      have hsubst1 : σ.subst v 1 = Function.update σ v 1 := by
        funext y; simp [Store.subst, Function.update]
      simp only [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
        qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe, QCAssertion.subst_apply]
      change ∑ o : Fin 2, _ = _
      rw [Fin.sum_univ_two]
      simp [qc_qMeasure_outcome_herm_eq_conj, hsubst0, hsubst1,
        QRegister.computationalBasisMeasurement_apply]
  | qIf cond t f iht ihf =>
      simp only [DynamicCircuit.compile_qcRawQIf, wp_qcRawQIf, krausBranches_qIf]
      by_cases hc : cond.holds σ <;> simp [hc, iht Θ σ, ihf Θ σ]
    | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.compile_seq, wp_qSeq, krausBranches_seq, List.map_flatMap,
        list_sum_flatMap]
      rw [ih₁ (wp p₂.compile Θ) σ]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨K₁, σ₁⟩ _
      rw [ih₂ Θ σ₁, conj_list_sum]
      simp only [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨K₂, σ₂⟩ _
      simp [Function.comp, conj_conj, conjTranspose_mul]

private theorem list_sum_nonneg {d : ℕ} {xs : List (HermitianMat (Fin d) ℂ)}
    (hpos : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.sum_cons]
      exact add_nonneg (hpos x (List.mem_cons_self ..))
        (ih fun y hy ↦ hpos y (List.mem_cons_of_mem _ hy))

private theorem list_map_sum_eq_zero_of_nonneg {α : Type*} {d : ℕ}
    (l : List α) (f : α → HermitianMat (Fin d) ℂ)
    (hpos : ∀ a ∈ l, 0 ≤ f a) (hsum : (l.map f).sum = 0) :
    ∀ a ∈ l, f a = 0 := by
  induction l with
  | nil => intro _ hx; cases hx
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons] at hsum
      have ha_nonneg : 0 ≤ f a := hpos a (List.mem_cons_self ..)
      have hl_nonneg : 0 ≤ (l.map f).sum :=
        list_sum_nonneg fun y hy ↦ by
          rcases List.mem_map.mp hy with ⟨b, hb, rfl⟩
          exact hpos b (List.mem_cons_of_mem _ hb)
      have ha0 : f a = 0 := le_antisymm (le_of_add_le_of_nonneg_left hsum.le hl_nonneg) ha_nonneg
      have hl0 : (l.map f).sum = 0 := by simpa [ha0] using hsum
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact ha0
      · exact ih (fun b hb ↦ hpos b (List.mem_cons_of_mem _ hb)) hl0 z hz'

private theorem matrix_eq_zero_of_conjTranspose_mul_self {d : ℕ}
    {B : Matrix (Fin d) (Fin d) ℂ} (h : Bᴴ * B = 0) : B = 0 := by
  ext i j
  have hdiag : ((Bᴴ * B) j j).re = 0 := by rw [h]; simp
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum] at hdiag
  have hterm (k : Fin d) : (star (B k j) * B k j).re = Complex.normSq (B k j) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  simp only [hterm] at hdiag
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ Complex.normSq_nonneg (B k j)).mp hdiag
  exact Complex.normSq_eq_zero.mp (hall i (Finset.mem_univ i))

/-- Finite-Kraus projector absorption: if a dynamic circuit `P` starting on `S_in` has zero
amplitude of landing outside `S_out` (`wp P.compile (1 - S_out) = 0` on `S_in`), then restricting
any postcondition `Θ` (even store-dependent) to `S_out` leaves `wp P.compile` on `S_in`
unchanged. -/
theorem wp_restrictPred_of_wp_compl_eq_zero {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (P : DynamicCircuit Var N) (S_in S_out : BitAssignment N → Bool)
    (hzero : ∀ σ, (restrictPred S_in (wp P.compile (constPredObs (fun β ↦ !S_out β))) σ).1 = 0)
    (Θ : QCAssertion Var (2 ^ N)) :
    restrictPred S_in (wp P.compile (restrictPred S_out Θ)) =
      restrictPred S_in (wp P.compile Θ) := by
  funext σ
  apply Subtype.ext
  rw [restrictPred_coe, restrictPred_coe, wp_compile_eq_krausBranches, wp_compile_eq_krausBranches,
    conj_list_sum, conj_list_sum, List.map_map, List.map_map]
  have hz := hzero σ
  rw [restrictPred_coe, wp_compile_eq_krausBranches, conj_list_sum, List.map_map] at hz
  have hmem_zero := list_map_sum_eq_zero_of_nonneg (krausBranches P σ) _
    (fun b _ ↦ HermitianMat.conj_nonneg _
      (HermitianMat.conj_nonneg _ (constPredObs (fun β ↦ !S_out β) b.2).2.1))
    hz
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨K, σ'⟩ hb
  have hb0 : (((constPredObs (fun β ↦ !S_out β) σ').1.conj Kᴴ).conj (predProj S_in)) = 0 :=
    hmem_zero (K, σ') hb
  have hmat : ((predProj (fun β ↦ !S_out β)) * K * predProj S_in)ᴴ *
      ((predProj (fun β ↦ !S_out β)) * K * predProj S_in) = 0 := by
    have h1 := congrArg HermitianMat.mat hb0
    simp only [constPredObs, restrictPred_coe, Observable.coe_one, HermitianMat.conj_apply_mat,
      HermitianMat.mat_one, HermitianMat.mat_zero, Matrix.mul_one] at h1
    calc ((predProj (fun β ↦ !S_out β)) * K * predProj S_in)ᴴ *
          ((predProj (fun β ↦ !S_out β)) * K * predProj S_in)
        = predProj S_in * (Kᴴ * (predProj (fun β ↦ !S_out β) *
            (predProj (fun β ↦ !S_out β))ᴴ) * K) * (predProj S_in)ᴴ := by
          simp [conjTranspose_mul, predProj_conjTranspose, Matrix.mul_assoc]
      _ = 0 := by simpa [predProj_conjTranspose, Matrix.mul_assoc] using h1
  have hB0 : (predProj (fun β ↦ !S_out β)) * K * predProj S_in = 0 :=
    matrix_eq_zero_of_conjTranspose_mul_self hmat
  have hK : predProj S_out * K * predProj S_in = K * predProj S_in := by
    rw [← one_sub_predProj, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, sub_eq_zero] at hB0
    exact hB0.symm
  have hK_adj : predProj S_in * (Kᴴ * predProj S_out) = predProj S_in * Kᴴ := by
    have h' := congrArg conjTranspose hK
    simpa [conjTranspose_mul, predProj_conjTranspose, Matrix.mul_assoc] using h'
  simp only [Function.comp, restrictPred_coe, conj_conj]
  exact congrArg (fun X ↦ (Θ σ').1.conj X) hK_adj

/-!
### Composable Subspace Realization (`SubspaceRealizes`)
-/

/-!
### Bridging `CleanRealizes` <-> `SubspaceRealizes` & Extracting Clean Suffix Unitaries
-/

/-- Reversible classical circuit AST whose `andGate` nodes compile to `4 T` `andCompute` in the
forward direction and `0 T` measurement-based `andUncompute` in the reverse direction. -/
inductive RevCompute (N : ℕ) : Type
  | id : RevCompute N
  | x (q : Wire N) : RevCompute N
  | cnot (c t : Wire N) (h : c ≠ t) : RevCompute N
  | andGate (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : RevCompute N
  | seq (p₁ p₂ : RevCompute N) : RevCompute N

namespace RevCompute

/-- Equivalent unitary reference `Circuit N` using ideal `TOFF` for `andGate`. -/
def toCircuit {N : ℕ} : RevCompute N → Circuit N
  | .id => .identity
  | .x q => .X q
  | .cnot c t h => .CNOT c t h
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a => .TOFF c₁ c₂ anc h₁₂ h₁a h₂a
  | .seq p₁ p₂ => .seq p₁.toCircuit p₂.toCircuit

/-- Number of `andGate` nodes in `p` (each contributes `4 T` in `wrapDyn`). -/
def numAnd {N : ℕ} : RevCompute N → ℕ
  | .id => 0
  | .x _ => 0
  | .cnot _ _ _ => 0
  | .andGate _ _ _ _ _ _ => 1
  | .seq p₁ p₂ => p₁.numAnd + p₂.numAnd

/-- Forward computational-basis bit transformation of `p`. -/
def fwdBits {N : ℕ} : RevCompute N → BitAssignment N → BitAssignment N
  | .id, β => β
  | .x q, β => Function.update β q (β q + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .andGate c₁ c₂ anc _ _ _, β => Function.update β anc (β anc + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.fwdBits (p₁.fwdBits β)

/-- Inverse computational-basis bit transformation of `p`. -/
def invBits {N : ℕ} : RevCompute N → BitAssignment N → BitAssignment N
  | .id, β => β
  | .x q, β => Function.update β q (β q + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .andGate c₁ c₂ anc _ _ _, β => Function.update β anc (β anc + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₁.invBits (p₂.invBits β)

/-- Clean-target precondition ensuring every `andGate` writes into a `|0⟩` ancilla. -/
def validOn {N : ℕ} : RevCompute N → BitAssignment N → Bool
  | .id, _ => true
  | .x _, _ => true
  | .cnot _ _ _, _ => true
  | .andGate _ _ anc _ _ _, β => β anc == 0
  | .seq p₁ p₂, β => p₁.validOn β && p₂.validOn (p₁.fwdBits β)

/-- Syntactic wire-containment predicate for `p`. -/
def UsesOnly {N : ℕ} (W : Set (Wire N)) : RevCompute N → Prop
  | .id => True
  | .x q => q ∈ W
  | .cnot c t _ => c ∈ W ∧ t ∈ W
  | .andGate c₁ c₂ anc _ _ _ => c₁ ∈ W ∧ c₂ ∈ W ∧ anc ∈ W
  | .seq p₁ p₂ => p₁.UsesOnly W ∧ p₂.UsesOnly W

@[simp]
theorem invBits_fwdBits {N : ℕ} (p : RevCompute N) (β : BitAssignment N) :
    p.invBits (p.fwdBits β) = β := by
  induction p generalizing β with
  | id => rfl
  | x q =>
      simp [fwdBits, invBits, Function.update_self, Function.update_idem,
        add_assoc, one_add_one_zmod2, Function.update_eq_self]
  | cnot c t h =>
      simp [fwdBits, invBits, Function.update_self, Function.update_of_ne h, Function.update_idem,
        add_assoc, add_self_zmod2, Function.update_eq_self]
  | andGate c₁ c₂ anc _ h₁a h₂a =>
      simp [fwdBits, invBits, Function.update_self, Function.update_of_ne h₁a,
        Function.update_of_ne h₂a, Function.update_idem, add_assoc, add_self_zmod2,
        Function.update_eq_self]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp [fwdBits, invBits, ih₂, ih₁]

@[simp]
theorem fwdBits_invBits {N : ℕ} (p : RevCompute N) (β : BitAssignment N) :
    p.fwdBits (p.invBits β) = β := by
  induction p generalizing β with
  | id => rfl
  | x q =>
      simp [fwdBits, invBits, Function.update_self, Function.update_idem,
        add_assoc, one_add_one_zmod2, Function.update_eq_self]
  | cnot c t h =>
      simp [fwdBits, invBits, Function.update_self, Function.update_of_ne h, Function.update_idem,
        add_assoc, add_self_zmod2, Function.update_eq_self]
  | andGate c₁ c₂ anc _ h₁a h₂a =>
      simp [fwdBits, invBits, Function.update_self, Function.update_of_ne h₁a,
        Function.update_of_ne h₂a, Function.update_idem, add_assoc, add_self_zmod2,
        Function.update_eq_self]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp [fwdBits, invBits, ih₁, ih₂]

theorem toCircuit_mulVec_ket {N : ℕ} (p : RevCompute N) (β : BitAssignment N) :
    p.toCircuit.eval.1.mulVec (ket β) = ket (p.fwdBits β) := by
  induction p generalizing β with
  | id =>
      dsimp [toCircuit, fwdBits]
      exact Matrix.one_mulVec _
  | x q => simpa [toCircuit, fwdBits] using ket_X q β
  | cnot c t h => simpa [toCircuit, fwdBits] using ket_CNOT c t h β
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      simpa [toCircuit, fwdBits] using ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ih₁, ih₂, fwdBits]

end RevCompute

/-!
### In-Place Binary-Splitting One-Hot Range Decoder (`oneHotProg` / `withUnaryOneHotDyn`)
-/

end GroupUnary

export GroupUnary (RevCompute)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
