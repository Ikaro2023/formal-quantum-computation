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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs

/-!
# Minimum-`T` Unsigned Comparators, Controlled Register Swaps, and Zero-Reflections

Self-contained `TOFF = 0` dynamic circuit primitives for `P450GroundEnergy` over `PrimitiveGate`:
1. Compositional clean-ancilla weakest-precondition SDK (`CleanRealizes`, `andSandwich`) supporting
   nested temporary-AND compute/uncompute sandwiches (`4` `T` compute, `0` `T` uncompute) around
   arbitrary `DynamicCircuit` bodies.
2. `w`-bit controlled register swap (`cswapRegDyn`) using `4 * w` `T` gates, `0` `TOFF` gates,
   and a single reusable clean ancilla wire.
3. Multi-qubit zero-state reflection `2|0^k⟩⟨0^k| - I` (`reflectZeroDyn`, `4 * (k - 2)` `T` gates)
   and single-wire-controlled zero-state reflection (`ctrlReflectZeroDyn`, `4 * (k - 1)` `T` gates).
4. Asymmetric `4 * w` `T` compute / `0` `T` uncompute unsigned `<` comparators (`ltComparatorDyn`,
   `withLtComparatorDyn`, `ltConstDyn`, `withLtConstFlagDyn`, `eqConstDyn`, `withEqConstFlagDyn`),
   plus the paired even-step QPE reflection controller (`withCenteredAbsDiffGtConstFlagDyn`,
   `4 * k` `T` per step-pair = `30` `T`/step at `16`-bit QPE).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! ## 1. Clean-Ancilla `wp` Equality Contract & Wire-Set Temporary-AND SDK -/

/-- Exact clean-ancilla `wp` realization contract shared across `P450GroundEnergy` modules. -/
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

/-- Temporary-AND compute/body/uncompute sandwich (`4` `T` compute, `0` `T` uncompute). -/
def andSandwich {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (mid : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
    (.seq mid (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))

@[simp]
theorem count_andSandwich_toff {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (mid : DynamicCircuit Var N) :
    (andSandwich v c₁ c₂ anc h₁₂ h₁a h₂a mid).count PrimitiveGate.TOFF =
      mid.count PrimitiveGate.TOFF := by
  simp [andSandwich]

@[simp]
theorem count_andSandwich_t {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (mid : DynamicCircuit Var N) :
    (andSandwich v c₁ c₂ anc h₁₂ h₁a h₂a mid).count PrimitiveGate.T =
      4 + mid.count PrimitiveGate.T := by
  simp [andSandwich]

@[simp]
theorem support_andSandwich {Var : Type} {N : ℕ} (v : Var) (c₁ c₂ anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (mid : DynamicCircuit Var N) :
    (andSandwich v c₁ c₂ anc h₁₂ h₁a h₂a mid).support = {c₁, c₂, anc} ∪ mid.support := by
  ext q
  simp only [andSandwich, DynamicCircuit.support_seq, DynamicCircuit.support_andCompute,
    DynamicCircuit.support_andUncompute, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

section KetAndProjectors

variable {N : ℕ}

/-- Computational-basis ket indexed by a bit assignment `β : BitAssignment N`. -/
noncomputable abbrev ket (β : BitAssignment N) : Fin (2 ^ N) → ℂ :=
  basisState ((basisBits N).symm β)

theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem single_eq_ket (g : Fin (2 ^ N)) :
    (Pi.single g 1 : Fin (2 ^ N) → ℂ) = ket (basisBits N g) := by
  simp [ket, basisState]

theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ}
    (h : ∀ β : BitAssignment N, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits N j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

/-- Overwrite the bits of register `r` in global bit assignment `β` with `γ`. -/
noncomputable def writeReg {k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) : BitAssignment N :=
  basisBits N (r.replaceIndex ((basisBits N).symm β) ((basisBits k).symm γ))

@[simp]
theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

theorem writeReg_apply_of_not_mem {k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (w : Wire N) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

theorem writeReg_eq_update {k : ℕ} (β : BitAssignment N) (r : QRegister k N)
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

/-- Local computational-basis index on `Fin (2 ^ k)` extracted from `β` along `r`. -/
noncomputable abbrev localIdx {k : ℕ} (r : QRegister k N) (β : BitAssignment N) :
    Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

theorem embedMatrix_mulVec_ket {k : ℕ} (r : QRegister k N)
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

theorem embedMatrix_permMatrix_mulVec_ket {k : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment N) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

theorem embedUnitary_permutationUnitary_mulVec_ket {k : ℕ} (r : QRegister k N)
    (e : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment N) :
    (r.embedUnitary (permutationUnitary e)).1.mulVec (ket β) =
      ket (writeReg β r (basisBits k (e (localIdx r β)))) := by
  rw [QRegister.embedUnitary_val, permutationUnitary, embedMatrix_permMatrix_mulVec_ket]
  rfl

theorem singleton_embedMatrix_mulVec_ket (q : Wire N) (A : Matrix (Fin 2) (Fin 2) ℂ)
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

theorem eval_seq_mulVec (c₁ c₂ : Circuit N) (ψ : Fin (2 ^ N) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

theorem ket_X (q : Wire N) (β : BitAssignment N) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]

theorem ket_Z (q : Wire N) (β : BitAssignment N) :
    (Circuit.Z q).eval.1.mulVec (ket β) = (if β q = 0 then (1 : ℂ) else -1) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem ket_CNOT (c t : Wire N) (h : c ≠ t) (β : BitAssignment N) :
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

theorem ket_TOFF (c₁ c₂ t : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
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

theorem toffoli_eval_mul_self (c₁ c₂ t : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval * (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_TOFF, Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
    Function.update_idem]
  have hadd : β t + β c₁ * β c₂ + β c₁ * β c₂ = β t := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

/-- Zero-outcome projector onto an arbitrary finite set of wires `S`. -/
noncomputable def zeroProjOn (S : Finset (Wire N)) : Operator (2 ^ N) :=
  Matrix.diagonal fun global ↦ if ∀ q ∈ S, basisBits N global q = 0 then 1 else 0

@[simp]
theorem zeroProjOn_empty : zeroProjOn (∅ : Finset (Wire N)) = 1 := by
  simp [zeroProjOn]

theorem zeroProjOn_mulVec_ket (S : Finset (Wire N)) (β : BitAssignment N) :
    (zeroProjOn S).mulVec (ket β) = if ∀ q ∈ S, β q = 0 then ket β else 0 := by
  funext j
  rw [zeroProjOn, ket, basisState, Matrix.mulVec_diagonal]
  by_cases hj : j = (basisBits N).symm β
  · subst hj
    rw [basisBits_basisBitsEquiv_symm, Pi.single_eq_same, mul_one]
    by_cases hS : ∀ q ∈ S, β q = 0
    · rw [ite_eq_left hS, ite_eq_left hS, Pi.single_eq_same]
    · rw [ite_eq_right hS, ite_eq_right hS, Pi.zero_apply]
  · rw [Pi.single_eq_of_ne hj, mul_zero]
    by_cases hS : ∀ q ∈ S, β q = 0
    · rw [ite_eq_left hS, Pi.single_eq_of_ne hj]
    · rw [ite_eq_right hS, Pi.zero_apply]

@[simp]
theorem zeroProjOn_conjTranspose (S : Finset (Wire N)) : (zeroProjOn S)ᴴ = zeroProjOn S := by
  ext i j
  simp only [zeroProjOn, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    by_cases h : ∀ q ∈ S, basisBits N i q = 0
    · rw [ite_eq_left h]; simp
    · rw [ite_eq_right h]; simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

theorem zeroProjOn_union (S₁ S₂ : Finset (Wire N)) :
    zeroProjOn (S₁ ∪ S₂) = zeroProjOn S₁ * zeroProjOn S₂ := by
  ext i j
  rw [zeroProjOn, zeroProjOn, zeroProjOn, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    have hiff : (∀ q ∈ S₁ ∪ S₂, basisBits N i q = 0) ↔
        (∀ q ∈ S₁, basisBits N i q = 0) ∧ (∀ q ∈ S₂, basisBits N i q = 0) := by
      simp [or_imp, forall_and]
    by_cases h1 : ∀ q ∈ S₁, basisBits N i q = 0 <;>
      by_cases h2 : ∀ q ∈ S₂, basisBits N i q = 0
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, mul_one]
    · rw [ite_eq_right (fun h ↦ h2 (hiff.mp h).2), ite_eq_left h1, ite_eq_right h2, mul_zero]
    · rw [ite_eq_right (fun h ↦ h1 (hiff.mp h).1), ite_eq_right h1, zero_mul]
    · rw [ite_eq_right (fun h ↦ h1 (hiff.mp h).1), ite_eq_right h1, zero_mul]
  · simp [Matrix.diagonal_apply_ne _ hij]

@[simp]
theorem zeroProjOn_mul_self (S : Finset (Wire N)) : zeroProjOn S * zeroProjOn S = zeroProjOn S := by
  rw [← zeroProjOn_union, Finset.union_idempotent]

theorem zeroProjOn_comm (S₁ S₂ : Finset (Wire N)) :
    zeroProjOn S₁ * zeroProjOn S₂ = zeroProjOn S₂ * zeroProjOn S₁ := by
  rw [← zeroProjOn_union, ← zeroProjOn_union, Finset.union_comm]

theorem basisBits_zero {k : ℕ} (i : Fin k) : basisBits k 0 i = 0 := by
  rw [basisBits_eq_div_mod]
  simp

theorem basisOutcomeProjector_zero_eq_zeroProjOn {k : ℕ} (r : QRegister k N) :
    r.basisOutcomeProjector 0 = zeroProjOn r.image := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, zeroProjOn]
  congr 1
  funext global
  have hiff : r.extractIndex global = 0 ↔ ∀ q ∈ r.image, basisBits N global q = 0 := by
    constructor
    · intro h q hq
      rw [QRegister.mem_image] at hq
      obtain ⟨i, rfl⟩ := hq
      rw [← r.basisBits_extractIndex, h, basisBits_zero]
    · intro h
      apply (basisBits k).injective
      funext i
      rw [r.basisBits_extractIndex, basisBits_zero]
      exact h (r i) (by rw [QRegister.mem_image]; exact ⟨i, rfl⟩)
  by_cases h : r.extractIndex global = 0
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]

theorem singleton_basisOutcomeProjector_zero_eq (q : Wire N) :
    (QRegister.singleton q).basisOutcomeProjector 0 = zeroProjOn {q} := by
  rw [basisOutcomeProjector_zero_eq_zeroProjOn, QRegister.image_singleton]

theorem zeroProjOn_le_one (S : Finset (Wire N)) :
    zeroProjOn S * (zeroProjOn S)ᴴ ≤ 1 := by
  rw [zeroProjOn_conjTranspose, zeroProjOn_mul_self]
  change (1 - zeroProjOn S).PosSemidef
  have hdiag : (1 : Operator (2 ^ N)) - zeroProjOn S =
      Matrix.diagonal (fun g ↦ if ∀ q ∈ S, basisBits N g q = 0 then (0 : ℂ) else 1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.one_apply, zeroProjOn, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; split_ifs <;> norm_num
    · simp [hij]
  rw [hdiag]
  refine Matrix.PosSemidef.diagonal fun g ↦ ?_
  split_ifs <;> norm_num

/-- Restrict an assertion onto `|0⟩` across an arbitrary `Finset` of scratch wires `S`. -/
noncomputable def restrictZeroWires {Var : Type} [Fintype Var]
    (M : QCAssertion Var (2 ^ N)) (S : Finset (Wire N)) : QCAssertion Var (2 ^ N) :=
  fun σ ↦ ⟨HermitianMat.conj (zeroProjOn S) (M σ).1, by
    constructor
    · exact (M σ).1.conj_nonneg (zeroProjOn S) (M σ).2.1
    · exact (HermitianMat.conj_mono (M σ).2.2).trans
        (HermitianMat.conj_one_le_one (zeroProjOn S) (zeroProjOn_le_one S))⟩

@[simp]
theorem restrictZeroWires_coe {Var : Type} [Fintype Var]
    (M : QCAssertion Var (2 ^ N)) (S : Finset (Wire N)) (σ : Store Var) :
    (restrictZeroWires M S σ).1 = (M σ).1.conj (zeroProjOn S) := rfl

@[simp]
theorem restrictZeroWires_empty {Var : Type} [Fintype Var] (M : QCAssertion Var (2 ^ N)) :
    restrictZeroWires M (∅ : Finset (Wire N)) = M := by
  funext σ; apply Subtype.ext; simp

theorem restrictZeroWires_image {Var : Type} [Fintype Var] {s : ℕ}
    (M : QCAssertion Var (2 ^ N)) (r : QRegister s N) :
    restrictZeroWires M r.image = restrictAssertionToZeroAncilla M r := by
  funext σ
  apply Subtype.ext
  simp [basisOutcomeProjector_zero_eq_zeroProjOn]

theorem restrictZeroWires_singleton {Var : Type} [Fintype Var]
    (M : QCAssertion Var (2 ^ N)) (q : Wire N) :
    restrictZeroWires M {q} = restrictAssertionToZeroAncilla M (QRegister.singleton q) := by
  rw [← QRegister.image_singleton q, restrictZeroWires_image]

theorem restrictZeroWires_union {Var : Type} [Fintype Var]
    (M : QCAssertion Var (2 ^ N)) (S₁ S₂ : Finset (Wire N)) :
    restrictZeroWires (restrictZeroWires M S₁) S₂ = restrictZeroWires M (S₁ ∪ S₂) := by
  funext σ
  apply Subtype.ext
  simp [conj_conj, zeroProjOn_union, zeroProjOn_comm S₁ S₂]

theorem restrictZeroWires_idem {Var : Type} [Fintype Var]
    (M : QCAssertion Var (2 ^ N)) (S : Finset (Wire N)) :
    restrictZeroWires (restrictZeroWires M S) S = restrictZeroWires M S := by
  rw [restrictZeroWires_union, Finset.union_idempotent]

theorem restrictZeroWires_comm {Var : Type} [Fintype Var]
    (M : QCAssertion Var (2 ^ N)) (S₁ S₂ : Finset (Wire N)) :
    restrictZeroWires (restrictZeroWires M S₁) S₂ =
      restrictZeroWires (restrictZeroWires M S₂) S₁ := by
  rw [restrictZeroWires_union, Finset.union_comm, ← restrictZeroWires_union]

theorem embedMatrix_comm_zeroProjOn_of_disjoint {k : ℕ}
    (r : QRegister k N) (S : Finset (Wire N)) (hdisj : Disjoint r.image S)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix A * zeroProjOn S = zeroProjOn S * r.embedMatrix A := by
  apply matrix_ext_ket
  intro β
  have hpres (l : Fin (2 ^ k)) :
      (∀ q ∈ S, writeReg β r (basisBits k l) q = 0) ↔ (∀ q ∈ S, β q = 0) := by
    refine forall₂_congr fun q hq ↦ ?_
    have hnot : q ∉ Set.range r.wires := by
      rintro ⟨i, rfl⟩
      exact Finset.disjoint_left.mp hdisj (by rw [QRegister.mem_image]; exact ⟨i, rfl⟩) hq
    rw [writeReg_apply_of_not_mem _ _ _ _ hnot]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
  by_cases hS : ∀ q ∈ S, β q = 0
  · rw [ite_eq_left hS, embedMatrix_mulVec_ket, Matrix.mulVec_sum_smul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [zeroProjOn_mulVec_ket, ite_eq_left ((hpres l).mpr hS)]
  · rw [ite_eq_right hS, Matrix.mulVec_zero, embedMatrix_mulVec_ket, Matrix.mulVec_sum_smul]
    symm
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [zeroProjOn_mulVec_ket, ite_eq_right (mt (hpres l).mp hS), smul_zero]

theorem circuit_eval_comm_zeroProjOn_of_disjoint
    (c : Circuit N) (S : Finset (Wire N)) (hdisj : Disjoint c.support S) :
    c.eval.1 * zeroProjOn S = zeroProjOn S * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g r =>
      exact embedMatrix_comm_zeroProjOn_of_disjoint r S hdisj g.eval.1
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]

theorem restrictZeroWires_wp_qAssign_comm {Var : Type} [Fintype Var]
    (U : Unitary (2 ^ N)) (S : Finset (Wire N))
    (hcomm : U.1 * zeroProjOn S = zeroProjOn S * U.1)
    (Θ : QCAssertion Var (2 ^ N)) :
    restrictZeroWires (qcWpQAssign U Θ) S = qcWpQAssign U (restrictZeroWires Θ S) := by
  funext σ
  apply Subtype.ext
  have hadj : zeroProjOn S * U.1ᴴ = U.1ᴴ * zeroProjOn S := by
    have h := congrArg conjTranspose hcomm
    simpa [zeroProjOn_conjTranspose] using h
  simp only [restrictZeroWires_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hadj]

/-- Any `DynamicCircuit` commutes with `restrictZeroWires` on wires disjoint from its support. -/
theorem restrictZeroWires_wp_comm_of_disjoint_support
    {Var : Type} [Fintype Var] [DecidableEq Var] [NeZero (2 ^ N)]
    (P : DynamicCircuit Var N) (S : Finset (Wire N))
    (hdisj : Disjoint P.support S) (Θ : QCAssertion Var (2 ^ N)) :
    restrictZeroWires (wp P.compile Θ) S = wp P.compile (restrictZeroWires Θ S) := by
  induction P using DynamicCircuit.qcInd generalizing Θ with
  | circuit c =>
      simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile]
      exact restrictZeroWires_wp_qAssign_comm c.eval S
        (circuit_eval_comm_zeroProjOn_of_disjoint c S hdisj) Θ
  | measure v r =>
      funext σ
      apply Subtype.ext
      simp only [DynamicCircuit.support_measure] at hdisj
      simp only [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
        restrictZeroWires_coe, qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe, map_sum,
        qc_qMeasure_outcome_herm_eq_conj, conj_conj, QCAssertion.subst_apply,
        CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      have hcomm : (r.basisOutcomeProjector o)ᴴ * zeroProjOn S =
          zeroProjOn S * (r.basisOutcomeProjector o)ᴴ := by
        rw [QRegister.basisOutcomeProjector_conjTranspose, QRegister.basisOutcomeProjector]
        exact embedMatrix_comm_zeroProjOn_of_disjoint r S hdisj (compProj o)
      rw [hcomm]
  | qIf cond t f iht ihf =>
      simp only [DynamicCircuit.support_qcRawQIf, Finset.disjoint_union_left] at hdisj
      funext σ
      apply Subtype.ext
      simp only [DynamicCircuit.compile_qcRawQIf, restrictZeroWires_coe, wp_qcRawQIf]
      split_ifs
      · exact congrArg Subtype.val (congrFun (iht hdisj.1 Θ) σ)
      · exact congrArg Subtype.val (congrFun (ihf hdisj.2 Θ) σ)
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [DynamicCircuit.compile_seq, wp_qSeq]
      rw [ih₁ hdisj.1, ih₂ hdisj.2]

end KetAndProjectors

/-! ### Wire-set formulation `CleanRealizesWires` & `andSandwich` Theorem -/

/-- Whole-system wire-set clean-ancilla realization predicate for induction without register
re-association. -/
def CleanRealizesWires {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (S : Finset (Wire N)) (U : Unitary (2 ^ N)) (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    restrictZeroWires (wp P.compile Θ) S = restrictZeroWires (qcWpQAssign U Θ) S) ∧
  (∀ Θ : QCAssertion Var (2 ^ N),
    restrictZeroWires (wp P.compile (restrictZeroWires Θ S)) S =
      restrictZeroWires (wp P.compile Θ) S) ∧
  U.1 * zeroProjOn S = zeroProjOn S * U.1

namespace CleanRealizesWires

variable {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]

theorem toCleanRealizes {k s : ℕ} {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizesWires v rScr.image (rAct.embedUnitary U) P) :
    CleanRealizes v rAct rScr U P := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro Θ hΘ
    rw [← restrictZeroWires_image, ← restrictZeroWires_image]
    exact h.2.2.1 Θ hΘ
  · intro Θ
    rw [← restrictZeroWires_image, ← restrictZeroWires_image, ← restrictZeroWires_image]
    exact h.2.2.2.1 Θ

theorem ofCleanRealizes {k s : ℕ} {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    (hdisj : rAct.DisjointWires rScr) {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v rAct rScr U P) :
    CleanRealizesWires v rScr.image (rAct.embedUnitary U) P := by
  have himg : Disjoint rAct.image rScr.image := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rw [QRegister.mem_image] at hq1 hq2
    obtain ⟨i, rfl⟩ := hq1
    obtain ⟨j, hj⟩ := hq2
    exact hdisj.ne i j hj.symm
  refine ⟨h.1, h.2.1, ?_, ?_, embedMatrix_comm_zeroProjOn_of_disjoint rAct rScr.image himg U.1⟩
  · intro Θ hΘ
    rw [restrictZeroWires_image, restrictZeroWires_image]
    exact h.2.2.1 Θ hΘ
  · intro Θ
    rw [restrictZeroWires_image, restrictZeroWires_image, restrictZeroWires_image]
    exact h.2.2.2 Θ

theorem circuit (v : Var) (S : Finset (Wire N)) (c : Circuit N)
    (htoff : c.count PrimitiveGate.TOFF = 0) (hdisj : Disjoint c.support S) :
    CleanRealizesWires v S c.eval (.circuit c) := by
  have hcomm := circuit_eval_comm_zeroProjOn_of_disjoint c S hdisj
  refine ⟨htoff, ?_, ?_, ?_, hcomm⟩
  · intro Θ hΘ σ val
    simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign,
      hΘ σ val]
  · intro Θ _
    simp
  · intro Θ
    simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile]
    rw [← restrictZeroWires_wp_qAssign_comm c.eval S hcomm, restrictZeroWires_idem]

theorem identity (v : Var) (S : Finset (Wire N)) :
    CleanRealizesWires v S 1 DynamicCircuit.identity :=
  circuit v S .identity rfl (by simp)

theorem seq {v : Var} {S : Finset (Wire N)} {U₁ U₂ : Unitary (2 ^ N)}
    {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : CleanRealizesWires v S U₁ P₁) (h₂ : CleanRealizesWires v S U₂ P₂) :
    CleanRealizesWires v S (U₂ * U₁) (.seq P₁ P₂) := by
  refine ⟨by simp [h₁.1, h₂.1], ?_, ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    simp only [DynamicCircuit.compile_seq, wp_qSeq]
    exact h₁.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ) σ val
  · intro Θ hΘ
    have hP₂v : ∀ σ val, wp P₂.compile Θ (Function.update σ v val) = wp P₂.compile Θ σ :=
      h₂.2.1 Θ hΘ
    have hS₂v : ∀ σ val,
        restrictZeroWires (wp P₂.compile Θ) S (Function.update σ v val) =
          restrictZeroWires (wp P₂.compile Θ) S σ := by
      intro σ val; apply Subtype.ext; simp [hP₂v σ val]
    simp only [DynamicCircuit.compile_seq, wp_qSeq]
    rw [← h₁.2.2.2.1 (wp P₂.compile Θ), h₁.2.2.1 _ hS₂v, h₂.2.2.1 Θ hΘ,
      ← restrictZeroWires_wp_qAssign_comm U₁ S h₁.2.2.2.2, restrictZeroWires_idem,
      qc_wp_qAssign_comp]
  · intro Θ
    simp only [DynamicCircuit.compile_seq, wp_qSeq]
    rw [← h₁.2.2.2.1 (wp P₂.compile (restrictZeroWires Θ S)), h₂.2.2.2.1 Θ,
      h₁.2.2.2.1 (wp P₂.compile Θ)]
  · simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc, h₁.2.2.2.2, ← Matrix.mul_assoc, h₂.2.2.2.2, Matrix.mul_assoc]

theorem congr_unitary {v : Var} {S : Finset (Wire N)} {U W : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (h : CleanRealizesWires v S U P)
    (heq : U.1 * zeroProjOn S = W.1 * zeroProjOn S)
    (hW_comm : W.1 * zeroProjOn S = zeroProjOn S * W.1) :
    CleanRealizesWires v S W P := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, hW_comm⟩
  intro Θ hΘ
  rw [h.2.2.1 Θ hΘ]
  funext σ
  apply Subtype.ext
  have hadj : zeroProjOn S * U.1ᴴ = zeroProjOn S * W.1ᴴ := by
    have h' := congrArg conjTranspose heq
    simpa [zeroProjOn_conjTranspose] using h'
  simp only [restrictZeroWires_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hadj]

theorem extend_wires {v : Var} {S : Finset (Wire N)} (T : Finset (Wire N))
    {U : Unitary (2 ^ N)} {P : DynamicCircuit Var N}
    (h : CleanRealizesWires v S U P)
    (hdisj : Disjoint P.support T)
    (hU_comm : U.1 * zeroProjOn T = zeroProjOn T * U.1) :
    CleanRealizesWires v (S ∪ T) U P := by
  have hUT : U.1 * zeroProjOn (S ∪ T) = zeroProjOn (S ∪ T) * U.1 := by
    rw [zeroProjOn_union, ← Matrix.mul_assoc, h.2.2.2.2, Matrix.mul_assoc, hU_comm,
      ← Matrix.mul_assoc]
  refine ⟨h.1, h.2.1, ?_, ?_, hUT⟩
  · intro Θ hΘ
    have hΘT : ∀ σ val,
        restrictZeroWires Θ T (Function.update σ v val) = restrictZeroWires Θ T σ := by
      intro σ val; apply Subtype.ext; simp [hΘ σ val]
    rw [Finset.union_comm, ← restrictZeroWires_union, ← restrictZeroWires_union,
      restrictZeroWires_wp_comm_of_disjoint_support P T hdisj, h.2.2.1 _ hΘT,
      restrictZeroWires_wp_qAssign_comm U T hU_comm]
  · intro Θ
    rw [← restrictZeroWires_union (wp P.compile (restrictZeroWires Θ (S ∪ T))) S T,
      ← restrictZeroWires_union Θ S T,
      ← restrictZeroWires_union (wp P.compile Θ) S T,
      ← restrictZeroWires_wp_comm_of_disjoint_support P T hdisj,
      restrictZeroWires_comm (wp P.compile (restrictZeroWires Θ S)) T S,
      h.2.2.2.1 Θ,
      restrictZeroWires_idem]

/-- General temporary-AND compute/body/uncompute sandwich theorem around an arbitrary
`DynamicCircuit` body `mid`. -/
theorem andSandwich {v : Var} {S : Finset (Wire N)}
    (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hc₁ : c₁ ∉ S) (hc₂ : c₂ ∉ S) (hanc : anc ∉ S)
    {U_mid W : Unitary (2 ^ N)} {mid : DynamicCircuit Var N}
    (hmid : CleanRealizesWires v S U_mid mid)
    (hW_act :
      let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      (T_anc * U_mid * T_anc).1 * P₀ = W.1 * P₀)
    (hW_anc :
      let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
      W.1 * P₀ = P₀ * W.1)
    (hW_S : W.1 * zeroProjOn S = zeroProjOn S * W.1) :
    CleanRealizesWires v (insert anc S) W
      (Comparators.andSandwich v c₁ c₂ anc h₁₂ h₁a h₂a mid) := by
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let V := T_anc * U_mid * T_anc
  have hdisj_triple : Disjoint ({c₁, c₂, anc} : Finset (Wire N)) S := by
    rw [Finset.disjoint_left]
    intro q hq hqS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hc₁ hqS
    · exact hc₂ hqS
    · exact hanc hqS
  have hdisj_comp :
      Disjoint (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).support S := by
    simpa [DynamicCircuit.support_andCompute] using hdisj_triple
  have hdisj_uncomp : Disjoint (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).support S := by
    simpa [DynamicCircuit.support_andUncompute] using hdisj_triple
  have hins : insert anc S = S ∪ {anc} := by
    rw [Finset.insert_eq, Finset.union_comm]
  have hW_comm : W.1 * zeroProjOn (insert anc S) = zeroProjOn (insert anc S) * W.1 := by
    rw [hins, zeroProjOn_union, ← singleton_basisOutcomeProjector_zero_eq]
    change W.1 * (zeroProjOn S * P₀) = zeroProjOn S * P₀ * W.1
    rw [← Matrix.mul_assoc, hW_S, Matrix.mul_assoc, hW_anc, ← Matrix.mul_assoc]
  refine ⟨by simp [hmid.1], ?_, ?_, ?_, hW_comm⟩
  · intro Θ _ σ val
    simp only [Comparators.andSandwich, DynamicCircuit.compile_seq, wp_qSeq]
    have hunv : ∀ σ' val',
        wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ (Function.update σ' v val') =
          wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ σ' :=
      DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ
    have hmidv := hmid.2.1 _ hunv
    simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, hmidv σ val]
  · intro Θ hΘ
    have hunv : ∀ σ' val',
        wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ (Function.update σ' v val') =
          wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ σ' :=
      DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ
    have hΘS : ∀ σ' val',
        restrictZeroWires Θ S (Function.update σ' v val') = restrictZeroWires Θ S σ' := by
      intro σ' val'; apply Subtype.ext; simp [hΘ σ' val']
    have hT_sq : T_anc * T_anc = 1 := toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a
    have hU_eq : U_mid * T_anc = T_anc * V := by
      dsimp only [V]; rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
    have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
    have hP₀_idem : P₀ * P₀ = P₀ := QRegister.basisOutcomeProjector_mul_self _ 0
    have hadj_VW : P₀ * V.1ᴴ = P₀ * W.1ᴴ := by
      have h : (V.1 * P₀)ᴴ = (W.1 * P₀)ᴴ := congrArg conjTranspose hW_act
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP₀_herm] at h
      exact h
    have hadj_W : P₀ * W.1ᴴ = W.1ᴴ * P₀ := by
      have h : (W.1 * P₀)ᴴ = (P₀ * W.1)ᴴ := congrArg conjTranspose hW_anc
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP₀_herm] at h
      exact h
    have hV_idem (Ψ : QCAssertion Var (2 ^ N)) :
        restrictAssertionToZeroAncilla
          (qcWpQAssign V (restrictAssertionToZeroAncilla Ψ (QRegister.singleton anc)))
          (QRegister.singleton anc) =
        restrictAssertionToZeroAncilla (qcWpQAssign V Ψ) (QRegister.singleton anc) := by
      funext σ
      apply Subtype.ext
      simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
      rw [← Matrix.mul_assoc, hadj_VW, hadj_W, Matrix.mul_assoc, hP₀_idem, ← hadj_W, ← hadj_VW]
    have hVW (Ψ : QCAssertion Var (2 ^ N)) :
        restrictAssertionToZeroAncilla (qcWpQAssign V Ψ) (QRegister.singleton anc) =
        restrictAssertionToZeroAncilla (qcWpQAssign W Ψ) (QRegister.singleton anc) := by
      funext σ
      apply Subtype.ext
      simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
      dsimp only [P₀] at hadj_VW
      rw [hadj_VW]
    rw [hins, ← restrictZeroWires_union, ← restrictZeroWires_union,
      restrictZeroWires_singleton, restrictZeroWires_singleton,
      restrictZeroWires_wp_qAssign_comm W S hW_S]
    simp only [Comparators.andSandwich, DynamicCircuit.compile_seq, wp_qSeq]
    rw [restrictZeroWires_wp_comm_of_disjoint_support _ S hdisj_comp,
      hmid.2.2.1 _ hunv,
      restrictZeroWires_wp_qAssign_comm U_mid S hmid.2.2.2.2,
      restrictZeroWires_wp_comm_of_disjoint_support _ S hdisj_uncomp]
    simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile]
    rw [DynamicCircuit.qc_wp_qAssign_andCompute c₁ c₂ anc h₁₂ h₁a h₂a,
      qc_wp_qAssign_comp, hU_eq, ← qc_wp_qAssign_comp, ← hV_idem,
      DynamicCircuit.qc_wp_toffoli_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a (restrictZeroWires Θ S) hΘS,
      hV_idem, hVW]
  · intro Θ
    have huncomp_clean :
        wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile
          (restrictZeroWires Θ (insert anc S)) =
        restrictZeroWires (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ) S := by
      rw [Finset.insert_eq, ← restrictZeroWires_union Θ {anc} S,
        ← restrictZeroWires_wp_comm_of_disjoint_support _ S hdisj_uncomp,
        restrictZeroWires_singleton Θ anc,
        DynamicCircuit.wp_andUncompute_clean_post v c₁ c₂ anc h₁₂ h₁a h₂a Θ]
    simp only [Comparators.andSandwich, DynamicCircuit.compile_seq, wp_qSeq]
    rw [huncomp_clean, hins, ← restrictZeroWires_union, ← restrictZeroWires_union,
      restrictZeroWires_wp_comm_of_disjoint_support _ S hdisj_comp,
      restrictZeroWires_wp_comm_of_disjoint_support _ S hdisj_comp,
      hmid.2.2.2.1]

/-- `jonesToffoli` satisfies `CleanRealizesWires` on any clean wire set `S` containing `anc` and
disjoint from `{c₁, c₂, target}`. -/
theorem jonesToffoli {v : Var} {S : Finset (Wire N)}
    (c₁ c₂ target anc : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ target) (h₂t : c₂ ≠ target)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hta : target ≠ anc)
    (hc₁ : c₁ ∉ S) (hc₂ : c₂ ∉ S) (ht : target ∉ S) (hanc : anc ∈ S) :
    CleanRealizesWires v S (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).eval
      (DynamicCircuit.jonesToffoli v c₁ c₂ target anc h₁₂ h₁a h₂a hta) := by
  let S' := S.erase anc
  have hS_eq : insert anc S' = S := Finset.insert_erase hanc
  have hc₁' : c₁ ∉ S' := fun h ↦ hc₁ (Finset.mem_of_mem_erase h)
  have hc₂' : c₂ ∉ S' := fun h ↦ hc₂ (Finset.mem_of_mem_erase h)
  have ht' : target ∉ S' := fun h ↦ ht (Finset.mem_of_mem_erase h)
  have hanc' : anc ∉ S' := Finset.notMem_erase anc S
  have hmid : CleanRealizesWires v S' (Circuit.CNOT anc target hta.symm).eval
      (.circuit (Circuit.CNOT anc target hta.symm)) := by
    refine circuit v S' (Circuit.CNOT anc target hta.symm) (by simp [Circuit.CNOT]) ?_
    rw [Circuit.support_cnot, Finset.disjoint_left]
    intro q hq hqS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hanc' hqS
    · exact ht' hqS
  have hW_act :
      let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      (T_anc * (Circuit.CNOT anc target hta.symm).eval * T_anc).1 * P₀ =
        (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).eval.1 * P₀ := by
    intro P₀ T_anc
    apply matrix_ext_ket
    intro β
    dsimp only [P₀, T_anc]
    rw [singleton_basisOutcomeProjector_zero_eq]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket,
      Finset.mem_singleton, forall_eq]
    by_cases hb : β anc = 0
    · simp only [hb, ↓reduceIte, ket_TOFF, zero_add, ket_CNOT,
        Function.update_self, Function.update_of_ne hta,
        Function.update_of_ne h₁t, Function.update_of_ne h₂t,
        Function.update_of_ne h₁a, Function.update_of_ne h₂a,
        Function.update_comm hta.symm, Function.update_idem,
        CharTwo.add_self_eq_zero]
      congr 1
      funext w
      by_cases hw : w = anc
      · subst hw; simp [Function.update_of_ne hta.symm, hb]
      · simp [Function.update_of_ne hw]
    · simp [hb]
  have hdisj_toff_anc : Disjoint (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).support {anc} := by
    rw [Circuit.support_toffoli, Finset.disjoint_left]
    intro q hq hqa
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq hqa
    subst hqa
    rcases hq with h | h | h
    · exact h₁a h.symm
    · exact h₂a h.symm
    · exact hta h.symm
  have hdisj_toff_S' : Disjoint (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).support S' := by
    rw [Circuit.support_toffoli, Finset.disjoint_left]
    intro q hq hqS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hc₁' hqS
    · exact hc₂' hqS
    · exact ht' hqS
  have hW_anc :
      let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
      (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).eval.1 * P₀ =
        P₀ * (Circuit.TOFF c₁ c₂ target h₁₂ h₁t h₂t).eval.1 := by
    dsimp only
    rw [singleton_basisOutcomeProjector_zero_eq]
    exact circuit_eval_comm_zeroProjOn_of_disjoint _ {anc} hdisj_toff_anc
  have hW_S' := circuit_eval_comm_zeroProjOn_of_disjoint _ S' hdisj_toff_S'
  have hsnd := andSandwich c₁ c₂ anc h₁₂ h₁a h₂a hc₁' hc₂' hanc' hmid hW_act hW_anc hW_S'
  rwa [hS_eq] at hsnd

end CleanRealizesWires

/-! ## 2. `w`-Bit Controlled Register Swap (`cswapDyn`, `cswapRegDyn`) -/

theorem fin_eq_castAdd_or_natAdd {a b : ℕ} (p : Fin (a + b)) :
    (∃ i : Fin a, p = Fin.castAdd b i) ∨ (∃ j : Fin b, p = Fin.natAdd a j) := by
  have hp := (finSumFinEquiv (m := a) (n := b)).apply_symm_apply p
  rcases h : finSumFinEquiv.symm p with i | j
  · rw [h] at hp; exact Or.inl ⟨i, hp.symm⟩
  · rw [h] at hp; exact Or.inr ⟨j, hp.symm⟩

/-- Apply `X` to the first `m` wires (`m ≤ k`) of `r`. -/
def xPrefixCirc {N k : ℕ} (r : QRegister k N) : (m : ℕ) → m ≤ k → Circuit N
  | 0, _ => .identity
  | m + 1, hm => xPrefixCirc r m (Nat.le_of_succ_le hm) ;;ᶜ Circuit.X (r ⟨m, hm⟩)

/-- Apply `X` to every wire of `r` (`0` `T` gates, `0` `TOFF` gates). -/
def xRegCirc {N k : ℕ} (r : QRegister k N) : Circuit N :=
  xPrefixCirc r k le_rfl

@[simp]
theorem count_xPrefixCirc_toff {N k : ℕ} (r : QRegister k N) (m : ℕ) (hm : m ≤ k) :
    (xPrefixCirc r m hm).count PrimitiveGate.TOFF = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [xPrefixCirc, ih (Nat.le_of_succ_le hm), Circuit.X]

@[simp]
theorem count_xPrefixCirc_t {N k : ℕ} (r : QRegister k N) (m : ℕ) (hm : m ≤ k) :
    (xPrefixCirc r m hm).count PrimitiveGate.T = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [xPrefixCirc, ih (Nat.le_of_succ_le hm), Circuit.X]

theorem support_xPrefixCirc_subset {N k : ℕ} (r : QRegister k N) (m : ℕ) (hm : m ≤ k) :
    (xPrefixCirc r m hm).support ⊆ r.image := by
  induction m with
  | zero => simp [xPrefixCirc]
  | succ m ih =>
      simp only [xPrefixCirc, Circuit.support_seq, Circuit.support_single, Finset.union_subset_iff,
        Finset.singleton_subset_iff]
      exact ⟨ih (Nat.le_of_succ_le hm), by rw [QRegister.mem_image]; exact ⟨⟨m, hm⟩, rfl⟩⟩

@[simp]
theorem count_xRegCirc_toff {N k : ℕ} (r : QRegister k N) :
    (xRegCirc r).count PrimitiveGate.TOFF = 0 :=
  count_xPrefixCirc_toff r k le_rfl

@[simp]
theorem count_xRegCirc_t {N k : ℕ} (r : QRegister k N) :
    (xRegCirc r).count PrimitiveGate.T = 0 :=
  count_xPrefixCirc_t r k le_rfl

theorem support_xRegCirc_subset {N k : ℕ} (r : QRegister k N) :
    (xRegCirc r).support ⊆ r.image :=
  support_xPrefixCirc_subset r k le_rfl

namespace ReflectionProofs

/-- Complement the first `m` wires of register `r` in global bit assignment `β`. -/
def flipPrefixBits {N k : ℕ} (r : QRegister k N) (m : ℕ) (β : BitAssignment N) :
    BitAssignment N :=
  fun q ↦ if ∃ i : Fin k, i.val < m ∧ r i = q then β q + 1 else β q

/-- Complement every wire of register `r` in global bit assignment `β`. -/
def flipRegBits {N k : ℕ} (r : QRegister k N) (β : BitAssignment N) : BitAssignment N :=
  fun q ↦ if q ∈ r.image then β q + 1 else β q

@[simp]
theorem flipRegBits_apply_reg {N k : ℕ} (r : QRegister k N) (β : BitAssignment N) (i : Fin k) :
    flipRegBits r β (r i) = β (r i) + 1 := by
  have hmem : r i ∈ r.image := by rw [QRegister.mem_image]; exact ⟨i, rfl⟩
  simp [flipRegBits, hmem]

theorem flipRegBits_apply_of_not_mem {N k : ℕ} (r : QRegister k N) (β : BitAssignment N)
    (q : Wire N) (hq : q ∉ r.image) :
    flipRegBits r β q = β q := by
  simp [flipRegBits, hq]

theorem xPrefixCirc_mulVec_ket {N k : ℕ} (r : QRegister k N) (m : ℕ) (hm : m ≤ k)
    (β : BitAssignment N) :
    (xPrefixCirc r m hm).eval.1.mulVec (ket β) = ket (flipPrefixBits r m β) := by
  induction m with
  | zero =>
      change (1 : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ).mulVec (ket β) = _
      rw [Matrix.one_mulVec]
      congr 1
      funext q
      simp [flipPrefixBits]
  | succ m ih =>
      simp only [xPrefixCirc, eval_seq_mulVec, ih (Nat.le_of_succ_le hm), ket_X]
      congr 1
      funext q
      by_cases hq : q = r ⟨m, hm⟩
      · subst hq
        rw [Function.update_self]
        have hnot : ¬ ∃ i : Fin k, i.val < m ∧ r i = r ⟨m, hm⟩ := by
          rintro ⟨i, hilt, hi⟩
          have hidx := r.wires.injective hi
          have hval := congrArg Fin.val hidx
          dsimp at hval
          omega
        have hyes : ∃ i : Fin k, i.val < m + 1 ∧ r i = r ⟨m, hm⟩ :=
          ⟨⟨m, hm⟩, Nat.lt_succ_self m, rfl⟩
        rw [flipPrefixBits, ite_eq_right hnot, flipPrefixBits, ite_eq_left hyes]
      · rw [Function.update_of_ne hq]
        have hiff : (∃ i : Fin k, i.val < m ∧ r i = q) ↔
            (∃ i : Fin k, i.val < m + 1 ∧ r i = q) := by
          constructor
          · rintro ⟨i, hilt, hi⟩
            exact ⟨i, Nat.lt_succ_of_lt hilt, hi⟩
          · rintro ⟨i, hilt, hi⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hilt with hlt | heq
            · exact ⟨i, hlt, hi⟩
            · have hi_eq : i = ⟨m, hm⟩ := Fin.ext heq
              subst hi_eq
              exact absurd hi.symm hq
        by_cases hex : ∃ i : Fin k, i.val < m ∧ r i = q
        · rw [flipPrefixBits, ite_eq_left hex, flipPrefixBits, ite_eq_left (hiff.mp hex)]
        · rw [flipPrefixBits, ite_eq_right hex, flipPrefixBits, ite_eq_right (mt hiff.mpr hex)]

theorem xRegCirc_mulVec_ket {N k : ℕ} (r : QRegister k N) (β : BitAssignment N) :
    (xRegCirc r).eval.1.mulVec (ket β) = ket (flipRegBits r β) := by
  rw [xRegCirc, xPrefixCirc_mulVec_ket]
  congr 1
  funext q
  have hiff : (∃ i : Fin k, i.val < k ∧ r i = q) ↔ q ∈ r.image := by
    rw [QRegister.mem_image]
    exact ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩, fun ⟨i, hi⟩ ↦ ⟨i, i.isLt, hi⟩⟩
  by_cases hq : q ∈ r.image
  · rw [flipPrefixBits, ite_eq_left (hiff.mpr hq), flipRegBits, ite_eq_left hq]
  · rw [flipPrefixBits, ite_eq_right (mt hiff.mp hq), flipRegBits, ite_eq_right hq]

theorem insert_zero_slice_one_image {N d : ℕ} (rScr : QRegister (d + 1) N) :
    insert (rScr 0) (rScr.slice 1 d (by omega)).image = rScr.image := by
  ext q
  simp only [Finset.mem_insert, QRegister.mem_image]
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨⟨1 + j.val, by omega⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · left
      congr 1
      ext
      exact hi0
    · right
      refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      rw [QRegister.slice_apply]
      congr 1
      ext
      dsimp
      omega

end ReflectionProofs

/-- Little-endian unsigned natural-number value `< 2 ^ w` of `r` on bit assignment `β`. -/
noncomputable abbrev regVal {N w : ℕ} (r : QRegister w N) (β : BitAssignment N) : ℕ :=
  (localIdx r β).val

theorem regVal_lt {N w : ℕ} (r : QRegister w N) (β : BitAssignment N) :
    regVal r β < 2 ^ w :=
  (localIdx r β).isLt

@[simp]
theorem extractIndex_val_eq_regVal {N w : ℕ} (r : QRegister w N) (g : Fin (2 ^ N)) :
    (r.extractIndex g).val = regVal r (basisBits N g) := by
  simp [regVal, localIdx, QRegister.extractIndex]

/-- Convert a `ZMod 2` wire bit to `{0, 1} ⊆ ℕ`. -/
def bitNat (b : ZMod 2) : ℕ := if b = 1 then 1 else 0

theorem bitNat_lt_two (b : ZMod 2) : bitNat b < 2 := by
  dsimp [bitNat]
  split_ifs <;> omega

theorem regVal_div_pow_mod_two {N w : ℕ} (r : QRegister w N) (β : BitAssignment N)
    {m : ℕ} (hm : m < w) :
    (regVal r β / 2 ^ m) % 2 = bitNat (β (r ⟨m, hm⟩)) := by
  have hb := basisBits_eq_div_mod w (localIdx r β) ⟨m, hm⟩
  rw [basisBits_basisBitsEquiv_symm] at hb
  dsimp only [regVal]
  have hmod : (localIdx r β).val / 2 ^ m % 2 < 2 := Nat.mod_lt _ (by omega)
  rcases (by omega : (localIdx r β).val / 2 ^ m % 2 = 0 ∨
      (localIdx r β).val / 2 ^ m % 2 = 1) with h0 | h1
  · rw [h0] at hb ⊢
    simp [hb, bitNat]
  · rw [h1] at hb ⊢
    simp [hb, bitNat]

theorem nat_div_pow_eq (x m : ℕ) :
    x / 2 ^ m = (x / 2 ^ m) % 2 + 2 * (x / 2 ^ (m + 1)) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- Conjugate a `DynamicCircuit` by `Circuit.X q` (`0` `T` gates, `0` `TOFF` gates). -/
def conjXDyn {Var : Type} {N : ℕ} (q : Wire N) (mid : DynamicCircuit Var N) :
    DynamicCircuit Var N :=
  .seq (.circuit (Circuit.X q)) (.seq mid (.circuit (Circuit.X q)))

/-- Conjugate a `DynamicCircuit` by `Circuit.CNOT c d` (`0` `T` gates, `0` `TOFF` gates). -/
def conjCNOTDyn {Var : Type} {N : ℕ} (c d : Wire N) (hcd : c ≠ d)
    (mid : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (.circuit (Circuit.CNOT c d hcd)) (.seq mid (.circuit (Circuit.CNOT c d hcd)))

@[simp]
theorem count_conjXDyn_toff {Var : Type} {N : ℕ} (q : Wire N) (mid : DynamicCircuit Var N) :
    (conjXDyn q mid).count PrimitiveGate.TOFF = mid.count PrimitiveGate.TOFF := by
  simp [conjXDyn, Circuit.X]

@[simp]
theorem count_conjXDyn_t {Var : Type} {N : ℕ} (q : Wire N) (mid : DynamicCircuit Var N) :
    (conjXDyn q mid).count PrimitiveGate.T = mid.count PrimitiveGate.T := by
  simp [conjXDyn, Circuit.X]

@[simp]
theorem support_conjXDyn {Var : Type} {N : ℕ} (q : Wire N) (mid : DynamicCircuit Var N) :
    (conjXDyn q mid).support = insert q mid.support := by
  ext w
  simp only [conjXDyn, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
    Circuit.support_single, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

@[simp]
theorem count_conjCNOTDyn_toff {Var : Type} {N : ℕ} (c d : Wire N) (hcd : c ≠ d)
    (mid : DynamicCircuit Var N) :
    (conjCNOTDyn c d hcd mid).count PrimitiveGate.TOFF = mid.count PrimitiveGate.TOFF := by
  simp [conjCNOTDyn, Circuit.CNOT]

@[simp]
theorem count_conjCNOTDyn_t {Var : Type} {N : ℕ} (c d : Wire N) (hcd : c ≠ d)
    (mid : DynamicCircuit Var N) :
    (conjCNOTDyn c d hcd mid).count PrimitiveGate.T = mid.count PrimitiveGate.T := by
  simp [conjCNOTDyn, Circuit.CNOT]

@[simp]
theorem support_conjCNOTDyn {Var : Type} {N : ℕ} (c d : Wire N) (hcd : c ≠ d)
    (mid : DynamicCircuit Var N) :
    (conjCNOTDyn c d hcd mid).support = {c, d} ∪ mid.support := by
  ext w
  simp only [conjCNOTDyn, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
    Circuit.support_cnot, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ### Multiplexed Predicate Unitaries, Oracle Unitaries, and `PredRealizes` Combinators -/

namespace ComparatorProofs

/-- Computational-basis projector onto states satisfying `g β = val`. -/
noncomputable def predDiag {N : ℕ} (g : BitAssignment N → Bool) (val : Bool) :
    Operator (2 ^ N) :=
  Matrix.diagonal fun idx ↦ if g (basisBits N idx) = val then (1 : ℂ) else 0

@[simp]
theorem predDiag_conjTranspose {N : ℕ} (g : BitAssignment N → Bool) (val : Bool) :
    (predDiag g val)ᴴ = predDiag g val := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [predDiag, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [predDiag, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem predDiag_mul_same {N : ℕ} (g : BitAssignment N → Bool) (val : Bool) :
    predDiag g val * predDiag g val = predDiag g val := by
  rw [predDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext idx
  split_ifs <;> norm_num

theorem predDiag_mul_diff {N : ℕ} (g : BitAssignment N → Bool) {v₁ v₂ : Bool} (hne : v₁ ≠ v₂) :
    predDiag g v₁ * predDiag g v₂ = 0 := by
  rw [predDiag, predDiag, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
    cases h : g (basisBits N i) <;> cases v₁ <;> cases v₂ <;> simp_all
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem predDiag_true_add_false {N : ℕ} (g : BitAssignment N → Bool) :
    predDiag g true + predDiag g false = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [predDiag, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    cases g (basisBits N i) <;> simp
  · simp [predDiag, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem predDiag_mulVec_ket {N : ℕ} (g : BitAssignment N → Bool) (val : Bool)
    (β : BitAssignment N) :
    (predDiag g val).mulVec (ket β) = if g β = val then ket β else 0 := by
  funext j
  rw [predDiag, ket, basisState, Matrix.mulVec_diagonal]
  by_cases hj : j = (basisBits N).symm β
  · subst hj
    rw [basisBits_basisBitsEquiv_symm, Pi.single_eq_same, mul_one]
    by_cases hv : g β = val
    · rw [ite_eq_left hv, ite_eq_left hv, Pi.single_eq_same]
    · rw [ite_eq_right hv, ite_eq_right hv, Pi.zero_apply]
  · rw [Pi.single_eq_of_ne hj, mul_zero]
    by_cases hv : g β = val
    · rw [ite_eq_left hv, Pi.single_eq_of_ne hj]
    · rw [ite_eq_right hv, Pi.zero_apply]

theorem embedMatrix_comm_predDiag {N t : ℕ} (rTarget : QRegister t N)
    (A : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ) (g : BitAssignment N → Bool)
    (hg : ∀ β γ, g (writeReg β rTarget γ) = g β) (val : Bool) :
    rTarget.embedMatrix A * predDiag g val = predDiag g val * rTarget.embedMatrix A := by
  apply matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, predDiag_mulVec_ket]
  by_cases hv : g β = val
  · rw [ite_eq_left hv, embedMatrix_mulVec_ket, Matrix.mulVec_sum_smul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [predDiag_mulVec_ket, hg β (basisBits t l), ite_eq_left hv]
  · rw [ite_eq_right hv, Matrix.mulVec_zero, embedMatrix_mulVec_ket, Matrix.mulVec_sum_smul]
    symm
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [predDiag_mulVec_ket, hg β (basisBits t l), ite_eq_right hv, smul_zero]

/-- Operator multiplexing `V₁` on `rTarget` when `g` is `true` and `V₀` when `g` is `false`. -/
noncomputable def muxPredMatrix {N t : ℕ} (rTarget : QRegister t N)
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool) : Operator (2 ^ N) :=
  rTarget.embedMatrix V₁.1 * predDiag g true +
    rTarget.embedMatrix V₀.1 * predDiag g false

theorem muxPredMatrix_mem_unitaryGroup {N t : ℕ} (rTarget : QRegister t N)
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool)
    (hg : ∀ β γ, g (writeReg β rTarget γ) = g β) :
    muxPredMatrix rTarget V₀ V₁ g ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  let U₁ := rTarget.embedMatrix V₁.1
  let U₀ := rTarget.embedMatrix V₀.1
  let P₁ := predDiag g true
  let P₀ := predDiag g false
  have hU₁ : U₁ * U₁ᴴ = 1 := by
    dsimp [U₁]
    rw [← rTarget.embedMatrix_conjTranspose, ← rTarget.embedMatrix_mul]
    have hV₁ : V₁.1 * V₁.1ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact V₁.2.2
    rw [hV₁, rTarget.embedMatrix_one]
  have hU₀ : U₀ * U₀ᴴ = 1 := by
    dsimp [U₀]
    rw [← rTarget.embedMatrix_conjTranspose, ← rTarget.embedMatrix_mul]
    have hV₀ : V₀.1 * V₀.1ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact V₀.2.2
    rw [hV₀, rTarget.embedMatrix_one]
  have hc₁ : U₁ * P₁ = P₁ * U₁ := embedMatrix_comm_predDiag rTarget V₁.1 g hg true
  have hc₀ : U₀ * P₀ = P₀ * U₀ := embedMatrix_comm_predDiag rTarget V₀.1 g hg false
  change (U₁ * P₁ + U₀ * P₀) * (U₁ * P₁ + U₀ * P₀)ᴴ = 1
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    predDiag_conjTranspose, predDiag_conjTranspose,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  have ht1 : U₁ * P₁ * (P₁ * U₁ᴴ) = P₁ := by
    calc U₁ * P₁ * (P₁ * U₁ᴴ)
        = U₁ * (P₁ * P₁) * U₁ᴴ := by simp only [Matrix.mul_assoc]
      _ = (U₁ * P₁) * U₁ᴴ := by rw [predDiag_mul_same]
      _ = P₁ * (U₁ * U₁ᴴ) := by rw [hc₁, Matrix.mul_assoc]
      _ = P₁ := by rw [hU₁, Matrix.mul_one]
  have ht2 : U₁ * P₁ * (P₀ * U₀ᴴ) = 0 := by
    calc U₁ * P₁ * (P₀ * U₀ᴴ)
        = U₁ * (P₁ * P₀) * U₀ᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [predDiag_mul_diff g (by decide), Matrix.mul_zero, Matrix.zero_mul]
  have ht3 : U₀ * P₀ * (P₁ * U₁ᴴ) = 0 := by
    calc U₀ * P₀ * (P₁ * U₁ᴴ)
        = U₀ * (P₀ * P₁) * U₁ᴴ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [predDiag_mul_diff g (by decide), Matrix.mul_zero, Matrix.zero_mul]
  have ht4 : U₀ * P₀ * (P₀ * U₀ᴴ) = P₀ := by
    calc U₀ * P₀ * (P₀ * U₀ᴴ)
        = U₀ * (P₀ * P₀) * U₀ᴴ := by simp only [Matrix.mul_assoc]
      _ = (U₀ * P₀) * U₀ᴴ := by rw [predDiag_mul_same]
      _ = P₀ * (U₀ * U₀ᴴ) := by rw [hc₀, Matrix.mul_assoc]
      _ = P₀ := by rw [hU₀, Matrix.mul_one]
  rw [ht1, ht2, ht3, ht4, add_zero, zero_add]
  exact predDiag_true_add_false g

/-- Whole-system unitary applying `V₁` on `rTarget` when `g β = true` and `V₀` when
`g β = false`. -/
noncomputable def muxPredUnitary {N t : ℕ} (rTarget : QRegister t N)
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool)
    (hg : ∀ β γ, g (writeReg β rTarget γ) = g β) : Unitary (2 ^ N) :=
  ⟨muxPredMatrix rTarget V₀ V₁ g, muxPredMatrix_mem_unitaryGroup rTarget V₀ V₁ g hg⟩

theorem muxPredUnitary_mulVec_ket {N t : ℕ} (rTarget : QRegister t N)
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool)
    (hg : ∀ β γ, g (writeReg β rTarget γ) = g β) (β : BitAssignment N) :
    (muxPredUnitary rTarget V₀ V₁ g hg).1.mulVec (ket β) =
      if g β then (rTarget.embedUnitary V₁).1.mulVec (ket β)
      else (rTarget.embedUnitary V₀).1.mulVec (ket β) := by
  change (muxPredMatrix rTarget V₀ V₁ g).mulVec (ket β) = _
  rw [muxPredMatrix, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    predDiag_mulVec_ket, predDiag_mulVec_ket]
  cases h : g β <;> simp

theorem muxPredUnitary_comm_zeroProjOn {N t : ℕ} (rTarget : QRegister t N)
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool)
    (hg : ∀ β γ, g (writeReg β rTarget γ) = g β)
    (S : Finset (Wire N)) (hdisj : Disjoint rTarget.image S) :
    (muxPredUnitary rTarget V₀ V₁ g hg).1 * zeroProjOn S =
      zeroProjOn S * (muxPredUnitary rTarget V₀ V₁ g hg).1 := by
  change muxPredMatrix rTarget V₀ V₁ g * zeroProjOn S =
    zeroProjOn S * muxPredMatrix rTarget V₀ V₁ g
  have hU₁ := embedMatrix_comm_zeroProjOn_of_disjoint rTarget S hdisj V₁.1
  have hU₀ := embedMatrix_comm_zeroProjOn_of_disjoint rTarget S hdisj V₀.1
  have hP (val : Bool) : predDiag g val * zeroProjOn S = zeroProjOn S * predDiag g val := by
    rw [predDiag, zeroProjOn, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext idx
    exact mul_comm _ _
  have ht1 : rTarget.embedMatrix V₁.1 * predDiag g true * zeroProjOn S =
      zeroProjOn S * (rTarget.embedMatrix V₁.1 * predDiag g true) := by
    rw [Matrix.mul_assoc, hP true, ← Matrix.mul_assoc, hU₁, Matrix.mul_assoc]
  have ht0 : rTarget.embedMatrix V₀.1 * predDiag g false * zeroProjOn S =
      zeroProjOn S * (rTarget.embedMatrix V₀.1 * predDiag g false) := by
    rw [Matrix.mul_assoc, hP false, ← Matrix.mul_assoc, hU₀, Matrix.mul_assoc]
  rw [muxPredMatrix, Matrix.add_mul, Matrix.mul_add, ht1, ht0]

theorem update_writeReg_comm {N t : ℕ} (β : BitAssignment N) (rTarget : QRegister t N)
    (γ : BitAssignment t) (q : Wire N) (hq : q ∉ rTarget.image) (val : ZMod 2) :
    Function.update (writeReg β rTarget γ) q val =
      writeReg (Function.update β q val) rTarget γ := by
  have hq_range : q ∉ Set.range rTarget.wires := by
    rintro ⟨i, rfl⟩
    exact hq (by rw [QRegister.mem_image]; exact ⟨i, rfl⟩)
  funext w
  by_cases hw : w ∈ Set.range rTarget.wires
  · obtain ⟨i, rfl⟩ := hw
    have hne : rTarget i ≠ q := fun h ↦ hq_range ⟨i, h⟩
    rw [Function.update_of_ne hne, writeReg_apply_reg, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw]
    by_cases hwq : w = q
    · subst hwq
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hwq, writeReg_apply_of_not_mem _ _ _ _ hw,
        Function.update_of_ne hwq]

theorem writeReg_apply_of_not_mem_image {N t : ℕ} (β : BitAssignment N)
    (rTarget : QRegister t N) (γ : BitAssignment t) (q : Wire N) (hq : q ∉ rTarget.image) :
    writeReg β rTarget γ q = β q := by
  apply writeReg_apply_of_not_mem
  rintro ⟨i, rfl⟩
  exact hq (by rw [QRegister.mem_image]; exact ⟨i, rfl⟩)

theorem circuit_eval_comm_embedMatrix_of_disjoint {N t : ℕ} (c : Circuit N)
    (rTarget : QRegister t N) (hdisj : Disjoint c.support rTarget.image)
    (A : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ) :
    c.eval.1 * rTarget.embedMatrix A = rTarget.embedMatrix A * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g r =>
      have hr : r.DisjointWires rTarget := by
        rw [QRegister.disjoint_iff]
        intro i j heq
        exact Finset.disjoint_left.mp hdisj
          (by rw [Circuit.support_gate, QRegister.mem_image]; exact ⟨i, rfl⟩)
          (by rw [QRegister.mem_image]; exact ⟨j, heq.symm⟩)
      exact r.embedMatrix_comm_of_disjoint rTarget hr g.eval.1 A
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]

theorem x_eval_mul_self {N : ℕ} (q : Wire N) :
    (Circuit.X q).eval * (Circuit.X q).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_X, Function.update_self, Function.update_idem]
  rw [add_assoc, one_add_one_zmod2, add_zero, Function.update_eq_self]

theorem cnot_eval_mul_self {N : ℕ} (c d : Wire N) (hcd : c ≠ d) :
    (Circuit.CNOT c d hcd).eval * (Circuit.CNOT c d hcd).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_CNOT, Function.update_self, Function.update_of_ne hcd, Function.update_idem]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]

theorem conj_selfInv_muxPredUnitary_mulVec_ket {N t : ℕ} (G : Circuit N)
    (hG_sq : G.eval * G.eval = 1)
    (rTarget : QRegister t N) (hdisj : Disjoint G.support rTarget.image)
    (π : BitAssignment N → BitAssignment N)
    (hket : ∀ β, G.eval.1.mulVec (ket β) = ket (π β))
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool)
    (hg : ∀ β γ, g (writeReg β rTarget γ) = g β)
    (hg' : ∀ β γ, g (π (writeReg β rTarget γ)) = g (π β))
    (β : BitAssignment N) :
    ((G.eval * muxPredUnitary rTarget V₀ V₁ g hg) * G.eval).1.mulVec (ket β) =
      (muxPredUnitary rTarget V₀ V₁ (fun β ↦ g (π β)) hg').1.mulVec (ket β) := by
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [hket β, muxPredUnitary_mulVec_ket, muxPredUnitary_mulVec_ket]
  let Vb : Unitary (2 ^ t) := if g (π β) then V₁ else V₀
  have hVb_left :
      (if g (π β) then (rTarget.embedUnitary V₁).1.mulVec (ket (π β))
        else (rTarget.embedUnitary V₀).1.mulVec (ket (π β))) =
      (rTarget.embedUnitary Vb).1.mulVec (ket (π β)) := by
    dsimp [Vb]; split_ifs <;> rfl
  have hVb_right :
      (if g (π β) then (rTarget.embedUnitary V₁).1.mulVec (ket β)
        else (rTarget.embedUnitary V₀).1.mulVec (ket β)) =
      (rTarget.embedUnitary Vb).1.mulVec (ket β) := by
    dsimp [Vb]; split_ifs <;> rfl
  rw [hVb_left, hVb_right, ← hket β, Matrix.mulVec_mulVec, QRegister.embedUnitary_val,
    circuit_eval_comm_embedMatrix_of_disjoint G rTarget hdisj Vb.1]
  have hsq_val : G.eval.1 * G.eval.1 = 1 := congrArg Subtype.val hG_sq
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hsq_val, Matrix.mul_one]

theorem localIdx_writeReg_of_disjoint {N d t : ℕ} (rData : QRegister d N)
    (rTarget : QRegister t N) (hDT : rData.DisjointWires rTarget)
    (β : BitAssignment N) (γ : BitAssignment t) :
    localIdx rData (writeReg β rTarget γ) = localIdx rData β := by
  unfold localIdx
  congr 1
  funext i
  apply writeReg_apply_of_not_mem
  rintro ⟨j, hj⟩
  exact hDT.ne i j hj.symm

theorem regVal_writeReg_of_disjoint {N d t : ℕ} (rData : QRegister d N)
    (rTarget : QRegister t N) (hDT : rData.DisjointWires rTarget)
    (β : BitAssignment N) (γ : BitAssignment t) :
    regVal rData (writeReg β rTarget γ) = regVal rData β :=
  congrArg Fin.val (localIdx_writeReg_of_disjoint rData rTarget hDT β γ)

end ComparatorProofs

/-- Block-diagonal `(d + t)`-qubit unitary applying `V₁` on the `t`-qubit right subregister when
`pred x = true` on the `d`-qubit left subregister `x : Fin (2 ^ d)`, and `V₀` when
`pred x = false`. -/
noncomputable def muxPredLocalUnitary {d t : ℕ} (pred : Fin (2 ^ d) → Bool)
    (V₀ V₁ : Unitary (2 ^ t)) : Unitary (2 ^ (d + t)) :=
  let rLeft : QRegister d (d + t) := QRegister.block 0 d (by omega)
  let rRight : QRegister t (d + t) := QRegister.block d t (by omega)
  have hLR : rLeft.DisjointWires rRight := by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hv := congrArg Fin.val h
    simp only [rLeft, rRight, QRegister.block_apply_val] at hv
    omega
  ComparatorProofs.muxPredUnitary rRight V₀ V₁ (fun γ ↦ pred (localIdx rLeft γ))
    (fun β γ ↦ congrArg pred (ComparatorProofs.localIdx_writeReg_of_disjoint rLeft rRight hLR β γ))

/-- `(1 + t)`-qubit single-bit-multiplexed unitary applying `V₀` when wire `0` is `0` and `V₁`
when wire `0` is `1`. -/
noncomputable abbrev muxBitLocalUnitary {t : ℕ} (V₀ V₁ : Unitary (2 ^ t)) :
    Unitary (2 ^ (1 + t)) :=
  muxPredLocalUnitary (fun b : Fin (2 ^ 1) ↦ decide (b.val = 1)) V₀ V₁

namespace ComparatorProofs

theorem embedUnitary_muxPredLocalUnitary {N d t : ℕ}
    (rData : QRegister d N) (rTarget : QRegister t N) (hDT : rData.DisjointWires rTarget)
    (pred : Fin (2 ^ d) → Bool) (V₀ V₁ : Unitary (2 ^ t)) :
    ((rData.concat rTarget hDT).embedUnitary (muxPredLocalUnitary pred V₀ V₁)) =
      muxPredUnitary rTarget V₀ V₁ (fun β ↦ pred (localIdx rData β))
        (fun β γ ↦ congrArg pred (localIdx_writeReg_of_disjoint rData rTarget hDT β γ)) := by
  apply Subtype.ext
  let rDT := rData.concat rTarget hDT
  let rLeft : QRegister d (d + t) := QRegister.block 0 d (by omega)
  let rRight : QRegister t (d + t) := QRegister.block d t (by omega)
  have hcompL : rDT.compose rLeft = rData := by
    apply QRegister.ext
    apply Function.Embedding.ext
    intro i
    have hidx : rLeft i = Fin.castAdd t i := Fin.ext (by simp [rLeft])
    change rDT (rLeft i) = rData i
    rw [hidx, QRegister.concat_apply_left]
  have hcompR : rDT.compose rRight = rTarget := by
    apply QRegister.ext
    apply Function.Embedding.ext
    intro j
    have hidx : rRight j = Fin.natAdd d j := Fin.ext (by simp [rRight])
    change rDT (rRight j) = rTarget j
    rw [hidx, QRegister.concat_apply_right]
  have hdiag (val : Bool) :
      predDiag (fun γ : BitAssignment (d + t) ↦ pred (localIdx rLeft γ)) val =
        rLeft.embedMatrix (Matrix.diagonal fun x ↦ if pred x = val then (1 : ℂ) else 0) := by
    rw [rLeft.embedMatrix_diagonal]
    rfl
  change rDT.embedMatrix (muxPredMatrix rRight V₀ V₁ _) = muxPredMatrix rTarget V₀ V₁ _
  rw [muxPredMatrix, muxPredMatrix, hdiag true, hdiag false,
    rDT.embedMatrix_add, rDT.embedMatrix_mul, rDT.embedMatrix_mul,
    ← rDT.embedMatrix_compose, ← rDT.embedMatrix_compose,
    ← rDT.embedMatrix_compose, ← rDT.embedMatrix_compose,
    hcompL, hcompR, rData.embedMatrix_diagonal, rData.embedMatrix_diagonal]
  rfl

/-- Clean-wire predicate realization invariant for reversible boolean flag compute-body-uncompute
trees. -/
def PredRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N t : ℕ} [NeZero (2 ^ N)]
    (v : Var) (S : Finset (Wire N)) (rTarget : QRegister t N)
    (V₀ V₁ : Unitary (2 ^ t)) (g : BitAssignment N → Bool)
    (P : DynamicCircuit Var N) : Prop :=
  Disjoint rTarget.image S ∧
  ∃ hg : ∀ β γ, g (writeReg β rTarget γ) = g β,
    CleanRealizesWires v S (muxPredUnitary rTarget V₀ V₁ g hg) P

namespace PredRealizes

variable {Var : Type} [Fintype Var] [DecidableEq Var] {N t : ℕ} [NeZero (2 ^ N)]

theorem congr_pred {v : Var} {S : Finset (Wire N)} {rTarget : QRegister t N}
    {V₀ V₁ : Unitary (2 ^ t)} {g g' : BitAssignment N → Bool}
    {P : DynamicCircuit Var N}
    (h : PredRealizes v S rTarget V₀ V₁ g P)
    (hg' : ∀ β γ, g' (writeReg β rTarget γ) = g' β)
    (heq : ∀ β : BitAssignment N, (∀ q ∈ S, β q = 0) → g β = g' β) :
    PredRealizes v S rTarget V₀ V₁ g' P := by
  obtain ⟨hdisj, hg, hw⟩ := h
  refine ⟨hdisj, hg',
    hw.congr_unitary ?_ (muxPredUnitary_comm_zeroProjOn rTarget V₀ V₁ g' hg' S hdisj)⟩
  apply matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
  by_cases hS : ∀ q ∈ S, β q = 0
  · rw [ite_eq_left hS, muxPredUnitary_mulVec_ket, muxPredUnitary_mulVec_ket, heq β hS]
  · rw [ite_eq_right hS, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem conjX {v : Var} {S : Finset (Wire N)} {rTarget : QRegister t N}
    {V₀ V₁ : Unitary (2 ^ t)} {g : BitAssignment N → Bool}
    {mid : DynamicCircuit Var N}
    (q : Wire N) (hqT : q ∉ rTarget.image) (hqS : q ∉ S)
    (hmid : PredRealizes v S rTarget V₀ V₁ g mid) :
    PredRealizes v S rTarget V₀ V₁
      (fun β ↦ g (Function.update β q (β q + 1)))
      (conjXDyn q mid) := by
  obtain ⟨hdisj, hg, hw⟩ := hmid
  have hg' : ∀ β γ, g (Function.update (writeReg β rTarget γ) q
      (writeReg β rTarget γ q + 1)) = g (Function.update β q (β q + 1)) := fun β γ ↦ by
    rw [writeReg_apply_of_not_mem_image β rTarget γ q hqT,
      update_writeReg_comm β rTarget γ q hqT, hg]
  refine ⟨hdisj, hg', ?_⟩
  have hx : CleanRealizesWires v S (Circuit.X q).eval (.circuit (Circuit.X q)) :=
    CleanRealizesWires.circuit v S (Circuit.X q) (by simp [Circuit.X])
      (by rw [Circuit.support_single, Finset.disjoint_singleton_left]; exact hqS)
  have hseq := hx.seq (hw.seq hx)
  have heval :
      ((Circuit.X q).eval * muxPredUnitary rTarget V₀ V₁ g hg) * (Circuit.X q).eval =
        muxPredUnitary rTarget V₀ V₁ (fun β ↦ g (Function.update β q (β q + 1))) hg' := by
    apply Subtype.ext
    apply matrix_ext_ket
    intro β
    exact conj_selfInv_muxPredUnitary_mulVec_ket (Circuit.X q) (x_eval_mul_self q)
      rTarget (by rw [Circuit.support_single, Finset.disjoint_singleton_left]; exact hqT)
      _ (ket_X q) V₀ V₁ g hg hg' β
  rwa [heval] at hseq

theorem conjCNOT {v : Var} {S : Finset (Wire N)} {rTarget : QRegister t N}
    {V₀ V₁ : Unitary (2 ^ t)} {g : BitAssignment N → Bool}
    {mid : DynamicCircuit Var N}
    (c d : Wire N) (hcd : c ≠ d)
    (hcT : c ∉ rTarget.image) (hdT : d ∉ rTarget.image)
    (hcS : c ∉ S) (hdS : d ∉ S)
    (hmid : PredRealizes v S rTarget V₀ V₁ g mid) :
    PredRealizes v S rTarget V₀ V₁
      (fun β ↦ g (Function.update β d (β d + β c)))
      (conjCNOTDyn c d hcd mid) := by
  obtain ⟨hdisj, hg, hw⟩ := hmid
  have hg' : ∀ β γ, g (Function.update (writeReg β rTarget γ) d
      (writeReg β rTarget γ d + writeReg β rTarget γ c)) =
      g (Function.update β d (β d + β c)) := fun β γ ↦ by
    rw [writeReg_apply_of_not_mem_image β rTarget γ d hdT,
      writeReg_apply_of_not_mem_image β rTarget γ c hcT,
      update_writeReg_comm β rTarget γ d hdT, hg]
  refine ⟨hdisj, hg', ?_⟩
  have hdisjS : Disjoint (Circuit.CNOT c d hcd).support S := by
    rw [Circuit.support_cnot, Finset.disjoint_left]
    intro w hw' hwS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
    rcases hw' with rfl | rfl
    · exact hcS hwS
    · exact hdS hwS
  have hdisjT : Disjoint (Circuit.CNOT c d hcd).support rTarget.image := by
    rw [Circuit.support_cnot, Finset.disjoint_left]
    intro w hw' hwT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
    rcases hw' with rfl | rfl
    · exact hcT hwT
    · exact hdT hwT
  have hcnot := CleanRealizesWires.circuit v S (Circuit.CNOT c d hcd)
    (by simp [Circuit.CNOT]) hdisjS
  have hseq := hcnot.seq (hw.seq hcnot)
  have heval :
      ((Circuit.CNOT c d hcd).eval * muxPredUnitary rTarget V₀ V₁ g hg) *
          (Circuit.CNOT c d hcd).eval =
        muxPredUnitary rTarget V₀ V₁ (fun β ↦ g (Function.update β d (β d + β c))) hg' := by
    apply Subtype.ext
    apply matrix_ext_ket
    intro β
    exact conj_selfInv_muxPredUnitary_mulVec_ket (Circuit.CNOT c d hcd)
      (cnot_eval_mul_self c d hcd) rTarget hdisjT _ (ket_CNOT c d hcd) V₀ V₁ g hg hg' β
  rwa [heval] at hseq

theorem andSandwich {v : Var} {S : Finset (Wire N)} {rTarget : QRegister t N}
    {V₀ V₁ : Unitary (2 ^ t)} {g : BitAssignment N → Bool}
    {mid : DynamicCircuit Var N}
    (c₁ c₂ anc : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hc₁T : c₁ ∉ rTarget.image) (hc₂T : c₂ ∉ rTarget.image) (haT : anc ∉ rTarget.image)
    (hc₁S : c₁ ∉ S) (hc₂S : c₂ ∉ S) (haS : anc ∉ S)
    (hmid : PredRealizes v S rTarget V₀ V₁ g mid) :
    PredRealizes v (insert anc S) rTarget V₀ V₁
      (fun β ↦ g (Function.update β anc (β c₁ * β c₂)))
      (Comparators.andSandwich v c₁ c₂ anc h₁₂ h₁a h₂a mid) := by
  obtain ⟨hdisj, hg, hw⟩ := hmid
  have hg' : ∀ β γ, g (Function.update (writeReg β rTarget γ) anc
      (writeReg β rTarget γ c₁ * writeReg β rTarget γ c₂)) =
      g (Function.update β anc (β c₁ * β c₂)) := fun β γ ↦ by
    rw [writeReg_apply_of_not_mem_image β rTarget γ c₁ hc₁T,
      writeReg_apply_of_not_mem_image β rTarget γ c₂ hc₂T,
      update_writeReg_comm β rTarget γ anc haT, hg]
  have hdisj_ins : Disjoint rTarget.image (insert anc S) :=
    Finset.disjoint_insert_right.mpr ⟨haT, hdisj⟩
  refine ⟨hdisj_ins, hg', ?_⟩
  have hdisj_toffT : Disjoint (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).support rTarget.image := by
    rw [Circuit.support_toffoli, Finset.disjoint_left]
    intro w hw' hwT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
    rcases hw' with rfl | rfl | rfl
    · exact hc₁T hwT
    · exact hc₂T hwT
    · exact haT hwT
  refine CleanRealizesWires.andSandwich c₁ c₂ anc h₁₂ h₁a h₂a hc₁S hc₂S haS hw ?_ ?_ ?_
  · apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      singleton_basisOutcomeProjector_zero_eq, zeroProjOn_mulVec_ket]
    by_cases h0 : ∀ q ∈ ({anc} : Finset (Wire N)), β q = 0
    · have hanc0 : β anc = 0 := h0 anc (Finset.mem_singleton_self _)
      rw [ite_eq_left h0]
      have hconj := conj_selfInv_muxPredUnitary_mulVec_ket
        (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a)
        (toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a)
        rTarget hdisj_toffT
        (fun δ ↦ Function.update δ anc (δ anc + δ c₁ * δ c₂))
        (ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a) V₀ V₁ g hg
        (fun δ γ ↦ by
          rw [writeReg_apply_of_not_mem_image δ rTarget γ anc haT,
            writeReg_apply_of_not_mem_image δ rTarget γ c₁ hc₁T,
            writeReg_apply_of_not_mem_image δ rTarget γ c₂ hc₂T,
            update_writeReg_comm δ rTarget γ anc haT, hg])
        β
      rw [hconj, muxPredUnitary_mulVec_ket, muxPredUnitary_mulVec_ket, hanc0, zero_add]
    · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  · rw [singleton_basisOutcomeProjector_zero_eq]
    exact muxPredUnitary_comm_zeroProjOn rTarget V₀ V₁ _ hg' {anc}
      (Finset.disjoint_singleton_right.mpr haT)
  · exact muxPredUnitary_comm_zeroProjOn rTarget V₀ V₁ _ hg' S hdisj

theorem of_muxBitBody {s : ℕ} {v : Var}
    (wFlag : Wire N) (rTarget : QRegister t N) (rBodyScr : QRegister s N)
    (hFT : (QRegister.singleton wFlag).DisjointWires rTarget)
    (hFS : ∀ j, wFlag ≠ rBodyScr j)
    (hTS : rTarget.DisjointWires rBodyScr)
    {V₀ V₁ : Unitary (2 ^ t)} {body : DynamicCircuit Var N}
    (hbody : CleanRealizes v ((QRegister.singleton wFlag).concat rTarget hFT)
      rBodyScr (muxBitLocalUnitary V₀ V₁) body) :
    PredRealizes v rBodyScr.image rTarget V₀ V₁
      (fun β ↦ decide (β wFlag = 1)) body := by
  have hwF : wFlag ∉ rTarget.image := by
    rw [QRegister.mem_image]
    rintro ⟨i, hi⟩
    exact hFT.ne 0 i hi.symm
  have hdisj_TS : Disjoint rTarget.image rBodyScr.image := by
    rw [Finset.disjoint_left]
    intro q hqT hqS
    rw [QRegister.mem_image] at hqT hqS
    obtain ⟨i, rfl⟩ := hqT
    obtain ⟨j, hj⟩ := hqS
    exact hTS.ne i j hj.symm
  have hdisj_act : ((QRegister.singleton wFlag).concat rTarget hFT).DisjointWires rBodyScr := by
    rw [QRegister.disjoint_iff]
    intro a b
    rcases fin_eq_castAdd_or_natAdd a with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · fin_cases i
      rw [QRegister.concat_apply_left]
      exact hFS b
    · rw [QRegister.concat_apply_right]
      exact hTS.ne i b
  have hwires := CleanRealizesWires.ofCleanRealizes hdisj_act hbody
  rw [embedUnitary_muxPredLocalUnitary (QRegister.singleton wFlag) rTarget hFT] at hwires
  refine congr_pred ⟨hdisj_TS, _, hwires⟩
    (fun β γ ↦ by rw [writeReg_apply_of_not_mem_image β rTarget γ wFlag hwF]) fun β _ ↦ ?_
  have hloc : localIdx (QRegister.singleton wFlag) β = if β wFlag = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β wFlag)
  change decide ((localIdx (QRegister.singleton wFlag) β).val = 1) = decide (β wFlag = 1)
  rw [hloc]
  rcases bit_cases (β wFlag) with hb | hb <;> simp [hb]

theorem toCleanRealizes {d s : ℕ} {v : Var}
    (rData : QRegister d N) (rTarget : QRegister t N) (rTotalScr : QRegister s N)
    (hDT : rData.DisjointWires rTarget)
    (pred : Fin (2 ^ d) → Bool)
    {V₀ V₁ : Unitary (2 ^ t)} {P : DynamicCircuit Var N}
    (h : PredRealizes v rTotalScr.image rTarget V₀ V₁
      (fun β ↦ pred (localIdx rData β)) P) :
    CleanRealizes v (rData.concat rTarget hDT) rTotalScr
      (muxPredLocalUnitary pred V₀ V₁) P := by
  obtain ⟨_, hg, hw⟩ := h
  apply CleanRealizesWires.toCleanRealizes
  rw [embedUnitary_muxPredLocalUnitary]
  exact hw

end PredRealizes

end ComparatorProofs

/-! ### 4a. Quantum-Quantum Unsigned `<` Comparator (`4 * w` `T` Compute / `0` `T` Uncompute) -/

/-- Initial LSB borrow step `(a_0, b_0) ↦ c_1 = (a_0 + 1) * b_0` around `next` (`4` `T` compute,
`0` `T` uncompute), restoring `wA` before `next` executes. -/
def ltFirstStepDyn {Var : Type} {N : ℕ} (v : Var) (wA wB wCout : Wire N)
    (hAB : wA ≠ wB) (hAO : wA ≠ wCout) (hBO : wB ≠ wCout)
    (next : DynamicCircuit Var N) : DynamicCircuit Var N :=
  conjXDyn wA (andSandwich v wA wB wCout hAB hAO hBO (conjXDyn wA next))

@[simp]
theorem count_ltFirstStepDyn_toff {Var : Type} {N : ℕ} (v : Var) (wA wB wCout : Wire N)
    (hAB : wA ≠ wB) (hAO : wA ≠ wCout) (hBO : wB ≠ wCout) (next : DynamicCircuit Var N) :
    (ltFirstStepDyn v wA wB wCout hAB hAO hBO next).count PrimitiveGate.TOFF =
      next.count PrimitiveGate.TOFF := by
  simp [ltFirstStepDyn]

@[simp]
theorem count_ltFirstStepDyn_t {Var : Type} {N : ℕ} (v : Var) (wA wB wCout : Wire N)
    (hAB : wA ≠ wB) (hAO : wA ≠ wCout) (hBO : wB ≠ wCout) (next : DynamicCircuit Var N) :
    (ltFirstStepDyn v wA wB wCout hAB hAO hBO next).count PrimitiveGate.T =
      4 + next.count PrimitiveGate.T := by
  simp [ltFirstStepDyn]

namespace LtProofs

theorem predRealizes_ltFirstStepDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N t : ℕ} [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)}
    {rTarget : QRegister t N} {V₀ V₁ : Unitary (2 ^ t)}
    {g : BitAssignment N → Bool}
    {next : DynamicCircuit Var N}
    (wA wB wCout : Wire N)
    (hAB : wA ≠ wB) (hAO : wA ≠ wCout) (hBO : wB ≠ wCout)
    (hAT : wA ∉ rTarget.image) (hBT : wB ∉ rTarget.image) (hOT : wCout ∉ rTarget.image)
    (hAS : wA ∉ S) (hBS : wB ∉ S) (hOS : wCout ∉ S)
    (hnext : ComparatorProofs.PredRealizes v S rTarget V₀ V₁ g next) :
    ComparatorProofs.PredRealizes v (insert wCout S) rTarget V₀ V₁
      (fun β ↦ g (Function.update β wCout ((β wA + 1) * β wB)))
      (ltFirstStepDyn v wA wB wCout hAB hAO hBO next) := by
  have ⟨_, hg, _⟩ := hnext
  unfold ltFirstStepDyn
  have h1 := hnext.conjX wA hAT hAS
  have h2 := h1.andSandwich wA wB wCout hAB hAO hBO hAT hBT hOT hAS hBS hOS
  have h3 := h2.conjX wA hAT (by simp [hAO, hAS])
  refine h3.congr_pred
    (fun β γ ↦ by
      rw [ComparatorProofs.writeReg_apply_of_not_mem_image β rTarget γ wA hAT,
        ComparatorProofs.writeReg_apply_of_not_mem_image β rTarget γ wB hBT,
        ComparatorProofs.update_writeReg_comm β rTarget γ wCout hOT, hg])
    fun β _ ↦ ?_
  congr 1
  funext q
  by_cases hqO : q = wCout
  · subst hqO
    simp [Function.update_of_ne hAO.symm, Function.update_of_ne hAB.symm]
  · by_cases hqA : q = wA
    · subst hqA
      simp only [Function.update_of_ne hqO, Function.update_self]
      rw [add_assoc, one_add_one_zmod2, add_zero]
    · simp [Function.update_of_ne hqO, Function.update_of_ne hqA]

end LtProofs

section AddCleanWires

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
  | circuit c =>
      intro σ
      exact HermitianMat.conj_mono (h σ)
  | measure x r =>
      intro σ
      exact Finset.sum_le_sum fun o _ ↦ HermitianMat.conj_mono (h _)
  | qIf b t f iht ihf =>
      intro σ
      by_cases hb : b.holds σ <;> simp [hb, iht h σ, ihf h σ]
  | seq p₁ p₂ ih₁ ih₂ =>
      exact ih₁ (ih₂ h)

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
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
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

private noncomputable def zeroObsOn {n : ℕ} (S : Finset (Wire n)) : Observable (Fin (2 ^ n)) :=
  ⟨(1 : HermitianMat (Fin (2 ^ n)) ℂ).conj (zeroProjOn S),
    (1 : HermitianMat (Fin (2 ^ n)) ℂ).conj_nonneg (zeroProjOn S) zero_le_one,
    HermitianMat.conj_one_le_one (zeroProjOn S) (zeroProjOn_le_one S)⟩

private theorem zeroObsOn_mat {n : ℕ} (S : Finset (Wire n)) :
    (zeroObsOn S).1.mat = zeroProjOn S := by
  simp [zeroObsOn, conj_apply_mat, zeroProjOn_conjTranspose, zeroProjOn_mul_self]

private theorem obs_sub_conj_zeroProjOn_bounds {n : ℕ} (S : Finset (Wire n))
    (M : Observable (Fin (2 ^ n))) (t : ℝ) (ht : 0 < t) :
    -(t ^ 2 • (1 : HermitianMat (Fin (2 ^ n)) ℂ) +
        (2 + t⁻¹ ^ 2) • (1 - (zeroObsOn S).1)) ≤
      M.1 - M.1.conj (zeroProjOn S) ∧
    M.1 - M.1.conj (zeroProjOn S) ≤
      t ^ 2 • (1 : HermitianMat (Fin (2 ^ n)) ℂ) +
        (1 + t⁻¹ ^ 2) • (1 - (zeroObsOn S).1) := by
  let P := zeroProjOn S
  let Q_herm : HermitianMat (Fin (2 ^ n)) ℂ := 1 - (zeroObsOn S).1
  let Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := 1 - P
  have hP_herm : Pᴴ = P := zeroProjOn_conjTranspose S
  have hP_idem : P * P = P := zeroProjOn_mul_self S
  have hQ_herm : Qᴴ = Q := by simp [Q, hP_herm]
  have hPQ_sum : P + Q = 1 := by simp [Q]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hclean_mat : (zeroObsOn S).1.mat = P := zeroObsOn_mat S
  have hconjP_le : M.1.conj P ≤ 1 :=
    (HermitianMat.conj_mono M.2.2).trans (zeroObsOn S).2.2
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

private theorem restrictZeroWires_wp_restrict_eq_of_clean
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (S : Finset (Wire n)) (U : Unitary (2 ^ n))
    (hcomm : U.1 * zeroProjOn S = zeroProjOn S * U.1)
    (P : DynamicCircuit Var n)
    (hclean : ∀ M : Observable (Fin (2 ^ n)),
      restrictZeroWires (wp P.compile (fun _ ↦ M)) S =
        restrictZeroWires (qcWpQAssign U (fun _ ↦ M)) S)
    (Θ : QCAssertion Var (2 ^ n)) :
    restrictZeroWires (wp P.compile (restrictZeroWires Θ S)) S =
      restrictZeroWires (wp P.compile Θ) S := by
  funext σ
  apply Subtype.ext
  let P₀ := zeroProjOn S
  let Q_obs : Observable (Fin (2 ^ n)) :=
    ⟨1 - (zeroObsOn S).1, sub_nonneg.mpr (zeroObsOn S).2.2,
      sub_le_self 1 (zeroObsOn S).2.1⟩
  have hQ_zero : (wpHerm P (fun _ ↦ Q_obs.1) σ).conj P₀ = 0 := by
    have hwpQ := congrArg (fun A ↦ (A σ).1) (hclean Q_obs)
    dsimp only [restrictZeroWires_coe] at hwpQ
    rw [← congrFun (wpHerm_eq_wp P (fun _ ↦ Q_obs)) σ] at hwpQ
    rw [hwpQ]
    ext1
    have hP₀_idem : P₀ * P₀ = P₀ := zeroProjOn_mul_self S
    have hclean_mat : (zeroObsOn S).1.mat = P₀ := zeroObsOn_mat S
    have hcomm' : U.1 * P₀ = P₀ * U.1 := hcomm
    have hcommH : P₀ * U.1ᴴ = U.1ᴴ * P₀ := by
      have h := congrArg conjTranspose hcomm
      simpa only [P₀, conjTranspose_mul, zeroProjOn_conjTranspose] using h
    simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_apply_mat, Q_obs, HermitianMat.mat_sub,
      HermitianMat.mat_one, hclean_mat, zeroProjOn_conjTranspose, conjTranspose_conjTranspose,
      HermitianMat.mat_zero]
    calc P₀ * (U.1ᴴ * (1 - P₀) * U.1) * P₀
      _ = (P₀ * U.1ᴴ) * (1 - P₀) * (U.1 * P₀) := by simp only [Matrix.mul_assoc]
      _ = U.1ᴴ * (P₀ * (1 - P₀) * P₀) * U.1 := by
          rw [hcommH, hcomm']; simp only [Matrix.mul_assoc]
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
    have hb := fun σ' ↦ obs_sub_conj_zeroProjOn_bounds S (Θ σ') t ht
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
  have hB := congrFun (wpHerm_eq_wp P (restrictZeroWires Θ S)) σ
  dsimp [A, B] at hEq
  simpa only [restrictZeroWires_coe, ← hA, ← hB] using hEq

/-- Enlarge the clean-wire set `S` to `S ∪ T` whenever `U` preserves `|0⟩` on `T`, even when `P`
physically touches wires in `T` (e.g. a clean flag wire read as `0` by `P`). -/
theorem CleanRealizesWires.add_wires {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)} (T : Finset (Wire N))
    {U : Unitary (2 ^ N)} {P : DynamicCircuit Var N}
    (h : CleanRealizesWires v S U P)
    (hU_comm : U.1 * zeroProjOn T = zeroProjOn T * U.1) :
    CleanRealizesWires v (S ∪ T) U P := by
  have hUT : U.1 * zeroProjOn (S ∪ T) = zeroProjOn (S ∪ T) * U.1 := by
    rw [zeroProjOn_union, ← Matrix.mul_assoc, h.2.2.2.2, Matrix.mul_assoc, hU_comm,
      ← Matrix.mul_assoc]
  have h3 : ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      restrictZeroWires (wp P.compile Θ) (S ∪ T) =
        restrictZeroWires (qcWpQAssign U Θ) (S ∪ T) := by
    intro Θ hΘ
    rw [← restrictZeroWires_union, ← restrictZeroWires_union, h.2.2.1 Θ hΘ]
  exact ⟨h.1, h.2.1, h3,
    restrictZeroWires_wp_restrict_eq_of_clean (S ∪ T) U hUT P
      (fun M ↦ h3 (fun _ ↦ M) (fun _ _ ↦ rfl)),
    hUT⟩

theorem ComparatorProofs.PredRealizes.add_clean {Var : Type} [Fintype Var] [DecidableEq Var]
    {N t : ℕ} [NeZero (2 ^ N)] {v : Var} {S : Finset (Wire N)} (T : Finset (Wire N))
    {rTarget : QRegister t N} {V₀ V₁ : Unitary (2 ^ t)}
    {g : BitAssignment N → Bool} {P : DynamicCircuit Var N}
    (h : ComparatorProofs.PredRealizes v S rTarget V₀ V₁ g P)
    (hdisjT : Disjoint rTarget.image T) :
    ComparatorProofs.PredRealizes v (S ∪ T) rTarget V₀ V₁ g P := by
  obtain ⟨hdisjS, hg, hw⟩ := h
  exact ⟨Finset.disjoint_union_right.mpr ⟨hdisjS, hdisjT⟩, hg,
    hw.add_wires T (ComparatorProofs.muxPredUnitary_comm_zeroProjOn rTarget V₀ V₁ g hg T hdisjT)⟩

theorem ComparatorProofs.PredRealizes.add_clean_subset {Var : Type} [Fintype Var] [DecidableEq Var]
    {N t : ℕ} [NeZero (2 ^ N)] {v : Var} {S S' : Finset (Wire N)}
    {rTarget : QRegister t N} {V₀ V₁ : Unitary (2 ^ t)}
    {g : BitAssignment N → Bool} {P : DynamicCircuit Var N}
    (h : ComparatorProofs.PredRealizes v S rTarget V₀ V₁ g P)
    (hsub : S ⊆ S')
    (hdisj' : Disjoint rTarget.image S') :
    ComparatorProofs.PredRealizes v S' rTarget V₀ V₁ g P := by
  rw [← Finset.union_sdiff_of_subset hsub]
  exact h.add_clean (S' \ S) (Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj')

end AddCleanWires

namespace ComparatorProofs

theorem nat_eq_of_bits_eq {k x y : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (hb : ∀ i < k, (x / 2 ^ i) % 2 = (y / 2 ^ i) % 2) : x = y := by
  induction k generalizing x y with
  | zero =>
      simp only [Nat.pow_zero] at hx hy
      omega
  | succ k ih =>
      have h0 := hb 0 (by omega)
      simp only [Nat.pow_zero, Nat.div_one] at h0
      have hdiv : x / 2 = y / 2 := by
        refine ih (by rw [pow_succ'] at hx; omega) (by rw [pow_succ'] at hy; omega) fun i hi ↦ ?_
        have hbi := hb (i + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at hbi
      omega

theorem nat_mod_pow_div_pow_mod_two {width z i : ℕ} (hi : i < width) :
    (z % 2 ^ width / 2 ^ i) % 2 = (z / 2 ^ i) % 2 := by
  have hw : width = i + 1 + (width - 1 - i) := by omega
  have hpow : 2 ^ width = 2 ^ i * (2 * 2 ^ (width - 1 - i)) := by
    conv_lhs => rw [hw]
    rw [Nat.pow_add, Nat.pow_add, pow_one]
    ring
  have hz : z = z % 2 ^ width + 2 ^ i * (2 * (2 ^ (width - 1 - i) * (z / 2 ^ width))) := by
    calc z = 2 ^ width * (z / 2 ^ width) + z % 2 ^ width := (Nat.div_add_mod z (2 ^ width)).symm
      _ = (2 ^ i * (2 * 2 ^ (width - 1 - i))) * (z / 2 ^ width) + z % 2 ^ width := by
          conv_lhs => arg 1; arg 1; rw [hpow]
      _ = z % 2 ^ width + 2 ^ i * (2 * (2 ^ (width - 1 - i) * (z / 2 ^ width))) := by ring
  conv_rhs => rw [hz]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem regVal_slice {N w offset width : ℕ} (r : QRegister w N) (h : offset + width ≤ w)
    (β : BitAssignment N) :
    regVal (r.slice offset width h) β = (regVal r β / 2 ^ offset) % 2 ^ width := by
  refine nat_eq_of_bits_eq (regVal_lt _ β) (Nat.mod_lt _ (by positivity)) fun i hi ↦ ?_
  rw [regVal_div_pow_mod_two (r.slice offset width h) β hi,
    nat_mod_pow_div_pow_mod_two hi, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    regVal_div_pow_mod_two r β (by omega)]
  rfl

theorem regVal_slice_suffix {N w offset width : ℕ} (r : QRegister w N) (h : offset + width ≤ w)
    (heq : offset + width = w) (β : BitAssignment N) :
    regVal (r.slice offset width h) β = regVal r β / 2 ^ offset := by
  rw [regVal_slice]
  apply Nat.mod_eq_of_lt
  have hlt : regVal r β < 2 ^ offset * 2 ^ width := by
    calc regVal r β < 2 ^ w := regVal_lt r β
      _ = 2 ^ (offset + width) := by rw [heq]
      _ = 2 ^ offset * 2 ^ width := Nat.pow_add 2 offset width
  exact Nat.div_lt_of_lt_mul hlt

theorem regVal_width_one {N : ℕ} (r : QRegister 1 N) (β : BitAssignment N) :
    regVal r β = bitNat (β (r 0)) := by
  have hlt := regVal_lt r β
  have hb := regVal_div_pow_mod_two r β (m := 0) (by omega)
  simp only [Nat.pow_zero, Nat.div_one] at hb
  change regVal r β = bitNat (β (r ⟨0, by omega⟩))
  rw [← hb]
  omega

end ComparatorProofs

/-- Carry wire at boundary `m` (`0 ≤ m ≤ nSteps`) of an `nSteps`-bit constant chain:
`wCin0` at `m = 0`, `rInter ⟨m - 1, _⟩` for `1 ≤ m < nSteps`, and `wFlag` at `m = nSteps`. -/
def constChainWire {N nSteps : ℕ} (wCin0 : Wire N) (rInter : QRegister (nSteps - 1) N)
    (wFlag : Wire N) (m : ℕ) : Wire N :=
  if m = 0 then wCin0
  else if hm : m - 1 < nSteps - 1 then rInter ⟨m - 1, hm⟩
  else wFlag

theorem slice_ne_constChainWire {N nSteps : ℕ}
    (rSlice : QRegister nSteps N) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N)
    (hSCin : ∀ i, rSlice i ≠ wCin0)
    (hSI : rSlice.DisjointWires rInter)
    (hSF : ∀ i, rSlice i ≠ wFlag)
    (i : Fin nSteps) (k : ℕ) :
    rSlice i ≠ constChainWire wCin0 rInter wFlag k := by
  unfold constChainWire
  split_ifs with h0 hk
  · exact hSCin i
  · exact hSI.ne i ⟨k - 1, hk⟩
  · exact hSF i

theorem constChainWire_ne_succ {N nSteps : ℕ}
    (wCin0 : Wire N) (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N)
    (hCinI : ∀ j, wCin0 ≠ rInter j)
    (hCinF : wCin0 ≠ wFlag)
    (hIF : ∀ j, rInter j ≠ wFlag)
    (m : ℕ) (hm_lt : m < nSteps) :
    constChainWire wCin0 rInter wFlag m ≠
      constChainWire wCin0 rInter wFlag (m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · change wCin0 ≠ if hm : 0 < nSteps - 1 then rInter ⟨0, hm⟩ else wFlag
    split_ifs with hm
    · exact hCinI ⟨0, hm⟩
    · exact hCinF
  · have hm1 : m - 1 < nSteps - 1 := by omega
    have hleft : constChainWire wCin0 rInter wFlag m = rInter ⟨m - 1, hm1⟩ := by
      unfold constChainWire
      split_ifs with h0
      · omega
      · rfl
    have hright : constChainWire wCin0 rInter wFlag (m + 1) =
        if hm : m < nSteps - 1 then rInter ⟨m, hm⟩ else wFlag := rfl
    rw [hleft, hright]
    split_ifs with hm
    · intro heq
      have hv := congrArg Fin.val (rInter.wires.injective heq)
      dsimp at hv
      omega
    · exact hIF ⟨m - 1, hm1⟩

theorem constChainWire_last {N nSteps : ℕ} (hn : 1 ≤ nSteps)
    (wCin0 : Wire N) (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) :
    constChainWire wCin0 rInter wFlag nSteps = wFlag := by
  unfold constChainWire
  split_ifs with h0 hm
  · omega
  · omega
  · rfl

namespace ConstChainProofs

/-- Clean-ancilla wire set accumulated across the last `d` steps of a constant-carry chain. -/
def constCleanSuffix {N nSteps : ℕ} (wCin0 : Wire N) (rInter : QRegister (nSteps - 1) N)
    (wFlag : Wire N) (S₀ : Finset (Wire N)) : ℕ → Finset (Wire N)
  | 0 => S₀
  | d + 1 =>
      insert (constChainWire wCin0 rInter wFlag (nSteps - d))
        (constCleanSuffix wCin0 rInter wFlag S₀ d)

theorem mem_constCleanSuffix_iff {N nSteps : ℕ} (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (S₀ : Finset (Wire N))
    (d : ℕ) (q : Wire N) :
    q ∈ constCleanSuffix wCin0 rInter wFlag S₀ d ↔
      q ∈ S₀ ∨ ∃ d' < d, q = constChainWire wCin0 rInter wFlag (nSteps - d') := by
  induction d with
  | zero => simp [constCleanSuffix]
  | succ d ih =>
      rw [constCleanSuffix, Finset.mem_insert, ih]
      constructor
      · rintro (rfl | hS | ⟨d', hd', rfl⟩)
        · exact Or.inr ⟨d, Nat.lt_succ_self d, rfl⟩
        · exact Or.inl hS
        · exact Or.inr ⟨d', Nat.lt_succ_of_lt hd', rfl⟩
      · rintro (hS | ⟨d', hd', rfl⟩)
        · exact Or.inr (Or.inl hS)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hd' with hlt | rfl
          · exact Or.inr (Or.inr ⟨d', hlt, rfl⟩)
          · exact Or.inl rfl

theorem constCleanSuffix_full {N nSteps : ℕ} (hn : 1 ≤ nSteps) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (S₀ : Finset (Wire N)) :
    constCleanSuffix wCin0 rInter wFlag S₀ nSteps = insert wFlag (rInter.image ∪ S₀) := by
  ext q
  rw [mem_constCleanSuffix_iff, Finset.mem_insert, Finset.mem_union, QRegister.mem_image]
  constructor
  · rintro (hS | ⟨d', hd', rfl⟩)
    · exact Or.inr (Or.inr hS)
    · dsimp [constChainWire]
      split_ifs with h0 hm
      · omega
      · exact Or.inr (Or.inl ⟨⟨nSteps - d' - 1, hm⟩, rfl⟩)
      · exact Or.inl rfl
  · rintro (rfl | ⟨j, rfl⟩ | hS)
    · refine Or.inr ⟨0, hn, ?_⟩
      dsimp [constChainWire]
      split_ifs with h0 hm
      · omega
      · omega
      · rfl
    · refine Or.inr ⟨nSteps - 1 - j.val, by omega, ?_⟩
      dsimp [constChainWire]
      split_ifs with h0 hm
      · omega
      · congr 1; ext; dsimp; omega
      · omega
    · exact Or.inl hS

end ConstChainProofs

/-! ### 4b. Quantum-Constant Unsigned `<` (`≤ 4 * (w - 1)` `T` Compute / `0` `T` Uncompute) -/

theorem slice_ne_right {N w start len : ℕ} (r : QRegister w N) (h : start + len ≤ w)
    (wOut : Wire N) (hne : ∀ i, r i ≠ wOut) :
    ∀ i, (r.slice start len h) i ≠ wOut :=
  fun _ heq ↦ hne _ heq

namespace LtConstProofs

end LtConstProofs

/-- Exact `T`-gate count of `withEqConstFlagDyn` and `eqConstDyn`: `0` when `2 ^ w ≤ C`, and
`4 * (w - 1)` when `C < 2 ^ w`. -/
def eqConstTCount (w C : ℕ) : ℕ :=
  if 2 ^ w ≤ C then 0 else 4 * (w - 1)

/-- Suffix of `d` constant-equality AND steps (`m = nSteps - d .. nSteps - 1`) wrapping `body`. -/
def eqCarryUpperDyn {Var : Type} {N nSteps : ℕ} (v : Var)
    (rSlice : QRegister nSteps N) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (C_up : ℕ)
    (hSCin : ∀ i, rSlice i ≠ wCin0)
    (hSI : rSlice.DisjointWires rInter)
    (hSF : ∀ i, rSlice i ≠ wFlag)
    (hCinI : ∀ j, wCin0 ≠ rInter j)
    (hCinF : wCin0 ≠ wFlag)
    (hIF : ∀ j, rInter j ≠ wFlag)
    (body : DynamicCircuit Var N) : (d : ℕ) → d ≤ nSteps → DynamicCircuit Var N
  | 0, _ => body
  | d + 1, hd =>
      let m := nSteps - 1 - d
      have hm_lt : m < nSteps := by omega
      let wA := rSlice ⟨m, hm_lt⟩
      let wCin := constChainWire wCin0 rInter wFlag m
      let wCout := constChainWire wCin0 rInter wFlag (m + 1)
      have hAC : wA ≠ wCin :=
        slice_ne_constChainWire rSlice wCin0 rInter wFlag hSCin hSI hSF ⟨m, hm_lt⟩ m
      have hAO : wA ≠ wCout :=
        slice_ne_constChainWire rSlice wCin0 rInter wFlag hSCin hSI hSF ⟨m, hm_lt⟩ (m + 1)
      have hCO : wCin ≠ wCout :=
        constChainWire_ne_succ wCin0 rInter wFlag hCinI hCinF hIF m hm_lt
      let next := eqCarryUpperDyn v rSlice wCin0 rInter wFlag C_up
        hSCin hSI hSF hCinI hCinF hIF body d (by omega)
      if (C_up / 2 ^ m) % 2 = 0 then
        ltFirstStepDyn v wA wCin wCout hAC hAO hCO next
      else
        andSandwich v wA wCin wCout hAC hAO hCO next

/-- `nSteps`-bit constant-equality AND chain (`nSteps ≥ 1`) computing
`decide (regVal rSlice = C_up ∧ β wCin0 = 1)` onto clean `wFlag` in `4 * nSteps` `T` gates
(`0` `T` uncompute, `0` `TOFF`). -/
def eqCarryChainDyn {Var : Type} {N nSteps : ℕ} (v : Var)
    (rSlice : QRegister nSteps N) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (C_up : ℕ)
    (hSCin : ∀ i, rSlice i ≠ wCin0)
    (hSI : rSlice.DisjointWires rInter)
    (hSF : ∀ i, rSlice i ≠ wFlag)
    (hCinI : ∀ j, wCin0 ≠ rInter j)
    (hCinF : wCin0 ≠ wFlag)
    (hIF : ∀ j, rInter j ≠ wFlag)
    (body : DynamicCircuit Var N) : DynamicCircuit Var N :=
  eqCarryUpperDyn v rSlice wCin0 rInter wFlag C_up
    hSCin hSI hSF hCinI hCinF hIF body nSteps le_rfl

@[simp]
theorem count_eqCarryChainDyn_toff {Var : Type} {N nSteps : ℕ} (v : Var)
    (rSlice : QRegister nSteps N) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (C_up : ℕ)
    (hSCin : ∀ i, rSlice i ≠ wCin0) (hSI : rSlice.DisjointWires rInter)
    (hSF : ∀ i, rSlice i ≠ wFlag) (hCinI : ∀ j, wCin0 ≠ rInter j)
    (hCinF : wCin0 ≠ wFlag) (hIF : ∀ j, rInter j ≠ wFlag)
    (body : DynamicCircuit Var N) :
    (eqCarryChainDyn v rSlice wCin0 rInter wFlag C_up
      hSCin hSI hSF hCinI hCinF hIF body).count PrimitiveGate.TOFF =
      body.count PrimitiveGate.TOFF := by
  suffices ∀ d hd,
      (eqCarryUpperDyn v rSlice wCin0 rInter wFlag C_up
        hSCin hSI hSF hCinI hCinF hIF body d hd).count PrimitiveGate.TOFF =
        body.count PrimitiveGate.TOFF from this nSteps le_rfl
  intro d hd
  induction d with
  | zero => rfl
  | succ d ih =>
      unfold eqCarryUpperDyn
      dsimp only
      split_ifs
      · rw [count_ltFirstStepDyn_toff, ih]
      · rw [count_andSandwich_toff, ih]

@[simp]
theorem count_eqCarryChainDyn_t {Var : Type} {N nSteps : ℕ} (v : Var)
    (rSlice : QRegister nSteps N) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (C_up : ℕ)
    (hSCin : ∀ i, rSlice i ≠ wCin0) (hSI : rSlice.DisjointWires rInter)
    (hSF : ∀ i, rSlice i ≠ wFlag) (hCinI : ∀ j, wCin0 ≠ rInter j)
    (hCinF : wCin0 ≠ wFlag) (hIF : ∀ j, rInter j ≠ wFlag)
    (body : DynamicCircuit Var N) :
    (eqCarryChainDyn v rSlice wCin0 rInter wFlag C_up
      hSCin hSI hSF hCinI hCinF hIF body).count PrimitiveGate.T =
      4 * nSteps + body.count PrimitiveGate.T := by
  suffices ∀ d hd,
      (eqCarryUpperDyn v rSlice wCin0 rInter wFlag C_up
        hSCin hSI hSF hCinI hCinF hIF body d hd).count PrimitiveGate.T =
        4 * d + body.count PrimitiveGate.T from this nSteps le_rfl
  intro d hd
  induction d with
  | zero => simp [eqCarryUpperDyn]
  | succ d ih =>
      unfold eqCarryUpperDyn
      dsimp only
      split_ifs
      · rw [count_ltFirstStepDyn_t, ih]; omega
      · rw [count_andSandwich_t, ih]; omega

/-- Compute `decide (regVal rA = C)` onto clean `wFlag` in `eqConstTCount w C ≤ 4 * (w - 1)` `T`
gates, run `body`, and uncompute in `0` `T` gates (`TOFF = 0`). -/
def withEqConstFlagDyn {Var : Type} {N w : ℕ} (v : Var)
    (rA : QRegister w N) (C : ℕ) (rCarry : QRegister (w - 2) N) (wFlag : Wire N)
    (hw : 1 ≤ w)
    (hAC : rA.DisjointWires rCarry)
    (hAF : ∀ i, rA i ≠ wFlag) (hCF : ∀ i, rCarry i ≠ wFlag)
    (body : DynamicCircuit Var N) : DynamicCircuit Var N :=
  if 2 ^ w ≤ C then
    body
  else if w = 1 then
    if C % 2 = 0 then
      conjCNOTDyn (rA ⟨0, hw⟩) wFlag (hAF ⟨0, hw⟩) (conjXDyn wFlag body)
    else
      conjCNOTDyn (rA ⟨0, hw⟩) wFlag (hAF ⟨0, hw⟩) body
  else if C % 2 = 0 then
    let rSlice := rA.slice 1 (w - 1) (by omega)
    let wCin0 := rA ⟨0, hw⟩
    conjXDyn wCin0
      (eqCarryChainDyn v rSlice wCin0 rCarry wFlag (C / 2)
        (fun i h ↦ by
          have hv := congrArg Fin.val (rA.wires.injective h)
          change 1 + i.val = 0 at hv
          omega)
        (hAC.compose_left _)
        (slice_ne_right rA _ wFlag hAF)
        (fun _ ↦ hAC.ne ⟨0, hw⟩ _)
        (hAF ⟨0, hw⟩)
        hCF
        body)
  else
    let rSlice := rA.slice 1 (w - 1) (by omega)
    let wCin0 := rA ⟨0, hw⟩
    eqCarryChainDyn v rSlice wCin0 rCarry wFlag (C / 2)
      (fun i h ↦ by
        have hv := congrArg Fin.val (rA.wires.injective h)
        change 1 + i.val = 0 at hv
        omega)
      (hAC.compose_left _)
      (slice_ne_right rA _ wFlag hAF)
      (fun _ ↦ hAC.ne ⟨0, hw⟩ _)
      (hAF ⟨0, hw⟩)
      hCF
      body

@[simp]
theorem count_withEqConstFlagDyn_toff {Var : Type} {N w : ℕ} (v : Var)
    (rA : QRegister w N) (C : ℕ) (rCarry : QRegister (w - 2) N) (wFlag : Wire N)
    (hw : 1 ≤ w) (hAC : rA.DisjointWires rCarry)
    (hAF : ∀ i, rA i ≠ wFlag) (hCF : ∀ i, rCarry i ≠ wFlag)
    (body : DynamicCircuit Var N) :
    (withEqConstFlagDyn v rA C rCarry wFlag hw hAC hAF hCF body).count PrimitiveGate.TOFF =
      body.count PrimitiveGate.TOFF := by
  unfold withEqConstFlagDyn
  split_ifs
  · rfl
  · simp
  · simp
  · simp
  · simp

@[simp]
theorem count_withEqConstFlagDyn_t {Var : Type} {N w : ℕ} (v : Var)
    (rA : QRegister w N) (C : ℕ) (rCarry : QRegister (w - 2) N) (wFlag : Wire N)
    (hw : 1 ≤ w) (hAC : rA.DisjointWires rCarry)
    (hAF : ∀ i, rA i ≠ wFlag) (hCF : ∀ i, rCarry i ≠ wFlag)
    (body : DynamicCircuit Var N) :
    (withEqConstFlagDyn v rA C rCarry wFlag hw hAC hAF hCF body).count PrimitiveGate.T =
      eqConstTCount w C + body.count PrimitiveGate.T := by
  unfold withEqConstFlagDyn
  split_ifs with hge hw1 hm1 hm2
  · rw [eqConstTCount, ite_eq_left hge, zero_add]
  · rw [count_conjCNOTDyn_t, count_conjXDyn_t, eqConstTCount, ite_eq_right hge, hw1]; simp
  · rw [count_conjCNOTDyn_t, eqConstTCount, ite_eq_right hge, hw1]; simp
  · dsimp only
    rw [eqConstTCount, ite_eq_right hge, count_conjXDyn_t, count_eqCarryChainDyn_t]
  · dsimp only
    rw [eqConstTCount, ite_eq_right hge, count_eqCarryChainDyn_t]

namespace EqConstProofs

theorem predRealizes_eqCarryChainDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N nSteps t : ℕ} [NeZero (2 ^ N)] {v : Var} {S₀ : Finset (Wire N)}
    (rSlice : QRegister nSteps N) (wCin0 : Wire N)
    (rInter : QRegister (nSteps - 1) N) (wFlag : Wire N) (C_up : ℕ)
    (rTarget : QRegister t N)
    (hn : 1 ≤ nSteps) (hCup : C_up < 2 ^ nSteps)
    (hSCin : ∀ i, rSlice i ≠ wCin0)
    (hSI : rSlice.DisjointWires rInter)
    (hSF : ∀ i, rSlice i ≠ wFlag)
    (hCinI : ∀ j, wCin0 ≠ rInter j)
    (hCinF : wCin0 ≠ wFlag)
    (hIF : ∀ j, rInter j ≠ wFlag)
    (hST : rSlice.DisjointWires rTarget)
    (hCinT : wCin0 ∉ rTarget.image)
    (hIT : rInter.DisjointWires rTarget)
    (hFT : wFlag ∉ rTarget.image)
    (hSS₀ : Disjoint rSlice.image S₀)
    (hCinS₀ : wCin0 ∉ S₀)
    (hIS₀ : Disjoint rInter.image S₀)
    (hFS₀ : wFlag ∉ S₀)
    {V₀ V₁ : Unitary (2 ^ t)} {body : DynamicCircuit Var N}
    (hbody : ComparatorProofs.PredRealizes v S₀ rTarget V₀ V₁
      (fun β ↦ decide (β wFlag = 1)) body) :
    ComparatorProofs.PredRealizes v (insert wFlag (rInter.image ∪ S₀)) rTarget V₀ V₁
      (fun β ↦ decide (regVal rSlice β = C_up ∧ β wCin0 = 1))
      (eqCarryChainDyn v rSlice wCin0 rInter wFlag C_up
        hSCin hSI hSF hCinI hCinF hIF body) := by
  have hS_notT (i : Fin nSteps) : rSlice i ∉ rTarget.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hST.ne i j hj.symm
  have hI_notT (i : Fin (nSteps - 1)) : rInter i ∉ rTarget.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hIT.ne i j hj.symm
  have hwire_notT (m : ℕ) : constChainWire wCin0 rInter wFlag m ∉ rTarget.image := by
    dsimp [constChainWire]
    split_ifs with h0 hm
    · exact hCinT
    · exact hI_notT ⟨m - 1, hm⟩
    · exact hFT
  have hS_notSuf (i : Fin nSteps) (d : ℕ) (hd : d ≤ nSteps) :
      rSlice i ∉ ConstChainProofs.constCleanSuffix wCin0 rInter wFlag S₀ d := by
    rw [ConstChainProofs.mem_constCleanSuffix_iff]
    rintro (hS | ⟨d', hd', heq⟩)
    · exact Finset.disjoint_left.mp hSS₀ (by rw [QRegister.mem_image]; exact ⟨i, rfl⟩) hS
    · exact slice_ne_constChainWire rSlice wCin0 rInter wFlag hSCin hSI hSF i _ heq
  have hwire_notSuf (m : ℕ) (d : ℕ) (hd : d < nSteps) (hmd : m ≤ nSteps - 1 - d) :
      constChainWire wCin0 rInter wFlag m ∉
        ConstChainProofs.constCleanSuffix wCin0 rInter wFlag S₀ d := by
    rw [ConstChainProofs.mem_constCleanSuffix_iff]
    rintro (hS | ⟨d', hd', heq⟩)
    · dsimp [constChainWire] at hS
      split_ifs at hS with h0 hm
      · exact hCinS₀ hS
      · exact Finset.disjoint_left.mp hIS₀
          (by rw [QRegister.mem_image]; exact ⟨⟨m - 1, hm⟩, rfl⟩) hS
      · omega
    · dsimp [constChainWire] at heq
      split_ifs at heq with h0 hm1 h0' hm2
      · omega
      · exact hCinI _ heq
      · exact hCinF heq
      · omega
      · have hv := congrArg Fin.val (rInter.wires.injective heq)
        dsimp at hv
        omega
      · exact hIF _ heq
      · omega
      · omega
      · omega
  have hout_notSuf (d : ℕ) (hd : d < nSteps) :
      constChainWire wCin0 rInter wFlag (nSteps - d) ∉
        ConstChainProofs.constCleanSuffix wCin0 rInter wFlag S₀ d := by
    rw [ConstChainProofs.mem_constCleanSuffix_iff]
    rintro (hS | ⟨d', hd', heq⟩)
    · dsimp [constChainWire] at hS
      split_ifs at hS with h0 hm
      · omega
      · exact Finset.disjoint_left.mp hIS₀
          (by rw [QRegister.mem_image]; exact ⟨⟨_, hm⟩, rfl⟩) hS
      · exact hFS₀ hS
    · dsimp [constChainWire] at heq
      split_ifs at heq with h0 hm1 h0' hm2
      · omega
      · omega
      · omega
      · omega
      · have hv := congrArg Fin.val (rInter.wires.injective heq)
        dsimp at hv
        omega
      · exact hIF _ heq
      · omega
      · exact (hIF _ heq.symm).elim
      · omega
  have hup (d : ℕ) (hd : d ≤ nSteps) :
      ComparatorProofs.PredRealizes v
        (ConstChainProofs.constCleanSuffix wCin0 rInter wFlag S₀ d)
        rTarget V₀ V₁
        (fun β ↦ decide
          (regVal rSlice β / 2 ^ (nSteps - d) = C_up / 2 ^ (nSteps - d) ∧
            β (constChainWire wCin0 rInter wFlag (nSteps - d)) = 1))
        (eqCarryUpperDyn v rSlice wCin0 rInter wFlag C_up
          hSCin hSI hSF hCinI hCinF hIF body d hd) := by
    induction d with
    | zero =>
        refine hbody.congr_pred
          (fun β γ ↦ by
            simp only [ComparatorProofs.regVal_writeReg_of_disjoint rSlice rTarget hST,
              ComparatorProofs.writeReg_apply_of_not_mem_image β rTarget γ _ (hwire_notT _)])
          fun β _ ↦ ?_
        have hs0 : regVal rSlice β / 2 ^ nSteps = 0 := Nat.div_eq_of_lt (regVal_lt rSlice β)
        have hc0 : C_up / 2 ^ nSteps = 0 := Nat.div_eq_of_lt hCup
        have hwf : constChainWire wCin0 rInter wFlag nSteps = wFlag :=
          constChainWire_last hn wCin0 rInter wFlag
        simp [hs0, hc0, hwf]
    | succ d ih =>
        let m := nSteps - 1 - d
        have hm_lt : m < nSteps := by omega
        have hm_succ : m + 1 = nSteps - d := by omega
        have hm_eq : nSteps - (d + 1) = m := by omega
        unfold eqCarryUpperDyn
        dsimp only
        have hAC : rSlice ⟨m, hm_lt⟩ ≠ constChainWire wCin0 rInter wFlag m :=
          slice_ne_constChainWire rSlice wCin0 rInter wFlag hSCin hSI hSF ⟨m, hm_lt⟩ m
        have hAO : rSlice ⟨m, hm_lt⟩ ≠ constChainWire wCin0 rInter wFlag (m + 1) :=
          slice_ne_constChainWire rSlice wCin0 rInter wFlag hSCin hSI hSF ⟨m, hm_lt⟩ (m + 1)
        have hCO :
            constChainWire wCin0 rInter wFlag m ≠
              constChainWire wCin0 rInter wFlag (m + 1) :=
          constChainWire_ne_succ wCin0 rInter wFlag hCinI hCinF hIF m hm_lt
        have hS_upd (val : ZMod 2) (β : BitAssignment N) :
            regVal rSlice (Function.update β (constChainWire wCin0 rInter wFlag (m + 1)) val) =
              regVal rSlice β := by
          unfold regVal localIdx
          congr 2; funext i
          exact Function.update_of_ne
            (slice_ne_constChainWire rSlice wCin0 rInter wFlag hSCin hSI hSF i (m + 1)) _ _
        have hsuf_eq :
            ConstChainProofs.constCleanSuffix wCin0 rInter wFlag S₀ (d + 1) =
              insert (constChainWire wCin0 rInter wFlag (m + 1))
                (ConstChainProofs.constCleanSuffix wCin0 rInter wFlag S₀ d) := by
          rw [ConstChainProofs.constCleanSuffix, hm_succ]
        rw [hsuf_eq]
        split_ifs with hbitC
        · have hstep := LtProofs.predRealizes_ltFirstStepDyn
            (rSlice ⟨m, hm_lt⟩)
            (constChainWire wCin0 rInter wFlag m)
            (constChainWire wCin0 rInter wFlag (m + 1))
            hAC hAO hCO
            (hS_notT _) (hwire_notT m) (hwire_notT (m + 1))
            (hS_notSuf _ d (by omega))
            (hwire_notSuf m d (by omega) le_rfl)
            (by rw [hm_succ]; exact hout_notSuf d (by omega))
            (ih (by omega))
          refine hstep.congr_pred
            (fun β γ ↦ by
              simp only [ComparatorProofs.regVal_writeReg_of_disjoint rSlice rTarget hST,
                ComparatorProofs.writeReg_apply_of_not_mem_image β rTarget γ _ (hwire_notT _)])
            fun β _ ↦ ?_
          rw [hS_upd, ← hm_succ, Function.update_self, hm_eq]
          have hbit_iff :
              ((β (rSlice ⟨m, hm_lt⟩) + 1) * β (constChainWire wCin0 rInter wFlag m) = 1) ↔
                (bitNat (β (rSlice ⟨m, hm_lt⟩)) = 0 ∧
                  β (constChainWire wCin0 rInter wFlag m) = 1) := by
            rcases bit_cases (β (rSlice ⟨m, hm_lt⟩)) with ha | ha <;>
              rcases bit_cases (β (constChainWire wCin0 rInter wFlag m)) with hc | hc <;>
              simp [ha, hc, bitNat, one_add_one_zmod2]
          have hbitA := regVal_div_pow_mod_two rSlice β hm_lt
          have hdivA := nat_div_pow_eq (regVal rSlice β) m
          have hdivC := nat_div_pow_eq C_up m
          have hmodA : regVal rSlice β / 2 ^ m % 2 < 2 := Nat.mod_lt _ (by omega)
          congr 1
          apply propext
          rw [hbit_iff, ← hbitA, hdivA, hdivC, hbitC]
          by_cases hP : β (constChainWire wCin0 rInter wFlag m) = 1
          · simp only [hP, and_true]; omega
          · simp only [hP, and_false]
        · have hbitC1 : (C_up / 2 ^ m) % 2 = 1 := by
            change ¬(C_up / 2 ^ m) % 2 = 0 at hbitC
            have hlt2 : (C_up / 2 ^ m) % 2 < 2 := Nat.mod_lt _ (by omega)
            omega
          have hstep := (ih (by omega)).andSandwich
            (rSlice ⟨m, hm_lt⟩)
            (constChainWire wCin0 rInter wFlag m)
            (constChainWire wCin0 rInter wFlag (m + 1))
            hAC hAO hCO
            (hS_notT _) (hwire_notT m) (hwire_notT (m + 1))
            (hS_notSuf _ d (by omega))
            (hwire_notSuf m d (by omega) le_rfl)
            (by rw [hm_succ]; exact hout_notSuf d (by omega))
          refine hstep.congr_pred
            (fun β γ ↦ by
              simp only [ComparatorProofs.regVal_writeReg_of_disjoint rSlice rTarget hST,
                ComparatorProofs.writeReg_apply_of_not_mem_image β rTarget γ _ (hwire_notT _)])
            fun β _ ↦ ?_
          rw [hS_upd, ← hm_succ, Function.update_self, hm_eq]
          have hbit_iff :
              (β (rSlice ⟨m, hm_lt⟩) * β (constChainWire wCin0 rInter wFlag m) = 1) ↔
                (bitNat (β (rSlice ⟨m, hm_lt⟩)) = 1 ∧
                  β (constChainWire wCin0 rInter wFlag m) = 1) := by
            rcases bit_cases (β (rSlice ⟨m, hm_lt⟩)) with ha | ha <;>
              rcases bit_cases (β (constChainWire wCin0 rInter wFlag m)) with hc | hc <;>
              simp [ha, hc, bitNat]
          have hbitA := regVal_div_pow_mod_two rSlice β hm_lt
          have hdivA := nat_div_pow_eq (regVal rSlice β) m
          have hdivC := nat_div_pow_eq C_up m
          have hmodA : regVal rSlice β / 2 ^ m % 2 < 2 := Nat.mod_lt _ (by omega)
          congr 1
          apply propext
          rw [hbit_iff, ← hbitA, hdivA, hdivC, hbitC1]
          by_cases hP : β (constChainWire wCin0 rInter wFlag m) = 1
          · simp only [hP, and_true]; omega
          · simp only [hP, and_false]
  have hfull := hup nSteps le_rfl
  rw [ConstChainProofs.constCleanSuffix_full hn] at hfull
  refine hfull.congr_pred
    (fun β γ ↦ by
      simp only [ComparatorProofs.regVal_writeReg_of_disjoint rSlice rTarget hST,
        ComparatorProofs.writeReg_apply_of_not_mem_image β rTarget γ wCin0 hCinT])
    fun β _ ↦ ?_
  have h0 : nSteps - nSteps = 0 := Nat.sub_self _
  have hw0 : constChainWire wCin0 rInter wFlag 0 = wCin0 := rfl
  rw [h0, Nat.pow_zero, Nat.div_one, Nat.div_one, hw0]

theorem predRealizes_withEqConstFlagDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N w t : ℕ} [NeZero (2 ^ N)] {v : Var} {S₀ : Finset (Wire N)}
    (rA : QRegister w N) (C : ℕ) (rCarry : QRegister (w - 2) N) (wFlag : Wire N)
    (rTarget : QRegister t N)
    (hw : 1 ≤ w)
    (hAC : rA.DisjointWires rCarry)
    (hAF : ∀ i, rA i ≠ wFlag) (hCF : ∀ i, rCarry i ≠ wFlag)
    (hAT : rA.DisjointWires rTarget)
    (hCT : rCarry.DisjointWires rTarget)
    (hFT : wFlag ∉ rTarget.image)
    (hAS₀ : Disjoint rA.image S₀)
    (hCS₀ : Disjoint rCarry.image S₀)
    (hFS₀ : wFlag ∉ S₀)
    {V₀ V₁ : Unitary (2 ^ t)} {body : DynamicCircuit Var N}
    (hbody : ComparatorProofs.PredRealizes v S₀ rTarget V₀ V₁
      (fun β ↦ decide (β wFlag = 1)) body) :
    ComparatorProofs.PredRealizes v (insert wFlag (rCarry.image ∪ S₀)) rTarget V₀ V₁
      (fun β ↦ decide (regVal rA β = C))
      (withEqConstFlagDyn v rA C rCarry wFlag hw hAC hAF hCF body) := by
  have hA_notT (i : Fin w) : rA i ∉ rTarget.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hAT.ne i j hj.symm
  have hA_notS₀ (i : Fin w) : rA i ∉ S₀ := fun h ↦
    Finset.disjoint_left.mp hAS₀ (by rw [QRegister.mem_image]; exact ⟨i, rfl⟩) h
  have hdisj_full : Disjoint rTarget.image (insert wFlag (rCarry.image ∪ S₀)) := by
    refine Finset.disjoint_insert_right.mpr ⟨hFT, Finset.disjoint_union_right.mpr ⟨?_, hbody.1⟩⟩
    rw [Finset.disjoint_left]
    intro q hqT hqC
    rw [QRegister.mem_image] at hqT hqC
    obtain ⟨j, rfl⟩ := hqT; obtain ⟨i, hi⟩ := hqC
    exact hCT.ne i j hi
  have hsub_S₀ : S₀ ⊆ insert wFlag (rCarry.image ∪ S₀) :=
    fun _ hq ↦ Finset.mem_insert_of_mem (Finset.mem_union_right _ hq)
  have hgA (β : BitAssignment N) (γ : BitAssignment t) :
      decide (regVal rA (writeReg β rTarget γ) = C) = decide (regVal rA β = C) := by
    rw [ComparatorProofs.regVal_writeReg_of_disjoint rA rTarget hAT]
  unfold withEqConstFlagDyn
  split_ifs with hge hw1 hm1 hm2
  · refine (hbody.add_clean_subset hsub_S₀ hdisj_full).congr_pred hgA fun β hS ↦ ?_
    have hf0 : β wFlag = 0 := hS wFlag (Finset.mem_insert_self _ _)
    have hne_C : regVal rA β ≠ C := ne_of_lt (Nat.lt_of_lt_of_le (regVal_lt rA β) hge)
    simp [hf0, hne_C]
  · subst hw1
    have hC0 : C = 0 := by omega
    subst hC0
    have h1 := hbody.conjX wFlag hFT hFS₀
    have h2 := h1.conjCNOT (rA 0) wFlag (hAF 0) (hA_notT 0) hFT (hA_notS₀ 0) hFS₀
    refine (h2.add_clean_subset hsub_S₀ hdisj_full).congr_pred
      (fun β γ ↦ by rw [ComparatorProofs.regVal_writeReg_of_disjoint rA rTarget hAT])
      fun β hS ↦ ?_
    have hf0 : β wFlag = 0 := hS wFlag (Finset.mem_insert_self _ _)
    rw [Function.update_self, Function.update_self, hf0, zero_add,
      ComparatorProofs.regVal_width_one]
    rcases bit_cases (β (rA 0)) with hb | hb <;> simp [hb, bitNat, one_add_one_zmod2]
  · subst hw1
    have hC1 : C = 1 := by omega
    subst hC1
    have h2 := hbody.conjCNOT (rA 0) wFlag (hAF 0) (hA_notT 0) hFT (hA_notS₀ 0) hFS₀
    refine (h2.add_clean_subset hsub_S₀ hdisj_full).congr_pred
      (fun β γ ↦ by rw [ComparatorProofs.regVal_writeReg_of_disjoint rA rTarget hAT])
      fun β hS ↦ ?_
    have hf0 : β wFlag = 0 := hS wFlag (Finset.mem_insert_self _ _)
    rw [Function.update_self, hf0, zero_add, ComparatorProofs.regVal_width_one]
    rcases bit_cases (β (rA 0)) with hb | hb <;> simp [hb, bitNat]
  · dsimp only
    let rSlice := rA.slice 1 (w - 1) (by omega)
    let wCin0 := rA ⟨0, hw⟩
    have hn : 1 ≤ w - 1 := by omega
    have hCup : C / 2 < 2 ^ (w - 1) := by
      have hpow_eq : 2 ^ w = 2 * 2 ^ (w - 1) := by
        conv_lhs => rw [show w = (w - 1) + 1 by omega]
        exact Nat.pow_succ'
      have hlt_pow : C < 2 ^ w := by omega
      rw [hpow_eq] at hlt_pow
      exact Nat.div_lt_of_lt_mul hlt_pow
    have hchain := predRealizes_eqCarryChainDyn rSlice wCin0 rCarry wFlag (C / 2)
      rTarget hn hCup
      (fun i h ↦ by
        have hv := congrArg Fin.val (rA.wires.injective h)
        change 1 + i.val = 0 at hv
        omega)
      (hAC.compose_left _)
      (fun _ ↦ hAF _)
      (fun _ ↦ hAC.ne ⟨0, hw⟩ _)
      (hAF ⟨0, hw⟩)
      hCF
      (hAT.compose_left _)
      (hA_notT ⟨0, hw⟩)
      hCT
      hFT
      (Finset.disjoint_of_subset_left (QRegister.image_compose_subset _ _) hAS₀)
      (hA_notS₀ ⟨0, hw⟩)
      hCS₀
      hFS₀
      hbody
    have hCin_notS' : wCin0 ∉ insert wFlag (rCarry.image ∪ S₀) := by
      simp only [Finset.mem_insert, Finset.mem_union, QRegister.mem_image]
      rintro (heq | ⟨j, hj⟩ | hS)
      · exact hAF ⟨0, hw⟩ heq
      · exact hAC.ne ⟨0, hw⟩ j hj.symm
      · exact hA_notS₀ ⟨0, hw⟩ hS
    have hx := hchain.conjX wCin0 (hA_notT ⟨0, hw⟩) hCin_notS'
    refine hx.congr_pred hgA fun β _ ↦ ?_
    have hSlice_upd : regVal rSlice (Function.update β wCin0 (β wCin0 + 1)) = regVal rSlice β := by
      unfold regVal localIdx
      congr 2; funext i
      apply Function.update_of_ne
      intro heq
      have hv := congrArg Fin.val (rA.wires.injective heq)
      change 1 + i.val = 0 at hv
      omega
    rw [hSlice_upd, Function.update_self,
      ComparatorProofs.regVal_slice_suffix rA _ (by omega) β, pow_one]
    have hbit_iff : (β wCin0 + 1 = 1) ↔ bitNat (β wCin0) = 0 := by
      rcases bit_cases (β wCin0) with hb | hb <;> simp [hb, bitNat, one_add_one_zmod2]
    have hbitA := regVal_div_pow_mod_two rA β hw
    simp only [Nat.pow_zero, Nat.div_one] at hbitA
    congr 1
    apply propext
    rw [hbit_iff, ← hbitA]
    omega
  · dsimp only
    let rSlice := rA.slice 1 (w - 1) (by omega)
    let wCin0 := rA ⟨0, hw⟩
    have hn : 1 ≤ w - 1 := by omega
    have hCup : C / 2 < 2 ^ (w - 1) := by
      have hpow_eq : 2 ^ w = 2 * 2 ^ (w - 1) := by
        conv_lhs => rw [show w = (w - 1) + 1 by omega]
        exact Nat.pow_succ'
      have hlt_pow : C < 2 ^ w := by omega
      rw [hpow_eq] at hlt_pow
      exact Nat.div_lt_of_lt_mul hlt_pow
    have hchain := predRealizes_eqCarryChainDyn rSlice wCin0 rCarry wFlag (C / 2)
      rTarget hn hCup
      (fun i h ↦ by
        have hv := congrArg Fin.val (rA.wires.injective h)
        change 1 + i.val = 0 at hv
        omega)
      (hAC.compose_left _)
      (fun _ ↦ hAF _)
      (fun _ ↦ hAC.ne ⟨0, hw⟩ _)
      (hAF ⟨0, hw⟩)
      hCF
      (hAT.compose_left _)
      (hA_notT ⟨0, hw⟩)
      hCT
      hFT
      (Finset.disjoint_of_subset_left (QRegister.image_compose_subset _ _) hAS₀)
      (hA_notS₀ ⟨0, hw⟩)
      hCS₀
      hFS₀
      hbody
    refine hchain.congr_pred hgA fun β _ ↦ ?_
    rw [ComparatorProofs.regVal_slice_suffix rA _ (by omega) β, pow_one]
    have hbit_iff : (β wCin0 = 1) ↔ bitNat (β wCin0) = 1 := by
      rcases bit_cases (β wCin0) with hb | hb <;> simp [hb, bitNat]
    have hbitA := regVal_div_pow_mod_two rA β hw
    simp only [Nat.pow_zero, Nat.div_one] at hbitA
    congr 1
    apply propext
    rw [hbit_iff, ← hbitA]
    omega

end EqConstProofs

/-- `CleanRealizes` for `withEqConstFlagDyn` wrapping any `wFlag`-multiplexed `body`
(`eqConstTCount w C ≤ 4 * (w - 1)` `T` compute, `0` `T` uncompute, `TOFF = 0`). -/
theorem cleanRealizes_withEqConstFlagDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N w t s : ℕ} [NeZero (2 ^ N)] (v : Var)
    (rA : QRegister w N) (C : ℕ) (rCarry : QRegister (w - 2) N) (wFlag : Wire N)
    (rTarget : QRegister t N) (rBodyScr : QRegister s N)
    (hw : 1 ≤ w)
    (hAC : rA.DisjointWires rCarry)
    (hAF : ∀ i, rA i ≠ wFlag) (hCF : ∀ i, rCarry i ≠ wFlag)
    (hAT : rA.DisjointWires rTarget)
    (hCT : rCarry.DisjointWires rTarget)
    (hFT : (QRegister.singleton wFlag).DisjointWires rTarget)
    (hAS : rA.DisjointWires rBodyScr)
    (hCS : rCarry.DisjointWires rBodyScr)
    (hFS : ∀ j, wFlag ≠ rBodyScr j)
    (hTS : rTarget.DisjointWires rBodyScr)
    {V₀ V₁ : Unitary (2 ^ t)} {body : DynamicCircuit Var N}
    (hbody : CleanRealizes v ((QRegister.singleton wFlag).concat rTarget hFT)
      rBodyScr (muxBitLocalUnitary V₀ V₁) body) :
    let hFC : (QRegister.singleton wFlag).DisjointWires rCarry := by
      rw [QRegister.disjoint_iff]; intro a j; fin_cases a; exact (hCF j).symm
    let hFCS : ((QRegister.singleton wFlag).concat rCarry hFC).DisjointWires rBodyScr := by
      rw [QRegister.disjoint_iff]; intro p j
      rcases fin_eq_castAdd_or_natAdd p with ⟨a, rfl⟩ | ⟨i, rfl⟩
      · fin_cases a; rw [QRegister.concat_apply_left]; exact hFS j
      · rw [QRegister.concat_apply_right]; exact hCS.ne i j
    CleanRealizes v (rA.concat rTarget hAT)
      (((QRegister.singleton wFlag).concat rCarry hFC).concat rBodyScr hFCS)
      (muxPredLocalUnitary (fun a : Fin (2 ^ w) ↦ decide (a.val = C)) V₀ V₁)
      (withEqConstFlagDyn v rA C rCarry wFlag hw hAC hAF hCF body) := by
  intro hFC hFCS
  let rTotalScr := ((QRegister.singleton wFlag).concat rCarry hFC).concat rBodyScr hFCS
  apply ComparatorProofs.PredRealizes.toCleanRealizes rA rTarget rTotalScr hAT
  have himg_scr : rTotalScr.image = insert wFlag (rCarry.image ∪ rBodyScr.image) := by
    ext q
    simp only [Finset.mem_insert, Finset.mem_union, QRegister.mem_image]
    constructor
    · rintro ⟨p, rfl⟩
      rcases fin_eq_castAdd_or_natAdd p with ⟨u, rfl⟩ | ⟨j, rfl⟩
      · rw [QRegister.concat_apply_left]
        rcases fin_eq_castAdd_or_natAdd u with ⟨a, rfl⟩ | ⟨i, rfl⟩
        · fin_cases a; rw [QRegister.concat_apply_left]; exact Or.inl rfl
        · rw [QRegister.concat_apply_right]; exact Or.inr (Or.inl ⟨i, rfl⟩)
      · rw [QRegister.concat_apply_right]; exact Or.inr (Or.inr ⟨j, rfl⟩)
    · rintro (rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Fin.castAdd s (Fin.castAdd (w - 2) 0), by
          rw [QRegister.concat_apply_left, QRegister.concat_apply_left]; rfl⟩
      · exact ⟨Fin.castAdd s (Fin.natAdd 1 i), by
          rw [QRegister.concat_apply_left, QRegister.concat_apply_right]⟩
      · exact ⟨Fin.natAdd (1 + (w - 2)) j, by rw [QRegister.concat_apply_right]⟩
  rw [himg_scr]
  have hFT' : wFlag ∉ rTarget.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hFT.ne 0 j hj.symm
  have hAS₀ : Disjoint rA.image rBodyScr.image := by
    rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
    obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2; exact hAS.ne i j hj.symm
  have hCS₀ : Disjoint rCarry.image rBodyScr.image := by
    rw [Finset.disjoint_left]; intro q h1 h2; rw [QRegister.mem_image] at h1 h2
    obtain ⟨i, rfl⟩ := h1; obtain ⟨j, hj⟩ := h2; exact hCS.ne i j hj.symm
  have hFS₀ : wFlag ∉ rBodyScr.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩; exact hFS j hj.symm
  exact EqConstProofs.predRealizes_withEqConstFlagDyn rA C rCarry wFlag rTarget hw
    hAC hAF hCF hAT hCT hFT' hAS₀ hCS₀ hFS₀
    (ComparatorProofs.PredRealizes.of_muxBitBody wFlag rTarget rBodyScr hFT hFS hTS hbody)

namespace CenteredProofs

end CenteredProofs

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators
