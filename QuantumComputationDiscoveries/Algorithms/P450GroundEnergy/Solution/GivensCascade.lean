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
public import QuantumComputation.Primitives.Phase
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm

/-!
# Batched Fermionic Givens Cascade, `104 T` Phase-Gradient Rotation & Spin-Swap (`GivensCascade`)

Implements the `TOFF = 0` Clifford + `T` + mid-circuit-measurement orbital basis-change and
turnaround micro-batched reflection gadgets for `P450GroundEnergy`:

1. **Compositional `CleanRealizes` & `ClassicalBracketProg` Engine (`Section 1`):**
   - Exact 4-conjunct clean-ancilla weakest-precondition contract `CleanRealizes` with sequential
     composition, circuit lifting, and subregister/scratch-extension combinators.
   - Structural temporary-AND AST `ClassicalBracketProg` lowering `.tempAnd` to
     `DynamicCircuit.andCompute` (`4 T`) and `DynamicCircuit.andUncompute` (`0 T`).
2. **`26`-`andCompute` (`104 T`) Ones'-Complement Signed Phase-Gradient Adder (`Section 2`):**
   - Controlled `13`-into-`14`-bit signed modular addition/subtraction on `phaseGradientState 14`
     via ones'-complement CNOT conjugation (`~(~y + k) = y - k mod 2^14`), using `26` `andCompute`s
     (`104 T`, `0 TOFF`) and `26` reusable clean scratch wires.
3. **2-Mode Fermionic Givens Rotation & Explicit `N = 2` JW Verification (`Section 3`):**
   - `twoModeGivensUnitary`, `0-T` Clifford diagonalizations (`givensHalfClifford`,
     `givensClifford`), explicit `N = 2` Pauli expansion of `1 - 2 • blockedOrbitalNumberOp 2`,
     and `twoModeGivensDyn` / `twoModeGivensInvDyn` (`104 T`, `0 TOFF`).
4. **57-Step Cascade Induction & `58`-Pair Spin-Swap Fredkin (`Section 4`):**
   - Exact `N`-mode Bogoliubov identities, `givensCascade_conj_Z0` on `58` spatial orbitals, spin-1
     Jordan–Wigner `Z`-string cancellation, and `spinSwap58Dyn` (`232 T`, `0 TOFF`, `1` clean wire).
5. **Turnaround Micro-Batched Schedule (`Section 5`):**
   - Parametric `K`-angle micro-batched reflection `batchedGivensReflectionDyn` (`K > 0`, including
     `K = 6, 10, 12, 19, 57`) executing `2 * ⌈57 / K⌉ - 1` batch loads by keeping batch `0`
     (`p = 0 .. K - 1`) live across the central `±Z_{0,σ}` reflection (`11,856 T` Givens total).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensCascade
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Real Circuit QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open scoped Matrix ComplexOrder MatrixOrder Real Circuit.Notation BigOperators

/-!
## Section 1: `CleanRealizes` Combinators & `ClassicalBracketProg` Engine
-/

/-- Exact 4-conjunct clean-ancilla weakest-precondition realization predicate for `DynamicCircuit`
(matching `CleanDyn.CleanRealizes` definitionally):
1. `P` uses zero `.TOFF` gates.
2. `wp P.compile` preserves `v`-store invariance of assertions.
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

private theorem restrict_wp_qAssign_restrict_eq {Var : Type} [Fintype Var] {N k s : ℕ}
    (rAct : QRegister k N) (rScr : QRegister s N) (hdisj : rAct.DisjointWires rScr)
    (U : Unitary (2 ^ k)) (Ψ : QCAssertion Var (2 ^ N)) :
    restrictAssertionToZeroAncilla
      (qcWpQAssign (rAct.embedUnitary U) (restrictAssertionToZeroAncilla Ψ rScr)) rScr =
    restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Ψ) rScr := by
  let P₀ := rScr.basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := rScr.basisOutcomeProjector_conjTranspose 0
  have hcomm : (rAct.embedUnitary U).1 * P₀ = P₀ * (rAct.embedUnitary U).1 :=
    rAct.embedMatrix_comm_of_disjoint rScr hdisj U.1 (compProj 0)
  have hcommH : P₀ * (rAct.embedUnitary U).1ᴴ = (rAct.embedUnitary U).1ᴴ * P₀ := by
    have h := congrArg conjTranspose hcomm
    simpa only [conjTranspose_mul, hP₀_herm] using h
  have hP₀_idem : P₀ * P₀ = P₀ := rScr.basisOutcomeProjector_mul_self 0
  funext σ
  apply Subtype.ext
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  change (Ψ σ).1.conj (P₀ * ((rAct.embedUnitary U).1ᴴ * P₀)) =
    (Ψ σ).1.conj (P₀ * (rAct.embedUnitary U).1ᴴ)
  rw [← Matrix.mul_assoc, hcommH, Matrix.mul_assoc, hP₀_idem, ← hcommH]

/-- `DynamicCircuit.identity` realizes `1` on any disjoint `(rAct, rScr)`. -/
theorem CleanRealizes.identity {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N) :
    CleanRealizes v rAct rScr 1 (.identity : DynamicCircuit Var N) := by
  refine ⟨rfl, fun _ hΘ ↦ hΘ, ?_, ?_⟩
  · intro Θ _
    funext σ
    apply Subtype.ext
    simp [qcWpQAssign, qcQAssignObsMap]
  · intro Θ
    funext σ
    apply Subtype.ext
    simp [conj_conj]

/-- Sequential composition of `CleanRealizes`: `.seq P₁ P₂` realizes `U₂ * U₁` while reusing
the same clean scratch register `rScr`. -/
theorem CleanRealizes.seq {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N} (hdisj : rAct.DisjointWires rScr)
    {U₁ U₂ : Unitary (2 ^ k)} {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : CleanRealizes v rAct rScr U₁ P₁) (h₂ : CleanRealizes v rAct rScr U₂ P₂) :
    CleanRealizes v rAct rScr (U₂ * U₁) (.seq P₁ P₂) := by
  refine ⟨by simp [h₁.1, h₂.1], ?_, ?_, ?_⟩
  · intro Θ hΘ
    simp only [DynamicCircuit.compile_seq, wp]
    exact h₁.2.1 (wp P₂.compile Θ) (h₂.2.1 Θ hΘ)
  · intro Θ hΘ
    simp only [DynamicCircuit.compile_seq, wp]
    have hU₂_inv : ∀ σ val,
        restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U₂) Θ) rScr
          (Function.update σ v val) =
        restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U₂) Θ) rScr σ := by
      intro σ val
      apply Subtype.ext
      simp [qcWpQAssign, qcQAssignObsMap, hΘ σ val]
    rw [← h₁.2.2.2 (wp P₂.compile Θ),
      h₂.2.2.1 Θ hΘ,
      h₁.2.2.1 _ hU₂_inv,
      restrict_wp_qAssign_restrict_eq rAct rScr hdisj U₁,
      qc_wp_qAssign_comp, ← rAct.embedUnitary_mul]
  · intro Θ
    simp only [DynamicCircuit.compile_seq, wp]
    rw [← h₁.2.2.2 (wp P₂.compile (restrictAssertionToZeroAncilla Θ rScr)),
      h₂.2.2.2 Θ,
      h₁.2.2.2 (wp P₂.compile Θ)]

/-- Replacing the target unitary `U` by an equal unitary `U'`. -/
theorem CleanRealizes.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U U' : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v rAct rScr U P) (hU : U = U') :
    CleanRealizes v rAct rScr U' P :=
  hU ▸ h

/-- Diagonal projector onto the subspace where every wire in `S` is in `|0⟩`. -/
noncomputable def zeroSetProj {n : ℕ} (S : Finset (Wire n)) : Operator (2 ^ n) :=
  Matrix.diagonal fun idx ↦ if ∀ w ∈ S, basisBits n idx w = 0 then 1 else 0

@[simp]
theorem zeroSetProj_empty {n : ℕ} : (zeroSetProj (∅ : Finset (Wire n))) = 1 := by
  ext i j
  simp [zeroSetProj, Matrix.diagonal_apply, Matrix.one_apply]

@[simp]
theorem zeroSetProj_conjTranspose {n : ℕ} (S : Finset (Wire n)) :
    (zeroSetProj S)ᴴ = zeroSetProj S := by
  simp [zeroSetProj]

@[simp]
theorem zeroSetProj_mul_self {n : ℕ} (S : Finset (Wire n)) :
    zeroSetProj S * zeroSetProj S = zeroSetProj S := by
  rw [zeroSetProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  by_cases h : ∀ w ∈ S, basisBits n i w = 0
  · rw [ite_eq_left h, mul_one]
  · rw [ite_eq_right h, mul_zero]

theorem zeroSetProj_union {n : ℕ} (S₁ S₂ : Finset (Wire n)) :
    zeroSetProj (S₁ ∪ S₂) = zeroSetProj S₁ * zeroSetProj S₂ := by
  rw [zeroSetProj, zeroSetProj, zeroSetProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  by_cases h1 : ∀ w ∈ S₁, basisBits n i w = 0 <;>
    by_cases h2 : ∀ w ∈ S₂, basisBits n i w = 0
  · have hall : ∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw1 | hw2
      · exact h1 w hw1
      · exact h2 w hw2
    rw [ite_eq_left hall, ite_eq_left h1, ite_eq_left h2, mul_one]
  · have hnot : ¬∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := fun hall ↦
      h2 (fun w hw ↦ hall w (Finset.mem_union_right S₁ hw))
    rw [ite_eq_right hnot, ite_eq_left h1, ite_eq_right h2, mul_zero]
  · have hnot : ¬∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := fun hall ↦
      h1 (fun w hw ↦ hall w (Finset.mem_union_left S₂ hw))
    rw [ite_eq_right hnot, ite_eq_right h1, zero_mul]
  · have hnot : ¬∀ w ∈ S₁ ∪ S₂, basisBits n i w = 0 := fun hall ↦
      h1 (fun w hw ↦ hall w (Finset.mem_union_left S₂ hw))
    rw [ite_eq_right hnot, ite_eq_right h1, zero_mul]

private theorem one_conj_zeroSetProj_mat {n : ℕ} (S : Finset (Wire n)) :
    ((1 : HermitianMat (Fin (2 ^ n)) ℂ).conj (zeroSetProj S)).mat = zeroSetProj S := by
  rw [conj_apply_mat, HermitianMat.mat_one, Matrix.mul_one, zeroSetProj_conjTranspose,
    zeroSetProj_mul_self]

/-- Restrict an assertion `Θ` onto `|0⟩` across an arbitrary `Finset` of physical wires. -/
noncomputable def restrictZeroSet {Var : Type} [Fintype Var] {n : ℕ}
    (S : Finset (Wire n)) (Θ : QCAssertion Var (2 ^ n)) : QCAssertion Var (2 ^ n) :=
  fun σ ↦ ⟨(Θ σ).1.conj (zeroSetProj S), by
    constructor
    · exact (Θ σ).1.conj_nonneg (zeroSetProj S) (Θ σ).2.1
    · apply (HermitianMat.conj_mono (Θ σ).2.2).trans
      apply HermitianMat.le_iff.mpr
      change (1 - (1 : HermitianMat (Fin (2 ^ n)) ℂ).conj (zeroSetProj S)).mat.PosSemidef
      have hmat :
          (1 - (1 : HermitianMat (Fin (2 ^ n)) ℂ).conj (zeroSetProj S)).mat =
            Matrix.diagonal fun idx ↦
              if ∀ w ∈ S, basisBits n idx w = 0 then (0 : ℂ) else 1 := by
        ext i j
        rw [HermitianMat.mat_sub, HermitianMat.mat_one, one_conj_zeroSetProj_mat, zeroSetProj,
          Matrix.sub_apply]
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
          by_cases h : ∀ w ∈ S, basisBits n i w = 0
          · rw [ite_eq_left h, ite_eq_left h, sub_self]
          · rw [ite_eq_right h, ite_eq_right h, sub_zero]
        · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      rw [hmat, posSemidef_diagonal_iff]
      intro idx
      split_ifs
      · exact le_rfl
      · exact zero_le_one⟩

@[simp]
theorem restrictZeroSet_coe {Var : Type} [Fintype Var] {n : ℕ}
    (S : Finset (Wire n)) (Θ : QCAssertion Var (2 ^ n)) (σ : Store Var) :
    (restrictZeroSet S Θ σ).1 = (Θ σ).1.conj (zeroSetProj S) := rfl

@[simp]
theorem restrictZeroSet_empty {Var : Type} [Fintype Var] {n : ℕ}
    (Θ : QCAssertion Var (2 ^ n)) :
    restrictZeroSet ∅ Θ = Θ := by
  funext σ
  apply Subtype.ext; ext1
  simp

theorem restrictZeroSet_union {Var : Type} [Fintype Var] {n : ℕ}
    (S₁ S₂ : Finset (Wire n)) (Θ : QCAssertion Var (2 ^ n)) :
    restrictZeroSet (S₁ ∪ S₂) Θ = restrictZeroSet S₁ (restrictZeroSet S₂ Θ) := by
  funext σ
  apply Subtype.ext; ext1
  simp [restrictZeroSet_coe, conj_apply_mat, zeroSetProj_union, conjTranspose_mul,
    zeroSetProj_conjTranspose, Matrix.mul_assoc]

@[simp]
theorem restrictZeroSet_idem {Var : Type} [Fintype Var] {n : ℕ}
    (S : Finset (Wire n)) (Θ : QCAssertion Var (2 ^ n)) :
    restrictZeroSet S (restrictZeroSet S Θ) = restrictZeroSet S Θ := by
  rw [← restrictZeroSet_union, Finset.union_idempotent]

/-- Classical reversible circuit AST with Gidney temporary-AND blocks (`tempAnd`). -/
inductive ClassicalBracketProg (n : ℕ) : Type where
  | id : ClassicalBracketProg n
  | x : Wire n → ClassicalBracketProg n
  | cnot (c t : Wire n) : c ≠ t → ClassicalBracketProg n
  | seq : ClassicalBracketProg n → ClassicalBracketProg n → ClassicalBracketProg n
  | tempAnd (c₁ c₂ anc : Wire n) :
      c₁ ≠ c₂ → c₁ ≠ anc → c₂ ≠ anc → ClassicalBracketProg n → ClassicalBracketProg n

namespace ClassicalBracketProg

variable {n : ℕ}

/-- Relocate a `k`-wire `ClassicalBracketProg` onto an ordered `k`-wire register in `N` qubits. -/
def onRegister {k N : ℕ} (r : QRegister k N) : ClassicalBracketProg k → ClassicalBracketProg N
  | .id => .id
  | .x u => .x (r u)
  | .cnot c t h => .cnot (r c) (r t) (fun heq ↦ h (r.wires.injective heq))
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc)
        (fun h ↦ h₁₂ (r.wires.injective h))
        (fun h ↦ h₁a (r.wires.injective h))
        (fun h ↦ h₂a (r.wires.injective h))
        (body.onRegister r)

/-- Syntactic support of all wires referenced by `p`. -/
def support : ClassicalBracketProg n → Finset (Wire n)
  | .id => ∅
  | .x u => {u}
  | .cnot c t _ => {c, t}
  | .seq p₁ p₂ => p₁.support ∪ p₂.support
  | .tempAnd c₁ c₂ anc _ _ _ body => {c₁, c₂, anc} ∪ body.support

/-- Equivalent Toffoli-based unitary `Circuit` for clean-ancilla semantic reasoning. -/
def toCircuit : ClassicalBracketProg n → Circuit n
  | .id => .identity
  | .x u => .X u
  | .cnot c t h => .CNOT c t h
  | .seq p₁ p₂ => .seq p₁.toCircuit p₂.toCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (.TOFF c₁ c₂ anc h₁₂ h₁a h₂a)
        (.seq body.toCircuit (.TOFF c₁ c₂ anc h₁₂ h₁a h₂a))

/-- Exact computational-basis bit-assignment semantics of `toCircuit`. -/
def evalBits : ClassicalBracketProg n → BitAssignment n → BitAssignment n
  | .id, β => β
  | .x u, β => Function.update β u (β u + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      let β₂ := body.evalBits β₁
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)

theorem support_onRegister {k N : ℕ} (r : QRegister k N) (p : ClassicalBracketProg k) :
    (p.onRegister r).support = p.support.map r.wires := by
  induction p with
  | id => simp [onRegister, support]
  | x u => simp [onRegister, support]
  | cnot c t _ => ext q; simp [onRegister, support]
  | seq p₁ p₂ ih₁ ih₂ => simp [onRegister, support, ih₁, ih₂, Finset.map_union]
  | tempAnd c₁ c₂ anc _ _ _ body ih => ext q; simp [onRegister, support, ih]

theorem evalBits_onRegister_apply_reg {k N : ℕ} (r : QRegister k N) (p : ClassicalBracketProg k)
    (β : BitAssignment N) (i : Fin k) :
    (p.onRegister r).evalBits β (r i) = p.evalBits (fun j ↦ β (r j)) i := by
  induction p generalizing β i with
  | id => rfl
  | x u =>
      simp only [onRegister, evalBits]
      by_cases hiu : i = u
      · subst hiu; simp
      · rw [Function.update_of_ne (fun h ↦ hiu (r.wires.injective h)),
          Function.update_of_ne hiu]
  | cnot c t _ =>
      simp only [onRegister, evalBits]
      by_cases hit : i = t
      · subst hit; simp
      · rw [Function.update_of_ne (fun heq ↦ hit (r.wires.injective heq)),
          Function.update_of_ne hit]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [onRegister, evalBits]
      rw [ih₂]
      congr 1; funext j; exact ih₁ β j
  | tempAnd c₁ c₂ anc _ _ _ body ih =>
      simp only [onRegister, evalBits]
      have hβ₁ : (fun j ↦ Function.update β (r anc) (β (r anc) + β (r c₁) * β (r c₂)) (r j)) =
          Function.update (fun j ↦ β (r j)) anc (β (r anc) + β (r c₁) * β (r c₂)) := by
        funext j
        by_cases hja : j = anc
        · subst hja; simp
        · rw [Function.update_of_ne (fun h ↦ hja (r.wires.injective h)),
            Function.update_of_ne hja]
      by_cases hia : i = anc
      · subst hia
        simp only [Function.update_self, ih _ i, ih _ c₁, ih _ c₂, hβ₁]
      · rw [Function.update_of_ne (fun h ↦ hia (r.wires.injective h)),
          Function.update_of_ne hia, ih _ i, hβ₁]

/-- Structural clean-ancilla validity for `ClassicalBracketProg`: `ValidBracket p S` witnesses that
`p` uses and cleanly uncomputes via `andUncompute` every wire in `S`. -/
inductive ValidBracket {n : ℕ} : ClassicalBracketProg n → Finset (Wire n) → Prop where
  | id : ValidBracket .id ∅
  | x (u : Wire n) : ValidBracket (.x u) ∅
  | cnot (c t : Wire n) (h : c ≠ t) : ValidBracket (.cnot c t h) ∅
  | seq {p₁ p₂ : ClassicalBracketProg n} {S₁ S₂ : Finset (Wire n)} :
      ValidBracket p₁ S₁ → ValidBracket p₂ S₂ →
      Disjoint p₁.support S₂ → Disjoint p₂.support S₁ →
      ValidBracket (.seq p₁ p₂) (S₁ ∪ S₂)
  | tempAnd {c₁ c₂ anc : Wire n} (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      {body : ClassicalBracketProg n} {S : Finset (Wire n)} :
      ValidBracket body S →
      c₁ ∉ S → c₂ ∉ S → anc ∉ S →
      (∀ β : BitAssignment n,
        body.evalBits β c₁ = β c₁ ∧ body.evalBits β c₂ = β c₂ ∧ body.evalBits β anc = β anc) →
      ValidBracket (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) (insert anc S)

theorem ValidBracket.onRegister {k N : ℕ} (r : QRegister k N)
    {p : ClassicalBracketProg k} {S : Finset (Wire k)} (hp : ValidBracket p S) :
    ValidBracket (p.onRegister r) (S.map r.wires) := by
  induction hp with
  | id => dsimp only [ClassicalBracketProg.onRegister]; simpa using ValidBracket.id
  | x u => dsimp only [ClassicalBracketProg.onRegister]; simpa using ValidBracket.x (r u)
  | cnot c t h =>
      dsimp only [ClassicalBracketProg.onRegister]
      simpa using ValidBracket.cnot (r c) (r t) (fun heq ↦ h (r.wires.injective heq))
  | seq _ _ hd₁ hd₂ ih₁ ih₂ =>
      rw [Finset.map_union]
      refine ValidBracket.seq ih₁ ih₂ ?_ ?_
      · rw [support_onRegister, Finset.disjoint_map]; exact hd₁
      · rw [support_onRegister, Finset.disjoint_map]; exact hd₂
  | @tempAnd c₁ c₂ anc _ _ _ body S _ hc₁ hc₂ hanc hpres ih =>
      rw [Finset.map_insert]
      refine ValidBracket.tempAnd _ _ _ ih (by simpa using hc₁) (by simpa using hc₂)
        (by simpa using hanc) ?_
      intro β
      simp only [evalBits_onRegister_apply_reg]
      exact hpres (fun j ↦ β (r j))

end ClassicalBracketProg

/-!
## Section 2: `26`-`andCompute` (`104 T`) Ones'-Complement Signed Phase-Gradient Adder
-/

/-! ### 5.2 Range Unitary (`givensRangeUnitary`) & Turnaround Telescoping -/

theorem compose_disjointWires_right {N m k s : ℕ} {r₁ : QRegister s N} {r : QRegister m N}
    {rSub : QRegister k m} (hd : r₁.DisjointWires r) :
    r₁.DisjointWires (r.compose rSub) := by
  rw [QRegister.disjoint_iff] at hd ⊢
  intro i j hij
  exact hd i (rSub j) hij

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensCascade
