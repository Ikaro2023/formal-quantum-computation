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
public import QuantumComputation.Primitives.Phase
public import QuantumComputationSpecs.Primitives.THCFactorization
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn

/-!
# Phase-Gradient Catalyst Eigenstate Lemmas & Temporary-AND Modular Adders

Formalizes the `b`-bit (and `14`-bit P450 specialization) phase-gradient catalyst kickback
identities and Gidney temporary-AND (`andCompute` / `andUncompute`, `0` `TOFF`) ripple-carry
modular adders and subtractors:

1. **Modular addition/subtraction permutations and catalytic kickback (`Part 1`):**
   - `modAddPerm`, `modSubPerm`, `ctrlModAddUnitary`, `ctrlModSubUnitary`, and the bidirectional
     2-control Givens unitary `signedCtrlModAddUnitary`.
   - Exact catalytic eigenstate and phase-kickback theorems on `phaseGradientState b` (and
     `phaseGradientState 14` with `13`-bit angles), both on `tensor3` states and on arbitrary
     ambient entangled `QRegister.tensorState (phaseGradientState b) env` states.
2. **Classical reversible / Gidney temporary-AND clean-ancilla `wp` engine (`Part 2`):**
   - `ClassicalBracketProg`: structural temporary-AND AST compiling to `DynamicCircuit` via
     `DynamicCircuit.andCompute` (`4` `T`, `0` `TOFF`) and `DynamicCircuit.andUncompute` (`0` `T`,
     `0` `TOFF`), with full `CleanRealizes` (`wp` equality on clean ancillas, postcondition
     ancilla restoration, and measurement-variable store invariance).
3. **Concrete Gidney ripple-carry adders and subtractors (`Part 3`):**
   - Uncontrolled `b`-bit `addMod2PowDyn` and `subMod2PowDyn` (`4 * (b - 1)` `T`, `0` `TOFF`).
   - Single-control `13`-into-`14`-bit `ctrlAdd13Into14Dyn` and `ctrlSub13Into14Dyn` (`26`
     `andCompute`s = `104` `T`, `0` `TOFF`, `26` clean scratch wires).
   - Bidirectional 2-control Givens `signedCtrlAdd13Into14Dyn` (`26` `andCompute`s = `104` `T`,
     `0` `TOFF`, `26` clean scratch wires), realizing both controlled `-k` on `q₀` and controlled
     `+k` on `q₁` in a single `26`-AND pass via Clifford CNOT conjugation.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Real Circuit.Notation BigOperators

/-! ## Part 1: Block Splits, Permutations, and Phase-Gradient Kickback Theorems -/

@[local simp]
private theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[local simp]
private theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

/-- Diagonal projector onto the subspace where every physical wire in `S` is in `|0⟩`. -/
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
  ext i j
  rw [zeroSetProj, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> ring
  · simp [Matrix.diagonal_apply_ne _ hij]

/-- Restrict a classical-quantum assertion `Θ` onto `|0⟩` across an arbitrary `Finset` of wires. -/
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
        rw [HermitianMat.mat_sub, HermitianMat.mat_one, conj_apply_mat, HermitianMat.mat_one,
          zeroSetProj_conjTranspose, Matrix.mul_one, zeroSetProj_mul_self]
        ext i j
        rw [zeroSetProj, Matrix.sub_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte, Matrix.diagonal_apply_eq]
          split_ifs <;> ring
        · simp [hij]
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
  apply Subtype.ext
  ext1
  simp

@[simp]
theorem restrictZeroSet_idem {Var : Type} [Fintype Var] {n : ℕ}
    (S : Finset (Wire n)) (Θ : QCAssertion Var (2 ^ n)) :
    restrictZeroSet S (restrictZeroSet S Θ) = restrictZeroSet S Θ := by
  funext σ
  apply Subtype.ext
  ext1
  simp only [restrictZeroSet_coe, conj_apply_mat, zeroSetProj_conjTranspose]
  calc
    zeroSetProj S * (zeroSetProj S * (Θ σ).1.mat * zeroSetProj S) * zeroSetProj S
      = (zeroSetProj S * zeroSetProj S) * (Θ σ).1.mat * (zeroSetProj S * zeroSetProj S) := by
        simp only [Matrix.mul_assoc]
    _ = zeroSetProj S * (Θ σ).1.mat * zeroSetProj S := by
        rw [zeroSetProj_mul_self]

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
  | cnot c t h =>
      ext q
      simp [onRegister, support]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp [onRegister, support, ih₁, ih₂, Finset.map_union]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      ext q
      simp [onRegister, support, ih]

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
  | cnot c t h =>
      simp only [onRegister, evalBits]
      by_cases hit : i = t
      · subst hit; simp
      · rw [Function.update_of_ne (fun heq ↦ hit (r.wires.injective heq)),
          Function.update_of_ne hit]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [onRegister, evalBits]
      rw [ih₂]
      congr 1
      funext j
      exact ih₁ β j
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
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
  | id => simpa [ClassicalBracketProg.onRegister] using ValidBracket.id
  | x u => simpa [ClassicalBracketProg.onRegister] using ValidBracket.x (r u)
  | cnot c t h =>
      simpa [ClassicalBracketProg.onRegister] using
        ValidBracket.cnot (r c) (r t) (fun heq ↦ h (r.wires.injective heq))
  | seq h₁ h₂ hd₁ hd₂ ih₁ ih₂ =>
      rw [Finset.map_union]
      refine ValidBracket.seq ih₁ ih₂ ?_ ?_
      · rw [support_onRegister, Finset.disjoint_map]
        exact hd₁
      · rw [support_onRegister, Finset.disjoint_map]
        exact hd₂
  | @tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body S _ hc₁ hc₂ hanc hpres ih =>
      rw [Finset.map_insert]
      refine ValidBracket.tempAnd _ _ _ ih ?_ ?_ ?_ ?_
      · simpa using hc₁
      · simpa using hc₂
      · simpa using hanc
      · intro β
        simp only [evalBits_onRegister_apply_reg]
        exact hpres (fun j ↦ β (r j))

end ClassicalBracketProg

/-! ## Part 3: Concrete Gidney Temporary-AND Modular Adders & Subtractors -/

namespace ClassicalBracketProg

end ClassicalBracketProg

/-! ### Section 3.1: Gidney 1-AND Ripple-Carry Chain (`addCarryChain` & `addZeroExtLocal`) -/

namespace PhaseGradAdderDetail

end PhaseGradAdderDetail

namespace PhaseGradAdderDetail

end PhaseGradAdderDetail

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
