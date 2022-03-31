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

public import QuantumComputation.Algorithms.QFT.Operators
public import QuantumComputation.QuantumHoareLogic.WP
import QuantumInfo.States.Mixed.MState

/-!
# Quantum Fourier Transform verification and weakest preconditions

This module defines the generic QFT programs in the `QProg` DSL and proves:
1. A generic weakest-precondition lemma for 1-indexed counting
`while` loops (`wp_qWhile_loopUnitary`).
2. Exact weakest-precondition formulas for the inner and outer while loops
   (`wp_qftInnerLoopGen`, `wp_qftOuterLoopGen`).
3. Exact weakest-precondition formulas for the complete generic QFT program
   (`wp_qftProgGen_const`).
-/

@[expose] public section

open Operator QProg.Notation
open scoped Matrix ComplexOrder
open Store (Expr)

namespace QFT

variable {Var : Type} [DecidableEq Var]

/-!
## Generic QFT program AST
-/

/-- Generic inner loop body: $\bar{q}[y, x] \apply CR(y - x + 1);\ y := y + 1$. -/
noncomputable def qftInnerBodyGen {d : ℕ} (n : ℕ)
    (crGate : Fin n → Fin n → ℕ → Unitary d) (x y : Var) : QProg Var d :=
  applyIndexed2 n (fun i j ↦ crGate i j (i.val - j.val + 1)) (fun σ ↦ σ y) (fun σ ↦ σ x) ;;
  y ≔ (fun σ ↦ σ y + 1)

/-- Generic inner while loop: $\mathbf{while}\ y \le n\ \mathbf{do}\ \dots$. -/
noncomputable def qftInnerLoopGen {d : ℕ} (n : ℕ)
    (crGate : Fin n → Fin n → ℕ → Unitary d) (x y : Var) : QProg Var d :=
  qwhile (fun σ ↦ σ y ≤ n) loop (qftInnerBodyGen n crGate x y)

/-- Generic outer loop body: $\bar{q}[x] \apply H;\ y := x + 1;\ \mathit{innerLoop};\ x := x + 1$.
-/
noncomputable def qftOuterBodyGen {d : ℕ} (n : ℕ)
    (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (x y : Var) : QProg Var d :=
  applyIndexed1 n hGate (fun σ ↦ σ x) ;;
  y ≔ (fun σ ↦ σ x + 1) ;;
  qftInnerLoopGen n crGate x y ;;
  x ≔ (fun σ ↦ σ x + 1)

/-- Generic outer while loop: $\mathbf{while}\ x \le n\ \mathbf{do}\ \dots$. -/
noncomputable def qftOuterLoopGen {d : ℕ} (n : ℕ)
    (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (x y : Var) : QProg Var d :=
  qwhile (fun σ ↦ σ x ≤ n) loop (qftOuterBodyGen n hGate crGate x y)

/-- Generic complete QFT program. -/
noncomputable def qftProgGen {d : ℕ} (n : ℕ)
    (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (swapGate : Unitary d) (x y : Var) : QProg Var d :=
  apply swapGate ;;
  x ≔ (1 : Expr Var) ;;
  qftOuterLoopGen n hGate crGate x y

/-!
## Weakest preconditions for the counting loops and full QFT program
-/

/-- Generic weakest precondition for a 1-indexed counting loop `while v ≤ n do body`. -/
theorem wp_qWhile_loopUnitary {d : ℕ} [NeZero d]
    (n : ℕ) (f : Fin n → Unitary d) (v : Var) (body : QProg Var d)
    (P : Store Var → Prop) (next : Store Var → Store Var)
    (Θ : CQAssertion (Store Var) d)
    (hbody : ∀ (m : ℕ) (hm : m < n) (Ψ : CQAssertion (Store Var) d) (σ : Store Var),
      P σ → σ v = (m + 1 : ℤ) →
      wp body Ψ σ = (Ψ (next σ)).conjUnitary (star (f ⟨m, hm⟩)))
    (hnext_v : ∀ σ : Store Var, next σ v = σ v + 1)
    (hnext_P : ∀ σ : Store Var, P σ → P (next σ))
    (hnext_Θ : ∀ σ : Store Var,
      Θ (Store.subst (next σ) v ((n + 1 : ℤ) : Expr Var)) =
        Θ (Store.subst σ v ((n + 1 : ℤ) : Expr Var)))
    {m : ℕ} (hm : m ≤ n) (σ : Store Var) (hP : P σ) (hv : σ v = (m + 1 : ℤ)) :
    wp (qwhile (fun τ ↦ τ v ≤ n) loop body) Θ σ =
      (Θ (Store.subst σ v ((n + 1 : ℤ) : Expr Var))).conjUnitary
        (star (loopUnitary n f m)) := by
  apply wp_qWhile_eq_of_stabilizes (fun τ ↦ τ v ≤ n) body Θ σ _ (n - m + 1)
  have haux : ∀ rem m : ℕ, n - m = rem → m ≤ n →
      ∀ k : ℕ, rem + 1 ≤ k → ∀ σ : Store Var, P σ → σ v = (m + 1 : ℤ) →
      whileRecWP (wp body) (fun τ ↦ τ v ≤ n) k Θ σ =
        (Θ (Store.subst σ v ((n + 1 : ℤ) : Expr Var))).conjUnitary
          (star (loopUnitary n f m)) := by
    intro rem
    induction rem with
    | zero =>
        intro m hrem hm k hk σ hP hv
        have hmn : m = n := by omega
        subst m
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
        rw [whileRecWP]
        have hguard : ¬ (σ v ≤ n) := by omega
        simp only [hguard, ↓reduceIte]
        rw [loopUnitary_of_ge n f (le_refl n), star_one, Observable.one_conjUnitary, ← hv,
          Store.subst_self_eq σ v]
    | succ r ih =>
        intro m hrem hm k hk σ hP hv
        have hlt : m < n := by omega
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
        rw [whileRecWP]
        have hguard : σ v ≤ n := by omega
        simp only [hguard, ↓reduceIte]
        rw [hbody m hlt _ σ hP hv,
          ih (m + 1) (by omega) (by omega) k' (by omega) (next σ) (hnext_P σ hP)
            (by rw [hnext_v, hv]; push_cast; ring)]
        rw [hnext_Θ, Observable.conjUnitary_conjUnitary, ← star_mul, ← loopUnitary_step n f hlt]
  intro k hk
  exact haux (n - m) m rfl hm k hk σ hP hv

/-- Exact weakest precondition for the generic inner loop. -/
theorem wp_qftInnerLoopGen {d : ℕ} [NeZero d]
    (n : ℕ) (crGate : Fin n → Fin n → ℕ → Unitary d) (x y : Var) (hxy : x ≠ y)
    (ℓ : Fin n) {m : ℕ} (hm : m ≤ n)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var)
    (hx : σ x = (ℓ.val + 1 : ℤ)) (hy : σ y = (m + 1 : ℤ)) :
    wp (qftInnerLoopGen n crGate x y) Θ σ =
      (Θ (Store.subst σ y ((n + 1 : ℤ) : Expr Var))).conjUnitary
        (star (innerLoopUnitaryGen n crGate ℓ m)) := by
  refine wp_qWhile_loopUnitary n (fun idx ↦ crGate idx ℓ (idx.val - ℓ.val + 1)) y
    (qftInnerBodyGen n crGate x y) (fun τ ↦ τ x = (ℓ.val + 1 : ℤ))
    (fun τ ↦ Store.subst τ y (fun ρ ↦ ρ y + 1)) Θ ?_ ?_ ?_ ?_ hm σ hx hy
  · intro j hj Ψ τ hτx hτy
    exact wp_applyIndexed2 n (fun i k ↦ crGate i k (i.val - k.val + 1))
      (fun ρ ↦ ρ y) (fun ρ ↦ ρ x) ⟨j, hj⟩ ℓ
      (Ψ.subst y (fun ρ ↦ ρ y + 1)) τ hτy hτx
  · intro τ; simp [Store.subst]
  · intro τ hτ; simp [Store.subst, hxy, hτ]
  · intro τ; rw [Store.subst_subst_same_const]

theorem wp_qftOuterBodyGen {d : ℕ} [NeZero d]
    (n : ℕ) (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (x y : Var) (hxy : x ≠ y) {ℓ : ℕ} (hℓ : ℓ < n)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) (hx : σ x = (ℓ + 1 : ℤ)) :
    wp (qftOuterBodyGen n hGate crGate x y) Θ σ =
      (Θ (Store.subst (Store.subst σ y ((n + 1 : ℤ) : Expr Var)) x
        (fun τ ↦ τ x + 1))).conjUnitary
        (star (innerLoopUnitaryGen n crGate ⟨ℓ, hℓ⟩ (ℓ + 1) * hGate ⟨ℓ, hℓ⟩)) := by
  simp only [qftOuterBodyGen, wp]
  rw [wp_applyIndexed1 n hGate (fun τ ↦ τ x) ⟨ℓ, hℓ⟩ _ σ hx]
  simp only [CQAssertion.qAssign_apply, CQAssertion.subst_apply]
  have hx₁ : Store.subst σ y (fun τ ↦ τ x + 1) x = ((⟨ℓ, hℓ⟩ : Fin n).val + 1 : ℤ) := by
    simp [Store.subst, hxy, hx]
  have hy₁ : Store.subst σ y (fun τ ↦ τ x + 1) y = ((ℓ + 1 : ℕ) + 1 : ℤ) := by
    simp [Store.subst, hx]
  rw [wp_qftInnerLoopGen n crGate x y hxy ⟨ℓ, hℓ⟩ (by omega : ℓ + 1 ≤ n) _ _ hx₁ hy₁]
  simp only [Observable.conjUnitary_conjUnitary, ← star_mul, CQAssertion.subst_apply,
    Store.subst_subst_same_const]

/-- Exact weakest precondition for the generic outer loop on any `y`-independent assertion `Θ`. -/
theorem wp_qftOuterLoopGen {d : ℕ} [NeZero d]
    (n : ℕ) (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (x y : Var) (hxy : x ≠ y) {ℓ : ℕ} (hℓ : ℓ ≤ n)
    (Θ : CQAssertion (Store Var) d) (hΘ_y : ∀ τ val, Θ (Store.subst τ y (val : Expr Var)) = Θ τ)
    (σ : Store Var) (hx : σ x = (ℓ + 1 : ℤ)) :
    wp (qftOuterLoopGen n hGate crGate x y) Θ σ =
      (Θ (Store.subst σ x ((n + 1 : ℤ) : Expr Var))).conjUnitary
        (star (outerLoopUnitaryGen n hGate crGate ℓ)) := by
  refine wp_qWhile_loopUnitary n
    (fun idx ↦ innerLoopUnitaryGen n crGate idx (idx.val + 1) * hGate idx) x
    (qftOuterBodyGen n hGate crGate x y) (fun _ ↦ True)
    (fun τ ↦ Store.subst (Store.subst τ y ((n + 1 : ℤ) : Expr Var)) x (fun ρ ↦ ρ x + 1))
    Θ ?_ ?_ ?_ ?_ hℓ σ trivial hx
  · intro j hj Ψ τ _ hτx
    exact wp_qftOuterBodyGen n hGate crGate x y hxy hj Ψ τ hτx
  · intro τ; simp [Store.subst, hxy]
  · intro _ _; trivial
  · intro τ; rw [Store.subst_subst_same_const, Store.subst_comm hxy, hΘ_y]

/-- Exact weakest precondition for the complete generic QFT program on any constant observable
assertion. -/
theorem wp_qftProgGen_const {d : ℕ} [NeZero d]
    (n : ℕ) (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (swapGate : Unitary d) (x y : Var) (hxy : x ≠ y) (A : Observable (Fin d)) :
    wp (qftProgGen n hGate crGate swapGate x y) (fun _ ↦ A) =
      (fun _ ↦ A.conjUnitary (star (qftCircuitUnitaryGen n hGate crGate swapGate))) := by
  funext σ
  have hx1 : (Store.subst σ x (1 : Expr Var)) x = (0 + 1 : ℤ) := by simp [Store.subst]
  simpa [qftProgGen, wp, qftCircuitUnitaryGen] using
    congrArg (Observable.conjUnitary (star swapGate))
      (wp_qftOuterLoopGen n hGate crGate x y hxy (Nat.zero_le n)
        (fun _ ↦ A) (fun _ _ ↦ rfl)
        (Store.subst σ x (1 : Expr Var)) hx1)

end QFT
