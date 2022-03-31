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

public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Logic.Function.Basic

/-!
# Variable stores and classical expressions

This file defines `Basic.Store` and `Basic.Expr`, along with variable substitution `Store.subst`.
-/

@[expose] public section

/-- The type of maps assigning to each variable a value of appropriate type.
For the moment, we restrict ourselves to `ℤ`.
Potential TODO: Extend to more general (or perhaps arbitrary) types. -/
abbrev Store (Var : Type*) : Type _ := Var → ℤ

namespace Store
variable {Var : Type*} [DecidableEq Var]

/-- The type of expression evaluated over the variable store. -/
abbrev Expr (Var : Type*) : Type _ := Store Var → ℤ

/-- Replace `x` with `e σ` in `σ`. -/
def subst (σ : Store Var) (x : Var) (e : Expr Var) : Store Var :=
  Function.update σ x (e σ)

theorem subst_eq_update (σ : Store Var) (x : Var) (e : Expr Var) :
    σ.subst x e = Function.update σ x (e σ) := rfl

@[simp, grind =]
theorem subst_self (σ : Store Var) (x : Var) (e : Expr Var) : σ.subst x e x = e σ :=
  Function.update_self _ _ _

@[simp, grind =]
theorem subst_of_ne (σ : Store Var) (x y : Var) (e : Expr Var) (h : y ≠ x) : σ.subst x e y = σ y :=
  Function.update_of_ne h _ _

@[simp]
lemma subst_self_eq (σ : Store Var) (v : Var) :
    σ.subst v (σ v : Expr Var) = σ :=
  Function.update_eq_self _ _

@[simp]
lemma subst_subst_same_const (σ : Store Var) (v : Var) (e : Expr Var) (val : ℤ) :
    (σ.subst v e).subst v val = σ.subst v val :=
  Function.update_idem _ _ _

lemma subst_comm {x y : Var} (hxy : x ≠ y) (σ : Store Var) (val_x val_y : ℤ) :
    (σ.subst y val_y).subst x val_x = (σ.subst x val_x).subst y val_y :=
  Function.update_comm hxy.symm _ _ _

end Store
