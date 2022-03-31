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

public import QuantumComputation.QuantumHoareLogic.CQState
public import Std.Do.WP.Monad

/-!
# A monad wrapping `CQState` transitions

This file defines `QMonad.Q`, and provides a `wp` instance for it.

Most of this file specializes to `Q State d Unit`, which corresponds via `Q.toStateFun` with
functions `CQState State d → CQState State d` which do not increase `CQState.trace`.

We equip `Q State d Unit` with an `OmegaCompletePartialOrder` induced from its state transitions.
-/

@[expose] public section

namespace QMonad
open Std.Do

/-- `Q` monad for classical states of type `State` and a single
quantum variable with `d` states. -/
def Q (State : Type) (d : ℕ) (α : Type) : Type :=
  {c : StateM (CQState State d) α //
    ∀ Δ : CQState State d, (Id.run <| StateT.run c Δ).2.trace ≤ Δ.trace}

namespace Q
variable {State : Type} {d : ℕ}

/-- The `Q` functor defined above is indeed a monad. -/
instance : Monad (Q State d) where
  pure a := ⟨pure a, fun _ => le_rfl⟩
  bind m f :=
    ⟨m.1 >>= (fun x ↦ (f x).1), fun Δ => by
      let +generalize t := (m.1 Δ).run
      exact ((f t.1).2 t.2).trans (m.2 Δ)⟩

/-- The `Q` functor defined above is a lawful monad. -/
instance : LawfulMonad (Q State d) where
  map_const := by intros; congr
  id_map := by intros; congr
  seqLeft_eq := by intros; congr
  seqRight_eq := by intros; congr
  pure_seq := by intros; congr
  bind_pure_comp := by intros; congr
  bind_map := by intros; congr
  pure_bind := by intros; congr
  bind_assoc := by
    intros
    apply Subtype.ext
    apply bind_assoc

/-- `WP` instance for `Q`. -/
instance : WPMonad (Q State d) (.arg (CQState State d) .pure) where
  wp m := wp m.1
  wp_pure := WPMonad.wp_pure
  wp_bind m f := WPMonad.wp_bind m.1 (fun a ↦ (f a).1)

/-- The state transition for an element of `Q State d Unit`.

Among other things, this is used to induce the order. -/
def toStateFun (a : Q State d Unit) : (CQState State d → CQState State d) :=
  fun Δ => Id.run (StateT.run a.1 Δ) |>.2

theorem trace_toStateFun_le (a : Q State d Unit) (Δ : CQState State d) :
    (a.toStateFun Δ).trace ≤ Δ.trace := a.2 Δ

theorem toStateFun_injective : Function.Injective (Q.toStateFun (State := State) (d := d)) :=
  fun _x _y hxy => Subtype.ext <| StateT.ext fun s => Id.ext <|
    Prod.ext (Subsingleton.elim _ _) congr($hxy s)

@[simp]
theorem toStateFun_pure (a : CQState State d) : (pure () : Q State d Unit).toStateFun a = a := rfl

@[simp]
theorem toStateFun_bind (m : Q State d Unit) (f : Unit → Q State d Unit) (Δ : CQState State d) :
    (m >>= f).toStateFun Δ = (f ()).toStateFun (m.toStateFun Δ) :=
  rfl

instance : PartialOrder (Q State d Unit) :=
  fast_instance% PartialOrder.lift Q.toStateFun Q.toStateFun_injective

/-- `Q.toStateFun` as an order-embedding. -/
@[simps]
def toStateFunEmb : Q State d Unit ↪o (CQState State d → CQState State d) where
  toFun := Q.toStateFun
  inj' := Q.toStateFun_injective
  map_rel_iff' := Iff.rfl

noncomputable instance : OmegaCompletePartialOrder (Q State d Unit) :=
  fast_instance% OmegaCompletePartialOrder.lift Q.toStateFunEmb.toOrderHom
    (fun ch ↦
      ⟨modify (OmegaCompletePartialOrder.ωSup (ch.map Q.toStateFunEmb.toOrderHom)),
       fun Δ ↦ CQState.trace_ωSup_le ((ch.map Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom Δ))
         Δ.trace (fun i ↦ (ch i).trace_toStateFun_le Δ)⟩)
    (fun _ _ h ↦ h)
    (fun _ ↦ rfl)

@[simp]
lemma val_ωSup (ch : OmegaCompletePartialOrder.Chain (Q State d Unit)) :
    (OmegaCompletePartialOrder.ωSup ch).1 =
      modify (OmegaCompletePartialOrder.ωSup (ch.map Q.toStateFunEmb.toOrderHom)) := rfl

@[simp]
theorem toStateFun_ωSup (ch : OmegaCompletePartialOrder.Chain (Q State d Unit)) :
    (OmegaCompletePartialOrder.ωSup ch).toStateFun =
      OmegaCompletePartialOrder.ωSup (ch.map Q.toStateFunEmb.toOrderHom) := rfl

@[gcongr]
lemma bind_mono_right {x : Q State d Unit} {f g : Unit → Q State d Unit} (h' : f ≤ g) :
    (x >>= f) ≤ (x >>= g) :=
  fun Δ => h' () (x.toStateFun Δ)

end Q

end QMonad
