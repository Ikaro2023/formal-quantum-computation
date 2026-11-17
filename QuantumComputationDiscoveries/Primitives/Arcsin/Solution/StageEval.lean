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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.PolyBoundA

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl

open Function Operator

abbrev numQubits : Nat := 100
abbrev numAnc : Nat := 50
abbrev totalAndCount : Nat := 776

inductive Op102 : Type where
  | x (q : Nat)
  | cx (c t : Nat)
  | and4t (c1 c2 t : Nat)
  | rccx0 (c1 c2 t : Nat)
  | rccx1 (c1 c2 t : Nat)
  | unand (c1 c2 t : Nat)
  | unquad (quads : List (Nat × Nat)) (lins : List Nat) (t : Nat)
  | z (q : Nat)
  | cz (c1 c2 : Nat)
  | hGadget (t : Nat) (posSteps negSteps : List (Bool × List Nat))
      (undoConst : Bool) (undoLins : List Nat)

@[inline] def mkX (q : Nat) : Op102 := .x q
@[inline] def mkCX (c t : Nat) : Op102 := .cx c t
@[inline] def mkAnd (c1 c2 t : Nat) : Op102 := .and4t c1 c2 t
@[inline] def mkRccx0 (c1 c2 t : Nat) : Op102 := .rccx0 c1 c2 t
@[inline] def mkRccx1 (c1 c2 t : Nat) : Op102 := .rccx1 c1 c2 t
@[inline] def mkUnand (c1 c2 t : Nat) : Op102 := .unand c1 c2 t
@[inline] def mkZ (q : Nat) : Op102 := .z q
@[inline] def mkCZ (c1 c2 : Nat) : Op102 := .cz c1 c2

def validUnquad102 (qs : List (Nat × Nat)) (ls : List Nat) (t : Nat) : Prop :=
  (∀ p ∈ qs, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧
  (∀ c ∈ ls, c < 100 ∧ c ≠ t) ∧
  t < 100

instance (qs : List (Nat × Nat)) (ls : List Nat) (t : Nat) :
    Decidable (validUnquad102 qs ls t) := by
  unfold validUnquad102
  infer_instance

def evalQuadBool102 (m : Fin 100 → Bool) : List (Nat × Nat) → Bool
  | [] => false
  | p :: qs =>
      let b := if h : p.1 < 100 ∧ p.2 < 100 then m ⟨p.1, h.1⟩ && m ⟨p.2, h.2⟩ else false
      xor b (evalQuadBool102 m qs)

def evalLinBool102 (m : Fin 100 → Bool) : List Nat → Bool
  | [] => false
  | c :: ls =>
      let b := if h : c < 100 then m ⟨c, h⟩ else false
      xor b (evalLinBool102 m ls)

def evalUnquad102 (m : Fin 100 → Bool) (qs : List (Nat × Nat)) (ls : List Nat) : Bool :=
  xor (evalQuadBool102 m qs) (evalLinBool102 m ls)

def add1Bools (b0 b1 b2 dt : Bool) : Bool × Bool × Bool :=
  let c0 := b0 && dt
  let b0' := xor b0 dt
  let c1 := b1 && c0
  (b0', xor b1 c0, xor b2 c1)

def add7Bools (b0 b1 b2 dt : Bool) : Bool × Bool × Bool :=
  let c0 := b0 && dt
  let b0' := xor b0 dt
  let c1 := b1 && c0
  let b1_a := xor b1 c0
  let b2_a := xor b2 c1
  let c1_b := b1_a && dt
  (b0', xor b1_a dt, xor (xor b2_a c1_b) dt)

def evalHPosBool (m : Fin 100 → Bool) :
    List (Bool × List Nat) → (Bool × Bool × Bool × Bool) → (Bool × Bool × Bool × Bool)
  | [], st => st
  | (xc, ls) :: rest, (dt, b0, b1, b2) =>
      let dt' := xor dt (xor xc (evalLinBool102 m ls))
      let p := add1Bools b0 b1 b2 dt'
      evalHPosBool m rest (dt', p.1, p.2.1, p.2.2)

def evalHNegBool (m : Fin 100 → Bool) :
    List (Bool × List Nat) → (Bool × Bool × Bool × Bool) → (Bool × Bool × Bool × Bool)
  | [], st => st
  | (xc, ls) :: rest, (dt, b0, b1, b2) =>
      let dt' := xor dt (xor xc (evalLinBool102 m ls))
      let p := add7Bools b0 b1 b2 dt'
      evalHNegBool m rest (dt', p.1, p.2.1, p.2.2)

def evalHGadgetBool (m : Fin 100 → Bool)
    (posSteps negSteps : List (Bool × List Nat))
    (undoConst : Bool) (undoLins : List Nat) : (Bool × Bool × Bool × Bool) :=
  let st1 := evalHPosBool m posSteps (false, false, false, false)
  let st2 := evalHNegBool m negSteps st1
  let dt_f := xor st2.1 (xor undoConst (evalLinBool102 m undoLins))
  (dt_f, st2.2.1, st2.2.2.1, st2.2.2.2)

def xorLinMask (t : Nat) : List Nat → Nat → Option Nat
  | [], m => some m
  | c :: cs, m =>
      cond (Nat.blt c 100 && !Nat.beq c t)
        (xorLinMask t cs (m ^^^ Nat.shiftLeft 1 c))
        none

def stepHStatic (t : Nat) :
    List (Bool × List Nat) → (Nat × Bool × Nat × Bool) → Option (Nat × Bool × Nat × Bool)
  | [], st => some st
  | (xc, ls) :: rest, (dtM, dtC, b0M, b0C) =>
      match xorLinMask t ls dtM with
      | some dtM' =>
          let dtC' := xor dtC xc
          stepHStatic t rest (dtM', dtC', b0M ^^^ dtM', xor b0C dtC')
      | none => none

def checkHGadgetStatic (t : Nat) (posSteps negSteps : List (Bool × List Nat))
    (undoConst : Bool) (undoLins : List Nat) : Bool :=
  Nat.blt t 100 &&
  Nat.beq posSteps.length negSteps.length &&
  match stepHStatic t posSteps (0, false, 0, false) with
  | some st1 =>
      match stepHStatic t negSteps st1 with
      | some (dtM2, dtC2, b0M2, b0C2) =>
          match xorLinMask t undoLins dtM2 with
          | some dtMf =>
              Nat.beq dtMf 0 && !(xor dtC2 undoConst) &&
              Nat.beq b0M2 0 && !b0C2
          | none => false
      | none => false
  | none => false

theorem checkHGadgetStatic_lt {t : Nat} {posSteps negSteps : List (Bool × List Nat)}
    {undoConst : Bool} {undoLins : List Nat}
    (h : checkHGadgetStatic t posSteps negSteps undoConst undoLins = true) : t < 100 := by
  unfold checkHGadgetStatic at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1.1

def execOp102 (m : Fin 100 → Bool) : Op102 → Option (Fin 100 → Bool)
  | .x q =>
      if h : q < 100 then
        some (Function.update m ⟨q, h⟩ (!m ⟨q, h⟩))
      else none
  | .cx c t =>
      if h : c < 100 ∧ t < 100 ∧ c ≠ t then
        some (Function.update m ⟨t, h.2.1⟩ (xor (m ⟨t, h.2.1⟩) (m ⟨c, h.1⟩)))
      else none
  | .and4t c1 c2 t =>
      if h : c1 < 100 ∧ c2 < 100 ∧ t < 100 ∧ c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t then
        if m ⟨t, h.2.2.1⟩ = false then
          some (Function.update m ⟨t, h.2.2.1⟩ (m ⟨c1, h.1⟩ && m ⟨c2, h.2.1⟩))
        else none
      else none
  | .rccx0 c1 c2 t =>
      if h : c1 < 100 ∧ c2 < 100 ∧ t < 100 ∧ c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t then
        if (m ⟨c1, h.1⟩ && m ⟨c2, h.2.1⟩ && m ⟨t, h.2.2.1⟩) = false then
          some (Function.update m ⟨t, h.2.2.1⟩
            (xor (m ⟨t, h.2.2.1⟩) (m ⟨c1, h.1⟩ && m ⟨c2, h.2.1⟩)))
        else none
      else none
  | .rccx1 c1 c2 t =>
      if h : c1 < 100 ∧ c2 < 100 ∧ t < 100 ∧ c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t then
        if (m ⟨c1, h.1⟩ && m ⟨c2, h.2.1⟩ && !m ⟨t, h.2.2.1⟩) = false then
          some (Function.update m ⟨t, h.2.2.1⟩
            (xor (m ⟨t, h.2.2.1⟩) (m ⟨c1, h.1⟩ && m ⟨c2, h.2.1⟩)))
        else none
      else none
  | .unand c1 c2 t =>
      if h : c1 < 100 ∧ c2 < 100 ∧ t < 100 ∧ c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t then
        if m ⟨t, h.2.2.1⟩ = (m ⟨c1, h.1⟩ && m ⟨c2, h.2.1⟩) then
          some (Function.update m ⟨t, h.2.2.1⟩ false)
        else none
      else none
  | .unquad qs ls t =>
      if h : validUnquad102 qs ls t then
        if m ⟨t, h.2.2⟩ = evalUnquad102 m qs ls then
          some (Function.update m ⟨t, h.2.2⟩ false)
        else none
      else none
  | .z q =>
      if q < 100 then some m else none
  | .cz c1 c2 =>
      if c1 < 100 ∧ c2 < 100 ∧ c1 ≠ c2 then some m else none
  | .hGadget t posSteps negSteps undoConst undoLins =>
      if h : checkHGadgetStatic t posSteps negSteps undoConst undoLins = true then
        have ht : t < 100 := checkHGadgetStatic_lt h
        if m ⟨t, ht⟩ = false then
          let res := evalHGadgetBool m posSteps negSteps undoConst undoLins
          some (Function.update m ⟨t, ht⟩ res.2.2.1)
        else none
      else none

def phaseOp102 (m : Fin 100 → Bool) : Op102 → Bool
  | .z q => if h : q < 100 then m ⟨q, h⟩ else false
  | .cz c1 c2 =>
      if h : c1 < 100 ∧ c2 < 100 then m ⟨c1, h.1⟩ && m ⟨c2, h.2⟩ else false
  | .hGadget _ posSteps negSteps undoConst undoLins =>
      (evalHGadgetBool m posSteps negSteps undoConst undoLins).2.2.2
  | _ => false

def phaseList102 : List Op102 → (Fin 100 → Bool) → Bool
  | [], _ => false
  | op :: ops, m =>
      match execOp102 m op with
      | none => false
      | some m' => xor (phaseOp102 m op) (phaseList102 ops m')

def Op102.noPhase : Op102 → Bool
  | .z _ => false
  | .cz _ _ => false
  | .hGadget _ _ _ _ _ => false
  | _ => true

theorem phaseOp102_of_noPhase (m : Fin 100 → Bool) {op : Op102} (h : op.noPhase = true) :
    phaseOp102 m op = false := by
  cases op <;> first | rfl | cases h

theorem phaseList102_of_noPhase : ∀ (ops : List Op102) (m : Fin 100 → Bool),
    (ops.all Op102.noPhase) = true → phaseList102 ops m = false
  | [], _, _ => rfl
  | op :: ops, m, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    dsimp only [phaseList102]
    cases execOp102 m op with
    | none => rfl
    | some m' =>
      dsimp only
      rw [phaseOp102_of_noPhase m h.1, phaseList102_of_noPhase ops m' h.2, Bool.false_xor]

def execList102 : List Op102 → (Fin 100 → Bool) → Option (Fin 100 → Bool)
  | [], m => some m
  | op :: ops, m =>
      match execOp102 m op with
      | none => none
      | some m' => execList102 ops m'

theorem execList102_append (l1 l2 : List Op102) (m : Fin 100 → Bool) :
    execList102 (l1 ++ l2) m = (execList102 l1 m).bind (execList102 l2) := by
  induction l1 generalizing m with
  | nil => rfl
  | cons op ops ih =>
    simp only [List.cons_append, execList102]
    cases execOp102 m op <;> simp [ih]

theorem phaseList102_append (l1 l2 : List Op102) {m m1 : Fin 100 → Bool}
    (h1 : execList102 l1 m = some m1) :
    phaseList102 (l1 ++ l2) m = xor (phaseList102 l1 m) (phaseList102 l2 m1) := by
  induction l1 generalizing m with
  | nil =>
    injection h1 with hm; subst hm
    simp [phaseList102]
  | cons op ops ih =>
    dsimp only [execList102] at h1
    cases hop : execOp102 m op with
    | none => rw [hop] at h1; cases h1
    | some ma =>
      rw [hop] at h1
      simp only [List.cons_append, phaseList102, hop, ih h1, Bool.xor_assoc]

theorem blt_false_iff (a b : Nat) : Nat.blt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, Nat.blt_eq, not_lt]

theorem beq_false_iff (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

def Op102.noUnquad : Op102 → Bool
  | .unquad _ _ _ => false
  | .z _ => false
  | .cz _ _ => false
  | .hGadget _ _ _ _ _ => false
  | _ => true

def revOp : Op102 → Op102
  | .x q => .x q
  | .cx c t => .cx c t
  | .and4t c1 c2 t => .unand c1 c2 t
  | .rccx0 c1 c2 t => .rccx1 c1 c2 t
  | .rccx1 c1 c2 t => .rccx0 c1 c2 t
  | .unand c1 c2 t => .and4t c1 c2 t
  | .unquad qs ls t => .unquad qs ls t
  | .z q => .z q
  | .cz c1 c2 => .cz c1 c2
  | .hGadget t pos neg uc ul => .hGadget t pos neg uc ul

def revOps (ops : List Op102) : List Op102 :=
  (ops.map revOp).reverse

theorem rccx0_rev_guard (a b c : Bool) (h : (a && b && c) = false) :
    (a && b && !xor c (a && b)) = false := by
  cases a <;> cases b <;> cases c <;> first | rfl | cases h

theorem rccx1_rev_guard (a b c : Bool) (h : (a && b && !c) = false) :
    (a && b && xor c (a && b)) = false := by
  cases a <;> cases b <;> cases c <;> first | rfl | cases h

theorem execOp102_revOp {m m' : Fin 100 → Bool} {op : Op102}
    (hnq : op.noUnquad = true)
    (h : execOp102 m op = some m') :
    execOp102 m' (revOp op) = some m := by
  cases op with
  | x q =>
    dsimp only [execOp102] at h
    split_ifs at h with hq
    injection h with hm'; subst hm'
    dsimp only [revOp, execOp102]
    rw [dite_eq_left hq]
    congr 1; funext w
    by_cases hw : w = ⟨q, hq⟩
    · subst hw; simp [Function.update_self]
    · simp [Function.update_of_ne hw]
  | cx c t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc
    injection h with hm'; subst hm'
    dsimp only [revOp, execOp102]
    rw [dite_eq_left hc]
    congr 1; funext w
    have hct : (⟨c, hc.1⟩ : Fin 100) ≠ ⟨t, hc.2.1⟩ := fun e => hc.2.2 (congrArg Fin.val e)
    by_cases hw : w = ⟨t, hc.2.1⟩
    · subst hw
      simp [Function.update_self, Function.update_of_ne hct]
    · simp [Function.update_of_ne hw]
  | and4t c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    dsimp only [revOp, execOp102]
    rw [dite_eq_left hc]
    have hc1t : (⟨c1, hc.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ := fun e => hc.2.2.2.2.1 (congrArg Fin.val e)
    have hc2t : (⟨c2, hc.2.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ :=
      fun e => hc.2.2.2.2.2 (congrArg Fin.val e)
    rw [Function.update_self, Function.update_of_ne hc1t, Function.update_of_ne hc2t,
        ite_eq_left rfl]
    congr 1; funext w
    by_cases hw : w = ⟨t, hc.2.2.1⟩
    · subst hw; simp [Function.update_self, hmt]
    · simp [Function.update_of_ne hw]
  | rccx0 c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    dsimp only [revOp, execOp102]
    rw [dite_eq_left hc]
    have hc1t : (⟨c1, hc.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ := fun e => hc.2.2.2.2.1 (congrArg Fin.val e)
    have hc2t : (⟨c2, hc.2.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ :=
      fun e => hc.2.2.2.2.2 (congrArg Fin.val e)
    rw [Function.update_self, Function.update_of_ne hc1t, Function.update_of_ne hc2t,
        ite_eq_left (rccx0_rev_guard _ _ _ hmt)]
    congr 1; funext w
    by_cases hw : w = ⟨t, hc.2.2.1⟩
    · subst hw; simp [Function.update_self]
    · simp [Function.update_of_ne hw]
  | rccx1 c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    dsimp only [revOp, execOp102]
    rw [dite_eq_left hc]
    have hc1t : (⟨c1, hc.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ := fun e => hc.2.2.2.2.1 (congrArg Fin.val e)
    have hc2t : (⟨c2, hc.2.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ :=
      fun e => hc.2.2.2.2.2 (congrArg Fin.val e)
    rw [Function.update_self, Function.update_of_ne hc1t, Function.update_of_ne hc2t,
        ite_eq_left (rccx1_rev_guard _ _ _ hmt)]
    congr 1; funext w
    by_cases hw : w = ⟨t, hc.2.2.1⟩
    · subst hw; simp [Function.update_self]
    · simp [Function.update_of_ne hw]
  | unand c1 c2 t =>
    dsimp only [execOp102] at h
    split_ifs at h with hc hmt
    injection h with hm'; subst hm'
    dsimp only [revOp, execOp102]
    rw [dite_eq_left hc, Function.update_self, ite_eq_left rfl]
    have hc1t : (⟨c1, hc.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ := fun e => hc.2.2.2.2.1 (congrArg Fin.val e)
    have hc2t : (⟨c2, hc.2.1⟩ : Fin 100) ≠ ⟨t, hc.2.2.1⟩ :=
      fun e => hc.2.2.2.2.2 (congrArg Fin.val e)
    rw [Function.update_of_ne hc1t, Function.update_of_ne hc2t]
    congr 1; funext w
    by_cases hw : w = ⟨t, hc.2.2.1⟩
    · subst hw; simp [Function.update_self, hmt]
    · simp [Function.update_of_ne hw]
  | unquad _ _ _ => cases hnq
  | z _ => cases hnq
  | cz _ _ => cases hnq
  | hGadget _ _ _ _ _ => cases hnq

theorem execList102_revOps : ∀ (ops : List Op102)
    (_ : (ops.all Op102.noUnquad) = true)
    {m m' : Fin 100 → Bool},
    execList102 ops m = some m' →
    execList102 (revOps ops) m' = some m
  | [], _, m, m', h => by injection h with h'; subst h'; rfl
  | op :: ops, hnq, m, m', h => by
    simp only [List.all_cons, Bool.and_eq_true] at hnq
    dsimp only [execList102] at h
    cases hop : execOp102 m op with
    | none => rw [hop] at h; cases h
    | some m1 =>
      rw [hop] at h
      have ih := execList102_revOps ops hnq.2 h
      have hrev : revOps (op :: ops) = revOps ops ++ [revOp op] := by simp [revOps]
      rw [hrev, execList102_append, ih, Option.bind_some, execList102, execOp102_revOp hnq.1 hop]
      rfl

theorem execList102_xorTargets {c : Nat} (hc : c < 100) :
    ∀ (ts : List Nat) (m : Fin 100 → Bool),
    ts.Nodup →
    (ts.all fun t => Nat.blt t 100 && !Nat.beq c t) = true →
    execList102 (ts.map (mkCX c)) m =
      some (fun w => if ts.elem w.val then xor (m w) (m ⟨c, hc⟩) else m w)
  | [], m, _, _ => by simp [execList102]
  | t :: rest, m, hnd, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true',
      beq_false_iff] at hall
    obtain ⟨⟨ht_lt, hct⟩, hrest_all⟩ := hall
    obtain ⟨ht_not_mem, hnd_rest⟩ := List.nodup_cons.mp hnd
    have hop : execOp102 m (mkCX c t) =
        some (Function.update m ⟨t, ht_lt⟩ (xor (m ⟨t, ht_lt⟩) (m ⟨c, hc⟩))) := by
      dsimp only [execOp102, mkCX]; rw [dite_eq_left ⟨hc, ht_lt, hct⟩]
    rw [List.map_cons, execList102, hop]
    dsimp only
    rw [execList102_xorTargets hc rest _ hnd_rest hrest_all]
    congr 1; funext w
    have hce : Function.update m ⟨t, ht_lt⟩ (xor (m ⟨t, ht_lt⟩) (m ⟨c, hc⟩)) ⟨c, hc⟩ = m ⟨c, hc⟩ :=
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; dsimp only at this; omega) _ _
    rw [hce, List.elem_cons]
    by_cases hwt : w.val = t
    · have hw_eq : w = ⟨t, ht_lt⟩ := Fin.ext hwt
      subst hw_eq
      simp [ht_not_mem, Function.update_self]
    · have hw_ne : w ≠ ⟨t, ht_lt⟩ := fun e => hwt (congrArg Fin.val e)
      have hb : (w.val == t) = false := beq_eq_false_iff_ne.mpr hwt
      rw [hb, Function.update_of_ne hw_ne]

def xorControlsBool (m : Fin 100 → Bool) : List Nat → Bool → Bool
  | [], acc => acc
  | c :: rest, acc =>
      xorControlsBool m rest (if h : c < 100 then xor acc (m ⟨c, h⟩) else acc)

theorem xorControlsBool_congr {m1 m2 : Fin 100 → Bool} :
    ∀ (cs : List Nat) (acc : Bool),
      (∀ c ∈ cs, ∀ hc : c < 100, m1 ⟨c, hc⟩ = m2 ⟨c, hc⟩) →
      xorControlsBool m1 cs acc = xorControlsBool m2 cs acc
  | [], acc, _ => rfl
  | c :: rest, acc, h => by
    dsimp only [xorControlsBool]
    have hc_eq : (if hc : c < 100 then xor acc (m1 ⟨c, hc⟩) else acc) =
        (if hc : c < 100 then xor acc (m2 ⟨c, hc⟩) else acc) := by
      split_ifs with hc
      · rw [h c List.mem_cons_self hc]
      · rfl
    rw [hc_eq]
    exact xorControlsBool_congr rest _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem execList102_xorControls {t : Nat} (ht : t < 100) :
    ∀ (cs : List Nat) (m : Fin 100 → Bool),
    (cs.all fun c => Nat.blt c 100 && !Nat.beq c t) = true →
    execList102 (cs.map fun c => mkCX c t) m =
      some (Function.update m ⟨t, ht⟩ (xorControlsBool m cs (m ⟨t, ht⟩)))
  | [], m, _ => by
    simp [execList102, xorControlsBool, Function.update_eq_self]
  | c :: rest, m, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true',
      beq_false_iff] at hall
    obtain ⟨⟨hc_lt, hct⟩, hrest⟩ := hall
    have hop : execOp102 m (mkCX c t) =
        some (Function.update m ⟨t, ht⟩ (xor (m ⟨t, ht⟩) (m ⟨c, hc_lt⟩))) := by
      dsimp only [execOp102, mkCX]; rw [dite_eq_left ⟨hc_lt, ht, hct⟩]
    rw [List.map_cons, execList102, hop]
    dsimp only
    set m1 := Function.update m ⟨t, ht⟩ (xor (m ⟨t, ht⟩) (m ⟨c, hc_lt⟩))
    rw [execList102_xorControls ht rest m1 hrest]
    congr 1
    funext w
    by_cases hwt : w = ⟨t, ht⟩
    · subst hwt
      simp only [Function.update_self, m1, xorControlsBool, dite_eq_left hc_lt]
      refine xorControlsBool_congr rest _ fun c' hc' hc'_lt => ?_
      have hc'_ne : (⟨c', hc'_lt⟩ : Fin 100) ≠ ⟨t, ht⟩ := by
        have h := List.all_eq_true.mp hrest c' hc'
        simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at h
        intro e; exact h.2 (congrArg Fin.val e)
      exact Function.update_of_ne hc'_ne _ _
    · simp only [Function.update_of_ne hwt, m1]

-- ============================================================================
-- Depth-7 WTree (wires 25..109)
-- ============================================================================

inductive WTree : Type where
  | leaf (v : Nat)
  | node (l r : WTree)

def tGet : Nat → WTree → Nat → Nat
  | _, .leaf v, _ => v
  | 0, .node l r, idx => cond (Nat.blt idx 1) (tGet 0 l idx) (tGet 0 r (idx - 1))
  | d + 1, .node l r, idx =>
      let half := Nat.shiftLeft 1 (d + 1)
      cond (Nat.blt idx half) (tGet d l idx) (tGet d r (idx - half))

def strictLeaf (v : Nat) : WTree :=
  match v with
  | 0 => .leaf 0
  | n + 1 => .leaf (n + 1)

theorem strictLeaf_eq (v : Nat) : strictLeaf v = .leaf v := by
  cases v <;> rfl

def forceNodeL (l' r : WTree) : WTree :=
  match l' with
  | .leaf x => .node (.leaf x) r
  | .node ll lr => .node (.node ll lr) r

theorem forceNodeL_eq (l' r : WTree) : forceNodeL l' r = .node l' r := by
  cases l' <;> rfl

def forceNodeR (l r' : WTree) : WTree :=
  match r' with
  | .leaf x => .node l (.leaf x)
  | .node rl rr => .node l (.node rl rr)

theorem forceNodeR_eq (l r' : WTree) : forceNodeR l r' = .node l r' := by
  cases r' <;> rfl

def someWTree (tr : WTree) : Option WTree :=
  match tr with
  | .leaf x => some (.leaf x)
  | .node l r => some (.node l r)

theorem someWTree_eq (tr : WTree) : someWTree tr = some tr := by
  cases tr <;> rfl

def tSet : Nat → WTree → Nat → Nat → WTree
  | _, .leaf _, _, v => strictLeaf v
  | 0, .node l r, idx, v =>
      cond (Nat.blt idx 1) (forceNodeL (tSet 0 l idx v) r) (forceNodeR l (tSet 0 r (idx - 1) v))
  | d + 1, .node l r, idx, v =>
      let half := Nat.shiftLeft 1 (d + 1)
      cond (Nat.blt idx half)
        (forceNodeL (tSet d l idx v) r)
        (forceNodeR l (tSet d r (idx - half) v))

inductive WTreeWF : Nat → WTree → Prop where
  | leaf (v : Nat) : WTreeWF 0 (.leaf v)
  | node {d : Nat} {l r : WTree} : WTreeWF d l → WTreeWF d r → WTreeWF (d + 1) (.node l r)

def checkWTreeWF : Nat → WTree → Bool
  | 0, .leaf _ => true
  | d + 1, .node l r => checkWTreeWF d l && checkWTreeWF d r
  | _, _ => false

theorem checkWTreeWF_sound : ∀ d tr, checkWTreeWF d tr = true → WTreeWF d tr
  | 0, .leaf v, _ => .leaf v
  | d + 1, .node l r, h => by
    dsimp only [checkWTreeWF] at h
    simp only [Bool.and_eq_true] at h
    exact .node (checkWTreeWF_sound d l h.1) (checkWTreeWF_sound d r h.2)

theorem tSet_wf : ∀ {d : Nat} {tr : WTree}, WTreeWF (d + 1) tr →
    ∀ idx v, WTreeWF (d + 1) (tSet d tr idx v)
  | 0, .node (.leaf _) (.leaf _), .node (.leaf _) (.leaf _), idx, _ => by
    dsimp only [tSet]
    rw [strictLeaf_eq, forceNodeL_eq, forceNodeR_eq]
    cases Nat.blt idx 1 <;> exact .node (.leaf _) (.leaf _)
  | d + 1, .node l r, .node hl hr, idx, v => by
    dsimp only [tSet]
    rw [forceNodeL_eq, forceNodeR_eq]
    cases Nat.blt idx (Nat.shiftLeft 1 (d + 1))
    · exact .node hl (tSet_wf hr _ _)
    · exact .node (tSet_wf hl _ _) hr

theorem tGet_tSet : ∀ {d : Nat} {tr : WTree}, WTreeWF (d + 1) tr →
    ∀ {idx j : Nat}, idx < 2 ^ (d + 1) → j < 2 ^ (d + 1) → ∀ v,
    tGet d (tSet d tr idx v) j = if j = idx then v else tGet d tr j
  | 0, .node (.leaf _) (.leaf _), .node (.leaf _) (.leaf _), idx, j, hidx, hj, v => by
    dsimp only [tSet]
    rw [strictLeaf_eq, forceNodeL_eq, forceNodeR_eq]
    have hi : idx = 0 ∨ idx = 1 := by omega
    have hjb : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hjb with rfl | rfl <;> rfl
  | d + 1, .node l r, .node hl hr, idx, j, hidx, hj, v => by
    have hpow : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by ring
    dsimp only [tGet, tSet]
    rw [forceNodeL_eq, forceNodeR_eq, shiftLeft_eq_mul_pow, one_mul]
    cases hbi : Nat.blt idx (2 ^ (d + 1))
    · have hi' : 2 ^ (d + 1) ≤ idx := (blt_false_iff _ _).1 hbi
      dsimp only [cond, tGet]
      rw [shiftLeft_eq_mul_pow, one_mul]
      cases hbj : Nat.blt j (2 ^ (d + 1))
      · have hj' : 2 ^ (d + 1) ≤ j := (blt_false_iff _ _).1 hbj
        dsimp only [cond]
        rw [tGet_tSet hr (by omega) (by omega)]
        split_ifs with h1 h2 <;> first | rfl | omega
      · have hj' : j < 2 ^ (d + 1) := Nat.blt_eq.mp hbj
        dsimp only [cond]
        rw [ite_eq_right (by omega)]
    · have hi' : idx < 2 ^ (d + 1) := Nat.blt_eq.mp hbi
      dsimp only [cond, tGet]
      rw [shiftLeft_eq_mul_pow, one_mul]
      cases hbj : Nat.blt j (2 ^ (d + 1))
      · have hj' : 2 ^ (d + 1) ≤ j := (blt_false_iff _ _).1 hbj
        dsimp only [cond]
        rw [ite_eq_right (by omega)]
      · have hj' : j < 2 ^ (d + 1) := Nat.blt_eq.mp hbj
        dsimp only [cond]
        exact tGet_tSet hl hi' hj' v



def sGet (tr : WTree) (q : Nat) : Nat :=
  tGet 6 tr q

def sSet (tr : WTree) (q v : Nat) : WTree :=
  tSet 6 tr q v

theorem sSet_wf {tr : WTree} (hwf : WTreeWF 7 tr) (q v : Nat) :
    WTreeWF 7 (sSet tr q v) :=
  tSet_wf hwf q v

theorem sGet_sSet {tr : WTree} (hwf : WTreeWF 7 tr) {q w : Nat}
    (hq : q < 100) (hw : w < 100) (v : Nat) :
    sGet (sSet tr q v) w = if w = q then v else sGet tr w :=
  tGet_tSet hwf (by omega : q < 2 ^ 7) (by omega : w < 2 ^ 7) v

def wGet (tr : WTree) (q : Nat) : Nat :=
  tGet 6 tr (q - 25)

def wSet (tr : WTree) (q v : Nat) : WTree :=
  tSet 6 tr (q - 25) v

theorem wSet_wf {tr : WTree} (hwf : WTreeWF 7 tr) (q v : Nat) :
    WTreeWF 7 (wSet tr q v) :=
  tSet_wf hwf (q - 25) v

theorem wGet_wSet {tr : WTree} (hwf : WTreeWF 7 tr) {q w : Nat}
    (hq1 : 25 ≤ q) (hq2 : q < 100) (hw1 : 25 ≤ w) (hw2 : w < 100) (v : Nat) :
    wGet (wSet tr q v) w = if w = q then v else wGet tr w := by
  unfold wGet wSet
  rw [tGet_tSet hwf (by omega : q - 25 < 2 ^ 7) (by omega : w - 25 < 2 ^ 7)]
  split_ifs with h1 h2 <;> first | rfl | omega



-- ============================================================================
-- Symbolic Evaluator (SymInv) & Column-Bag Reducer (reduceBag)
-- ============================================================================

def evalSymMask : Nat → (Nat → Bool) → Nat → Bool
  | 0, _, _ => false
  | n + 1, env, mask => xor (evalSymMask n env mask) (mask.testBit n && env n)

theorem evalSymMask_zero (env : Nat → Bool) : ∀ n, evalSymMask n env 0 = false
  | 0 => rfl
  | n + 1 => by simp [evalSymMask, evalSymMask_zero env n]

theorem xor_and_distrib (a b c : Bool) : xor (a && c) (b && c) = (xor a b && c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor_xor_comm (a b c d : Bool) : xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem evalSymMask_xor (env : Nat → Bool) (m1 m2 : Nat) :
    ∀ n, evalSymMask n env (m1 ^^^ m2) = xor (evalSymMask n env m1) (evalSymMask n env m2)
  | 0 => rfl
  | n + 1 => by
    dsimp only [evalSymMask]
    rw [Nat.testBit_xor, ← xor_and_distrib, evalSymMask_xor env m1 m2 n, xor_xor_comm]

theorem evalSymMask_two_pow_of_le (env : Nat → Bool) {j : Nat} :
    ∀ n, n ≤ j → evalSymMask n env (2 ^ j) = false
  | 0, _ => rfl
  | n + 1, hle => by
    dsimp only [evalSymMask]
    rw [evalSymMask_two_pow_of_le env n (by omega), Nat.testBit_two_pow,
        decide_eq_false (by omega : j ≠ n), Bool.false_and, Bool.xor_false]

theorem evalSymMask_two_pow (env : Nat → Bool) {j : Nat} :
    ∀ n, j < n → evalSymMask n env (2 ^ j) = env j
  | 0, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, hj => by
    dsimp only [evalSymMask]
    by_cases hjn : j = n
    · subst hjn
      rw [evalSymMask_two_pow_of_le env j (Nat.le_refl j), Nat.testBit_two_pow]
      simp
    · rw [evalSymMask_two_pow env n (by omega), Nat.testBit_two_pow,
          decide_eq_false hjn, Bool.false_and, Bool.xor_false]

theorem evalSymMask_shiftLeft_one (env : Nat → Bool) {j n : Nat} (hj : j < n) :
    evalSymMask n env (Nat.shiftLeft 1 j) = env j := by
  rw [shiftLeft_eq_mul_pow, one_mul]
  exact evalSymMask_two_pow env n hj

theorem evalSymMask_congr (env1 env2 : Nat → Bool) (m : Nat) :
    ∀ n, (∀ i < n, m.testBit i = true → env1 i = env2 i) →
      evalSymMask n env1 m = evalSymMask n env2 m
  | 0, _ => rfl
  | n + 1, h => by
    dsimp only [evalSymMask]
    rw [evalSymMask_congr env1 env2 m n (fun i hi htb => h i (by omega) htb)]
    by_cases htb : m.testBit n = true
    · rw [htb, h n (by omega) htb]
    · simp only [Bool.not_eq_true] at htb; rw [htb]; rfl

theorem testBit_eq_false_of_shiftRight_zero {m b i : Nat}
    (h : Nat.shiftRight m b = 0) (hi : b ≤ i) : m.testBit i = false := by
  have h1 : m.testBit (b + (i - b)) = (Nat.shiftRight m b).testBit (i - b) :=
    (Nat.testBit_shiftRight m).symm
  rw [Nat.add_sub_of_le hi, h, Nat.zero_testBit] at h1
  exact h1

def checkDefsWF : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | b, (u, v) :: rest =>
      Nat.beq (Nat.shiftRight u b) 0 &&
      Nat.beq (Nat.shiftRight v b) 0 &&
      checkDefsWF (b + 1) rest

def buildSymEnvAux (N : Nat) : Nat → List (Nat × Nat) → (Nat → Bool) → (Nat → Bool)
  | _, [], env => env
  | b, (u, v) :: rest, env =>
      let val := evalSymMask N env u && evalSymMask N env v
      buildSymEnvAux N (b + 1) rest (fun i => if i = b then val else env i)

def baseSymEnv (m0 : Fin 100 → Bool) (i : Nat) : Bool :=
  if i = 0 then true
  else if h : i - 1 < 100 then m0 ⟨i - 1, h⟩
  else false

def buildSymEnv (N : Nat) (m0 : Fin 100 → Bool) (defs : List (Nat × Nat)) : Nat → Bool :=
  buildSymEnvAux N 103 defs (baseSymEnv m0)

theorem buildSymEnvAux_lt (N : Nat) :
    ∀ (b : Nat) (defs : List (Nat × Nat)) (env : Nat → Bool) {i : Nat},
      i < b → buildSymEnvAux N b defs env i = env i
  | _, [], _, _, _ => rfl
  | b, (u, v) :: rest, env, i, hi => by
    dsimp only [buildSymEnvAux]
    rw [buildSymEnvAux_lt N (b + 1) rest _ (by omega : i < b + 1)]
    exact ite_eq_right (by omega)

theorem evalSymMask_buildSymEnvAux (N : Nat) :
    ∀ (b : Nat) (defs : List (Nat × Nat)) (env : Nat → Bool) {m : Nat},
      Nat.shiftRight m b = 0 →
      evalSymMask N (buildSymEnvAux N b defs env) m = evalSymMask N env m := by
  intro b defs env m hsh
  refine evalSymMask_congr _ _ m N (fun i _ htb => ?_)
  have hib : i < b := by
    by_contra hge
    have hf := testBit_eq_false_of_shiftRight_zero hsh (Nat.le_of_not_lt hge)
    rw [hf] at htb; cases htb
  exact buildSymEnvAux_lt N b defs env hib

theorem buildSymEnvAux_spec (N : Nat) :
    ∀ (b : Nat) (defs : List (Nat × Nat)) (env : Nat → Bool),
      checkDefsWF b defs = true →
      ∀ (k : Nat) (p : Nat × Nat), defs[k]? = some p →
        let envF := buildSymEnvAux N b defs env
        envF (b + k) = (evalSymMask N envF p.1 && evalSymMask N envF p.2)
  | b, [], env, _, k, p, hk => by cases hk
  | b, (u, v) :: rest, env, hwf, k, p, hk => by
    dsimp only [checkDefsWF] at hwf
    simp only [Bool.and_eq_true, Nat.beq_eq] at hwf
    obtain ⟨⟨hu, hv⟩, hrest⟩ := hwf
    cases k with
    | zero =>
      injection hk with hp; subst hp
      dsimp only [buildSymEnvAux]
      let env1 : Nat → Bool := fun i =>
        if i = b then (evalSymMask N env u && evalSymMask N env v) else env i
      have h_at_b : buildSymEnvAux N (b + 1) rest env1 (b + 0) = env1 b := by
        rw [Nat.add_zero]
        exact buildSymEnvAux_lt N (b + 1) rest env1 (by omega)
      have env1_b : env1 b = (evalSymMask N env u && evalSymMask N env v) := ite_eq_left rfl
      have hu1 : evalSymMask N (buildSymEnvAux N (b + 1) rest env1) u = evalSymMask N env u := by
        refine evalSymMask_congr _ _ u N (fun i _ htb => ?_)
        have hib : i < b := by
          by_contra hge
          have hf := testBit_eq_false_of_shiftRight_zero hu (Nat.le_of_not_lt hge)
          rw [hf] at htb; cases htb
        rw [buildSymEnvAux_lt N (b + 1) rest env1 (by omega : i < b + 1)]
        exact ite_eq_right (by omega)
      have hv1 : evalSymMask N (buildSymEnvAux N (b + 1) rest env1) v = evalSymMask N env v := by
        refine evalSymMask_congr _ _ v N (fun i _ htb => ?_)
        have hib : i < b := by
          by_contra hge
          have hf := testBit_eq_false_of_shiftRight_zero hv (Nat.le_of_not_lt hge)
          rw [hf] at htb; cases htb
        rw [buildSymEnvAux_lt N (b + 1) rest env1 (by omega : i < b + 1)]
        exact ite_eq_right (by omega)
      rw [h_at_b, env1_b, hu1, hv1]
    | succ k =>
      dsimp only [List.getElem?_cons_succ] at hk
      dsimp only [buildSymEnvAux]
      have ih := buildSymEnvAux_spec N (b + 1) rest
        (fun i => if i = b then (evalSymMask N env u && evalSymMask N env v) else env i)
        hrest k p hk
      dsimp only at ih
      rw [show b + (k + 1) = b + 1 + k by omega]
      exact ih

def DefsOK (N : Nat) (env : Nat → Bool) (defs : List (Nat × Nat)) : Prop :=
  103 + defs.length ≤ N ∧
  ∀ (k : Nat) (p : Nat × Nat), defs[k]? = some p →
    env (103 + k) = (evalSymMask N env p.1 && evalSymMask N env p.2)

theorem defsOK_buildSymEnv (N : Nat) (m0 : Fin 100 → Bool) (defs : List (Nat × Nat))
    (hlen : 103 + defs.length ≤ N) (hwf : checkDefsWF 103 defs = true) :
    DefsOK N (buildSymEnv N m0 defs) defs :=
  ⟨hlen, buildSymEnvAux_spec N 103 defs (baseSymEnv m0) hwf⟩

def findDefIdx : List (Nat × Nat) → Nat → Nat → Nat → Option Nat
  | [], _, _, _ => none
  | p :: rest, u, v, k =>
      cond ((Nat.beq p.1 u && Nat.beq p.2 v) || (Nat.beq p.1 v && Nat.beq p.2 u))
        (some k)
        (findDefIdx rest u v (k + 1))

theorem findDefIdx_sound {N : Nat} {env : Nat → Bool} :
    ∀ (defs : List (Nat × Nat)) (u v base k : Nat),
      (∀ (j : Nat) (p : Nat × Nat), defs[j]? = some p →
        env (base + j) = (evalSymMask N env p.1 && evalSymMask N env p.2)) →
      findDefIdx defs u v base = some k →
      k < base + defs.length ∧
      env k = (evalSymMask N env u && evalSymMask N env v)
  | [], _, _, _, _, _, h => by cases h
  | p :: rest, u, v, base, k, hspec, h => by
    dsimp only [findDefIdx] at h
    cases hc : ((Nat.beq p.1 u && Nat.beq p.2 v) || (Nat.beq p.1 v && Nat.beq p.2 u))
    · rw [hc, Bool.cond_false] at h
      obtain ⟨hlt, hev⟩ := findDefIdx_sound rest u v (base + 1) k
        (fun j q hq => by
          rw [show base + 1 + j = base + (j + 1) by omega]; exact hspec (j + 1) q hq) h
      exact ⟨by dsimp only [List.length_cons]; omega, hev⟩
    · rw [hc, Bool.cond_true] at h
      injection h with hk; subst hk
      have hp0 := hspec 0 p rfl
      rw [Nat.add_zero] at hp0
      refine ⟨by dsimp only [List.length_cons]; omega, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hp0
      · rw [hp0, Bool.and_comm]

def checkRccx0DisjLoop (v mt : Nat) : List (Nat × Nat) → Nat → Bool
  | [], _ => false
  | p :: rest, base =>
      cond (Nat.beq mt (Nat.shiftLeft 1 base) && Nat.beq (p.1 ^^^ p.2) v)
        true
        (checkRccx0DisjLoop v mt rest (base + 1))

theorem rccx0_disj_bool (u a b : Bool) : (u && xor a b && (a && b)) = false := by
  cases u <;> cases a <;> cases b <;> rfl

theorem checkRccx0DisjLoop_sound {N : Nat} {env : Nat → Bool} :
    ∀ (defs : List (Nat × Nat)) (v mt base : Nat),
      base + defs.length ≤ N →
      (∀ (j : Nat) (p : Nat × Nat), defs[j]? = some p →
        env (base + j) = (evalSymMask N env p.1 && evalSymMask N env p.2)) →
      checkRccx0DisjLoop v mt defs base = true →
      ∀ u_b : Bool, (u_b && evalSymMask N env v && evalSymMask N env mt) = false
  | [], _, _, _, _, _, h, _ => by cases h
  | p :: rest, v, mt, base, hlen, hspec, h, u_b => by
    dsimp only [checkRccx0DisjLoop] at h
    cases hc : (Nat.beq mt (Nat.shiftLeft 1 base) && Nat.beq (p.1 ^^^ p.2) v)
    · rw [hc, Bool.cond_false] at h
      exact checkRccx0DisjLoop_sound rest v mt (base + 1)
        (by dsimp only [List.length_cons] at hlen; omega)
        (fun j q hq => by
          rw [show base + 1 + j = base + (j + 1) by omega]; exact hspec (j + 1) q hq)
        h u_b
    · simp only [Bool.and_eq_true, Nat.beq_eq] at hc
      obtain ⟨hmt_eq, hv_eq⟩ := hc
      have hp0 := hspec 0 p rfl
      rw [Nat.add_zero] at hp0
      subst hv_eq
      rw [evalSymMask_xor, hmt_eq,
          evalSymMask_shiftLeft_one env (by dsimp only [List.length_cons] at hlen; omega),
          hp0]
      exact rccx0_disj_bool _ _ _

structure SymInv (N : Nat) (env : Nat → Bool) (tr : WTree) (m : Fin 100 → Bool) : Prop where
  wf : WTreeWF 7 tr
  h0 : 0 < N
  henv0 : env 0 = true
  hWire : ∀ w : Fin 100, m w = evalSymMask N env (sGet tr w.val)

theorem SymInv.update {N : Nat} {env : Nat → Bool} {tr : WTree} {m : Fin 100 → Bool}
    (hI : SymInv N env tr m) {t : Nat} (ht : t < 100) (v : Nat) (b : Bool)
    (hb : evalSymMask N env v = b) :
    SymInv N env (sSet tr t v) (Function.update m ⟨t, ht⟩ b) := by
  refine ⟨sSet_wf hI.wf t v, hI.h0, hI.henv0, fun w => ?_⟩
  by_cases hwt : w = ⟨t, ht⟩
  · subst hwt
    simp [Function.update_self, sGet_sSet hI.wf ht ht, hb]
  · have hne : w.val ≠ t := fun e => hwt (Fin.ext e)
    simp [Function.update_of_ne hwt, sGet_sSet hI.wf ht w.isLt, hne, hI.hWire w]

def sumQuadSym (defs : List (Nat × Nat)) (tr : WTree) (t : Nat) : List (Nat × Nat) → Option Nat
  | [] => some 0
  | (c1, c2) :: qs =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t)
        (match findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
         | some idx =>
             match sumQuadSym defs tr t qs with
             | some rest => some (Nat.shiftLeft 1 idx ^^^ rest)
             | none => none
         | none => none)
        none

def sumLinSym (tr : WTree) (t : Nat) : List Nat → Option Nat
  | [] => some 0
  | c :: ls =>
      cond (Nat.blt c 100 && !Nat.beq c t)
        (match sumLinSym tr t ls with
         | some rest => some (sGet tr c ^^^ rest)
         | none => none)
        none

theorem sumQuadSym_sound {N : Nat} {env : Nat → Bool} {defs : List (Nat × Nat)}
    {tr : WTree} {m : Fin 100 → Bool}
    (hDefs : DefsOK N env defs)
    (hI : SymInv N env tr m) (t : Nat) :
    ∀ (qs : List (Nat × Nat)) {mq : Nat},
      sumQuadSym defs tr t qs = some mq →
      (∀ p ∈ qs, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧
      evalSymMask N env mq = evalQuadBool102 m qs
  | [], _, h => by
    injection h with hq; subst hq
    exact ⟨(fun _ hp => by cases hp), evalSymMask_zero env N⟩
  | (c1, c2) :: qs, mq, h => by
    dsimp only [sumQuadSym] at h
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && !Nat.beq c1 c2 &&
      !Nat.beq c1 t && !Nat.beq c2 t)
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    cases hf : findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
    | none => rw [hf] at h; cases h
    | some idx =>
      rw [hf] at h; dsimp only at h
      cases hrest : sumQuadSym defs tr t qs with
      | none => rw [hrest] at h; cases h
      | some rest =>
        rw [hrest] at h; dsimp only at h
        injection h with hmq; subst hmq
        simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
        obtain ⟨⟨⟨⟨hc1, hc2⟩, h12⟩, h1t⟩, h2t⟩ := hc
        obtain ⟨hidx_lt, hev⟩ := findDefIdx_sound defs (sGet tr c1) (sGet tr c2) 103 idx hDefs.2 hf
        obtain ⟨hq_v, hq_ev⟩ := sumQuadSym_sound hDefs hI t qs hrest
        refine ⟨fun p hp => ?_, ?_⟩
        · rcases List.mem_cons.mp hp with rfl | hmem
          · exact ⟨hc1, hc2, h12, h1t, h2t⟩
          · exact hq_v p hmem
        · dsimp only [evalQuadBool102]
          rw [dite_eq_left ⟨hc1, hc2⟩, evalSymMask_xor,
              evalSymMask_shiftLeft_one env (by have := hDefs.1; omega), hev,
              ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩, hq_ev]

theorem sumLinSym_sound {N : Nat} {env : Nat → Bool} {tr : WTree} {m : Fin 100 → Bool}
    (hI : SymInv N env tr m) (t : Nat) :
    ∀ (ls : List Nat) {ml : Nat},
      sumLinSym tr t ls = some ml →
      (∀ c ∈ ls, c < 100 ∧ c ≠ t) ∧
      evalSymMask N env ml = evalLinBool102 m ls
  | [], _, h => by
    injection h with hl; subst hl
    exact ⟨(fun _ hc => by cases hc), evalSymMask_zero env N⟩
  | c :: ls, ml, h => by
    dsimp only [sumLinSym] at h
    cases hc : (Nat.blt c 100 && !Nat.beq c t)
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    cases hrest : sumLinSym tr t ls with
    | none => rw [hrest] at h; cases h
    | some rest =>
      rw [hrest] at h; dsimp only at h
      injection h with hml; subst hml
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
      obtain ⟨hclt, hct⟩ := hc
      obtain ⟨hl_v, hl_ev⟩ := sumLinSym_sound hI t ls hrest
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨hclt, hct⟩
        · exact hl_v x hmem
      · dsimp only [evalLinBool102]
        rw [dite_eq_left hclt, evalSymMask_xor, ← hI.hWire ⟨c, hclt⟩, hl_ev]

theorem rccx1_sym_guard (a b z : Bool) (h : (a && b && xor z (a && b)) = false) :
    (a && b && !z) = false := by
  cases a <;> cases b <;> cases z <;> first | rfl | cases h

def stepSymOpt (defs : List (Nat × Nat)) (tr : WTree) : Op102 → Option WTree
  | .x q =>
      cond (Nat.blt q 100)
        (someWTree (sSet tr q (sGet tr q ^^^ 1))) none
  | .cx c t =>
      cond (Nat.blt c 100 && Nat.blt t 100 && !Nat.beq c t)
        (someWTree (sSet tr t (sGet tr t ^^^ sGet tr c))) none
  | .and4t c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
            Nat.beq (sGet tr t) 0)
        (match findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
         | some idx => someWTree (sSet tr t (Nat.shiftLeft 1 idx))
         | none => none)
        none
  | .rccx0 c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
            checkRccx0DisjLoop (sGet tr c2) (sGet tr t) defs 103)
        (match findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
         | some idx => someWTree (sSet tr t (sGet tr t ^^^ Nat.shiftLeft 1 idx))
         | none => none)
        none
  | .rccx1 c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t)
        (match findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
         | some idx =>
             let mt' := sGet tr t ^^^ Nat.shiftLeft 1 idx
             cond (checkRccx0DisjLoop (sGet tr c2) mt' defs 103)
               (someWTree (sSet tr t mt')) none
         | none => none)
        none
  | .unand c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t)
        (match findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
         | some idx =>
             cond (Nat.beq (sGet tr t) (Nat.shiftLeft 1 idx))
               (someWTree (sSet tr t 0)) none
         | none => none)
        none
  | .unquad qs ls t =>
      cond (Nat.blt t 100)
        (match sumQuadSym defs tr t qs with
         | some mq =>
             match sumLinSym tr t ls with
             | some ml =>
                 cond (Nat.beq (sGet tr t) (mq ^^^ ml))
                   (someWTree (sSet tr t 0)) none
             | none => none
         | none => none)
        none
  | .z _ => none
  | .cz _ _ => none
  | .hGadget _ _ _ _ _ => none

theorem xor_true_eq_not (b : Bool) : xor b true = !b := by
  cases b <;> rfl

theorem stepSymOpt_sound {N : Nat} {env : Nat → Bool} {defs : List (Nat × Nat)}
    {tr tr' : WTree} {m : Fin 100 → Bool}
    (hDefs : DefsOK N env defs)
    (hI : SymInv N env tr m)
    {op : Op102}
    (hok : stepSymOpt defs tr op = some tr') :
    ∃ m', execOp102 m op = some m' ∧ SymInv N env tr' m' := by
  cases op with
  | x q =>
    dsimp only [stepSymOpt] at hok
    cases hc : Nat.blt q 100
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    have hq : q < 100 := Nat.blt_eq.mp hc
    have h1 : evalSymMask N env 1 = true := by
      have := evalSymMask_shiftLeft_one env hI.h0
      simpa using this.trans hI.henv0
    have hval : evalSymMask N env (sGet tr q ^^^ 1) = !m ⟨q, hq⟩ := by
      rw [evalSymMask_xor, h1, ← hI.hWire ⟨q, hq⟩, xor_true_eq_not]
    exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hq], hI.update hq _ _ hval⟩
  | cx c t =>
    dsimp only [stepSymOpt] at hok
    cases hc : (Nat.blt c 100 && Nat.blt t 100 && !Nat.beq c t)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
    obtain ⟨⟨hclt, htlt⟩, hct⟩ := hc
    have hval : evalSymMask N env (sGet tr t ^^^ sGet tr c) = xor (m ⟨t, htlt⟩) (m ⟨c, hclt⟩) := by
      rw [evalSymMask_xor, ← hI.hWire ⟨t, htlt⟩, ← hI.hWire ⟨c, hclt⟩]
    exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left ⟨hclt, htlt, hct⟩],
      hI.update htlt _ _ hval⟩
  | and4t c1 c2 t =>
    dsimp only [stepSymOpt] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
                Nat.beq (sGet tr t) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases hf : findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
    | none => rw [hf] at hok; cases hok
    | some idx =>
      rw [hf] at hok; dsimp only at hok; rw [someWTree_eq] at hok
      injection hok with htr'; subst htr'
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hc1, hc2⟩, ht⟩, h12⟩, h1t⟩, h2t⟩, hvt0⟩ := hc
      obtain ⟨hidx_lt, hev⟩ := findDefIdx_sound defs (sGet tr c1) (sGet tr c2) 103 idx hDefs.2 hf
      have hmt0 : m ⟨t, ht⟩ = false := by
        rw [hI.hWire ⟨t, ht⟩, hvt0, evalSymMask_zero]
      have hval : evalSymMask N env (Nat.shiftLeft 1 idx) = (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) := by
        rw [evalSymMask_shiftLeft_one env (by have := hDefs.1; omega), hev,
            ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩]
      exact ⟨_, (by
          dsimp only [execOp102]
          rw [dite_eq_left ⟨hc1, hc2, ht, h12, h1t, h2t⟩, ite_eq_left hmt0]),
        hI.update ht _ _ hval⟩
  | rccx0 c1 c2 t =>
    dsimp only [stepSymOpt] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
                checkRccx0DisjLoop (sGet tr c2) (sGet tr t) defs 103)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases hf : findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
    | none => rw [hf] at hok; cases hok
    | some idx =>
      rw [hf] at hok; dsimp only at hok; rw [someWTree_eq] at hok
      injection hok with htr'; subst htr'
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
      obtain ⟨⟨⟨⟨⟨⟨hc1, hc2⟩, ht⟩, h12⟩, h1t⟩, h2t⟩, hdisj⟩ := hc
      obtain ⟨hidx_lt, hev⟩ := findDefIdx_sound defs (sGet tr c1) (sGet tr c2) 103 idx hDefs.2 hf
      have hguard : (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩ && m ⟨t, ht⟩) = false := by
        rw [hI.hWire ⟨c1, hc1⟩, hI.hWire ⟨c2, hc2⟩, hI.hWire ⟨t, ht⟩]
        exact checkRccx0DisjLoop_sound defs (sGet tr c2) (sGet tr t) 103 hDefs.1 hDefs.2 hdisj _
      have hval : evalSymMask N env (sGet tr t ^^^ Nat.shiftLeft 1 idx) =
          xor (m ⟨t, ht⟩) (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) := by
        rw [evalSymMask_xor, evalSymMask_shiftLeft_one env (by have := hDefs.1; omega), hev,
            ← hI.hWire ⟨t, ht⟩, ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩]
      exact ⟨_, (by
          dsimp only [execOp102]
          rw [dite_eq_left ⟨hc1, hc2, ht, h12, h1t, h2t⟩, ite_eq_left hguard]),
        hI.update ht _ _ hval⟩
  | rccx1 c1 c2 t =>
    dsimp only [stepSymOpt] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases hf : findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
    | none => rw [hf] at hok; cases hok
    | some idx =>
      rw [hf] at hok; dsimp only at hok
      cases hdisj : checkRccx0DisjLoop (sGet tr c2) (sGet tr t ^^^ Nat.shiftLeft 1 idx) defs 103
      · rw [hdisj, Bool.cond_false] at hok; cases hok
      rw [hdisj, Bool.cond_true, someWTree_eq] at hok
      injection hok with htr'; subst htr'
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
      obtain ⟨⟨⟨⟨⟨hc1, hc2⟩, ht⟩, h12⟩, h1t⟩, h2t⟩ := hc
      obtain ⟨hidx_lt, hev⟩ := findDefIdx_sound defs (sGet tr c1) (sGet tr c2) 103 idx hDefs.2 hf
      have hval : evalSymMask N env (sGet tr t ^^^ Nat.shiftLeft 1 idx) =
          xor (m ⟨t, ht⟩) (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) := by
        rw [evalSymMask_xor, evalSymMask_shiftLeft_one env (by have := hDefs.1; omega), hev,
            ← hI.hWire ⟨t, ht⟩, ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩]
      have hguard0 : (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩ &&
          xor (m ⟨t, ht⟩) (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩)) = false := by
        rw [← hval, hI.hWire ⟨c1, hc1⟩, hI.hWire ⟨c2, hc2⟩]
        exact checkRccx0DisjLoop_sound defs (sGet tr c2) (sGet tr t ^^^ Nat.shiftLeft 1 idx)
          103 hDefs.1 hDefs.2 hdisj _
      have hguard : (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩ && !m ⟨t, ht⟩) = false :=
        rccx1_sym_guard _ _ _ hguard0
      exact ⟨_, (by
          dsimp only [execOp102]
          rw [dite_eq_left ⟨hc1, hc2, ht, h12, h1t, h2t⟩, ite_eq_left hguard]),
        hI.update ht _ _ hval⟩
  | unand c1 c2 t =>
    dsimp only [stepSymOpt] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases hf : findDefIdx defs (sGet tr c1) (sGet tr c2) 103 with
    | none => rw [hf] at hok; cases hok
    | some idx =>
      rw [hf] at hok; dsimp only at hok
      cases heq : Nat.beq (sGet tr t) (Nat.shiftLeft 1 idx)
      · rw [heq, Bool.cond_false] at hok; cases hok
      rw [heq, Bool.cond_true, someWTree_eq] at hok
      injection hok with htr'; subst htr'
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
      obtain ⟨⟨⟨⟨⟨hc1, hc2⟩, ht⟩, h12⟩, h1t⟩, h2t⟩ := hc
      obtain ⟨hidx_lt, hev⟩ := findDefIdx_sound defs (sGet tr c1) (sGet tr c2) 103 idx hDefs.2 hf
      have hmt : m ⟨t, ht⟩ = (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) := by
        rw [hI.hWire ⟨t, ht⟩, Nat.beq_eq.mp heq,
            evalSymMask_shiftLeft_one env (by have := hDefs.1; omega), hev,
            ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩]
      exact ⟨_, (by
          dsimp only [execOp102]
          rw [dite_eq_left ⟨hc1, hc2, ht, h12, h1t, h2t⟩, ite_eq_left hmt]),
        hI.update ht 0 false (evalSymMask_zero env N)⟩
  | unquad qs ls t =>
    dsimp only [stepSymOpt] at hok
    cases hc : Nat.blt t 100
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true] at hok
    cases hq : sumQuadSym defs tr t qs with
    | none => rw [hq] at hok; cases hok
    | some mq =>
      rw [hq] at hok; dsimp only at hok
      cases hl : sumLinSym tr t ls with
      | none => rw [hl] at hok; cases hok
      | some ml =>
        rw [hl] at hok; dsimp only at hok
        cases heq : Nat.beq (sGet tr t) (mq ^^^ ml)
        · rw [heq, Bool.cond_false] at hok; cases hok
        rw [heq, Bool.cond_true, someWTree_eq] at hok
        injection hok with htr'; subst htr'
        have ht : t < 100 := Nat.blt_eq.mp hc
        obtain ⟨hq_v, hq_ev⟩ := sumQuadSym_sound hDefs hI t qs hq
        obtain ⟨hl_v, hl_ev⟩ := sumLinSym_sound hI t ls hl
        have hvalid : validUnquad102 qs ls t := ⟨hq_v, hl_v, ht⟩
        have hmt : m ⟨t, ht⟩ = evalUnquad102 m qs ls := by
          rw [hI.hWire ⟨t, ht⟩, Nat.beq_eq.mp heq, evalSymMask_xor, hq_ev, hl_ev]
          rfl
        exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hvalid, ite_eq_left hmt],
          hI.update ht 0 false (evalSymMask_zero env N)⟩
  | z _ => cases hok
  | cz _ => cases hok
  | hGadget _ _ _ _ _ => cases hok

def runSymListOpt (defs : List (Nat × Nat)) : List Op102 → WTree → Option WTree
  | [], tr => some tr
  | op :: ops, tr =>
      match stepSymOpt defs tr op with
      | some tr1 => runSymListOpt defs ops tr1
      | none => none

theorem runSymListOpt_sound {N : Nat} {env : Nat → Bool} {defs : List (Nat × Nat)}
    (hDefs : DefsOK N env defs) :
    ∀ (ops : List Op102) {tr tr' : WTree} {m : Fin 100 → Bool},
      SymInv N env tr m →
      runSymListOpt defs ops tr = some tr' →
      ∃ m', execList102 ops m = some m' ∧ SymInv N env tr' m'
  | [], _, _, m, hI, hok => by
    injection hok with htr'; subst htr'
    exact ⟨m, rfl, hI⟩
  | op :: ops, tr, tr', m, hI, hok => by
    dsimp only [runSymListOpt] at hok
    cases h1 : stepSymOpt defs tr op with
    | none => rw [h1] at hok; cases hok
    | some tr1 =>
      rw [h1] at hok
      obtain ⟨m1, hex1, hI1⟩ := stepSymOpt_sound hDefs hI h1
      obtain ⟨m', hex2, hI'⟩ := runSymListOpt_sound hDefs ops hI1 hok
      exact ⟨m', by dsimp only [execList102]; rw [hex1]; exact hex2, hI'⟩

-- ============================================================================
-- Column-Bag Reduction Engine (evalCol, evalBag, BagStep, reduceBag)
-- ============================================================================

def evalCol (N : Nat) (env : Nat → Bool) : List Nat → Nat
  | [] => 0
  | m :: ms => (cond (evalSymMask N env m) 1 0) + evalCol N env ms

def evalBag (N : Nat) (env : Nat → Bool) : List (List Nat) → Nat
  | [] => 0
  | col :: rest => evalCol N env col + 2 * evalBag N env rest

def removeOne (x : Nat) : List Nat → Option (List Nat)
  | [] => none
  | m :: ms =>
      cond (Nat.beq m x)
        (some ms)
        (match removeOne x ms with
         | some ms' => some (m :: ms')
         | none => none)

theorem removeOne_sound (N : Nat) (env : Nat → Bool) (x : Nat) :
    ∀ (col col' : List Nat),
      removeOne x col = some col' →
      evalCol N env col = (cond (evalSymMask N env x) 1 0) + evalCol N env col'
  | [], _, h => by cases h
  | m :: ms, col', h => by
    dsimp only [removeOne] at h
    cases hc : Nat.beq m x
    · rw [hc, Bool.cond_false] at h
      cases hrem : removeOne x ms with
      | none => rw [hrem] at h; cases h
      | some ms' =>
        rw [hrem] at h; dsimp only at h
        injection h with hcol'; subst hcol'
        dsimp only [evalCol]
        rw [removeOne_sound N env x ms ms' hrem]
        omega
    · rw [hc, Bool.cond_true] at h
      injection h with hcol'; subst hcol'
      rw [Nat.beq_eq.mp hc]
      rfl

theorem fa_bool_id (a b u : Bool) :
    (cond (xor a u) 1 0) + (cond (xor b u) 1 0) + (cond u 1 0) =
    (cond (xor (xor a b) u) 1 0) + 2 * (cond (xor u (a && b)) 1 0) := by
  cases a <;> cases b <;> cases u <;> rfl

theorem ha_bool_id (a b : Bool) :
    (cond a 1 0) + (cond b 1 0) =
    (cond (xor a b) 1 0) + 2 * (cond (a && b) 1 0) := by
  cases a <;> cases b <;> rfl

theorem disjXor_bool_id (du dv u : Bool) :
    (cond (du && dv) 1 0) + (cond (u && xor du dv) 1 0) =
    cond (xor (du && dv) (u && xor du dv)) 1 0 := by
  cases du <;> cases dv <;> cases u <;> rfl

def stepColFA (a b u k : Nat) (c0 c1 : List Nat) : Option (List Nat × List Nat) :=
  let in1 := a ^^^ u
  let in2 := b ^^^ u
  match removeOne in1 c0 with
  | none => none
  | some r1 =>
      match removeOne in2 r1 with
      | none => none
      | some r2 =>
          match if Nat.beq u 0 then some r2 else removeOne u r2 with
          | none => none
          | some r3 =>
              let sum_m := a ^^^ b ^^^ u
              let carry_m := u ^^^ Nat.shiftLeft 1 (103 + k)
              some (sum_m :: r3, carry_m :: c1)

theorem stepColFA_sound {N : Nat} {env : Nat → Bool} {a b u k : Nat}
    (hk_lt : 103 + k < N)
    (hk_ev : env (103 + k) = (evalSymMask N env a && evalSymMask N env b))
    {c0 c1 c0' c1' : List Nat}
    (h : stepColFA a b u k c0 c1 = some (c0', c1')) :
    evalCol N env c0 + 2 * evalCol N env c1 =
      evalCol N env c0' + 2 * evalCol N env c1' := by
  dsimp only [stepColFA] at h
  cases hr1 : removeOne (a ^^^ u) c0 with
  | none => rw [hr1] at h; cases h
  | some r1 =>
    rw [hr1] at h; dsimp only at h
    cases hr2 : removeOne (b ^^^ u) r1 with
    | none => rw [hr2] at h; cases h
    | some r2 =>
      rw [hr2] at h; dsimp only at h
      have hrem1 := removeOne_sound N env (a ^^^ u) c0 r1 hr1
      have hrem2 := removeOne_sound N env (b ^^^ u) r1 r2 hr2
      by_cases hu0 : Nat.beq u 0 = true
      · rw [ite_eq_left hu0] at h; dsimp only at h
        injection h with hpair
        injection hpair with hc0' hc1'
        subst hc0' hc1'
        have hu_eq : u = 0 := Nat.beq_eq.mp hu0
        subst hu_eq
        rw [Nat.xor_zero] at hrem1 hrem2
        have hha := ha_bool_id (evalSymMask N env a) (evalSymMask N env b)
        dsimp only [evalCol]
        rw [hrem1, hrem2, Nat.xor_zero, Nat.zero_xor]
        simp only [evalSymMask_xor, evalSymMask_shiftLeft_one env hk_lt, hk_ev]
        omega
      · rw [ite_eq_right hu0] at h
        cases hr3 : removeOne u r2 with
        | none => rw [hr3] at h; cases h
        | some r3 =>
          rw [hr3] at h; dsimp only at h
          injection h with hpair
          injection hpair with hc0' hc1'
          subst hc0' hc1'
          have hrem3 := removeOne_sound N env u r2 r3 hr3
          have hfa := fa_bool_id (evalSymMask N env a) (evalSymMask N env b) (evalSymMask N env u)
          dsimp only [evalCol]
          rw [hrem1, hrem2, hrem3]
          simp only [evalSymMask_xor, evalSymMask_shiftLeft_one env hk_lt, hk_ev]
          omega

def applyBagFA (a b u k : Nat) : Nat → List (List Nat) → Option (List (List Nat))
  | 0, c0 :: c1 :: rest =>
      match stepColFA a b u k c0 c1 with
      | some (c0', c1') => some (c0' :: c1' :: rest)
      | none => none
  | idx + 1, c0 :: rest =>
      match applyBagFA a b u k idx rest with
      | some rest' => some (c0 :: rest')
      | none => none
  | _, _ => none

theorem applyBagFA_sound {N : Nat} {env : Nat → Bool} {a b u k : Nat}
    (hk_lt : 103 + k < N)
    (hk_ev : env (103 + k) = (evalSymMask N env a && evalSymMask N env b)) :
    ∀ (idx : Nat) (bag bag' : List (List Nat)),
      applyBagFA a b u k idx bag = some bag' →
      evalBag N env bag' = evalBag N env bag
  | 0, [], _, h => by cases h
  | 0, [_], _, h => by cases h
  | 0, c0 :: c1 :: rest, bag', h => by
    dsimp only [applyBagFA] at h
    cases hst : stepColFA a b u k c0 c1 with
    | none => rw [hst] at h; cases h
    | some p =>
      rcases p with ⟨c0', c1'⟩
      rw [hst] at h; dsimp only at h
      injection h with hbag'; subst hbag'
      have hcol := stepColFA_sound hk_lt hk_ev hst
      dsimp only [evalBag]
      omega
  | idx + 1, [], _, h => by cases h
  | idx + 1, c0 :: rest, bag', h => by
    dsimp only [applyBagFA] at h
    cases hst : applyBagFA a b u k idx rest with
    | none => rw [hst] at h; cases h
    | some rest' =>
      rw [hst] at h; dsimp only at h
      injection h with hbag'; subst hbag'
      dsimp only [evalBag]
      rw [applyBagFA_sound hk_lt hk_ev idx rest rest' hst]

def stepColDisjXor (k1 k2 : Nat) (c0 : List Nat) : Option (List Nat) :=
  let m1 := Nat.shiftLeft 1 (103 + k1)
  let m2 := Nat.shiftLeft 1 (103 + k2)
  match removeOne m1 c0 with
  | none => none
  | some r1 =>
      match removeOne m2 r1 with
      | none => none
      | some r2 => some ((m1 ^^^ m2) :: r2)

theorem stepColDisjXor_sound {N : Nat} {env : Nat → Bool} {k1 k2 : Nat} {p1 p2 : Nat × Nat}
    (hk1_lt : 103 + k1 < N) (hk2_lt : 103 + k2 < N)
    (hk1_ev : env (103 + k1) = (evalSymMask N env p1.1 && evalSymMask N env p1.2))
    (hk2_ev : env (103 + k2) = (evalSymMask N env p2.1 && evalSymMask N env p2.2))
    (hdisj : (p1.1 ^^^ p1.2) = p2.2)
    {c0 c0' : List Nat}
    (h : stepColDisjXor k1 k2 c0 = some c0') :
    evalCol N env c0' = evalCol N env c0 := by
  dsimp only [stepColDisjXor] at h
  cases hr1 : removeOne (Nat.shiftLeft 1 (103 + k1)) c0 with
  | none => rw [hr1] at h; cases h
  | some r1 =>
    rw [hr1] at h; dsimp only at h
    cases hr2 : removeOne (Nat.shiftLeft 1 (103 + k2)) r1 with
    | none => rw [hr2] at h; cases h
    | some r2 =>
      rw [hr2] at h; dsimp only at h
      injection h with hc0'; subst hc0'
      have hrem1 := removeOne_sound N env (Nat.shiftLeft 1 (103 + k1)) c0 r1 hr1
      have hrem2 := removeOne_sound N env (Nat.shiftLeft 1 (103 + k2)) r1 r2 hr2
      have h_id := disjXor_bool_id (evalSymMask N env p1.1)
        (evalSymMask N env p1.2) (evalSymMask N env p2.1)
      have hp2_2 : evalSymMask N env p2.2 =
          xor (evalSymMask N env p1.1) (evalSymMask N env p1.2) := by
        rw [← hdisj, evalSymMask_xor]
      dsimp only [evalCol]
      rw [hrem1, hrem2]
      simp only [evalSymMask_xor, evalSymMask_shiftLeft_one env hk1_lt,
        evalSymMask_shiftLeft_one env hk2_lt, hk1_ev, hk2_ev, hp2_2]
      omega

def applyBagDisjXor (k1 k2 : Nat) : Nat → List (List Nat) → Option (List (List Nat))
  | 0, c0 :: rest =>
      match stepColDisjXor k1 k2 c0 with
      | some c0' => some (c0' :: rest)
      | none => none
  | idx + 1, c0 :: rest =>
      match applyBagDisjXor k1 k2 idx rest with
      | some rest' => some (c0 :: rest')
      | none => none
  | _, [] => none

theorem applyBagDisjXor_sound {N : Nat} {env : Nat → Bool} {k1 k2 : Nat} {p1 p2 : Nat × Nat}
    (hk1_lt : 103 + k1 < N) (hk2_lt : 103 + k2 < N)
    (hk1_ev : env (103 + k1) = (evalSymMask N env p1.1 && evalSymMask N env p1.2))
    (hk2_ev : env (103 + k2) = (evalSymMask N env p2.1 && evalSymMask N env p2.2))
    (hdisj : (p1.1 ^^^ p1.2) = p2.2) :
    ∀ (idx : Nat) (bag bag' : List (List Nat)),
      applyBagDisjXor k1 k2 idx bag = some bag' →
      evalBag N env bag' = evalBag N env bag
  | 0, [], _, h => by cases h
  | 0, c0 :: rest, bag', h => by
    dsimp only [applyBagDisjXor] at h
    cases hst : stepColDisjXor k1 k2 c0 with
    | none => rw [hst] at h; cases h
    | some c0' =>
      rw [hst] at h; dsimp only at h
      injection h with hbag'; subst hbag'
      dsimp only [evalBag]
      rw [stepColDisjXor_sound hk1_lt hk2_lt hk1_ev hk2_ev hdisj hst]
  | idx + 1, [], _, h => by cases h
  | idx + 1, c0 :: rest, bag', h => by
    dsimp only [applyBagDisjXor] at h
    cases hst : applyBagDisjXor k1 k2 idx rest with
    | none => rw [hst] at h; cases h
    | some rest' =>
      rw [hst] at h; dsimp only at h
      injection h with hbag'; subst hbag'
      dsimp only [evalBag]
      rw [applyBagDisjXor_sound hk1_lt hk2_lt hk1_ev hk2_ev hdisj idx rest rest' hst]

inductive BagStep : Type where
  | fa (col k u : Nat)
  | disjXor (col k1 k2 : Nat)

def stepBag (defs : List (Nat × Nat)) (bag : List (List Nat)) : BagStep → Option (List (List Nat))
  | .fa col k u =>
      match defs[k]? with
      | some (a, b) => applyBagFA a b u k col bag
      | none => none
  | .disjXor col k1 k2 =>
      match defs[k1]?, defs[k2]? with
      | some p1, some p2 =>
          cond (Nat.beq (p1.1 ^^^ p1.2) p2.2)
            (applyBagDisjXor k1 k2 col bag) none
      | _, _ => none

theorem stepBag_sound {N : Nat} {env : Nat → Bool} {defs : List (Nat × Nat)}
    (hDefs : DefsOK N env defs)
    {bag bag' : List (List Nat)} {st : BagStep}
    (h : stepBag defs bag st = some bag') :
    evalBag N env bag' = evalBag N env bag := by
  cases st with
  | fa col k u =>
    dsimp only [stepBag] at h
    cases hk : defs[k]? with
    | none => rw [hk] at h; cases h
    | some p =>
      rcases p with ⟨a, b⟩
      rw [hk] at h; dsimp only at h
      have hlt : k < defs.length := (List.getElem?_eq_some_iff.mp hk).1
      exact applyBagFA_sound (by have := hDefs.1; omega) (hDefs.2 k (a, b) hk) col bag bag' h
  | disjXor col k1 k2 =>
    dsimp only [stepBag] at h
    cases hk1 : defs[k1]? with
    | none => rw [hk1] at h; cases h
    | some p1 =>
      rw [hk1] at h
      cases hk2 : defs[k2]? with
      | none => rw [hk2] at h; cases h
      | some p2 =>
        rw [hk2] at h; dsimp only at h
        cases hc : Nat.beq (p1.1 ^^^ p1.2) p2.2
        · rw [hc, Bool.cond_false] at h; cases h
        rw [hc, Bool.cond_true] at h
        have hlt1 : k1 < defs.length := (List.getElem?_eq_some_iff.mp hk1).1
        have hlt2 : k2 < defs.length := (List.getElem?_eq_some_iff.mp hk2).1
        exact applyBagDisjXor_sound (by have := hDefs.1; omega) (by have := hDefs.1; omega)
          (hDefs.2 k1 p1 hk1) (hDefs.2 k2 p2 hk2) (Nat.beq_eq.mp hc) col bag bag' h

def reduceBag (defs : List (Nat × Nat)) : List BagStep → List (List Nat) → Option (List (List Nat))
  | [], bag => some bag
  | st :: sts, bag =>
      match stepBag defs bag st with
      | some bag1 => reduceBag defs sts bag1
      | none => none

theorem reduceBag_sound {N : Nat} {env : Nat → Bool} {defs : List (Nat × Nat)}
    (hDefs : DefsOK N env defs) :
    ∀ (sts : List BagStep) {bag bag' : List (List Nat)},
      reduceBag defs sts bag = some bag' →
      evalBag N env bag' = evalBag N env bag
  | [], _, _, h => by injection h with h'; subst h'; rfl
  | st :: sts, bag, bag', h => by
    dsimp only [reduceBag] at h
    cases h1 : stepBag defs bag st with
    | none => rw [h1] at h; cases h
    | some bag1 =>
      rw [h1] at h
      rw [reduceBag_sound hDefs sts h, stepBag_sound hDefs h1]

def targVal : List Nat → (Fin 100 → Bool) → Nat
  | [], _ => 0
  | w :: ws, m =>
      let b := if h : w < 100 then m ⟨w, h⟩ else false
      (cond b 1 0) + 2 * targVal ws m

theorem targVal_lt : ∀ (ws : List Nat) (m : Fin 100 → Bool), targVal ws m < 2 ^ ws.length
  | [], _ => by simp [targVal]
  | w :: ws, m => by
    dsimp only [targVal, List.length_cons]
    have ih := targVal_lt ws m
    have hb : (cond (if h : w < 100 then m ⟨w, h⟩ else false) 1 0) ≤ 1 := by
      cases (if h : w < 100 then m ⟨w, h⟩ else false) <;> decide
    have hpow : 2 ^ (ws.length + 1) = 2 * 2 ^ ws.length := by ring
    omega

def targVal2 : List Nat → (Fin 100 → Bool) → Nat
  | [w1, w2], m => targVal [w1] m + targVal [w2] m
  | w1 :: w2 :: w3 :: ws, m => targVal [w1] m + 2 * targVal2 (w2 :: w3 :: ws) m
  | _, _ => 0

def checkBagExact (trf : WTree) : List Nat → List (List Nat) → Bool
  | [w1, w2], [[m2, m1], []] =>
      Nat.blt w1 100 && Nat.blt w2 100 &&
      Nat.beq m1 (sGet trf w1) && Nat.beq m2 (sGet trf w2)
  | w1 :: w2 :: w3 :: ws, [m] :: cols =>
      Nat.blt w1 100 && Nat.beq m (sGet trf w1) && checkBagExact trf (w2 :: w3 :: ws) cols
  | _, _ => false

theorem checkBagExact_sound {N : Nat} {env : Nat → Bool} {trf : WTree} {mf : Fin 100 → Bool}
    (hIf : SymInv N env trf mf) :
    ∀ (ws : List Nat) (bag : List (List Nat)),
      checkBagExact trf ws bag = true →
      evalBag N env bag = targVal2 ws mf
  | [], _, h => by cases h
  | [_], _, h => by cases h
  | [_, _], [], h => by cases h
  | [_, _], [] :: _, h => by cases h
  | [_, _], [_] :: _, h => by cases h
  | [_, _], (_ :: _ :: _ :: _) :: _, h => by cases h
  | [_, _], [_, _] :: [], h => by cases h
  | [_, _], [_, _] :: (_ :: _) :: _, h => by cases h
  | [_, _], [_, _] :: [] :: _ :: _, h => by cases h
  | [w1, w2], [[m2, m1], []], h => by
    dsimp only [checkBagExact] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨hw1, hw2⟩, hm1⟩, hm2⟩ := h
    dsimp only [evalBag, evalCol, targVal2, targVal]
    rw [dite_eq_left hw1, dite_eq_left hw2, hIf.hWire ⟨w1, hw1⟩, hIf.hWire ⟨w2, hw2⟩, hm1, hm2]
    dsimp only
    omega
  | _ :: _ :: _ :: _, [], h => by cases h
  | _ :: _ :: _ :: _, [] :: _, h => by cases h
  | _ :: _ :: _ :: _, (_ :: _ :: _) :: _, h => by cases h
  | w1 :: w2 :: w3 :: ws, [m] :: cols, h => by
    dsimp only [checkBagExact] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hw1, hm⟩, hrest⟩ := h
    have ih := checkBagExact_sound hIf (w2 :: w3 :: ws) cols hrest
    dsimp only [evalBag, evalCol, targVal2, targVal]
    rw [dite_eq_left hw1, hIf.hWire ⟨w1, hw1⟩, hm]
    dsimp only
    omega

def xorMaskList : List Nat → Nat
  | [] => 0
  | m :: ms => m ^^^ xorMaskList ms

theorem cond_xor_mod_two (a b : Bool) (r : Nat) (hr : r % 2 = cond b 1 0) :
    ((cond a 1 0) + r) % 2 = cond (xor a b) 1 0 := by
  cases a <;> cases b
  · change r % 2 = 0 at hr; change (0 + r) % 2 = 0; omega
  · change r % 2 = 1 at hr; change (0 + r) % 2 = 1; omega
  · change r % 2 = 0 at hr; change (1 + r) % 2 = 1; omega
  · change r % 2 = 1 at hr; change (1 + r) % 2 = 0; omega

theorem evalCol_mod_two (N : Nat) (env : Nat → Bool) :
    ∀ (col : List Nat),
      evalCol N env col % 2 = cond (evalSymMask N env (xorMaskList col)) 1 0
  | [] => by simp [evalCol, xorMaskList, evalSymMask_zero]
  | m :: ms => by
    dsimp only [evalCol, xorMaskList]
    rw [evalSymMask_xor]
    exact cond_xor_mod_two _ _ _ (evalCol_mod_two N env ms)

def checkBagMod (trf : WTree) : List Nat → List (List Nat) → Bool
  | [], _ => false
  | [w], [col] =>
      Nat.blt w 100 && Nat.beq (xorMaskList col) (sGet trf w)
  | [_], _ => false
  | w1 :: w2 :: ws, [m] :: cols =>
      Nat.blt w1 100 && Nat.beq m (sGet trf w1) && checkBagMod trf (w2 :: ws) cols
  | _ :: _ :: _, _ => false

theorem checkBagMod_sound {N : Nat} {env : Nat → Bool} {trf : WTree} {mf : Fin 100 → Bool}
    (hIf : SymInv N env trf mf) :
    ∀ (ws : List Nat) (bag : List (List Nat)),
      checkBagMod trf ws bag = true →
      evalBag N env bag % 2 ^ ws.length = targVal ws mf
  | [], _, h => by cases h
  | [w], [], h => by cases h
  | [w], [col], h => by
    dsimp only [checkBagMod] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨hw, hxor⟩ := h
    change evalBag N env [col] % 2 = targVal [w] mf
    dsimp only [evalBag, targVal]
    rw [dite_eq_left hw, hIf.hWire ⟨w, hw⟩]
    dsimp only
    rw [← hxor, Nat.mul_zero, Nat.add_zero, Nat.add_zero, evalCol_mod_two]
  | [w], _ :: _ :: _, h => by cases h
  | w1 :: w2 :: ws, [], h => by cases h
  | w1 :: w2 :: ws, [] :: _, h => by cases h
  | w1 :: w2 :: ws, (_ :: _ :: _) :: _, h => by cases h
  | w1 :: w2 :: ws, [m] :: cols, h => by
    dsimp only [checkBagMod] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hw1, hm⟩, hrest⟩ := h
    have ih := checkBagMod_sound hIf (w2 :: ws) cols hrest
    dsimp only [evalBag, evalCol, targVal, List.length_cons] at ih ⊢
    rw [dite_eq_left hw1, hIf.hWire ⟨w1, hw1⟩, hm, Nat.add_zero]
    dsimp only
    have hb0 : cond (evalSymMask N env (sGet trf w1)) 1 0 < 2 := by
      cases evalSymMask N env (sGet trf w1) <;> decide
    set b0 := cond (evalSymMask N env (sGet trf w1)) 1 0
    set R := evalBag N env cols
    set P := 2 ^ (ws.length + 1)
    have hdiv := Nat.div_add_mod R P
    have hmod_lt : R % P < P := Nat.mod_lt _ (by positivity)
    have hpow : 2 ^ (ws.length + 1 + 1) = 2 * P := by dsimp [P]; ring
    have heq : b0 + 2 * R = (b0 + 2 * (R % P)) + (R / P) * (2 * P) := by linarith
    rw [hpow, heq, Nat.add_mul_mod_self_right, ih, Nat.mod_eq_of_lt]
    have htlt := targVal_lt (w2 :: ws) mf
    dsimp only [List.length_cons] at htlt
    omega

-- ============================================================================
-- Stage-Level Symbolic Certificates (mkSymTree0, checkSymTree0, checkNonOutSym)
-- ============================================================================

def buildSymTree (cleanW : List Nat) : Nat → Nat → WTree
  | 0, base =>
      let v := if base < 100 && !(cleanW.elem base) then Nat.shiftLeft 1 (base + 1) else 0
      .leaf v
  | d + 1, base =>
      let half := Nat.shiftLeft 1 d
      .node (buildSymTree cleanW d base) (buildSymTree cleanW d (base + half))

def mkSymTree0 (cleanW : List Nat) : WTree :=
  buildSymTree cleanW 7 0

def checkSymTree0 (cleanW : List Nat) (tr0 : WTree) : Nat → Bool
  | 0 => true
  | q + 1 =>
      let exp := if cleanW.elem q then 0 else Nat.shiftLeft 1 (q + 1)
      Nat.beq (sGet tr0 q) exp && checkSymTree0 cleanW tr0 q

theorem checkSymTree0_sound (cleanW : List Nat) (tr0 : WTree) :
    ∀ (k : Nat), checkSymTree0 cleanW tr0 k = true →
      ∀ (q : Nat), q < k →
        sGet tr0 q = if cleanW.elem q then 0 else Nat.shiftLeft 1 (q + 1)
  | 0, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | k + 1, h, q, hq => by
    dsimp only [checkSymTree0] at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    by_cases hqk : q = k
    · subst hqk; exact h.1
    · exact checkSymTree0_sound cleanW tr0 k h.2 q (by omega)

theorem symInv_of_checkSymTree0 {N : Nat} {cleanW : List Nat} {tr0 : WTree}
    {m0 : Fin 100 → Bool} {defs : List (Nat × Nat)}
    (hlen : 103 + defs.length ≤ N)
    (hwf : checkWTreeWF 7 tr0 = true)
    (ht0 : checkSymTree0 cleanW tr0 100 = true)
    (hclean : ∀ w : Fin 100, w.val ∈ cleanW → m0 w = false) :
    SymInv N (buildSymEnv N m0 defs) tr0 m0 := by
  refine ⟨checkWTreeWF_sound 7 tr0 hwf, by omega, ?_, fun w => ?_⟩
  · unfold buildSymEnv
    rw [buildSymEnvAux_lt N 103 defs (baseSymEnv m0) (by omega)]
    rfl
  · have hget := checkSymTree0_sound cleanW tr0 100 ht0 w.val w.isLt
    rw [hget]
    cases helem : cleanW.elem w.val
    · rw [ite_eq_right Bool.false_ne_true]
      rw [evalSymMask_shiftLeft_one _ (by have := w.isLt; omega)]
      unfold buildSymEnv
      rw [buildSymEnvAux_lt N 103 defs (baseSymEnv m0) (by have := w.isLt; omega)]
      unfold baseSymEnv
      rw [ite_eq_right (by omega), dite_eq_left (by have := w.isLt; omega)]
      congr 1
    · rw [ite_eq_left rfl]
      rw [evalSymMask_zero]
      exact hclean w (List.mem_of_elem_eq_true helem)

def checkNonOutSym (outW : List Nat) (tr0 trf : WTree) : Nat → Bool
  | 0 => true
  | q + 1 =>
      (outW.elem q || Nat.beq (sGet trf q) (sGet tr0 q)) &&
      checkNonOutSym outW tr0 trf q

theorem checkNonOutSym_sound (outW : List Nat) (tr0 trf : WTree) :
    ∀ (k : Nat), checkNonOutSym outW tr0 trf k = true →
      ∀ (q : Nat), q < k → q ∉ outW → sGet trf q = sGet tr0 q
  | 0, _, _, hq, _ => absurd hq (Nat.not_lt_zero _)
  | k + 1, h, q, hq, hnot => by
    dsimp only [checkNonOutSym] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    by_cases hqk : q = k
    · subst hqk
      rcases h.1 with helem | heq
      · exact absurd (List.mem_of_elem_eq_true helem) hnot
      · exact heq
    · exact checkNonOutSym_sound outW tr0 trf k h.2 q (by omega) hnot

def checkStageSymMod (N : Nat) (cleanW outW : List Nat) (ops : List Op102)
    (defs : List (Nat × Nat)) (initBag : List (List Nat)) (sts : List BagStep) : Bool :=
  let tr0 := mkSymTree0 cleanW
  Nat.ble (103 + defs.length) N &&
  checkWTreeWF 7 tr0 &&
  checkSymTree0 cleanW tr0 100 &&
  checkDefsWF 103 defs &&
  match runSymListOpt defs ops tr0, reduceBag defs sts initBag with
  | some trf, some bagf =>
      checkNonOutSym outW tr0 trf 100 &&
      checkBagMod trf outW bagf
  | _, _ => false

theorem checkStageSymMod_sound {N : Nat} {cleanW outW : List Nat} {ops : List Op102}
    {defs : List (Nat × Nat)} {initBag : List (List Nat)} {sts : List BagStep}
    (hcert : checkStageSymMod N cleanW outW ops defs initBag sts = true)
    {m0 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ cleanW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, w.val ∉ outW → mf w = m0 w) ∧
      targVal outW mf = evalBag N (buildSymEnv N m0 defs) initBag % 2 ^ outW.length := by
  unfold checkStageSymMod at hcert
  dsimp only at hcert
  set tr0 := mkSymTree0 cleanW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcert
  obtain ⟨⟨⟨⟨hlen, hwf⟩, ht0⟩, hdwf⟩, hrun⟩ := hcert
  cases hsym : runSymListOpt defs ops tr0 with
  | none => rw [hsym] at hrun; cases hrun
  | some trf =>
    rw [hsym] at hrun
    cases hbag : reduceBag defs sts initBag with
    | none => rw [hbag] at hrun; cases hrun
    | some bagf =>
      rw [hbag] at hrun; dsimp only at hrun
      simp only [Bool.and_eq_true] at hrun
      obtain ⟨hnon, hbm⟩ := hrun
      have hDefs := defsOK_buildSymEnv N m0 defs hlen hdwf
      have hI0 := symInv_of_checkSymTree0 hlen hwf ht0 hclean
      obtain ⟨mf, hex, hIf⟩ := runSymListOpt_sound hDefs ops hI0 hsym
      have hbag_eq := reduceBag_sound hDefs sts hbag
      have hmod_eq := checkBagMod_sound hIf outW bagf hbm
      refine ⟨mf, hex, fun w hw => ?_, by rw [← hmod_eq, hbag_eq]⟩
      have hs_eq := checkNonOutSym_sound outW tr0 trf 100 hnon w.val w.isLt hw
      rw [hIf.hWire w, hs_eq, ← hI0.hWire w]

def checkStageSymExact (N : Nat) (cleanW outW : List Nat) (ops : List Op102)
    (defs : List (Nat × Nat)) (initBag : List (List Nat)) (sts : List BagStep) : Bool :=
  let tr0 := mkSymTree0 cleanW
  Nat.ble (103 + defs.length) N &&
  checkWTreeWF 7 tr0 &&
  checkSymTree0 cleanW tr0 100 &&
  checkDefsWF 103 defs &&
  match runSymListOpt defs ops tr0, reduceBag defs sts initBag with
  | some trf, some bagf =>
      checkNonOutSym outW tr0 trf 100 &&
      checkBagExact trf outW bagf
  | _, _ => false

theorem checkStageSymExact_sound {N : Nat} {cleanW outW : List Nat} {ops : List Op102}
    {defs : List (Nat × Nat)} {initBag : List (List Nat)} {sts : List BagStep}
    (hcert : checkStageSymExact N cleanW outW ops defs initBag sts = true)
    {m0 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ cleanW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, w.val ∉ outW → mf w = m0 w) ∧
      targVal2 outW mf = evalBag N (buildSymEnv N m0 defs) initBag := by
  unfold checkStageSymExact at hcert
  dsimp only at hcert
  set tr0 := mkSymTree0 cleanW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcert
  obtain ⟨⟨⟨⟨hlen, hwf⟩, ht0⟩, hdwf⟩, hrun⟩ := hcert
  cases hsym : runSymListOpt defs ops tr0 with
  | none => rw [hsym] at hrun; cases hrun
  | some trf =>
    rw [hsym] at hrun
    cases hbag : reduceBag defs sts initBag with
    | none => rw [hbag] at hrun; cases hrun
    | some bagf =>
      rw [hbag] at hrun; dsimp only at hrun
      simp only [Bool.and_eq_true] at hrun
      obtain ⟨hnon, hbe⟩ := hrun
      have hDefs := defsOK_buildSymEnv N m0 defs hlen hdwf
      have hI0 := symInv_of_checkSymTree0 hlen hwf ht0 hclean
      obtain ⟨mf, hex, hIf⟩ := runSymListOpt_sound hDefs ops hI0 hsym
      have hbag_eq := reduceBag_sound hDefs sts hbag
      have hex_eq := checkBagExact_sound hIf outW bagf hbe
      refine ⟨mf, hex, fun w hw => ?_, by rw [← hex_eq, hbag_eq]⟩
      have hs_eq := checkNonOutSym_sound outW tr0 trf 100 hnon w.val w.isLt hw
      rw [hIf.hWire w, hs_eq, ← hI0.hWire w]

def checkExtraSym (trf : WTree) : List (Nat × Nat) → Bool
  | [] => true
  | (w, m) :: rest =>
      Nat.blt w 100 && Nat.beq (sGet trf w) m && checkExtraSym trf rest

theorem checkExtraSym_sound {N : Nat} {env : Nat → Bool} {trf : WTree} {mf : Fin 100 → Bool}
    (hIf : SymInv N env trf mf) :
    ∀ (extraW : List (Nat × Nat)),
      checkExtraSym trf extraW = true →
      ∀ p ∈ extraW, ∀ (hw : p.1 < 100), mf ⟨p.1, hw⟩ = evalSymMask N env p.2
  | [], _, _, hp, _ => by cases hp
  | (w, m) :: rest, h, p, hp, hw => by
    dsimp only [checkExtraSym] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    rcases List.mem_cons.mp hp with rfl | hmem
    · rw [hIf.hWire ⟨w, hw⟩, h.1.2]
    · exact checkExtraSym_sound hIf rest h.2 p hmem hw

def checkStageSymModExtra (N : Nat) (cleanW outW : List Nat) (extraW : List (Nat × Nat))
    (ops : List Op102) (defs : List (Nat × Nat)) (initBag : List (List Nat))
    (sts : List BagStep) : Bool :=
  let tr0 := mkSymTree0 cleanW
  Nat.ble (103 + defs.length) N &&
  checkWTreeWF 7 tr0 &&
  checkSymTree0 cleanW tr0 100 &&
  checkDefsWF 103 defs &&
  match runSymListOpt defs ops tr0, reduceBag defs sts initBag with
  | some trf, some bagf =>
      checkNonOutSym (outW ++ extraW.map Prod.fst) tr0 trf 100 &&
      checkExtraSym trf extraW &&
      checkBagMod trf outW bagf
  | _, _ => false

theorem checkStageSymModExtra_sound {N : Nat} {cleanW outW : List Nat} {extraW : List (Nat × Nat)}
    {ops : List Op102} {defs : List (Nat × Nat)} {initBag : List (List Nat)} {sts : List BagStep}
    (hcert : checkStageSymModExtra N cleanW outW extraW ops defs initBag sts = true)
    {m0 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ cleanW → m0 w = false) :
    ∃ mf : Fin 100 → Bool,
      execList102 ops m0 = some mf ∧
      (∀ w : Fin 100, w.val ∉ outW ++ extraW.map Prod.fst → mf w = m0 w) ∧
      (∀ p ∈ extraW, ∀ (hw : p.1 < 100), mf ⟨p.1, hw⟩ = evalSymMask N (buildSymEnv N m0 defs) p.2) ∧
      targVal outW mf = evalBag N (buildSymEnv N m0 defs) initBag % 2 ^ outW.length := by
  unfold checkStageSymModExtra at hcert
  dsimp only at hcert
  set tr0 := mkSymTree0 cleanW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcert
  obtain ⟨⟨⟨⟨hlen, hwf⟩, ht0⟩, hdwf⟩, hrun⟩ := hcert
  cases hsym : runSymListOpt defs ops tr0 with
  | none => rw [hsym] at hrun; cases hrun
  | some trf =>
    rw [hsym] at hrun
    cases hbag : reduceBag defs sts initBag with
    | none => rw [hbag] at hrun; cases hrun
    | some bagf =>
      rw [hbag] at hrun; dsimp only at hrun
      simp only [Bool.and_eq_true] at hrun
      obtain ⟨⟨hnon, hext⟩, hbm⟩ := hrun
      have hDefs := defsOK_buildSymEnv N m0 defs hlen hdwf
      have hI0 := symInv_of_checkSymTree0 hlen hwf ht0 hclean
      obtain ⟨mf, hex, hIf⟩ := runSymListOpt_sound hDefs ops hI0 hsym
      have hbag_eq := reduceBag_sound hDefs sts hbag
      have hmod_eq := checkBagMod_sound hIf outW bagf hbm
      refine ⟨mf, hex, fun w hw => ?_, checkExtraSym_sound hIf extraW hext,
        by rw [← hmod_eq, hbag_eq]⟩
      have hs_eq := checkNonOutSym_sound (outW ++ extraW.map Prod.fst)
        tr0 trf 100 hnon w.val w.isLt hw
      rw [hIf.hWire w, hs_eq, ← hI0.hWire w]



-- ============================================================================
-- Op102.inSub, execList102_congr_sub, and execList102_revOps_congr_ge25
-- ============================================================================

def Op102.inSub (p : Nat → Bool) : Op102 → Bool
  | .x q => p q
  | .cx c t => p c && p t
  | .and4t c1 c2 t => p c1 && p c2 && p t
  | .rccx0 c1 c2 t => p c1 && p c2 && p t
  | .rccx1 c1 c2 t => p c1 && p c2 && p t
  | .unand c1 c2 t => p c1 && p c2 && p t
  | .unquad qs ls t => (qs.all fun q => p q.1 && p q.2) && (ls.all p) && p t
  | .z q => p q
  | .cz c1 c2 => p c1 && p c2
  | .hGadget t pos neg _ ul =>
      (pos.all fun s => s.2.all p) && (neg.all fun s => s.2.all p) && (ul.all p) && p t

theorem evalQuadBool102_congr_sub (p : Nat → Bool) {m1 m2 : Fin 100 → Bool}
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    ∀ qs : List (Nat × Nat), (qs.all fun q => p q.1 && p q.2) = true →
      evalQuadBool102 m2 qs = evalQuadBool102 m1 qs
  | [], _ => rfl
  | q :: qs, hq => by
    simp only [List.all_cons, Bool.and_eq_true] at hq
    simp only [evalQuadBool102, evalQuadBool102_congr_sub p hin qs hq.2]
    by_cases hlt : q.1 < 100 ∧ q.2 < 100
    · simp only [dite_eq_left hlt, hin ⟨q.1, hlt.1⟩ hq.1.1, hin ⟨q.2, hlt.2⟩ hq.1.2]
    · simp only [dite_eq_right hlt]

theorem evalLinBool102_congr_sub (p : Nat → Bool) {m1 m2 : Fin 100 → Bool}
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    ∀ ls : List Nat, (ls.all p) = true →
      evalLinBool102 m2 ls = evalLinBool102 m1 ls
  | [], _ => rfl
  | c :: ls, hl => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    simp only [evalLinBool102, evalLinBool102_congr_sub p hin ls hl.2]
    by_cases hlt : c < 100
    · simp only [dite_eq_left hlt, hin ⟨c, hlt⟩ hl.1]
    · simp only [dite_eq_right hlt]

theorem evalHPosBool_congr_sub (p : Nat → Bool) {m1 m2 : Fin 100 → Bool}
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    ∀ (steps : List (Bool × List Nat)) (st : Bool × Bool × Bool × Bool),
      (steps.all fun s => s.2.all p) = true →
      evalHPosBool m2 steps st = evalHPosBool m1 steps st
  | [], _, _ => rfl
  | (xc, ls) :: rest, (dt, b0, b1, b2), hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    dsimp only [evalHPosBool]
    rw [evalLinBool102_congr_sub p hin ls hs.1, evalHPosBool_congr_sub p hin rest _ hs.2]

theorem evalHNegBool_congr_sub (p : Nat → Bool) {m1 m2 : Fin 100 → Bool}
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    ∀ (steps : List (Bool × List Nat)) (st : Bool × Bool × Bool × Bool),
      (steps.all fun s => s.2.all p) = true →
      evalHNegBool m2 steps st = evalHNegBool m1 steps st
  | [], _, _ => rfl
  | (xc, ls) :: rest, (dt, b0, b1, b2), hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    dsimp only [evalHNegBool]
    rw [evalLinBool102_congr_sub p hin ls hs.1, evalHNegBool_congr_sub p hin rest _ hs.2]

theorem evalHGadgetBool_congr_sub (p : Nat → Bool) {m1 m2 : Fin 100 → Bool}
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w)
    {pos neg : List (Bool × List Nat)} {uc : Bool} {ul : List Nat}
    (hpos : (pos.all fun s => s.2.all p) = true)
    (hneg : (neg.all fun s => s.2.all p) = true)
    (hul : (ul.all p) = true) :
    evalHGadgetBool m2 pos neg uc ul = evalHGadgetBool m1 pos neg uc ul := by
  unfold evalHGadgetBool
  dsimp only
  rw [evalHPosBool_congr_sub p hin pos _ hpos,
      evalHNegBool_congr_sub p hin neg _ hneg,
      evalLinBool102_congr_sub p hin ul hul]

theorem phaseOp102_congr_sub (p : Nat → Bool) {op : Op102} (hp : op.inSub p = true)
    {m1 m2 : Fin 100 → Bool}
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    phaseOp102 m2 op = phaseOp102 m1 op := by
  cases op with
  | z q =>
    dsimp only [Op102.inSub] at hp
    dsimp only [phaseOp102]
    by_cases hq : q < 100
    · rw [dite_eq_left hq, dite_eq_left hq, hin ⟨q, hq⟩ hp]
    · rw [dite_eq_right hq, dite_eq_right hq]
  | cz c1 c2 =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [phaseOp102]
    by_cases hc : c1 < 100 ∧ c2 < 100
    · rw [dite_eq_left hc, dite_eq_left hc, hin ⟨c1, hc.1⟩ hp.1, hin ⟨c2, hc.2⟩ hp.2]
    · rw [dite_eq_right hc, dite_eq_right hc]
  | hGadget _ pos neg uc ul =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [phaseOp102]
    rw [evalHGadgetBool_congr_sub p hin hp.1.1.1 hp.1.1.2 hp.1.2]
  | _ => rfl

theorem execOp102_congr_sub (p : Nat → Bool) {op : Op102} (hp : op.inSub p = true)
    {m1 m1' m2 : Fin 100 → Bool}
    (h1 : execOp102 m1 op = some m1')
    (hin : ∀ w : Fin 100, p w.val = true → m2 w = m1 w) :
    ∃ m2', execOp102 m2 op = some m2' ∧
      (∀ w : Fin 100, p w.val = false → m2' w = m2 w) ∧
      (∀ w : Fin 100, p w.val = true → m2' w = m1' w) := by
  cases op with
  | x q =>
    dsimp only [Op102.inSub] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hq
    injection h1 with hm1'; subst hm1'
    refine ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hq], fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp] at hw; cases hw) _ _
    · by_cases hwq : w = ⟨q, hq⟩
      · subst hwq; simp [Function.update_self, hin ⟨q, hq⟩ hp]
      · simp [Function.update_of_ne hwq, hin w hw]
  | cx c t =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc
    injection h1 with hm1'; subst hm1'
    refine ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hc], fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, hc.2.1⟩
      · subst hwt
        simp [Function.update_self, hin ⟨t, hc.2.1⟩ hp.2, hin ⟨c, hc.1⟩ hp.1]
      · simp [Function.update_of_ne hwt, hin w hw]
  | and4t c1 c2 t =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc hmt
    injection h1 with hm1'; subst hm1'
    have hmt2 : m2 ⟨t, hc.2.2.1⟩ = false := (hin ⟨t, hc.2.2.1⟩ hp.2).trans hmt
    refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hc, ite_eq_left hmt2]),
      fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, hc.2.2.1⟩
      · subst hwt
        simp [Function.update_self, hin ⟨c1, hc.1⟩ hp.1.1, hin ⟨c2, hc.2.1⟩ hp.1.2]
      · simp [Function.update_of_ne hwt, hin w hw]
  | rccx0 c1 c2 t =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc hmt
    injection h1 with hm1'; subst hm1'
    have hmt2 : (m2 ⟨c1, hc.1⟩ && m2 ⟨c2, hc.2.1⟩ && m2 ⟨t, hc.2.2.1⟩) = false := by
      rw [hin ⟨c1, hc.1⟩ hp.1.1, hin ⟨c2, hc.2.1⟩ hp.1.2, hin ⟨t, hc.2.2.1⟩ hp.2, hmt]
    refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hc, ite_eq_left hmt2]),
      fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, hc.2.2.1⟩
      · subst hwt
        simp [Function.update_self, hin ⟨t, hc.2.2.1⟩ hp.2,
          hin ⟨c1, hc.1⟩ hp.1.1, hin ⟨c2, hc.2.1⟩ hp.1.2]
      · simp [Function.update_of_ne hwt, hin w hw]
  | rccx1 c1 c2 t =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc hmt
    injection h1 with hm1'; subst hm1'
    have hmt2 : (m2 ⟨c1, hc.1⟩ && m2 ⟨c2, hc.2.1⟩ && !m2 ⟨t, hc.2.2.1⟩) = false := by
      rw [hin ⟨c1, hc.1⟩ hp.1.1, hin ⟨c2, hc.2.1⟩ hp.1.2, hin ⟨t, hc.2.2.1⟩ hp.2, hmt]
    refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hc, ite_eq_left hmt2]),
      fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, hc.2.2.1⟩
      · subst hwt
        simp [Function.update_self, hin ⟨t, hc.2.2.1⟩ hp.2,
          hin ⟨c1, hc.1⟩ hp.1.1, hin ⟨c2, hc.2.1⟩ hp.1.2]
      · simp [Function.update_of_ne hwt, hin w hw]
  | unand c1 c2 t =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc hmt
    injection h1 with hm1'; subst hm1'
    have hmt2 : m2 ⟨t, hc.2.2.1⟩ = (m2 ⟨c1, hc.1⟩ && m2 ⟨c2, hc.2.1⟩) := by
      rw [hin ⟨t, hc.2.2.1⟩ hp.2, hin ⟨c1, hc.1⟩ hp.1.1, hin ⟨c2, hc.2.1⟩ hp.1.2, hmt]
    refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hc, ite_eq_left hmt2]),
      fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, hc.2.2.1⟩
      · subst hwt; simp [Function.update_self]
      · simp [Function.update_of_ne hwt, hin w hw]
  | unquad qs ls t =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc hmt
    injection h1 with hm1'; subst hm1'
    have hmt2 : m2 ⟨t, hc.2.2⟩ = evalUnquad102 m2 qs ls := by
      rw [hin ⟨t, hc.2.2⟩ hp.2, hmt]
      unfold evalUnquad102
      rw [evalQuadBool102_congr_sub p hin qs hp.1.1, evalLinBool102_congr_sub p hin ls hp.1.2]
    refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hc, ite_eq_left hmt2]),
      fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, hc.2.2⟩
      · subst hwt; simp [Function.update_self]
      · simp [Function.update_of_ne hwt, hin w hw]
  | z q =>
    dsimp only [execOp102] at h1
    split_ifs at h1 with hq
    injection h1 with hm1'; subst hm1'
    exact ⟨m2, by dsimp only [execOp102]; rw [ite_eq_left hq], fun _ _ => rfl, hin⟩
  | cz c1 c2 =>
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc
    injection h1 with hm1'; subst hm1'
    exact ⟨m2, by dsimp only [execOp102]; rw [ite_eq_left hc], fun _ _ => rfl, hin⟩
  | hGadget t pos neg uc ul =>
    dsimp only [Op102.inSub] at hp
    simp only [Bool.and_eq_true] at hp
    dsimp only [execOp102] at h1
    split_ifs at h1 with hc hmt
    injection h1 with hm1'; subst hm1'
    have ht : t < 100 := checkHGadgetStatic_lt hc
    have hmt2 : m2 ⟨t, ht⟩ = false := (hin ⟨t, ht⟩ hp.2).trans hmt
    have hev : evalHGadgetBool m2 pos neg uc ul = evalHGadgetBool m1 pos neg uc ul :=
      evalHGadgetBool_congr_sub p hin hp.1.1.1 hp.1.1.2 hp.1.2
    refine ⟨_, (by dsimp only [execOp102]; rw [dite_eq_left hc, ite_eq_left hmt2]),
      fun w hw => ?_, fun w hw => ?_⟩
    · exact Function.update_of_ne
        (fun e => by subst e; dsimp only at hw; rw [hp.2] at hw; cases hw) _ _
    · by_cases hwt : w = ⟨t, ht⟩
      · subst hwt; simp [Function.update_self, hev]
      · simp [Function.update_of_ne hwt, hin w hw]

theorem execList102_congr_sub (p : Nat → Bool) : ∀ (ops : List Op102)
    (_ : (ops.all (Op102.inSub p)) = true)
    {m1 m1' m2 : Fin 100 → Bool},
    execList102 ops m1 = some m1' →
    (∀ w : Fin 100, p w.val = true → m2 w = m1 w) →
    ∃ m2', execList102 ops m2 = some m2' ∧
      (∀ w : Fin 100, p w.val = false → m2' w = m2 w) ∧
      (∀ w : Fin 100, p w.val = true → m2' w = m1' w)
  | [], _, m1, m1', m2, h1, hin => by
    injection h1 with hm1'; subst hm1'
    exact ⟨m2, rfl, fun _ _ => rfl, hin⟩
  | op :: ops, hp, m1, m1', m2, h1, hin => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    dsimp only [execList102] at h1
    cases hop1 : execOp102 m1 op with
    | none => rw [hop1] at h1; cases h1
    | some m1_a =>
      rw [hop1] at h1
      obtain ⟨m2_a, hop2, hout_a, hin_a⟩ := execOp102_congr_sub p hp.1 hop1 hin
      obtain ⟨m2', hex2, hout_b, hin_b⟩ := execList102_congr_sub p ops hp.2 h1 hin_a
      refine ⟨m2', by simp [execList102, hop2, hex2],
        fun w hw => (hout_b w hw).trans (hout_a w hw), hin_b⟩

theorem phaseList102_congr_sub (p : Nat → Bool) : ∀ (ops : List Op102)
    (_ : (ops.all (Op102.inSub p)) = true)
    {m1 m1' m2 : Fin 100 → Bool},
    execList102 ops m1 = some m1' →
    (∀ w : Fin 100, p w.val = true → m2 w = m1 w) →
    phaseList102 ops m2 = phaseList102 ops m1
  | [], _, _, _, _, _, _ => rfl
  | op :: ops, hp, m1, m1', m2, h1, hin => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    dsimp only [execList102] at h1
    cases hop1 : execOp102 m1 op with
    | none => rw [hop1] at h1; cases h1
    | some m1_a =>
      rw [hop1] at h1
      obtain ⟨m2_a, hop2, _, hin_a⟩ := execOp102_congr_sub p hp.1 hop1 hin
      dsimp only [phaseList102]
      rw [hop1, hop2]
      dsimp only
      rw [phaseOp102_congr_sub p hp.1 hin, phaseList102_congr_sub p ops hp.2 h1 hin_a]


theorem execList102_outSub (p : Nat → Bool) {ops : List Op102}
    (hp : (ops.all (Op102.inSub p)) = true)
    {m m' : Fin 100 → Bool} (hex : execList102 ops m = some m') :
    ∀ w : Fin 100, p w.val = false → m' w = m w := by
  obtain ⟨m2', hex2, hout, _⟩ := execList102_congr_sub p ops hp hex (fun _ _ => rfl)
  rw [hex] at hex2; injection hex2 with e; subst e
  exact hout

def pNoStash (stashW q : Nat) : Bool := !Nat.beq q stashW

def hopOps (src dst : Nat) : List Op102 :=
  if Nat.beq src dst then [] else [mkCX src dst, mkCX dst src]

def RelayInv (b48 : Bool) (stash : Fin 100) (m_log m_phys : Fin 100 → Bool) : Prop :=
  m_log stash = false ∧
  m_phys stash = b48 ∧
  ∀ w : Fin 100, w ≠ stash → m_phys w = m_log w

theorem exec_hopOps_ne {m : Fin 100 → Bool} {s d : Fin 100}
    (hne : s ≠ d) (hd : m d = false) :
    execList102 (hopOps s.val d.val) m =
      some (Function.update (Function.update m d (m s)) s false) := by
  have hv : s.val ≠ d.val := fun e => hne (Fin.ext e)
  have hbeq : Nat.beq s.val d.val = false := (beq_false_iff s.val d.val).mpr hv
  have hc1 : s.val < 100 ∧ d.val < 100 ∧ s.val ≠ d.val := ⟨s.isLt, d.isLt, hv⟩
  have hc2 : d.val < 100 ∧ s.val < 100 ∧ d.val ≠ s.val := ⟨d.isLt, s.isLt, hv.symm⟩
  unfold hopOps
  rw [hbeq, ite_eq_right Bool.false_ne_true]
  dsimp only [mkCX, execList102, execOp102]
  rw [dite_eq_left hc1]
  dsimp only [execList102, execOp102]
  rw [dite_eq_left hc2]
  dsimp only [execList102]
  have hs1 : (⟨s.val, hc1.1⟩ : Fin 100) = s := Fin.ext rfl
  have hd1 : (⟨d.val, hc1.2.1⟩ : Fin 100) = d := Fin.ext rfl
  rw [hs1, hd1, hd, Bool.false_xor,
      Function.update_self, Function.update_of_ne hne, Bool.xor_self]

theorem exec_swap48_relay {m : Fin 100 → Bool} {s0 : Fin 100}
    (hne : (⟨48, by decide⟩ : Fin 100) ≠ s0)
    (hs0 : m s0 = false) :
    ∃ m_phys, execList102 (hopOps 48 s0.val) m = some m_phys ∧
      RelayInv (m ⟨48, by decide⟩) s0 (Function.update m ⟨48, by decide⟩ false) m_phys := by
  refine ⟨_, exec_hopOps_ne hne hs0, ?_, ?_, fun w hw => ?_⟩
  · rw [Function.update_of_ne hne.symm]; exact hs0
  · rw [Function.update_of_ne hne.symm, Function.update_self]
  · by_cases hw48 : w = ⟨48, by decide⟩
    · subst hw48; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw48, Function.update_of_ne hw, Function.update_of_ne hw48]

theorem exec_chunk_relay {b48 : Bool} {s : Fin 100}
    {m_log m_log' m_phys : Fin 100 → Bool} {ops : List Op102}
    (hinv : RelayInv b48 s m_log m_phys)
    (hp : (ops.all (Op102.inSub (pNoStash s.val))) = true)
    (hex : execList102 ops m_log = some m_log') :
    ∃ m_phys', execList102 ops m_phys = some m_phys' ∧
      RelayInv b48 s m_log' m_phys' := by
  have hp_false : pNoStash s.val s.val = false := by
    unfold pNoStash; simp [Nat.beq_refl]
  have hin_eq : ∀ w : Fin 100, pNoStash s.val w.val = true → m_phys w = m_log w := by
    intro w hw
    have hne : w ≠ s := fun e => by subst e; rw [hp_false] at hw; cases hw
    exact hinv.2.2 w hne
  obtain ⟨m_phys', hex_p, hout_p, hin_p⟩ :=
    execList102_congr_sub (pNoStash s.val) ops hp hex hin_eq
  have hlog_s : m_log' s = false :=
    (execList102_outSub (pNoStash s.val) hp hex s hp_false).trans hinv.1
  have hphys_s : m_phys' s = b48 :=
    (hout_p s hp_false).trans hinv.2.1
  refine ⟨m_phys', hex_p, hlog_s, hphys_s, fun w hw => hin_p w ?_⟩
  unfold pNoStash
  have hvn : w.val ≠ s.val := fun e => hw (Fin.ext e)
  exact (Bool.not_eq_true' _).mpr ((beq_false_iff w.val s.val).mpr hvn)

theorem phaseList102_chunk_relay {b48 : Bool} {s : Fin 100}
    {m_log m_log' m_phys : Fin 100 → Bool} {ops : List Op102}
    (hinv : RelayInv b48 s m_log m_phys)
    (hp : (ops.all (Op102.inSub (pNoStash s.val))) = true)
    (hex : execList102 ops m_log = some m_log') :
    phaseList102 ops m_phys = phaseList102 ops m_log := by
  have hp_false : pNoStash s.val s.val = false := by
    unfold pNoStash; simp [Nat.beq_refl]
  have hin_eq : ∀ w : Fin 100, pNoStash s.val w.val = true → m_phys w = m_log w := by
    intro w hw
    have hne : w ≠ s := fun e => by subst e; rw [hp_false] at hw; cases hw
    exact hinv.2.2 w hne
  exact phaseList102_congr_sub (pNoStash s.val) ops hp hex hin_eq

theorem phaseList102_hopOps (src dst : Nat) (m : Fin 100 → Bool) :
    phaseList102 (hopOps src dst) m = false := by
  apply phaseList102_of_noPhase
  unfold hopOps
  split_ifs <;> rfl

theorem exec_hop_relay {b48 : Bool} {s1 s2 : Fin 100}
    {m_log m_phys : Fin 100 → Bool}
    (hinv : RelayInv b48 s1 m_log m_phys)
    (hs2 : s1 = s2 ∨ m_log s2 = false) :
    ∃ m_phys', execList102 (hopOps s1.val s2.val) m_phys = some m_phys' ∧
      RelayInv b48 s2 m_log m_phys' := by
  by_cases heq : s1 = s2
  · subst heq
    have hhop : hopOps s1.val s1.val = [] := by unfold hopOps; simp [Nat.beq_refl]
    rw [hhop]
    exact ⟨m_phys, rfl, hinv⟩
  · rcases hs2 with h | hm_s2
    · exact absurd h heq
    · have hp_s2 : m_phys s2 = false := (hinv.2.2 s2 (Ne.symm heq)).trans hm_s2
      refine ⟨_, exec_hopOps_ne heq hp_s2, hm_s2, ?_, fun w hw => ?_⟩
      · rw [Function.update_of_ne (Ne.symm heq), Function.update_self]; exact hinv.2.1
      · by_cases hws1 : w = s1
        · subst hws1; rw [Function.update_self, hinv.1]
        · rw [Function.update_of_ne hws1, Function.update_of_ne hw]; exact hinv.2.2 w hws1

theorem exec_unswap48_relay {b48 : Bool} {s : Fin 100}
    {m_log m_phys : Fin 100 → Bool}
    (hinv : RelayInv b48 s m_log m_phys)
    (hne : s ≠ ⟨48, by decide⟩)
    (h48 : m_log ⟨48, by decide⟩ = false) :
    execList102 (hopOps s.val 48) m_phys =
      some (Function.update m_log ⟨48, by decide⟩ b48) := by
  have hp48 : m_phys ⟨48, by decide⟩ = false := (hinv.2.2 ⟨48, by decide⟩ hne.symm).trans h48
  rw [exec_hopOps_ne hne hp48]
  congr 1; funext w
  by_cases hws : w = s
  · subst hws; rw [Function.update_self, Function.update_of_ne hne, hinv.1]
  · rw [Function.update_of_ne hws]
    by_cases hw48 : w = ⟨48, by decide⟩
    · subst hw48; rw [Function.update_self, Function.update_self, hinv.2.1]
    · rw [Function.update_of_ne hw48, Function.update_of_ne hw48]; exact hinv.2.2 w hws

def Op102.ge25 (op : Op102) : Bool := op.inSub (Nat.ble 25)

theorem execList102_congr_ge25 (ops : List Op102)
    (hge : (ops.all Op102.ge25) = true)
    {m1 m1' m2 : Fin 100 → Bool}
    (h1 : execList102 ops m1 = some m1')
    (hhigh : ∀ w : Fin 100, 25 ≤ w.val → m2 w = m1 w) :
    ∃ m2', execList102 ops m2 = some m2' ∧
      (∀ w : Fin 100, w.val < 25 → m2' w = m2 w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → m2' w = m1' w) := by
  obtain ⟨m2', hex, hlo, hhi⟩ := execList102_congr_sub (Nat.ble 25) ops hge h1
    (fun w hw => hhigh w (Nat.ble_eq.mp hw))
  refine ⟨m2', hex, fun w hw => hlo w ?_, fun w hw => hhi w (Nat.ble_eq.mpr hw)⟩
  cases h : Nat.ble 25 w.val
  · rfl
  · have := Nat.ble_eq.mp h; omega

def checkStageSymUncomp (N : Nat) (cleanW : List Nat)
    (fwdOps uncompOps : List Op102) (defs : List (Nat × Nat)) : Bool :=
  let tr0 := mkSymTree0 cleanW
  Nat.ble (103 + defs.length) N &&
  checkWTreeWF 7 tr0 &&
  checkSymTree0 cleanW tr0 100 &&
  checkDefsWF 103 defs &&
  uncompOps.all Op102.ge25 &&
  match runSymListOpt defs fwdOps tr0 with
  | some tr1 =>
      match runSymListOpt defs uncompOps tr1 with
      | some tr2 => checkNonOutSym [] tr0 tr2 100
      | none => false
  | none => false

theorem checkStageSymUncomp_sound {N : Nat} {cleanW : List Nat}
    {fwdOps uncompOps : List Op102} {defs : List (Nat × Nat)}
    (hcert : checkStageSymUncomp N cleanW fwdOps uncompOps defs = true)
    {m0 m1 m2 : Fin 100 → Bool}
    (hclean : ∀ w : Fin 100, w.val ∈ cleanW → m0 w = false)
    (hfwd : execList102 fwdOps m0 = some m1)
    (hhigh : ∀ w : Fin 100, 25 ≤ w.val → m2 w = m1 w) :
    ∃ m2', execList102 uncompOps m2 = some m2' ∧
      (∀ w : Fin 100, w.val < 25 → m2' w = m2 w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → m2' w = m0 w) := by
  unfold checkStageSymUncomp at hcert
  dsimp only at hcert
  set tr0 := mkSymTree0 cleanW
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcert
  obtain ⟨⟨⟨⟨⟨hlen, hwf⟩, ht0⟩, hdwf⟩, hge⟩, hrun⟩ := hcert
  cases hsym1 : runSymListOpt defs fwdOps tr0 with
  | none => rw [hsym1] at hrun; cases hrun
  | some tr1 =>
    rw [hsym1] at hrun; dsimp only at hrun
    cases hsym2 : runSymListOpt defs uncompOps tr1 with
    | none => rw [hsym2] at hrun; cases hrun
    | some tr2 =>
      rw [hsym2] at hrun; dsimp only at hrun
      have hDefs := defsOK_buildSymEnv N m0 defs hlen hdwf
      have hI0 := symInv_of_checkSymTree0 hlen hwf ht0 hclean
      obtain ⟨m1', hex1, hI1⟩ := runSymListOpt_sound hDefs fwdOps hI0 hsym1
      have hm1_eq : m1' = m1 := Option.some.inj (hex1.symm.trans hfwd)
      subst hm1_eq
      obtain ⟨m1_u, hex_u, hI2⟩ := runSymListOpt_sound hDefs uncompOps hI1 hsym2
      obtain ⟨m2', hex2, hlo, hhi⟩ := execList102_congr_ge25 uncompOps hge hex_u hhigh
      refine ⟨m2', hex2, hlo, fun w hw => ?_⟩
      have hs_eq := checkNonOutSym_sound [] tr0 tr2 100 hrun w.val w.isLt (by intro hm; cases hm)
      rw [hhi w hw, hI2.hWire w, hs_eq, ← hI0.hWire w]

theorem execList102_revOps_congr_ge25 {ops : List Op102}
    (hnq : (ops.all Op102.noUnquad) = true)
    (hge : ((revOps ops).all Op102.ge25) = true)
    {m0 m1 m2 : Fin 100 → Bool}
    (hfwd : execList102 ops m0 = some m1)
    (hhigh : ∀ w : Fin 100, 25 ≤ w.val → m2 w = m1 w) :
    ∃ m2', execList102 (revOps ops) m2 = some m2' ∧
      (∀ w : Fin 100, w.val < 25 → m2' w = m2 w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → m2' w = m0 w) :=
  execList102_congr_ge25 (revOps ops) hge (execList102_revOps ops hnq hfwd) hhigh

theorem execList102_flipList :
    ∀ (ws : List Nat) (m : Fin 100 → Bool),
      ws.Nodup →
      (ws.all fun w => Nat.blt w 100) = true →
      execList102 (ws.map mkX) m =
        some (fun w => if ws.elem w.val then !m w else m w)
  | [], m, _, _ => by simp [execList102]
  | q :: rest, m, hnd, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hall
    obtain ⟨hq_lt, hrest_all⟩ := hall
    obtain ⟨hq_not_mem, hnd_rest⟩ := List.nodup_cons.mp hnd
    have hop : execOp102 m (mkX q) = some (Function.update m ⟨q, hq_lt⟩ (!m ⟨q, hq_lt⟩)) := by
      dsimp only [execOp102, mkX]; rw [dite_eq_left hq_lt]
    rw [List.map_cons, execList102, hop]
    dsimp only
    rw [execList102_flipList rest _ hnd_rest hrest_all]
    congr 1; funext w
    rw [List.elem_cons]
    by_cases hwq : w.val = q
    · have hw_eq : w = ⟨q, hq_lt⟩ := Fin.ext hwq
      subst hw_eq
      simp [hq_not_mem, Function.update_self]
    · have hw_ne : w ≠ ⟨q, hq_lt⟩ := fun e => hwq (congrArg Fin.val e)
      have hb : (w.val == q) = false := beq_eq_false_iff_ne.mpr hwq
      rw [hb, Function.update_of_ne hw_ne]

-- ============================================================================
-- 512-bit Bit-Parallel WTree Evaluator for Stage 4.2 (sq9)
-- ============================================================================


theorem allM512_testBit {bit : Nat} (hbit : bit < 512) : allM512.testBit bit = true := by
  revert bit hbit; decide +kernel

structure BitPar512Inv (bit : Nat) (tr : WTree) (m : Fin 100 → Bool) : Prop where
  wf : WTreeWF 7 tr
  hbit : bit < 512
  hWire : ∀ w : Fin 100, m w = (sGet tr w.val).testBit bit

theorem BitPar512Inv.update {bit : Nat} {tr : WTree} {m : Fin 100 → Bool}
    (hI : BitPar512Inv bit tr m) {t : Nat} (ht : t < 100) (v : Nat) (b : Bool)
    (hb : v.testBit bit = b) :
    BitPar512Inv bit (sSet tr t v) (Function.update m ⟨t, ht⟩ b) := by
  refine ⟨sSet_wf hI.wf t v, hI.hbit, fun w => ?_⟩
  by_cases hwt : w = ⟨t, ht⟩
  · subst hwt
    simp [Function.update_self, sGet_sSet hI.wf ht ht, hb]
  · have hne : w.val ≠ t := fun e => hwt (Fin.ext e)
    simp [Function.update_of_ne hwt, sGet_sSet hI.wf ht w.isLt, hne, hI.hWire w]

def someNat (v : Nat) : Option Nat :=
  match v with
  | 0 => some 0
  | n + 1 => some (n + 1)

theorem someNat_eq (v : Nat) : someNat v = some v := by
  cases v <;> rfl

def fastXor (a b : Nat) : Nat :=
  cond (Nat.beq b 0) a (cond (Nat.beq a 0) b (a ^^^ b))

theorem fastXor_eq (a b : Nat) : fastXor a b = a ^^^ b := by
  unfold fastXor
  cases h1 : Nat.beq b 0
  · cases h2 : Nat.beq a 0
    · rfl
    · rw [Nat.beq_eq.mp h2, Nat.zero_xor]; rfl
  · rw [Nat.beq_eq.mp h1, Nat.xor_zero]; rfl

def fastLandXor (a b acc : Nat) : Nat :=
  cond (Nat.beq a 0 || Nat.beq b 0) acc (fastXor (a &&& b) acc)

theorem fastLandXor_eq (a b acc : Nat) : fastLandXor a b acc = (a &&& b) ^^^ acc := by
  unfold fastLandXor
  cases h : (Nat.beq a 0 || Nat.beq b 0)
  · dsimp only [cond]; exact fastXor_eq (a &&& b) acc
  · dsimp only [cond]
    simp only [Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | rfl
    · rw [Nat.zero_and, Nat.zero_xor]
    · rw [Nat.and_zero, Nat.zero_xor]

def evalQuad512Opt (tr : WTree) (t : Nat) : List (Nat × Nat) → Option Nat
  | [] => some 0
  | (a, b) :: rest =>
      cond (Nat.blt a 100 && Nat.blt b 100 &&
            (!Nat.beq a b) && (!Nat.beq a t) && (!Nat.beq b t))
        (match evalQuad512Opt tr t rest with
         | some acc => someNat (fastLandXor (sGet tr a) (sGet tr b) acc)
         | none => none)
        none

abbrev evalQuad512 := evalQuad512Opt

def evalLin512Opt (tr : WTree) (t : Nat) : List Nat → Option Nat
  | [] => some 0
  | c :: rest =>
      cond (Nat.blt c 100 && (!Nat.beq c t))
        (match evalLin512Opt tr t rest with
         | some acc => someNat (fastXor (sGet tr c) acc)
         | none => none)
        none

abbrev evalLin512 := evalLin512Opt

def stepBitPar512 (tr : WTree) : Op102 → Option WTree
  | .x q =>
      cond (Nat.blt q 100)
        (someWTree (sSet tr q (sGet tr q ^^^ allM512))) none
  | .cx c t =>
      cond (Nat.blt c 100 && Nat.blt t 100 && !Nat.beq c t)
        (someWTree (sSet tr t (sGet tr t ^^^ sGet tr c))) none
  | .and4t c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
            Nat.beq (sGet tr t) 0)
        (someWTree (sSet tr t (sGet tr c1 &&& sGet tr c2))) none
  | .rccx0 _ _ _ => none
  | .rccx1 _ _ _ => none
  | .unand c1 c2 t =>
      cond (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
            !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
            Nat.beq (sGet tr t) (sGet tr c1 &&& sGet tr c2))
        (someWTree (sSet tr t 0)) none
  | .unquad qs ls t =>
      cond (Nat.blt t 100)
        (match evalQuad512Opt tr t qs, evalLin512Opt tr t ls with
         | some vq, some vl =>
             cond (Nat.beq (sGet tr t) (vq ^^^ vl))
               (someWTree (sSet tr t 0)) none
         | _, _ => none)
        none
  | .z _ => none
  | .cz _ _ => none
  | .hGadget _ _ _ _ _ => none

theorem evalQuad512_sound {bit : Nat} {m : Fin 100 → Bool}
    {tr : WTree} (hI : BitPar512Inv bit tr m) (t : Nat) :
    ∀ (qs : List (Nat × Nat)) {vq : Nat},
      evalQuad512Opt tr t qs = some vq →
      (∀ p ∈ qs, p.1 < 100 ∧ p.2 < 100 ∧ p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧
      vq.testBit bit = evalQuadBool102 m qs
  | [], vq, h => by
    injection h with hvq; subst hvq
    exact ⟨fun _ hp => (by cases hp), Nat.zero_testBit bit⟩
  | (a, b) :: rest, vq, h => by
    dsimp only [evalQuad512Opt] at h
    cases hc : (Nat.blt a 100 && Nat.blt b 100 &&
                (!Nat.beq a b) && (!Nat.beq a t) && (!Nat.beq b t))
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    cases hrest : evalQuad512Opt tr t rest with
    | none => rw [hrest] at h; cases h
    | some acc =>
      rw [hrest] at h; dsimp only at h
      rw [someNat_eq, fastLandXor_eq] at h
      injection h with hvq; subst hvq
      obtain ⟨hrest_v, hrest_ev⟩ := evalQuad512_sound hI t rest hrest
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
      obtain ⟨⟨⟨⟨ha_hi, hb_hi⟩, hab⟩, hat⟩, hbt⟩ := hc
      have hprod : (sGet tr a &&& sGet tr b).testBit bit = (m ⟨a, ha_hi⟩ && m ⟨b, hb_hi⟩) := by
        rw [Nat.testBit_and, ← hI.hWire ⟨a, ha_hi⟩, ← hI.hWire ⟨b, hb_hi⟩]
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hmem
        · exact ⟨ha_hi, hb_hi, hab, hat, hbt⟩
        · exact hrest_v p hmem
      · dsimp only [evalQuadBool102]
        rw [dite_eq_left ⟨ha_hi, hb_hi⟩, Nat.testBit_xor, hprod, hrest_ev]

theorem evalLin512_sound {bit : Nat} {m : Fin 100 → Bool}
    {tr : WTree} (hI : BitPar512Inv bit tr m) (t : Nat) :
    ∀ (ls : List Nat) {vl : Nat},
      evalLin512Opt tr t ls = some vl →
      (∀ c ∈ ls, c < 100 ∧ c ≠ t) ∧
      vl.testBit bit = evalLinBool102 m ls
  | [], vl, h => by
    injection h with hvl; subst hvl
    exact ⟨fun _ hc => (by cases hc), Nat.zero_testBit bit⟩
  | c :: rest, vl, h => by
    dsimp only [evalLin512Opt] at h
    cases hc : (Nat.blt c 100 && (!Nat.beq c t))
    · rw [hc, Bool.cond_false] at h; cases h
    rw [hc, Bool.cond_true] at h
    cases hrest : evalLin512Opt tr t rest with
    | none => rw [hrest] at h; cases h
    | some acc =>
      rw [hrest] at h; dsimp only at h
      rw [someNat_eq, fastXor_eq] at h
      injection h with hvl; subst hvl
      obtain ⟨hrest_v, hrest_ev⟩ := evalLin512_sound hI t rest hrest
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
      obtain ⟨hc_hi, hct⟩ := hc
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨hc_hi, hct⟩
        · exact hrest_v x hmem
      · dsimp only [evalLinBool102]
        rw [dite_eq_left hc_hi, Nat.testBit_xor, ← hI.hWire ⟨c, hc_hi⟩, hrest_ev]

theorem stepBitPar512_sound {bit : Nat} {tr tr' : WTree} {m : Fin 100 → Bool}
    (hI : BitPar512Inv bit tr m) {op : Op102}
    (hok : stepBitPar512 tr op = some tr') :
    ∃ m', execOp102 m op = some m' ∧ BitPar512Inv bit tr' m' := by
  cases op with
  | x q =>
    dsimp only [stepBitPar512] at hok
    cases hc : Nat.blt q 100
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    have hq : q < 100 := Nat.blt_eq.mp hc
    have hval : (sGet tr q ^^^ allM512).testBit bit = !m ⟨q, hq⟩ := by
      rw [Nat.testBit_xor, allM512_testBit hI.hbit, ← hI.hWire ⟨q, hq⟩, xor_true_eq_not]
    exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hq], hI.update hq _ _ hval⟩
  | cx c t =>
    dsimp only [stepBitPar512] at hok
    cases hc : (Nat.blt c 100 && Nat.blt t 100 && !Nat.beq c t)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff] at hc
    obtain ⟨⟨hclt, htlt⟩, hct⟩ := hc
    have hval : (sGet tr t ^^^ sGet tr c).testBit bit = xor (m ⟨t, htlt⟩) (m ⟨c, hclt⟩) := by
      rw [Nat.testBit_xor, ← hI.hWire ⟨t, htlt⟩, ← hI.hWire ⟨c, hclt⟩]
    exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left ⟨hclt, htlt, hct⟩],
      hI.update htlt _ _ hval⟩
  | and4t c1 c2 t =>
    dsimp only [stepBitPar512] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
                Nat.beq (sGet tr t) 0)
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hc1, hc2⟩, ht⟩, h12⟩, h1t⟩, h2t⟩, hvt0⟩ := hc
    have hmt0 : m ⟨t, ht⟩ = false := by rw [hI.hWire ⟨t, ht⟩, hvt0, Nat.zero_testBit]
    have hval : (sGet tr c1 &&& sGet tr c2).testBit bit = (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) := by
      rw [Nat.testBit_and, ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩]
    exact ⟨_, (by
        dsimp only [execOp102]
        rw [dite_eq_left ⟨hc1, hc2, ht, h12, h1t, h2t⟩, ite_eq_left hmt0]),
      hI.update ht _ _ hval⟩
  | rccx0 _ _ _ => cases hok
  | rccx1 _ _ _ => cases hok
  | unand c1 c2 t =>
    dsimp only [stepBitPar512] at hok
    cases hc : (Nat.blt c1 100 && Nat.blt c2 100 && Nat.blt t 100 &&
                !Nat.beq c1 c2 && !Nat.beq c1 t && !Nat.beq c2 t &&
                Nat.beq (sGet tr t) (sGet tr c1 &&& sGet tr c2))
    · rw [hc, Bool.cond_false] at hok; cases hok
    rw [hc, Bool.cond_true, someWTree_eq] at hok
    injection hok with htr'; subst htr'
    simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_false_iff, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hc1, hc2⟩, ht⟩, h12⟩, h1t⟩, h2t⟩, hvteq⟩ := hc
    have hmt : m ⟨t, ht⟩ = (m ⟨c1, hc1⟩ && m ⟨c2, hc2⟩) := by
      rw [hI.hWire ⟨t, ht⟩, hvteq, Nat.testBit_and, ← hI.hWire ⟨c1, hc1⟩, ← hI.hWire ⟨c2, hc2⟩]
    exact ⟨_, (by
        dsimp only [execOp102]
        rw [dite_eq_left ⟨hc1, hc2, ht, h12, h1t, h2t⟩, ite_eq_left hmt]),
      hI.update ht 0 false (Nat.zero_testBit bit)⟩
  | unquad qs ls t =>
    dsimp only [stepBitPar512] at hok
    cases htb : Nat.blt t 100
    · rw [htb, Bool.cond_false] at hok; cases hok
    rw [htb, Bool.cond_true] at hok
    cases hq : evalQuad512Opt tr t qs with
    | none => rw [hq] at hok; cases hok
    | some vq =>
      rw [hq] at hok
      cases hl : evalLin512Opt tr t ls with
      | none => rw [hl] at hok; cases hok
      | some vl =>
        rw [hl] at hok; dsimp only at hok
        cases heq : Nat.beq (sGet tr t) (vq ^^^ vl)
        · rw [heq, Bool.cond_false] at hok; cases hok
        rw [heq, Bool.cond_true, someWTree_eq] at hok
        injection hok with htr'; subst htr'
        have ht : t < 100 := Nat.blt_eq.mp htb
        have hvt : sGet tr t = vq ^^^ vl := Nat.beq_eq.mp heq
        obtain ⟨hq_v, hq_ev⟩ := evalQuad512_sound hI t qs hq
        obtain ⟨hl_v, hl_ev⟩ := evalLin512_sound hI t ls hl
        have hval : validUnquad102 qs ls t := ⟨hq_v, hl_v, ht⟩
        have hmt : m ⟨t, ht⟩ = evalUnquad102 m qs ls := by
          rw [hI.hWire ⟨t, ht⟩, hvt, Nat.testBit_xor, hq_ev, hl_ev]; rfl
        exact ⟨_, by dsimp only [execOp102]; rw [dite_eq_left hval, ite_eq_left hmt],
          hI.update ht 0 false (Nat.zero_testBit bit)⟩
  | z _ => cases hok
  | cz _ => cases hok
  | hGadget _ _ _ _ _ => cases hok

def runBitPar512 : List Op102 → WTree → Option WTree
  | [], tr => some tr
  | op :: ops, tr =>
      match stepBitPar512 tr op with
      | some tr1 => runBitPar512 ops tr1
      | none => none

theorem runBitPar512_sound {bit : Nat} :
    ∀ (ops : List Op102) {tr trf : WTree} {m0 : Fin 100 → Bool},
      BitPar512Inv bit tr m0 →
      runBitPar512 ops tr = some trf →
      ∃ mf, execList102 ops m0 = some mf ∧ BitPar512Inv bit trf mf
  | [], _, _, m0, hI, h => by
    injection h with h'; subst h'
    exact ⟨m0, rfl, hI⟩
  | op :: ops, tr, trf, m0, hI, h => by
    dsimp only [runBitPar512] at h
    cases h1 : stepBitPar512 tr op with
    | none => rw [h1] at h; cases h
    | some tr1 =>
      rw [h1] at h
      obtain ⟨m1, hex1, hI1⟩ := stepBitPar512_sound hI h1
      obtain ⟨mf, hexf, hIf⟩ := runBitPar512_sound ops hI1 h
      exact ⟨mf, by dsimp only [execList102]; rw [hex1]; exact hexf, hIf⟩


def rangeList (sout : Nat) : Nat → List Nat
  | 0 => []
  | M + 1 => sout :: rangeList (sout + 1) M

end QuantumComputation.Specs.ArcsinImpl
