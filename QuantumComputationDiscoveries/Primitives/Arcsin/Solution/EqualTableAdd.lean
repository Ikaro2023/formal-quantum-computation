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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.StepSemantics

@[expose] public section

namespace QuantumComputation.Specs

namespace ArcsinImpl

open Operator Matrix QProg Function Step
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

namespace Step


def Avoids : Step n → Wire n → Prop
  | x q, w => q ≠ w
  | cnot c t, w => c ≠ w ∧ t ≠ w
  | and4t c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | rccx0 c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | rccx1 c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | unand c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | unxorList sources t, w => (∀ c ∈ sources, c ≠ w) ∧ t ≠ w
  | unquad quads lins t, w =>
      (∀ p ∈ quads, p.1 ≠ w ∧ p.2 ≠ w) ∧ (∀ c ∈ lins, c ≠ w) ∧ t ≠ w

theorem avoids_inv {s : Step n} {w : Wire n} (h : s.Avoids w) : s.inv.Avoids w := by
  cases s <;> exact h

theorem run_writeReg_of_avoids {k : ℕ} (s : Step n) (r : QRegister k n)
    (h : ∀ i, s.Avoids (r i)) (β : BitAssignment n) (γ : BitAssignment k) :
    s.run (writeReg β r γ) = (s.run β).map (writeReg · r γ) := by
  have hn : ∀ w, (∀ i, w ≠ r i) → w ∉ Set.range r.wires := fun w hw ⟨i, hi⟩ ↦ hw i hi.symm
  cases s with
  | x q =>
    have hq := hn q (fun i ↦ h i)
    simp only [run, Option.map_some, writeReg_apply_of_not_mem _ _ _ _ hq,
      writeReg_update_of_not_mem _ _ _ hq]
  | cnot c t =>
    have hc := hn c (fun i ↦ (h i).1)
    have ht := hn t (fun i ↦ (h i).2)
    simp only [run]
    split_ifs <;> simp only [Option.map_some, writeReg_apply_of_not_mem _ _ _ _ hc,
      writeReg_apply_of_not_mem _ _ _ _ ht, writeReg_update_of_not_mem _ _ _ ht]
  | and4t c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | rccx0 c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | rccx1 c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | unand c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | unxorList sources t =>
    have ht := hn t (fun i ↦ (h i).2)
    have hmap : sources.map (writeReg β r γ) = sources.map β :=
      List.map_congr_left fun c hc ↦
        writeReg_apply_of_not_mem _ _ _ _ (hn c (fun i ↦ (h i).1 c hc))
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ ht, hmap]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | unquad quads lins t =>
    have ht := hn t (fun i ↦ (h i).2.2)
    have hqmap : quads.map (fun p ↦ (writeReg β r γ) p.1 * (writeReg β r γ) p.2) =
        quads.map (fun p ↦ β p.1 * β p.2) :=
      List.map_congr_left fun p hp ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _ (hn p.1 (fun i ↦ ((h i).1 p hp).1)),
            writeReg_apply_of_not_mem _ _ _ _ (hn p.2 (fun i ↦ ((h i).1 p hp).2))]
    have hlmap : lins.map (writeReg β r γ) = lins.map β :=
      List.map_congr_left fun c hc ↦
        writeReg_apply_of_not_mem _ _ _ _ (hn c (fun i ↦ (h i).2.1 c hc))
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ ht, hqmap, hlmap]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]

theorem run_inv {s : Step n} (hno : s.NoUnxor) {β γ : BitAssignment n} (hs : s.run β = some γ) :
    s.inv.run γ = some β := by
  have hb : ∀ a b : ZMod 2, a + b + b = a := fun a b ↦ by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  cases s with
  | x q =>
    simp only [run, inv, Option.some.injEq] at hs ⊢
    rw [← hs, update_self, update_idem, hb, update_eq_self]
  | cnot c t =>
    simp only [run, inv] at hs ⊢
    split_ifs at hs with hct <;> simp only [Option.some.injEq] at hs <;> rw [← hs]
    · rw [ite_eq_left hct, update_self, update_of_ne hct, update_idem, hb, update_eq_self]
    · rw [ite_eq_right hct]
  | and4t c₁ c₂ t =>
    simp only [run, inv] at hs ⊢
    split_ifs at hs with hct ht0 <;> simp only [Option.some.injEq] at hs <;> rw [← hs]
    · rw [ite_eq_left hct, update_self, update_of_ne hct.2.1, update_of_ne hct.2.2, ite_eq_left rfl,
        Option.some.injEq, update_idem, ← ht0, update_eq_self]
    · rw [ite_eq_right hct]
  | unand c₁ c₂ t =>
    simp only [run, inv] at hs ⊢
    split_ifs at hs with hct ht <;> simp only [Option.some.injEq] at hs <;> rw [← hs]
    · rw [ite_eq_left hct, update_self, ite_eq_left rfl, update_of_ne hct.2.1, update_of_ne hct.2.2,
        Option.some.injEq, update_idem, ← ht, update_eq_self]
    · rw [ite_eq_right hct]
  | rccx0 _ _ _ => exact hno.elim
  | rccx1 _ _ _ => exact hno.elim
  | unxorList _ _ => exact hno.elim
  | unquad _ _ _ => exact hno.elim
end Step

theorem runList_writeReg_of_avoids {k : ℕ} (ss : List (Step n)) (r : QRegister k n)
    (h : ∀ s ∈ ss, ∀ i, s.Avoids (r i)) (β : BitAssignment n) (γ : BitAssignment k) :
    runList ss (writeReg β r γ) = (runList ss β).map (writeReg · r γ) := by
  induction ss generalizing β with
  | nil => rfl
  | cons s ss ih =>
    rw [runList_cons, runList_cons, Step.run_writeReg_of_avoids s r (h s List.mem_cons_self)]
    rcases s.run β with _ | δ
    · rfl
    · exact ih (fun s hs ↦ h s (List.mem_cons_of_mem _ hs)) δ

theorem runList_inv {ss : List (Step n)} (hno : ∀ s ∈ ss, s.NoUnxor) {β γ : BitAssignment n}
    (hs : runList ss β = some γ) :
    runList (ss.reverse.map Step.inv) γ = some β := by
  induction ss generalizing β with
  | nil => exact (Option.some.inj hs).symm ▸ rfl
  | cons s ss ih =>
    rw [runList_cons, Option.bind_eq_some_iff] at hs
    obtain ⟨δ, hδ, hγ⟩ := hs
    rw [List.reverse_cons, List.map_append, List.map_singleton, runList_append,
      ih (fun s hs ↦ hno s (List.mem_cons_of_mem _ hs)) hγ,
      Option.bind_some, runList_cons, Step.run_inv (hno s List.mem_cons_self) hδ,
      Option.bind_some, runList_nil]

open Step

variable {n : ℕ}

theorem add_add_self_zmod2 (x y : ZMod 2) : x + y + y = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := rfl

theorem maj_val (a b c : ZMod 2) : ((a + c) * (b + c) + c).val = (a.val + b.val + c.val) / 2 := by
  revert a b c
  decide

theorem bit_zero_mod_two_pow (x K : ℕ) :
    ((x % 2 ^ (K + 1) / 2 ^ ((0 : Fin (K + 1)) : ℕ) % 2 : ℕ) : ZMod 2) = x := by
  rw [Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 K.succ_ne_zero),
    ZMod.natCast_mod]

theorem bit_succ_mod_two_pow (x K : ℕ) (i : Fin (K + 1)) :
    x % 2 ^ (K + 2) / 2 ^ (i.succ : ℕ) % 2 = x / 2 % 2 ^ (K + 1) / 2 ^ (i : ℕ) % 2 := by
  rw [Fin.val_succ, pow_succ' 2 (i : ℕ), ← Nat.div_div_eq_div_mul, pow_succ' 2 (K + 1),
    Nat.mod_mul_right_div_self]

/-- Ripple-carry core on `k + 1` bits using 4-`T` `and4t` + 0-`T` `unand`. -/
def rippleSteps : (k : ℕ) → QRegister (k + 1) n → QRegister (k + 1) n → Wire n →
    QRegister k n → List (Step n)
  | 0, rA, rB, ci, _ => [cnot (rA 0) (rB 0), cnot ci (rB 0)]
  | k + 1, rA, rB, ci, rC =>
      [cnot ci (rA 0), cnot ci (rB 0), and4t (rA 0) (rB 0) (rC 0), cnot ci (rC 0)] ++
        rippleSteps k (regTail rA) (regTail rB) (rC 0) (regTail rC) ++
        [cnot ci (rC 0), unand (rA 0) (rB 0) (rC 0), cnot ci (rA 0), cnot (rA 0) (rB 0)]

theorem runList_rippleSteps (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rC)
    (hBC : rB.DisjointWires rC) (hA : ci ∉ Set.range rA.wires) (hB : ci ∉ Set.range rB.wires)
    (hC : ci ∉ Set.range rC.wires) (β : BitAssignment n) (hclean : ∀ i, β (rC i) = 0) :
    runList (rippleSteps k rA rB ci rC) β = some (writeReg β rB (basisBits (k + 1)
      ⟨((localIdx rA β : ℕ) + (localIdx rB β : ℕ) + (β ci).val) % 2 ^ (k + 1),
        Nat.mod_lt _ (by positivity)⟩)) := by
  induction k generalizing ci β with
  | zero =>
    have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
    have hib : ci ≠ rB 0 := fun h ↦ hB ⟨0, h.symm⟩
    simp only [rippleSteps, runList_cons, Step.run, ite_eq_left hab, ite_eq_left hib,
      Option.bind_some, runList_nil, update_self, update_idem, update_of_ne hib]
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Fin.fin_one_eq_zero i) hi),
      basisBits_mk_apply, bit_zero_mod_two_pow, localIdx_val_succ, localIdx_val_succ,
      Option.some.injEq]
    congr 1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val,
      two_eq_zero_zmod2, zero_mul, add_zero]
    ring
  | succ k ih =>
    have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
    have hac : rA 0 ≠ rC 0 := hAC.ne 0 0
    have hbc : rB 0 ≠ rC 0 := hBC.ne 0 0
    have hia : ci ≠ rA 0 := fun h ↦ hA ⟨0, h.symm⟩
    have hib : ci ≠ rB 0 := fun h ↦ hB ⟨0, h.symm⟩
    have hic : ci ≠ rC 0 := fun h ↦ hC ⟨0, h.symm⟩
    have hcA : rC 0 ∉ Set.range rA.wires := fun ⟨i, h⟩ ↦ hAC.ne i 0 h
    have hcB : rC 0 ∉ Set.range rB.wires := fun ⟨i, h⟩ ↦ hBC.ne i 0 h
    have hbA : rB 0 ∉ Set.range rA.wires := fun ⟨i, h⟩ ↦ hAB.ne i 0 h
    have haB' : rA 0 ∉ Set.range (regTail rB).wires := not_mem_regTail (not_mem_of_disjoint hAB 0)
    have hbB' : rB 0 ∉ Set.range (regTail rB).wires := zero_not_mem_regTail rB
    have hcB' : rC 0 ∉ Set.range (regTail rB).wires := not_mem_regTail hcB
    have hiB' : ci ∉ Set.range (regTail rB).wires := not_mem_regTail hB
    obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = update (update (update β (rA 0) (β (rA 0) + β ci)) (rB 0)
        (β (rB 0) + β ci)) (rC 0) ((β (rA 0) + β ci) * (β (rB 0) + β ci) + β ci) := ⟨_, rfl⟩
    have hβ1o : ∀ w, w ≠ rA 0 → w ≠ rB 0 → w ≠ rC 0 → β1 w = β w := fun w h₁ h₂ h₃ ↦ by
      rw [hβ1, update_of_ne h₃, update_of_ne h₂, update_of_ne h₁]
    have hβ1i : β1 ci = β ci := hβ1o ci hia hib hic
    have hfwd : runList [cnot ci (rA 0), cnot ci (rB 0), and4t (rA 0) (rB 0) (rC 0),
        cnot ci (rC 0)] β = some β1 := by
      rw [hβ1]
      simp [Step.run, hab, hac, hbc, hia, hib, hic, hab.symm, hac.symm, hbc.symm, hclean 0]
    have hcl1 : ∀ i, β1 (regTail rC i) = 0 := fun i ↦ by
      rw [hβ1o _ (fun h ↦ hAC.ne 0 i.succ (h.symm.trans (regTail_apply rC i)))
        (fun h ↦ hBC.ne 0 i.succ (h.symm.trans (regTail_apply rC i))) (regTail_ne_zero rC i),
        regTail_apply]
      exact hclean i.succ
    have hidx : ∀ r : QRegister (k + 1) n, rA 0 ∉ Set.range r.wires → rB 0 ∉ Set.range r.wires →
        rC 0 ∉ Set.range r.wires → localIdx r β1 = localIdx r β := fun r h₁ h₂ h₃ ↦ by
      rw [hβ1, localIdx_update_of_not_mem _ _ h₃, localIdx_update_of_not_mem _ _ h₂,
        localIdx_update_of_not_mem _ _ h₁]
    have hcore := ih (regTail rA) (regTail rB) (rC 0) (regTail rC)
      ((hAB.compose_left _).compose_right _) ((hAC.compose_left _).compose_right _)
      ((hBC.compose_left _).compose_right _) (not_mem_regTail hcA) hcB'
      (zero_not_mem_regTail rC) β1 hcl1
    rw [hidx _ (zero_not_mem_regTail rA) (not_mem_regTail hbA) (not_mem_regTail hcA),
      hidx _ haB' hbB' hcB'] at hcore
    have hβ1a : β1 (rA 0) = β (rA 0) + β ci := by
      rw [hβ1, update_of_ne hac, update_of_ne hab, update_self]
    have hβ1b : β1 (rB 0) = β (rB 0) + β ci := by rw [hβ1, update_of_ne hbc, update_self]
    have hβ1c : β1 (rC 0) = (β (rA 0) + β ci) * (β (rB 0) + β ci) + β ci := by
      rw [hβ1, update_self]
    have hcond : β1 (rC 0) + β ci = β1 (rA 0) * β1 (rB 0) := by
      rw [hβ1a, hβ1b, hβ1c, add_add_self_zmod2]
    have hT : ((localIdx rA β : ℕ) + (localIdx rB β : ℕ) + (β ci).val) / 2 =
        (localIdx (regTail rA) β : ℕ) + (localIdx (regTail rB) β : ℕ) + (β1 (rC 0)).val := by
      rw [localIdx_val_succ rA β, localIdx_val_succ rB β, hβ1c, maj_val]
      omega
    rw [rippleSteps, runList_append, runList_append, hfwd, Option.bind_some, hcore,
      Option.bind_some]
    simp only [runList_cons, runList_nil, Step.run, ite_eq_left hic, ite_eq_left hia,
      ite_eq_left hab,
      ite_eq_left (show rA 0 ≠ rB 0 ∧ rA 0 ≠ rC 0 ∧ rB 0 ≠ rC 0 from ⟨hab, hac, hbc⟩),
      update_self, update_of_ne hic, update_of_ne hac, update_of_ne hbc,
      writeReg_apply_of_not_mem _ _ _ _ hcB', writeReg_apply_of_not_mem _ _ _ _ hiB',
      writeReg_apply_of_not_mem _ _ _ _ haB', writeReg_apply_of_not_mem _ _ _ _ hbB', hβ1i,
      ite_eq_left hcond, Option.bind_some, Option.some.injEq]
    rw [writeReg_succ β rB]
    funext w
    by_cases hw0 : w = rB 0
    · subst hw0
      rw [update_self, update_self, update_of_ne hab.symm, update_of_ne hbc, update_of_ne hbc,
        writeReg_apply_of_not_mem _ _ _ _ hbB', basisBits_mk_apply, bit_zero_mod_two_pow,
        localIdx_val_succ rA β, localIdx_val_succ rB β, hβ1a, hβ1b]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val,
        two_eq_zero_zmod2, zero_mul, add_zero, add_add_self_zmod2]
      ring
    · rw [update_of_ne hw0, update_of_ne hw0]
      by_cases hwa : w = rA 0
      · subst hwa
        rw [update_self, hβ1a, add_add_self_zmod2, writeReg_apply_of_not_mem _ _ _ _ haB']
      · rw [update_of_ne hwa]
        by_cases hwc : w = rC 0
        · subst hwc
          rw [update_self, writeReg_apply_of_not_mem _ _ _ _ hcB', hclean 0]
        · rw [update_of_ne hwc, update_of_ne hwc]
          by_cases hwB : w ∈ Set.range (regTail rB).wires
          · obtain ⟨i, rfl⟩ := hwB
            rw [writeReg_apply_reg, writeReg_apply_reg, basisBits_mk_apply, basisBits_mk_apply,
              bit_succ_mod_two_pow, hT]
          · rw [writeReg_apply_of_not_mem _ _ _ _ hwB, writeReg_apply_of_not_mem _ _ _ _ hwB,
              hβ1o w hwa hw0 hwc]

variable {n : ℕ}

/-- Value of an optional control wire, `1` when there is no control. -/
def ctrlVal : Option (Wire n) → BitAssignment n → ZMod 2
  | none, _ => 1
  | some c, β => β c

/-- Flip of the wire `t`, controlled by the optional control wire. -/
def ctrlFlip : Option (Wire n) → Wire n → Step n
  | none, t => x t
  | some c, t => cnot c t

/-- The optional control wire `c` is not the wire `w`. -/
def CtrlNe (c : Option (Wire n)) (w : Wire n) : Prop := ∀ c₀, c = some c₀ → c₀ ≠ w

theorem ctrlVal_update {c : Option (Wire n)} {w : Wire n} (h : CtrlNe c w) (β : BitAssignment n)
    (a : ZMod 2) : ctrlVal c (update β w a) = ctrlVal c β := by
  cases c with
  | none => rfl
  | some c₀ => exact update_of_ne (h c₀ rfl) _ _

theorem ctrlVal_writeReg {k : ℕ} {c : Option (Wire n)} {r : QRegister k n}
    (h : ∀ i, CtrlNe c (r i)) (β : BitAssignment n) (γ : BitAssignment k) :
    ctrlVal c (writeReg β r γ) = ctrlVal c β := by
  cases c with
  | none => rfl
  | some c₀ => exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ h i c₀ rfl hi.symm

theorem run_ctrlFlip {c : Option (Wire n)} {t : Wire n} (h : CtrlNe c t) (β : BitAssignment n) :
    (ctrlFlip c t).run β = some (update β t (β t + ctrlVal c β)) := by
  cases c with
  | none => rfl
  | some c₀ => exact ite_eq_left (h c₀ rfl)

/-- XOR of the constant `d` into the register `rY`, controlled by `c`. -/
def xorSteps (c : Option (Wire n)) : (w : ℕ) → QRegister w n → BitAssignment w → List (Step n)
  | 0, _, _ => []
  | w + 1, rY, d => (if d 0 = 1 then [ctrlFlip c (rY 0)] else []) ++
      xorSteps c w (regTail rY) (fun i ↦ d i.succ)

theorem runList_xorSteps (c : Option (Wire n)) (w : ℕ) (rY : QRegister w n)
    (d : BitAssignment w) (hc : ∀ i, CtrlNe c (rY i)) (β : BitAssignment n) :
    runList (xorSteps c w rY d) β =
      some (writeReg β rY (fun i ↦ β (rY i) + ctrlVal c β * d i)) := by
  induction w generalizing β with
  | zero =>
    rw [xorSteps, runList_nil, show (fun i : Fin 0 ↦ β (rY i) + ctrlVal c β * d i) =
      fun i ↦ β (rY i) from funext fun i ↦ i.elim0, writeReg_self]
  | succ w ih =>
    have hhead : runList (if d 0 = 1 then [ctrlFlip c (rY 0)] else []) β =
        some (update β (rY 0) (β (rY 0) + ctrlVal c β * d 0)) := by
      split_ifs with hd
      · rw [runList_cons, run_ctrlFlip (hc 0), Option.bind_some, runList_nil, hd, mul_one]
      · rw [(bit_cases (d 0)).resolve_right hd, mul_zero, add_zero, update_eq_self, runList_nil]
    rw [xorSteps, runList_append, hhead, Option.bind_some,
      ih (regTail rY) (fun i ↦ d i.succ) (fun i ↦ by rw [regTail_apply]; exact hc i.succ),
      ctrlVal_update (hc 0), writeReg_succ β rY,
      writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail rY)]
    congr 3
    funext i
    rw [update_of_ne (regTail_ne_zero rY i), regTail_apply]

/-- Steps computing `c ∧ ¬t` into the clean wire `c'` using 4-`T` `and4t`. -/
def andNotSteps : Option (Wire n) → Wire n → Wire n → List (Step n)
  | none, t, c' => [x t, cnot t c', x t]
  | some c, t, c' => [x t, and4t c t c', x t]

/-- Steps uncomputing `c' = c ∧ t` in 0 `T` gates (`unand`). -/
def unAndSteps : Option (Wire n) → Wire n → Wire n → List (Step n)
  | none, t, c' => [cnot t c']
  | some c, t, c' => [unand c t c']

/-- Unary-iteration lookup using `and4t` (`4 T`) and `unand` (`0 T`). -/
def lookupSteps (w : ℕ) (rY : QRegister w n) : (m : ℕ) → Option (Wire n) → QRegister m n →
    QRegister m n → (ℕ → BitAssignment w) → List (Step n)
  | 0, c, _, _, T => xorSteps c w rY (T 0)
  | m + 1, c, rX, rW, T =>
      andNotSteps c (rX 0) (rW 0) ++
      lookupSteps w rY m (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j)) ++
      [ctrlFlip c (rW 0)] ++
      lookupSteps w rY m (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j + 1)) ++
      unAndSteps c (rX 0) (rW 0)

theorem CtrlNe.some {a w : Wire n} (h : a ≠ w) : CtrlNe (some a) w :=
  fun _ h' ↦ Option.some.inj h' ▸ h

theorem runList_andNotSteps (c : Option (Wire n)) (t c' : Wire n) (htc : t ≠ c')
    (hct : CtrlNe c t) (hcc : CtrlNe c c') (β : BitAssignment n) (h0 : β c' = 0) :
    runList (andNotSteps c t c') β = some (update β c' (ctrlVal c β * (β t + 1))) := by
  have hb : β t + 1 + 1 = β t := by rw [add_assoc, one_add_one_zmod2, add_zero]
  cases c with
  | none =>
    simp only [andNotSteps, runList_cons, Step.run, ite_eq_left htc, Option.bind_some, runList_nil,
      update_self, update_of_ne htc.symm, update_of_ne htc, h0, zero_add, ctrlVal, one_mul,
      Option.some.injEq]
    rw [update_comm htc, update_idem, hb, update_comm htc.symm, update_eq_self]
  | some c₀ =>
    have h₁ := hct c₀ rfl
    have h₂ := hcc c₀ rfl
    simp only [andNotSteps, runList_cons, Step.run, ite_eq_left (show c₀ ≠ t ∧ c₀ ≠ c' ∧ t ≠ c' from
      ⟨h₁, h₂, htc⟩), Option.bind_some, runList_nil, update_self, update_of_ne htc.symm,
      update_of_ne htc, update_of_ne h₁, h0, ↓reduceIte, ctrlVal, Option.some.injEq]
    rw [update_comm htc, update_idem, hb, update_comm htc.symm, update_eq_self, mul_comm]

theorem runList_unAndSteps (c : Option (Wire n)) (t c' : Wire n) (htc : t ≠ c')
    (hct : CtrlNe c t) (hcc : CtrlNe c c') (β : BitAssignment n)
    (h : β c' = ctrlVal c β * β t) :
    runList (unAndSteps c t c') β = some (update β c' 0) := by
  cases c with
  | none =>
    simp only [unAndSteps, runList_cons, Step.run, ite_eq_left htc, Option.bind_some,
      runList_nil, h, ctrlVal, one_mul, CharTwo.add_self_eq_zero]
  | some c₀ =>
    simp only [ctrlVal] at h
    simp only [unAndSteps, runList_cons, Step.run, ite_eq_left (show c₀ ≠ t ∧ c₀ ≠ c' ∧ t ≠ c' from
      ⟨hct c₀ rfl, hcc c₀ rfl, htc⟩), ite_eq_left h, Option.bind_some, runList_nil]

theorem runList_lookupSteps (w : ℕ) (rY : QRegister w n) (m : ℕ) (c : Option (Wire n))
    (rX rW : QRegister m n) (T : ℕ → BitAssignment w) (hXW : rX.DisjointWires rW)
    (hXY : rX.DisjointWires rY) (hWY : rW.DisjointWires rY) (hcX : ∀ i, CtrlNe c (rX i))
    (hcW : ∀ i, CtrlNe c (rW i)) (hcY : ∀ i, CtrlNe c (rY i)) (β : BitAssignment n)
    (hclean : ∀ i, β (rW i) = 0) :
    runList (lookupSteps w rY m c rX rW T) β =
      some (writeReg β rY (fun i ↦ β (rY i) + ctrlVal c β * T (localIdx rX β) i)) := by
  induction m generalizing c T β with
  | zero =>
    have h0 : (localIdx rX β : ℕ) = 0 := Nat.lt_one_iff.mp (by simp)
    rw [lookupSteps, runList_xorSteps c w rY _ hcY, h0]
  | succ m ih =>
    have htc : rX 0 ≠ rW 0 := hXW.ne 0 0
    have hcY' : rW 0 ∉ Set.range rY.wires := not_mem_of_disjoint hWY 0
    have htY : rX 0 ∉ Set.range rY.wires := not_mem_of_disjoint hXY 0
    have hcX' : rW 0 ∉ Set.range (regTail rX).wires :=
      fun ⟨i, h⟩ ↦ hXW.ne i.succ 0 (by rw [← regTail_apply]; exact h)
    have hXY' : (regTail rX).DisjointWires rY := hXY.compose_left _
    have hWY' : (regTail rW).DisjointWires rY := hWY.compose_left _
    have hstep : ∀ (F : BitAssignment w) (a : ZMod 2) (T' : ℕ → BitAssignment w),
        runList (lookupSteps w rY m (some (rW 0)) (regTail rX) (regTail rW) T')
          (update (writeReg β rY F) (rW 0) a) =
        some (update (writeReg β rY (fun i ↦ F i + a * T' (localIdx (regTail rX) β) i))
          (rW 0) a) := by
      intro F a T'
      rw [ih (some (rW 0)) (regTail rX) (regTail rW) T' ((hXW.compose_left _).compose_right _)
        hXY' hWY' (fun i ↦ CtrlNe.some fun h ↦ hcX' ⟨i, h.symm⟩)
        (fun i ↦ CtrlNe.some (regTail_ne_zero rW i).symm) (fun i ↦ CtrlNe.some (hWY.ne 0 i)) _
        (fun i ↦ by rw [update_of_ne (regTail_ne_zero rW i), writeReg_apply_of_not_mem _ _ _ _
          (not_mem_of_disjoint hWY' i), regTail_apply, hclean]),
        localIdx_update_of_not_mem _ _ hcX',
        localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.mp hXY'),
        writeReg_update_of_not_mem _ _ _ hcY', writeReg_writeReg]
      simp only [ctrlVal, update_self]
      congr 3
      funext i
      rw [update_of_ne (hWY.ne 0 i).symm, writeReg_apply_reg]
    have hβ : update β (rW 0) (ctrlVal c β * (β (rX 0) + 1)) =
        update (writeReg β rY (fun i ↦ β (rY i))) (rW 0) (ctrlVal c β * (β (rX 0) + 1)) := by
      rw [writeReg_self]
    rw [lookupSteps, runList_append, runList_append, runList_append, runList_append,
      runList_andNotSteps c _ _ htc (hcX 0) (hcW 0) β (hclean 0), Option.bind_some, hβ, hstep,
      Option.bind_some, runList_cons, run_ctrlFlip (hcW 0), Option.bind_some, runList_nil,
      Option.bind_some, update_self, ctrlVal_update (hcW 0), ctrlVal_writeReg hcY, update_idem,
      hstep, Option.bind_some, runList_unAndSteps c _ _ htc (hcX 0) (hcW 0), update_idem,
      update_eq_self_iff.mpr (by rw [writeReg_apply_of_not_mem _ _ _ _ hcY', hclean])]
    · congr 2
      funext i
      rw [localIdx_val_succ rX β]
      rcases bit_cases (β (rX 0)) with hb | hb <;> rw [hb]
      · rw [ZMod.val_zero, zero_add, zero_add, mul_one, CharTwo.add_self_eq_zero, zero_mul,
          add_zero]
      · rw [ZMod.val_one, one_add_one_zmod2, mul_zero, zero_mul, add_zero, zero_add, add_comm 1]
    · rw [update_self, ctrlVal_update (hcW 0), ctrlVal_writeReg hcY, update_of_ne htc,
        writeReg_apply_of_not_mem _ _ _ _ htY, mul_add, mul_one, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]

variable {n : ℕ}

/-- Swap of registers `rA` and `rB`, controlled by wire `c`, using clean wire `w_clean`
(`4 T` per bit). -/
def cswapSteps (c w_clean : Wire n) : (w : ℕ) → QRegister w n → QRegister w n → List (Step n)
  | 0, _, _ => []
  | w + 1, rA, rB =>
      [cnot (rB 0) (rA 0), and4t c (rA 0) w_clean, cnot w_clean (rB 0),
       unand c (rA 0) w_clean, cnot (rB 0) (rA 0)] ++
        cswapSteps c w_clean w (regTail rA) (regTail rB)

theorem cswapSteps_avoids (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n) (v : Wire n)
    (hc : c ≠ v) (hwc : w_clean ≠ v) (hA : v ∉ Set.range rA.wires) (hB : v ∉ Set.range rB.wires) :
    ∀ s ∈ cswapSteps c w_clean w rA rB, s.Avoids v := by
  induction w with
  | zero => simp [cswapSteps]
  | succ w ih =>
    have ha : rA 0 ≠ v := fun h ↦ hA ⟨0, h⟩
    have hb : rB 0 ≠ v := fun h ↦ hB ⟨0, h⟩
    intro s hs
    simp only [cswapSteps, List.cons_append, List.mem_cons, List.nil_append] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | hs
    · exact ⟨hb, ha⟩
    · exact ⟨hc, ha, hwc⟩
    · exact ⟨hwc, hb⟩
    · exact ⟨hc, ha, hwc⟩
    · exact ⟨hb, ha⟩
    · exact ih _ _ (not_mem_regTail hA) (not_mem_regTail hB) s hs

theorem runList_cswapSteps (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n)
    (hAB : rA.DisjointWires rB) (hcA : c ∉ Set.range rA.wires) (hcB : c ∉ Set.range rB.wires)
    (hwc : c ≠ w_clean) (hwA : w_clean ∉ Set.range rA.wires) (hwB : w_clean ∉ Set.range rB.wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (cswapSteps c w_clean w rA rB) β = some β' ∧
      (∀ v, v ∉ Set.range rA.wires → v ∉ Set.range rB.wires → β' v = β v) ∧
      (∀ i, β' (rA i) = β (rA i) + β c * (β (rA i) + β (rB i))) ∧
      (∀ i, β' (rB i) = β (rB i) + β c * (β (rA i) + β (rB i))) := by
  induction w generalizing β with
  | zero => exact ⟨β, rfl, fun _ _ _ ↦ rfl, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ w ih =>
    have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
    have hca : c ≠ rA 0 := fun h ↦ hcA ⟨0, h.symm⟩
    have hcb : c ≠ rB 0 := fun h ↦ hcB ⟨0, h.symm⟩
    have haw : rA 0 ≠ w_clean := fun h ↦ hwA ⟨0, h⟩
    have hbw : rB 0 ≠ w_clean := fun h ↦ hwB ⟨0, h⟩
    obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = update (update β (rA 0) (β (rA 0) + β c *
        (β (rA 0) + β (rB 0)))) (rB 0) (β (rB 0) + β c * (β (rA 0) + β (rB 0))) := ⟨_, rfl⟩
    have h3 : runList [cnot (rB 0) (rA 0), and4t c (rA 0) w_clean, cnot w_clean (rB 0),
        unand c (rA 0) w_clean, cnot (rB 0) (rA 0)] β = some β1 := by
      have hb : ∀ a b x : ZMod 2, a + b + (b + x * (a + b)) = a + x * (a + b) := fun a b x ↦ by
        rw [← add_assoc, add_assoc a b b, CharTwo.add_self_eq_zero, add_zero]
      simp only [runList_cons, Step.run, ite_eq_left hab.symm,
        ite_eq_left (show c ≠ rA 0 ∧ c ≠ w_clean ∧ rA 0 ≠ w_clean from ⟨hca, hwc, haw⟩),
        ite_eq_left hbw.symm, Option.bind_some, runList_nil,
        update_of_ne haw.symm, update_of_ne hbw.symm, hw0, ↓reduceIte,
        update_self, update_of_ne hca, update_of_ne hcb, update_of_ne hwc, update_of_ne hab.symm,
        update_of_ne hab, update_of_ne haw, update_of_ne hbw, hβ1, Option.some.injEq]
      funext v
      by_cases hva : v = rA 0
      · subst hva; simp only [update_self, update_of_ne hab, hb]
      · by_cases hvb : v = rB 0
        · subst hvb; simp only [update_of_ne hab.symm, update_self, update_of_ne hbw]
        · by_cases hvw : v = w_clean
          · subst hvw; simp only [update_of_ne haw.symm, update_of_ne hbw.symm, update_self, hw0]
          · simp only [update_of_ne hva, update_of_ne hvb, update_of_ne hvw]
    have hβ1o : ∀ v, v ≠ rA 0 → v ≠ rB 0 → β1 v = β v := fun v h₁ h₂ ↦ by
      rw [hβ1, update_of_ne h₂, update_of_ne h₁]
    obtain ⟨β2, h2, hfr, h2A, h2B⟩ := ih (regTail rA) (regTail rB)
      ((hAB.compose_left _).compose_right _) (not_mem_regTail hcA) (not_mem_regTail hcB)
      (not_mem_regTail hwA) (not_mem_regTail hwB) β1 (by rw [hβ1o w_clean haw.symm hbw.symm, hw0])
    refine ⟨β2, by rw [cswapSteps, runList_append, h3, Option.bind_some, h2],
      fun v hvA hvB ↦ by
        rw [hfr v (not_mem_regTail hvA) (not_mem_regTail hvB),
          hβ1o v (fun h ↦ hvA ⟨0, h.symm⟩) (fun h ↦ hvB ⟨0, h.symm⟩)],
      fun i ↦ ?_, fun i ↦ ?_⟩
    · cases i using Fin.cases with
      | zero =>
        rw [hfr _ (zero_not_mem_regTail rA) (not_mem_regTail (not_mem_of_disjoint hAB 0)),
          hβ1, update_of_ne hab, update_self]
      | succ j =>
        rw [← regTail_apply, h2A, hβ1o _ (regTail_ne_zero rA j)
          (fun h ↦ hAB.ne j.succ 0 (by rw [← regTail_apply]; exact h)),
          hβ1o _ (fun h ↦ hAB.ne 0 j.succ (by rw [← regTail_apply]; exact h.symm))
          (regTail_ne_zero rB j), hβ1o c hca hcb, regTail_apply, regTail_apply]
    · cases i using Fin.cases with
      | zero =>
        rw [hfr _ (fun ⟨j, h⟩ ↦ hAB.ne j.succ 0 (by rw [← regTail_apply]; exact h))
          (zero_not_mem_regTail rB), hβ1, update_self]
      | succ j =>
        rw [← regTail_apply, h2B, hβ1o _ (regTail_ne_zero rA j)
          (fun h ↦ hAB.ne j.succ 0 (by rw [← regTail_apply]; exact h)),
          hβ1o _ (fun h ↦ hAB.ne 0 j.succ (by rw [← regTail_apply]; exact h.symm))
          (regTail_ne_zero rB j), hβ1o c hca hcb, regTail_apply, regTail_apply]

/-- Swaps of the blocks `B l` and `B (l + off)` for `l < k`, controlled by `c` with clean wire
`w_clean`. -/
def levelSwap (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off : ℕ) : ℕ → List (Step n)
  | 0 => []
  | k + 1 => levelSwap c w_clean w B off k ++ cswapSteps c w_clean w (B k) (B (k + off))

theorem levelSwap_avoids (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ)
    (v : Wire n) (hc : c ≠ v) (hwc : w_clean ≠ v) (hB : ∀ l, v ∉ Set.range (B l).wires) :
    ∀ s ∈ levelSwap c w_clean w B off k, s.Avoids v := by
  induction k with
  | zero => simp [levelSwap]
  | succ k ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s hs
    · exact cswapSteps_avoids _ _ _ _ _ v hc hwc (hB _) (hB _) s hs

theorem runList_levelSwap (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ)
    (hk : k ≤ off)
    (hD : ∀ l l', l < 2 * off → l' < 2 * off → l ≠ l' → (B l).DisjointWires (B l'))
    (hc : ∀ l, c ∉ Set.range (B l).wires) (hwc : c ≠ w_clean)
    (hwB : ∀ l, w_clean ∉ Set.range (B l).wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (levelSwap c w_clean w B off k) β = some β' ∧
      (∀ v, (∀ l < k, v ∉ Set.range (B l).wires ∧ v ∉ Set.range (B (l + off)).wires) → β' v = β v) ∧
      ∀ l < k, ∀ i, β' (B l i) = β (B (l + off * (β c).val) i) := by
  induction k with
  | zero => exact ⟨β, rfl, fun _ _ ↦ rfl, fun l hl ↦ absurd hl (Nat.not_lt_zero l)⟩
  | succ k ih =>
    obtain ⟨β1, h1, hfr1, h1B⟩ := ih (by omega)
    obtain ⟨β2, h2, hfr2, h2A, h2B⟩ := runList_cswapSteps c w_clean w (B k) (B (k + off))
      (hD _ _ (by omega) (by omega) (by omega)) (hc _) (hc _) hwc (hwB _) (hwB _) β1
      (by rw [hfr1 w_clean fun l _ ↦ ⟨hwB l, hwB _⟩, hw0])
    have hc1 : β1 c = β c := hfr1 c fun l _ ↦ ⟨hc l, hc _⟩
    refine ⟨β2, by rw [levelSwap, runList_append, h1, Option.bind_some, h2],
      fun v hv ↦ by
        rw [hfr2 v (hv k (by omega)).1 (hv k (by omega)).2,
          hfr1 v fun l hl ↦ hv l (by omega)],
      fun l hl i ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
    · rw [hfr2 _ (not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i)
        (not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i), h1B l hl i]
    · rw [hl, h2A, hc1, hfr1 _ fun l' hl' ↦
          ⟨not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i,
            not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i⟩,
        hfr1 _ fun l' hl' ↦
          ⟨not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i,
            not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i⟩]
      rcases bit_cases (β c) with h | h <;> rw [h]
      · simp
      · rw [one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add,
          show ZMod.val (1 : ZMod 2) = 1 from rfl, mul_one]

/-- Moves block `B v` to position `0`, where `v` is the value of `rc`, using clean wire
`w_clean`. -/
def swapTree (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) :
    (s : ℕ) → QRegister s n → List (Step n)
  | 0, _ => []
  | s + 1, rc => levelSwap (rc (Fin.last s)) w_clean w B (2 ^ s) (2 ^ s) ++
      swapTree w_clean w B s (rc.slice 0 s (by omega))

theorem cswapSteps_noUnxor (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n) :
    ∀ st ∈ cswapSteps c w_clean w rA rB, st.NoUnxor := by
  induction w with
  | zero => simp [cswapSteps]
  | succ w ih =>
    intro st hst
    simp only [cswapSteps, List.cons_append, List.mem_cons, List.nil_append] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | hst
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact ih _ _ st hst

theorem levelSwap_noUnxor (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ) :
    ∀ st ∈ levelSwap c w_clean w B off k, st.NoUnxor := by
  induction k with
  | zero => simp [levelSwap]
  | succ k ih =>
    intro st hst
    rcases List.mem_append.mp hst with hst | hst
    · exact ih st hst
    · exact cswapSteps_noUnxor _ _ _ _ _ st hst

theorem swapTree_noUnxor (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n) : ∀ st ∈ swapTree w_clean w B s rc, st.NoUnxor := by
  induction s with
  | zero => simp [swapTree]
  | succ s ih =>
    intro st hst
    rcases List.mem_append.mp hst with hst | hst
    · exact levelSwap_noUnxor _ _ _ _ _ _ st hst
    · exact ih _ st hst

theorem swapTree_avoids (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n) (v : Wire n) (hwc : w_clean ≠ v) (hc : v ∉ Set.range rc.wires)
    (hB : ∀ l, v ∉ Set.range (B l).wires) :
    ∀ st ∈ swapTree w_clean w B s rc, st.Avoids v := by
  induction s with
  | zero => simp [swapTree]
  | succ s ih =>
    intro st hst
    rcases List.mem_append.mp hst with hst | hst
    · exact levelSwap_avoids _ _ _ _ _ _ v (fun h ↦ hc ⟨_, h⟩) hwc hB st hst
    · exact ih _ (not_mem_slice hc _ _ _) st hst

theorem runList_swapTree (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n)
    (hD : ∀ l l', l < 2 ^ s → l' < 2 ^ s → l ≠ l' → (B l).DisjointWires (B l'))
    (hc : ∀ j l, rc j ∉ Set.range (B l).wires)
    (hwrc : w_clean ∉ Set.range rc.wires) (hwB : ∀ l, w_clean ∉ Set.range (B l).wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (swapTree w_clean w B s rc) β = some β' ∧
      (∀ v, (∀ l, v ∉ Set.range (B l).wires) → β' v = β v) ∧
      ∀ i, β' (B 0 i) = β (B (localIdx rc β) i) := by
  induction s generalizing β with
  | zero =>
    refine ⟨β, rfl, fun _ _ ↦ rfl, fun i ↦ ?_⟩
    rw [show (localIdx rc β : ℕ) = 0 from Nat.lt_one_iff.mp (by simp)]
  | succ s ih =>
    obtain ⟨β1, h1, hfr1, h1B⟩ := runList_levelSwap (rc (Fin.last s)) w_clean w B (2 ^ s) (2 ^ s)
      le_rfl (fun l l' hl hl' ↦ hD l l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega))
      (hc _) (fun h ↦ hwrc ⟨Fin.last s, h⟩) hwB β hw0
    have hc' : ∀ j l, (rc.slice 0 s (by omega)) j ∉ Set.range (B l).wires := fun j l ↦ by
      rw [QRegister.slice_apply]
      exact hc _ l
    obtain ⟨β2, h2, hfr2, h2B⟩ := ih (rc.slice 0 s (by omega))
      (fun l l' hl hl' ↦ hD l l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)) hc'
      (not_mem_slice hwrc 0 s (by omega)) β1 (by rw [hfr1 w_clean fun l _ ↦ ⟨hwB l, hwB _⟩, hw0])
    have hrc : localIdx (rc.slice 0 s (by omega)) β1 = localIdx (rc.slice 0 s (by omega)) β := by
      simp only [localIdx]
      congr 1
      funext j
      exact hfr1 _ fun l _ ↦ ⟨hc' j l, hc' j _⟩
    have hlast : (localIdx (rc.slice s 1 (by omega)) β : ℕ) = (β (rc (Fin.last s))).val := by
      rw [localIdx_val, Fin.sum_univ_one, QRegister.slice_apply]
      simp only [Fin.val_zero, pow_zero, mul_one, add_zero]
      rfl
    refine ⟨β2, by rw [swapTree, runList_append, h1, Option.bind_some, h2],
      fun v hv ↦ by rw [hfr2 v hv, hfr1 v fun l _ ↦ ⟨hv l, hv _⟩],
      fun i ↦ ?_⟩
    rw [h2B, hrc, h1B _ (localIdx _ β).isLt, localIdx_val_split rc s 1 rfl β, hlast]

variable {n : ℕ}

/-- Little-endian bits of the table entry `f x mod 2^w`. -/
def tableBits (w : ℕ) (f : ℕ → ℕ) (x : ℕ) : BitAssignment w :=
  fun i ↦ ((f x / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2)

theorem tableBits_eq (w : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    tableBits w f x = basisBits w ⟨f x % 2 ^ w, Nat.mod_lt _ (by positivity)⟩ := by
  funext i
  have h : 2 ^ w = 2 ^ (i : ℕ) * 2 ^ (w - i) := by rw [← pow_add, Nat.add_sub_cancel' i.isLt.le]
  rw [basisBits_mk_apply, tableBits, h, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

theorem ctrlNe_none (w : Wire n) : CtrlNe none w := fun _ h ↦ (Option.some_ne_none _ h.symm).elim

/-- The entries `f (l + 2^s h)` for `l < 2^s`, `K + 1` bits each, laid out side by side. -/
def wideTable (s K : ℕ) (f : ℕ → ℕ) (h : ℕ) : BitAssignment (2 ^ s * (K + 1)) :=
  fun p ↦ tableBits (K + 1) f ((p : ℕ) / (K + 1) + 2 ^ s * h) ⟨p % (K + 1), Nat.mod_lt _ K.succ_pos⟩

/-- Block `l mod 2^s` of `w` consecutive wires of `rD`. -/
def dataBlock (s w : ℕ) (rD : QRegister (2 ^ s * w) n) (l : ℕ) : QRegister w n :=
  rD.slice (l % 2 ^ s * w) w (by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.mod_lt _ (by positivity)))

theorem dataBlock_disjoint (s w : ℕ) (rD : QRegister (2 ^ s * w) n) {l l' : ℕ} (hl : l < 2 ^ s)
    (hl' : l' < 2 ^ s) (h : l ≠ l') : (dataBlock s w rD l).DisjointWires (dataBlock s w rD l') := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  rw [dataBlock, dataBlock, QRegister.slice_apply, QRegister.slice_apply] at heq
  have hv := congrArg Fin.val (rD.wires.injective heq)
  simp only [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at hv
  have hw : 0 < w := (Nat.zero_le _).trans_lt i.isLt
  apply h
  have hd := congrArg (· / w) hv
  simp only [add_comm _ (i : ℕ), add_comm _ (j : ℕ), Nat.add_mul_div_right _ _ hw,
    Nat.div_eq_of_lt i.isLt, Nat.div_eq_of_lt j.isLt, zero_add] at hd
  exact hd

theorem writeReg_wideTable_dataBlock (β : BitAssignment n) (s K : ℕ) (f : ℕ → ℕ)
    (rD : QRegister (2 ^ s * (K + 1)) n) (h l : ℕ) (hl : l < 2 ^ s) (i : Fin (K + 1)) :
    writeReg β rD (wideTable s K f h) (dataBlock s (K + 1) rD l i) =
      tableBits (K + 1) f (l + 2 ^ s * h) i := by
  have hd : (l * (K + 1) + i) / (K + 1) = l := by
    rw [add_comm, Nat.add_mul_div_right _ _ K.succ_pos, Nat.div_eq_of_lt i.isLt, zero_add]
  have hm : (l * (K + 1) + i) % (K + 1) = i := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  rw [dataBlock, QRegister.slice_apply, writeReg_apply_reg, wideTable]
  simp only [Nat.mod_eq_of_lt hl, hd, hm]

/-- Sub-Toffoli (`4T/0T`) select-swap lookup and Gidney ripple-carry addition on `2 * k` data wires
(`k` output wires `b` followed by `k` input wires `x`), using `and4t` (`4 T`) + `unand` (`0 T`)
at every lookup, swap, and addition carry step (`0` `.TOFF` gates). -/
def equalTableAddCore (K s : ℕ) (f : ℕ → ℕ) (rD : QRegister (2 ^ s * (K + 1)) n)
    (rXl : QRegister s n) (rXh rW : QRegister (K + 1 - s) n) (rB : QRegister (K + 1) n)
    (ci : Wire n) (rC : QRegister K n) : List (Step n) :=
  lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f) ++
    swapTree ci (K + 1) (dataBlock s (K + 1) rD) s rXl ++
    rippleSteps K (dataBlock s (K + 1) rD 0) rB ci rC ++
    (swapTree ci (K + 1) (dataBlock s (K + 1) rD) s rXl).reverse.map Step.inv ++
    lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f)

theorem runList_equalTableAddCore (K s : ℕ) (f : ℕ → ℕ) (rD : QRegister (2 ^ s * (K + 1)) n)
    (rXl : QRegister s n) (rXh rW : QRegister (K + 1 - s) n) (rB : QRegister (K + 1) n)
    (ci : Wire n) (rC : QRegister K n)
    (hDl : rD.DisjointWires rXl) (hDh : rD.DisjointWires rXh) (hDW : rD.DisjointWires rW)
    (hDB : rD.DisjointWires rB) (hDC : rD.DisjointWires rC) (hlB : rXl.DisjointWires rB)
    (hhW : rXh.DisjointWires rW) (hhB : rXh.DisjointWires rB) (hWB : rW.DisjointWires rB)
    (hCB : rC.DisjointWires rB) (hiD : ci ∉ Set.range rD.wires) (hiXl : ci ∉ Set.range rXl.wires)
    (hiB : ci ∉ Set.range rB.wires) (hiC : ci ∉ Set.range rC.wires) (β : BitAssignment n)
    (hD : ∀ i, β (rD i) = 0) (hW : ∀ i, β (rW i) = 0) (hci : β ci = 0) (hC : ∀ i, β (rC i) = 0) :
    runList (equalTableAddCore K s f rD rXl rXh rW rB ci rC) β =
      some (writeReg β rB (basisBits (K + 1)
        ⟨(f ((localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ)) % 2 ^ (K + 1) +
          (localIdx rB β : ℕ)) % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩)) := by
  set B := dataBlock s (K + 1) rD with hBdef
  set S := swapTree ci (K + 1) B s rXl with hS
  have hnB : ∀ {v}, v ∉ Set.range rD.wires → ∀ l, v ∉ Set.range (B l).wires :=
    fun hv _ ↦ not_mem_slice hv _ _ _
  have hlook := fun β' ↦ runList_lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f) hhW
    (QRegister.disjoint_comm.mp hDh) (QRegister.disjoint_comm.mp hDW)
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β'
  set x := (localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ) with hx
  set β1 := writeReg β rD (wideTable s K f (localIdx rXh β)) with hβ1
  have h1 : runList (lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f)) β = some β1 := by
    rw [hlook β hW]
    simp only [hD, ctrlVal, zero_add, one_mul]
    rfl
  have hb1 : ∀ v, v ∉ Set.range rD.wires → β1 v = β v := fun v hv ↦
    writeReg_apply_of_not_mem _ _ _ _ hv
  obtain ⟨β2, h2, hfr2_B, h2B⟩ := runList_swapTree ci (K + 1) B s rXl
    (fun l l' hl hl' h ↦ dataBlock_disjoint s (K + 1) rD hl hl' h)
    (fun j ↦ hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) j))
    hiXl (hnB hiD) β1 (by rw [hb1 _ hiD, hci])
  have hfr2 : ∀ v, v ∉ Set.range rD.wires → β2 v = β1 v := fun v hv ↦ hfr2_B v (hnB hv)
  have hB0 : localIdx (B 0) β2 = ⟨f x % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩ := by
    have hl := (localIdx rXl β).isLt
    have : (fun i ↦ β2 (B 0 i)) = tableBits (K + 1) f x := funext fun i ↦ by
      rw [h2B, localIdx_writeReg_of_disjoint _ _ _ hDl, hβ1,
        writeReg_wideTable_dataBlock _ _ _ _ _ _ _ hl]
    simp only [localIdx, this, tableBits_eq, basisBitsEquiv_symm_basisBits]
  have hrB : localIdx rB β2 = localIdx rB β := by
    simp only [localIdx]
    congr 1
    funext i
    rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDB) i),
      hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDB) i)]
  set γ := basisBits (K + 1) ⟨(f x % 2 ^ (K + 1) + (localIdx rB β : ℕ)) % 2 ^ (K + 1),
    Nat.mod_lt _ (by positivity)⟩ with hγ
  have h3 : runList (rippleSteps K (B 0) rB ci rC) β2 = some (writeReg β2 rB γ) := by
    rw [runList_rippleSteps K (B 0) rB ci rC (hDB.compose_left _) (hDC.compose_left _)
      (QRegister.disjoint_comm.mp hCB) (hnB hiD 0) hiB hiC β2 (fun i ↦ by
        rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDC) i),
          hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDC) i), hC]),
      hB0, hrB, hfr2 _ hiD, hb1 _ hiD, hci, ZMod.val_zero, add_zero]
  have h4 : runList (S.reverse.map Step.inv) (writeReg β2 rB γ) = some (writeReg β1 rB γ) := by
    rw [runList_writeReg_of_avoids _ rB (fun st hst i ↦ by
        obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hst
        exact Step.avoids_inv (swapTree_avoids ci (K + 1) B s rXl _
          (fun h ↦ hiB ⟨i, h.symm⟩)
          (not_mem_of_disjoint (QRegister.disjoint_comm.mp hlB) i)
          (hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDB) i))
          st' (List.mem_reverse.mp hst'))),
      runList_inv (swapTree_noUnxor ci (K + 1) B s rXl) h2, Option.map_some]
  rw [equalTableAddCore, runList_append, runList_append, runList_append, runList_append, h1,
    Option.bind_some, ← hS, h2, Option.bind_some, h3, Option.bind_some, h4, Option.bind_some,
    hlook _ (fun i ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hWB i),
        hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDW) i), hW])]
  simp only [localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.mp hhB),
    hβ1, localIdx_writeReg_of_disjoint _ _ _ hDh,
    writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDB _), writeReg_apply_reg, ctrlVal,
    one_mul, CharTwo.add_self_eq_zero]
  rw [writeReg_comm _ rB rD (QRegister.disjoint_comm.mp hDB), writeReg_writeReg,
    show (fun _ : Fin (2 ^ s * (K + 1)) ↦ (0 : ZMod 2)) = fun i ↦ β (rD i) from
      funext fun i ↦ (hD i).symm, writeReg_self]

theorem writeReg_eq_of_eqOn {k : ℕ} (β β' : BitAssignment n) (r : QRegister k n)
    (h : ∀ w ∉ Set.range r.wires, β' w = β w) : writeReg β r (fun i ↦ β' (r i)) = β' := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, h w hw]

theorem eq_zero_of_localIdx_eq_zero {k : ℕ} (r : QRegister k n) (β : BitAssignment n)
    (h : localIdx r β = 0) (i : Fin k) : β (r i) = 0 := by
  have hi := congrArg (fun j ↦ basisBits k j i) h
  simp only [localIdx, basisBits_basisBitsEquiv_symm] at hi
  rw [hi, basisBits_eq_div_mod]
  simp

/-- Sub-Toffoli select-swap QROM lookup and Gidney ripple-carry addition on `2 * k` data wires. -/
def equalTableAddSteps (k s : ℕ) (hs : s ≤ k) (f : ℕ → ℕ) :
    QRegister (2 * k) n → QRegister (2 ^ s * k + k) n → List (Step n) :=
  match k with
  | 0 => fun _ _ => []
  | K + 1 => fun rData rAnc =>
      equalTableAddCore K s f (rAnc.slice 0 (2 ^ s * (K + 1)) (by omega))
        (rData.slice (K + 1) s (by omega)) (rData.slice (K + 1 + s) (K + 1 - s) (by omega))
        (rAnc.slice (2 ^ s * (K + 1)) (K + 1 - s) (by omega)) (rData.slice 0 (K + 1) (by omega))
        (rAnc ⟨2 ^ s * (K + 1), by omega⟩)
        (rAnc.slice (2 ^ s * (K + 1) + 1) K (by omega))

theorem runList_equalTableAddSteps (k s : ℕ) (hs : s ≤ k) (f : ℕ → ℕ)
    (rData : QRegister (2 * k) n) (rAnc : QRegister (2 ^ s * k + k) n)
    (hdisj : rData.DisjointWires rAnc) (σ : Equiv.Perm (Fin (2 ^ (2 * k))))
    (hσ : ∀ j, (σ j : ℕ) =
      (j % 2 ^ k + f (j / 2 ^ k)) % 2 ^ k + 2 ^ k * (j / 2 ^ k))
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0) :
    runList (equalTableAddSteps k s hs f rData rAnc) β =
      some (writeReg β rData (basisBits (2 * k) (σ (localIdx rData β)))) := by
  cases k with
  | zero =>
    have h : σ (localIdx rData β) = localIdx rData β := Fin.ext (by
      rw [hσ]
      simp only [pow_zero, Nat.mod_one, Nat.div_one, one_mul, zero_add])
    rw [equalTableAddSteps, runList_nil, h, basisBits_basisBitsEquiv_symm, writeReg_self]
  | succ K =>
    have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
    have hDA : ∀ {a b : ℕ} (r : QRegister a (2 * (K + 1)))
        (r' : QRegister b (2 ^ s * (K + 1) + (K + 1))),
        (rAnc.compose r').DisjointWires (rData.compose r) := fun _ _ ↦
      QRegister.disjoint_comm.mp ((hdisj.compose_left _).compose_right _)
    have hx : (localIdx (rData.slice (K + 1) (K + 1) (by omega)) β : ℕ) =
        (localIdx (rData.slice (K + 1) s (by omega)) β : ℕ) +
          2 ^ s * (localIdx (rData.slice (K + 1 + s) (K + 1 - s) (by omega)) β : ℕ) := by
      rw [localIdx_val_split _ s (K + 1 - s) (by omega)]
      simp only [localIdx_slice_slice, add_zero]
    have hXB : (rData.slice 0 (K + 1) (by omega)).DisjointWires
        (rData.slice (K + 1) (K + 1) (by omega)) :=
      QRegister.slice_disjoint_of_le rData 0 (K + 1) (K + 1) (K + 1)
        (by omega) (by omega) (by omega)
    rw [equalTableAddSteps, runList_equalTableAddCore K s f _ _ _ _ _ _ _ (hDA _ _) (hDA _ _)
      (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega)) (hDA _ _)
      (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega))
      (QRegister.disjoint_comm.mp
        (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
      (QRegister.disjoint_comm.mp (hDA _ _))
      (QRegister.disjoint_comm.mp
        (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
      (hDA _ _) (hDA _ _)
      (apply_not_mem_slice rAnc _ 0 _ (by omega) (Or.inr (by simp)))
      (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h)
      (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h)
      (apply_not_mem_slice rAnc _ (2 ^ s * (K + 1) + 1) K (by omega) (Or.inl (by dsimp; omega)))
      β (fun _ ↦ hclean _) (fun _ ↦ hclean _) (hclean _) (fun _ ↦ hclean _), ← hx]
    refine congrArg some ?_
    rw [← writeReg_eq_of_eqOn β (writeReg β (rData.slice 0 (K + 1) (by omega)) _) rData
      fun w hw ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, h⟩ ↦ hw ⟨_, h⟩]
    congr 1
    rw [← basisBits_basisBitsEquiv_symm (2 * (K + 1)) (fun p ↦ _)]
    congr 1
    apply Fin.ext
    have hB := (localIdx (rData.slice 0 (K + 1) (by omega)) β).isLt
    rw [hσ, localIdx_val_split rData (K + 1) (K + 1) (by omega) β, ← localIdx,
      localIdx_val_split rData (K + 1) (K + 1) (by omega), localIdx_writeReg,
      basisBitsEquiv_symm_basisBits, localIdx_writeReg_of_disjoint _ _ _ hXB,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hB, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hB]
    simp only [zero_add, Nat.mod_add_mod]
    rw [add_comm (f _)]


theorem andCount_ctrlFlip (c : Option (Wire n)) (t : Wire n) :
    (ctrlFlip c t).andCount = 0 := by
  cases c <;> rfl

theorem andCount_xorSteps (c : Option (Wire n)) (w : ℕ) (rY : QRegister w n)
    (d : BitAssignment w) : ((xorSteps c w rY d).map Step.andCount).sum = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [xorSteps, List.map_append, List.sum_append, ih]
    split_ifs <;> simp [andCount_ctrlFlip]

theorem andCount_andNotSteps (c : Option (Wire n)) (t c' : Wire n) :
    ((andNotSteps c t c').map Step.andCount).sum ≤ 1 := by
  cases c <;> simp [andNotSteps, Step.andCount]

theorem andCount_unAndSteps (c : Option (Wire n)) (t c' : Wire n) :
    ((unAndSteps c t c').map Step.andCount).sum = 0 := by
  cases c <;> rfl

theorem andCount_lookupSteps (w : ℕ) (rY : QRegister w n) (m : ℕ)
    (c : Option (Wire n)) (rX rW : QRegister m n) (T : ℕ → BitAssignment w) :
    ((lookupSteps w rY m c rX rW T).map Step.andCount).sum ≤ 2 ^ m - 1 := by
  induction m generalizing c T with
  | zero => simp [lookupSteps, andCount_xorSteps]
  | succ m ih =>
    rw [lookupSteps]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, andCount_ctrlFlip, andCount_unAndSteps]
    have h0 := andCount_andNotSteps c (rX 0) (rW 0)
    have h1 := ih (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j))
    have h2 := ih (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j + 1))
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

theorem andCount_rippleSteps (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) : ((rippleSteps k rA rB ci rC).map Step.andCount).sum = k := by
  induction k generalizing ci with
  | zero => rfl
  | succ k ih =>
    rw [rippleSteps, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
    omega

theorem andCount_equalTableAddSteps_zero (k : ℕ) (f : ℕ → ℕ)
    (rData : QRegister (2 * k) n) (rAnc : QRegister (2 ^ 0 * k + k) n) :
    ((equalTableAddSteps k 0 (Nat.zero_le k) f rData rAnc).map Step.andCount).sum ≤
      2 * 2 ^ k + k := by
  cases k with
  | zero => simp [equalTableAddSteps]
  | succ K =>
    unfold equalTableAddSteps equalTableAddCore
    simp only [swapTree, List.reverse_nil, List.map_nil, List.append_nil,
      List.map_append, List.sum_append, Nat.sub_zero]
    have h1 := andCount_lookupSteps (2 ^ 0 * (K + 1)) (rAnc.slice 0 (2 ^ 0 * (K + 1)) (by omega))
      (K + 1) none (rData.slice (K + 1 + 0) (K + 1) (by omega))
      (rAnc.slice (2 ^ 0 * (K + 1)) (K + 1) (by omega)) (wideTable 0 K f)
    have h2 := andCount_rippleSteps K
      (dataBlock 0 (K + 1) (rAnc.slice 0 (2 ^ 0 * (K + 1)) (by omega)) 0)
      (rData.slice 0 (K + 1) (by omega)) (rAnc ⟨2 ^ 0 * (K + 1), by omega⟩)
      (rAnc.slice (2 ^ 0 * (K + 1) + 1) K (by omega))
    omega


end ArcsinImpl

end QuantumComputation.Specs
