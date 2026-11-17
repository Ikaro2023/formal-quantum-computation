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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.LowerKraus

@[expose] public section

namespace QuantumComputation.Specs

namespace ArcsinImpl

open Operator Matrix QProg Function
open scoped Matrix ComplexOrder MatrixOrder

variable {Var : Type} {n : ℕ}

namespace Step

def NoUnxor : Step n → Prop
  | unxorList _ _ => False
  | unquad _ _ _ => False
  | rccx0 _ _ _ => False
  | rccx1 _ _ _ => False
  | _ => True

def run : Step n → BitAssignment n → Option (BitAssignment n)
  | x q, β => some (update β q (β q + 1))
  | cnot c t, β => if c ≠ t then some (update β t (β t + β c)) else some β
  | and4t c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β t = 0 then some (update β t (β c₁ * β c₂)) else none
      else some β
  | rccx0 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β c₁ * β c₂ * β t = 0 then some (update β t (β t + β c₁ * β c₂)) else none
      else some β
  | rccx1 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β c₁ * β c₂ * (β t + 1) = 0 then some (update β t (β t + β c₁ * β c₂)) else none
      else some β
  | unand c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β t = β c₁ * β c₂ then some (update β t 0) else none
      else some β
  | unxorList sources t, β =>
      if t ∉ sources then
        if β t = (sources.map β).sum then some (update β t 0) else none
      else some β
  | unquad quads lins t, β =>
      if (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins then
        if β t = (quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum then
          some (update β t 0)
        else none
      else some β

def rawRun : Step n → BitAssignment n → Option (BitAssignment n)
  | x q, β => some (update β q (β q + 1))
  | cnot c t, β => if c ≠ t then some (update β t (β t + β c)) else some β
  | and4t c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then some (update β t (β t + β c₁ * β c₂)) else some β
  | rccx0 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then some (update β t (β t + β c₁ * β c₂)) else some β
  | rccx1 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then some (update β t (β t + β c₁ * β c₂)) else some β
  | unand c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β t = β c₁ * β c₂ then some (update β t 0) else none
      else some β
  | unxorList sources t, β =>
      if t ∉ sources then
        if β t = (sources.map β).sum then some (update β t 0) else none
      else some β
  | unquad quads lins t, β =>
      if (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins then
        if β t = (quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum then
          some (update β t 0)
        else none
      else some β

def inv : Step n → Step n
  | x q => x q
  | cnot c t => cnot c t
  | and4t c₁ c₂ t => unand c₁ c₂ t
  | rccx0 c₁ c₂ t => rccx1 c₁ c₂ t
  | rccx1 c₁ c₂ t => rccx0 c₁ c₂ t
  | unand c₁ c₂ t => and4t c₁ c₂ t
  | unxorList sources t => unxorList sources t
  | unquad quads lins t => unquad quads lins t

def compile (v : Var) : Step n → DynamicCircuit Var n
  | x q => .circuit (Circuit.X q)
  | cnot c t => if h : c ≠ t then .circuit (Circuit.CNOT c t h) else .identity
  | and4t c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then .circuit (AND4T c₁ c₂ t h.1 h.2.1 h.2.2)
      else .identity
  | rccx0 c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then .circuit (RCCX0 c₁ c₂ t h.1 h.2.1 h.2.2)
      else .identity
  | rccx1 c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then .circuit (RCCX1 c₁ c₂ t h.1 h.2.1 h.2.2)
      else .identity
  | unand c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        .seq (.circuit (Circuit.H t)) (.seq (.measure v (QRegister.singleton t))
          (.qIf (fun σ ↦ σ v = 1) (.circuit (fixup c₁ c₂ t h.1)) .identity))
      else .identity
  | unxorList sources t =>
      if _ : t ∉ sources then
        .seq (.circuit (Circuit.H t)) (.seq (.measure v (QRegister.singleton t))
          (.qIf (fun σ ↦ σ v = 1) (.circuit (fixupZ sources t)) .identity))
      else .identity
  | unquad quads lins t =>
      if _ : (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins then
        .seq (.circuit (Circuit.H t)) (.seq (.measure v (QRegister.singleton t))
          (.qIf (fun σ ↦ σ v = 1) (.circuit (fixupQuad quads lins t)) .identity))
      else .identity

def andCount : Step n → ℕ
  | and4t _ _ _ => 1
  | rccx0 _ _ _ => 1
  | rccx1 _ _ _ => 1
  | _ => 0

theorem eq_of_update_eq {β β' : BitAssignment n} {q : Wire n} {a a' : ZMod 2}
    (h : update β q a = update β' q a') (hq : β q = β' q) : β = β' := by
  funext w
  by_cases hw : w = q
  · subst hw
    exact hq
  · simpa [update_of_ne hw] using congrFun h w

theorem update_apply_eq {β β' : BitAssignment n} {q w : Wire n} {a a' : ZMod 2}
    (h : update β q a = update β' q a') (hw : w ≠ q) : β w = β' w := by
  simpa [update_of_ne hw] using congrFun h w

theorem rawRun_of_run {s : Step n} {β γ : BitAssignment n} (h : s.run β = some γ) :
    s.rawRun β = some γ := by
  cases s with
  | x _ => exact h
  | cnot _ _ => exact h
  | unand _ _ _ => exact h
  | unxorList _ _ => exact h
  | unquad _ _ _ => exact h
  | and4t c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [run, rawRun, ite_eq_left hd] at h ⊢
      split_ifs at h with ht0
      simp only [Option.some.injEq] at h ⊢
      rw [← h, ht0, zero_add]
    · simp only [run, rawRun, ite_eq_right hd] at h ⊢
      exact h
  | rccx0 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [run, rawRun, ite_eq_left hd] at h ⊢
      split_ifs at h with ht0
      exact h
    · simp only [run, rawRun, ite_eq_right hd] at h ⊢
      exact h
  | rccx1 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [run, rawRun, ite_eq_left hd] at h ⊢
      split_ifs at h with ht0
      exact h
    · simp only [run, rawRun, ite_eq_right hd] at h ⊢
      exact h

theorem rawRun_injective {s : Step n} {β β' γ : BitAssignment n} (h : s.rawRun β = some γ)
    (h' : s.rawRun β' = some γ) : β = β' := by
  cases s with
  | x q =>
    simp only [rawRun, Option.some.injEq] at h h'
    rw [← h'] at h
    exact eq_of_update_eq h (by simpa using congrFun h q)
  | cnot c t =>
    by_cases hd : c ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc := update_apply_eq h hd
      exact eq_of_update_eq h (by simpa [hc] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | and4t c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by simpa [hc₁, hc₂] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | rccx0 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by simpa [hc₁, hc₂] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | rccx1 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by simpa [hc₁, hc₂] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | unand c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd] at h h'
      split_ifs at h h' with ht ht'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by rw [ht, ht', hc₁, hc₂])
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | unxorList sources t =>
    by_cases hd : t ∉ sources
    · simp only [rawRun, ite_eq_left hd] at h h'
      split_ifs at h h' with ht ht'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      have hmap : sources.map β = sources.map β' :=
        List.map_congr_left fun c hc ↦ update_apply_eq h (fun eq ↦ hd (eq ▸ hc))
      exact eq_of_update_eq h (by rw [ht, ht', hmap])
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | unquad quads lins t =>
    by_cases hd : (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins
    · simp only [rawRun, ite_eq_left hd] at h h'
      split_ifs at h h' with ht ht'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      have hqmap : quads.map (fun p ↦ β p.1 * β p.2) = quads.map (fun p ↦ β' p.1 * β' p.2) :=
        List.map_congr_left fun p hp ↦ by
          rw [update_apply_eq h (hd.1 p hp).2.1, update_apply_eq h (hd.1 p hp).2.2]
      have hlmap : lins.map β = lins.map β' :=
        List.map_congr_left fun c hc ↦ update_apply_eq h (fun eq ↦ hd.2 (eq ▸ hc))
      exact eq_of_update_eq h (by rw [ht, ht', hqmap, hlmap])
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm

theorem count_T_compile (v : Var) (s : Step n) :
    (s.compile v).count PrimitiveGate.T ≤ 4 * s.andCount := by
  cases s <;> simp [compile, andCount] <;> split_ifs <;>
    simp [fixup, count_T_AND4T, count_T_RCCX0, count_T_RCCX1, count_T_fixupZ, count_T_fixupQuad]

theorem count_TOFF_compile (v : Var) (s : Step n) :
    (s.compile v).count PrimitiveGate.TOFF = 0 := by
  cases s <;> simp [compile] <;> split_ifs <;>
    simp [fixup, count_TOFF_AND4T, count_TOFF_RCCX0, count_TOFF_RCCX1, count_TOFF_fixupZ,
      count_TOFF_fixupQuad]

theorem unand_scalar (a b : ZMod 2) (ψ : Fin (2 ^ n) → ℂ) :
    sqrtHalf • (sqrtHalf • ψ + bitSign a • sqrtHalf • bitSign b • ψ) =
      if a = b then ψ else 0 := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [bitSign, one_ne_zero, zero_ne_one, ↓reduceIte, one_smul, neg_smul, smul_neg,
      smul_add, smul_smul] <;> match_scalars <;>
    first
      | linear_combination 2 * sqrtHalf_mul_sqrtHalf
      | linear_combination 0 * sqrtHalf_mul_sqrtHalf

theorem exists_lowerKraus [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (s : Step n) :
    ∃ R, LowerKraus (s.compile v).compile R ∧
      (∀ β γ, s.run β = some γ → R.mulVec (ket β) = ket γ) ∧
      (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (s.rawRun β)) := by
  cases s with
  | x q =>
    refine ⟨_, lowerKraus_circuit _, ?_, fun β ↦ ⟨1, by rw [one_smul, rawRun, optKet, ket_X]⟩⟩
    intro β γ h
    simp only [run, Option.some.injEq] at h
    rw [← h, ket_X]
  | cnot c t =>
    by_cases hd : c ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, fun β ↦ ⟨1, by rw [one_smul, ket_CNOT c t hd β]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, ket_CNOT]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | and4t c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, ?_⟩
      · intro β γ h
        split_ifs at h with ht0
        simp only [Option.some.injEq] at h
        simp only [← h, ket_AND4T_eq_smul, ht0, cleanAndPhase, ↓reduceIte, one_smul, zero_add]
      · intro β
        exact ⟨cleanAndPhase (β c₁) (β c₂) (β t),
          ket_AND4T_eq_smul c₁ c₂ t hd.1 hd.2.1 hd.2.2 β⟩
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | rccx0 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, ?_⟩
      · intro β γ h
        split_ifs at h with ht0
        simp only [Option.some.injEq] at h
        rw [← h, ket_RCCX0_eq_smul, rccx0Phase_eq_one ht0, one_smul]
      · intro β
        exact ⟨rccx0Phase (β c₁) (β c₂) (β t),
          ket_RCCX0_eq_smul c₁ c₂ t hd.1 hd.2.1 hd.2.2 β⟩
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | rccx1 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, ?_⟩
      · intro β γ h
        split_ifs at h with ht0
        simp only [Option.some.injEq] at h
        rw [← h, ket_RCCX1_eq_smul, rccx0Phase_eq_one ht0, one_smul]
      · intro β
        exact ⟨rccx0Phase (β c₁) (β c₂) (β t + 1),
          ket_RCCX1_eq_smul c₁ c₂ t hd.1 hd.2.1 hd.2.2 β⟩
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | unand c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd]
      have hmain : ∀ β,
          ((sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
            (fixup c₁ c₂ t hd.1).eval.1 * (QRegister.singleton t).basisOutcomeProjector 1)) *
            (Circuit.H t).eval.1).mulVec (ket β) =
          optKet (if β t = β c₁ * β c₂ then some (update β t 0) else none) := by
        intro β
        have hH : (Circuit.H t).eval.1.mulVec (ket β) =
            sqrtHalf • (ket (update β t 0) + bitSign (β t) • ket (update β t 1)) := ket_H t β
        have hF : (fixup c₁ c₂ t hd.1).eval.1.mulVec (ket (update β t 1)) =
            bitSign (β c₁ * β c₂) • ket (update β t 0) := by
          rw [fixup_mulVec_ket, update_of_ne hd.2.1, update_of_ne hd.2.2, update_self, update_idem,
            one_add_one_zmod2]
        simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
          hF, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
        rw [unand_scalar]
        split_ifs <;> rfl
      refine ⟨_, (lowerKraus_circuit (Circuit.H t)).qSeq
        (lowerKraus_measure_singleton_qIf v t (lowerKraus_circuit (fixup c₁ c₂ t hd.1))),
        ?_, fun β ↦ ⟨1, by rw [one_smul, hmain]⟩⟩
      intro β γ h
      rw [hmain, h, optKet]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | unxorList sources t =>
    by_cases hd : t ∉ sources
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd]
      have hmain : ∀ β,
          ((sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
            (fixupZ sources t).eval.1 * (QRegister.singleton t).basisOutcomeProjector 1)) *
            (Circuit.H t).eval.1).mulVec (ket β) =
          optKet (if β t = (sources.map β).sum then some (update β t 0) else none) := by
        intro β
        have hH : (Circuit.H t).eval.1.mulVec (ket β) =
            sqrtHalf • (ket (update β t 0) + bitSign (β t) • ket (update β t 1)) := ket_H t β
        have hmap : sources.map (update β t 1) = sources.map β :=
          List.map_congr_left fun c hc ↦ update_of_ne (fun eq : c = t ↦ hd (eq ▸ hc)) _ _
        have hF : (fixupZ sources t).eval.1.mulVec (ket (update β t 1)) =
            bitSign ((sources.map β).sum) • ket (update β t 0) := by
          rw [fixupZ_mulVec_ket, hmap, update_self, update_idem, one_add_one_zmod2]
        simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
          hF, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
        rw [unand_scalar]
        split_ifs <;> rfl
      refine ⟨_, (lowerKraus_circuit (Circuit.H t)).qSeq
        (lowerKraus_measure_singleton_qIf v t (lowerKraus_circuit (fixupZ sources t))),
        ?_, fun β ↦ ⟨1, by rw [one_smul, hmain]⟩⟩
      intro β γ h
      rw [hmain, h, optKet]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | unquad quads lins t =>
    by_cases hd : (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd]
      have hmain : ∀ β,
          ((sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
            (fixupQuad quads lins t).eval.1 * (QRegister.singleton t).basisOutcomeProjector 1)) *
            (Circuit.H t).eval.1).mulVec (ket β) =
          optKet (if β t = (quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum then
            some (update β t 0) else none) := by
        intro β
        have hH : (Circuit.H t).eval.1.mulVec (ket β) =
            sqrtHalf • (ket (update β t 0) + bitSign (β t) • ket (update β t 1)) := ket_H t β
        have hqmap : quads.map (fun p ↦ (update β t 1) p.1 * (update β t 1) p.2) =
            quads.map (fun p ↦ β p.1 * β p.2) :=
          List.map_congr_left fun p hp ↦ by
            rw [update_of_ne (hd.1 p hp).2.1, update_of_ne (hd.1 p hp).2.2]
        have hlmap : lins.map (update β t 1) = lins.map β :=
          List.map_congr_left fun c hc ↦ update_of_ne (fun eq : c = t ↦ hd.2 (eq ▸ hc)) _ _
        have hF : (fixupQuad quads lins t).eval.1.mulVec (ket (update β t 1)) =
            bitSign ((quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum) •
              ket (update β t 0) := by
          rw [fixupQuad_mulVec_ket _ _ _ (fun p hp ↦ (hd.1 p hp).1), hqmap, hlmap,
            update_self, update_idem, one_add_one_zmod2]
        simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
          hF, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
        rw [unand_scalar]
        split_ifs <;> rfl
      refine ⟨_, (lowerKraus_circuit (Circuit.H t)).qSeq
        (lowerKraus_measure_singleton_qIf v t (lowerKraus_circuit (fixupQuad quads lins t))),
        ?_, fun β ↦ ⟨1, by rw [one_smul, hmain]⟩⟩
      intro β γ h
      rw [hmain, h, optKet]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]

end Step

/-- Run a list of steps from left to right. -/
def runList : List (Step n) → BitAssignment n → Option (BitAssignment n)
  | [], β => some β
  | s :: ss, β => (s.run β).bind (runList ss)

/-- Underlying support run of a list of steps. -/
def rawRunList : List (Step n) → BitAssignment n → Option (BitAssignment n)
  | [], β => some β
  | s :: ss, β => (s.rawRun β).bind (rawRunList ss)

/-- Compile a list of steps to a sequence of dynamic circuits. -/
def compileList (v : Var) : List (Step n) → DynamicCircuit Var n
  | [] => .identity
  | s :: ss => .seq (s.compile v) (compileList v ss)

@[simp] theorem runList_nil (β : BitAssignment n) : runList [] β = some β := rfl

@[simp] theorem runList_cons (s : Step n) (ss : List (Step n)) (β : BitAssignment n) :
    runList (s :: ss) β = (s.run β).bind (runList ss) := rfl

theorem runList_append (ss ts : List (Step n)) (β : BitAssignment n) :
    runList (ss ++ ts) β = (runList ss β).bind (runList ts) := by
  induction ss generalizing β with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.cons_append, runList_cons, ih]
    cases s.run β <;> rfl

theorem rawRunList_of_runList {ss : List (Step n)} {β γ : BitAssignment n}
    (h : runList ss β = some γ) : rawRunList ss β = some γ := by
  induction ss generalizing β with
  | nil => exact h
  | cons s ss ih =>
    simp only [runList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨δ, hδ, hγ⟩ := h
    simp only [rawRunList, Step.rawRun_of_run hδ, Option.bind_some]
    exact ih hγ

theorem rawRunList_injective {ss : List (Step n)} {β β' γ : BitAssignment n}
    (h : rawRunList ss β = some γ) (h' : rawRunList ss β' = some γ) : β = β' := by
  induction ss generalizing β β' with
  | nil => exact (Option.some.inj h).trans (Option.some.inj h').symm
  | cons s ss ih =>
    simp only [rawRunList, Option.bind_eq_some_iff] at h h'
    obtain ⟨δ, hδ, hγ⟩ := h
    obtain ⟨δ', hδ', hγ'⟩ := h'
    exact Step.rawRun_injective hδ ((ih hγ hγ') ▸ hδ')

theorem exists_lowerKraus_compileList [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (ss : List (Step n)) :
    ∃ R, LowerKraus (compileList v ss).compile R ∧
      (∀ β γ, runList ss β = some γ → R.mulVec (ket β) = ket γ) ∧
      (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (rawRunList ss β)) := by
  induction ss with
  | nil =>
    refine ⟨1, lowerKraus_skip, ?_,
      fun β ↦ ⟨1, by rw [one_smul, rawRunList, optKet, Matrix.one_mulVec]⟩⟩
    intro β γ h
    simp only [runList_nil, Option.some.injEq] at h
    rw [← h, Matrix.one_mulVec]
  | cons s ss ih =>
    obtain ⟨R₁, hK₁, hR₁, hRaw₁⟩ := s.exists_lowerKraus v
    obtain ⟨R₂, hK₂, hR₂, hRaw₂⟩ := ih
    refine ⟨R₂ * R₁, hK₁.qSeq hK₂, ?_, ?_⟩
    · intro β γ h
      simp only [runList_cons, Option.bind_eq_some_iff] at h
      obtain ⟨δ, hδ, hγ⟩ := h
      rw [← Matrix.mulVec_mulVec, hR₁ β δ hδ, hR₂ δ γ hγ]
    · intro β
      obtain ⟨z₁, hz₁⟩ := hRaw₁ β
      rw [← Matrix.mulVec_mulVec, hz₁, Matrix.mulVec_smul]
      rcases hraw : s.rawRun β with _ | δ
      · exact ⟨0, by simp [rawRunList, hraw, optKet]⟩
      · obtain ⟨z₂, hz₂⟩ := hRaw₂ δ
        refine ⟨z₁ * z₂, ?_⟩
        simp only [rawRunList, hraw, Option.bind_some, optKet, hz₂, smul_smul]

theorem count_T_compileList (v : Var) (ss : List (Step n)) :
    (compileList v ss).count PrimitiveGate.T ≤ 4 * (ss.map Step.andCount).sum := by
  induction ss with
  | nil => simp [compileList]
  | cons s ss ih =>
    simp only [compileList, DynamicCircuit.count, List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (s.count_T_compile v) ih

theorem count_TOFF_compileList (v : Var) (ss : List (Step n)) :
    (compileList v ss).count PrimitiveGate.TOFF = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [compileList, ih, s.count_TOFF_compile v]

/-- A step list that maps every clean-ancilla basis state by the basis permutation `σ` of the
target register realizes `permutationUnitary σ` as a clean subroutine. -/
theorem realizesCleanSubroutine_compileList [DecidableEq Var] [NeZero (2 ^ n)]
    {k m : ℕ} (v : Var) (ss : List (Step n)) (rTarget : QRegister k n) (rAnc : QRegister m n)
    (hdisj : rTarget.DisjointWires rAnc) (σ : Equiv.Perm (Fin (2 ^ k)))
    (hrun : ∀ β, localIdx rAnc β = 0 →
      runList ss β = some (writeReg β rTarget (basisBits k (σ (localIdx rTarget β))))) :
    RealizesCleanSubroutine rTarget rAnc hdisj (permutationUnitary σ)
      (compileList v ss).compile := by
  obtain ⟨R, hK, hR, hRaw⟩ := exists_lowerKraus_compileList v ss
  refine realizesCleanSubroutine_of_lowerKraus rTarget rAnc hdisj _ hK
    (matrix_ext_ket fun β ↦ ?_)
  have hE : ∀ γ, (rTarget.embedUnitary (permutationUnitary σ)).1.mulVec (ket γ) =
      ket (writeReg γ rTarget (basisBits k (σ (localIdx rTarget γ)))) := fun γ ↦ by
    have h := embedMatrix_permMatrix_mulVec_ket rTarget σ⁻¹ γ
    rw [Equiv.Perm.inv_def, Equiv.symm_symm] at h
    rw [QRegister.embedUnitary_val]
    exact h
  have hanc : ∀ γ δ, localIdx rAnc (writeReg γ rTarget δ) = localIdx rAnc γ :=
    fun γ δ ↦ localIdx_writeReg_of_disjoint γ rTarget rAnc hdisj δ
  simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket]
  by_cases hβ : localIdx rAnc β = 0
  · rw [hR β _ (hrun β hβ), ite_eq_left hβ, hE, basisOutcomeProjector_mulVec_ket, hanc,
      ite_eq_left hβ]
  · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hRaw β
    rw [hz, Matrix.mulVec_smul]
    rcases hγ : rawRunList ss β with _ | γ
    · simp [optKet]
    · rw [optKet, basisOutcomeProjector_mulVec_ket, ite_eq_right, smul_zero]
      intro hγ0
      have h0 :
          localIdx rAnc (writeReg γ rTarget (basisBits k (σ.symm (localIdx rTarget γ)))) = 0 := by
        rw [hanc]
        exact hγ0
      have hpre := rawRunList_of_runList (hrun _ h0)
      simp only [localIdx_writeReg, basisBitsEquiv_symm_basisBits, Equiv.apply_symm_apply,
        writeReg_writeReg, writeReg_self] at hpre
      exact hβ (rawRunList_injective hγ hpre ▸ h0)

variable {n k : ℕ}

/-- A register without its first wire. -/
abbrev regTail (r : QRegister (k + 1) n) : QRegister k n := r.slice 1 k (by omega)

theorem regTail_apply (r : QRegister (k + 1) n) (i : Fin k) : regTail r i = r i.succ := by
  rw [QRegister.slice_apply]
  congr 1
  ext
  simp [add_comm]

theorem regTail_ne_zero (r : QRegister (k + 1) n) (i : Fin k) : regTail r i ≠ r 0 := by
  rw [regTail_apply]
  exact fun h ↦ Fin.succ_ne_zero i (r.wires.injective h)

theorem zero_not_mem_regTail (r : QRegister (k + 1) n) : r 0 ∉ Set.range (regTail r).wires :=
  fun ⟨i, hi⟩ ↦ regTail_ne_zero r i hi

theorem not_mem_regTail {r : QRegister (k + 1) n} {w : Wire n} (hw : w ∉ Set.range r.wires) :
    w ∉ Set.range (regTail r).wires :=
  fun ⟨i, hi⟩ ↦ hw ⟨i.succ, by rw [← hi, regTail_apply]⟩

theorem not_mem_of_disjoint {m : ℕ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (i : Fin k) : r i ∉ Set.range s.wires :=
  fun ⟨j, hj⟩ ↦ h.ne i j hj.symm

theorem apply_not_mem_slice (r : QRegister k n) (j : Fin k) (a b : ℕ) (h : a + b ≤ k)
    (hj : (j : ℕ) < a ∨ a + b ≤ j) : r j ∉ Set.range (r.slice a b h).wires := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val (r.wires.injective ((QRegister.slice_apply r a b h i).symm.trans hi))
  change a + (i : ℕ) = j at this
  omega

theorem writeReg_succ (β : BitAssignment n) (r : QRegister (k + 1) n)
    (γ : BitAssignment (k + 1)) :
    writeReg β r γ = update (writeReg β (regTail r) (fun i ↦ γ i.succ)) (r 0) (γ 0) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    cases i using Fin.cases with
    | zero => rw [update_self]
    | succ j =>
      rw [update_of_ne (fun h ↦ Fin.succ_ne_zero j (r.wires.injective h)), ← regTail_apply,
        writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, update_of_ne (fun h ↦ hw ⟨0, h.symm⟩),
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_regTail hw)]

theorem writeReg_update_of_not_mem (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) {w : Wire n} (hw : w ∉ Set.range r.wires) (x : ZMod 2) :
    writeReg (update β w x) r γ = update (writeReg β r γ) w x := by
  funext w'
  by_cases hw' : w' ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw'
    rw [writeReg_apply_reg, update_of_ne (fun h ↦ hw ⟨i, h⟩), writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw']
    by_cases h : w' = w
    · subst h
      rw [update_self, update_self]
    · rw [update_of_ne h, update_of_ne h, writeReg_apply_of_not_mem _ _ _ _ hw']

theorem localIdx_update_of_not_mem (r : QRegister k n) (β : BitAssignment n) {w : Wire n}
    (hw : w ∉ Set.range r.wires) (x : ZMod 2) : localIdx r (update β w x) = localIdx r β := by
  simp only [localIdx]
  congr 1
  funext i
  exact update_of_ne (fun h ↦ hw ⟨i, h⟩) _ _

theorem not_mem_slice {N : ℕ} {r : QRegister N n} {w : Wire n} (hw : w ∉ Set.range r.wires)
    (a b : ℕ) (h : a + b ≤ N) : w ∉ Set.range (r.slice a b h).wires :=
  fun ⟨i, hi⟩ ↦ hw ⟨_, (QRegister.slice_apply r a b h i).symm.trans hi⟩

theorem localIdx_slice_slice {N : ℕ} (r : QRegister N n) (a b c d : ℕ) (h : a + b ≤ N)
    (h' : c + d ≤ b) (β : BitAssignment n) :
    localIdx ((r.slice a b h).slice c d h') β = localIdx (r.slice (a + c) d (by omega)) β := by
  simp only [localIdx, QRegister.slice_apply, Nat.add_assoc]

theorem localIdx_val (r : QRegister k n) (β : BitAssignment n) :
    (localIdx r β : ℕ) = ∑ i : Fin k, (β (r i)).val * 2 ^ (i : ℕ) := by
  simp [localIdx, basisBits, ZMod.finEquiv]
  rfl

theorem localIdx_val_succ (r : QRegister (k + 1) n) (β : BitAssignment n) :
    (localIdx r β : ℕ) = (β (r 0)).val + 2 * (localIdx (regTail r) β : ℕ) := by
  rw [localIdx_val, localIdx_val, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [regTail_apply, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem localIdx_val_split {N : ℕ} (r : QRegister N n) (a b : ℕ) (h : a + b = N)
    (β : BitAssignment n) :
    (localIdx r β : ℕ) = (localIdx (r.slice 0 a (by omega)) β : ℕ) +
      2 ^ a * (localIdx (r.slice a b (by omega)) β : ℕ) := by
  subst h
  rw [localIdx_val, localIdx_val, localIdx_val, Finset.mul_sum, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [QRegister.slice_apply, zero_add]
    rfl
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    change (β (r ⟨a + i, by omega⟩)).val * 2 ^ (a + (i : ℕ)) =
      2 ^ a * ((β (r ⟨a + i, by omega⟩)).val * 2 ^ (i : ℕ))
    ring

theorem writeReg_comm {m : ℕ} (β : BitAssignment n) (r : QRegister k n) (s : QRegister m n)
    (hdisj : r.DisjointWires s) (γ : BitAssignment k) (δ : BitAssignment m) :
    writeReg (writeReg β r γ) s δ = writeReg (writeReg β s δ) r γ := by
  funext w
  by_cases hr : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hr
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hdisj i), writeReg_apply_reg,
      writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hr]
    by_cases hs : w ∈ Set.range s.wires
    · obtain ⟨j, rfl⟩ := hs
      rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hs, writeReg_apply_of_not_mem _ _ _ _ hs,
        writeReg_apply_of_not_mem _ _ _ _ hr]

theorem basisBits_mk_apply (m : ℕ) (hm : m < 2 ^ k) (i : Fin k) :
    basisBits k ⟨m, hm⟩ i = ((m / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) :=
  basisBits_eq_div_mod k ⟨m, hm⟩ i

variable {n : ℕ}


end ArcsinImpl

end QuantumComputation.Specs
