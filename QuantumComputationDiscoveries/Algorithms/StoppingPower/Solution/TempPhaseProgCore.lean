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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ZeroAncUspCore

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModTempPhaseProg
@[expose] public section
section SharedScope
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem
open BchCubeDecoder StreamingBchComparator
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
theorem wire_ne_of_lt {M : ℕ} {a b : Wire M} (h : a.val < b.val) : a ≠ b :=
  InPlaceFullAddSlice.wire_ne_of_lt h
theorem wire_ne_of_gt {M : ℕ} {a b : Wire M} (h : b.val < a.val) : a ≠ b :=
  (wire_ne_of_lt h).symm
theorem dite_true_eq {c : Prop} {inst : Decidable c} (hc : c) {α : Sort*}
    {t : c → α} {e : ¬ c → α} : dite c t e = t hc := by simp [hc]
theorem mul_mulVec_prog {n : ℕ} (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (v : Fin (2 ^ n) → ℂ) : (A * B).mulVec v = A.mulVec (B.mulVec v) :=
  (Matrix.mulVec_mulVec v A B).symm
noncomputable def writeRegProg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeRegProg_apply_reg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeRegProg β r γ (r i) = γ i :=
  InPlaceFullAddSlice.writeRegProg_apply_reg β r γ i
theorem writeRegProg_apply_of_not_mem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeRegProg β r γ w = β w :=
  InPlaceFullAddSlice.writeRegProg_apply_of_not_mem β r γ w hw
noncomputable abbrev localIdxProg {k n : ℕ} (r : QRegister k n) (β : BitAssignment n) :
    Fin (2 ^ k) := (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket_prog {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdxProg r β) • ket (writeRegProg β r (basisBits k l)) :=
  InPlaceFullAddSlice.embedMatrix_mulVec_ket_prog r A β
inductive CliffProg (M : ℕ) where
  | nil : CliffProg M
  | x (q : Wire M) : CliffProg M
  | cnot (c t : Wire M) (h : c ≠ t) : CliffProg M
  | seq (c₁ c₂ : CliffProg M) : CliffProg M
namespace CliffProg
def eval {M : ℕ} : CliffProg M → BitAssignment M → BitAssignment M
  | .nil, β => β
  | .x q, β => Function.update β q (β q + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .seq c₁ c₂, β => c₂.eval (c₁.eval β)
def inv {M : ℕ} : CliffProg M → CliffProg M
  | .nil => .nil
  | .x q => .x q
  | .cnot c t h => .cnot c t h
  | .seq c₁ c₂ => .seq c₂.inv c₁.inv
def toCircuit {M : ℕ} : CliffProg M → Circuit M
  | .nil => .identity
  | .x q => Circuit.X q
  | .cnot c t h => Circuit.CNOT c t h
  | .seq c₁ c₂ => c₁.toCircuit ;;ᶜ c₂.toCircuit
def onRegister {M n : ℕ} (r : QRegister M n) : CliffProg M → CliffProg n
  | .nil => .nil
  | .x q => .x (r q)
  | .cnot c t h => .cnot (r c) (r t) (r.wires.injective.ne h)
  | .seq c₁ c₂ => .seq (c₁.onRegister r) (c₂.onRegister r)
def SupportsBelow {M : ℕ} (bound : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x q => q.val < bound
  | .cnot c t _ => c.val < bound ∧ t.val < bound
  | .seq c₁ c₂ => c₁.SupportsBelow bound ∧ c₂.SupportsBelow bound
protected def toSlice {M : ℕ} : CliffProg M → InPlaceFullAddSlice.CliffProg M
  | .nil => .nil
  | .x q => .x q
  | .cnot c t h => .cnot c t h
  | .seq c₁ c₂ => .seq c₁.toSlice c₂.toSlice
protected theorem toSlice_eval {M : ℕ} : ∀ (c : CliffProg M) (β), c.toSlice.eval β = c.eval β
  | .nil, _ | .x _, _ | .cnot _ _ _, _ => rfl
  | .seq _ _, _ => by simp [CliffProg.toSlice, eval, InPlaceFullAddSlice.CliffProg.eval,
      CliffProg.toSlice_eval]
protected theorem toSlice_inv {M : ℕ} : ∀ c : CliffProg M, c.toSlice.inv = c.inv.toSlice
  | .nil | .x _ | .cnot _ _ _ => rfl
  | .seq _ _ => by simp [CliffProg.toSlice, inv, InPlaceFullAddSlice.CliffProg.inv,
      CliffProg.toSlice_inv]
protected theorem toSlice_toCircuit {M : ℕ} :
    ∀ c : CliffProg M, c.toSlice.toCircuit = c.toCircuit
  | .nil | .x _ | .cnot _ _ _ => rfl
  | .seq _ _ => by simp [CliffProg.toSlice, toCircuit, InPlaceFullAddSlice.CliffProg.toCircuit,
      CliffProg.toSlice_toCircuit]
protected theorem toSlice_onRegister {M n : ℕ} (r : QRegister M n) :
    ∀ c : CliffProg M, c.toSlice.onRegister r = (c.onRegister r).toSlice
  | .nil | .x _ | .cnot _ _ _ => rfl
  | .seq _ _ => by simp [CliffProg.toSlice, onRegister, InPlaceFullAddSlice.CliffProg.onRegister,
      CliffProg.toSlice_onRegister]
@[simp] theorem toCircuit_count_toff {M : ℕ} (c : CliffProg M) :
    c.toCircuit.count PrimitiveGate.TOFF = 0 := c.toSlice_toCircuit ▸ c.toSlice.toCircuit_count_toff
@[simp] theorem toCircuit_count_t {M : ℕ} (c : CliffProg M) :
    c.toCircuit.count PrimitiveGate.T = 0 := c.toSlice_toCircuit ▸ c.toSlice.toCircuit_count_t
theorem toCircuit_eval_ket {M : ℕ} (c : CliffProg M) (β : BitAssignment M) :
    c.toCircuit.eval.1.mulVec (ket β) = ket (c.eval β) := by
  rw [← c.toSlice_toCircuit, ← c.toSlice_eval]
  exact c.toSlice.toCircuit_eval_ket β
theorem onRegister_toCircuit_eval {M n : ℕ} (r : QRegister M n) (c : CliffProg M) :
    ((c.onRegister r).toCircuit).eval = (c.toCircuit.onRegister r).eval := by
  simpa [← (c.onRegister r).toSlice_toCircuit, ← c.toSlice_onRegister, ← c.toSlice_toCircuit]
    using c.toSlice.onRegister_toCircuit_eval r
theorem inv_eval {M : ℕ} (c : CliffProg M) (β : BitAssignment M) :
    c.inv.eval (c.eval β) = β := by
  simpa [← c.inv.toSlice_eval, ← c.toSlice_inv, ← c.toSlice_eval] using c.toSlice.inv_eval β
theorem eval_outside {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound →
      ∀ (β : BitAssignment M) (w : Wire M), bound ≤ w.val → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x _, hq, _, _, hw | .cnot _ _ _, ⟨_, hq⟩, _, _, hw =>
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le hq hw)) _ _
  | .seq c₁ c₂, ⟨h₁, h₂⟩, _, w, hw =>
      (eval_outside c₂ h₂ _ w hw).trans (eval_outside c₁ h₁ _ w hw)
theorem inv_supportsBelow {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound → c.inv.SupportsBelow bound
  | .nil, h | .x _, h | .cnot _ _ _, h => h
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => ⟨inv_supportsBelow c₂ h₂, inv_supportsBelow c₁ h₁⟩
end CliffProg
inductive TempPhaseProg (m : ℕ) where
  | nil : TempPhaseProg m
  | cliff (c : CliffProg m) : TempPhaseProg m
  | z (q : Wire m) : TempPhaseProg m
  | seq (p₁ p₂ : TempPhaseProg m) : TempPhaseProg m
  | tempAnd (c₁ c₂ anc : Wire m) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : TempPhaseProg m) : TempPhaseProg m
namespace TempPhaseProg
def x {m : ℕ} (q : Wire m) : TempPhaseProg m := .cliff (.x q)
def cnot {m : ℕ} (c t : Wire m) (h : c ≠ t) : TempPhaseProg m := .cliff (.cnot c t h)
def evalBits {m : ℕ} : TempPhaseProg m → BitAssignment m → BitAssignment m
  | .nil, β | .z _, β => β
  | .cliff c, β => c.eval β
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₂ := body.evalBits (Function.update β anc (β anc + β c₁ * β c₂))
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)
def evalSign {m : ℕ} : TempPhaseProg m → BitAssignment m → ZMod 2
  | .nil, _ | .cliff _, _ => 0
  | .z q, β => β q
  | .seq p₁ p₂, β => p₁.evalSign β + p₂.evalSign (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      body.evalSign (Function.update β anc (β anc + β c₁ * β c₂))
def countTempAnd {m : ℕ} : TempPhaseProg m → ℕ
  | .nil | .cliff _ | .z _ => 0
  | .seq p₁ p₂ => p₁.countTempAnd + p₂.countTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.countTempAnd
def toToffCircuit {m : ℕ} : TempPhaseProg m → Circuit m
  | .nil => .identity
  | .cliff c => c.toCircuit
  | .z q => Circuit.Z q
  | .seq p₁ p₂ => p₁.toToffCircuit ;;ᶜ p₂.toToffCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toToffCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
def onRegister {m n : ℕ} (r : QRegister m n) : TempPhaseProg m → TempPhaseProg n
  | .nil => .nil
  | .cliff c => .cliff (c.onRegister r)
  | .z q => .z (r q)
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)
        (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a) (body.onRegister r)
def toDyn {Var : Type} {n : ℕ} (v : Var) : TempPhaseProg n → DynamicCircuit Var n
  | .nil => .circuit .identity
  | .cliff c => .circuit c.toCircuit
  | .z q => .circuit (Circuit.Z q)
  | .seq p₁ p₂ => .seq (p₁.toDyn v) (p₂.toDyn v)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq (body.toDyn v) (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
protected def toSlice {m : ℕ} : TempPhaseProg m → InPlaceFullAddSlice.TempPhaseProg m
  | .nil => .nil
  | .cliff c => .cliff c.toSlice
  | .z q => .z q
  | .seq p₁ p₂ => .seq p₁.toSlice p₂.toSlice
  | .tempAnd c₁ c₂ a h₁ h₂ h₃ b => .tempAnd c₁ c₂ a h₁ h₂ h₃ b.toSlice
protected theorem toSlice_evalBits {m : ℕ} :
    ∀ (p : TempPhaseProg m) (β), p.toSlice.evalBits β = p.evalBits β
  | .nil, _ | .z _, _ => rfl
  | .cliff c, β => c.toSlice_eval β
  | .seq _ _, _ | .tempAnd _ _ _ _ _ _ _, _ => by
      simp [TempPhaseProg.toSlice, evalBits, InPlaceFullAddSlice.TempPhaseProg.evalBits,
        TempPhaseProg.toSlice_evalBits]
protected theorem toSlice_evalSign {m : ℕ} :
    ∀ (p : TempPhaseProg m) (β), p.toSlice.evalSign β = p.evalSign β
  | .nil, _ | .cliff _, _ | .z _, _ => rfl
  | .seq _ _, _ | .tempAnd _ _ _ _ _ _ _, _ => by
      simp [TempPhaseProg.toSlice, evalSign, InPlaceFullAddSlice.TempPhaseProg.evalSign,
        TempPhaseProg.toSlice_evalBits, TempPhaseProg.toSlice_evalSign]
protected theorem toSlice_count {m : ℕ} :
    ∀ p : TempPhaseProg m, p.toSlice.countTempAnd = p.countTempAnd
  | .nil | .cliff _ | .z _ => rfl
  | .seq _ _ | .tempAnd _ _ _ _ _ _ _ => by
      simp [TempPhaseProg.toSlice, countTempAnd,
        InPlaceFullAddSlice.TempPhaseProg.countTempAnd, TempPhaseProg.toSlice_count]
protected theorem toSlice_toToffCircuit {m : ℕ} :
    ∀ p : TempPhaseProg m, p.toSlice.toToffCircuit = p.toToffCircuit
  | .nil | .z _ => rfl
  | .cliff c => c.toSlice_toCircuit
  | .seq _ _ | .tempAnd _ _ _ _ _ _ _ => by
      simp [TempPhaseProg.toSlice, toToffCircuit,
        InPlaceFullAddSlice.TempPhaseProg.toToffCircuit, TempPhaseProg.toSlice_toToffCircuit]
protected theorem toSlice_onRegister {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempPhaseProg m, p.toSlice.onRegister r = (p.onRegister r).toSlice
  | .nil | .z _ => rfl
  | .cliff c => congrArg _ (c.toSlice_onRegister r)
  | .seq _ _ | .tempAnd _ _ _ _ _ _ _ => by
      simp [TempPhaseProg.toSlice, onRegister, InPlaceFullAddSlice.TempPhaseProg.onRegister,
        TempPhaseProg.toSlice_onRegister]
protected theorem toSlice_toDyn {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempPhaseProg n, p.toSlice.toDyn v = p.toDyn v
  | .nil | .z _ => rfl
  | .cliff c => congrArg _ c.toSlice_toCircuit
  | .seq _ _ | .tempAnd _ _ _ _ _ _ _ => by
      simp [TempPhaseProg.toSlice, toDyn, InPlaceFullAddSlice.TempPhaseProg.toDyn,
        TempPhaseProg.toSlice_toDyn]
@[simp] theorem onRegister_countTempAnd {m n : ℕ} (r : QRegister m n) (p : TempPhaseProg m) :
    (p.onRegister r).countTempAnd = p.countTempAnd := by
  rw [← (p.onRegister r).toSlice_count, ← p.toSlice_onRegister, ← p.toSlice_count]
  exact p.toSlice.onRegister_countTempAnd r
@[simp] theorem toDyn_count_toff {Var : Type} {n : ℕ} (v : Var) (p : TempPhaseProg n) :
    (p.toDyn v).count PrimitiveGate.TOFF = 0 := p.toSlice_toDyn v ▸ p.toSlice.toDyn_count_toff v
@[simp] theorem toDyn_count_t {Var : Type} {n : ℕ} (v : Var) (p : TempPhaseProg n) :
    (p.toDyn v).count PrimitiveGate.T = 4 * p.countTempAnd := by
  rw [← p.toSlice_toDyn, ← p.toSlice_count]
  exact p.toSlice.toDyn_count_t v
theorem bitSign_eq_neg_one_pow (b : ZMod 2) : bitSign b = (-1 : ℂ) ^ b.val :=
  InPlaceFullAddSlice.TempPhaseProg.bitSign_eq_neg_one_pow b
theorem neg_one_pow_zmod2_mul (a b : ZMod 2) :
    ((-1 : ℂ) ^ a.val) * ((-1 : ℂ) ^ b.val) = (-1 : ℂ) ^ (a + b).val :=
  InPlaceFullAddSlice.TempPhaseProg.neg_one_pow_zmod2_mul a b
theorem toToffCircuit_eval_ket {m : ℕ} (p : TempPhaseProg m) (β : BitAssignment m) :
    (p.toToffCircuit).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (p.evalSign β).val) • ket (p.evalBits β) := by
  rw [← p.toSlice_toToffCircuit, ← p.toSlice_evalSign, ← p.toSlice_evalBits]
  exact p.toSlice.toToffCircuit_eval_ket β
theorem onRegister_toToffCircuit_eval {m n : ℕ} (r : QRegister m n) (p : TempPhaseProg m) :
    ((p.onRegister r).toToffCircuit).eval = (p.toToffCircuit.onRegister r).eval := by
  simpa [← (p.onRegister r).toSlice_toToffCircuit, ← p.toSlice_onRegister,
    ← p.toSlice_toToffCircuit] using p.toSlice.onRegister_toToffCircuit_eval r
end TempPhaseProg
def cleanRem (M rem : ℕ) (β : BitAssignment M) : Prop :=
  ∀ w : Wire M, M - rem ≤ w.val → β w = 0
theorem cleanRem_anti {M rem₁ rem₂ : ℕ} (hle : rem₁ ≤ rem₂) {β : BitAssignment M}
    (h : cleanRem M rem₂ β) : cleanRem M rem₁ β := fun w hw ↦ h w (by omega)
def tailScr {M n : ℕ} (rComb : QRegister M n) (rem : ℕ) (h : rem ≤ M) : Fin rem → Wire n :=
  fun j ↦ rComb ⟨(M - rem) + j.val, by omega⟩
theorem tailScr_succ {M n : ℕ} (rComb : QRegister M n) (rem' : ℕ) (h : rem' + 1 ≤ M) :
    tailScr rComb (rem' + 1) h =
      Fin.cons (rComb ⟨M - (rem' + 1), by omega⟩) (tailScr rComb rem' (by omega)) :=
  InPlaceFullAddSlice.tailScr_succ rComb rem' h
theorem w3_projZeroAll_eq {n : ℕ} :
    ∀ (k : ℕ) (scr : Fin k → Wire n), InPlaceFullAddSlice.projZeroAll k scr = projZeroAll k scr
  | 0, _ => rfl
  | k + 1, _ => congrArg (_ * ·) (w3_projZeroAll_eq k _)
theorem projZeroAll_tailScr_sub {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M) (hle : rem₁ ≤ rem₂) :
    projZeroAll rem₁ (tailScr rComb rem₁ h₁) * projZeroAll rem₂ (tailScr rComb rem₂ h₂) =
      projZeroAll rem₂ (tailScr rComb rem₂ h₂) := by
  rw [← w3_projZeroAll_eq, ← w3_projZeroAll_eq]
  exact InPlaceFullAddSlice.projZeroAll_tailScr_sub rComb h₁ h₂ hle
def ValidCleanRem (M : ℕ) : ℕ → TempPhaseProg M → Prop
  | _, .nil | _, .cliff _ | _, .z _ => True
  | rem, .seq p₁ p₂ =>
      ∃ remMid : ℕ, remMid ≤ M ∧ ValidCleanRem M rem p₁ ∧ ValidCleanRem M remMid p₂ ∧
        (∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remMid (p₁.evalBits β))
  | rem, .tempAnd c₁ c₂ anc _ _ _ body =>
      M - rem ≤ anc.val ∧ let rem' := M - (anc.val + 1)
        ValidCleanRem M rem' body ∧ (∀ β₁ : BitAssignment M, cleanRem M rem' β₁ →
          body.evalBits β₁ c₁ = β₁ c₁ ∧ body.evalBits β₁ c₂ = β₁ c₂ ∧
            body.evalBits β₁ anc = β₁ anc)
theorem eval_onRegister_prog_ket {M n : ℕ} (rComb : QRegister M n)
    (p : TempPhaseProg M) (β : BitAssignment n) :
    let γ : BitAssignment M := fun idx ↦ β (rComb idx)
    ((p.onRegister rComb).toToffCircuit).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (p.evalSign γ).val) • ket (writeRegProg β rComb (p.evalBits γ)) := by
  intro γ
  rw [← (p.onRegister rComb).toSlice_toToffCircuit, ← p.toSlice_onRegister,
    ← p.toSlice_evalSign, ← p.toSlice_evalBits]
  exact InPlaceFullAddSlice.eval_onRegister_prog_ket rComb p.toSlice β
theorem RealizesCleanUnitary_seq_asym {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : RealizesCleanUnitary v P₁ c₁ U₁) (h₂ : RealizesCleanUnitary v P₂ c₂ U₂)
    (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) :
    RealizesCleanUnitary v P₁ (.seq c₁ c₂) (U₂ * U₁) :=
  InPlaceFullAddSlice.RealizesCleanUnitary_seq_asym hP₁ hP₂ h₁ h₂ hclean
private theorem validCleanRem_toSlice {M : ℕ} : ∀ (p : TempPhaseProg M) (rem : ℕ),
    ValidCleanRem M rem p → InPlaceFullAddSlice.ValidCleanRem M rem p.toSlice
  | .nil, _, _ | .cliff _, _, _ | .z _, _, _ => trivial
  | .seq p₁ p₂, rem, ⟨rm, hm, hv₁, hv₂, hp⟩ => ⟨rm, hm, validCleanRem_toSlice p₁ rem hv₁,
      validCleanRem_toSlice p₂ rm hv₂, fun β hβ ↦ (p₁.toSlice_evalBits β).symm ▸ hp β hβ⟩
  | .tempAnd _ _ _ _ _ _ b, _, ⟨ha, hvb, hpb⟩ => ⟨ha, validCleanRem_toSlice b _ hvb,
      fun β₁ hβ₁ ↦ (b.toSlice_evalBits β₁).symm ▸ hpb β₁ hβ₁⟩
theorem realizes_of_validCleanRem {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (p : TempPhaseProg M) (rem : ℕ)
    (hrem : rem ≤ M) (hv : ValidCleanRem M rem p) :
    RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
      ((p.onRegister rComb).toDyn v) (((p.onRegister rComb).toToffCircuit).eval) := by
  rw [← w3_projZeroAll_eq, ← (p.onRegister rComb).toSlice_toDyn,
    ← (p.onRegister rComb).toSlice_toToffCircuit, ← p.toSlice_onRegister]
  exact InPlaceFullAddSlice.realizes_of_validCleanRem v rComb p.toSlice rem hrem
    (validCleanRem_toSlice p rem hv)
theorem validCleanRem_mono {M : ℕ} : ∀ {p : TempPhaseProg M} {rem₁ rem₂ : ℕ}, rem₁ ≤ rem₂ →
    ValidCleanRem M rem₁ p → ValidCleanRem M rem₂ p
  | .nil, _, _, _, _ | .cliff _, _, _, _, _ | .z _, _, _, _, _ => trivial
  | .seq _ _, _, _, hle, ⟨rm, hm, hv₁, hv₂, hp⟩ =>
      ⟨rm, hm, validCleanRem_mono hle hv₁, hv₂, fun β hβ ↦ hp β (cleanRem_anti hle hβ)⟩
  | .tempAnd _ _ _ _ _ _ _, _, _, hle, ⟨_, hvB, hpB⟩ => ⟨by omega, hvB, hpB⟩
theorem PreservesStoreConst_toDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (p : TempPhaseProg n) : PreservesStoreConst (p.toDyn v) :=
  p.toSlice_toDyn v ▸ InPlaceFullAddSlice.PreservesStoreConst_toDyn v p.toSlice
private theorem w3_realizes_signedPerm_core {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kAct mClean mWork : ℕ} [NeZero (2 ^ n)] (v : Var) (rAct : QRegister kAct n)
    (rWork : QRegister mWork n) (hdisj : rAct.DisjointWires rWork) (hw_len : mClean ≤ mWork)
    (U : Unitary (2 ^ kAct)) (perm : BitAssignment kAct → BitAssignment kAct)
    (phase : BitAssignment kAct → ZMod 2)
    (hU : ∀ (α : BitAssignment kAct) (l : Fin (2 ^ kAct)), U.1 l ((basisBitsEquiv kAct).symm α) =
      if l = (basisBitsEquiv kAct).symm (perm α) then ((-1 : ℂ) ^ (phase α).val) else 0)
    (p : TempPhaseProg (kAct + mClean)) (hValid : ValidCleanRem (kAct + mClean) mClean p)
    (hBits : ∀ α : BitAssignment kAct, p.evalBits (padZeroBits α) = padZeroBits (perm α))
    (hSign : ∀ α : BitAssignment kAct, p.evalSign (padZeroBits α) = phase α) :
    let rSub : QRegister mClean n := rWork.slice 0 mClean (by omega)
    let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
    let dyn := (p.onRegister rComb).toDyn v
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork U dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧ dyn.count PrimitiveGate.T = 4 * p.countTempAnd := by
  intro rSub rComb dyn
  refine ⟨?_, TempPhaseProg.toDyn_count_toff v _, by simp [dyn]⟩
  have hrem : mClean ≤ kAct + mClean := Nat.le_add_left mClean kAct
  let P_work := projZeroAll mWork rWork.wires
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mWork _
  have hrSub (j : Fin mClean) : rSub j = rWork ⟨j.val, by omega⟩ :=
    (rWork.slice_apply 0 mClean (by omega) j).trans (congrArg rWork (Fin.ext (Nat.zero_add j.val)))
  have hsub : projZeroAll mClean (tailScr rComb mClean hrem) * P_work = P_work :=
    matrix_ext_ket fun β ↦ by
      simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
      by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
      · have hs (j : Fin mClean) : β (tailScr rComb mClean hrem j) = 0 := by
          dsimp only [tailScr, rComb]
          rw [show (⟨(kAct + mClean - mClean) + j.val, _⟩ : Fin (kAct + mClean)) =
            Fin.natAdd kAct j from Fin.ext (show (kAct + mClean - mClean) + j.val =
              kAct + j.val by omega), QRegister.concat_apply_right, hrSub j]
          exact hw _
        simp [hw, hs, ket_projZeroAll]
      · simp [hw]
  have hMono := RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose mClean _) hPw hsub
    (realizes_of_validCleanRem v rComb p mClean hrem hValid)
  have hUeq : ((p.onRegister rComb).toToffCircuit).eval.1 * P_work =
      (rAct.embedUnitary U).1 * P_work := matrix_ext_ket fun β ↦ by
    simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, eval_onRegister_prog_ket]
      let α : BitAssignment kAct := fun i ↦ β (rAct i)
      have hpad : (fun idx ↦ β (rComb idx)) = padZeroBits α := funext fun idx ↦
        Fin.addCases (fun i ↦ by simp [rComb, padZeroBits, α])
          (fun j ↦ by simp [rComb, padZeroBits, hrSub j, hw]) idx
      have hwComb : writeRegProg β rComb (padZeroBits (perm α)) =
          writeRegProg β rAct (perm α) := funext fun w ↦ by
        by_cases hmem : w ∈ Set.range rComb.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [writeRegProg_apply_reg]
          refine Fin.addCases (fun _ ↦ by simp [rComb, padZeroBits]) (fun j ↦ ?_) idx
          have hnotAct : rSub j ∉ Set.range rAct.wires := fun ⟨i, hi⟩ ↦
            hdisj.ne i ⟨j.val, by omega⟩ (hi.trans (hrSub j))
          have hrw : writeRegProg β rAct (perm α) (rSub j) = 0 :=
            (writeRegProg_apply_of_not_mem _ _ _ _ hnotAct).trans
              ((congrArg β (hrSub j)).trans (hw _))
          simp [rComb, padZeroBits, hrw]
        · have hnotAct : w ∉ Set.range rAct.wires := fun ⟨i, hi⟩ ↦
            hmem ⟨Fin.castAdd mClean i, (by simp [rComb] : rComb _ = rAct i).trans hi⟩
          rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem,
            writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
      rw [hpad, hBits α, hSign α, hwComb, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
      change _ = ∑ l : Fin (2 ^ kAct), U.1 l ((basisBitsEquiv kAct).symm α) • _
      simp_rw [hU α, ite_smul, zero_smul]
      simp [(basisBitsEquiv kAct).apply_symm_apply (perm α)]
    · simp [hw]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw hMono hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := PreservesStoreConst_toDyn v (p.onRegister rComb) M_obs
  refine ⟨M_out, hM_out, ?_⟩
  rw [← congrFun hM_out default, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val (hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default)
theorem realizes_phaseDiagUnitary_cleanWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kAct mClean mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : mClean ≤ mWork)
    (pred : BitAssignment kAct → ZMod 2)
    (p : TempPhaseProg (kAct + mClean))
    (hValid : ValidCleanRem (kAct + mClean) mClean p)
    (hBits : ∀ α : BitAssignment kAct, p.evalBits (padZeroBits α) = padZeroBits α)
    (hSign : ∀ α : BitAssignment kAct, p.evalSign (padZeroBits α) = pred α) :
    let rSub : QRegister mClean n := rWork.slice 0 mClean (by omega)
    let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
    let dyn := (p.onRegister rComb).toDyn v
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (phaseDiagUnitary pred) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 4 * p.countTempAnd :=
  w3_realizes_signedPerm_core v rAct rWork hdisj hw_len (phaseDiagUnitary pred) id pred
    (fun α l ↦ by
      by_cases hl : l = (basisBitsEquiv kAct).symm α
      · simp [hl, phaseDiagUnitary, (basisBitsEquiv kAct).apply_symm_apply α]
      · simp [phaseDiagUnitary, hl])
    p hValid hBits hSign
structure ScopedBlock (M rem : ℕ) (setup : BitAssignment M → BitAssignment M)
    (body : TempPhaseProg M) (p : TempPhaseProg M) : Prop where
  valid : ValidCleanRem M rem p
  bits : ∀ β : BitAssignment M, cleanRem M rem β → p.evalBits β = β
  sign : ∀ β : BitAssignment M, cleanRem M rem β → p.evalSign β = body.evalSign (setup β)
theorem ScopedBlock.cast_rem {M rem₁ rem₂ : ℕ} (h : rem₁ = rem₂)
    {s : BitAssignment M → BitAssignment M} {leaf p : TempPhaseProg M}
    (hb : ScopedBlock M rem₁ s leaf p) : ScopedBlock M rem₂ s leaf p := h ▸ hb
theorem ScopedBlock.z_kick {M rem : ℕ} (q : Wire M) : ScopedBlock M rem id (.z q) (.z q) :=
  ⟨trivial, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
theorem ScopedBlock.trans {M rem₁ rem₂ : ℕ} {s₁ s₂ : BitAssignment M → BitAssignment M}
    {leaf mid outer : TempPhaseProg M} (hOuter : ScopedBlock M rem₁ s₁ mid outer)
    (hInner : ScopedBlock M rem₂ s₂ leaf mid)
    (hClean : ∀ β, cleanRem M rem₁ β → cleanRem M rem₂ (s₁ β)) :
    ScopedBlock M rem₁ (s₂ ∘ s₁) leaf outer :=
  ⟨hOuter.valid, hOuter.bits, fun β hβ ↦ by
    rw [hOuter.sign β hβ, hInner.sign (s₁ β) (hClean β hβ), Function.comp_apply]⟩
def withCliffAlloc {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) : TempPhaseProg M :=
  .seq (.cliff c) (.seq body (.cliff c.inv))
@[simp] theorem withCliffAlloc_countTempAnd {M : ℕ} (c : CliffProg M)
    (body : TempPhaseProg M) : (withCliffAlloc c body).countTempAnd = body.countTempAnd := by
  simp [withCliffAlloc, TempPhaseProg.countTempAnd]
theorem ScopedBlock.withCliffAlloc_block {M rem remIn : ℕ} (hremIn : remIn ≤ M)
    (hle : remIn ≤ rem) (c : CliffProg M) (hc : c.SupportsBelow (M - remIn))
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M remIn sBody leaf body) :
    ScopedBlock M rem (sBody ∘ c.eval) leaf (withCliffAlloc c body) := by
  have hcl (β : BitAssignment M) (hβ : cleanRem M rem β) : cleanRem M remIn (c.eval β) :=
    fun w hw ↦ (c.eval_outside hc β w hw).trans (hβ w (by omega))
  exact ⟨⟨remIn, hremIn, trivial,
      ⟨0, Nat.zero_le M, hBody.valid, trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩, hcl⟩,
    fun β hβ ↦ by
      simp [withCliffAlloc, TempPhaseProg.evalBits, hBody.bits _ (hcl β hβ), c.inv_eval],
    fun β hβ ↦ by
      simp [withCliffAlloc, TempPhaseProg.evalSign, TempPhaseProg.evalBits,
        hBody.sign _ (hcl β hβ)]⟩
def withTempBit {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : TempPhaseProg M) : TempPhaseProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body
@[simp] theorem withTempBit_countTempAnd {M : ℕ} (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : TempPhaseProg M) :
    (withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body).countTempAnd = 1 + body.countTempAnd := rfl
private theorem w3_z2_cancel (x y : ZMod 2) : x + y + y = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
private theorem w3_split_bitsVal {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) := by
  rw [bitsVal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ by
    rw [Fin.val_succ, pow_succ]
    ring)
private theorem w3_mk_eq {M a b : ℕ} {ha : a < M} {hb : b < M} (h : a = b) :
    (⟨a, ha⟩ : Wire M) = ⟨b, hb⟩ := Fin.ext h
theorem w3_mk_ne {M a b : ℕ} {ha : a < M} {hb : b < M} (h : a ≠ b) :
    (⟨a, ha⟩ : Wire M) ≠ ⟨b, hb⟩ := Fin.ne_of_val_ne h
private theorem w3_ne_mk {M b : ℕ} {w : Wire M} {hb : b < M} (h : w.val ≠ b) :
    w ≠ ⟨b, hb⟩ := Fin.ne_of_val_ne h
theorem w3_ne_mk_of_lt {M b : ℕ} {w : Wire M} {hb : b < M} (h : w.val < b) :
    w ≠ ⟨b, hb⟩ := Fin.ne_of_val_ne (Nat.ne_of_lt h)
theorem w3_mk_ne_of_gt {M a : ℕ} {w : Wire M} {ha : a < M} (h : w.val < a) :
    (⟨a, ha⟩ : Wire M) ≠ w := Fin.ne_of_val_ne (Nat.ne_of_gt h)
private theorem w3_cleanRem_mk {M rem pos : ℕ} {hpos : pos < M} {β : BitAssignment M}
    (hβ : cleanRem M rem β) (hu : M - rem ≤ pos) : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ hu
private theorem w3_cleanRem_upd {M rem : ℕ} {β : BitAssignment M} {u : Wire M} {v : ZMod 2}
    (hu : u.val < M - rem) (hβ : cleanRem M rem β) : cleanRem M rem (Function.update β u v) :=
  fun w hw ↦ (Function.update_of_ne (wire_ne_of_gt (by omega)) _ _).trans (hβ w hw)
private theorem w3_cleanRem_upd_mk {M rem pos : ℕ} {hpos : pos < M} {β : BitAssignment M}
    {v : ZMod 2} (hu : pos < M - rem) (hβ : cleanRem M rem β) :
    cleanRem M rem (Function.update β ⟨pos, hpos⟩ v) := w3_cleanRem_upd hu hβ
private theorem w3_lt_ne_cur {M cur : ℕ} {w : Wire M} (hw : w.val < cur) {hc : cur < M} :
    (w = ⟨cur, hc⟩) = False := eq_false (w3_ne_mk_of_lt hw)
private theorem w3_cur_ne_lt {M cur : ℕ} {w : Wire M} (hw : w.val < cur) {hc : cur < M} :
    ((⟨cur, hc⟩ : Wire M) = w) = False := eq_false (w3_mk_ne_of_gt hw)
private theorem w3_lt_ne_add {M cur : ℕ} {w : Wire M} (hw : w.val < cur) {k : ℕ}
    {hk : cur + k < M} : (w = ⟨cur + k, hk⟩) = False :=
  eq_false (w3_ne_mk_of_lt (Nat.lt_of_lt_of_le hw (Nat.le_add_right cur k)))
private theorem w3_add_ne_lt {M cur : ℕ} {w : Wire M} (hw : w.val < cur) {k : ℕ}
    {hk : cur + k < M} : ((⟨cur + k, hk⟩ : Wire M) = w) = False :=
  eq_false (w3_mk_ne_of_gt (Nat.lt_of_lt_of_le hw (Nat.le_add_right cur k)))
private theorem w3_fn_ne_add {M cur : ℕ} {ι : Type*} {f : ι → Wire M}
    (hf : ∀ i, (f i).val < cur) {k : ℕ} {hk : cur + k < M} (i : ι) :
    (f i = ⟨cur + k, hk⟩) = False := w3_lt_ne_add (hf i)
private theorem w3_add_ne_fn {M cur : ℕ} {ι : Type*} {f : ι → Wire M}
    (hf : ∀ i, (f i).val < cur) {k : ℕ} {hk : cur + k < M} (i : ι) :
    ((⟨cur + k, hk⟩ : Wire M) = f i) = False := w3_add_ne_lt (hf i)
private theorem w3_withCliffAlloc_cur {M : ℕ} (cur curIn : ℕ) (hIn : curIn ≤ M) (hle : cur ≤ curIn)
    (c : CliffProg M) (hc : c.SupportsBelow curIn) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - curIn) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ c.eval) leaf (withCliffAlloc c body) :=
  ScopedBlock.withCliffAlloc_block (by omega) (by omega) c
    (by simpa [show M - (M - curIn) = curIn by omega] using hc) hBody
theorem ScopedBlock.withTempBit_block {M : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < pos) (hc₂ : c₂.val < pos)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (pos + 1)) sBody leaf body) : ScopedBlock M (M - pos)
    (fun β ↦ sBody (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂))) leaf (withTempBit c₁ c₂
    ⟨pos, hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) body) := by
  have hcl (β : BitAssignment M) (hβ : cleanRem M (M - pos) β) :
      cleanRem M (M - (pos + 1)) (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)) :=
    w3_cleanRem_upd_mk (by omega) (cleanRem_anti (by omega) hβ)
  refine ⟨⟨show M - (M - pos) ≤ pos by omega, hBody.valid,
    fun β₁ hβ₁ ↦ by simp [hBody.bits β₁ hβ₁]⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · have hanc0 := w3_cleanRem_mk (hpos := hpos) hβ (by omega)
    let β₁ := Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)
    simp only [withTempBit, TempPhaseProg.evalBits, hanc0, zero_add]
    change Function.update (body.evalBits β₁) ⟨pos, hpos⟩ _ = β
    rw [hBody.bits β₁ (hcl β hβ)]
    funext w
    rcases eq_or_ne w ⟨pos, hpos⟩ with rfl | hw
    · simp [β₁, Function.update_of_ne (w3_ne_mk_of_lt hc₁),
        Function.update_of_ne (w3_ne_mk_of_lt hc₂), CharTwo.add_self_eq_zero, hanc0]
    · simp [β₁, Function.update_of_ne hw]
  · simpa [withTempBit, TempPhaseProg.evalSign, w3_cleanRem_mk (hpos := hpos) hβ (by omega)]
      using hBody.sign _ (hcl β hβ)
def andXor {M : ℕ} (c₁ c₂ target anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (hat : anc ≠ target) : TempPhaseProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a
    (.cnot anc target hat)
@[simp] theorem andXor_countTempAnd {M : ℕ} (c₁ c₂ target anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ target) :
    (andXor c₁ c₂ target anc h₁₂ h₁a h₂a hat).countTempAnd = 1 := rfl
@[simp] theorem andXor_evalSign {M : ℕ} (c₁ c₂ target anc : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ target) (β : BitAssignment M) :
    (andXor c₁ c₂ target anc h₁₂ h₁a h₂a hat).evalSign β = 0 := rfl
theorem andXor_valid_and_eval {M rem : ℕ}
    (c₁ c₂ target anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ target) (h₂t : c₂ ≠ target)
    (hc₁ : c₁.val < anc.val) (hc₂ : c₂.val < anc.val) (ht : target.val < anc.val)
    (hanc_rem : M - rem ≤ anc.val) :
    let p := andXor c₁ c₂ target anc h₁₂
      (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) (wire_ne_of_gt ht)
    ValidCleanRem M rem p ∧
      ∀ β : BitAssignment M, cleanRem M rem β →
        p.evalBits β = Function.update β target (β target + β c₁ * β c₂) := by
  intro p
  have hat : anc ≠ target := wire_ne_of_gt ht
  refine ⟨⟨hanc_rem, trivial, fun _ _ ↦ by
    simp [TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval, Function.update_of_ne h₁t,
      Function.update_of_ne h₂t, Function.update_of_ne hat]⟩, fun β hβ ↦ funext fun w ↦ ?_⟩
  have hanc0 : β anc = 0 := hβ anc hanc_rem
  rcases eq_or_ne w anc with rfl | hw_a
  · simp [p, andXor, TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval, hanc0,
      Function.update_of_ne h₁t, Function.update_of_ne h₂t, Function.update_of_ne hat,
      Function.update_of_ne (wire_ne_of_lt hc₁), Function.update_of_ne (wire_ne_of_lt hc₂),
      CharTwo.add_self_eq_zero]
  · rcases eq_or_ne w target with rfl | hw_t
    · simp [p, andXor, TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval, hanc0,
        Function.update_of_ne hw_a]
    · simp [p, andXor, TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval,
        Function.update_of_ne hw_a, Function.update_of_ne hw_t]
theorem halfAdd_val_eq (x y : ZMod 2) : (x + y).val + 2 * (x * y).val = x.val + y.val := by
  decide +revert
def withFullAdd {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b cin : Wire M) (hab : a ≠ b)
    (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let sW : Wire M := ⟨cur, by omega⟩
  let cW : Wire M := ⟨cur + 1, by omega⟩
  withCliffAlloc (.seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm))
    (withTempBit a b cW hab (w3_ne_mk_of_lt (by omega)) (w3_ne_mk_of_lt (by omega))
      (withCliffAlloc (.seq (.cnot cin b hbc.symm) (.seq (.cnot cin a hac.symm)
        (.seq (.cnot cin cW (w3_ne_mk_of_lt (by omega)))
          (.seq (.cnot a sW (w3_ne_mk_of_lt ha))
            (.seq (.cnot b sW (w3_ne_mk_of_lt hb)) (.cnot cin sW (w3_ne_mk_of_lt hc)))))))
        body))
@[simp] theorem withFullAdd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur)
    (hb : b.val < cur) (hc : cin.val < cur) (body : TempPhaseProg M) :
    (withFullAdd cur hcur a b cin hab hac hbc ha hb hc body).countTempAnd =
      1 + body.countTempAnd := by simp [withFullAdd]
def fullAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b cin : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update (Function.update β ⟨cur, by omega⟩ (β a + β b + β cin))
    ⟨cur + 1, by omega⟩ (β cin + (β a + β cin) * (β b + β cin))
theorem fullAdd_val_eq (x y z : ZMod 2) :
    (x + y + z).val + 2 * (z + (x + z) * (y + z)).val = x.val + y.val + z.val := by decide +revert
private theorem w3_fullAdd_clean {M cur rem : ℕ} (hcur : cur + 2 ≤ M)
    (a b c : Wire M) {β : BitAssignment M} (hrem : cur + 2 ≤ M - rem) (hβ : cleanRem M rem β) :
    cleanRem M rem (fullAddSetup cur hcur a b c β) :=
  w3_cleanRem_upd_mk (by omega) (w3_cleanRem_upd_mk (by omega) hβ)
private theorem w3_fullAdd_lt {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b c w : Wire M)
    (β : BitAssignment M) (hw : w.val < cur) : fullAddSetup cur hcur a b c β w = β w := by
  dsimp [fullAddSetup]
  rw [Function.update_of_ne (w3_ne_mk_of_lt (by omega)),
    Function.update_of_ne (w3_ne_mk_of_lt hw)]
private theorem w3_fullAdd_sum {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b c : Wire M)
    (β : BitAssignment M) : fullAddSetup cur hcur a b c β ⟨cur, by omega⟩ = β a + β b + β c := by
  dsimp [fullAddSetup]
  rw [Function.update_of_ne (w3_mk_ne (by omega)), Function.update_self]
theorem ScopedBlock.withFullAdd_block {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur)
    (hb : b.val < cur) (hc : cin.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 2)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ fullAddSetup cur hcur a b cin) leaf
    (withFullAdd cur hcur a b cin hab hac hbc ha hb hc body) := by
  let sumWire : Wire M := ⟨cur, by omega⟩
  let coutWire : Wire M := ⟨cur + 1, by omega⟩
  let cPre : CliffProg M := .seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm)
  let cInner : CliffProg M := .seq (.cnot cin b hbc.symm) (.seq (.cnot cin a hac.symm)
    (.seq (.cnot cin coutWire (w3_ne_mk_of_lt (by omega)))
      (.seq (.cnot a sumWire (w3_ne_mk_of_lt ha))
        (.seq (.cnot b sumWire (w3_ne_mk_of_lt hb)) (.cnot cin sumWire (w3_ne_mk_of_lt hc))))))
  have h1 := w3_withCliffAlloc_cur (cur + 2) (cur + 2) hcur le_rfl cInner (by
    dsimp [cInner, sumWire, coutWire, CliffProg.SupportsBelow]
    omega) hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) (cur + 1) hcur a b hab (by omega) (by omega) h1
  have h3 := w3_withCliffAlloc_cur cur (cur + 1) (by omega) (by omega) cPre (by
    dsimp [cPre, CliffProg.SupportsBelow]
    omega) h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withFullAdd]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, fullAddSetup, cPre, cInner, CliffProg.eval]
  congr 2
  rw [show (⟨cur + 1, hcur⟩ : Wire M) = coutWire from rfl,
    show (⟨cur, _⟩ : Wire M) = sumWire from rfl]
  have hs0 : β sumWire = 0 := w3_cleanRem_mk hβ (by omega)
  have has : a ≠ sumWire := w3_ne_mk_of_lt ha
  have hbs : b ≠ sumWire := w3_ne_mk_of_lt hb
  have hcs : cin ≠ sumWire := w3_ne_mk_of_lt hc
  have hacout : a ≠ coutWire := w3_ne_mk_of_lt (by omega)
  have hbcout : b ≠ coutWire := w3_ne_mk_of_lt (by omega)
  have hccout : cin ≠ coutWire := w3_ne_mk_of_lt (by omega)
  have hsc : sumWire ≠ coutWire := w3_mk_ne (by omega)
  funext w
  rcases eq_or_ne w coutWire with rfl | hwc
  · simp only [Function.update_self, Function.update_of_ne hsc.symm, Function.update_of_ne hacout,
      Function.update_of_ne hacout.symm, Function.update_of_ne hbcout,
      Function.update_of_ne hbcout.symm, Function.update_of_ne hccout, Function.update_of_ne hab,
      Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
      Function.update_of_ne hbc.symm]
    ring
  · rcases eq_or_ne w sumWire with rfl | hws
    · simp only [hs0, zero_add, w3_z2_cancel, Function.update_self, Function.update_of_ne hsc,
        Function.update_of_ne has.symm, Function.update_of_ne hbs, Function.update_of_ne hbs.symm,
        Function.update_of_ne hcs, Function.update_of_ne hacout, Function.update_of_ne hacout.symm,
        Function.update_of_ne hbcout, Function.update_of_ne hbcout.symm,
        Function.update_of_ne hccout, Function.update_of_ne hab, Function.update_of_ne hab.symm,
        Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm]
    · rcases eq_or_ne w a with rfl | hwa
      · simp only [w3_z2_cancel, Function.update_self, Function.update_of_ne has,
          Function.update_of_ne hacout, Function.update_of_ne hbcout,
          Function.update_of_ne hccout, Function.update_of_ne hab,
          Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
          Function.update_of_ne hbc.symm]
      · rcases eq_or_ne w b with rfl | hwb
        · simp only [w3_z2_cancel, Function.update_self, Function.update_of_ne hbs,
            Function.update_of_ne hbcout, Function.update_of_ne hccout,
            Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
            Function.update_of_ne hbc.symm]
        · simp only [Function.update_of_ne hwc, Function.update_of_ne hws,
            Function.update_of_ne hwa, Function.update_of_ne hwb]
def withLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let out : Wire M := ⟨cur, by omega⟩
  withCliffAlloc (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))
    (withTempBit a b out hab (w3_ne_mk_of_lt ha) (w3_ne_mk_of_lt hb)
      (withCliffAlloc (.seq (.cnot prev b hbp.symm)
        (.seq (.cnot b a hab.symm) (.cnot prev out (w3_ne_mk_of_lt hp)))) body))
@[simp] theorem withLtStep_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (hp : prev.val < cur) (hbp : b ≠ prev) (body : TempPhaseProg M) :
    (withLtStep cur hcur a b prev hab ha hb hp hbp body).countTempAnd =
      1 + body.countTempAnd := by simp [withLtStep]
def ltStepSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update β ⟨cur, by omega⟩ (β prev + (β a + β b) * (β b + β prev))
theorem ltStep_bit_iff (a b prev : ZMod 2) :
    (prev + (a + b) * (b + prev)) = 1 ↔ (a.val < b.val ∨ (a.val = b.val ∧ prev = 1)) := by
  decide +revert
theorem ScopedBlock.withLtStep_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b) (hap : a ≠ prev) (ha : a.val < cur) (hb : b.val < cur)
    (hp : prev.val < cur) (hbp : b ≠ prev) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ ltStepSetup cur hcur a b prev) leaf
    (withLtStep cur hcur a b prev hab ha hb hp hbp body) := by
  let out : Wire M := ⟨cur, by omega⟩
  let cPre : CliffProg M := .seq (.cnot b a hab.symm) (.cnot prev b hbp.symm)
  let cPost : CliffProg M := .seq (.cnot prev b hbp.symm)
    (.seq (.cnot b a hab.symm) (.cnot prev out (w3_ne_mk_of_lt hp)))
  have h1 := w3_withCliffAlloc_cur (cur + 1) (cur + 1) hcur le_rfl cPost
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, show cur < cur + 1 by omega⟩ hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur a b hab ha hb h1
  have h3 := w3_withCliffAlloc_cur cur cur (by omega) le_rfl cPre ⟨⟨hb, ha⟩, hp, hb⟩ h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withLtStep]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, ltStepSetup, cPre, cPost, CliffProg.eval]
  congr 2
  rw [show (⟨cur, hcur⟩ : Wire M) = out from rfl]
  have hao : a ≠ out := w3_ne_mk_of_lt ha
  have hbo : b ≠ out := w3_ne_mk_of_lt hb
  have hpo : prev ≠ out := w3_ne_mk_of_lt hp
  funext w
  rcases eq_or_ne w out with rfl | hwo
  · simp only [Function.update_self, Function.update_of_ne hao, Function.update_of_ne hao.symm,
      Function.update_of_ne hbo, Function.update_of_ne hbo.symm, Function.update_of_ne hpo,
      Function.update_of_ne hab, Function.update_of_ne hab.symm, Function.update_of_ne hap.symm,
      Function.update_of_ne hbp.symm]
    ring
  · rcases eq_or_ne w a with rfl | hwa
    · simp only [w3_z2_cancel, Function.update_self, Function.update_of_ne hao,
        Function.update_of_ne hbo, Function.update_of_ne hpo, Function.update_of_ne hab,
        Function.update_of_ne hab.symm, Function.update_of_ne hap.symm,
        Function.update_of_ne hbp.symm]
    · rcases eq_or_ne w b with rfl | hwb
      · simp only [w3_z2_cancel, Function.update_self, Function.update_of_ne hbo,
          Function.update_of_ne hpo, Function.update_of_ne hab.symm,
          Function.update_of_ne hap.symm, Function.update_of_ne hbp.symm]
      · simp only [Function.update_of_ne hwo, Function.update_of_ne hwa,
          Function.update_of_ne hwb]
def withLtCompLoop {M : ℕ} : (W cur : ℕ) → cur + W + 1 ≤ M → (a b : Fin W → Wire M) →
    (∀ j, a j ≠ b j) → (∀ j, (a j).val < cur) → (∀ j, (b j).val < cur) →
    TempPhaseProg M → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, body => body
  | W + 1, cur, hcur, a, b, hab, ha, hb, body =>
      withLtStep (cur + 1) (by omega) (a 0) (b 0) ⟨cur, by omega⟩ (hab 0)
        (lt_trans (ha 0) (by omega)) (lt_trans (hb 0) (by omega)) (show cur < cur + 1 by omega)
        (w3_ne_mk_of_lt (hb 0))
        (withLtCompLoop W (cur + 1) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          (fun j ↦ hab j.succ) (fun j ↦ lt_trans (ha j.succ) (by omega))
          (fun j ↦ lt_trans (hb j.succ) (by omega)) body)
@[simp] theorem withLtCompLoop_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
      (withLtCompLoop W cur hcur a b hab ha hb body).countTempAnd = W + body.countTempAnd
  | 0, _, _, _, _, _, _, _, _ => by simp [withLtCompLoop]
  | W + 1, _, _, _, _, _, _, _, _ => by
      simp only [withLtCompLoop, withLtStep_countTempAnd, withLtCompLoop_countTempAnd]
      omega
theorem ScopedBlock.withLtCompLoop_block {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (leaf body : TempPhaseProg M)
      (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (cur + W + 1)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - (cur + 1)) (fun β ↦ sBody (setup β)) leaf
          (withLtCompLoop W cur hcur a b hab ha hb body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - (cur + 1)) β →
          cleanRem M (M - (cur + W + 1)) (setup β) ∧ (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
          ((setup β ⟨cur + W, by omega⟩ = 1) ↔
            (bitsVal (fun j ↦ β (a j)) < bitsVal (fun j ↦ β (b j)) ∨
              (bitsVal (fun j ↦ β (a j)) = bitsVal (fun j ↦ β (b j)) ∧ β ⟨cur, by omega⟩ = 1)))
  | 0, _, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hβ ↦ ⟨hβ, fun _ _ ↦ rfl, by simp [bitsVal]⟩⟩
  | W + 1, cur, hcur, a, b, hab, ha, hb, leaf, body, sBody, hBody => by
      let prev : Wire M := ⟨cur, by omega⟩
      obtain ⟨setupInner, hInner, hSpecInner⟩ := ScopedBlock.withLtCompLoop_block W (cur + 1)
        (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ) (fun j ↦ hab j.succ)
        (fun j ↦ lt_trans (ha j.succ) (by omega)) (fun j ↦ lt_trans (hb j.succ) (by omega))
        leaf body sBody (hBody.cast_rem (by omega))
      have hStep := ScopedBlock.withLtStep_block (M := M) (cur + 1) (by omega) (a 0) (b 0) prev
        (hab 0) (w3_ne_mk_of_lt (ha 0)) (lt_trans (ha 0) (by omega)) (lt_trans (hb 0) (by omega))
        (show cur < cur + 1 by omega) (w3_ne_mk_of_lt (hb 0)) hInner
      refine ⟨fun β ↦ setupInner (ltStepSetup (cur + 1) (by omega) (a 0) (b 0) prev β),
        hStep, fun β hβ ↦ ?_⟩
      let β₁ := ltStepSetup (cur + 1) (by omega) (a 0) (b 0) prev β
      obtain ⟨hcl, hbelow, hlt_ih⟩ := hSpecInner β₁
        (w3_cleanRem_upd_mk (by omega) (cleanRem_anti (by omega) hβ))
      have ha_fun : (fun j : Fin W ↦ β₁ (a j.succ)) = fun j ↦ β (a j.succ) := funext fun j ↦
        Function.update_of_ne (w3_ne_mk_of_lt (lt_trans (ha j.succ) (by omega))) _ _
      have hb_fun : (fun j : Fin W ↦ β₁ (b j.succ)) = fun j ↦ β (b j.succ) := funext fun j ↦
        Function.update_of_ne (w3_ne_mk_of_lt (lt_trans (hb j.succ) (by omega))) _ _
      have hbit1 : β₁ ⟨cur + 1, by omega⟩ = 1 ↔ ((β (a 0)).val < (β (b 0)).val ∨
          ((β (a 0)).val = (β (b 0)).val ∧ β ⟨cur, by omega⟩ = 1)) := by
        simpa [β₁, ltStepSetup, prev] using ltStep_bit_iff (β (a 0)) (β (b 0)) (β ⟨cur, by omega⟩)
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcl,
        fun w hw ↦ (hbelow w (by omega)).trans
          (Function.update_of_ne (w3_ne_mk_of_lt (by omega)) _ _), ?_⟩
      dsimp only
      have := ZMod.val_lt (β (a 0))
      have := ZMod.val_lt (β (b 0))
      rw [show (⟨cur + (W + 1), _⟩ : Wire M) = ⟨cur + 1 + W, by omega⟩ from w3_mk_eq (by omega),
        hlt_ih, ha_fun, hb_fun, hbit1,
        w3_split_bitsVal (fun j ↦ β (a j)), w3_split_bitsVal (fun j ↦ β (b j))]
      by_cases hp1 : β ⟨cur, by omega⟩ = 1
      · simp only [hp1, and_true]
        omega
      · simp only [hp1, and_false, or_false]
        omega
def withUnarySplit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur) (hsel : sel.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let hiW : Wire M := ⟨cur, by omega⟩
  withTempBit loWire sel hiW hlo_sel (w3_ne_mk_of_lt hlo) (w3_ne_mk_of_lt hsel)
    (withCliffAlloc (.cnot hiW loWire (w3_mk_ne_of_gt hlo)) body)
@[simp] theorem withUnarySplit_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (loWire sel : Wire M) (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur)
    (hsel : sel.val < cur) (body : TempPhaseProg M) :
    (withUnarySplit cur hcur loWire sel hlo_sel hlo hsel body).countTempAnd =
      1 + body.countTempAnd := by simp [withUnarySplit]
def unarySplitSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update (Function.update β ⟨cur, by omega⟩ (β loWire * β sel))
    loWire (β loWire + β loWire * β sel)
theorem ScopedBlock.withUnarySplit_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (loWire sel : Wire M) (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur)
    (hsel : sel.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ unarySplitSetup cur hcur loWire sel) leaf
    (withUnarySplit cur hcur loWire sel hlo_sel hlo hsel body) := by
  let hiWire : Wire M := ⟨cur, by omega⟩
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur loWire sel hlo_sel hlo hsel
    (w3_withCliffAlloc_cur (cur + 1) (cur + 1) hcur le_rfl
      (.cnot hiWire loWire (w3_mk_ne_of_gt hlo)) ⟨show cur < cur + 1 by omega, by omega⟩ hBody)
  refine ⟨h2.valid, h2.bits, fun β hβ ↦ ?_⟩
  dsimp only [withUnarySplit]
  rw [h2.sign β hβ]
  dsimp only [Function.comp_apply, unarySplitSetup, hiWire, CliffProg.eval]
  congr 2
  rw [show (⟨cur, hcur⟩ : Wire M) = hiWire from rfl]
  funext w
  rcases eq_or_ne w loWire with rfl | hwl
  · simp only [Function.update_self]
    rw [Function.update_of_ne (w3_ne_mk_of_lt hlo : w ≠ hiWire)]
  · simp only [Function.update_of_ne hwl]
def withUnarySplitRange {M : ℕ} (base L : ℕ) (sel : Wire M) (hsel : sel.val < base)
    (hcur : base + 2 * L ≤ M) : (K : ℕ) → K ≤ L → TempPhaseProg M → TempPhaseProg M
  | 0, _, body => body
  | K + 1, hK, body =>
      let idx := L - (K + 1)
      withUnarySplit (base + L + idx) (by omega) ⟨base + idx, by omega⟩ sel
        (wire_ne_of_gt (show sel.val < base + idx by omega))
        (show base + idx < base + L + idx by omega) (by omega)
        (withUnarySplitRange base L sel hsel hcur K (by omega) body)
@[simp] theorem withUnarySplitRange_countTempAnd {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L) (body : TempPhaseProg M),
      (withUnarySplitRange base L sel hsel hcur K hK body).countTempAnd = K + body.countTempAnd
  | 0, _, _ => by simp [withUnarySplitRange]
  | K + 1, _, body => by
      simp only [withUnarySplitRange, withUnarySplit_countTempAnd,
        withUnarySplitRange_countTempAnd base L sel hsel hcur K _ body]
      omega
theorem ScopedBlock.withUnarySplitRange_block {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L) (leaf body : TempPhaseProg M)
      (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (base + 2 * L)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - (base + 2 * L - K)) (fun β ↦ sBody (setup β)) leaf
          (withUnarySplitRange base L sel hsel hcur K hK body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - (base + 2 * L - K)) β →
          cleanRem M (M - (base + 2 * L)) (setup β) ∧
          (∀ w : Wire M, (w.val < base + (L - K) ∨
              (base + L ≤ w.val ∧ w.val < base + L + (L - K))) →
            setup β w = β w) ∧
          (∀ (i : ℕ) (_ : L - K ≤ i) (hhi : i < L),
            setup β ⟨base + i, by omega⟩ = β ⟨base + i, by omega⟩ + β ⟨base + i, by omega⟩ * β sel ∧
            setup β ⟨base + L + i, by omega⟩ = β ⟨base + i, by omega⟩ * β sel)
  | 0, _, _, _, _, hBody => ⟨id, hBody, fun _ hβ ↦
      ⟨hβ, fun _ _ ↦ rfl, fun _ hlo hhi ↦ absurd (lt_of_le_of_lt hlo hhi) (by omega)⟩⟩
  | K + 1, hK, leaf, body, sBody, hBody => by
      let idx := L - (K + 1)
      let pos := base + L + idx
      have hidx : idx = L - (K + 1) := rfl
      have hpos : pos = base + L + idx := rfl
      obtain ⟨setupInner, hInner, hSpecInner⟩ := ScopedBlock.withUnarySplitRange_block base L
        sel hsel hcur K (by omega) leaf body sBody hBody
      have hStep := ScopedBlock.withUnarySplit_block (M := M) pos (by omega) ⟨base + idx, by omega⟩
        sel (wire_ne_of_gt (show sel.val < base + idx by omega))
        (show base + idx < pos by omega) (by omega) (hInner.cast_rem (by omega))
      refine ⟨fun β ↦ setupInner (unarySplitSetup pos (by omega) ⟨base + idx, by omega⟩ sel β),
        hStep.cast_rem (by omega), fun β hβ ↦ ?_⟩
      let β₁ := unarySplitSetup pos (by omega) ⟨base + idx, by omega⟩ sel β
      obtain ⟨hcl, hbelow, hsplit⟩ := hSpecInner β₁
        (w3_cleanRem_upd_mk (by omega) (w3_cleanRem_upd_mk (by omega)
          (cleanRem_anti (by omega) hβ)))
      have hβ₁_ne {w : Wire M} (h1 : w.val ≠ base + idx) (h2 : w.val ≠ pos) : β₁ w = β w :=
        (Function.update_of_ne (w3_ne_mk h1) _ _).trans (Function.update_of_ne (w3_ne_mk h2) _ _)
      refine ⟨hcl, fun w hw ↦ (hbelow w
        (hw.imp (fun _ ↦ by omega) fun ⟨h1, _⟩ ↦ ⟨h1, by omega⟩)).trans
        (hβ₁_ne (by omega) (by omega)), fun i hlo hhi ↦ ?_⟩
      dsimp only
      rcases eq_or_ne i idx with rfl | hi
      · rw [hbelow _ (Or.inl (show base + idx < base + (L - K) by omega)),
          hbelow _ (Or.inr ⟨show base + L ≤ base + L + idx by omega,
            show base + L + idx < base + L + (L - K) by omega⟩)]
        exact ⟨Function.update_self _ _ _,
          (Function.update_of_ne (w3_mk_ne (by omega)) _ _).trans (Function.update_self _ _ _)⟩
      · obtain ⟨h1, h2⟩ := hsplit i (by omega) hhi
        rw [h1, h2, hβ₁_ne (show base + i ≠ base + idx by omega) (show base + i ≠ pos by omega),
          hβ₁_ne (by omega) (by omega)]
        exact ⟨rfl, rfl⟩
def rippleAddCarryWires {M : ℕ} : (W cur : ℕ) → cur + 2 * W ≤ M → Wire M → Fin (W + 1) → Wire M
  | 0, _, _, cin => fun _ ↦ cin
  | W + 1, cur, hcur, _ =>
      Fin.cons ⟨cur, by omega⟩ (rippleAddCarryWires W (cur + 2) (by omega) ⟨cur + 1, by omega⟩)
theorem rippleAddCarryWires_bounds {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
    (cin : Wire M), cin.val < cur → (∀ k : Fin (W + 1), (rippleAddCarryWires W cur hcur cin
    k).val < cur + 2 * W) ∧ (∀ k : Fin (W + 1), cin.val ≤ (rippleAddCarryWires W cur hcur cin
    k).val)
  | 0, _, _, _, hcin => ⟨fun _ ↦ hcin, fun _ ↦ le_rfl⟩
  | W + 1, cur, _, _, hcin => by
      obtain ⟨hhi, hlo⟩ := rippleAddCarryWires_bounds (M := M) W (cur + 2) (by omega)
        ⟨cur + 1, by omega⟩ (show cur + 1 < cur + 2 by omega)
      exact ⟨Fin.cases (show cur < _ by omega) fun i ↦ lt_of_lt_of_le (hhi i) (by omega),
        Fin.cases (Nat.le_of_lt hcin) fun i ↦ le_trans (show _ ≤ cur + 1 by omega) (hlo i)⟩
def withRippleAddCarry {M : ℕ} : (W cur : ℕ) → cur + 2 * W ≤ M → (a b : Fin W → Wire M) →
    (cin : Wire M) → (∀ j, a j ≠ b j) → (∀ j, a j ≠ cin) → (∀ j, b j ≠ cin) →
    (∀ j, (a j).val < cur) → (∀ j, (b j).val < cur) → cin.val < cur →
    TempPhaseProg M → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _, _, _, body => body
  | W + 1, cur, hcur, a, b, cin, hab, hac, hbc, ha, hb, hc, body =>
      withFullAdd cur (by omega) (a 0) (b 0) cin (hab 0) (hac 0) (hbc 0) (ha 0) (hb 0) hc
        (withRippleAddCarry W (cur + 2) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          ⟨cur + 1, by omega⟩ (fun j ↦ hab j.succ)
          (fun j ↦ w3_ne_mk_of_lt (lt_trans (ha j.succ) (by omega)))
          (fun j ↦ w3_ne_mk_of_lt (lt_trans (hb j.succ) (by omega)))
          (fun j ↦ lt_trans (ha j.succ) (by omega)) (fun j ↦ lt_trans (hb j.succ) (by omega))
          (show cur + 1 < cur + 2 by omega) body)
@[simp] theorem withRippleAddCarry_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 2 * W ≤ M) (a b : Fin W → Wire M) (cin : Wire M)
      (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (hc : cin.val < cur)
      (body : TempPhaseProg M),
      (withRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc body).countTempAnd =
        W + body.countTempAnd
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [withRippleAddCarry]
  | W + 1, _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [withRippleAddCarry, withFullAdd_countTempAnd, withRippleAddCarry_countTempAnd]
      omega
theorem ScopedBlock.withRippleAddCarry_block {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
    (a b : Fin W → Wire M) (cin : Wire M) (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin)
    (hbc : ∀ j, b j ≠ cin) (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur)
    (hc : cin.val < cur) (leaf body : TempPhaseProg M)
    (sBody : BitAssignment M → BitAssignment M), ScopedBlock M (M - (cur + 2 * W)) sBody leaf
    body → ∃ setup : BitAssignment M → BitAssignment M, ScopedBlock M (M - cur)
    (fun β ↦ sBody (setup β)) leaf
    (withRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc body) ∧ ∀ β : BitAssignment M,
    cleanRem M (M - cur) β → cleanRem M (M - (cur + 2 * W)) (setup β) ∧
    (∀ w : Wire M, w.val < cur → setup β w = β w) ∧ bitsVal
    (fun k ↦ setup β (rippleAddCarryWires W cur hcur cin k)) = bitsVal (fun j ↦ β (a j)) +
    bitsVal (fun j ↦ β (b j)) + (β cin).val
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hβ ↦ ⟨by simpa using hβ, fun _ _ ↦ rfl,
        by simp [rippleAddCarryWires, bitsVal]⟩⟩
  | W + 1, cur, hcur, a, b, cin, hab, hac, hbc, ha, hb, hc, leaf, body, sBody, hBody => by
      let cinNext : Wire M := ⟨cur + 1, by omega⟩
      obtain ⟨setupInner, hInner, hSpecInner⟩ := ScopedBlock.withRippleAddCarry_block W (cur + 2)
        (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ) cinNext (fun j ↦ hab j.succ)
        (fun j ↦ w3_ne_mk_of_lt (lt_trans (ha j.succ) (by omega)))
        (fun j ↦ w3_ne_mk_of_lt (lt_trans (hb j.succ) (by omega)))
        (fun j ↦ lt_trans (ha j.succ) (by omega)) (fun j ↦ lt_trans (hb j.succ) (by omega))
        (show cur + 1 < cur + 2 by omega) leaf body sBody (hBody.cast_rem (by omega))
      refine ⟨fun β ↦ setupInner (fullAddSetup cur (by omega) (a 0) (b 0) cin β),
        ScopedBlock.withFullAdd_block (M := M) cur (by omega) (a 0) (b 0) cin (hab 0) (hac 0)
          (hbc 0) (ha 0) (hb 0) hc hInner, fun β hβ ↦ ?_⟩
      let β₁ := fullAddSetup cur (by omega) (a 0) (b 0) cin β
      obtain ⟨hcl, hbelow, hsum_ih⟩ := hSpecInner β₁
        (w3_fullAdd_clean (by omega) (a 0) (b 0) cin (by omega) (cleanRem_anti (by omega) hβ))
      have hbelow₁ (w : Wire M) (hw : w.val < cur) : β₁ w = β w :=
        w3_fullAdd_lt cur (by omega) (a 0) (b 0) cin w β hw
      refine ⟨by simpa [show cur + 2 + 2 * W = cur + 2 * (W + 1) by omega] using hcl,
        fun w hw ↦ (hbelow w (by omega)).trans (hbelow₁ w hw), ?_⟩
      dsimp only [rippleAddCarryWires]
      rw [w3_split_bitsVal]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [(hbelow ⟨cur, by omega⟩ (show cur < cur + 2 by omega)).trans
          (w3_fullAdd_sum cur (by omega) (a 0) (b 0) cin β),
        hsum_ih, show (fun j : Fin W ↦ β₁ (a j.succ)) = fun j ↦ β (a j.succ) from
          funext fun j ↦ hbelow₁ _ (ha j.succ),
        show (fun j : Fin W ↦ β₁ (b j.succ)) = fun j ↦ β (b j.succ) from
          funext fun j ↦ hbelow₁ _ (hb j.succ),
        show β₁ cinNext = _ from Function.update_self _ _ _,
        w3_split_bitsVal (fun j ↦ β (a j)), w3_split_bitsVal (fun j ↦ β (b j))]
      have := fullAdd_val_eq (β (a 0)) (β (b 0)) (β cin)
      omega
end SharedScope
end
end ModTempPhaseProg

section ModMomSlot0LocalAndMomCombine288
@[expose] public section
namespace MomSlot0LocalAndMomCombine288Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end MomSlot0LocalAndMomCombine288Alt
namespace MomSlot0LocalAndMomCombine288
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat SpecsAux
-- Root solution namespace already active.
open PosMomSelectSandwich (slotBitProj)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open MomSlots01Slot1ProjKinetic hiding padZeroBits phaseDiagUnitary
open scoped Matrix ComplexOrder MatrixOrder BigOperators
theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by decide +revert
theorem ite_pos_eq {c : Prop} {_h : Decidable c} (hc : c) {α : Sort*} {a b : α} :
    @ite α c _h a b = a := by simp [hc]
theorem ite_neg_eq {c : Prop} {_h : Decidable c} (hnc : ¬c) {α : Sort*} {a b : α} :
    @ite α c _h a b = b := by simp [hnc]
theorem dite_pos_eq {c : Prop} {_h : Decidable c} (hc : c) {α : Sort*}
    {t : c → α} {e : ¬c → α} : @dite α c _h t e = t hc := by simp [hc]
theorem dite_neg_eq {c : Prop} {_h : Decidable c} (hnc : ¬c) {α : Sort*}
    {t : c → α} {e : ¬c → α} : @dite α c _h t e = e hnc := by simp [hnc]
theorem diagonal_mulVec_apply {N : ℕ} (d : Fin N → ℂ) (v : Fin N → ℂ) (i : Fin N) :
    (Matrix.diagonal d).mulVec v i = d i * v i := Matrix.mulVec_diagonal d v i
def withCtrl3Z {M : ℕ} (cur : ℕ) (hcur : cur + 3 ≤ M) (acc c0 c1 c2 : Wire M)
    (ha0 : acc ≠ c0) (ha : acc.val < cur) (hc0 : c0.val < cur) (hc1 : c1.val < cur)
    (hc2 : c2.val < cur) : TempPhaseProg M :=
  withTempBit acc c0 ⟨cur, by omega⟩ ha0 (wire_ne_of_lt ha) (wire_ne_of_lt hc0)
    (withTempBit ⟨cur, by omega⟩ c1 ⟨cur + 1, by omega⟩ (w3_mk_ne_of_gt hc1)
      (w3_mk_ne (by omega)) (w3_ne_mk_of_lt (by omega))
      (withTempBit ⟨cur + 1, by omega⟩ c2 ⟨cur + 2, hcur⟩ (w3_mk_ne_of_gt (by omega))
        (w3_mk_ne (by omega)) (w3_ne_mk_of_lt (by omega)) (.z ⟨cur + 2, hcur⟩)))
@[simp] theorem withCtrl3Z_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 3 ≤ M)
    (acc c0 c1 c2 : Wire M) (ha0 : acc ≠ c0) (ha : acc.val < cur) (hc0 : c0.val < cur)
    (hc1 : c1.val < cur) (hc2 : c2.val < cur) :
    (withCtrl3Z cur hcur acc c0 c1 c2 ha0 ha hc0 hc1 hc2).countTempAnd = 3 := rfl
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.ScopedBlock.withCtrl3Z_block {M : ℕ}
    (cur : ℕ)
    (hcur : cur + 3 ≤ M) (acc c0 c1 c2 : Wire M) (ha0 : acc ≠ c0) (ha : acc.val < cur)
    (hc0 : c0.val < cur) (hc1 : c1.val < cur) (hc2 : c2.val < cur) : ∃ setup : BitAssignment M
    → BitAssignment M, ScopedBlock M (M - cur) setup (.z ⟨cur + 2, hcur⟩)
    (withCtrl3Z cur hcur acc c0 c1 c2 ha0 ha hc0 hc1 hc2) ∧ ∀ β : BitAssignment M, cleanRem M
    (M - cur) β → (withCtrl3Z cur hcur acc c0 c1 c2 ha0 ha hc0 hc1 hc2).evalSign β = β acc * β
    c0 * β c1 * β c2 := by
  have h0 := ScopedBlock.withTempBit_block (M := M) cur (by omega) acc c0 ha0 ha hc0
    (ScopedBlock.withTempBit_block (M := M) (cur + 1) (by omega) ⟨cur, by omega⟩ c1
      (w3_mk_ne_of_gt hc1) (show cur < cur + 1 by omega) (by omega)
      (ScopedBlock.withTempBit_block (M := M) (cur + 2) hcur ⟨cur + 1, by omega⟩ c2
        (w3_mk_ne_of_gt (by omega)) (show cur + 1 < cur + 2 by omega) (by omega)
        (ScopedBlock.z_kick ⟨cur + 2, hcur⟩)))
  refine ⟨_, h0, fun β hβ ↦ ?_⟩
  simpa only [withCtrl3Z, TempPhaseProg.evalSign, id, Function.update_self,
    Function.update_of_ne (w3_ne_mk_of_lt hc1 : c1 ≠ ⟨cur, by omega⟩),
    Function.update_of_ne (w3_ne_mk_of_lt hc2 : c2 ≠ ⟨cur, by omega⟩),
    Function.update_of_ne (w3_ne_mk_of_lt (by omega) : c2 ≠ ⟨cur + 1, by omega⟩),
    Function.update_of_ne (w3_mk_ne (by omega) : (⟨cur + 1, _⟩ : Wire M) ≠ ⟨cur, _⟩)]
    using h0.sign β hβ
def muxBitSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (sel a b : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update β ⟨cur, hcur⟩ (if β sel = 1 then β b else β a)
def withMuxBit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (sel a b : Wire M) (hab : a ≠ b)
    (_hsa : sel ≠ a) (hsb : sel ≠ b) (hs : sel.val < cur) (ha : a.val < cur)
    (hb : b.val < cur) (body : TempPhaseProg M) : TempPhaseProg M :=
  withCliffAlloc (.cnot a b hab) (withTempBit sel b ⟨cur, hcur⟩ hsb (wire_ne_of_lt hs)
    (wire_ne_of_lt hb) (withCliffAlloc (.seq (.cnot a b hab)
      (.cnot a ⟨cur, hcur⟩ (wire_ne_of_lt ha))) body))
@[simp] theorem withMuxBit_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (sel a b : Wire M) (hab : a ≠ b) (hsa : sel ≠ a) (hsb : sel ≠ b) (hs : sel.val < cur)
    (ha : a.val < cur) (hb : b.val < cur) (body : TempPhaseProg M) :
    (withMuxBit cur hcur sel a b hab hsa hsb hs ha hb body).countTempAnd =
      1 + body.countTempAnd := by simp [withMuxBit]
theorem ScopedBlock.withMuxBit_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (sel a b : Wire M)
    (hab : a ≠ b) (hsa : sel ≠ a) (hsb : sel ≠ b) (hs : sel.val < cur) (ha : a.val < cur)
    (hb : b.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ muxBitSetup cur hcur sel a b) leaf
    (withMuxBit cur hcur sel a b hab hsa hsb hs ha hb body) := by
  let out : Wire M := ⟨cur, hcur⟩
  have h3 := w3_withCliffAlloc_cur cur cur (by omega) le_rfl (.cnot a b hab) ⟨ha, hb⟩
    (ScopedBlock.withTempBit_block (M := M) cur hcur sel b hsb hs hb
      (w3_withCliffAlloc_cur (cur + 1) (cur + 1) hcur le_rfl
        (.seq (.cnot a b hab) (.cnot a out (wire_ne_of_lt ha)))
        ⟨⟨by omega, by omega⟩, ⟨by omega, show cur < cur + 1 by omega⟩⟩ hBody))
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withMuxBit]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, muxBitSetup, CliffProg.eval]
  congr 2
  have halg : ∀ s x y : ZMod 2, s * (y + x) + x = if s = 1 then y else x := by decide
  have haout : a ≠ out := wire_ne_of_lt ha
  have hbout : b ≠ out := wire_ne_of_lt hb
  funext w
  rcases eq_or_ne w out with rfl | hwo
  · simp only [out, Function.update_self, Function.update_of_ne haout, Function.update_of_ne hbout,
      Function.update_of_ne hbout.symm, Function.update_of_ne hab, Function.update_of_ne hsb, halg]
  · rcases eq_or_ne w b with rfl | hwb
    · simp only [out, w3_z2_cancel, Function.update_self, Function.update_of_ne haout,
        Function.update_of_ne hbout, Function.update_of_ne hbout.symm, Function.update_of_ne hab]
    · simp only [out, Function.update_of_ne hwo, Function.update_of_ne hwb]
def withMuxReg {M : ℕ} : (W cur : ℕ) → cur + W ≤ M → (sel : Wire M) →
    (a b : Fin W → Wire M) → (∀ i, a i ≠ b i) → (∀ i, sel ≠ a i) → (∀ i, sel ≠ b i) →
    sel.val < cur → (∀ i, (a i).val < cur) → (∀ i, (b i).val < cur) →
    TempPhaseProg M → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _, _, _, body => body
  | W + 1, cur, hcur, sel, a, b, hab, hsa, hsb, hs, ha, hb, body =>
      withMuxBit cur (by omega) sel (a 0) (b 0) (hab 0) (hsa 0) (hsb 0) hs (ha 0) (hb 0)
        (withMuxReg W (cur + 1) (by omega) sel (fun i ↦ a i.succ) (fun i ↦ b i.succ)
          (fun i ↦ hab i.succ) (fun i ↦ hsa i.succ) (fun i ↦ hsb i.succ)
          (lt_trans hs (by omega)) (fun i ↦ lt_trans (ha i.succ) (by omega))
          (fun i ↦ lt_trans (hb i.succ) (by omega)) body)
@[simp] theorem withMuxReg_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M) (sel : Wire M) (a b : Fin W → Wire M)
      (hab : ∀ i, a i ≠ b i) (hsa : ∀ i, sel ≠ a i) (hsb : ∀ i, sel ≠ b i)
      (hs : sel.val < cur) (ha : ∀ i, (a i).val < cur) (hb : ∀ i, (b i).val < cur)
      (body : TempPhaseProg M),
      (withMuxReg W cur hcur sel a b hab hsa hsb hs ha hb body).countTempAnd =
        W + body.countTempAnd
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [withMuxReg]
  | W + 1, _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [withMuxReg, withMuxBit_countTempAnd, withMuxReg_countTempAnd]
      omega
theorem ScopedBlock.withMuxReg_block {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M) (sel : Wire M) (a b : Fin W → Wire M)
      (hab : ∀ i, a i ≠ b i) (hsa : ∀ i, sel ≠ a i) (hsb : ∀ i, sel ≠ b i) (hs : sel.val < cur)
      (ha : ∀ i, (a i).val < cur) (hb : ∀ i, (b i).val < cur) (leaf body : TempPhaseProg M)
      (sBody : BitAssignment M → BitAssignment M), ScopedBlock M (M - (cur + W)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
          (withMuxReg W cur hcur sel a b hab hsa hsb hs ha hb body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - (cur + W)) (setup β) ∧ (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
          (∀ i : Fin W, setup β ⟨cur + i.val, by omega⟩ = if β sel = 1 then β (b i) else β (a i))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody.cast_rem (by omega), fun _ hβ ↦
        ⟨by simpa using hβ, fun _ _ ↦ rfl, fun i ↦ Fin.elim0 i⟩⟩
  | W + 1, cur, hcur, sel, a, b, hab, hsa, hsb, hs, ha, hb, leaf, body, sBody, hBody => by
      obtain ⟨setupInner, hInner, hSpecInner⟩ := ScopedBlock.withMuxReg_block W (cur + 1)
        (by omega) sel (fun i ↦ a i.succ) (fun i ↦ b i.succ) (fun i ↦ hab i.succ)
        (fun i ↦ hsa i.succ) (fun i ↦ hsb i.succ) (lt_trans hs (by omega))
        (fun i ↦ lt_trans (ha i.succ) (by omega)) (fun i ↦ lt_trans (hb i.succ) (by omega))
        leaf body sBody (hBody.cast_rem (by omega))
      refine ⟨fun β ↦ setupInner (muxBitSetup cur (by omega) sel (a 0) (b 0) β),
        ScopedBlock.withMuxBit_block (M := M) cur (by omega) sel (a 0) (b 0)
          (hab 0) (hsa 0) (hsb 0) hs (ha 0) (hb 0) hInner, fun β hβ ↦ ?_⟩
      let β₁ := muxBitSetup cur (by omega) sel (a 0) (b 0) β
      obtain ⟨hcl, hbelow, hbits⟩ := hSpecInner β₁
        (w3_cleanRem_upd_mk (by omega) (cleanRem_anti (by omega) hβ))
      refine ⟨by simpa [show cur + 1 + W = cur + (W + 1) by omega] using hcl,
        fun w hw ↦ (hbelow w (by omega)).trans (Function.update_of_ne (wire_ne_of_lt hw) _ _),
        Fin.cases ((hbelow ⟨cur, by omega⟩ (show cur < cur + 1 by omega)).trans
          (Function.update_self _ _ _)) fun k ↦ ?_⟩
      dsimp only
      rw [show (⟨cur + k.succ.val, _⟩ : Wire M) = ⟨(cur + 1) + k.val, by omega⟩ from
          w3_mk_eq (by
            simp [Fin.val_succ]
            omega), hbits k,
        show β₁ sel = β sel from Function.update_of_ne (wire_ne_of_lt hs) _ _,
        show β₁ (b k.succ) = β (b k.succ) from
          Function.update_of_ne (wire_ne_of_lt (hb k.succ)) _ _,
        show β₁ (a k.succ) = β (a k.succ) from
          Function.update_of_ne (wire_ne_of_lt (ha k.succ)) _ _]
theorem bitsVal_castSucc_add_last {n : ℕ} (f : Fin (n + 1) → ZMod 2) :
    bitsVal f = bitsVal (fun i : Fin n ↦ f i.castSucc) + (f (Fin.last n)).val * 2 ^ n :=
  Fin.sum_univ_castSucc _
theorem bitsVal_of_testBit {W : ℕ} : ∀ (n : ℕ), n < 2 ^ W → bitsVal
    (fun j : Fin W ↦ if n.testBit j.val then (1 : ZMod 2) else 0) = n
  | n, hn => by
      induction W generalizing n with
      | zero => simp [bitsVal, show n = 0 by simpa using hn]
      | succ W ih =>
          rw [w3_split_bitsVal, show (0 : Fin (W + 1)).val = 0 from rfl,
            show (if n.testBit 0 then (1 : ZMod 2) else 0).val = n % 2 by
              rcases Nat.mod_two_eq_zero_or_one n with h | h
              all_goals simp [Nat.testBit_zero, h],
            show (fun j : Fin W ↦ if n.testBit j.succ.val then (1 : ZMod 2) else 0) =
              fun j ↦ if (n / 2).testBit j.val then 1 else 0 from
                funext fun j ↦ by simp [Fin.val_succ, Nat.testBit_succ],
            ih (n / 2) (by
              rw [pow_succ'] at hn
              omega)]
          omega
theorem w3_elec0_lt {mPayload : ℕ} (kIdx : Fin 218) (w : ℕ) (_hw : w < 18) :
    18 * kIdx.val + w < coreWiresSym mPayload := by
  have := kIdx.isLt
  dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
theorem w3_elecK_lt {mPayload k w : ℕ} (_hw : 18 * k ≤ w ∧ w < 18 * (k + 1)) :
    w - 18 * k < coreWiresSym mPayload := by
  dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
def swapElec0Bits {mPayload : ℕ} (kIdx : Fin 218) (β : BitAssignment (coreWiresSym mPayload))
    : BitAssignment (coreWiresSym mPayload) :=
  if kIdx.val = 0 then β
  else fun w ↦
    if hw0 : w.val < 18 then β ⟨18 * kIdx.val + w.val, w3_elec0_lt kIdx w.val hw0⟩
    else if hwK : 18 * kIdx.val ≤ w.val ∧ w.val < 18 * (kIdx.val + 1) then
      β ⟨w.val - 18 * kIdx.val, w3_elecK_lt hwK⟩
    else β w
private theorem swapElec0Bits_apply_of_ne {mPayload : ℕ} {kIdx : Fin 218} (hk0 : kIdx.val ≠ 0)
    (β : BitAssignment (coreWiresSym mPayload)) (w : Wire (coreWiresSym mPayload)) :
    swapElec0Bits kIdx β w =
      if hw0 : w.val < 18 then β ⟨18 * kIdx.val + w.val, w3_elec0_lt kIdx w.val hw0⟩
      else if hwK : 18 * kIdx.val ≤ w.val ∧ w.val < 18 * (kIdx.val + 1) then
        β ⟨w.val - 18 * kIdx.val, w3_elecK_lt hwK⟩
      else β w := by
  unfold swapElec0Bits
  rw [ite_neg_eq hk0]
@[simp] theorem swapElec0Bits_involutive {mPayload : ℕ} (kIdx : Fin 218)
    (β : BitAssignment (coreWiresSym mPayload)) :
    swapElec0Bits kIdx (swapElec0Bits kIdx β) = β := by
  by_cases hk0 : kIdx.val = 0
  · simp [swapElec0Bits, hk0]
  · funext w
    rw [swapElec0Bits_apply_of_ne hk0]
    by_cases hw0 : w.val < 18
    · rw [dite_pos_eq hw0, swapElec0Bits_apply_of_ne hk0,
        dite_neg_eq (show ¬ 18 * kIdx.val + w.val < 18 by omega),
        dite_pos_eq (show 18 * kIdx.val ≤ 18 * kIdx.val + w.val ∧
          18 * kIdx.val + w.val < 18 * (kIdx.val + 1) by omega)]
      exact congrArg β (Fin.ext (show 18 * kIdx.val + w.val - 18 * kIdx.val = w.val by omega))
    · rw [dite_neg_eq hw0]
      by_cases hwK : 18 * kIdx.val ≤ w.val ∧ w.val < 18 * (kIdx.val + 1)
      · rw [dite_pos_eq hwK, swapElec0Bits_apply_of_ne hk0,
          dite_pos_eq (show w.val - 18 * kIdx.val < 18 by omega)]
        exact congrArg β
          (Fin.ext (show 18 * kIdx.val + (w.val - 18 * kIdx.val) = w.val by omega))
      · rw [dite_neg_eq hwK, swapElec0Bits_apply_of_ne hk0, dite_neg_eq hw0, dite_neg_eq hwK]
theorem swapElec0Bits_apply_high {mPayload : ℕ} (kIdx : Fin 218)
    (β : BitAssignment (coreWiresSym mPayload)) {w : Wire (coreWiresSym mPayload)}
    (hw : 3924 ≤ w.val) : swapElec0Bits kIdx β w = β w := by
  by_cases hk0 : kIdx.val = 0
  · simp [swapElec0Bits, hk0]
  · have := kIdx.isLt
    rw [swapElec0Bits_apply_of_ne hk0, dite_neg_eq (show ¬ w.val < 18 by omega),
      dite_neg_eq (show ¬ (18 * kIdx.val ≤ w.val ∧ w.val < 18 * (kIdx.val + 1)) by omega)]
def slot0ElecIdx {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (β : BitAssignment (coreWiresSym mPayload)) : Fin 218 :=
  let u36 : ℕ := ∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val
  let bPar : ℕ := (β (corePayloadSym mPayload ⟨36, by omega⟩)).val
  ⟨2 * (u36 % 109) + bPar, by
    have := Nat.mod_lt u36 (show 0 < 109 by decide)
    have := ZMod.val_lt (β (corePayloadSym mPayload ⟨36, by omega⟩))
    omega⟩
theorem slot0ElecIdx_swapElec0Bits {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (kIdx : Fin 218) (β : BitAssignment (coreWiresSym mPayload)) :
    slot0ElecIdx hmPay (swapElec0Bits kIdx β) = slot0ElecIdx hmPay β := by
  have hpay (j : Fin mPayload) :
      swapElec0Bits kIdx β (corePayloadSym mPayload j) = β (corePayloadSym mPayload j) :=
    swapElec0Bits_apply_high kIdx β (by
      dsimp [corePayloadSym, MomSlot0LocalAndMomCombine288Alt.qreg_block_apply,
        MomSlot0LocalAndMomCombine288Alt.qreg_block_wires_apply,
        MomSlot0LocalAndMomCombine288Alt.qreg_whole_wires,
        MomSlot0LocalAndMomCombine288Alt.emb_trans_apply,
        MomSlot0LocalAndMomCombine288Alt.emb_refl_apply,
        MomSlot0LocalAndMomCombine288Alt.emb_mk_apply, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]
      omega)
  dsimp only [slot0ElecIdx]
  simp_rw [hpay]
noncomputable def slot0LocalPhaseBit {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (β : BitAssignment (coreWiresSym mPayload)) : ZMod 2 :=
  let c0 := β ⟨SpecsAux.SpecMirror.systemQubits, by
    dsimp [coreWiresSym, selWiresSym]
    omega⟩
  let c1 := β ⟨SpecsAux.SpecMirror.systemQubits + 1, by
    dsimp [coreWiresSym, selWiresSym]
    omega⟩
  let c2 := β ⟨SpecsAux.SpecMirror.systemQubits + 2, by
    dsimp [coreWiresSym, selWiresSym]
    omega⟩
  if c0 = 0 ∧ c1 = 0 ∧ c2 = 1 then
    let u36 : ℕ :=
      ∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val
    let bPar : ℕ := (β (corePayloadSym mPayload ⟨36, by omega⟩)).val
    let uCmp42 : ℕ :=
      ∑ i : Fin 42, (β (corePayloadSym mPayload ⟨37 + i.val, by omega⟩)).val * 2 ^ i.val
    if u36 = 2 ^ 36 - 1 then β (corePayloadSym mPayload ⟨79, by omega⟩)
    else
      let axisLocal : ℕ := (2 * (u36 % 327) + bPar) % 3
      let u6Val : ℕ := bitsVal (fun b : Fin 6 ↦
        β ⟨6 * axisLocal + b.val, by
          have : axisLocal < 3 := Nat.mod_lt _ (by omega)
          dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
          omega⟩)
      if uCmp42 < MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff
          ⟨u6Val, bitsVal_lt_two_pow _⟩
      then 1 else 0
  else 0
noncomputable def uSlot0Local {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) : Unitary
    (2 ^ (coreWiresSym mPayload)) := phaseDiagUnitary (slot0LocalPhaseBit hmPay w_eff)
theorem phaseDiagUnitary_val_eq_diag {K : ℕ} (pred : BitAssignment K → ZMod 2) :
    (phaseDiagUnitary pred).1 = Matrix.diagonal
      (fun g ↦ (-1 : ℂ) ^ (pred (basisBits K g)).val) := rfl
theorem uSlot0Local_sa {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (uSlot0Local hmPay w_eff).1ᴴ = (uSlot0Local hmPay w_eff).1 := by
  rw [uSlot0Local, phaseDiagUnitary_val_eq_diag]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [hij, hij.symm]
theorem uSlot0Local_offCoin {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (uSlot0Local hmPay w_eff).1 * (1 - FullSysMomSlots0135Concrete.momCoinProj mPayload
    (FullSysPrepare6Slot.fullSysCoinIdx 0)) = 1 - FullSysMomSlots0135Concrete.momCoinProj
    mPayload (FullSysPrepare6Slot.fullSysCoinIdx 0) := by
  rw [← momCoinProj_eq_fullSys mPayload _,
    show FullSysPrepare6Slot.fullSysCoinIdx 0 = 4 from rfl, uSlot0Local,
    phaseDiagUnitary_val_eq_diag, Matrix.mul_sub, Matrix.mul_one, momCoinProj,
    slotBitProj, slotBitProj, slotBitProj, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  rcases eq_or_ne g₁ g₂ with rfl | hg
  · simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    by_cases hAll : basisBits (coreWiresSym mPayload) g₁ (iSlot0Mom mPayload) = 0 ∧
        basisBits (coreWiresSym mPayload) g₁ (iSlot1Mom mPayload) = 0 ∧
        basisBits (coreWiresSym mPayload) g₁ (iSlot2Mom mPayload) = 1
    · rcases hAll with ⟨hc0, hc1, hc2⟩
      simp [show (coinBitFin2 4 0).val = 0 from rfl, show (coinBitFin2 4 1).val = 0 from rfl,
        show (coinBitFin2 4 2).val = 1 from rfl, hc0, hc1, hc2]
    · have hp0 : slot0LocalPhaseBit hmPay w_eff (basisBits (coreWiresSym mPayload) g₁) = 0 := by
        unfold slot0LocalPhaseBit
        rw [show (⟨SpecsAux.SpecMirror.systemQubits,
          _⟩ : Wire _) = iSlot0Mom mPayload from Fin.ext rfl,
          show (⟨SpecsAux.SpecMirror.systemQubits + 1, _⟩ : Wire _) = iSlot1Mom mPayload from
            Fin.ext rfl,
          show (⟨SpecsAux.SpecMirror.systemQubits + 2, _⟩ : Wire _) = iSlot2Mom mPayload from
            Fin.ext rfl]
        exact MomSlots01Slot1ProjKinetic.ite_neg_s1 hAll
      simp [hp0]
  · simp [hg]
theorem unitaryConj_uSlot0Local_on_coin4 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (w_eff : ℝ) (U : Unitary (2 ^ (coreWiresSym mPayload)))
    (kMap : BitAssignment (coreWiresSym mPayload) → Fin 218)
    (hkInv : ∀ β, kMap (swapElec0Bits (kMap β) β) = kMap β)
    (hkActive : ∀ β, β (iSlot0Mom mPayload) = 0 → β (iSlot1Mom mPayload) = 0 →
      β (iSlot2Mom mPayload) = 1 →
      (∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val) ≠
        2 ^ 36 - 1 → kMap β = slot0ElecIdx hmPay β)
    (hAct : ∀ β, β (iSlot0Mom mPayload) = 0 → β (iSlot1Mom mPayload) = 0 →
      β (iSlot2Mom mPayload) = 1 → U.1.mulVec (ket β) = ket (swapElec0Bits (kMap β) β)) :
    (HoistedSwapSelectBridge.unitaryConj U (uSlot0Local hmPay w_eff)).1 *
        FullSysMomSlots0135Concrete.momCoinProj mPayload 4 =
      (MomSlots01Slot0ElectronKinetic.slot0SelectUnitary hmPay w_eff).1 *
        FullSysMomSlots0135Concrete.momCoinProj mPayload 4 := by
  have hCore : SpecsAux.SpecMirror.systemQubits + 6 + mPayload ≤ coreWiresSym mPayload := by
    dsimp [coreWiresSym, selWiresSym]
    omega
  have hPayWire (j : Fin mPayload) :
      corePayloadSym mPayload j = ⟨SpecsAux.SpecMirror.systemQubits + 6 + j.val, by omega⟩ := by
    ext
    dsimp [corePayloadSym, MomSlot0LocalAndMomCombine288Alt.qreg_block_apply,
      MomSlot0LocalAndMomCombine288Alt.qreg_block_wires_apply,
      MomSlot0LocalAndMomCombine288Alt.qreg_whole_wires,
      MomSlot0LocalAndMomCombine288Alt.emb_trans_apply,
      MomSlot0LocalAndMomCombine288Alt.emb_refl_apply,
      MomSlot0LocalAndMomCombine288Alt.emb_mk_apply]
  have hSysHigh : 3924 ≤ SpecsAux.SpecMirror.systemQubits := by
    dsimp [SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega
  have hS0 : 3924 ≤ (iSlot0Mom mPayload).val := hSysHigh
  have hS1 : 3924 ≤ (iSlot1Mom mPayload).val :=
    show 3924 ≤ SpecsAux.SpecMirror.systemQubits + 1 from Nat.le_add_right_of_le hSysHigh
  have hS2 : 3924 ≤ (iSlot2Mom mPayload).val :=
    show 3924 ≤ SpecsAux.SpecMirror.systemQubits + 2 from Nat.le_add_right_of_le hSysHigh
  have hUinv_ket (β) (hc0 : β (iSlot0Mom mPayload) = 0) (hc1 : β (iSlot1Mom mPayload) = 0)
      (hc2 : β (iSlot2Mom mPayload) = 1) :
      U.1ᴴ.mulVec (ket β) = ket (swapElec0Bits (kMap β) β) := by
    rw [← show U.1.mulVec (ket (swapElec0Bits (kMap β) β)) = ket β by
        rw [hAct _ ((swapElec0Bits_apply_high _ β hS0).trans hc0)
          ((swapElec0Bits_apply_high _ β hS1).trans hc1)
          ((swapElec0Bits_apply_high _ β hS2).trans hc2), hkInv β, swapElec0Bits_involutive],
      ← mul_mulVec_prog, show U.1ᴴ * U.1 = 1 from congrArg Subtype.val (inv_mul_cancel U),
      Matrix.one_mulVec]
  have hdiag_ket (d : Fin (2 ^ coreWiresSym mPayload) → ℂ) (γ) :
      (Matrix.diagonal d).mulVec (ket γ) =
        d ((basisBitsEquiv (coreWiresSym mPayload)).symm γ) • ket γ := funext fun i ↦ by
    rcases eq_or_ne i ((basisBitsEquiv (coreWiresSym mPayload)).symm γ) with rfl | hi
    · simp [diagonal_mulVec_apply, ket]
    · simp [diagonal_mulVec_apply, ket, hi]
  have hbb_symm (γ) := (basisBitsEquiv (coreWiresSym mPayload)).apply_symm_apply γ
  refine matrix_ext_ket fun β ↦ ?_
  rw [← momCoinProj_eq_fullSys mPayload 4]
  have hProjKet : (momCoinProj mPayload 4).mulVec (ket β) =
      if β (iSlot0Mom mPayload) = 0 ∧ β (iSlot1Mom mPayload) = 0 ∧
        β (iSlot2Mom mPayload) = 1 then ket β else 0 := by
    rw [momCoinProj, slotBitProj, slotBitProj, slotBitProj, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, hdiag_ket, hbb_symm β]
    simp only [show (coinBitFin2 4 0).val = 0 from rfl,
      show (coinBitFin2 4 1).val = 0 from rfl, show (coinBitFin2 4 2).val = 1 from rfl]
    rcases zmod2_cases (β (iSlot0Mom mPayload)) with a0 | a0
    all_goals rcases zmod2_cases (β (iSlot1Mom mPayload)) with a1 | a1
    all_goals rcases zmod2_cases (β (iSlot2Mom mPayload)) with a2 | a2
    all_goals simp [a0, a1, a2]
  rw [mul_mulVec_prog, mul_mulVec_prog, hProjKet]
  split_ifs with hcoin
  · obtain ⟨hc0, hc1, hc2⟩ := hcoin
    have hPhase (kIdx : Fin 218)
        (hk : (∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val) ≠
          2 ^ 36 - 1 → kIdx = slot0ElecIdx hmPay β) :
        slot0LocalPhaseBit hmPay w_eff (swapElec0Bits kIdx β) =
          MomSlots01Slot0ElectronKinetic.slot0PhaseBit hmPay w_eff β := by
      have hpay (j : Fin mPayload) :
          swapElec0Bits kIdx β (corePayloadSym mPayload j) = β (corePayloadSym mPayload j) :=
        swapElec0Bits_apply_high kIdx β (by
          rw [congrArg Fin.val (hPayWire j)]
          exact Nat.le_add_right_of_le (Nat.le_add_right_of_le hSysHigh))
      have hcRaw : β ⟨SpecsAux.SpecMirror.systemQubits, by omega⟩ = 0 ∧
          β ⟨SpecsAux.SpecMirror.systemQubits + 1, by omega⟩ = 0 ∧
          β ⟨SpecsAux.SpecMirror.systemQubits + 2, by omega⟩ = 1 :=
        ⟨(congrArg β (Fin.ext rfl)).trans hc0, (congrArg β (Fin.ext rfl)).trans hc1,
          (congrArg β (Fin.ext rfl)).trans hc2⟩
      unfold slot0LocalPhaseBit MomSlots01Slot0ElectronKinetic.slot0PhaseBit
      dsimp only
      rw [swapElec0Bits_apply_high _ β hSysHigh,
        swapElec0Bits_apply_high _ β (show 3924 ≤ SpecsAux.SpecMirror.systemQubits + 1 by omega),
        swapElec0Bits_apply_high _ β (show 3924 ≤ SpecsAux.SpecMirror.systemQubits + 2 by omega)]
      simp_rw [hpay]
      rw [ite_pos_eq hcRaw, ite_pos_eq hcRaw]
      let u36 : ℕ :=
        ∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val
      by_cases htie : u36 = 2 ^ 36 - 1
      · rw [ite_pos_eq htie, ite_pos_eq htie]
      · rw [ite_neg_eq htie, ite_neg_eq htie]
        obtain rfl := hk htie
        let bPar : ℕ := (β (corePayloadSym mPayload ⟨36, by omega⟩)).val
        let mRaw : Fin 654 := ⟨2 * (u36 % 327) + bPar, by
          have := Nat.mod_lt u36 (show 0 < 327 by omega)
          have := ZMod.val_lt (β (corePayloadSym mPayload ⟨36, by omega⟩))
          omega⟩
        let mAx : Fin 654 := MomSlots01Slot0ElectronKinetic.crtPerm654 mRaw
        set idx6 := (TwosCompAndWire0Cancel.elec654Axes mAx).extractIndex
          ((coreSysSym mPayload).extractIndex ((basisBitsEquiv (coreWiresSym mPayload)).symm β))
        suffices (⟨bitsVal _, bitsVal_lt_two_pow _⟩ : Fin 64) = idx6 by rw [this]
        refine Fin.ext ?_
        rw [← show bitsVal (basisBits 6 idx6) = idx6.val from
          (congrArg bitsVal (funext (basisBits_eq_testBit 6 idx6))).trans
            (bitsVal_of_testBit idx6.val idx6.isLt)]
        refine congrArg bitsVal (funext fun b ↦ ?_)
        have hq : 6 * (mRaw.val % 3) + b.val < 18 := by
          have := Nat.mod_lt mRaw.val (show 0 < 3 by omega)
          omega
        have hel0 :
            swapElec0Bits (slot0ElecIdx hmPay β) β ⟨6 * (mRaw.val % 3) + b.val, by omega⟩ =
            β ⟨18 * (slot0ElecIdx hmPay β).val + (6 * (mRaw.val % 3) + b.val), by
              have := (slot0ElecIdx hmPay β).isLt
              omega⟩ := by
          by_cases hk0 : (slot0ElecIdx hmPay β).val = 0
          · rw [swapElec0Bits, ite_pos_eq hk0]
            exact congrArg β (w3_mk_eq (by omega))
          · rw [swapElec0Bits_apply_of_ne hk0, dite_pos_eq hq]
        have hw_eq : (coreSysSym mPayload ((TwosCompAndWire0Cancel.elec654Axes mAx) b) :
            Wire (coreWiresSym mPayload)) =
            ⟨18 * (slot0ElecIdx hmPay β).val + (6 * (mRaw.val % 3) + b.val), by
              have := (slot0ElecIdx hmPay β).isLt
              omega⟩ := Fin.ext (by
          dsimp [coreSysSym, TwosCompAndWire0Cancel.elec654Axes,
            MomSlot0LocalAndMomCombine288Alt.qreg_block_apply,
            MomSlot0LocalAndMomCombine288Alt.qreg_block_wires_apply,
            MomSlot0LocalAndMomCombine288Alt.qreg_whole_wires,
            MomSlot0LocalAndMomCombine288Alt.emb_trans_apply,
            MomSlot0LocalAndMomCombine288Alt.emb_refl_apply,
            MomSlot0LocalAndMomCombine288Alt.emb_mk_apply]
          rw [show (slot0ElecIdx hmPay β).val = mAx.val / 3 from
              (MomSlots01Slot0ElectronKinetic.crtPerm654_slot0_div3 u36 bPar (ZMod.val_lt _)).symm,
            ← MomSlots01Slot0ElectronKinetic.crtPerm654_mod3 mRaw]
          omega)
        rw [hel0, QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hw_eq]
        exact (congrFun (hbb_symm β) _).symm
    rw [HoistedSwapSelectBridge.unitaryConj_val, mul_mulVec_prog, mul_mulVec_prog,
      hAct β hc0 hc1 hc2,
      show (uSlot0Local hmPay w_eff).1 = _ from phaseDiagUnitary_val_eq_diag _,
      hdiag_ket, hbb_symm, Matrix.mulVec_smul,
      hUinv_ket _ ((swapElec0Bits_apply_high _ β hS0).trans hc0)
        ((swapElec0Bits_apply_high _ β hS1).trans hc1)
        ((swapElec0Bits_apply_high _ β hS2).trans hc2),
      hkInv β, swapElec0Bits_involutive, hPhase (kMap β) (hkActive β hc0 hc1 hc2)]
    change _ = (MomSlots01Slot0ElectronKinetic.slot0SelectDiag hmPay w_eff).mulVec (ket β)
    unfold MomSlots01Slot0ElectronKinetic.slot0SelectDiag
    rw [hdiag_ket, hbb_symm]
  · simp
abbrev slot0LocalWorkWires : ℕ := 288
open MeasureBranchHadamardSem hiding ket matrix_ext_ket
open BchCubeDecoder StreamingBchComparator
open scoped Circuit.Notation
abbrev slot0LocalTCost : ℕ := 500
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.ScopedBlock.withLtComp_clean_block
    {M W cur : ℕ}
    (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur)
    {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M}
    (hBody : ScopedBlock M (M - (cur + W + 1)) sBody leaf body) :
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
        (withLtCompLoop W cur hcur a b hab ha hb body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - cur) β →
        cleanRem M (M - (cur + W + 1)) (setup β) ∧ (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
        setup β ⟨cur + W, by omega⟩ =
          if bitsVal (fun j ↦ β (a j)) < bitsVal (fun j ↦ β (b j)) then 1 else 0 := by
  obtain ⟨setup, hBlk, hSpec⟩ :=
    ScopedBlock.withLtCompLoop_block W cur hcur a b hab ha hb leaf body sBody hBody
  refine ⟨setup, ⟨validCleanRem_mono (by omega) hBlk.valid,
    fun _ hβ ↦ hBlk.bits _ (cleanRem_anti (by omega) hβ),
    fun _ hβ ↦ hBlk.sign _ (cleanRem_anti (by omega) hβ)⟩, fun β hβ ↦ ?_⟩
  obtain ⟨hcl, hbelow, hiff⟩ := hSpec β (cleanRem_anti (by omega) hβ)
  have hprev0 : β ⟨cur, by omega⟩ = 0 := w3_cleanRem_mk hβ (by omega)
  refine ⟨hcl, hbelow, ?_⟩
  rcases zmod2_cases (setup β ⟨cur + W, by omega⟩) with hz | ho
  · exact hz.trans (ite_eq_right_iff.mpr fun hlt ↦
      absurd (hz.symm.trans (hiff.mpr (Or.inl hlt))) (by decide)).symm
  · exact ho.trans (ite_eq_left_iff.mpr fun hnot ↦ (hiff.mp ho).elim
      (fun hlt ↦ absurd hlt hnot) fun ⟨_, h1⟩ ↦ absurd (hprev0.symm.trans h1) (by decide)).symm
theorem cleanRem_padZeroBits {kAct mClean : ℕ} (α : BitAssignment kAct) :
    cleanRem (kAct + mClean) mClean (padZeroBits α) := fun w hw ↦
  (congrArg (padZeroBits α) (show w = Fin.natAdd kAct ⟨w.val - kAct, by omega⟩ from
    Fin.ext (show w.val = kAct + (w.val - kAct) by omega))).trans (Fin.addCases_right _)
theorem coreWiresSym_ge_4034 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    4034 ≤ coreWiresSym mPayload := by
  dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
theorem step_witness {α : Type} (x : α) : ∃ y : α, y = x := ⟨x, rfl⟩
theorem bitsVal_fin6 (f : Fin 6 → ZMod 2) : bitsVal f = (f 0).val + (f 1).val * 2 + (f 2).val
    * 4 + (f 3).val * 8 + (f 4).val * 16 + (f 5).val * 32 := by
  rw [bitsVal_castSucc_add_last, bitsVal_castSucc_add_last, bitsVal_castSucc_add_last,
    bitsVal_castSucc_add_last, bitsVal_castSucc_add_last]
  simp [bitsVal]
theorem six_mul_add_lt_core {mPayload ax : ℕ} (hax : ax < 3) (b : Fin 6) :
    6 * ax + b.val < coreWiresSym mPayload := by
  have := b.isLt
  dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
theorem slot0_coin_zero_of_not (b c0 c1 c2 : ZMod 2) (h : ¬(c0 = 0 ∧ c1 = 0 ∧ c2 = 1)) : b *
    (c0 + 1) * (c1 + 1) * c2 = 0 := by decide +revert
theorem pay36_lt_payload {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (i : Fin 36) :
    i.val < mPayload := lt_of_lt_of_le (lt_trans i.isLt (by decide)) hmPay
theorem pay37_lt_80 (i : Fin 42) : 37 + i.val < 80 := by omega
theorem pay37_lt_payload {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (i : Fin 42) :
    37 + i.val < mPayload := lt_of_lt_of_le (pay37_lt_80 i) hmPay
theorem nat_lt3_cases {a : ℕ} (ha : a < 3) : a = 0 ∨ a = 1 ∨ a = 2 := by omega
theorem six_mul_congr {a a' : ℕ} (h : a = a') (k : ℕ) : 6 * a + k = 6 * a' + k := h ▸ rfl
attribute [local irreducible] withLtCompLoop
theorem bitsVal_fin5 (f : Fin 5 → ZMod 2) : bitsVal f = (f 0).val + (f 1).val * 2 + (f 2).val
    * 4 + (f 3).val * 8 + (f 4).val * 16 := by
  rw [bitsVal_castSucc_add_last, bitsVal_castSucc_add_last, bitsVal_castSucc_add_last,
    bitsVal_castSucc_add_last]
  simp [bitsVal]
theorem slot0Thresh_lt_two_pow_42 {w_eff : ℝ}
    (hw : LiteralKineticAndMidpoint128.elecQuadCenterOffset < w_eff) (u : Fin 64) :
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u < 2 ^ 42 := by
  have hw_pos : 0 < w_eff := lt_trans MomSlots01Slot0ElectronKinetic.elecQuadCenterOffset_pos hw
  obtain ⟨hlo, _⟩ := MomSlots01Slot0ElectronKinetic.slot0_scaled_axis_bounds u
  have hdiv_lo : -1 < 654 * ((2 * π / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ^ 2 / 2) *
      ((MomSlots01Slot0ElectronKinetic.slot0AxisInt u : ℝ) ^ 2 - 961 / 2) / w_eff := by
    rw [lt_div_iff₀ hw_pos]
    linarith
  rw [MomSlots01Slot0ElectronKinetic.slot0Thresh_eq_floor]
  refine (Nat.floor_lt
    (MomSlots01Slot0ElectronKinetic.slot0ThreshReal_bounds (le_of_lt hw) u).1).mpr ?_
  unfold MomSlots01Slot0ElectronKinetic.slot0ThreshReal
  nlinarith [show (0 : ℝ) < (2 : ℝ) ^ 41 by norm_num,
    show (2 : ℝ) ^ 41 * 2 = ((2 ^ 42 : ℕ) : ℝ) by norm_num]
theorem slot0Thresh_eq_of_natAbs (w_eff : ℝ) (u : Fin 64) (m : Fin 32)
    (h : (MomSlots01Slot0ElectronKinetic.slot0AxisInt u).natAbs = m.val) :
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u =
      MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff ⟨m.val, lt_trans m.isLt (by decide)⟩ := by
  unfold MomSlots01Slot0ElectronKinetic.slot0Thresh
  have hax : ∀ x : Fin 32, MomSlots01Slot0ElectronKinetic.slot0AxisInt
      ⟨x.val, lt_trans x.isLt (by decide)⟩ = (x.val : ℤ) := by decide
  have hnat : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) ^ 2 = (z : ℝ) ^ 2
    | .ofNat _ => by simp [Int.natAbs]
    | .negSucc _ => by
        simp only [Int.natAbs, Int.cast_negSucc]
        push_cast
        ring
  rw [show (MomSlots01Slot0ElectronKinetic.slot0AxisInt u : ℝ) ^ 2 =
    (MomSlots01Slot0ElectronKinetic.slot0AxisInt
      ⟨m.val, lt_trans m.isLt (by decide)⟩ : ℝ) ^ 2 by
      rw [hax m, ← hnat (MomSlots01Slot0ElectronKinetic.slot0AxisInt u), h]
      norm_cast]
theorem fullAdd_and_eq (x y z : ZMod 2) :
    (x + y + z) * (z + (x + z) * (y + z)) = x * y * z := by decide +revert
theorem cliff_eval_update_outside {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound →
      ∀ (γ : BitAssignment M) (out : Wire M), bound ≤ out.val → ∀ (v : ZMod 2),
        c.eval (Function.update γ out v) = Function.update (c.eval γ) out v
  | .nil, _, _, _, _, _ => rfl
  | .x q, hq, γ, out, hout, v => by
      have hne : q ≠ out := wire_ne_of_lt (lt_of_lt_of_le hq hout)
      simp only [CliffProg.eval, Function.update_of_ne hne, Function.update_comm hne.symm]
  | .cnot ctrl tgt _, ⟨hc, ht⟩, γ, out, hout, v => by
      have hne_c : ctrl ≠ out := wire_ne_of_lt (lt_of_lt_of_le hc hout)
      have hne_t : tgt ≠ out := wire_ne_of_lt (lt_of_lt_of_le ht hout)
      simp only [CliffProg.eval, Function.update_of_ne hne_c, Function.update_of_ne hne_t,
        Function.update_comm hne_t.symm]
  | .seq c₁ c₂, ⟨h₁, h₂⟩, γ, out, hout, v => by
      simp only [CliffProg.eval, cliff_eval_update_outside c₁ h₁ γ out hout v,
        cliff_eval_update_outside c₂ h₂ (c₁.eval γ) out hout v]
theorem cliff_supportsBelow_mono {M b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    ∀ {c : CliffProg M}, c.SupportsBelow b₁ → c.SupportsBelow b₂
  | .nil, _ => trivial
  | .x _, hq => lt_of_lt_of_le hq h
  | .cnot _ _ _, ⟨hc, ht⟩ => ⟨lt_of_lt_of_le hc h, lt_of_lt_of_le ht h⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨cliff_supportsBelow_mono h h₁, cliff_supportsBelow_mono h h₂⟩
def withHalfAdd0 {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (body : TempPhaseProg M) : TempPhaseProg M :=
  withCliffAlloc (.seq (.cnot a ⟨cur, by omega⟩ (wire_ne_of_lt ha))
    (.cnot b ⟨cur, by omega⟩ (wire_ne_of_lt hb)))
    (withTempBit a b ⟨cur + 1, hcur⟩ hab (w3_ne_mk_of_lt (by omega))
      (w3_ne_mk_of_lt (by omega)) body)
@[simp] theorem withHalfAdd0_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) :
    (withHalfAdd0 cur hcur a b hab ha hb body).countTempAnd = 1 + body.countTempAnd := by
  simp [withHalfAdd0]
def halfAdd0Setup {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update (Function.update β ⟨cur, by omega⟩ (β a + β b)) ⟨cur + 1, hcur⟩ (β a * β b)
private theorem w3_halfAdd0_clean {M cur rem : ℕ} (hcur : cur + 2 ≤ M)
    (a b : Wire M) {β : BitAssignment M} (hrem : cur + 2 ≤ M - rem) (hβ : cleanRem M rem β) :
    cleanRem M rem (halfAdd0Setup cur hcur a b β) :=
  w3_cleanRem_upd_mk (by omega) (w3_cleanRem_upd_mk (by omega) hβ)
theorem halfAdd0Setup_lt {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b w : Wire M)
    (β : BitAssignment M) (hw : w.val < cur) : halfAdd0Setup cur hcur a b β w = β w := by
  dsimp [halfAdd0Setup]
  rw [Function.update_of_ne (w3_ne_mk_of_lt (by omega)),
    Function.update_of_ne (w3_ne_mk_of_lt hw)]
theorem halfAdd0Setup_sum {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b : Wire M)
    (β : BitAssignment M) : halfAdd0Setup cur hcur a b β ⟨cur, by omega⟩ = β a + β b := by
  dsimp [halfAdd0Setup]
  rw [Function.update_of_ne (w3_mk_ne (by omega)), Function.update_self]
theorem halfAdd0Setup_cout {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b : Wire M)
    (β : BitAssignment M) : halfAdd0Setup cur hcur a b β ⟨cur + 1, hcur⟩ = β a * β b :=
  Function.update_self _ _ _
theorem ScopedBlock.withHalfAdd0_block {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b : Wire M)
    (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 2)) sBody leaf body) : ScopedBlock M (M - cur)
    (sBody ∘ halfAdd0Setup cur hcur a b) leaf (withHalfAdd0 cur hcur a b hab ha hb body) := by
  let sumWire : Wire M := ⟨cur, by omega⟩
  have h2 := w3_withCliffAlloc_cur cur (cur + 1) (by omega) (by omega)
    (.seq (.cnot a sumWire (wire_ne_of_lt ha)) (.cnot b sumWire (wire_ne_of_lt hb)))
    ⟨⟨by omega, show cur < cur + 1 by omega⟩, ⟨by omega, show cur < cur + 1 by omega⟩⟩
    (ScopedBlock.withTempBit_block (M := M) (cur + 1) hcur a b hab (by omega) (by omega) hBody)
  refine ⟨h2.valid, h2.bits, fun β hβ ↦ ?_⟩
  dsimp only [withHalfAdd0]
  rw [h2.sign β hβ]
  dsimp only [Function.comp_apply, halfAdd0Setup, CliffProg.eval]
  congr 2
  rw [show (⟨cur, _⟩ : Wire M) = sumWire from rfl]
  have hs0 : β sumWire = 0 := w3_cleanRem_mk hβ (by omega)
  funext w
  rcases eq_or_ne w ⟨cur + 1, hcur⟩ with rfl | hc
  · simp only [Function.update_self]
    rw [Function.update_of_ne (w3_ne_mk_of_lt ha : a ≠ sumWire),
      Function.update_of_ne (w3_ne_mk_of_lt ha : a ≠ sumWire),
      Function.update_of_ne (w3_ne_mk_of_lt hb : b ≠ sumWire),
      Function.update_of_ne (w3_ne_mk_of_lt hb : b ≠ sumWire)]
  · rcases eq_or_ne w sumWire with rfl | hs
    · simp only [hs0, zero_add, Function.update_self, Function.update_of_ne hc]
      rw [Function.update_of_ne (w3_ne_mk_of_lt hb : b ≠ sumWire)]
    · simp only [Function.update_of_ne hc, Function.update_of_ne hs]
def withAffineAnd {M : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M) (cPre : CliffProg M) (a b : Wire M)
    (hab : a ≠ b) (ha : a.val < pos) (hb : b.val < pos) (body : TempPhaseProg M) :
    TempPhaseProg M :=
  withCliffAlloc cPre (withTempBit a b ⟨pos, hpos⟩ hab (wire_ne_of_lt ha) (wire_ne_of_lt hb)
    (withCliffAlloc cPre.inv body))
@[simp] theorem withAffineAnd_countTempAnd {M : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M)
    (cPre : CliffProg M) (a b : Wire M) (hab : a ≠ b) (ha : a.val < pos) (hb : b.val < pos)
    (body : TempPhaseProg M) :
    (withAffineAnd pos hpos cPre a b hab ha hb body).countTempAnd = 1 + body.countTempAnd := by
  simp [withAffineAnd]
theorem ScopedBlock.withAffineAnd_block {M : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M)
    (cPre : CliffProg M) (hc : cPre.SupportsBelow pos) (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < pos) (hb : b.val < pos) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (pos + 1)) sBody leaf body) :
    ScopedBlock M (M - pos) (fun β ↦ sBody (Function.update β ⟨pos, hpos⟩ (cPre.eval β a *
    cPre.eval β b))) leaf (withAffineAnd pos hpos cPre a b hab ha hb body) := by
  have h1 := w3_withCliffAlloc_cur (pos + 1) (pos + 1) hpos le_rfl cPre.inv
    (cliff_supportsBelow_mono (by omega) (CliffProg.inv_supportsBelow cPre hc)) hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) pos hpos a b hab ha hb h1
  have h3 := w3_withCliffAlloc_cur pos pos (by omega) le_rfl cPre hc h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withAffineAnd]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply]
  congr 2
  rw [cliff_eval_update_outside cPre.inv (CliffProg.inv_supportsBelow cPre hc)
    (cPre.eval β) ⟨pos, hpos⟩ le_rfl, CliffProg.inv_eval]
theorem fin_0_ne_1 {n : ℕ} : (0 : Fin (n + 2)) ≠ 1 := fun h ↦ by
  simpa [Nat.mod_eq_of_lt (by omega : 1 < n + 2)] using congrArg Fin.val h
theorem fin_0_ne_2 {n : ℕ} : (0 : Fin (n + 3)) ≠ 2 := fun h ↦ by
  simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2 < n + 3)] using congrArg Fin.val h
theorem fin_1_ne_2 {n : ℕ} : (1 : Fin (n + 3)) ≠ 2 := fun h ↦ by
  simpa [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 1 < n + 3),
    Nat.mod_eq_of_lt (by omega : 2 < n + 3)] using congrArg Fin.val h
def mod3NextW1 {M steps : ℕ} (s1 c1 : Wire M) (w1 : Fin (steps + 3) → Wire M) :
    Fin (steps + 2) → Wire M :=
  fun i ↦ if i.val = 0 then s1 else if i.val = 1 then c1 else w1 ⟨i.val + 1, by omega⟩
def mod3NextW2 {M steps : ℕ} (s2 : Wire M) (w2 : Fin (steps + 3) → Wire M) :
    Fin (steps + 2) → Wire M :=
  fun i ↦ if i.val = 0 then s2 else w2 ⟨i.val + 1, by omega⟩
theorem mod3NextW1_lt {M steps cur : ℕ} (hcur : cur + 4 ≤ M)
    (w1 : Fin (steps + 3) → Wire M) (hw1_lt : ∀ i, (w1 i).val < cur)
    (i : Fin (steps + 2)) :
    (mod3NextW1 (⟨cur, by omega⟩ : Wire M) (⟨cur + 3, by omega⟩ : Wire M) w1 i).val <
      cur + 4 := by
  dsimp only [mod3NextW1]
  split_ifs
  · exact show cur < cur + 4 by omega
  · exact show cur + 3 < cur + 4 by omega
  · exact lt_trans (hw1_lt ⟨i.val + 1, by omega⟩) (by omega)
theorem mod3NextW2_lt {M steps cur : ℕ} (hcur : cur + 4 ≤ M)
    (w2 : Fin (steps + 3) → Wire M) (hw2_lt : ∀ i, (w2 i).val < cur)
    (i : Fin (steps + 2)) :
    (mod3NextW2 (⟨cur + 2, by omega⟩ : Wire M) w2 i).val < cur + 4 := by
  dsimp only [mod3NextW2]
  split_ifs
  · exact show cur + 2 < cur + 4 by omega
  · exact lt_trans (hw2_lt ⟨i.val + 1, by omega⟩) (by omega)
theorem mod3NextW1_inj {M steps : ℕ} {cur : ℕ} (hcur : cur + 4 ≤ M)
    (w1 : Fin (steps + 3) → Wire M) (hw1_lt : ∀ i, (w1 i).val < cur)
    (hw1_inj : Function.Injective w1) : Function.Injective
      (mod3NextW1 (⟨cur, by omega⟩ : Wire M) (⟨cur + 3, by omega⟩ : Wire M) w1) := fun i j hij ↦ by
  have hv := congrArg Fin.val hij
  have := hw1_lt ⟨i.val + 1, by omega⟩
  have := hw1_lt ⟨j.val + 1, by omega⟩
  dsimp only [mod3NextW1] at hij hv
  split_ifs at hij hv
  all_goals try exact Fin.ext (by
    dsimp at hv
    omega)
  have hinj := congrArg Fin.val (hw1_inj hij)
  exact Fin.ext (by
    dsimp at hinj
    omega)
theorem mod3NextW2_inj {M steps : ℕ} {cur : ℕ} (hcur : cur + 4 ≤ M)
    (w2 : Fin (steps + 3) → Wire M) (hw2_lt : ∀ i, (w2 i).val < cur)
    (hw2_inj : Function.Injective w2) :
    Function.Injective (mod3NextW2 (⟨cur + 2, by omega⟩ : Wire M) w2) := fun i j hij ↦ by
  have hv := congrArg Fin.val hij
  have := hw2_lt ⟨i.val + 1, by omega⟩
  have := hw2_lt ⟨j.val + 1, by omega⟩
  dsimp only [mod3NextW2] at hij hv
  split_ifs at hij hv
  all_goals try exact Fin.ext (by
    dsimp at hv
    omega)
  have hinj := congrArg Fin.val (hw2_inj hij)
  exact Fin.ext (by
    dsimp at hinj
    omega)
def withMod3AllOnesReduce {M : ℕ} :
    (steps cur : ℕ) → cur + 4 * steps ≤ M → (w1 w2 : Fin (steps + 2) → Wire M) →
    (∀ i, (w1 i).val < cur) → (∀ i, (w2 i).val < cur) →
    Function.Injective w1 → Function.Injective w2 →
    ((a1 b1 a2 b2 : Wire M) → a1 ≠ b1 → a2 ≠ b2 → a1.val < cur + 4 * steps →
      b1.val < cur + 4 * steps → a2.val < cur + 4 * steps → b2.val < cur + 4 * steps →
      TempPhaseProg M) → TempPhaseProg M
  | 0, _, _, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj, kBody =>
      kBody (w1 0) (w1 1) (w2 0) (w2 1) (hw1_inj.ne fin_0_ne_1) (hw2_inj.ne fin_0_ne_1)
        (hw1_lt 0) (hw1_lt 1) (hw2_lt 0) (hw2_lt 1)
  | steps + 1, cur, hcur, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj, kBody =>
      withFullAdd cur (by omega) (w1 0) (w1 1) (w1 2)
        (hw1_inj.ne fin_0_ne_1) (hw1_inj.ne fin_0_ne_2) (hw1_inj.ne fin_1_ne_2)
        (hw1_lt 0) (hw1_lt 1) (hw1_lt 2)
        (withFullAdd (cur + 2) (by omega) ⟨cur + 1, by omega⟩ (w2 0) (w2 1)
          (w3_mk_ne_of_gt (lt_trans (hw2_lt 0) (by omega)))
          (w3_mk_ne_of_gt (lt_trans (hw2_lt 1) (by omega))) (hw2_inj.ne fin_0_ne_1)
          (show cur + 1 < cur + 2 by omega) (lt_trans (hw2_lt 0) (by omega))
          (lt_trans (hw2_lt 1) (by omega))
          (withMod3AllOnesReduce steps (cur + 4) (by omega)
            (mod3NextW1 ⟨cur, by omega⟩ ⟨cur + 3, by omega⟩ w1)
            (mod3NextW2 ⟨cur + 2, by omega⟩ w2)
            (mod3NextW1_lt (by omega) w1 hw1_lt) (mod3NextW2_lt (by omega) w2 hw2_lt)
            (mod3NextW1_inj (by omega) w1 hw1_lt hw1_inj)
            (mod3NextW2_inj (by omega) w2 hw2_lt hw2_inj)
            (fun a1 b1 a2 b2 h12 h34 _ _ _ _ ↦
              kBody a1 b1 a2 b2 h12 h34 (by omega) (by omega) (by omega) (by omega))))
theorem withMod3AllOnesReduce_countTempAnd {M : ℕ} :
    ∀ (steps cur : ℕ) (hcur : cur + 4 * steps ≤ M)
      (w1 w2 : Fin (steps + 2) → Wire M)
      (hw1_lt : ∀ i, (w1 i).val < cur) (hw2_lt : ∀ i, (w2 i).val < cur)
      (hw1_inj : Function.Injective w1) (hw2_inj : Function.Injective w2)
      (kBody : (a1 b1 a2 b2 : Wire M) → a1 ≠ b1 → a2 ≠ b2 →
        a1.val < cur + 4 * steps → b1.val < cur + 4 * steps →
        a2.val < cur + 4 * steps → b2.val < cur + 4 * steps → TempPhaseProg M) (N : ℕ),
      (∀ a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2,
        (kBody a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2).countTempAnd = N) →
      (withMod3AllOnesReduce steps cur hcur w1 w2 hw1_lt hw2_lt hw1_inj
        hw2_inj kBody).countTempAnd = 2 * steps + N
  | 0, _, _, _, _, _, _, _, _, _, _, hN => by
      simpa [withMod3AllOnesReduce] using hN _ _ _ _ _ _ _ _ _ _
  | steps + 1, cur, _, _, _, _, _, _, _, _, N, hN => by
      rw [withMod3AllOnesReduce, withFullAdd_countTempAnd, withFullAdd_countTempAnd,
        withMod3AllOnesReduce_countTempAnd steps (cur + 4) _ _ _ _ _ _ _ _ N
          (fun a1 b1 a2 b2 h12 h34 _ _ _ _ ↦ hN a1 b1 a2 b2 h12 h34 _ _ _ _)]
      omega
theorem sum_fin_succ1 {α : Type*} [AddCommMonoid α] {n : ℕ} (f : Fin (n + 1) → α) :
    (∑ i : Fin (n + 1), f i) = f 0 + ∑ k : Fin n, f ⟨k.val + 1, by omega⟩ := by
  rw [Fin.sum_univ_succ]
  exact congrArg (f 0 + ·) (Finset.sum_congr rfl fun _ _ ↦ congrArg f (Fin.ext rfl))
theorem sum_fin_succ2 {α : Type*} [AddCommMonoid α] {n : ℕ} (f : Fin (n + 2) → α) :
    (∑ i : Fin (n + 2), f i) = f 0 + f 1 + ∑ k : Fin n, f ⟨k.val + 2, by omega⟩ := by
  rw [sum_fin_succ1 f, sum_fin_succ1 (fun k : Fin (n + 1) ↦ f ⟨k.val + 1, by omega⟩),
    ← add_assoc]
  exact congrArg₂ (· + ·) (congrArg (f 0 + ·) (congrArg f (Fin.ext (Nat.zero_add 1).symm)))
    (Finset.sum_congr rfl fun k _ ↦
      congrArg f (Fin.ext (show k.val + 1 + 1 = k.val + 2 by omega)))
theorem sum_fin_succ3 {α : Type*} [AddCommMonoid α] {n : ℕ} (f : Fin (n + 3) → α) :
    (∑ i : Fin (n + 3), f i) = f 0 + f 1 + f 2 + ∑ k : Fin n, f ⟨k.val + 3, by omega⟩ := by
  rw [sum_fin_succ2 f, sum_fin_succ1 (fun k : Fin (n + 1) ↦ f ⟨k.val + 2, by omega⟩),
    ← add_assoc]
  exact congrArg₂ (· + ·) (congrArg (f 0 + f 1 + ·)
    (congrArg f (Fin.ext (show 0 + 2 = 2 % (n + 3) from (Nat.mod_eq_of_lt (by omega)).symm))))
    (Finset.sum_congr rfl fun k _ ↦
      congrArg f (Fin.ext (show k.val + 1 + 2 = k.val + 3 by omega)))
theorem prod_fin_succ1 {α : Type*} [CommMonoid α] {n : ℕ} (f : Fin (n + 1) → α) :
    (∏ i : Fin (n + 1), f i) = f 0 * ∏ k : Fin n, f ⟨k.val + 1, by omega⟩ := by
  rw [Fin.prod_univ_succ]
  exact congrArg (f 0 * ·) (Finset.prod_congr rfl fun _ _ ↦ congrArg f (Fin.ext rfl))
theorem prod_fin_succ2 {α : Type*} [CommMonoid α] {n : ℕ} (f : Fin (n + 2) → α) :
    (∏ i : Fin (n + 2), f i) = f 0 * f 1 * ∏ k : Fin n, f ⟨k.val + 2, by omega⟩ := by
  rw [prod_fin_succ1 f, prod_fin_succ1 (fun k : Fin (n + 1) ↦ f ⟨k.val + 1, by omega⟩),
    ← mul_assoc]
  exact congrArg₂ (· * ·) (congrArg (f 0 * ·) (congrArg f (Fin.ext (Nat.zero_add 1).symm)))
    (Finset.prod_congr rfl fun k _ ↦
      congrArg f (Fin.ext (show k.val + 1 + 1 = k.val + 2 by omega)))
theorem prod_fin_succ3 {α : Type*} [CommMonoid α] {n : ℕ} (f : Fin (n + 3) → α) :
    (∏ i : Fin (n + 3), f i) = f 0 * f 1 * f 2 * ∏ k : Fin n, f ⟨k.val + 3, by omega⟩ := by
  rw [prod_fin_succ2 f, prod_fin_succ1 (fun k : Fin (n + 1) ↦ f ⟨k.val + 2, by omega⟩),
    ← mul_assoc]
  exact congrArg₂ (· * ·) (congrArg (f 0 * f 1 * ·)
    (congrArg f (Fin.ext (show 0 + 2 = 2 % (n + 3) from (Nat.mod_eq_of_lt (by omega)).symm))))
    (Finset.prod_congr rfl fun k _ ↦ congrArg f
      (Fin.ext (show k.val + 1 + 2 = k.val + 3 by omega)))
theorem ScopedBlock.withMod3AllOnesReduce_block {M : ℕ} :
    ∀ (steps cur : ℕ) (hcur : cur + 4 * steps ≤ M) (w1 w2 : Fin (steps + 2) → Wire M)
      (hw1_lt : ∀ i, (w1 i).val < cur) (hw2_lt : ∀ i, (w2 i).val < cur)
      (hw1_inj : Function.Injective w1) (hw2_inj : Function.Injective w2)
      (kBody : (a1 b1 a2 b2 : Wire M) → a1 ≠ b1 → a2 ≠ b2 → a1.val < cur + 4 * steps →
        b1.val < cur + 4 * steps → a2.val < cur + 4 * steps → b2.val < cur + 4 * steps →
        TempPhaseProg M) (leaf : TempPhaseProg M)
      (sBody : Wire M → Wire M → Wire M → Wire M → BitAssignment M → BitAssignment M),
      (∀ a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2, ScopedBlock M (M - (cur + 4 * steps))
        (sBody a1 b1 a2 b2) leaf (kBody a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2)) →
      ∃ (a1 b1 a2 b2 : Wire M) (_ : a1 ≠ b1) (_ : a2 ≠ b2) (_ : a1.val < cur + 4 * steps)
        (_ : b1.val < cur + 4 * steps) (_ : a2.val < cur + 4 * steps)
        (_ : b2.val < cur + 4 * steps) (setup : BitAssignment M → BitAssignment M),
        ScopedBlock M (M - cur) (fun β ↦ sBody a1 b1 a2 b2 (setup β)) leaf
          (withMod3AllOnesReduce steps cur hcur w1 w2 hw1_lt hw2_lt hw1_inj hw2_inj kBody) ∧
        ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - (cur + 4 * steps)) (setup β) ∧
          (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
          (((setup β a1).val + (setup β b1).val + 2 * ((setup β a2).val + (setup β b2).val)) % 3 =
            ((∑ i : Fin (steps + 2), (β (w1 i)).val) +
              2 * (∑ i : Fin (steps + 2), (β (w2 i)).val)) % 3) ∧
          (setup β a1 * setup β b1 * (setup β a2 * setup β b2) =
            (∏ i : Fin (steps + 2), β (w1 i)) * (∏ i : Fin (steps + 2), β (w2 i)))
  | 0, _, _, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj, kBody, _, _, hK =>
      ⟨w1 0, w1 1, w2 0, w2 1, hw1_inj.ne fin_0_ne_1, hw2_inj.ne fin_0_ne_1,
        hw1_lt 0, hw1_lt 1, hw2_lt 0, hw2_lt 1, id, hK (w1 0) (w1 1) (w2 0) (w2 1) _ _ _ _ _ _,
        fun _ hβ ↦ ⟨hβ, fun _ _ ↦ rfl, by simp [Fin.sum_univ_two], by simp [Fin.prod_univ_two]⟩⟩
  | steps + 1, cur, hcur, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj, kBody, leaf, sBody, hK => by
      let s1 : Wire M := ⟨cur, by omega⟩
      let c2 : Wire M := ⟨cur + 1, by omega⟩
      let s2 : Wire M := ⟨cur + 2, by omega⟩
      let c1 : Wire M := ⟨cur + 3, by omega⟩
      let w1' := mod3NextW1 s1 c1 w1
      let w2' := mod3NextW2 s2 w2
      obtain ⟨a1, b1, a2, b2, h12, h34, _, _, _, _, stIn, hIn, hSpecIn⟩ :=
        ScopedBlock.withMod3AllOnesReduce_block steps (cur + 4) (by omega) w1' w2'
          (mod3NextW1_lt (by omega) w1 hw1_lt) (mod3NextW2_lt (by omega) w2 hw2_lt)
          (mod3NextW1_inj (by omega) w1 hw1_lt hw1_inj)
          (mod3NextW2_inj (by omega) w2 hw2_lt hw2_inj)
          (fun x1 y1 x2 y2 p12 p34 _ _ _ _ ↦ kBody x1 y1 x2 y2 p12 p34
            (by omega) (by omega) (by omega) (by omega)) leaf sBody
          (fun x1 y1 x2 y2 p12 p34 _ _ _ _ ↦ (hK x1 y1 x2 y2 p12 p34
            (by omega) (by omega) (by omega) (by omega)).cast_rem (by omega))
      have hFA1 := ScopedBlock.withFullAdd_block (M := M) cur (by omega) (w1 0) (w1 1) (w1 2)
        (hw1_inj.ne fin_0_ne_1) (hw1_inj.ne fin_0_ne_2) (hw1_inj.ne fin_1_ne_2)
        (hw1_lt 0) (hw1_lt 1) (hw1_lt 2)
        (ScopedBlock.withFullAdd_block (M := M) (cur + 2) (by omega) c2 (w2 0) (w2 1)
          (w3_mk_ne_of_gt (lt_trans (hw2_lt 0) (by omega)))
          (w3_mk_ne_of_gt (lt_trans (hw2_lt 1) (by omega))) (hw2_inj.ne fin_0_ne_1)
          (show cur + 1 < cur + 2 by omega) (lt_trans (hw2_lt 0) (by omega))
          (lt_trans (hw2_lt 1) (by omega)) (hIn.cast_rem (by omega)))
      let setupStep (β : BitAssignment M) := stIn (fullAddSetup (cur + 2) (by omega) c2 (w2 0)
        (w2 1) (fullAddSetup cur (by omega) (w1 0) (w1 1) (w1 2) β))
      refine ⟨a1, b1, a2, b2, h12, h34, by omega, by omega, by omega, by omega, setupStep,
        hFA1, fun β hβ ↦ ?_⟩
      let β₁ := fullAddSetup cur (by omega) (w1 0) (w1 1) (w1 2) β
      let β₂ := fullAddSetup (cur + 2) (by omega) c2 (w2 0) (w2 1) β₁
      have hβ₁_lt (w : Wire M) (hw : w.val < cur) : β₁ w = β w :=
        w3_fullAdd_lt cur (by omega) (w1 0) (w1 1) (w1 2) w β hw
      have hβ₂_lt (w : Wire M) (hw : w.val < cur + 2) : β₂ w = β₁ w :=
        w3_fullAdd_lt (cur + 2) (by omega) c2 (w2 0) (w2 1) w β₁ hw
      obtain ⟨hclIn, hbelIn, hmodIn, hprodIn⟩ := hSpecIn β₂ (w3_fullAdd_clean (by omega) c2 (w2 0)
        (w2 1) (by omega) (w3_fullAdd_clean (by omega) (w1 0) (w1 1) (w1 2) (by omega)
          (cleanRem_anti (by omega) hβ)))
      have hs1_v : β₂ s1 = β (w1 0) + β (w1 1) + β (w1 2) :=
        (hβ₂_lt s1 (show cur < cur + 2 by omega)).trans
          (w3_fullAdd_sum cur (by omega) (w1 0) (w1 1) (w1 2) β)
      have hc2_v : β₁ c2 = β (w1 2) + (β (w1 0) + β (w1 2)) * (β (w1 1) + β (w1 2)) :=
        Function.update_self _ _ _
      have hs2_v : β₂ s2 = β₁ c2 + β (w2 0) + β (w2 1) :=
        (w3_fullAdd_sum (cur + 2) (by omega) c2 (w2 0) (w2 1) β₁).trans
          (by rw [hβ₁_lt _ (hw2_lt 0), hβ₁_lt _ (hw2_lt 1)])
      have hc1_v : β₂ c1 = β (w2 1) + (β₁ c2 + β (w2 1)) * (β (w2 0) + β (w2 1)) :=
        (Function.update_self _ _ _).trans (by rw [hβ₁_lt _ (hw2_lt 0), hβ₁_lt _ (hw2_lt 1)])
      have hw1'_r (k : Fin steps) : β₂ (w1' ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩) =
          β (w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩) := by
        have hklt := hw1_lt ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩
        have hdef : w1' ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ =
            w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩ := by
          dsimp only [w1', mod3NextW1]
          rw [ite_neg_eq (Nat.succ_ne_zero (k.val + 1)),
            ite_neg_eq fun h ↦ Nat.succ_ne_zero k.val (Nat.succ.inj h)]
        exact (congrArg β₂ hdef).trans ((hβ₂_lt _ (lt_trans hklt (by omega))).trans (hβ₁_lt _ hklt))
      have hw2'_r (k : Fin (steps + 1)) : β₂ (w2' ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩) =
          β (w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩) := by
        have hklt := hw2_lt ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩
        have hdef : w2' ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩ =
            w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ := by
          dsimp only [w2', mod3NextW2]
          exact ite_neg_eq (Nat.succ_ne_zero k.val)
        exact (congrArg β₂ hdef).trans ((hβ₂_lt _ (lt_trans hklt (by omega))).trans (hβ₁_lt _ hklt))
      refine ⟨by simpa [show cur + 4 + 4 * steps = cur + 4 * (steps + 1) by omega] using hclIn,
        fun w hw ↦ (hbelIn w (by omega)).trans ((hβ₂_lt w (by omega)).trans (hβ₁_lt w hw)), ?_, ?_⟩
      · dsimp only [setupStep]
        rw [hmodIn, sum_fin_succ2 (fun i : Fin (steps + 2) ↦ (β₂ (w1' i)).val),
          sum_fin_succ1 (fun i : Fin (steps + 1 + 1) ↦ (β₂ (w2' i)).val),
          sum_fin_succ3 (fun i : Fin (steps + 1 + 2) ↦ (β (w1 i)).val),
          sum_fin_succ2 (fun i : Fin (steps + 1 + 2) ↦ (β (w2 i)).val),
          show β₂ (w1' 0) = β₂ s1 from rfl, show β₂ (w1' 1) = β₂ c1 from rfl,
          show β₂ (w2' 0) = β₂ s2 from rfl,
          Finset.sum_congr rfl fun k _ ↦ congrArg ZMod.val (hw1'_r k),
          Finset.sum_congr rfl fun k _ ↦ congrArg ZMod.val (hw2'_r k)]
        have := hs1_v ▸ hc2_v ▸ fullAdd_val_eq (β (w1 0)) (β (w1 1)) (β (w1 2))
        have := hs2_v ▸ hc1_v ▸ fullAdd_val_eq (β₁ c2) (β (w2 0)) (β (w2 1))
        omega
      · dsimp only [setupStep]
        rw [hprodIn, prod_fin_succ2 (fun i : Fin (steps + 2) ↦ β₂ (w1' i)),
          prod_fin_succ1 (fun i : Fin (steps + 1 + 1) ↦ β₂ (w2' i)),
          prod_fin_succ3 (fun i : Fin (steps + 1 + 2) ↦ β (w1 i)),
          prod_fin_succ2 (fun i : Fin (steps + 1 + 2) ↦ β (w2 i)),
          show β₂ (w1' 0) = β₂ s1 from rfl, show β₂ (w1' 1) = β₂ c1 from rfl,
          show β₂ (w2' 0) = β₂ s2 from rfl, Finset.prod_congr rfl fun k _ ↦ hw1'_r k,
          Finset.prod_congr rfl fun k _ ↦ hw2'_r k]
        have h1 : β₂ s1 * β₁ c2 = β (w1 0) * β (w1 1) * β (w1 2) :=
          hs1_v ▸ hc2_v ▸ fullAdd_and_eq _ _ _
        have h2 : β₂ s2 * β₂ c1 = β₁ c2 * β (w2 0) * β (w2 1) :=
          hs2_v ▸ hc1_v ▸ fullAdd_and_eq _ _ _
        calc β₂ s1 * β₂ c1 * (∏ k : Fin steps, β (w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩)) *
            (β₂ s2 * ∏ k : Fin (steps + 1), β (w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩))
            = (β₂ s1 * (β₂ s2 * β₂ c1)) *
                (∏ k : Fin steps, β (w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩)) *
              (∏ k : Fin (steps + 1), β (w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩)) := by ring
          _ = _ := by
              rw [h2, show β₂ s1 * (β₁ c2 * β (w2 0) * β (w2 1)) =
                (β₂ s1 * β₁ c2) * (β (w2 0) * β (w2 1)) by ring, h1]
              ring
theorem tailDecode_algebra (vs1 vd1 vt2 vbp : ZMod 2) :
    let vall := vt2 * vd1
    let vw1 := (vd1 + vall) * (vbp + 1)
    let vw2 := (vt2 + 1 + vbp + vall + vw1) * (vs1 + vbp + vw1)
    let ax := (vs1.val + vd1.val + vbp.val + 2 * vt2.val) % 3
    (vs1 + vd1 + vt2 + vw1 + vw2) = (if ax = 2 then 1 else 0) ∧
      (ax ≠ 2 → (vd1 + vbp + vall + vw2) = (if ax = 1 then 1 else 0)) := by decide +revert
def withSlot0TailDecode {M : ℕ} (cur : ℕ) (hcur : cur + 9 ≤ M) (a1 b1 a2 b2 bParW : Wire M)
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (ha1 : a1.val < cur) (hb1 : b1.val < cur)
    (ha2 : a2.val < cur) (hb2 : b2.val < cur) (hbp : bParW.val < cur) (body : TempPhaseProg M)
    : TempPhaseProg M :=
  let s1 : Wire M := ⟨cur, by omega⟩
  let t2 : Wire M := ⟨cur + 2, by omega⟩
  let d1 : Wire M := ⟨cur + 3, by omega⟩
  let allW : Wire M := ⟨cur + 4, by omega⟩
  let w1W : Wire M := ⟨cur + 5, by omega⟩
  let w2W : Wire M := ⟨cur + 6, by omega⟩
  let selAW : Wire M := ⟨cur + 7, by omega⟩
  let selBW : Wire M := ⟨cur + 8, hcur⟩
  let cPreW1 : CliffProg M := .seq (.cnot allW d1 (w3_mk_ne (by omega))) (.x bParW)
  let cPreW2 : CliffProg M := .seq (.x t2) (.seq (.cnot bParW t2 (w3_ne_mk_of_lt (by omega)))
    (.seq (.cnot allW t2 (w3_mk_ne (by omega))) (.seq (.cnot w1W t2 (w3_mk_ne (by omega)))
      (.seq (.cnot bParW s1 (wire_ne_of_lt hbp)) (.cnot w1W s1 (w3_mk_ne (by omega)))))))
  let cSelAB : CliffProg M := .seq (.cnot d1 selAW (w3_mk_ne (by omega)))
    (.seq (.cnot bParW selAW (w3_ne_mk_of_lt (by omega)))
      (.seq (.cnot allW selAW (w3_mk_ne (by omega)))
        (.seq (.cnot w2W selAW (w3_mk_ne (by omega)))
          (.seq (.cnot s1 selBW (w3_mk_ne (by omega)))
            (.seq (.cnot d1 selBW (w3_mk_ne (by omega)))
              (.seq (.cnot t2 selBW (w3_mk_ne (by omega)))
                (.seq (.cnot w1W selBW (w3_mk_ne (by omega)))
                  (.cnot w2W selBW (w3_mk_ne (by omega))))))))))
  withHalfAdd0 cur (by omega) a1 b1 hab1 ha1 hb1
    (withFullAdd (cur + 2) (by omega) ⟨cur + 1, by omega⟩ a2 b2
      (w3_mk_ne_of_gt (by omega)) (w3_mk_ne_of_gt (by omega)) hab2
      (show cur + 1 < cur + 2 by omega) (by omega) (by omega)
      (withTempBit t2 d1 allW (w3_mk_ne (by omega)) (w3_mk_ne (by omega))
        (w3_mk_ne (by omega))
        (withAffineAnd (cur + 5) (by omega) cPreW1 d1 bParW (w3_mk_ne_of_gt (by omega))
          (show cur + 3 < cur + 5 by omega) (by omega)
          (withAffineAnd (cur + 6) (by omega) cPreW2 t2 s1 (w3_mk_ne (by omega))
            (show cur + 2 < cur + 6 by omega) (show cur < cur + 6 by omega)
            (withCliffAlloc cSelAB body)))))
@[simp] theorem withSlot0TailDecode_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 9 ≤ M)
    (a1 b1 a2 b2 bParW : Wire M) (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (ha1 : a1.val < cur)
    (hb1 : b1.val < cur) (ha2 : a2.val < cur) (hb2 : b2.val < cur) (hbp : bParW.val < cur)
    (body : TempPhaseProg M) : (withSlot0TailDecode cur hcur a1 b1 a2 b2 bParW hab1 hab2 ha1
    hb1 ha2 hb2 hbp body).countTempAnd = 5 + body.countTempAnd := by
  simp [withSlot0TailDecode]
  omega
theorem ScopedBlock.withSlot0TailDecode_block {M : ℕ} (cur : ℕ) (hcur : cur + 9 ≤ M)
    (a1 b1 a2 b2 bParW : Wire M) (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2)
    (ha1 : a1.val < cur) (hb1 : b1.val < cur) (ha2 : a2.val < cur) (hb2 : b2.val < cur)
    (hbp : bParW.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 9)) sBody leaf body) :
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
        (withSlot0TailDecode cur hcur a1 b1 a2 b2 bParW hab1 hab2 ha1 hb1 ha2 hb2 hbp body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - cur) β →
        cleanRem M (M - (cur + 9)) (setup β) ∧ (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
        setup β ⟨cur + 4, by omega⟩ = β a1 * β b1 * (β a2 * β b2) ∧
        (let ax := ((β a1).val + (β b1).val + 2 * ((β a2).val + (β b2).val) + (β bParW).val) % 3
         setup β ⟨cur + 8, hcur⟩ = (if ax = 2 then 1 else 0) ∧
           (ax ≠ 2 → setup β ⟨cur + 7, by omega⟩ = (if ax = 1 then 1 else 0))) := by
  let s1 : Wire M := ⟨cur, by omega⟩
  let c2_w : Wire M := ⟨cur + 1, by omega⟩
  let t2 : Wire M := ⟨cur + 2, by omega⟩
  let d1 : Wire M := ⟨cur + 3, by omega⟩
  let allOnesW : Wire M := ⟨cur + 4, by omega⟩
  let w1W : Wire M := ⟨cur + 5, by omega⟩
  let w2W : Wire M := ⟨cur + 6, by omega⟩
  let selAW : Wire M := ⟨cur + 7, by omega⟩
  let selBW : Wire M := ⟨cur + 8, hcur⟩
  let cPreW1 : CliffProg M := .seq (.cnot allOnesW d1 (w3_mk_ne (by omega))) (.x bParW)
  let cPreW2 : CliffProg M := .seq (.x t2) (.seq (.cnot bParW t2 (w3_ne_mk_of_lt (by omega)))
    (.seq (.cnot allOnesW t2 (w3_mk_ne (by omega))) (.seq (.cnot w1W t2 (w3_mk_ne (by omega)))
      (.seq (.cnot bParW s1 (w3_ne_mk_of_lt hbp)) (.cnot w1W s1 (w3_mk_ne (by omega)))))))
  let cSelAB : CliffProg M := .seq (.cnot d1 selAW (w3_mk_ne (by omega)))
    (.seq (.cnot bParW selAW (w3_ne_mk_of_lt (by omega)))
      (.seq (.cnot allOnesW selAW (w3_mk_ne (by omega)))
        (.seq (.cnot w2W selAW (w3_mk_ne (by omega)))
          (.seq (.cnot s1 selBW (w3_mk_ne (by omega)))
            (.seq (.cnot d1 selBW (w3_mk_ne (by omega)))
              (.seq (.cnot t2 selBW (w3_mk_ne (by omega)))
                (.seq (.cnot w1W selBW (w3_mk_ne (by omega)))
                  (.cnot w2W selBW (w3_mk_ne (by omega))))))))))
  have hcSel : cSelAB.SupportsBelow (cur + 9) := by
    dsimp [cSelAB, CliffProg.SupportsBelow, s1, t2, d1, allOnesW, w1W, w2W, selAW, selBW]
    omega
  have hcW2 : cPreW2.SupportsBelow (cur + 6) := by
    dsimp [cPreW2, CliffProg.SupportsBelow, s1, t2, allOnesW, w1W]
    omega
  have hcW1 : cPreW1.SupportsBelow (cur + 5) := by
    dsimp [cPreW1, CliffProg.SupportsBelow, d1, allOnesW]
    omega
  have h1 := ScopedBlock.withHalfAdd0_block (M := M) cur (by omega) a1 b1 hab1 ha1 hb1
    (ScopedBlock.withFullAdd_block (M := M) (cur + 2) (by omega) c2_w a2 b2
      (w3_mk_ne_of_gt (by omega)) (w3_mk_ne_of_gt (by omega)) hab2
      (show cur + 1 < cur + 2 by omega) (by omega) (by omega)
      (ScopedBlock.withTempBit_block (M := M) (cur + 4) (by omega) t2 d1 (w3_mk_ne (by omega))
        (show cur + 2 < cur + 4 by omega) (show cur + 3 < cur + 4 by omega)
        (ScopedBlock.withAffineAnd_block (M := M) (cur + 5) (by omega) cPreW1 hcW1 d1 bParW
          (w3_mk_ne_of_gt (by omega)) (show cur + 3 < cur + 5 by omega) (by omega)
          (ScopedBlock.withAffineAnd_block (M := M) (cur + 6) (by omega) cPreW2 hcW2 t2 s1
            (w3_mk_ne (by omega)) (show cur + 2 < cur + 6 by omega)
            (show cur < cur + 6 by omega)
            (w3_withCliffAlloc_cur (cur + 7) (cur + 9) hcur (by omega) cSelAB hcSel hBody)))))
  let setup (β : BitAssignment M) : BitAssignment M :=
    let γ2 := fullAddSetup (cur + 2) (by omega) c2_w a2 b2
      (halfAdd0Setup cur (by omega) a1 b1 β)
    let γ3 := Function.update γ2 allOnesW (γ2 t2 * γ2 d1)
    let γ4 := Function.update γ3 w1W (cPreW1.eval γ3 d1 * cPreW1.eval γ3 bParW)
    cSelAB.eval (Function.update γ4 w2W (cPreW2.eval γ4 t2 * cPreW2.eval γ4 s1))
  refine ⟨setup, h1, fun β hβ ↦ ?_⟩
  let γ1 := halfAdd0Setup cur (by omega) a1 b1 β
  let γ2 := fullAddSetup (cur + 2) (by omega) c2_w a2 b2 γ1
  let γ3 := Function.update γ2 allOnesW (γ2 t2 * γ2 d1)
  let γ4 := Function.update γ3 w1W (cPreW1.eval γ3 d1 * cPreW1.eval γ3 bParW)
  let γ5 := Function.update γ4 w2W (cPreW2.eval γ4 t2 * cPreW2.eval γ4 s1)
  let out := cSelAB.eval γ5
  have hγ5_clean7 : cleanRem M (M - (cur + 7)) γ5 :=
    w3_cleanRem_upd_mk (by omega) (w3_cleanRem_upd_mk (by omega)
      (w3_cleanRem_upd_mk (by omega) (w3_fullAdd_clean (by omega) c2_w a2 b2 (by omega)
        (w3_halfAdd0_clean (by omega) a1 b1 (by omega) (cleanRem_anti (by omega) hβ)))))
  have hγ5_below7 (w : Wire M) (hw : w.val < cur + 7) : out w = γ5 w := by
    dsimp only [out, cSelAB, CliffProg.eval]
    have hB : w ≠ selBW := w3_ne_mk_of_lt (by omega)
    have hA : w ≠ selAW := w3_ne_mk_of_lt hw
    rw [Function.update_of_ne hB, Function.update_of_ne hB, Function.update_of_ne hB,
      Function.update_of_ne hB, Function.update_of_ne hB, Function.update_of_ne hA,
      Function.update_of_ne hA, Function.update_of_ne hA, Function.update_of_ne hA]
  have hbel2 (w : Wire M) (hw : w.val < cur) : γ2 w = β w :=
    (w3_fullAdd_lt (cur + 2) (by omega) c2_w a2 b2 w γ1 (by omega)).trans
      (halfAdd0Setup_lt cur (by omega) a1 b1 w β hw)
  have hbel_cur (w : Wire M) (hw : w.val < cur) : out w = β w :=
    (hγ5_below7 w (by omega)).trans (by
      dsimp only [γ5, γ4, γ3]
      rw [Function.update_of_ne (w3_ne_mk_of_lt (by omega) : w ≠ w2W),
        Function.update_of_ne (w3_ne_mk_of_lt (by omega) : w ≠ w1W),
        Function.update_of_ne (w3_ne_mk_of_lt (by omega) : w ≠ allOnesW), hbel2 w hw])
  have hc2_v : γ1 c2_w = β a1 * β b1 := Function.update_self _ _ _
  have hs1_2 : γ2 s1 = β a1 + β b1 := (w3_fullAdd_lt (cur + 2) (by omega) c2_w a2 b2 s1 γ1
    (show cur < cur + 2 by omega)).trans (halfAdd0Setup_sum cur (by omega) a1 b1 β)
  have ht2_2 : γ2 t2 = γ1 c2_w + β a2 + β b2 :=
    (w3_fullAdd_sum (cur + 2) (by omega) c2_w a2 b2 γ1).trans (by
      dsimp only [γ1]
      rw [halfAdd0Setup_lt cur (by omega) a1 b1 a2 β ha2,
        halfAdd0Setup_lt cur (by omega) a1 b1 b2 β hb2])
  have hd1_2 : γ2 d1 = β b2 + (γ1 c2_w + β b2) * (β a2 + β b2) :=
    (Function.update_self _ _ _).trans (by
      dsimp only [γ1]
      rw [halfAdd0Setup_lt cur (by omega) a1 b1 a2 β ha2,
        halfAdd0Setup_lt cur (by omega) a1 b1 b2 β hb2])
  let vs1 := γ2 s1
  let vd1 := γ2 d1
  let vt2 := γ2 t2
  let vbp := β bParW
  let vw1 := (vd1 + vt2 * vd1) * (vbp + 1)
  let vw2 := (vt2 + 1 + vbp + vt2 * vd1 + vw1) * (vs1 + vbp + vw1)
  have hw1_4 : γ4 ⟨cur + 5, by omega⟩ = vw1 := by
    simp [γ4, γ3, cPreW1, CliffProg.eval, d1, allOnesW, w1W,
      w3_lt_ne_add hbp, w3_add_ne_lt hbp, hbel2 bParW hbp, vd1, vt2, vbp, vw1]
  have hw2_5 : γ5 w2W = vw2 := by
    change Function.update γ4 w2W (cPreW2.eval γ4 t2 * cPreW2.eval γ4 s1) w2W = vw2
    rw [Function.update_self]
    simp [cPreW2, CliffProg.eval, s1, t2, allOnesW, w1W, w3_lt_ne_add hbp, hw1_4]
    simp [γ4, γ3, s1, t2, d1, allOnesW, w1W, w3_lt_ne_add hbp, hbel2 bParW hbp,
      vs1, vd1, vt2, vbp, vw2]
  have hw1_5 : γ5 ⟨cur + 5, by omega⟩ = vw1 :=
    (Function.update_of_ne (w3_mk_ne (by omega)) _ _).trans hw1_4
  have hselA_out : out selAW = vd1 + vbp + vt2 * vd1 + vw2 := by
    simp [out, cSelAB, CliffProg.eval, s1, t2, d1, allOnesW, w1W, w2W, selAW, selBW,
      w3_lt_ne_add hbp, w3_cleanRem_mk hγ5_clean7 (by omega : M - (M - (cur + 7)) ≤ cur + 7),
      hw2_5]
    simp [γ5, γ4, γ3, d1, allOnesW, w1W, w2W, w3_lt_ne_add hbp, hbel2 bParW hbp, vd1, vt2, vbp]
  have hselB_out : out selBW = vs1 + vd1 + vt2 + vw1 + vw2 := by
    simp [out, cSelAB, CliffProg.eval, s1, t2, d1, allOnesW, w1W, w2W, selAW, selBW,
      w3_lt_ne_add hbp, w3_cleanRem_mk hγ5_clean7 (by omega : M - (M - (cur + 7)) ≤ cur + 8),
      hw1_5, hw2_5]
    simp [γ5, γ4, γ3, s1, t2, d1, allOnesW, w1W, w2W, vs1, vd1, vt2]
  have hall_out : out allOnesW = β a1 * β b1 * (β a2 * β b2) := by
    rw [hγ5_below7 allOnesW (show cur + 4 < cur + 7 by omega)]
    simp only [γ5, γ4, γ3, Function.update_apply, allOnesW, w1W, w2W, Fin.mk.injEq,
      add_right_inj, Nat.reduceEqDiff, ↓reduceIte, ht2_2, hd1_2, fullAdd_and_eq, hc2_v]
    ring
  have hax_mod : (vs1.val + vd1.val + vbp.val + 2 * vt2.val) % 3 =
      ((β a1).val + (β b1).val + 2 * ((β a2).val + (β b2).val) + (β bParW).val) % 3 := by
    have : vs1.val + 2 * (γ1 c2_w).val = (β a1).val + (β b1).val := by
      rw [show vs1 = β a1 + β b1 from hs1_2, hc2_v]
      exact halfAdd_val_eq (β a1) (β b1)
    have : vt2.val + 2 * vd1.val = (γ1 c2_w).val + (β a2).val + (β b2).val := by
      rw [show vt2 = _ from ht2_2, show vd1 = _ from hd1_2]
      exact fullAdd_val_eq (γ1 c2_w) (β a2) (β b2)
    dsimp only [vbp]
    omega
  obtain ⟨hAlgB, hAlgA⟩ := tailDecode_algebra vs1 vd1 vt2 vbp
  rw [hax_mod] at hAlgB hAlgA
  exact ⟨fun w hw ↦ (cSelAB.eval_outside hcSel γ5 w (by omega)).trans (hγ5_clean7 w (by omega)),
    hbel_cur, hall_out, hselB_out.trans hAlgB, fun hne2 ↦ hselA_out.trans (hAlgA hne2)⟩
theorem mag5_natAbs_eq (u0 u1 u2 u3 u4 u5 : ZMod 2) :
    let c1 := (u0 + 1) * u5
    let c2 := (u1 + u5) * c1
    let c3 := (u2 + u5) * c2
    let uVal := u0.val + u1.val * 2 + u2.val * 4 + u3.val * 8 + u4.val * 16 + u5.val * 32
    (MomSlots01Slot0ElectronKinetic.slot0AxisInt ⟨uVal, by
      have : u0.val < 2 ∧ u1.val < 2 ∧ u2.val < 2 ∧ u3.val < 2 ∧ u4.val < 2 ∧ u5.val < 2 :=
        ⟨u0.val_lt, u1.val_lt, u2.val_lt, u3.val_lt, u4.val_lt, u5.val_lt⟩
      omega⟩).natAbs = u0.val + ((u1 + u5) + c1).val * 2 + ((u2 + u5) + c2).val * 4 +
        ((u3 + u5) + c3).val * 8 + (u4 + u5 + (u3 + u5) * c3).val * 16 := by decide +revert
def mag5Wires {M : ℕ} (cur : ℕ) (hcur : cur + 8 ≤ M) (u0 : Wire M) : Fin 5 → Wire M
  | ⟨0, _⟩ => u0
  | ⟨1, _⟩ => ⟨cur + 1, by omega⟩
  | ⟨2, _⟩ => ⟨cur + 3, by omega⟩
  | ⟨3, _⟩ => ⟨cur + 5, by omega⟩
  | ⟨4, _⟩ => ⟨cur + 7, hcur⟩
def withMag5 {M : ℕ} (cur : ℕ) (hcur : cur + 8 ≤ M) (ax012 : Fin 6 → Wire M)
    (hax_lt : ∀ i, (ax012 i).val < cur) (hax_inj : Function.Injective ax012)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let u0 := ax012 0
  let u1 := ax012 1
  let u2 := ax012 2
  let u3 := ax012 3
  let u4 := ax012 4
  let u5 := ax012 5
  let m4W : Wire M := ⟨cur + 7, hcur⟩
  let cPreSign : CliffProg M := .seq (.x u0) (.seq (.cnot u5 u1 (hax_inj.ne (by decide)))
    (.seq (.cnot u5 u2 (hax_inj.ne (by decide))) (.cnot u5 u3 (hax_inj.ne (by decide)))))
  let cPostMag : CliffProg M := .seq (.cnot u5 u1 (hax_inj.ne (by decide)))
    (.seq (.cnot u5 u2 (hax_inj.ne (by decide))) (.seq (.cnot u5 u3 (hax_inj.ne (by decide)))
      (.seq (.cnot u4 m4W (w3_ne_mk_of_lt (lt_trans (hax_lt 4) (by omega))))
        (.seq (.cnot u5 m4W (w3_ne_mk_of_lt (lt_trans (hax_lt 5) (by omega))))
          (.cnot ⟨cur + 6, by omega⟩ m4W (w3_mk_ne (by omega)))))))
  withCliffAlloc cPreSign (withTempBit u0 u5 ⟨cur, by omega⟩ (hax_inj.ne (by decide))
    (wire_ne_of_lt (hax_lt 0)) (wire_ne_of_lt (hax_lt 5))
    (withCliffAlloc (.x u0)
      (withHalfAdd0 (cur + 1) (by omega) u1 ⟨cur, by omega⟩ (wire_ne_of_lt (hax_lt 1))
        (lt_trans (hax_lt 1) (by omega)) (show cur < cur + 1 by omega)
        (withHalfAdd0 (cur + 3) (by omega) u2 ⟨cur + 2, by omega⟩
          (w3_ne_mk_of_lt (lt_trans (hax_lt 2) (by omega)))
          (lt_trans (hax_lt 2) (by omega)) (show cur + 2 < cur + 3 by omega)
          (withHalfAdd0 (cur + 5) (by omega) u3 ⟨cur + 4, by omega⟩
            (w3_ne_mk_of_lt (lt_trans (hax_lt 3) (by omega)))
            (lt_trans (hax_lt 3) (by omega)) (show cur + 4 < cur + 5 by omega)
            (withCliffAlloc cPostMag body))))))
@[simp] theorem withMag5_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 8 ≤ M)
    (ax012 : Fin 6 → Wire M) (hax_lt : ∀ i, (ax012 i).val < cur)
    (hax_inj : Function.Injective ax012) (body : TempPhaseProg M) :
    (withMag5 cur hcur ax012 hax_lt hax_inj body).countTempAnd = 4 + body.countTempAnd := by
  simp [withMag5]
  omega
theorem ScopedBlock.withMag5_block {M : ℕ} (cur : ℕ) (hcur : cur + 8 ≤ M)
    (ax012 : Fin 6 → Wire M) (hax_lt : ∀ i, (ax012 i).val < cur)
    (hax_inj : Function.Injective ax012) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 8)) sBody leaf body) : ∃
    setup : BitAssignment M → BitAssignment M, ScopedBlock M (M - cur)
    (fun β ↦ sBody (setup β)) leaf (withMag5 cur hcur ax012 hax_lt hax_inj body) ∧ ∀ β :
    BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - (cur + 8)) (setup β) ∧
    (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
    (MomSlots01Slot0ElectronKinetic.slot0AxisInt ⟨bitsVal (fun b : Fin 6 ↦ β (ax012 b)),
    bitsVal_lt_two_pow _⟩).natAbs = bitsVal
    (fun i : Fin 5 ↦ setup β (mag5Wires cur hcur (ax012 0) i)) := by
  let u0 := ax012 0
  let u1 := ax012 1
  let u2 := ax012 2
  let u3 := ax012 3
  let u4 := ax012 4
  let u5 := ax012 5
  let c1_mag : Wire M := ⟨cur, by omega⟩
  let m1W : Wire M := ⟨cur + 1, by omega⟩
  let c2_mag : Wire M := ⟨cur + 2, by omega⟩
  let m2W : Wire M := ⟨cur + 3, by omega⟩
  let c3_mag : Wire M := ⟨cur + 4, by omega⟩
  let m3W : Wire M := ⟨cur + 5, by omega⟩
  let c4_mag : Wire M := ⟨cur + 6, by omega⟩
  let m4W : Wire M := ⟨cur + 7, hcur⟩
  let cPreSign : CliffProg M := .seq (.x u0) (.seq (.cnot u5 u1 (hax_inj.ne (by decide)))
    (.seq (.cnot u5 u2 (hax_inj.ne (by decide))) (.cnot u5 u3 (hax_inj.ne (by decide)))))
  let cPostMag : CliffProg M := .seq (.cnot u5 u1 (hax_inj.ne (by decide)))
    (.seq (.cnot u5 u2 (hax_inj.ne (by decide))) (.seq (.cnot u5 u3 (hax_inj.ne (by decide)))
      (.seq (.cnot u4 m4W (w3_ne_mk_of_lt (lt_trans (hax_lt 4) (by omega))))
        (.seq (.cnot u5 m4W (w3_ne_mk_of_lt (lt_trans (hax_lt 5) (by omega))))
          (.cnot c4_mag m4W (w3_mk_ne (by omega)))))))
  have hcPost : cPostMag.SupportsBelow (cur + 8) := by
    have : (ax012 1).val < cur ∧ (ax012 2).val < cur ∧ (ax012 3).val < cur ∧
        (ax012 4).val < cur ∧ (ax012 5).val < cur :=
      ⟨hax_lt 1, hax_lt 2, hax_lt 3, hax_lt 4, hax_lt 5⟩
    dsimp [cPostMag, CliffProg.SupportsBelow, c4_mag, m4W, u1, u2, u3, u4, u5]
    omega
  have hcPre : cPreSign.SupportsBelow cur := by
    have : (ax012 0).val < cur ∧ (ax012 1).val < cur ∧ (ax012 2).val < cur ∧
        (ax012 3).val < cur ∧ (ax012 5).val < cur :=
      ⟨hax_lt 0, hax_lt 1, hax_lt 2, hax_lt 3, hax_lt 5⟩
    dsimp [cPreSign, CliffProg.SupportsBelow, u0, u1, u2, u3, u5]
    omega
  have h1 := w3_withCliffAlloc_cur cur cur (by omega) le_rfl cPreSign hcPre
    (ScopedBlock.withTempBit_block (M := M) cur (by omega) u0 u5 (hax_inj.ne (by decide))
      (hax_lt 0) (hax_lt 5)
      (w3_withCliffAlloc_cur (cur + 1) (cur + 1) (by omega) le_rfl (.x u0)
        (lt_trans (hax_lt 0) (by omega))
        (ScopedBlock.withHalfAdd0_block (M := M) (cur + 1) (by omega) u1 c1_mag
          (w3_ne_mk_of_lt (hax_lt 1)) (lt_trans (hax_lt 1) (by omega))
          (show cur < cur + 1 by omega)
          (ScopedBlock.withHalfAdd0_block (M := M) (cur + 3) (by omega) u2 c2_mag
            (w3_ne_mk_of_lt (lt_trans (hax_lt 2) (by omega)))
            (lt_trans (hax_lt 2) (by omega)) (show cur + 2 < cur + 3 by omega)
            (ScopedBlock.withHalfAdd0_block (M := M) (cur + 5) (by omega) u3 c3_mag
              (w3_ne_mk_of_lt (lt_trans (hax_lt 3) (by omega)))
              (lt_trans (hax_lt 3) (by omega)) (show cur + 4 < cur + 5 by omega)
              (w3_withCliffAlloc_cur (cur + 7) (cur + 8) hcur (by omega)
                cPostMag hcPost hBody))))))
  let δ5f (β : BitAssignment M) : BitAssignment M :=
    let δ0 := cPreSign.eval β
    let δ2 := (CliffProg.x u0).eval (Function.update δ0 c1_mag (δ0 u0 * δ0 u5))
    halfAdd0Setup (cur + 5) (by omega) u3 c3_mag
      (halfAdd0Setup (cur + 3) (by omega) u2 c2_mag
        (halfAdd0Setup (cur + 1) (by omega) u1 c1_mag δ2))
  let setup (β : BitAssignment M) : BitAssignment M := cPostMag.eval (δ5f β)
  refine ⟨setup, h1, fun β hβ ↦ ?_⟩
  let δ0 := cPreSign.eval β
  let δ1 := Function.update δ0 c1_mag (δ0 u0 * δ0 u5)
  let δ2 := (CliffProg.x u0).eval δ1
  let δ3 := halfAdd0Setup (cur + 1) (by omega) u1 c1_mag δ2
  let δ4 := halfAdd0Setup (cur + 3) (by omega) u2 c2_mag δ3
  let δ5 := halfAdd0Setup (cur + 5) (by omega) u3 c3_mag δ4
  have hδ5_clean7 : cleanRem M (M - (cur + 7)) δ5 :=
    w3_halfAdd0_clean (by omega) u3 c3_mag (by omega)
      (w3_halfAdd0_clean (by omega) u2 c2_mag (by omega)
        (w3_halfAdd0_clean (by omega) u1 c1_mag (by omega)
          (w3_cleanRem_upd (lt_trans (hax_lt 0) (by omega)) (w3_cleanRem_upd_mk (by omega)
            fun w hw ↦ (cPreSign.eval_outside hcPre β w (by omega)).trans (hβ w (by omega))))))
  have hδ0_ax (i : Fin 6) : δ0 (ax012 i) = if i = 0 then β u0 + 1
      else if i = 1 ∨ i = 2 ∨ i = 3 then β (ax012 i) + β u5 else β (ax012 i) := by
    dsimp only [δ0, cPreSign, CliffProg.eval, u0, u1, u2, u3, u5]
    fin_cases i
    all_goals simp [hax_inj.eq_iff]
  have hδ2_lt (w : Wire M) (hw : w.val < cur) : δ2 w = Function.update δ0 u0 (β u0) w := by
    dsimp only [δ2, δ1, CliffProg.eval]
    rcases eq_or_ne w u0 with rfl | hwu0
    · rw [Function.update_self, Function.update_self, Function.update_of_ne (w3_ne_mk_of_lt hw)]
      dsimp only [u0]
      rw [hδ0_ax 0, ite_pos_eq rfl, w3_z2_cancel]
    · rw [Function.update_of_ne hwu0, Function.update_of_ne (w3_ne_mk_of_lt hw : w ≠ c1_mag),
        Function.update_of_ne hwu0]
  have hδ5_lt (w : Wire M) (hw : w.val < cur) : δ5 w = Function.update δ0 u0 (β u0) w :=
    (halfAdd0Setup_lt (cur + 5) (by omega) u3 c3_mag w δ4 (by omega)).trans
      ((halfAdd0Setup_lt (cur + 3) (by omega) u2 c2_mag w δ3 (by omega)).trans
        ((halfAdd0Setup_lt (cur + 1) (by omega) u1 c1_mag w δ2 (by omega)).trans (hδ2_lt w hw)))
  have hδ5_ax (i : Fin 6) : δ5 (ax012 i) =
      if i = 1 ∨ i = 2 ∨ i = 3 then β (ax012 i) + β u5 else β (ax012 i) := by
    rw [hδ5_lt (ax012 i) (hax_lt i)]
    dsimp only [u0, u5]
    fin_cases i
    all_goals simp [hax_inj.eq_iff, hδ0_ax, u5]
  have hbel_cur (w : Wire M) (hw : w.val < cur) : setup β w = β w := by
    change cPostMag.eval δ5 w = β w
    dsimp only [cPostMag, CliffProg.eval]
    rw [Function.update_of_ne (w3_ne_mk_of_lt (by omega : w.val < cur + 7)),
      Function.update_of_ne (w3_ne_mk_of_lt (by omega : w.val < cur + 7)),
      Function.update_of_ne (w3_ne_mk_of_lt (by omega : w.val < cur + 7))]
    by_cases hex : ∃ i : Fin 6, w = ax012 i
    · obtain ⟨i, rfl⟩ := hex
      dsimp only [u1, u2, u3, u5]
      fin_cases i
      all_goals simp [hax_inj.eq_iff, hδ5_ax, u5]
    · simp only [u0, u1, u2, u3, Function.update_apply,
        show ∀ i : Fin 6, (w = ax012 i) = False from fun i ↦ eq_false fun h ↦ hex ⟨i, h⟩,
        ↓reduceIte, hδ5_lt w hw, δ0, cPreSign, CliffProg.eval]
  let vc1 := (β u0 + 1) * β u5
  let vc2 := (β u1 + β u5) * vc1
  let vc3 := (β u2 + β u5) * vc2
  have hc1_v : δ2 c1_mag = vc1 := by
    dsimp only [δ2, δ1, CliffProg.eval, vc1, u0, u5]
    rw [Function.update_of_ne (w3_mk_ne_of_gt (hax_lt 0)), Function.update_self,
      hδ0_ax 0, hδ0_ax 5]
    simp [u0]
  have hδ2_ax (i : Fin 6) (hi : i = 1 ∨ i = 2 ∨ i = 3) : δ2 (ax012 i) = β (ax012 i) + β u5 := by
    rw [hδ2_lt (ax012 i) (hax_lt i)]
    rcases hi with rfl | rfl | rfl
    all_goals simp [u0, u5, hax_inj.eq_iff, hδ0_ax]
  have hc2_v : δ3 c2_mag = vc2 := (halfAdd0Setup_cout (cur + 1) (by omega) u1 c1_mag δ2).trans
    (by rw [hδ2_ax 1 (Or.inl rfl), hc1_v])
  have hδ3_u2 : δ3 u2 = β u2 + β u5 :=
    (halfAdd0Setup_lt (cur + 1) (by omega) u1 c1_mag u2 δ2 (lt_trans (hax_lt 2) (by omega))).trans
      (hδ2_ax 2 (Or.inr (Or.inl rfl)))
  have hδ4_u3 : δ4 u3 = β u3 + β u5 :=
    (halfAdd0Setup_lt (cur + 3) (by omega) u2 c2_mag u3 δ3 (lt_trans (hax_lt 3) (by omega))).trans
      ((halfAdd0Setup_lt (cur + 1) (by omega) u1 c1_mag u3 δ2
        (lt_trans (hax_lt 3) (by omega))).trans (hδ2_ax 3 (Or.inr (Or.inr rfl))))
  have hc3_v : δ4 c3_mag = vc3 :=
    (halfAdd0Setup_cout (cur + 3) (by omega) u2 c2_mag δ3).trans (by rw [hδ3_u2, hc2_v])
  have hc4_v : δ5 c4_mag = (β u3 + β u5) * vc3 :=
    (halfAdd0Setup_cout (cur + 5) (by omega) u3 c3_mag δ4).trans (by rw [hδ4_u3, hc3_v])
  have hcPost_mid (w : Wire M) (hlo : cur ≤ w.val) (hhi : w.val < cur + 7) : setup β w = δ5 w := by
    change cPostMag.eval δ5 w = δ5 w
    dsimp only [cPostMag, CliffProg.eval]
    have hm : w ≠ m4W := w3_ne_mk_of_lt hhi
    rw [Function.update_of_ne hm, Function.update_of_ne hm, Function.update_of_ne hm,
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le (hax_lt 3) hlo) : w ≠ u3),
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le (hax_lt 2) hlo) : w ≠ u2),
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le (hax_lt 1) hlo) : w ≠ u1)]
  have hm1_v : setup β m1W = (β u1 + β u5) + vc1 :=
    (hcPost_mid m1W (show cur ≤ cur + 1 by omega) (show cur + 1 < cur + 7 by omega)).trans
      ((halfAdd0Setup_lt (cur + 5) (by omega) u3 c3_mag m1W δ4
        (show cur + 1 < cur + 5 by omega)).trans
        ((halfAdd0Setup_lt (cur + 3) (by omega) u2 c2_mag m1W δ3
          (show cur + 1 < cur + 3 by omega)).trans
          ((halfAdd0Setup_sum (cur + 1) (by omega) u1 c1_mag δ2).trans
            (by rw [hδ2_ax 1 (Or.inl rfl), hc1_v]))))
  have hm2_v : setup β m2W = (β u2 + β u5) + vc2 :=
    (hcPost_mid m2W (show cur ≤ cur + 3 by omega) (show cur + 3 < cur + 7 by omega)).trans
      ((halfAdd0Setup_lt (cur + 5) (by omega) u3 c3_mag m2W δ4
        (show cur + 3 < cur + 5 by omega)).trans
        ((halfAdd0Setup_sum (cur + 3) (by omega) u2 c2_mag δ3).trans (by rw [hδ3_u2, hc2_v])))
  have hm3_v : setup β m3W = (β u3 + β u5) + vc3 :=
    (hcPost_mid m3W (show cur ≤ cur + 5 by omega) (show cur + 5 < cur + 7 by omega)).trans
      ((halfAdd0Setup_sum (cur + 5) (by omega) u3 c3_mag δ4).trans (by rw [hδ4_u3, hc3_v]))
  have hm4_v : setup β m4W = β u4 + β u5 + (β u3 + β u5) * vc3 := by
    change cPostMag.eval δ5 m4W = _
    simp [cPostMag, CliffProg.eval, u1, u2, u3, u4, u5, c4_mag, m4W,
      w3_fn_ne_add hax_lt, w3_add_ne_fn hax_lt, hax_inj.eq_iff,
      w3_cleanRem_mk hδ5_clean7 (by omega : M - (M - (cur + 7)) ≤ cur + 7),
      hδ5_ax 4, hδ5_ax 5, hc4_v]
  refine ⟨fun w hw ↦ (cPostMag.eval_outside hcPost δ5 w (by omega)).trans
    (hδ5_clean7 w (by omega)), hbel_cur, ?_⟩
  have : (β u0).val < 2 ∧ (β u1).val < 2 ∧ (β u2).val < 2 ∧ (β u3).val < 2 ∧
      (β u4).val < 2 ∧ (β u5).val < 2 :=
    ⟨(β u0).val_lt, (β u1).val_lt, (β u2).val_lt, (β u3).val_lt, (β u4).val_lt, (β u5).val_lt⟩
  rw [show (⟨bitsVal (fun b : Fin 6 ↦ β (ax012 b)), bitsVal_lt_two_pow _⟩ : Fin 64) =
      ⟨(β u0).val + (β u1).val * 2 + (β u2).val * 4 + (β u3).val * 8 + (β u4).val * 16 +
        (β u5).val * 32, by omega⟩ from w3_mk_eq (bitsVal_fin6 _), bitsVal_fin5]
  dsimp only [mag5Wires]
  change (MomSlots01Slot0ElectronKinetic.slot0AxisInt _).natAbs =
    (setup β u0).val + (setup β m1W).val * 2 + (setup β m2W).val * 4 +
      (setup β m3W).val * 8 + (setup β m4W).val * 16
  rw [hbel_cur u0 (hax_lt 0), hm1_v, hm2_v, hm3_v, hm4_v]
  exact mag5_natAbs_eq (β u0) (β u1) (β u2) (β u3) (β u4) (β u5)
def subMask5 (sub mask : Fin 32) : Bool := (sub.val &&& mask.val) == sub.val
def isPow2_5 (m : ℕ) : Bool :=
  m == 1 || m == 2 || m == 4 || m == 8 || m == 16
def anfOffset : ℕ → ℕ
  | 0 => 0
  | m + 1 => anfOffset m + if isPow2_5 (m + 1) then 0 else 1
def lsbIdx5 (m : ℕ) : Fin 5 := if m.testBit 0 then 0 else if m.testBit 1 then 1 else if
    m.testBit 2 then 2 else if m.testBit 3 then 3 else 4
def restMask5 (m : Fin 32) : Fin 32 :=
  ⟨(m.val ^^^ (1 <<< (lsbIdx5 m.val).val)) % 32, Nat.mod_lt _ (by decide)⟩
def anfBasisWire {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (m : Fin 32) : Wire M :=
  if m.val = 0 then mag5 0
  else if m.val = 1 then mag5 0
  else if m.val = 2 then mag5 1
  else if m.val = 4 then mag5 2
  else if m.val = 8 then mag5 3
  else if m.val = 16 then mag5 4
  else ⟨cur + min 25 (anfOffset (m.val - 1)),
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.min_le_left _ _) _) (by omega)⟩
theorem anfOffset_31 : anfOffset 31 = 26 := by decide
theorem subMask5_zero (u : Fin 32) : subMask5 0 u = true := by decide +revert
theorem anf_step_props (k : Fin 32) :
    (1 ≤ k.val → isPow2_5 k.val = false →
      anfOffset (k.val - 1) ≤ 25 ∧ anfOffset k.val = anfOffset (k.val - 1) + 1 ∧
      1 ≤ (restMask5 k).val ∧ (restMask5 k).val < k.val ∧
      (isPow2_5 (restMask5 k).val = false →
        anfOffset ((restMask5 k).val - 1) < anfOffset (k.val - 1)) ∧
      ((restMask5 k).val = 1 → lsbIdx5 k.val ≠ 0) ∧
      ((restMask5 k).val = 2 → lsbIdx5 k.val ≠ 1) ∧
      ((restMask5 k).val = 4 → lsbIdx5 k.val ≠ 2) ∧
      ((restMask5 k).val = 8 → lsbIdx5 k.val ≠ 3) ∧
      ((restMask5 k).val = 16 → lsbIdx5 k.val ≠ 4)) ∧
    (1 ≤ k.val → isPow2_5 k.val = true →
      anfOffset k.val = anfOffset (k.val - 1) ∧
      (k.val = 1 ∨ k.val = 2 ∨ k.val = 4 ∨ k.val = 8 ∨ k.val = 16)) := by
  have ha : ∀ m : Fin 32, 1 ≤ m.val → isPow2_5 m.val = false →
      anfOffset (m.val - 1) ≤ 25 ∧ anfOffset m.val = anfOffset (m.val - 1) + 1 ∧
      1 ≤ (restMask5 m).val ∧ (restMask5 m).val < m.val ∧
      (isPow2_5 (restMask5 m).val = false →
        anfOffset ((restMask5 m).val - 1) < anfOffset (m.val - 1)) := by decide
  have hb : ∀ m : Fin 32, 1 ≤ m.val → isPow2_5 m.val = false →
      ((restMask5 m).val = 1 → lsbIdx5 m.val ≠ 0) ∧
      ((restMask5 m).val = 2 → lsbIdx5 m.val ≠ 1) ∧
      ((restMask5 m).val = 4 → lsbIdx5 m.val ≠ 2) ∧
      ((restMask5 m).val = 8 → lsbIdx5 m.val ≠ 3) ∧
      ((restMask5 m).val = 16 → lsbIdx5 m.val ≠ 4) := by decide
  exact ⟨fun h1 h2 ↦ let ⟨a1, a2, a3, a4, a5⟩ := ha k h1 h2
    ⟨a1, a2, a3, a4, a5, hb k h1 h2⟩, by decide +revert⟩
theorem anfBasisWire_lt_of_le {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M) (mag5 : Fin 5 → Wire M)
    (hmag_lt : ∀ i, (mag5 i).val < cur) (m : Fin 32) {lim : ℕ} (_hlim : lim ≤ 31)
    (hm : m.val ≤ lim) : (anfBasisWire cur hcur mag5 m).val < cur + anfOffset lim := by
  have hmono : ∀ d : ℕ, anfOffset m.val ≤ anfOffset (m.val + d) := fun d ↦ by
    induction d with
    | zero => exact le_rfl
    | succ d ih =>
        rw [show m.val + (d + 1) = (m.val + d) + 1 by omega]
        dsimp [anfOffset]
        omega
  dsimp [anfBasisWire]
  split_ifs with h0 h1 h2 h4 h8 h16
  all_goals try exact lt_of_lt_of_le (hmag_lt _) (Nat.le_add_right _ _)
  have hnp : isPow2_5 m.val = false := by simp [isPow2_5, h1, h2, h4, h8, h16]
  obtain ⟨h25, hsucc, _⟩ := (anf_step_props m).1 (by omega) hnp
  change cur + min 25 (anfOffset (m.val - 1)) < cur + anfOffset lim
  have hle_off : anfOffset m.val ≤ anfOffset lim := by
    simpa [Nat.add_sub_of_le hm] using hmono (lim - m.val)
  rw [Nat.min_eq_right h25]
  omega
private theorem w3_anfWire_np {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (k : Fin 32) (hk1 : 1 ≤ k.val) (hnp : isPow2_5 k.val = false) :
    anfBasisWire cur hcur mag5 k = ⟨cur + anfOffset (k.val - 1), by
      have := ((anf_step_props k).1 hk1 hnp).1
      omega⟩ := by
  obtain ⟨h25, _⟩ := (anf_step_props k).1 hk1 hnp
  have hnp' : k.val ≠ 1 ∧ k.val ≠ 2 ∧ k.val ≠ 4 ∧ k.val ≠ 8 ∧ k.val ≠ 16 := by
    simpa [isPow2_5, Bool.or_eq_false_iff, beq_eq_false_iff_ne, and_assoc] using hnp
  dsimp [anfBasisWire]
  rw [ite_neg_eq (by omega), ite_neg_eq hnp'.1, ite_neg_eq hnp'.2.1, ite_neg_eq hnp'.2.2.1,
    ite_neg_eq hnp'.2.2.2.1, ite_neg_eq hnp'.2.2.2.2]
  exact w3_mk_eq (by rw [Nat.min_eq_right h25])
theorem anfStep_ctrl_bounds_and_ne {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) (k : Fin 32) (hk1 : 1 ≤ k.val)
    (hnp : isPow2_5 k.val = false) :
    let wRest := anfBasisWire cur hcur mag5 (restMask5 k)
    let wLsb := mag5 (lsbIdx5 k.val)
    let pos := cur + anfOffset (k.val - 1)
    wRest ≠ wLsb ∧ wRest.val < pos ∧ wLsb.val < pos := by
  obtain ⟨h25, _, hr1, _, hroff, ne1, ne2, ne4, ne8, ne16⟩ := (anf_step_props k).1 hk1 hnp
  have hlsb : (mag5 (lsbIdx5 k.val)).val < cur + anfOffset (k.val - 1) :=
    lt_of_lt_of_le (hmag_lt _) (Nat.le_add_right _ _)
  cases hrp : isPow2_5 (restMask5 k).val with
  | false =>
      have hw := w3_anfWire_np cur hcur mag5 (restMask5 k) hr1 hrp
      have hoff := hroff hrp
      refine ⟨wire_ne_of_gt (lt_of_lt_of_le (hmag_lt _) ?_), ?_, hlsb⟩
      all_goals
        rw [hw]
        dsimp
        omega
  | true =>
      have hp (i : Fin 5) (hw : anfBasisWire cur hcur mag5 (restMask5 k) = mag5 i)
          (hne : lsbIdx5 k.val ≠ i) :
          anfBasisWire cur hcur mag5 (restMask5 k) ≠ mag5 (lsbIdx5 k.val) ∧
            (anfBasisWire cur hcur mag5 (restMask5 k)).val < cur + anfOffset (k.val - 1) ∧
            (mag5 (lsbIdx5 k.val)).val < cur + anfOffset (k.val - 1) := by
        rw [hw]
        exact ⟨hmag_inj.ne hne.symm, lt_of_lt_of_le (hmag_lt i) (Nat.le_add_right _ _), hlsb⟩
      rcases ((anf_step_props (restMask5 k)).2 hr1 hrp).2 with h | h | h | h | h
      · exact hp 0 (by simp [anfBasisWire, h]) (ne1 h)
      · exact hp 1 (by simp [anfBasisWire, h]) (ne2 h)
      · exact hp 2 (by simp [anfBasisWire, h]) (ne4 h)
      · exact hp 3 (by simp [anfBasisWire, h]) (ne8 h)
      · exact hp 4 (by simp [anfBasisWire, h]) (ne16 h)
def withAnf5Loop {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M) (mag5 : Fin 5 → Wire M)
    (hmag_lt : ∀ i, (mag5 i).val < cur) (hmag_inj : Function.Injective mag5)
    (body : TempPhaseProg M) : (rem : ℕ) → rem ≤ 31 → TempPhaseProg M
  | 0, _ => body
  | rem + 1, hrem =>
      let k : Fin 32 := ⟨32 - (rem + 1), by omega⟩
      have hk1 : 1 ≤ k.val := show 1 ≤ 32 - (rem + 1) by omega
      let next := withAnf5Loop cur hcur mag5 hmag_lt hmag_inj body rem (Nat.le_of_succ_le hrem)
      if hnp : isPow2_5 k.val = false then
        have h25 := ((anf_step_props k).1 hk1 hnp).1
        have hb := anfStep_ctrl_bounds_and_ne cur hcur mag5 hmag_lt hmag_inj k hk1 hnp
        withTempBit (anfBasisWire cur hcur mag5 (restMask5 k)) (mag5 (lsbIdx5 k.val))
          ⟨cur + anfOffset (k.val - 1), by omega⟩ hb.1
          (wire_ne_of_lt hb.2.1) (wire_ne_of_lt hb.2.2) next
      else next
theorem withAnf5Loop_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) (body : TempPhaseProg M) :
    ∀ (rem : ℕ) (hrem : rem ≤ 31),
      (withAnf5Loop cur hcur mag5 hmag_lt hmag_inj body rem hrem).countTempAnd +
        anfOffset (31 - rem) = 26 + body.countTempAnd
  | 0, _ => by
      simp [withAnf5Loop, anfOffset_31]
      omega
  | rem + 1, hrem => by
      let k : Fin 32 := ⟨32 - (rem + 1), by omega⟩
      have hk1 : 1 ≤ k.val := show 1 ≤ 32 - (rem + 1) by omega
      have ih := withAnf5Loop_countTempAnd cur hcur mag5 hmag_lt hmag_inj body rem
        (Nat.le_of_succ_le hrem)
      dsimp only [withAnf5Loop]
      by_cases hnp : isPow2_5 k.val = false
      · have hsucc := ((anf_step_props k).1 hk1 hnp).2.1
        rw [show k.val = 31 - rem from show 32 - (rem + 1) = 31 - rem by omega,
          show (31 - rem) - 1 = 31 - (rem + 1) by omega] at hsucc
        rw [dite_pos_eq hnp, withTempBit_countTempAnd]
        omega
      · have heq_off := ((anf_step_props k).2 hk1 ((Bool.not_eq_false _).mp hnp)).1
        rw [show k.val = 31 - rem from show 32 - (rem + 1) = 31 - rem by omega,
          show (31 - rem) - 1 = 31 - (rem + 1) by omega] at heq_off
        rw [dite_neg_eq hnp]
        omega
theorem mag5_apply_eq_testBit {M : ℕ} (mag5 : Fin 5 → Wire M) (β : BitAssignment M)
    (i : Fin 5) : β (mag5 i) =
    if (bitsVal (fun r : Fin 5 ↦ β (mag5 r))).testBit i.val then 1 else 0 := by
  have h5 : ∀ (b0 b1 b2 b3 b4 : ZMod 2) (i : Fin 5),
      (if (b0.val + b1.val * 2 + b2.val * 4 + b3.val * 8 + b4.val * 16).testBit i.val then
        (1 : ZMod 2) else 0) = ![b0, b1, b2, b3, b4] i := by decide
  rw [bitsVal_fin5 (fun r : Fin 5 ↦ β (mag5 r)),
    h5 (β (mag5 0)) (β (mag5 1)) (β (mag5 2)) (β (mag5 3)) (β (mag5 4)) i]
  fin_cases i
  all_goals rfl
private theorem w3_sh5_lt (j : Fin 5) : 1 <<< j.val < 32 := by decide +revert
theorem ScopedBlock.withAnf5Loop_block {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 26)) sBody leaf body) :
    ∀ (rem : ℕ) (hrem : rem ≤ 31),
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - (cur + anfOffset (31 - rem))) (fun β ↦ sBody (setup β)) leaf
          (withAnf5Loop cur hcur mag5 hmag_lt hmag_inj body rem hrem) ∧
        ∀ β : BitAssignment M, cleanRem M (M - (cur + anfOffset (31 - rem))) β →
          (∀ m : Fin 32, 1 ≤ m.val → m.val ≤ 31 - rem → β (anfBasisWire cur hcur mag5 m) =
            if subMask5 m ⟨bitsVal (fun i : Fin 5 ↦ β (mag5 i)), bitsVal_lt_two_pow _⟩
            then 1 else 0) →
          cleanRem M (M - (cur + 26)) (setup β) ∧
          (∀ w : Wire M, w.val < cur + anfOffset (31 - rem) → setup β w = β w) ∧
          (∀ m : Fin 32, 1 ≤ m.val → setup β (anfBasisWire cur hcur mag5 m) =
            if subMask5 m ⟨bitsVal (fun i : Fin 5 ↦ β (mag5 i)), bitsVal_lt_two_pow _⟩
            then 1 else 0)
  | 0, _ => ⟨id, by simpa [withAnf5Loop, anfOffset_31] using hBody, fun _ hβ hpre ↦
      ⟨by simpa [anfOffset_31] using hβ, fun _ _ ↦ rfl, fun m hm1 ↦ hpre m hm1 (by omega)⟩⟩
  | rem + 1, hrem => by
      let k : Fin 32 := ⟨32 - (rem + 1), by omega⟩
      have hk1 : 1 ≤ k.val := show 1 ≤ 32 - (rem + 1) by omega
      have hkm1 : k.val - 1 = 31 - (rem + 1) := show 32 - (rem + 1) - 1 = _ by omega
      have hk_eq : k.val = 31 - rem := show 32 - (rem + 1) = _ by omega
      obtain ⟨stNext, hNext, hNextSpec⟩ := ScopedBlock.withAnf5Loop_block cur hcur mag5
        hmag_lt hmag_inj hBody rem (Nat.le_of_succ_le hrem)
      dsimp only [withAnf5Loop]
      by_cases hnp : isPow2_5 k.val = false
      · rw [dite_pos_eq hnp]
        obtain ⟨h25, hsucc, hr1, hrlt, _⟩ := (anf_step_props k).1 hk1 hnp
        have hb := anfStep_ctrl_bounds_and_ne cur hcur mag5 hmag_lt hmag_inj k hk1 hnp
        let pos : ℕ := cur + anfOffset (k.val - 1)
        have hpos_eq : pos = cur + anfOffset (31 - (rem + 1)) := by rw [← hkm1]
        have hpos1_eq : pos + 1 = cur + anfOffset (31 - rem) := by
          dsimp [pos]
          rw [← hk_eq, hsucc]
          omega
        let wRest := anfBasisWire cur hcur mag5 (restMask5 k)
        let wLsb := mag5 (lsbIdx5 k.val)
        let anc : Wire M := ⟨pos, by omega⟩
        refine ⟨fun β ↦ stNext (Function.update β anc (β wRest * β wLsb)),
          (ScopedBlock.withTempBit_block (M := M) pos (by omega) wRest wLsb hb.1 hb.2.1 hb.2.2
            (hNext.cast_rem (by rw [hpos1_eq]))).cast_rem (by rw [hpos_eq]), fun β hβ hpre ↦ ?_⟩
        let β₁ := Function.update β anc (β wRest * β wLsb)
        have hcl₁ : cleanRem M (M - (cur + anfOffset (31 - rem))) β₁ := by
          rw [← hpos1_eq]
          refine w3_cleanRem_upd_mk (by omega) (cleanRem_anti ?_ hβ)
          rw [← hpos_eq]
          omega
        have hu_eq : (⟨bitsVal (fun i : Fin 5 ↦ β₁ (mag5 i)), bitsVal_lt_two_pow _⟩ : Fin 32) =
            ⟨bitsVal (fun i : Fin 5 ↦ β (mag5 i)), bitsVal_lt_two_pow _⟩ :=
          w3_mk_eq (congrArg bitsVal (funext fun i ↦ Function.update_of_ne
            (wire_ne_of_lt (lt_of_lt_of_le (hmag_lt i) (Nat.le_add_right _ _))) _ _))
        have hmul_sub : ∀ (k' u : Fin 32), 1 ≤ k'.val → isPow2_5 k'.val = false →
            (if subMask5 (restMask5 k') u then (1 : ZMod 2) else 0) *
              (if u.val.testBit (lsbIdx5 k'.val).val then 1 else 0) =
              if subMask5 k' u then 1 else 0 := by decide
        obtain ⟨hclF, hbelF, hallF⟩ := hNextSpec β₁ hcl₁ fun m hm1 hm_le ↦ by
          rw [hu_eq]
          by_cases hmlt : m.val < k.val
          · rw [show β₁ _ = β _ from Function.update_of_ne (wire_ne_of_lt
              (anfBasisWire_lt_of_le cur hcur mag5 hmag_lt m (by omega) (by omega))) _ _]
            exact hpre m hm1 (by omega)
          · rw [show m = k from Fin.ext (by omega), w3_anfWire_np cur hcur mag5 k hk1 hnp]
            change Function.update β anc (β wRest * β wLsb) anc = _
            rw [Function.update_self, hpre (restMask5 k) hr1 (by omega),
              mag5_apply_eq_testBit mag5 β (lsbIdx5 k.val)]
            exact hmul_sub k _ hk1 hnp
        simp_rw [hu_eq] at hallF
        refine ⟨hclF, fun w hw ↦ ?_, hallF⟩
        rw [← hpos_eq] at hw
        exact (hbelF w (by
          rw [← hpos1_eq]
          omega)).trans (Function.update_of_ne (wire_ne_of_lt hw) _ _)
      · rw [dite_neg_eq hnp]
        have hp := (Bool.not_eq_false _).mp hnp
        have hoff_eq : anfOffset (31 - rem) = anfOffset (31 - (rem + 1)) := by
          rw [← hk_eq, ((anf_step_props k).2 hk1 hp).1, hkm1]
        have hex : ∀ m : Fin 32, 1 ≤ m.val → isPow2_5 m.val = true →
            ∃ i : Fin 5, m = ⟨1 <<< i.val, w3_sh5_lt i⟩ := by decide
        have hpow_sub : ∀ (i : Fin 5) (u : Fin 32),
            (if u.val.testBit i.val then (1 : ZMod 2) else 0) =
              if subMask5 ⟨1 <<< i.val, w3_sh5_lt i⟩ u then 1 else 0 := by decide
        refine ⟨stNext, hNext.cast_rem (by rw [hoff_eq]), fun β hβ hpre ↦ ?_⟩
        obtain ⟨hclF, hbelF, hallF⟩ := hNextSpec β (by rwa [hoff_eq]) fun m hm1 hm_le ↦ by
          by_cases hmlt : m.val < k.val
          · exact hpre m hm1 (by omega)
          · obtain ⟨i, hi⟩ := hex k hk1 hp
            rw [show m = k from Fin.ext (by omega), hi,
              show anfBasisWire cur hcur mag5 ⟨1 <<< i.val, w3_sh5_lt i⟩ = mag5 i by
                fin_cases i
                all_goals rfl,
              ← hpow_sub i]
            exact mag5_apply_eq_testBit mag5 β i
        exact ⟨hclF, fun w hw ↦ hbelF w (by rwa [hoff_eq]), hallF⟩
noncomputable def anfCoeff5 (tbl : Fin 32 → ℕ) (j : ℕ) (mask : Fin 32) : ZMod 2 :=
  ∑ x : Fin 32, (if subMask5 x mask then (1 : ZMod 2) else 0) *
    (if (tbl x).testBit j then (1 : ZMod 2) else 0)
theorem anf5_eval_eq (tbl : Fin 32 → ℕ) (j : ℕ) (u : Fin 32) :
    (∑ mask : Fin 32, anfCoeff5 tbl j mask * (if subMask5 mask u then (1 : ZMod 2) else 0)) =
      if (tbl u).testBit j then 1 else 0 := by
  have hmob : ∀ x u : Fin 32, (∑ y : Fin 32, (if subMask5 x y then (1 : ZMod 2) else 0) *
      (if subMask5 y u then 1 else 0)) = if x = u then 1 else 0 := by decide
  dsimp only [anfCoeff5]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (x : Fin 32) : (∑ y : Fin 32, ((if subMask5 x y then (1 : ZMod 2) else 0) *
      (if (tbl x).testBit j then 1 else 0)) * (if subMask5 y u then 1 else 0)) =
      (if (tbl x).testBit j then 1 else 0) * (if x = u then 1 else 0) := by
    rw [← hmob x u, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp_rw [hterm]
  simp [mul_ite]
def anfTermVal {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M) (mag5 : Fin 5 → Wire M)
    (γ : BitAssignment M) (m : Fin 32) : ZMod 2 :=
  if m.val = 0 then 1 else γ (anfBasisWire cur hcur mag5 m)
theorem w3_anfW_lt26 {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M) (mag5 : Fin 5 → Wire M)
    (hmag_lt : ∀ i, (mag5 i).val < cur) (m : Fin 32) :
    (anfBasisWire cur hcur mag5 m).val < cur + 26 :=
  lt_of_lt_of_eq (anfBasisWire_lt_of_le cur hcur mag5 hmag_lt m le_rfl (by omega))
    (congrArg (cur + ·) anfOffset_31)
noncomputable def anfSingleMaskCliff {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur) (outJ : Wire M)
    (hout : cur + 26 ≤ outJ.val) (c : ZMod 2) (m : Fin 32) : CliffProg M :=
  let _ := Classical.propDecidable (c = 1)
  if c = 1 then
    if m.val = 0 then .x outJ
    else .cnot (anfBasisWire cur hcur mag5 m) outJ
      (wire_ne_of_lt (lt_of_lt_of_le (w3_anfW_lt26 cur hcur mag5 hmag_lt m) hout))
  else .nil
noncomputable def anfColLoop {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur) (outJ : Wire M)
    (hout : cur + 26 ≤ outJ.val) (tbl : Fin 32 → ℕ) (j : ℕ) : (n : ℕ) → n ≤ 32 → CliffProg M
  | 0, _ => .nil
  | n + 1, hn =>
      .seq (anfColLoop cur hcur mag5 hmag_lt outJ hout tbl j n (Nat.le_of_succ_le hn))
        (anfSingleMaskCliff cur hcur mag5 hmag_lt outJ hout (anfCoeff5 tbl j ⟨n, hn⟩) ⟨n, hn⟩)
theorem anfColLoop_supportsBelow {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur) (outJ : Wire M)
    (hout : cur + 26 ≤ outJ.val) {bound : ℕ} (hb : outJ.val < bound) (tbl : Fin 32 → ℕ)
    (j : ℕ) : ∀ (n : ℕ) (hn : n ≤ 32),
      (anfColLoop cur hcur mag5 hmag_lt outJ hout tbl j n hn).SupportsBelow bound
  | 0, _ => trivial
  | n + 1, hn => by
      refine ⟨anfColLoop_supportsBelow cur hcur mag5 hmag_lt outJ hout hb tbl j n
        (Nat.le_of_succ_le hn), ?_⟩
      dsimp only [anfSingleMaskCliff]
      split_ifs
      · exact hb
      · exact ⟨lt_trans (lt_of_lt_of_le (w3_anfW_lt26 cur hcur mag5 hmag_lt _) hout) hb, hb⟩
      · trivial
theorem anfColLoop_eval {M : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M) (mag5 : Fin 5 → Wire M)
    (hmag_lt : ∀ i, (mag5 i).val < cur) (outJ : Wire M) (hout : cur + 26 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) : ∀ (n : ℕ) (hn : n ≤ 32) (γ : BitAssignment M),
      (anfColLoop cur hcur mag5 hmag_lt outJ hout tbl j n hn).eval γ = Function.update γ outJ
        (γ outJ + ∑ i : Fin n, anfCoeff5 tbl j ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ *
          anfTermVal cur hcur mag5 γ ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)
  | 0, _, _ => by simp [anfColLoop, CliffProg.eval]
  | n + 1, hn, γ => by
      have hsm (c : ZMod 2) (m : Fin 32) (δ : BitAssignment M) :
          (anfSingleMaskCliff cur hcur mag5 hmag_lt outJ hout c m).eval δ =
            Function.update δ outJ (δ outJ + c * anfTermVal cur hcur mag5 δ m) := by
        dsimp only [anfSingleMaskCliff, anfTermVal]
        rcases zmod2_cases c with rfl | rfl
        · rw [ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1)]
          simp [CliffProg.eval]
        · rw [ite_pos_eq rfl, one_mul]
          by_cases hm0 : m.val = 0
          all_goals simp [hm0, CliffProg.eval]
      dsimp only [anfColLoop, CliffProg.eval]
      rw [anfColLoop_eval cur hcur mag5 hmag_lt outJ hout tbl j n (Nat.le_of_succ_le hn) γ,
        hsm, Function.update_self, Function.update_idem,
        show anfTermVal cur hcur mag5 _ ⟨n, hn⟩ = anfTermVal cur hcur mag5 γ ⟨n, hn⟩ by
          dsimp only [anfTermVal]
          split_ifs
          · rfl
          · exact Function.update_of_ne
              (wire_ne_of_lt (lt_of_lt_of_le (w3_anfW_lt26 cur hcur mag5 hmag_lt _) hout)) _ _,
        Fin.sum_univ_castSucc, add_assoc]
      rfl
noncomputable def anfAllColsCliff {M : ℕ} (W cur : ℕ) (hcur : cur + 26 + W ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (tbl : Fin 32 → ℕ) : (k : ℕ) → k ≤ W → CliffProg M
  | 0, _ => .nil
  | k + 1, hk =>
      .seq (anfAllColsCliff W cur hcur mag5 hmag_lt tbl k (Nat.le_of_succ_le hk))
        (anfColLoop cur (by omega) mag5 hmag_lt ⟨cur + 26 + k, by omega⟩
          (show cur + 26 ≤ cur + 26 + k by omega) tbl k 32 le_rfl)
theorem anfAllColsCliff_supportsBelow {M : ℕ} (W cur : ℕ) (hcur : cur + 26 + W ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur) (tbl : Fin 32 → ℕ) :
    ∀ (k : ℕ) (hk : k ≤ W),
      (anfAllColsCliff W cur hcur mag5 hmag_lt tbl k hk).SupportsBelow (cur + 26 + k)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨cliff_supportsBelow_mono (by omega)
        (anfAllColsCliff_supportsBelow W cur hcur mag5 hmag_lt tbl k (Nat.le_of_succ_le hk)),
       anfColLoop_supportsBelow cur (by omega) mag5 hmag_lt ⟨cur + 26 + k, by omega⟩
         (show cur + 26 ≤ cur + 26 + k by omega)
         (show cur + 26 + k < cur + 26 + (k + 1) by omega) tbl k 32 le_rfl⟩
noncomputable def withAnf5ThreshLoad {M : ℕ} (W cur : ℕ) (hcur : cur + 26 + W ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) (tbl : Fin 32 → ℕ) (body : TempPhaseProg M) :
    TempPhaseProg M := withAnf5Loop cur (by omega) mag5 hmag_lt hmag_inj (withCliffAlloc
    (anfAllColsCliff W cur hcur mag5 hmag_lt tbl W le_rfl) body) 31 le_rfl
@[simp] theorem withAnf5ThreshLoad_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + 26 + W ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) (tbl : Fin 32 → ℕ) (body : TempPhaseProg M) :
    (withAnf5ThreshLoad W cur hcur mag5 hmag_lt hmag_inj tbl body).countTempAnd =
      26 + body.countTempAnd := by
  simpa [withAnf5ThreshLoad, anfOffset, withCliffAlloc_countTempAnd] using
    withAnf5Loop_countTempAnd cur (by omega) mag5 hmag_lt hmag_inj
      (withCliffAlloc (anfAllColsCliff W cur hcur mag5 hmag_lt tbl W le_rfl) body) 31 le_rfl
theorem ScopedBlock.withAnf5ThreshLoad_block {M : ℕ} (W cur : ℕ) (hcur : cur + 26 + W ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) (tbl : Fin 32 → ℕ)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 26 + W)) sBody leaf body) :
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
        (withAnf5ThreshLoad W cur hcur mag5 hmag_lt hmag_inj tbl body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - cur) β →
        cleanRem M (M - (cur + 26 + W)) (setup β) ∧
        (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
        (∀ j : Fin W, setup β ⟨cur + 26 + j.val, by omega⟩ =
          if (tbl ⟨bitsVal (fun i : Fin 5 ↦ β (mag5 i)), bitsVal_lt_two_pow _⟩).testBit j.val
          then 1 else 0) := by
  let cAll := anfAllColsCliff W cur hcur mag5 hmag_lt tbl W le_rfl
  have hcAll_supp := anfAllColsCliff_supportsBelow W cur hcur mag5 hmag_lt tbl W le_rfl
  have hCliff := w3_withCliffAlloc_cur (cur + 26) (cur + 26 + W) hcur (by omega)
    cAll hcAll_supp hBody
  obtain ⟨stAnf, hAnf, hAnfSpec⟩ :=
    ScopedBlock.withAnf5Loop_block cur (by omega) mag5 hmag_lt hmag_inj hCliff 31 le_rfl
  refine ⟨fun β ↦ cAll.eval (stAnf β), hAnf.cast_rem (by simp [anfOffset]), fun β hβ ↦ ?_⟩
  obtain ⟨hclAnf, hbelAnf, hbasisAnf⟩ :=
    hAnfSpec β (by simpa [anfOffset] using hβ) (fun _ hm1 hm0 ↦ absurd hm0 (by omega))
  let u : Fin 32 := ⟨bitsVal (fun i : Fin 5 ↦ β (mag5 i)), bitsVal_lt_two_pow _⟩
  have hcols : ∀ (k : ℕ) (hk : k ≤ W),
      let γ' := (anfAllColsCliff W cur hcur mag5 hmag_lt tbl k hk).eval (stAnf β)
      (∀ w : Wire M, w.val < cur + 26 → γ' w = stAnf β w) ∧
      (∀ (j : ℕ) (hj : j < k),
        γ' ⟨cur + 26 + j, by omega⟩ = if (tbl u).testBit j then 1 else 0) := by
    intro k hk
    induction k with
    | zero => exact ⟨fun _ _ ↦ rfl, fun _ hj ↦ absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
        obtain ⟨hlow, hprev⟩ := ih (Nat.le_of_succ_le hk)
        let γ₁ := (anfAllColsCliff W cur hcur mag5 hmag_lt tbl k (Nat.le_of_succ_le hk)).eval
          (stAnf β)
        let outK : Wire M := ⟨cur + 26 + k, by omega⟩
        have hout0 : γ₁ outK = 0 :=
          ((anfAllColsCliff W cur hcur mag5 hmag_lt tbl k (Nat.le_of_succ_le hk)).eval_outside
            (anfAllColsCliff_supportsBelow W cur hcur mag5 hmag_lt tbl k _) _ outK
            (show cur + 26 + k ≤ cur + 26 + k from le_rfl)).trans
            (hclAnf outK (show M - (M - (cur + 26)) ≤ cur + 26 + k by omega))
        have hterm (m : Fin 32) : anfTermVal cur (by omega) mag5 γ₁ m =
            if subMask5 m u then 1 else 0 := by
          dsimp only [anfTermVal]
          by_cases hm0 : m.val = 0
          · rw [ite_pos_eq hm0, show m = 0 from Fin.ext hm0, subMask5_zero u]
            rfl
          · rw [ite_neg_eq hm0]
            exact (hlow _ (w3_anfW_lt26 cur (by omega) mag5 hmag_lt m)).trans
              (hbasisAnf m (by omega))
        dsimp only [anfAllColsCliff, CliffProg.eval]
        change (∀ w : Wire M, w.val < cur + 26 →
            (anfColLoop cur _ mag5 hmag_lt outK _ tbl k 32 le_rfl).eval γ₁ w = stAnf β w) ∧ _
        rw [anfColLoop_eval cur (by omega) mag5 hmag_lt outK _ tbl k 32 le_rfl γ₁, hout0,
          zero_add, show (∑ i : Fin 32, anfCoeff5 tbl k ⟨i.val, _⟩ * anfTermVal cur _ mag5 γ₁
            ⟨i.val, _⟩) = ∑ m : Fin 32, anfCoeff5 tbl k m *
              (if subMask5 m u then 1 else 0) from
            Finset.sum_congr rfl fun m _ ↦ by rw [hterm m], anf5_eval_eq tbl k u]
        refine ⟨fun w hw ↦ ?_, fun j hj ↦ ?_⟩
        · rw [Function.update_of_ne (w3_ne_mk_of_lt (by omega))]
          exact hlow w hw
        · rcases eq_or_ne j k with rfl | hjk
          · exact Function.update_self _ _ _
          · rw [Function.update_of_ne (w3_mk_ne (by omega))]
            exact hprev j (by omega)
  obtain ⟨hlowC, hcolsC⟩ := hcols W le_rfl
  refine ⟨fun w hw ↦ (cAll.eval_outside hcAll_supp _ w (by omega)).trans (hclAnf w (by omega)),
    fun w hw ↦ (hlowC w (by omega)).trans (hbelAnf w (by simpa [anfOffset] using hw)),
    fun j ↦ hcolsC j.val j.isLt⟩
theorem add_mod3_left (x b : ℕ) : (x + b) % 3 = (x % 3 + b) % 3 := by omega
theorem mod327_mul2_add_mod3 (x b : ℕ) : (2 * (x % 327) + b) % 3 = ((2 * x) % 3 + b) % 3 := by
  omega
theorem even_odd_bits_mul2_mod3 :
    ∀ (n : ℕ) (f : Fin (2 * n) → ZMod 2),
      (2 * (∑ i : Fin (2 * n), (f i).val * 2 ^ i.val)) % 3 =
        ((∑ m : Fin n, (f ⟨2 * m.val + 1, by omega⟩).val) +
          2 * (∑ m : Fin n, (f ⟨2 * m.val, by omega⟩).val)) % 3
  | 0, _ => rfl
  | n + 1, f => by
      have hp_ev : ∀ k : ℕ, (2 * 2 ^ (2 * k)) % 3 = 2 := fun k ↦ by
        induction k with
        | zero => rfl
        | succ k ih =>
            rw [show 2 * 2 ^ (2 * (k + 1)) = 4 * (2 * 2 ^ (2 * k)) by
              rw [Nat.mul_succ, pow_add]
              ring]
            omega
      let g : Fin ((2 * n + 1) + 1) → ZMod 2 := fun i ↦ f ⟨i.val, by omega⟩
      have hfg : (∑ i : Fin (2 * (n + 1)), (f i).val * 2 ^ i.val) =
          ∑ i : Fin ((2 * n + 1) + 1), (g i).val * 2 ^ i.val :=
        Finset.sum_bij (fun i _ ↦ ⟨i.val, by omega⟩) (fun _ _ ↦ Finset.mem_univ _)
          (fun _ _ _ _ h ↦ Fin.ext (congrArg Fin.val h))
          (fun j _ ↦ ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩) (fun _ _ ↦ rfl)
      have ih := even_odd_bits_mul2_mod3 n (fun i : Fin (2 * n) ↦ f ⟨i.val, by omega⟩)
      dsimp only at ih
      have hlo : (∑ i : Fin (2 * n),
          (g i.castSucc.castSucc).val * 2 ^ i.castSucc.castSucc.val) =
          ∑ i : Fin (2 * n), (f ⟨i.val, by omega⟩).val * 2 ^ i.val := rfl
      rw [hfg, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hlo,
        Fin.sum_univ_castSucc (n := n), Fin.sum_univ_castSucc (n := n)]
      dsimp only [g, Fin.val_castSucc, Fin.val_last]
      rw [Nat.mul_add, Nat.mul_add]
      have hpe := hp_ev n
      have hpo : (2 * 2 ^ (2 * n + 1)) % 3 = 1 := by
        rw [show 2 * 2 ^ (2 * n + 1) = 2 * (2 * 2 ^ (2 * n)) by
          rw [pow_succ]
          ring]
        omega
      have hev : (2 * ((f ⟨2 * n, by omega⟩).val * 2 ^ (2 * n))) % 3 =
          (2 * (f ⟨2 * n, by omega⟩).val) % 3 := by
        rw [show 2 * ((f ⟨2 * n, _⟩).val * 2 ^ (2 * n)) =
          (f ⟨2 * n, _⟩).val * (2 * 2 ^ (2 * n)) by ring, Nat.mul_mod, hpe]
        omega
      have hod : (2 * ((f ⟨2 * n + 1, by omega⟩).val * 2 ^ (2 * n + 1))) % 3 =
          (f ⟨2 * n + 1, by omega⟩).val % 3 := by
        rw [show 2 * ((f ⟨2 * n + 1, _⟩).val * 2 ^ (2 * n + 1)) =
          (f ⟨2 * n + 1, _⟩).val * (2 * 2 ^ (2 * n + 1)) by ring, Nat.mul_mod, hpo]
        omega
      omega
theorem zmod2_mul_eq_one_iff (a b : ZMod 2) : a * b = 1 ↔ a = 1 ∧ b = 1 := by decide +revert
theorem even_odd_prod_eq_one_iff_u36_allOnes (f : Fin 36 → ZMod 2) :
    (∏ m : Fin 18, f ⟨2 * m.val + 1, by omega⟩) * (∏ m : Fin 18, f ⟨2 * m.val, by omega⟩) = 1 ↔
      (∑ i : Fin 36, (f i).val * 2 ^ i.val) = 2 ^ 36 - 1 := by
  have hprod {K : ℕ} (g : Fin K → ZMod 2) : (∏ i, g i) = 1 ↔ ∀ i, g i = 1 := by
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Fin.prod_univ_castSucc, zmod2_mul_eq_one_iff, ih]
        exact ⟨fun ⟨hl, hh⟩ ↦ Fin.lastCases hh hl, fun h ↦ ⟨fun j ↦ h j.castSucc, h _⟩⟩
  have hbits {K : ℕ} (g : Fin K → ZMod 2) :
      (∑ i, (g i).val * 2 ^ i.val) + 1 = 2 ^ K ↔ ∀ i, g i = 1 := by
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Fin.sum_univ_castSucc, pow_succ]
        dsimp only [Fin.val_castSucc, Fin.val_last]
        have : (∑ i : Fin K, (g i.castSucc).val * 2 ^ i.val) < 2 ^ K :=
          bitsVal_lt_two_pow (fun i : Fin K ↦ g i.castSucc)
        refine ⟨fun hs ↦ ?_, fun h ↦ ?_⟩
        · rcases zmod2_cases (g (Fin.last K)) with h0 | h1
          · rw [h0, show (0 : ZMod 2).val = 0 from rfl, zero_mul] at hs
            omega
          · refine Fin.lastCases h1 fun j ↦ (ih fun i ↦ g i.castSucc).mp ?_ j
            rw [h1, show (1 : ZMod 2).val = 1 from rfl, one_mul] at hs
            omega
        · have := (ih fun x : Fin K ↦ g x.castSucc).mpr fun j ↦ h j.castSucc
          rw [h (Fin.last K), show (1 : ZMod 2).val = 1 from rfl, one_mul]
          omega
  rw [zmod2_mul_eq_one_iff, hprod, hprod, show ((∀ m : Fin 18, f ⟨2 * m.val + 1, by omega⟩ = 1) ∧
      (∀ m : Fin 18, f ⟨2 * m.val, by omega⟩ = 1)) ↔ ∀ i : Fin 36, f i = 1 from
    ⟨fun ⟨ho, he⟩ i ↦ if hp : i.val % 2 = 0 then
        (congrArg f (Fin.ext (show i.val = 2 * (i.val / 2) by omega))).trans
          (he ⟨i.val / 2, by omega⟩)
      else (congrArg f (Fin.ext (show i.val = 2 * (i.val / 2) + 1 by omega))).trans
          (ho ⟨i.val / 2, by omega⟩),
     fun h ↦ ⟨fun _ ↦ h _, fun _ ↦ h _⟩⟩, ← hbits f]
  have : 1 ≤ 2 ^ 36 := Nat.one_le_two_pow
  omega
theorem mag5Wires_lt_and_inj {M : ℕ} (cur : ℕ) (hcur : cur + 8 ≤ M) (u0 : Wire M)
    (hu0 : u0.val < cur) : (∀ i : Fin 5, (mag5Wires cur hcur u0 i).val < cur + 8) ∧
    Function.Injective (mag5Wires cur hcur u0) := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · fin_cases i
    all_goals
      dsimp [mag5Wires]
      omega
  · have hv := congrArg Fin.val hij
    fin_cases i
    all_goals
      fin_cases j
      all_goals
        dsimp [mag5Wires] at hv
        first | rfl | omega
theorem wire_offset_inj {M n : ℕ} (base : ℕ) (h : ∀ i : Fin n, base + i.val < M) :
    Function.Injective (fun i : Fin n ↦ (⟨base + i.val, h i⟩ : Wire M)) := fun _ _ hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp only at hv
  exact Fin.ext (by omega)
noncomputable def slot0TailProg {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires)) (h12 : a1 ≠ b1)
    (h34 : a2 ≠ b2) (ha1 : a1.val < coreWiresSym mPayload + 64)
    (hb1 : b1.val < coreWiresSym mPayload + 64) (ha2 : a2.val < coreWiresSym mPayload + 64)
    (hb2 : b2.val < coreWiresSym mPayload + 64) :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  have hM (k : ℕ) (hk : k < C + 208) : k < M := by
    dsimp [M, slot0LocalWorkWires]
    omega
  let payW (k : ℕ) (hk : k < 80) : Wire M := ⟨3954 + k, hM _ (by omega)⟩
  let c0 : Wire M := ⟨3948, hM _ (by omega)⟩
  let c1 : Wire M := ⟨3949, hM _ (by omega)⟩
  let c2 : Wire M := ⟨3950, hM _ (by omega)⟩
  let bParW : Wire M := payW 36 (by omega)
  let bTieW : Wire M := payW 79 (by omega)
  let cmpPay42 : Fin 42 → Wire M := fun j ↦ payW (37 + j.val) (by omega)
  let elecAx (a : ℕ) (ha : a < 3) : Fin 6 → Wire M := fun b ↦ ⟨6 * a + b.val, hM _ (by omega)⟩
  let threshTbl : Fin 32 → ℕ := fun m ↦
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff ⟨m.val, lt_trans m.isLt (by decide)⟩
  let allOnesW : Wire M := ⟨C + 64 + 4, hM _ (by omega)⟩
  let selAW : Wire M := ⟨C + 64 + 7, hM _ (by omega)⟩
  let selBW : Wire M := ⟨C + 64 + 8, hM _ (by omega)⟩
  let ax01 : Fin 6 → Wire M := fun i ↦ ⟨C + 73 + i.val, hM _ (by omega)⟩
  let ax012 : Fin 6 → Wire M := fun i ↦ ⟨C + 79 + i.val, hM _ (by omega)⟩
  let mag5 : Fin 5 → Wire M := mag5Wires (C + 85) (hM _ (by omega)) (ax012 0)
  have hmag := mag5Wires_lt_and_inj (C + 85) (hM _ (by omega)) (ax012 0)
    (show C + 79 + 0 < C + 85 by omega)
  let thresh42 : Fin 42 → Wire M := fun j ↦ ⟨C + 93 + 26 + j.val, hM _ (by omega)⟩
  let ltOut : Wire M := ⟨C + 161 + 42, hM _ (by omega)⟩
  let phaseBody : Wire M := ⟨C + 204, hM _ (by omega)⟩
  withSlot0TailDecode (C + 64) (hM _ (by omega)) a1 b1 a2 b2 bParW h12 h34 ha1 hb1 ha2 hb2
    (show 3954 + 36 < C + 64 by omega)
    (withMuxReg 6 (C + 73) (hM _ (by omega)) selAW (elecAx 0 (by decide))
      (elecAx 1 (by decide)) (fun i ↦ w3_mk_ne (by omega)) (fun i ↦ w3_mk_ne (by omega))
      (fun i ↦ w3_mk_ne (by omega)) (show C + 64 + 7 < C + 73 by omega)
      (fun i ↦ show 6 * 0 + i.val < C + 73 by omega)
      (fun i ↦ show 6 * 1 + i.val < C + 73 by omega)
      (withMuxReg 6 (C + 79) (hM _ (by omega)) selBW ax01 (elecAx 2 (by decide))
        (fun i ↦ w3_mk_ne (by omega)) (fun i ↦ w3_mk_ne (by omega))
        (fun i ↦ w3_mk_ne (by omega)) (show C + 64 + 8 < C + 79 by omega)
        (fun i ↦ show C + 73 + i.val < C + 79 by omega)
        (fun i ↦ show 6 * 2 + i.val < C + 79 by omega)
        (withMag5 (C + 85) (hM _ (by omega)) ax012
          (fun i ↦ show C + 79 + i.val < C + 85 by omega)
          (wire_offset_inj (C + 79) fun i ↦ hM _ (by omega))
          (withAnf5ThreshLoad 42 (C + 93) (hM _ (by omega)) mag5 hmag.1 hmag.2 threshTbl
            (withLtCompLoop 42 (C + 161) (hM _ (by omega)) cmpPay42 thresh42
              (fun j ↦ w3_mk_ne (by omega))
              (fun j ↦ show 3954 + (37 + j.val) < C + 161 by omega)
              (fun j ↦ show C + 93 + 26 + j.val < C + 161 by omega)
              (withMuxBit (C + 204) (hM _ (by omega)) allOnesW ltOut bTieW
                (w3_mk_ne (by omega)) (w3_mk_ne (by omega)) (w3_mk_ne (by omega))
                (show C + 64 + 4 < C + 204 by omega) (show C + 161 + 42 < C + 204 by omega)
                (show 3954 + 79 < C + 204 by omega)
                (withCliffAlloc (.seq (.x c0) (.x c1))
                  (withCtrl3Z (C + 205) (hM _ (by omega)) phaseBody c0 c1 c2
                    (w3_mk_ne (by omega)) (show C + 204 < C + 205 by omega)
                    (show 3948 < C + 205 by omega) (show 3949 < C + 205 by omega)
                    (show 3950 < C + 205 by omega)))))))))
theorem slot0Core_add64_le {mPayload : ℕ} :
    coreWiresSym mPayload + 4 * 16 ≤ coreWiresSym mPayload + slot0LocalWorkWires :=
  Nat.add_le_add_left (by decide) _
theorem slot0Pay_lt_core {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (k : ℕ) (hk : k < 80) :
    3954 + k < coreWiresSym mPayload :=
  lt_of_lt_of_le (Nat.add_lt_add_left hk 3954) (coreWiresSym_ge_4034 hmPay)
def slot0PayW {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (k : ℕ) (hk : k < 80) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires) :=
  ⟨3954 + k, lt_of_lt_of_le (slot0Pay_lt_core hmPay k hk) (Nat.le_add_right _ _)⟩
theorem slot0Odd18_lt80 (m : Fin 18) : 2 * m.val + 1 < 80 := by omega
theorem slot0Even18_lt80 (m : Fin 18) : 2 * m.val < 80 := by omega
theorem slot0Odd18_lt36 (m : Fin 18) : 2 * m.val + 1 < 36 := by omega
theorem slot0Even18_lt36 (m : Fin 18) : 2 * m.val < 36 := by omega
def slot0InitW1 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires) :=
  slot0PayW hmPay (2 * m.val + 1) (slot0Odd18_lt80 m)
def slot0InitW2 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires) :=
  slot0PayW hmPay (2 * m.val) (slot0Even18_lt80 m)
theorem slot0InitW1_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    (slot0InitW1 hmPay m).val < coreWiresSym mPayload :=
  slot0Pay_lt_core hmPay _ (slot0Odd18_lt80 m)
theorem slot0InitW2_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    (slot0InitW2 hmPay m).val < coreWiresSym mPayload :=
  slot0Pay_lt_core hmPay _ (slot0Even18_lt80 m)
theorem slot0InitW1_inj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Injective (slot0InitW1 hmPay) := fun _ _ hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW1, slot0PayW] at hv
  exact Fin.ext (by omega)
theorem slot0InitW2_inj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Injective (slot0InitW2 hmPay) := fun _ _ hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW2, slot0PayW] at hv
  exact Fin.ext (by omega)
theorem slot0Coin_lt_core (mPayload c : ℕ) (hc : c < 3) :
    3948 + c < coreWiresSym mPayload := by
  dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
theorem slot0SysCoin_lt_core (mPayload : ℕ) :
    SpecsAux.SpecMirror.systemQubits < coreWiresSym mPayload ∧
    SpecsAux.SpecMirror.systemQubits + 1 < coreWiresSym mPayload ∧
    SpecsAux.SpecMirror.systemQubits + 2 < coreWiresSym mPayload := by
  dsimp [coreWiresSym, selWiresSym]
  exact ⟨by omega, by omega, by omega⟩
noncomputable def slot0LocalProg {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires) := withMod3AllOnesReduce 16
    (coreWiresSym mPayload) slot0Core_add64_le (slot0InitW1 hmPay) (slot0InitW2 hmPay)
    (slot0InitW1_lt hmPay) (slot0InitW2_lt hmPay) (slot0InitW1_inj hmPay)
    (slot0InitW2_inj hmPay) (fun a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2 ↦ slot0TailProg hmPay
    w_eff a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2)
@[simp] theorem slot0LocalProg_countTempAnd {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0LocalProg hmPay w_eff).countTempAnd = 125 := by
  unfold slot0LocalProg
  refine withMod3AllOnesReduce_countTempAnd 16 _ _ _ _ _ _ _ _ _ 93
    fun _ _ _ _ _ _ _ _ _ _ ↦ ?_
  unfold slot0TailProg
  dsimp only
  rw [withSlot0TailDecode_countTempAnd, withMuxReg_countTempAnd, withMuxReg_countTempAnd,
    withMag5_countTempAnd, withAnf5ThreshLoad_countTempAnd, withLtCompLoop_countTempAnd,
    withMuxBit_countTempAnd, withCliffAlloc_countTempAnd, withCtrl3Z_countTempAnd]
theorem slot0LocalProg_spec {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (hw_eff : LiteralKineticAndMidpoint128.elecQuadCenterOffset < w_eff) : ValidCleanRem
    (coreWiresSym mPayload + slot0LocalWorkWires) slot0LocalWorkWires
    (slot0LocalProg hmPay w_eff) ∧ (∀ α : BitAssignment (coreWiresSym mPayload),
    (slot0LocalProg hmPay w_eff).evalBits (padZeroBits α) = padZeroBits α) ∧ (∀ α :
    BitAssignment (coreWiresSym mPayload), (slot0LocalProg hmPay w_eff).evalSign (padZeroBits
    α) = slot0LocalPhaseBit hmPay w_eff α) := by
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  have hM : C + 208 ≤ M := Nat.add_le_add_left (by decide) C
  have hsc := slot0SysCoin_lt_core mPayload
  let w1 := slot0InitW1 hmPay
  let w2 := slot0InitW2 hmPay
  let payW (k : ℕ) (hk : k < 80) : Wire M := ⟨3954 + k, by omega⟩
  let c0 : Wire M := ⟨3948, by omega⟩
  let c1 : Wire M := ⟨3949, by omega⟩
  let c2 : Wire M := ⟨3950, by omega⟩
  let bParW : Wire M := payW 36 (by omega)
  let bTieW : Wire M := payW 79 (by omega)
  let cmpPay42 : Fin 42 → Wire M := fun j ↦ payW (37 + j.val) (by omega)
  let elecAx (a : ℕ) (ha : a < 3) : Fin 6 → Wire M := fun b ↦ ⟨6 * a + b.val, by omega⟩
  let threshTbl : Fin 32 → ℕ := fun m ↦
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff ⟨m.val, lt_trans m.isLt (by decide)⟩
  let allOnesW : Wire M := ⟨C + 64 + 4, by omega⟩
  let selAW : Wire M := ⟨C + 64 + 7, by omega⟩
  let selBW : Wire M := ⟨C + 64 + 8, by omega⟩
  let ax01 : Fin 6 → Wire M := fun i ↦ ⟨C + 73 + i.val, by omega⟩
  let ax012 : Fin 6 → Wire M := fun i ↦ ⟨C + 79 + i.val, by omega⟩
  let mag5 : Fin 5 → Wire M := mag5Wires (C + 85) (by omega) (ax012 0)
  have hmag :=
    mag5Wires_lt_and_inj (C + 85) (by omega) (ax012 0) (show C + 79 + 0 < C + 85 by omega)
  let thresh42 : Fin 42 → Wire M := fun j ↦ ⟨C + 93 + 26 + j.val, by omega⟩
  let ltOut : Wire M := ⟨C + 161 + 42, by omega⟩
  let phaseBody : Wire M := ⟨C + 204, by omega⟩
  let leafZ : TempPhaseProg M := .z ⟨C + 205 + 2, by omega⟩
  obtain ⟨stCtrl, hCtrl, hCtrlSign⟩ := ScopedBlock.withCtrl3Z_block (M := M) (C + 205)
    (by omega) phaseBody c0 c1 c2 (w3_mk_ne (by omega)) (show C + 204 < C + 205 by omega)
    (show 3948 < C + 205 by omega) (show 3949 < C + 205 by omega) (show 3950 < C + 205 by omega)
  let cFlip : CliffProg M := .seq (.x c0) (.x c1)
  have hFlipSupp : cFlip.SupportsBelow (C + 205) :=
    ⟨show 3948 < C + 205 by omega, show 3949 < C + 205 by omega⟩
  have hMuxTie := ScopedBlock.withMuxBit_block (M := M) (C + 204) (by omega) allOnesW ltOut
    bTieW (w3_mk_ne (by omega)) (w3_mk_ne (by omega)) (w3_mk_ne (by omega))
    (show C + 64 + 4 < C + 204 by omega) (show C + 161 + 42 < C + 204 by omega)
    (show 3954 + 79 < C + 204 by omega)
    (w3_withCliffAlloc_cur (C + 205) (C + 205) (by omega) le_rfl cFlip hFlipSupp hCtrl)
  obtain ⟨stLt, hLt, hLtSpec⟩ := ScopedBlock.withLtComp_clean_block (M := M) (W := 42)
    (cur := C + 161) (by omega) cmpPay42 thresh42 (fun _ ↦ w3_mk_ne (by omega))
    (fun j ↦ show 3954 + (37 + j.val) < C + 161 by omega)
    (fun j ↦ show C + 93 + 26 + j.val < C + 161 by omega) (hMuxTie.cast_rem (by omega))
  obtain ⟨stAnf, hAnf, hAnfSpec⟩ := ScopedBlock.withAnf5ThreshLoad_block (M := M) 42 (C + 93)
    (by omega) mag5 hmag.1 hmag.2 threshTbl (hLt.cast_rem (by omega))
  obtain ⟨stMag, hMag, hMagSpec⟩ := ScopedBlock.withMag5_block (M := M) (C + 85) (by omega)
    ax012 (fun i ↦ show C + 79 + i.val < C + 85 by omega)
    (wire_offset_inj (C + 79) fun _ ↦ by omega) (hAnf.cast_rem (by omega))
  obtain ⟨stM2, hM2, hM2Spec⟩ := ScopedBlock.withMuxReg_block (M := M) 6 (C + 79) (by omega)
    selBW ax01 (elecAx 2 (by decide)) (fun _ ↦ w3_mk_ne (by omega))
    (fun _ ↦ w3_mk_ne (by omega)) (fun _ ↦ w3_mk_ne (by omega))
    (show C + 64 + 8 < C + 79 by omega) (fun i ↦ show C + 73 + i.val < C + 79 by omega)
    (fun i ↦ show 6 * 2 + i.val < C + 79 by omega) _ _ _ (hMag.cast_rem (by omega))
  obtain ⟨stM1, hM1, hM1Spec⟩ := ScopedBlock.withMuxReg_block (M := M) 6 (C + 73) (by omega)
    selAW (elecAx 0 (by decide)) (elecAx 1 (by decide)) (fun _ ↦ w3_mk_ne (by omega))
    (fun _ ↦ w3_mk_ne (by omega)) (fun _ ↦ w3_mk_ne (by omega))
    (show C + 64 + 7 < C + 73 by omega) (fun i ↦ show 6 * 0 + i.val < C + 73 by omega)
    (fun i ↦ show 6 * 1 + i.val < C + 73 by omega) _ _ _ (hM2.cast_rem (by omega))
  choose stDec hDec hDecSpec using
    fun (a1 b1 a2 b2 : Wire M) (h12 : a1 ≠ b1) (h34 : a2 ≠ b2) (ha1 : a1.val < C + 64)
        (hb1 : b1.val < C + 64) (ha2 : a2.val < C + 64) (hb2 : b2.val < C + 64) ↦
      ScopedBlock.withSlot0TailDecode_block (M := M) (C + 64) (by omega) a1 b1 a2 b2 bParW
        h12 h34 ha1 hb1 ha2 hb2 (show 3954 + 36 < C + 64 by omega) (hM1.cast_rem (by omega))
  obtain ⟨a1, b1, a2, b2, h12, h34, ha1, hb1, ha2, hb2, stRed, hRed, hRedSpec⟩ :=
    ScopedBlock.withMod3AllOnesReduce_block (M := M) 16 C slot0Core_add64_le w1 w2
      (slot0InitW1_lt hmPay) (slot0InitW2_lt hmPay) (slot0InitW1_inj hmPay)
      (slot0InitW2_inj hmPay) (fun a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2 ↦
        slot0TailProg hmPay w_eff a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2) leafZ
      (fun a1 b1 a2 b2 ↦ if h : a1 ≠ b1 ∧ a2 ≠ b2 ∧ a1.val < C + 64 ∧ b1.val < C + 64 ∧
          a2.val < C + 64 ∧ b2.val < C + 64 then
        fun β ↦ stCtrl (cFlip.eval (muxBitSetup (C + 204) (by omega) allOnesW ltOut bTieW
          (stLt (stAnf (stMag (stM2 (stM1 (stDec a1 b1 a2 b2 h.1 h.2.1 h.2.2.1 h.2.2.2.1
            h.2.2.2.2.1 h.2.2.2.2.2 β)))))))) else id)
      fun a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2 ↦ by
        rw [dite_pos_eq ⟨h12, h34, ha1, hb1, ha2, hb2⟩]
        exact hDec a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2
  have hTop : ScopedBlock M slot0LocalWorkWires _ leafZ (slot0LocalProg hmPay w_eff) :=
    hRed.cast_rem (Nat.add_sub_cancel_left _ _)
  refine ⟨hTop.valid, fun α ↦ hTop.bits _ (cleanRem_padZeroBits α), fun α ↦ ?_⟩
  let β₀ : BitAssignment M := padZeroBits (mClean := slot0LocalWorkWires) α
  have hpad (k : ℕ) (hk : k < C) :
      β₀ ⟨k, lt_of_lt_of_le hk (Nat.le_add_right C slot0LocalWorkWires)⟩ = α ⟨k, hk⟩ :=
    Fin.addCases_left ⟨k, hk⟩
  have hpay (k : ℕ) (hk : k < 80) : β₀ (slot0PayW hmPay k hk) =
      α (corePayloadSym mPayload ⟨k, lt_of_lt_of_le hk hmPay⟩) :=
    (hpad (3954 + k) (slot0Pay_lt_core hmPay k hk)).trans (congrArg α (Fin.ext (by
      dsimp [corePayloadSym, MomSlot0LocalAndMomCombine288Alt.qreg_block_apply,
        MomSlot0LocalAndMomCombine288Alt.qreg_block_wires_apply,
        MomSlot0LocalAndMomCombine288Alt.qreg_whole_wires,
        MomSlot0LocalAndMomCombine288Alt.emb_trans_apply,
        MomSlot0LocalAndMomCombine288Alt.emb_refl_apply,
        MomSlot0LocalAndMomCombine288Alt.emb_mk_apply, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits])))
  obtain ⟨hcl0, hbel0, hmod0, hprod0⟩ :=
    hRedSpec β₀ (cleanRem_anti (by omega) (cleanRem_padZeroBits α))
  let β₁ := stRed β₀
  let dβ := stDec a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2 β₁
  obtain ⟨hcl1, hbel1, hall1, hselB1, hselA1⟩ :=
    hDecSpec a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2 β₁ hcl0
  obtain ⟨hcl2, hbel2, hv2⟩ := hM1Spec dβ (cleanRem_anti (by omega) hcl1)
  obtain ⟨hcl3, hbel3, hv3⟩ := hM2Spec _ (cleanRem_anti (by omega) hcl2)
  obtain ⟨hcl4, hbel4, hv4⟩ := hMagSpec _ (cleanRem_anti (by omega) hcl3)
  obtain ⟨hcl5, hbel5, hv5⟩ := hAnfSpec _ (cleanRem_anti (by omega) hcl4)
  obtain ⟨hcl6, hbel6, hv6⟩ := hLtSpec _ (cleanRem_anti (by omega) hcl5)
  let β₅ := stAnf (stMag (stM2 (stM1 dβ)))
  let β₆ := stLt β₅
  let β₇ := muxBitSetup (C + 204) (by omega) allOnesW ltOut bTieW β₆
  let β₈ := cFlip.eval β₇
  have hcl8 : cleanRem M (M - (C + 205)) β₈ := fun w hw ↦
    (cFlip.eval_outside hFlipSupp β₇ w (by omega)).trans
      (w3_cleanRem_upd_mk (by omega) (cleanRem_anti (by omega) hcl6) w hw)
  change (slot0LocalProg hmPay w_eff).evalSign β₀ = slot0LocalPhaseBit hmPay w_eff α
  rw [hTop.sign β₀ (cleanRem_padZeroBits α), dite_pos_eq ⟨h12, h34, ha1, hb1, ha2, hb2⟩]
  change leafZ.evalSign (stCtrl β₈) = _
  rw [← hCtrl.sign β₈ hcl8, hCtrlSign β₈ hcl8]
  have hkeep5 {w : Wire M} (hw : w.val < C + 64) : β₅ w = β₁ w :=
    (hbel5 w (by omega)).trans ((hbel4 w (by omega)).trans
      ((hbel3 w (by omega)).trans ((hbel2 w (by omega)).trans (hbel1 w hw))))
  have hkeep7 {w : Wire M} (hw : w.val < C) : β₇ w = α ⟨w.val, hw⟩ :=
    (Function.update_of_ne (w3_ne_mk_of_lt (by omega)) _ _).trans
      ((hbel6 w (by omega)).trans ((hkeep5 (by omega)).trans
        ((hbel0 w hw).trans (hpad w.val hw))))
  have hc_sys (c : ℕ) (hc3 : c < 3) : α ⟨3948 + c, slot0Coin_lt_core mPayload c hc3⟩ =
      α ⟨SpecsAux.SpecMirror.systemQubits + c, by
        dsimp [coreWiresSym, selWiresSym]
        omega⟩ :=
    congrArg α (w3_mk_eq (by
      dsimp [SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]))
  have hc0_8 : β₈ c0 = α ⟨SpecsAux.SpecMirror.systemQubits, hsc.1⟩ + 1 := by
    dsimp only [β₈, cFlip, CliffProg.eval]
    rw [Function.update_of_ne (w3_mk_ne (by decide)), Function.update_self,
      hkeep7 (slot0Coin_lt_core mPayload 0 (by decide)), hc_sys 0 (by decide)]
    rfl
  have hc1_8 : β₈ c1 = α ⟨SpecsAux.SpecMirror.systemQubits + 1, hsc.2.1⟩ + 1 := by
    dsimp only [β₈, cFlip, CliffProg.eval]
    rw [Function.update_self, Function.update_of_ne (w3_mk_ne (by decide)),
      hkeep7 (slot0Coin_lt_core mPayload 1 (by decide)), hc_sys 1 (by decide)]
  have hc2_8 : β₈ c2 = α ⟨SpecsAux.SpecMirror.systemQubits + 2, hsc.2.2⟩ := by
    dsimp only [β₈, cFlip, CliffProg.eval]
    rw [Function.update_of_ne (w3_mk_ne (by decide)),
      Function.update_of_ne (w3_mk_ne (by decide)),
      hkeep7 (slot0Coin_lt_core mPayload 2 (by decide)), hc_sys 2 (by decide)]
  rw [hc0_8, hc1_8, hc2_8]
  by_cases hcoin : α ⟨SpecsAux.SpecMirror.systemQubits, hsc.1⟩ = 0 ∧
      α ⟨SpecsAux.SpecMirror.systemQubits + 1, hsc.2.1⟩ = 0 ∧
      α ⟨SpecsAux.SpecMirror.systemQubits + 2, hsc.2.2⟩ = 1
  · have ⟨h0z, h1z, h2o⟩ := hcoin
    rw [show β₈ phaseBody * (α ⟨SpecsAux.SpecMirror.systemQubits, hsc.1⟩ + 1) *
        (α ⟨SpecsAux.SpecMirror.systemQubits + 1, hsc.2.1⟩ + 1) *
        α ⟨SpecsAux.SpecMirror.systemQubits + 2, hsc.2.2⟩ = β₈ phaseBody by
      rw [h0z, h1z, h2o]
      ring]
    unfold slot0LocalPhaseBit
    rw [ite_pos_eq hcoin]
    dsimp only
    have hpb_8 : β₈ phaseBody = if β₆ allOnesW = 1 then β₆ bTieW else β₆ ltOut := by
      dsimp only [β₈, cFlip, CliffProg.eval]
      rw [Function.update_of_ne (w3_mk_ne (by omega)),
        Function.update_of_ne (w3_mk_ne (by omega))]
      exact Function.update_self _ _ _
    have hall6 : β₆ allOnesW = β₁ a1 * β₁ b1 * (β₁ a2 * β₁ b2) :=
      (hbel6 allOnesW (show C + 64 + 4 < C + 161 by omega)).trans
        ((hbel5 allOnesW (show C + 64 + 4 < C + 93 by omega)).trans
          ((hbel4 allOnesW (show C + 64 + 4 < C + 85 by omega)).trans
            ((hbel3 allOnesW (show C + 64 + 4 < C + 79 by omega)).trans
              ((hbel2 allOnesW (show C + 64 + 4 < C + 73 by omega)).trans hall1))))
    rw [hpb_8, hall6]
    let f36 : Fin 36 → ZMod 2 := fun i ↦
      α (corePayloadSym mPayload ⟨i.val, pay36_lt_payload hmPay i⟩)
    have hw1_f (m : Fin 18) : β₀ (w1 m) = f36 ⟨2 * m.val + 1, slot0Odd18_lt36 m⟩ :=
      hpay _ (slot0Odd18_lt80 m)
    have hw2_f (m : Fin 18) : β₀ (w2 m) = f36 ⟨2 * m.val, slot0Even18_lt36 m⟩ :=
      hpay _ (slot0Even18_lt80 m)
    have hall_iff : β₁ a1 * β₁ b1 * (β₁ a2 * β₁ b2) = 1 ↔ (∑ i : Fin 36, (α (corePayloadSym
        mPayload ⟨i.val, pay36_lt_payload hmPay i⟩)).val * 2 ^ i.val) = 2 ^ 36 - 1 := by
      rw [hprod0, show (∏ i, β₀ (w1 i)) * (∏ i, β₀ (w2 i)) = _ from congrArg₂ (· * ·)
        (Finset.prod_congr rfl fun m _ ↦ hw1_f m) (Finset.prod_congr rfl fun m _ ↦ hw2_f m)]
      exact even_odd_prod_eq_one_iff_u36_allOnes f36
    have hpay5 (k : ℕ) (hk : k < 80) :
        β₅ (payW k hk) = α (corePayloadSym mPayload ⟨k, lt_of_lt_of_le hk hmPay⟩) :=
      (hkeep5 (show 3954 + k < C + 64 by omega)).trans
        ((hbel0 _ (slot0Pay_lt_core hmPay k hk)).trans (hpay k hk))
    by_cases hAll : β₁ a1 * β₁ b1 * (β₁ a2 * β₁ b2) = 1
    · rw [ite_pos_eq hAll, ite_pos_eq (hall_iff.mp hAll)]
      exact (hbel6 bTieW (show 3954 + 79 < C + 161 by omega)).trans (hpay5 79 (by decide))
    · rw [ite_neg_eq hAll, ite_neg_eq (mt hall_iff.mpr hAll)]
      have hax_eq : (((β₁ a1).val + (β₁ b1).val + 2 * ((β₁ a2).val + (β₁ b2).val) +
          (β₁ bParW).val) % 3) = (2 * ((∑ i : Fin 36, (f36 i).val * 2 ^ i.val) % 327) +
            (α (corePayloadSym mPayload ⟨36, lt_of_lt_of_le (by decide) hmPay⟩)).val) % 3 := by
        rw [show β₁ bParW = α (corePayloadSym mPayload ⟨36, lt_of_lt_of_le (by decide) hmPay⟩)
            from (hbel0 _ (slot0Pay_lt_core hmPay 36 (by decide))).trans (hpay 36 (by decide)),
          mod327_mul2_add_mod3, even_odd_bits_mul2_mod3 18 f36, add_mod3_left, hmod0,
          show (∑ i, (β₀ (w1 i)).val) = _ from
            Finset.sum_congr rfl fun m _ ↦ congrArg ZMod.val (hw1_f m),
          show (∑ i, (β₀ (w2 i)).val) = _ from
            Finset.sum_congr rfl fun m _ ↦ congrArg ZMod.val (hw2_f m)]
      let axα := (2 * ((∑ i : Fin 36, (f36 i).val * 2 ^ i.val) % 327) +
        (α (corePayloadSym mPayload ⟨36, lt_of_lt_of_le (by decide) hmPay⟩)).val) % 3
      have hax_lt : axα < 3 := Nat.mod_lt _ (by decide)
      have hax012_bits (b : Fin 6) : stM2 (stM1 dβ) (ax012 b) =
          α ⟨6 * axα + b.val, six_mul_add_lt_core hax_lt b⟩ := by
        rw [hv3 b, hbel2 selBW (show C + 64 + 8 < C + 73 by omega),
          show dβ selBW = _ from hselB1, hax_eq]
        have hel (a : ℕ) (ha : a < 3) : dβ (elecAx a ha b) =
            α ⟨6 * a + b.val, six_mul_add_lt_core ha b⟩ :=
          (hbel1 _ (show 6 * a + b.val < C + 64 by omega)).trans
            ((hbel0 _ (six_mul_add_lt_core ha b)).trans (hpad _ (six_mul_add_lt_core ha b)))
        rcases nat_lt3_cases hax_lt with r0 | r1 | r2
        · rw [ite_neg_eq (by omega : axα ≠ 2), ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1),
            hv2 b, show dβ selAW = _ from hselA1 (by omega), hax_eq,
            ite_neg_eq (by omega : axα ≠ 1), ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1),
            hel 0 (by decide)]
          exact congrArg α (Fin.ext (six_mul_congr r0.symm b.val))
        · rw [ite_neg_eq (by omega : axα ≠ 2), ite_neg_eq (by decide : (0 : ZMod 2) ≠ 1),
            hv2 b, show dβ selAW = _ from hselA1 (by omega), hax_eq, ite_pos_eq r1,
            ite_pos_eq rfl, hel 1 (by decide)]
          exact congrArg α (Fin.ext (six_mul_congr r1.symm b.val))
        · rw [ite_pos_eq r2, ite_pos_eq rfl,
            (hbel2 _ (show 6 * 2 + b.val < C + 73 by omega)).trans (hel 2 (by decide))]
          exact congrArg α (Fin.ext (six_mul_congr r2.symm b.val))
      let u6 : Fin 64 :=
        ⟨bitsVal (fun b : Fin 6 ↦ α ⟨6 * axα + b.val, six_mul_add_lt_core hax_lt b⟩),
          bitsVal_lt_two_pow _⟩
      rw [show (⟨bitsVal (fun b : Fin 6 ↦ stM2 (stM1 dβ) (ax012 b)),
          bitsVal_lt_two_pow _⟩ : Fin 64) = u6 from
            w3_mk_eq (congrArg bitsVal (funext hax012_bits))] at hv4
      have hthr_eq := slot0Thresh_eq_of_natAbs w_eff u6
        ⟨bitsVal (fun i : Fin 5 ↦ stMag (stM2 (stM1 dβ)) (mag5 i)), bitsVal_lt_two_pow _⟩ hv4
      dsimp only [β₆, β₅, ltOut]
      rw [hv6, show bitsVal (fun j : Fin 42 ↦ β₅ (cmpPay42 j)) = ∑ i : Fin 42,
            (α (corePayloadSym mPayload ⟨37 + i.val, pay37_lt_payload hmPay i⟩)).val *
              2 ^ i.val from
          Finset.sum_congr rfl fun j _ ↦
            congrArg (fun x : ZMod 2 ↦ x.val * 2 ^ j.val) (hpay5 (37 + j.val) (pay37_lt_80 j)),
        show bitsVal (fun j : Fin 42 ↦ β₅ (thresh42 j)) =
            MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u6 by
          rw [show (fun j : Fin 42 ↦ β₅ (thresh42 j)) = fun j ↦
              if (MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u6).testBit j.val then 1 else 0
            from funext fun j ↦ by
              rw [hthr_eq]
              exact hv5 j]
          exact bitsVal_of_testBit _ (slot0Thresh_lt_two_pow_42 hw_eff u6)]
  · unfold slot0LocalPhaseBit
    rw [ite_neg_eq hcoin]
    exact slot0_coin_zero_of_not _ _ _ _ hcoin
attribute [local irreducible] slot0LocalProg
inductive TempCzProg (m : ℕ) where
  | nil : TempCzProg m
  | cliff (c : CliffProg m) : TempCzProg m
  | cz (c t : Wire m) (hct : c ≠ t) : TempCzProg m
  | seq (p₁ p₂ : TempCzProg m) : TempCzProg m
  | tempAnd (c₁ c₂ anc : Wire m) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : TempCzProg m) : TempCzProg m
namespace TempCzProg
def czCircuit {m : ℕ} (c t : Wire m) (hct : c ≠ t) : Circuit m :=
  Circuit.H t ;;ᶜ Circuit.CNOT c t hct ;;ᶜ Circuit.H t
def evalBits {m : ℕ} : TempCzProg m → BitAssignment m → BitAssignment m
  | .nil, β | .cz _ _ _, β => β
  | .cliff c, β => c.eval β
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₂ := body.evalBits (Function.update β anc (β anc + β c₁ * β c₂))
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)
def evalSign {m : ℕ} : TempCzProg m → BitAssignment m → ZMod 2
  | .nil, _ | .cliff _, _ => 0
  | .cz c t _, β => β c * β t
  | .seq p₁ p₂, β => p₁.evalSign β + p₂.evalSign (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      body.evalSign (Function.update β anc (β anc + β c₁ * β c₂))
def countTempAnd {m : ℕ} : TempCzProg m → ℕ
  | .nil | .cliff _ | .cz _ _ _ => 0
  | .seq p₁ p₂ => p₁.countTempAnd + p₂.countTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.countTempAnd
def toToffCircuit {m : ℕ} : TempCzProg m → Circuit m
  | .nil => .identity
  | .cliff c => c.toCircuit
  | .cz c t hct => czCircuit c t hct
  | .seq p₁ p₂ => p₁.toToffCircuit ;;ᶜ p₂.toToffCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toToffCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
def onRegister {m n : ℕ} (r : QRegister m n) : TempCzProg m → TempCzProg n
  | .nil => .nil
  | .cliff c => .cliff (c.onRegister r)
  | .cz c t hct => .cz (r c) (r t) (r.wires.injective.ne hct)
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => .tempAnd (r c₁) (r c₂) (r anc)
      (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
      (body.onRegister r)
def toDyn {Var : Type} {n : ℕ} (v : Var) : TempCzProg n → DynamicCircuit Var n
  | .nil => .circuit .identity
  | .cliff c => .circuit c.toCircuit
  | .cz c t hct => .circuit (czCircuit c t hct)
  | .seq p₁ p₂ => .seq (p₁.toDyn v) (p₂.toDyn v)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq (body.toDyn v) (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
@[simp] theorem onRegister_countTempAnd {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempCzProg m, (p.onRegister r).countTempAnd = p.countTempAnd
  | .nil | .cliff _ | .cz _ _ _ => rfl
  | .seq p₁ p₂ => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
  | .tempAnd _ _ _ _ _ _ body => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
@[simp] theorem toDyn_count_toff {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempCzProg n, (p.toDyn v).count PrimitiveGate.TOFF = 0
  | .nil | .cliff _ => by simp [toDyn]
  | .cz _ _ _ => by simp [toDyn, czCircuit]
  | .seq _ _ => by simp [toDyn, toDyn_count_toff]
  | .tempAnd _ _ _ _ _ _ _ => by
      simp [toDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, toDyn_count_toff]
@[simp] theorem toDyn_count_t {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempCzProg n, (p.toDyn v).count PrimitiveGate.T = 4 * p.countTempAnd
  | .nil | .cliff _ => by simp [toDyn, countTempAnd]
  | .cz _ _ _ => by simp [toDyn, czCircuit, countTempAnd]
  | .seq _ _ => by
      simp [toDyn, countTempAnd, toDyn_count_t]
      ring
  | .tempAnd _ _ _ _ _ _ _ => by
      simp [toDyn, DynamicCircuit.count_andCompute_t, DynamicCircuit.count_andUncompute_t,
        countTempAnd, toDyn_count_t]
      ring
theorem toToffCircuit_eval_ket {m : ℕ} : ∀ (p : TempCzProg m) (β : BitAssignment m),
    (p.toToffCircuit).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (p.evalSign β).val) • MeasureBranchHadamardSem.ket (p.evalBits β)
  | .nil, _ => by simp [toToffCircuit, evalSign, TempCzProg.evalBits]
  | .cliff c, _ => by simp [toToffCircuit, evalSign, TempCzProg.evalBits, c.toCircuit_eval_ket]
  | .cz c t hct, β => OctahedralOrbit.ket_CZ c t hct β
  | .seq p₁ p₂, β => by
      rw [toToffCircuit, eval_seq_mulVec, toToffCircuit_eval_ket p₁, Matrix.mulVec_smul,
        toToffCircuit_eval_ket p₂, smul_smul, TempPhaseProg.neg_one_pow_zmod2_mul]
      rfl
  | .tempAnd _ _ _ _ _ _ body, _ => by
      rw [toToffCircuit, eval_seq_mulVec, eval_seq_mulVec, ket_TOFF,
        toToffCircuit_eval_ket body, Matrix.mulVec_smul, ket_TOFF]
      rfl
theorem onRegister_toToffCircuit_eval {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempCzProg m,
      ((p.onRegister r).toToffCircuit).eval = (p.toToffCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toToffCircuit]
  | .cliff c => by simp [onRegister, toToffCircuit, c.onRegister_toCircuit_eval]
  | .cz c t hct => by
      simp [onRegister, toToffCircuit, czCircuit, Circuit.eval_seq,
        show (Circuit.H (r t)).eval = ((Circuit.H t).onRegister r).eval by
          simp only [Circuit.H, Circuit.single, Circuit.onRegister]
          congr 2,
        show (Circuit.CNOT (r c) (r t) (r.wires.injective.ne hct)).eval =
            ((Circuit.CNOT c t hct).onRegister r).eval by
          simp only [Circuit.CNOT, Circuit.onRegister]
          congr 2
          exact MomSlot0LocalAndMomCombine288Alt.qreg_ext fun i ↦ by
            fin_cases i
            all_goals rfl]
  | .seq _ _ => by simp [onRegister, toToffCircuit, Circuit.eval_seq, onRegister_toToffCircuit_eval]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [onRegister, toToffCircuit, Circuit.eval_seq, onRegister_toToffCircuit_eval r body,
        show (Circuit.TOFF (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)
            (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)).eval =
            ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).onRegister r).eval by
          simp only [Circuit.TOFF, Circuit.onRegister]
          congr 2
          exact MomSlot0LocalAndMomCombine288Alt.qreg_ext fun i ↦ by
            fin_cases i
            all_goals rfl]
end TempCzProg
structure MomLocalSlotData (mPayload mPGTwist : ℕ) (k : Fin 6)
    (uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))) where
  mWork : ℕ
  oracle : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist k
  uLocalCat : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload + mPGTwist))
  uLocalEff : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))
  hIntertwines : ∀ cfg (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m, U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    FullSysMomSlots0135Concrete.IntertwinesMomCat U_catTwist (uLocalCat cfg) (uLocalEff cfg)
  hLocalSA : ∀ cfg, (uLocalEff cfg).1ᴴ = (uLocalEff cfg).1
  hLocalOffCoin : ∀ cfg, (uLocalEff cfg).1 * (1 - FullSysMomSlots0135Concrete.momCoinProj
    mPayload (FullSysPrepare6Slot.fullSysCoinIdx k)) =
    1 - FullSysMomSlots0135Concrete.momCoinProj mPayload
      (FullSysPrepare6Slot.fullSysCoinIdx k)
  hConjOnCoin : ∀ cfg, (HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) (uLocalEff cfg)).1 *
    FullSysMomSlots0135Concrete.momCoinProj mPayload
      (FullSysPrepare6Slot.fullSysCoinIdx k) =
    (oracle.uSlotEff cfg).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx k)
noncomputable def MomLocalSlotData.ofCoreOnly {mPayload mPGTwist : ℕ} {k : Fin 6}
    {uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))} (mWork : ℕ)
    (oracle : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist k)
    (uLocalEff : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (hLocalSA : ∀ cfg, (uLocalEff cfg).1ᴴ = (uLocalEff cfg).1)
    (hLocalOffCoin : ∀ cfg, (uLocalEff cfg).1 * (1 - FullSysMomSlots0135Concrete.momCoinProj
      mPayload (FullSysPrepare6Slot.fullSysCoinIdx k)) = 1 -
      FullSysMomSlots0135Concrete.momCoinProj mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx k))
    (hConjOnCoin : ∀ cfg,
      (HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) (uLocalEff cfg)).1 *
        FullSysMomSlots0135Concrete.momCoinProj mPayload
          (FullSysPrepare6Slot.fullSysCoinIdx k) =
      (oracle.uSlotEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx k)) :
    MomLocalSlotData mPayload mPGTwist k uBarrel where
  mWork := mWork
  oracle := oracle
  uLocalCat := fun cfg ↦ (QRegister.block 0
    (FullSysMomSlots0135Concrete.momCoreWires mPayload)
    (FullSysMomSlots0135Concrete.mom_zero_add_le _ mPGTwist)).embedUnitary (uLocalEff cfg)
  uLocalEff := uLocalEff
  hIntertwines := fun cfg U_cat _ ↦
    FullSysMomSlots0135Concrete.intertwinesMomCat_of_coreOnly U_cat (uLocalEff cfg)
  hLocalSA := hLocalSA
  hLocalOffCoin := hLocalOffCoin
  hConjOnCoin := hConjOnCoin
theorem unitaryConj_on_coin_of_barrel_id {mPayload : ℕ} (c : Fin 8)
    (B M_slot : Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (hBId : B.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      FullSysMomSlots0135Concrete.momCoinProj mPayload c) (hSlotSA : M_slot.1ᴴ = M_slot.1)
    (hSlotOff : M_slot.1 * (1 - FullSysMomSlots0135Concrete.momCoinProj mPayload c) =
      1 - FullSysMomSlots0135Concrete.momCoinProj mPayload c) :
    (HoistedSwapSelectBridge.unitaryConj B M_slot).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      M_slot.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c := by
  have hLeftOff := FullSysMomSlots0135Concrete.offProj_left_of_sa_and_right
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose mPayload c) hSlotSA hSlotOff
  have hComm : M_slot.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      FullSysMomSlots0135Concrete.momCoinProj mPayload c * M_slot.1 := by
    rw [← sub_sub_cancel M_slot.1 (M_slot.1 * _),
      show M_slot.1 - M_slot.1 * _ = 1 - _ by simpa [Matrix.mul_sub] using hSlotOff,
      ← show M_slot.1 - _ * M_slot.1 = 1 - _ by simpa [Matrix.sub_mul] using hLeftOff,
      sub_sub_cancel]
  have hBB : B.1ᴴ * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      FullSysMomSlots0135Concrete.momCoinProj mPayload c := by
    rw [← hBId, ← Matrix.mul_assoc, show B.1ᴴ * B.1 = 1 from Matrix.mem_unitaryGroup_iff'.mp B.2,
      Matrix.one_mul, hBId]
  rw [HoistedSwapSelectBridge.unitaryConj_val, Matrix.mul_assoc, Matrix.mul_assoc, hBId, hComm,
    ← Matrix.mul_assoc, hBB, ← hComm]
theorem barrel_comm_momCoinProj {mPayload : ℕ}
    (B : Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (hHigh : ∀ q : Wire (FullSysMomSlots0135Concrete.momCoreWires mPayload), 3924 ≤ q.val →
      ∀ b : Fin 2, B.1 * slotBitProj q b = slotBitProj q b * B.1) (c : Fin 8) :
    B.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      FullSysMomSlots0135Concrete.momCoinProj mPayload c * B.1 := by
  have hsys : 3924 ≤ SpecsAux.SpecMirror.systemQubits := by
    dsimp [SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega
  rw [FullSysMomSlots0135Concrete.momCoinProj]
  exact FullSysMomSlots0135Concrete.op_comm_triple B.1 _ _ _
    (hHigh _ (show 3924 ≤ SpecsAux.SpecMirror.systemQubits from hsys) _)
    (hHigh _ (show 3924 ≤ SpecsAux.SpecMirror.systemQubits + 1 from Nat.le_add_right_of_le hsys) _)
    (hHigh _ (show 3924 ≤ SpecsAux.SpecMirror.systemQubits + 2 from Nat.le_add_right_of_le hsys) _)
theorem unitaryConj_on_coin_transfer {mPayload : ℕ} (c : Fin 8)
    (B M_all M_slot : Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (hBComm : B.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      FullSysMomSlots0135Concrete.momCoinProj mPayload c * B.1)
    (hLocal : M_all.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      M_slot.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c) :
    (HoistedSwapSelectBridge.unitaryConj B M_all).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      (HoistedSwapSelectBridge.unitaryConj B M_slot).1 *
        FullSysMomSlots0135Concrete.momCoinProj mPayload c := by
  simp only [HoistedSwapSelectBridge.unitaryConj_val, Matrix.mul_assoc]
  rw [hBComm, ← Matrix.mul_assoc M_all.1, hLocal, Matrix.mul_assoc M_slot.1, ← hBComm]
noncomputable def slot0LocalData {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (kMap : SpecsAux.SpecMirror.Configuration → BitAssignment (coreWiresSym mPayload) → Fin 218)
    (hkInv : ∀ cfg β, kMap cfg (swapElec0Bits (kMap cfg β) β) = kMap cfg β)
    (hkActive : ∀ cfg β, β (MomSlots01Slot0ElectronKinetic.iSlot0Mom mPayload) = 0 →
      β (MomSlots01Slot0ElectronKinetic.iSlot1Mom mPayload) = 0 →
      β (MomSlots01Slot0ElectronKinetic.iSlot2Mom mPayload) = 1 →
      (∑ i : Fin 36, (β (corePayloadSym mPayload ⟨i.val, by omega⟩)).val * 2 ^ i.val) ≠
        2 ^ 36 - 1 → kMap cfg β = slot0ElecIdx hmPay β)
    (hAct : ∀ cfg β, β (MomSlots01Slot0ElectronKinetic.iSlot0Mom mPayload) = 0 →
      β (MomSlots01Slot0ElectronKinetic.iSlot1Mom mPayload) = 0 →
      β (MomSlots01Slot0ElectronKinetic.iSlot2Mom mPayload) = 1 →
      (uBarrel cfg).1.mulVec (ket β) = ket (swapElec0Bits (kMap cfg β) β)) :
    MomLocalSlotData mPayload 48 0 uBarrel :=
  MomLocalSlotData.ofCoreOnly slot0LocalWorkWires
    (MomSlot0CircuitHalf.slot0ElectronKineticOracleSym hmPay)
    (fun _ ↦ uSlot0Local hmPay lambdaSlot0TeHi)
    (fun _ ↦ uSlot0Local_sa hmPay lambdaSlot0TeHi)
    (fun _ ↦ uSlot0Local_offCoin hmPay lambdaSlot0TeHi)
    (fun cfg ↦ unitaryConj_uSlot0Local_on_coin4 hmPay lambdaSlot0TeHi (uBarrel cfg)
      (kMap cfg) (hkInv cfg) (hkActive cfg) (hAct cfg))
noncomputable def liftOracleWithIdOnCoin {mPayload mPGTwist : ℕ} {k : Fin 6}
    (s : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist k)
    (uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (hBId : ∀ cfg, (uBarrel cfg).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx k) =
      FullSysMomSlots0135Concrete.momCoinProj mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx k)) :
    MomLocalSlotData mPayload mPGTwist k uBarrel :=
  ⟨s.mWork, s, s.uSlotCat, s.uSlotEff,
    s.hIntertwines, s.hSA, s.hOffCoin, fun cfg ↦ unitaryConj_on_coin_of_barrel_id
      (FullSysPrepare6Slot.fullSysCoinIdx k) (uBarrel cfg) (s.uSlotEff cfg)
      (hBId cfg) (s.hSA cfg) (s.hOffCoin cfg)⟩
structure CombinedLocalMomData {mPayload mPGTwist mWorkSelect : ℕ}
    (uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)))
    (s0 : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist 0)
    (s1 : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist 1)
    (s3 : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist 3)
    (s5 : FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload mPGTwist 5) where
  uMomLocalCat : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload + mPGTwist))
  uMomLocal : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))
  hIntertwinesMomLocal : ∀ cfg (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m, U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    FullSysMomSlots0135Concrete.IntertwinesMomCat U_catTwist
      (uMomLocalCat cfg) (uMomLocal cfg)
  hMomLocal_sa : ∀ cfg, (uMomLocal cfg).1ᴴ = (uMomLocal cfg).1
  hMomLocal_on_P0 : ∀ cfg,
    (uMomLocal cfg).1 * slotBitProj (FullSysMomSlots0135Concrete.iSlot2Mom mPayload) 0 =
      slotBitProj (FullSysMomSlots0135Concrete.iSlot2Mom mPayload) 0
  hCoin4 : ∀ cfg, (HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) (uMomLocal cfg)).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload 4 =
    (s0.uSlotEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 4
  hCoin5 : ∀ cfg, (HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) (uMomLocal cfg)).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload 5 =
    (s1.uSlotEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 5
  hCoin6 : ∀ cfg, (HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) (uMomLocal cfg)).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload 6 =
    (s3.uSlotEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 6
  hCoin7 : ∀ cfg, (HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) (uMomLocal cfg)).1 *
      FullSysMomSlots0135Concrete.momCoinProj mPayload 7 =
    (s5.uSlotEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 7
theorem combineFourLocalMomSlots_alg {mPayload mPGTwist : ℕ}
    {uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))}
    (l0 : MomLocalSlotData mPayload mPGTwist 0 uBarrel)
    (l1 : MomLocalSlotData mPayload mPGTwist 1 uBarrel)
    (l3 : MomLocalSlotData mPayload mPGTwist 3 uBarrel)
    (l5 : MomLocalSlotData mPayload mPGTwist 5 uBarrel) (cfg : SpecsAux.SpecMirror.Configuration) :
    let u01 := l1.uLocalEff cfg * l0.uLocalEff cfg
    let u35 := l5.uLocalEff cfg * l3.uLocalEff cfg
    let uAll := u35 * u01
    uAll.1ᴴ = uAll.1 ∧
      uAll.1 * slotBitProj (FullSysMomSlots0135Concrete.iSlot2Mom mPayload) 0 =
        slotBitProj (FullSysMomSlots0135Concrete.iSlot2Mom mPayload) 0 ∧
      uAll.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 4 =
        (l0.uLocalEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 4 ∧
      uAll.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 5 =
        (l1.uLocalEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 5 ∧
      uAll.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 6 =
        (l3.uLocalEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 6 ∧
      uAll.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 7 =
        (l5.uLocalEff cfg).1 * FullSysMomSlots0135Concrete.momCoinProj mPayload 7 := by
  have h01 := FullSysMomSlots0135Concrete.disjoint_two_proj_comm_and_sum
    (FullSysMomSlots0135Concrete.momCoinProj mPayload 4)
    (FullSysMomSlots0135Concrete.momCoinProj mPayload 5) (l0.uLocalEff cfg) (l1.uLocalEff cfg)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose mPayload 4)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose mPayload 5)
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne mPayload (by decide))
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne mPayload (by decide))
    (l0.hLocalOffCoin cfg) (l1.hLocalOffCoin cfg) (l0.hLocalSA cfg) (l1.hLocalSA cfg)
  have h35 := FullSysMomSlots0135Concrete.disjoint_two_proj_comm_and_sum
    (FullSysMomSlots0135Concrete.momCoinProj mPayload 6)
    (FullSysMomSlots0135Concrete.momCoinProj mPayload 7) (l3.uLocalEff cfg) (l5.uLocalEff cfg)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose mPayload 6)
    (FullSysMomSlots0135Concrete.momCoinProj_conjTranspose mPayload 7)
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne mPayload (by decide))
    (FullSysMomSlots0135Concrete.momCoinProj_mul_of_ne mPayload (by decide))
    (l3.hLocalOffCoin cfg) (l5.hLocalOffCoin cfg) (l3.hLocalSA cfg) (l5.hLocalSA cfg)
  have hsa {q1 q2 : Wire (FullSysMomSlots0135Concrete.momCoreWires mPayload)}
      {b1 b2 : Fin 2} :
      (slotBitProj q1 b1 * slotBitProj q2 b2)ᴴ = slotBitProj q1 b1 * slotBitProj q2 b2 := by
    rw [Matrix.conjTranspose_mul, FullSysMomSlots0135Concrete.slotBitProj_self_adj,
      FullSysMomSlots0135Concrete.slotBitProj_self_adj,
      FullSysMomSlots0135Concrete.slotBitProj_comm_any]
  have hAll := FullSysMomSlots0135Concrete.disjoint_two_proj_comm_and_sum
    (FullSysMomSlots0135Concrete.slot45MomProj mPayload)
    (FullSysMomSlots0135Concrete.slot67MomProj mPayload)
    (l1.uLocalEff cfg * l0.uLocalEff cfg) (l5.uLocalEff cfg * l3.uLocalEff cfg) hsa hsa
    (FullSysMomSlots0135Concrete.slot45MomProj_mul_slot67MomProj mPayload)
    (FullSysMomSlots0135Concrete.slot67MomProj_mul_slot45MomProj mPayload)
    (FullSysMomSlots0135Concrete.momCoinProj_4_add_5_eq_slot45 mPayload ▸ h01.2.2.2.2.1)
    (FullSysMomSlots0135Concrete.momCoinProj_6_add_7_eq_slot67 mPayload ▸ h35.2.2.2.2.1)
    h01.2.1 h35.2.1
  have hstep {A B C P Q : Operator (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))}
      (h1 : A * P = B * P) (h2 : P * Q = Q) (h3 : B * Q = C * Q) : A * Q = C * Q := by
    rw [← h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, h3]
  exact ⟨hAll.2.1, hAll.2.2.2.2.2 _
      (FullSysMomSlots0135Concrete.slot45MomProj_mul_iSlot2_zero mPayload)
      (FullSysMomSlots0135Concrete.slot67MomProj_mul_iSlot2_zero mPayload),
    hstep hAll.2.2.1 (FullSysMomSlots0135Concrete.slot45MomProj_mul_momCoinProj mPayload
      (c := 4) (by decide) (by decide)) h01.2.2.1,
    hstep hAll.2.2.1 (FullSysMomSlots0135Concrete.slot45MomProj_mul_momCoinProj mPayload
      (c := 5) (by decide) (by decide)) h01.2.2.2.1,
    hstep hAll.2.2.2.1 (FullSysMomSlots0135Concrete.slot67MomProj_mul_momCoinProj mPayload
      (c := 6) (by decide) (by decide)) h35.2.2.1,
    hstep hAll.2.2.2.1 (FullSysMomSlots0135Concrete.slot67MomProj_mul_momCoinProj mPayload
      (c := 7) (by decide) (by decide)) h35.2.2.2.1⟩
noncomputable def combineFourLocalMomSlots {mPayload mPGTwist mWorkSelect : ℕ}
    {uBarrel : SpecsAux.SpecMirror.Configuration →
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload))}
    (l0 : MomLocalSlotData mPayload mPGTwist 0 uBarrel)
    (l1 : MomLocalSlotData mPayload mPGTwist 1 uBarrel)
    (l3 : MomLocalSlotData mPayload mPGTwist 3 uBarrel)
    (l5 : MomLocalSlotData mPayload mPGTwist 5 uBarrel)
    (_hw0 : l0.mWork ≤ mWorkSelect) (_hw1 : l1.mWork ≤ mWorkSelect)
    (_hw3 : l3.mWork ≤ mWorkSelect) (_hw5 : l5.mWork ≤ mWorkSelect)
    (hBarrelHigh : ∀ cfg (q : Wire (FullSysMomSlots0135Concrete.momCoreWires mPayload)),
      3924 ≤ q.val → ∀ b : Fin 2,
        (uBarrel cfg).1 * slotBitProj q b = slotBitProj q b * (uBarrel cfg).1) :
    CombinedLocalMomData (mWorkSelect := mWorkSelect) uBarrel
      l0.oracle l1.oracle l3.oracle l5.oracle :=
  { uMomLocalCat := fun cfg ↦
      (l5.uLocalCat cfg * l3.uLocalCat cfg) * (l1.uLocalCat cfg * l0.uLocalCat cfg)
    uMomLocal := fun cfg ↦
      (l5.uLocalEff cfg * l3.uLocalEff cfg) * (l1.uLocalEff cfg * l0.uLocalEff cfg)
    hIntertwinesMomLocal := fun cfg U_cat hU ↦
      .mul (.mul (l5.hIntertwines cfg U_cat hU) (l3.hIntertwines cfg U_cat hU))
        (.mul (l1.hIntertwines cfg U_cat hU) (l0.hIntertwines cfg U_cat hU))
    hMomLocal_sa := fun cfg ↦ (combineFourLocalMomSlots_alg l0 l1 l3 l5 cfg).1
    hMomLocal_on_P0 := fun cfg ↦ (combineFourLocalMomSlots_alg l0 l1 l3 l5 cfg).2.1
    hCoin4 := fun cfg ↦ (unitaryConj_on_coin_transfer 4 _ _ _ (barrel_comm_momCoinProj _
      (hBarrelHigh cfg) 4) (combineFourLocalMomSlots_alg l0 l1 l3 l5 cfg).2.2.1).trans
      (l0.hConjOnCoin cfg)
    hCoin5 := fun cfg ↦ (unitaryConj_on_coin_transfer 5 _ _ _ (barrel_comm_momCoinProj _
      (hBarrelHigh cfg) 5) (combineFourLocalMomSlots_alg l0 l1 l3 l5 cfg).2.2.2.1).trans
      (l1.hConjOnCoin cfg)
    hCoin6 := fun cfg ↦ (unitaryConj_on_coin_transfer 6 _ _ _ (barrel_comm_momCoinProj _
      (hBarrelHigh cfg) 6) (combineFourLocalMomSlots_alg l0 l1 l3 l5 cfg).2.2.2.2.1).trans
      (l3.hConjOnCoin cfg)
    hCoin7 := fun cfg ↦ (unitaryConj_on_coin_transfer 7 _ _ _ (barrel_comm_momCoinProj _
      (hBarrelHigh cfg) 7) (combineFourLocalMomSlots_alg l0 l1 l3 l5 cfg).2.2.2.2.2).trans
      (l5.hConjOnCoin cfg) }
end MomSlot0LocalAndMomCombine288
end
end ModMomSlot0LocalAndMomCombine288

section ModTempPhasePerm
@[expose] public section
section SharedScope
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem
open StreamingBchComparator
open MomSlot0CircuitHalf (padZeroBits)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
theorem realizes_signedPerm_cleanWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kAct mClean mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : mClean ≤ mWork)
    (U : Unitary (2 ^ kAct))
    (perm : BitAssignment kAct → BitAssignment kAct)
    (phase : BitAssignment kAct → ZMod 2)
    (hU : ∀ α : BitAssignment kAct,
      U.1.mulVec (ket α) = ((-1 : ℂ) ^ (phase α).val) • ket (perm α))
    (p : TempPhaseProg (kAct + mClean))
    (hValid : ValidCleanRem (kAct + mClean) mClean p)
    (hBits : ∀ α : BitAssignment kAct, p.evalBits (padZeroBits α) = padZeroBits (perm α))
    (hSign : ∀ α : BitAssignment kAct, p.evalSign (padZeroBits α) = phase α) :
    let rSub : QRegister mClean n := rWork.slice 0 mClean (by omega)
    let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
    let dyn := (p.onRegister rComb).toDyn v
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork U dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 4 * p.countTempAnd :=
  w3_realizes_signedPerm_core v rAct rWork hdisj hw_len U perm phase
    (fun α l ↦ by
      simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using
        congrFun (hU α) l)
    p hValid hBits hSign
theorem CliffProg.supportsBelow_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) :
    ∀ {c : CliffProg M}, c.SupportsBelow b₁ → c.SupportsBelow b₂
  | .nil, _ => trivial
  | .x _, h => lt_of_lt_of_le h hle
  | .cnot _ _ _, ⟨hc, ht⟩ => ⟨lt_of_lt_of_le hc hle, lt_of_lt_of_le ht hle⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨supportsBelow_mono hle h₁, supportsBelow_mono hle h₂⟩
def CliffDisjoint {M : ℕ} (mutW : Wire M → Prop) : CliffProg M → Prop
  | .nil => True
  | .x q => ¬ mutW q
  | .cnot c t _ => ¬ mutW c ∧ ¬ mutW t
  | .seq c₁ c₂ => CliffDisjoint mutW c₁ ∧ CliffDisjoint mutW c₂
theorem CliffDisjoint.inv {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c → CliffDisjoint mutW c.inv
  | .nil, _ => trivial
  | .x _, h | .cnot _ _ _, h => h
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨h₂.inv, h₁.inv⟩
theorem CliffDisjoint.eval_mut {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c →
      ∀ (β : BitAssignment M) {w : Wire M}, mutW w → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x _, hq, _, _, hw => Function.update_of_ne (fun h ↦ hq (Eq.mp (congrArg mutW h) hw)) _ _
  | .cnot _ _ _, ⟨_, hnt⟩, _, _, hw =>
      Function.update_of_ne (fun h ↦ hnt (Eq.mp (congrArg mutW h) hw)) _ _
  | .seq _ _, ⟨h₁, h₂⟩, _, _, hw => (h₂.eval_mut _ hw).trans (h₁.eval_mut _ hw)
theorem CliffDisjoint.eval_congr_nonMut {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c → ∀ {β₁ β₂ : BitAssignment M},
      (∀ w, ¬ mutW w → β₁ w = β₂ w) → ∀ w, ¬ mutW w → c.eval β₁ w = c.eval β₂ w
  | .nil, _, _, _, hEq, w, hw => hEq w hw
  | .x q, hq, _, _, hEq, w, hw => by
      rcases eq_or_ne w q with rfl | hwq
      · simp [CliffProg.eval, hEq w hq]
      · simp [CliffProg.eval, Function.update_of_ne hwq, hEq w hw]
  | .cnot c t _, ⟨hnc, hnt⟩, _, _, hEq, w, hw => by
      rcases eq_or_ne w t with rfl | hwt
      · simp [CliffProg.eval, hEq w hnt, hEq c hnc]
      · simp [CliffProg.eval, Function.update_of_ne hwt, hEq w hw]
  | .seq _ _, ⟨h₁, h₂⟩, _, _, hEq, w, hw =>
      h₂.eval_congr_nonMut (fun u hu ↦ h₁.eval_congr_nonMut hEq u hu) w hw
inductive TempCtx (M : ℕ) where
  | hole : TempCtx M
  | seqPre (c : CliffProg M) (K : TempCtx M) : TempCtx M
  | seqPost (K : TempCtx M) (c : CliffProg M) : TempCtx M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (K : TempCtx M) : TempCtx M
namespace TempCtx
def plug {M : ℕ} : TempCtx M → TempPhaseProg M → TempPhaseProg M
  | .hole, body => body
  | .seqPre c K, body => .seq (.cliff c) (K.plug body)
  | .seqPost K c, body => .seq (K.plug body) (.cliff c)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, body => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (K.plug body)
def append {M : ℕ} : TempCtx M → TempCtx M → TempCtx M
  | .hole, G => G
  | .seqPre c K, G => .seqPre c (K.append G)
  | .seqPost K c, G => .seqPost (K.append G) c
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, G => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (K.append G)
theorem append_plug {M : ℕ} : ∀ (F G : TempCtx M) (body : TempPhaseProg M),
    (F.append G).plug body = F.plug (G.plug body)
  | .hole, _, _ => rfl
  | .seqPre _ K, G, b | .seqPost K _, G, b | .tempAnd _ _ _ _ _ _ K, G, b =>
      by simp [append, plug, append_plug K G b]
def countTempAnd {M : ℕ} : TempCtx M → ℕ
  | .hole => 0
  | .seqPre _ K | .seqPost K _ => K.countTempAnd
  | .tempAnd _ _ _ _ _ _ K => 1 + K.countTempAnd
@[simp] theorem plug_countTempAnd {M : ℕ} : ∀ (K : TempCtx M) (body : TempPhaseProg M),
    (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd
  | .hole, _ => by simp [plug, countTempAnd]
  | .seqPre _ K, b | .seqPost K _, b =>
      by simp [plug, countTempAnd, TempPhaseProg.countTempAnd, plug_countTempAnd K b]
  | .tempAnd _ _ _ _ _ _ K, b => by
      simp only [plug, countTempAnd, TempPhaseProg.countTempAnd, plug_countTempAnd K b]
      omega
def fwdBits {M : ℕ} : TempCtx M → BitAssignment M → BitAssignment M
  | .hole, β => β
  | .seqPre c K, β => K.fwdBits (c.eval β)
  | .seqPost K _, β => K.fwdBits β
  | .tempAnd c₁ c₂ anc _ _ _ K, β => K.fwdBits (Function.update β anc (β anc + β c₁ * β c₂))
def DisjointFrom {M : ℕ} (mutW : Wire M → Prop) : TempCtx M → Prop
  | .hole => True
  | .seqPre c K => CliffDisjoint mutW c ∧ K.DisjointFrom mutW
  | .seqPost K c => K.DisjointFrom mutW ∧ CliffDisjoint mutW c
  | .tempAnd c₁ c₂ anc _ _ _ K => ¬ mutW c₁ ∧ ¬ mutW c₂ ∧ ¬ mutW anc ∧ K.DisjointFrom mutW
def SupportsBelowCtx {M : ℕ} (curHole : ℕ) : TempCtx M → Prop
  | .hole => True
  | .seqPre c K => c.SupportsBelow curHole ∧ K.SupportsBelowCtx curHole
  | .seqPost K c => K.SupportsBelowCtx curHole ∧ c.SupportsBelow curHole
  | .tempAnd _ _ anc _ _ _ K => anc.val < curHole ∧ K.SupportsBelowCtx curHole
theorem disjointFrom_append {M : ℕ} {mutW : Wire M → Prop} : ∀ {F G : TempCtx M},
    F.DisjointFrom mutW → G.DisjointFrom mutW → (F.append G).DisjointFrom mutW
  | .hole, _, _, hG => hG
  | .seqPre _ _, _, hF, hG => ⟨hF.1, disjointFrom_append hF.2 hG⟩
  | .seqPost _ _, _, hF, hG => ⟨disjointFrom_append hF.1 hG, hF.2⟩
  | .tempAnd _ _ _ _ _ _ _, _, hF, hG =>
      ⟨hF.1, hF.2.1, hF.2.2.1, disjointFrom_append hF.2.2.2 hG⟩
theorem supportsBelowCtx_append {M c₁ c₂ : ℕ} (hle : c₁ ≤ c₂) : ∀ {F G : TempCtx M},
    F.SupportsBelowCtx c₁ → G.SupportsBelowCtx c₂ → (F.append G).SupportsBelowCtx c₂
  | .hole, _, _, hG => hG
  | .seqPre _ _, _, hF, hG =>
      ⟨CliffProg.supportsBelow_mono hle hF.1, supportsBelowCtx_append hle hF.2 hG⟩
  | .seqPost _ _, _, hF, hG =>
      ⟨supportsBelowCtx_append hle hF.1 hG, CliffProg.supportsBelow_mono hle hF.2⟩
  | .tempAnd _ _ _ _ _ _ _, _, hF, hG =>
      ⟨lt_of_lt_of_le hF.1 hle, supportsBelowCtx_append hle hF.2 hG⟩
theorem plug_evalSign {M : ℕ} : ∀ (K : TempCtx M) (body : TempPhaseProg M)
    (β : BitAssignment M),
    (K.plug body).evalSign β = body.evalSign (K.fwdBits β)
  | .hole, _, _ => rfl
  | .seqPre _ K, b, _ | .seqPost K _, b, _ | .tempAnd _ _ _ _ _ _ K, b, _ => by
      simp [plug, fwdBits, TempPhaseProg.evalSign, TempPhaseProg.evalBits, plug_evalSign K b]
theorem plug_evalBits_split {M : ℕ} {mutW : Wire M → Prop} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) {body : TempPhaseProg M}
    (hBodyNonMut : ∀ γ w, ¬ mutW w → body.evalBits γ w = γ w) (q₀ : Wire M)
    (β : BitAssignment M) : (∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits
    (K.fwdBits β) w) ∧ (∀ w, ¬ mutW w → (K.plug body).evalBits β w = (K.plug (.z q₀)).evalBits
    β w) := by
  induction K generalizing β with
  | hole => exact ⟨fun _ _ ↦ rfl, fun w hw ↦ hBodyNonMut β w hw⟩
  | seqPre c _ ih => exact ih hDisj.2 (c.eval β)
  | seqPost _ _ ih =>
      obtain ⟨hM, hN⟩ := ih hDisj.1 β
      exact ⟨fun w hw ↦ (hDisj.2.eval_mut _ hw).trans (hM w hw),
        fun w hw ↦ hDisj.2.eval_congr_nonMut hN w hw⟩
  | tempAnd c₁ c₂ anc _ _ _ K₁ ih =>
      obtain ⟨hM, hN⟩ := ih hDisj.2.2.2 (Function.update β anc (β anc + β c₁ * β c₂))
      refine ⟨fun w hw ↦ (Function.update_of_ne (fun h ↦ hDisj.2.2.1
        (Eq.mp (congrArg mutW h) hw)) _ _).trans (hM w hw), fun w hw ↦ ?_⟩
      dsimp only [plug, TempPhaseProg.evalBits]
      by_cases hwa : w = anc
      · rw [hwa]
        simp [hN anc hDisj.2.2.1, hN c₁ hDisj.1, hN c₂ hDisj.2.1]
      · simp [Function.update_of_ne hwa, hN w hw]
theorem plug_validCleanRem {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyValid : ValidCleanRem M (M - curHole) body)
    (hBodyNonMut : ∀ γ w, ¬ mutW w → body.evalBits γ w = γ w) (q₀ : Wire M) :
    ∀ {rem : ℕ}, M - curHole ≤ rem → ValidCleanRem M rem (K.plug (.z q₀)) →
      ValidCleanRem M rem (K.plug body) := by
  induction K with
  | hole => exact fun hle _ ↦ validCleanRem_mono hle hBodyValid
  | seqPre c _ ih =>
      intro rem _ ⟨remMid, _, _, hv₁, hpres₁⟩
      refine ⟨max remMid (M - curHole), by omega, trivial, ih hDisj.2 hSupp.2
        (Nat.le_max_right _ _) (validCleanRem_mono (Nat.le_max_left _ _) hv₁),
        fun β hβ w hw ↦ ?_⟩
      by_cases hw1 : M - remMid ≤ w.val
      · exact hpres₁ β hβ w hw1
      · exact (c.eval_outside hSupp.1 β w (by omega)).trans (hβ w (by omega))
  | seqPost _ _ ih =>
      exact fun hle ⟨_, _, hv₁, _, _⟩ ↦ ⟨0, Nat.zero_le M, ih hDisj.1 hSupp.1 hle hv₁,
        trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩
  | tempAnd c₁ c₂ anc _ _ _ _ ih =>
      intro _ _ ⟨hanc_lo, hv₁, hpres₁⟩
      refine ⟨hanc_lo, ih hDisj.2.2.2 hSupp.2 (by
        have := hSupp.1
        omega) hv₁, fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨_, hN⟩ := plug_evalBits_split hDisj.2.2.2 hBodyNonMut q₀ β₁
      rw [hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
      exact hpres₁ β₁ hβ₁
end TempCtx
theorem ScopedBlock.graft_mutating_body {M rem curHole : ℕ} [NeZero M] (mutW : Wire M → Prop)
    [DecidablePred mutW] (K : TempCtx M) (hDisj : K.DisjointFrom mutW)
    (hSupp : K.SupportsBelowCtx curHole) (hle : M - curHole ≤ rem)
    (setup : BitAssignment M → BitAssignment M) (hProbe : ∀ q : Wire M, ScopedBlock M rem
    setup (.z q) (K.plug (.z q))) (body : TempPhaseProg M)
    (hBodyValid : ValidCleanRem M (M - curHole) body)
    (hBodyNonMut : ∀ γ w, ¬ mutW w → body.evalBits γ w = γ w) : ValidCleanRem M rem
    (K.plug body) ∧ (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd ∧ (∀ β :
    BitAssignment M, cleanRem M rem β → (K.plug body).evalSign β = body.evalSign (setup β)) ∧
    (∀ β : BitAssignment M, cleanRem M rem β → ∀ w : Wire M, (K.plug body).evalBits β w = if
    mutW w then body.evalBits (setup β) w else β w) := by
  let q₀ : Wire M := ⟨0, NeZero.pos M⟩
  have hFwd (β : BitAssignment M) (hβ : cleanRem M rem β) : K.fwdBits β = setup β :=
    funext fun q ↦ (K.plug_evalSign (.z q) β).symm.trans ((hProbe q).sign β hβ)
  refine ⟨K.plug_validCleanRem hDisj hSupp hBodyValid hBodyNonMut q₀ hle (hProbe q₀).valid,
    K.plug_countTempAnd body, fun β hβ ↦ by rw [K.plug_evalSign, hFwd β hβ], fun β hβ w ↦ ?_⟩
  obtain ⟨hM, hN⟩ := K.plug_evalBits_split hDisj hBodyNonMut q₀ β
  by_cases hw : mutW w
  · simp [hw, hM w hw, hFwd β hβ]
  · simp [hw, hN w hw, (hProbe q₀).bits β hβ]
def ctxCliffAlloc {M : ℕ} (c : CliffProg M) : TempCtx M := .seqPre c (.seqPost .hole c.inv)
@[simp] theorem ctxCliffAlloc_plug {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) :
    (ctxCliffAlloc c).plug body = withCliffAlloc c body := rfl
theorem ctxCliffAlloc_disjoint {M : ℕ} {mutW : Wire M → Prop} {c : CliffProg M}
    (hc : CliffDisjoint mutW c) : (ctxCliffAlloc c).DisjointFrom mutW := ⟨hc, trivial, hc.inv⟩
theorem ctxCliffAlloc_supports {M bound : ℕ} {c : CliffProg M} (hc : c.SupportsBelow bound) :
    (ctxCliffAlloc c).SupportsBelowCtx bound := ⟨hc, trivial, CliffProg.inv_supportsBelow c hc⟩
def ctxTempBit {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    TempCtx M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a .hole
@[simp] theorem ctxTempBit_plug {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (body : TempPhaseProg M) :
    (ctxTempBit c₁ c₂ anc h₁₂ h₁a h₂a).plug body =
      withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body := rfl
def cswapBitProg {M : ℕ} (ctrl a b anc : Wire M) (hab : a ≠ b) (hca : ctrl ≠ a)
    (hc_anc : ctrl ≠ anc) (ha_anc : a ≠ anc) (hb_anc : anc ≠ b) : TempPhaseProg M :=
  .seq (.cnot b a hab.symm)
    (.seq (andXor ctrl a b anc hca hc_anc ha_anc hb_anc) (.cnot b a hab.symm))
@[simp] theorem cswapBitProg_countTempAnd {M : ℕ} (ctrl a b anc : Wire M) (hab : a ≠ b)
    (hca : ctrl ≠ a) (hc_anc : ctrl ≠ anc) (ha_anc : a ≠ anc) (hb_anc : anc ≠ b) :
    (cswapBitProg ctrl a b anc hab hca hc_anc ha_anc hb_anc).countTempAnd = 1 := by
  simp [cswapBitProg, TempPhaseProg.cnot, TempPhaseProg.countTempAnd]
@[simp] theorem cswapBitProg_evalSign {M : ℕ} (ctrl a b anc : Wire M) (hab : a ≠ b)
    (hca : ctrl ≠ a) (hc_anc : ctrl ≠ anc) (ha_anc : a ≠ anc) (hb_anc : anc ≠ b)
    (β : BitAssignment M) :
    (cswapBitProg ctrl a b anc hab hca hc_anc ha_anc hb_anc).evalSign β = 0 := by
  simp [cswapBitProg, TempPhaseProg.cnot, TempPhaseProg.evalSign]
theorem cswapBit_algebra (c x y : ZMod 2) :
    ((x + y) + (y + c * (x + y)) = if c = 1 then y else x) ∧
    (y + c * (x + y) = if c = 1 then x else y) := by decide +revert
theorem cswapBitProg_valid_and_eval {M rem : ℕ} (hrem : rem ≤ M) (ctrl a b anc : Wire M)
    (hab : a ≠ b) (hca : ctrl ≠ a) (hcb : ctrl ≠ b) (hc_lt : ctrl.val < anc.val)
    (ha_lt : a.val < M - rem) (hb_lt : b.val < M - rem) (hanc_rem : M - rem ≤ anc.val) :
    let p := cswapBitProg ctrl a b anc hab hca (wire_ne_of_lt hc_lt)
      (wire_ne_of_lt (lt_of_lt_of_le ha_lt hanc_rem))
      (wire_ne_of_gt (lt_of_lt_of_le hb_lt hanc_rem))
    ValidCleanRem M rem p ∧ ∀ β : BitAssignment M, cleanRem M rem β → p.evalBits β =
      Function.update (Function.update β b (if β ctrl = 1 then β a else β b)) a
        (if β ctrl = 1 then β b else β a) := by
  intro p
  obtain ⟨hvAnd, hevAnd⟩ := andXor_valid_and_eval (rem := rem) ctrl a b anc hca hcb hab hc_lt
    (lt_of_lt_of_le ha_lt hanc_rem) (lt_of_lt_of_le hb_lt hanc_rem) hanc_rem
  have hc1 (β : BitAssignment M) (hβ : cleanRem M rem β) :
      cleanRem M rem ((TempPhaseProg.cnot b a hab.symm).evalBits β) := w3_cleanRem_upd ha_lt hβ
  refine ⟨⟨rem, hrem, trivial, ⟨0, Nat.zero_le M, hvAnd, trivial, fun _ _ _ hw ↦ absurd hw
    (by omega)⟩, hc1⟩, fun β hβ ↦ funext fun w ↦ ?_⟩
  dsimp only [p, cswapBitProg, TempPhaseProg.evalBits]
  rw [hevAnd _ (hc1 β hβ)]
  dsimp only [TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval]
  obtain ⟨hAlgA, hAlgB⟩ := cswapBit_algebra (β ctrl) (β a) (β b)
  rcases eq_or_ne w a with rfl | hwa
  · simp [Function.update_of_ne hab, Function.update_of_ne hab.symm, Function.update_of_ne hca,
      hAlgA]
  · rcases eq_or_ne w b with rfl | hwb
    · simp [Function.update_of_ne hwa, Function.update_of_ne hca, hAlgB]
    · simp [Function.update_of_ne hwa, Function.update_of_ne hwb]
def cswapRegProg {M : ℕ} : (k : ℕ) → (ctrl : Wire M) → (regA regB : Fin k → Wire M) →
    (anc : Wire M) → (hab : ∀ i, regA i ≠ regB i) → (hca : ∀ i, ctrl ≠ regA i) →
    (hc_lt : ctrl.val < anc.val) → (ha_lt : ∀ i, (regA i).val < anc.val) →
    (hb_lt : ∀ i, (regB i).val < anc.val) → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _ => .nil
  | k + 1, ctrl, regA, regB, anc, hab, hca, hc_lt, ha_lt, hb_lt =>
      .seq (cswapBitProg ctrl (regA 0) (regB 0) anc (hab 0) (hca 0) (wire_ne_of_lt hc_lt)
          (wire_ne_of_lt (ha_lt 0)) (wire_ne_of_gt (hb_lt 0)))
        (cswapRegProg k ctrl (fun i ↦ regA i.succ) (fun i ↦ regB i.succ) anc
          (fun i ↦ hab i.succ) (fun i ↦ hca i.succ) hc_lt
          (fun i ↦ ha_lt i.succ) (fun i ↦ hb_lt i.succ))
@[simp] theorem cswapRegProg_countTempAnd {M : ℕ} :
    ∀ (k : ℕ) (ctrl : Wire M) (regA regB : Fin k → Wire M) (anc : Wire M)
      (hab : ∀ i, regA i ≠ regB i) (hca : ∀ i, ctrl ≠ regA i) (hc_lt : ctrl.val < anc.val)
      (ha_lt : ∀ i, (regA i).val < anc.val) (hb_lt : ∀ i, (regB i).val < anc.val),
      (cswapRegProg k ctrl regA regB anc hab hca hc_lt ha_lt hb_lt).countTempAnd = k
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, _, _, _, _, _ => by
      simp only [cswapRegProg, TempPhaseProg.countTempAnd, cswapBitProg_countTempAnd,
        cswapRegProg_countTempAnd]
      omega
@[simp] theorem cswapRegProg_evalSign {M : ℕ} :
    ∀ (k : ℕ) (ctrl : Wire M) (regA regB : Fin k → Wire M) (anc : Wire M)
      (hab : ∀ i, regA i ≠ regB i) (hca : ∀ i, ctrl ≠ regA i) (hc_lt : ctrl.val < anc.val)
      (ha_lt : ∀ i, (regA i).val < anc.val) (hb_lt : ∀ i, (regB i).val < anc.val)
      (β : BitAssignment M),
      (cswapRegProg k ctrl regA regB anc hab hca hc_lt ha_lt hb_lt).evalSign β = 0
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, _, _, _, _, _, _ => by
      simp [cswapRegProg, TempPhaseProg.evalSign, cswapRegProg_evalSign]
theorem cswapRegProg_valid_and_eval {M rem : ℕ} (hrem : rem ≤ M) :
    ∀ (k : ℕ) (ctrl : Wire M) (regA regB : Fin k → Wire M) (anc : Wire M)
      (hab : ∀ i, regA i ≠ regB i) (hca : ∀ i, ctrl ≠ regA i) (_ : ∀ i, ctrl ≠ regB i)
      (_ : Function.Injective regA) (_ : Function.Injective regB) (_ : ∀ i j, regA i ≠ regB j)
      (hc_lt : ctrl.val < anc.val) (ha_lt : ∀ i, (regA i).val < M - rem)
      (hb_lt : ∀ i, (regB i).val < M - rem) (hanc_rem : M - rem ≤ anc.val),
      let p := cswapRegProg k ctrl regA regB anc hab hca hc_lt
        (fun i ↦ lt_of_lt_of_le (ha_lt i) hanc_rem) (fun i ↦ lt_of_lt_of_le (hb_lt i) hanc_rem)
      ValidCleanRem M rem p ∧ ∀ β : BitAssignment M, cleanRem M rem β → ∀ w : Wire M,
        p.evalBits β w =
          if hA : ∃ i, w = regA i then if β ctrl = 1 then β (regB hA.choose) else β w
          else if hB : ∃ i, w = regB i then if β ctrl = 1 then β (regA hB.choose) else β w
          else β w
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨trivial, fun _ _ _ ↦ by simp [cswapRegProg, TempPhaseProg.evalBits]⟩
  | k + 1, ctrl, regA, regB, anc, hab, hca, hcb, hinjA, hinjB, hdisjAB,
      hc_lt, ha_lt, hb_lt, hanc_rem => by
      let p0 := cswapBitProg ctrl (regA 0) (regB 0) anc (hab 0) (hca 0) (wire_ne_of_lt hc_lt)
        (wire_ne_of_lt (lt_of_lt_of_le (ha_lt 0) hanc_rem))
        (wire_ne_of_gt (lt_of_lt_of_le (hb_lt 0) hanc_rem))
      obtain ⟨hv0, hev0⟩ := cswapBitProg_valid_and_eval hrem ctrl (regA 0) (regB 0) anc
        (hab 0) (hca 0) (hcb 0) hc_lt (ha_lt 0) (hb_lt 0) hanc_rem
      obtain ⟨hvRest, hevRest⟩ := cswapRegProg_valid_and_eval hrem k ctrl (fun i ↦ regA i.succ)
        (fun i ↦ regB i.succ) anc (fun i ↦ hab i.succ) (fun i ↦ hca i.succ)
        (fun i ↦ hcb i.succ) (hinjA.comp (Fin.succ_injective k))
        (hinjB.comp (Fin.succ_injective k)) (fun i j ↦ hdisjAB i.succ j.succ) hc_lt
        (fun i ↦ ha_lt i.succ) (fun i ↦ hb_lt i.succ) hanc_rem
      have hcl0 (β : BitAssignment M) (hβ : cleanRem M rem β) :
          cleanRem M rem (p0.evalBits β) := by
        rw [hev0 β hβ]
        exact w3_cleanRem_upd (ha_lt 0) (w3_cleanRem_upd (hb_lt 0) hβ)
      refine ⟨⟨rem, hrem, hv0, hvRest, hcl0⟩, fun β hβ w ↦ ?_⟩
      let β₁ := p0.evalBits β
      have hA_succ (j : Fin k) : β₁ (regA j.succ) = β (regA j.succ) := by
        simp [β₁, p0, hev0 β hβ, Function.update_of_ne (hinjA.ne (Fin.succ_ne_zero j)),
          Function.update_of_ne (hdisjAB j.succ 0)]
      have hB_succ (j : Fin k) : β₁ (regB j.succ) = β (regB j.succ) := by
        simp [β₁, p0, hev0 β hβ, Function.update_of_ne (hdisjAB 0 j.succ).symm,
          Function.update_of_ne (hinjB.ne (Fin.succ_ne_zero j))]
      dsimp only [cswapRegProg, TempPhaseProg.evalBits]
      rw [hevRest β₁ (hcl0 β hβ) w, show β₁ ctrl = β ctrl by
        simp [β₁, p0, hev0 β hβ, Function.update_of_ne (hca 0), Function.update_of_ne (hcb 0)]]
      by_cases hAs : ∃ j : Fin k, w = regA j.succ
      · have hA_all : ∃ i, w = regA i := ⟨hAs.choose.succ, hAs.choose_spec⟩
        simp [hAs, hA_all, hB_succ, show β₁ w = β w by rw [hAs.choose_spec, hA_succ],
          hinjA (hA_all.choose_spec.symm.trans hAs.choose_spec)]
      · by_cases hBs : ∃ j : Fin k, w = regB j.succ
        · have hB_all : ∃ i, w = regB i := ⟨hBs.choose.succ, hBs.choose_spec⟩
          have hA_none : ¬ ∃ i, w = regA i := fun ⟨i, hi⟩ ↦
            hdisjAB i hBs.choose.succ (hi.symm.trans hBs.choose_spec)
          simp [hAs, hBs, hA_none, hB_all, hA_succ,
            show β₁ w = β w by rw [hBs.choose_spec, hB_succ],
            hinjB (hB_all.choose_spec.symm.trans hBs.choose_spec)]
        · simp only [hAs, hBs, ↓reduceDIte]
          dsimp only [β₁]
          rw [hev0 β hβ]
          rcases eq_or_ne w (regA 0) with rfl | hwA0
          · have hA_all : ∃ i, regA 0 = regA i := ⟨0, rfl⟩
            simp [hA_all, hinjA hA_all.choose_spec.symm]
          · rcases eq_or_ne w (regB 0) with rfl | hwB0
            · have hB_all : ∃ i, regB 0 = regB i := ⟨0, rfl⟩
              have hA_none : ¬ ∃ i, regB 0 = regA i := fun ⟨i, hi⟩ ↦ hdisjAB i 0 hi.symm
              simp [Function.update_of_ne hwA0, hA_none, hB_all, hinjB hB_all.choose_spec.symm]
            · have hA_none : ¬ ∃ i, w = regA i := fun ⟨i, hi⟩ ↦
                Fin.cases (fun h : w = regA 0 ↦ hwA0 h)
                  (fun j (h : w = regA j.succ) ↦ hAs ⟨j, h⟩) i hi
              have hB_none : ¬ ∃ i, w = regB i := fun ⟨i, hi⟩ ↦
                Fin.cases (fun h : w = regB 0 ↦ hwB0 h)
                  (fun j (h : w = regB j.succ) ↦ hBs ⟨j, h⟩) i hi
              simp [Function.update_of_ne hwA0, Function.update_of_ne hwB0, hA_none, hB_none]
end SharedScope
end
end ModTempPhasePerm

end QuantumComputation.Specs.StoppingPowerSolution
