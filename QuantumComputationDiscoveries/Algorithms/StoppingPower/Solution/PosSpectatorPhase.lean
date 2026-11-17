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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPartnerMux123

@[expose] public section
set_option Elab.async false
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModPosSlots24SpectatorPrunedPhase
set_option maxRecDepth 4096
@[expose] public section
namespace PosSlots24SpectatorPrunedPhase
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open OctahedralOrbit
open Dyadic128CoulombMath
open CanonRank7Circuit
open MeasureBranchHadamardSem
  (projZeroAll ket_projZeroAll projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary)
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open StreamingBchComparator
attribute [local irreducible] lookup3xPow2Val copyXorRegCircuit
section TempPhaseMiddleKick
def ge216Bit (n3 n4 n5 n6 n7 : ZMod 2) : ZMod 2 :=
  (n7 * n6) * (1 + (1 + n5) * (1 + n4 * n3))
theorem ge216Bit_eq_decide (v : Fin 256) :
    let b := basisBits 8 v
    ge216Bit (b ⟨3, by decide⟩) (b ⟨4, by decide⟩) (b ⟨5, by decide⟩)
      (b ⟨6, by decide⟩) (b ⟨7, by decide⟩) = if 216 ≤ v.val then 1 else 0 := by
  revert v
  decide
def ge218Bit (a1b a2b a3b a4b a5b a6b a7b : ZMod 2) : ZMod 2 :=
  (a7b * a6b) * (1 + (1 + a5b) * (1 + (a4b * a3b) * (1 + (1 + a2b) * (1 + a1b))))
theorem ge218Bit_eq_decide (v : Fin 256) :
    let b := basisBits 8 v
    ge218Bit (b ⟨1, by decide⟩) (b ⟨2, by decide⟩) (b ⟨3, by decide⟩) (b ⟨4, by decide⟩)
      (b ⟨5, by decide⟩) (b ⟨6, by decide⟩) (b ⟨7, by decide⟩) =
      if 218 ≤ v.val then 1 else 0 := by
  revert v
  decide
def ge217Bit (p0 p1 p2 p3 p4 p5 p6 p7 : ZMod 2) : ZMod 2 :=
  (p7 * p6) * (1 + (1 + p5) * (1 + (p4 * p3) * (1 + (1 + p2) * (1 + p1) * (1 + p0))))
theorem ge217Bit_eq_decide (v : Fin 256) :
    let b := basisBits 8 v
    ge217Bit (b ⟨0, by decide⟩) (b ⟨1, by decide⟩) (b ⟨2, by decide⟩) (b ⟨3, by decide⟩)
      (b ⟨4, by decide⟩) (b ⟨5, by decide⟩) (b ⟨6, by decide⟩) (b ⟨7, by decide⟩) =
      if 217 ≤ v.val then 1 else 0 := by
  revert v
  decide
def tailDecision11Bit
    (b2 b1 s0 sr ih rz ge216 ge218 ge217 inR keepLt tSign : ZMod 2) : ZMod 2 :=
  let d6 := inR * keepLt * (1 + s0 * ge217) * (1 + rz + s0 + tSign)
  let d8 := (1 + sr) * (1 + ge218) * (1 + (1 + s0) * ge216) * (d6 + ih * (rz + d6))
  (1 + b2) * (s0 + (1 + b1) * (s0 + rz + d8))
theorem tailDecision11Bit_eq_bool
    (b2 b1 s0 sr ih rz ge216 ge218 ge217 inR keepLt tSign : ZMod 2) : tailDecision11Bit b2 b1
    s0 sr ih rz ge216 ge218 ge217 inR keepLt tSign = if tailDecisionBool (b2 == 1) (b1 == 1)
    (s0 == 1) (sr == 1) (ih == 1) (rz == 1) (!(ge216 == 1)) (!(ge218 == 1)) (!(ge217 == 1))
    ((inR == 1) && (keepLt == 1)) (tSign == 1) then 1 else 0 := by
  revert b2 b1 s0 sr ih rz ge216 ge218 ge217 inR keepLt tSign
  decide
def litVal (x : ZMod 2) (neg : Bool) : ZMod 2 := if neg then 1 + x else x
@[simp] theorem litVal_false (x : ZMod 2) : litVal x false = x := rfl
@[simp] theorem litVal_true (x : ZMod 2) : litVal x true = 1 + x := rfl
theorem litVal_invol (x : ZMod 2) (neg : Bool) : litVal (litVal x neg) neg = x := by
  revert x neg
  decide
theorem optX_eval {M : ℕ} (c : Wire M) (neg : Bool) (γ : BitAssignment M) (w : Wire M) :
    (if neg then CliffProg.x c else .nil).eval γ w =
      if w = c then litVal (γ c) neg else γ w := by
  rcases eq_or_ne w c with rfl | hwc
  · cases neg
    all_goals simp [CliffProg.eval, litVal, add_comm]
  · cases neg
    all_goals simp [CliffProg.eval, hwc]
def flipPair {M : ℕ} (c₁ : Wire M) (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool) : CliffProg M :=
  .seq (if neg₁ then .x c₁ else .nil) (if neg₂ then .x c₂ else .nil)
theorem flipPair_eval {M : ℕ} (c₁ : Wire M) (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool)
    (h₁₂ : c₁ ≠ c₂) (γ : BitAssignment M) (w : Wire M) : (flipPair c₁ neg₁ c₂ neg₂).eval γ w =
    if w = c₁ then litVal (γ c₁) neg₁ else if w = c₂ then litVal (γ c₂) neg₂ else γ w := by
  dsimp only [flipPair, CliffProg.eval]
  rcases eq_or_ne w c₂ with rfl | hw2
  · simp [optX_eval, h₁₂.symm]
  · simp [optX_eval, hw2]
theorem flipPair_eval_update_other {M : ℕ} (c₁ : Wire M) (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool)
    (t : Wire M) (val : ZMod 2)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (γ : BitAssignment M) :
    (flipPair c₁ neg₁ c₂ neg₂).eval (Function.update ((flipPair c₁ neg₁ c₂ neg₂).eval γ) t val) =
      Function.update γ t val := by
  funext w
  rw [flipPair_eval c₁ neg₁ c₂ neg₂ h₁₂]
  rcases eq_or_ne c₁ w with rfl | hw1
  · simp only [↓reduceIte, Function.update_of_ne h₁t,
      flipPair_eval c₁ neg₁ c₂ neg₂ h₁₂, litVal_invol]
  · rcases eq_or_ne c₂ w with rfl | hw2
    · simp only [hw1.symm, ↓reduceIte, Function.update_of_ne h₂t,
        flipPair_eval c₁ neg₁ c₂ neg₂ h₁₂, litVal_invol]
    · rcases eq_or_ne t w with rfl | hwt
      · simp only [hw1.symm, hw2.symm, ↓reduceIte, Function.update_self]
      · simp only [hw1.symm, hw2.symm, ↓reduceIte, Function.update_of_ne hwt.symm,
          flipPair_eval c₁ neg₁ c₂ neg₂ h₁₂]
def withLitAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let cFlip : CliffProg M := flipPair c₁ neg₁ c₂ neg₂
  withCliffAlloc cFlip
    (withTempBit c₁ c₂ ⟨cur, hcur⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂)
      (withCliffAlloc cFlip body))
@[simp] theorem withLitAnd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M)
    (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur)
    (hc₂ : c₂.val < cur) (body : TempPhaseProg M) :
    (withLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ body).countTempAnd = 1 +
    body.countTempAnd := by
  simp [withLitAnd]
def stepLitAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ : Wire M) (neg₂ : Bool) (β : BitAssignment M) : BitAssignment M := Function.update β
    ⟨cur, hcur⟩ (litVal (β c₁) neg₁ * litVal (β c₂) neg₂)
theorem stepLitAnd_of_ne {M cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M} {neg₁ : Bool}
    {c₂ : Wire M} {neg₂ : Bool} {β : BitAssignment M} {w : Wire M} (hw : w.val ≠ cur) :
    stepLitAnd cur hcur c₁ neg₁ c₂ neg₂ β w = β w :=
  Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)) _ _
def stepLitAndXor1 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ extra : Wire M) (neg₂ : Bool) (β : BitAssignment M) : BitAssignment M :=
  Function.update β ⟨cur, hcur⟩ (litVal (β c₁) neg₁ * litVal (β c₂ + β extra) neg₂)
theorem stepLitAndXor1_of_ne {M cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M} {neg₁ : Bool}
    {c₂ extra : Wire M} {neg₂ : Bool} {β : BitAssignment M} {w : Wire M} (hw : w.val ≠ cur) :
    stepLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂ β w = β w :=
  Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)) _ _
def stepLitAndXor2 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ e₁ e₂ : Wire M) (neg₂ : Bool) (β : BitAssignment M) : BitAssignment M :=
  Function.update β ⟨cur, hcur⟩ (litVal (β c₁) neg₁ * litVal (β c₂ + β e₁ + β e₂) neg₂)
theorem stepLitAndXor2_of_ne {M cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M} {neg₁ : Bool}
    {c₂ e₁ e₂ : Wire M} {neg₂ : Bool} {β : BitAssignment M} {w : Wire M} (hw : w.val ≠ cur) :
    stepLitAndXor2 cur hcur c₁ neg₁ c₂ e₁ e₂ neg₂ β w = β w :=
  Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)) _ _
theorem stepLitAnd_eq {M cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M} {neg₁ : Bool}
    {c₂ : Wire M} {neg₂ : Bool} {β : BitAssignment M} {w : Wire M} (hw : w.val = cur) :
    stepLitAnd cur hcur c₁ neg₁ c₂ neg₂ β w = litVal (β c₁) neg₁ * litVal (β c₂) neg₂ :=
  (Fin.ext hw : w = ⟨cur, hcur⟩) ▸ Function.update_self _ _ _
theorem eval_stepLitAnd {M cur : ℕ} {hcur : cur + 1 ≤ M}
    {c₁ : Wire M} {neg₁ : Bool} {c₂ : Wire M} {neg₂ : Bool}
    {prev next : BitAssignment M}
    (hstep : stepLitAnd cur hcur c₁ neg₁ c₂ neg₂ prev = next) :
    (∀ w : Wire M, w.val ≠ cur → next w = prev w) ∧
    (∀ w : Wire M, w.val = cur → next w = litVal (prev c₁) neg₁ * litVal (prev c₂) neg₂) :=
  ⟨fun w hw ↦ (congrFun hstep.symm w).trans (stepLitAnd_of_ne hw),
   fun w hw ↦ (congrFun hstep.symm w).trans (stepLitAnd_eq hw)⟩
theorem stepLitAndXor1_eq {M cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M} {neg₁ : Bool}
    {c₂ extra : Wire M} {neg₂ : Bool} {β : BitAssignment M} {w : Wire M} (hw : w.val = cur) :
    stepLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂ β w =
      litVal (β c₁) neg₁ * litVal (β c₂ + β extra) neg₂ :=
  (Fin.ext hw : w = ⟨cur, hcur⟩) ▸ Function.update_self _ _ _
theorem stepLitAndXor2_eq {M cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M} {neg₁ : Bool}
    {c₂ e₁ e₂ : Wire M} {neg₂ : Bool} {β : BitAssignment M} {w : Wire M} (hw : w.val = cur) :
    stepLitAndXor2 cur hcur c₁ neg₁ c₂ e₁ e₂ neg₂ β w =
      litVal (β c₁) neg₁ * litVal (β c₂ + β e₁ + β e₂) neg₂ :=
  (Fin.ext hw : w = ⟨cur, hcur⟩) ▸ Function.update_self _ _ _
theorem ScopedBlock.withLitAnd_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M)
    (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur)
    (hc₂ : c₂.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ stepLitAnd cur hcur c₁ neg₁ c₂ neg₂) leaf
    (withLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ body) := by
  let cFlip : CliffProg M := flipPair c₁ neg₁ c₂ neg₂
  have hOptS {c : Wire M} {b : Bool} {k : ℕ} (hk : c.val < k) :
      (if b then CliffProg.x c else .nil).SupportsBelow k := by
    cases b
    all_goals simp [CliffProg.SupportsBelow, hk]
  have hSuppIn : cFlip.SupportsBelow (cur + 1) :=
    ⟨hOptS (Nat.lt_succ_of_lt hc₁), hOptS (Nat.lt_succ_of_lt hc₂)⟩
  have hSuppOut : cFlip.SupportsBelow cur := ⟨hOptS hc₁, hOptS hc₂⟩
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl cFlip ((by omega : M - (M - cur) = cur).symm ▸ hSuppOut)
    (ScopedBlock.withTempBit_block (M := M) cur hcur c₁ c₂ h₁₂ hc₁ hc₂
      (ScopedBlock.withCliffAlloc_block (M := M) (rem := M - (cur + 1)) (remIn := M - (cur + 1))
        (by omega) le_rfl cFlip ((by omega : M - (M - (cur + 1)) = cur + 1).symm ▸ hSuppIn)
        hBody))
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withLitAnd]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, stepLitAnd, cFlip]
  congr 1
  have h1o : c₁ ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hc₁
  have h2o : c₂ ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hc₂
  rw [flipPair_eval_update_other c₁ neg₁ c₂ neg₂ ⟨cur, hcur⟩ _ h₁₂ h1o h2o β,
      flipPair_eval c₁ neg₁ c₂ neg₂ h₁₂, flipPair_eval c₁ neg₁ c₂ neg₂ h₁₂]
  simp only [↓reduceIte, h₁₂.symm]
def withLitAndXor1 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ extra : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₂ : extra ≠ c₂) (hc₁ : c₁.val < cur)
    (hc₂ : c₂.val < cur) (_he : extra.val < cur) (body : TempPhaseProg M) : TempPhaseProg M :=
    withCliffAlloc (.cnot extra c₂ he₂) (withLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂
    (withCliffAlloc (.cnot extra c₂ he₂) body))
@[simp] theorem withLitAndXor1_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (c₁ : Wire M) (neg₁ : Bool) (c₂ extra : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂)
    (he₂ : extra ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (he : extra.val < cur)
    (body : TempPhaseProg M) : (withLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂ h₁₂ he₂ hc₁ hc₂
    he body).countTempAnd = 1 + body.countTempAnd := by
  simp [withLitAndXor1]
theorem cnot_conj_update_cur {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₂ ex : Wire M)
    (he₂ : ex ≠ c₂) (hc₂ : c₂.val < cur) (he : ex.val < cur)
    (β : BitAssignment M) (val : ZMod 2) :
    (CliffProg.cnot ex c₂ he₂).eval
      (Function.update ((CliffProg.cnot ex c₂ he₂).eval β) ⟨cur, hcur⟩ val) =
    Function.update β ⟨cur, hcur⟩ val := by
  funext w
  rcases eq_or_ne w ⟨cur, hcur⟩ with rfl | hwo
  · simp only [CliffProg.eval, Function.update_of_ne (wire_ne_of_lt hc₂ : c₂ ≠ ⟨cur, hcur⟩).symm,
      Function.update_self]
  · rcases eq_or_ne w c₂ with rfl | hw2
    · simp only [CliffProg.eval, Function.update_self, Function.update_of_ne hwo,
        Function.update_of_ne (wire_ne_of_lt he : ex ≠ ⟨cur, hcur⟩), Function.update_of_ne he₂,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp only [CliffProg.eval, Function.update_of_ne hw2, Function.update_of_ne hwo]
theorem ScopedBlock.withLitAndXor1_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M)
    (neg₁ : Bool) (c₂ extra : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₂ : extra ≠ c₂)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (he : extra.val < cur)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) : ScopedBlock M (M - cur)
    (sBody ∘ stepLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂) leaf (withLitAndXor1 cur hcur c₁
    neg₁ c₂ extra neg₂ h₁₂ he₂ hc₁ hc₂ he body) := by
  have h1 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - (cur + 1))
    (remIn := M - (cur + 1)) (by omega) le_rfl (.cnot extra c₂ he₂) ⟨by omega, by omega⟩ hBody
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl (.cnot extra c₂ he₂) ⟨by omega, by omega⟩
    (ScopedBlock.withLitAnd_block (M := M) cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ h1)
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withLitAndXor1]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, stepLitAnd, stepLitAndXor1]
  rw [show (CliffProg.cnot extra c₂ he₂).eval β c₁ = β c₁ by
        simp [CliffProg.eval, Function.update_of_ne h₁₂],
    show (CliffProg.cnot extra c₂ he₂).eval β c₂ = β c₂ + β extra by simp [CliffProg.eval],
    cnot_conj_update_cur cur hcur c₂ extra he₂ hc₂ he β]
def withLitAndXor2 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ e₁ e₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₁₂ : e₁ ≠ c₂) (he₂₂ : e₂ ≠ c₂)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (_he₁ : e₁.val < cur) (he₂ : e₂.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M := withCliffAlloc (.cnot e₁ c₂ he₁₂)
    (withLitAndXor1 cur hcur c₁ neg₁ c₂ e₂ neg₂ h₁₂ he₂₂ hc₁ hc₂ he₂ (withCliffAlloc (.cnot e₁
    c₂ he₁₂) body))
@[simp] theorem withLitAndXor2_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (c₁ : Wire M) (neg₁ : Bool) (c₂ e₁ e₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂)
    (he₁₂ : e₁ ≠ c₂) (he₂₂ : e₂ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur)
    (he₁ : e₁.val < cur) (he₂ : e₂.val < cur) (body : TempPhaseProg M) : (withLitAndXor2 cur
    hcur c₁ neg₁ c₂ e₁ e₂ neg₂ h₁₂ he₁₂ he₂₂ hc₁ hc₂ he₁ he₂ body).countTempAnd = 1 +
    body.countTempAnd := by
  simp [withLitAndXor2]
theorem ScopedBlock.withLitAndXor2_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M)
    (neg₁ : Bool) (c₂ e₁ e₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₁₂ : e₁ ≠ c₂)
    (he₂₂ : e₂ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (he₁ : e₁.val < cur)
    (he₂ : e₂.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ stepLitAndXor2 cur hcur c₁ neg₁ c₂ e₁ e₂ neg₂) leaf
    (withLitAndXor2 cur hcur c₁ neg₁ c₂ e₁ e₂ neg₂ h₁₂ he₁₂ he₂₂ hc₁ hc₂ he₁ he₂ body) := by
  have h1 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - (cur + 1))
    (remIn := M - (cur + 1)) (by omega) le_rfl (.cnot e₁ c₂ he₁₂) ⟨by omega, by omega⟩ hBody
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl (.cnot e₁ c₂ he₁₂) ⟨by omega, by omega⟩
    (ScopedBlock.withLitAndXor1_block (M := M) cur hcur c₁ neg₁ c₂ e₂ neg₂ h₁₂ he₂₂ hc₁ hc₂ he₂ h1)
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withLitAndXor2]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, stepLitAndXor1, stepLitAndXor2]
  rw [show (CliffProg.cnot e₁ c₂ he₁₂).eval β c₁ = β c₁ by
        simp [CliffProg.eval, Function.update_of_ne h₁₂],
      show (CliffProg.cnot e₁ c₂ he₁₂).eval β c₂ = β c₂ + β e₁ by simp [CliffProg.eval],
      show (CliffProg.cnot e₁ c₂ he₁₂).eval β e₂ = β e₂ by
        simp [CliffProg.eval, Function.update_of_ne he₂₂],
    cnot_conj_update_cur cur hcur c₂ e₁ he₁₂ hc₂ he₁ β]
attribute [local irreducible] stepLitAnd stepLitAndXor1 stepLitAndXor2
theorem ScopedBlock.exists_withLitAnd {M : ℕ} {cur : ℕ} {hcur : cur + 1 ≤ M} {c₁ : Wire M}
    {neg₁ : Bool} {c₂ : Wire M} {neg₂ : Bool} {h₁₂ : c₁ ≠ c₂} {hc₁ : c₁.val < cur}
    {hc₂ : c₂.val < cur} {leaf body : TempPhaseProg M}
    {Goal : (BitAssignment M → BitAssignment M) → Prop} (h : ∃ sBody, ScopedBlock M (M - (cur
    + 1)) sBody leaf body ∧ Goal (sBody ∘ stepLitAnd cur hcur c₁ neg₁ c₂ neg₂)) : ∃ s,
    ScopedBlock M (M - cur) s leaf (withLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ body) ∧
    Goal s :=
  let ⟨_, hB, hG⟩ := h
  ⟨_, ScopedBlock.withLitAnd_block cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ hB, hG⟩
end TempPhaseMiddleKick
section MidPhaseMux2T
open MeasureBranchHadamardSem (bitSign sqrtHalf bit_cases)
theorem p2t_eval_seq_mulVec {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) :=
  MeasureBranchHadamardSem.eval_seq_mulVec c₁ c₂ ψ
theorem p2t_ket_X {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [← mbh_ket_eq_ket, MeasureBranchHadamardSem.ket_X, mbh_ket_eq_ket]
theorem p2t_ket_CNOT {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [← mbh_ket_eq_ket, MeasureBranchHadamardSem.ket_CNOT, mbh_ket_eq_ket]
theorem p2t_ket_TOFF {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) = ket
    (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [← mbh_ket_eq_ket, MeasureBranchHadamardSem.ket_TOFF, mbh_ket_eq_ket]
theorem p2t_ket_H {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      sqrtHalf • (ket (Function.update β q 0) + bitSign (β q) • ket (Function.update β q 1)) := by
  simpa only [mbh_ket_eq_ket] using MeasureBranchHadamardSem.ket_H q β
theorem p2t_ket_projector_zero {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 := by
  simpa only [mbh_ket_eq_ket] using MeasureBranchHadamardSem.ket_projector_zero q β
theorem p2t_ket_eq_single {n : ℕ} (β : BitAssignment n) :
    ket β = Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) := by
  funext y
  simp [ket, basisState]
noncomputable def p2t_ketPredProj {n : ℕ} (S : BitAssignment n → Prop) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  haveI := Classical.decPred S
  Matrix.diagonal (fun g : Fin (2 ^ n) ↦ if S (basisBits n g) then (1 : ℂ) else 0)
theorem p2t_ketPredProj_conjTranspose {n : ℕ} (S : BitAssignment n → Prop) :
    (p2t_ketPredProj S)ᴴ = p2t_ketPredProj S := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hs : S (basisBits n i)
    all_goals simp [p2t_ketPredProj, Matrix.diagonal, hs]
  · simp [p2t_ketPredProj, Matrix.conjTranspose_apply, Matrix.diagonal, hij, Ne.symm hij]
theorem p2t_ketPredProj_mul_ket {n : ℕ} (S : BitAssignment n → Prop)
    [DecidablePred S] (β : BitAssignment n) :
    (p2t_ketPredProj S).mulVec (ket β) = if S β then ket β else 0 := by
  rw [p2t_ket_eq_single β]
  ext i
  rw [p2t_ketPredProj, Matrix.mulVec_diagonal]
  by_cases hig : i = (basisBitsEquiv n).symm β
  · subst hig
    by_cases hs : S β
    all_goals simp [(basisBitsEquiv n).apply_symm_apply β, hs]
  · by_cases hs : S β
    all_goals simp [hig, hs]
theorem p2t_ketPredProj_mul_imp {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β : BitAssignment n, S₁ β → S₂ β) :
    p2t_ketPredProj S₂ * p2t_ketPredProj S₁ = p2t_ketPredProj S₁ := by
  classical
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
  by_cases h1 : S₁ β
  · rw [ite_eq_left h1, p2t_ketPredProj_mul_ket, ite_eq_left (h β h1)]
  · rw [ite_eq_right h1, Matrix.mulVec_zero]
theorem p2t_ketPredProj_mul_imp_right {n : ℕ} {S₁ S₂ : BitAssignment n → Prop}
    (h : ∀ β : BitAssignment n, S₁ β → S₂ β) :
    p2t_ketPredProj S₁ * p2t_ketPredProj S₂ = p2t_ketPredProj S₁ := by
  have hc := congrArg conjTranspose (p2t_ketPredProj_mul_imp h)
  simpa only [Matrix.conjTranspose_mul, p2t_ketPredProj_conjTranspose] using hc
theorem p2t_projZeroAll_eq_ketPredProj {n k : ℕ} (scr : Fin k → Wire n) :
    projZeroAll k scr = p2t_ketPredProj (fun β ↦ ∀ j : Fin k, β (scr j) = 0) := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [ket_projZeroAll, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
theorem p2t_basisOutcomeProjector_zero_eq_ketPredProj {n k : ℕ} (r : QRegister k n) :
    r.basisOutcomeProjector 0 = p2t_ketPredProj (fun β ↦ ∀ j : Fin k, β (r j) = 0) := by
  rw [← projZeroAll_eq_basisOutcomeProjector_zero, p2t_projZeroAll_eq_ketPredProj]
def p2t_RealizesConstCleanUnitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (d : DynamicCircuit Var n)
    (U : Unitary (2 ^ n)) : Prop := PreservesStoreConst d ∧ ∀ M : Observable (Fin (2 ^ n)), ∀ σ :
    Store Var, P * (wp d.compile (fun _ ↦ M) σ).1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P
theorem p2t_RealizesConstCleanUnitary_of_clean {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U : Unitary (2 ^ n)} (hP : Pᴴ = P)
    (hConst : PreservesStoreConst d) (hReal : RealizesCleanUnitary v P d U) :
    p2t_RealizesConstCleanUnitary P d U := by
  refine ⟨hConst, fun M σ ↦ ?_⟩
  have hc := congrArg HermitianMat.mat (hReal.2 (fun _ ↦ M) (fun _ _ ↦ rfl) σ)
  simpa [HermitianMat.conj_apply_mat, hP, wpQAssignCompat, qAssignObsMap,
    Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using hc
theorem p2t_RealizesConstCleanUnitary_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (c : Circuit n) :
    p2t_RealizesConstCleanUnitary (Var := Var) P (.circuit c) c.eval := by
  refine ⟨PreservesStoreConst.circuit c, fun M σ ↦ ?_⟩
  simp [DynamicCircuit.compile_circuit,
    wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc]
theorem p2t_RealizesConstCleanUnitary_mono_proj {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P_small P_big : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U : Unitary (2 ^ n)} (hPs : P_smallᴴ = P_small)
    (hPb : P_bigᴴ = P_big) (hsub : P_small * P_big = P_big)
    (hd : p2t_RealizesConstCleanUnitary P_small d U) : p2t_RealizesConstCleanUnitary P_big d U
    := by
  have hleft : P_big * P_small = P_big := by
    simpa [Matrix.conjTranspose_mul, hPs, hPb] using congrArg conjTranspose hsub
  refine ⟨hd.1, fun M σ ↦ ?_⟩
  have hWrap (X) : P_big * (P_small * X * P_small) * P_big = P_big * X * P_big := by
    simp only [← Matrix.mul_assoc, hleft]
    simp only [Matrix.mul_assoc, hsub]
  rw [← hWrap, hd.2 M σ, hWrap]
theorem p2t_RealizesConstCleanUnitary_congr_unitary {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP : Pᴴ = P)
    (hd : p2t_RealizesConstCleanUnitary P d U₁) (heq : U₁.1 * P = U₂.1 * P) :
    p2t_RealizesConstCleanUnitary P d U₂ := by
  have hadj : P * U₁.1ᴴ = P * U₂.1ᴴ := by
    simpa [Matrix.conjTranspose_mul, hP] using congrArg conjTranspose heq
  refine ⟨hd.1, fun M σ ↦ ?_⟩
  rw [hd.2 M σ]
  calc P * (U₁.1ᴴ * M.1.1 * U₁.1) * P
      = (P * U₁.1ᴴ) * M.1.1 * (U₁.1 * P) := by simp only [Matrix.mul_assoc]
    _ = (P * U₂.1ᴴ) * M.1.1 * (U₂.1 * P) := by rw [hadj, heq]
    _ = P * (U₂.1ᴴ * M.1.1 * U₂.1) * P := by simp only [Matrix.mul_assoc]
theorem p2t_RealizesConstCleanUnitary_seq_proj {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d₁ d₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : p2t_RealizesConstCleanUnitary P₁ d₁ U₁)
    (h₂ : p2t_RealizesConstCleanUnitary P₂ d₂ U₂) (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) :
    p2t_RealizesConstCleanUnitary P₁ (.seq d₁ d₂) (U₂ * U₁) := by
  have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP₁, hP₂, Matrix.mul_assoc] using
      congrArg conjTranspose hclean
  refine ⟨PreservesStoreConst.seq h₁.1 h₂.1, fun M σ ↦ ?_⟩
  obtain ⟨M₂, hM₂⟩ := h₂.1 M
  have hSeqWp : wp (DynamicCircuit.seq d₁ d₂).compile (fun _ ↦ M) σ =
      wp d₁.compile (fun _ ↦ M₂) σ := by
    simp only [DynamicCircuit.compile_seq, wp_qSeq, hM₂]
  have hSand (X) : P₁ * (U₁.1ᴴ * X * U₁.1) * P₁ =
      (P₁ * U₁.1ᴴ) * (P₂ * X * P₂) * (U₁.1 * P₁) :=
    (by simp only [Matrix.mul_assoc] : _ = (P₁ * U₁.1ᴴ) * X * (U₁.1 * P₁)).trans
      ((by rw [hadj, hclean] : (P₁ * U₁.1ᴴ * P₂) * X * (P₂ * (U₁.1 * P₁)) = _).symm.trans
        (by simp only [Matrix.mul_assoc]))
  rw [hSeqWp, h₁.2 M₂ σ, hSand, ← congrFun hM₂ σ, h₂.2 M σ, ← hSand]
  simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem p2t_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace {Var : Type} [Fintype Var]
    [DecidableEq Var] {n k mClean : ℕ} [NeZero (2 ^ n)] (rData : QRegister k n)
    (rClean : QRegister mClean n) (uTarget : Unitary (2 ^ k)) (d : DynamicCircuit Var n) (hd :
    p2t_RealizesConstCleanUnitary (rClean.basisOutcomeProjector 0) d (rData.embedUnitary
    uTarget)) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rClean uTarget
    d := by
  intro M
  obtain ⟨M', hWp⟩ := hd.1 M
  refine ⟨M', hWp, ?_⟩
  let σ₀ : Store Var := fun _ ↦ 0
  have hEq := hd.2 M σ₀
  rw [congrFun hWp σ₀] at hEq
  exact hEq
def p2t_DiagIndepOf {n : ℕ} (W : Wire n → Prop) (U : Unitary (2 ^ n)) : Prop := ∃ φ :
    BitAssignment n → ℂ, (∀ β : BitAssignment n, U.1.mulVec (ket β) = φ β • ket β) ∧ (∀ (β :
    BitAssignment n) (w : Wire n) (val : ZMod 2), W w → φ (Function.update β w val) = φ β)
theorem p2t_RealizesConstCleanUnitary_withConjCircuit_diag {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] {S_pre S_post : BitAssignment n → Prop}
    {cFwd cRev : Circuit n} {dBody : DynamicCircuit Var n} {U_target : Unitary (2 ^ n)}
    (hdBody : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_post) dBody U_target)
    (_hInv : cRev.eval * cFwd.eval = 1)
    (hConjU : cRev.eval * (U_target * cFwd.eval) = U_target) (hFwdS : ∀ β : BitAssignment n,
    S_pre β → ∃ β' : BitAssignment n, S_post β' ∧ cFwd.eval.1.mulVec (ket β) = ket β') :
    p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_pre)
    (.seq (.circuit cFwd) (.seq dBody (.circuit cRev))) U_target := by
  have hPreH := p2t_ketPredProj_conjTranspose S_pre
  have hPostH := p2t_ketPredProj_conjTranspose S_post
  have hAllH := p2t_ketPredProj_conjTranspose (fun _ : BitAssignment n ↦ True)
  have hClean1 : p2t_ketPredProj S_post * (cFwd.eval.1 * p2t_ketPredProj S_pre) =
      cFwd.eval.1 * p2t_ketPredProj S_pre := by
    classical
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro β
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · obtain ⟨β', hsp, hket⟩ := hFwdS β hs
      rw [ite_eq_left hs, hket, p2t_ketPredProj_mul_ket, ite_eq_left hsp]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hClean2 : p2t_ketPredProj (fun _ : BitAssignment n ↦ True) *
      (U_target.1 * p2t_ketPredProj S_post) = U_target.1 * p2t_ketPredProj S_post := by
    classical
    have hId : p2t_ketPredProj (fun _ : BitAssignment n ↦ True) = 1 := by
      ext i j
      by_cases hij : i = j
      all_goals simp [p2t_ketPredProj, Matrix.diagonal, Matrix.one_apply, hij]
    rw [hId, Matrix.one_mul]
  have hdPostRev : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_post)
      (.seq dBody (.circuit cRev)) (cRev.eval * U_target) :=
    p2t_RealizesConstCleanUnitary_seq_proj hPostH hAllH hdBody
      (p2t_RealizesConstCleanUnitary_circuit _ cRev) hClean2
  have hdAll : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_pre)
      (.seq (.circuit cFwd) (.seq dBody (.circuit cRev))) ((cRev.eval * U_target) * cFwd.eval) :=
    p2t_RealizesConstCleanUnitary_seq_proj hPreH hPostH
      (p2t_RealizesConstCleanUnitary_circuit _ cFwd) hdPostRev hClean1
  have hUnit : ((cRev.eval * U_target) * cFwd.eval).1 * p2t_ketPredProj S_pre =
      U_target.1 * p2t_ketPredProj S_pre := by
    rw [mul_assoc, hConjU]
  exact p2t_RealizesConstCleanUnitary_congr_unitary hPreH hdAll hUnit
theorem p2t_RealizesConstCleanUnitary_withTempAnd_diag {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) {W : Wire n → Prop} (hWanc : W anc)
    {S_pre S_post : BitAssignment n → Prop} {dBody : DynamicCircuit Var n}
    {U_target : Unitary (2 ^ n)} (hDiag : p2t_DiagIndepOf W U_target)
    (hAnc0 : ∀ β : BitAssignment n, S_pre β → β anc = 0) (hFwd : ∀ β : BitAssignment n, S_pre
    β → S_post (Function.update β anc (β c₁ * β c₂))) (hdBody : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj S_post) dBody U_target) : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj S_pre) (.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a) (.seq dBody
    (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))) U_target := by
  obtain ⟨φ, hφKet, hφIndep⟩ := hDiag
  let P_pre := p2t_ketPredProj S_pre
  let P_post := p2t_ketPredProj S_post
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  have hPreH : P_preᴴ = P_pre := p2t_ketPredProj_conjTranspose S_pre
  have hPostH : P_postᴴ = P_post := p2t_ketPredProj_conjTranspose S_post
  have hP₀H : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hP₀_eq : P₀ = p2t_ketPredProj (fun β ↦ β anc = 0) :=
    MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ by
      classical rw [mbh_ket_eq_ket, p2t_ket_projector_zero, p2t_ketPredProj_mul_ket]
  have hP₀_pre : P₀ * P_pre = P_pre := hP₀_eq ▸ p2t_ketPredProj_mul_imp hAnc0
  have hPre_P₀ : P_pre * P₀ = P_pre := hP₀_eq ▸ p2t_ketPredProj_mul_imp_right hAnc0
  have hPost_T_pre : P_post * (T_anc.1 * P_pre) = T_anc.1 * P_pre := by
    classical
    refine MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ ?_
    dsimp only [P_pre, P_post, T_anc]
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · rw [ite_eq_left hs, p2t_ket_TOFF, hAnc0 β hs, zero_add, p2t_ketPredProj_mul_ket,
        ite_eq_left (hFwd β hs)]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPre_Tadj_Post : P_pre * T_anc.1ᴴ * P_post = P_pre * T_anc.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPostH, hPreH, Matrix.mul_assoc] using
      congrArg conjTranspose hPost_T_pre
  have hTU_comm : U_target.1 * T_anc.1 = T_anc.1 * U_target.1 :=
    MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ by
      dsimp only [T_anc]
      rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ket_TOFF,
        hφKet, hφKet, hφIndep _ anc _ hWanc, Matrix.mulVec_smul, p2t_ket_TOFF]
  have hTU_adj_comm : T_anc.1ᴴ * U_target.1ᴴ = U_target.1ᴴ * T_anc.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg conjTranspose hTU_comm
  have hP₀_U_pre : P₀ * (U_target.1 * P_pre) = U_target.1 * P_pre := by
    classical
    refine MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ ?_
    dsimp only [P_pre, P₀]
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · rw [ite_eq_left hs, hφKet, Matrix.mulVec_smul, p2t_ket_projector_zero, ite_eq_left (hAnc0 β
        hs)]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPre_Uadj_P₀ : P_pre * U_target.1ᴴ * P₀ = P_pre * U_target.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP₀H, hPreH, Matrix.mul_assoc] using
      congrArg conjTranspose hP₀_U_pre
  refine ⟨PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (PreservesStoreConst.seq hdBody.1 (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂)),
    fun M σ ↦ ?_⟩
  let dUncomp := DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂
  obtain ⟨M_uncomp, hUncomp_wp⟩ := PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂ M
  obtain ⟨M_body, hBody_wp⟩ := hdBody.1 M_uncomp
  have hBodySeqWp : wp (.qSeq dBody.compile dUncomp.compile) (fun _ ↦ M) = fun _ ↦ M_body :=
    funext fun τ ↦ by rw [wp_qSeq, hUncomp_wp, hBody_wp]
  have hStep1 : P₀ * (wp (DynamicCircuit.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
      (DynamicCircuit.seq dBody dUncomp)).compile (fun _ ↦ M) σ).1.1 * P₀ =
      P₀ * (T_anc.1ᴴ * M_body.1.1 * T_anc.1) * P₀ := by
    have hRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
      (DynCircuitExt.restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a
        (.qSeq dBody.compile dUncomp.compile) (fun _ ↦ M)) σ))
    rw [hBodySeqWp] at hRaw
    simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
      QRegister.basisOutcomeProjector_conjTranspose, DynamicCircuit.compile_seq,
      HermitianMat.conj_apply_mat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hRaw ⊢
    exact hRaw
  have hStepUncomp : P₀ * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) * P₀ = P₀ * M.1.1 * P₀ := by
    have hRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
      (DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M) (fun _ _ ↦ rfl)) σ))
    rw [hUncomp_wp] at hRaw
    simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
      QRegister.basisOutcomeProjector_conjTranspose, HermitianMat.conj_apply_mat,
      wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hRaw ⊢
    exact hRaw
  have hBodyConj : P_post * M_body.1.1 * P_post =
      P_post * (U_target.1ᴴ * M_uncomp.1.1 * U_target.1) * P_post :=
    (congrFun hBody_wp σ).symm ▸ hdBody.2 M_uncomp σ
  have hS0 (X) : P_pre * X * P_pre = P_pre * (P₀ * X * P₀) * P_pre := by
    simp only [← Matrix.mul_assoc, hPre_P₀]
    simp only [Matrix.mul_assoc, hP₀_pre]
  have hSand {P₂ U₁ U₂} (hL : P_pre * U₁ * P₂ = P_pre * U₁)
      (hR : P₂ * (U₂ * P_pre) = U₂ * P_pre) (X) :
      P_pre * (U₁ * X * U₂) * P_pre = (P_pre * U₁) * (P₂ * X * P₂) * (U₂ * P_pre) :=
    (by simp only [Matrix.mul_assoc] : _ = (P_pre * U₁) * X * (U₂ * P_pre)).trans
      ((by rw [hL, hR] : (P_pre * U₁ * P₂) * X * (P₂ * (U₂ * P_pre)) = _).symm.trans
        (by simp only [Matrix.mul_assoc]))
  have hSwap (X) : T_anc.1ᴴ * (U_target.1ᴴ * X * U_target.1) * T_anc.1 =
      U_target.1ᴴ * (T_anc.1ᴴ * X * T_anc.1) * U_target.1 := by
    calc T_anc.1ᴴ * (U_target.1ᴴ * X * U_target.1) * T_anc.1
        = (T_anc.1ᴴ * U_target.1ᴴ) * X * (U_target.1 * T_anc.1) := by simp only [Matrix.mul_assoc]
      _ = (U_target.1ᴴ * T_anc.1ᴴ) * X * (T_anc.1 * U_target.1) := by rw [hTU_adj_comm, hTU_comm]
      _ = U_target.1ᴴ * (T_anc.1ᴴ * X * T_anc.1) * U_target.1 := by simp only [Matrix.mul_assoc]
  rw [hS0, hStep1, ← hS0, hSand hPre_Tadj_Post hPost_T_pre, hBodyConj,
    ← hSand hPre_Tadj_Post hPost_T_pre, hSwap, hSand hPre_Uadj_P₀ hP₀_U_pre,
    hStepUncomp, ← hSand hPre_Uadj_P₀ hP₀_U_pre]
noncomputable def p2t_lockVal {α : Sort _} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem p2t_lockVal_eq {α : Sort _} (x : α) : p2t_lockVal x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)
noncomputable def p2t_omega8 : ℂ := (1 + Complex.I) / (√2 : ℂ)
theorem p2t_omega8_sq : p2t_omega8 ^ 2 = Complex.I :=
  PosSlots24PartnerMuxZeroT123.omega8P_sq
theorem p2t_omega8_pow_four : p2t_omega8 ^ 4 = -1 :=
  PosSlots24PartnerMuxZeroT123.omega8P_pow_four
theorem p2t_sqrtHalf_mul_self_two : (sqrtHalf * sqrtHalf : ℂ) * 2 = 1 :=
  PosSlots24PartnerMuxZeroT123.sqrtHalf_mul_self_two
theorem p2t_ket_S {n : ℕ} (q : Wire n) (γ : BitAssignment n) : (Circuit.S q).eval.1.mulVec
    (ket γ) = (if γ q = 0 then (1 : ℂ) else Complex.I) • ket γ := by
  simpa only [mbh_ket_eq_ket] using PosSlots24PartnerMuxZeroT123.ket_S_p q γ
theorem p2t_ket_T {n : ℕ} (q : Wire n) (γ : BitAssignment n) : (Circuit.T q).eval.1.mulVec
    (ket γ) = (if γ q = 0 then (1 : ℂ) else p2t_omega8) • ket γ := by
  simpa only [mbh_ket_eq_ket, PosSlots24PartnerMuxZeroT123.fTP,
    PosSlots24PartnerMuxZeroT123.omega8P, p2t_omega8] using PosSlots24PartnerMuxZeroT123.ket_T_p q γ
theorem p2t_ket_Tinv {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.T q).inverse.eval.1.mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else -p2t_omega8 ^ 3) • ket γ := by
  simpa only [mbh_ket_eq_ket, PosSlots24PartnerMuxZeroT123.fTiP,
    PosSlots24PartnerMuxZeroT123.omega8P, p2t_omega8] using
    PosSlots24PartnerMuxZeroT123.ket_Tinv_p q γ
noncomputable def p2t_diagTPhase (b : ZMod 2) : ℂ :=
  if b = 0 then p2t_omega8 else -p2t_omega8 ^ 3
noncomputable def p2t_boundTPhase (b : ZMod 2) : ℂ :=
  if b = 0 then -p2t_omega8 ^ 3 else p2t_omega8
theorem p2t_diagTPhase_zero_mul_bound (x : ZMod 2) :
    p2t_diagTPhase (x + 0) * p2t_boundTPhase x = 1 := by
  rcases bit_cases x with rfl | rfl
  · simp only [add_zero, p2t_diagTPhase, p2t_boundTPhase, ↓reduceIte]
    linear_combination -p2t_omega8_pow_four
  · simp only [add_zero, p2t_diagTPhase, p2t_boundTPhase, one_ne_zero, ↓reduceIte]
    linear_combination -p2t_omega8_pow_four
theorem p2t_diagTPhase_one_mul_bound (x : ZMod 2) :
    p2t_diagTPhase (x + 1) * p2t_boundTPhase x = (-Complex.I) * bitSign x := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases bit_cases x with rfl | rfl
  · simp only [zero_add, p2t_diagTPhase, p2t_boundTPhase, bitSign, one_ne_zero, ↓reduceIte]
    rw [← p2t_omega8_sq]
    linear_combination (p2t_omega8 ^ 2) * p2t_omega8_pow_four
  · simp only [h11, p2t_diagTPhase, p2t_boundTPhase, bitSign, one_ne_zero, ↓reduceIte]
    rw [← p2t_omega8_sq]
    ring
def p2t_oneHotBitStep {n : ℕ} (z u y : Wire n) (huz : u ≠ z) (hyz : y ≠ z) : Circuit n :=
  Circuit.CNOT y z hyz ;;ᶜ (Circuit.T z).inverse ;;ᶜ
  Circuit.CNOT u z huz ;;ᶜ Circuit.T z ;;ᶜ
  Circuit.CNOT u z huz ;;ᶜ Circuit.CNOT y z hyz
def p2t_oneHotBoundaryFix {n : ℕ} (z uRef : Wire n) (huz : uRef ≠ z) : Circuit n :=
  Circuit.T z ;;ᶜ Circuit.X z ;;ᶜ
  Circuit.CNOT uRef z huz ;;ᶜ (Circuit.T z).inverse ;;ᶜ
  Circuit.CNOT uRef z huz ;;ᶜ Circuit.X z
theorem p2t_oneHotBitStep_count_toff {n : ℕ} (z u y : Wire n) (huz : u ≠ z) (hyz : y ≠ z) :
    (p2t_oneHotBitStep z u y huz hyz).count PrimitiveGate.TOFF = 0 := by
  simp [p2t_oneHotBitStep, Circuit.T, Circuit.CNOT, Circuit.inverse_gate,
    Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count]
theorem p2t_oneHotBitStep_count_t {n : ℕ} (z u y : Wire n) (huz : u ≠ z) (hyz : y ≠ z) :
    (p2t_oneHotBitStep z u y huz hyz).count PrimitiveGate.T = 2 := by
  simp [p2t_oneHotBitStep, Circuit.T, Circuit.CNOT, Circuit.inverse_gate,
    Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count]
theorem p2t_oneHotBoundaryFix_count_toff {n : ℕ} (z uRef : Wire n) (huz : uRef ≠ z) :
    (p2t_oneHotBoundaryFix z uRef huz).count PrimitiveGate.TOFF = 0 := by
  simp [p2t_oneHotBoundaryFix, Circuit.T, Circuit.X, Circuit.CNOT, Circuit.inverse_gate,
    Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count]
theorem p2t_oneHotBoundaryFix_count_t {n : ℕ} (z uRef : Wire n) (huz : uRef ≠ z) :
    (p2t_oneHotBoundaryFix z uRef huz).count PrimitiveGate.T = 2 := by
  simp [p2t_oneHotBoundaryFix, Circuit.T, Circuit.X, Circuit.CNOT, Circuit.inverse_gate,
    Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count]
theorem p2t_oneHotBitStep_ket {n : ℕ} (z u y : Wire n) (huz : u ≠ z) (hyz : y ≠ z)
    (γ : BitAssignment n) : (p2t_oneHotBitStep z u y huz hyz).eval.1.mulVec (ket γ) =
    (if γ u = 0 then (1 : ℂ) else p2t_diagTPhase (γ z + γ y)) • ket γ := by
  have h := PosSlots24PartnerMuxZeroT123.ket_oneHotBitStep z u y hyz huz γ
  dsimp only [p2t_oneHotBitStep, PosSlots24PartnerMuxZeroT123.oneHotBitStep] at h ⊢
  rw [mbh_ket_eq_ket] at h
  refine h.trans (congrArg₂ (· • ·) ?_ rfl)
  rcases bit_cases (γ u) with hu | hu
  · simp [hu, PosSlots24PartnerMuxZeroT123.oneHotBitPhase_zero_u]
  · dsimp only [PosSlots24PartnerMuxZeroT123.oneHotBitPhase]
    rcases bit_cases (γ z + γ y) with hzy | hzy
    · rw [hu, hzy]
      simp [PosSlots24PartnerMuxZeroT123.fTP, PosSlots24PartnerMuxZeroT123.fTiP,
        PosSlots24PartnerMuxZeroT123.omega8P, p2t_diagTPhase, p2t_omega8]
    · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      rw [hu, hzy]
      simp [h11, PosSlots24PartnerMuxZeroT123.fTP, PosSlots24PartnerMuxZeroT123.fTiP,
        PosSlots24PartnerMuxZeroT123.omega8P, p2t_diagTPhase, p2t_omega8]
theorem p2t_oneHotBoundaryFix_ket {n : ℕ} (z uRef : Wire n) (huz : uRef ≠ z)
    (γ : BitAssignment n) : (p2t_oneHotBoundaryFix z uRef huz).eval.1.mulVec (ket γ) =
    (if γ uRef = 0 then p2t_boundTPhase (γ z) else 1) • ket γ := by
  have h := PosSlots24PartnerMuxZeroT123.ket_oneHotBoundaryFix z uRef huz γ
  dsimp only [p2t_oneHotBoundaryFix, PosSlots24PartnerMuxZeroT123.oneHotBoundaryFix] at h ⊢
  rw [mbh_ket_eq_ket] at h
  refine h.trans (congrArg₂ (· • ·) ?_ rfl)
  rcases bit_cases (γ uRef) with hu | hu
  · dsimp only [PosSlots24PartnerMuxZeroT123.oneHotBoundaryPhase]
    rcases bit_cases (γ z) with hz | hz
    · rw [hu, hz]
      simp [PosSlots24PartnerMuxZeroT123.fTP, PosSlots24PartnerMuxZeroT123.fTiP,
        PosSlots24PartnerMuxZeroT123.omega8P, p2t_boundTPhase, p2t_omega8]
    · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      rw [hu, hz]
      simp [h11, PosSlots24PartnerMuxZeroT123.fTP, PosSlots24PartnerMuxZeroT123.fTiP,
        PosSlots24PartnerMuxZeroT123.omega8P, p2t_boundTPhase, p2t_omega8]
  · simp [hu, PosSlots24PartnerMuxZeroT123.oneHotBoundaryPhase_one]
def p2t_cBitStepRange {n : ℕ}
    (z : Wire n) (rOH64 rCol64 : QRegister 64 n)
    (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z)
    (start : ℕ) : (m : ℕ) → (hm : start + m ≤ 64) → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let sl : Fin 64 := ⟨start + m, by omega⟩
      p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start m (by omega) ;;ᶜ
        p2t_oneHotBitStep z (rOH64 sl) (rCol64 sl) (hOHz sl) (hColz sl)
theorem p2t_cBitStepRange_count_toff {n : ℕ}
    (z : Wire n) (rOH64 rCol64 : QRegister 64 n)
    (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z)
    (start : ℕ) :
    ∀ (m : ℕ) (hm : start + m ≤ 64),
      (p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      rw [p2t_cBitStepRange, Circuit.count_seq,
        p2t_cBitStepRange_count_toff z rOH64 rCol64 hOHz hColz start m (by omega),
        p2t_oneHotBitStep_count_toff]
theorem p2t_cBitStepRange_count_t {n : ℕ}
    (z : Wire n) (rOH64 rCol64 : QRegister 64 n)
    (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z)
    (start : ℕ) :
    ∀ (m : ℕ) (hm : start + m ≤ 64),
      (p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start m hm).count PrimitiveGate.T = 2 * m
  | 0, _ => rfl
  | m + 1, hm => by
      rw [p2t_cBitStepRange, Circuit.count_seq,
        p2t_cBitStepRange_count_t z rOH64 rCol64 hOHz hColz start m (by omega),
        p2t_oneHotBitStep_count_t]
      omega
theorem p2t_cBitStepRange_ket {n : ℕ}
    (z : Wire n) (rOH64 rCol64 : QRegister 64 n)
    (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z)
    (start : ℕ) (sel : Fin 64) (γ : BitAssignment n)
    (hOH : ∀ sl : Fin 64, γ (rOH64 sl) = if sl = sel then 1 else 0) :
    ∀ (m : ℕ) (hm : start + m ≤ 64),
      (p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start m hm).eval.1.mulVec (ket γ) =
        (if start ≤ sel.val ∧ sel.val < start + m then
           p2t_diagTPhase (γ z + γ (rCol64 sel))
         else 1) • ket γ
  | 0, _ => by
      have hnot : ¬ (start ≤ sel.val ∧ sel.val < start + 0) := by omega
      simp [p2t_cBitStepRange]
  | m + 1, hm => by
      rw [p2t_cBitStepRange, p2t_eval_seq_mulVec,
        p2t_cBitStepRange_ket z rOH64 rCol64 hOHz hColz start sel γ hOH m (by omega),
        Matrix.mulVec_smul, p2t_oneHotBitStep_ket, smul_smul, hOH ⟨start + m, by omega⟩]
      refine congrArg₂ (· • ·) ?_ rfl
      by_cases hsl : (⟨start + m, by omega⟩ : Fin 64) = sel
      · subst hsl
        have hprev : ¬ (start ≤ start + m ∧ start + m < start + m) := by omega
        have hcur : start ≤ start + m ∧ start + m < start + (m + 1) := by omega
        simp [hcur]
      · have hne : sel.val ≠ start + m := fun h ↦ hsl (Fin.ext h.symm)
        have hiff : (start ≤ sel.val ∧ sel.val < start + m) ↔
            (start ≤ sel.val ∧ sel.val < start + (m + 1)) := by omega
        simp [hsl, hiff]
def p2t_cPhaseMuxCore {n : ℕ} (start : ℕ) (hStart : start ≤ 64) (z uRef : Wire n)
    (rOH64 rCol64 : QRegister 64 n) (huz : uRef ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) : Circuit n :=
  Circuit.H z ;;ᶜ
  p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start (64 - start) (by omega) ;;ᶜ
  p2t_oneHotBoundaryFix z uRef huz ;;ᶜ
  Circuit.H z ;;ᶜ
  Circuit.S z
theorem p2t_cPhaseMuxCore_count_toff {n : ℕ} (start : ℕ) (hStart : start ≤ 64)
    (z uRef : Wire n) (rOH64 rCol64 : QRegister 64 n) (huz : uRef ≠ z)
    (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z) (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) :
    (p2t_cPhaseMuxCore start hStart z uRef rOH64 rCol64 huz hOHz hColz).count
    PrimitiveGate.TOFF = 0 := by
  simp [p2t_cPhaseMuxCore, Circuit.H, Circuit.S, Circuit.single, Circuit.count,
    p2t_cBitStepRange_count_toff, p2t_oneHotBoundaryFix_count_toff]
theorem p2t_cPhaseMuxCore_count_t {n : ℕ} (start : ℕ) (hStart : start ≤ 64) (z uRef : Wire n)
    (rOH64 rCol64 : QRegister 64 n) (huz : uRef ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) : (p2t_cPhaseMuxCore start hStart z uRef rOH64
    rCol64 huz hOHz hColz).count PrimitiveGate.T = 2 * (64 - start) + 2 := by
  simp [p2t_cPhaseMuxCore, Circuit.H, Circuit.S, Circuit.single, Circuit.count,
    p2t_cBitStepRange_count_t, p2t_oneHotBoundaryFix_count_t]
theorem p2t_cPhaseMuxCore_ket {n : ℕ} (start : ℕ) (hStart : start ≤ 64) (z uRef : Wire n)
    (rOH64 rCol64 : QRegister 64 n) (huz : uRef ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) (sel : Fin 64) (β : BitAssignment n)
    (hβz : β z = 0) (hOH : ∀ sl : Fin 64, β (rOH64 sl) = if sl = sel then 1 else 0)
    (hRef : β uRef = if sel.val < start then 1 else 0) : (p2t_cPhaseMuxCore start hStart z
    uRef rOH64 rCol64 huz hOHz hColz).eval.1.mulVec (ket β) = ket (Function.update β z (if
    sel.val < start then 0 else β (rCol64 sel))) := by
  let g0 := Function.update β z 0
  let g1 := Function.update β z 1
  have hOH0 : ∀ sl : Fin 64, g0 (rOH64 sl) = if sl = sel then 1 else 0 := fun sl ↦ by
    simpa [g0, Function.update_of_ne (hOHz sl)] using hOH sl
  have hOH1 : ∀ sl : Fin 64, g1 (rOH64 sl) = if sl = sel then 1 else 0 := fun sl ↦ by
    simpa [g1, Function.update_of_ne (hOHz sl)] using hOH sl
  have hAfterH0 : (Circuit.H z).eval.1.mulVec (sqrtHalf • (ket g0 + ket g1)) = ket g0 := by
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, p2t_ket_H, g0, g1,
      Function.update_self, Function.update_idem]
    ext idx
    simp only [bitSign, ↓reduceIte, one_ne_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β z 0) idx) * p2t_sqrtHalf_mul_self_two
  dsimp only [p2t_cPhaseMuxCore]
  simp only [p2t_eval_seq_mulVec]
  rw [p2t_ket_H z β, hβz]
  change (Circuit.S z).eval.1.mulVec ((Circuit.H z).eval.1.mulVec ((p2t_oneHotBoundaryFix z
    uRef huz).eval.1.mulVec ((p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start (64 - start)
    (by omega)).eval.1.mulVec (sqrtHalf • (ket g0 + bitSign 0 • ket g1))))) = _
  have hInner : (p2t_oneHotBoundaryFix z uRef huz).eval.1.mulVec
      ((p2t_cBitStepRange z rOH64 rCol64 hOHz hColz start (64 - start) (by omega)).eval.1.mulVec
        (sqrtHalf • (ket g0 + bitSign 0 • ket g1))) =
      sqrtHalf •
        ((((if start ≤ sel.val ∧ sel.val < 64 then p2t_diagTPhase (0 + β (rCol64 sel)) else 1) *
          (if (if sel.val < start then (1 : ZMod 2) else 0) = 0 then
            p2t_boundTPhase 0 else 1)) : ℂ) •
        ket (Function.update β z 0) +
        (((if start ≤ sel.val ∧ sel.val < 64 then p2t_diagTPhase (1 + β (rCol64 sel)) else 1) *
          (if (if sel.val < start then (1 : ZMod 2) else 0) = 0 then
            p2t_boundTPhase 1 else 1)) : ℂ) •
        ket (Function.update β z 1)) := by
    simp only [bitSign, ↓reduceIte, one_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
      p2t_cBitStepRange_ket z rOH64 rCol64 hOHz hColz start sel g0 hOH0,
      p2t_cBitStepRange_ket z rOH64 rCol64 hOHz hColz start sel g1 hOH1,
      p2t_oneHotBoundaryFix_ket, smul_smul, show start + (64 - start) = 64 by omega]
    simp only [g0, g1, Function.update_self, Function.update_of_ne (hColz sel),
      Function.update_of_ne huz, hRef]
  rw [hInner]
  dsimp only [g0, g1] at hAfterH0
  by_cases hlt : sel.val < start
  · simp only [hlt, show ¬ (start ≤ sel.val) by omega, false_and, one_ne_zero, ↓reduceIte,
      one_mul, one_smul, hAfterH0, p2t_ket_S, Function.update_self]
  · simp only [hlt, show start ≤ sel.val by omega, sel.isLt, and_self, ↓reduceIte]
    rcases bit_cases (β (rCol64 sel)) with hy | hy
    · rw [hy, p2t_diagTPhase_zero_mul_bound 0, p2t_diagTPhase_zero_mul_bound 1]
      simp only [one_smul, hAfterH0, p2t_ket_S, Function.update_self, ↓reduceIte]
    · rw [hy, p2t_diagTPhase_one_mul_bound 0, p2t_diagTPhase_one_mul_bound 1]
      have hAfterH1 : (Circuit.H z).eval.1.mulVec (sqrtHalf • (((-Complex.I) * bitSign 0) •
          ket (Function.update β z 0) + ((-Complex.I) * bitSign 1) • ket (Function.update β z 1))) =
          (-Complex.I) • ket (Function.update β z 1) := by
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, p2t_ket_H,
          Function.update_self, Function.update_idem]
        ext idx
        simp only [bitSign, ↓reduceIte, one_ne_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination
          (-Complex.I * ket (Function.update β z 1) idx) * p2t_sqrtHalf_mul_self_two
      rw [hAfterH1, Matrix.mulVec_smul, p2t_ket_S, Function.update_self, smul_smul]
      have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
        rw [show (-Complex.I) * Complex.I = -(Complex.I ^ 2) by ring, Complex.I_sq]
        ring
      simp only [one_ne_zero, ↓reduceIte, hI, one_smul]
def p2t_cXorOhPrefix {n : ℕ}
    (rOH64 : QRegister 64 n) (wParity : Wire n)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) :
    (k : ℕ) → (hk : k ≤ 64) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let sl : Fin 64 := ⟨k, by omega⟩
      p2t_cXorOhPrefix rOH64 wParity hOHP k (by omega) ;;ᶜ
        Circuit.CNOT (rOH64 sl) wParity (hOHP sl)
theorem p2t_cXorOhPrefix_count_toff {n : ℕ}
    (rOH64 : QRegister 64 n) (wParity : Wire n)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) :
    ∀ (k : ℕ) (hk : k ≤ 64),
      (p2t_cXorOhPrefix rOH64 wParity hOHP k hk).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      simp [p2t_cXorOhPrefix, Circuit.CNOT, Circuit.count,
        p2t_cXorOhPrefix_count_toff rOH64 wParity hOHP k (by omega)]
theorem p2t_cXorOhPrefix_count_t {n : ℕ}
    (rOH64 : QRegister 64 n) (wParity : Wire n)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) :
    ∀ (k : ℕ) (hk : k ≤ 64),
      (p2t_cXorOhPrefix rOH64 wParity hOHP k hk).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      simp [p2t_cXorOhPrefix, Circuit.CNOT, Circuit.count,
        p2t_cXorOhPrefix_count_t rOH64 wParity hOHP k (by omega)]
theorem p2t_cXorOhPrefix_ket {n : ℕ}
    (rOH64 : QRegister 64 n) (wParity : Wire n)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity)
    (sel : Fin 64) (γ : BitAssignment n)
    (hOH : ∀ sl : Fin 64, γ (rOH64 sl) = if sl = sel then 1 else 0) :
    ∀ (k : ℕ) (hk : k ≤ 64),
      (p2t_cXorOhPrefix rOH64 wParity hOHP k hk).eval.1.mulVec (ket γ) =
        ket (Function.update γ wParity (γ wParity + if sel.val < k then 1 else 0))
  | 0, _ => by
      simp [p2t_cXorOhPrefix, Function.update_eq_self]
  | k + 1, hk => by
      rw [p2t_cXorOhPrefix, p2t_eval_seq_mulVec,
        p2t_cXorOhPrefix_ket rOH64 wParity hOHP sel γ hOH k (by omega),
        p2t_ket_CNOT, Function.update_self,
        Function.update_of_ne (hOHP ⟨k, by omega⟩),
        Function.update_idem, hOH ⟨k, by omega⟩]
      refine congrArg ket (funext fun w ↦ ?_)
      by_cases hw : w = wParity
      · subst hw
        simp only [Function.update_self]
        by_cases hsk : (⟨k, by omega⟩ : Fin 64) = sel
        · subst hsk
          simp [Nat.lt_succ_self k]
        · have hne : sel.val ≠ k := fun h ↦ hsk (Fin.ext h.symm)
          simp [hsk, show sel.val < k ↔ sel.val < k + 1 by omega]
      · simp [Function.update_of_ne hw]
def p2t_cCenterCol64Raw {n : ℕ} (rCol64 : QRegister 64 n) :
    (m : ℕ) → (hm : m ≤ 63) → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      p2t_cCenterCol64Raw rCol64 m (by omega) ;;ᶜ
        Circuit.CNOT (rCol64 0) (rCol64 ⟨m + 1, by omega⟩)
          (rCol64.wires.injective.ne (Fin.ne_of_val_ne (Nat.zero_ne_add_one m)))
theorem p2t_cCenterCol64Raw_count_toff {n : ℕ} (rCol64 : QRegister 64 n) :
    ∀ (m : ℕ) (hm : m ≤ 63),
      (p2t_cCenterCol64Raw rCol64 m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [p2t_cCenterCol64Raw, Circuit.CNOT, Circuit.count,
        p2t_cCenterCol64Raw_count_toff rCol64 m (by omega)]
theorem p2t_cCenterCol64Raw_count_t {n : ℕ} (rCol64 : QRegister 64 n) :
    ∀ (m : ℕ) (hm : m ≤ 63),
      (p2t_cCenterCol64Raw rCol64 m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [p2t_cCenterCol64Raw, Circuit.CNOT, Circuit.count,
        p2t_cCenterCol64Raw_count_t rCol64 m (by omega)]
noncomputable def p2t_centerAssign {n : ℕ} (rCol64 : QRegister 64 n) (m : ℕ)
    (γ : BitAssignment n) : BitAssignment n := writeReg γ rCol64 (fun sl ↦ if 1 ≤ sl.val ∧
    sl.val ≤ m then γ (rCol64 sl) + γ (rCol64 0) else γ (rCol64 sl))
theorem p2t_cCenterCol64Raw_ket {n : ℕ} (rCol64 : QRegister 64 n) (γ : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 63),
      (p2t_cCenterCol64Raw rCol64 m hm).eval.1.mulVec (ket γ) =
        ket (p2t_centerAssign rCol64 m γ)
  | 0, _ => by
      simp only [p2t_cCenterCol64Raw, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      refine congrArg ket (funext fun w ↦ ?_)
      by_cases hw : w ∈ Set.range rCol64.wires
      · obtain ⟨sl, rfl⟩ := hw
        rw [p2t_centerAssign, writeReg_apply_reg, ite_eq_right (by omega)]
      · exact (writeReg_apply_of_not_mem γ rCol64 _ w hw).symm
  | m + 1, hm => by
      rw [p2t_cCenterCol64Raw, p2t_eval_seq_mulVec,
        p2t_cCenterCol64Raw_ket rCol64 γ m (by omega), p2t_ket_CNOT]
      refine congrArg ket (funext fun w ↦ ?_)
      let slM : Fin 64 := ⟨m + 1, by omega⟩
      by_cases hw : w ∈ Set.range rCol64.wires
      · obtain ⟨sl, rfl⟩ := hw
        by_cases hsl : sl = slM
        · subst hsl
          simp [p2t_centerAssign, slM, writeReg_apply_reg,
            show 1 ≤ m + 1 by omega, show ¬ (m + 1 ≤ m) by omega]
        · rw [Function.update_of_ne (rCol64.wires.injective.ne hsl)]
          have hne : sl.val ≠ m + 1 := fun h ↦ hsl (Fin.ext h)
          simp only [p2t_centerAssign, writeReg_apply_reg,
            show (1 ≤ sl.val ∧ sl.val ≤ m) ↔ (1 ≤ sl.val ∧ sl.val ≤ m + 1) by omega]
      · rw [Function.update_of_ne (fun h ↦ hw ⟨slM, h.symm⟩)]
        simp [p2t_centerAssign, writeReg_apply_of_not_mem _ rCol64 _ w hw]
def p2t_phaseMuxColT (hb : ℕ) : ℕ :=
  if 64 ≤ hb then 0 else if 2 ≤ hb then 2 * (65 - hb) else 128
def p2t_cPhaseMuxCol64 {n : ℕ} (hb : ℕ) (z wParity : Wire n) (rOH64 rCol64 : QRegister 64 n)
    (hpz : wParity ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) :
    Circuit n :=
  if h64 : 64 ≤ hb then
    .identity
  else if h2 : 2 ≤ hb then
    p2t_cXorOhPrefix rOH64 wParity hOHP hb (by omega) ;;ᶜ
    p2t_cPhaseMuxCore hb (by omega) z wParity rOH64 rCol64 hpz hOHz hColz ;;ᶜ
    p2t_cXorOhPrefix rOH64 wParity hOHP hb (by omega)
  else
    let cCent := p2t_cCenterCol64Raw rCol64 63 (le_refl 63)
    cCent ;;ᶜ
    p2t_cPhaseMuxCore 1 (by decide) z (rOH64 0) rOH64 rCol64
      (hOHz 0) hOHz hColz ;;ᶜ
    cCent ;;ᶜ
    Circuit.CNOT (rCol64 0) z (hColz 0)
theorem p2t_cPhaseMuxCol64_count_toff {n : ℕ} (hb : ℕ) (z wParity : Wire n)
    (rOH64 rCol64 : QRegister 64 n) (hpz : wParity ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) :
    (p2t_cPhaseMuxCol64 hb z wParity rOH64 rCol64 hpz hOHz hColz hOHP).count
    PrimitiveGate.TOFF = 0 := by
  dsimp only [p2t_cPhaseMuxCol64]
  split_ifs with h64 h2
  · rfl
  · simp [Circuit.count_seq, p2t_cXorOhPrefix_count_toff, p2t_cPhaseMuxCore_count_toff]
  · simp [p2t_cCenterCol64Raw_count_toff, p2t_cPhaseMuxCore_count_toff,
      Circuit.count]
theorem p2t_cPhaseMuxCol64_count_t {n : ℕ} (hb : ℕ) (z wParity : Wire n)
    (rOH64 rCol64 : QRegister 64 n) (hpz : wParity ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) :
    (p2t_cPhaseMuxCol64 hb z wParity rOH64 rCol64 hpz hOHz hColz hOHP).count PrimitiveGate.T =
    p2t_phaseMuxColT hb := by
  dsimp only [p2t_cPhaseMuxCol64, p2t_phaseMuxColT]
  split_ifs with h64 h2
  · rfl
  · simp only [Circuit.count_seq, p2t_cXorOhPrefix_count_t, p2t_cPhaseMuxCore_count_t]
    omega
  · simp [p2t_cCenterCol64Raw_count_t, p2t_cPhaseMuxCore_count_t,
      Circuit.count]
theorem p2t_cPhaseMuxCol64_ket {n : ℕ} (hb : ℕ) (z wParity : Wire n)
    (rOH64 rCol64 : QRegister 64 n) (hpz : wParity ≠ z) (hOHz : ∀ sl : Fin 64, rOH64 sl ≠ z)
    (hColz : ∀ sl : Fin 64, rCol64 sl ≠ z) (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity)
    (hColP : ∀ sl : Fin 64, rCol64 sl ≠ wParity) (hOHCol : rOH64.DisjointWires rCol64)
    (sel : Fin 64) (β : BitAssignment n) (hβz : β z = 0) (hβP : β wParity = 0)
    (hOH : ∀ sl : Fin 64, β (rOH64 sl) = if sl = sel then 1 else 0)
    (hClean : ∀ sl : Fin 64, sl.val < hb → β (rCol64 sl) = 0) : (p2t_cPhaseMuxCol64 hb z
    wParity rOH64 rCol64 hpz hOHz hColz hOHP).eval.1.mulVec (ket β) = ket
    (Function.update β z (β (rCol64 sel))) := by
  dsimp only [p2t_cPhaseMuxCol64]
  by_cases h64 : 64 ≤ hb
  · simp only [h64, ↓reduceDIte, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    rw [hClean sel (Nat.lt_of_lt_of_le sel.isLt h64), ← hβz, Function.update_eq_self]
  · simp only [h64, ↓reduceDIte]
    by_cases h2 : 2 ≤ hb
    · simp only [h2, ↓reduceDIte, p2t_eval_seq_mulVec]
      rw [p2t_cXorOhPrefix_ket rOH64 wParity hOHP sel β hOH hb (by omega), hβP, zero_add]
      let β₁ := Function.update β wParity (if sel.val < hb then 1 else 0)
      have hβ₁OH : ∀ sl : Fin 64, β₁ (rOH64 sl) = if sl = sel then 1 else 0 :=
        fun sl ↦ (Function.update_of_ne (hOHP sl) _ _).trans (hOH sl)
      rw [p2t_cPhaseMuxCore_ket hb (by omega) z wParity rOH64 rCol64 hpz hOHz hColz sel β₁
            ((Function.update_of_ne hpz.symm _ _).trans hβz) hβ₁OH (Function.update_self _ _ _),
          show (if sel.val < hb then 0 else β₁ (rCol64 sel)) = β (rCol64 sel) by
            by_cases hlt : sel.val < hb
            · simp [hlt, hClean sel hlt]
            · simp [β₁, hlt, Function.update_of_ne (hColP sel)]]
      let β₂ := Function.update β₁ z (β (rCol64 sel))
      rw [p2t_cXorOhPrefix_ket rOH64 wParity hOHP sel β₂
            (fun sl ↦ (Function.update_of_ne (hOHz sl) _ _).trans (hβ₁OH sl)) hb (by omega)]
      refine congrArg ket (funext fun w ↦ ?_)
      rcases eq_or_ne w wParity with rfl | hwP
      · simp [β₂, β₁, Function.update_of_ne hpz, CharTwo.add_self_eq_zero, hβP]
      · rcases eq_or_ne w z with rfl | hwz
        · simp [β₂, hwP]
        · simp [β₂, β₁, hwP, hwz]
    · simp only [h2, ↓reduceDIte, p2t_eval_seq_mulVec]
      rw [p2t_cCenterCol64Raw_ket rCol64 β 63 (le_refl 63)]
      let β₁ := p2t_centerAssign rCol64 63 β
      have hzNotCol : z ∉ Set.range rCol64.wires := fun ⟨sl, hsl⟩ ↦ hColz sl hsl
      have hβ₁OH : ∀ sl : Fin 64, β₁ (rOH64 sl) = if sl = sel then 1 else 0 := fun sl ↦
        (writeReg_apply_of_not_mem β rCol64 _ _ (fun ⟨_, hs₂⟩ ↦ hOHCol.ne sl _ hs₂.symm)).trans
          (hOH sl)
      have hβ₁Ref : β₁ (rOH64 0) = if sel.val < 1 then 1 else 0 := by
        rw [hβ₁OH 0]
        rcases eq_or_ne (0 : Fin 64) sel with rfl | hs0
        · rfl
        · have hne : sel.val ≠ 0 := fun h ↦ hs0 (Fin.ext h.symm)
          simp [hs0, show ¬ sel.val < 1 by omega]
      rw [p2t_cPhaseMuxCore_ket 1 (by decide) z (rOH64 0) rOH64 rCol64 (hOHz 0) hOHz hColz sel β₁
            ((writeReg_apply_of_not_mem β rCol64 _ z hzNotCol).trans hβz) hβ₁OH hβ₁Ref,
          show (if sel.val < 1 then 0 else β₁ (rCol64 sel)) = β (rCol64 sel) + β (rCol64 0) by
            by_cases hs0 : sel.val < 1
            · rw [show sel = (0 : Fin 64) from Fin.ext (Nat.lt_one_iff.mp hs0)]
              exact (CharTwo.add_self_eq_zero (β (rCol64 0))).symm
            · simp [hs0, β₁, p2t_centerAssign, writeReg_apply_reg,
                show 1 ≤ sel.val ∧ sel.val ≤ 63 from
                  ⟨Nat.not_lt.mp hs0, Nat.le_of_lt_succ sel.isLt⟩],
          p2t_cCenterCol64Raw_ket, p2t_ket_CNOT]
      let β₂ := Function.update β₁ z (β (rCol64 sel) + β (rCol64 0))
      let β₃ := p2t_centerAssign rCol64 63 β₂
      change ket (Function.update β₃ z (β₃ z + β₃ (rCol64 0))) = _
      have hβ₂Col : ∀ sl : Fin 64, β₂ (rCol64 sl) = β₁ (rCol64 sl) :=
        fun sl ↦ Function.update_of_ne (hColz sl) _ _
      have hβ₁0 : β₁ (rCol64 0) = β (rCol64 0) := by simp [β₁, p2t_centerAssign, writeReg_apply_reg]
      have hβ₃z : β₃ z = β (rCol64 sel) + β (rCol64 0) :=
        (writeReg_apply_of_not_mem β₂ rCol64 _ z hzNotCol).trans (Function.update_self _ _ _)
      have hβ₃0 : β₃ (rCol64 0) = β (rCol64 0) := by
        simp [β₃, p2t_centerAssign, writeReg_apply_reg, hβ₂Col 0, hβ₁0]
      refine congrArg ket (funext fun w ↦ ?_)
      by_cases hwz : w = z
      · subst hwz
        rw [Function.update_self, Function.update_self, hβ₃z, hβ₃0,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · rw [Function.update_of_ne hwz, Function.update_of_ne hwz]
        by_cases hwC : w ∈ Set.range rCol64.wires
        · obtain ⟨sl, rfl⟩ := hwC
          dsimp only [β₃, p2t_centerAssign]
          rw [writeReg_apply_reg, hβ₂Col sl, hβ₂Col 0, hβ₁0]
          dsimp only [β₁, p2t_centerAssign]
          rw [writeReg_apply_reg]
          by_cases hcond : 1 ≤ sl.val ∧ sl.val ≤ 63
          · simp only [hcond, and_self, ↓reduceIte, add_assoc, CharTwo.add_self_eq_zero, add_zero]
          · simp only [hcond, ↓reduceIte]
        · exact (writeReg_apply_of_not_mem β₂ rCol64 _ w hwC).trans
            ((Function.update_of_ne hwz _ _).trans (writeReg_apply_of_not_mem β rCol64 _ w hwC))
theorem p2t_slice_disjoint {m n o₁ w₁ o₂ w₂ : ℕ} (r : QRegister m n) (h₁ : o₁ + w₁ ≤ m)
    (h₂ : o₂ + w₂ ≤ m) (hd : o₁ + w₁ ≤ o₂ ∨ o₂ + w₂ ≤ o₁) : (r.slice o₁ w₁ h₁).DisjointWires
    (r.slice o₂ w₂ h₂) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  rw [QRegister.slice_apply, QRegister.slice_apply] at heq
  have hv := congrArg Fin.val (r.wires.injective heq)
  dsimp at hv
  omega
def p2t_czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.H b ;;ᶜ Circuit.CNOT a b h ;;ᶜ Circuit.H b
theorem p2t_czCircuit_count_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (p2t_czCircuit a b h).count PrimitiveGate.TOFF = 0 := by
  simp [p2t_czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]
theorem p2t_czCircuit_count_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (p2t_czCircuit a b h).count PrimitiveGate.T = 0 := by
  simp [p2t_czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]
theorem p2t_ket_czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (p2t_czCircuit a b h).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β a * β b).val) • ket β := by
  simpa only [p2t_czCircuit, PosSlots24PartnerMuxZeroT123.czCircuit, mbh_ket_eq_ket] using
    PosSlots24PartnerMuxZeroT123.ket_czCircuit a b h β
theorem p2t_extractIndex_congr {q n : ℕ} (r : QRegister q n) (g₁ g₂ : Fin (2 ^ n))
    (h : ∀ idx : Fin q, basisBits n g₁ (r idx) = basisBits n g₂ (r idx)) :
    r.extractIndex g₁ = r.extractIndex g₂ := by
  apply (basisBitsEquiv q).injective
  funext idx
  change basisBits q (r.extractIndex g₁) idx = basisBits q (r.extractIndex g₂) idx
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact h idx
theorem p2t_concat_ne {q₁ q₂ k n : ℕ} (r₁ : QRegister q₁ n) (r₂ : QRegister q₂ n)
    (r₃ : QRegister k n) (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃)
    (h₂₃ : r₂.DisjointWires r₃) :
    ∀ (idx : Fin (q₁ + q₂)) (sl : Fin k), (r₁.concat r₂ h₁₂) idx ≠ r₃ sl := fun idx sl ↦
  Fin.addCases (fun c ↦ (QRegister.concat_apply_left r₁ r₂ h₁₂ c).symm ▸ h₁₃.ne c sl)
    (fun o ↦ (QRegister.concat_apply_right r₁ r₂ h₁₂ o).symm ▸ h₂₃.ne o sl) idx
theorem p2t_embed_diagSign_diagIndep {q k n : ℕ} [NeZero (2 ^ n)] (rData : QRegister q n)
    (rOH : QRegister k n) (hne : ∀ (idx : Fin q) (sl : Fin k), rData idx ≠ rOH sl)
    (f : Fin (2 ^ q) → Bool) : p2t_DiagIndepOf (fun w ↦ w ∈ Set.range rOH.wires)
    (rData.embedUnitary (diagSignUnitary f)) := by
  refine ⟨fun β ↦ if f (rData.extractIndex ((basisBitsEquiv n).symm β)) then (-1 : ℂ) else 1,
    fun β ↦ by rw [p2t_ket_eq_single β, embedUnitary_diagSignUnitary_mulVec_single],
    fun β w val hw ↦ ?_⟩
  rcases hw with ⟨sl, rfl⟩
  dsimp only
  rw [p2t_extractIndex_congr rData _ ((basisBitsEquiv n).symm β) fun idx ↦ by
    rw [(basisBitsEquiv n).apply_symm_apply, (basisBitsEquiv n).apply_symm_apply]
    exact Function.update_of_ne (hne idx sl) _ _]
end MidPhaseMux2T
set_option maxRecDepth 512
end PosSlots24SpectatorPrunedPhase
end
end ModPosSlots24SpectatorPrunedPhase

end QuantumComputation.Specs.StoppingPowerSolution
