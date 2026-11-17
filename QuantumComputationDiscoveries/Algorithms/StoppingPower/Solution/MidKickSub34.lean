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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.K6SweepAndLoad273


@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section MidKickSub33
local instance (priority := 1000000) instNeZeroTwoPow_MidKickSub33 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `34`-Wire Clean Mid-Kick Subroutine (`MidKickSub33`)

Self-contained `34`-wire clean-ancilla `196 + 4 * B` `T` (`0` `.TOFF`) 3-stage mid-phase
kickback oracle `dKickZeroSub34Dyn` and `B`-bit midpoint magnitude table
`pos24TailMag30MidpointB` (`1 ≤ B ≤ 27`, midpoint bounds up to `B ≤ 29`):
- Stage A (`mk34_dComp3`, `23` `TempAnd`s = `92 T` on `rScr34[3..26)`): conjugates three
  `0-T` `CZ` gates by `hadamardReg (rScr34.slice 0 3)` to XOR `(u1, vL, d3)` onto `rHold3`
  while restoring `rSub31 := rScr34.slice 3 31` to `|0⟩^31`.
- Stage B (`mk34_dMidKickB`, `B + 3` `TempAnd`s = `4 * B + 12 T` on `rScr31[0..B+4)`):
  initializes `prev0 = 1 + keep[29 - B]` (`keep[0..30-B) < 2^(29-B)`), runs the `B`-bit
  comparator `keep[30-B..30) < rOutTop[0..B)`, computes `(d5, d6, d7)` in `3` `TempAnd`s,
  and applies the `0-T` diagonal phase kick `midKickPhaseBitB`.
- Stage C (`mk34_dComp3`, `23` `TempAnd`s = `92 T`): uncomputes `rHold3` back to `|0⟩^3`
  with `+1` phase, yielding `RealizesCleanUnitary` on `projZeroAll 34 rScr34.wires`.
-/

public section

namespace MidKickSub33

section ConfigMidKickSub33

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit
open Dyadic128CoulombMath (orbitCount47905)
open MeasureBranchHadamardSem
  (projZeroAll ket_projZeroAll projZeroAll_conjTranspose RealizesCleanUnitary)
open StreamingBchComparator
open PosSlots24BranchConcrete
open PosSlots24SemanticBridge
open PosSlots24SpectatorPrunedPhase
open PrunedQromLookup

/- ## Section 1: `B`-Bit Midpoint Magnitude Table & `midKickPhaseBitB` Specification -/

theorem mk34_bitsVal_congr_len {M N : ℕ} (hMN : M = N) (f : Fin M → ZMod 2) (g : Fin N → ZMod 2)
    (h : ∀ i : Fin M, f i = g ⟨i.val, hMN ▸ i.isLt⟩) : bitsVal f = bitsVal g := by
  subst hMN
  exact congrArg bitsVal (funext h)

theorem mk34_bitsVal_split_le {M : ℕ} (K : ℕ) (hK : K ≤ M) (f : Fin M → ZMod 2) :
    bitsVal f = bitsVal (fun i : Fin K ↦ f ⟨i.val, by omega⟩) +
      2 ^ K * bitsVal (fun j : Fin (M - K) ↦ f ⟨K + j.val, by omega⟩) := by
  rw [mk34_bitsVal_congr_len (by omega : M = K + (M - K)) f (fun x ↦ f ⟨x.val, by omega⟩) fun _ ↦
    rfl]
  simp only [bitsVal, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [pow_add]
  ring
/-- `B`-bit midpoint approximation to `pos24TailMag30`, formed from its top `B` bits plus `2 ^
  (29 - B)`. -/
noncomputable def pos24TailMag30MidpointB (B : ℕ) (_hB1 : 1 ≤ B) (hB29 : B ≤ 29)
    (rOrbit : Fin orbitCount47905) : Fin (2 ^ 30) :=
  ⟨((pos24TailMag30 rOrbit).val / 2 ^ (30 - B)) * 2 ^ (30 - B) + 2 ^ (29 - B), by
    have hm := (pos24TailMag30 rOrbit).isLt
    have hpow30 : 2 ^ B * 2 ^ (30 - B) = 2 ^ 30 :=
      (pow_add 2 B (30 - B)).symm.trans (congrArg (2 ^ ·) (by omega))
    have hq_lt : (pos24TailMag30 rOrbit).val / 2 ^ (30 - B) < 2 ^ B := by
      by_contra hge
      have hle := Nat.mul_le_mul_right (2 ^ (30 - B)) (Nat.le_of_not_lt hge)
      have hdm := Nat.div_mul_le_self (pos24TailMag30 rOrbit).val (2 ^ (30 - B))
      omega
    have hq_succ : ((pos24TailMag30 rOrbit).val / 2 ^ (30 - B) + 1) * 2 ^ (30 - B) ≤ 2 ^ 30 :=
      (Nat.mul_le_mul_right (2 ^ (30 - B)) hq_lt).trans_eq hpow30
    have hhalf : 2 ^ (29 - B) < 2 ^ (30 - B) := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [Nat.add_one_mul] at hq_succ
    omega⟩

@[scoped simp] theorem pos24TailMag30MidpointB_val (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤ 29)
    (rOrbit : Fin orbitCount47905) : (pos24TailMag30MidpointB B hB1 hB29 rOrbit).val =
    ((pos24TailMag30 rOrbit).val / 2 ^ (30 - B)) * 2 ^ (30 - B) + 2 ^ (29 - B) := rfl

theorem pos24TailMag30MidpointB_bounds (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤
    29) (rOrbit : Fin orbitCount47905) :
    (pos24TailMag30 rOrbit).val ≤ (pos24TailMag30MidpointB B hB1 hB29 rOrbit).val + 2 ^ (29 - B) ∧
    (pos24TailMag30MidpointB B hB1 hB29 rOrbit).val ≤ (pos24TailMag30 rOrbit).val + 2 ^ (29 - B) :=
      by
  have hdiv := Nat.div_add_mod (pos24TailMag30 rOrbit).val (2 ^ (30 - B))
  have hmod := Nat.mod_lt (pos24TailMag30 rOrbit).val (Nat.two_pow_pos (30 - B))
  have h2 : 2 ^ (30 - B) = 2 * 2 ^ (29 - B) := by
    have he : 30 - B = (29 - B) + 1 := by omega
    rw [he, pow_succ']
  rw [pos24TailMag30MidpointB_val]
  rw [Nat.mul_comm] at hdiv
  omega

theorem pos24TailMag30MidpointB_eq_topBits (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤
    29) (rOrbit : Fin orbitCount47905) (outTop
    : Fin B → ZMod 2) (hout : ∀ j : Fin B,
      outTop j = basisBits 30 (pos24TailMag30 rOrbit) ⟨(30 - B) + j.val, by omega⟩)
    : 2 ^ (29 - B) + 2 ^ (30 - B) * bitsVal outTop =
      (pos24TailMag30MidpointB B hB1 hB29 rOrbit).val := by
  have hm := (bitsVal_basisBits (pos24TailMag30 rOrbit)).symm
  have hsplit := mk34_bitsVal_split_le (30 - B) (by omega) (basisBits 30 (pos24TailMag30 rOrbit))
  let lo := bitsVal (fun i : Fin (30 - B) ↦ basisBits 30 (pos24TailMag30 rOrbit) ⟨i.val, by omega⟩)
  have hlo : lo < 2 ^ (30 - B) := bitsVal_lt_two_pow _
  have htopEq : bitsVal (fun j : Fin (30 - (30 - B)) ↦
      basisBits 30 (pos24TailMag30 rOrbit) ⟨(30 - B) + j.val, by omega⟩) = bitsVal outTop :=
    mk34_bitsVal_congr_len (by omega) _ outTop fun j ↦ (hout ⟨j.val, by omega⟩).symm
  have hmEq : (pos24TailMag30 rOrbit).val = lo + bitsVal outTop * 2 ^ (30 - B) := by
    rw [hm, hsplit, htopEq, Nat.mul_comm]
  have hdiv : (pos24TailMag30 rOrbit).val / 2 ^ (30 - B) = bitsVal outTop := by
    rw [hmEq, Nat.add_mul_div_right lo (bitsVal outTop) (Nat.two_pow_pos (30 - B)),
      Nat.div_eq_zero_iff.mpr (.inr hlo), zero_add]
  rw [pos24TailMag30MidpointB_val, hdiv]
  ring

/-- Exact mid-phase kickback bit on `rCore` and `(B + 1)`-wire top QROM slice `rOutTop`. -/
def midKickPhaseBitB {n : ℕ} (B : ℕ) (rCore : QRegister posCoreWires n)
    (rOutTop : QRegister (B + 1) n) (δ : BitAssignment n) : ZMod 2 :=
  tailDecision11Bit
    (δ (rCore ⟨3950, by decide⟩)) (δ (rCore ⟨3949, by decide⟩)) (δ (rCore ⟨3948, by decide⟩))
    (δ (rCore ⟨4016, by decide⟩)) (δ (rCore ⟨3984, by decide⟩)) (δ (rCore ⟨4033, by decide⟩))
    (ge216Bit (δ (rCore ⟨3963, by decide⟩)) (δ (rCore ⟨3964, by decide⟩))
      (δ (rCore ⟨3965, by decide⟩)) (δ (rCore ⟨3966, by decide⟩)) (δ (rCore ⟨3967, by decide⟩)))
    (ge218Bit (δ (rCore ⟨3969, by decide⟩)) (δ (rCore ⟨3970, by decide⟩))
      (δ (rCore ⟨3971, by decide⟩)) (δ (rCore ⟨3972, by decide⟩)) (δ (rCore ⟨3973, by decide⟩))
      (δ (rCore ⟨3974, by decide⟩)) (δ (rCore ⟨3975, by decide⟩)))
    (ge217Bit (δ (rCore ⟨3976, by decide⟩)) (δ (rCore ⟨3977, by decide⟩))
      (δ (rCore ⟨3978, by decide⟩)) (δ (rCore ⟨3979, by decide⟩)) (δ (rCore ⟨3980, by decide⟩))
      (δ (rCore ⟨3981, by decide⟩)) (δ (rCore ⟨3982, by decide⟩)) (δ (rCore ⟨3983, by decide⟩)))
    1
    (if bitsVal (fun k : Fin 30 ↦ δ (rCore ⟨3986 + k.val, by dsimp [posCoreWires]; omega⟩)) <
        2 ^ (29 - B) + 2 ^ (30 - B) * bitsVal (fun j : Fin B ↦ δ (rOutTop ⟨j.val, by omega⟩))
     then 1 else 0)
    (δ (rOutTop ⟨B, by omega⟩))

/- ## Section 2: `TempCtx` Compilation & Clean-Workspace Unitary Helpers -/

theorem mk34_ket_Z {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β q).val) • ket β := by
  rw [← mbh_ket_eq_ket, MeasureBranchHadamardSem.ket_Z, mbh_ket_eq_ket,
    TempPhaseProg.bitSign_eq_neg_one_pow]

@[scoped simp] theorem mk34_append_countTempAnd {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd := by
  induction F with
  | hole => simp [TempCtx.append, TempCtx.countTempAnd]
  | seqPre _ _ ih => simp [TempCtx.append, TempCtx.countTempAnd, ih]
  | seqPost _ _ ih => simp [TempCtx.append, TempCtx.countTempAnd, ih]
  | tempAnd _ _ _ _ _ _ _ ih =>
      simp only [TempCtx.append, TempCtx.countTempAnd, ih]
      omega

@[scoped simp] theorem mk34_ctxCliffAlloc_countTempAnd {M : ℕ} (c : CliffProg M) :
    (ctxCliffAlloc c).countTempAnd = 0 := rfl

@[scoped simp] theorem mk34_ctxLitAnd_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (c₁ : Wire M) (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (body : TempPhaseProg M) :
    (ctxLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂).plug body = withLitAnd cur hcur c₁ neg₁
    c₂ neg₂ h₁₂ hc₁ hc₂ body := ctxLitAnd_plug cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ body

@[scoped simp] theorem mk34_ctxLitAnd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val <
      cur) : (ctxLitAnd cur hcur c₁ neg₁
    c₂ neg₂ h₁₂ hc₁ hc₂).countTempAnd = 1 := by simp [ctxLitAnd, ctxTempBit, TempCtx.countTempAnd]

/-- `TempCtx` wrapper for `withLitAndXor1` (`1` `TempAnd`). -/
def mk34_ctxLitAndXor1 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ extra : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₂ : extra ≠ c₂) (hc₁ : c₁.val < cur)
    (hc₂ : c₂.val < cur) (_he : extra.val < cur) : TempCtx M :=
    (ctxCliffAlloc (.cnot extra c₂ he₂)).append ((ctxLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁
    hc₂).append (ctxCliffAlloc (.cnot extra c₂ he₂)))

@[scoped simp] theorem mk34_ctxLitAndXor1_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (c₁ : Wire M) (neg₁ : Bool) (c₂
    extra : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₂ : extra ≠ c₂) (hc₁ : c₁.val <
      cur) (hc₂ : c₂.val < cur) (he :
    extra.val <
      cur) (body : TempPhaseProg M) :
      (mk34_ctxLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂ h₁₂ he₂ hc₁ hc₂
    he).plug body = withLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂ h₁₂ he₂ hc₁ hc₂ he body := by
  simp only [mk34_ctxLitAndXor1, TempCtx.append_plug, ctxCliffAlloc_plug, mk34_ctxLitAnd_plug,
    withLitAndXor1]

@[scoped simp] theorem mk34_ctxLitAndXor1_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (c₁ : Wire M) (neg₁ :
    Bool) (c₂ extra : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₂ : extra ≠ c₂) (hc₁ : c₁.val <
      cur) (hc₂ : c₂.val < cur)
    (he : extra.val <
      cur) : (mk34_ctxLitAndXor1 cur hcur c₁ neg₁ c₂ extra neg₂ h₁₂ he₂ hc₁ hc₂ he).countTempAnd =
      1 :=
    by
  simp [mk34_ctxLitAndXor1]

/-- `TempCtx` wrapper for `withLitAndXor2` (`1` `TempAnd`). -/
def mk34_ctxLitAndXor2 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ e₁ e₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₁₂ : e₁ ≠ c₂) (he₂₂ : e₂ ≠ c₂)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (_he₁ : e₁.val < cur) (he₂ : e₂.val < cur) :
    TempCtx M := (ctxCliffAlloc (.cnot e₁ c₂ he₁₂)).append ((mk34_ctxLitAndXor1 cur hcur c₁
    neg₁ c₂ e₂ neg₂ h₁₂ he₂₂ hc₁ hc₂ he₂).append (ctxCliffAlloc (.cnot e₁ c₂ he₁₂)))

@[scoped simp] theorem mk34_ctxLitAndXor2_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (c₁ : Wire M) (neg₁ : Bool) (c₂ e₁
    e₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₁₂ : e₁ ≠ c₂) (he₂₂ : e₂ ≠ c₂) (hc₁ : c₁.val <
      cur) (hc₂ : c₂.val <
    cur) (he₁ : e₁.val < cur) (he₂ : e₂.val <
      cur) (body : TempPhaseProg M) : (mk34_ctxLitAndXor2 cur hcur c₁ neg₁ c₂ e₁
    e₂ neg₂ h₁₂ he₁₂ he₂₂ hc₁ hc₂ he₁ he₂).plug body =
      withLitAndXor2 cur hcur c₁ neg₁ c₂ e₁ e₂ neg₂ h₁₂ he₁₂ he₂₂ hc₁
    hc₂ he₁ he₂ body := by
  simp only [mk34_ctxLitAndXor2, TempCtx.append_plug, ctxCliffAlloc_plug, mk34_ctxLitAndXor1_plug,
    withLitAndXor2]

@[scoped simp] theorem mk34_ctxLitAndXor2_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (c₁ : Wire M) (neg₁ :
    Bool) (c₂ e₁ e₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (he₁₂ : e₁ ≠ c₂) (he₂₂ : e₂ ≠ c₂)
      (hc₁ : c₁.val < cur) (hc₂
    : c₂.val <
      cur) (he₁ : e₁.val < cur) (he₂ : e₂.val <
      cur) : (mk34_ctxLitAndXor2 cur hcur c₁ neg₁ c₂ e₁ e₂ neg₂ h₁₂
    he₁₂ he₂₂ hc₁ hc₂ he₁ he₂).countTempAnd = 1 := by simp [mk34_ctxLitAndXor2]

/-- `TempCtx` wrapper for a single ripple comparator step `withLtStep` (`1` `TempAnd`). -/
def mk34_ctxLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (_hp : prev.val < cur) (hbp : b ≠ prev) : TempCtx M :=
  let out : Wire M := ⟨cur, by omega⟩
  let cPre : CliffProg M := .seq (.cnot b a hab.symm) (.cnot prev b hbp.symm)
  let cPost : CliffProg M :=
    .seq (.cnot prev b hbp.symm)
      (.seq (.cnot b a hab.symm)
        (.cnot prev out (wire_ne_of_lt (by dsimp [out]; omega))))
  (ctxCliffAlloc cPre).append
    ((ctxTempBit a b out hab
        (wire_ne_of_lt (by dsimp [out]; omega))
        (wire_ne_of_lt (by dsimp [out]; omega))).append
      (ctxCliffAlloc cPost))

@[scoped simp] theorem mk34_ctxLtStep_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (a b prev : Wire M) (hab : a ≠ b) (ha
    : a.val <
      cur) (hb : b.val < cur) (hp : prev.val <
      cur) (hbp : b ≠ prev) (body : TempPhaseProg M) : (mk34_ctxLtStep
    cur hcur a b prev hab ha hb hp hbp).plug body =
      withLtStep cur hcur a b prev hab ha hb hp hbp body := by
  simp only [mk34_ctxLtStep, TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug, withLtStep]

@[scoped simp] theorem mk34_ctxLtStep_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤
    M) (a b prev : Wire M) (hab : a ≠
    b) (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val <
      cur) (hbp : b ≠ prev) : (mk34_ctxLtStep cur hcur a b prev
    hab ha hb hp hbp).countTempAnd = 1 := by
  simp [mk34_ctxLtStep, ctxTempBit, TempCtx.countTempAnd]

/-- `TempCtx` wrapper for `W`-step comparator loop `withLtCompLoop` (`W` `TempAnd`s). -/
def mk34_ctxLtCompLoop {M : ℕ} : (W : ℕ) → (cur : ℕ) → (hcur : cur + W + 1 ≤ M) →
    (a b : Fin W → Wire M) → (hab : ∀ j, a j ≠ b j) →
    (ha : ∀ j, (a j).val < cur) → (hb : ∀ j, (b j).val < cur) → TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, hcur, a, b, hab, ha, hb =>
      let prev : Wire M := ⟨cur, by omega⟩
      (mk34_ctxLtStep (cur + 1) (by omega) (a 0) (b 0) prev (hab 0)
        (lt_trans (ha 0) (by omega)) (lt_trans (hb 0) (by omega))
        (by dsimp [prev]; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp [prev]; omega))).append
        (mk34_ctxLtCompLoop W (cur + 1) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ b j.succ) (fun j ↦ hab j.succ)
          (fun j ↦ lt_trans (ha j.succ) (by omega))
          (fun j ↦ lt_trans (hb j.succ) (by omega)))

@[scoped simp] theorem mk34_ctxLtCompLoop_plug {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
      (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
      (mk34_ctxLtCompLoop W cur hcur a b hab ha hb).plug body =
        withLtCompLoop W cur hcur a b hab ha hb body
  | 0, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, a, b, hab, ha, hb, body => by
      simp only [mk34_ctxLtCompLoop, TempCtx.append_plug, mk34_ctxLtStep_plug,
        mk34_ctxLtCompLoop_plug, withLtCompLoop]

@[scoped simp] theorem mk34_ctxLtCompLoop_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur),
      (mk34_ctxLtCompLoop W cur hcur a b hab ha hb).countTempAnd = W
  | 0, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, a, b, hab, ha, hb => by
      simp only [mk34_ctxLtCompLoop, mk34_append_countTempAnd, mk34_ctxLtStep_countTempAnd,
        mk34_ctxLtCompLoop_countTempAnd]
      omega

theorem mk34_writeRegProg_self {M n : ℕ} (β : BitAssignment n) (rComb : QRegister M n) :
    writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β := by
  funext q
  by_cases hmem : q ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hmem
    exact writeRegProg_apply_reg β rComb _ idx
  · exact writeRegProg_apply_of_not_mem β rComb _ q hmem

theorem mk34_writeRegProg_idem {M n : ℕ} (β : BitAssignment n) (rComb : QRegister M n)
    (γ₁ γ₂ : BitAssignment M) :
    writeRegProg (writeRegProg β rComb γ₁) rComb γ₂ = writeRegProg β rComb γ₂ := by
  funext q
  by_cases hmem : q ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hmem
    rw [writeRegProg_apply_reg, writeRegProg_apply_reg]
  · rw [writeRegProg_apply_of_not_mem (writeRegProg β rComb γ₁) rComb γ₂ q hmem,
      writeRegProg_apply_of_not_mem β rComb
        γ₁ q hmem, writeRegProg_apply_of_not_mem β rComb γ₂ q hmem]

theorem mk34_writeRegProg_update {M n : ℕ} (β : BitAssignment n) (rComb : QRegister M n)
    (γ : BitAssignment M) (anc :
    Wire M) (val : ZMod 2) : Function.update (writeRegProg β rComb γ) (rComb anc) val =
      writeRegProg β rComb
    (Function.update γ anc val) := by
  funext q
  by_cases hmem : q ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hmem
    by_cases hia : idx = anc
    · subst hia
      rw [Function.update_self, writeRegProg_apply_reg, Function.update_self]
    · rw [Function.update_of_ne (rComb.wires.injective.ne hia),
          writeRegProg_apply_reg, writeRegProg_apply_reg, Function.update_of_ne hia]
  · have hne : q ≠ rComb anc := fun h ↦ hmem ⟨anc, h.symm⟩
    rw[Function.update_of_ne hne, writeRegProg_apply_of_not_mem _ rComb _ q hmem,
        writeRegProg_apply_of_not_mem _ rComb _ q hmem]

/-- Compiles a `TempCtx M` around `cLeaf` into a reversible `Circuit n` using Toffoli gates. -/
def mk34_ctxToToff {M n : ℕ} (rComb : QRegister M n) (cLeaf : Circuit n) : TempCtx M → Circuit n
  | .hole => cLeaf
  | .seqPre c K => (c.onRegister rComb).toCircuit ;;ᶜ mk34_ctxToToff rComb cLeaf K
  | .seqPost K c => mk34_ctxToToff rComb cLeaf K ;;ᶜ (c.onRegister rComb).toCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
        (rComb.wires.injective.ne h₂a) ;;ᶜ
      mk34_ctxToToff rComb cLeaf K ;;ᶜ
      Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
        (rComb.wires.injective.ne h₂a)

/-- Compiles a `TempCtx M` around `cLeaf` into a `0`-`.TOFF` `DynamicCircuit Var n` with
  measurement uncompute. -/
def mk34_ctxToDyn {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) (cLeaf : Circuit n) :
    TempCtx M → DynamicCircuit Var n
  | .hole => .circuit cLeaf
  | .seqPre c K => .seq (.circuit (c.onRegister rComb).toCircuit) (mk34_ctxToDyn v rComb cLeaf K)
  | .seqPost K c => .seq (mk34_ctxToDyn v rComb cLeaf K) (.circuit (c.onRegister rComb).toCircuit)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq
        (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
        (.seq (mk34_ctxToDyn v rComb cLeaf K)
          (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)))

theorem mk34_ctxToDyn_count_toff {Var : Type} {M n : ℕ} (v : Var)
    (rComb : QRegister M n) (cLeaf : Circuit n) : ∀ K : TempCtx M,
      (mk34_ctxToDyn v rComb cLeaf K).count PrimitiveGate.TOFF = cLeaf.count PrimitiveGate.TOFF
  | .hole => by simp [mk34_ctxToDyn]
  | .seqPre _ K => by simp [mk34_ctxToDyn, mk34_ctxToDyn_count_toff v rComb cLeaf K]
  | .seqPost K _ => by simp [mk34_ctxToDyn, mk34_ctxToDyn_count_toff v rComb cLeaf K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp [mk34_ctxToDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, mk34_ctxToDyn_count_toff v rComb cLeaf K]

theorem mk34_ctxToDyn_count_t {Var : Type} {M n : ℕ} (v : Var)
    (rComb : QRegister M n) (cLeaf : Circuit n) : ∀ K : TempCtx M,
      (mk34_ctxToDyn v rComb cLeaf K).count PrimitiveGate.T =
        4 * K.countTempAnd + cLeaf.count PrimitiveGate.T
  | .hole => by simp [mk34_ctxToDyn, TempCtx.countTempAnd]
  | .seqPre _ K => by
      simp [mk34_ctxToDyn, TempCtx.countTempAnd, mk34_ctxToDyn_count_t v rComb cLeaf K]
  | .seqPost K _ => by
      simp [mk34_ctxToDyn, TempCtx.countTempAnd, mk34_ctxToDyn_count_t v rComb cLeaf K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp only [mk34_ctxToDyn, DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
          DynamicCircuit.count_andUncompute_t, TempCtx.countTempAnd,
            mk34_ctxToDyn_count_t v rComb cLeaf K]
      ring

theorem mk34_ctxToDyn_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb :
    QRegister M n) (cLeaf : Circuit n) (K : TempCtx M) : PreservesStoreConst
      (mk34_ctxToDyn v rComb cLeaf K) := by
  let _ : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩
  induction K with
  | hole => exact PreservesStoreConst.circuit _
  | seqPre _ _ ih => exact PreservesStoreConst.seq (PreservesStoreConst.circuit _) ih
  | seqPost _ _ ih => exact PreservesStoreConst.seq ih (PreservesStoreConst.circuit _)
  | tempAnd c₁ c₂ anc h₁₂ _ _ _ ih =>
      exact PreservesStoreConst.seq (PreservesStoreConst.circuit _) (PreservesStoreConst.seq ih
        (PreservesStoreConst.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂)))

theorem mk34_cliff_onRegister_eval_ket {M n : ℕ} (rComb : QRegister M n)
    (c : CliffProg M) (β : BitAssignment n) :
    ((c.onRegister rComb).toCircuit).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      MeasureBranchHadamardSem.ket (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) := by
  simpa only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, TempPhaseProg.evalSign,
    TempPhaseProg.evalBits, ZMod.val_zero, _root_.pow_zero, one_smul]
    using eval_onRegister_prog_ket rComb (.cliff c) β

theorem mk34_writeRegProg_read {M n : ℕ} (β : BitAssignment n) (rComb : QRegister M n)
    (g : BitAssignment M) : (fun idx ↦ writeRegProg β rComb g (rComb idx)) = g :=
  funext fun idx ↦ writeRegProg_apply_reg β rComb g idx

theorem mk34_ctxToToff_eval_ket {M n : ℕ} (rComb : QRegister M n)
    (cLeaf : Circuit n) (fLeaf : BitAssignment M → ZMod 2) (hLeaf : ∀ β : BitAssignment n,
      cLeaf.eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
        ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rComb idx))).val) • MeasureBranchHadamardSem.ket β)
    (q₀ : Wire M) : ∀ (K : TempCtx M) (β : BitAssignment n),
      let γ : BitAssignment M := fun idx ↦ β (rComb idx)
      (mk34_ctxToToff rComb cLeaf K).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
        ((-1 : ℂ) ^ (fLeaf (K.fwdBits γ)).val) •
          MeasureBranchHadamardSem.ket (writeRegProg β rComb ((K.plug (.z q₀)).evalBits γ))
  | .hole, β => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      rw [hLeaf β, mk34_writeRegProg_self]
  | .seqPre c K₁, β => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      rw [MeasureBranchHadamardSem.eval_seq_mulVec, mk34_cliff_onRegister_eval_ket,
        mk34_ctxToToff_eval_ket rComb cLeaf
          fLeaf hLeaf q₀ K₁, mk34_writeRegProg_read, mk34_writeRegProg_idem]
  | .seqPost K₁ c, β => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      rw [MeasureBranchHadamardSem.eval_seq_mulVec,
        mk34_ctxToToff_eval_ket rComb cLeaf fLeaf hLeaf q₀ K₁ β,
          Matrix.mulVec_smul, mk34_cliff_onRegister_eval_ket, mk34_writeRegProg_read,
            mk34_writeRegProg_idem]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, β => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      let γ : BitAssignment M := fun idx ↦ β (rComb idx)
      let γ₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
      have hβ₁ : Function.update β (rComb anc) (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) =
          writeRegProg β rComb γ₁ := by
        have h := mk34_writeRegProg_update β rComb γ anc (γ anc + γ c₁ * γ c₂)
        rwa [mk34_writeRegProg_self] at h
      rw [MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.eval_seq_mulVec,
          MeasureBranchHadamardSem.ket_TOFF, hβ₁,
            mk34_ctxToToff_eval_ket rComb cLeaf fLeaf hLeaf q₀ K₁ (writeRegProg β
          rComb γ₁), mk34_writeRegProg_read, mk34_writeRegProg_idem, Matrix.mulVec_smul,
          MeasureBranchHadamardSem.ket_TOFF, writeRegProg_apply_reg, writeRegProg_apply_reg,
            writeRegProg_apply_reg,
          mk34_writeRegProg_update]

theorem mk34_cleanRem_of_tailScr {M n : ℕ} (rComb : QRegister M n) {rem : ℕ} (hrem : rem ≤ M)
    {β : BitAssignment n} (hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0) :
    cleanRem M rem (fun idx ↦ β (rComb idx)) := fun w hw ↦ by
  rw [show w = ⟨(M - rem) + (w.val - (M - rem)), by omega⟩ from Fin.ext (by dsimp; omega)]
  exact hz ⟨w.val - (M - rem), by omega⟩

theorem mk34_projZeroAll_clean_step {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem remMid : ℕ} (hrem : rem ≤ M) (hmid : remMid ≤ M)
    (U : Operator (2 ^ n)) (fStep : BitAssignment M → BitAssignment M) (ph : BitAssignment n → ℂ)
    (hU : ∀ β : BitAssignment n, U.mulVec (MeasureBranchHadamardSem.ket β) =
        ph β • MeasureBranchHadamardSem.ket (writeRegProg β rComb (fStep (fun idx ↦
          β (rComb idx)))))
    (hpres : ∀ γ : BitAssignment M, cleanRem M rem γ → cleanRem M remMid (fStep γ)) :
    projZeroAll remMid (tailScr rComb remMid hmid) *
      (U * projZeroAll rem (tailScr rComb rem hrem)) =
      U * projZeroAll rem (tailScr rComb rem hrem) := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0
  · simp only [hz, imp_true_iff, ↓reduceIte, hU β, Matrix.mulVec_smul, ket_projZeroAll]
    have hout : ∀ j : Fin remMid,
        writeRegProg β rComb (fStep (fun idx ↦ β (rComb idx))) (tailScr rComb remMid hmid j) = 0 :=
      fun j ↦ by
        dsimp [tailScr]
        rw [writeRegProg_apply_reg]
        exact hpres _ (mk34_cleanRem_of_tailScr rComb hrem hz)
          ⟨(M - remMid) + j.val, by omega⟩ (by dsimp; omega)
    simp only [hout, imp_true_iff, ↓reduceIte]
  · simp only [hz, ↓reduceIte, Matrix.mulVec_zero]

theorem mk34_realizesCleanUnitary_ctxToDyn
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) (cLeaf : Circuit n) (fLeaf : BitAssignment M → ZMod 2)
    (hLeaf : ∀ β : BitAssignment n, cLeaf.eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
        ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rComb idx))).val) • MeasureBranchHadamardSem.ket β)
    (q₀ : Wire M) : ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M),
      ValidCleanRem M rem (K.plug (.z q₀)) →
      RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
        (mk34_ctxToDyn v rComb cLeaf K) ((mk34_ctxToToff rComb cLeaf K).eval)
  | .hole, rem, hrem, _ => RealizesCleanUnitary.circuit v _ cLeaf
  | .seqPre c K₁, rem, hrem, ⟨remMid, hmid, _, hv₂, hpres⟩ => by
      have ih₁ := RealizesCleanUnitary.circuit v (projZeroAll rem (tailScr rComb rem hrem))
        (c.onRegister rComb).toCircuit
      have ih₂ := mk34_realizesCleanUnitary_ctxToDyn v rComb cLeaf fLeaf hLeaf q₀ K₁ remMid hmid hv₂
      have hclean := mk34_projZeroAll_clean_step rComb hrem hmid
        ((c.onRegister rComb).toCircuit).eval.1 c.eval (fun _ ↦ 1)
        (fun β ↦ by rw [one_smul, mk34_cliff_onRegister_eval_ket]) hpres
      have hseq := RealizesCleanUnitary_seq_asym (projZeroAll_conjTranspose rem _)
        (projZeroAll_conjTranspose remMid _) ih₁ ih₂ hclean
      have heq : (mk34_ctxToToff rComb cLeaf K₁).eval * ((c.onRegister rComb).toCircuit).eval =
          (mk34_ctxToToff rComb cLeaf (.seqPre c K₁)).eval := by
        simp [mk34_ctxToToff, Circuit.eval_seq]
      simpa [mk34_ctxToDyn, heq] using hseq
  | .seqPost K₁ c, rem, hrem, ⟨remMid, hmid, hv₁, _, hpres⟩ => by
      have ih₁ := mk34_realizesCleanUnitary_ctxToDyn v rComb cLeaf fLeaf hLeaf q₀ K₁ rem hrem hv₁
      have ih₂ := RealizesCleanUnitary.circuit v (projZeroAll remMid (tailScr rComb remMid hmid))
        (c.onRegister rComb).toCircuit
      have hclean := mk34_projZeroAll_clean_step rComb hrem hmid
        (mk34_ctxToToff rComb cLeaf K₁).eval.1 (K₁.plug (.z q₀)).evalBits _
        (mk34_ctxToToff_eval_ket rComb cLeaf fLeaf hLeaf q₀ K₁) hpres
      have hseq := RealizesCleanUnitary_seq_asym (projZeroAll_conjTranspose rem _)
        (projZeroAll_conjTranspose remMid _) ih₁ ih₂ hclean
      have heq : ((c.onRegister rComb).toCircuit).eval * (mk34_ctxToToff rComb cLeaf K₁).eval =
          (mk34_ctxToToff rComb cLeaf (.seqPost K₁ c)).eval := by
        simp [mk34_ctxToToff, Circuit.eval_seq]
      simpa [mk34_ctxToDyn, heq] using hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, rem, hrem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      have hrem1 : rem' + 1 ≤ M := by omega
      have ihBody :=
        mk34_realizesCleanUnitary_ctxToDyn v rComb cLeaf fLeaf hLeaf q₀ K₁ rem' hrem' hvBody
      have hdisj : ∀ j : Fin rem', rComb anc ≠ tailScr rComb rem' hrem' j := fun j h ↦ by
        have hinj := congrArg Fin.val (rComb.wires.injective h)
        dsimp [tailScr, rem'] at hinj
        omega
      let U_body := (mk34_ctxToToff rComb cLeaf K₁).eval
      let U_clean := (mk34_ctxToToff rComb cLeaf (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁)).eval
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        rem' (tailScr rComb rem' hrem') hdisj (mk34_ctxToDyn v rComb cLeaf K₁) U_body U_clean ihBody
        (fun β hanc0 _ ↦ by
          simp only [U_clean, U_body, mk34_ctxToToff, MeasureBranchHadamardSem.eval_seq_mulVec,
            MeasureBranchHadamardSem.ket_TOFF, hanc0, zero_add])
        (fun β hanc0 hscr0 ↦ by
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
          have hγ₁_clean : cleanRem M rem' β₁ := fun w hw ↦ by
            dsimp only [β₁]
            rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [rem'] at hw; omega))]
            exact mk34_cleanRem_of_tailScr rComb hrem' hscr0 w hw
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hγ₁_clean
          have hfinal_anc :
              ((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).plug (.z q₀)).evalBits γ anc = 0 := by
            dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
            change Function.update ((K₁.plug (.z q₀)).evalBits β₁) anc
              ((K₁.plug (.z q₀)).evalBits β₁ anc +
                (K₁.plug (.z q₀)).evalBits β₁ c₁ * (K₁.plug (.z q₀)).evalBits β₁ c₂) anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, show γ anc = 0 from hanc0, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [show U_clean.1.mulVec (MeasureBranchHadamardSem.ket β) =
            _ from mk34_ctxToToff_eval_ket rComb cLeaf fLeaf
              hLeaf q₀ (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁) β, Matrix.mulVec_smul,
              MeasureBranchHadamardSem.ket_projector_zero, writeRegProg_apply_reg, hfinal_anc]
          simp)
      have hscr_eq : projZeroAll (rem' + 1) (Fin.cons (rComb anc) (tailScr rComb rem' hrem')) =
          projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1) := by
        rw [show anc = ⟨M - (rem' + 1), by omega⟩ from Fin.ext (by dsimp [rem']; omega),
          ← tailScr_succ rComb rem' hrem1]
      exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (rem' + 1) _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hrem1 hrem (by omega))
        (by simpa [mk34_ctxToDyn, hscr_eq] using hstep)
/- ## Section 3: Stages A & C (`mk34_cComp3` / `mk34_dComp3`, `23` `TempAnd`s = `92 T` Each) -/

/-- High `86`-wire slice `rCore[3948..4034)` read by the mid-phase kickback decision polynomial. -/
abbrev mk34_rCoreHi86 {n : ℕ} (rCore : QRegister posCoreWires n) : QRegister 86 n :=
  rCore.slice 3948 86 (by dsimp [posCoreWires]; omega)

/-- Persistent `3`-wire hold slice `rScr34[0..3)` carrying `(u1, vL, d3)` across Stage B. -/
abbrev mk34_rHold3 {n : ℕ} (rScr34 : QRegister 34 n) : QRegister 3 n :=
  rScr34.slice 0 3 (by decide)

/-- Clean `31`-wire workspace slice `rScr34[3..34)` shared across Stages A, B, and C. -/
abbrev mk34_rSub31 {n : ℕ} (rScr34 : QRegister 34 n) : QRegister 31 n :=
  rScr34.slice 3 31 (by decide)

/-- Clean `23`-wire prefix `rSub31[0..23)` (`rScr34[3..26)`) used by Stages A and C. -/
abbrev mk34_rSub23 {n : ℕ} (rScr34 : QRegister 34 n) : QRegister 23 n :=
  (mk34_rSub31 rScr34).slice 0 23 (by decide)

theorem mk34_disj_concat_left {m₁ m₂ k n : ℕ} {r₁ : QRegister m₁ n} {r₂ : QRegister m₂ n}
    {r₃ : QRegister k n} (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃)
    (h₂₃ : r₂.DisjointWires r₃) : (r₁.concat r₂ h₁₂).DisjointWires r₃ :=
  QRegister.disjoint_iff.mpr fun a b heq ↦
    Fin.addCases
      (fun i hi ↦ h₁₃.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
      (fun j hj ↦ h₂₃.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj)) a heq

theorem mk34_rHold3_disjoint_rSub31 {n : ℕ} (rScr34 : QRegister 34 n) :
    (mk34_rHold3 rScr34).DisjointWires (mk34_rSub31 rScr34) :=
  QRegister.disjoint_iff.mpr fun a b h ↦ by
    have heq : rScr34 ⟨0 + a.val, by omega⟩ = rScr34 ⟨3 + b.val, by omega⟩ := by
      simpa [mk34_rHold3, mk34_rSub31, QRegister.slice_apply] using h
    have hv := congrArg Fin.val (rScr34.wires.injective heq)
    dsimp at hv
    omega

/-- Active `89`-wire register `rCoreHi86 ++ rHold3` shared across Stages A, B, and C. -/
abbrev mk34_rAct89 {n : ℕ} (rCore : QRegister posCoreWires n) (rScr34 : QRegister 34 n)
    (hCS : rCore.DisjointWires rScr34) : QRegister 89 n :=
  (mk34_rCoreHi86 rCore).concat (mk34_rHold3 rScr34) ((hCS.compose_left _).compose_right _)

/-- Combined `112`-wire register `rAct89 ++ rSub23` for Stages A and C. -/
def mk34_rComb112 {n : ℕ} (rCore : QRegister posCoreWires n) (rScr34 : QRegister 34 n)
    (hCS : rCore.DisjointWires rScr34) : QRegister 112 n :=
  (mk34_rAct89 rCore rScr34 hCS).concat (mk34_rSub23 rScr34)
    (mk34_disj_concat_left _ (((hCS.compose_left _).compose_right _).compose_right _)
      ((mk34_rHold3_disjoint_rSub31 rScr34).compose_right _))
theorem mk34_tailScr_rComb112 {n : ℕ} (rCore : QRegister posCoreWires n) (rScr34 : QRegister 34 n)
    (hCS : rCore.DisjointWires rScr34) :
    tailScr (mk34_rComb112 rCore rScr34 hCS) 23 (by decide) = (mk34_rSub23 rScr34).wires := by
  funext j
  dsimp only [tailScr, mk34_rComb112]
  have h1 : (⟨(112 - 23) + j.val, by omega⟩ : Fin ((86 + 3) + 23)) = Fin.natAdd 89 j := by
    ext; dsimp
  rw [h1, QRegister.concat_apply_right]

/-- Target `3`-bit vector `(u1, vL, d3)` XORed onto `rHold3` by Stage A and uncomputed by Stage
  C. -/
def mk34_holdVec {n : ℕ} (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    BitAssignment 3 :=
  let s0 := β (rCore ⟨3948, by decide⟩)
  let b1 := β (rCore ⟨3949, by decide⟩)
  let b2 := β (rCore ⟨3950, by decide⟩)
  let sr := β (rCore ⟨4016, by decide⟩)
  let ge216 := ge216Bit (β (rCore ⟨3963, by decide⟩)) (β (rCore ⟨3964, by decide⟩))
    (β (rCore ⟨3965, by decide⟩)) (β (rCore ⟨3966, by decide⟩)) (β (rCore ⟨3967, by decide⟩))
  let ge218 := ge218Bit (β (rCore ⟨3969, by decide⟩)) (β (rCore ⟨3970, by decide⟩))
    (β (rCore ⟨3971, by decide⟩)) (β (rCore ⟨3972, by decide⟩)) (β (rCore ⟨3973, by decide⟩))
    (β (rCore ⟨3974, by decide⟩)) (β (rCore ⟨3975, by decide⟩))
  let ge217 := ge217Bit (β (rCore ⟨3976, by decide⟩)) (β (rCore ⟨3977, by decide⟩))
    (β (rCore ⟨3978, by decide⟩)) (β (rCore ⟨3979, by decide⟩)) (β (rCore ⟨3980, by decide⟩))
    (β (rCore ⟨3981, by decide⟩)) (β (rCore ⟨3982, by decide⟩)) (β (rCore ⟨3983, by decide⟩))
  let u1 := (1 + b2) * (1 + b1)
  let d0 := (1 + s0) * ge216
  let u2 := (1 + sr) * (1 + ge218)
  let u3 := u2 * (1 + d0)
  let vL := u1 * u3
  let d3 := s0 * ge217
  fun i ↦ if i.val = 0 then u1 else if i.val = 1 then vL else d3

/-- Diagonal leaf phase polynomial `γ[86]*γ[106] + γ[87]*γ[110] + γ[88]*γ[111]` for Stages A and
  C. -/
def mk34_fLeafComp3 (γ : BitAssignment 112) : ZMod 2 :=
  γ ⟨86, by decide⟩ * γ ⟨106, by decide⟩ +
  γ ⟨87, by decide⟩ * γ ⟨110, by decide⟩ +
  γ ⟨88, by decide⟩ * γ ⟨111, by decide⟩

/-- `0`-`T`, `0`-`.TOFF` three-`CZ` leaf circuit for Stages A and C. -/
def mk34_cLeafComp3On {n : ℕ} (rComb : QRegister 112 n) : Circuit n :=
  asymMid_czCircuit (rComb ⟨86, by decide⟩) (rComb ⟨106, by decide⟩)
    (rComb.wires.injective.ne (by decide)) ;;ᶜ
  asymMid_czCircuit (rComb ⟨87, by decide⟩) (rComb ⟨110, by decide⟩)
    (rComb.wires.injective.ne (by decide)) ;;ᶜ
  asymMid_czCircuit (rComb ⟨88, by decide⟩) (rComb ⟨111, by decide⟩)
    (rComb.wires.injective.ne (by decide))

@[scoped simp] theorem mk34_cLeafComp3On_count_toff {n : ℕ} (rComb : QRegister 112 n) :
    (mk34_cLeafComp3On rComb).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_cLeafComp3On, asymMid_czCircuit_count_toff, Circuit.count]

@[scoped simp] theorem mk34_cLeafComp3On_count_t {n : ℕ} (rComb : QRegister 112 n) :
    (mk34_cLeafComp3On rComb).count PrimitiveGate.T = 0 := by
  simp [mk34_cLeafComp3On, asymMid_czCircuit_count_t, Circuit.count]

theorem mk34_cLeafComp3On_eval_mbh_ket {n : ℕ} (rComb : QRegister 112 n) (β : BitAssignment n) :
    (mk34_cLeafComp3On rComb).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafComp3 (fun idx ↦ β (rComb idx))).val) •
        MeasureBranchHadamardSem.ket β := by
  rw [mbh_ket_eq_ket]
  dsimp only [mk34_cLeafComp3On]
  simp only [asymMid_eval_seq_mulVec, Matrix.mulVec_smul, asymMid_ket_czCircuit,
    smul_smul, TempPhaseProg.neg_one_pow_zmod2_mul]
  congr 3
  dsimp only [mk34_fLeafComp3]
  ring
/-- `23`-`TempAnd` context (`92 T`, `23` clean wires `89..111`) computing `u1` (`106`), `vL`
  (`110`), and `d3` (`111`). -/
def mk34_ctxComp23 : TempCtx 112 :=
  (ctxLitAnd 89 (by decide) ⟨16, by decide⟩ false ⟨15,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 90 (by decide) ⟨17, by decide⟩ true ⟨89,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 91 (by decide) ⟨19, by decide⟩ false ⟨18,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 92 (by decide) ⟨91, by decide⟩ false ⟨90,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 93 (by decide) ⟨27, by decide⟩ false ⟨26,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 94 (by decide) ⟨24, by decide⟩ false ⟨23,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 95 (by decide) ⟨22, by decide⟩ true ⟨21,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 96 (by decide) ⟨94, by decide⟩ false ⟨95,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 97 (by decide) ⟨25, by decide⟩ true ⟨96,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 98 (by decide) ⟨93, by decide⟩ false ⟨97,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 99 (by decide) ⟨35, by decide⟩ false ⟨34,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 100 (by decide) ⟨32, by decide⟩ false ⟨31,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 101 (by decide) ⟨30, by decide⟩ true ⟨29,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 102 (by decide) ⟨101, by decide⟩ false ⟨28,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 103 (by decide) ⟨100, by decide⟩ false ⟨102,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 104 (by decide) ⟨33, by decide⟩ true ⟨103,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 105 (by decide) ⟨99, by decide⟩ false ⟨104,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 106 (by decide) ⟨2, by decide⟩ true ⟨1,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 107 (by decide) ⟨0, by decide⟩ true ⟨92,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 108 (by decide) ⟨68, by decide⟩ true ⟨98,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 109 (by decide) ⟨108, by decide⟩ false ⟨107,
    by decide⟩ true (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 110 (by decide) ⟨106, by decide⟩ false ⟨109,
    by decide⟩ false (by decide) (by decide) (by decide)).append <|
  ctxLitAnd 111 (by decide) ⟨0, by decide⟩ false ⟨105,
    by decide⟩ false (by decide) (by decide) (by decide)
@[scoped simp] theorem mk34_ctxComp23_countTempAnd : mk34_ctxComp23.countTempAnd = 23 := by
  simp [mk34_ctxComp23]

attribute [local irreducible] stepLitAnd stepLitAndXor1 stepLitAndXor2

/-- Leaf wire specification for `mk34_ctxComp23` on hold wires `86..88` and target wires `106,
  110, 111`. -/
def mk34_comp3Spec (φ : BitAssignment 112)
    (b2 b1 s0 sr ge216 ge218 ge217 h0 h1 h2 : ZMod 2) : Prop :=
  let u1 := (1 + b2) * (1 + b1)
  let d0 := (1 + s0) * ge216
  let u2 := (1 + sr) * (1 + ge218)
  let u3 := u2 * (1 + d0)
  let vL := u1 * u3
  let d3 := s0 * ge217
  φ ⟨86, by decide⟩ = h0 ∧
  φ ⟨87, by decide⟩ = h1 ∧
  φ ⟨88, by decide⟩ = h2 ∧
  φ ⟨106, by decide⟩ = u1 ∧
  φ ⟨110, by decide⟩ = vL ∧
  φ ⟨111, by decide⟩ = d3

theorem mk34_stepLitAnd_apply {M cur : ℕ} (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ : Wire M) (neg₂ : Bool) (β : BitAssignment M) (w : Wire M) :
    stepLitAnd cur hcur c₁ neg₁ c₂ neg₂ β w =
      if w.val = cur then litVal (β c₁) neg₁ * litVal (β c₂) neg₂ else β w := by
  by_cases hw : w.val = cur
  · simp only [hw, ↓reduceIte, stepLitAnd_eq hw]
  · simp only [hw, ↓reduceIte, stepLitAnd_of_ne hw]

theorem mk34_ctxComp23_scoped_of_wire (q : Wire 112) : ∃ s23 : BitAssignment 112 →
    BitAssignment 112, ScopedBlock 112 23
    s23 (.z q) (mk34_ctxComp23.plug (.z q)) ∧ ∀ γ : BitAssignment 112,
      mk34_comp3Spec (s23 γ) (γ ⟨2, by decide⟩) (γ ⟨1,
    by decide⟩) (γ ⟨0, by decide⟩) (γ ⟨68,
      by decide⟩) (ge216Bit (γ ⟨15, by decide⟩) (γ ⟨16, by decide⟩) (γ ⟨17, by
    decide⟩) (γ ⟨18, by decide⟩) (γ ⟨19,
      by decide⟩)) (ge218Bit (γ ⟨21, by decide⟩) (γ ⟨22, by decide⟩) (γ ⟨23, by
    decide⟩) (γ ⟨24, by decide⟩) (γ ⟨25, by decide⟩) (γ ⟨26, by decide⟩) (γ ⟨27,
      by decide⟩)) (ge217Bit (γ ⟨28, by
    decide⟩) (γ ⟨29, by decide⟩) (γ ⟨30, by decide⟩) (γ ⟨31, by decide⟩) (γ ⟨32, by decide⟩) (γ ⟨33,
      by decide⟩) (γ ⟨34,
    by decide⟩) (γ ⟨35, by decide⟩)) (γ ⟨86, by decide⟩) (γ ⟨87, by decide⟩) (γ ⟨88, by decide⟩) :=
      by
  simp only [mk34_ctxComp23, TempCtx.append_plug, mk34_ctxLitAnd_plug]
  change ∃ s23, ScopedBlock 112 (112 - 89) s23 (.z q) _ ∧ _
  repeat refine ScopedBlock.exists_withLitAnd ?_
  refine ⟨fun γ ↦ γ, ScopedBlock.z_kick q, fun γ ↦ ?_⟩
  dsimp only [Function.comp_apply, mk34_comp3Spec, ge216Bit, ge218Bit, ge217Bit]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mk34_stepLitAnd_apply]
  · simp [mk34_stepLitAnd_apply]
  · simp [mk34_stepLitAnd_apply]
  · simp [mk34_stepLitAnd_apply, litVal_true]
  · simp [mk34_stepLitAnd_apply, litVal_false, litVal_true]
  · simp [mk34_stepLitAnd_apply, litVal_false, litVal_true]
theorem mk34_ctxComp23_fwdBits_wire (q : Wire 112) (γ : BitAssignment 112) (hγ : cleanRem 112 23 γ)
    : ∃ s23 :
    BitAssignment 112 → BitAssignment 112,
      mk34_ctxComp23.fwdBits γ q = s23 γ q ∧ mk34_comp3Spec (s23 γ) (γ ⟨2, by
    decide⟩) (γ ⟨1, by decide⟩) (γ ⟨0, by decide⟩) (γ ⟨68,
      by decide⟩) (ge216Bit (γ ⟨15, by decide⟩) (γ ⟨16, by decide⟩)
    (γ ⟨17, by decide⟩) (γ ⟨18, by decide⟩) (γ ⟨19,
      by decide⟩)) (ge218Bit (γ ⟨21, by decide⟩) (γ ⟨22, by decide⟩) (γ
    ⟨23,
      by decide⟩) (γ ⟨24, by decide⟩) (γ ⟨25, by decide⟩) (γ ⟨26, by decide⟩) (γ ⟨27,
      by decide⟩)) (ge217Bit (γ ⟨28,
    by decide⟩) (γ ⟨29, by decide⟩) (γ ⟨30, by decide⟩) (γ ⟨31, by decide⟩) (γ ⟨32,
      by decide⟩) (γ ⟨33, by decide⟩) (γ
    ⟨34,
      by decide⟩) (γ ⟨35, by decide⟩)) (γ ⟨86, by decide⟩) (γ ⟨87, by decide⟩) (γ ⟨88,
      by decide⟩) := by
  obtain ⟨s23, hB, hSpec⟩ := mk34_ctxComp23_scoped_of_wire q
  have h₁ := mk34_ctxComp23.plug_evalSign (.z q) γ
  have h₂ := hB.sign γ hγ
  dsimp [TempPhaseProg.evalSign] at h₁ h₂
  exact ⟨s23, h₁.symm.trans h₂, hSpec γ⟩

/-- Plugged `TempPhaseProg 112` witness for `mk34_ctxComp23`. -/
def mk34_pComp23 : TempPhaseProg 112 := mk34_ctxComp23.plug (.z ⟨0, by decide⟩)

theorem mk34_pComp23_eq : mk34_ctxComp23.plug (.z ⟨0, by decide⟩) = mk34_pComp23 := rfl

theorem mk34_pComp23_valid_and_bits : ValidCleanRem 112 23 mk34_pComp23 ∧ (∀ γ : BitAssignment
    112, cleanRem 112 23 γ → mk34_pComp23.evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxComp23_scoped_of_wire ⟨0, by decide⟩
  exact ⟨hB.valid, hB.bits⟩

/-- Inner diagonal phase `Circuit n` for Stages A and C (`23` Toffoli pairs + `3` `CZ`s). -/
def mk34_cComp3Inner {n : ℕ} (rCore : QRegister posCoreWires n) (rScr34 : QRegister 34 n)
    (hCS : rCore.DisjointWires rScr34) : Circuit n :=
  let rComb := mk34_rComb112 rCore rScr34 hCS
  mk34_ctxToToff rComb (mk34_cLeafComp3On rComb) mk34_ctxComp23

/-- Stage A / Stage C reversible `Circuit n` XORing `mk34_holdVec rCore β` onto `rHold3`. -/
def mk34_cComp3 {n : ℕ} (rCore : QRegister posCoreWires n) (rScr34 : QRegister 34 n)
    (hCS : rCore.DisjointWires rScr34) : Circuit n :=
  hadamardReg (mk34_rHold3 rScr34) ;;ᶜ
    mk34_cComp3Inner rCore rScr34 hCS ;;ᶜ
    hadamardReg (mk34_rHold3 rScr34)

attribute [local irreducible] mk34_ctxComp23

theorem mk34_cComp3Inner_eval_ket {n : ℕ} (rCore : QRegister posCoreWires n)
    (rScr34 : QRegister 34 n)
    (hCS : rCore.DisjointWires rScr34) (β : BitAssignment n)
    (h23 : ∀ j : Fin 23, β (mk34_rSub23 rScr34 j) = 0) :
    (mk34_cComp3Inner rCore rScr34 hCS).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (∑ i : Fin 3, β (mk34_rHold3 rScr34 i) * mk34_holdVec rCore β i).val) • ket β :=
        by
  let rComb := mk34_rComb112 rCore rScr34 hCS
  let γ : BitAssignment 112 := fun idx ↦ β (rComb idx)
  have hcr : cleanRem 112 23 γ := mk34_cleanRem_of_tailScr rComb (by decide) fun j ↦ by
    rw [congrFun (mk34_tailScr_rComb112 rCore rScr34 hCS) j]
    exact h23 j
  rw [mk34_cComp3Inner, ← mbh_ket_eq_ket,
    mk34_ctxToToff_eval_ket rComb _ _ (mk34_cLeafComp3On_eval_mbh_ket rComb) ⟨0,
      by decide⟩ mk34_ctxComp23 β,
    mk34_pComp23_eq, mk34_pComp23_valid_and_bits.2 _ hcr, mk34_writeRegProg_self, mbh_ket_eq_ket]
  congr 3
  change mk34_fLeafComp3 (mk34_ctxComp23.fwdBits γ) = _
  obtain ⟨_, he86, hw86⟩ := mk34_ctxComp23_fwdBits_wire ⟨86, by decide⟩ γ hcr
  obtain ⟨_, he87, hw87⟩ := mk34_ctxComp23_fwdBits_wire ⟨87, by decide⟩ γ hcr
  obtain ⟨_, he88, hw88⟩ := mk34_ctxComp23_fwdBits_wire ⟨88, by decide⟩ γ hcr
  obtain ⟨_, he106, hw106⟩ := mk34_ctxComp23_fwdBits_wire ⟨106, by decide⟩ γ hcr
  obtain ⟨_, he110, hw110⟩ := mk34_ctxComp23_fwdBits_wire ⟨110, by decide⟩ γ hcr
  obtain ⟨_, he111, hw111⟩ := mk34_ctxComp23_fwdBits_wire ⟨111, by decide⟩ γ hcr
  dsimp only [mk34_fLeafComp3]
  rw [he86.trans hw86.1, he87.trans hw87.2.1, he88.trans hw88.2.2.1, he106.trans hw106.2.2.2.1,
    he110.trans hw110.2.2.2.2.1, he111.trans hw111.2.2.2.2.2, Fin.sum_univ_three]
  have hc (k : Fin 86) : γ ⟨k.val,
    by omega⟩ = β (rCore ⟨3948 + k.val, by dsimp [posCoreWires]; omega⟩) := by
    dsimp only [γ, rComb, mk34_rComb112, mk34_rAct89]
    rw [show (⟨k.val,
      by omega⟩ : Fin ((86 + 3) + 23)) = Fin.castAdd 23 (Fin.castAdd 3 k) from Fin.ext rfl,
      QRegister.concat_apply_left, QRegister.concat_apply_left]
    simp [mk34_rCoreHi86]
  have hh (i : Fin 3) : γ ⟨86 + i.val, by omega⟩ = β (mk34_rHold3 rScr34 i) := by
    dsimp only [γ, rComb, mk34_rComb112, mk34_rAct89]
    rw [show (⟨86 + i.val,
      by omega⟩ : Fin ((86 + 3) + 23)) = Fin.castAdd 23 (Fin.natAdd 86 i) from Fin.ext rfl,
      QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hh0 : γ ⟨86, by decide⟩ = β (mk34_rHold3 rScr34 0) := hh 0
  have hh1 : γ ⟨87, by decide⟩ = β (mk34_rHold3 rScr34 1) := hh 1
  have hh2 : γ ⟨88, by decide⟩ = β (mk34_rHold3 rScr34 2) := hh 2
  rw [hh0, hh1, hh2]
  simp only [mk34_holdVec, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
    (by decide : (1 : ℕ) ≠ 0), (by decide : (2 : ℕ) ≠ 0), (by decide : (2 : ℕ) ≠ 1)]
  rw [hc ⟨0, by decide⟩, hc ⟨1, by decide⟩, hc ⟨2, by decide⟩, hc ⟨68, by decide⟩,
    hc ⟨15, by decide⟩, hc ⟨16, by decide⟩, hc ⟨17, by decide⟩, hc ⟨18, by decide⟩,
    hc ⟨19, by decide⟩, hc ⟨21, by decide⟩, hc ⟨22, by decide⟩, hc ⟨23, by decide⟩,
    hc ⟨24, by decide⟩, hc ⟨25, by decide⟩, hc ⟨26, by decide⟩, hc ⟨27, by decide⟩,
    hc ⟨28, by decide⟩, hc ⟨29, by decide⟩, hc ⟨30, by decide⟩, hc ⟨31, by decide⟩,
    hc ⟨32, by decide⟩, hc ⟨33, by decide⟩, hc ⟨34, by decide⟩, hc ⟨35, by decide⟩]
  rfl
theorem mk34_cComp3_eval_ket {n : ℕ} (rCore : QRegister posCoreWires n)
    (rScr34 : QRegister 34 n) (hCS : rCore.DisjointWires rScr34) (β : BitAssignment n)
    (h23 : ∀ j : Fin 23, β (mk34_rSub23 rScr34 j) = 0) :
    (mk34_cComp3 rCore rScr34 hCS).eval.1.mulVec (ket β) = ket (writeReg β (mk34_rHold3
    rScr34) (fun i ↦ β (mk34_rHold3 rScr34 i) + mk34_holdVec rCore β i)) := by
  dsimp only [mk34_cComp3]
  simp only [Circuit.eval_seq, Submonoid.coe_mul]
  refine hadamardReg_conj_phase_mulVec_ket (mk34_rHold3 rScr34)
    (mk34_cComp3Inner rCore rScr34 hCS).eval.1 (mk34_holdVec rCore β) β fun γHold ↦ ?_
  let β' := writeReg β (mk34_rHold3 rScr34) γHold
  have h23' : ∀ j : Fin 23, β' (mk34_rSub23 rScr34 j) = 0 := fun j ↦
    (writeReg_apply_of_not_mem β (mk34_rHold3 rScr34) γHold _ fun ⟨i, hi⟩ ↦
      ((mk34_rHold3_disjoint_rSub31 rScr34).compose_right _).ne i j hi).trans (h23 j)
  have hCoreEq : ∀ idx : Fin posCoreWires, β' (rCore idx) = β (rCore idx) := fun idx ↦
    writeReg_apply_of_not_mem β (mk34_rHold3 rScr34) γHold _ fun ⟨i, hi⟩ ↦
      (hCS.compose_right _).ne idx i hi.symm
  rw [mk34_cComp3Inner_eval_ket rCore rScr34 hCS β' h23',
    show mk34_holdVec rCore β' = mk34_holdVec rCore β from funext fun i ↦ by
      simp only [mk34_holdVec, hCoreEq]]
  exact congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β')
    (Finset.sum_congr rfl fun i _ ↦ by
      rw [show β' (mk34_rHold3 rScr34 i) = γHold i from writeReg_apply_reg β _ γHold i])

theorem mk34_hadamardReg_preserves_projZeroAll {w k n : ℕ} (rP : QRegister w n) (scr : Fin k →
    Wire n)
    (hdisj : ∀ i : Fin w, ∀ j : Fin k, rP i ≠ scr j) :
    projZeroAll k scr * ((hadamardReg rP).eval.1 * projZeroAll k scr) =
      (hadamardReg rP).eval.1 * projZeroAll k scr := by
  induction w with
  | zero =>
      dsimp only [hadamardReg]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul,
        MeasureBranchHadamardSem.projZeroAll_mul_self]
  | succ m ih =>
      let P := projZeroAll k scr
      let rTail := rP.slice 1 m (by omega)
      have hH : (hadamardReg rP).eval.1 = (hadamardReg rTail).eval.1 * (Circuit.H (rP 0)).eval.1 :=
        by
        simp [hadamardReg, rTail]
      have h0 : P * ((Circuit.H (rP 0)).eval.1 * P) = (Circuit.H (rP 0)).eval.1 * P := by
        apply MeasureBranchHadamardSem.matrix_ext_ket
        intro β
        rw [mul_mulVec_prog, mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin k, β (scr j) = 0
        · rw [ite_eq_left hz, MeasureBranchHadamardSem.ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
            Matrix.mulVec_smul, ket_projZeroAll,
            ite_eq_left (fun j ↦ (Function.update_of_ne (hdisj 0 j).symm ..).trans (hz j)),
            ket_projZeroAll,
            ite_eq_left (fun j ↦ (Function.update_of_ne (hdisj 0 j).symm ..).trans (hz j))]
        · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have hT : P * ((hadamardReg rTail).eval.1 * P) = (hadamardReg rTail).eval.1 * P :=
        ih rTail fun i j ↦ by
          dsimp only [rTail]
          rw [QRegister.slice_apply]
          exact hdisj ⟨1 + i.val, by omega⟩ j
      change P * ((hadamardReg rP).eval.1 * P) = (hadamardReg rP).eval.1 * P
      rw [hH, Matrix.mul_assoc (hadamardReg rTail).eval.1, ← h0,
        ← Matrix.mul_assoc (hadamardReg rTail).eval.1 P,
        ← Matrix.mul_assoc P ((hadamardReg rTail).eval.1 * P), hT,
          Matrix.mul_assoc (hadamardReg rTail).eval.1 P, h0]

attribute [local irreducible] mk34_cComp3

/- ## Section 4: Stage B (`mk34_cMidKickB` / `mk34_dMidKickB`, `B + 3` `TempAnd`s = `4 * B + 12 T`)
-/

/-- Total register width `(89 + (B + 1)) + (B + 4)` for Stage B (`1 ≤ B ≤ 27`). -/
abbrev mk34_mB (B : ℕ) : ℕ := (89 + (B + 1)) + (B + 4)

/-- Clean `(B + 4)`-wire prefix `rSub31[0..B+4)` (`rScr34[3..B+7)`) used by Stage B (`B ≤ 27`). -/
abbrev mk34_rSubB {n : ℕ} (B : ℕ) (_hB27 : B ≤ 27) (rScr34 : QRegister 34 n) : QRegister
    (B + 4) n := (mk34_rSub31 rScr34).slice 0 (B + 4) (by omega)

/-- Active `(89 + (B + 1))`-wire register `rAct89 ++ rOutTop` for Stage B. -/
abbrev mk34_rActB {n : ℕ} (B : ℕ)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr34)
    (hOutS : rOutTop.DisjointWires rScr34) : QRegister (89 + (B + 1)) n :=
  (mk34_rAct89 rCore rScr34 hCS).concat rOutTop
    (mk34_disj_concat_left _ (hCOut.compose_left _) (hOutS.compose_right _).symm)

/-- Combined `(mk34_mB B)`-wire register `rActB ++ rSubB` for Stage B. -/
def mk34_rCombB {n : ℕ} (B : ℕ) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr34)
    (hOutS : rOutTop.DisjointWires rScr34) : QRegister (mk34_mB B) n :=
  (mk34_rActB B rCore rOutTop rScr34 hCOut hCS hOutS).concat (mk34_rSubB B hB27 rScr34)
    (mk34_disj_concat_left _
      (mk34_disj_concat_left _ (((hCS.compose_left _).compose_right _).compose_right _)
        ((mk34_rHold3_disjoint_rSub31 rScr34).compose_right _))
      ((hOutS.compose_right _).compose_right _))
theorem mk34_tailScr_rCombB {n : ℕ} (B : ℕ) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr34)
    (hOutS : rOutTop.DisjointWires rScr34) :
    tailScr (mk34_rCombB B hB27 rCore rOutTop rScr34 hCOut hCS hOutS) (B + 4)
      (by dsimp [mk34_mB]; omega) = (mk34_rSubB B hB27 rScr34).wires := by
  funext j
  dsimp only [tailScr, mk34_rCombB]
  have h1 : (⟨(mk34_mB B - (B + 4)) + j.val, by dsimp [mk34_mB]; omega⟩ :
      Fin ((89 + (B + 1)) + (B + 4))) = Fin.natAdd (89 + (B + 1)) j := by
    ext
    dsimp [mk34_mB]
    omega
  rw [h1, QRegister.concat_apply_right]

/-- Diagonal leaf phase polynomial for Stage B on `mk34_mB B` wires. -/
def mk34_fLeafMidB (B : ℕ) (γ : BitAssignment (mk34_mB B)) : ZMod 2 :=
  γ ⟨0, by dsimp [mk34_mB]; omega⟩ +
  γ ⟨2, by dsimp [mk34_mB]; omega⟩ * γ ⟨0, by dsimp [mk34_mB]; omega⟩ +
  γ ⟨86, by dsimp [mk34_mB]; omega⟩ * γ ⟨0, by dsimp [mk34_mB]; omega⟩ +
  γ ⟨86, by dsimp [mk34_mB]; omega⟩ * γ ⟨85, by dsimp [mk34_mB]; omega⟩ +
  γ ⟨87, by dsimp [mk34_mB]; omega⟩ * γ ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩ +
  γ ⟨87, by dsimp [mk34_mB]; omega⟩ * γ ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩

/-- `0`-`T`, `0`-`.TOFF` diagonal `Z` + five-`CZ` leaf circuit for Stage B. -/
def mk34_cLeafMidBOn {n : ℕ} (B : ℕ) (rComb : QRegister (mk34_mB B) n) : Circuit n :=
  let w0 : Wire (mk34_mB B) := ⟨0, by dsimp [mk34_mB]; omega⟩
  let w2 : Wire (mk34_mB B) := ⟨2, by dsimp [mk34_mB]; omega⟩
  let w85 : Wire (mk34_mB B) := ⟨85, by dsimp [mk34_mB]; omega⟩
  let w86 : Wire (mk34_mB B) := ⟨86, by dsimp [mk34_mB]; omega⟩
  let w87 : Wire (mk34_mB B) := ⟨87, by dsimp [mk34_mB]; omega⟩
  let wd6 : Wire (mk34_mB B) := ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩
  let wd7 : Wire (mk34_mB B) := ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩
  Circuit.Z (rComb w0) ;;ᶜ
  asymMid_czCircuit (rComb w2) (rComb w0)
    (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [w2, w0]; omega))) ;;ᶜ
  asymMid_czCircuit (rComb w86) (rComb w0)
    (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [w86, w0]; omega))) ;;ᶜ
  asymMid_czCircuit (rComb w86) (rComb w85)
    (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [w86, w85]; omega))) ;;ᶜ
  asymMid_czCircuit (rComb w87) (rComb wd6)
    (rComb.wires.injective.ne (wire_ne_of_lt (by dsimp [w87, wd6]; omega))) ;;ᶜ
  asymMid_czCircuit (rComb w87) (rComb wd7)
    (rComb.wires.injective.ne (wire_ne_of_lt (by dsimp [w87, wd7]; omega)))

@[scoped simp]
theorem mk34_cLeafMidBOn_count_toff {n : ℕ} (B : ℕ) (rComb : QRegister (mk34_mB B) n) :
    (mk34_cLeafMidBOn B rComb).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_cLeafMidBOn, asymMid_czCircuit_count_toff, Circuit.Z, Circuit.single, Circuit.count]

@[scoped simp]
theorem mk34_cLeafMidBOn_count_t {n : ℕ} (B : ℕ) (rComb : QRegister (mk34_mB B) n) :
    (mk34_cLeafMidBOn B rComb).count PrimitiveGate.T = 0 := by
  simp [mk34_cLeafMidBOn, asymMid_czCircuit_count_t, Circuit.Z, Circuit.single, Circuit.count]

theorem mk34_cLeafMidBOn_eval_mbh_ket {n : ℕ} (B : ℕ) (rComb : QRegister (mk34_mB B) n)
    (β : BitAssignment n) :
    (mk34_cLeafMidBOn B rComb).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafMidB B (fun idx ↦ β (rComb idx))).val) •
        MeasureBranchHadamardSem.ket β := by
  rw [mbh_ket_eq_ket]
  dsimp only [mk34_cLeafMidBOn]
  simp only [asymMid_eval_seq_mulVec, Matrix.mulVec_smul, mk34_ket_Z, asymMid_ket_czCircuit,
    smul_smul, TempPhaseProg.neg_one_pow_zmod2_mul]
  congr 3
  dsimp only [mk34_fLeafMidB]
  ring
theorem mk34_fLeafMidB_eq_tailDecision (B : ℕ) (φ : BitAssignment (mk34_mB B))
    (b2 b1 s0 sr ih rz ge216 ge218 ge217 keepLt tSign : ZMod 2)
    (hs0 : φ ⟨0, by dsimp [mk34_mB]; omega⟩ = s0) (hb2 : φ ⟨2, by dsimp [mk34_mB]; omega⟩ = b2)
    (hrz : φ ⟨85, by dsimp [mk34_mB]; omega⟩ = rz)
    (hu1 : φ ⟨86, by dsimp [mk34_mB]; omega⟩ = (1 + b2) * (1 + b1))
    (hvL : φ ⟨87, by dsimp [mk34_mB]; omega⟩ =
      ((1 + b2) * (1 + b1)) * (((1 + sr) * (1 + ge218)) * (1 + (1 + s0) * ge216)))
    (hd6 : φ ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩ =
      (keepLt * (1 + s0 * ge217)) * (1 + (tSign + rz + s0)))
    (hd7 : φ ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩ =
      ih * (rz + (keepLt * (1 + s0 * ge217)) * (1 + (tSign + rz + s0)))) : mk34_fLeafMidB B φ =
      tailDecision11Bit b2 b1 s0 sr ih rz ge216 ge218 ge217 1 keepLt tSign := by
  dsimp only [mk34_fLeafMidB, tailDecision11Bit]
  rw [hs0, hb2, hrz, hu1, hvL, hd6, hd7]
  ring

theorem mk34_midpoint_lt_iff (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (keep : Fin 30 → ZMod 2) (outTop : Fin B → ZMod 2) :
    (bitsVal (fun j : Fin B ↦ keep ⟨(30 - B) + j.val, by omega⟩) < bitsVal outTop ∨
      (bitsVal (fun j : Fin B ↦ keep ⟨(30 - B) + j.val, by omega⟩) = bitsVal outTop ∧
        1 + keep ⟨29 - B, by omega⟩ = 1)) ↔
    bitsVal keep < 2 ^ (29 - B) + 2 ^ (30 - B) * bitsVal outTop := by
  let A := bitsVal (fun j : Fin B ↦ keep ⟨(30 - B) + j.val, by omega⟩)
  let T := bitsVal outTop
  let P := 2 ^ (29 - B)
  let L := bitsVal (fun i : Fin (29 - B) ↦ keep ⟨i.val, by omega⟩)
  let m := keep ⟨29 - B, by omega⟩
  have hPpos : 0 < P := Nat.two_pow_pos (29 - B)
  have h2P : 2 ^ (30 - B) = 2 * P := by rw [show 30 - B = (29 - B) + 1 by omega, pow_succ']
  have hL : L < P := bitsVal_lt_two_pow _
  have hm_lt : m.val < 2 := ZMod.val_lt m
  have hm0 : 1 + m = 1 ↔ m.val = 0 := by
    rcases zmod2_eq_zero_or_one m with hm | hm
    · simp [hm]
    · simp [hm]
  have htopEq : bitsVal (fun j : Fin (30 - (30 - B)) ↦ keep ⟨(30 - B) + j.val, by omega⟩) = A :=
    mk34_bitsVal_congr_len (by omega) _ _ fun _ ↦ rfl
  have hmid1 : bitsVal (fun j : Fin ((30 - B) - (29 - B)) ↦
      keep ⟨(29 - B) + j.val, by omega⟩) = m.val := by
    rw [mk34_bitsVal_congr_len (by omega : (30 - B) - (29 - B) = 1) _ (fun _ : Fin 1 ↦ m)
      (fun j ↦ congrArg keep (Fin.ext (by dsimp; omega)))]
    simp [bitsVal, m]
  have hkeepEq : bitsVal keep = L + P * m.val + (2 * P) * A := by
    rw [mk34_bitsVal_split_le (30 - B) (by omega) keep, htopEq,
      mk34_bitsVal_split_le (29 - B) (by omega) (fun i : Fin (30 - B) ↦ keep ⟨i.val, by omega⟩),
      hmid1, h2P]
  change (A < T ∨ (A = T ∧ 1 + m = 1)) ↔ bitsVal keep < P + 2 ^ (30 - B) * T
  rw [hm0, hkeepEq, h2P]
  rcases lt_trichotomy A T with hAT | hEq | hTA
  · have hmul := Nat.mul_le_mul_left (2 * P) hAT
    have hmP := Nat.mul_le_mul_left P (by omega : m.val ≤ 1)
    rw [Nat.mul_succ] at hmul
    exact ⟨fun _ ↦ by omega, fun _ ↦ Or.inl hAT⟩
  · rw [hEq]
    by_cases hmval : m.val = 0
    · simp [hmval, hL]
    · have hm1 : m.val = 1 := by omega
      simp [hm1]
  · have hmul := Nat.mul_le_mul_left (2 * P) hTA
    rw [Nat.mul_succ] at hmul
    refine ⟨fun h ↦ ?_, fun _ ↦ by omega⟩
    have hle : A ≤ T := h.elim le_of_lt fun h' ↦ le_of_eq h'.1
    omega
/-- Initializes `prev0` (`⟨90 + B, _⟩`) from `|0⟩` to `1 + keep[29 - B]` (`0` `T`). -/
def mk34_cInitPrev (B : ℕ) (_hB1 : 1 ≤ B) (hB27 : B ≤ 27) : CliffProg (mk34_mB B) :=
  .seq (.x ⟨90 + B, by dsimp [mk34_mB]; omega⟩)
    (.cnot ⟨38 + (29 - B), by dsimp [mk34_mB]; omega⟩ ⟨90 + B, by dsimp [mk34_mB]; omega⟩
      (wire_ne_of_lt (by dsimp; omega)))

/-- `3`-`TempAnd` context computing `d5` (`90 + 2 * B + 1`), `d6` (`90 + 2 * B + 2`), and `d7`
  (`90 + 2 * B + 3`). -/
def mk34_ctxTail3 (B : ℕ) : TempCtx (mk34_mB B) :=
  (ctxLitAnd (90 + 2 * B + 1) (by dsimp [mk34_mB]; omega)
    ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ false
    ⟨88, by dsimp [mk34_mB]; omega⟩ true
    (wire_ne_of_gt (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega)).append <|
  (mk34_ctxLitAndXor2 (90 + 2 * B + 2) (by dsimp [mk34_mB]; omega)
    ⟨90 + 2 * B + 1, by dsimp [mk34_mB]; omega⟩ false
    ⟨89 + B, by dsimp [mk34_mB]; omega⟩
    ⟨85, by dsimp [mk34_mB]; omega⟩
    ⟨0, by dsimp [mk34_mB]; omega⟩ true
    (wire_ne_of_gt (by dsimp; omega))
    (wire_ne_of_lt (by dsimp; omega))
    (wire_ne_of_lt (by dsimp; omega))
    (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)).append <|
  mk34_ctxLitAndXor1 (90 + 2 * B + 3) (by dsimp [mk34_mB]; omega)
    ⟨36, by dsimp [mk34_mB]; omega⟩ false
    ⟨85, by dsimp [mk34_mB]; omega⟩
    ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩ false
    (wire_ne_of_lt (by dsimp; omega))
    (wire_ne_of_gt (by dsimp; omega))
    (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)

/-- `(B + 3)`-`TempAnd` Stage-B context on `mk34_mB B` wires (`prev0` + `B`-bit comparator + `d5,
  d6, d7`). -/
def mk34_ctxMidB (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) : TempCtx (mk34_mB B) :=
  (ctxCliffAlloc (mk34_cInitPrev B hB1 hB27)).append <|
  (mk34_ctxLtCompLoop B (90 + B) (by dsimp [mk34_mB]; omega)
    (fun j ↦ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩)
    (fun j ↦ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
    (fun j ↦ wire_ne_of_lt (by dsimp; omega))
    (fun j ↦ by dsimp; omega)
    (fun j ↦ by dsimp; omega)).append <|
  mk34_ctxTail3 B

@[scoped simp] theorem mk34_ctxMidB_countTempAnd (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) :
    (mk34_ctxMidB B hB1 hB27).countTempAnd = B + 3 := by simp [mk34_ctxMidB, mk34_ctxTail3]

theorem mk34_ctxTail3_spec (B : ℕ) (q : Wire (mk34_mB B)) :
    ∃ sTail : BitAssignment (mk34_mB B) → BitAssignment (mk34_mB B),
      ScopedBlock (mk34_mB B) 3 sTail (.z q) ((mk34_ctxTail3 B).plug (.z q)) ∧
      (∀ (γ : BitAssignment (mk34_mB B)) (w : Wire (mk34_mB B)),
        w.val < 90 + 2 * B + 1 → sTail γ w = γ w) ∧ (∀ γ : BitAssignment (mk34_mB B),
        sTail γ ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩ =
          (γ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ * (1 + γ ⟨88, by dsimp [mk34_mB]; omega⟩)) *
          (1 + (γ ⟨89 + B, by dsimp [mk34_mB]; omega⟩ + γ ⟨85, by dsimp [mk34_mB]; omega⟩ +
            γ ⟨0, by dsimp [mk34_mB]; omega⟩))) ∧ (∀ γ : BitAssignment (mk34_mB B),
        sTail γ ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩ = γ ⟨36, by dsimp [mk34_mB]; omega⟩ *
          (γ ⟨85, by dsimp [mk34_mB]; omega⟩ + (γ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ *
              (1 + γ ⟨88, by dsimp [mk34_mB]; omega⟩)) *
            (1 + (γ ⟨89 + B, by dsimp [mk34_mB]; omega⟩ + γ ⟨85, by dsimp [mk34_mB]; omega⟩ +
              γ ⟨0, by dsimp [mk34_mB]; omega⟩)))) := by
  simp only [mk34_ctxTail3, TempCtx.append_plug, mk34_ctxLitAnd_plug, mk34_ctxLitAndXor2_plug,
    mk34_ctxLitAndXor1_plug]
  refine ⟨_, ((ScopedBlock.withLitAnd_block (M := mk34_mB B) (90 + 2 * B + 1) _ _ _ _ _ _ _ _
    ((ScopedBlock.withLitAndXor2_block (M := mk34_mB B) (90 + 2 * B + 2) _ _ _ _ _ _ _ _ _ _ _ _ _ _
      ((ScopedBlock.withLitAndXor1_block (M := mk34_mB B) (90 + 2 * B + 3) _ _ _ _ _ _ _ _ _ _ _
        (ScopedBlock.z_kick q)).cast_rem
          (rem₂ := mk34_mB B - (90 + 2 * B + 2 + 1)) (by omega))).cast_rem
        (rem₂ := mk34_mB B - (90 + 2 * B + 1 + 1)) (by omega))).cast_rem
      (rem₂ := 3) (by dsimp [mk34_mB]; omega)),
    fun γ w hw ↦ ?_, fun γ ↦ ?_, fun γ ↦ ?_⟩
  · dsimp only [Function.comp_apply, id_eq]
    rw [stepLitAndXor1_of_ne (by omega), stepLitAndXor2_of_ne (by omega),
      stepLitAnd_of_ne (by omega)]
  · dsimp only [Function.comp_apply, id_eq]
    rw [stepLitAndXor1_of_ne (by dsimp; omega), stepLitAndXor2_eq (by dsimp),
      stepLitAnd_eq (by dsimp),
      stepLitAnd_of_ne (by dsimp; omega), stepLitAnd_of_ne (by dsimp; omega),
      stepLitAnd_of_ne (by dsimp; omega), litVal_false, litVal_true, litVal_false, litVal_true]
  · dsimp only [Function.comp_apply, id_eq]
    rw [stepLitAndXor1_eq (by dsimp), stepLitAndXor2_of_ne (by dsimp; omega),
      stepLitAnd_of_ne (by dsimp; omega), stepLitAndXor2_of_ne (by dsimp; omega),
      stepLitAnd_of_ne (by dsimp; omega), stepLitAndXor2_eq (by dsimp), stepLitAnd_eq (by dsimp),
      stepLitAnd_of_ne (by dsimp; omega), stepLitAnd_of_ne (by dsimp; omega),
      stepLitAnd_of_ne (by dsimp; omega), litVal_false, litVal_false, litVal_false,
      litVal_true, litVal_false, litVal_true]
/-- Leaf wire specification for `mk34_ctxMidB` on active wires and `(d6, d7)`. -/
def mk34_midBSpec (B : ℕ) (φ γ : BitAssignment (mk34_mB B)) (keepLt : ZMod 2) : Prop :=
  let s0 := γ ⟨0, by dsimp [mk34_mB]; omega⟩
  let rz := γ ⟨85, by dsimp [mk34_mB]; omega⟩
  let ih := γ ⟨36, by dsimp [mk34_mB]; omega⟩
  let d3 := γ ⟨88, by dsimp [mk34_mB]; omega⟩
  let tSign := γ ⟨89 + B, by dsimp [mk34_mB]; omega⟩
  let d6 := (keepLt * (1 + d3)) * (1 + (tSign + rz + s0))
  (∀ w : Wire (mk34_mB B), w.val < 90 + B → φ w = γ w) ∧
  φ ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩ = d6 ∧
  φ ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩ = ih * (rz + d6)

theorem mk34_ctxMidB_scoped_of_wire (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (q : Wire (mk34_mB B)) :
    ∃ sMid : BitAssignment (mk34_mB B) → BitAssignment (mk34_mB B),
      ScopedBlock (mk34_mB B) (B + 4) sMid (.z q) ((mk34_ctxMidB B hB1 hB27).plug (.z q)) ∧
      ∀ γ : BitAssignment (mk34_mB B), cleanRem (mk34_mB B) (B + 4) γ → mk34_midBSpec B (sMid γ) γ
          (if bitsVal (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) <
              2 ^ (29 - B) + 2 ^ (30 - B) *
                bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
           then 1 else 0) := by
  obtain ⟨sTail, hTail, hTailBelow, hTailD6, hTailD7⟩ := mk34_ctxTail3_spec B q
  obtain ⟨setupLt, hLt, hSpecLt⟩ :=
    ScopedBlock.withLtCompLoop_block (M := mk34_mB B) B (90 + B) (by dsimp [mk34_mB]; omega)
      (fun j ↦ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩)
      (fun j ↦ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
      (fun j ↦ wire_ne_of_lt (by dsimp; omega))
      (fun j ↦ by dsimp; omega)
      (fun j ↦ by dsimp; omega)
      (.z q) ((mk34_ctxTail3 B).plug (.z q)) sTail
      (hTail.cast_rem (by dsimp [mk34_mB]; omega))
  simp only [mk34_ctxMidB, TempCtx.append_plug, ctxCliffAlloc_plug, mk34_ctxLtCompLoop_plug]
  have hSuppInit : (mk34_cInitPrev B hB1 hB27).SupportsBelow (mk34_mB B - (B + 3)) := by
    dsimp [mk34_cInitPrev, CliffProg.SupportsBelow, mk34_mB]
    exact ⟨by omega, by omega, by omega⟩
  refine ⟨_, ScopedBlock.withCliffAlloc_block (M := mk34_mB B) (rem := B + 4) (remIn := B + 3)
    (by dsimp [mk34_mB]; omega) (by omega) (mk34_cInitPrev B hB1 hB27) hSuppInit
    (hLt.cast_rem (by dsimp [mk34_mB]; omega)), fun γ hγ ↦ ?_⟩
  let γ₁ := (mk34_cInitPrev B hB1 hB27).eval γ
  have hγ₁_ne : ∀ w : Wire (mk34_mB B), w.val ≠ 90 + B → γ₁ w = γ w := fun w hw ↦ by
    dsimp only [γ₁, mk34_cInitPrev, CliffProg.eval]
    rw [Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)),
      Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h))]
  have hγ₁_prev : γ₁ ⟨90 + B, by dsimp [mk34_mB]; omega⟩ =
      1 + γ ⟨38 + (29 - B), by dsimp [mk34_mB]; omega⟩ := by
    dsimp only [γ₁, mk34_cInitPrev, CliffProg.eval]
    rw [Function.update_self, Function.update_self,
      Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)),
      hγ _ (by dsimp [mk34_mB]; omega), zero_add]
  obtain ⟨_, hLtBelow, hLtCarry⟩ := hSpecLt γ₁ fun w hw ↦
    (hγ₁_ne w (by dsimp [mk34_mB] at hw; omega)).trans (hγ w (by dsimp [mk34_mB] at hw ⊢; omega))
  have hsBelow : ∀ w : Wire (mk34_mB B), w.val < 90 + B → setupLt γ₁ w = γ w := fun w hw ↦
    (hLtBelow w hw).trans (hγ₁_ne w (by omega))
  have hA_eq : (fun j : Fin B ↦ γ₁ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩) =
      (fun j : Fin B ↦ γ ⟨38 + ((30 - B) + j.val), by dsimp [mk34_mB]; omega⟩) :=
    funext fun j ↦ (hγ₁_ne _ (by dsimp; omega)).trans (congrArg γ (Fin.ext (by dsimp; omega)))
  have hB_eq : (fun j : Fin B ↦ γ₁ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) =
      (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) :=
    funext fun j ↦ hγ₁_ne _ (by dsimp; omega)
  have hIff : setupLt γ₁ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ = 1 ↔
      bitsVal (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) <
        2 ^ (29 - B) + 2 ^ (30 - B) *
          bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) := by
    rw [show (⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ : Wire (mk34_mB B)) =
        ⟨(90 + B) + B, by dsimp [mk34_mB]; omega⟩ from Fin.ext (by dsimp; omega),
      hLtCarry, hA_eq, hB_eq, hγ₁_prev]
    exact mk34_midpoint_lt_iff B hB1 hB27
      (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩)
      (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
  have hKeepEq : setupLt γ₁ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ =
      (if bitsVal (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) <
          2 ^ (29 - B) + 2 ^ (30 - B) *
            bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
       then 1 else 0) := by
    rcases zmod2_eq_zero_or_one (setupLt γ₁ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩) with hs | hs
    · simp only [hs, mt hIff.mpr (by simp [hs]), ↓reduceIte]
    · simp only [hs, hIff.mp hs, ↓reduceIte]
  dsimp only [Function.comp_apply, mk34_midBSpec]
  refine ⟨fun w hw ↦ (hTailBelow (setupLt γ₁) w (by omega)).trans (hsBelow w hw), ?_, ?_⟩
  · rw [hTailD6 (setupLt γ₁), hKeepEq, hsBelow _ (by dsimp; omega), hsBelow _ (by dsimp; omega),
      hsBelow _ (by dsimp; omega), hsBelow _ (by dsimp; omega)]
  · rw [hTailD7 (setupLt γ₁), hsBelow _ (by dsimp; omega), hsBelow _ (by dsimp; omega), hKeepEq,
      hsBelow _ (by dsimp; omega), hsBelow _ (by dsimp; omega), hsBelow _ (by dsimp; omega)]
theorem mk34_ctxMidB_fwdBits_fLeaf (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (γ : BitAssignment (mk34_mB B)) (hγ : cleanRem (mk34_mB B) (B + 4) γ)
    (b1 sr ge216 ge218 ge217 : ZMod 2) (hu1 : γ ⟨86, by dsimp [mk34_mB]; omega⟩ =
      (1 + γ ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + b1)) (hvL : γ ⟨87, by dsimp [mk34_mB]; omega⟩ =
      ((1 + γ ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + b1)) *
        (((1 + sr) * (1 + ge218)) * (1 + (1 + γ ⟨0, by dsimp [mk34_mB]; omega⟩) * ge216)))
    (hd3 : γ ⟨88, by dsimp [mk34_mB]; omega⟩ = γ ⟨0, by dsimp [mk34_mB]; omega⟩ * ge217) :
    mk34_fLeafMidB B ((mk34_ctxMidB B hB1 hB27).fwdBits γ) = tailDecision11Bit
        (γ ⟨2, by dsimp [mk34_mB]; omega⟩) b1 (γ ⟨0, by dsimp [mk34_mB]; omega⟩)
        sr (γ ⟨36, by dsimp [mk34_mB]; omega⟩) (γ ⟨85, by dsimp [mk34_mB]; omega⟩)
        ge216 ge218 ge217 1
        (if bitsVal (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) <
            2 ^ (29 - B) + 2 ^ (30 - B) *
              bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) then 1 else 0)
        (γ ⟨89 + B, by dsimp [mk34_mB]; omega⟩) := by
  have hWire : ∀ q : Wire (mk34_mB B),
    ∃ sMid : BitAssignment (mk34_mB B) → BitAssignment (mk34_mB B),
      (mk34_ctxMidB B hB1 hB27).fwdBits γ q = sMid γ q ∧ mk34_midBSpec B (sMid γ) γ
        (if bitsVal (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) <
            2 ^ (29 - B) + 2 ^ (30 - B) *
              bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
         then 1 else 0) := fun q ↦ by
    obtain ⟨sMid, hB, hSpec⟩ := mk34_ctxMidB_scoped_of_wire B hB1 hB27 q
    exact ⟨sMid, ((mk34_ctxMidB B hB1 hB27).plug_evalSign (.z q) γ).symm.trans (hB.sign γ hγ),
      hSpec γ hγ⟩
  have hLow : ∀ (k : ℕ) (hk : k < 89),
      (mk34_ctxMidB B hB1 hB27).fwdBits γ ⟨k, by dsimp [mk34_mB]; omega⟩ =
        γ ⟨k, by dsimp [mk34_mB]; omega⟩ := fun k hk ↦ by
    obtain ⟨_, he, hw⟩ := hWire ⟨k, by dsimp [mk34_mB]; omega⟩
    exact he.trans (hw.1 _ (by dsimp; omega))
  obtain ⟨_, hed6, hwd6⟩ := hWire ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩
  obtain ⟨_, hed7, hwd7⟩ := hWire ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩
  exact mk34_fLeafMidB_eq_tailDecision B ((mk34_ctxMidB B hB1 hB27).fwdBits γ)
    _ _ _ _ _ _ _ _ _ _ _
    (hLow 0 (by decide)) (hLow 2 (by decide)) (hLow 85 (by decide))
    ((hLow 86 (by decide)).trans hu1) ((hLow 87 (by decide)).trans hvL)
    (hd3 ▸ hed6.trans hwd6.2.1) (hd3 ▸ hed7.trans hwd7.2.2)
/-- Plugged `TempPhaseProg (mk34_mB B)` witness for Stage B (`mk34_ctxMidB`). -/
def mk34_pMidB (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) : TempPhaseProg (mk34_mB B) :=
  (mk34_ctxMidB B hB1 hB27).plug (.z ⟨0, by dsimp [mk34_mB]; omega⟩)

theorem mk34_pMidB_eq (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) :
    (mk34_ctxMidB B hB1 hB27).plug (.z ⟨0, by dsimp [mk34_mB]; omega⟩) =
      mk34_pMidB B hB1 hB27 := rfl

theorem mk34_pMidB_valid_and_bits (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) : ValidCleanRem
    (mk34_mB B) (B + 4) (mk34_pMidB B hB1 hB27) ∧ (∀ γ : BitAssignment (mk34_mB B), cleanRem
    (mk34_mB B) (B + 4) γ → (mk34_pMidB B hB1 hB27).evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxMidB_scoped_of_wire B hB1 hB27 ⟨0, by dsimp [mk34_mB]; omega⟩
  exact ⟨hB.valid, hB.bits⟩

/-- Stage B reversible `Circuit n` (`B + 3` Toffoli pairs + diagonal `Z` + five `CZ`s). -/
def mk34_cMidKickB {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr34)
    (hOutS : rOutTop.DisjointWires rScr34) : Circuit n :=
  let rComb := mk34_rCombB B hB27 rCore rOutTop rScr34 hCOut hCS hOutS
  mk34_ctxToToff rComb (mk34_cLeafMidBOn B rComb) (mk34_ctxMidB B hB1 hB27)

attribute [local irreducible] mk34_ctxMidB

theorem mk34_cMidKickB_eval_ket_raw {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr34)
    (hOutS : rOutTop.DisjointWires rScr34) (β : BitAssignment n)
    (hSubB : ∀ j : Fin (B + 4), β (mk34_rSubB B hB27 rScr34 j) = 0) :
    let rComb := mk34_rCombB B hB27 rCore rOutTop rScr34 hCOut hCS hOutS
    (mk34_cMidKickB B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafMidB B
        ((mk34_ctxMidB B hB1 hB27).fwdBits (fun idx ↦ β (rComb idx)))).val) • ket β := by
  intro rComb
  have hcr : cleanRem (mk34_mB B) (B + 4) (fun idx ↦ β (rComb idx)) :=
    mk34_cleanRem_of_tailScr rComb (by dsimp [mk34_mB]; omega) fun j ↦ by
      rw [congrFun (mk34_tailScr_rCombB B hB27 rCore rOutTop rScr34 hCOut hCS hOutS) j]
      exact hSubB j
  rw [mk34_cMidKickB, ← mbh_ket_eq_ket,
    mk34_ctxToToff_eval_ket rComb _ _ (mk34_cLeafMidBOn_eval_mbh_ket B rComb)
      ⟨0, by dsimp [mk34_mB]; omega⟩ (mk34_ctxMidB B hB1 hB27) β,
    mk34_pMidB_eq, (mk34_pMidB_valid_and_bits B hB1 hB27).2 _ hcr,
    mk34_writeRegProg_self, mbh_ket_eq_ket]

theorem mk34_cMidKickB_eval_ket {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤
    27) (rCore : QRegister posCoreWires n)
    (rOutTop : QRegister (B +
      1) n) (rScr34 : QRegister 34 n) (hCOut : rCore.DisjointWires rOutTop) (hCS :
    rCore.DisjointWires rScr34) (hOutS : rOutTop.DisjointWires rScr34) (β : BitAssignment n)
      (hHold : ∀ i : Fin 3, β
    (mk34_rHold3 rScr34 i) = mk34_holdVec rCore β i) (hSubB : ∀ j : Fin (B + 4),
      β (mk34_rSubB B hB27 rScr34 j) = 0) :
    (mk34_cMidKickB B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^
    (midKickPhaseBitB B rCore rOutTop β).val) • ket β := by
  rw [mk34_cMidKickB_eval_ket_raw B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS β hSubB]
  congr 3
  let rComb := mk34_rCombB B hB27 rCore rOutTop rScr34 hCOut hCS hOutS
  let γ : BitAssignment (mk34_mB B) := fun idx ↦ β (rComb idx)
  have hcr : cleanRem (mk34_mB B) (B + 4) γ :=
    mk34_cleanRem_of_tailScr rComb (by dsimp [mk34_mB]; omega) fun j ↦ by
      rw [congrFun (mk34_tailScr_rCombB B hB27 rCore rOutTop rScr34 hCOut hCS hOutS) j]
      exact hSubB j
  have hc (k : Fin 86) : γ ⟨k.val, by dsimp [mk34_mB]; omega⟩ =
      β (rCore ⟨3948 + k.val, by dsimp [posCoreWires]; omega⟩) := by
    dsimp only [γ, rComb, mk34_rCombB]
    have h1 : (⟨k.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
        Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.castAdd 3 k)) := Fin.ext rfl
    rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
    simp [mk34_rCoreHi86]
  have hh (i : Fin 3) : γ ⟨86 + i.val, by dsimp [mk34_mB]; omega⟩ = mk34_holdVec rCore β i := by
    dsimp only [γ, rComb, mk34_rCombB]
    have h1 : (⟨86 + i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
        Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.natAdd 86 i)) := Fin.ext rfl
    rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_right]
    exact hHold i
  have ho (j : Fin (B + 1)) : γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩ = β (rOutTop j) := by
    dsimp only [γ, rComb, mk34_rCombB]
    have h1 : (⟨89 + j.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
        Fin.castAdd (B + 4) (Fin.natAdd 89 j) := Fin.ext rfl
    rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hu1 : γ ⟨86, by dsimp [mk34_mB]; omega⟩ =
      (1 + γ ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + β (rCore ⟨3949, by decide⟩)) := by
    rw [hc ⟨2, by decide⟩]
    simpa only [Fin.val_zero, add_zero, mk34_holdVec, ↓reduceIte] using hh 0
  have hvL : γ ⟨87, by dsimp [mk34_mB]; omega⟩ =
      ((1 + γ ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + β (rCore ⟨3949, by decide⟩))) *
        (((1 + β (rCore ⟨4016, by decide⟩)) *
            (1 + ge218Bit (β (rCore ⟨3969, by decide⟩)) (β (rCore ⟨3970, by decide⟩))
              (β (rCore ⟨3971, by decide⟩)) (β (rCore ⟨3972, by decide⟩))
              (β (rCore ⟨3973, by decide⟩)) (β (rCore ⟨3974, by decide⟩))
              (β (rCore ⟨3975, by decide⟩)))) * (1 + (1 + γ ⟨0, by dsimp [mk34_mB]; omega⟩) *
            ge216Bit (β (rCore ⟨3963, by decide⟩)) (β (rCore ⟨3964, by decide⟩))
              (β (rCore ⟨3965, by decide⟩)) (β (rCore ⟨3966, by decide⟩))
              (β (rCore ⟨3967, by decide⟩)))) := by
    rw [hc ⟨2, by decide⟩, hc ⟨0, by decide⟩]
    simpa only [Fin.val_one, (by decide : (1 : ℕ) ≠ 0), ↓reduceIte, mk34_holdVec] using hh 1
  have hd3 : γ ⟨88, by dsimp [mk34_mB]; omega⟩ = γ ⟨0, by dsimp [mk34_mB]; omega⟩ *
        ge217Bit (β (rCore ⟨3976, by decide⟩)) (β (rCore ⟨3977, by decide⟩))
          (β (rCore ⟨3978, by decide⟩)) (β (rCore ⟨3979, by decide⟩))
          (β (rCore ⟨3980, by decide⟩)) (β (rCore ⟨3981, by decide⟩))
          (β (rCore ⟨3982, by decide⟩)) (β (rCore ⟨3983, by decide⟩)) := by
    rw [hc ⟨0, by decide⟩]
    simpa only [Fin.val_two, (by decide : (2 : ℕ) ≠ 0), (by decide : (2 : ℕ) ≠ 1),
      ↓reduceIte, mk34_holdVec] using hh 2
  change mk34_fLeafMidB B ((mk34_ctxMidB B hB1 hB27).fwdBits γ) = _
  rw [mk34_ctxMidB_fwdBits_fLeaf B hB1 hB27 γ hcr _ _ _ _ _ hu1 hvL hd3,
    hc ⟨2, by decide⟩, hc ⟨0, by decide⟩, hc ⟨36, by decide⟩, hc ⟨85, by decide⟩,
    show (fun k : Fin 30 ↦ γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) =
        fun k : Fin 30 ↦ β (rCore ⟨3986 + k.val, by dsimp [posCoreWires]; omega⟩) from
      funext fun k ↦ (hc ⟨38 + k.val, by omega⟩).trans
        (congrArg (fun idx ↦ β (rCore idx)) (Fin.ext (by dsimp; omega))),
    show (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) =
        fun j : Fin B ↦ β (rOutTop ⟨j.val, by omega⟩) from funext fun j ↦ ho ⟨j.val, by omega⟩,
    ho ⟨B, by omega⟩]
  rfl

attribute [local irreducible] mk34_cMidKickB

/- ## Section 5: Top-Level `34`-Wire 3-Stage Mid-Kick Subroutine (`cKickZeroSub34` /
`dKickZeroSub34Dyn`) -/

/-- Top-level `34`-wire clean-ancilla reversible `Circuit n` for the 3-stage mid-phase kickback. -/
def cKickZeroSub34 {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr34)
    (hOutS : rOutTop.DisjointWires rScr34) : Circuit n :=
  mk34_cComp3 rCore rScr34 hCS ;;ᶜ
    mk34_cMidKickB B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS ;;ᶜ
    mk34_cComp3 rCore rScr34 hCS

theorem cKickZeroSub34_eval_mulVec_ket {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤
    27) (rCore : QRegister posCoreWires n)
    (rOutTop : QRegister (B +
      1) n) (rScr34 : QRegister 34 n) (hCOut : rCore.DisjointWires rOutTop) (hCS :
    rCore.DisjointWires rScr34) (hOutS : rOutTop.DisjointWires rScr34) (δ : BitAssignment n)
      (hScr0 : ∀ s : Fin 34, δ
    (rScr34 s) =
      0) : (cKickZeroSub34 B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS).eval.1.mulVec (ket δ) =
      ((-1 : ℂ)
    ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ := by
  let δ₁ := writeReg δ (mk34_rHold3 rScr34) (mk34_holdVec rCore δ)
  have hHold0 : ∀ i : Fin 3, δ (mk34_rHold3 rScr34 i) = 0 := fun i ↦ by
    dsimp only [mk34_rHold3]
    exact (congrArg δ (QRegister.slice_apply _ _ _ _ _)).trans (hScr0 ⟨0 + i.val, by omega⟩)
  have hSub31_0 : ∀ j : Fin 31, δ (mk34_rSub31 rScr34 j) = 0 := fun j ↦ by
    dsimp only [mk34_rSub31]
    exact (congrArg δ (QRegister.slice_apply _ _ _ _ _)).trans (hScr0 ⟨3 + j.val, by omega⟩)
  have hSub31_δ₁ : ∀ j : Fin 31, δ₁ (mk34_rSub31 rScr34 j) = 0 := fun j ↦
    (writeReg_apply_of_not_mem δ (mk34_rHold3 rScr34) _ _ fun ⟨i, hi⟩ ↦
      (mk34_rHold3_disjoint_rSub31 rScr34).ne i j hi).trans (hSub31_0 j)
  have hSub23 : ∀ (ξ : BitAssignment n), (∀ j : Fin 31, ξ (mk34_rSub31 rScr34 j) = 0) →
      ∀ j : Fin 23, ξ (mk34_rSub23 rScr34 j) = 0 := fun ξ h j ↦ by
    dsimp only [mk34_rSub23]
    exact (congrArg ξ (QRegister.slice_apply _ _ _ _ _)).trans (h ⟨0 + j.val, by omega⟩)
  have hCore_δ₁ : ∀ idx : Fin posCoreWires, δ₁ (rCore idx) = δ (rCore idx) := fun idx ↦
    writeReg_apply_of_not_mem δ (mk34_rHold3 rScr34) _ _ fun ⟨i, hi⟩ ↦
      (hCS.compose_right _).ne idx i hi.symm
  have hOut_δ₁ : ∀ idx : Fin (B + 1), δ₁ (rOutTop idx) = δ (rOutTop idx) := fun idx ↦
    writeReg_apply_of_not_mem δ (mk34_rHold3 rScr34) _ _ fun ⟨i, hi⟩ ↦
      (hOutS.compose_right _).ne idx i hi.symm
  have hHold_δ₁ : ∀ i : Fin 3, δ₁ (mk34_rHold3 rScr34 i) = mk34_holdVec rCore δ₁ i := fun i ↦ by
    rw [show mk34_holdVec rCore δ₁ = mk34_holdVec rCore δ from funext fun _ ↦
      by simp only [mk34_holdVec, hCore_δ₁]]
    exact writeReg_apply_reg δ (mk34_rHold3 rScr34) _ i
  dsimp only [cKickZeroSub34]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [mk34_cComp3_eval_ket rCore rScr34 hCS δ (hSub23 δ hSub31_0),
    show writeReg δ (mk34_rHold3 rScr34) (fun i ↦
      δ (mk34_rHold3 rScr34 i) + mk34_holdVec rCore δ i) = δ₁
      from congrArg (writeReg δ (mk34_rHold3 rScr34)) (funext fun i ↦ by rw [hHold0 i, zero_add]),
    mk34_cMidKickB_eval_ket B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS δ₁ hHold_δ₁ (fun j ↦ by
      dsimp only [mk34_rSubB]
      exact (congrArg δ₁ (QRegister.slice_apply _ _ _ _ _)).trans (hSub31_δ₁ ⟨0 + j.val,
        by omega⟩)),
    show midKickPhaseBitB B rCore rOutTop δ₁ = midKickPhaseBitB B rCore rOutTop δ by
      simp only [midKickPhaseBitB, hCore_δ₁, hOut_δ₁],
    Matrix.mulVec_smul, mk34_cComp3_eval_ket rCore rScr34 hCS δ₁ (hSub23 δ₁ hSub31_δ₁)]
  refine congrArg _ (congrArg ket (funext fun q ↦ ?_))
  by_cases hq : q ∈ Set.range (mk34_rHold3 rScr34).wires
  · obtain ⟨i, rfl⟩ := hq
    rw [writeReg_apply_reg, hHold_δ₁ i, CharTwo.add_self_eq_zero, hHold0 i]
  · exact (writeReg_apply_of_not_mem δ₁ (mk34_rHold3 rScr34) _ q hq).trans
      (writeReg_apply_of_not_mem δ (mk34_rHold3 rScr34) _ q hq)
set_option maxRecDepth 512

end ConfigMidKickSub33

end MidKickSub33
end
end MidKickSub33

section MidK6Sub126
local instance (priority := 1000000) instNeZeroTwoPow_MidK6Sub126 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `126`-Wire Unbuffered `MidK6` Oracle (`MidK6Sub126`)

Specializes the `K = 6` `4`-way row-palette QROM phase oracle to:
- `H = 0` (`126 ≤ mClean`, all `1,728` buffer bits XORed onto dirty `rCore[0..1728)` and
  restored via `k6_fixUnbufDyn` + `k6_cCzSweep27Raw`, eliminating `rBufClean` wires above
  `rClean[125]`),
- `B - 3` active pre-mux / stream columns (`col = 0, 1` and `col ∈ [2 + (30 - B), 27)` for
  `6 ≤ B ≤ 27`), leaving `rClean[64 .. 64 + (30 - B))` (`≥ 3` wires) untouched at `|0⟩`
  through Stage 5 so `rScr34 := rClean[64..67) ++ rClean[95..126)` supplies `34` clean
  ancillas to `MidKickSub33.dKickZeroSub34Dyn` (`196 + 4 * B` `T`, `0` `.TOFF`).

Total `.T` count: `≤ 5900 + 260 * B` (`{24: 12140, 25: 12400, 26: 12660, 27: 12920}`),
`0` `.TOFF`, realizing `diagSignUnitary (k6MidPhaseBitSpecB B hB1 hB29 slot2SwappedTo0)`
on `rCore.concat rOrbit16 hCO` with clean workspace `rClean`.
-/

public section

namespace MidK6Sub126

section ConfigMidK6Sub126

set_option maxRecDepth 8000

local instance (priority :=
  1000000) instLoc_MidK6Sub126_1InstNeZeroTwoPowMidK6Sub126 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open OctahedralOrbit Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open StreamingBchComparator
open PosSlots24CompactPhase288
open PosSlots24SemanticBridge
open PrunedQromLookup
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open PosSlots24PartnerMux288 (sandPhase18 orbitRankFin16)
open PosSlots24PartnerMux288 (val_orbitRankFin16)
open MidKickSub33

attribute [local irreducible]
  k6SuperRow w128OrbitBiasedQ30 k6ReconTop6BitBool pos24TailMag30 pos24TailSign k6BitNat
  k6SubGatesPalBit k6Pal24Bit k6P0Bit k6P1Bit k6_oneHot4Val prunedEffIdx cKickZeroSub34
  phaseLookupPrunedCircuit hadamardReg
  p2t_cPhaseMuxCol64 k6LoadTreeCircuit k6_cOneHot4Raw
  k6_cPhaseMux4All6Raw k6_cXorDiffTop6Raw k6_cCzCol64Raw k6_cCzSweep27Raw

/-- `B`-bit midpoint magnitude threshold reconstructed from the top `B` magnitude bits of a
`31`-bit `K = 6` word `w31`. -/
def k6MidMagThresholdB (B : ℕ) (_hB1 : 1 ≤ B) (hB29 : B ≤ 29) (w31 : BitAssignment 31) : ℕ :=
  2 ^ (29 - B) + 2 ^ (30 - B) * bitsVal (fun j : Fin B ↦ w31 ⟨(30 - B) + j.val, by omega⟩)

/-- Effective `K = 6` mid-phase Boolean specification at `B`-bit midpoint precision on
`rCore.concat rOrbit16`. -/
noncomputable def k6MidPhaseBitSpecB (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤ 29)
    (_slot2SwappedTo0 : Bool) (x : Fin (2 ^ (posCoreWires + 16))) : Bool :=
  let βL := unpackCoreBits x
  let idx := unpackOrbitIdx x
  let rCoreL := QRegExt.ofFin posCoreWires
  let w31 := k6EffWord31 idx
  tailDecisionBool
    (βL (wSlot2Core rCoreL) == 1)
    (βL (wSlot1Core rCoreL) == 1)
    (βL (wSlot0Core rCoreL) == 1)
    (βL (wSubReject rCoreL) == 1)
    (βL (wIsHead rCoreL) == 1)
    (βL (wRejectZero rCoreL) == 1)
    (decide (regVal (rNucIdx rCoreL) βL < 216))
    (decide (regVal (rAnchorIdx rCoreL) βL < 218))
    (decide (regVal (rPartnerIdx rCoreL) βL < 217))
    (decide (regVal (rTailKeep30 rCoreL) βL < k6MidMagThresholdB B hB1 hB29 w31))
    (w31 ⟨30, by decide⟩ == 1)

theorem sandPhase18_k6MidPhaseBitSpecB_eq (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤
    29) (slot2SwappedTo0 : Bool) : sandPhase18
    slot2SwappedTo0 (k6MidPhaseBitSpecB B hB1 hB29 slot2SwappedTo0) =
      sandPhase18 slot2SwappedTo0 (midPhaseBitSpec
    slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 hB29)) := by
  funext w
  dsimp only [sandPhase18]
  let bits := basisBits (posCoreWires + 18) w
  let βC : BitAssignment posCoreWires := fun i ↦ bits (Fin.castAdd 18 i)
  let βP : BitAssignment 18 := fun j ↦ bits (Fin.natAdd posCoreWires j)
  let rk := orbitRankFin16 slot2SwappedTo0 βC βP
  let x := (basisBitsEquiv (posCoreWires + 16)).symm fun m ↦
    if hm : m.val < posCoreWires then βC ⟨m.val, hm⟩
    else basisBits 16 rk ⟨m.val - posCoreWires, by omega⟩
  have hUnpack : unpackOrbitIdx x = rk := by
    dsimp only [unpackOrbitIdx]
    rw [show (fun j : Fin 16 ↦ basisBits (posCoreWires + 16) x (Fin.natAdd posCoreWires j)) =
        basisBits 16 rk from funext fun j ↦ by
      change (basisBitsEquiv (posCoreWires + 16)) x (Fin.natAdd posCoreWires j) = _
      rw [(basisBitsEquiv (posCoreWires + 16)).apply_symm_apply,
        dite_eq_right (by simp [Fin.natAdd] : ¬ (Fin.natAdd posCoreWires j).val < posCoreWires)]
      exact congrArg (basisBits 16 rk) (Fin.ext (by simp [Fin.natAdd]))]
    exact (basisBitsEquiv 16).symm_apply_apply rk
  have hLt : (unpackOrbitIdx x).val < orbitCount47905 := by
    rw [hUnpack, val_orbitRankFin16]
    exact (tetRank65 _).isLt
  let rOrbit : Fin orbitCount47905 := ⟨(unpackOrbitIdx x).val, hLt⟩
  have hIdx : (⟨rOrbit.val, by have := rOrbit.isLt; dsimp [orbitCount47905] at *; omega⟩ :
      Fin (2 ^ 16)) = unpackOrbitIdx x := Fin.ext rfl
  have hW31 := k6EffWord31_eq_of_lt_orbit rOrbit
  dsimp only at hW31
  rw [hIdx] at hW31
  have hEff := effEntry_eq_of_lt_orbit pos24TailSign (pos24TailMag30MidpointB B hB1 hB29) rOrbit
  dsimp only at hEff
  rw [hIdx] at hEff
  have hTop : k6MidMagThresholdB B hB1 hB29 (k6Table31 (rOrbit.val / 64) ⟨rOrbit.val % 64,
      Nat.mod_lt _ (by decide)⟩) = (pos24TailMag30MidpointB B hB1 hB29 rOrbit).val :=
    pos24TailMag30MidpointB_eq_topBits B hB1 hB29 rOrbit _ fun j ↦
      k6Table31_low30_eq_basisBits rOrbit ⟨(30 - B) + j.val, by omega⟩
  change k6MidPhaseBitSpecB B hB1 hB29 slot2SwappedTo0 x =
    midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 hB29) x
  unfold k6MidPhaseBitSpecB midPhaseBitSpec
  dsimp only
  rw [hW31, hTop, k6Table31_sign_eq rOrbit, hEff.1, hEff.2]
theorem slice_disjoint_slice {m n : ℕ} (r : QRegister m n) (s₁ k₁ s₂ k₂ : ℕ) (h₁ : s₁ + k₁ ≤
    m) (h₂ : s₂ + k₂ ≤ m)
    (hsep : s₁ + k₁ ≤ s₂ ∨ s₂ + k₂ ≤ s₁) : (r.slice s₁ k₁ h₁).DisjointWires (r.slice s₂ k₂ h₂) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  rw [QRegister.slice_apply, QRegister.slice_apply] at hij
  have hv := congrArg Fin.val (r.wires.injective hij)
  dsimp at hv; omega

theorem disj_symmAux {k₁ k₂ n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    (h : r₁.DisjointWires r₂) : r₂.DisjointWires r₁ := Disjoint.symm h

/-- All `1,728` dirty buffer wires `rCore[0..1728)` (`H = 0`). -/
abbrev rDirtyOf {n : ℕ} (rCore : QRegister posCoreWires n) : QRegister 1728 n :=
  rCore.slice 0 1728 (by dsimp [posCoreWires]; omega)

/-- `64` one-hot slot wires `rClean[0..64)`. -/
abbrev rOH64Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 64 n := rClean.slice 0 64 (by omega)

/-- `25` bottom magnitude output wires `rClean[64..89)`. -/
abbrev rOutBBot25Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 25 n := rClean.slice 64 25 (by omega)

/-- `6` top output wires `rClean[89..95)` (`5` top magnitude bits + `1` sign bit). -/
abbrev rOutBTop6Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 6 n := rClean.slice 89 6 (by omega)

/-- `B + 1` active output wires `rClean[64 + (30 - B) .. 95)` read by `dKickZeroSub34Dyn`. -/
abbrev rOutTopOf {n mClean : ℕ} (B : ℕ) (_hB1 : 1 ≤ B) (_hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) : QRegister (B + 1) n :=
  rClean.slice (64 + (30 - B)) (B + 1) (by omega)

/-- `3` untouched clean LSB output wires `rClean[64..67)` (`B ≤ 27` keeps `[64..67)` at `|0⟩`). -/
abbrev rHold3Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 3 n := rClean.slice 64 3 (by omega)

/-- `31` clean scratch wires `rClean[95..126)` freed after Stage 5d. -/
abbrev rSub31Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 31 n := rClean.slice 95 31 (by omega)

/-- Combined `34`-wire clean scratch register `rClean[64..67) ++ rClean[95..126)` for Stage 6. -/
abbrev rScr34Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 34 n := (rHold3Of hmClean rClean).concat (rSub31Of hmClean rClean)
    (slice_disjoint_slice rClean 64 3 95 31 (by omega) (by omega) (Or.inl (by omega)))

/-- `18` auxiliary palette wires `rClean[95..113)` (`pal1, pal2, pal3`). -/
abbrev rPal18Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 18 n := rClean.slice 95 18 (by omega)

/-- `24` row-palette wires `rClean[89..113)` (`pal0 ++ pal1 ++ pal2 ++ pal3`). -/
abbrev rPal24Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 24 n := (rOutBTop6Of hmClean rClean).concat (rPal18Of hmClean rClean)
    (slice_disjoint_slice rClean 89 6 95 18 (by omega) (by omega) (Or.inl (by omega)))

theorem rPal24Of_apply {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (t : Fin 24) :
    rPal24Of hmClean rClean t = rClean ⟨89 + t.val, by omega⟩ := by
  by_cases ht : t.val < 6
  · have hEq : t = Fin.castAdd 18 ⟨t.val, ht⟩ := Fin.ext rfl
    exact ((congrArg (rPal24Of hmClean rClean).wires hEq).trans
      (QRegister.concat_apply_left _ _ _ _)).trans
      (by dsimp only [rOutBTop6Of]; rw [QRegister.slice_apply])
  · have hEq : t = Fin.natAdd 6 (⟨t.val - 6, by omega⟩ : Fin 18) :=
      Fin.ext (by dsimp [Fin.natAdd]; omega)
    exact ((congrArg (rPal24Of hmClean rClean).wires hEq).trans
      (QRegister.concat_apply_right _ _ _ _)).trans
      (by dsimp only [rPal18Of]; rw [QRegister.slice_apply]
          exact congrArg rClean.wires (Fin.ext (by dsimp; omega)))

theorem wRootCtrl_ne_rDirty {n : ℕ} {rCore : QRegister posCoreWires n}
    {rOrbit16 : QRegister 16 n} (hCO : rCore.DisjointWires rOrbit16) (f : Fin 1728) :
    rOrbit16 ⟨15, by decide⟩ ≠ rDirtyOf rCore f :=
  ((hCO.compose_left _).ne f ⟨15, by decide⟩).symm

theorem wRootCtrl_ne_rPal24 {n mClean : ℕ} (hmClean : 126 ≤
    mClean) {rOrbit16 : QRegister 16 n} {rClean : QRegister
    mClean n} (hOC : rOrbit16.DisjointWires rClean) (t : Fin 24) : rOrbit16 ⟨15,
      by decide⟩ ≠ rPal24Of hmClean rClean
    t := by
  rw [rPal24Of_apply]
  exact hOC.ne ⟨15, by decide⟩ _

/-- `2` palette selector wires `rClean[113..115)` (`p0, p1`). -/
abbrev rP2Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 2 n := rClean.slice 113 2 (by omega)

/-- Pre-mux parity wire `rClean[115]`. -/
abbrev wParity2Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    Wire n := rClean ⟨115, by omega⟩

/-- Stream scratch wire `rClean[115]`. -/
abbrev wStreamOf {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    Wire n := rClean ⟨115, by omega⟩

/-- Stage-5b phase-mux parity wire `rClean[125]`. -/
abbrev wParity3Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    Wire n := rClean ⟨125, by omega⟩

/-- `10` tree scratch wires `rClean[116..126)` (`QRegister (1 + 9) n`) for Stage 3
  `k6LoadTreeDyn`. -/
abbrev rWalk10TreeOf {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister (1 + 9) n := rClean.slice 116 (1 + 9) (by omega)

/-- `10` unary walk scratch wires `rClean[116..126)` for Stage 4 / Stage 8. -/
abbrev rWalk10Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 10 n := rClean.slice 116 10 (by omega)

/-- `4` one-hot palette selector wires `rClean[115..119)` for Stage 5a/5b/5d. -/
abbrev rOH4Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 4 n := rClean.slice 115 4 (by omega)

/-- `6` palette diff wires `rClean[119..125)` for Stage 5b/5c/5d. -/
abbrev rDiff6Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 6 n := rClean.slice 119 6 (by omega)

/-- `30` Stage-5d `measureXReset` wires `rClean[95..125)`. -/
abbrev rMeas5c30Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 30 n := rClean.slice 95 30 (by omega)

/-- `27` pre-mux / stream target wires `rP2 ++ rOutBBot25` (`rClean[113..115) ++
  rClean[64..89)`). -/
abbrev rTarget27Of {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 27 n := (rP2Of hmClean rClean).concat (rOutBBot25Of hmClean rClean)
    (slice_disjoint_slice rClean 113 2 64 25 (by omega) (by omega) (Or.inr (by omega)))

theorem rTarget27Of_apply_lt2 {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (col : Fin 27)
    (hcol : col.val < 2) : rTarget27Of hmClean rClean col = rClean ⟨113 + col.val, by omega⟩ := by
  have hceq : col = Fin.castAdd 25 ⟨col.val, hcol⟩ := Fin.ext rfl
  exact ((congrArg (rTarget27Of hmClean rClean).wires hceq).trans
    (QRegister.concat_apply_left _ _ _ _)).trans
    (by dsimp only [rP2Of]; rw [QRegister.slice_apply])

theorem rTarget27Of_apply_ge2 {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (col : Fin 27)
    (hcol : ¬ col.val < 2) : rTarget27Of hmClean rClean col = rClean ⟨64 + (col.val - 2),
      by omega⟩ := by
  have hceq : col = Fin.natAdd 2 (⟨col.val - 2, by omega⟩ : Fin 25) :=
    Fin.ext (by dsimp [Fin.natAdd]; omega)
  exact ((congrArg (rTarget27Of hmClean rClean).wires hceq).trans
    (QRegister.concat_apply_right _ _ _ _)).trans
    (by dsimp only [rOutBBot25Of]; rw [QRegister.slice_apply])

theorem rTarget27Of_mem_clean {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (col : Fin 27) :
    rTarget27Of hmClean rClean col ∈ Set.range rClean.wires := by
  by_cases hcol : col.val < 2
  · rw [rTarget27Of_apply_lt2 hmClean rClean col hcol]
    exact ⟨⟨113 + col.val, by omega⟩, rfl⟩
  · rw [rTarget27Of_apply_ge2 hmClean rClean col hcol]
    exact ⟨⟨64 + (col.val - 2), by omega⟩, rfl⟩

/-- Active `64`-to-`1` pre-mux / stream column predicate for `B`-bit midpoint precision:
retains `col = 0, 1` (`rP2`) and `col ∈ [2 + (30 - B), 27)`, skipping `col ∈ [2, 2 + (30 - B))`
so `rClean[64 .. 64 + (30 - B))` stays untouched at `|0⟩`. -/
def k6ActiveCol (B : ℕ) (col : Fin 27) : Bool := decide (col.val < 2 ∨ 2 + (30 - B) ≤ col.val)

/-- Number of active pre-mux columns among `{0, ..., m - 1}`. -/
def k6ActiveCount (B : ℕ) : (m : ℕ) → m ≤ 27 → ℕ
  | 0, _ => 0
  | m + 1, hm =>
      k6ActiveCount B m (Nat.le_of_succ_le hm) +
        if k6ActiveCol B ⟨m, hm⟩ then 1 else 0

theorem k6ActiveCount_27 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : k6ActiveCount B 27 (le_refl 27) =
    B - 3 := by
  interval_cases B <;> rfl

/-- Stage-2 `64`-to-`1` pre-mux circuit over the `B - 3` active columns of `rBuf1728` (`hb = 0`). -/
noncomputable def cPreMuxRaw {n : ℕ} (B : ℕ)
    (wParity : Wire n) (rOH64 : QRegister 64 n) (rTarget27 : QRegister 27 n)
    (rBuf1728 : QRegister 1728 n) (hPOut : ∀ m : Fin 27, wParity ≠ rTarget27 m)
    (hOHOut : rOH64.DisjointWires rTarget27) (hBufOut : rBuf1728.DisjointWires rTarget27)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) : (m : ℕ) → (hm : m ≤ 27) → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let col : Fin 27 := ⟨m, hm⟩
      cPreMuxRaw B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP m
        (Nat.le_of_succ_le hm) ;;ᶜ
        if k6ActiveCol B col then
          p2t_cPhaseMuxCol64 0 (rTarget27 col) wParity rOH64 (k6_rCol64 rBuf1728 col)
            (hPOut col)
            (fun sl ↦ hOHOut.ne sl col)
            (fun sl ↦ by rw [k6_rCol64_apply]; exact hBufOut.ne _ col)
            hOHP
        else
          .identity

theorem cPreMuxRaw_count_toff {n : ℕ} (B : ℕ)
    (wParity : Wire n) (rOH64 : QRegister 64 n) (rTarget27 : QRegister 27 n)
    (rBuf1728 : QRegister 1728 n) (hPOut : ∀ m : Fin 27, wParity ≠ rTarget27 m)
    (hOHOut : rOH64.DisjointWires rTarget27) (hBufOut : rBuf1728.DisjointWires rTarget27)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) : ∀ (m : ℕ) (hm : m ≤ 27),
      (cPreMuxRaw B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP m hm).count
        PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cPreMuxRaw]
      rw [Circuit.count_seq,
        cPreMuxRaw_count_toff B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP m
          (Nat.le_of_succ_le hm)]
      split_ifs
      · simp [p2t_cPhaseMuxCol64_count_toff]
      · rfl

theorem cPreMuxRaw_count_t {n : ℕ} (B : ℕ)
    (wParity : Wire n) (rOH64 : QRegister 64 n) (rTarget27 : QRegister 27 n)
    (rBuf1728 : QRegister 1728 n) (hPOut : ∀ m : Fin 27, wParity ≠ rTarget27 m)
    (hOHOut : rOH64.DisjointWires rTarget27) (hBufOut : rBuf1728.DisjointWires rTarget27)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) : ∀ (m : ℕ) (hm : m ≤ 27),
      (cPreMuxRaw B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP m hm).count
        PrimitiveGate.T = 128 * k6ActiveCount B m hm
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cPreMuxRaw, k6ActiveCount]
      rw [Circuit.count_seq,
        cPreMuxRaw_count_t B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP m
          (Nat.le_of_succ_le hm)]
      split_ifs with hAct
      · rw [p2t_cPhaseMuxCol64_count_t]
        change 128 * k6ActiveCount B m (Nat.le_of_succ_le hm) + 128 = _
        omega
      · change 128 * k6ActiveCount B m (Nat.le_of_succ_le hm) + 0 = _
        omega

theorem cPreMuxRaw_ket {n : ℕ} (B : ℕ)
    (wParity : Wire n) (rOH64 : QRegister 64 n) (rTarget27 : QRegister 27 n)
    (rBuf1728 : QRegister 1728 n) (hPOut : ∀ m : Fin 27, wParity ≠ rTarget27 m)
    (hOHOut : rOH64.DisjointWires rTarget27) (hBufOut : rBuf1728.DisjointWires rTarget27)
    (hOHP : ∀ sl : Fin 64, rOH64 sl ≠ wParity) (hBufP : ∀ flat : Fin 1728, rBuf1728 flat ≠ wParity)
    (hOHBuf : rOH64.DisjointWires rBuf1728) (sel : Fin 64) (β : BitAssignment n)
    (hOut0 : ∀ m : Fin 27, β (rTarget27 m) = 0) (hβP : β wParity = 0)
    (hOH : ∀ sl : Fin 64, β (rOH64 sl) = if sl = sel then 1 else 0) :
    (cPreMuxRaw B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP 27
      (le_refl 27)).eval.1.mulVec (ket β) = ket (writeReg β rTarget27
        (fun m ↦ if k6ActiveCol B m then β (rBuf1728 ⟨m.val * 64 + sel.val, by omega⟩) else 0)) :=
          by
  have haux : ∀ (j : ℕ) (hj : j ≤ 27),
      (cPreMuxRaw B wParity rOH64 rTarget27 rBuf1728 hPOut hOHOut hBufOut hOHP j
        hj).eval.1.mulVec (ket β) = ket (writeReg β rTarget27 (fun m ↦ if m.val < j then
          if k6ActiveCol B m then β (rBuf1728 ⟨m.val * 64 + sel.val, by omega⟩) else 0
        else 0)) := by
    intro j hj
    have hwr_congr : ∀ (f g : Fin 27 → ZMod 2), (∀ m, f m = g m) →
        writeReg β rTarget27 f = writeReg β rTarget27 g := fun f g hfg ↦
      congrArg (writeReg β rTarget27) (funext hfg)
    induction j with
    | zero =>
        simp only [cPreMuxRaw, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
        refine congrArg ket (funext fun w ↦ ?_)
        by_cases hw : w ∈ Set.range rTarget27.wires
        · obtain ⟨m, rfl⟩ := hw
          rw [writeReg_apply_reg]
          simp [hOut0 m]
        · exact (writeReg_apply_of_not_mem β rTarget27 _ w hw).symm
    | succ j ih =>
        dsimp only [cPreMuxRaw]
        rw [p2t_eval_seq_mulVec, ih (Nat.le_of_succ_le hj)]
        let βj := writeReg β rTarget27 (fun m ↦
          if m.val < j then
            if k6ActiveCol B m then β (rBuf1728 ⟨m.val * 64 + sel.val, by omega⟩) else 0
          else 0)
        let col : Fin 27 := ⟨j, hj⟩
        split_ifs with hAct
        · have hOHCol : rOH64.DisjointWires (k6_rCol64 rBuf1728 col) := by
            rw [QRegister.disjoint_iff]
            intro s₁ s₂
            rw [k6_rCol64_apply]
            exact hOHBuf.ne s₁ _
          rw [p2t_cPhaseMuxCol64_ket 0 (rTarget27 col) wParity rOH64 (k6_rCol64 rBuf1728 col)
                (hPOut col) (fun sl ↦ hOHOut.ne sl col)
                (fun sl ↦ by rw [k6_rCol64_apply]; exact hBufOut.ne _ col)
                hOHP (fun sl ↦ by rw [k6_rCol64_apply]; exact hBufP _) hOHCol sel βj
                (by dsimp [βj, col]; rw [writeReg_apply_reg]; simp)
                (by dsimp [βj]; rw [writeReg_apply_of_not_mem β rTarget27 _ wParity
                      (fun ⟨m, hm⟩ ↦ hPOut m hm.symm), hβP])
                (fun sl ↦ by dsimp [βj]; rw [writeReg_apply_of_not_mem β rTarget27 _ (rOH64 sl)
                      (fun ⟨m, hm⟩ ↦ hOHOut.ne sl m hm.symm), hOH sl])
                (fun _ hsl ↦ absurd hsl (Nat.not_lt_zero _)),
              show βj (k6_rCol64 rBuf1728 col sel) = β (rBuf1728 ⟨j * 64 + sel.val, by omega⟩) by
                rw [k6_rCol64_apply]
                exact writeReg_apply_of_not_mem β rTarget27 _ _ (fun ⟨m, hm⟩ ↦
                  hBufOut.ne _ m hm.symm)]
          refine congrArg ket (funext fun w ↦ ?_)
          by_cases hw : w ∈ Set.range rTarget27.wires
          · obtain ⟨m, rfl⟩ := hw
            by_cases hmm : m = col
            · subst hmm
              rw [Function.update_self, writeReg_apply_reg]
              simp [show col.val < j + 1 by dsimp [col]; omega, hAct, col]
            · rw [Function.update_of_ne (rTarget27.wires.injective.ne hmm)]
              dsimp [βj]
              rw [writeReg_apply_reg, writeReg_apply_reg]
              have hne : m.val ≠ j := fun h ↦ hmm (Fin.ext h)
              simp [show (m.val < j) ↔ (m.val < j + 1) by omega]
          · rw [Function.update_of_ne (fun h ↦ hw ⟨col, h.symm⟩)]
            dsimp [βj]
            rw [writeReg_apply_of_not_mem β rTarget27 _ w hw,
              writeReg_apply_of_not_mem β rTarget27 _ w hw]
        · simp only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
          refine congrArg ket (hwr_congr _ _ fun m ↦ ?_)
          by_cases hmm : m = col
          · subst hmm
            simp [col, hAct]
          · have hne : m.val ≠ j := fun h ↦ hmm (Fin.ext h)
            simp [show (m.val < j) ↔ (m.val < j + 1) by omega]
  rw [haux 27 (le_refl 27)]
  exact congrArg ket (congrArg (writeReg β rTarget27) (funext fun m ↦ by simp [m.isLt]))
/-- External clean-ancilla invariant on `rClean[64..mClean)`. -/
def s_ext {n mClean : ℕ} (rClean : QRegister mClean n) (γ : BitAssignment n) : Prop :=
  ∀ k : Fin mClean, 64 ≤ k.val → γ (rClean k) = 0

/-- Entry invariant of `dMidKickInnerOf`: `rClean[64..mClean)` is `0` and `rOH64` holds one-hot
  `sel`. -/
def s_in {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ : BitAssignment n) : Prop := s_ext rClean γ ∧ ∀ sl :
    Fin 64, γ (rOH64Of hmClean rClean sl) = if sl = localIdx (k6_rSel6Of rOrbit16) γ then 1
    else 0

theorem s_ext_indep_OH {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) : ∀ β₁ β₂ :
    BitAssignment n,
      (∀ w : Wire n, w ∉ Set.range (rOH64Of hmClean rClean).wires → β₁ w = β₂ w) → s_ext rClean β₁
    → s_ext rClean β₂ := by
  intro β₁ β₂ hEq hExt k hk
  rw [← hEq (rClean k) (fun ⟨sl, hsl⟩ ↦ by
    dsimp only [rOH64Of] at hsl
    rw [QRegister.slice_apply] at hsl
    have hv := congrArg Fin.val (rClean.wires.injective hsl)
    dsimp at hv; omega)]
  exact hExt k hk

/-- Canonical `H = 0` stage state updating `rClean` to `vClean` and `rCore[0..1728)` to `vDirty`. -/
noncomputable def mkState {n mClean : ℕ} (rCore : QRegister posCoreWires n)
    (rClean : QRegister mClean n) (_hCC : rCore.DisjointWires rClean) (γ₀ : BitAssignment n)
    (vClean : Fin mClean → ZMod 2) (vDirty : Fin 1728 → ZMod 2) : BitAssignment n := writeReg
    (writeReg γ₀ rClean vClean) (rDirtyOf rCore) vDirty

theorem mkState_clean {n mClean : ℕ} (rCore : QRegister posCoreWires n)
    (rClean : QRegister mClean n) (hCC :
    rCore.DisjointWires rClean) (γ₀ : BitAssignment n) (vClean : Fin mClean →
      ZMod 2) (vDirty : Fin 1728 → ZMod 2) (k :
    Fin mClean) : mkState rCore rClean hCC γ₀ vClean vDirty (rClean k) = vClean k := by
  dsimp only [mkState]
  rw [writeReg_apply_of_not_mem _ (rDirtyOf rCore) _ (rClean k)
    (fun ⟨d, hd⟩ ↦ (hCC.compose_left _).ne d k hd), writeReg_apply_reg]

theorem mkState_dirty {n mClean : ℕ} (rCore : QRegister posCoreWires n)
    (rClean : QRegister mClean n) (hCC :
    rCore.DisjointWires rClean) (γ₀ : BitAssignment n) (vClean : Fin mClean →
      ZMod 2) (vDirty : Fin 1728 → ZMod 2) (d :
    Fin 1728) : mkState rCore rClean hCC γ₀ vClean vDirty (rDirtyOf rCore d) = vDirty d := by
  dsimp only [mkState]
  exact writeReg_apply_reg _ _ _ _

theorem mkState_other {n mClean : ℕ} (rCore : QRegister posCoreWires n)
    (rClean : QRegister mClean n) (hCC :
    rCore.DisjointWires rClean) (γ₀ : BitAssignment n) (vClean : Fin mClean →
      ZMod 2) (vDirty : Fin 1728 → ZMod 2) (w :
    Wire n) (hNotClean : w ∉ Set.range rClean.wires)
      (hNotDirty : w ∉ Set.range (rDirtyOf rCore).wires) : mkState
    rCore rClean hCC γ₀ vClean vDirty w = γ₀ w := by
  dsimp only [mkState]
  rw [writeReg_apply_of_not_mem _ _ _ w hNotDirty, writeReg_apply_of_not_mem _ _ _ w hNotClean]

attribute [local irreducible] mkState

theorem eq_mkState {n mClean : ℕ} (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC :
    rCore.DisjointWires rClean) (β γ₀ : BitAssignment n) (vClean : Fin mClean →
      ZMod 2) (vDirty : Fin 1728 → ZMod 2)
    (hClean : ∀ k : Fin mClean, β (rClean k) = vClean k) (hDirty : ∀ d : Fin 1728,
      β (rDirtyOf rCore d) = vDirty d)
    (hOther : ∀ w : Wire n,
      w ∉ Set.range rClean.wires → w ∉ Set.range (rDirtyOf rCore).wires → β w = γ₀ w) : β =
    mkState rCore rClean hCC γ₀ vClean vDirty := by
  funext w
  by_cases hc : w ∈ Set.range rClean.wires
  · obtain ⟨k, rfl⟩ := hc
    rw [hClean k, mkState_clean]
  · by_cases hd : w ∈ Set.range (rDirtyOf rCore).wires
    · obtain ⟨d, rfl⟩ := hd
      rw [hDirty d, mkState_dirty]
    · rw [hOther w hc hd, mkState_other rCore rClean hCC γ₀ vClean vDirty w hc hd]

theorem mkState_orbit {n mClean : ℕ} (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) (γ₀ : BitAssignment n)
    (vClean : Fin mClean → ZMod 2) (vDirty : Fin 1728 → ZMod 2) (i : Fin 16) : mkState
    rCore rClean hCC γ₀ vClean vDirty (rOrbit16 i) = γ₀ (rOrbit16 i) := mkState_other rCore
    rClean hCC γ₀ vClean vDirty (rOrbit16 i) (fun ⟨k, hk⟩ ↦ hOC.ne i k hk.symm)
    (fun ⟨d, hd⟩ ↦ (hCO.compose_left _).ne d i hd)

theorem flat_lt_1728 (m : Fin 27) (sel : Fin 64) : m.val * 64 + sel.val < 1728 := by omega

theorem div64_lt_27 (d : Fin 1728) : d.val / 64 < 27 := by omega

theorem col_lt_27 {v : ℕ} (hv : v < 89) : 2 + (v - 64) < 27 := by omega

theorem pal_lt_24 {v : ℕ} (hv : v < 113) : v - 89 < 24 := by omega

theorem tbl_lt_31 {v : ℕ} (hv : v < 95) : v - 64 < 31 := by omega

/-- Initial dirty bit read from `rCore[0..1728)` at column `m` and slot `sel(γ₀)`. -/
noncomputable def gBit {n : ℕ} (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (γ₀ : BitAssignment n) (m : Fin 27) : ZMod 2 :=
  γ₀ (rDirtyOf rCore ⟨m.val * 64 + (k6_selOf rOrbit16 γ₀).val,
    flat_lt_1728 m (k6_selOf rOrbit16 γ₀)⟩)

/-- Initial dirty bit reconstructed from post-tree `α` by adding `k6_bufWord1728`. -/
noncomputable def gOf {n : ℕ} (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (α : BitAssignment n) (m : Fin 27) : ZMod 2 :=
  let flat : Fin 1728 :=
    ⟨m.val * 64 + (k6_selOf rOrbit16 α).val, flat_lt_1728 m (k6_selOf rOrbit16 α)⟩
  α (rDirtyOf rCore flat) + k6_bufWord1728 (k6_qOf rOrbit16 α) flat

/-- Target `±1` diagonal sign factor for `k6MidPhaseBitSpecB B`. -/
noncomputable def signOf {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤ 29)
    (slot2SwappedTo0 : Bool) (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (hCO : rCore.DisjointWires rOrbit16) (α : BitAssignment n) : ℂ := if k6MidPhaseBitSpecB B
    hB1 hB29 slot2SwappedTo0 ((rCore.concat rOrbit16 hCO).extractIndex ((basisBitsEquiv
    n).symm α)) then (-1 : ℂ) else 1

theorem signOf_congr {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤
    29) (slot2SwappedTo0 : Bool) (rCore : QRegister
    posCoreWires n) (rOrbit16 : QRegister 16 n) (hCO : rCore.DisjointWires rOrbit16)
      (α₁ α₂ : BitAssignment n)
    (hCoreHigh : ∀ c : Fin posCoreWires,
      3948 ≤ c.val → α₁ (rCore c) = α₂ (rCore c)) (hOrb : ∀ i : Fin 16, α₁ (rOrbit16
    i) = α₂ (rOrbit16 i)) : signOf B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO α₁ =
      signOf B hB1 hB29
    slot2SwappedTo0 rCore rOrbit16 hCO α₂ := by
  let rData := rCore.concat rOrbit16 hCO
  let x₁ := rData.extractIndex ((basisBitsEquiv n).symm α₁)
  let x₂ := rData.extractIndex ((basisBitsEquiv n).symm α₂)
  have hBit : ∀ i : Fin (posCoreWires + 16), basisBits (posCoreWires + 16) x₁ i = α₁ (rData i) ∧
      basisBits (posCoreWires + 16) x₂ i = α₂ (rData i) := fun i ↦
    ⟨(QRegister.basisBits_extractIndex rData _ i).trans
      (congrFun ((basisBitsEquiv n).apply_symm_apply α₁ : basisBits n _ = α₁) (rData i)),
     (QRegister.basisBits_extractIndex rData _ i).trans
      (congrFun ((basisBitsEquiv n).apply_symm_apply α₂ : basisBits n _ = α₂) (rData i))⟩
  have hCoreBit : ∀ c : Fin posCoreWires, 3948 ≤ c.val →
      unpackCoreBits x₁ c = unpackCoreBits x₂ c := fun c hc ↦ by
    obtain ⟨hb₁, hb₂⟩ := hBit (Fin.castAdd 16 c)
    dsimp only [unpackCoreBits, rData] at hb₁ hb₂ ⊢
    rw [QRegister.concat_apply_left] at hb₁ hb₂
    rw [hb₁, hb₂, hCoreHigh c hc]
  have hIdxEq : unpackOrbitIdx x₁ = unpackOrbitIdx x₂ :=
    congrArg (basisBitsEquiv 16).symm (funext fun i ↦ by
      obtain ⟨hb₁, hb₂⟩ := hBit (Fin.natAdd posCoreWires i)
      dsimp only [rData] at hb₁ hb₂
      rw [QRegister.concat_apply_right] at hb₁ hb₂
      exact hb₁.trans ((hOrb i).trans hb₂.symm))
  let rL := QRegExt.ofFin posCoreWires
  have hSub (s : Fin 80) : unpackCoreBits x₁ ((rSubPayloadCore rL) s) =
      unpackCoreBits x₂ ((rSubPayloadCore rL) s) :=
    hCoreBit ⟨3954 + s.val, by dsimp [posCoreWires]; omega⟩ (by dsimp; omega)
  dsimp only [signOf, k6MidPhaseBitSpecB]
  refine congrArg (fun b : Bool ↦ if b then (-1 : ℂ) else 1) ?_
  rw [hIdxEq, hCoreBit (wSlot2Core rL) (by decide), hCoreBit (wSlot1Core rL) (by decide),
    hCoreBit (wSlot0Core rL) (by decide), hCoreBit (wSubReject rL) (by decide),
    hCoreBit (wIsHead rL) (by decide), hCoreBit (wRejectZero rL) (by decide),
    regVal_congr_cross (rNucIdx rL) (rNucIdx rL) (unpackCoreBits x₁) (unpackCoreBits x₂)
      (fun t ↦ by dsimp only [rNucIdx]; rw [QRegister.slice_apply]; exact hSub _),
    regVal_congr_cross (rAnchorIdx rL) (rAnchorIdx rL) (unpackCoreBits x₁) (unpackCoreBits x₂)
      (fun t ↦ by dsimp only [rAnchorIdx]; rw [QRegister.slice_apply]; exact hSub _),
    regVal_congr_cross (rPartnerIdx rL) (rPartnerIdx rL) (unpackCoreBits x₁) (unpackCoreBits x₂)
      (fun t ↦ by dsimp only [rPartnerIdx]; rw [QRegister.slice_apply]; exact hSub _),
    regVal_congr_cross (rTailKeep30 rL) (rTailKeep30 rL) (unpackCoreBits x₁) (unpackCoreBits x₂)
      (fun t ↦ by dsimp only [rTailKeep30]; rw [QRegister.slice_apply]; exact hSub _)]
theorem signOf_eq {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤ 29) (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (hCO : rCore.DisjointWires rOrbit16) (α : BitAssignment n) : signOf B hB1 hB29
    slot2SwappedTo0 rCore rOrbit16 hCO α = if k6MidPhaseBitSpecB B hB1 hB29 slot2SwappedTo0
    ((rCore.concat rOrbit16 hCO).extractIndex ((basisBitsEquiv n).symm α)) then (-1 : ℂ) else
    1 := rfl

attribute [local irreducible] signOf

/-- Initial dirty vector `rCore[0..1728)` before `k6LoadTreeDyn`. -/
def vDirty0 {n : ℕ} (rCore : QRegister posCoreWires n) (γ₀ : BitAssignment n) : Fin 1728 →
    ZMod 2 := fun d ↦ γ₀ (rDirtyOf rCore d)

/-- Post-tree dirty vector `rCore[0..1728)` after `k6LoadTreeDyn` (`H = 0`). -/
noncomputable def vDirty1 {n : ℕ} (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (γ₀ : BitAssignment n) : Fin 1728 → ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  fun d ↦
    γ₀ (rDirtyOf rCore d) +
      k6BufBit q ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩ ⟨d.val / 64, div64_lt_27 d⟩

/-- Stage-2 clean vector after `cPreMuxRaw` (`rClean[64 .. 64 + (30 - B))` stays `0`). -/
noncomputable def vClean2 {n mClean : ℕ} (B : ℕ) (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h89 : k.val < 89 then gBit rCore rOrbit16 γ₀ ⟨2 + (k.val - 64), col_lt_27 h89⟩
  else if k.val = 113 then gBit rCore rOrbit16 γ₀ ⟨0, by decide⟩
  else if k.val = 114 then gBit rCore rOrbit16 γ₀ ⟨1, by decide⟩
  else 0

/-- Stage-3 clean vector after `k6LoadTreeDyn` (`H = 0`). -/
noncomputable def vClean3 {n mClean : ℕ} (B : ℕ) (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  let sel := k6_selOf rOrbit16 γ₀
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h89 : k.val < 89 then gBit rCore rOrbit16 γ₀ ⟨2 + (k.val - 64), col_lt_27 h89⟩
  else if h113 : k.val < 113 then k6Pal24Bit q sel ⟨k.val - 89, pal_lt_24 h113⟩
  else if k.val = 113 then gBit rCore rOrbit16 γ₀ ⟨0, by decide⟩
  else if k.val = 114 then gBit rCore rOrbit16 γ₀ ⟨1, by decide⟩
  else 0

/-- Stage-4 clean vector before column `idx` of `dStreamRemDyn`. -/
noncomputable def vCleanStream {n mClean : ℕ} (B idx : ℕ)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  let sel := k6_selOf rOrbit16 γ₀
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h89 : k.val < 89 then
    if 2 + (k.val - 64) < idx then k6BufBit q sel ⟨2 + (k.val - 64), col_lt_27 h89⟩
    else gBit rCore rOrbit16 γ₀ ⟨2 + (k.val - 64), col_lt_27 h89⟩
  else if h113 : k.val < 113 then k6Pal24Bit q sel ⟨k.val - 89, pal_lt_24 h113⟩
  else if k.val = 113 then
    if 0 < idx then k6P0Bit q sel else gBit rCore rOrbit16 γ₀ ⟨0, by decide⟩
  else if k.val = 114 then
    if 1 < idx then k6P1Bit q sel else gBit rCore rOrbit16 γ₀ ⟨1, by decide⟩
  else 0

/-- Stage-4 intermediate clean vector after `p2t_cPhaseMuxCol64` at active column `idx`. -/
noncomputable def vCleanStreamMux {n mClean : ℕ} (B idx : ℕ) (hidx : idx < 27)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 := if k.val
    = 115 then gBit rCore rOrbit16 γ₀ ⟨idx, hidx⟩ + k6BufBit (k6_qOf rOrbit16 γ₀)
    (k6_selOf rOrbit16 γ₀) ⟨idx, hidx⟩ else vCleanStream B idx rCore rOrbit16 rClean γ₀ k

/-- Stage-4 intermediate clean vector after `CNOT wStream (rTarget27 col)` at active column
  `idx`. -/
noncomputable def vCleanStreamCnot {n mClean : ℕ} (B idx : ℕ) (hidx : idx < 27)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 := if k.val
    = 115 then gBit rCore rOrbit16 γ₀ ⟨idx, hidx⟩ + k6BufBit (k6_qOf rOrbit16 γ₀)
    (k6_selOf rOrbit16 γ₀) ⟨idx, hidx⟩ else vCleanStream B (idx + 1) rCore rOrbit16 rClean
    γ₀ k

/-- Stage-5a clean vector upon completing `dStreamRemDyn` (`idx = 27`). -/
noncomputable def vClean5a {n mClean : ℕ} (B : ℕ) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  let sel := k6_selOf rOrbit16 γ₀
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h89 : k.val < 89 then k6BufBit q sel ⟨2 + (k.val - 64), col_lt_27 h89⟩
  else if h113 : k.val < 113 then k6Pal24Bit q sel ⟨k.val - 89, pal_lt_24 h113⟩
  else if k.val = 113 then k6P0Bit q sel
  else if k.val = 114 then k6P1Bit q sel
  else 0

/-- Stage-5b clean vector after `k6_cOneHot4Raw`. -/
noncomputable def vClean5b {n mClean : ℕ} (B : ℕ) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  let sel := k6_selOf rOrbit16 γ₀
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h89 : k.val < 89 then k6BufBit q sel ⟨2 + (k.val - 64), col_lt_27 h89⟩
  else if h113 : k.val < 113 then k6Pal24Bit q sel ⟨k.val - 89, pal_lt_24 h113⟩
  else if k.val = 113 then k6P0Bit q sel
  else if k.val = 114 then k6P1Bit q sel
  else if h119 : k.val < 119 then
    k6_oneHot4Val (k6P0Bit q sel) (k6P1Bit q sel) ⟨k.val - 115, by omega⟩
  else 0

/-- Stage-5c clean vector after `k6_cPhaseMux4All6Raw ;;ᶜ k6_cXorDiffTop6Raw`. -/
noncomputable def vClean5c {n mClean : ℕ} (B : ℕ) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  let sel := k6_selOf rOrbit16 γ₀
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h95 : k.val < 95 then k6Table31 q sel ⟨k.val - 64, tbl_lt_31 h95⟩
  else if h125 : k.val < 125 then k6_meas5cTableBit q sel ⟨k.val - 95, by omega⟩
  else 0

/-- Stage-5d clean vector entering Stage 6 `dKickZeroSub34Dyn`. -/
noncomputable def vClean5 {n mClean : ℕ} (B : ℕ) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (γ₀ : BitAssignment n) (k : Fin mClean) : ZMod 2 :=
  let q := k6_qOf rOrbit16 γ₀
  let sel := k6_selOf rOrbit16 γ₀
  if k.val < 64 then γ₀ (rClean k)
  else if k.val < 64 + (30 - B) then 0
  else if h95 : k.val < 95 then k6Table31 q sel ⟨k.val - 64, tbl_lt_31 h95⟩
  else 0

/-- Stage-7 clean vector after resetting `rOutTop`. -/
def vClean7 {n mClean : ℕ} (rClean : QRegister mClean n) (γ₀ : BitAssignment n)
    (k : Fin mClean) : ZMod 2 := if k.val < 64 then γ₀ (rClean k) else 0

/-- Stage predicate for `H = 0` `mkState` basis states. -/
def atStage {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (vClean : BitAssignment n → Fin mClean → ZMod 2)
    (vDirty : BitAssignment n → Fin 1728 → ZMod 2) (α : BitAssignment n) : Prop := ∃ γ₀ :
    BitAssignment n, s_in hmClean rOrbit16 rClean γ₀ ∧ α = mkState rCore rClean hCC γ₀
    (vClean γ₀) (vDirty γ₀)

/-- Deterministic recovery of `γ₀` from any post-tree stage state `α`. -/
noncomputable def recoverInit {n mClean : ℕ}
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (α : BitAssignment n) : BitAssignment n :=
  let q := k6_qOf rOrbit16 α
  writeReg
    (writeReg α rClean (fun k ↦ if k.val < 64 then α (rClean k) else 0))
    (rDirtyOf rCore)
    (fun d ↦ α (rDirtyOf rCore d) +
      k6BufBit q ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩ ⟨d.val / 64, div64_lt_27 d⟩)

theorem not_mem_rTarget27Of_clean {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (k : Fin
    mClean) (hk1 : k.val < 64 ∨ 89 ≤
      k.val) (hk2 : k.val ≠ 113) (hk3 : k.val ≠ 114) : rClean k ∉ Set.range
    (rTarget27Of hmClean rClean).wires := by
  rintro ⟨col, hcol⟩
  by_cases hlt : col.val < 2
  · rw [rTarget27Of_apply_lt2 hmClean rClean col hlt] at hcol
    have hv := congrArg Fin.val (rClean.wires.injective hcol)
    dsimp at hv; omega
  · rw [rTarget27Of_apply_ge2 hmClean rClean col hlt] at hcol
    have hv := congrArg Fin.val (rClean.wires.injective hcol)
    dsimp at hv; omega

theorem mkState_invariants {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (B : ℕ) (hB1 : 1 ≤ B) (hB29 : B ≤ 29) (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (γ₀ : BitAssignment n) (hγ₀ : s_in hmClean rOrbit16 rClean γ₀)
    (vClean : Fin mClean → ZMod 2)
    (hvOH : ∀ k : Fin mClean, k.val < 64 → vClean k = γ₀ (rClean k)) :
    let α := mkState rCore rClean hCC γ₀ vClean (vDirty1 rCore rOrbit16 γ₀)
    k6_qOf rOrbit16 α = k6_qOf rOrbit16 γ₀ ∧
    k6_selOf rOrbit16 α = k6_selOf rOrbit16 γ₀ ∧
    signOf B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO α =
      signOf B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO γ₀ ∧
    (∀ m : Fin 27, gOf rCore rOrbit16 α m = gBit rCore rOrbit16 γ₀ m) ∧
    (∀ m : Fin 27, k6_tStreamOf rOrbit16 α m = k6_tStreamOf rOrbit16 γ₀ m) ∧
    (∀ sl : Fin 64, α (rOH64Of hmClean rClean sl) =
      if sl = k6_selOf rOrbit16 γ₀ then 1 else 0) := by
  intro α
  have hOrb : ∀ i : Fin 16, α (rOrbit16 i) = γ₀ (rOrbit16 i) :=
    mkState_orbit rCore rOrbit16 rClean hCO hCC hOC γ₀ vClean _
  have hHi : localIdx (k6_rHi10Of rOrbit16) α = localIdx (k6_rHi10Of rOrbit16) γ₀ :=
    localIdx_eq_of_apply_eq_loc _ α γ₀ fun j ↦ by
      dsimp only [k6_rHi10Of]; rw [QRegister.slice_apply]; exact hOrb _
  have hSel : k6_selOf rOrbit16 α = k6_selOf rOrbit16 γ₀ :=
    localIdx_eq_of_apply_eq_loc _ α γ₀ fun j ↦ by
      dsimp only [k6_rSel6Of]; rw [QRegister.slice_apply]; exact hOrb _
  have hQ : k6_qOf rOrbit16 α = k6_qOf rOrbit16 γ₀ := by
    dsimp [k6_qOf]; rw [hHi]
  have hSign : signOf B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO α = signOf B hB1
      hB29 slot2SwappedTo0 rCore rOrbit16 hCO γ₀ := signOf_congr B hB1 hB29 slot2SwappedTo0
      rCore rOrbit16 hCO α γ₀ (fun c _ ↦ mkState_other rCore rClean hCC γ₀ vClean _ (rCore c)
        (fun ⟨k, hk⟩ ↦ hCC.ne c k hk.symm) fun ⟨d, hd⟩ ↦ by
          dsimp only [rDirtyOf] at hd
          rw [QRegister.slice_apply] at hd
          have hv := congrArg Fin.val (rCore.wires.injective hd)
          dsimp at hv
          omega) hOrb
  refine ⟨hQ, hSel, hSign, fun m ↦ ?_, fun m ↦ ?_, fun sl ↦ ?_⟩
  · dsimp only [gOf, gBit]
    simp only [hSel, hQ]
    let flat : Fin 1728 := ⟨m.val * 64 + (k6_selOf rOrbit16 γ₀).val, by omega⟩
    have hDirty : α (rDirtyOf rCore flat) = vDirty1 rCore rOrbit16 γ₀ flat := by
      dsimp only [α]; rw [mkState_dirty]
    rw [hDirty]
    dsimp only [vDirty1, k6_bufWord1728]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · dsimp [k6_tStreamOf]; rw [hQ, hSel]
  · dsimp only [rOH64Of]
    rw [QRegister.slice_apply]
    have hc : α (rClean ⟨0 + sl.val, by omega⟩) = γ₀ (rClean ⟨0 + sl.val, by omega⟩) := by
      dsimp [α]; rw [mkState_clean]; exact hvOH _ (by dsimp; omega)
    rw [hc]
    have h0 := hγ₀.2 sl
    dsimp only [rOH64Of] at h0
    rw [QRegister.slice_apply] at h0
    exact h0

theorem recoverInit_mkState {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rCore : QRegister posCoreWires n) (rOrbit16 :
    QRegister 16 n) (rClean : QRegister mClean n) (hCO : rCore.DisjointWires rOrbit16)
      (hCC : rCore.DisjointWires
    rClean) (hOC : rOrbit16.DisjointWires rClean) (γ₀ : BitAssignment n)
      (hγ₀ : s_in hmClean rOrbit16 rClean γ₀)
    (vClean : Fin mClean → ZMod 2) (hvOH : ∀ k : Fin mClean,
      k.val < 64 → vClean k = γ₀ (rClean k)) : recoverInit
    rCore rOrbit16 rClean (mkState rCore rClean hCC γ₀ vClean (vDirty1 rCore rOrbit16 γ₀)) = γ₀ :=
      by
  let α := mkState rCore rClean hCC γ₀ vClean (vDirty1 rCore rOrbit16 γ₀)
  obtain ⟨hQ, _, _, _, _, _⟩ := mkState_invariants hmClean 1 (le_refl 1) (by decide) true
      rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ vClean hvOH
  funext w
  dsimp only [recoverInit]
  change (writeReg (writeReg α rClean (fun k ↦ if k.val < 64 then α (rClean k) else 0))
    (rDirtyOf rCore) _ w) = γ₀ w
  by_cases hd : w ∈ Set.range (rDirtyOf rCore).wires
  · obtain ⟨d, rfl⟩ := hd
    rw [writeReg_apply_reg]
    have hαd := mkState_dirty rCore rClean hCC γ₀ vClean (vDirty1 rCore rOrbit16 γ₀) d
    rw [hαd, hQ]
    dsimp only [vDirty1]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [writeReg_apply_of_not_mem _ _ _ w hd]
    by_cases hc : w ∈ Set.range rClean.wires
    · obtain ⟨k, rfl⟩ := hc
      rw [writeReg_apply_reg]
      by_cases hk : k.val < 64
      · simp only [hk, ↓reduceIte]
        dsimp [α]; rw [mkState_clean]; exact hvOH k hk
      · simp only [hk, ↓reduceIte]
        exact (hγ₀.1 k (by omega)).symm
    · rw [writeReg_apply_of_not_mem _ _ _ w hc]
      exact mkState_other rCore rClean hCC γ₀ vClean _ w hc hd

attribute [local irreducible] recoverInit K6StageSpec DynCircuitExt.substToffoliCircuit

/-- Pads `(B + 1)`-bit Stage-7 measurement outcomes `f7Top` with `30 - B` leading `false` bits. -/
def k6PadF7 (B : ℕ) (f7Top : Fin (B + 1) → Bool) (b : Fin 31) : Bool :=
  if hb : 30 - B ≤ b.val then f7Top ⟨b.val - (30 - B), by omega⟩ else false

/-- Number of active stream columns in the remaining `rem` steps `[27 - rem, 27)`. -/
def streamRemActiveCount (B : ℕ) : (rem : ℕ) → rem ≤ 27 → ℕ
  | 0, _ => 0
  | rem + 1, hrem =>
      (if k6ActiveCol B ⟨27 - (rem + 1), by omega⟩ then 1 else 0) +
        streamRemActiveCount B rem (Nat.le_of_succ_le hrem)

theorem streamRemActiveCount_27 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    streamRemActiveCount B 27 (le_refl 27) = B - 3 := by
  interval_cases B <;> rfl

theorem lt_mClean_115 {mClean : ℕ} (hmClean : 126 ≤ mClean) : 115 < mClean := by omega

theorem sub_succ_lt_27 (rem : ℕ) : 27 - (rem + 1) < 27 := by omega

theorem disj_rWalk10_rOH64 {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    (rWalk10Of hmClean rClean).DisjointWires (rOH64Of hmClean rClean) :=
  slice_disjoint_slice rClean 116 10 0 64 (by omega) (by omega) (Or.inr (by omega))

theorem disj_rP2_rOH4 {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n)
    : (rP2Of hmClean rClean).DisjointWires (rOH4Of hmClean rClean) :=
    slice_disjoint_slice rClean 113 2 115 4 (by omega) (by omega) (Or.inl (by omega))

theorem rDiff6_zero_not_mem_oneHot4 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (hPOH4 : (rP2Of hmClean rClean).DisjointWires (rOH4Of
    hmClean rClean)) : rDiff6Of hmClean rClean 0 ∉ (k6_cOneHot4Raw (rP2Of hmClean
    rClean) (rOH4Of hmClean rClean) hPOH4).support :=
  k6_cOneHot4Raw_not_mem_support (rDiff6Of hmClean rClean 0) _ _ hPOH4
    (fun _ ↦ by
      dsimp only [rDiff6Of, rP2Of]
      rw [QRegister.slice_apply, QRegister.slice_apply]
      exact fun h ↦ by have hv := congrArg Fin.val (rClean.wires.injective h); dsimp at hv; omega)
    (fun _ ↦ by
      dsimp only [rDiff6Of, rOH4Of]
      rw [QRegister.slice_apply, QRegister.slice_apply]
      exact fun h ↦ by have hv := congrArg Fin.val (rClean.wires.injective h); dsimp at hv; omega)

theorem disj_rOH4_rDiff6 {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    (rOH4Of hmClean rClean).DisjointWires (rDiff6Of hmClean rClean) :=
  slice_disjoint_slice rClean 115 4 119 6 (by omega) (by omega) (Or.inl (by omega))

theorem disj_rPal18_rDiff6 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) :
    (rPal18Of hmClean rClean).DisjointWires (rDiff6Of hmClean rClean) :=
  slice_disjoint_slice rClean 95 18 119 6 (by omega) (by omega) (Or.inl (by omega))

theorem disj_rDiff6_rOutBTop6 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) :
    (rDiff6Of hmClean rClean).DisjointWires (rOutBTop6Of hmClean rClean) :=
  slice_disjoint_slice rClean 119 6 89 6 (by omega) (by omega) (Or.inr (by omega))

theorem disj_rOutTop_rScr34 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    (rOutTopOf B hB1 hB27 hmClean rClean).DisjointWires (rScr34Of hmClean rClean) :=
    k6_disjoint_concat_right (slice_disjoint_slice rClean (64 + (30 - B)) (B + 1) 64 3
    (by omega) (by omega) (Or.inr (by omega))) (slice_disjoint_slice rClean (64 + (30 - B))
    (B + 1) 95 31 (by omega) (by omega) (Or.inl (by omega))) _

theorem wParity3_ne_wStream {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) : wParity3Of hmClean rClean ≠ wStreamOf hmClean rClean :=
  fun h ↦ by have hv := congrArg Fin.val (rClean.wires.injective h); dsimp at hv; omega

theorem rOH64_ne_wStream {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (sl : Fin 64) :
    rOH64Of hmClean rClean sl ≠ wStreamOf hmClean rClean := by
  dsimp only [rOH64Of, wStreamOf]; rw [QRegister.slice_apply]
  exact fun h ↦ by have hv := congrArg Fin.val (rClean.wires.injective h); dsimp at hv; omega

theorem rCol64_ne_wStream {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rCore : QRegister posCoreWires n) (rClean :
    QRegister mClean n) (hCC : rCore.DisjointWires rClean) (col : Fin 27) (sl : Fin 64) : k6_rCol64
      (rDirtyOf rCore)
    col sl ≠ wStreamOf hmClean rClean := by
  rw [k6_rCol64_apply]
  exact (hCC.compose_left _).ne _ ⟨115, by omega⟩

theorem rOH64_ne_wParity3 {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (sl : Fin 64) :
    rOH64Of hmClean rClean sl ≠ wParity3Of hmClean rClean := by
  dsimp only [rOH64Of, wParity3Of]; rw [QRegister.slice_apply]
  exact fun h ↦ by have hv := congrArg Fin.val (rClean.wires.injective h); dsimp at hv; omega

theorem wStream_ne_rTarget27 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (col : Fin 27) :
    wStreamOf hmClean rClean ≠ rTarget27Of hmClean rClean col := fun h ↦
  not_mem_rTarget27Of_clean hmClean rClean ⟨115, by omega⟩
    (Or.inr (by dsimp; omega)) (by dsimp; omega) (by dsimp; omega) ⟨col, h.symm⟩

theorem disj_rOH64_rTarget27 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) : (rOH64Of hmClean rClean).DisjointWires
    (rTarget27Of hmClean rClean) := k6_disjoint_concat_right (slice_disjoint_slice
    rClean 0 64 113 2 (by omega) (by omega) (Or.inl (by omega))) (slice_disjoint_slice
    rClean 0 64 64 25 (by omega) (by omega) (Or.inl (by omega))) _

theorem wParity2_ne_rWalk10Tree {n mClean : ℕ} (hmClean : 126 ≤
    mClean) (rClean : QRegister mClean n) (i : Fin (1 + 9))
    : wParity2Of hmClean rClean ≠ rWalk10TreeOf hmClean rClean i := by
  dsimp only [wParity2Of, rWalk10TreeOf]; rw [QRegister.slice_apply]
  exact fun h ↦ by have hv := congrArg Fin.val (rClean.wires.injective h); dsimp at hv; omega

theorem disj_rWalk10Tree_rPal24 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) : (rWalk10TreeOf hmClean rClean).DisjointWires
    (rPal24Of hmClean rClean) := k6_disjoint_concat_right (slice_disjoint_slice rClean
    116 10 89 6 (by omega) (by omega) (Or.inr (by omega))) (slice_disjoint_slice rClean 116
    10 95 18 (by omega) (by omega) (Or.inr (by omega))) _

theorem wRootCtrl_ne_rX10 {n : ℕ} (rOrbit16 : QRegister 16 n) (i : Fin (1 + 9)) :
    k6_wRootCtrlOf rOrbit16 ≠ k6_rX10Of rOrbit16 i := by
  dsimp only [k6_wRootCtrlOf, k6_rX10Of]; rw [QRegister.slice_apply]
  exact fun h ↦ by have hv := congrArg Fin.val (rOrbit16.wires.injective h); dsimp at hv; omega

theorem cKickZeroSub34_eval_ket {n : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (rOutTop : QRegister (B + 1) n) (rScr34 : QRegister 34 n)
    (hCO : rCore.DisjointWires rOrbit16) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr34) (hOutS : rOutTop.DisjointWires rScr34)
    (β α₅ : BitAssignment n) (hScr5 : ∀ s : Fin 34, α₅ (rScr34 s) = 0)
    (hCoreHigh5 : ∀ c : Fin posCoreWires, 3948 ≤ c.val → α₅ (rCore c) = β (rCore c))
    (hOut5 : ∀ b : Fin (B + 1), α₅ (rOutTop b) =
        k6Table31 (prunedEffIdx 10 749 (localIdx (k6_rHi10Of rOrbit16) β).val)
          (localIdx (k6_rSel6Of rOrbit16) β) ⟨(30 - B) + b.val, by omega⟩) :
    let rData := rCore.concat rOrbit16 hCO
    let x := rData.extractIndex ((basisBitsEquiv n).symm β)
    (cKickZeroSub34 B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS).eval.1.mulVec (ket α₅) =
      (if k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0 x then (-1 : ℂ) else 1) •
        ket α₅ := by
  intro rData x
  let idx := unpackOrbitIdx x
  let βL := unpackCoreBits x
  let rCoreL := QRegExt.ofFin posCoreWires
  let g₀ := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g₀ = β := (basisBitsEquiv n).apply_symm_apply β
  have hIdxEq : localIdx rOrbit16 β = idx :=
    (localIdx_congr_cross rOrbit16 rRefOrbit16 β (refInitAssign idx) fun i ↦ by
      have hb := QRegister.basisBits_extractIndex rData g₀ (Fin.natAdd posCoreWires i)
      dsimp only [rData] at hb
      rw [hgβ, QRegister.concat_apply_right] at hb
      have hb2 : basisBits 16 idx i =
          basisBits (posCoreWires + 16) (rData.extractIndex g₀) (Fin.natAdd posCoreWires i) :=
        congrFun ((basisBitsEquiv 16).apply_symm_apply
          (fun j ↦ basisBits (posCoreWires + 16) (rData.extractIndex g₀)
            (Fin.natAdd posCoreWires j))) i
      exact (hb.symm.trans hb2.symm).trans
        (refInitAssign_orbit idx i).symm).trans (localIdx_refOrbit16_eq idx)
  have hSplitOrbit64 : (localIdx rOrbit16 β : ℕ) =
      (localIdx (k6_rSel6Of rOrbit16) β : ℕ) + 64 * (localIdx (k6_rHi10Of rOrbit16) β : ℕ) := by
    rw [show (localIdx rOrbit16 β : ℕ) = ∑ k : Fin (6 + 10),
      (β (rOrbit16 k)).val * 2 ^ k.val from rfl,
      Fin.sum_univ_add, localIdx_val, localIdx_val]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) ?_
    · dsimp only [k6_rSel6Of]
      rw [Fin.val_castAdd, QRegister.slice_apply,
        show (⟨0 + i.val, by omega⟩ : Fin 16) = Fin.castAdd 10 i from Fin.ext (by dsimp; omega)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp only [k6_rHi10Of]
      rw [Fin.val_natAdd, QRegister.slice_apply,
        show (⟨6 + j.val, by omega⟩ : Fin 16) = Fin.natAdd 6 j from Fin.ext rfl, pow_add]
      ring
  have hIdxVal : (localIdx rOrbit16 β : ℕ) = idx.val := congrArg Fin.val hIdxEq
  have hselLt := (localIdx (k6_rSel6Of rOrbit16) β).isLt
  have hOutEff : ∀ b : Fin (B + 1),
      α₅ (rOutTop b) = k6EffWord31 idx ⟨(30 - B) + b.val, by omega⟩ := fun b ↦ by
    rw [hOut5 b, show (localIdx (k6_rHi10Of rOrbit16) β).val = idx.val / 64 by omega,
      show localIdx (k6_rSel6Of rOrbit16) β = ⟨idx.val % 64, Nat.mod_lt _ (by decide)⟩
        from Fin.ext (by dsimp; omega)]
    rfl
  have hCoreHigh : ∀ c : Fin posCoreWires, 3948 ≤ c.val → α₅ (rCore c) = βL c := fun c hge ↦ by
    have hb := QRegister.basisBits_extractIndex rData g₀ (Fin.castAdd 16 c)
    dsimp only [βL, unpackCoreBits, x, rData] at hb ⊢
    rw [hgβ, QRegister.concat_apply_left] at hb
    exact (hCoreHigh5 c hge).trans hb.symm
  have hSubEqL : ∀ s : Fin 80, α₅ ((rSubPayloadCore rCore) s) = βL ((rSubPayloadCore rCoreL) s) :=
    fun s ↦ hCoreHigh ⟨3954 + s.val, by dsimp [posCoreWires]; omega⟩ (by dsimp; omega)
  have hbitsOfReg : ∀ {W : ℕ} (r : QRegister W n) (t : Fin W),
      basisBits W ⟨regVal r α₅, regVal_lt_two_pow r α₅⟩ t = α₅ (r t) := fun {W} r t ↦ by
    have hfn : basisBits W ⟨regVal r α₅, regVal_lt_two_pow r α₅⟩ = fun u ↦ α₅ (r u) := by
      apply (basisBitsEquiv W).symm.injective
      ext
      simp [regVal, bitsVal_eq_symm_val]
    exact congrFun hfn t
  have hbSlice : ∀ (off : ℕ) (hoff : off + 8 ≤ 80) (t : Fin 8) (m : ℕ)
      (_ : m = 3954 + off + t.val) (hmlt : m < posCoreWires), α₅ (rCore ⟨m, hmlt⟩) =
        basisBits 8 ⟨regVal ((rSubPayloadCore rCoreL).slice off 8 hoff) βL,
          regVal_lt_two_pow _ _⟩ t := fun off hoff t m hm _ ↦ by
    have hreg : regVal ((rSubPayloadCore rCore).slice off 8 hoff) α₅ =
        regVal ((rSubPayloadCore rCoreL).slice off 8 hoff) βL :=
      regVal_congr_cross ((rSubPayloadCore rCore).slice off 8 hoff)
        ((rSubPayloadCore rCoreL).slice off 8 hoff) α₅ βL fun u ↦ by
          rw [QRegister.slice_apply, QRegister.slice_apply]
          exact hSubEqL _
    rw [show (⟨regVal ((rSubPayloadCore rCoreL).slice off 8 hoff) βL,
      regVal_lt_two_pow _ _⟩ : Fin (2 ^ 8)) =
        ⟨regVal ((rSubPayloadCore rCore).slice off 8 hoff) α₅,
          regVal_lt_two_pow _ _⟩ from Fin.ext hreg.symm,
      hbitsOfReg ((rSubPayloadCore rCore).slice off 8 hoff) t, QRegister.slice_apply]
    dsimp only [rSubPayloadCore]
    rw [QRegister.slice_apply]
    exact congrArg (α₅ ∘ rCore.wires) (Fin.ext (by dsimp; omega))
  have hGe216 : ge216Bit (α₅ (rCore ⟨3963, by decide⟩)) (α₅ (rCore ⟨3964, by decide⟩))
      (α₅ (rCore ⟨3965, by decide⟩)) (α₅ (rCore ⟨3966, by decide⟩)) (α₅ (rCore ⟨3967, by decide⟩)) =
      if 216 ≤ regVal (rNucIdx rCoreL) βL then 1 else 0 := by
    rw [hbSlice 6 (by decide) ⟨3, by decide⟩ 3963 rfl (by decide),
      hbSlice 6 (by decide) ⟨4, by decide⟩ 3964 rfl (by decide),
      hbSlice 6 (by decide) ⟨5, by decide⟩ 3965 rfl (by decide),
        hbSlice 6 (by decide) ⟨6, by decide⟩ 3966 rfl (by decide),
      hbSlice 6 (by decide) ⟨7, by decide⟩ 3967 rfl (by decide)]
    exact ge216Bit_eq_decide ⟨regVal (rNucIdx rCoreL) βL, regVal_lt_two_pow _ _⟩
  have hGe218 : ge218Bit (α₅ (rCore ⟨3969, by decide⟩)) (α₅ (rCore ⟨3970, by decide⟩))
      (α₅ (rCore ⟨3971, by decide⟩)) (α₅ (rCore ⟨3972, by decide⟩)) (α₅ (rCore ⟨3973, by decide⟩))
      (α₅ (rCore ⟨3974, by decide⟩)) (α₅ (rCore ⟨3975, by decide⟩)) =
      if 218 ≤ regVal (rAnchorIdx rCoreL) βL then 1 else 0 := by
    rw [hbSlice 14 (by decide) ⟨1, by decide⟩ 3969 rfl (by decide),
      hbSlice 14 (by decide) ⟨2, by decide⟩ 3970 rfl (by decide),
      hbSlice 14 (by decide) ⟨3, by decide⟩ 3971 rfl (by decide),
        hbSlice 14 (by decide) ⟨4, by decide⟩ 3972 rfl (by decide),
      hbSlice 14 (by decide) ⟨5, by decide⟩ 3973 rfl (by decide),
        hbSlice 14 (by decide) ⟨6, by decide⟩ 3974 rfl (by decide),
      hbSlice 14 (by decide) ⟨7, by decide⟩ 3975 rfl (by decide)]
    exact ge218Bit_eq_decide ⟨regVal (rAnchorIdx rCoreL) βL, regVal_lt_two_pow _ _⟩
  have hGe217 : ge217Bit (α₅ (rCore ⟨3976, by decide⟩)) (α₅ (rCore ⟨3977, by decide⟩))
      (α₅ (rCore ⟨3978, by decide⟩)) (α₅ (rCore ⟨3979, by decide⟩)) (α₅ (rCore ⟨3980, by decide⟩))
      (α₅ (rCore ⟨3981, by decide⟩)) (α₅ (rCore ⟨3982, by decide⟩)) (α₅ (rCore ⟨3983, by decide⟩)) =
      if 217 ≤ regVal (rPartnerIdx rCoreL) βL then 1 else 0 := by
    rw [hbSlice 22 (by decide) ⟨0, by decide⟩ 3976 rfl (by decide),
      hbSlice 22 (by decide) ⟨1, by decide⟩ 3977 rfl (by decide),
      hbSlice 22 (by decide) ⟨2, by decide⟩ 3978 rfl (by decide),
        hbSlice 22 (by decide) ⟨3, by decide⟩ 3979 rfl (by decide),
      hbSlice 22 (by decide) ⟨4, by decide⟩ 3980 rfl (by decide),
        hbSlice 22 (by decide) ⟨5, by decide⟩ 3981 rfl (by decide),
      hbSlice 22 (by decide) ⟨6, by decide⟩ 3982 rfl (by decide),
        hbSlice 22 (by decide) ⟨7, by decide⟩ 3983 rfl (by decide)]
    exact ge217Bit_eq_decide ⟨regVal (rPartnerIdx rCoreL) βL, regVal_lt_two_pow _ _⟩
  have hKeepVal : bitsVal (fun k : Fin 30 ↦
    α₅ (rCore ⟨3986 + k.val, by dsimp [posCoreWires]; omega⟩)) =
      regVal (rTailKeep30 rCoreL) βL := by
    refine (congrArg bitsVal (funext fun k ↦ ?_)).trans
      (regVal_congr_cross (rTailKeep30 rCore) (rTailKeep30 rCoreL) α₅ βL fun _ ↦ hSubEqL _)
    dsimp only [rTailKeep30, rSubPayloadCore]
    simp only [QRegister.slice_apply]
    exact congrArg (α₅ ∘ rCore.wires) (Fin.ext (by dsimp; omega))
  have hB29 : B ≤ 29 := by omega
  have hThreshEq :
      2 ^ (29 - B) + 2 ^ (30 - B) * bitsVal (fun j : Fin B ↦ α₅ (rOutTop ⟨j.val, by omega⟩)) =
        k6MidMagThresholdB B hB1 hB29 (k6EffWord31 idx) :=
    congrArg (fun v : ℕ ↦ 2 ^ (29 - B) + 2 ^ (30 - B) * v)
      (congrArg bitsVal (funext fun j ↦ hOutEff ⟨j.val, by omega⟩))
  have hSignOut : α₅ (rOutTop ⟨B, by omega⟩) = k6EffWord31 idx ⟨30, by decide⟩ := by
    simpa only [Nat.sub_add_cancel (by omega : B ≤ 30)] using hOutEff ⟨B, by omega⟩
  rw [cKickZeroSub34_eval_mulVec_ket B hB1 hB27 rCore rOutTop rScr34 hCOut hCS hOutS α₅ hScr5]
  refine congrArg (· • ket α₅) ?_
  have hMidEq : midKickPhaseBitB B rCore rOutTop α₅ =
      if k6MidPhaseBitSpecB B hB1 hB29 slot2SwappedTo0 x then 1 else 0 := by
    dsimp only [midKickPhaseBitB]
    rw [hGe216, hGe218, hGe217, hKeepVal, hThreshEq, hSignOut, tailDecision11Bit_eq_bool]
    have hSlot2 : α₅ (rCore ⟨3950, by decide⟩) = βL (wSlot2Core rCoreL) :=
      hCoreHigh ⟨3950, by dsimp [posCoreWires]; omega⟩ (by dsimp; omega)
    have hSlot1 : α₅ (rCore ⟨3949, by decide⟩) = βL (wSlot1Core rCoreL) :=
      hCoreHigh ⟨3949, by dsimp [posCoreWires]; omega⟩ (by dsimp; omega)
    have hSlot0 : α₅ (rCore ⟨3948, by decide⟩) = βL (wSlot0Core rCoreL) :=
      hCoreHigh ⟨3948, by dsimp [posCoreWires]; omega⟩ (by dsimp; omega)
    have hSubRej : α₅ (rCore ⟨4016, by decide⟩) = βL (wSubReject rCoreL) := hSubEqL ⟨62, by decide⟩
    have hHead : α₅ (rCore ⟨3984, by decide⟩) = βL (wIsHead rCoreL) := hSubEqL ⟨30, by decide⟩
    have hRejZ : α₅ (rCore ⟨4033, by decide⟩) = βL (wRejectZero rCoreL) := hSubEqL ⟨79, by decide⟩
    have hNotGe : ∀ a b : ℕ,
        Bool.not ((if b ≤ a then (1 : ZMod 2) else 0) == 1) = decide (a < b) := fun a b ↦ by
      by_cases hp : b ≤ a
      · simp only [hp, ↓reduceIte, Nat.not_lt.mpr hp, decide_false]
        rfl
      · simp only [hp, ↓reduceIte, Nat.lt_of_not_ge hp, decide_true]
        rfl
    have hKeepDec : ∀ a b : ℕ, ((if a < b then (1 : ZMod 2) else 0) == 1) = decide (a < b) :=
      fun a b ↦ by
        by_cases hk : a < b
        · simp only [hk, ↓reduceIte, decide_true]
          rfl
        · simp only [hk, ↓reduceIte, decide_false]
          rfl
    rw [hSlot2, hSlot1, hSlot0, hSubRej, hHead, hRejZ, hNotGe _ 216, hNotGe _ 218, hNotGe _ 217,
      hKeepDec, show ((1 :
        ZMod 2) == 1) = true from rfl, Bool.true_and]
    rfl
  have hSpecIrrel : k6MidPhaseBitSpecB B hB1 hB29 slot2SwappedTo0 x =
      k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0 x := rfl
  rw [hMidEq, hSpecIrrel]
  by_cases hb : k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0 x
  · simp [hb]
  · simp [hb]

theorem k6PadF7_sum_eq (B : ℕ) (_hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (f7Top : Fin (B + 1) → Bool) (tbl : Fin 31 → ZMod 2) :
    (∑ b : Fin 31, if k6PadF7 B f7Top b then tbl b else 0) =
      ∑ j : Fin (B + 1), if f7Top j then tbl ⟨(30 - B) + j.val, by omega⟩ else 0 := by
  have hsum : ∀ {M N : ℕ} (hMN : M = N) (f : Fin M → ZMod 2),
      (∑ i : Fin M, f i) = ∑ j : Fin N, f ⟨j.val, hMN.symm ▸ j.isLt⟩ := by
    rintro _ _ rfl _
    rfl
  rw [hsum (by omega : 31 = (30 - B) + (B + 1))
    (fun b ↦ if k6PadF7 B f7Top b then tbl b else 0), Fin.sum_univ_add,
    Finset.sum_eq_zero (fun i _ ↦ ite_eq_right (by
      dsimp only [k6PadF7]
      rw [dite_eq_right (by rw [Fin.val_castAdd]; omega)]
      decide)),
    zero_add]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hjIdx : (⟨(Fin.natAdd (30 - B) j).val, by omega⟩ : Fin 31) = ⟨(30 - B) + j.val, by omega⟩ :=
    Fin.ext (Fin.val_natAdd (30 - B) j)
  have hw : k6PadF7 B f7Top ⟨(30 - B) + j.val, by omega⟩ = f7Top j := by
    dsimp only [k6PadF7]
    rw [dite_eq_left (by omega : 30 - B ≤ (30 - B) + j.val)]
    exact congrArg f7Top (Fin.ext (by dsimp; omega))
  rw [hjIdx, hw]

theorem vClean3_eq_stream0 {n mClean : ℕ} (B : ℕ) (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n) (γ₀ : BitAssignment n) :
    vClean3 B rCore rOrbit16 rClean γ₀ = vCleanStream B 0 rCore rOrbit16 rClean γ₀ := by
  funext k
  dsimp [vClean3, vCleanStream]

set_option maxRecDepth 512

end ConfigMidK6Sub126

end MidK6Sub126

end
end MidK6Sub126

end QuantumComputation.Specs.StoppingPowerSolution
