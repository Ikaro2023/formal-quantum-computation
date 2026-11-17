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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WeightedCsa3Gen

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosSlots24OrbitToggleFastM
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24OrbitToggleFastM (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace PosSlots24OrbitToggleFastM

open Operator QProg Matrix HermitianMat _root_.DynamicCircuit DynCircuitExt
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.

/-- Zero-extend `β : BitAssignment N` to `BitAssignment M` by setting trailing wires `[N .. M)`
  to `0`. -/
def padZeroRightBits {N M : ℕ} (β : BitAssignment N) : BitAssignment M :=
  fun w ↦ if hw : w.val < N then β ⟨w.val, hw⟩ else 0

theorem padZeroRightBits_lt {N M : ℕ} (β : BitAssignment N) {w : Wire M} (hw : w.val < N) :
    padZeroRightBits β w = β ⟨w.val, hw⟩ := dite_eq_left hw

theorem padZeroRightBits_injective {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (padZeroRightBits (N := N) (M := M)) := fun _ _ h ↦
  funext fun u ↦ by
    simpa only [padZeroRightBits, dite_eq_left u.isLt, Fin.eta] using
      congrFun h ⟨u.val, lt_of_lt_of_le u.isLt hNM⟩

theorem padZeroRightBits_update {N M : ℕ} (hNM : N ≤ M) (β : BitAssignment N)
    (q : Wire N) (v : ZMod 2) :
    padZeroRightBits (M := M) (Function.update β q v) =
      Function.update (padZeroRightBits (M := M) β) ⟨q.val, lt_of_lt_of_le q.isLt hNM⟩ v := by
  funext w
  by_cases hq : w.val = q.val
  · obtain rfl : w = ⟨q.val, lt_of_lt_of_le q.isLt hNM⟩ := Fin.ext hq
    simp [padZeroRightBits, q.isLt]
  · have hneM : w ≠ ⟨q.val, lt_of_lt_of_le q.isLt hNM⟩ :=
      fun e ↦ hq (congrArg (fun x : Fin M ↦ x.val) e)
    by_cases hw : w.val < N
    · simp [padZeroRightBits, hw, hneM,
        Function.update_of_ne (fun e : (⟨w.val, hw⟩ : Wire N) = q ↦
          hq (congrArg (fun x : Fin N ↦ x.val) e))]
    · simp [padZeroRightBits, hw, hneM]

theorem cleanRem_padZeroRightBits_iff {N M : ℕ} (hNM : N ≤ M) (rem : ℕ) (β : BitAssignment N) :
    cleanRem N (rem - (M - N)) β ↔ cleanRem M rem (padZeroRightBits (M := M) β) :=
  ⟨fun h w hw ↦ if hlt : w.val < N then by
      simpa only [padZeroRightBits, dite_eq_left hlt] using h ⟨w.val, hlt⟩ (by dsimp; omega)
    else by simp [padZeroRightBits, dite_eq_right hlt],
   fun h u hu ↦ by
    simpa only [padZeroRightBits, dite_eq_left u.isLt, Fin.eta] using
      h ⟨u.val, lt_of_lt_of_le u.isLt hNM⟩ (by dsimp; have := u.isLt; omega)⟩

def narrowCliffProg {M : ℕ} (N : ℕ) : (c : CliffProg M) → c.SupportsBelow N → CliffProg N
  | .nil, _ => .nil
  | .x q, hq => .x ⟨q.val, hq⟩
  | .cnot c t hne, ⟨hc, ht⟩ =>
      .cnot ⟨c.val, hc⟩ ⟨t.val, ht⟩ (fun e ↦ hne (Fin.ext (congrArg (fun x : Fin N ↦ x.val) e)))
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => .seq (narrowCliffProg N c₁ h₁) (narrowCliffProg N c₂ h₂)

theorem eval_narrowCliffProg_padZeroRightBits {N M : ℕ} (hNM : N ≤ M) :
    ∀ (c : CliffProg M) (hc : c.SupportsBelow N) (β : BitAssignment N),
      c.eval (padZeroRightBits (M := M) β) =
        padZeroRightBits (M := M) ((narrowCliffProg N c hc).eval β)
  | .nil, _, _ => rfl
  | .x q, hq, β => by
      dsimp only [narrowCliffProg, CliffProg.eval]
      rw [padZeroRightBits_update hNM β ⟨q.val, hq⟩, padZeroRightBits_lt β hq]
  | .cnot c t _, ⟨hc, ht⟩, β => by
      dsimp only [narrowCliffProg, CliffProg.eval]
      rw [padZeroRightBits_update hNM β ⟨t.val, ht⟩,
        padZeroRightBits_lt β ht, padZeroRightBits_lt β hc]
  | .seq c₁ c₂, ⟨h₁, h₂⟩, β => by
      simp only [narrowCliffProg, CliffProg.eval,
        eval_narrowCliffProg_padZeroRightBits hNM c₁ h₁ β,
        eval_narrowCliffProg_padZeroRightBits hNM c₂ h₂]

/-- Prop-valued wire-bound predicate (`all wires < bound`) for `TempPhaseProg M`. -/
def supportsBelowProp {M : ℕ} (bound : ℕ) : TempPhaseProg M → Prop
  | .nil => True
  | .cliff c => c.SupportsBelow bound
  | .z q => q.val < bound
  | .seq p₁ p₂ => supportsBelowProp bound p₁ ∧ supportsBelowProp bound p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      c₁.val < bound ∧ c₂.val < bound ∧ anc.val < bound ∧ supportsBelowProp bound body

def narrowTempPhaseProg {M : ℕ} (N : ℕ) :
    (p : TempPhaseProg M) → supportsBelowProp N p → TempPhaseProg N
  | .nil, _ => .nil
  | .cliff c, hc => .cliff (narrowCliffProg N c hc)
  | .z q, hq => .z ⟨q.val, hq⟩
  | .seq p₁ p₂, ⟨h₁, h₂⟩ => .seq (narrowTempPhaseProg N p₁ h₁) (narrowTempPhaseProg N p₂ h₂)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, ⟨hc₁, hc₂, hanc, hb⟩ =>
      .tempAnd ⟨c₁.val, hc₁⟩ ⟨c₂.val, hc₂⟩ ⟨anc.val, hanc⟩
        (fun e ↦ h₁₂ (Fin.ext (congrArg (fun x : Fin N ↦ x.val) e)))
        (fun e ↦ h₁a (Fin.ext (congrArg (fun x : Fin N ↦ x.val) e)))
        (fun e ↦ h₂a (Fin.ext (congrArg (fun x : Fin N ↦ x.val) e)))
        (narrowTempPhaseProg N body hb)

@[simp] theorem countTempAnd_narrowTempPhaseProg {M : ℕ} (N : ℕ) :
    ∀ (p : TempPhaseProg M) (hp : supportsBelowProp N p),
      (narrowTempPhaseProg N p hp).countTempAnd = p.countTempAnd
  | .nil, _ | .cliff _, _ | .z _, _ => rfl
  | .seq p₁ p₂, ⟨h₁, h₂⟩ => by
      simp [narrowTempPhaseProg, TempPhaseProg.countTempAnd,
        countTempAnd_narrowTempPhaseProg N p₁ h₁, countTempAnd_narrowTempPhaseProg N p₂ h₂]
  | .tempAnd _ _ _ _ _ _ body, ⟨_, _, _, hb⟩ => by
      simp [narrowTempPhaseProg, TempPhaseProg.countTempAnd,
        countTempAnd_narrowTempPhaseProg N body hb]

private theorem padZeroRightBits_update_and {N M : ℕ} (hNM : N ≤ M) (β : BitAssignment N)
    {c₁ c₂ anc : Wire M} (hc₁ : c₁.val < N) (hc₂ : c₂.val < N) (hanc : anc.val < N) :
    Function.update (padZeroRightBits (M := M) β) anc
      (padZeroRightBits (M := M) β anc +
        padZeroRightBits (M := M) β c₁ * padZeroRightBits (M := M) β c₂) =
    padZeroRightBits (M := M) (Function.update β ⟨anc.val, hanc⟩
      (β ⟨anc.val, hanc⟩ + β ⟨c₁.val, hc₁⟩ * β ⟨c₂.val, hc₂⟩)) := by
  rw [padZeroRightBits_update hNM β ⟨anc.val, hanc⟩, Fin.eta,
    padZeroRightBits_lt β hanc, padZeroRightBits_lt β hc₁, padZeroRightBits_lt β hc₂]

theorem evalBits_narrowTempPhaseProg_padZeroRightBits {N M : ℕ} (hNM : N ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : supportsBelowProp N p) (β : BitAssignment N),
      p.evalBits (padZeroRightBits (M := M) β) =
        padZeroRightBits (M := M) ((narrowTempPhaseProg N p hp).evalBits β)
  | .nil, _, _ | .z _, _, _ => rfl
  | .cliff c, hc, β => eval_narrowCliffProg_padZeroRightBits hNM c hc β
  | .seq p₁ p₂, ⟨h₁, h₂⟩, β => by
      simp only [narrowTempPhaseProg, TempPhaseProg.evalBits,
        evalBits_narrowTempPhaseProg_padZeroRightBits hNM p₁ h₁ β,
        evalBits_narrowTempPhaseProg_padZeroRightBits hNM p₂ h₂]
  | .tempAnd c₁ c₂ anc _ _ _ body, ⟨hc₁, hc₂, hanc, hb⟩, β => by
      dsimp only [narrowTempPhaseProg, TempPhaseProg.evalBits]
      rw [padZeroRightBits_update_and hNM β hc₁ hc₂ hanc,
        evalBits_narrowTempPhaseProg_padZeroRightBits hNM body hb,
        padZeroRightBits_update_and hNM _ hc₁ hc₂ hanc]

theorem evalSign_narrowTempPhaseProg_padZeroRightBits {N M : ℕ} (hNM : N ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : supportsBelowProp N p) (β : BitAssignment N),
      p.evalSign (padZeroRightBits (M := M) β) = (narrowTempPhaseProg N p hp).evalSign β
  | .nil, _, _ | .cliff _, _, _ => rfl
  | .z q, hq, β => padZeroRightBits_lt β hq
  | .seq p₁ p₂, ⟨h₁, h₂⟩, β => by
      simp only [narrowTempPhaseProg, TempPhaseProg.evalSign,
        evalSign_narrowTempPhaseProg_padZeroRightBits hNM p₁ h₁ β,
        evalBits_narrowTempPhaseProg_padZeroRightBits hNM p₁ h₁ β,
        evalSign_narrowTempPhaseProg_padZeroRightBits hNM p₂ h₂]
  | .tempAnd c₁ c₂ anc _ _ _ body, ⟨hc₁, hc₂, hanc, hb⟩, β => by
      dsimp only [narrowTempPhaseProg, TempPhaseProg.evalSign]
      rw [padZeroRightBits_update_and hNM β hc₁ hc₂ hanc]
      exact evalSign_narrowTempPhaseProg_padZeroRightBits hNM body hb _

theorem validCleanRem_narrowTempPhaseProg {N M : ℕ} (hNM : N ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : supportsBelowProp N p) (rem : ℕ),
      ValidCleanRem M rem p → ValidCleanRem N (rem - (M - N)) (narrowTempPhaseProg N p hp)
  | .nil, _, _, _ | .cliff _, _, _, _ | .z _, _, _, _ => trivial
  | .seq p₁ p₂, ⟨h₁, h₂⟩, rem, ⟨remMid, _, hv₁, hv₂, hpres⟩ =>
      ⟨remMid - (M - N), by omega, validCleanRem_narrowTempPhaseProg hNM p₁ h₁ rem hv₁,
        validCleanRem_narrowTempPhaseProg hNM p₂ h₂ remMid hv₂, fun β hβ ↦ by
        have hm := hpres _ ((cleanRem_padZeroRightBits_iff hNM rem β).mp hβ)
        rw [evalBits_narrowTempPhaseProg_padZeroRightBits hNM p₁ h₁ β] at hm
        exact (cleanRem_padZeroRightBits_iff hNM remMid _).mpr hm⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, ⟨hc₁, hc₂, hanc, hb⟩, rem, ⟨_, hvB, hpresB⟩ => by
      have hr : N - (anc.val + 1) = (M - (anc.val + 1)) - (M - N) := by omega
      refine ⟨by change N - (rem - (M - N)) ≤ anc.val; omega,
        hr ▸ validCleanRem_narrowTempPhaseProg hNM body hb _ hvB, fun β₁ hcl₁ ↦ ?_⟩
      have h := hpresB _ ((cleanRem_padZeroRightBits_iff hNM _ β₁).mp (hr ▸ hcl₁))
      simpa only [evalBits_narrowTempPhaseProg_padZeroRightBits hNM body hb β₁,
        padZeroRightBits_lt _ hc₁, padZeroRightBits_lt _ hc₂,
        padZeroRightBits_lt _ hanc] using h

end PosSlots24OrbitToggleFastM
end
end PosSlots24OrbitToggleFastM

section PosSlots24PartnerMuxZeroT123
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24PartnerMuxZeroT123 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace PosSlots24PartnerMuxZeroT123

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit hiding
  ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (bit_cases)
open BchCubeDecoder
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288

theorem zmod2_sign_eq (z : ZMod 2) :
    (if decide (z = 1) then (-1 : ℂ) else 1) = (-1 : ℂ) ^ z.val := by
  rcases bit_cases z with rfl | rfl <;> norm_num

theorem bitsVal_sum {d : ℕ} (f : Fin d → ZMod 2) :
    bitsVal f = ∑ j : Fin d, (f j).val * 2 ^ j.val := rfl

/-- Rooted binary-to-unary expansion on `d` address bits (`2 ^ d - 1` `tempAnd`s, expanding ANY
pre-computed root bit `β ⟨cur, _⟩` onto `[cur .. cur + 2 ^ d)` as
`(if k = bitsVal addr then β ⟨cur, _⟩ else 0)`). -/
def ctxRootedUnaryTree {M : ℕ} :
    (d : ℕ) → (cur : ℕ) → (hcur : cur + 2 ^ d ≤ M) →
    (addr : Fin d → Wire M) → (haddr : ∀ j, (addr j).val < cur) →
    TempCtx M
  | 0, _, _, _, _ => .hole
  | d + 1, cur, hcur, addr, haddr =>
      (ctxRootedUnaryTree d cur (tree_cur_step hcur)
        (fun j ↦ addr j.castSucc) (fun j ↦ haddr j.castSucc)).append
        (ctxUnarySplitRange cur (2 ^ d) (addr (Fin.last d)) (haddr (Fin.last d))
          (tree_split_step hcur) (2 ^ d) le_rfl)

theorem ctxRootedUnaryTree_countTempAnd {M : ℕ} :
    ∀ (d cur : ℕ) (hcur : cur + 2 ^ d ≤ M)
      (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < cur),
      (ctxRootedUnaryTree d cur hcur addr haddr).countTempAnd = 2 ^ d - 1
  | 0, _, _, _, _ => rfl
  | d + 1, cur, _, _, _ => by
      dsimp only [ctxRootedUnaryTree]
      rw [TempCtx.append_countTempAnd, ctxRootedUnaryTree_countTempAnd d cur,
        ctxUnarySplitRange_countTempAnd]
      have := Nat.one_le_pow d 2 (by omega)
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega

theorem ScopedBlock.ctxRootedUnaryTree_block {M : ℕ} :
    ∀ (d cur : ℕ) (hcur : cur + 2 ^ d ≤ M)
      (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < cur)
      (leaf body : TempPhaseProg M) (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (cur + 2 ^ d)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - (cur + 1)) (fun β ↦ sBody (setup β)) leaf
          ((ctxRootedUnaryTree d cur hcur addr haddr).plug body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - (cur + 1)) β →
          cleanRem M (M - (cur + 2 ^ d)) (setup β) ∧
          (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
          (∀ (k : ℕ) (hk : k < 2 ^ d),
            setup β ⟨cur + k, by omega⟩ =
              if k = bitsVal (fun j ↦ β (addr j)) then β ⟨cur, by omega⟩ else 0)
  | 0, cur, _, _, _, _, _, _, hBody =>
      ⟨id, hBody.cast_rem (by norm_num), fun β hβ ↦ ⟨hβ, fun _ _ ↦ rfl, fun k hk ↦ by
        obtain rfl : k = 0 := by omega
        simp⟩⟩
  | d + 1, cur, hcur, addr, haddr, leaf, body, sBody, hBody => by
      let L := 2 ^ d
      have hL2 : 2 ^ (d + 1) = 2 * L := by dsimp [L]; ring
      obtain ⟨sSplit, hSplit, hSpecSplit⟩ :=
        ScopedBlock.withUnarySplitRange_block cur L (addr (Fin.last d)) (haddr (Fin.last d))
          (tree_split_step hcur) L le_rfl leaf body sBody (hBody.cast_rem (by omega))
      obtain ⟨sTree, hTree, hSpecTree⟩ := ScopedBlock.ctxRootedUnaryTree_block d cur
          (tree_cur_step hcur) (fun j ↦ addr j.castSucc) (fun j ↦ haddr j.castSucc) leaf _
          (fun β ↦ sBody (sSplit β)) (hSplit.cast_rem (by omega))
      have hPlugEq : (ctxRootedUnaryTree (d + 1) cur hcur addr haddr).plug body =
          (ctxRootedUnaryTree d cur (tree_cur_step hcur) (fun j ↦ addr j.castSucc)
            (fun j ↦ haddr j.castSucc)).plug (withUnarySplitRange cur L (addr (Fin.last d))
              (haddr (Fin.last d)) (tree_split_step hcur) L le_rfl body) := by
        simp [ctxRootedUnaryTree, L, TempCtx.append_plug, ctxUnarySplitRange_plug]
      refine ⟨fun β ↦ sSplit (sTree β), hPlugEq ▸ hTree, fun β hβ ↦ ?_⟩
      obtain ⟨hcl1, hbelow1, hunary1⟩ := hSpecTree β hβ
      obtain ⟨hcl2, hbelow2, hsplit2⟩ := hSpecSplit (sTree β)
        (by simpa [show cur + 2 * L - L = cur + 2 ^ d by dsimp [L]; omega] using hcl1)
      have hmsb : sTree β (addr (Fin.last d)) = β (addr (Fin.last d)) :=
        hbelow1 _ (haddr (Fin.last d))
      have splitTop : bitsVal (fun j ↦ β (addr j)) =
          bitsVal (fun j ↦ β (addr j.castSucc)) + L * (β (addr (Fin.last d))).val := by
        simp only [bitsVal_sum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, L]
        ring
      have hlo_lt : bitsVal (fun j ↦ β (addr j.castSucc)) < L := bitsVal_lt_two_pow _
      refine ⟨(show M - (cur + 2 * L) = M - (cur + 2 ^ (d + 1)) by omega) ▸ hcl2,
        fun w hw ↦ (hbelow2 w (Or.inl (by omega))).trans (hbelow1 w hw), fun k hk ↦ ?_⟩
      dsimp only
      let r0 : ZMod 2 := β ⟨cur, by omega⟩
      have hgoal0 :
          (if k = bitsVal (fun j ↦ β (addr j)) then β ⟨cur, by omega⟩ else (0 : ZMod 2)) =
          if k = bitsVal (fun j ↦ β (addr j)) then r0 else 0 := rfl
      rw [hgoal0]
      by_cases hkL : k < L
      · have hun1 : sTree β ⟨cur + k, by omega⟩ =
            if k = bitsVal (fun j ↦ β (addr j.castSucc)) then r0 else 0 := hunary1 k hkL
        rw [(hsplit2 k (by omega) hkL).1, hun1, hmsb, splitTop]
        rcases bit_cases (β (addr (Fin.last d))) with hb | hb <;>
          simp only [hb, ZMod.val_zero, ZMod.val_one, mul_zero, mul_one, add_zero,
            show k ≠ bitsVal (fun j ↦ β (addr j.castSucc)) + L by omega,
            ↓reduceIte, CharTwo.add_self_eq_zero, r0]
      · let i := k - L
        have hi : i < L := by omega
        have hw_eq : (⟨cur + k, by omega⟩ : Wire M) = ⟨cur + L + i, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have hun2 : sTree β ⟨cur + i, by omega⟩ =
            if i = bitsVal (fun j ↦ β (addr j.castSucc)) then r0 else 0 := hunary1 i hi
        rw [hw_eq, (hsplit2 i (by omega) hi).2, hun2, hmsb, splitTop,
          show k = L + i by omega]
        rcases bit_cases (β (addr (Fin.last d))) with hb | hb
        · simp only [hb, ZMod.val_zero, mul_zero, add_zero,
            show L + i ≠ bitsVal (fun j ↦ β (addr j.castSucc)) by omega, ↓reduceIte]
        · simp only [hb, ZMod.val_one, mul_one]
          by_cases hieq : i = bitsVal (fun j ↦ β (addr j.castSucc))
          · rw [hieq, add_comm, ite_eq_left rfl, ite_eq_left rfl]
          · rw [ite_eq_right hieq, ite_eq_right (by omega)]

theorem bitsVal_prefix_succ (b : Fin 8 → ZMod 2) (d : ℕ) (hd : d + 1 ≤ 8) :
    bitsVal (fun j : Fin (d + 1) ↦ b ⟨j.val, by omega⟩) =
      bitsVal (fun j : Fin d ↦ b ⟨j.val, by omega⟩) + (b ⟨d, by omega⟩).val * 2 ^ d := by
  rw [bitsVal_sum, Fin.sum_univ_castSucc, bitsVal_sum]
  simp only [Fin.val_castSucc, Fin.val_last]

theorem bitsVal_eight (b : Fin 8 → ZMod 2) : bitsVal b = (b 0).val + 2 * (b 1).val + 4 *
    (b 2).val + 8 * (b 3).val + 16 * (b 4).val + 32 * (b 5).val + 64 * (b 6).val + 128 *
    (b 7).val := by
  change bitsVal (fun j : Fin 8 ↦ b ⟨j.val, by omega⟩) = _
  rw [bitsVal_prefix_succ b 7 (by omega), bitsVal_prefix_succ b 6 (by omega),
    bitsVal_prefix_succ b 5 (by omega), bitsVal_prefix_succ b 4 (by omega),
    bitsVal_prefix_succ b 3 (by omega), bitsVal_prefix_succ b 2 (by omega),
    bitsVal_prefix_succ b 1 (by omega), bitsVal_prefix_succ b 0 (by omega),
    show bitsVal (fun j : Fin 0 ↦ b ⟨j.val, by omega⟩) = 0 from rfl]
  change 0 + (b 0).val * 1 + (b 1).val * 2 + (b 2).val * 4 + (b 3).val * 8 +
    (b 4).val * 16 + (b 5).val * 32 + (b 6).val * 64 + (b 7).val * 128 = _
  ring

theorem ScopedBlock.tempBit_step {M : ℕ} (sOuter : BitAssignment M → BitAssignment M)
    (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur)
    (hc₂ : c₂.val < cur) {sInner : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) (fun β ↦ sOuter
    (sInner β)) leaf body) : ∃ sNext : BitAssignment M → BitAssignment M, ScopedBlock M
    (M - cur) (fun β ↦ sOuter (sNext β)) leaf (withTempBit c₁ c₂ ⟨cur, hcur⟩ h₁₂
    (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) body) ∧ ∀ β, sNext β = sInner
    (Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂)) := ⟨fun β ↦ sInner (Function.update β ⟨cur,
    hcur⟩ (β c₁ * β c₂)), ScopedBlock.withTempBit_block cur hcur c₁ c₂ h₁₂ hc₁ hc₂ hBody, fun
    _ ↦ rfl⟩

theorem ScopedBlock.cliffAlloc_step {M rem remIn : ℕ}
    (sOuter : BitAssignment M → BitAssignment M) (hremIn : remIn ≤ M) (hle : remIn ≤ rem)
    (c : CliffProg M) (hSupp : c.SupportsBelow (M - remIn))
    {sInner : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M remIn (fun β ↦ sOuter (sInner β)) leaf body) : ∃ sNext :
    BitAssignment M → BitAssignment M, ScopedBlock M rem (fun β ↦ sOuter (sNext β)) leaf
    (withCliffAlloc c body) ∧ ∀ β, sNext β = sInner (c.eval β) := ⟨fun β ↦ sInner (c.eval β),
    ScopedBlock.withCliffAlloc_block hremIn hle c hSupp hBody, fun _ ↦ rfl⟩

private theorem zm2_not_iff (x : ZMod 2) : 1 + x = 1 ↔ x = 0 := by
  rcases bit_cases x with rfl | rfl <;> decide

private theorem zm2_and_iff (x y : ZMod 2) : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide

private theorem zm2_andNot_iff (p x : ZMod 2) : p * x + p = 1 ↔ p = 1 ∧ x = 0 := by
  rcases bit_cases p with rfl | rfl <;> rcases bit_cases x with rfl | rfl <;> decide

private theorem zm2_andNot_iff' (p x : ZMod 2) : p + p * x = 1 ↔ p = 1 ∧ x = 0 :=
  add_comm p (p * x) ▸ zm2_andNot_iff p x

private theorem dyadic_bkt_eq {V k lo off : ℕ} {root : ZMod 2}
    (h1 : root = 1 → V = off + lo) (h0 : root ≠ 1 → off + k ≠ V) :
    (if k = lo then root else 0) = if off + k = V then 1 else 0 := by
  rcases bit_cases root with rfl | rfl
  · simp [ite_neg (h0 (by decide))]
  · have := h1 rfl
    simp only [show (off + k = V) ↔ (k = lo) from ⟨by omega, by omega⟩]

theorem dyadic218_block_bits (b : Fin 8 → ZMod 2) :
    let V := bitsVal b
    let p0 := b 7 * b 6
    let p1 := p0 * b 5 + p0
    let p2 := p1 * b 4
    let p3 := p2 * b 3
    let p4 := p3 * b 2 + p3
    let r5 := p4 * b 1 + p4
    (∀ k < 128, (if k = bitsVal (fun j : Fin 7 ↦ b ⟨j.val, by omega⟩) then
      (1 + b 7 : ZMod 2) else 0) = if k = V then 1 else 0) ∧
    (∀ k < 64, (if k = bitsVal (fun j : Fin 6 ↦ b ⟨j.val, by omega⟩) then
      (b 7 + p0 : ZMod 2) else 0) = if 128 + k = V then 1 else 0) ∧
    (∀ k < 16, (if k = bitsVal (fun j : Fin 4 ↦ b ⟨j.val, by omega⟩) then
      (p1 + p2 : ZMod 2) else 0) = if 192 + k = V then 1 else 0) ∧
    (∀ k < 8, (if k = bitsVal (fun j : Fin 3 ↦ b ⟨j.val, by omega⟩) then
      (p2 + p3 : ZMod 2) else 0) = if 208 + k = V then 1 else 0) ∧
    (∀ k < 2, (if k = bitsVal (fun j : Fin 1 ↦ b ⟨j.val, by omega⟩) then
      r5 else 0) = if 216 + k = V then 1 else 0) := by
  intro V p0 p1 p2 p3 p4 r5
  have := ZMod.val_lt (b 1); have := ZMod.val_lt (b 2); have := ZMod.val_lt (b 3)
  have := ZMod.val_lt (b 4); have := ZMod.val_lt (b 5); have := ZMod.val_lt (b 6)
  have := ZMod.val_lt (b 7)
  have hbOne (i : Fin 8) : b i = 1 ↔ (b i).val = 1 := by
    rcases bit_cases (b i) with h | h <;> simp [h]
  have hbZero (i : Fin 8) : b i = 0 ↔ (b i).val = 0 := by
    rcases bit_cases (b i) with h | h <;> simp [h]
  suffices ∀ (V0 lo7 lo6 lo4 lo3 lo1 : ℕ), lo1 < 2 →
      lo3 = lo1 + (b 1).val * 2 + (b 2).val * 4 → lo4 = lo3 + (b 3).val * 8 →
      lo6 = lo4 + (b 4).val * 16 + (b 5).val * 32 → lo7 = lo6 + (b 6).val * 64 →
      V0 = lo7 + (b 7).val * 128 →
      (∀ k < 128, (if k = lo7 then (1 + b 7 : ZMod 2) else 0) = if k = V0 then 1 else 0) ∧
      (∀ k < 64, (if k = lo6 then (b 7 + p0 : ZMod 2) else 0) = if 128 + k = V0 then 1 else 0) ∧
      (∀ k < 16, (if k = lo4 then (p1 + p2 : ZMod 2) else 0) = if 192 + k = V0 then 1 else 0) ∧
      (∀ k < 8, (if k = lo3 then (p2 + p3 : ZMod 2) else 0) = if 208 + k = V0 then 1 else 0) ∧
      (∀ k < 2, (if k = lo1 then r5 else 0) = if 216 + k = V0 then 1 else 0) from
    this V _ _ _ _ _ (bitsVal_lt_two_pow _)
      (by rw [bitsVal_prefix_succ b 2 (by omega), bitsVal_prefix_succ b 1 (by omega)]; rfl)
      (bitsVal_prefix_succ b 3 (by omega))
      (by rw [bitsVal_prefix_succ b 5 (by omega), bitsVal_prefix_succ b 4 (by omega)]; rfl)
      (bitsVal_prefix_succ b 6 (by omega)) (bitsVal_prefix_succ b 7 (by omega))
  intro V0 lo7 lo6 lo4 lo3 lo1 _ _ _ _ _ _
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · simpa only [Nat.zero_add] using
      dyadic_bkt_eq (V := V0) (k := k) (lo := lo7) (off := 0) (root := 1 + b 7)
        (fun hr ↦ by simp only [zm2_not_iff, hbZero] at hr; omega)
        (fun hr ↦ by simp only [ne_eq, zm2_not_iff, hbZero] at hr; omega)
  · exact dyadic_bkt_eq
      (fun hr ↦ by simp only [p0, zm2_andNot_iff', hbOne, hbZero] at hr; omega)
      (fun hr ↦ by simp only [ne_eq, p0, zm2_andNot_iff', hbOne, hbZero] at hr; omega)
  · exact dyadic_bkt_eq
      (fun hr ↦ by
        simp only [p2, p1, p0, zm2_and_iff, zm2_andNot_iff, zm2_andNot_iff', hbOne, hbZero] at hr
        omega)
      (fun hr ↦ by
        simp only [ne_eq, p2, p1, p0, zm2_and_iff, zm2_andNot_iff, zm2_andNot_iff',
          hbOne, hbZero] at hr
        omega)
  · exact dyadic_bkt_eq
      (fun hr ↦ by
        simp only [p3, p2, p1, p0, zm2_and_iff, zm2_andNot_iff, zm2_andNot_iff',
          hbOne, hbZero] at hr
        omega)
      (fun hr ↦ by
        simp only [ne_eq, p3, p2, p1, p0, zm2_and_iff, zm2_andNot_iff, zm2_andNot_iff',
          hbOne, hbZero] at hr
        omega)
  · exact dyadic_bkt_eq
      (fun hr ↦ by
        simp only [r5, p4, p3, p2, p1, p0, zm2_and_iff, zm2_andNot_iff, hbOne, hbZero] at hr
        omega)
      (fun hr ↦ by
        simp only [ne_eq, r5, p4, p3, p2, p1, p0, zm2_and_iff, zm2_andNot_iff, hbOne, hbZero] at hr
        omega)

theorem RestoresAll.rootedTree {M : ℕ} :
    ∀ (d cur : ℕ) (hcur : cur + 2 ^ d ≤ M)
      (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < cur),
      RestoresAll (ctxRootedUnaryTree d cur hcur addr haddr)
  | 0, _, _, _, _ => RestoresAll.hole
  | d + 1, cur, _, _, _ =>
      RestoresAll.append (RestoresAll.rootedTree d cur _ _ _)
        (RestoresAll.unarySplitRange _ _ _ _ _ _ _)

attribute [local irreducible] ctxRootedUnaryTree
theorem rAnchorIdx_apply_ofFin {n : ℕ} (rCore : QRegister posCoreWires n) (k : Fin 8) :
    rAnchorIdx rCore k = rCore (rAnchorIdx (QRegExt.ofFin posCoreWires) k) := rfl

set_option maxRecDepth 2000

end PosSlots24PartnerMuxZeroT123
end
end PosSlots24PartnerMuxZeroT123

section PosSlots24SpectatorPrunedPhase
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24SpectatorPrunedPhase (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

set_option maxRecDepth 4096

public section

namespace PosSlots24SpectatorPrunedPhase

open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open OctahedralOrbit
open CanonRank7Circuit
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN

attribute [local irreducible] lookup3xPow2Val copyXorRegCircuit

section TempPhaseMiddleKick

/-- `TempCtx` version of `withLitAnd` (`1` `tempAnd`, never touches wires outside `{c₁, c₂, ⟨cur,
  _⟩}`). -/
def ctxLitAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool) (c₂ : Wire M)
    (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) : TempCtx M :=
  let cFlip : CliffProg M := flipPair c₁ neg₁ c₂ neg₂
  (ctxCliffAlloc cFlip).append
    ((ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂)).append
      (ctxCliffAlloc cFlip))

theorem ctxLitAnd_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M) (neg₁ : Bool)
    (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur)
    (body : TempPhaseProg M) : (ctxLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂).plug body =
    withLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂ body := by
  simp [ctxLitAnd, TempCtx.append_plug, withLitAnd]

end TempPhaseMiddleKick

section AsymmetricBracketingCzMid

open MeasureBranchHadamardSem (bitSign sqrtHalf bit_cases)

theorem asymMid_eval_seq_mulVec {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) :=
  MeasureBranchHadamardSem.eval_seq_mulVec c₁ c₂ ψ

theorem asymMid_ket_CNOT {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [← mbh_ket_eq_ket, MeasureBranchHadamardSem.ket_CNOT, mbh_ket_eq_ket]

theorem asymMid_ket_H {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      sqrtHalf • (ket (Function.update β q 0) + bitSign (β q) • ket (Function.update β q 1)) := by
  simpa only [mbh_ket_eq_ket] using MeasureBranchHadamardSem.ket_H q β

def asymMid_czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.H b ;;ᶜ Circuit.CNOT a b h ;;ᶜ Circuit.H b

theorem asymMid_czCircuit_count_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (asymMid_czCircuit a b h).count PrimitiveGate.TOFF = 0 := by
  simp [asymMid_czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]

theorem asymMid_czCircuit_count_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (asymMid_czCircuit a b h).count PrimitiveGate.T = 0 := by
  simp [asymMid_czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]

theorem asymMid_sqrtHalf_mul_self_two : (sqrtHalf * sqrtHalf : ℂ) * 2 = 1 := by
  rw [show (sqrtHalf : ℂ) = ((√(1 / 2 : ℝ) : ℝ) : ℂ) by simp [sqrtHalf],
    ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem asymMid_ket_czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (asymMid_czCircuit a b h).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (β a * β b).val) • ket β := by
  let g0 := Function.update β b 0
  let g1 := Function.update β b 1
  have hg0b : g0 b = 0 := Function.update_self _ _ _
  have hg1b : g1 b = 1 := Function.update_self _ _ _
  have hg00 : Function.update g0 b 0 = g0 := Function.update_idem _ _ _
  have hg01 : Function.update g0 b 1 = g1 := Function.update_idem _ _ _
  have hg10 : Function.update g1 b 0 = g0 := Function.update_idem _ _ _
  have hg11 : Function.update g1 b 1 = g1 := Function.update_idem _ _ _
  have hH0 : (Circuit.H b).eval.1.mulVec (ket g0) = sqrtHalf • (ket g0 + bitSign 0 • ket g1) := by
    rw [asymMid_ket_H, hg0b, hg00, hg01]
  have hH1 : (Circuit.H b).eval.1.mulVec (ket g1) = sqrtHalf • (ket g0 + bitSign 1 • ket g1) := by
    rw [asymMid_ket_H, hg1b, hg10, hg11]
  have hg0a : g0 a = β a := Function.update_of_ne h _ _
  have hg1a : g1 a = β a := Function.update_of_ne h _ _
  dsimp only [asymMid_czCircuit]
  rw [asymMid_eval_seq_mulVec, asymMid_eval_seq_mulVec, asymMid_ket_H]
  change (Circuit.H b).eval.1.mulVec
      ((Circuit.CNOT a b h).eval.1.mulVec (sqrtHalf • (ket g0 + bitSign (β b) • ket g1))) = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    asymMid_ket_CNOT, asymMid_ket_CNOT, hg0a, hg1a,
    hg0b, hg1b, Matrix.mulVec_add, Matrix.mulVec_smul]
  rcases bit_cases (β a) with ha | ha <;> rcases bit_cases (β b) with hb | hb
  · rw [ha, add_zero, add_zero, hg00, hg11, hH0, hH1, hb]
    ext idx
    simp [bitSign, (hb ▸ rfl : g0 = Function.update β b (β b)).trans (Function.update_eq_self b β)]
    linear_combination (ket β idx) * asymMid_sqrtHalf_mul_self_two
  · rw [ha, add_zero, add_zero, hg00, hg11, hH0, hH1, hb]
    ext idx
    simp [bitSign, (hb ▸ rfl : g1 = Function.update β b (β b)).trans (Function.update_eq_self b β)]
    linear_combination (ket β idx) * asymMid_sqrtHalf_mul_self_two
  · rw [ha, show (0 : ZMod 2) + 1 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl,
      hg01, hg10, hH1, hH0, hb]
    ext idx
    simp [bitSign, (hb ▸ rfl : g0 = Function.update β b (β b)).trans (Function.update_eq_self b β)]
    linear_combination (ket β idx) * asymMid_sqrtHalf_mul_self_two
  · rw [ha, show (0 : ZMod 2) + 1 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl,
      hg01, hg10, hH1, hH0, hb]
    ext idx
    simp [bitSign, (hb ▸ rfl : g1 = Function.update β b (β b)).trans (Function.update_eq_self b β)]
    linear_combination -(ket β idx) * asymMid_sqrtHalf_mul_self_two

end AsymmetricBracketingCzMid

set_option maxRecDepth 512

end PosSlots24SpectatorPrunedPhase
end
end PosSlots24SpectatorPrunedPhase

section OrbitSandHeld46
local instance (priority := 1000000) instNeZeroTwoPow_OrbitSandHeld46 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace OrbitSandHeld46

section ConfigOrbitSandHeld46

set_option maxRecDepth 4096

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.
open MeasureBranchHadamardSem
  (ket projZeroAll projZeroAll_conjTranspose projZeroAll_eq_basisOutcomeProjector_zero)
open PosSlots24OrbitToggleFast288 hiding
  ite_pos ite_neg dite_pos dite_neg rawOrbitCoord128 orbitRankFin16 matrix_ext_ket
open PosSlots24SpectatorPrunedPhase (p2t_RealizesConstCleanUnitary)

local instance (priority := 100000) instLoc_OrbitSandHeld46_1InstNeZeroTwoPowHeld46
    (k : ℕ) : NeZero (2 ^ k) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

theorem constClean_of_embeddedCleanWorkspace {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k mClean : ℕ} (rData : QRegister k n) (rClean : QRegister mClean n)
    (uTarget : Unitary (2 ^ k)) (d : DynamicCircuit Var n) (hd :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rClean uTarget d) :
    p2t_RealizesConstCleanUnitary (projZeroAll mClean rClean.wires) d
    (rData.embedUnitary uTarget) :=
  ⟨fun M ↦ let ⟨M', hWp, _⟩ := hd M; ⟨M', hWp⟩, fun M σ ↦ by
    obtain ⟨_, hWp, hEq⟩ := hd M
    rw [congrFun hWp σ]
    rw [← projZeroAll_eq_basisOutcomeProjector_zero rClean] at hEq
    simpa [HermitianMat.conj_apply_mat, projZeroAll_conjTranspose, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
      using hEq⟩

theorem cliff_eval_congr_nonMut_held46 {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (c : CliffProg M), CliffDisjoint mutW c →
      ∀ {β₁ β₂ : BitAssignment M}, (∀ w, ¬ mutW w → β₁ w = β₂ w) →
      ∀ {w : Wire M}, ¬ mutW w → c.eval β₁ w = c.eval β₂ w
  | .nil, _, _, _, hEq, w, hw => hEq w hw
  | .x u, hu, _, _, hEq, w, hw => by
      dsimp only [CliffProg.eval]
      by_cases hwu : w = u
      · subst hwu; simp [Function.update_self, hEq w hu]
      · simp [Function.update_of_ne hwu, hEq w hw]
  | .cnot ctrl tgt _, ⟨hc, ht⟩, _, _, hEq, w, hw => by
      dsimp only [CliffProg.eval]
      by_cases hwt : w = tgt
      · subst hwt; simp [Function.update_self, hEq w ht, hEq ctrl hc]
      · simp [Function.update_of_ne hwt, hEq w hw]
  | .seq c₁ c₂, ⟨hd₁, hd₂⟩, _, _, hEq, _, hw =>
      cliff_eval_congr_nonMut_held46 c₂ hd₂
        (fun _ hu ↦ cliff_eval_congr_nonMut_held46 c₁ hd₁ hEq hu) hw

theorem fwdBits_congr_nonMut {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {K : TempCtx M}, K.DisjointFrom mutW →
      ∀ {β₁ β₂ : BitAssignment M}, (∀ w, ¬ mutW w → β₁ w = β₂ w) →
      ∀ w, ¬ mutW w → K.fwdBits β₁ w = K.fwdBits β₂ w
  | .hole, _, _, _, hEq, w, hw => hEq w hw
  | .seqPre c K₁, ⟨hdc, hdK₁⟩, _, _, hEq, w, hw =>
      fwdBits_congr_nonMut hdK₁ (fun _ hu ↦ cliff_eval_congr_nonMut_held46 c hdc hEq hu) w hw
  | .seqPost _ _, ⟨hdK₁, _⟩, _, _, hEq, w, hw => fwdBits_congr_nonMut hdK₁ hEq w hw
  | .tempAnd c₁ c₂ anc _ _ _ K₁, ⟨h₁, h₂, ha, hdK₁⟩, _, _, hEq, w, hw =>
      fwdBits_congr_nonMut hdK₁ (fun u hu ↦ if hua : u = anc then by
        subst hua; simp [Function.update_self, hEq u ha, hEq c₁ h₁, hEq c₂ h₂]
      else by simp [Function.update_of_ne hua, hEq u hu]) w hw

attribute [local irreducible] ctxAxisFold7 ctxSort3Clamp65

theorem embedUnitary_diagSignUnitary_mulVec_ket_held46 {n k : ℕ} (r : QRegister k n)
    (phase : Fin (2 ^ k) → Bool) (α : BitAssignment n) :
    (r.embedUnitary (diagSignUnitary phase)).1.mulVec (ket α) = ((-1 : ℂ) ^ (if phase
    ((basisBitsEquiv k).symm (fun m ↦ α (r m))) then (1 : ZMod 2) else 0).val) • ket α := by
  rw [show ket α = Pi.single ((basisBitsEquiv n).symm α) 1 from rfl,
    embedUnitary_diagSignUnitary_mulVec_single,
    show r.extractIndex ((basisBitsEquiv n).symm α) =
      (basisBitsEquiv k).symm (fun m ↦ α (r m)) by
      simp [QRegister.extractIndex]]
  cases phase ((basisBitsEquiv k).symm (fun m ↦ α (r m))) <;> simp

set_option maxRecDepth 512

end ConfigOrbitSandHeld46

end OrbitSandHeld46

end
end OrbitSandHeld46

end QuantumComputation.Specs.StoppingPowerSolution
