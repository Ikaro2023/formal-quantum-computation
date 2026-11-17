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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DisjointWiresSymm
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SubspaceLift128
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosSlots24Barrel3Pass
local instance (priority := 1000000) instNeZeroTwoPow_PosSlots24Barrel3Pass (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace PosSlots24Barrel3Pass

section ConfigPosSlots24Barrel3Pass

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

local instance (priority := 1000000) instLoc_PosSlots24Barrel3Pass_1InstNeZeroTwoPowPosBa (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit hiding
  ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (ket bit_cases matrix_ext_ket eval_seq_mulVec ket_CNOT)
open MeasureBranchHadamardSem (projZeroAll ket_projZeroAll projZeroAll_conjTranspose)
open MeasureBranchHadamardSem (projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary)
open StreamingBchComparator BchCubeDecoder
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding
  ite_pos ite_neg dite_pos dite_neg
-- Root solution namespace already active.
open MomSlot0CircuitHalf (padZeroBits)

/-- Kernel-neutral identity barrier backed by `Classical.choice`. -/
noncomputable def lockVal3P {α : Sort _} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)

theorem lockVal3P_eq {α : Sort _} (x : α) : lockVal3P x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)

local instance (priority := 100000) instLoc_PosSlots24Barrel3Pass_2InstNeZeroTwoPow3P (k : ℕ) :
  NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Aliases out-of-range `8`-bit values `[218 .. 256)` onto `[90 .. 128)` (`< 218`)
matching the un-split `[90 .. 128)` wires of the `210`-`TempAnd` prefix decoder. -/
def aliasIdx218 (v : ℕ) : ℕ := if v < 218 then v else v - 128

theorem aliasIdx218_lt {v : ℕ} (hv : v < 256) : aliasIdx218 v < 218 := by
  dsimp only [aliasIdx218]
  split_ifs <;> omega

theorem aliasIdx218_of_lt {v : ℕ} (hv : v < 218) : aliasIdx218 v = v := ite_eq_left hv

/-- Clamped `8`-bit index mapping `[218 .. 256)` to `0` (`E_0` no-op). -/
def clampIdx218 (v : ℕ) : ℕ := if v < 218 then v else 0

theorem clampIdx218_lt (v : ℕ) : clampIdx218 v < 218 := by
  dsimp only [clampIdx218]
  split_ifs <;> omega

/-- Unclamped `18`-bit `218`-slot table value on `posCoreWires`: reads electron slot
`aliasIdx218 (regVal (rAnchorIdx rCoreL) βL) ∈ {0 .. 217}`. -/
noncomputable def anchorTblVal218Unclamped (x : Fin (2 ^ posCoreWires)) : Fin (2 ^ 18) :=
  let βL := basisBits posCoreWires x
  let rCoreL := QRegExt.ofFin posCoreWires
  let u := aliasIdx218 (regVal (rAnchorIdx rCoreL) βL)
  have hu : u < 218 :=
    aliasIdx218_lt (by simpa using regVal_lt_two_pow (rAnchorIdx rCoreL) βL)
  (basisBitsEquiv 18).symm fun j ↦ βL (rElecSlot rCoreL ⟨u, hu⟩ j)

theorem basisBits_anchorTblVal218Unclamped (x : Fin (2 ^ posCoreWires)) (j : Fin 18) :
    basisBits 18 (anchorTblVal218Unclamped x) j =
      basisBits posCoreWires x
        (rElecSlot (QRegExt.ofFin posCoreWires)
          ⟨aliasIdx218
              (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x)),
            aliasIdx218_lt (by
              simpa using
                regVal_lt_two_pow (rAnchorIdx (QRegExt.ofFin posCoreWires))
                  (basisBits posCoreWires x))⟩ j) :=
  basisBits_symm_apply_at _ j

/-- `< 218`-Clamped `18`-bit `218`-slot table value on `posCoreWires`: reads electron slot
`clampIdx218 (regVal (rAnchorIdx rCoreL) βL) ∈ {0 .. 217}` (`E_0` when `idx >= 218`). -/
noncomputable def anchorTblVal218 (x : Fin (2 ^ posCoreWires)) : Fin (2 ^ 18) :=
  let βL := basisBits posCoreWires x
  let rCoreL := QRegExt.ofFin posCoreWires
  let u := clampIdx218 (regVal (rAnchorIdx rCoreL) βL)
  have hu : u < 218 := clampIdx218_lt _
  (basisBitsEquiv 18).symm fun j ↦ βL (rElecSlot rCoreL ⟨u, hu⟩ j)

theorem basisBits_anchorTblVal218 (x : Fin (2 ^ posCoreWires)) (j : Fin 18) : basisBits 18
    (anchorTblVal218 x) j = basisBits posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires)
    ⟨clampIdx218 (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x)),
      clampIdx218_lt _⟩ j) := basisBits_symm_apply_at _ j

theorem rAnchorIdx_ofFin_val (d : Fin 8) : (rAnchorIdx (QRegExt.ofFin posCoreWires) d).val = 3968 +
    d.val := by
  dsimp [rAnchorIdx, rSubPayloadCore, QRegister.slice_apply, QRegExt.ofFin,
    PosSlots24PartnerMuxZeroT123Alt.qreg_slice_wires,
    PosSlots24PartnerMuxZeroT123Alt.qreg_whole_wires,
    PosSlots24PartnerMuxZeroT123Alt.emb_trans_apply,
    PosSlots24PartnerMuxZeroT123Alt.emb_refl_apply,
    PosSlots24PartnerMuxZeroT123Alt.emb_mk_apply,
    PosSlots24PartnerMuxZeroT123Alt.qreg_block_apply,
    PosSlots24PartnerMuxZeroT123Alt.qreg_block_wires_apply]
  omega

/-- Zero-gate `QRegister` re-targeting `rAnchorIdx` (`[3968 .. 3976)`) of `rCore` to any
disjoint `8`-wire index register `rIdx8`, preserving `rElecSlot` (`[0 .. 3924)`). -/
def rCoreSubstAnchor {n : ℕ} (rCore : QRegister posCoreWires n) (rIdx8 : QRegister 8 n) (hCI :
    rCore.DisjointWires rIdx8) : QRegister posCoreWires n where
  wires :=
    { toFun := fun i ↦
        if h : 3968 ≤ i.val ∧ i.val < 3976 then rIdx8 ⟨i.val - 3968, by omega⟩
        else rCore i
      inj' := fun i₁ i₂ heq ↦ by
        dsimp only at heq
        by_cases h₁ : 3968 ≤ i₁.val ∧ i₁.val < 3976 <;>
          by_cases h₂ : 3968 ≤ i₂.val ∧ i₂.val < 3976 <;>
          simp only [h₁, h₂, ↓reduceDIte] at heq
        · have hv := congrArg Fin.val (rIdx8.wires.injective heq)
          dsimp only at hv
          exact Fin.ext (by omega)
        · exact absurd heq (hCI.ne i₂ _).symm
        · exact absurd heq (hCI.ne i₁ _)
        · exact rCore.wires.injective heq }

theorem rCoreSubstAnchor_elecSlot {n : ℕ} (rCore : QRegister posCoreWires n)
    (rIdx8 : QRegister 8 n) (hCI : rCore.DisjointWires rIdx8) (e : Fin 218) (j : Fin 18) :
    rElecSlot (rCoreSubstAnchor rCore rIdx8 hCI) e j = rElecSlot rCore e j := by
  rw [rElecSlot_apply_ofFin (rCoreSubstAnchor rCore rIdx8 hCI), rElecSlot_apply_ofFin rCore]
  have := e.isLt
  have := j.isLt
  exact dite_eq_right (show ¬ (3968 ≤ 18 * e.val + j.val ∧ 18 * e.val + j.val < 3976) by omega)

theorem rCoreSubstAnchor_anchorIdx {n : ℕ} (rCore : QRegister posCoreWires n)
    (rIdx8 : QRegister 8 n) (hCI : rCore.DisjointWires rIdx8) (d : Fin 8) :
    rAnchorIdx (rCoreSubstAnchor rCore rIdx8 hCI) d = rIdx8 d := by
  have hval := rAnchorIdx_ofFin_val d
  have := d.isLt
  have hin : 3968 ≤ (rAnchorIdx (QRegExt.ofFin posCoreWires) d).val ∧
      (rAnchorIdx (QRegExt.ofFin posCoreWires) d).val < 3976 := ⟨by omega, by omega⟩
  exact (dite_eq_left hin).trans (congrArg rIdx8 (Fin.ext (by dsimp; omega)))

def ctxAnchorUnary218UnclampedRaw {M : ℕ} (rCore : QRegister posCoreWires M) (base : ℕ) (hb : base +
    218 ≤ M)
    (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) : TempCtx M :=
  have h128 : base + 2 ^ 7 ≤ M := by norm_num at *; omega
  have h218 : base + 128 + 90 ≤ M := by omega
  (ctxMobiusUnaryTree 7 base h128
    (fun j ↦ rAnchorIdx rCore ⟨j.val, by omega⟩)
    (fun j ↦ by rw [rAnchorIdx_apply_ofFin rCore]; exact hCoreLt _)).append
    (ctxUnarySplitPrefix base 128 90 (by decide) (rAnchorIdx rCore 7)
      (by rw [rAnchorIdx_apply_ofFin rCore]; exact hCoreLt _) h218 90 le_rfl)

noncomputable def ctxAnchorUnary218Unclamped {M : ℕ} (rCore : QRegister posCoreWires M)
    (base : ℕ) (hb : base + 218 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base)
    : TempCtx M := lockVal3P (ctxAnchorUnary218UnclampedRaw rCore base hb hCoreLt)

theorem ctxAnchorUnary218Unclamped_countTempAnd {M : ℕ} (rCore : QRegister posCoreWires M)
    (base : ℕ) (hb : base + 218 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) :
    (ctxAnchorUnary218Unclamped rCore base hb hCoreLt).countTempAnd = 210 := by
  rw [ctxAnchorUnary218Unclamped, lockVal3P_eq, ctxAnchorUnary218UnclampedRaw,
    TempCtx.append_countTempAnd, ctxMobiusUnaryTree_countTempAnd, ctxUnarySplitPrefix_countTempAnd]
  norm_num

theorem RestoresAll.anchorUnary218Unclamped {M : ℕ} (rCore : QRegister posCoreWires M)
    (base : ℕ) (hb : base + 218 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) :
    RestoresAll (ctxAnchorUnary218Unclamped rCore base hb hCoreLt) := by
  rw [ctxAnchorUnary218Unclamped, lockVal3P_eq]
  exact RestoresAll.append (RestoresAll.mobiusTree 7 base _ _ _) (RestoresAll.unarySplitPrefix base
    128 90 _ _ _ _ 90 le_rfl)

theorem ScopedBlock.of_prog_eq {M rem : ℕ} {setup : BitAssignment M → BitAssignment M} {out p₁ p₂ :
    TempPhaseProg M} (h : p₁ = p₂)
    (hb : ScopedBlock M rem setup out p₂) : ScopedBlock M rem setup out p₁ :=
  Eq.ndrec (motive := fun p ↦ ScopedBlock M rem setup out p) hb h.symm

private theorem ScopedBlock.fwdBits_spec_of_z_probes {M : ℕ} (K : TempCtx M) (base endIdx uBase : ℕ)
    (huB : uBase + 218 ≤ M)
    (idxFn : ℕ → ℕ) (rCore : QRegister posCoreWires M) (hBlock : ∀ q : Wire M,
      ∃ setup : BitAssignment M → BitAssignment M,
    ScopedBlock M (M - base) setup (.z q) (K.plug (.z q)) ∧ ∀ γ : BitAssignment M, cleanRem M (M -
      base) γ → cleanRem M (M - endIdx) (setup γ) ∧
    (∀ w : Wire M, w.val < base → setup γ w = γ w) ∧ (∀ (u : ℕ) (hu : u < 218), setup γ ⟨uBase + u,
      by omega⟩ =
    if u = idxFn (regVal (rAnchorIdx rCore) γ) then 1 else 0)) : (∀ q : Wire M, ScopedBlock M (M -
      base) K.fwdBits (.z q) (K.plug (.z q))) ∧
    (∀ γ : BitAssignment M, cleanRem M (M - base) γ → cleanRem M (M - endIdx) (K.fwdBits γ) ∧
      (∀ w : Wire M, w.val < base → K.fwdBits γ w = γ w) ∧
    (∀ (u : ℕ) (hu : u < 218), K.fwdBits γ ⟨uBase + u, by omega⟩ = if u = idxFn (regVal (rAnchorIdx
      rCore) γ) then 1 else 0)) := by
  let q₀ : Wire M := ⟨0, by omega⟩
  have hFwdEq : ∀ γ, cleanRem M (M - base) γ → ∀ q : Wire M, K.fwdBits γ q = (hBlock q).choose γ
    q :=
    fun γ hγ q ↦ (K.plug_evalSign (.z q) γ).symm.trans ((hBlock q).choose_spec.1.sign γ hγ)
  exact ⟨fun q ↦ scopedBlock_fwdBits K q₀ (hBlock q₀).choose_spec.1 q, fun γ hγ ↦
    ⟨fun w hw ↦ (hFwdEq γ hγ w).trans (((hBlock w).choose_spec.2 γ hγ).1 w hw),
     fun w hw ↦ (hFwdEq γ hγ w).trans (((hBlock w).choose_spec.2 γ hγ).2.1 w hw),
     fun u hu ↦ (hFwdEq γ hγ ⟨uBase + u, by omega⟩).trans
       (((hBlock ⟨uBase + u, by omega⟩).choose_spec.2 γ hγ).2.2 u hu)⟩⟩

private theorem aliasIdx218_rhs_eq {u lo7 : ℕ} (_hu : u < 218) (hlo : lo7 < 128) (b7 : ZMod 2) :
    (if u = aliasIdx218 (lo7 + 128 * b7.val) then (1 : ZMod 2) else 0) = if b7 = 0 then (if u =
      lo7 then 1 else 0)
    else if lo7 < 90 then (if u = lo7 + 128 then 1 else 0) else (if u = lo7 then 1 else 0) := by
  rcases bit_cases b7 with rfl | rfl
  · simp [aliasIdx218_of_lt (show lo7 < 218 by omega)]
  · simp only [show ¬ ((1 : ZMod 2) = 0) by decide, ↓reduceIte, ZMod.val_one, mul_one, aliasIdx218]
    by_cases h90 : lo7 < 90
    · simp only [h90, ↓reduceIte, show lo7 + 128 < 218 by omega]
    · simp only [h90, ↓reduceIte, show ¬ (lo7 + 128 < 218) by omega, Nat.add_sub_cancel]

theorem ScopedBlock.ctxAnchorUnary218Unclamped_fwdBits_spec {M : ℕ}
    (rCore : QRegister posCoreWires M) (base : ℕ) (hb : base + 218 ≤ M)
    (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) :
    let K := ctxAnchorUnary218Unclamped rCore base hb hCoreLt
    (∀ q : Wire M, ScopedBlock M (M - base) K.fwdBits (.z q) (K.plug (.z q))) ∧
    (∀ γ : BitAssignment M, cleanRem M (M - base) γ →
      cleanRem M (M - (base + 218)) (K.fwdBits γ) ∧
      (∀ w : Wire M, w.val < base → K.fwdBits γ w = γ w) ∧
      (∀ (u : ℕ) (hu : u < 218),
        K.fwdBits γ ⟨base + u, by omega⟩ =
          if u = aliasIdx218 (regVal (rAnchorIdx rCore) γ) then 1 else 0)) := by
  dsimp only
  let K := ctxAnchorUnary218Unclamped rCore base hb hCoreLt
  have hAncLt : ∀ d : Fin 8, (rAnchorIdx rCore d).val < base := fun d ↦ by
    rw [rAnchorIdx_apply_ofFin rCore]
    exact hCoreLt _
  refine ScopedBlock.fwdBits_spec_of_z_probes K base (base + 218) base hb aliasIdx218 rCore fun q ↦
    ?_
  have h128 : base + 2 ^ 7 ≤ M := by norm_num at *; omega
  obtain ⟨sPref, hPrefBlk, hPrefSpec⟩ :=
    ScopedBlock.withUnarySplitPrefix_block base 128 90 (by decide)
      (rAnchorIdx rCore 7) (hAncLt 7) (by omega) 90 le_rfl (.z q) (.z q) id (ScopedBlock.z_kick q)
  obtain ⟨sTree, hTreeBlk, hTreeSpec⟩ :=
    ScopedBlock.ctxMobiusUnaryTree_block 7 base h128
      (fun j ↦ rAnchorIdx rCore ⟨j.val, by omega⟩) (fun j ↦ hAncLt _)
      (.z q) _ sPref (hPrefBlk.cast_rem (by norm_num))
  have hPlugK : K.plug (.z q) = (ctxMobiusUnaryTree 7 base h128 (fun j ↦ rAnchorIdx rCore ⟨j.val,
    by omega⟩) (fun j ↦ hAncLt _)).plug
      (withUnarySplitPrefix base 128 90 (by decide) (rAnchorIdx rCore 7) (hAncLt 7) (by omega) 90
        le_rfl (.z q)) := by
    dsimp only [K, ctxAnchorUnary218Unclamped, ctxAnchorUnary218UnclampedRaw]
    rw [lockVal3P_eq, TempCtx.append_plug, ctxUnarySplitPrefix_plug]
  refine ⟨fun γ ↦ sPref (sTree γ), ScopedBlock.of_prog_eq hPlugK hTreeBlk, fun γ hγ ↦ ?_⟩
  obtain ⟨hcl1, hbelow1, hunary1⟩ := hTreeSpec γ hγ
  obtain ⟨hcl2, hbelow2, hsplit2⟩ := hPrefSpec (sTree γ) (cleanRem_cast (by norm_num) hcl1)
  have hmsb_eq : sTree γ (rAnchorIdx rCore 7) = γ (rAnchorIdx rCore 7) := hbelow1 _ (hAncLt 7)
  let lo7 := bitsVal (fun j : Fin 7 ↦ γ (rAnchorIdx rCore ⟨j.val, by omega⟩))
  have hlo7_lt : lo7 < 128 := by simp [lo7]
  have hRegSplit : regVal (rAnchorIdx rCore) γ = lo7 + 128 * (γ (rAnchorIdx rCore 7)).val := by
    rw [show regVal (rAnchorIdx rCore) γ =
          ∑ d : Fin (7 + 1), (γ (rAnchorIdx rCore d)).val * 2 ^ d.val from rfl,
        Fin.sum_univ_castSucc, show (2 : ℕ) ^ (Fin.last 7).val = 128 by decide,
        show (Fin.last 7 : Fin 8) = 7 from rfl, mul_comm _ 128]
    rfl
  refine ⟨cleanRem_cast (by omega) hcl2,
    fun w hw ↦ (hbelow2 w (Or.inl (by omega))).trans (hbelow1 w hw), fun u hu ↦ ?_⟩
  dsimp only
  rw [hRegSplit, aliasIdx218_rhs_eq hu hlo7_lt (γ (rAnchorIdx rCore 7))]
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  by_cases hu90 : u < 90
  · rw [(hsplit2 u (by omega) hu90).1, hunary1 u (show u < 128 by omega), hmsb_eq]
    change (if u = lo7 then (1 : ZMod 2) else 0) +
      (if u = lo7 then 1 else 0) * γ (rAnchorIdx rCore 7) = _
    rcases bit_cases (γ (rAnchorIdx rCore 7)) with hb7 | hb7
    · simp only [hb7, ↓reduceIte, mul_zero, add_zero]
    · by_cases hulo : u = lo7
      · subst hulo
        simp only [hb7, h10, hu90, show lo7 ≠ lo7 + 128 by omega, ↓reduceIte, mul_one,
          CharTwo.add_self_eq_zero]
      · simp only [hb7, h10, hulo, show u ≠ lo7 + 128 by omega, ↓reduceIte, mul_one, add_zero,
          ite_self]
  · by_cases hu128 : u < 128
    · rw [hbelow2 ⟨base + u, by omega⟩ (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩),
          hunary1 u (show u < 128 by omega)]
      change (if u = lo7 then (1 : ZMod 2) else 0) = _
      rcases bit_cases (γ (rAnchorIdx rCore 7)) with hb7 | hb7
      · simp only [hb7, ↓reduceIte]
      · by_cases h90 : lo7 < 90
        · simp only [hb7, h10, h90, show u ≠ lo7 by omega, show u ≠ lo7 + 128 by omega, ↓reduceIte]
        · simp only [hb7, h10, h90, ↓reduceIte]
    · rw [show (⟨base + u, by omega⟩ : Wire M) = ⟨base + 128 + (u - 128), by omega⟩ from
            Fin.ext (by dsimp; omega),
          (hsplit2 (u - 128) (by omega) (by omega)).2,
          hunary1 (u - 128) (show u - 128 < 128 by omega), hmsb_eq]
      change (if u - 128 = lo7 then (1 : ZMod 2) else 0) * γ (rAnchorIdx rCore 7) = _
      rcases bit_cases (γ (rAnchorIdx rCore 7)) with hb7 | hb7
      · simp only [hb7, ↓reduceIte, mul_zero, show u ≠ lo7 by omega]
      · by_cases h90 : lo7 < 90
        · simp only [hb7, h10, h90, ↓reduceIte, mul_one,
            show (u - 128 = lo7) ↔ (u = lo7 + 128) by omega]
        · simp only [hb7, h10, h90, show u - 128 ≠ lo7 by omega, show u ≠ lo7 by omega,
            ↓reduceIte, mul_one]

attribute [local irreducible] ctxAnchorUnary218Unclamped

theorem dyadic218_oob_bit (b : Fin 8 → ZMod 2) :
    let V := bitsVal b
    let p0 := b 7 * b 6
    let p1 := p0 * b 5 + p0
    let p2 := p1 * b 4
    let p3 := p2 * b 3
    let p4 := p3 * b 2 + p3
    let r5 := p4 * b 1 + p4
    (p0 + p1 + p3 + r5 : ZMod 2) = if V < 218 then 0 else 1 := by
  intro V p0 p1 p2 p3 p4 r5
  dsimp only [V, r5, p4, p3, p2, p1, p0]
  have hV := bitsVal_eight b
  have hlt : (b 0).val < 2 ∧ (b 1).val < 2 ∧ (b 2).val < 2 ∧ (b 3).val < 2 ∧
      (b 4).val < 2 ∧ (b 5).val < 2 ∧ (b 6).val < 2 :=
    ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
     ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _⟩
  have h11 : (1 + 1 : ZMod 2) = 0 := rfl
  have bv (x : ZMod 2) : (x = 0 ∧ x.val = 0) ∨ (x = 1 ∧ x.val = 1) :=
    (bit_cases x).imp (fun h ↦ ⟨h, by simp [h]⟩) (fun h ↦ ⟨h, by simp [h]⟩)
  rcases bv (b 7) with ⟨h7, h7v⟩ | ⟨h7, h7v⟩
  · simp only [ite_eq_left (show bitsVal b < 218 by omega), h7, zero_mul, add_zero]
  · rcases bv (b 6) with ⟨h6, h6v⟩ | ⟨h6, h6v⟩
    · simp only [ite_eq_left (show bitsVal b < 218 by omega), h7, h6, mul_zero, zero_mul, add_zero]
    · rcases bv (b 5) with ⟨h5, h5v⟩ | ⟨h5, h5v⟩
      · rcases bv (b 4) with ⟨h4, h4v⟩ | ⟨h4, h4v⟩
        · simp only [ite_eq_left (show bitsVal b < 218 by omega), h7, h6, h5, h4,
            mul_one, mul_zero, zero_mul, zero_add, add_zero, h11]
        · rcases bv (b 3) with ⟨h3, h3v⟩ | ⟨h3, h3v⟩
          · simp only [ite_eq_left (show bitsVal b < 218 by omega), h7, h6, h5, h4, h3,
              mul_one, mul_zero, zero_mul, zero_add, add_zero, h11]
          · rcases bv (b 2) with ⟨h2, h2v⟩ | ⟨h2, h2v⟩
            · rcases bv (b 1) with ⟨h1, h1v⟩ | ⟨h1, h1v⟩
              · simp only [ite_eq_left (show bitsVal b < 218 by omega), h7, h6, h5, h4, h3, h2, h1,
                  mul_one, mul_zero, zero_add, h11]
              · simp only [ite_eq_right (show ¬ bitsVal b < 218 by omega), h7, h6, h5, h4, h3, h2,
                  h1,
                  mul_one, mul_zero, zero_add, add_zero, h11]
            · simp only [ite_eq_right (show ¬ bitsVal b < 218 by omega), h7, h6, h5, h4, h3, h2,
                mul_one, mul_zero, zero_mul, zero_add, add_zero, h11]
      · simp only [ite_eq_right (show ¬ bitsVal b < 218 by omega), h7, h6, h5,
          mul_one, zero_mul, add_zero, h11]

/-- `6`-`TempAnd` prefix header on `[base .. base + 6)` computing `p0, p1, p2, p3, p4, r5` from
`rAnchorIdx rCore`. -/
def ctxAnchorClampHdr6Raw {M : ℕ} (rCore : QRegister posCoreWires M) (base : ℕ)
    (hb : base + 6 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) : TempCtx M :=
  let a : Fin 8 → Wire M := fun k ↦ rAnchorIdx rCore k
  have ha : ∀ k : Fin 8, (a k).val < base := fun k ↦ by
    dsimp [a]
    rw [rAnchorIdx_apply_ofFin rCore]
    exact hCoreLt _
  let wP0 : Wire M := ⟨base + 0, by omega⟩
  let wP1 : Wire M := ⟨base + 1, by omega⟩
  let wP2 : Wire M := ⟨base + 2, by omega⟩
  let wP3 : Wire M := ⟨base + 3, by omega⟩
  let wP4 : Wire M := ⟨base + 4, by omega⟩
  let wR5 : Wire M := ⟨base + 5, by omega⟩
  have haAdd (k : Fin 8) (d : ℕ) : (a k).val < base + d := lt_of_lt_of_le (ha k) (Nat.le_add_right
    base d)
  (ctxTempBit (a 7) (a 6) wP0 ((rAnchorIdx rCore).wires.injective.ne (by decide)) (wire_ne_of_lt
    (haAdd 7 0)) (wire_ne_of_lt (haAdd 6 0))).append <|
  (ctxTempBit wP0 (a 5) wP1 (wire_ne_of_gt (haAdd 5 0)) (wire_ne_of_lt (show base + 0 < base +
    1 by omega)) (wire_ne_of_lt (haAdd 5 1))).append <|
  (ctxCliffAlloc (.cnot wP0 wP1 (wire_ne_of_lt (show base + 0 < base + 1 by omega)))).append <|
  (ctxTempBit wP1 (a 4) wP2 (wire_ne_of_gt (haAdd 4 1)) (wire_ne_of_lt (show base + 1 < base +
    2 by omega)) (wire_ne_of_lt (haAdd 4 2))).append <|
  (ctxTempBit wP2 (a 3) wP3 (wire_ne_of_gt (haAdd 3 2)) (wire_ne_of_lt (show base + 2 < base +
    3 by omega)) (wire_ne_of_lt (haAdd 3 3))).append <|
  (ctxTempBit wP3 (a 2) wP4 (wire_ne_of_gt (haAdd 2 3)) (wire_ne_of_lt (show base + 3 < base +
    4 by omega)) (wire_ne_of_lt (haAdd 2 4))).append <|
  (ctxCliffAlloc (.cnot wP3 wP4 (wire_ne_of_lt (show base + 3 < base + 4 by omega)))).append <|
  (ctxTempBit wP4 (a 1) wR5 (wire_ne_of_gt (haAdd 1 4)) (wire_ne_of_lt (show base + 4 < base +
    5 by omega)) (wire_ne_of_lt (haAdd 1 5))).append <|
  ctxCliffAlloc (.cnot wP4 wR5 (wire_ne_of_lt (show base + 4 < base + 5 by omega)))

/-- `219`-`TempAnd` (`876 T`) `< 218`-clamped dyadic unary decoder on `[base .. base + 224)`:
wires `[base .. base + 6)` hold the `6` dyadic prefix carries and wires `[base + 6 .. base + 224)`
hold
exact `218`-slot unary bits `u = clampIdx218 (regVal (rAnchorIdx rCore) γ)` (`u = 0` when `idx >=
218`). -/
def ctxAnchorUnary218Raw {M : ℕ} (rCore : QRegister posCoreWires M) (base : ℕ)
    (hb : base + 224 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) : TempCtx M :=
  let a : Fin 8 → Wire M := fun k ↦ rAnchorIdx rCore k
  have ha : ∀ k : Fin 8, (a k).val < base := fun k ↦ by
    dsimp [a]
    rw [rAnchorIdx_apply_ofFin rCore]
    exact hCoreLt _
  let uBase := base + 6
  let wP0 : Wire M := ⟨base + 0, by omega⟩
  let wP1 : Wire M := ⟨base + 1, by omega⟩
  let wP2 : Wire M := ⟨base + 2, by omega⟩
  let wP3 : Wire M := ⟨base + 3, by omega⟩
  let wR5 : Wire M := ⟨base + 5, by omega⟩
  let uRootA : Wire M := ⟨uBase + 0, by omega⟩
  let uRootB : Wire M := ⟨uBase + 128, by omega⟩
  let uRootC : Wire M := ⟨uBase + 192, by omega⟩
  let uRootD : Wire M := ⟨uBase + 208, by omega⟩
  let uRootE : Wire M := ⟨uBase + 216, by omega⟩
  (ctxAnchorClampHdr6Raw rCore base (by omega) hCoreLt).append <|
  (ctxCliffAlloc (.seq (.x uRootA) (.cnot (a 7) uRootA
    (wire_ne_of_lt (lt_of_lt_of_le (ha 7) (by dsimp [uRootA, uBase]; omega)))))).append <|
  (ctxRootedUnaryTree 7 (uBase + 0) (by norm_num at *; omega) (fun j ↦ a ⟨j.val, by omega⟩)
    (fun j ↦ lt_of_lt_of_le (ha _) (by dsimp [uBase]; omega))).append <|
  (ctxCliffAlloc (.seq
    (.cnot (a 7) uRootB (wire_ne_of_lt (lt_of_lt_of_le (ha 7) (by dsimp [uRootB, uBase]; omega))))
    (.cnot wP0 uRootB (wire_ne_of_lt (by dsimp [wP0, uRootB, uBase]; omega))))).append <|
  (ctxRootedUnaryTree 6 (uBase + 128) (by norm_num at *; omega) (fun j ↦ a ⟨j.val, by omega⟩)
    (fun j ↦ lt_of_lt_of_le (ha _) (by dsimp [uBase]; omega))).append <|
  (ctxCliffAlloc (.seq (.cnot wP1 uRootC (wire_ne_of_lt (by dsimp [wP1, uRootC, uBase]; omega)))
    (.cnot wP2 uRootC (wire_ne_of_lt (by dsimp [wP2, uRootC, uBase]; omega))))).append <|
  (ctxRootedUnaryTree 4 (uBase + 192) (by norm_num at *; omega) (fun j ↦ a ⟨j.val, by omega⟩)
    (fun j ↦ lt_of_lt_of_le (ha _) (by dsimp [uBase]; omega))).append <|
  (ctxCliffAlloc (.seq (.cnot wP2 uRootD (wire_ne_of_lt (by dsimp [wP2, uRootD, uBase]; omega)))
    (.cnot wP3 uRootD (wire_ne_of_lt (by dsimp [wP3, uRootD, uBase]; omega))))).append <|
  (ctxRootedUnaryTree 3 (uBase + 208) (by norm_num at *; omega) (fun j ↦ a ⟨j.val, by omega⟩)
    (fun j ↦ lt_of_lt_of_le (ha _) (by dsimp [uBase]; omega))).append <|
  (ctxCliffAlloc (.cnot wR5 uRootE (wire_ne_of_lt (by dsimp [wR5, uRootE, uBase]; omega)))).append
    <|
  (ctxRootedUnaryTree 1 (uBase + 216) (by norm_num at *; omega) (fun j ↦ a ⟨j.val, by omega⟩)
    (fun j ↦ lt_of_lt_of_le (ha _) (by dsimp [uBase]; omega))).append <|
  ctxCliffAlloc (.seq (.cnot wP0 uRootA (wire_ne_of_lt (by dsimp [wP0, uRootA, uBase]; omega)))
    (.seq (.cnot wP1 uRootA (wire_ne_of_lt (by dsimp [wP1, uRootA, uBase]; omega)))
      (.seq (.cnot wP3 uRootA (wire_ne_of_lt (by dsimp [wP3, uRootA, uBase]; omega)))
            (.cnot wR5 uRootA (wire_ne_of_lt (by dsimp [wR5, uRootA, uBase]; omega))))))

noncomputable def ctxAnchorUnary218 {M : ℕ} (rCore : QRegister posCoreWires M) (base : ℕ)
    (hb : base + 224 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) : TempCtx M :=
      lockVal3P (ctxAnchorUnary218Raw rCore base hb hCoreLt)

theorem ctxAnchorUnary218_countTempAnd {M : ℕ} (rCore : QRegister posCoreWires M) (base : ℕ)
    (hb : base + 224 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) :
      (ctxAnchorUnary218 rCore base hb hCoreLt).countTempAnd = 219 := by
  rw [ctxAnchorUnary218, lockVal3P_eq]
  dsimp only [ctxAnchorUnary218Raw, ctxAnchorClampHdr6Raw]
  repeat rw [TempCtx.append_countTempAnd]
  repeat rw [ctxRootedUnaryTree_countTempAnd]
  rfl

theorem RestoresAll.anchorUnary218 {M : ℕ} (rCore : QRegister posCoreWires M) (base : ℕ)
    (hb : base + 224 ≤ M) (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) : RestoresAll
      (ctxAnchorUnary218 rCore base hb hCoreLt) := by
  rw [ctxAnchorUnary218, lockVal3P_eq]
  dsimp only [ctxAnchorUnary218Raw, ctxAnchorClampHdr6Raw]
  exact RestoresAll.append
    (RestoresAll.append (RestoresAll.tempBit _ _ _) <| RestoresAll.append (RestoresAll.tempBit _ _
      _) <|
     RestoresAll.append (RestoresAll.cliffAlloc _) <| RestoresAll.append (RestoresAll.tempBit _ _ _)
       <|
     RestoresAll.append (RestoresAll.tempBit _ _ _) <| RestoresAll.append (RestoresAll.tempBit _ _
       _) <|
     RestoresAll.append (RestoresAll.cliffAlloc _) <|
     RestoresAll.append (RestoresAll.tempBit _ _ _) (RestoresAll.cliffAlloc _))
    (RestoresAll.append (RestoresAll.cliffAlloc _) <| RestoresAll.append (RestoresAll.rootedTree 7 _
      _ _ _) <|
     RestoresAll.append (RestoresAll.cliffAlloc _) <| RestoresAll.append (RestoresAll.rootedTree 6 _
       _ _ _) <|
     RestoresAll.append (RestoresAll.cliffAlloc _) <| RestoresAll.append (RestoresAll.rootedTree 4 _
       _ _ _) <|
     RestoresAll.append (RestoresAll.cliffAlloc _) <| RestoresAll.append (RestoresAll.rootedTree 3 _
       _ _ _) <|
     RestoresAll.append (RestoresAll.cliffAlloc _) <|
     RestoresAll.append (RestoresAll.rootedTree 1 _ _ _ _) (RestoresAll.cliffAlloc _))

private theorem ScopedBlock.ctxTempBit_plug_block {M : ℕ} (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire
    M) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur)
    {sInner : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M} (hBody : ScopedBlock
      M (M - (cur + 1)) sInner leaf body) :
    ScopedBlock M (M - cur) (fun β ↦ sInner (Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂))) leaf
    ((ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂)).plug body) := by
  obtain ⟨sNext, hBlk, eNext⟩ :=
    ScopedBlock.tempBit_step (M := M) id cur hcur c₁ c₂ h₁₂ hc₁ hc₂ (sInner := sInner) hBody
  rw [ctxTempBit_plug]
  rwa [show (fun β ↦ id (sNext β)) = fun β ↦ sInner (Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂))
    from funext eNext] at hBlk

private theorem ScopedBlock.ctxCliff_plug_block {M rem remIn : ℕ}
    (hremIn : remIn ≤ M) (hle : remIn ≤ rem) (c : CliffProg M) (hSupp : c.SupportsBelow (M - remIn))
    {sInner : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M} (hBody : ScopedBlock
      M remIn sInner leaf body) :
    ScopedBlock M rem (fun β ↦ sInner (c.eval β)) leaf ((ctxCliffAlloc c).plug body) := by
  obtain ⟨sNext, hBlk, eNext⟩ :=
    ScopedBlock.cliffAlloc_step (M := M) id hremIn hle c hSupp (sInner := sInner) hBody
  rw [ctxCliffAlloc_plug]
  rwa [show (fun β ↦ id (sNext β)) = fun β ↦ sInner (c.eval β) from funext eNext] at hBlk

private theorem ScopedBlock.rootedBranch_block {M : ℕ}
    (d rCur : ℕ) (hcur : rCur + 2 ^ d ≤ M)
    (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < rCur)
    (cR : CliffProg M) (hSupp : cR.SupportsBelow (rCur + 1))
    (hFrame : ∀ (γ : BitAssignment M) (w : Wire M),
      w ≠ ⟨rCur, by have := Nat.one_le_pow d 2 (by decide); omega⟩ → cR.eval γ w = γ w)
    {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M}
    (hBody : ScopedBlock M (M - (rCur + 2 ^ d)) sBody leaf body) :
    ∃ sBr : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - rCur) (fun γ ↦ sBody (sBr γ)) leaf
        ((ctxCliffAlloc cR).plug ((ctxRootedUnaryTree d rCur hcur addr haddr).plug body)) ∧
      ∀ γ : BitAssignment M, cleanRem M (M - rCur) γ →
        cleanRem M (M - (rCur + 2 ^ d)) (sBr γ) ∧
        (∀ w : Wire M, w.val < rCur → sBr γ w = γ w) ∧
        (∀ (k : ℕ) (hk : k < 2 ^ d),
          sBr γ ⟨rCur + k, by omega⟩ =
            if k = bitsVal (fun j ↦ γ (addr j))
            then cR.eval γ ⟨rCur, by have := Nat.one_le_pow d 2 (by decide); omega⟩ else 0) := by
  have h2d : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  obtain ⟨sT, hT, hSpecT⟩ :=
    ScopedBlock.ctxRootedUnaryTree_block d rCur hcur addr haddr leaf body sBody hBody
  have hSupp' : cR.SupportsBelow (M - (M - (rCur + 1))) := by
    rwa [show M - (M - (rCur + 1)) = rCur + 1 by omega]
  refine ⟨fun γ ↦ sT (cR.eval γ),
    ScopedBlock.ctxCliff_plug_block (by omega) (by omega) cR hSupp' hT, fun γ hγ ↦ ?_⟩
  have hcl0 : cleanRem M (M - (rCur + 1)) (cR.eval γ) := fun w hw ↦
    (hFrame γ w (wire_ne_of_gt (show rCur < w.val by omega))).trans (hγ w (by omega))
  obtain ⟨hclT, hbelT, hunT⟩ := hSpecT (cR.eval γ) hcl0
  have hadr : (fun j ↦ (cR.eval γ) (addr j)) = fun j ↦ γ (addr j) :=
    funext fun j ↦ hFrame γ (addr j) (wire_ne_of_lt (haddr j))
  refine ⟨hclT, fun w hw ↦ (hbelT w hw).trans (hFrame γ w (wire_ne_of_lt hw)), fun k hk ↦ ?_⟩
  have hev := hunT k hk
  rwa [hadr] at hev

private theorem ScopedBlock.rootedBranch_cnot2 {M : ℕ}
    (d rCur : ℕ) (hcur : rCur + 2 ^ d ≤ M)
    (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < rCur)
    (w₁ w₂ : Wire M) (hw₁ : w₁.val < rCur) (hw₂ : w₂.val < rCur)
    (hne₁ : w₁ ≠ ⟨rCur, by have := Nat.one_le_pow d 2 (by decide); omega⟩)
    (hne₂ : w₂ ≠ ⟨rCur, by have := Nat.one_le_pow d 2 (by decide); omega⟩)
    {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M}
    (hBody : ScopedBlock M (M - (rCur + 2 ^ d)) sBody leaf body) :
    ∃ sBr : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - rCur) (fun γ ↦ sBody (sBr γ)) leaf
        ((ctxCliffAlloc
          (.seq (.cnot w₁ ⟨rCur, by have := Nat.one_le_pow d 2 (by decide); omega⟩ hne₁)
            (.cnot w₂ ⟨rCur, by have := Nat.one_le_pow d 2 (by decide); omega⟩ hne₂))).plug
          ((ctxRootedUnaryTree d rCur hcur addr haddr).plug body)) ∧
      ∀ γ : BitAssignment M, cleanRem M (M - rCur) γ →
        cleanRem M (M - (rCur + 2 ^ d)) (sBr γ) ∧
        (∀ w : Wire M, w.val < rCur → sBr γ w = γ w) ∧
        (∀ (k : ℕ) (hk : k < 2 ^ d),
          sBr γ ⟨rCur + k, by omega⟩ =
            if k = bitsVal (fun j ↦ γ (addr j)) then γ w₁ + γ w₂ else 0) := by
  have h2d : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  let uR : Wire M := ⟨rCur, by omega⟩
  obtain ⟨sBr, hBlk, hSpec⟩ :=
    ScopedBlock.rootedBranch_block d rCur hcur addr haddr
      (.seq (.cnot w₁ uR hne₁) (.cnot w₂ uR hne₂))
      ⟨⟨by omega, by dsimp [uR]; omega⟩, ⟨by omega, by dsimp [uR]; omega⟩⟩
      (fun γ w hw ↦ by
        dsimp only [CliffProg.eval]
        rw [Function.update_of_ne hw, Function.update_of_ne hw])
      hBody
  refine ⟨sBr, hBlk, fun γ hγ ↦ ?_⟩
  obtain ⟨hcl, hbel, hun⟩ := hSpec γ hγ
  refine ⟨hcl, hbel, fun k hk ↦ (hun k hk).trans ?_⟩
  have hr : (CliffProg.seq (.cnot w₁ uR hne₁) (.cnot w₂ uR hne₂)).eval γ uR = γ w₁ + γ w₂ := by
    dsimp only [CliffProg.eval, uR]
    rw [Function.update_self, Function.update_self, hγ ⟨rCur, by omega⟩ (by dsimp; omega),
        zero_add, Function.update_of_ne hne₂]
  rw [hr]

theorem ScopedBlock.ctxAnchorUnary218_fwdBits_spec {M : ℕ}
    (rCore : QRegister posCoreWires M) (base : ℕ) (hb : base + 224 ≤ M)
    (hCoreLt : ∀ i : Fin posCoreWires, (rCore i).val < base) :
    let K := ctxAnchorUnary218 rCore base hb hCoreLt
    (∀ q : Wire M, ScopedBlock M (M - base) K.fwdBits (.z q) (K.plug (.z q))) ∧
    (∀ γ : BitAssignment M, cleanRem M (M - base) γ →
      cleanRem M (M - (base + 224)) (K.fwdBits γ) ∧
      (∀ w : Wire M, w.val < base → K.fwdBits γ w = γ w) ∧
      (∀ (u : ℕ) (hu : u < 218),
        K.fwdBits γ ⟨base + 6 + u, by omega⟩ =
          if u = clampIdx218 (regVal (rAnchorIdx rCore) γ) then 1 else 0)) := by
  dsimp only
  let K := ctxAnchorUnary218 rCore base hb hCoreLt
  let a : Fin 8 → Wire M := fun k ↦ rAnchorIdx rCore k
  have ha : ∀ k : Fin 8, (a k).val < base := fun k ↦ by
    dsimp [a]
    rw [rAnchorIdx_apply_ofFin rCore]
    exact hCoreLt _
  let uBase := base + 6
  let wP0 : Wire M := ⟨base + 0, by omega⟩
  let wP1 : Wire M := ⟨base + 1, by omega⟩
  let wP2 : Wire M := ⟨base + 2, by omega⟩
  let wP3 : Wire M := ⟨base + 3, by omega⟩
  let wP4 : Wire M := ⟨base + 4, by omega⟩
  let wR5 : Wire M := ⟨base + 5, by omega⟩
  let uRootA : Wire M := ⟨uBase + 0, by omega⟩
  let uRootE : Wire M := ⟨uBase + 216, by omega⟩
  let cP1 : CliffProg M := .cnot wP0 wP1 (wire_ne_of_lt (by dsimp [wP0, wP1]; omega))
  let cP4 : CliffProg M := .cnot wP3 wP4 (wire_ne_of_lt (by dsimp [wP3, wP4]; omega))
  let cP5 : CliffProg M := .cnot wP4 wR5 (wire_ne_of_lt (by dsimp [wP4, wR5]; omega))
  let cRA : CliffProg M := .seq (.x uRootA)
    (.cnot (a 7) uRootA (wire_ne_of_lt (lt_of_lt_of_le (ha 7) (by dsimp [uRootA, uBase]; omega))))
  let cRE : CliffProg M := .cnot wR5 uRootE (wire_ne_of_lt (by dsimp [wR5, uRootE, uBase]; omega))
  let cOob : CliffProg M :=
    .seq (.cnot wP0 uRootA (wire_ne_of_lt (by dsimp [wP0, uRootA, uBase]; omega)))
      (.seq (.cnot wP1 uRootA (wire_ne_of_lt (by dsimp [wP1, uRootA, uBase]; omega)))
        (.seq (.cnot wP3 uRootA (wire_ne_of_lt (by dsimp [wP3, uRootA, uBase]; omega)))
              (.cnot wR5 uRootA (wire_ne_of_lt (by dsimp [wR5, uRootA, uBase]; omega)))))
  refine ScopedBlock.fwdBits_spec_of_z_probes K base (base + 224) uBase (by dsimp [uBase]; omega)
    clampIdx218 rCore fun q ↦ ?_
  have hOob := ScopedBlock.ctxCliff_plug_block (M := M)
    (rem := M - (base + 224)) (remIn := M - (base + 224)) (by omega) le_rfl cOob
    ⟨⟨by dsimp [wP0]; omega, by dsimp [uRootA, uBase]; omega⟩,
     ⟨by dsimp [wP1]; omega, by dsimp [uRootA, uBase]; omega⟩,
     ⟨by dsimp [wP3]; omega, by dsimp [uRootA, uBase]; omega⟩,
     ⟨by dsimp [wR5]; omega, by dsimp [uRootA, uBase]; omega⟩⟩ (ScopedBlock.z_kick q)
  have haAdd (k : Fin 8) (d : ℕ) : (a k).val < base + d := lt_of_lt_of_le (ha k) (Nat.le_add_right
    base d)
  have haU (k : Fin 8) (d : ℕ) : (a k).val < uBase + d := lt_of_lt_of_le (haAdd k 6)
    (Nat.le_add_right uBase d)
  obtain ⟨sTE, hTE, hSpecTE⟩ := ScopedBlock.rootedBranch_block 1 (uBase + 216) (show uBase + 216 +
    2 ≤ M by omega)
    (fun j ↦ a ⟨j.val, by omega⟩) (fun _ ↦ haU _ 216) cRE ⟨show base + 5 < uBase + 216 + 1 by
      omega, show uBase + 216 < uBase + 216 + 1 by omega⟩
    (fun _ _ hw ↦ Function.update_of_ne hw _ _) (hOob.cast_rem (by omega))
  obtain ⟨sTD, hTD, hSpecTD⟩ := ScopedBlock.rootedBranch_cnot2 3 (uBase + 208) (show uBase + 208 +
    8 ≤ M by omega)
    (fun j ↦ a ⟨j.val, by omega⟩) (fun _ ↦ haU _ 208) wP2 wP3 (show base + 2 < uBase + 208 by omega)
      (show base + 3 < uBase + 208 by omega)
    (wire_ne_of_lt (show base + 2 < uBase + 208 by omega)) (wire_ne_of_lt (show base + 3 < uBase +
      208 by omega)) (hTE.cast_rem (by omega))
  obtain ⟨sTC, hTC, hSpecTC⟩ := ScopedBlock.rootedBranch_cnot2 4 (uBase + 192) (show uBase + 192 +
    16 ≤ M by omega)
    (fun j ↦ a ⟨j.val, by omega⟩) (fun _ ↦ haU _ 192) wP1 wP2 (show base + 1 < uBase + 192 by omega)
      (show base + 2 < uBase + 192 by omega)
    (wire_ne_of_lt (show base + 1 < uBase + 192 by omega)) (wire_ne_of_lt (show base + 2 < uBase +
      192 by omega)) (hTD.cast_rem (by omega))
  obtain ⟨sTB, hTB, hSpecTB⟩ := ScopedBlock.rootedBranch_cnot2 6 (uBase + 128) (show uBase + 128 +
    64 ≤ M by omega)
    (fun j ↦ a ⟨j.val, by omega⟩) (fun _ ↦ haU _ 128) (a 7) wP0 (haU 7 128) (show base + 0 < uBase +
      128 by omega)
    (wire_ne_of_lt (haU 7 128)) (wire_ne_of_lt (show base + 0 < uBase + 128 by omega)) (hTC.cast_rem
      (by omega))
  obtain ⟨sTA, hTA, hSpecTA⟩ := ScopedBlock.rootedBranch_block 7 (uBase + 0) (show uBase + 0 +
    128 ≤ M by omega)
    (fun j ↦ a ⟨j.val, by omega⟩) (fun _ ↦ haU _ 0) cRA
    ⟨show uBase + 0 < uBase + 0 + 1 by
      omega, ⟨lt_of_lt_of_le (haU 7 0) (Nat.le_add_right (uBase + 0) 1), show uBase + 0 < uBase +
      0 + 1 by omega⟩⟩
    (fun _ _ hw ↦ by
      dsimp only [cRA, CliffProg.eval, uRootA]
      rw [Function.update_of_ne hw, Function.update_of_ne hw]) (hTB.cast_rem (by omega))
  have hp5c := ScopedBlock.ctxCliff_plug_block (rem := M - (base + 6)) (remIn := M - (base +
    6)) (by omega) le_rfl cP5
    ⟨show base + 4 < M - (M - (base + 6)) by omega, show base + 5 < M - (M - (base + 6)) by omega⟩
      (hTA.cast_rem (by omega))
  have hp5 := ScopedBlock.ctxTempBit_plug_block (base + 5) (by omega) wP4 (a 1) (wire_ne_of_gt
    (haAdd 1 4))
    (show base + 4 < base + 5 by omega) (haAdd 1 5) (hp5c.cast_rem (by omega))
  have hp4c := ScopedBlock.ctxCliff_plug_block (rem := M - (base + 5)) (remIn := M - (base +
    5)) (by omega) le_rfl cP4
    ⟨show base + 3 < M - (M - (base + 5)) by omega, show base + 4 < M - (M - (base + 5)) by omega⟩
      (hp5.cast_rem (by omega))
  have hp4 := ScopedBlock.ctxTempBit_plug_block (base + 4) (by omega) wP3 (a 2) (wire_ne_of_gt
    (haAdd 2 3))
    (show base + 3 < base + 4 by omega) (haAdd 2 4) (hp4c.cast_rem (by omega))
  have hp3 := ScopedBlock.ctxTempBit_plug_block (base + 3) (by omega) wP2 (a 3) (wire_ne_of_gt
    (haAdd 3 2))
    (show base + 2 < base + 3 by omega) (haAdd 3 3) (hp4.cast_rem (by omega))
  have hp2 := ScopedBlock.ctxTempBit_plug_block (base + 2) (by omega) wP1 (a 4) (wire_ne_of_gt
    (haAdd 4 1))
    (show base + 1 < base + 2 by omega) (haAdd 4 2) (hp3.cast_rem (by omega))
  have hp1c := ScopedBlock.ctxCliff_plug_block (rem := M - (base + 2)) (remIn := M - (base +
    2)) (by omega) le_rfl cP1
    ⟨show base + 0 < M - (M - (base + 2)) by omega, show base + 1 < M - (M - (base + 2)) by omega⟩
      (hp2.cast_rem (by omega))
  have hp1 := ScopedBlock.ctxTempBit_plug_block (base + 1) (by omega) wP0 (a 5) (wire_ne_of_gt
    (haAdd 5 0))
    (show base + 0 < base + 1 by omega) (haAdd 5 1) (hp1c.cast_rem (by omega))
  have hp0 := ScopedBlock.ctxTempBit_plug_block (base + 0) (by omega) (a 7) (a 6)
    ((rAnchorIdx rCore).wires.injective.ne (by decide)) (haAdd 7 0) (haAdd 6 0) (hp1.cast_rem (by
      omega))
  refine ⟨_, ScopedBlock.of_prog_eq (hb := hp0.cast_rem (by omega)) (by
    dsimp only [K, ctxAnchorUnary218, ctxAnchorUnary218Raw, ctxAnchorClampHdr6Raw]
    rw [lockVal3P_eq]
    repeat rw [TempCtx.append_plug]), fun γ hγ ↦ ?_⟩
  dsimp only [id_eq]
  let b : Fin 8 → ZMod 2 := fun k ↦ γ (a k)
  let gp1 := Function.update γ wP0 (γ (a 7) * γ (a 6))
  let gp2 := Function.update gp1 wP1 (gp1 wP0 * gp1 (a 5))
  let gp3 := cP1.eval gp2
  let gp4 := Function.update gp3 wP2 (gp3 wP1 * gp3 (a 4))
  let gp5 := Function.update gp4 wP3 (gp4 wP2 * gp4 (a 3))
  let gp6 := Function.update gp5 wP4 (gp5 wP3 * gp5 (a 2))
  let gp7 := cP4.eval gp6
  let gp8 := Function.update gp7 wR5 (gp7 wP4 * gp7 (a 1))
  let γH := cP5.eval gp8
  let γA := sTA γH
  let γB := sTB γA
  let γC := sTC γB
  let γD := sTD γC
  let γE := sTE γD
  let γF := cOob.eval γE
  change cleanRem M (M - (base + 224)) γF ∧ (∀ w : Wire M, w.val < base → γF w = γ w) ∧
    (∀ (u : ℕ) (hu : u < 218),
      γF ⟨uBase + u, by omega⟩ = if u = clampIdx218 (regVal (rAnchorIdx rCore) γ) then 1 else 0)
  have hγH_clean : cleanRem M (M - uBase) γH := fun w hw ↦ by
    dsimp only [γH, gp8, gp7, gp6, gp5, gp4, gp3, gp2, gp1, cP1, cP4, cP5, CliffProg.eval]
    repeat rw [Function.update_of_ne (wire_ne_of_gt (by
      dsimp [wP0, wP1, wP2, wP3, wP4, wR5, uBase] at hw ⊢; omega))]
    exact hγ w (by dsimp [uBase] at hw; omega)
  have hγH_lt : ∀ w : Wire M, w.val < base → γH w = γ w := fun w hw ↦ by
    dsimp only [γH, gp8, gp7, gp6, gp5, gp4, gp3, gp2, gp1, cP1, cP4, cP5, CliffProg.eval]
    repeat rw [Function.update_of_ne (wire_ne_of_lt (by
      dsimp [wP0, wP1, wP2, wP3, wP4, wR5]; omega))]
  let p0 := b 7 * b 6
  let p1 := p0 * b 5 + p0
  let p2 := p1 * b 4
  let p3 := p2 * b 3
  let p4 := p3 * b 2 + p3
  let r5 := p4 * b 1 + p4
  have hgp_a : ∀ k : Fin 8, gp1 (a k) = b k ∧ gp3 (a k) = b k ∧ gp4 (a k) = b k ∧ gp5 (a k) = b k ∧
    gp7 (a k) = b k :=
    fun k ↦ by
      have hk := ha k
      dsimp only [gp7, gp6, gp5, gp4, gp3, gp2, gp1, cP1, cP4, CliffProg.eval, b]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals repeat rw [Function.update_of_ne (wire_ne_of_lt (by
        dsimp [wP0, wP1, wP2, wP3, wP4]; omega))]
  have v_gp1 : gp1 wP0 = p0 := Function.update_self _ _ _
  have v_gp3 : gp3 wP1 = p1 := by
    dsimp only [gp3, gp2, cP1, CliffProg.eval]
    rw [Function.update_self, Function.update_self, v_gp1, (hgp_a 5).1,
        Function.update_of_ne (wire_ne_of_lt (show base + 0 < base + 1 by omega)), v_gp1]
  have v_gp4 : gp4 wP2 = p2 := (Function.update_self _ _ _).trans (congrArg₂ _ v_gp3 (hgp_a 4).2.1)
  have v_gp5 : gp5 wP3 = p3 := (Function.update_self _ _ _).trans (congrArg₂ _ v_gp4 (hgp_a
    3).2.2.1)
  have v_gp7 : gp7 wP4 = p4 := by
    dsimp only [gp7, gp6, cP4, CliffProg.eval]
    rw [Function.update_self, Function.update_self, v_gp5, (hgp_a 2).2.2.2.1,
        Function.update_of_ne (wire_ne_of_lt (show base + 3 < base + 4 by omega)), v_gp5]
  obtain ⟨hp0_H, hp1_H, hp2_H, hp3_H⟩ :
      γH wP0 = p0 ∧ γH wP1 = p1 ∧ γH wP2 = p2 ∧ γH wP3 = p3 := by
    dsimp only [γH, gp8, gp7, gp6, gp5, gp4, gp3, gp2, cP1, cP4, cP5, CliffProg.eval]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      repeat rw [Function.update_of_ne (wire_ne_of_lt
        (by dsimp [wP0, wP1, wP2, wP3, wP4, wR5]; omega))]
    exacts [v_gp1, v_gp3, v_gp4, v_gp5]
  have hr5_H : γH wR5 = r5 := by
    dsimp only [γH, gp8, cP5, CliffProg.eval]
    rw [Function.update_self, Function.update_self, v_gp7, (hgp_a 1).2.2.2.2,
        Function.update_of_ne (wire_ne_of_lt (show base + 4 < base + 5 by omega)), v_gp7]
  obtain ⟨hclA, hKeepA0, hunA⟩ := hSpecTA γH (cleanRem_cast (by omega) hγH_clean)
  obtain ⟨hclB, hKeepB, hunB⟩ := hSpecTB γA (cleanRem_cast (by norm_num) hclA)
  obtain ⟨hclC, hKeepC, hunC⟩ := hSpecTC γB (cleanRem_cast (by norm_num) hclB)
  obtain ⟨hclD, hKeepD, hunD⟩ := hSpecTD γC (cleanRem_cast (by norm_num) hclC)
  obtain ⟨hclE, hKeepE, hunE⟩ := hSpecTE γD (cleanRem_cast (by norm_num) hclD)
  have hKeepE' (w : Wire M) (hw : w.val < uBase + 216) : γE w = γD w := hKeepE w hw
  have hKeepED (w) (hw : w.val < uBase + 208) : γE w = γC w :=
    (hKeepE' w (by omega)).trans (hKeepD w hw)
  have hKeepEDC (w) (hw : w.val < uBase + 192) : γE w = γB w :=
    (hKeepED w (by omega)).trans (hKeepC w hw)
  have hKeepEDCB (w) (hw : w.val < uBase + 128) : γE w = γA w :=
    (hKeepEDC w (by omega)).trans (hKeepB w hw)
  have hKeepA (w) (hw : w.val < uBase) : γA w = γH w := hKeepA0 w (by omega)
  have hKeepAB (w) (hw : w.val < uBase) : γB w = γH w := (hKeepB w (by omega)).trans (hKeepA w hw)
  have hKeepABC (w) (hw : w.val < uBase) : γC w = γH w :=
    (hKeepC w (by omega)).trans (hKeepAB w hw)
  have hKeepABCD (w) (hw : w.val < uBase) : γD w = γH w :=
    (hKeepD w (by omega)).trans (hKeepABC w hw)
  have hKeepAllHdr (w) (hw : w.val < uBase) : γE w = γH w :=
    (hKeepE' w (by omega)).trans (hKeepABCD w hw)
  have hAdr : ∀ {d : ℕ} (hd : d ≤ 8) (δ : BitAssignment M), (∀ w : Wire M, w.val < uBase → δ w =
    γH w) →
      (fun j : Fin d ↦ δ (a ⟨j.val, by omega⟩)) = fun j ↦ b ⟨j.val, by omega⟩ :=
    fun _ _ hδ ↦ funext fun j ↦
      (hδ _ (lt_of_lt_of_le (ha _) (by dsimp [uBase]; omega))).trans (hγH_lt _ (ha _))
  obtain ⟨hBA, hBB, hBC, hBD, hBE⟩ := dyadic218_block_bits b
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_, fun u hu ↦ ?_⟩
  · dsimp only [γF, cOob, CliffProg.eval]
    repeat rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [uRootA, uBase] at hw ⊢; omega))]
    exact hclE w (by dsimp [uBase]; norm_num; omega)
  · dsimp only [γF, cOob, CliffProg.eval]
    repeat rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [uRootA, uBase]; omega))]
    exact (hKeepAllHdr w (by dsimp [uBase]; omega)).trans (hγH_lt w hw)
  · have hA_eval : ∀ (k : ℕ) (hk : k < 128),
        γA ⟨uBase + 0 + k, by norm_num; omega⟩ = if k = bitsVal b then 1 else 0 := fun k hk ↦ by
      have hroot : cRA.eval γH ⟨uBase + 0, by omega⟩ = 1 + b 7 := by
        dsimp only [cRA, CliffProg.eval, uRootA]
        rw [Function.update_self, Function.update_self,
            hγH_clean ⟨uBase + 0, by omega⟩ (by dsimp [uBase]; omega), zero_add,
            Function.update_of_ne (wire_ne_of_lt (lt_of_lt_of_le (ha 7) (by dsimp [uBase]; omega))),
            hγH_lt (a 7) (ha 7)]
      have hev := hunA k (by norm_num; exact hk)
      rw [hroot, hAdr (by decide) γH (fun _ _ ↦ rfl)] at hev
      exact hev.trans (hBA k hk)
    by_cases hu0 : u = 0
    · subst hu0
      have huA_E : γE uRootA = if 0 = bitsVal b then 1 else 0 :=
        (hKeepEDCB uRootA (show uBase + 0 < uBase + 128 by omega)).trans (hA_eval 0 (by decide))
      have hF0 : γF uRootA = γE uRootA + (p0 + p1 + p3 + r5) := by
        dsimp only [γF, cOob, CliffProg.eval]
        rw [Function.update_self, Function.update_self, Function.update_self, Function.update_self]
        repeat rw [Function.update_of_ne (wire_ne_of_lt (by
          dsimp [wP0, wP1, wP3, wR5, uRootA, uBase]; omega))]
        rw [hKeepAllHdr wP0 (by dsimp [wP0, uBase]; omega), hp0_H,
            hKeepAllHdr wP1 (by dsimp [wP1, uBase]; omega), hp1_H,
            hKeepAllHdr wP3 (by dsimp [wP3, uBase]; omega), hp3_H,
            hKeepAllHdr wR5 (by dsimp [wR5, uBase]; omega), hr5_H]
        ring
      change γF uRootA = if 0 = clampIdx218 (bitsVal b) then 1 else 0
      rw [hF0, huA_E, dyadic218_oob_bit b]
      dsimp only [clampIdx218]
      by_cases hlt218 : bitsVal b < 218
      · simp only [hlt218, ↓reduceIte, add_zero]
      · simp only [hlt218, show ¬(0 = bitsVal b) by omega, ↓reduceIte, zero_add]
    · have hF_ne : γF ⟨uBase + u, by omega⟩ = γE ⟨uBase + u, by omega⟩ := by
        dsimp only [γF, cOob, CliffProg.eval]
        repeat rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [uRootA, uBase]; omega))]
      change γF ⟨uBase + u, by omega⟩ = if u = clampIdx218 (bitsVal b) then 1 else 0
      have hClampRhs : (if u = clampIdx218 (bitsVal b) then (1 : ZMod 2) else 0) = if u =
        bitsVal b then 1 else 0 := by
        dsimp only [clampIdx218]
        by_cases hlt218 : bitsVal b < 218
        · simp only [hlt218, ↓reduceIte]
        · simp only [hlt218, hu0, show ¬(u = bitsVal b) by omega, ↓reduceIte]
      rw [hF_ne, hClampRhs]
      by_cases hu128 : u < 128
      · exact (hKeepEDCB _ (show uBase + u < uBase + 128 by omega)).trans (hA_eval u hu128)
      · by_cases hu192 : u < 192
        · rw [hKeepEDC _ (show uBase + u < uBase + 192 by omega),
              show (⟨uBase + u, by omega⟩ : Wire M) =
                ⟨uBase + 128 + (u - 128), by omega⟩ from Fin.ext (by dsimp; omega)]
          have hev := hunB (u - 128) (by omega)
          rw [hAdr (by decide) γA hKeepA, hKeepA (a 7) (lt_of_lt_of_le (ha 7) (by omega)),
              hγH_lt (a 7) (ha 7), hKeepA wP0 (show base + 0 < uBase by omega), hp0_H] at hev
          simpa only [show 128 + (u - 128) = u by omega] using hev.trans (hBB (u - 128) (by omega))
        · by_cases hu208 : u < 208
          · rw [hKeepED _ (show uBase + u < uBase + 208 by omega),
                show (⟨uBase + u, by omega⟩ : Wire M) =
                  ⟨uBase + 192 + (u - 192), by omega⟩ from Fin.ext (by dsimp; omega)]
            have hev := hunC (u - 192) (by omega)
            rw [hAdr (by decide) γB hKeepAB, hKeepAB wP1 (show base + 1 < uBase by omega), hp1_H,
                hKeepAB wP2 (show base + 2 < uBase by omega), hp2_H] at hev
            simpa only [show 192 + (u - 192) = u by omega] using
              hev.trans (hBC (u - 192) (by omega))
          · by_cases hu216 : u < 216
            · rw [hKeepE' _ (show uBase + u < uBase + 216 by omega),
                  show (⟨uBase + u, by omega⟩ : Wire M) =
                    ⟨uBase + 208 + (u - 208), by omega⟩ from Fin.ext (by dsimp; omega)]
              have hev := hunD (u - 208) (by omega)
              rw [hAdr (by decide) γC hKeepABC, hKeepABC wP2 (show base + 2 < uBase by omega),
                  hp2_H, hKeepABC wP3 (show base + 3 < uBase by omega), hp3_H] at hev
              simpa only [show 208 + (u - 208) = u by omega] using
                hev.trans (hBD (u - 208) (by omega))
            · rw [show (⟨uBase + u, by omega⟩ : Wire M) =
                  ⟨uBase + 216 + (u - 216), by omega⟩ from Fin.ext (by dsimp; omega)]
              have hroot : cRE.eval γD ⟨uBase + 216, by omega⟩ = r5 := by
                dsimp only [cRE, CliffProg.eval, uRootE]
                rw [Function.update_self, show γD ⟨uBase + 216, by omega⟩ = 0 from
                      hclD ⟨uBase + 216, by omega⟩ (by dsimp [uBase]; omega),
                    zero_add, hKeepABCD wR5 (show base + 5 < uBase by omega), hr5_H]
              have hev := hunE (u - 216) (by omega)
              rw [hroot, hAdr (by decide) γD hKeepABCD] at hev
              simpa only [show 216 + (u - 216) = u by omega] using
                hev.trans (hBE (u - 216) (by omega))

attribute [local irreducible] ctxAnchorUnary218

/-- Balanced depth-`d` binary tree of leaf circuits indexed by `[lo .. lo + 2 ^ d)`. -/
def binCircuitTree {n : ℕ} (leaf : ℕ → Circuit n) : (d lo : ℕ) → Circuit n
  | 0, lo => leaf lo
  | d + 1, lo => binCircuitTree leaf d lo ;;ᶜ binCircuitTree leaf d (lo + 2 ^ d)

private theorem binCircuitTree_count_eq_sum {n a : ℕ} (leaf : ℕ → Circuit n) (g : PrimitiveGate a)
    (c : ℕ → ℕ) (hc : ∀ idx, (leaf idx).count g = c idx) :
    ∀ (d lo : ℕ), (binCircuitTree leaf d lo).count g = ∑ idx ∈ Finset.Ico lo (lo + 2 ^ d), c idx
  | 0, lo => by
      dsimp only [binCircuitTree]
      rw [show lo + 2 ^ 0 = lo + 1 from rfl, Nat.Ico_succ_singleton, Finset.sum_singleton, hc]
  | d + 1, lo => by
      dsimp only [binCircuitTree]
      rw [Circuit.count_seq, binCircuitTree_count_eq_sum leaf g c hc d lo,
          binCircuitTree_count_eq_sum leaf g c hc d (lo + 2 ^ d),
          show lo + 2 ^ (d + 1) = lo + 2 ^ d + 2 ^ d by ring]
      exact Finset.sum_Ico_consecutive c (Nat.le_add_right lo (2 ^ d))
        (Nat.le_add_right (lo + 2 ^ d) (2 ^ d))

private theorem binCircuitTree_count_zero {n a : ℕ} (leaf : ℕ → Circuit n) (g : PrimitiveGate a)
    (hc : ∀ idx, (leaf idx).count g = 0) (d lo : ℕ) : (binCircuitTree leaf d lo).count g = 0 := by
  rw [binCircuitTree_count_eq_sum leaf g (fun _ ↦ 0) hc d lo, Finset.sum_const_zero]

private theorem binCircuitTree_eval_ket_prod {n : ℕ} (leaf : ℕ → Circuit n)
    (β : BitAssignment n) (Φ : ℕ → ℂ)
    (hΦ : ∀ idx, (leaf idx).eval.1.mulVec (ket β) = Φ idx • ket β) :
    ∀ (d lo : ℕ),
      (binCircuitTree leaf d lo).eval.1.mulVec (ket β) =
        (∏ idx ∈ Finset.Ico lo (lo + 2 ^ d), Φ idx) • ket β
  | 0, lo => by
      dsimp only [binCircuitTree]
      rw [show lo + 2 ^ 0 = lo + 1 from rfl, Nat.Ico_succ_singleton, Finset.prod_singleton, hΦ]
  | d + 1, lo => by
      dsimp only [binCircuitTree]
      rw [eval_seq_mulVec, binCircuitTree_eval_ket_prod leaf β Φ hΦ d lo, Matrix.mulVec_smul,
          binCircuitTree_eval_ket_prod leaf β Φ hΦ d (lo + 2 ^ d), smul_smul,
          show lo + 2 ^ (d + 1) = lo + 2 ^ d + 2 ^ d by ring]
      exact congrArg (· • ket β) (Finset.prod_Ico_consecutive Φ (Nat.le_add_right lo (2 ^ d))
        (Nat.le_add_right (lo + 2 ^ d) (2 ^ d)))

private theorem prod_Ico_zero_cut {N B : ℕ} (hNB : N ≤ B) (g : Fin N → ℂ) :
    (∏ idx ∈ Finset.Ico 0 B, if hlt : idx < N then g ⟨idx, hlt⟩ else 1) = ∏ i : Fin N, g i := by
  let gc : ℕ → ℂ := fun idx ↦ if hlt : idx < N then g ⟨idx, hlt⟩ else 1
  have hTail : ∏ idx ∈ Finset.Ico N B, gc idx = 1 :=
    Finset.prod_eq_one fun idx hmem ↦ dite_eq_right (by rw [Finset.mem_Ico] at hmem; omega)
  rw [← Finset.prod_Ico_consecutive gc (Nat.zero_le N) hNB, hTail, mul_one, Nat.Ico_zero_eq_range,
    ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ ↦ dite_eq_left i.isLt

/-- Structurally recursive depth-`d` binary tree of `0-T CZ` phase kicks over all `218` electron
slots
`E_0 .. E_{217}` (`e = ⟨lo, hlt⟩`, `0 ≤ lo < 218`). -/
def all218SlotsCzTree {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18) (rCore : QRegister posCoreWires n)
    (rUnary : QRegister 218 n)
    (hCU : rCore.DisjointWires rUnary) : (d lo : ℕ) → Circuit n :=
  binCircuitTree fun lo ↦
    if hlt : lo < 218 then
      slotOneCzCircuit f j₀ (rUnary ⟨lo, hlt⟩) (rElecSlot rCore ⟨lo, hlt⟩)
        (fun _ h' ↦ hCU.ne _ ⟨lo, hlt⟩ h'.symm)
    else .identity

/-- Balanced depth-`8` binary-tree `0-T CZ` phase kick across all `218` electron slots `E_0 ..
E_{217}`. -/
noncomputable def all218SlotsCzCircuit {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18) (rCore : QRegister
    posCoreWires n) (rUnary : QRegister 218 n)
    (hCU : rCore.DisjointWires rUnary) : Circuit n :=
  lockVal3P (all218SlotsCzTree f j₀ rCore rUnary hCU 8 0)

theorem all218SlotsCzCircuit_eq {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18) (rCore : QRegister
    posCoreWires n) (rUnary : QRegister 218 n)
    (hCU : rCore.DisjointWires rUnary) : all218SlotsCzCircuit f j₀ rCore rUnary hCU =
      all218SlotsCzTree f j₀ rCore rUnary hCU 8 0 := lockVal3P_eq _

@[simp] theorem all218SlotsCzCircuit_count_toff {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (rUnary : QRegister 218 n)
    (hCU : rCore.DisjointWires rUnary) :
    (all218SlotsCzCircuit f j₀ rCore rUnary hCU).count PrimitiveGate.TOFF = 0 := by
  rw [all218SlotsCzCircuit_eq, all218SlotsCzTree]
  refine binCircuitTree_count_zero _ _ (fun lo ↦ ?_) 8 0
  split_ifs
  · simp [slotOneCzCircuit]
  · rfl

@[simp] theorem all218SlotsCzCircuit_count_t {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (rUnary : QRegister 218 n)
    (hCU : rCore.DisjointWires rUnary) :
    (all218SlotsCzCircuit f j₀ rCore rUnary hCU).count PrimitiveGate.T = 0 := by
  rw [all218SlotsCzCircuit_eq, all218SlotsCzTree]
  refine binCircuitTree_count_zero _ _ (fun lo ↦ ?_) 8 0
  split_ifs
  · simp [slotOneCzCircuit]
  · rfl

theorem all218SlotsCzCircuit_eval_ket {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (hf0 : f j₀ = true) (rCore : QRegister posCoreWires n) (rUnary : QRegister 218 n) (hCU :
      rCore.DisjointWires rUnary) (β : BitAssignment n) :
    (all218SlotsCzCircuit f j₀ rCore rUnary hCU).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (∑ i :
    Fin 218, β (rUnary i) * ∑ j : Fin 18, if f j = true then β (rElecSlot rCore i j) else 0).val) •
      ket β := by
  let gSlot : Fin 218 → ZMod 2 := fun i ↦
    β (rUnary i) * ∑ j : Fin 18, if f j = true then β (rElecSlot rCore i j) else 0
  rw [all218SlotsCzCircuit_eq, all218SlotsCzTree,
      binCircuitTree_eval_ket_prod _ β
        (fun idx ↦ if hlt : idx < 218 then (-1 : ℂ) ^ (gSlot ⟨idx, hlt⟩).val else 1)
        (fun lo ↦ by
          by_cases hlt : lo < 218
          · rw [dite_eq_left hlt, dite_eq_left hlt]
            exact slotOneCzCircuit_eval_ket f j₀ hf0 _ _ _ β
          · rw [dite_eq_right hlt, dite_eq_right hlt]
            simp) 8 0,
      show 0 + 2 ^ 8 = 256 by
        decide, prod_Ico_zero_cut (by decide) (fun i ↦ (-1 : ℂ) ^ (gSlot i).val),
      ← neg_one_pow_sum_zmod2]

attribute [local irreducible] all218SlotsCzCircuit

abbrev mAnchorUnclamped : ℕ := posCoreWires + 218
abbrev mAnchorClamped : ℕ := posCoreWires + 224

/-- Generic embedding of `posCoreWires` into `[0 .. posCoreWires)` of `M`. -/
def rCoreInGen {M : ℕ} (hM : posCoreWires ≤ M) : QRegister posCoreWires M :=
  { wires := { toFun := Fin.castLE hM
               inj' := fun _ _ h ↦ Fin.castLE_injective _ h } }

abbrev rCoreInAnchorUnclamped : QRegister posCoreWires mAnchorUnclamped :=
  rCoreInGen (Nat.le_add_right posCoreWires 218)

abbrev rCoreInAnchorClamped : QRegister posCoreWires mAnchorClamped :=
  rCoreInGen (Nat.le_add_right posCoreWires 224)

theorem rElecSlot_inGen_val {M : ℕ} (hM : posCoreWires ≤ M) (e : Fin 218) (j : Fin 18) : (rElecSlot
    (rCoreInGen hM) e j).val = 18 * e.val + j.val := rfl

theorem rElecSlot_inGen_lt {M : ℕ} (hM : posCoreWires ≤ M) (e : Fin 218) (j : Fin 18) : (rElecSlot
    (rCoreInGen hM) e j).val < posCoreWires := by
  rw [rElecSlot_apply_ofFin (rCoreInGen hM)]
  exact (rElecSlot (QRegExt.ofFin posCoreWires) e j).isLt

theorem rElecSlot_inGen_lt3924 {M : ℕ} (hM : posCoreWires ≤ M) (e : Fin 218) (j : Fin 18) :
    (rElecSlot (rCoreInGen hM) e j).val < 3924 := by
  rw [rElecSlot_inGen_val]; have := e.isLt; have := j.isLt; omega

theorem rAnchorIdx_inGen_ge3968 {M : ℕ} (hM : posCoreWires ≤ M) (d : Fin 8) : 3968 ≤ (rAnchorIdx
    (rCoreInGen hM) d).val := by
  rw [rAnchorIdx_apply_ofFin (rCoreInGen hM)]
  have h := rAnchorIdx_ofFin_val d
  change 3968 ≤ (rAnchorIdx (QRegExt.ofFin posCoreWires) d).val
  omega

theorem hSlice6_218 : 6 + 218 ≤ 224 := by decide

/-- Parametric `218`-slot `X`-reset phase-fixup circuit over `mClean` clean scratch wires with
unary slice `[uOff .. uOff + 218)`. -/
noncomputable def dAnchorPhaseFixGenRaw {Var : Type} {n : ℕ} (mClean uOff : ℕ)
    (huOff : uOff + 218 ≤ mClean) (K : TempCtx (posCoreWires + mClean)) (f : Fin 18 → Bool)
    (v : Var) (rCore : QRegister posCoreWires n) (rWork : QRegister mClean n) (hCW :
      rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  match findTrueBitAux f 18 (le_refl 18) with
  | none => .identity
  | some j₀ =>
      let rSub : QRegister 218 n := rWork.slice uOff 218 huOff
      let hCS : rCore.DisjointWires rSub := hCW.compose_right _
      let rComb : QRegister (posCoreWires + mClean) n := rCore.concat rWork hCW
      let leaf := all218SlotsCzCircuit f j₀ rCore rSub hCS
      toDynWithCircuit v rComb leaf K

theorem dAnchorPhaseFixGenRaw_toff {Var : Type} {n : ℕ} (mClean uOff : ℕ)
    (huOff : uOff + 218 ≤ mClean) (K : TempCtx (posCoreWires + mClean)) (f : Fin 18 → Bool)
    (v : Var) (rCore : QRegister posCoreWires n) (rWork : QRegister mClean n)
    (hCW : rCore.DisjointWires rWork) : (dAnchorPhaseFixGenRaw mClean uOff huOff K f v rCore rWork
      hCW).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dAnchorPhaseFixGenRaw]
  cases findTrueBitAux f 18 (le_refl 18) with
  | none => rfl
  | some j₀ =>
      exact toDynWithDyn_count_toff v _ (.circuit _)
        (all218SlotsCzCircuit_count_toff f j₀ rCore _ _) _

theorem dAnchorPhaseFixGenRaw_t_le {Var : Type} {n : ℕ} (mClean uOff nAnd : ℕ) (huOff : uOff +
    218 ≤ mClean) (K : TempCtx (posCoreWires + mClean))
    (hCnt : K.countTempAnd = nAnd) (f : Fin 18 → Bool) (v : Var) (rCore : QRegister posCoreWires n)
      (rWork : QRegister mClean n)
    (hCW : rCore.DisjointWires rWork) : (dAnchorPhaseFixGenRaw mClean uOff huOff K f v rCore rWork
      hCW).count PrimitiveGate.T ≤ 4 * nAnd := by
  dsimp only [dAnchorPhaseFixGenRaw]
  cases findTrueBitAux f 18 (le_refl 18) with
  | none => exact Nat.zero_le _
  | some j₀ =>
      change (toDynWithDyn v _ (.circuit _) _).count PrimitiveGate.T ≤ 4 * nAnd
      rw [toDynWithDyn_count_t, DynamicCircuit.count, all218SlotsCzCircuit_count_t, add_zero, hCnt]

theorem regVal_rAnchorIdx_lt256 {m : ℕ} (r : QRegister posCoreWires m) (γ : BitAssignment m) :
    regVal (rAnchorIdx r) γ < 256 := by
  simpa using regVal_lt_two_pow (rAnchorIdx r) γ

private theorem concat_rCoreInGen_apply {n mClean : ℕ} (rCore : QRegister posCoreWires n) (rWork :
    QRegister mClean n)
    (hCW : rCore.DisjointWires rWork) (i : Fin posCoreWires) : (rCore.concat rWork hCW) (rCoreInGen
      (Nat.le_add_right posCoreWires mClean) i) = rCore i := by
  rw [show rCoreInGen (Nat.le_add_right posCoreWires mClean) i = Fin.castAdd mClean i from Fin.ext
    rfl, QRegister.concat_apply_left]

private theorem concat_slice_unary_apply {n mClean uOff : ℕ} (huOff : uOff + 218 ≤ mClean) (rCore :
    QRegister posCoreWires n) (rWork : QRegister mClean n)
    (hCW : rCore.DisjointWires rWork) (i : ℕ) (hi : i < 218) : (rCore.concat rWork hCW)
      ⟨posCoreWires + uOff + i, by omega⟩ =
    (rWork.slice uOff 218 huOff) ⟨i, hi⟩ := by
  rw [show (⟨posCoreWires + uOff + i, by omega⟩ : Wire (posCoreWires + mClean)) =
        Fin.natAdd posCoreWires ⟨uOff + i, by omega⟩ from Fin.ext (by dsimp; omega),
      QRegister.concat_apply_right, QRegister.slice_apply]

private theorem rComb_padZeroBits_facts {n mClean : ℕ}
    (rCore : QRegister posCoreWires n) (rWork : QRegister mClean n)
    (hCW : rCore.DisjointWires rWork) (β : BitAssignment n) (hw : ∀ i : Fin mClean, β (rWork i) =
      0) :
    let rComb := rCore.concat rWork hCW
    let α : BitAssignment posCoreWires := fun i ↦ β (rCore i)
    (fun idx ↦ β (rComb idx)) = padZeroBits (mClean := mClean) α ∧
    cleanRem (posCoreWires + mClean) mClean (padZeroBits (mClean := mClean) α) ∧
    writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β ∧
    (∀ i : Fin posCoreWires,
      padZeroBits (mClean := mClean) α (rCoreInGen (Nat.le_add_right posCoreWires mClean) i) =
        α i) := by
  refine ⟨funext fun idx ↦ ?_, fun w hw' ↦ ?_, funext fun w ↦ ?_, fun i ↦ ?_⟩
  · refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      simp [padZeroBits]
    · rw [QRegister.concat_apply_right, padZeroBits, Fin.addCases_right]
      exact hw j
  · rw [show w = Fin.natAdd posCoreWires ⟨w.val - posCoreWires, by omega⟩ from Fin.ext (by
      dsimp; omega)]
    exact Fin.addCases_right _
  · by_cases hm : w ∈ Set.range (rCore.concat rWork hCW).wires
    · obtain ⟨idx, rfl⟩ := hm
      exact writeRegProg_apply_reg _ _ _ _
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
  · rw [show rCoreInGen (Nat.le_add_right posCoreWires mClean) i = Fin.castAdd mClean i from Fin.ext
      rfl]
    simp [padZeroBits]

private theorem realizesEmbedded_of_toDynWithCircuit {Var : Type} [Fintype Var] [DecidableEq Var] {n
    kAct mClean : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rCore : QRegister posCoreWires n) (rWork : QRegister mClean
      n) (hCW : rCore.DisjointWires rWork)
    (leaf : Circuit n) (K : TempCtx (posCoreWires + mClean)) (U_clean : Unitary (2 ^ n)) (U_target :
      Unitary (2 ^ kAct)) (hSmall : RealizesCleanUnitary v
    (projZeroAll mClean (tailScr (rCore.concat rWork hCW) mClean (Nat.le_add_left mClean
      posCoreWires)))
    (toDynWithCircuit v (rCore.concat rWork hCW) leaf K) U_clean) (hUeq : U_clean.1 * projZeroAll
      mClean rWork.wires =
    (rAct.embedUnitary U_target).1 * projZeroAll mClean rWork.wires) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    rAct rWork U_target (toDynWithCircuit v (rCore.concat rWork hCW) leaf K) := by
  let rComb := rCore.concat rWork hCW
  let P_work := projZeroAll mClean rWork.wires
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mClean _
  have htail_work : tailScr rComb mClean (Nat.le_add_left mClean posCoreWires) = rWork.wires := by
    funext j
    dsimp [tailScr, rComb]
    rw [show (⟨(posCoreWires + mClean - mClean) + j.val, by omega⟩ : Fin (posCoreWires + mClean)) =
          Fin.natAdd posCoreWires j from Fin.ext (by dsimp; omega),
        QRegister.concat_apply_right]
  have hSmallW : RealizesCleanUnitary v P_work (toDynWithCircuit v rComb leaf K) U_clean := by
    dsimp only [P_work, rComb] at htail_work ⊢
    rwa [← htail_work]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw hSmallW hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ :=
    toDynWithDyn_preservesStoreConst v rComb (.circuit leaf) (PreservesStoreConst.circuit leaf) K
      M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  rw [← congrFun hM_out default, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val hconj

theorem dAnchorPhaseFixGenRaw_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero
    (2 ^ n)]
    (mClean uOff : ℕ) (huOff : uOff + 218 ≤ mClean) (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256,
      idxFn val < 218) (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (htbl : ∀ (x : Fin (2 ^ posCoreWires)) (j : Fin 18), basisBits 18 (tbl x) j =
      basisBits posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires)
    ⟨idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x)),
    hIdxLt _ (regVal_rAnchorIdx_lt256 (QRegExt.ofFin posCoreWires) (basisBits posCoreWires x))⟩ j))
    (K : TempCtx (posCoreWires + mClean)) (hRest : RestoresAll K) (hSpec : (∀ q : Wire (posCoreWires
      + mClean),
    ScopedBlock (posCoreWires + mClean) ((posCoreWires + mClean) - posCoreWires) K.fwdBits (.z q)
      (K.plug (.z q))) ∧
    ∀ γ : BitAssignment (posCoreWires + mClean), cleanRem (posCoreWires + mClean) ((posCoreWires +
      mClean) - posCoreWires) γ →
    cleanRem (posCoreWires + mClean) ((posCoreWires + mClean) - (posCoreWires + uOff +
      218)) (K.fwdBits γ) ∧
    (∀ w : Wire (posCoreWires + mClean), w.val < posCoreWires → K.fwdBits γ w = γ w) ∧
    (∀ (u : ℕ) (_ : u < 218), K.fwdBits γ ⟨posCoreWires + uOff + u, by omega⟩ =
    if u = idxFn (regVal (rAnchorIdx (rCoreInGen (Nat.le_add_right posCoreWires mClean))) γ) then 1
      else 0))
    (f : Fin 18 → Bool) (v : Var) (rCore : QRegister posCoreWires n) (rWork : QRegister mClean n)
      (hCW : rCore.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork (diagSignUnitary (fun x ↦
      f2Parity 18 f (tbl x)))
    (dAnchorPhaseFixGenRaw mClean uOff huOff K f v rCore rWork hCW) := by
  let M := posCoreWires + mClean
  let rCoreM := rCoreInGen (Nat.le_add_right posCoreWires mClean)
  dsimp only [dAnchorPhaseFixGenRaw]
  obtain ⟨hSome, hNone⟩ := findTrueBitAux_spec f 18 (le_refl 18)
  cases hfind : findTrueBitAux f 18 (le_refl 18) with
  | none =>
      have hf (j : Fin 18) : f j = false := hNone hfind j.val j.isLt
      have hPar : (fun x ↦ f2Parity 18 f (tbl x)) = fun _ ↦ false := funext fun x ↦ by
        have hp := sign_f2Parity_eq_prod 18 f (tbl x)
        simp only [hf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Finset.prod_const_one] at hp
        exact Bool.eq_false_iff.mpr fun ht ↦ by
          rw [ht] at hp
          norm_num at hp
      rw [hPar, diagSignUnitary_false]
      exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rCore rWork
  | some j₀ =>
      let rSub : QRegister 218 n := rWork.slice uOff 218 huOff
      let rComb : QRegister M n := rCore.concat rWork hCW
      let leaf := all218SlotsCzCircuit f j₀ rCore rSub (hCW.compose_right _)
      obtain ⟨hProbes, hFwdSpec⟩ := hSpec
      let q₀ : Wire M := ⟨0, by dsimp [M]; omega⟩
      let phComb : BitAssignment M → ZMod 2 := fun γ ↦
        ∑ i : Fin 218, γ ⟨posCoreWires + uOff + i.val, by dsimp [M]; omega⟩ *
          ∑ j : Fin 18, if f j = true then γ (rElecSlot rCoreM i j) else 0
      have hLeafKet (β : BitAssignment n) :
          leaf.eval.1.mulVec (ket β) =
            ((-1 : ℂ) ^ (phComb (fun idx ↦ β (rComb idx))).val) • ket β := by
        rw [all218SlotsCzCircuit_eval_ket f j₀ (hSome j₀ hfind) rCore rSub _ β]
        refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β)
          (Finset.sum_congr rfl fun i _ ↦ ?_)
        have hs (j : Fin 18) : β (rElecSlot rCore i j) = β (rComb (rElecSlot rCoreM i j)) := by
          rw [rElecSlot_apply_ofFin rCore, rElecSlot_apply_ofFin rCoreM, concat_rCoreInGen_apply]
        dsimp only [rSub]
        simp_rw [congrArg β (concat_slice_unary_apply huOff rCore rWork hCW i.val i.isLt).symm, hs]
        rfl
      obtain ⟨U_clean, hSmall, hKetClean⟩ :=
        realizes_toDynWithDyn_of_valid v rComb 0 (Nat.zero_le _) (.z q₀)
          (fun _ _ ↦ Nat.zero_le _) (fun _ ↦ rfl) (.circuit leaf) leaf.eval
          (RealizesCleanUnitary.circuit v _ leaf) phComb hLeafKet K mClean
          (Nat.le_add_left mClean posCoreWires) (((hProbes q₀).cast_rem (by omega)).valid)
      refine realizesEmbedded_of_toDynWithCircuit v rCore rCore rWork hCW leaf K U_clean _
        hSmall (matrix_ext_ket fun β ↦ ?_)
      simp only [mul_mulVec_prog, ket_projZeroAll]
      by_cases hw : ∀ i : Fin mClean, β (rWork i) = 0
      · simp only [hw, imp_true_iff, ↓reduceIte, hKetClean]
        let α : BitAssignment posCoreWires := fun i ↦ β (rCore i)
        obtain ⟨hpad, hcleanPad, hwId, hCorePadRaw⟩ := rComb_padZeroBits_facts rCore rWork hCW β hw
        rw [hRest (.z q₀) (fun _ ↦ rfl) _, hwId, hpad]
        obtain ⟨_, hCoreLt, hUnary⟩ :=
          hFwdSpec (padZeroBits (mClean := mClean) α) (cleanRem_cast (by omega) hcleanPad)
        let γK := K.fwdBits (padZeroBits (mClean := mClean) α)
        let x := (basisBitsEquiv posCoreWires).symm α
        have hxBits : basisBits posCoreWires x = α := basisBits_symm_apply α
        have hAncEq : regVal (rAnchorIdx rCoreM) (padZeroBits (mClean := mClean) α) =
            regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x) := by
          rw [hxBits]
          exact regVal_congr_cross _ _ _ _ fun k ↦
            (congrArg (padZeroBits α) (rAnchorIdx_apply_ofFin rCoreM k)).trans (hCorePadRaw _)
        have hPh : phComb γK = ∑ j : Fin 18, if f j = true then basisBits 18 (tbl x) j else 0 := by
          dsimp only [phComb, γK]
          let i₀ : Fin 218 :=
            ⟨idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x)),
              hIdxLt _ (regVal_rAnchorIdx_lt256 _ (basisBits posCoreWires x))⟩
          rw [Finset.sum_eq_single i₀]
          · rw [hUnary i₀.val i₀.isLt, hAncEq, ite_eq_left rfl, one_mul]
            exact Finset.sum_congr rfl fun j _ ↦ by
              rw [hCoreLt _ (rElecSlot_inGen_lt (Nat.le_add_right _ _) i₀ j),
                  rElecSlot_apply_ofFin rCoreM, (show _ = α _ from hCorePadRaw _), ← hxBits,
                  htbl x j]
          · intro i _ hne
            rw [hUnary i.val i.isLt, hAncEq, ite_eq_right (fun hv ↦ hne (Fin.ext hv)), zero_mul]
          · exact fun habs ↦ absurd (Finset.mem_univ i₀) habs
        let g := (basisBitsEquiv n).symm β
        have hket : (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) = ket β :=
          funext fun u ↦ by simp [g, ket, basisState]
        rw [hPh, neg_one_pow_sum_zmod2,
            Finset.prod_congr rfl fun j _ ↦ sign_zmod2_bool_if (f j) (basisBits 18 (tbl x) j),
            ← sign_f2Parity_eq_prod, ← hket, embedUnitary_diagSignUnitary_mulVec_single, hket,
            show rCore.extractIndex g = x from eq_of_basisBits_eq fun i ↦ by
              rw [QRegister.basisBits_extractIndex, hxBits, basisBits_symm_apply_at]]
      · simp [hw]

/-- Unclamped `<= 840-T` (`0 .TOFF`, `218` clean wires) `X`-reset phase fixup for
`anchorTblVal218Unclamped`. -/
noncomputable def dAnchorPhaseFix218Unclamped {Var : Type} {n : ℕ} (f : Fin 18 → Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rWork218 : QRegister 218 n)
    (hCW : rCore.DisjointWires rWork218) : DynamicCircuit Var n := lockVal3P
    (dAnchorPhaseFixGenRaw 218 0 (by decide) (ctxAnchorUnary218Unclamped
    rCoreInAnchorUnclamped posCoreWires le_rfl (fun i ↦ i.isLt)) f v rCore rWork218 hCW)

theorem dAnchorPhaseFix218Unclamped_eq {Var : Type} {n : ℕ} (f : Fin 18 → Bool) (v : Var) (rCore :
    QRegister posCoreWires n) (rWork218 : QRegister 218 n)
    (hCW : rCore.DisjointWires rWork218) : dAnchorPhaseFix218Unclamped f v rCore rWork218 hCW
    = dAnchorPhaseFixGenRaw 218 0 (by decide) (ctxAnchorUnary218Unclamped rCoreInAnchorUnclamped
      posCoreWires le_rfl (fun i ↦ i.isLt)) f v rCore rWork218 hCW :=
    lockVal3P_eq _

theorem dAnchorPhaseFix218Unclamped_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)]
    (f : Fin 18 → Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rWork218 : QRegister 218 n)
    (hCW : rCore.DisjointWires rWork218) :
    let dyn := dAnchorPhaseFix218Unclamped f v rCore rWork218 hCW
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork218
        (diagSignUnitary (fun x ↦ f2Parity 18 f (anchorTblVal218Unclamped x))) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T ≤ 840 := by
  dsimp only
  rw [dAnchorPhaseFix218Unclamped_eq]
  obtain ⟨hP, hS⟩ := ScopedBlock.ctxAnchorUnary218Unclamped_fwdBits_spec
    rCoreInAnchorUnclamped posCoreWires le_rfl (fun i ↦ i.isLt)
  refine ⟨dAnchorPhaseFixGenRaw_realizes 218 0 (by decide) aliasIdx218 (fun _ hv ↦ aliasIdx218_lt
    hv)
    anchorTblVal218Unclamped basisBits_anchorTblVal218Unclamped _
    (RestoresAll.anchorUnary218Unclamped _ _ _ _)
    ⟨hP, fun γ hγ ↦ by
      obtain ⟨h1, h2, h3⟩ := hS γ hγ
      exact ⟨h1, h2, fun u hu ↦ by simpa only [Nat.add_zero] using h3 u hu⟩⟩
    f v rCore rWork218 hCW,
    dAnchorPhaseFixGenRaw_toff _ _ _ _ f v rCore rWork218 hCW,
    dAnchorPhaseFixGenRaw_t_le 218 0 210 _ _
      (ctxAnchorUnary218Unclamped_countTempAnd _ _ _ _) f v rCore rWork218 hCW⟩

/-- `< 218`-Clamped `<= 876-T` (`0 .TOFF`, `224` clean wires) `X`-reset phase fixup for
`anchorTblVal218`. -/
noncomputable def dAnchorPhaseFix218 {Var : Type} {n : ℕ} (f : Fin 18 → Bool) (v : Var) (rCore :
    QRegister posCoreWires n) (rWork224 : QRegister 224 n)
    (hCW : rCore.DisjointWires rWork224) : DynamicCircuit Var n := lockVal3P
    (dAnchorPhaseFixGenRaw 224 6 hSlice6_218 (ctxAnchorUnary218 rCoreInAnchorClamped
    posCoreWires le_rfl (fun i ↦ i.isLt)) f v rCore rWork224 hCW)

theorem dAnchorPhaseFix218_eq {Var : Type} {n : ℕ} (f : Fin 18 → Bool) (v : Var) (rCore : QRegister
    posCoreWires n) (rWork224 : QRegister 224 n)
    (hCW : rCore.DisjointWires rWork224) : dAnchorPhaseFix218 f v rCore rWork224 hCW =
    dAnchorPhaseFixGenRaw 224 6 hSlice6_218 (ctxAnchorUnary218 rCoreInAnchorClamped
    posCoreWires le_rfl (fun i ↦ i.isLt)) f v rCore rWork224 hCW := lockVal3P_eq _

theorem dAnchorPhaseFix218_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^
    n)]
    (f : Fin 18 → Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rWork224 : QRegister 224 n)
    (hCW : rCore.DisjointWires rWork224) :
    let dyn := dAnchorPhaseFix218 f v rCore rWork224 hCW
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork224
        (diagSignUnitary (fun x ↦ f2Parity 18 f (anchorTblVal218 x))) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T ≤ 876 := by
  dsimp only
  rw [dAnchorPhaseFix218_eq]
  refine ⟨dAnchorPhaseFixGenRaw_realizes 224 6 hSlice6_218 clampIdx218 (fun val _ ↦
    clampIdx218_lt val) anchorTblVal218 basisBits_anchorTblVal218 _
    (RestoresAll.anchorUnary218 _ _ _ _) (ScopedBlock.ctxAnchorUnary218_fwdBits_spec
    rCoreInAnchorClamped posCoreWires le_rfl (fun i ↦ i.isLt)) f v rCore rWork224 hCW,
    dAnchorPhaseFixGenRaw_toff _ _ _ _ f v rCore rWork224 hCW, dAnchorPhaseFixGenRaw_t_le 224
    6 219 _ _ (ctxAnchorUnary218_countTempAnd _ _ _ _) f v rCore rWork224 hCW⟩

attribute [local irreducible] dAnchorPhaseFix218Unclamped dAnchorPhaseFix218

/-- Classical `18`-bit `E_0`-centered table value (`tbl x ⊕ E_0(x)`). -/
noncomputable def centeredDiffTblE0 (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18)) (x : Fin (2 ^
    posCoreWires)) : Fin (2 ^ 18) :=
  let βL := basisBits posCoreWires x
  let rCoreL := QRegExt.ofFin posCoreWires
  (basisBitsEquiv 18).symm fun j ↦
    basisBits 18 (tbl x) j + βL (rElecSlot rCoreL 0 j)

theorem basisBits_centeredDiffTblE0 (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (x : Fin (2 ^ posCoreWires)) (j : Fin 18) : basisBits 18 (centeredDiffTblE0 tbl x) j =
      basisBits 18 (tbl x) j + basisBits posCoreWires x
    (rElecSlot (QRegExt.ofFin posCoreWires) 0 j) := basisBits_symm_apply_at _ j

/-- XORs `E_0[0 .. b)` into `E_{k + 1}[0 .. b)` (`k < 217`, `0` `TempAnd`s) inside `M ≥
posCoreWires`. -/
def cXorE0SlotBits {M : ℕ} (hM : posCoreWires ≤ M) (k : ℕ) (hk : k < 217) :
    (b : ℕ) → (hb : b ≤ 18) → CliffProg M
  | 0, _ => .nil
  | b + 1, hb =>
      let j : Fin 18 := ⟨b, by omega⟩
      .seq (cXorE0SlotBits hM k hk b (by omega))
        (.cnot (rElecSlot (rCoreInGen hM) 0 j) (rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j)
          (wire_ne_of_lt (by
            rw [rElecSlot_inGen_val, rElecSlot_inGen_val]; dsimp; omega)))

theorem cXorE0SlotBits_supports {M : ℕ} (hM : posCoreWires ≤ M) (k : ℕ) (hk : k < 217) :
    ∀ (b : ℕ) (hb : b ≤ 18), (cXorE0SlotBits hM k hk b hb).SupportsBelow posCoreWires
  | 0, _ => trivial
  | b + 1, hb =>
      ⟨cXorE0SlotBits_supports hM k hk b (by omega),
        rElecSlot_inGen_lt hM _ _, rElecSlot_inGen_lt hM _ _⟩

theorem cXorE0SlotBits_eval {M : ℕ} (hM : posCoreWires ≤ M) (k : ℕ) (hk : k < 217)
    (γ : BitAssignment M) :
    ∀ (b : ℕ) (hb : b ≤ 18),
      (∀ w : Wire M, (∀ j : Fin 18, w ≠ rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) →
        (cXorE0SlotBits hM k hk b hb).eval γ w = γ w) ∧
      (∀ j : Fin 18,
        (cXorE0SlotBits hM k hk b hb).eval γ (rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) =
          γ (rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) +
            if j.val < b then γ (rElecSlot (rCoreInGen hM) 0 j) else 0)
  | 0, _ => ⟨fun _ _ ↦ rfl, fun _ ↦ by simp [cXorE0SlotBits, CliffProg.eval]⟩
  | b + 1, hb => by
      obtain ⟨hOther, hSlot⟩ := cXorE0SlotBits_eval hM k hk γ b (by omega)
      let jb : Fin 18 := ⟨b, by omega⟩
      have hE0_ne (j : Fin 18) :
          rElecSlot (rCoreInGen hM) 0 jb ≠ rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j :=
        wire_ne_of_lt (by
          simp only [rElecSlot_inGen_val, jb]
          have := j.isLt
          omega)
      refine ⟨fun w hw ↦ ?_, fun j ↦ ?_⟩
      · dsimp only [cXorE0SlotBits, CliffProg.eval]
        exact (Function.update_of_ne (hw jb) _ _).trans (hOther w hw)
      · dsimp only [cXorE0SlotBits, CliffProg.eval]
        by_cases hjb : j = jb
        · subst hjb
          simp [Function.update_self, hSlot jb, hOther _ hE0_ne, jb]
        · have hw_ne : rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j ≠
              rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ jb := fun h ↦ hjb <| Fin.ext <| by
            have hv := congrArg Fin.val h
            rw [rElecSlot_inGen_val, rElecSlot_inGen_val] at hv
            dsimp [jb] at hv ⊢
            omega
          rw [Function.update_of_ne hw_ne, hSlot j]
          have : j.val ≠ b := fun hv ↦ hjb (Fin.ext hv)
          simp [show (j.val < b + 1) ↔ (j.val < b) by omega]

/-- XORs `E_0` into all `s` slots `E_1 .. E_s` (`s ≤ 217`, `0` `TempAnd`s). -/
def cXorE0AllSlots217 {M : ℕ} (hM : posCoreWires ≤ M) : (s : ℕ) → (hs : s ≤ 217) → CliffProg M
  | 0, _ => .nil
  | s + 1, hs => .seq (cXorE0AllSlots217 hM s (by omega)) (cXorE0SlotBits hM s (by omega) 18 le_rfl)

theorem cXorE0AllSlots217_supports {M : ℕ} (hM : posCoreWires ≤ M) :
    ∀ (s : ℕ) (hs : s ≤ 217), (cXorE0AllSlots217 hM s hs).SupportsBelow posCoreWires
  | 0, _ => trivial
  | s + 1, _ =>
      ⟨cXorE0AllSlots217_supports hM s (by omega), cXorE0SlotBits_supports hM s (by omega) 18
      le_rfl⟩

theorem cXorE0AllSlots217_eval {M : ℕ} (hM : posCoreWires ≤ M) (γ : BitAssignment M) :
    ∀ (s : ℕ) (hs : s ≤ 217),
      (∀ w : Wire M, (∀ (k : ℕ) (_ : k < 217) (j : Fin 18),
        w ≠ rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) →
        (cXorE0AllSlots217 hM s hs).eval γ w = γ w) ∧
      (∀ (k : ℕ) (hk : k < 217) (j : Fin 18),
        (cXorE0AllSlots217 hM s hs).eval γ (rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) =
          γ (rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) +
            if k < s then γ (rElecSlot (rCoreInGen hM) 0 j) else 0)
  | 0, _ => ⟨fun _ _ ↦ rfl, fun _ _ _ ↦ by simp [cXorE0AllSlots217, CliffProg.eval]⟩
  | s + 1, hs => by
      obtain ⟨hOtherPrev, hSlotPrev⟩ := cXorE0AllSlots217_eval hM γ s (by omega)
      let γ₁ := (cXorE0AllSlots217 hM s (by omega)).eval γ
      obtain ⟨hOtherStep, hSlotStep⟩ := cXorE0SlotBits_eval hM s (by omega) γ₁ 18 le_rfl
      have hE0_γ₁ (j : Fin 18) :
          γ₁ (rElecSlot (rCoreInGen hM) 0 j) = γ (rElecSlot (rCoreInGen hM) 0 j) :=
        hOtherPrev _ fun k _ j' ↦ wire_ne_of_lt (by
          rw [rElecSlot_inGen_val, rElecSlot_inGen_val]
          have := j.isLt
          dsimp
          omega)
      refine ⟨fun w hw ↦ (hOtherStep w (hw s (by omega))).trans (hOtherPrev w hw), fun k hk j ↦ ?_⟩
      dsimp only [cXorE0AllSlots217, CliffProg.eval]
      by_cases hks : k = s
      · subst hks
        change (cXorE0SlotBits hM k (by omega) 18 le_rfl).eval γ₁ _ = _
        rw [hSlotStep j, ite_eq_left j.isLt, hE0_γ₁ j, show γ₁ _ = _ from hSlotPrev k hk j,
            ite_eq_right (Nat.lt_irrefl k), add_zero, ite_eq_left (Nat.lt_succ_self k)]
      · have hSlotNe (j' : Fin 18) : rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j ≠
            rElecSlot (rCoreInGen hM) ⟨s + 1, by omega⟩ j' := fun h ↦ hks <| by
          have hv := congrArg Fin.val h
          rw [rElecSlot_inGen_val, rElecSlot_inGen_val] at hv
          have := j.isLt
          have := j'.isLt
          dsimp at hv
          omega
        change (cXorE0SlotBits hM s (by omega) 18 le_rfl).eval γ₁ _ = _
        rw [hOtherStep _ hSlotNe, show γ₁ _ = _ from hSlotPrev k hk j]
        simp [show (k < s + 1) ↔ (k < s) by omega]

/-- Kernel-locked `3,906`-CNOT `E_0`-centering Clifford pre/post pass (`0` `TempAnd`s). -/
noncomputable def cXorE0217Locked {M : ℕ} (hM : posCoreWires ≤ M) : CliffProg M :=
  lockVal3P (cXorE0AllSlots217 hM 217 le_rfl)

theorem cXorE0217Locked_eq {M : ℕ} (hM : posCoreWires ≤ M) : cXorE0217Locked hM = cXorE0AllSlots217
    hM 217 le_rfl := lockVal3P_eq _

theorem cXorE0217Locked_supports {M : ℕ} (hM : posCoreWires ≤ M) : (cXorE0217Locked
    hM).SupportsBelow posCoreWires := by
  rw [cXorE0217Locked_eq]; exact cXorE0AllSlots217_supports hM 217 le_rfl

theorem cXorE0217Locked_eval {M : ℕ} (hM : posCoreWires ≤ M) (γ : BitAssignment M) : (∀ w : Wire M,
    (∀ (k : ℕ) (_ : k < 217) (j : Fin 18), w ≠ rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) →
      (cXorE0217Locked hM).eval γ w = γ w) ∧
    (∀ (k : ℕ) (hk : k < 217) (j : Fin 18), (cXorE0217Locked hM).eval γ (rElecSlot (rCoreInGen hM)
      ⟨k + 1, by omega⟩ j) =
    γ (rElecSlot (rCoreInGen hM) ⟨k + 1, by omega⟩ j) + if k < 217 then γ (rElecSlot (rCoreInGen hM)
      0 j) else 0) := by
  rw [cXorE0217Locked_eq]; exact cXorE0AllSlots217_eval hM γ 217 le_rfl

attribute [local irreducible] cXorE0217Locked

/-- Balanced depth-`d` binary tree of `36-T` `slotOneHotAux` circuits across the `217` active
`E_0`-centered slots `E_1 .. E_{217}` (`u = lo + 1 ∈ {1 .. 217}`). -/
def all217SlotsOneHotTree {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n)
    (rUnary : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hAU : rAnchor18.DisjointWires rUnary) : (d lo : ℕ) →
      Circuit n :=
  binCircuitTree fun lo ↦
    if hlt : lo < 217 then
      let e : Fin 218 := ⟨lo + 1, by omega⟩
      slotOneHotAux rAnchor18 (rUnary e) (rElecSlot rCore e)
        (fun j ↦ (hAU.ne j e).symm)
        (fun j ↦ by rw [rElecSlot_apply_ofFin rCore]; exact hCA.ne _ j) 18 (le_refl 18)
    else .identity

/-- Kernel-locked `7,848-T` (`7,812 + 36`) diagonal phase-difference leaf circuit (`0 .TOFF`). -/
noncomputable def leafDiag217Circuit {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18 :
    QRegister 18 n) (rUnary : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hAU : rAnchor18.DisjointWires rUnary) : Circuit n :=
  lockVal3P
    (all217SlotsOneHotTree rCore rAnchor18 rUnary hCA hAU 8 0 ;;ᶜ
     oobFixAux rAnchor18 (rUnary ⟨0, by decide⟩) (fun j ↦ (hAU.ne j ⟨0, by decide⟩).symm) 18
       (le_refl 18))

theorem leafDiag217Circuit_eq {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18
    n) (rUnary : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hAU : rAnchor18.DisjointWires rUnary) :
      leafDiag217Circuit rCore rAnchor18 rUnary hCA hAU =
    (all217SlotsOneHotTree rCore rAnchor18 rUnary hCA hAU 8 0 ;;ᶜ
    oobFixAux rAnchor18 (rUnary ⟨0, by decide⟩) (fun j ↦ (hAU.ne j ⟨0, by decide⟩).symm) 18 (le_refl
      18)) :=
  lockVal3P_eq _

@[simp] theorem leafDiag217Circuit_count_toff {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18
    : QRegister 18 n) (rUnary : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hAU : rAnchor18.DisjointWires rUnary) :
    (leafDiag217Circuit rCore rAnchor18 rUnary hCA hAU).count PrimitiveGate.TOFF = 0 := by
  rw [leafDiag217Circuit_eq, Circuit.count_seq, oobFixAux_count_toff, add_zero,
    all217SlotsOneHotTree]
  exact binCircuitTree_count_zero _ _ (fun lo ↦ by
    by_cases hlt : lo < 217
    · rw [dite_eq_left hlt]
      exact slotOneHotAux_count_toff _ _ _ _ _ 18 (le_refl 18)
    · rw [dite_eq_right hlt]
      rfl) 8 0

@[simp] theorem leafDiag217Circuit_count_t {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18 :
    QRegister 18 n) (rUnary : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hAU : rAnchor18.DisjointWires rUnary) :
    (leafDiag217Circuit rCore rAnchor18 rUnary hCA hAU).count PrimitiveGate.T = 7848 := by
  let gc : ℕ → ℕ := fun idx ↦ if idx < 217 then 36 else 0
  have ht0 : ∑ idx ∈ Finset.Ico 217 256, gc idx = 0 :=
    Finset.sum_eq_zero fun idx hmem ↦ ite_eq_right (by rw [Finset.mem_Ico] at hmem; omega)
  have hh0 : ∑ idx ∈ Finset.Ico 0 217, gc idx = 7812 := by
    rw [Finset.sum_congr rfl fun idx hmem ↦ ite_eq_left (by rw [Finset.mem_Ico] at hmem; omega),
        Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  rw [leafDiag217Circuit_eq, Circuit.count_seq, all217SlotsOneHotTree,
      binCircuitTree_count_eq_sum _ _ gc (fun lo ↦ by
        by_cases hlt : lo < 217
        · rw [dite_eq_left hlt]
          exact (slotOneHotAux_count_t _ _ _ _ _ 18 (le_refl 18)).trans (ite_eq_left hlt).symm
        · rw [dite_eq_right hlt]
          exact (ite_eq_right hlt).symm) 8 0,
      oobFixAux_count_t _ _ _ 18 (le_refl 18), show 0 + 2 ^ 8 = 256 by decide,
      ← Finset.sum_Ico_consecutive gc (Nat.zero_le 217) (by decide : 217 ≤ 256),
      ht0, add_zero, hh0]

theorem leafDiag217Circuit_eval_ket {n : ℕ} (rCore : QRegister posCoreWires n) (rAnchor18 :
    QRegister 18 n) (rUnary : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hAU : rAnchor18.DisjointWires rUnary) (β : BitAssignment
      n) :
    (leafDiag217Circuit rCore rAnchor18 rUnary hCA hAU).eval.1.mulVec (ket β) = ((∏ i : Fin 217,
      ∏ j : Fin 18,
    oneHotBitPhase (β (rAnchor18 j)) (β (rUnary ⟨i.val + 1, by omega⟩)) (β (rElecSlot rCore ⟨i.val +
      1, by omega⟩ j))) *
    (∏ j : Fin 18, oneHotBoundaryPhase (β (rAnchor18 j)) (β (rUnary ⟨0, by decide⟩)))) • ket β := by
  let gSlot : Fin 217 → ℂ := fun i ↦
    ∏ j : Fin 18, oneHotBitPhase (β (rAnchor18 j)) (β (rUnary ⟨i.val + 1, by omega⟩))
      (β (rElecSlot rCore ⟨i.val + 1, by omega⟩ j))
  rw [leafDiag217Circuit_eq, eval_seq_mulVec, all217SlotsOneHotTree,
      binCircuitTree_eval_ket_prod _ β
        (fun idx ↦ if hlt : idx < 217 then gSlot ⟨idx, hlt⟩ else 1)
        (fun lo ↦ by
          by_cases hlt : lo < 217
          · rw [dite_eq_left hlt, dite_eq_left hlt]
            exact slotOneHotAux_eval_ket _ _ _ _ _ β 18 (le_refl 18)
          · rw [dite_eq_right hlt, dite_eq_right hlt]
            simp) 8 0,
      Matrix.mulVec_smul, oobFixAux_eval_ket _ _ _ β 18 (le_refl 18), smul_smul,
      show 0 + 2 ^ 8 = 256 by decide, prod_Ico_zero_cut (by decide) gSlot]

attribute [local irreducible] leafDiag217Circuit

/-- Local `18`-CNOT `E_0` post-XOR (`0 T`, `0 .TOFF`) restoring `tbl` from `centeredDiffTblE0
tbl`. -/
def localPostXorE0 : (m : ℕ) → (hm : m ≤ 18) → Circuit (posCoreWires + 18)
  | 0, _ => .identity
  | m + 1, hm =>
      let j : Fin 18 := ⟨m, by omega⟩
      let cWire : Wire (posCoreWires + 18) :=
        Fin.castAdd 18 (rElecSlot (QRegExt.ofFin posCoreWires) 0 j)
      let tWire : Wire (posCoreWires + 18) := Fin.natAdd posCoreWires j
      localPostXorE0 m (Nat.le_of_succ_le hm) ;;ᶜ
      Circuit.CNOT cWire tWire (wire_ne_of_lt (by
        change (rElecSlot (QRegExt.ofFin posCoreWires) 0 j).val < posCoreWires + j.val
        exact lt_of_lt_of_le (rElecSlot (QRegExt.ofFin posCoreWires) 0 j).isLt (Nat.le_add_right _
          _)))

def localPostHSAndXorE0_18 : Circuit (posCoreWires + 18) :=
  localHSPrefix 18 (le_refl 18) ;;ᶜ localPostXorE0 18 (le_refl 18)

theorem localPostXorE0_count_toff :
    ∀ (m : ℕ) (hm : m ≤ 18), (localPostXorE0 m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [localPostXorE0]
      rw [Circuit.count_seq, localPostXorE0_count_toff m (Nat.le_of_succ_le hm), zero_add]; rfl

theorem localPostXorE0_count_t :
    ∀ (m : ℕ) (hm : m ≤ 18), (localPostXorE0 m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [localPostXorE0]
      rw [Circuit.count_seq, localPostXorE0_count_t m (Nat.le_of_succ_le hm), zero_add]; rfl

theorem localPostHSAndXorE0_18_count_toff : localPostHSAndXorE0_18.count PrimitiveGate.TOFF = 0 :=
  by
  dsimp only [localPostHSAndXorE0_18]
  rw [Circuit.count_seq, localHSPrefix_count_toff, localPostXorE0_count_toff]

theorem localPostHSAndXorE0_18_count_t : localPostHSAndXorE0_18.count PrimitiveGate.T = 0 := by
  dsimp only [localPostHSAndXorE0_18]
  rw [Circuit.count_seq, localHSPrefix_count_t, localPostXorE0_count_t]

/-- Partial bit-XOR adding `E_0[0 .. m)` onto the `18` anchor wires. -/
def xorE0Pref18 :
    (m : ℕ) → (hm : m ≤ 18) → BitAssignment (posCoreWires + 18) → BitAssignment (posCoreWires + 18)
  | 0, _, γ => γ
  | m + 1, hm, γ =>
      let j : Fin 18 := ⟨m, by omega⟩
      let γ' := xorE0Pref18 m (Nat.le_of_succ_le hm) γ
      Function.update γ' (Fin.natAdd posCoreWires j)
        (γ' (Fin.natAdd posCoreWires j) +
          γ' (Fin.castAdd 18 (rElecSlot (QRegExt.ofFin posCoreWires) 0 j)))

theorem xorE0Pref18_core :
    ∀ (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment (posCoreWires + 18)) (i : Fin posCoreWires),
      xorE0Pref18 m hm γ (Fin.castAdd 18 i) = γ (Fin.castAdd 18 i)
  | 0, _, _, _ => rfl
  | m + 1, hm, γ, i => by
      dsimp only [xorE0Pref18]
      rw [Function.update_of_ne (wire_ne_of_lt (by
        simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)),
          xorE0Pref18_core m (Nat.le_of_succ_le hm) γ i]

theorem xorE0Pref18_anchor :
    ∀ (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment (posCoreWires + 18)) (j : Fin 18),
      xorE0Pref18 m hm γ (Fin.natAdd posCoreWires j) =
        γ (Fin.natAdd posCoreWires j) +
          if j.val < m then γ (Fin.castAdd 18 (rElecSlot (QRegExt.ofFin posCoreWires) 0 j)) else 0
  | 0, _, _, _ => by simp [xorE0Pref18]
  | m + 1, hm, γ, j => by
      dsimp only [xorE0Pref18]
      let jm : Fin 18 := ⟨m, by omega⟩
      by_cases hjm : j = jm
      · rw [hjm, Function.update_self, xorE0Pref18_anchor m (Nat.le_of_succ_le hm) γ jm,
            ite_eq_right (Nat.lt_irrefl m), add_zero, xorE0Pref18_core m (Nat.le_of_succ_le hm) γ _,
            ite_eq_left (Nat.lt_succ_self m)]
      · have hne : Fin.natAdd posCoreWires j ≠ Fin.natAdd posCoreWires jm :=
          fun h ↦ hjm (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))
        rw [Function.update_of_ne hne, xorE0Pref18_anchor m (Nat.le_of_succ_le hm) γ j]
        have hval_ne : j.val ≠ m := fun hv ↦ hjm (Fin.ext hv)
        simp [show (j.val < m + 1) ↔ (j.val < m) by omega]

theorem localPostXorE0_eval_ket :
    ∀ (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment (posCoreWires + 18)),
      (localPostXorE0 m hm).eval.1.mulVec (ket γ) = ket (xorE0Pref18 m hm γ)
  | 0, _, _ => by simp [localPostXorE0, xorE0Pref18]
  | m + 1, hm, γ => by
      dsimp only [localPostXorE0, xorE0Pref18]
      rw [eval_seq_mulVec, localPostXorE0_eval_ket m (Nat.le_of_succ_le hm) γ, ket_CNOT]

theorem xorE0Pref18_writePref18_centeredDiffTblE0
    (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (α : BitAssignment (posCoreWires + 18)) :
    let x := (basisBitsEquiv posCoreWires).symm (fun i ↦ α (Fin.castAdd 18 i))
    xorE0Pref18 18 (le_refl 18)
      (writePref18 (basisBits 18 (centeredDiffTblE0 tbl x)) 18 (le_refl 18) α) =
    writePref18 (basisBits 18 (tbl x)) 18 (le_refl 18) α := by
  intro x
  funext w
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) w
  · rw [xorE0Pref18_core, writePref18_core, writePref18_core]
  · rw[xorE0Pref18_anchor, ite_eq_left j.isLt, writePref18_lt _ 18 (le_refl 18) α j.val j.isLt,
      writePref18_core, writePref18_lt _ 18 (le_refl 18) α j.val j.isLt,
      basisBits_centeredDiffTblE0]
    have hE0 : basisBits posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires) 0 j) =
      α (Fin.castAdd 18 (rElecSlot (QRegExt.ofFin posCoreWires) 0 j)) :=
      basisBits_symm_apply_at (fun i ↦ α (Fin.castAdd 18 i)) _
    rw [hE0, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Complete `18`-qubit `E_0`-centered `X`-basis conjugated load unitary for arbitrary `tbl`. -/
noncomputable def uFullAnchorLoadE0 (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18)) : Unitary (2 ^
    (posCoreWires + 18)) :=
  (localPostHSAndXorE0_18.eval * uDiag18 (centeredDiffTblE0 tbl)) * (localHPrefix 18 (le_refl
    18)).eval

private theorem not_mem_range_concat {n k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (h₁₂ : r₁.DisjointWires r₂)
    {q : Wire n} (hq₁ : q ∉ Set.range r₁.wires) (hq₂ : q ∉ Set.range r₂.wires) :
    q ∉ Set.range (r₁.concat r₂ h₁₂).wires := fun ⟨u, hu⟩ ↦ by
  by_cases hu₁ : u.val < k₁
  · rw [show u = Fin.castAdd k₂ ⟨u.val, hu₁⟩ from Fin.ext rfl, QRegister.concat_apply_left] at hu
    exact hq₁ ⟨_, hu⟩
  · rw [show u = Fin.natAdd k₁ ⟨u.val - k₁, by omega⟩ from Fin.ext (by dsimp; omega),
        QRegister.concat_apply_right] at hu
    exact hq₂ ⟨_, hu⟩

private theorem concat_replaceIndex_symm_eq {n k₁ k₂ : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂
    n) (h₁₂ : r₁.DisjointWires r₂)
    (g h : Fin (2 ^ n)) (α' : BitAssignment (k₁ + k₂)) (hL : ∀ i : Fin k₁, α' (Fin.castAdd k₂ i) =
      basisBits n h (r₁ i))
    (hR : ∀ j : Fin k₂, α' (Fin.natAdd k₁ j) = basisBits n h (r₂ j)) (hOut : ∀ q : Wire n,
      q ∉ Set.range r₁.wires → q ∉ Set.range r₂.wires →
    basisBits n g q = basisBits n h q) : (r₁.concat r₂ h₁₂).replaceIndex g ((basisBitsEquiv (k₁ +
      k₂)).symm α') = h :=
  eq_of_basisBits_eq fun q ↦ by
    by_cases hq₂ : q ∈ Set.range r₂.wires
    · obtain ⟨j, rfl⟩ := hq₂
      conv_lhs =>
        rw [← QRegister.concat_apply_right r₁ r₂ h₁₂ j, QRegister.basisBits_replaceIndex_apply]
      exact (basisBits_symm_apply_at α' _).trans (hR j)
    · by_cases hq₁ : q ∈ Set.range r₁.wires
      · obtain ⟨i, rfl⟩ := hq₁
        conv_lhs =>
          rw [← QRegister.concat_apply_left r₁ r₂ h₁₂ i, QRegister.basisBits_replaceIndex_apply]
        exact (basisBits_symm_apply_at α' _).trans (hL i)
      · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (not_mem_range_concat r₁ r₂ h₁₂ hq₁
          hq₂)]
        exact hOut q hq₁ hq₂

theorem uFullAnchorLoadE0_embed_mulVec_single_of_zero {n : ℕ} (tbl : Fin (2 ^ posCoreWires) →
    Fin (2 ^ 18)) (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (hCA : rCore.DisjointWires rAnchor18) (g : Fin (2 ^ n))
    (hgA0 : rAnchor18.extractIndex g = 0) : ((rCore.concat rAnchor18 hCA).embedUnitary
      (uFullAnchorLoadE0 tbl)).1.mulVec (Pi.single g 1) = Pi.single
    (rAnchor18.replaceIndex g (tbl (rCore.extractIndex g))) 1 := by
  let rAct18 := rCore.concat rAnchor18 hCA
  let w := rAct18.extractIndex g
  let α := basisBits (posCoreWires + 18) w
  have hα_zero : ∀ (k : ℕ) (hk : k < 18), α (Fin.natAdd posCoreWires ⟨k, by omega⟩) = 0 :=
    fun k hk ↦ by
    dsimp only [α, w]
    rw [QRegister.basisBits_extractIndex, QRegister.concat_apply_right]
    exact (QRegExt.extractIndex_eq_zero_iff rAnchor18 g).mp hgA0 ⟨k, hk⟩
  have hxEq : ((basisBitsEquiv posCoreWires).symm fun i ↦ α (Fin.castAdd 18 i)) = rCore.extractIndex
    g :=
    eq_of_basisBits_eq fun i ↦ by
      dsimp only [α, w]
      rw [basisBits_symm_apply_at, QRegister.basisBits_extractIndex, QRegister.concat_apply_left,
        QRegister.basisBits_extractIndex]
  let α' := writePref18 (basisBits 18 (tbl (rCore.extractIndex g))) 18 (le_refl 18) α
  let l : Fin (2 ^ (posCoreWires + 18)) := (basisBitsEquiv (posCoreWires + 18)).symm α'
  have hket_w : (Pi.single w (1 : ℂ) : Fin (2 ^ (posCoreWires + 18)) → ℂ) = ket α :=
    funext fun u ↦ by simp [ket, basisState, α]
  have hket_l : ket α' = (Pi.single l (1 : ℂ) : Fin (2 ^ (posCoreWires + 18)) → ℂ) :=
    funext fun u ↦ by simp [ket, basisState, l]
  have hloc : (uFullAnchorLoadE0 tbl).1.mulVec (Pi.single w 1) = Pi.single l 1 := by
    rw [hket_w]
    dsimp only [uFullAnchorLoadE0, localPostHSAndXorE0_18, uDiag18]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    have hconj := localConj_eval_ket (centeredDiffTblE0 tbl) 18 (le_refl 18) α hα_zero
    dsimp only at hconj
    rw [hconj, localPostXorE0_eval_ket, xorE0Pref18_writePref18_centeredDiffTblE0 tbl α]
    dsimp only [α'] at hket_l ⊢
    rw [hxEq]
    exact hket_l
  change (rAct18.embedMatrix (uFullAnchorLoadE0 tbl).1).mulVec (Pi.single g 1) = _
  rw [rAct18.embedMatrix_mulVec_single_factors, hloc, QRegister.tensorState_single_replaceIndex]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ))
    (concat_replaceIndex_symm_eq rCore rAnchor18 hCA g _ α' (fun i ↦ ?_) (fun j ↦ ?_) (fun q _ hqA ↦
      ?_))
  · dsimp only [α', α, w]
    rw [writePref18_core, QRegister.basisBits_extractIndex, QRegister.concat_apply_left,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ hCA.ne i j hj.symm)]
  · rw [QRegister.basisBits_replaceIndex_apply]
    exact writePref18_lt _ 18 (le_refl 18) α j.val j.isLt
  · exact (QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqA).symm

/-- Parametric leaf phase function for `dAnchorDiagLoadGen` on `(posCoreWires + mClean, 18)`. -/
noncomputable def ΦLeafAnchorGen (mClean uOff : ℕ) (huOff : uOff + 218 ≤ mClean) (γ : BitAssignment
    (posCoreWires + mClean)) (ζ : BitAssignment 18) : ℂ :=
  (∏ i : Fin 217, ∏ j : Fin 18,
    oneHotBitPhase (ζ j)
      (γ ⟨posCoreWires + uOff + (i.val + 1), by omega⟩)
      (γ (rElecSlot (rCoreInGen (Nat.le_add_right posCoreWires mClean)) ⟨i.val + 1, by omega⟩ j))) *
  (∏ j : Fin 18,
    oneHotBoundaryPhase (ζ j)
      (γ ⟨posCoreWires + uOff + 0, by omega⟩))

theorem disj_of_concat_left {n k₁ k₂ m : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {rW : QRegister m n} {h₁₂ : r₁.DisjointWires r₂} (h : (r₁.concat r₂ h₁₂).DisjointWires rW) :
      r₁.DisjointWires rW := QRegister.disjoint_iff.mpr fun i k heq ↦
  h.ne (Fin.castAdd k₂ i) k ((QRegister.concat_apply_left r₁ r₂ h₁₂ i).trans heq)

theorem disj_of_concat_right {n k₁ k₂ m : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {rW : QRegister m n} {h₁₂ : r₁.DisjointWires r₂} (h : (r₁.concat r₂ h₁₂).DisjointWires rW) :
      r₂.DisjointWires rW := QRegister.disjoint_iff.mpr fun j k heq ↦
  h.ne (Fin.natAdd k₁ j) k ((QRegister.concat_apply_right r₁ r₂ h₁₂ j).trans heq)

/-- Parametric diagonal phase-mux core for `dAnchorLoadGen`. -/
noncomputable def dAnchorDiagLoadGenRaw {Var : Type} {n : ℕ} (mClean uOff : ℕ) (huOff : uOff +
    218 ≤ mClean) (KU : TempCtx (posCoreWires + mClean)) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mClean n)
      (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork) : DynamicCircuit Var n :=
  let hM : posCoreWires ≤ posCoreWires + mClean := Nat.le_add_right posCoreWires mClean
  let hCW := disj_of_concat_left hActW
  let hAW := disj_of_concat_right hActW
  let rSub : QRegister 218 n := rWork.slice uOff 218 huOff
  let hAS : rAnchor18.DisjointWires rSub := hAW.compose_right _
  let rComb : QRegister (posCoreWires + mClean) n := rCore.concat rWork hCW
  let leaf := leafDiag217Circuit rCore rAnchor18 rSub hCA hAS
  let KLoad := (ctxCliffAlloc (cXorE0217Locked hM)).append KU
  toDynWithCircuit v rComb leaf KLoad

theorem dAnchorDiagLoadGenRaw_toff {Var : Type} {n : ℕ} (mClean uOff : ℕ) (huOff : uOff +
    218 ≤ mClean) (KU : TempCtx (posCoreWires + mClean)) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mClean n)
      (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork) : (dAnchorDiagLoadGenRaw mClean
    uOff huOff KU v rCore rAnchor18 rWork hCA hActW).count PrimitiveGate.TOFF = 0 :=
    toDynWithDyn_count_toff v _ (.circuit _)
    (leafDiag217Circuit_count_toff rCore rAnchor18 _ hCA _) _

theorem dAnchorDiagLoadGenRaw_t {Var : Type} {n : ℕ} (mClean uOff nAnd : ℕ) (huOff : uOff +
    218 ≤ mClean)
    (KU : TempCtx (posCoreWires + mClean)) (hCnt : KU.countTempAnd = nAnd) (v : Var) (rCore :
      QRegister posCoreWires n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mClean n) (hCA : rCore.DisjointWires rAnchor18) (hActW : (rCore.concat
      rAnchor18 hCA).DisjointWires rWork) :
    (dAnchorDiagLoadGenRaw mClean uOff huOff KU v rCore rAnchor18 rWork hCA hActW).count
      PrimitiveGate.T = 4 * nAnd + 7848 := by
  dsimp only [dAnchorDiagLoadGenRaw, toDynWithCircuit]
  rw [toDynWithDyn_count_t, DynamicCircuit.count, leafDiag217Circuit_count_t,
    TempCtx.append_countTempAnd, hCnt]
  dsimp only [ctxCliffAlloc, TempCtx.countTempAnd]
  rw [zero_add]

theorem dAnchorDiagLoadGenRaw_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero
    (2 ^ n)]
    (mClean uOff : ℕ) (huOff : uOff + 218 ≤ mClean) (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256,
      idxFn val < 218) (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (htbl : ∀ (x : Fin (2 ^ posCoreWires)) (j : Fin 18), basisBits 18 (tbl x) j =
      basisBits posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires)
    ⟨idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x)),
    hIdxLt _ (regVal_rAnchorIdx_lt256 (QRegExt.ofFin posCoreWires) (basisBits posCoreWires x))⟩ j))
    (KU : TempCtx (posCoreWires + mClean)) (hRestU : RestoresAll KU) (hSpecU : (∀ q : Wire
      (posCoreWires + mClean),
    ScopedBlock (posCoreWires + mClean) ((posCoreWires + mClean) - posCoreWires) KU.fwdBits (.z q)
      (KU.plug (.z q))) ∧
    ∀ γ : BitAssignment (posCoreWires + mClean), cleanRem (posCoreWires + mClean) ((posCoreWires +
      mClean) - posCoreWires) γ →
    cleanRem (posCoreWires + mClean) ((posCoreWires + mClean) - (posCoreWires + uOff +
      218)) (KU.fwdBits γ) ∧
    (∀ w : Wire (posCoreWires + mClean), w.val < posCoreWires → KU.fwdBits γ w = γ w) ∧
    (∀ (u : ℕ) (_ : u < 218), KU.fwdBits γ ⟨posCoreWires + uOff + u, by omega⟩ =
    if u = idxFn (regVal (rAnchorIdx (rCoreInGen (Nat.le_add_right posCoreWires mClean))) γ) then 1
      else 0))
    (v : Var) (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork : QRegister
      mClean n) (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rCore.concat rAnchor18 hCA) rWork (uDiag18 (centeredDiffTblE0 tbl)) (dAnchorDiagLoadGenRaw
      mClean uOff huOff KU v rCore rAnchor18 rWork hCA hActW) := by
  let M := posCoreWires + mClean
  let hM : posCoreWires ≤ M := Nat.le_add_right posCoreWires mClean
  let rCoreM := rCoreInGen hM
  dsimp only [dAnchorDiagLoadGenRaw]
  let hCW := disj_of_concat_left hActW
  let hAW := disj_of_concat_right hActW
  let rSub : QRegister 218 n := rWork.slice uOff 218 huOff
  let rComb : QRegister M n := rCore.concat rWork hCW
  have hCombA : rComb.DisjointWires rAnchor18 :=
    disj_concat_left hCW hCA (QRegister.disjoint_iff.mpr fun i j heq ↦ (hAW.ne j i) heq.symm)
  let leaf := leafDiag217Circuit rCore rAnchor18 rSub hCA (hAW.compose_right _)
  let cPre := cXorE0217Locked hM
  let KLoad := (ctxCliffAlloc cPre).append KU
  obtain ⟨hProbesU, hFwdSpecU⟩ := hSpecU
  let q₀ : Wire M := ⟨0, by dsimp [M]; omega⟩
  have hValidK : ValidCleanRem M mClean (KLoad.plug (.z q₀)) := by
    dsimp only [KLoad]
    rw [TempCtx.append_plug, ctxCliffAlloc_plug]
    exact (ScopedBlock.withCliffAlloc_block (Nat.le_add_left mClean posCoreWires) le_rfl cPre
      (by simpa [M] using cXorE0217Locked_supports hM) ((hProbesU q₀).cast_rem (by omega))).valid
  have hLeafKet (β : BitAssignment n) : leaf.eval.1.mulVec (ket β) =
      ΦLeafAnchorGen mClean uOff huOff (fun idx ↦ β (rComb idx)) (fun j ↦ β (rAnchor18 j)) •
        ket β := by
    rw [leafDiag217Circuit_eval_ket rCore rAnchor18 rSub hCA _ β]
    refine congrArg (· • ket β) (congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun j _ ↦ ?_)
      (Finset.prod_congr rfl fun j _ ↦ congrArg (oneHotBoundaryPhase _)
        (congrArg β (concat_slice_unary_apply huOff rCore rWork hCW 0 (by decide)).symm)))
    dsimp only [rComb, rCoreM]
    rw [congrArg β (concat_slice_unary_apply huOff rCore rWork hCW (i.val + 1) (by omega)).symm,
        rElecSlot_apply_ofFin rCore, rElecSlot_apply_ofFin (rCoreInGen hM), concat_rCoreInGen_apply]
  obtain ⟨U_clean, hSmall, hKetClean⟩ := realizes_toDynWithDyn_diagComplex v rComb rAnchor18
      hCombA 0 (Nat.zero_le _) (.z q₀) (fun _ _ ↦ Nat.zero_le _) (fun _ ↦ rfl) (.circuit leaf)
      leaf.eval (RealizesCleanUnitary.circuit v _ leaf) (ΦLeafAnchorGen mClean uOff huOff)
      hLeafKet KLoad mClean (Nat.le_add_left mClean posCoreWires) hValidK
  let rAct18 := rCore.concat rAnchor18 hCA
  refine realizesEmbedded_of_toDynWithCircuit v rAct18 rCore rWork hCW leaf KLoad U_clean _
    hSmall (matrix_ext_ket fun β ↦ ?_)
  simp only [mul_mulVec_prog, ket_projZeroAll]
  by_cases hw : ∀ i : Fin mClean, β (rWork i) = 0
  · simp only [hw, imp_true_iff, ↓reduceIte, hKetClean]
    let α : BitAssignment posCoreWires := fun i ↦ β (rCore i)
    let ζ : BitAssignment 18 := fun j ↦ β (rAnchor18 j)
    obtain ⟨hpad, hcleanPad, hwId, hCorePadRaw⟩ := rComb_padZeroBits_facts rCore rWork hCW β hw
    rw [(RestoresAll.append (RestoresAll.cliffAlloc _) hRestU) (.z q₀) (fun _ ↦ rfl) _, hwId, hpad]
    let pad := padZeroBits (mClean := mClean) α
    let γPre := cPre.eval pad
    let γL := KLoad.fwdBits pad
    have hγL_eq : γL = KU.fwdBits γPre := TempCtx.append_fwdBits (ctxCliffAlloc cPre) KU pad
    obtain ⟨hOtherPre, hSlotPre⟩ := cXorE0217Locked_eval hM pad
    have hCleanPre : cleanRem M (M - posCoreWires) γPre := fun w hw' ↦
      (hOtherPre w fun k _ j' h ↦ Nat.ne_of_gt (lt_of_lt_of_le (rElecSlot_inGen_lt hM ⟨k + 1,
        by omega⟩ j') (show posCoreWires ≤ w.val by omega))
        (congrArg Fin.val h)).trans (hcleanPad w (show M - mClean ≤ w.val by omega))
    obtain ⟨_, hCoreLt, hUnary⟩ := hFwdSpecU γPre hCleanPre
    let x := (basisBitsEquiv posCoreWires).symm α
    have hxBits : basisBits posCoreWires x = α := basisBits_symm_apply α
    have hAncEq : regVal (rAnchorIdx rCoreM) γPre = regVal (rAnchorIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires x) := by
      rw [hxBits]
      refine regVal_congr_cross _ _ _ _ fun d ↦ ?_
      dsimp only [γPre]
      rw [hOtherPre _ (fun k _ j' h ↦ Nat.ne_of_gt (lt_of_lt_of_le (rElecSlot_inGen_lt3924 hM ⟨k +
        1, by omega⟩ j')
            (le_trans (by decide : 3924 ≤ 3968) (rAnchorIdx_inGen_ge3968 hM d))) (congrArg Fin.val
              h)), rAnchorIdx_apply_ofFin rCoreM]
      exact hCorePadRaw _
    have hSlotL (i : Fin 217) (j : Fin 18) : γL (rElecSlot rCoreM ⟨i.val + 1, by omega⟩ j) =
        basisBits posCoreWires x (rElecSlot (QRegExt.ofFin _) ⟨i.val + 1, by omega⟩ j) +
          basisBits posCoreWires x (rElecSlot (QRegExt.ofFin _) 0 j) := by
      rw [hγL_eq, hCoreLt _ (rElecSlot_inGen_lt hM _ _)]
      dsimp only [γPre]
      rw [hSlotPre i.val i.isLt j, ite_eq_left i.isLt, rElecSlot_apply_ofFin rCoreM,
          rElecSlot_apply_ofFin rCoreM]
      dsimp only [pad]
      rw [hCorePadRaw, hCorePadRaw, hxBits]
    have hUnaryL (u : ℕ) (hu : u < 218) :
        γL ⟨posCoreWires + uOff + u, by dsimp [M]; omega⟩ =
          if u = idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires))
            (basisBits posCoreWires x)) then 1 else 0 := by rw [hγL_eq, hUnary u hu, hAncEq]
    have hΦVal : ΦLeafAnchorGen mClean uOff huOff γL ζ =
        ∏ j : Fin 18, targetDiagScalar (ζ j) (basisBits 18 (centeredDiffTblE0 tbl x) j) := by
      dsimp only [ΦLeafAnchorGen]
      rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      let u₀ := idxFn (regVal (rAnchorIdx (QRegExt.ofFin _)) (basisBits posCoreWires x))
      have hu₀_lt : u₀ < 218 := hIdxLt _ (regVal_rAnchorIdx_lt256 _ (basisBits posCoreWires x))
      by_cases hu0 : u₀ = 0
      · rw [Finset.prod_eq_one fun i _ ↦ by
              rw [hUnaryL (i.val + 1) (by omega), ite_eq_right (by omega), oneHotBitPhase_zero_u],
            one_mul, hUnaryL 0 (by decide), ite_eq_left hu0.symm, oneHotBoundaryPhase_one,
            show basisBits 18 (centeredDiffTblE0 tbl x) j = 0 by
              rw [basisBits_centeredDiffTblE0, htbl x j,
                  show (⟨u₀, hu₀_lt⟩ : Fin 218) = 0 from Fin.ext hu0, CharTwo.add_self_eq_zero]]
        simp [targetDiagScalar]
      · let i₀ : Fin 217 := ⟨u₀ - 1, by omega⟩
        rw [Finset.prod_eq_single i₀]
        · rw [hUnaryL (i₀.val + 1) (by omega), ite_eq_left (by dsimp [i₀]; omega),
              hUnaryL 0 (by decide), ite_eq_right (Ne.symm hu0),
              oneHotBitPhase_one_mul_boundary_zero, hSlotL i₀ j,
              basisBits_centeredDiffTblE0, htbl x j,
              show (⟨i₀.val + 1, _⟩ : Fin 218) = ⟨u₀, hu₀_lt⟩ from Fin.ext (by dsimp [i₀]; omega)]
        · intro i _ hne
          rw [hUnaryL (i.val + 1) (by omega),
              ite_eq_right (fun hv ↦ hne (Fin.ext (by dsimp [i₀]; omega))), oneHotBitPhase_zero_u]
        · exact fun habs ↦ absurd (Finset.mem_univ i₀) habs
    change ΦLeafAnchorGen mClean uOff huOff γL ζ • ket β = _
    let g := (basisBitsEquiv n).symm β
    have hket : (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) = ket β :=
      funext fun u ↦ by simp [g, ket, basisState]
    rw [hΦVal, ← hket, uDiag18, diagComplexUnitaryN,
        embedUnitary_diagComplexUnitary_mulVec_single, hket]
    refine congrArg (· • ket β) ?_
    dsimp only [ΦDiagM]
    rw [show ((basisBitsEquiv posCoreWires).symm fun i ↦
          basisBits (posCoreWires + 18) (rAct18.extractIndex g) (Fin.castAdd 18 i)) = x from
        eq_of_basisBits_eq fun i ↦ by
          rw [basisBits_symm_apply_at, QRegister.basisBits_extractIndex,
              QRegister.concat_apply_left, hxBits, basisBits_symm_apply_at]]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [show (⟨j.val, by omega⟩ : Fin 18) = j from Fin.ext rfl,
        QRegister.basisBits_extractIndex, QRegister.concat_apply_right, basisBits_symm_apply_at]
  · simp [hw]

/-- Parametric `E_0`-centered `217 × 18` `2-T` one-hot phase-difference load circuit. -/
noncomputable def dAnchorLoadGenRaw {Var : Type} {n : ℕ} (mClean uOff : ℕ) (huOff : uOff +
    218 ≤ mClean) (KU : TempCtx (posCoreWires + mClean)) (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mClean n)
      (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork) : DynamicCircuit Var n :=
  let rAct18 := rCore.concat rAnchor18 hCA
  DynamicCircuit.seq
    (.circuit (embedCircuit123 rAct18 (localHPrefix 18 (le_refl 18))))
    (DynamicCircuit.seq
      (dAnchorDiagLoadGenRaw mClean uOff huOff KU v rCore rAnchor18 rWork hCA hActW)
      (.circuit (embedCircuit123 rAct18 localPostHSAndXorE0_18)))

private theorem dAnchorLoadGenRaw_spec_of_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (uOff nAnd : ℕ) (huOff : uOff + 218 ≤ mClean) (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (KU : TempCtx (posCoreWires + mClean)) (hCnt : KU.countTempAnd = nAnd)
    (v : Var) (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n)
    (rWork : QRegister mClean n) (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork)
    (hDiag : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rAnchor18 hCA) rWork (uDiag18 (centeredDiffTblE0 tbl))
      (dAnchorDiagLoadGenRaw mClean uOff huOff KU v rCore rAnchor18 rWork hCA hActW)) :
    let dyn := dAnchorLoadGenRaw mClean uOff huOff KU v rCore rAnchor18 rWork hCA hActW
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        (rCore.concat rAnchor18 hCA) rWork (uFullAnchorLoadE0 tbl) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 4 * nAnd + 7848 := by
  let rAct18 := rCore.concat rAnchor18 hCA
  have hPreH := DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var) rAct18
    rWork
    (localHPrefix 18 (le_refl 18)).eval (embedCircuit123 rAct18 (localHPrefix 18 (le_refl 18)))
    (embedCircuit123_eval rAct18 _)
  have hPost := DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var) rAct18
    rWork
    localPostHSAndXorE0_18.eval (embedCircuit123 rAct18 localPostHSAndXorE0_18)
    (embedCircuit123_eval rAct18 _)
  refine ⟨hPreH.seq hActW (hDiag.seq hActW hPost), ?_, ?_⟩
  · dsimp only [dAnchorLoadGenRaw, DynamicCircuit.count]
    rw [embedCircuit123_count, localHPrefix_count_toff, zero_add, embedCircuit123_count,
      localPostHSAndXorE0_18_count_toff, add_zero]
    exact dAnchorDiagLoadGenRaw_toff _ _ _ _ v rCore rAnchor18 rWork hCA hActW
  · dsimp only [dAnchorLoadGenRaw, DynamicCircuit.count]
    rw [embedCircuit123_count, localHPrefix_count_t, zero_add, embedCircuit123_count,
      localPostHSAndXorE0_18_count_t, add_zero]
    exact dAnchorDiagLoadGenRaw_t mClean uOff nAnd huOff KU hCnt v rCore rAnchor18 rWork hCA hActW

/-- Unclamped `8,688-T` (`0 .TOFF`, `218` clean scratch wires) `AnchorMux218` load realizing
`uFullAnchorLoadE0 anchorTblVal218Unclamped`. -/
noncomputable def dAnchorLoad218Unclamped {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork218 : QRegister 218 n)
      (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork218) : DynamicCircuit Var n :=
  lockVal3P (dAnchorLoadGenRaw 218 0 (by decide) (ctxAnchorUnary218Unclamped
    rCoreInAnchorUnclamped posCoreWires le_rfl (fun i ↦ i.isLt)) v rCore rAnchor18 rWork218 hCA
      hActW)

theorem dAnchorLoad218Unclamped_eq {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (rWork218 : QRegister 218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hActW : (rCore.concat rAnchor18 hCA).DisjointWires
      rWork218) : dAnchorLoad218Unclamped v
    rCore rAnchor18 rWork218 hCA hActW = dAnchorLoadGenRaw 218 0 (by decide)
    (ctxAnchorUnary218Unclamped rCoreInAnchorUnclamped posCoreWires le_rfl (fun i ↦ i.isLt)) v rCore
      rAnchor18 rWork218 hCA hActW := lockVal3P_eq _

theorem dAnchorLoad218Unclamped_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2
    ^ n)]
    (v : Var) (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork218 : QRegister
      218 n)
    (hCA : rCore.DisjointWires rAnchor18) (hActW : (rCore.concat rAnchor18 hCA).DisjointWires
      rWork218) :
    let dyn := dAnchorLoad218Unclamped v rCore rAnchor18 rWork218 hCA hActW
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        (rCore.concat rAnchor18 hCA) rWork218 (uFullAnchorLoadE0 anchorTblVal218Unclamped) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 8688 := by
  dsimp only
  rw [dAnchorLoad218Unclamped_eq]
  obtain ⟨hP, hS⟩ := ScopedBlock.ctxAnchorUnary218Unclamped_fwdBits_spec
    rCoreInAnchorUnclamped posCoreWires le_rfl (fun i ↦ i.isLt)
  exact dAnchorLoadGenRaw_spec_of_diag 0 210 (by decide) anchorTblVal218Unclamped _
    (ctxAnchorUnary218Unclamped_countTempAnd _ _ _ _) v rCore rAnchor18 rWork218 hCA hActW
    (dAnchorDiagLoadGenRaw_realizes 218 0 (by decide) aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv)
      anchorTblVal218Unclamped basisBits_anchorTblVal218Unclamped _
      (RestoresAll.anchorUnary218Unclamped _ _ _ _)
      ⟨hP, fun γ hγ ↦ by
        obtain ⟨h1, h2, h3⟩ := hS γ hγ
        exact ⟨h1, h2, fun u hu ↦ by simpa only [Nat.add_zero] using h3 u hu⟩⟩
      v rCore rAnchor18 rWork218 hCA hActW)

/-- `< 218`-Clamped `8,724-T` (`0 .TOFF`, `224` clean scratch wires) `AnchorMux218` load realizing
`uFullAnchorLoadE0 anchorTblVal218`. -/
noncomputable def dAnchorLoad218 {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (rWork224 : QRegister 224 n)
    (hCA : rCore.DisjointWires rAnchor18) (hActW : (rCore.concat rAnchor18 hCA).DisjointWires
      rWork224) : DynamicCircuit Var n :=
  lockVal3P (dAnchorLoadGenRaw 224 6 hSlice6_218 (ctxAnchorUnary218 rCoreInAnchorClamped
    posCoreWires le_rfl (fun i ↦ i.isLt)) v rCore rAnchor18 rWork224 hCA hActW)

theorem dAnchorLoad218_eq {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister posCoreWires n)
    (rAnchor18 : QRegister 18 n) (rWork224 : QRegister 224 n) (hCA : rCore.DisjointWires rAnchor18)
    (hActW : (rCore.concat rAnchor18 hCA).DisjointWires rWork224) : dAnchorLoad218 v rCore
    rAnchor18 rWork224 hCA hActW = dAnchorLoadGenRaw 224 6 hSlice6_218 (ctxAnchorUnary218
    rCoreInAnchorClamped posCoreWires le_rfl (fun i ↦ i.isLt)) v rCore rAnchor18 rWork224 hCA
      hActW := lockVal3P_eq _

theorem dAnchorLoad218_spec {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister posCoreWires n) (rAnchor18 : QRegister 18 n) (rWork224 : QRegister
      224 n)
    (hCA : rCore.DisjointWires rAnchor18) (hActW : (rCore.concat rAnchor18 hCA).DisjointWires
      rWork224) :
    let dyn := dAnchorLoad218 v rCore rAnchor18 rWork224 hCA hActW
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        (rCore.concat rAnchor18 hCA) rWork224 (uFullAnchorLoadE0 anchorTblVal218) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 8724 := by
  dsimp only
  rw [dAnchorLoad218_eq]
  exact dAnchorLoadGenRaw_spec_of_diag 6 219 hSlice6_218 anchorTblVal218 _
    (ctxAnchorUnary218_countTempAnd _ _ _ _) v rCore rAnchor18 rWork224 hCA hActW
    (dAnchorDiagLoadGenRaw_realizes 224 6 hSlice6_218 clampIdx218 (fun val _ ↦ clampIdx218_lt val)
      anchorTblVal218 basisBits_anchorTblVal218 _ (RestoresAll.anchorUnary218 _ _ _ _)
      (ScopedBlock.ctxAnchorUnary218_fwdBits_spec rCoreInAnchorClamped posCoreWires le_rfl (fun i ↦
        i.isLt))
      v rCore rAnchor18 rWork224 hCA hActW)

attribute [local irreducible] uFullAnchorLoadE0 dAnchorLoad218Unclamped dAnchorLoad218

/-- Local `54`-CNOT (`0 T`, `0 .TOFF`) prefix circuit swapping wires `[0 .. m)` with `[18 .. 18 +
m)`. -/
def cSwap18LocalAux : (m : ℕ) → (hm : m ≤ 18) → Circuit 36
  | 0, _ => .identity
  | m + 1, hm =>
      cSwap18LocalAux m (Nat.le_of_succ_le hm) ;;ᶜ
      PosPostPrep80MergedVep.cSwap2 ⟨m, by omega⟩ ⟨18 + m, by omega⟩ (wire_ne_of_lt (by
        dsimp; omega))

def cSwap18Local : Circuit 36 := cSwap18LocalAux 18 (le_refl 18)

theorem cSwap18LocalAux_count_toff :
    ∀ (m : ℕ) (hm : m ≤ 18), (cSwap18LocalAux m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cSwap18LocalAux, PosPostPrep80MergedVep.cSwap2, Circuit.count]
      rw [cSwap18LocalAux_count_toff m (Nat.le_of_succ_le hm)]
      rfl

theorem cSwap18LocalAux_count_t :
    ∀ (m : ℕ) (hm : m ≤ 18), (cSwap18LocalAux m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cSwap18LocalAux, PosPostPrep80MergedVep.cSwap2, Circuit.count]
      rw [cSwap18LocalAux_count_t m (Nat.le_of_succ_le hm)]
      rfl

def swap18Pref (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment 36) : BitAssignment 36 :=
  fun w ↦
    if hw1 : w.val < m then γ ⟨18 + w.val, by omega⟩
    else if hw2 : 18 ≤ w.val ∧ w.val < 18 + m then γ ⟨w.val - 18, by omega⟩
    else γ w

theorem cSwap2_eval_ket {n : ℕ} (a b : Wire n) (hne : a ≠ b) (δ : BitAssignment n) :
    (PosPostPrep80MergedVep.cSwap2 a b hne).eval.1.mulVec (ket δ) =
    ket (fun q ↦ δ (Equiv.swap a b q)) := by
  unfold PosPostPrep80MergedVep.cSwap2
  rw [eval_seq_mulVec, ket_CNOT, eval_seq_mulVec, ket_CNOT, ket_CNOT]
  congr 1; funext q
  by_cases h1 : q = a
  · subst h1; simp [hne, hne.symm, PosPostPrep80MergedVep.zmod2_swap_a]
  · by_cases h2 : q = b
    · subst h2; simp [hne, hne.symm, PosPostPrep80MergedVep.zmod2_swap_b]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem cSwap18LocalAux_eval_ket :
    ∀ (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment 36),
      (cSwap18LocalAux m hm).eval.1.mulVec (ket γ) = ket (swap18Pref m hm γ)
  | 0, hm, γ => by
      rw [show swap18Pref 0 hm γ = γ from funext fun w ↦ by
        dsimp only [swap18Pref]
        rw [dite_eq_right (Nat.not_lt_zero _), dite_eq_right (by omega)]]
      simp [cSwap18LocalAux]
  | m + 1, hm, γ => by
      dsimp only [cSwap18LocalAux]
      rw [eval_seq_mulVec, cSwap18LocalAux_eval_ket m (Nat.le_of_succ_le hm) γ, cSwap2_eval_ket]
      congr 1
      funext w
      let a : Wire 36 := ⟨m, by omega⟩
      let b : Wire 36 := ⟨18 + m, by omega⟩
      change swap18Pref m (Nat.le_of_succ_le hm) γ (Equiv.swap a b w) = swap18Pref (m + 1) hm γ w
      by_cases hwa : w = a
      · subst hwa
        rw [Equiv.swap_apply_left]
        dsimp [swap18Pref, a, b]
        rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (Nat.lt_succ_self m)]
      · by_cases hwb : w = b
        · subst hwb
          rw [Equiv.swap_apply_right]
          dsimp [swap18Pref, a, b]
          rw [dite_eq_right (Nat.lt_irrefl m), dite_eq_right (by omega), dite_eq_right (by omega),
              dite_eq_left ⟨by omega, by omega⟩]
          exact congrArg γ (Fin.ext (by dsimp; omega))
        · rw [Equiv.swap_apply_of_ne_of_ne hwa hwb]
          have : w.val ≠ m ∧ w.val ≠ 18 + m := ⟨fun v ↦ hwa (Fin.ext v), fun v ↦ hwb (Fin.ext v)⟩
          dsimp [swap18Pref]
          by_cases h1 : w.val < m
          · rw [dite_eq_left h1, dite_eq_left (show w.val < m + 1 by omega)]
          · rw [dite_eq_right h1, dite_eq_right (show ¬ w.val < m + 1 by omega)]
            by_cases h2 : 18 ≤ w.val ∧ w.val < 18 + m
            · rw [dite_eq_left h2, dite_eq_left ⟨h2.1, by omega⟩]
            · rw [dite_eq_right h2, dite_eq_right (by omega)]

/-- `54`-CNOT (`0 T`, `0 .TOFF`) register swap between disjoint `18`-wire registers `rA` and
`rB`. -/
def cSwap18 {n : ℕ} (rA rB : QRegister 18 n) (hAB : rA.DisjointWires rB) : Circuit n :=
  embedCircuit123 (rA.concat rB hAB) cSwap18Local

@[simp]
theorem cSwap18_count_toff {n : ℕ} (rA rB : QRegister 18 n) (hAB : rA.DisjointWires rB) : (cSwap18
    rA rB hAB).count PrimitiveGate.TOFF = 0 := by
  dsimp [cSwap18, cSwap18Local]
  rw [embedCircuit123_count]
  exact cSwap18LocalAux_count_toff 18 (le_refl 18)

@[simp] theorem cSwap18_count_t {n : ℕ} (rA rB : QRegister 18 n) (hAB : rA.DisjointWires rB) :
    (cSwap18 rA rB hAB).count PrimitiveGate.T = 0 := by
  dsimp [cSwap18, cSwap18Local]
  rw [embedCircuit123_count]
  exact cSwap18LocalAux_count_t 18 (le_refl 18)

theorem cSwap18_eval_mulVec_single {n : ℕ} (rA rB : QRegister 18 n) (hAB : rA.DisjointWires rB) (g :
    Fin (2 ^ n)) :
    (cSwap18 rA rB hAB).eval.1.mulVec (Pi.single g 1) = Pi.single (rB.replaceIndex (rA.replaceIndex
      g (rB.extractIndex g)) (rA.extractIndex g)) 1 := by
  let rAB := rA.concat rB hAB
  let w : Fin (2 ^ 36) := rAB.extractIndex g
  let γ := basisBits 36 w
  let γ' := swap18Pref 18 (le_refl 18) γ
  let l : Fin (2 ^ 36) := (basisBitsEquiv 36).symm γ'
  have hloc : cSwap18Local.eval.1.mulVec (Pi.single w 1) = Pi.single l 1 := by
    rw [show (Pi.single w (1 : ℂ) : Fin (2 ^ 36) → ℂ) = ket γ by
          rw [PosPostPrep80MergedVep.ket_eq_single_local, (basisBitsEquiv 36).symm_apply_apply],
        cSwap18Local, cSwap18LocalAux_eval_ket, PosPostPrep80MergedVep.ket_eq_single_local γ']
  dsimp only [cSwap18]
  rw [embedCircuit123_eval, QRegister.embedUnitary_val, rAB.embedMatrix_mulVec_single_factors, hloc,
    QRegister.tensorState_single_replaceIndex]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ))
    (concat_replaceIndex_symm_eq rA rB hAB g _ γ' (fun i ↦ ?_) (fun j ↦ ?_) (fun q hqA hqB ↦ ?_))
  · dsimp only [γ', swap18Pref, γ, w]
    rw [dite_eq_left (by dsimp; exact i.isLt),
        show (⟨18 + (Fin.castAdd 18 i).val, by dsimp; omega⟩ : Wire 36) = Fin.natAdd 18 i from
          Fin.ext rfl,
        QRegister.basisBits_extractIndex, QRegister.concat_apply_right,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ hAB.ne i j hj.symm),
        QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
  · dsimp only [γ', swap18Pref, γ, w]
    rw [dite_eq_right (by dsimp; omega), dite_eq_left ⟨by dsimp; omega, by dsimp; omega⟩,
        show (⟨(Fin.natAdd 18 j).val - 18, by dsimp; omega⟩ : Wire 36) = Fin.castAdd 18 j from
          Fin.ext (by dsimp; omega),
        QRegister.basisBits_extractIndex, QRegister.concat_apply_left,
        QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqB,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqA]

attribute [local irreducible] cSwap18Local

/-- Electron slot `e` (`18` wires) inside `rData` (`kData` wires) via `selMux : QRegister
posCoreWires kData`. -/
def rDataElec {kData : ℕ} (selMux : QRegister posCoreWires kData) (e : Fin 218) : QRegister 18
    kData :=
  selMux.compose (rElecSlot (QRegExt.ofFin posCoreWires) e)

/-- `8`-wire anchor index inside `rData` (`kData` wires) via `selMux : QRegister posCoreWires
kData`. -/
def rDataAnchor {kData : ℕ} (selMux : QRegister posCoreWires kData) : QRegister 8 kData :=
  selMux.compose (rAnchorIdx (QRegExt.ofFin posCoreWires))

theorem rDataElec_disjoint {kData : ℕ} (selMux : QRegister posCoreWires kData) {e₁ e₂ : Fin 218}
    (hne : e₁ ≠ e₂) :
    (rDataElec selMux e₁).DisjointWires (rDataElec selMux e₂) := by
  rw [QRegister.disjoint_iff]
  intro j₁ j₂ heq
  have hinj := selMux.wires.injective heq
  have hv := congrArg Fin.val hinj
  change 18 * e₁.val + j₁.val = 18 * e₂.val + j₂.val at hv
  have := j₁.isLt; have := j₂.isLt
  exact hne (Fin.ext (by omega))

theorem rDataElec_disjoint_anchor {kData : ℕ} (selMux : QRegister posCoreWires kData) (e : Fin
    218) :
    (rDataElec selMux e).DisjointWires (rDataAnchor selMux) := by
  rw [QRegister.disjoint_iff]
  intro j d heq
  have hinj := selMux.wires.injective heq
  have hv := congrArg Fin.val hinj
  have h1 : (rElecSlot (QRegExt.ofFin posCoreWires) e j).val = 18 * e.val + j.val := rfl
  have h2 : (rAnchorIdx (QRegExt.ofFin posCoreWires) d).val = 3968 + d.val := rAnchorIdx_ofFin_val d
  rw [h1, h2] at hv
  have := e.isLt; have := j.isLt; omega

/-- Active electron slot `u₀ ∈ Fin 218` of data basis index `x : Fin (2 ^ kData)`. -/
def dataActiveSlot {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) (x : Fin (2 ^ kData)) : Fin 218 :=
  ⟨idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires
    (selMux.extractIndex x))),
    hIdxLt _ (regVal_rAnchorIdx_lt256 _ _)⟩

theorem dataActiveSlot_eq_of_anchor_eq {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) {x y : Fin (2 ^ kData)} (hAnc :
    (rDataAnchor selMux).extractIndex x = (rDataAnchor selMux).extractIndex y) :
    dataActiveSlot selMux idxFn hIdxLt x = dataActiveSlot selMux idxFn hIdxLt y := by
  apply Fin.ext; dsimp only [dataActiveSlot]
  refine congrArg idxFn (regVal_congr_cross _ _ _ _ fun d ↦ ?_)
  rw [← QRegister.basisBits_extractIndex, ← QRegister.extractIndex_compose,
      ← QRegister.basisBits_extractIndex (rAnchorIdx _) (selMux.extractIndex y),
      ← QRegister.extractIndex_compose]
  exact congrFun (congrArg (basisBits 8) hAnc) d

theorem rDataAnchor_extract_replace_elec {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (e : Fin 218) (x : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) : (rDataAnchor selMux).extractIndex
    ((rDataElec selMux e).replaceIndex x v) = (rDataAnchor selMux).extractIndex x :=
    QRegister.extractIndex_replaceIndex_of_disjoint (rDataAnchor selMux) (rDataElec selMux e)
    (rDataElec_disjoint_anchor selMux e).symm x v

/-- Involutive basis-index swap between `rDataElec selMux 0` and `rDataElec selMux (dataActiveSlot
x)`. -/
noncomputable def swap0DataIdx {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) (x : Fin (2 ^ kData)) : Fin (2 ^
      kData) :=
  let u := dataActiveSlot selMux idxFn hIdxLt x
  if u = 0 then x
  else
    (rDataElec selMux u).replaceIndex
      ((rDataElec selMux 0).replaceIndex x ((rDataElec selMux u).extractIndex x))
      ((rDataElec selMux 0).extractIndex x)

theorem swap0DataIdx_anchor_eq {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) (x : Fin (2 ^ kData)) : (rDataAnchor
      selMux).extractIndex (swap0DataIdx selMux idxFn hIdxLt x) =
    (rDataAnchor selMux).extractIndex x := by
  dsimp only [swap0DataIdx]
  split_ifs with hu0
  · rfl
  · rw [rDataAnchor_extract_replace_elec, rDataAnchor_extract_replace_elec]

private theorem extract_rDataElec_swap0DataIdx {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) (z : Fin (2 ^ kData)) (e : Fin 218) :
    (rDataElec selMux e).extractIndex (swap0DataIdx selMux idxFn hIdxLt z) =
    (rDataElec selMux (Equiv.swap 0 (dataActiveSlot selMux idxFn hIdxLt z) e)).extractIndex z := by
  let u := dataActiveSlot selMux idxFn hIdxLt z
  dsimp only [swap0DataIdx]
  split_ifs with hu0
  · change _ = (rDataElec selMux (Equiv.swap 0 u e)).extractIndex z
    rw [show u = 0 from hu0, Equiv.swap_self, Equiv.refl_apply]
  · change _ = (rDataElec selMux (Equiv.swap 0 u e)).extractIndex z
    have hd0u : (rDataElec selMux 0).DisjointWires (rDataElec selMux u) :=
      rDataElec_disjoint selMux (Ne.symm hu0)
    by_cases he0 : e = 0
    · subst he0
      rw [Equiv.swap_apply_left, QRegister.extractIndex_replaceIndex_of_disjoint _ _ hd0u,
        QRegister.extractIndex_replaceIndex]
    · by_cases heu : e = u
      · subst heu
        rw [Equiv.swap_apply_right, QRegister.extractIndex_replaceIndex]
      · rw [Equiv.swap_apply_of_ne_of_ne he0 heu,
            QRegister.extractIndex_replaceIndex_of_disjoint _ _ (rDataElec_disjoint selMux heu),
            QRegister.extractIndex_replaceIndex_of_disjoint _ _ (rDataElec_disjoint selMux he0)]

theorem swap0DataIdx_involutive {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) :
    Function.Involutive (swap0DataIdx selMux idxFn hIdxLt) := fun x ↦ by
  have huEq := dataActiveSlot_eq_of_anchor_eq selMux idxFn hIdxLt (swap0DataIdx_anchor_eq selMux
    idxFn hIdxLt x)
  let u := dataActiveSlot selMux idxFn hIdxLt x
  change swap0DataIdx selMux idxFn hIdxLt (swap0DataIdx selMux idxFn hIdxLt x) = x
  by_cases hu0 : u = 0
  · have h1 : swap0DataIdx selMux idxFn hIdxLt x = x := ite_eq_left hu0
    rw [h1, h1]
  · have hdisj := rDataElec_disjoint selMux (Ne.symm hu0)
    let y0 := swap0DataIdx selMux idxFn hIdxLt x
    change swap0DataIdx selMux idxFn hIdxLt y0 = x
    dsimp only [swap0DataIdx]
    rw [show dataActiveSlot selMux idxFn hIdxLt y0 = u from huEq, ite_eq_right hu0,
        show y0 = _ from ite_eq_right hu0, QRegister.extractIndex_replaceIndex,
        QRegister.extractIndex_replaceIndex_of_disjoint _ _ hdisj,
        QRegister.extractIndex_replaceIndex, QRegister.replaceIndex_comm_of_disjoint _ _ hdisj,
        QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_replaceIndex,
        QRegister.replaceIndex_extractIndex, QRegister.replaceIndex_extractIndex]

noncomputable def swap0DataPerm {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) : Equiv.Perm (Fin (2 ^ kData)) :=
  Equiv.ofBijective (swap0DataIdx selMux idxFn hIdxLt)
    (swap0DataIdx_involutive selMux idxFn hIdxLt).bijective

/-- Self-inverse `18`-wire `rElec[0] <-> rElec[idxFn(rAnchorIdx)]` permutation unitary on
`rData`. -/
noncomputable def uSwap0Gen {kData : ℕ} (selMux : QRegister posCoreWires kData) (idxFn : ℕ →
    ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) : Unitary (2 ^ kData) :=
  Operator.permutationUnitary (swap0DataPerm selMux idxFn hIdxLt)

theorem uSwap0Gen_conjTranspose {kData : ℕ} (selMux : QRegister posCoreWires kData) (idxFn : ℕ →
    ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) :
    (uSwap0Gen selMux idxFn hIdxLt).1ᴴ = (uSwap0Gen selMux idxFn hIdxLt).1 := by
  have hsq : swap0DataPerm selMux idxFn hIdxLt * swap0DataPerm selMux idxFn hIdxLt = 1 := by
    apply Equiv.ext; exact swap0DataIdx_involutive selMux idxFn hIdxLt
  have hinv : (uSwap0Gen selMux idxFn hIdxLt)⁻¹ = uSwap0Gen selMux idxFn hIdxLt := by
    apply mul_eq_one_iff_inv_eq.mp
    dsimp [uSwap0Gen]
    rw [← OperatorExt.permutationUnitary_mul, hsq, OperatorExt.permutationUnitary_one]
  rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hinv]

theorem permUnitary_apply {d : ℕ} (e : Equiv.Perm (Fin d)) (x y : Fin d) :
    (Operator.permutationUnitary e).1 x y = if x = e y then 1 else 0 := by
  change (Equiv.Perm.permMatrix ℂ (e⁻¹)) x y = _
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Equiv.Perm.inv_def]
  by_cases h : x = e y
  · subst h
    simp
  · simp [h, show e.symm x ≠ y from fun heq ↦ h (by rw [← heq, Equiv.apply_symm_apply])]

theorem mul_permUnitary_apply {d : ℕ} (A : Operator d) (e : Equiv.Perm (Fin d)) (x y : Fin d) : (A *
    (Operator.permutationUnitary e).1) x y = A x (e y) := by
  rw [Matrix.mul_apply]
  simp_rw [permUnitary_apply]
  rw [Finset.sum_eq_single (e y)]
  · simp
  · intro z _ hz
    rw [ite_eq_right hz, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem permUnitary_mul_apply {d : ℕ} (A : Operator d) (e : Equiv.Perm (Fin d)) (x y : Fin d) :
    ((Operator.permutationUnitary e).1 * A) x y = A (e.symm x) y := by
  rw [Matrix.mul_apply]
  simp_rw [permUnitary_apply]
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro z _ hz
    rw [ite_eq_right (fun heq ↦ hz (by rw [heq, Equiv.symm_apply_apply])), zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem unitaryConj_uSwap0Gen_apply {kData : ℕ} (selMux : QRegister posCoreWires kData) (idxFn : ℕ →
    ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218)
    (uInner : Unitary (2 ^ kData)) (y x : Fin (2 ^ kData)) : (HoistedSwapSelectBridge.unitaryConj
      (uSwap0Gen selMux idxFn hIdxLt) uInner).1 y x =
    uInner.1 (swap0DataIdx selMux idxFn hIdxLt y) (swap0DataIdx selMux idxFn hIdxLt x) := by
  rw [HoistedSwapSelectBridge.unitaryConj_val, uSwap0Gen_conjTranspose]
  dsimp only [uSwap0Gen]
  rw [mul_permUnitary_apply, permUnitary_mul_apply, (swap0DataPerm selMux idxFn
    hIdxLt).symm_apply_eq.mpr (swap0DataIdx_involutive selMux idxFn hIdxLt y).symm]
  rfl

/-- Universal invariance contract for an inner unitary `uInner` on `rData` conjugated by
`SWAP_18(rElec[0], rAnchor18)`:
1. `preserves_elec_and_anchor`: nonzero transitions preserve all `218` electron slots and
`rAnchorIdx`.
2. `indep_elec_nonzero`: matrix entries are independent of slots `e ≠ 0` when row and col agree on
slot `e`. -/
structure IsElec0LocalPreserving {kData : ℕ}
    (selMux : QRegister posCoreWires kData) (uInner : Unitary (2 ^ kData)) : Prop where
  preserves_elec_and_anchor :
    ∀ (z' z : Fin (2 ^ kData)), uInner.1 z' z ≠ 0 →
      (∀ e : Fin 218, (rDataElec selMux e).extractIndex z' = (rDataElec selMux e).extractIndex z) ∧
      (rDataAnchor selMux).extractIndex z' = (rDataAnchor selMux).extractIndex z
  indep_elec_nonzero :
    ∀ (z' z : Fin (2 ^ kData)) (e : Fin 218), e ≠ 0 →
      (rDataElec selMux e).extractIndex z' = (rDataElec selMux e).extractIndex z →
      ∀ v : Fin (2 ^ 18),
        uInner.1 ((rDataElec selMux e).replaceIndex z' v) ((rDataElec selMux e).replaceIndex z v) =
          uInner.1 z' z

theorem IsElec0LocalPreserving.of_diagonal {kData : ℕ} (selMux : QRegister posCoreWires kData)
    (uInner : Unitary (2 ^ kData))
    (d : Fin (2 ^ kData) → ℂ) (hd : uInner.1 = Matrix.diagonal d) (hindep : ∀ (z : Fin (2 ^ kData))
      (e : Fin 218), e ≠ 0 → ∀ v : Fin (2 ^ 18),
    d ((rDataElec selMux e).replaceIndex z v) = d z) : IsElec0LocalPreserving selMux uInner where
  preserves_elec_and_anchor z' z hnz := by
    have heq : z' = z := by
      by_contra hne; rw [hd, Matrix.diagonal_apply_ne _ hne] at hnz; exact hnz rfl
    subst heq; exact ⟨fun _ ↦ rfl, rfl⟩
  indep_elec_nonzero z' z e he hExtr v := by
    rw [hd]
    by_cases hzz : z' = z
    · subst hzz; simp [Matrix.diagonal, hindep z' e he v]
    · have hne : (rDataElec selMux e).replaceIndex z' v ≠ (rDataElec selMux e).replaceIndex z v :=
        fun h ↦ by
        have h1 := congrArg (fun w ↦ (rDataElec selMux e).replaceIndex w ((rDataElec selMux
          e).extractIndex z)) h
        rw [QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_replaceIndex,
          ← hExtr, QRegister.replaceIndex_extractIndex, hExtr, QRegister.replaceIndex_extractIndex]
            at h1
        exact hzz h1
      simp [Matrix.diagonal, hzz, hne]

theorem IsElec0LocalPreserving.inv {kData : ℕ} {selMux : QRegister posCoreWires kData}
    {uInner : Unitary (2 ^ kData)} (h : IsElec0LocalPreserving selMux uInner) :
      IsElec0LocalPreserving selMux uInner⁻¹ := by
  have hcoe : (uInner⁻¹).1 = uInner.1ᴴ := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  refine ⟨fun z' z hnz ↦ ?_, fun z' z e he hExtr v ↦ ?_⟩
  · rw [hcoe, Matrix.conjTranspose_apply, star_ne_zero] at hnz
    obtain ⟨h1, h2⟩ := h.preserves_elec_and_anchor z z' hnz
    exact ⟨fun e ↦ (h1 e).symm, h2.symm⟩
  · rw [hcoe, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
        h.indep_elec_nonzero z z' e he hExtr.symm v]

noncomputable def slotValueSwapFn {k : ℕ} (r : QRegister 18 k) (a b : Fin (2 ^ 18)) (w : Fin (2 ^
    k)) : Fin (2 ^ k) :=
  r.replaceIndex w (Equiv.swap a b (r.extractIndex w))

theorem slotValueSwapFn_involutive {k : ℕ} (r : QRegister 18 k) (a b : Fin (2 ^ 18)) :
    Function.Involutive (slotValueSwapFn r a b) := fun w ↦ by
  dsimp [slotValueSwapFn]
  rw [QRegister.extractIndex_replaceIndex, Equiv.swap_apply_self,
    QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_extractIndex]

noncomputable def slotValueSwapPerm {k : ℕ} (r : QRegister 18 k) (a b : Fin (2 ^ 18)) : Equiv.Perm
    (Fin (2 ^ k)) :=
  Equiv.ofBijective (slotValueSwapFn r a b) (slotValueSwapFn_involutive r a b).bijective

theorem IsElec0LocalPreserving.mul {kData : ℕ} {selMux : QRegister posCoreWires kData} {u₂ u₁ :
    Unitary (2 ^ kData)}
    (h₂ : IsElec0LocalPreserving selMux u₂) (h₁ : IsElec0LocalPreserving selMux u₁) :
      IsElec0LocalPreserving selMux (u₂ * u₁) where
  preserves_elec_and_anchor z' z hnz := by
    rw [Submonoid.coe_mul, Matrix.mul_apply] at hnz
    obtain ⟨w, _, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    obtain ⟨he₂, ha₂⟩ := h₂.preserves_elec_and_anchor z' w (left_ne_zero_of_mul hmul)
    obtain ⟨he₁, ha₁⟩ := h₁.preserves_elec_and_anchor w z (right_ne_zero_of_mul hmul)
    exact ⟨fun e ↦ (he₂ e).trans (he₁ e), ha₂.trans ha₁⟩
  indep_elec_nonzero z' z e he hExtr v := by
    simp only [Submonoid.coe_mul, Matrix.mul_apply]
    let rE := rDataElec selMux e
    let v₀ := rE.extractIndex z
    let σ := slotValueSwapPerm rE v₀ v
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases hw : rE.extractIndex w = v₀
    · have hσw : σ w = rE.replaceIndex w v := by
        dsimp [σ, slotValueSwapPerm, slotValueSwapFn]; rw [hw, Equiv.swap_apply_left]
      rw[hσw, h₂.indep_elec_nonzero z' w e he (hExtr.trans hw.symm) v, h₁.indep_elec_nonzero w z e
        he hw v]
    · have h1_zero : u₁.1 w z = 0 :=
        Classical.byContradiction fun hnz ↦ hw ((h₁.preserves_elec_and_anchor w z hnz).1 e)
      have h1'_zero : u₁.1 (σ w) (rE.replaceIndex z v) = 0 := by
        by_contra hnz
        have hex := (h₁.preserves_elec_and_anchor (σ w) (rE.replaceIndex z v) hnz).1 e
        dsimp [σ, slotValueSwapPerm, slotValueSwapFn] at hex
        rw [QRegister.extractIndex_replaceIndex, QRegister.extractIndex_replaceIndex] at hex
        exact hw ((Equiv.swap v₀ v).injective (hex.trans (Equiv.swap_apply_left v₀ v).symm))
      rw [h1_zero, h1'_zero, mul_zero, mul_zero]

theorem anchorTblVal218Unclamped_eq_extract (y : Fin (2 ^ posCoreWires)) : anchorTblVal218Unclamped
    y = (rElecSlot (QRegExt.ofFin posCoreWires) ⟨aliasIdx218
    (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires y)), aliasIdx218_lt
      (regVal_rAnchorIdx_lt256 _ _)⟩).extractIndex y :=
  eq_of_basisBits_eq fun j ↦ by
    rw [basisBits_anchorTblVal218Unclamped, QRegister.basisBits_extractIndex]

theorem anchorTblVal218_eq_extract (y : Fin (2 ^ posCoreWires)) : anchorTblVal218 y =
    (rElecSlot (QRegExt.ofFin posCoreWires) ⟨clampIdx218 (regVal (rAnchorIdx
    (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires y)), clampIdx218_lt _⟩).extractIndex y :=
  eq_of_basisBits_eq fun j ↦ by
    rw [basisBits_anchorTblVal218, QRegister.basisBits_extractIndex]

theorem compose_rDataElec_replaceIndex {n kData : ℕ} (rData : QRegister kData n) (selMux : QRegister
    posCoreWires kData)
    (e : Fin 218) (g : Fin (2 ^ n)) (x : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) : (rData.compose
      (rDataElec selMux e)).replaceIndex (rData.replaceIndex g x) v =
    rData.replaceIndex g ((rDataElec selMux e).replaceIndex x v) :=
  eq_of_basisBits_eq fun q ↦ by
    let rE := rDataElec selMux e
    by_cases hqE : q ∈ Set.range (rData.compose rE).wires
    · obtain ⟨j, rfl⟩ := hqE
      rw [QRegister.basisBits_replaceIndex_apply]
      change _ = basisBits n (rData.replaceIndex g (rE.replaceIndex x v)) (rData (rE j))
      rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
    · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqE]
      by_cases hqD : q ∈ Set.range rData.wires
      · obtain ⟨i, rfl⟩ := hqD
        have hiNotE : i ∉ Set.range rE.wires := fun ⟨j, hj⟩ ↦ hqE ⟨j, congrArg rData hj⟩
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hiNotE]
      · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqD,
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hqD]

theorem embedMatrix_mulVec_single_sum {n k : ℕ} (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin
    (2 ^ k)) ℂ) (g : Fin (2 ^ n)) :
    (r.embedMatrix A).mulVec (Pi.single g 1) = ∑ y : Fin (2 ^ k), A y (r.extractIndex g) • Pi.single
      (r.replaceIndex g y) 1 := by
  have hcol : A.mulVec (Pi.single (r.extractIndex g) 1) = ∑ y : Fin (2 ^ k), A y (r.extractIndex g)
    • Pi.single y 1 := by
    funext z
    rw [Matrix.mulVec_single_one, Finset.sum_apply]
    symm
    rw [Finset.sum_eq_single z]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]; rfl
    · intro y _ hyz
      rw [Pi.smul_apply, Pi.single_eq_of_ne hyz.symm, smul_zero]
    · intro hz; exact (hz (Finset.mem_univ z)).elim
  rw [r.embedMatrix_mulVec_single_factors, hcol, QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]

/-- Extends a register embedding by `18` identity wires on the right. -/
abbrev selExtendRight18 {a kData : ℕ} (r : QRegister a kData) : QRegister (a + 18) (kData +
    18) where
  wires :=
    { toFun := fun u ↦
        if h : u.val < a then Fin.castAdd 18 (r ⟨u.val, h⟩)
        else Fin.natAdd kData ⟨u.val - a, by omega⟩
      inj' := fun u₁ u₂ heq ↦ by
        have hv := congrArg Fin.val heq
        dsimp at hv
        by_cases h1 : u₁.val < a
        · by_cases h2 : u₂.val < a
          · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd] at hv
            exact Fin.ext (congrArg (fun w : Fin a ↦ w.val) (r.wires.injective (Fin.ext hv)))
          · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd] at hv
            have := (r ⟨u₁.val, h1⟩).isLt
            omega
        · by_cases h2 : u₂.val < a
          · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd] at hv
            have := (r ⟨u₂.val, h2⟩).isLt
            omega
          · simp only [h1, h2, ↓reduceDIte] at hv
            exact Fin.ext (by omega) }

private theorem compose_selExtendRight18 {n a kData : ℕ} (rData : QRegister kData n) (rAnchor18 :
    QRegister 18 n)
    (r : QRegister a kData) (hDA : rData.DisjointWires rAnchor18) : (rData.concat rAnchor18
      hDA).compose (selExtendRight18 r) =
    (rData.compose r).concat rAnchor18 (hDA.compose_left r) :=
  QRegister.ext (Function.Embedding.ext fun u ↦ Fin.addCases
    (fun i ↦ by
      change (rData.concat rAnchor18 hDA) (selExtendRight18 r (Fin.castAdd 18 i)) =
        ((rData.compose r).concat rAnchor18 _) (Fin.castAdd 18 i)
      rw [show selExtendRight18 r (Fin.castAdd 18 i) = Fin.castAdd 18 (r i) from
            Fin.ext (by dsimp [selExtendRight18]; rw [dite_eq_left i.isLt]; rfl),
          QRegister.concat_apply_left, QRegister.concat_apply_left]
      rfl)
    (fun j ↦ by
      change (rData.concat rAnchor18 hDA) (selExtendRight18 r (Fin.natAdd a j)) =
        ((rData.compose r).concat rAnchor18 _) (Fin.natAdd a j)
      rw [show selExtendRight18 r (Fin.natAdd a j) = Fin.natAdd kData j from
            Fin.ext (by dsimp [selExtendRight18]; rw [dite_eq_right (by omega)]; dsimp; omega),
          QRegister.concat_apply_right, QRegister.concat_apply_right]) u)

def selData18 (kData : ℕ) : QRegister kData (kData + 18) := QRegister.block 0 kData (by omega)

theorem compose_selData18 {n kData : ℕ} (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (hDA : rData.DisjointWires rAnchor18) :
    (rData.concat rAnchor18 hDA).compose (selData18 kData) = rData :=
  QRegister.ext (Function.Embedding.ext fun i ↦ by
    change (rData.concat rAnchor18 hDA) ⟨0 + i.val, _⟩ = rData i
    rw [show (⟨0 + i.val, by omega⟩ : Wire (kData + 18)) = Fin.castAdd 18 i from Fin.ext (by simp),
      QRegister.concat_apply_left])

def selSwap36 {kData : ℕ} (selMux : QRegister posCoreWires kData) : QRegister 36 (kData + 18) :=
  selExtendRight18 (rDataElec selMux 0)

theorem swap0ConjPre_mulVec_single_of_zero {n kData : ℕ}
    (rData : QRegister kData n) (rAnchor18 : QRegister 18 n)
    (selMux : QRegister posCoreWires kData) (hDA : rData.DisjointWires rAnchor18)
    (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218)
    (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (htbl : ∀ y : Fin (2 ^ posCoreWires), tbl y = (rElecSlot (QRegExt.ofFin posCoreWires)
      ⟨idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires y)),
        hIdxLt _ (regVal_rAnchorIdx_lt256 _ _)⟩).extractIndex y)
    {uInner : Unitary (2 ^ kData)} (hPres : IsElec0LocalPreserving selMux uInner)
    (g : Fin (2 ^ n)) (hgA0 : rAnchor18.extractIndex g = 0) :
    let rCoreMux := rData.compose selMux
    let rE0 := rData.compose (rDataElec selMux 0)
    let tblData : Fin (2 ^ kData) → Fin (2 ^ 18) := fun x ↦ tbl (selMux.extractIndex x)
    ((cSwap18 rE0 rAnchor18 (hDA.compose_left _)).eval.1 *
      ((rData.embedUnitary uInner).1 *
        ((cSwap18 rE0 rAnchor18 (hDA.compose_left _)).eval.1 *
          ((rCoreMux.concat rAnchor18 (hDA.compose_left selMux)).embedUnitary (uFullAnchorLoadE0
            tbl)).1))).mulVec
        (Pi.single g 1) =
    (setTableOp rData rAnchor18 tblData *
      (rData.embedUnitary (HoistedSwapSelectBridge.unitaryConj (uSwap0Gen selMux idxFn hIdxLt)
        uInner)).1).mulVec
        (Pi.single g 1) := by
  intro rCoreMux rE0 tblData
  have htblD : ∀ z : Fin (2 ^ kData),
      tblData z = (rDataElec selMux (dataActiveSlot selMux idxFn hIdxLt z)).extractIndex z :=
        fun z ↦ by
    dsimp only [tblData, dataActiveSlot, rDataElec]
    rw [htbl (selMux.extractIndex z), QRegister.extractIndex_compose]
  let x := rData.extractIndex g
  let u₀ := dataActiveSlot selMux idxFn hIdxLt x
  let rE0L := rDataElec selMux 0
  let v₀ := rE0L.extractIndex x
  let va := tblData x
  let x₁ := rE0L.replaceIndex x va
  simp only [← Matrix.mulVec_mulVec]
  rw [uFullAnchorLoadE0_embed_mulVec_single_of_zero tbl rCoreMux rAnchor18 _ g hgA0,
    QRegister.extractIndex_compose rData selMux g]
  change (cSwap18 rE0 rAnchor18 _).eval.1.mulVec ((rData.embedUnitary uInner).1.mulVec
    ((cSwap18 rE0 rAnchor18 _).eval.1.mulVec (Pi.single (rAnchor18.replaceIndex g va) 1))) = _
  rw [cSwap18_eval_mulVec_single, QRegister.extractIndex_replaceIndex rAnchor18 g va,
    (QRegister.extractIndex_replaceIndex_of_disjoint rE0 rAnchor18 (hDA.compose_left _) g va).trans
      (QRegister.extractIndex_compose rData rE0L g)]
  let g₂ := rAnchor18.replaceIndex (rE0.replaceIndex (rAnchor18.replaceIndex g va) va) v₀
  have hg₂_eq : g₂ = rAnchor18.replaceIndex (rData.replaceIndex g x₁) v₀ := by
    dsimp only [g₂, x₁, x]
    rw [QRegister.replaceIndex_comm_of_disjoint rE0 rAnchor18 (hDA.compose_left _),
        QRegister.replaceIndex_replaceIndex]
    refine congrArg (fun z ↦ rAnchor18.replaceIndex z v₀) ?_
    conv_lhs => rw [(QRegister.replaceIndex_extractIndex rData g).symm]
    exact compose_rDataElec_replaceIndex rData selMux 0 g (rData.extractIndex g) va
  change (cSwap18 rE0 rAnchor18 _).eval.1.mulVec
    ((rData.embedMatrix uInner.1).mulVec (Pi.single g₂ 1)) = _
  rw [embedMatrix_mulVec_single_sum rData uInner.1 g₂, show rData.extractIndex g₂ = x₁ by
        rw [hg₂_eq, QRegister.extractIndex_replaceIndex_of_disjoint rData rAnchor18 hDA,
            QRegister.extractIndex_replaceIndex], Matrix.mulVec_sum]
  conv_rhs =>
    rw [QRegister.embedUnitary_val, embedMatrix_mulVec_single_sum rData _ g, Matrix.mulVec_sum]
  let τ := slotValueSwapPerm rE0L v₀ va
  rw [← Equiv.sum_comp τ]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, show rData.extractIndex g = x from rfl,
    unitaryConj_uSwap0Gen_apply, setTableOp_mulVec_single, QRegister.extractIndex_replaceIndex rData
      g y]
  by_cases hMatch :
      (∀ e : Fin 218, (rDataElec selMux e).extractIndex y = (rDataElec selMux e).extractIndex x) ∧
      (rDataAnchor selMux).extractIndex y = (rDataAnchor selMux).extractIndex x
  · obtain ⟨hEl, hAn⟩ := hMatch
    have hy0 : rE0L.extractIndex y = v₀ := hEl 0
    have hτy : τ y = rE0L.replaceIndex y va := by
      dsimp [τ, slotValueSwapPerm, slotValueSwapFn]
      rw [hy0, Equiv.swap_apply_left]
    have hu_yx := dataActiveSlot_eq_of_anchor_eq selMux idxFn hIdxLt hAn
    have htbl_yx : tblData y = va := by
      rw [htblD y, hu_yx, hEl u₀]
      exact (htblD x).symm
    have hAmp : uInner.1 (τ y) x₁ =
        uInner.1 (swap0DataIdx selMux idxFn hIdxLt y) (swap0DataIdx selMux idxFn hIdxLt x) := by
      rw [hτy]
      by_cases hu0 : u₀ = 0
      · have hv : va = v₀ := (htblD x).trans (by
          change (rDataElec selMux u₀).extractIndex x = v₀
          rw [hu0])
        have hsy0 : swap0DataIdx selMux idxFn hIdxLt y = y := by
          dsimp [swap0DataIdx]
          rw [hu_yx, ite_eq_left hu0]
        have hsx0 : swap0DataIdx selMux idxFn hIdxLt x = x := by
          dsimp [swap0DataIdx]
          rw [ite_eq_left hu0]
        rw [hsy0, hsx0,
            show rE0L.replaceIndex y va = y by rw [hv, ← hy0, QRegister.replaceIndex_extractIndex],
            show x₁ = x by rw [show x₁ = rE0L.replaceIndex x va from rfl, hv,
              QRegister.replaceIndex_extractIndex]]
      · have hdisj := rDataElec_disjoint selMux (Ne.symm hu0)
        have hsy : swap0DataIdx selMux idxFn hIdxLt y =
            (rDataElec selMux u₀).replaceIndex (rE0L.replaceIndex y va) v₀ := by
          dsimp [swap0DataIdx, va]
          rw [hu_yx, ite_eq_right hu0, hy0, hEl u₀, htblD x]
        have hsx : swap0DataIdx selMux idxFn hIdxLt x =
            (rDataElec selMux u₀).replaceIndex x₁ v₀ := by
          dsimp [swap0DataIdx, x₁, va]
          rw [ite_eq_right hu0, htblD x]
        have hRep (z : Fin (2 ^ kData))
            (hz : (rDataElec selMux u₀).extractIndex z = (rDataElec selMux u₀).extractIndex x) :
            z = (rDataElec selMux u₀).replaceIndex z va :=
          (QRegister.replaceIndex_extractIndex (rDataElec selMux u₀) z).symm.trans
            (congrArg ((rDataElec selMux u₀).replaceIndex z) (hz.trans (htblD x).symm))
        conv_lhs =>
          rw [show rE0L.replaceIndex y va =
                (rDataElec selMux u₀).replaceIndex (swap0DataIdx selMux idxFn hIdxLt y) va by
                rw [hsy, QRegister.replaceIndex_replaceIndex]
                exact hRep _ ((QRegister.extractIndex_replaceIndex_of_disjoint _ _ hdisj.symm
                  y va).trans (hEl u₀)),
              show x₁ = (rDataElec selMux u₀).replaceIndex
                (swap0DataIdx selMux idxFn hIdxLt x) va by
                rw [hsx, QRegister.replaceIndex_replaceIndex]
                exact hRep _ (QRegister.extractIndex_replaceIndex_of_disjoint _ _ hdisj.symm x va)]
        exact hPres.indep_elec_nonzero _ _ u₀ hu0 (by
          rw [hsy, hsx, QRegister.extractIndex_replaceIndex,
              QRegister.extractIndex_replaceIndex]) va
    rw [cSwap18_eval_mulVec_single, hAmp, htbl_yx]
    refine congrArg
      ((uInner.1 (swap0DataIdx selMux idxFn hIdxLt y) (swap0DataIdx selMux idxFn hIdxLt x)) • ·) ?_
    rw [show rAnchor18.extractIndex (rData.replaceIndex g₂ (τ y)) = v₀ by
          rw [QRegister.extractIndex_replaceIndex_of_disjoint rAnchor18 rData hDA.symm, hg₂_eq,
              QRegister.extractIndex_replaceIndex],
        show rE0.extractIndex (rData.replaceIndex g₂ (τ y)) = va by
          rw [show rE0 = rData.compose rE0L from rfl, QRegister.extractIndex_compose,
              QRegister.extractIndex_replaceIndex, hτy, QRegister.extractIndex_replaceIndex],
        show rData.replaceIndex g₂ (τ y) = rAnchor18.replaceIndex (rData.replaceIndex g (τ y)) v₀ by
          rw [hg₂_eq, QRegister.replaceIndex_comm_of_disjoint rData rAnchor18 hDA,
              QRegister.replaceIndex_replaceIndex],
        QRegister.replaceIndex_comm_of_disjoint rE0 rAnchor18 (hDA.compose_left _),
        QRegister.replaceIndex_replaceIndex, compose_rDataElec_replaceIndex rData selMux 0 g _ v₀,
        hτy, QRegister.replaceIndex_replaceIndex, ← hy0, QRegister.replaceIndex_extractIndex]
  · have hL0 : uInner.1 (τ y) x₁ = 0 := by
      by_contra hnz
      obtain ⟨hEl', hAn'⟩ := hPres.preserves_elec_and_anchor (τ y) x₁ hnz
      refine hMatch ⟨fun e ↦ ?_, ?_⟩
      · by_cases he0 : e = 0
        · subst he0
          have h0 := hEl' 0
          dsimp [τ, slotValueSwapPerm, slotValueSwapFn, x₁] at h0
          rw [QRegister.extractIndex_replaceIndex, QRegister.extractIndex_replaceIndex] at h0
          exact (Equiv.swap v₀ va).injective (h0.trans (Equiv.swap_apply_left v₀ va).symm)
        · have he := hEl' e
          dsimp [τ, slotValueSwapPerm, slotValueSwapFn, x₁] at he
          rwa [QRegister.extractIndex_replaceIndex_of_disjoint _ _ (rDataElec_disjoint selMux he0),
               QRegister.extractIndex_replaceIndex_of_disjoint _ _ (rDataElec_disjoint selMux he0)]
            at he
      · dsimp [τ, slotValueSwapPerm, slotValueSwapFn, x₁] at hAn'
        rwa [rDataAnchor_extract_replace_elec, rDataAnchor_extract_replace_elec] at hAn'
    have hR0 : uInner.1 (swap0DataIdx selMux idxFn hIdxLt y)
        (swap0DataIdx selMux idxFn hIdxLt x) = 0 := by
      by_contra hnz
      obtain ⟨hEl', hAn'⟩ := hPres.preserves_elec_and_anchor _ _ hnz
      rw [swap0DataIdx_anchor_eq, swap0DataIdx_anchor_eq] at hAn'
      refine hMatch ⟨fun e ↦ ?_, hAn'⟩
      have h := hEl' (Equiv.swap 0 u₀ e)
      rwa [extract_rDataElec_swap0DataIdx, extract_rDataElec_swap0DataIdx,
           dataActiveSlot_eq_of_anchor_eq selMux idxFn hIdxLt hAn', Equiv.swap_apply_self] at h
    rw [hL0, hR0, zero_smul, zero_smul]

theorem swap0_work_h18 {mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) : 0 + 18 ≤ mWork := by omega
theorem swap0_work_hRest {mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) : 18 + (mWork -
    18) ≤ mWork := by omega
theorem swap0_work_hCleanRest {mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) : 0 + mClean ≤ mWork -
    18 := by omega
theorem swap0_work_hCleanWork {mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) : 0 + mClean ≤ mWork :=
  by omega

abbrev swap0Anchor18Reg {n mClean mWork : ℕ} (rWork : QRegister mWork n) (hW : 18 +
    mClean ≤ mWork) : QRegister 18 n := rWork.slice 0 18 (swap0_work_h18 hW)

abbrev swap0RestReg {n mClean mWork : ℕ} (rWork : QRegister mWork n) (hW : 18 + mClean ≤ mWork) :
    QRegister (mWork - 18) n := rWork.slice 18 (mWork - 18) (swap0_work_hRest hW)

theorem concat_swap0Regs_basisOutcomeProjector_zero {n mClean mWork : ℕ} (rWork : QRegister mWork n)
    (hW : 18 + mClean ≤ mWork)
    (hAR : (swap0Anchor18Reg rWork hW).DisjointWires (swap0RestReg rWork hW)) :
    ((swap0Anchor18Reg rWork hW).concat (swap0RestReg rWork hW) hAR).basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 := by
  let rC := (swap0Anchor18Reg rWork hW).concat (swap0RestReg rWork hW) hAR
  let selF : QRegister (18 + (mWork - 18)) mWork :=
    ⟨⟨fun idx ↦ ⟨idx.val, by omega⟩,
      fun _ _ h ↦ Fin.ext (congrArg (fun w : Fin mWork ↦ w.val) h)⟩⟩
  let selB : QRegister mWork (18 + (mWork - 18)) :=
    ⟨⟨fun idx ↦ ⟨idx.val, by omega⟩,
      fun _ _ h ↦ Fin.ext (congrArg (fun w : Fin (18 + (mWork - 18)) ↦ w.val) h)⟩⟩
  have hCF : rWork.compose selF = rC := QRegister.ext (Function.Embedding.ext fun idx ↦
    Fin.addCases
      (fun i ↦ by
        change rWork ⟨i.val, _⟩ = rC (Fin.castAdd (mWork - 18) i)
        rw [QRegister.concat_apply_left]
        exact congrArg rWork (Fin.ext (by
          dsimp [swap0Anchor18Reg, QRegister.slice, QRegister.block, Fin.natAddEmb]; omega)))
      (fun j ↦ by
        change rWork ⟨18 + j.val, _⟩ = rC (Fin.natAdd 18 j)
        rw [QRegister.concat_apply_right]
        exact congrArg rWork (Fin.ext (by
          dsimp [swap0RestReg, QRegister.slice, QRegister.block, Fin.natAddEmb]))) idx)
  have hCB : rC.compose selB = rWork := QRegister.ext (Function.Embedding.ext fun k ↦ by
    change rC (selB k) = rWork k
    rw [← hCF]
    exact congrArg rWork (Fin.ext rfl))
  exact ((congrArg (fun r ↦ r.basisOutcomeProjector 0 * rC.basisOutcomeProjector 0) hCB.symm).trans
    ((QRegExt.compose_zero_mul_basisOutcomeProjector_zero rC) selB)).symm.trans
    ((congrArg (fun r ↦ rWork.basisOutcomeProjector 0 * r.basisOutcomeProjector 0) hCF.symm).trans
      ((QRegExt.basisOutcomeProjector_zero_mul_compose_zero rWork) selF))

/-- Parametric `SWAP_18(rElec[0], rAnchor18)` conjugation bracket around `dInner`. -/
abbrev swap0ScrLoadReg {n mClean mWork : ℕ} (rWork : QRegister mWork n) (hW : 18 + mClean ≤ mWork) :
    QRegister mClean n := (swap0RestReg rWork hW).slice 0 mClean (swap0_work_hCleanRest hW)

abbrev swap0ScrFixReg {n mClean mWork : ℕ} (rWork : QRegister mWork n) (hW : 18 + mClean ≤ mWork) :
    QRegister mClean n := rWork.slice 0 mClean (swap0_work_hCleanWork hW)

theorem swap0_disj_core_anchor {n kData mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) {rData :
    QRegister kData n} {selMux : QRegister posCoreWires kData}
    {rWork : QRegister mWork n} (hDW : rData.DisjointWires rWork) : (rData.compose
      selMux).DisjointWires (swap0Anchor18Reg rWork hW) :=
  (hDW.compose_right _).compose_left selMux

theorem swap0_disj_coreAnchor_scrLoad {n kData mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) {rData :
    QRegister kData n} {selMux : QRegister posCoreWires kData}
    {rWork : QRegister mWork n} (hDW : rData.DisjointWires rWork) : ((rData.compose
    selMux).concat (swap0Anchor18Reg rWork hW) (swap0_disj_core_anchor hW hDW)).DisjointWires
      (swap0ScrLoadReg rWork hW) :=
  (disj_concat_left (swap0_disj_core_anchor hW hDW) ((hDW.compose_right _).compose_left selMux)
    (rWork.slice_disjoint_of_le 0 18 18 (mWork - 18) (swap0_work_h18 hW) (swap0_work_hRest hW)
      le_rfl)).compose_right _

theorem swap0_disj_core_scrFix {n kData mClean mWork : ℕ} (hW : 18 + mClean ≤ mWork) {rData :
    QRegister kData n} {selMux : QRegister posCoreWires kData}
    {rWork : QRegister mWork n} (hDW : rData.DisjointWires rWork) : (rData.compose
      selMux).DisjointWires (swap0ScrFixReg rWork hW) :=
  (hDW.compose_left selMux).compose_right _

set_option backward.isDefEq.respectTransparency true

noncomputable def dAnchorSwap0ConjGenRaw {Var : Type} {n kData mClean mWork : ℕ} (hW : 18 +
    mClean ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n) (hDW : rData.DisjointWires
      rWork) (dLoad : DynamicCircuit Var n)
    (dFix : (Fin 18 → Bool) → DynamicCircuit Var n) (dInner : DynamicCircuit Var n) : DynamicCircuit
      Var n :=
  let rAnchor18 := swap0Anchor18Reg rWork hW
  let rE0 := rData.compose (rDataElec selMux 0)
  let cSw := DynamicCircuit.circuit (cSwap18 rE0 rAnchor18 ((hDW.compose_right _).compose_left _))
  DynamicCircuit.seq (DynamicCircuit.seq dLoad (DynamicCircuit.seq cSw (DynamicCircuit.seq dInner
    cSw)))
    (DynCircuitExt.measureXResetAndBranch v 18 rAnchor18 dFix)

theorem dAnchorSwap0ConjGenRaw_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n kData mClean
    mWork : ℕ} [NeZero (2 ^ n)]
    (hW : 18 + mClean ≤ mWork) (idxFn : ℕ → ℕ) (hIdxLt : ∀ val < 256, idxFn val < 218) (tbl : Fin (2
      ^ posCoreWires) → Fin (2 ^ 18))
    (htbl : ∀ y : Fin (2 ^ posCoreWires), tbl y = (rElecSlot (QRegExt.ofFin posCoreWires)
    ⟨idxFn (regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires y)),
      hIdxLt _ (regVal_rAnchorIdx_lt256 _ _)⟩).extractIndex y)
    (v : Var) (rData : QRegister kData n) (selMux : QRegister posCoreWires kData) (rWork : QRegister
      mWork n) (hDW : rData.DisjointWires rWork)
    {dLoad : DynamicCircuit Var n} {dFix : (Fin 18 → Bool) → DynamicCircuit Var n} (hLoadSpec :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    ((rData.compose selMux).concat (swap0Anchor18Reg rWork hW) (swap0_disj_core_anchor hW hDW))
      (swap0ScrLoadReg rWork hW) (uFullAnchorLoadE0 tbl) dLoad)
    (hFixSpec : ∀ (f : Fin 18 → Bool), DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.compose selMux) (swap0ScrFixReg rWork hW)
    (diagSignUnitary (fun y ↦ f2Parity 18 f (tbl y))) (dFix f)) {uInner : Unitary (2 ^ kData)}
      {dInner : DynamicCircuit Var n}
    (hInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData (swap0RestReg rWork hW)
      uInner dInner)
    (hPres : IsElec0LocalPreserving selMux uInner) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rWork
    (HoistedSwapSelectBridge.unitaryConj (uSwap0Gen selMux idxFn hIdxLt) uInner)
      (dAnchorSwap0ConjGenRaw hW v rData selMux rWork hDW dLoad dFix dInner) := by
  let rCoreMux := rData.compose selMux
  let rAnchor18 := swap0Anchor18Reg rWork hW
  let rRest := swap0RestReg rWork hW
  let hDA : rData.DisjointWires rAnchor18 := hDW.compose_right _
  let hDR : rData.DisjointWires rRest := hDW.compose_right _
  let hAR : rAnchor18.DisjointWires rRest :=
    rWork.slice_disjoint_of_le 0 18 18 (mWork - 18) (swap0_work_h18 hW) (swap0_work_hRest hW) le_rfl
  let rAct := rData.concat rAnchor18 hDA
  have hActR : rAct.DisjointWires rRest := disj_concat_left hDA hDR hAR
  have hProjEq := concat_swap0Regs_basisOutcomeProjector_zero rWork hW hAR
  let rE0 := rData.compose (rDataElec selMux 0)
  let hE0A : rE0.DisjointWires rAnchor18 := hDA.compose_left _
  have hWiden {kSub : ℕ} (sel : QRegister kSub (kData + 18)) {rSub : QRegister kSub n}
      (heq : rAct.compose sel = rSub) {U : Unitary (2 ^ kSub)} {d : DynamicCircuit Var n}
      (h : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rSub rRest U d) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rRest (sel.embedUnitary U) d :=
    (Eq.ndrec (motive := fun r ↦ DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r rRest _
      _) h heq.symm).widenActive
  have hL1 := hWiden (selExtendRight18 selMux) (compose_selExtendRight18 rData rAnchor18 selMux hDA)
    (by
    have hLS := hLoadSpec
    dsimp only [swap0ScrLoadReg, QRegister.slice] at hLS
    exact hLS.widenWorkspace)
  have hSw := hWiden (selSwap36 selMux) (compose_selExtendRight18 rData rAnchor18 (rDataElec selMux
    0) hDA)
    (DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit _ rRest cSwap18Local.eval
      (cSwap18 rE0 rAnchor18 hE0A) (embedCircuit123_eval (rE0.concat rAnchor18 hE0A) cSwap18Local))
  have hIn := hWiden (selData18 kData) (compose_selData18 rData rAnchor18 hDA) hInner
  have hPre := hL1.seq hActR (hSw.seq hActR (hIn.seq hActR hSw))
  let tblData : Fin (2 ^ kData) → Fin (2 ^ 18) := fun x ↦ tbl (selMux.extractIndex x)
  have hComp : (rAct.embedUnitary ((((selSwap36 selMux).embedUnitary cSwap18Local.eval *
      (selData18 kData).embedUnitary uInner) * (selSwap36 selMux).embedUnitary
      cSwap18Local.eval) * (selExtendRight18 selMux).embedUnitary (uFullAnchorLoadE0 tbl))).1 *
      (rAnchor18.concat rRest hAR).basisOutcomeProjector 0 = setTableOp rData rAnchor18
      tblData * (rData.embedUnitary (HoistedSwapSelectBridge.unitaryConj (uSwap0Gen selMux
      idxFn hIdxLt) uInner)).1 * (rAnchor18.concat rRest hAR).basisOutcomeProjector 0 := by
    have hEmbL : (rAct.embedUnitary
        ((selExtendRight18 selMux).embedUnitary (uFullAnchorLoadE0 tbl))).1 =
        ((rCoreMux.concat rAnchor18 (hDA.compose_left selMux)).embedUnitary
          (uFullAnchorLoadE0 tbl)).1 := by
      rw [← QRegister.embedUnitary_compose, compose_selExtendRight18 rData rAnchor18 selMux hDA]
    have hEmbS : (rAct.embedUnitary ((selSwap36 selMux).embedUnitary cSwap18Local.eval)).1 =
        (cSwap18 rE0 rAnchor18 hE0A).eval.1 := by
      rw [← QRegister.embedUnitary_compose, selSwap36,
          compose_selExtendRight18 rData rAnchor18 (rDataElec selMux 0) hDA]
      exact (congrArg Subtype.val (embedCircuit123_eval _ cSwap18Local)).symm
    have hEmbI : (rAct.embedUnitary ((selData18 kData).embedUnitary uInner)).1 =
        (rData.embedUnitary uInner).1 := by
      rw [← QRegister.embedUnitary_compose, compose_selData18 rData rAnchor18 hDA]
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, hEmbL, hEmbS, hEmbI]
    refine matrix_ext_ket fun β ↦ ?_
    let g : Fin (2 ^ n) := (basisBitsEquiv n).symm β
    have hProjApply {kP : ℕ} (r : QRegister kP n) :
        (r.basisOutcomeProjector 0).mulVec (Pi.single g 1) =
          if r.extractIndex g = 0 then Pi.single g 1 else 0 := funext fun i ↦ by
      rw [Matrix.mulVec_single_one, QRegister.basisOutcomeProjector_eq_diagonal,
          apply_ite (fun v : Fin (2 ^ n) → ℂ ↦ v i)]
      by_cases hig : i = g
      · simp [hig, Matrix.diagonal]
      · simp [hig, Matrix.diagonal]
    have hMulZero (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : M.mulVec 0 = 0 :=
      funext fun _ ↦ by simp [Matrix.mulVec, dotProduct]
    have hProjVec : ((rAnchor18.concat rRest hAR).basisOutcomeProjector 0).mulVec (ket β) =
        if rRest.extractIndex g = 0 ∧ rAnchor18.extractIndex g = 0 then Pi.single g 1 else 0 := by
      rw [show ket β = Pi.single g 1 from rfl,
          QRegExt.concat_basisOutcomeProjector_zero rAnchor18 rRest hAR,
          ← Matrix.mulVec_mulVec, hProjApply rRest]
      by_cases hR0 : rRest.extractIndex g = 0
      · simp only [hR0, true_and, ↓reduceIte, hProjApply rAnchor18]
      · simp only [hR0, false_and, ↓reduceIte, hMulZero]
    conv_lhs => rw [← Matrix.mulVec_mulVec, hProjVec]
    conv_rhs => rw [← Matrix.mulVec_mulVec, hProjVec]
    by_cases hRA : rRest.extractIndex g = 0 ∧ rAnchor18.extractIndex g = 0
    · rw [ite_eq_left hRA]
      simpa only [Matrix.mul_assoc] using swap0ConjPre_mulVec_single_of_zero rData rAnchor18 selMux
        hDA idxFn hIdxLt tbl htbl hPres g hRA.2
    · rw [ite_eq_right hRA, hMulZero, hMulZero]
  have hCont (f : Fin 18 → Bool) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData (rAnchor18.concat rRest hAR)
        (diagSignUnitary (fun x ↦ f2Parity 18 f (tblData x))) (dFix f) := by
    have hFS := hFixSpec f
    dsimp only [swap0ScrFixReg, QRegister.slice] at hFS
    have hwa := hFS.widenWorkspace.widenActive
    have hdiagEq : selMux.embedUnitary (diagSignUnitary (fun y ↦ f2Parity 18 f (tbl y))) =
        diagSignUnitary (fun x ↦ f2Parity 18 f (tblData x)) :=
      Subtype.ext <| matrix_ext_ket fun γ ↦ by
        let x := (basisBitsEquiv kData).symm γ
        rw [show ket γ = Pi.single x 1 from rfl, embedUnitary_diagSignUnitary_mulVec_single]
        funext z
        rw [Matrix.mulVec_single_one]
        by_cases hzx : z = x
        · simp [hzx, diagSignUnitary, Matrix.diagonal, tblData]
        · simp [hzx, diagSignUnitary, Matrix.diagonal]
    rw [hdiagEq] at hwa
    exact fun M_obs ↦ (hwa M_obs).imp fun _ ⟨hwp, hproj⟩ ↦ ⟨hwp, by rwa [hProjEq]⟩
  have hOut := DynCircuitExt.realizesCleanTableXUncompute v rData rAnchor18 rRest hDA hDR hAR
    tblData hPre hComp hCont
  exact fun M_obs ↦ (hOut M_obs).imp fun _ ⟨hwp, hproj⟩ ↦ ⟨hwp, by rwa [hProjEq] at hproj⟩

theorem dAnchorSwap0ConjGenRaw_toff {Var : Type} {n kData mClean mWork : ℕ} (hW : 18 +
    mClean ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n) (hDW : rData.DisjointWires
      rWork) {dLoad : DynamicCircuit Var n}
    {dFix : (Fin 18 → Bool) → DynamicCircuit Var n} (hLoadToff : dLoad.count PrimitiveGate.TOFF = 0)
    (hFixToff : ∀ f, (dFix f).count PrimitiveGate.TOFF = 0) (dInner : DynamicCircuit Var n) :
    (dAnchorSwap0ConjGenRaw hW v rData selMux rWork hDW dLoad dFix dInner).count PrimitiveGate.TOFF
      = dInner.count PrimitiveGate.TOFF := by
  unfold dAnchorSwap0ConjGenRaw
  have hM : (DynCircuitExt.measureXResetAndBranch v 18 (swap0Anchor18Reg rWork hW) dFix).count
    PrimitiveGate.TOFF ≤ 0 :=
    DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 18 _ dFix 0
      (fun f ↦ le_of_eq (hFixToff f))
  simp only [DynamicCircuit.count, hLoadToff, cSwap18_count_toff]
  omega

theorem dAnchorSwap0ConjGenRaw_t_le {Var : Type} {n kData mClean mWork : ℕ} (hW : 18 +
    mClean ≤ mWork) (tLoad tFix : ℕ) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n) (hDW : rData.DisjointWires
      rWork) {dLoad : DynamicCircuit Var n}
    {dFix : (Fin 18 → Bool) → DynamicCircuit Var n} (hLoadT : dLoad.count PrimitiveGate.T ≤ tLoad)
    (hFixT : ∀ f, (dFix f).count PrimitiveGate.T ≤ tFix) (dInner : DynamicCircuit Var n) :
    (dAnchorSwap0ConjGenRaw hW v rData selMux rWork hDW dLoad dFix dInner).count PrimitiveGate.T ≤
      (tLoad + tFix) + dInner.count PrimitiveGate.T := by
  unfold dAnchorSwap0ConjGenRaw
  have hM : (DynCircuitExt.measureXResetAndBranch v 18 (swap0Anchor18Reg rWork hW) dFix).count
    PrimitiveGate.T ≤ tFix :=
    DynCircuitExt.count_measureXResetAndBranch_T_le v 18 _ dFix tFix hFixT
  simp only [DynamicCircuit.count, cSwap18_count_t]
  omega

theorem swap0_unclamped_hW {mWork : ℕ} (hW : 236 ≤ mWork) : 18 + 218 ≤ mWork := hW

theorem swap0_clamped_hW {mWork : ℕ} (hW : 242 ≤ mWork) : 18 + 224 ≤ mWork := hW

/-- Unclamped `<= 9,528 + dInner.count .T` (`236 <= mWork`, `0` extra `.TOFF`) `AnchorMux218` +
`SWAP_18(rElec[0], rAnchor18)` conjugation bracket for `Pass 1` (`coinBarrelIdxFast < 218`). -/
noncomputable def dAnchorSwap0Conj218Unclamped {Var : Type} {n kData mWork : ℕ} (hW : 236 ≤ mWork)
    (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n) (hDW : rData.DisjointWires
      rWork) (dInner : DynamicCircuit Var n) : DynamicCircuit Var n
    := lockVal3P (dAnchorSwap0ConjGenRaw (swap0_unclamped_hW hW) v rData selMux rWork hDW
    (dAnchorLoad218Unclamped v (rData.compose selMux) (swap0Anchor18Reg rWork
    (swap0_unclamped_hW hW)) (swap0ScrLoadReg rWork (swap0_unclamped_hW hW))
    (swap0_disj_core_anchor (swap0_unclamped_hW hW) hDW) (swap0_disj_coreAnchor_scrLoad
    (swap0_unclamped_hW hW) hDW)) (fun f ↦ dAnchorPhaseFix218Unclamped f v (rData.compose
    selMux) (swap0ScrFixReg rWork (swap0_unclamped_hW hW)) (swap0_disj_core_scrFix
    (swap0_unclamped_hW hW) hDW)) dInner)

theorem dAnchorSwap0Conj218Unclamped_eq {Var : Type} {n kData mWork : ℕ} (hW : 236 ≤ mWork)
    (v : Var) (rData : QRegister kData n) (selMux : QRegister posCoreWires kData) (rWork : QRegister
      mWork n) (hDW : rData.DisjointWires rWork)
    (dInner : DynamicCircuit Var n) : dAnchorSwap0Conj218Unclamped hW v rData selMux rWork hDW
    dInner = dAnchorSwap0ConjGenRaw (swap0_unclamped_hW hW) v rData selMux rWork hDW
      (dAnchorLoad218Unclamped v (rData.compose selMux) (swap0Anchor18Reg rWork
    (swap0_unclamped_hW hW)) (swap0ScrLoadReg rWork (swap0_unclamped_hW hW)) (swap0_disj_core_anchor
      (swap0_unclamped_hW hW) hDW) (swap0_disj_coreAnchor_scrLoad
    (swap0_unclamped_hW hW) hDW)) (fun f ↦ dAnchorPhaseFix218Unclamped f v (rData.compose
    selMux) (swap0ScrFixReg rWork (swap0_unclamped_hW hW)) (swap0_disj_core_scrFix
      (swap0_unclamped_hW hW) hDW)) dInner := lockVal3P_eq _

theorem dAnchorSwap0Conj218Unclamped_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mWork : ℕ} [NeZero (2 ^ n)]
    (hW : 236 ≤ mWork) (v : Var)
    (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData)
    (rWork : QRegister mWork n)
    (hDW : rData.DisjointWires rWork)
    {uInner : Unitary (2 ^ kData)} {dInner : DynamicCircuit Var n}
    (hInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rData (rWork.slice 18 (mWork - 18) (swap0_work_hRest (swap0_unclamped_hW hW))) uInner dInner)
    (hPres : IsElec0LocalPreserving selMux uInner) :
    let dyn := dAnchorSwap0Conj218Unclamped hW v rData selMux rWork hDW dInner
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rWork
        (HoistedSwapSelectBridge.unitaryConj
          (uSwap0Gen selMux aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv)) uInner) dyn ∧
      dyn.count PrimitiveGate.TOFF = dInner.count PrimitiveGate.TOFF ∧
      dyn.count PrimitiveGate.T ≤ 9528 + dInner.count PrimitiveGate.T := by
  dsimp only
  rw [dAnchorSwap0Conj218Unclamped_eq]
  have hL := dAnchorLoad218Unclamped_spec v (rData.compose selMux)
    (swap0Anchor18Reg rWork (swap0_unclamped_hW hW))
    (swap0ScrLoadReg rWork (swap0_unclamped_hW hW))
    (swap0_disj_core_anchor (swap0_unclamped_hW hW) hDW)
    (swap0_disj_coreAnchor_scrLoad (swap0_unclamped_hW hW) hDW)
  have hF := fun f ↦ dAnchorPhaseFix218Unclamped_spec f v (rData.compose selMux)
    (swap0ScrFixReg rWork (swap0_unclamped_hW hW))
    (swap0_disj_core_scrFix (swap0_unclamped_hW hW) hDW)
  refine ⟨dAnchorSwap0ConjGenRaw_realizes (swap0_unclamped_hW hW) aliasIdx218 (fun _ hv ↦
    aliasIdx218_lt hv) anchorTblVal218Unclamped anchorTblVal218Unclamped_eq_extract v rData
    selMux rWork hDW hL.1 (fun f ↦ (hF f).1) hInner hPres, dAnchorSwap0ConjGenRaw_toff
    (swap0_unclamped_hW hW) v rData selMux rWork hDW hL.2.1 (fun f ↦ (hF f).2.1) dInner,
    dAnchorSwap0ConjGenRaw_t_le (swap0_unclamped_hW hW) 8688 840 v rData selMux rWork hDW
    (le_of_eq hL.2.2) (fun f ↦ (hF f).2.2) dInner⟩

/-- `< 218`-Clamped `<= 9,600 + dInner.count .T` (`242 <= mWork`, `0` extra `.TOFF`) `AnchorMux218`
+
`SWAP_18(rElec[0], rAnchor18)` conjugation bracket for `Pass 2` and `Pass 3` (`idx >= 218` maps to
`E_0`). -/
noncomputable def dAnchorSwap0Conj218 {Var : Type} {n kData mWork : ℕ} (hW : 242 ≤ mWork)
    (v : Var) (rData : QRegister kData n) (selMux : QRegister posCoreWires kData) (rWork : QRegister
      mWork n) (hDW : rData.DisjointWires rWork)
    (dInner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  lockVal3P (dAnchorSwap0ConjGenRaw (swap0_clamped_hW hW) v rData selMux rWork hDW
    (dAnchorLoad218 v (rData.compose selMux) (swap0Anchor18Reg rWork (swap0_clamped_hW hW))
      (swap0ScrLoadReg rWork (swap0_clamped_hW hW)) (swap0_disj_core_anchor (swap0_clamped_hW hW)
        hDW)
      (swap0_disj_coreAnchor_scrLoad (swap0_clamped_hW hW) hDW))
    (fun f ↦ dAnchorPhaseFix218 f v (rData.compose selMux) (swap0ScrFixReg rWork (swap0_clamped_hW
      hW))
      (swap0_disj_core_scrFix (swap0_clamped_hW hW) hDW)) dInner)

theorem dAnchorSwap0Conj218_eq {Var : Type} {n kData mWork : ℕ} (hW : 242 ≤ mWork) (v : Var)
    (rData : QRegister kData n) (selMux : QRegister posCoreWires kData)
    (rWork : QRegister mWork n) (hDW : rData.DisjointWires rWork) (dInner : DynamicCircuit Var n) :
      dAnchorSwap0Conj218 hW v rData selMux rWork hDW dInner =
    dAnchorSwap0ConjGenRaw (swap0_clamped_hW hW) v rData selMux rWork hDW
    (dAnchorLoad218 v (rData.compose selMux) (swap0Anchor18Reg rWork (swap0_clamped_hW hW))
    (swap0ScrLoadReg rWork (swap0_clamped_hW hW)) (swap0_disj_core_anchor (swap0_clamped_hW hW) hDW)
      (swap0_disj_coreAnchor_scrLoad (swap0_clamped_hW hW) hDW))
    (fun f ↦ dAnchorPhaseFix218 f v (rData.compose selMux) (swap0ScrFixReg rWork (swap0_clamped_hW
      hW))
    (swap0_disj_core_scrFix (swap0_clamped_hW hW) hDW)) dInner := lockVal3P_eq _

theorem dAnchorSwap0Conj218_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mWork : ℕ} [NeZero (2 ^ n)] (hW : 242 ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n) (hDW : rData.DisjointWires
      rWork)
    {uInner : Unitary (2 ^ kData)} {dInner : DynamicCircuit Var n}
    (hInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rData (rWork.slice 18 (mWork - 18) (swap0_work_hRest (swap0_clamped_hW hW))) uInner dInner)
    (hPres : IsElec0LocalPreserving selMux uInner) :
    let dyn := dAnchorSwap0Conj218 hW v rData selMux rWork hDW dInner
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rWork
        (HoistedSwapSelectBridge.unitaryConj
          (uSwap0Gen selMux clampIdx218 (fun val _ ↦ clampIdx218_lt val)) uInner) dyn ∧
      dyn.count PrimitiveGate.TOFF = dInner.count PrimitiveGate.TOFF ∧
      dyn.count PrimitiveGate.T ≤ 9600 + dInner.count PrimitiveGate.T := by
  dsimp only
  rw [dAnchorSwap0Conj218_eq]
  have hL := dAnchorLoad218_spec v (rData.compose selMux) (swap0Anchor18Reg rWork (swap0_clamped_hW
    hW))
    (swap0ScrLoadReg rWork (swap0_clamped_hW hW)) (swap0_disj_core_anchor (swap0_clamped_hW hW) hDW)
    (swap0_disj_coreAnchor_scrLoad (swap0_clamped_hW hW) hDW)
  have hF := fun f ↦ dAnchorPhaseFix218_spec f v (rData.compose selMux)
    (swap0ScrFixReg rWork (swap0_clamped_hW hW)) (swap0_disj_core_scrFix (swap0_clamped_hW hW) hDW)
  exact ⟨dAnchorSwap0ConjGenRaw_realizes (swap0_clamped_hW hW) clampIdx218 (fun val _ ↦
    clampIdx218_lt val) anchorTblVal218 anchorTblVal218_eq_extract v rData selMux rWork hDW
    hL.1 (fun f ↦ (hF f).1) hInner hPres, dAnchorSwap0ConjGenRaw_toff (swap0_clamped_hW hW) v
    rData selMux rWork hDW hL.2.1 (fun f ↦ (hF f).2.1) dInner, dAnchorSwap0ConjGenRaw_t_le
    (swap0_clamped_hW hW) 8724 876 v rData selMux rWork hDW (le_of_eq hL.2.2) (fun f ↦ (hF
    f).2.2) dInner⟩

attribute [local irreducible] dAnchorSwap0Conj218Unclamped dAnchorSwap0Conj218

set_option maxRecDepth 512

end ConfigPosSlots24Barrel3Pass
end PosSlots24Barrel3Pass
end
end PosSlots24Barrel3Pass

end QuantumComputation.Specs.StoppingPowerSolution
