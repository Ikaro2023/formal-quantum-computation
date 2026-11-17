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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CleanCoin3Weights
set_option Elab.async false

/-!
# Seam-Fold, `BorrowWide`, and Tight-Coins Spine

Combines Stage-A/B `uSlot0AddFull` boundary-seam cancellation with 9-tier `BorrowWide` Stage-A
(`47,882 T` at `mWork = 194`), 7 `α = 135,598 Ha` 3-coin preparation witnesses, and 10-horizon
Stage-2 tiers `[T9, T1, T6, T5, T6, T2, T3, T3, T0, T1]` at `mWork = 194`
(`stoppingPowerAncillas = 374`, `Q = 4,322`).
-/

@[expose] public section

set_option allowUnsafeReducibility true
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency false

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace TierTightSpine

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
  ModWrapCoarse8PureMomentum.modWrapNeZeroPow2
  PosSlots24BranchConcrete.instNeZeroTwoPow

local instance (priority := 1000000) instNeZeroTwoPowK8 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFast (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

section Part1_ZeroAncAndTightCoins135598

open QuantumComputation
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
open FullSysPrepare6Slot (fullSysCoinIdx)
open MeasureBranchHadamardSem (ket sqrtHalf)
open PosPostPrep80MergedVep (ket_eq_single_local)
open SegmentAndTopClosure (rCleanSubW cleanZeroEmbedIdx compressCleanUnitary)
open ZeroAncillaUSP hiding ket
open ZeroSubwireCoinPrep80 hiding bits4 bits4_0 bits4_1 bits4_2 bits4_3 upd_bits4_0 upd_bits4_1
  upd_bits4_2 upd_bits4_3
open Coin3PerHorizon5799
open CoinPrepSub85AndAlphaOpt
open GqspCleanCoinAndGuardBridge

/-- First-wire Clifford+`T` word `coinU0_15` (`L = 38`). -/
def coinU0_15 : List HSTGate := List.append (α :=
  HSTGate) [.H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T] (List.append (α :=
  HSTGate) [.H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H] (List.append (α :=
  HSTGate) [.T, .H, .T, .S, .S, .H] ((([] : List HSTGate)))))

theorem coinU0_15_eval :
    evalList coinU0_15 matId = ⟨⟨120, 40, 88, -8⟩, ⟨-152, 8, -88, -104⟩, ⟨8, -152, 104, 88⟩, ⟨-40,
      -120, -8, 88⟩, 16⟩ := by
  dsimp only [coinU0_15]
  refine (evalList_append [.H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T] _ ⟨⟨1, 0,
    0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, 0⟩ ⟨⟨-2, 4, -2, 4⟩, ⟨-2, 8, 2, 4⟩, ⟨4, 2, 8,
    -2⟩, ⟨-4, 2, -4, 2⟩, 7⟩ rfl).trans ?_
  refine (evalList_append [.H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H] _ ⟨⟨-2,
    4, -2, 4⟩, ⟨-2, 8, 2, 4⟩, ⟨4, 2, 8, -2⟩, ⟨-4, 2, -4, 2⟩, 7⟩ ⟨⟨-16, -24, 72, 48⟩, ⟨-80, -8, 24,
    -32⟩, ⟨-32, 24, -8, -80⟩, ⟨-48, -72, 24, 16⟩, 14⟩ rfl).trans ?_
  refine (evalList_append [.T, .H, .T, .S, .S, .H] _ ⟨⟨-16, -24, 72, 48⟩, ⟨-80, -8, 24, -32⟩, ⟨-32,
    24, -8, -80⟩, ⟨-48, -72, 24, 16⟩, 14⟩ ⟨⟨120, 40, 88, -8⟩, ⟨-152, 8, -88, -104⟩, ⟨8, -152, 104,
    88⟩, ⟨-40, -120, -8, 88⟩, 16⟩ rfl).trans ?_
  rfl

-- ============================================================================
-- Section 1: Zero-`.tempAnd` 3-Coin Combinator (Affine Stage-3 Bypass)
-- ============================================================================

/-- Predicate certifying that an `AnfLayer3` layer uses no `wCoinAnc` (`b0 && b1`) CNOTs. -/
def isAffineAnf3 (l : AnfLayer3) : Bool :=
  !l.z0 && !l.z1

theorem isAffineAnf3_eq_true_iff (l : AnfLayer3) (h : isAffineAnf3 l = true) :
    l.z0 = false ∧ l.z1 = false := by
  rcases l with ⟨c0, x0, y0, z0, c1, x1, y1, z1⟩
  cases z0
  · cases z1
    · exact ⟨rfl, rfl⟩
    · simp [isAffineAnf3] at h
  · simp [isAffineAnf3] at h

/-- Zero-`.tempAnd` 4-wire `CleanPrepProg 4` running `cStages1To2HGen` followed directly by
  `cAnfMux3`. -/
noncomputable def pCoinPrepZeroAncGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) : CleanPrepProg 4 :=
  CleanPrepProg.seq (.circ (cStages1To2HGen w0 ls2)) (.circ (cAnfMux3 ls3))

/-- Zero-`.tempAnd` 4-wire `CleanPrepProg 4` followed by the `0-T` parity twist `cParity2`. -/
noncomputable def pCoinPrepZeroAncParityGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) : CleanPrepProg 4 :=
  CleanPrepProg.seq (pCoinPrepZeroAncGen w0 ls2 ls3) (.circ cParity2)

theorem tBound_pCoinPrepZeroAncGen_eq
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) :
    (pCoinPrepZeroAncGen w0 ls2 ls3).tBound = (hstWordTCount w0 + ls2.length) + ls3.length := by
  simp [pCoinPrepZeroAncGen, CleanPrepProg.tBound,
    count_t_cStages1To2HGen, count_toff_cStages1To2HGen,
    count_t_cAnfMux3, count_toff_cAnfMux3]

theorem tBound_pCoinPrepZeroAncParityGen_eq
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) :
    (pCoinPrepZeroAncParityGen w0 ls2 ls3).tBound = (hstWordTCount w0 + ls2.length) + ls3.length :=
      by
  have hc : (CleanPrepProg.circ cParity2).tBound = 0 := rfl
  change (pCoinPrepZeroAncGen w0 ls2 ls3).tBound + (CleanPrepProg.circ cParity2).tBound = _
  rw [hc, add_zero, tBound_pCoinPrepZeroAncGen_eq]

theorem not_mem_support_cToggleCoin2Anf_false (c x y : Bool) :
    wCoinAnc ∉ (cToggleCoin2Anf c x y false).support := by
  dsimp only [cToggleCoin2Anf]
  refine not_mem_support_seq_local ?_
    (not_mem_support_seq_local ?_ (not_mem_support_seq_local ?_ ?_))
  · cases c
    · simp
    · exact not_mem_support_x_of_ne (by decide)
  · cases x
    · simp
    · exact not_mem_support_cnot_of_ne _ (by decide) (by decide)
  · cases y
    · simp
    · exact not_mem_support_cnot_of_ne _ (by decide) (by decide)
  · simp

theorem not_mem_support_cAnf3Layer_of_affine (l : AnfLayer3) (hl : isAffineAnf3 l = true) :
    wCoinAnc ∉ (cAnf3Layer l).support := by
  rcases isAffineAnf3_eq_true_iff l hl with ⟨hz0, hz1⟩
  dsimp only [cAnf3Layer]
  rw [hz0, hz1]
  exact not_mem_support_seq_local (not_mem_support_cToggleCoin2Anf_false _ _ _)
    (not_mem_support_seq_local (not_mem_support_hstGate_of_ne .T (by decide))
      (not_mem_support_seq_local (not_mem_support_cToggleCoin2Anf_false _ _ _)
        (not_mem_support_seq_local (not_mem_support_hstGate_of_ne .H (by decide))
          (not_mem_support_cToggleCoin2Anf_false _ _ _))))

theorem not_mem_support_cAnfMux3_of_affine (ls : List AnfLayer3)
    (hAff : ls.all isAffineAnf3 = true) :
    wCoinAnc ∉ (cAnfMux3 ls).support := by
  induction ls with
  | nil => simp [cAnfMux3]
  | cons l rest ih =>
      rw [List.all_cons, Bool.and_eq_true] at hAff
      exact not_mem_support_seq_local
        (not_mem_support_cAnf3Layer_of_affine l hAff.1) (ih hAff.2)

theorem validDyn_pCoinPrepZeroAncGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    (hAff : ls3.all isAffineAnf3 = true) :
    CleanPrepProg.ValidDyn sCoinAnc4 (pCoinPrepZeroAncGen w0 ls2 ls3) :=
  ⟨Finset.disjoint_singleton_right.mpr (not_mem_support_cStages1To2HGen w0 ls2),
   Finset.disjoint_singleton_right.mpr (not_mem_support_cAnfMux3_of_affine ls3 hAff)⟩

theorem validDyn_pCoinPrepZeroAncParityGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    (hAff : ls3.all isAffineAnf3 = true) :
    CleanPrepProg.ValidDyn sCoinAnc4 (pCoinPrepZeroAncParityGen w0 ls2 ls3) :=
  ⟨validDyn_pCoinPrepZeroAncGen w0 ls2 ls3 hAff,
   Finset.disjoint_singleton_right.mpr not_mem_support_cParity2⟩

theorem pCoinPrepZeroAncParityGen_preserves_clean
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) :
    (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 *
        (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1 *
        (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 =
      (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1 *
        (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 := by
  refine preservesCleanSubW_of_preservesWire coinHwa _ fun w hw ↦ ?_
  have hwEq : w = wCoinAnc := by
    ext
    change w.val = 3
    omega
  subst hwEq
  have h1 : PreservesWire wCoinAnc (cStages1To2HGen w0 ls2).eval.1 :=
    PreservesWire.of_not_mem_support (not_mem_support_cStages1To2HGen w0 ls2)
  have h2 : PreservesWire wCoinAnc (cAnfMux3 ls3).eval.1 :=
    preservesWire_cAnfMux3_of_ne ls3 (by decide)
  have h3 : PreservesWire wCoinAnc cParity2.eval.1 := preservesWire_wCoinAnc_cParity2
  simp only [pCoinPrepZeroAncParityGen, pCoinPrepZeroAncGen, CleanPrepProg.toCircuit,
    Circuit.eval_seq, Submonoid.coe_mul]
  exact h3.mul (h2.mul h1)

/-- Compressed 3-qubit coin unitary extracted from `pCoinPrepZeroAncParityGen`. -/
noncomputable def uCoin3ZeroAncParityGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) : Unitary (2 ^ 3) :=
  compressCleanUnitary coinHwa (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval
    (pCoinPrepZeroAncParityGen_preserves_clean w0 ls2 ls3)

theorem cToggleCoin2Anf_false_mulVec_ket_bool (c x y b0 b1 b2 : Bool) :
    (cToggleCoin2Anf c x y false).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) (zmodOfBool b2) 0)) =
      ket (bits4 (zmodOfBool b0) (zmodOfBool b1)
        (zmodOfBool (xor b2 (toggleBoolAnf3 c x y false b0 b1))) 0) := by
  rw [← zmodOfBool_false]
  simp only [cToggleCoin2Anf, MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [cAnfStepC_mulVec_ket, cAnfStepX_mulVec_ket, cAnfStepY_mulVec_ket, cAnfStepZ_mulVec_ket]
  have hbool : xor (xor (xor (xor b2 c) (x && b0)) (y && b1)) (false && false) =
      xor b2 (toggleBoolAnf3 c x y false b0 b1) := by
    revert c x y b0 b1 b2
    decide
  rw [hbool]

theorem cToggleCoin2Anf_false_mulVec_pair (c x y b0 b1 : Bool) (m : Mat2Zw) :
    (cToggleCoin2Anf c x y false).eval.1.mulVec
        (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
          m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0)) =
      (stepToggleBool (toggleBoolAnf3 c x y false b0 b1) m).toMatrix 0 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        (stepToggleBool (toggleBoolAnf3 c x y false b0 b1) m).toMatrix 1 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have h0 := cToggleCoin2Anf_false_mulVec_ket_bool c x y b0 b1 false
  have h1 := cToggleCoin2Anf_false_mulVec_ket_bool c x y b0 b1 true
  rw [zmodOfBool_false] at h0
  rw [zmodOfBool_true] at h1
  rw [h0, h1]
  cases hd : toggleBoolAnf3 c x y false b0 b1
  · rfl
  · have ht0 : (stepToggleBool true m).toMatrix 0 0 = m.toMatrix 1 0 := by
      rw [toMatrix_entry00, toMatrix_entry10]
      rfl
    have ht1 : (stepToggleBool true m).toMatrix 1 0 = m.toMatrix 0 0 := by
      rw [toMatrix_entry10, toMatrix_entry00]
      rfl
    have hz1 : zmodOfBool (xor false true) = 1 := rfl
    have hz0 : zmodOfBool (xor true true) = 0 := rfl
    rw [hz1, hz0, ht0, ht1]
    exact add_comm _ _

theorem cAnf3Layer_affine_mulVec_pair (l : AnfLayer3) (hl : isAffineAnf3 l = true)
    (b0 b1 : Bool) (m : Mat2Zw) :
    (cAnf3Layer l).eval.1.mulVec
        (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
          m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0)) =
      (stepAnf3Layer l b0 b1 m).toMatrix 0 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        (stepAnf3Layer l b0 b1 m).toMatrix 1 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
  rcases isAffineAnf3_eq_true_iff l hl with ⟨hz0, hz1⟩
  dsimp only [cAnf3Layer, stepAnf3Layer]
  rw [hz0, hz1]
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [cToggleCoin2Anf_false_mulVec_pair, hstGateCircuit_wCoin2_anf_mulVec_pair,
    cToggleCoin2Anf_false_mulVec_pair, hstGateCircuit_wCoin2_anf_mulVec_pair,
    cToggleCoin2Anf_false_mulVec_pair]

theorem cAnfMux3_affine_mulVec_pair (ls : List AnfLayer3)
    (hAff : ls.all isAffineAnf3 = true) (b0 b1 : Bool) (m : Mat2Zw) :
    (cAnfMux3 ls).eval.1.mulVec
        (m.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
          m.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0)) =
      (evalAnf3Layers ls b0 b1 m).toMatrix 0 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        (evalAnf3Layers ls b0 b1 m).toMatrix 1 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
  induction ls generalizing m with
  | nil => simp [cAnfMux3, evalAnf3Layers]
  | cons l rest ih =>
      rw [List.all_cons, Bool.and_eq_true] at hAff
      simp only [cAnfMux3, evalAnf3Layers, MeasureBranchHadamardSem.eval_seq_mulVec]
      rw [cAnf3Layer_affine_mulVec_pair l hAff.1, ih hAff.2]

theorem h_then_cAnfMux3_affine_mulVec_ket (ls3 : List AnfLayer3)
    (hAff : ls3.all isAffineAnf3 = true) (b0 b1 : Bool) :
    (Circuit.seq (hstGateCircuit .H wCoin2) (cAnfMux3 ls3)).eval.1.mulVec
        (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) =
      (evalAnf3Layers ls3 b0 b1 matPlus).toMatrix 0 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        (evalAnf3Layers ls3 b0 b1 matPlus).toMatrix 1 0 •
          ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
  have hid : ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) =
      matId.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        matId.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
    have h00 : matId.toMatrix 0 0 = 1 := by simp [matId, Mat2Zw.toMatrix, Zw.toComplex]
    have h10 : matId.toMatrix 1 0 = 0 := by simp [matId, Mat2Zw.toMatrix, Zw.toComplex]
    rw [h00, h10, one_smul, zero_smul, add_zero]
  have hH : (hstGateCircuit .H wCoin2).eval.1.mulVec
      (ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0)) =
      matPlus.toMatrix 0 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 0 0) +
        matPlus.toMatrix 1 0 • ket (bits4 (zmodOfBool b0) (zmodOfBool b1) 1 0) := by
    conv_lhs => rw [hid]
    exact hstGateCircuit_wCoin2_anf_mulVec_pair .H b0 b1 0 matId
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [hH, cAnfMux3_affine_mulVec_pair ls3 hAff b0 b1 matPlus]

theorem pCoinPrepZeroAncGen_mulVec_zero_eq_pCoinPrepGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    (hAff : ls3.all isAffineAnf3 = true) :
    (pCoinPrepZeroAncGen w0 ls2 ls3).toCircuit.eval.1.mulVec (ket (bits4 0 0 0 0)) =
      (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1.mulVec (ket (bits4 0 0 0 0)) := by
  have hne10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  have hSplitZ : (pCoinPrepZeroAncGen w0 ls2 ls3).toCircuit.eval.1 =
      (Circuit.seq (hstGateCircuit .H wCoin2) (cAnfMux3 ls3)).eval.1 *
      ((cStage2Gen ls2).eval.1 * (hstWordCircuit w0 wCoin0).eval.1) := by
    simp only [pCoinPrepZeroAncGen, cStages1To2HGen, CleanPrepProg.toCircuit,
      Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  have hSplitG : (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1 =
      (Circuit.seq (hstGateCircuit .H wCoin2) (pStage3Gen ls3).toCircuit).eval.1 *
      ((cStage2Gen ls2).eval.1 * (hstWordCircuit w0 wCoin0).eval.1) := by
    simp only [pCoinPrepGen, cStages1To2HGen, CleanPrepProg.toCircuit,
      Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hSplitZ, hSplitG]
  simp only [← Matrix.mulVec_mulVec]
  rw [hstWordCircuit_eval_eq_embedMatrix, singleton_embedMatrix_mulVec_ket]
  simp only [bits4_0, ↓reduceIte, upd_bits4_0]
  have hs0 := cStage2Gen_mulVec_ket ls2 false
  have hs1 := cStage2Gen_mulVec_ket ls2 true
  rw [zmodOfBool_false] at hs0
  rw [zmodOfBool_true] at hs1
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hs0, hs1]
  have hz00 := h_then_cAnfMux3_affine_mulVec_ket ls3 hAff false false
  have hz01 := h_then_cAnfMux3_affine_mulVec_ket ls3 hAff false true
  have hz10 := h_then_cAnfMux3_affine_mulVec_ket ls3 hAff true false
  have hz11 := h_then_cAnfMux3_affine_mulVec_ket ls3 hAff true true
  have hp00 := h_then_pStage3Gen_mulVec_ket ls3 false false
  have hp01 := h_then_pStage3Gen_mulVec_ket ls3 false true
  have hp10 := h_then_pStage3Gen_mulVec_ket ls3 true false
  have hp11 := h_then_pStage3Gen_mulVec_ket ls3 true true
  rw [zmodOfBool_false] at hz00 hp00
  rw [zmodOfBool_false, zmodOfBool_true] at hz01 hp01
  rw [zmodOfBool_true, zmodOfBool_false] at hz10 hp10
  rw [zmodOfBool_true] at hz11 hp11
  rw [hz00, hz01, hz10, hz11, hp00, hp01, hp10, hp11]

theorem uCoin3ZeroAncParityGen_col0_eq
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    (hAff : ls3.all isAffineAnf3 = true) (c : Fin 8) :
    (uCoin3ZeroAncParityGen w0 ls2 ls3).1 c 0 = coin3Col0AmpParityGen w0 ls2 ls3 c := by
  rw [← uCoin3ParityGen_col0_eq w0 ls2 ls3 c]
  change (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa c) (cleanZeroEmbedIdx coinHwa 0) =
    (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa c) (cleanZeroEmbedIdx coinHwa 0)
  have hket0 : ket (bits4 0 0 0 0) = Pi.single (cleanZeroEmbedIdx coinHwa 0) (1 : ℂ) := by
    rw [cleanZeroEmbedIdx_coin4_zero_local, ket_eq_single_local]
  have hColZ : (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa c) (cleanZeroEmbedIdx coinHwa 0) =
      ((pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1.mulVec (ket (bits4 0 0 0 0)))
        (cleanZeroEmbedIdx coinHwa c) := by
    rw [hket0]
    exact (congrFun (Matrix.mulVec_single_one
      (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa 0)) (cleanZeroEmbedIdx coinHwa c)).symm
  have hColP : (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa c) (cleanZeroEmbedIdx coinHwa 0) =
      ((pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1.mulVec (ket (bits4 0 0 0 0)))
        (cleanZeroEmbedIdx coinHwa c) := by
    rw [hket0]
    exact (congrFun (Matrix.mulVec_single_one
      (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa 0)) (cleanZeroEmbedIdx coinHwa c)).symm
  rw [hColZ, hColP]
  have hSeqZ : (pCoinPrepZeroAncParityGen w0 ls2 ls3).toCircuit.eval.1 =
      cParity2.eval.1 * (pCoinPrepZeroAncGen w0 ls2 ls3).toCircuit.eval.1 := rfl
  have hSeqP : (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1 =
      cParity2.eval.1 * (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1 := rfl
  rw [hSeqZ, hSeqP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    pCoinPrepZeroAncGen_mulVec_zero_eq_pCoinPrepGen w0 ls2 ls3 hAff]

/-- Turnkey constructor building `Coin3CleanProgSpecOfWeights` from `pCoinPrepZeroAncParityGen`. -/
noncomputable def mkCoin3CleanProgSpecOfZeroAncParityGenWeights
    {wTarget : Fin 6 → ℝ} {α_real err_w : ℝ} {tCoin : ℕ}
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3)
    (hAff : ls3.all isAffineAnf3 = true)
    (hT : (pCoinPrepZeroAncParityGen w0 ls2 ls3).tBound ≤ tCoin)
    (hWeightErr :
      ∑ k : Fin 6,
        |α_real * ‖(uCoin3ZeroAncParityGen w0 ls2 ls3).1 (fullSysCoinIdx k) 0‖ ^ 2 - wTarget k| ≤
          err_w) :
    Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w where
  pPrep := pCoinPrepZeroAncParityGen w0 ls2 ls3
  hT := hT
  hValid := validDyn_pCoinPrepZeroAncParityGen w0 ls2 ls3 hAff
  hClean := pCoinPrepZeroAncParityGen_preserves_clean w0 ls2 ls3
  uCoin := uCoin3ZeroAncParityGen w0 ls2 ls3
  hUCoin := rfl
  hWeightErr := hWeightErr

-- ============================================================================
-- Section 1: Generic 6-Slot Weight Error & Spec Conversion Helpers
-- ============================================================================

theorem ha135598_div1 : (135598 : ℝ) = ((135598 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  norm_num

theorem wIdealRat_eq_div :
    wIdealRat 0 = ((3441613 : ℕ) : ℝ) / ((100 : ℕ) : ℝ) ∧
    wIdealRat 1 = ((51871 : ℕ) : ℝ) / ((125 : ℕ) : ℝ) ∧
    wIdealRat 2 = ((231140195423637 : ℕ) : ℝ) / ((4294967296 : ℕ) : ℝ) ∧
    wIdealRat 3 = ((75557863725914323419136 : ℕ) : ℝ) / ((3754873682634714703 : ℕ) : ℝ) ∧
    wIdealRat 4 = ((115221930763381 : ℕ) : ℝ) / ((4294967296 : ℕ) : ℝ) ∧
    wIdealRat 5 = ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [wIdealRat]
  · norm_num [wIdealRat]
  · norm_num [wIdealRat]
  · norm_num [wIdealRat]
  · norm_num [wIdealRat]
  · norm_num [wIdealRat]

theorem sixSlot_err_of_col0_eq_gen
    {wTarget : Fin 6 → ℝ} {α_real : ℝ}
    {α_nat errNano wn0 wd0 wn1 wd1 wn2 wd2 wn3 wd3 wn4 wd4 wn5 wd5 : ℕ}
    {e0 e1 e2 e3 e4 e5 : ℕ}
    {uCoin : Unitary (2 ^ 3)}
    {w0 : List HSTGate} {ls2 : List AffineLayer2} {ls3 : List AnfLayer3}
    (ha : α_real = ((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ))
    (h4 : uCoin.1 4 0 = coin3Col0AmpParityGen w0 ls2 ls3 4)
    (h5 : uCoin.1 5 0 = coin3Col0AmpParityGen w0 ls2 ls3 5)
    (h0 : uCoin.1 0 0 = coin3Col0AmpParityGen w0 ls2 ls3 0)
    (h6 : uCoin.1 6 0 = coin3Col0AmpParityGen w0 ls2 ls3 6)
    (h1 : uCoin.1 1 0 = coin3Col0AmpParityGen w0 ls2 ls3 1)
    (h7 : uCoin.1 7 0 = coin3Col0AmpParityGen w0 ls2 ls3 7)
    (hw :
      wTarget 0 = ((wn0 : ℕ) : ℝ) / ((wd0 : ℕ) : ℝ) ∧
      wTarget 1 = ((wn1 : ℕ) : ℝ) / ((wd1 : ℕ) : ℝ) ∧
      wTarget 2 = ((wn2 : ℕ) : ℝ) / ((wd2 : ℕ) : ℝ) ∧
      wTarget 3 = ((wn3 : ℕ) : ℝ) / ((wd3 : ℕ) : ℝ) ∧
      wTarget 4 = ((wn4 : ℕ) : ℝ) / ((wd4 : ℕ) : ℝ) ∧
      wTarget 5 = ((wn5 : ℕ) : ℝ) / ((wd5 : ℕ) : ℝ))
    (hk0 : |((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ) *
        ‖coin3Col0AmpGen w0 ls2 ls3 5‖ ^ 2 - ((wn0 : ℕ) : ℝ) / ((wd0 : ℕ) : ℝ)| ≤
      ((e0 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ))
    (hk1 : |((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ) *
        ‖coin3Col0AmpGen w0 ls2 ls3 4‖ ^ 2 - ((wn1 : ℕ) : ℝ) / ((wd1 : ℕ) : ℝ)| ≤
      ((e1 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ))
    (hk2 : |((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ) *
        ‖coin3Col0AmpGen w0 ls2 ls3 0‖ ^ 2 - ((wn2 : ℕ) : ℝ) / ((wd2 : ℕ) : ℝ)| ≤
      ((e2 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ))
    (hk3 : |((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ) *
        ‖coin3Col0AmpGen w0 ls2 ls3 6‖ ^ 2 - ((wn3 : ℕ) : ℝ) / ((wd3 : ℕ) : ℝ)| ≤
      ((e3 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ))
    (hk4 : |((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ) *
        ‖coin3Col0AmpGen w0 ls2 ls3 1‖ ^ 2 - ((wn4 : ℕ) : ℝ) / ((wd4 : ℕ) : ℝ)| ≤
      ((e4 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ))
    (hk5 : |((α_nat : ℕ) : ℝ) / ((1 : ℕ) : ℝ) *
        ‖coin3Col0AmpGen w0 ls2 ls3 7‖ ^ 2 - ((wn5 : ℕ) : ℝ) / ((wd5 : ℕ) : ℝ)| ≤
      ((e5 : ℕ) : ℝ) / ((1000000000 : ℕ) : ℝ))
    (hsum : e0 + e1 + e2 + e3 + e4 + e5 ≤ errNano) :
    ∑ k : Fin 6,
      |α_real * ‖uCoin.1 (fullSysCoinIdx k) 0‖ ^ 2 - wTarget k| ≤
      (((errNano : ℕ) : ℝ) / 1000000000) := by
  have h01 : ∑ k : Fin 6,
      |α_real * ‖uCoin.1 (fullSysCoinIdx k) 0‖ ^ 2 - wTarget k| =
      |α_real * ‖uCoin.1 4 0‖ ^ 2 - wTarget 0| +
      |α_real * ‖uCoin.1 5 0‖ ^ 2 - wTarget 1| +
      |α_real * ‖uCoin.1 0 0‖ ^ 2 - wTarget 2| +
      |α_real * ‖uCoin.1 6 0‖ ^ 2 - wTarget 3| +
      |α_real * ‖uCoin.1 1 0‖ ^ 2 - wTarget 4| +
      |α_real * ‖uCoin.1 7 0‖ ^ 2 - wTarget 5| := by
    rw [Fin.sum_univ_six]
    dsimp only [fullSysCoinIdx]
    simp only [↓reduceIte,
      show (1 : Fin 6) ≠ 0 by decide,
      show (2 : Fin 6) ≠ 0 by decide, show (2 : Fin 6) ≠ 1 by decide,
      show (3 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 1 by decide,
      show (3 : Fin 6) ≠ 2 by decide,
      show (4 : Fin 6) ≠ 0 by decide, show (4 : Fin 6) ≠ 1 by decide,
      show (4 : Fin 6) ≠ 2 by decide, show (4 : Fin 6) ≠ 3 by decide,
      show (5 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 1 by decide,
      show (5 : Fin 6) ≠ 2 by decide, show (5 : Fin 6) ≠ 3 by decide,
      show (5 : Fin 6) ≠ 4 by decide]
  rw [h01, ha, h4, h5, h0, h6, h1, h7, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
    hw.2.2.2.2.1, hw.2.2.2.2.2]
  dsimp only [coin3Col0AmpParityGen]
  have hsumR : (e0 : ℝ) + e1 + e2 + e3 + e4 + e5 ≤ errNano := by exact_mod_cast hsum
  linarith

/-- Convert `Coin3CleanProgSpecOfWeights wIdealRat` directly into `Coin3CleanProgSpec`. -/
def mux2_4 : List AffineLayer2 :=
  List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false, false, false,
    false⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false, true, false, true⟩,
    ⟨true, true, true, true⟩, ⟨true, true, true, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, false, true, false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩,
    ⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true, false⟩, ⟨false, false,
    false, false⟩, ⟨true, true, true, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩,
    ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false,
    true, false, true⟩, ⟨true, true, true, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false, true, false,
    true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false, true,
    true⟩] (([] : List AffineLayer2)))))
theorem mux2_4_0_eval :
    evalMux2Layers mux2_4 false matPlus = ⟨⟨-16000, -15104, -4224, -34816⟩, ⟨128, -2816, 18816,
      8448⟩, ⟨18816, -2816, 128, -8448⟩, ⟨4224, 15104, 16000, -34816⟩, 31⟩ := by
  dsimp only [mux2_4]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩] _ false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0,
    0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-16, 0, -4, -8⟩, ⟨12, 4, 0, -4⟩, ⟨-12, -4, 0, 4⟩, ⟨-16,
    8, 4, 0⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, false, true, false⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true,
    false⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩] _ false ⟨⟨-16, 0, -4, -8⟩, ⟨12,
    4, 0, -4⟩, ⟨-12, -4, 0, 4⟩, ⟨-16, 8, 4, 0⟩, 9⟩ ⟨⟨256, -64, -80, -64⟩, ⟨208, -80, -32, -16⟩,
    ⟨-208, -16, -32, -80⟩, ⟨256, 64, 80, 64⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true,
    true, true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false, true,
    false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩] _ false ⟨⟨256, -64, -80, -64⟩,
    ⟨208, -80, -32, -16⟩, ⟨-208, -16, -32, -80⟩, ⟨256, 64, 80, 64⟩, 17⟩ ⟨⟨-4608, 0, 192, -256⟩,
    ⟨576, -2880, -384, -1856⟩, ⟨-576, -1856, -384, -2880⟩, ⟨-4608, 256, -192, 0⟩, 25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false,
    true, false, true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false,
    true, true⟩] _ false ⟨⟨-4608, 0, 192, -256⟩, ⟨576, -2880, -384, -1856⟩, ⟨-576, -1856, -384,
    -2880⟩, ⟨-4608, 256, -192, 0⟩, 25⟩ ⟨⟨-16000, -15104, -4224, -34816⟩, ⟨128, -2816, 18816, 8448⟩,
    ⟨18816, -2816, 128, -8448⟩, ⟨4224, 15104, 16000, -34816⟩, 31⟩ rfl).trans ?_
  rfl
theorem mux2_4_1_eval :
    evalMux2Layers mux2_4 true matPlus = ⟨⟨23168, 24832, -12416, -7936⟩, ⟨-3712, -11008, 19328,
      -16384⟩, ⟨-19328, 11008, 3712, -16384⟩, ⟨-12416, 24832, 23168, 7936⟩, 31⟩ := by
  dsimp only [mux2_4]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩] _ true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0,
    0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨16, -8, 4, -8⟩, ⟨-4, 4, 8, 4⟩, ⟨-4, -4, -8, -4⟩, ⟨-16,
    -8, 4, -8⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, false, true, false⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true,
    false⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩] _ true ⟨⟨16, -8, 4, -8⟩, ⟨-4, 4,
    8, 4⟩, ⟨-4, -4, -8, -4⟩, ⟨-16, -8, 4, -8⟩, 9⟩ ⟨⟨-128, -160, -112, -96⟩, ⟨-208, 144, 32, -48⟩,
    ⟨-208, 48, -32, -144⟩, ⟨128, -96, -112, -160⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true,
    true, true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false, true,
    false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩] _ true ⟨⟨-128, -160, -112, -96⟩,
    ⟨-208, 144, 32, -48⟩, ⟨-208, 48, -32, -144⟩, ⟨128, -96, -112, -160⟩, 17⟩ ⟨⟨-2944, -384, -2880,
    1024⟩, ⟨-1600, -64, -2688, 2368⟩, ⟨-1600, -2368, 2688, 64⟩, ⟨2944, 1024, -2880, -384⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false,
    true, false, true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, false,
    true, true⟩] _ true ⟨⟨-2944, -384, -2880, 1024⟩, ⟨-1600, -64, -2688, 2368⟩, ⟨-1600, -2368, 2688,
    64⟩, ⟨2944, 1024, -2880, -384⟩, 25⟩ ⟨⟨23168, 24832, -12416, -7936⟩, ⟨-3712, -11008, 19328,
    -16384⟩, ⟨-19328, 11008, 3712, -16384⟩, ⟨-12416, 24832, 23168, 7936⟩, 31⟩ rfl).trans ?_
  rfl
/-- Shared Stage-3 `AnfLayer3` sequence `mux3_4` (`L3 = 34`, `zeroAnc = true`). -/
def mux3_4 : List AnfLayer3 :=
  List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨true, true, true, false,
    true, true, true, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false,
    true, false, true, false, true, false⟩, ⟨false, true, true, false, false, true, true, false⟩,
    ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false,
    false, false⟩, ⟨false, false, false, false, false, false, false, false⟩] (List.append (α :=
    AnfLayer3) [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, false, false,
    true, true, false, false⟩, ⟨false, true, false, false, false, true, false, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨false, false, true, false, false, false, true,
    false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, true, false,
    false, false, true, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, true, false, false, false, true, false⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true,
    true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨false, true, false, false, false, true,
    false, false⟩, ⟨true, false, false, false, true, false, false, false⟩] (List.append (α :=
    AnfLayer3) [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true, false, false,
    true, true, false, false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨true, true,
    true, false, true, true, true, false⟩, ⟨false, false, true, false, false, false, true, false⟩,
    ⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false, true, false,
    true, false⟩, ⟨true, true, true, false, true, true, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨false, true, true, false, false, true, true, false⟩, ⟨true, true, true, false,
    true, false, false, false⟩] (([] : List AnfLayer3))))))
theorem mux3_4_affine : mux3_4.all isAffineAnf3 = true := by
  decide
theorem mux3_4_00_eval :
    evalAnf3Layers mux3_4 false false matPlus = ⟨⟨-41728, -154112, 21760, 31232⟩, ⟨-60160, 54272,
      -27904, -8704⟩, ⟨-27904, 54272, -60160, 8704⟩, ⟨-21760, 154112, 41728, 31232⟩, 35⟩ := by
  dsimp only [mux3_4]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false,
    false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩] _ false false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, -16, -4,
    0⟩, ⟨4, 12, 0, -4⟩, ⟨4, 4, 0, -12⟩, ⟨-8, 0, -4, -16⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨false, true, false, false, false, true, false, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, true, false, false,
    false, true, false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false,
    true, false, false, false, true, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩] _ false false ⟨⟨8, -16, -4, 0⟩, ⟨4, 12, 0, -4⟩, ⟨4, 4, 0, -12⟩, ⟨-8, 0, -4, -16⟩,
    9⟩ ⟨⟨-96, -64, -16, -128⟩, ⟨-112, 48, -256, -144⟩, ⟨-112, 144, 256, -48⟩, ⟨96, -128, -16, -64⟩,
    17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨false, true, false,
    false, false, true, false, false⟩, ⟨true, false, false, false, true, false, false,
    false⟩] _ false false ⟨⟨-96, -64, -16, -128⟩, ⟨-112, 48, -256, -144⟩, ⟨-112, 144, 256, -48⟩,
    ⟨96, -128, -16, -64⟩, 17⟩ ⟨⟨1024, -1664, 2880, 2560⟩, ⟨-192, 1216, -3072, -1984⟩, ⟨192, -1984,
    -3072, 1216⟩, ⟨1024, -2560, -2880, 1664⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨true, false, false, false, true, false, false, false⟩,
    ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, true, false, false, false,
    true, false⟩, ⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ false false ⟨⟨1024, -1664, 2880, 2560⟩, ⟨-192, 1216, -3072, -1984⟩, ⟨192, -1984,
    -3072, 1216⟩, ⟨1024, -2560, -2880, 1664⟩, 25⟩ ⟨⟨-21504, 42496, -10496, 11776⟩, ⟨61696, 28416,
    23040, 30464⟩, ⟨-61696, 30464, 23040, 28416⟩, ⟨-21504, -11776, 10496, -42496⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨true, true,
    true, false, true, false, false, false⟩] _ false false ⟨⟨-21504, 42496, -10496, 11776⟩, ⟨61696,
    28416, 23040, 30464⟩, ⟨-61696, 30464, 23040, 28416⟩, ⟨-21504, -11776, 10496, -42496⟩,
    33⟩ ⟨⟨-41728, -154112, 21760, 31232⟩, ⟨-60160, 54272, -27904, -8704⟩, ⟨-27904, 54272, -60160,
    8704⟩, ⟨-21760, 154112, 41728, 31232⟩, 35⟩ rfl).trans ?_
  rfl
theorem mux3_4_01_eval :
    evalAnf3Layers mux3_4 false true matPlus = ⟨⟨-59136, 33280, 13056, -51200⟩, ⟨77056, 35840,
      134400, -40960⟩, ⟨134400, 35840, 77056, 40960⟩, ⟨-13056, -33280, 59136, -51200⟩, 35⟩ := by
  dsimp only [mux3_4]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false,
    false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩] _ false true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-8, 0, 4,
    8⟩, ⟨4, -12, -8, 12⟩, ⟨4, -12, 8, 12⟩, ⟨8, 8, 4, 0⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨false, true, false, false, false, true, false, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, true, false, false,
    false, true, false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false,
    true, false, false, false, true, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩] _ false true ⟨⟨-8, 0, 4, 8⟩, ⟨4, -12, -8, 12⟩, ⟨4, -12, 8, 12⟩, ⟨8, 8, 4, 0⟩, 9⟩ ⟨⟨160,
    -128, -176, 64⟩, ⟨-208, -80, -64, -16⟩, ⟨-208, 16, 64, 80⟩, ⟨-160, 64, -176, -128⟩,
    17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨false, true, false,
    false, false, true, false, false⟩, ⟨true, false, false, false, true, false, false,
    false⟩] _ false true ⟨⟨160, -128, -176, 64⟩, ⟨-208, -80, -64, -16⟩, ⟨-208, 16, 64, 80⟩, ⟨-160,
    64, -176, -128⟩, 17⟩ ⟨⟨-1408, 1536, 1856, -768⟩, ⟨3776, 1216, 1792, 2496⟩, ⟨-3776, 2496, 1792,
    1216⟩, ⟨-1408, 768, -1856, -1536⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨true, false, false, false, true, false, false, false⟩,
    ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, true, false, false, false,
    true, false⟩, ⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ false true ⟨⟨-1408, 1536, 1856, -768⟩, ⟨3776, 1216, 1792, 2496⟩, ⟨-3776, 2496, 1792,
    1216⟩, ⟨-1408, 768, -1856, -1536⟩, 25⟩ ⟨⟨33280, 45568, -50944, -19456⟩, ⟨-18176, 45824, -512,
    1280⟩, ⟨-18176, -1280, 512, -45824⟩, ⟨-33280, -19456, -50944, 45568⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨true, true,
    true, false, true, false, false, false⟩] _ false true ⟨⟨33280, 45568, -50944, -19456⟩, ⟨-18176,
    45824, -512, 1280⟩, ⟨-18176, -1280, 512, -45824⟩, ⟨-33280, -19456, -50944, 45568⟩, 33⟩ ⟨⟨-59136,
    33280, 13056, -51200⟩, ⟨77056, 35840, 134400, -40960⟩, ⟨134400, 35840, 77056, 40960⟩, ⟨-13056,
    -33280, 59136, -51200⟩, 35⟩ rfl).trans ?_
  rfl
theorem mux3_4_10_eval :
    evalAnf3Layers mux3_4 true false matPlus = ⟨⟨23296, -111104, -26880, -10752⟩, ⟨-112896, -60416,
      3328, -65024⟩, ⟨-3328, 60416, 112896, -65024⟩, ⟨-26880, -111104, 23296, 10752⟩, 35⟩ := by
  dsimp only [mux3_4]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false,
    false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩] _ true false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-4, -12, 0,
    -12⟩, ⟨8, 0, -12, 0⟩, ⟨-8, 0, -12, 0⟩, ⟨-4, 12, 0, 12⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨false, true, false, false, false, true, false, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, true, false, false,
    false, true, false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false,
    true, false, false, false, true, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩] _ true false ⟨⟨-4, -12, 0, -12⟩, ⟨8, 0, -12, 0⟩, ⟨-8, 0, -12, 0⟩, ⟨-4, 12, 0, 12⟩,
    9⟩ ⟨⟨-256, 0, -80, 128⟩, ⟨-48, 48, -160, 112⟩, ⟨48, 112, -160, 48⟩, ⟨-256, -128, 80, 0⟩,
    17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨false, true, false,
    false, false, true, false, false⟩, ⟨true, false, false, false, true, false, false,
    false⟩] _ true false ⟨⟨-256, 0, -80, 128⟩, ⟨-48, 48, -160, 112⟩, ⟨48, 112, -160, 48⟩, ⟨-256,
    -128, 80, 0⟩, 17⟩ ⟨⟨512, 2688, 3648, -2816⟩, ⟨1856, -960, -512, 448⟩, ⟨-1856, 448, -512, -960⟩,
    ⟨512, 2816, -3648, -2688⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨true, false, false, false, true, false, false, false⟩,
    ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, true, false, false, false,
    true, false⟩, ⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ true false ⟨⟨512, 2688, 3648, -2816⟩, ⟨1856, -960, -512, 448⟩, ⟨-1856, 448, -512,
    -960⟩, ⟨512, 2816, -3648, -2688⟩, 25⟩ ⟨⟨22272, 7936, -12288, -47872⟩, ⟨-37888, 25600, -35072,
    47616⟩, ⟨37888, 47616, -35072, 25600⟩, ⟨22272, 47872, 12288, -7936⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨true, true,
    true, false, true, false, false, false⟩] _ true false ⟨⟨22272, 7936, -12288, -47872⟩, ⟨-37888,
    25600, -35072, 47616⟩, ⟨37888, 47616, -35072, 25600⟩, ⟨22272, 47872, 12288, -7936⟩, 33⟩ ⟨⟨23296,
    -111104, -26880, -10752⟩, ⟨-112896, -60416, 3328, -65024⟩, ⟨-3328, 60416, 112896, -65024⟩,
    ⟨-26880, -111104, 23296, 10752⟩, 35⟩ rfl).trans ?_
  rfl
theorem mux3_4_11_eval :
    evalAnf3Layers mux3_4 true true matPlus = ⟨⟨-1280, 143872, 52480, -81920⟩, ⟨42752, -20480,
      -13568, 41984⟩, ⟨13568, 20480, -42752, 41984⟩, ⟨52480, 143872, -1280, 81920⟩, 35⟩ := by
  dsimp only [mux3_4]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false,
    false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩] _ true true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-4, 4, 8,
    12⟩, ⟨8, -8, 12, 0⟩, ⟨-8, 0, 12, -8⟩, ⟨-4, -12, -8, -4⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨false, true, false, false, false, true, false, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, true, false, false,
    false, true, false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false,
    true, false, false, false, true, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩] _ true true ⟨⟨-4, 4, 8, 12⟩, ⟨8, -8, 12, 0⟩, ⟨-8, 0, 12, -8⟩, ⟨-4, -12, -8, -4⟩,
    9⟩ ⟨⟨-192, -32, -144, -32⟩, ⟨16, 240, -32, 112⟩, ⟨-16, 112, -32, 240⟩, ⟨-192, 32, 144, 32⟩,
    17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨false, true, false,
    false, false, true, false, false⟩, ⟨true, false, false, false, true, false, false,
    false⟩] _ true true ⟨⟨-192, -32, -144, -32⟩, ⟨16, 240, -32, 112⟩, ⟨-16, 112, -32, 240⟩, ⟨-192,
    32, 144, 32⟩, 17⟩ ⟨⟨3456, -128, -64, -2176⟩, ⟨1856, -1728, 2048, -2496⟩, ⟨-1856, -2496, 2048,
    -1728⟩, ⟨3456, 2176, 64, 128⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨true, false, false, false, true, false, false, false⟩,
    ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, true, false, false, false,
    true, false⟩, ⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ true true ⟨⟨3456, -128, -64, -2176⟩, ⟨1856, -1728, 2048, -2496⟩, ⟨-1856, -2496, 2048,
    -1728⟩, ⟨3456, 2176, 64, 128⟩, 25⟩ ⟨⟨44800, -28416, -33792, 27904⟩, ⟨33280, 37376, 34048,
    -13824⟩, ⟨33280, 13824, -34048, -37376⟩, ⟨-44800, 27904, -33792, -28416⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨true, true,
    true, false, true, false, false, false⟩] _ true true ⟨⟨44800, -28416, -33792, 27904⟩, ⟨33280,
    37376, 34048, -13824⟩, ⟨33280, 13824, -34048, -37376⟩, ⟨-44800, 27904, -33792, -28416⟩,
    33⟩ ⟨⟨-1280, 143872, 52480, -81920⟩, ⟨42752, -20480, -13568, 41984⟩, ⟨13568, 20480, -42752,
    41984⟩, ⟨52480, 143872, -1280, 81920⟩, 35⟩ rfl).trans ?_
  rfl
abbrev gqsp_sixSlot_err_of_col0_eq_gen := @sixSlot_err_of_col0_eq_gen

/-- Shared Stage-2 `AffineLayer2` sequence `mux2_6` (`L2 = 34`). -/
def mux2_6 : List AffineLayer2 :=
  List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false, false, false,
    false⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩,
    ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨false, false, false,
    false⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨true,
    true, true, true⟩, ⟨false, false, false, false⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false, false, false,
    false⟩, ⟨true, false, true, false⟩, ⟨true, false, true, false⟩, ⟨false, false, false, false⟩,
    ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩,
    ⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false,
    true, false, true⟩, ⟨true, false, true, false⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨false, false, true,
    false⟩] (([] : List AffineLayer2))))))
theorem mux2_6_0_eval :
    evalMux2Layers mux2_6 false matPlus = ⟨⟨-45824, -89600, -12544, 65536⟩, ⟨111872, -31744, 68864,
      38912⟩, ⟨68864, -31744, 111872, -38912⟩, ⟨12544, 89600, 45824, 65536⟩, 35⟩ := by
  dsimp only [mux2_6]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true,
    true⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] _ false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0,
    0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-4, 4, 0, 4⟩, ⟨8, 0, 20, 0⟩, ⟨-8, 0, 20, 0⟩, ⟨-4, -4, 0,
    -4⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨false,
    false, false, false⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] _ false ⟨⟨-4, 4, 0, 4⟩, ⟨8, 0,
    20, 0⟩, ⟨-8, 0, 20, 0⟩, ⟨-4, -4, 0, -4⟩, 9⟩ ⟨⟨-256, -32, 80, 32⟩, ⟨112, -80, 160, 112⟩, ⟨112,
    -112, -160, 80⟩, ⟨256, 32, 80, -32⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨true, false, true, false⟩, ⟨true, false, true, false⟩, ⟨false, false,
    false, false⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] _ false ⟨⟨-256, -32, 80,
    32⟩, ⟨112, -80, 160, 112⟩, ⟨112, -112, -160, 80⟩, ⟨256, 32, 80, -32⟩, 17⟩ ⟨⟨-448, 1728, 640,
    -1088⟩, ⟨0, 3200, -832, -4224⟩, ⟨0, -4224, -832, 3200⟩, ⟨-448, 1088, -640, -1728⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true,
    true, true⟩, ⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩,
    ⟨false, true, false, true⟩, ⟨true, false, true, false⟩] _ false ⟨⟨-448, 1728, 640, -1088⟩, ⟨0,
    3200, -832, -4224⟩, ⟨0, -4224, -832, 3200⟩, ⟨-448, 1088, -640, -1728⟩, 25⟩ ⟨⟨768, -1280, -22016,
    -20224⟩, ⟨8704, 35328, 50944, -61440⟩, ⟨8704, 61440, -50944, -35328⟩, ⟨-768, -20224, -22016,
    -1280⟩, 33⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, false, true,
    false⟩] _ false ⟨⟨768, -1280, -22016, -20224⟩, ⟨8704, 35328, 50944, -61440⟩, ⟨8704, 61440,
    -50944, -35328⟩, ⟨-768, -20224, -22016, -1280⟩, 33⟩ ⟨⟨-45824, -89600, -12544, 65536⟩, ⟨111872,
    -31744, 68864, 38912⟩, ⟨68864, -31744, 111872, -38912⟩, ⟨12544, 89600, 45824, 65536⟩,
    35⟩ rfl).trans ?_
  rfl
theorem mux2_6_1_eval :
    evalMux2Layers mux2_6 true matPlus = ⟨⟨127744, -19968, 4352, -82944⟩, ⟨61184, -71680, 40704,
      14336⟩, ⟨40704, -71680, 61184, -14336⟩, ⟨-4352, 19968, -127744, -82944⟩, 35⟩ := by
  dsimp only [mux2_6]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true,
    true⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] _ true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0,
    0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, -8, 4, 8⟩, ⟨-4, -4, -16, -4⟩, ⟨4, -4, -16, -4⟩, ⟨8, -8,
    -4, 8⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨false,
    false, false, false⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] _ true ⟨⟨8, -8, 4, 8⟩, ⟨-4, -4,
    -16, -4⟩, ⟨4, -4, -16, -4⟩, ⟨8, -8, -4, 8⟩, 9⟩ ⟨⟨-32, -192, 48, 128⟩, ⟨208, 112, -128, 48⟩,
    ⟨208, -48, 128, -112⟩, ⟨32, 128, 48, -192⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨true, false, true, false⟩, ⟨true, false, true, false⟩, ⟨false, false,
    false, false⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] _ true ⟨⟨-32, -192, 48,
    128⟩, ⟨208, 112, -128, 48⟩, ⟨208, -48, 128, -112⟩, ⟨32, 128, 48, -192⟩, 17⟩ ⟨⟨1408, 128, 4800,
    896⟩, ⟨-1728, 1856, -768, 832⟩, ⟨1728, 832, -768, 1856⟩, ⟨1408, -896, -4800, -128⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true,
    true, true⟩, ⟨true, false, true, false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩,
    ⟨false, true, false, true⟩, ⟨true, false, true, false⟩] _ true ⟨⟨1408, 128, 4800, 896⟩, ⟨-1728,
    1856, -768, 832⟩, ⟨1728, 832, -768, 1856⟩, ⟨1408, -896, -4800, -128⟩, 25⟩ ⟨⟨29184, -8704, 33536,
    -2560⟩, ⟨37120, -55040, -46080, -768⟩, ⟨-37120, -768, -46080, -55040⟩, ⟨29184, 2560, -33536,
    8704⟩, 33⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, false, true,
    false⟩] _ true ⟨⟨29184, -8704, 33536, -2560⟩, ⟨37120, -55040, -46080, -768⟩, ⟨-37120, -768,
    -46080, -55040⟩, ⟨29184, 2560, -33536, 8704⟩, 33⟩ ⟨⟨127744, -19968, 4352, -82944⟩, ⟨61184,
    -71680, 40704, 14336⟩, ⟨40704, -71680, 61184, -14336⟩, ⟨-4352, 19968, -127744, -82944⟩,
    35⟩ rfl).trans ?_
  rfl
/-- Shared Stage-3 `AnfLayer3` sequence `mux3_11` (`L3 = 35`, `zeroAnc = false`). -/
def mux3_11 : List AnfLayer3 :=
  List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨true, true, true, false,
    true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩,
    ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false, true, false,
    false, false⟩, ⟨false, true, true, false, false, true, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, false, true, true,
    true, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, false,
    false, true, true, false, false, true⟩, ⟨false, false, false, true, false, false, false, true⟩,
    ⟨true, true, true, false, true, true, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨true, false, false, false, true, false,
    false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨true, false, true, false, true, false, true,
    false⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, true, false, false, false, true, false⟩, ⟨true, false, false, true,
    true, false, false, true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    true, false, false, true, true, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true, true, true,
    true, true⟩, ⟨false, false, true, false, false, false, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨false, true, true, true,
    false, true, true, true⟩, ⟨false, false, true, true, false, false, false,
    true⟩] (([] : List AnfLayer3))))))
theorem mux3_11_00_eval :
    evalAnf3Layers mux3_11 false false matPlus = ⟨⟨-96512, -12544, -128768, -173824⟩, ⟨-59648,
      -15104, 63744, -67840⟩, ⟨-67840, 63744, -15104, -59648⟩, ⟨173824, 128768, 12544, 96512⟩,
      36⟩ := by
  dsimp only [mux3_11]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ false false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨20, 4, 0,
    4⟩, ⟨8, 0, -4, 0⟩, ⟨-8, 0, -4, 0⟩, ⟨20, -4, 0, -4⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, true, true, true, true, true, true⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩,
    ⟨true, true, true, true, true, true, true, true⟩, ⟨true, false, false, true, true, false, false,
    true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, false, true, false,
    false, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩] _ false false ⟨⟨20, 4,
    0, 4⟩, ⟨8, 0, -4, 0⟩, ⟨-8, 0, -4, 0⟩, ⟨20, -4, 0, -4⟩, 9⟩ ⟨⟨144, 16, 224, 80⟩, ⟨0, -224, 48,
    -32⟩, ⟨0, 32, -48, 224⟩, ⟨-144, 80, 224, 16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, false, false, false, false,
    false, false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true,
    false, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true,
    false⟩] _ false false ⟨⟨144, 16, 224, 80⟩, ⟨0, -224, 48, -32⟩, ⟨0, 32, -48, 224⟩, ⟨-144, 80,
    224, 16⟩, 17⟩ ⟨⟨3008, 704, 3968, -704⟩, ⟨-896, 512, 1984, -1664⟩, ⟨-896, 1664, -1984, -512⟩,
    ⟨-3008, -704, 3968, 704⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ false false ⟨⟨3008, 704, 3968, -704⟩, ⟨-896, 512, 1984, -1664⟩, ⟨-896, 1664, -1984,
    -512⟩, ⟨-3008, -704, 3968, 704⟩, 25⟩ ⟨⟨-9472, -11520, -65024, -14592⟩, ⟨4096, 50688, -36608,
    512⟩, ⟨-4096, 512, -36608, 50688⟩, ⟨-9472, 14592, 65024, 11520⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, true, true, false, false, false,
    true⟩] _ false false ⟨⟨-9472, -11520, -65024, -14592⟩, ⟨4096, 50688, -36608, 512⟩, ⟨-4096, 512,
    -36608, 50688⟩, ⟨-9472, 14592, 65024, 11520⟩, 33⟩ ⟨⟨-96512, -12544, -128768, -173824⟩, ⟨-59648,
    -15104, 63744, -67840⟩, ⟨-67840, 63744, -15104, -59648⟩, ⟨173824, 128768, 12544, 96512⟩,
    36⟩ rfl).trans ?_
  rfl
theorem mux3_11_01_eval :
    evalAnf3Layers mux3_11 false true matPlus = ⟨⟨93440, -129792, 88832, 2816⟩, ⟨-150272, -72960,
      -8448, 85248⟩, ⟨-85248, 8448, 72960, 150272⟩, ⟨2816, 88832, -129792, 93440⟩, 36⟩ := by
  dsimp only [mux3_11]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ false true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, 16, -4,
    8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, true, true, true, true, true, true⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩,
    ⟨true, true, true, true, true, true, true, true⟩, ⟨true, false, false, true, true, false, false,
    true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, false, true, false,
    false, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩] _ false true ⟨⟨8, 16,
    -4, 8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ ⟨⟨-112, 16, -128, 208⟩, ⟨32, -224,
    -80, 32⟩, ⟨-32, 32, -80, -224⟩, ⟨-112, -208, 128, -16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, false, false, false, false,
    false, false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true,
    false, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true,
    false⟩] _ false true ⟨⟨-112, 16, -128, 208⟩, ⟨32, -224, -80, 32⟩, ⟨-32, 32, -80, -224⟩, ⟨-112,
    -208, 128, -16⟩, 17⟩ ⟨⟨1152, -1024, 1728, -512⟩, ⟨-960, 3904, 512, 3392⟩, ⟨-960, -3392, -512,
    -3904⟩, ⟨-1152, -512, 1728, -1024⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ false true ⟨⟨1152, -1024, 1728, -512⟩, ⟨-960, 3904, 512, 3392⟩, ⟨-960, -3392, -512,
    -3904⟩, ⟨-1152, -512, 1728, -1024⟩, 25⟩ ⟨⟨40448, -16384, -36608, -24576⟩, ⟨-58624, 34560, 10240,
    -2304⟩, ⟨58624, -2304, 10240, 34560⟩, ⟨40448, 24576, 36608, 16384⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, true, true, false, false, false,
    true⟩] _ false true ⟨⟨40448, -16384, -36608, -24576⟩, ⟨-58624, 34560, 10240, -2304⟩, ⟨58624,
    -2304, 10240, 34560⟩, ⟨40448, 24576, 36608, 16384⟩, 33⟩ ⟨⟨93440, -129792, 88832, 2816⟩,
    ⟨-150272, -72960, -8448, 85248⟩, ⟨-85248, 8448, 72960, 150272⟩, ⟨2816, 88832, -129792, 93440⟩,
    36⟩ rfl).trans ?_
  rfl
theorem mux3_11_10_eval :
    evalAnf3Layers mux3_11 true false matPlus = ⟨⟨-196864, 63232, 40192, -768⟩, ⟨-8448, -114432,
      -102144, 27392⟩, ⟨27392, -102144, -114432, -8448⟩, ⟨768, -40192, -63232, 196864⟩, 36⟩ := by
  dsimp only [mux3_11]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ true false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, 16, -4,
    8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, true, true, true, true, true, true⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩,
    ⟨true, true, true, true, true, true, true, true⟩, ⟨true, false, false, true, true, false, false,
    true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, false, true, false,
    false, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩] _ true false ⟨⟨8, 16,
    -4, 8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ ⟨⟨-80, -48, -64, -176⟩, ⟨96, 256,
    -112, 0⟩, ⟨-96, 0, -112, 256⟩, ⟨-80, 176, 64, 48⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, false, false, false, false,
    false, false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true,
    false, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true,
    false⟩] _ true false ⟨⟨-80, -48, -64, -176⟩, ⟨96, 256, -112, 0⟩, ⟨-96, 0, -112, 256⟩, ⟨-80, 176,
    64, 48⟩, 17⟩ ⟨⟨576, -3520, -1792, -448⟩, ⟨-1920, 3200, 1472, -1152⟩, ⟨-1920, 1152, -1472,
    -3200⟩, ⟨-576, -448, -1792, -3520⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ true false ⟨⟨576, -3520, -1792, -448⟩, ⟨-1920, 3200, 1472, -1152⟩, ⟨-1920, 1152,
    -1472, -3200⟩, ⟨-576, -448, -1792, -3520⟩, 25⟩ ⟨⟨56320, 15872, 37120, 29696⟩, ⟨-32512, -27392,
    28672, -16640⟩, ⟨-32512, 16640, -28672, 27392⟩, ⟨-56320, 29696, 37120, 15872⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, true, true, false, false, false,
    true⟩] _ true false ⟨⟨56320, 15872, 37120, 29696⟩, ⟨-32512, -27392, 28672, -16640⟩, ⟨-32512,
    16640, -28672, 27392⟩, ⟨-56320, 29696, 37120, 15872⟩, 33⟩ ⟨⟨-196864, 63232, 40192, -768⟩,
    ⟨-8448, -114432, -102144, 27392⟩, ⟨27392, -102144, -114432, -8448⟩, ⟨768, -40192, -63232,
    196864⟩, 36⟩ rfl).trans ?_
  rfl
theorem mux3_11_11_eval :
    evalAnf3Layers mux3_11 true true matPlus = ⟨⟨19200, 30976, -154368, -131328⟩, ⟨61184, 25344,
      -97024, 111872⟩, ⟨-111872, 97024, -25344, -61184⟩, ⟨-131328, -154368, 30976, 19200⟩, 36⟩ := by
  dsimp only [mux3_11]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ true true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, -8, 4,
    -16⟩, ⟨4, 4, -8, -4⟩, ⟨4, 4, 8, -4⟩, ⟨-8, -16, 4, -8⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, true, true, true, true, true, true⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩,
    ⟨true, true, true, true, true, true, true, true⟩, ⟨true, false, false, true, true, false, false,
    true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, false, true, false,
    false, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩] _ true true ⟨⟨8, -8, 4,
    -16⟩, ⟨4, 4, -8, -4⟩, ⟨4, 4, 8, -4⟩, ⟨-8, -16, 4, -8⟩, 9⟩ ⟨⟨16, 16, 128, -272⟩, ⟨-128, -32, 80,
    128⟩, ⟨-128, -128, -80, 32⟩, ⟨-16, -272, 128, 16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, true, false, false, true, true, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, false, false, false, false,
    false, false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true,
    false, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, true,
    false⟩] _ true true ⟨⟨16, 16, 128, -272⟩, ⟨-128, -32, 80, 128⟩, ⟨-128, -128, -80, 32⟩, ⟨-16,
    -272, 128, 16⟩, 17⟩ ⟨⟨-384, -1408, 2112, -1280⟩, ⟨3392, 1088, -3456, -832⟩, ⟨3392, 832, 3456,
    -1088⟩, ⟨384, -1280, 2112, -1408⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ true true ⟨⟨-384, -1408, 2112, -1280⟩, ⟨3392, 1088, -3456, -832⟩, ⟨3392, 832, 3456,
    -1088⟩, ⟨384, -1280, 2112, -1408⟩, 25⟩ ⟨⟨51968, -13568, 23552, 43776⟩, ⟨-13824, 12288, 37120,
    38912⟩, ⟨-13824, -38912, -37120, -12288⟩, ⟨-51968, 43776, 23552, -13568⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, true, true, false, false, false,
    true⟩] _ true true ⟨⟨51968, -13568, 23552, 43776⟩, ⟨-13824, 12288, 37120, 38912⟩, ⟨-13824,
    -38912, -37120, -12288⟩, ⟨-51968, 43776, 23552, -13568⟩, 33⟩ ⟨⟨19200, 30976, -154368, -131328⟩,
    ⟨61184, 25344, -97024, 111872⟩, ⟨-111872, 97024, -25344, -61184⟩, ⟨-131328, -154368, 30976,
    19200⟩, 36⟩ rfl).trans ?_
  rfl
/-- Shared Stage-2 `AffineLayer2` sequence `mux2_8` (`L2 = 36`). -/
def mux2_8 : List AffineLayer2 :=
  List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, true, true,
    true⟩, ⟨true, false, true, false⟩, ⟨false, false, false, false⟩, ⟨true, false, true, false⟩,
    ⟨true, false, true, false⟩, ⟨true, true, true, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩,
    ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨false, true,
    false, true⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false, false, false,
    false⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩,
    ⟨false, false, false, false⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false, false, false,
    false⟩, ⟨true, true, true, true⟩, ⟨true, false, true, false⟩, ⟨false, true, false, true⟩,
    ⟨false, false, false, false⟩, ⟨false, false, false, false⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩,
    ⟨true, false, true, true⟩] (([] : List AffineLayer2))))))
theorem mux2_8_0_eval :
    evalMux2Layers mux2_8 false matPlus = ⟨⟨4608, -167936, 152576, 206848⟩, ⟨135168, 19968, 74240,
      137728⟩, ⟨135168, -137728, -74240, -19968⟩, ⟨-4608, 206848, 152576, -167936⟩, 37⟩ := by
  dsimp only [mux2_8]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨true, false, true, false⟩, ⟨false, false, false, false⟩, ⟨true, false, true,
    false⟩, ⟨true, false, true, false⟩, ⟨true, true, true, true⟩] _ false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0,
    0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨0, 16, -4, 8⟩, ⟨12, 4, 0, -4⟩, ⟨-12, -4, 0, 4⟩, ⟨0, -8, 4,
    -16⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩,
    ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] _ false ⟨⟨0, 16, -4, 8⟩, ⟨12, 4, 0, -4⟩,
    ⟨-12, -4, 0, 4⟩, ⟨0, -8, 4, -16⟩, 9⟩ ⟨⟨32, -224, 80, -64⟩, ⟨-176, -80, -160, 80⟩, ⟨-176, -80,
    160, 80⟩, ⟨-32, -64, 80, -224⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, false, true,
    false⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩] _ false ⟨⟨32, -224, 80, -64⟩,
    ⟨-176, -80, -160, 80⟩, ⟨-176, -80, 160, 80⟩, ⟨-32, -64, 80, -224⟩, 17⟩ ⟨⟨1472, 2240, -1152,
    2752⟩, ⟨1536, 3840, 320, 512⟩, ⟨-1536, 512, 320, 3840⟩, ⟨1472, -2752, 1152, -2240⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false,
    false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true, false⟩, ⟨false, true, false,
    true⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩] _ false ⟨⟨1472, 2240, -1152,
    2752⟩, ⟨1536, 3840, 320, 512⟩, ⟨-1536, 512, 320, 3840⟩, ⟨1472, -2752, 1152, -2240⟩, 25⟩ ⟨⟨22016,
    12288, 58112, -46592⟩, ⟨-18688, -42240, -3584, -16128⟩, ⟨-18688, 16128, 3584, 42240⟩, ⟨-22016,
    -46592, 58112, 12288⟩, 33⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true,
    false, true⟩, ⟨true, false, true, true⟩] _ false ⟨⟨22016, 12288, 58112, -46592⟩, ⟨-18688,
    -42240, -3584, -16128⟩, ⟨-18688, 16128, 3584, 42240⟩, ⟨-22016, -46592, 58112, 12288⟩,
    33⟩ ⟨⟨4608, -167936, 152576, 206848⟩, ⟨135168, 19968, 74240, 137728⟩, ⟨135168, -137728, -74240,
    -19968⟩, ⟨-4608, 206848, 152576, -167936⟩, 37⟩ rfl).trans ?_
  rfl
theorem mux2_8_1_eval :
    evalMux2Layers mux2_8 true matPlus = ⟨⟨-137216, -152064, -135680, -136704⟩, ⟨99840, 27648,
      -138240, 168960⟩, ⟨-99840, 168960, -138240, 27648⟩, ⟨-137216, 136704, 135680, 152064⟩, 37⟩ :=
      by
  dsimp only [mux2_8]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨true, false, true, false⟩, ⟨false, false, false, false⟩, ⟨true, false, true,
    false⟩, ⟨true, false, true, false⟩, ⟨true, true, true, true⟩] _ true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0,
    0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, -16, -4, -8⟩, ⟨-4, 4, -8, -4⟩, ⟨-4, 4, 8, -4⟩, ⟨-8, -8,
    -4, -16⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false, true, false, true⟩,
    ⟨false, true, false, true⟩, ⟨false, true, false, true⟩] _ true ⟨⟨8, -16, -4, -8⟩, ⟨-4, 4, -8,
    -4⟩, ⟨-4, 4, 8, -4⟩, ⟨-8, -8, -4, -16⟩, 9⟩ ⟨⟨192, -224, -48, -32⟩, ⟨-16, -48, -160, -112⟩, ⟨16,
    -112, -160, -48⟩, ⟨192, 32, 48, 224⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨false,
    false, false, false⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, false, true,
    false⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩] _ true ⟨⟨192, -224, -48, -32⟩,
    ⟨-16, -48, -160, -112⟩, ⟨16, -112, -160, -48⟩, ⟨192, 32, 48, 224⟩, 17⟩ ⟨⟨-1664, -768, 3136,
    -896⟩, ⟨1088, 2496, -2432, -2496⟩, ⟨-1088, -2496, -2432, 2496⟩, ⟨-1664, 896, -3136, 768⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨false,
    false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true, false⟩, ⟨false, true, false,
    true⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩] _ true ⟨⟨-1664, -768, 3136,
    -896⟩, ⟨1088, 2496, -2432, -2496⟩, ⟨-1088, -2496, -2432, 2496⟩, ⟨-1664, 896, -3136, 768⟩,
    25⟩ ⟨⟨-44288, -12032, 37888, 9984⟩, ⟨7168, 36864, -57600, -14848⟩, ⟨-7168, -14848, -57600,
    36864⟩, ⟨-44288, -9984, -37888, 12032⟩, 33⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true,
    false, true⟩, ⟨true, false, true, true⟩] _ true ⟨⟨-44288, -12032, 37888, 9984⟩, ⟨7168, 36864,
    -57600, -14848⟩, ⟨-7168, -14848, -57600, 36864⟩, ⟨-44288, -9984, -37888, 12032⟩, 33⟩ ⟨⟨-137216,
    -152064, -135680, -136704⟩, ⟨99840, 27648, -138240, 168960⟩, ⟨-99840, 168960, -138240, 27648⟩,
    ⟨-137216, 136704, 135680, 152064⟩, 37⟩ rfl).trans ?_
  rfl
/-- Shared Stage-3 `AnfLayer3` sequence `mux3_13` (`L3 = 35`, `zeroAnc = false`). -/
def mux3_13 : List AnfLayer3 :=
  List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨true, true, false, true,
    true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩,
    ⟨false, true, false, true, false, true, false, true⟩, ⟨true, false, true, true, true, false,
    true, true⟩, ⟨false, true, true, false, false, true, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, true, false,
    true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩,
    ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false, true, false, false,
    false, true⟩, ⟨true, true, false, true, true, true, false, true⟩] (List.append (α :=
    AnfLayer3) [⟨false, true, false, true, false, true, false, true⟩, ⟨false, false, true, true,
    false, false, true, true⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨true, false, false, false, true, false,
    false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, false, true, false, false, false, true⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    true, false, false, true, true, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, true, true, true,
    true, true, true⟩, ⟨false, false, false, true, false, false, false, true⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨false, true, true, true,
    false, true, true, true⟩, ⟨false, false, false, false, false, false, false,
    true⟩] (([] : List AnfLayer3))))))
theorem mux3_13_00_eval :
    evalAnf3Layers mux3_13 false false matPlus = ⟨⟨-96512, -12544, -128768, -173824⟩, ⟨-59648,
      -15104, 63744, -67840⟩, ⟨-67840, 63744, -15104, -59648⟩, ⟨173824, 128768, 12544, 96512⟩,
      36⟩ := by
  dsimp only [mux3_13]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨true, false, true, true,
    true, false, true, true⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ false false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨20, 4, 0,
    4⟩, ⟨8, 0, -4, 0⟩, ⟨-8, 0, -4, 0⟩, ⟨20, -4, 0, -4⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, true, false, true, false,
    true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false, true,
    false, false, false, true⟩, ⟨true, true, false, true, true, true, false,
    true⟩] _ false false ⟨⟨20, 4, 0, 4⟩, ⟨8, 0, -4, 0⟩, ⟨-8, 0, -4, 0⟩, ⟨20, -4, 0, -4⟩, 9⟩ ⟨⟨144,
    16, 224, 80⟩, ⟨0, -224, 48, -32⟩, ⟨0, 32, -48, 224⟩, ⟨-144, 80, 224, 16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, true, true, false, false, true, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ false false ⟨⟨144, 16, 224, 80⟩, ⟨0, -224, 48, -32⟩, ⟨0, 32, -48, 224⟩, ⟨-144, 80, 224,
    16⟩, 17⟩ ⟨⟨3008, 704, 3968, -704⟩, ⟨-896, 512, 1984, -1664⟩, ⟨-896, 1664, -1984, -512⟩, ⟨-3008,
    -704, 3968, 704⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, true, false, false, false, true⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, true,
    true, true, true, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ false false ⟨⟨3008, 704, 3968, -704⟩, ⟨-896, 512, 1984, -1664⟩, ⟨-896, 1664, -1984,
    -512⟩, ⟨-3008, -704, 3968, 704⟩, 25⟩ ⟨⟨-9472, -11520, -65024, -14592⟩, ⟨4096, 50688, -36608,
    512⟩, ⟨-4096, 512, -36608, 50688⟩, ⟨-9472, 14592, 65024, 11520⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, false, false, false, false, false,
    true⟩] _ false false ⟨⟨-9472, -11520, -65024, -14592⟩, ⟨4096, 50688, -36608, 512⟩, ⟨-4096, 512,
    -36608, 50688⟩, ⟨-9472, 14592, 65024, 11520⟩, 33⟩ ⟨⟨-96512, -12544, -128768, -173824⟩, ⟨-59648,
    -15104, 63744, -67840⟩, ⟨-67840, 63744, -15104, -59648⟩, ⟨173824, 128768, 12544, 96512⟩,
    36⟩ rfl).trans ?_
  rfl
theorem mux3_13_01_eval :
    evalAnf3Layers mux3_13 false true matPlus = ⟨⟨-98560, 14080, 79104, -124672⟩, ⟨69376, 132352,
      113920, -41216⟩, ⟨-41216, 113920, 132352, 69376⟩, ⟨124672, -79104, -14080, 98560⟩, 36⟩ := by
  dsimp only [mux3_13]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨true, false, true, true,
    true, false, true, true⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ false true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨4, 4, 8,
    -12⟩, ⟨0, -8, 12, 8⟩, ⟨0, -8, -12, 8⟩, ⟨-4, -12, 8, 4⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, true, false, true, false,
    true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false, true,
    false, false, false, true⟩, ⟨true, true, false, true, true, true, false,
    true⟩] _ false true ⟨⟨4, 4, 8, -12⟩, ⟨0, -8, 12, 8⟩, ⟨0, -8, -12, 8⟩, ⟨-4, -12, 8, 4⟩,
    9⟩ ⟨⟨-256, 0, -80, -96⟩, ⟨112, 176, -64, -48⟩, ⟨-112, -48, -64, 176⟩, ⟨-256, 96, 80, 0⟩,
    17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, true, true, false, false, true, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ false true ⟨⟨-256, 0, -80, -96⟩, ⟨112, 176, -64, -48⟩, ⟨-112, -48, -64, 176⟩, ⟨-256,
    96, 80, 0⟩, 17⟩ ⟨⟨1664, 1152, -320, 2944⟩, ⟨832, 576, 1536, 4160⟩, ⟨-832, 4160, 1536, 576⟩,
    ⟨1664, -2944, 320, -1152⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, true, false, false, false, true⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, true,
    true, true, true, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ false true ⟨⟨1664, 1152, -320, 2944⟩, ⟨832, 576, 1536, 4160⟩, ⟨-832, 4160, 1536, 576⟩,
    ⟨1664, -2944, 320, -1152⟩, 25⟩ ⟨⟨14336, -20480, -50432, 44032⟩, ⟨24832, 4352, -15872, -50944⟩,
    ⟨24832, 50944, 15872, -4352⟩, ⟨-14336, 44032, -50432, -20480⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, false, false, false, false, false,
    true⟩] _ false true ⟨⟨14336, -20480, -50432, 44032⟩, ⟨24832, 4352, -15872, -50944⟩, ⟨24832,
    50944, 15872, -4352⟩, ⟨-14336, 44032, -50432, -20480⟩, 33⟩ ⟨⟨-98560, 14080, 79104, -124672⟩,
    ⟨69376, 132352, 113920, -41216⟩, ⟨-41216, 113920, 132352, 69376⟩, ⟨124672, -79104, -14080,
    98560⟩, 36⟩ rfl).trans ?_
  rfl
theorem mux3_13_10_eval :
    evalAnf3Layers mux3_13 true false matPlus = ⟨⟨-196864, 63232, 40192, -768⟩, ⟨-8448, -114432,
      -102144, 27392⟩, ⟨27392, -102144, -114432, -8448⟩, ⟨768, -40192, -63232, 196864⟩, 36⟩ := by
  dsimp only [mux3_13]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨true, false, true, true,
    true, false, true, true⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ true false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, 16, -4,
    8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, true, false, true, false,
    true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false, true,
    false, false, false, true⟩, ⟨true, true, false, true, true, true, false,
    true⟩] _ true false ⟨⟨8, 16, -4, 8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ ⟨⟨-80,
    -48, -64, -176⟩, ⟨96, 256, -112, 0⟩, ⟨-96, 0, -112, 256⟩, ⟨-80, 176, 64, 48⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, true, true, false, false, true, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ true false ⟨⟨-80, -48, -64, -176⟩, ⟨96, 256, -112, 0⟩, ⟨-96, 0, -112, 256⟩, ⟨-80, 176,
    64, 48⟩, 17⟩ ⟨⟨576, -3520, -1792, -448⟩, ⟨-1920, 3200, 1472, -1152⟩, ⟨-1920, 1152, -1472,
    -3200⟩, ⟨-576, -448, -1792, -3520⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, true, false, false, false, true⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, true,
    true, true, true, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ true false ⟨⟨576, -3520, -1792, -448⟩, ⟨-1920, 3200, 1472, -1152⟩, ⟨-1920, 1152, -1472,
    -3200⟩, ⟨-576, -448, -1792, -3520⟩, 25⟩ ⟨⟨56320, 15872, 37120, 29696⟩, ⟨-32512, -27392, 28672,
    -16640⟩, ⟨-32512, 16640, -28672, 27392⟩, ⟨-56320, 29696, 37120, 15872⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, false, false, false, false, false,
    true⟩] _ true false ⟨⟨56320, 15872, 37120, 29696⟩, ⟨-32512, -27392, 28672, -16640⟩, ⟨-32512,
    16640, -28672, 27392⟩, ⟨-56320, 29696, 37120, 15872⟩, 33⟩ ⟨⟨-196864, 63232, 40192, -768⟩,
    ⟨-8448, -114432, -102144, 27392⟩, ⟨27392, -102144, -114432, -8448⟩, ⟨768, -40192, -63232,
    196864⟩, 36⟩ rfl).trans ?_
  rfl
theorem mux3_13_11_eval :
    evalAnf3Layers mux3_13 true true matPlus = ⟨⟨19200, 30976, -154368, -131328⟩, ⟨61184, 25344,
      -97024, 111872⟩, ⟨-111872, 97024, -25344, -61184⟩, ⟨-131328, -154368, 30976, 19200⟩, 36⟩ := by
  dsimp only [mux3_13]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨true, false, true, true,
    true, false, true, true⟩, ⟨false, true, true, false, false, true, true, false⟩] _ true true ⟨⟨1,
    0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, -8, 4, -16⟩, ⟨4, 4, -8, -4⟩, ⟨4, 4,
    8, -4⟩, ⟨-8, -16, 4, -8⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, true, false, true, false,
    true, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨false, false, false, true,
    false, false, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩] _ true true ⟨⟨8,
    -8, 4, -16⟩, ⟨4, 4, -8, -4⟩, ⟨4, 4, 8, -4⟩, ⟨-8, -16, 4, -8⟩, 9⟩ ⟨⟨16, 16, 128, -272⟩, ⟨-128,
    -32, 80, 128⟩, ⟨-128, -128, -80, 32⟩, ⟨-16, -272, 128, 16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, true, true, false, false, true, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨true, false, true, false, true, false, true, false⟩, ⟨true, false,
    false, false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ true true ⟨⟨16, 16, 128, -272⟩, ⟨-128, -32, 80, 128⟩, ⟨-128, -128, -80, 32⟩, ⟨-16,
    -272, 128, 16⟩, 17⟩ ⟨⟨-384, -1408, 2112, -1280⟩, ⟨3392, 1088, -3456, -832⟩, ⟨3392, 832, 3456,
    -1088⟩, ⟨384, -1280, 2112, -1408⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, true, false, false, false, true⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, true,
    true, true, true, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ true true ⟨⟨-384, -1408, 2112, -1280⟩, ⟨3392, 1088, -3456, -832⟩, ⟨3392, 832, 3456,
    -1088⟩, ⟨384, -1280, 2112, -1408⟩, 25⟩ ⟨⟨51968, -13568, 23552, 43776⟩, ⟨-13824, 12288, 37120,
    38912⟩, ⟨-13824, -38912, -37120, -12288⟩, ⟨-51968, 43776, 23552, -13568⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, true, true, false, true, true, true⟩, ⟨false, false, false, false, false, false, false,
    true⟩] _ true true ⟨⟨51968, -13568, 23552, 43776⟩, ⟨-13824, 12288, 37120, 38912⟩, ⟨-13824,
    -38912, -37120, -12288⟩, ⟨-51968, 43776, 23552, -13568⟩, 33⟩ ⟨⟨19200, 30976, -154368, -131328⟩,
    ⟨61184, 25344, -97024, 111872⟩, ⟨-111872, 97024, -25344, -61184⟩, ⟨-131328, -154368, 30976,
    19200⟩, 36⟩ rfl).trans ?_
  rfl
/-- Shared Stage-2 `AffineLayer2` sequence `mux2_5` (`L2 = 30`). -/
def mux2_5 : List AffineLayer2 :=
  List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true,
    false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨true,
    false, true, false⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨true, false, true, false⟩, ⟨true, true, true,
    true⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false,
    false, false, false⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨true, false, true,
    false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩,
    ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] (List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, true, true,
    true⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩] (([] : List AffineLayer2)))))
theorem mux2_5_0_eval :
    evalMux2Layers mux2_5 false matPlus = ⟨⟨-10624, -38144, 9344, -7680⟩, ⟨-14976, -8448, 11392,
      2816⟩, ⟨11392, -8448, -14976, -2816⟩, ⟨-9344, 38144, 10624, -7680⟩, 31⟩ := by
  dsimp only [mux2_5]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true,
    false, true, false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩, ⟨true, false, true, false⟩, ⟨false, true, false, true⟩] _ false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0,
    0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨12, 4, -8, 4⟩, ⟨0, 0, 4, 16⟩, ⟨0, 16, 4, 0⟩, ⟨12, -4, 8,
    -4⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨true, false, true, false⟩, ⟨true,
    true, true, true⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩] _ false ⟨⟨12, 4, -8, 4⟩, ⟨0, 0,
    4, 16⟩, ⟨0, 16, 4, 0⟩, ⟨12, -4, 8, -4⟩, 9⟩ ⟨⟨112, 48, -96, -48⟩, ⟨96, -256, -144, 96⟩, ⟨-96, 96,
    -144, -256⟩, ⟨112, 48, 96, -48⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨true,
    false, true, false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] _ false ⟨⟨112, 48, -96,
    -48⟩, ⟨96, -256, -144, 96⟩, ⟨-96, 96, -144, -256⟩, ⟨112, 48, 96, -48⟩, 17⟩ ⟨⟨576, 448, -4352,
    192⟩, ⟨-2432, -2688, 704, -640⟩, ⟨2432, -640, 704, -2688⟩, ⟨576, -192, 4352, -448⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩] _ false ⟨⟨576, 448, -4352, 192⟩, ⟨-2432, -2688, 704, -640⟩, ⟨2432, -640, 704, -2688⟩,
    ⟨576, -192, 4352, -448⟩, 25⟩ ⟨⟨-10624, -38144, 9344, -7680⟩, ⟨-14976, -8448, 11392, 2816⟩,
    ⟨11392, -8448, -14976, -2816⟩, ⟨-9344, 38144, 10624, -7680⟩, 31⟩ rfl).trans ?_
  rfl
theorem mux2_5_1_eval :
    evalMux2Layers mux2_5 true matPlus = ⟨⟨-18304, -12544, -29312, 4352⟩, ⟨19328, -11008, -3712,
      16384⟩, ⟨-3712, -11008, 19328, -16384⟩, ⟨29312, 12544, 18304, 4352⟩, 31⟩ := by
  dsimp only [mux2_5]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true,
    false, true, false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩, ⟨true, false, true, false⟩, ⟨false, true, false, true⟩] _ true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0,
    0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨20, -4, 0, -4⟩, ⟨8, 0, -4, 0⟩, ⟨8, 0, 4, 0⟩, ⟨-20, -4, 0,
    -4⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨true, false, true, false⟩, ⟨true,
    true, true, true⟩, ⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩] _ true ⟨⟨20, -4, 0, -4⟩, ⟨8, 0,
    -4, 0⟩, ⟨8, 0, 4, 0⟩, ⟨-20, -4, 0, -4⟩, 9⟩ ⟨⟨-48, -144, -128, 272⟩, ⟨0, -32, -112, 64⟩, ⟨0, -64,
    112, 32⟩, ⟨48, 272, -128, -144⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨true,
    false, true, false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] _ true ⟨⟨-48, -144, -128,
    272⟩, ⟨0, -32, -112, 64⟩, ⟨0, -64, 112, 32⟩, ⟨48, 272, -128, -144⟩, 17⟩ ⟨⟨-2560, 128, 576,
    1024⟩, ⟨-1984, 576, -4608, -320⟩, ⟨-1984, 320, 4608, -576⟩, ⟨2560, 1024, 576, 128⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨true, true, true,
    true⟩] _ true ⟨⟨-2560, 128, 576, 1024⟩, ⟨-1984, 576, -4608, -320⟩, ⟨-1984, 320, 4608, -576⟩,
    ⟨2560, 1024, 576, 128⟩, 25⟩ ⟨⟨-18304, -12544, -29312, 4352⟩, ⟨19328, -11008, -3712, 16384⟩,
    ⟨-3712, -11008, 19328, -16384⟩, ⟨29312, 12544, 18304, 4352⟩, 31⟩ rfl).trans ?_
  rfl
/-- Shared Stage-3 `AnfLayer3` sequence `mux3_8` (`L3 = 35`, `zeroAnc = false`). -/
def mux3_8 : List AnfLayer3 :=
  List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨true, true, true, false,
    true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, false,
    true, true, true, false, true, true⟩, ⟨true, false, false, true, true, false, false, true⟩,
    ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false, true, false,
    false, false⟩, ⟨false, true, true, false, false, true, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true, false, true,
    true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨true, true,
    false, false, true, true, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩,
    ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, true, false, false, false,
    true, false⟩, ⟨true, true, false, true, true, true, false, true⟩] (List.append (α :=
    AnfLayer3) [⟨false, true, false, true, false, true, false, true⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨false,
    false, true, true, false, false, true, true⟩, ⟨true, false, false, false, true, false, false,
    false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, false, false, false, true,
    false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, true, false, false, false, true, false⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    false, true, false, true, false, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true, true, true,
    true, true⟩, ⟨false, false, true, false, false, false, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨false, false, true, true, false, false, true, true⟩, ⟨false, true, false, false,
    false, true, false, false⟩, ⟨false, false, false, false, false, false, true,
    false⟩] (([] : List AnfLayer3))))))
theorem mux3_8_00_eval :
    evalAnf3Layers mux3_8 false false matPlus = ⟨⟨-96512, -12544, -128768, -173824⟩, ⟨-59648,
      -15104, 63744, -67840⟩, ⟨-67840, 63744, -15104, -59648⟩, ⟨173824, 128768, 12544, 96512⟩,
      36⟩ := by
  dsimp only [mux3_8]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ false false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨20, 4, 0,
    4⟩, ⟨8, 0, -4, 0⟩, ⟨-8, 0, -4, 0⟩, ⟨20, -4, 0, -4⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, true, false,
    false, false, true, false⟩, ⟨true, true, false, true, true, true, false,
    true⟩] _ false false ⟨⟨20, 4, 0, 4⟩, ⟨8, 0, -4, 0⟩, ⟨-8, 0, -4, 0⟩, ⟨20, -4, 0, -4⟩, 9⟩ ⟨⟨144,
    16, 224, 80⟩, ⟨0, -224, 48, -32⟩, ⟨0, 32, -48, 224⟩, ⟨-144, 80, 224, 16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, false, false, false, true,
    false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ false false ⟨⟨144, 16, 224, 80⟩, ⟨0, -224, 48, -32⟩, ⟨0, 32, -48, 224⟩, ⟨-144, 80, 224,
    16⟩, 17⟩ ⟨⟨3008, 704, 3968, -704⟩, ⟨-896, 512, 1984, -1664⟩, ⟨-896, 1664, -1984, -512⟩, ⟨-3008,
    -704, 3968, 704⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ false false ⟨⟨3008, 704, 3968, -704⟩, ⟨-896, 512, 1984, -1664⟩, ⟨-896, 1664, -1984,
    -512⟩, ⟨-3008, -704, 3968, 704⟩, 25⟩ ⟨⟨-9472, -11520, -65024, -14592⟩, ⟨4096, 50688, -36608,
    512⟩, ⟨-4096, 512, -36608, 50688⟩, ⟨-9472, 14592, 65024, 11520⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    false, false, false, true, false, false⟩, ⟨false, false, false, false, false, false, true,
    false⟩] _ false false ⟨⟨-9472, -11520, -65024, -14592⟩, ⟨4096, 50688, -36608, 512⟩, ⟨-4096, 512,
    -36608, 50688⟩, ⟨-9472, 14592, 65024, 11520⟩, 33⟩ ⟨⟨-96512, -12544, -128768, -173824⟩, ⟨-59648,
    -15104, 63744, -67840⟩, ⟨-67840, 63744, -15104, -59648⟩, ⟨173824, 128768, 12544, 96512⟩,
    36⟩ rfl).trans ?_
  rfl
theorem mux3_8_01_eval :
    evalAnf3Layers mux3_8 false true matPlus = ⟨⟨106240, -69376, -8960, 80640⟩, ⟨-9472, 30464,
      61696, 203008⟩, ⟨-203008, -61696, -30464, 9472⟩, ⟨80640, -8960, -69376, 106240⟩, 36⟩ := by
  dsimp only [mux3_8]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ false true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨12, -12, 0,
    -12⟩, ⟨8, 0, 4, 0⟩, ⟨8, 0, -4, 0⟩, ⟨-12, -12, 0, -12⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, true, false,
    false, false, true, false⟩, ⟨true, true, false, true, true, true, false,
    true⟩] _ false true ⟨⟨12, -12, 0, -12⟩, ⟨8, 0, 4, 0⟩, ⟨8, 0, -4, 0⟩, ⟨-12, -12, 0, -12⟩,
    9⟩ ⟨⟨-32, 0, 48, -224⟩, ⟨-16, -80, 224, 144⟩, ⟨16, 144, 224, -80⟩, ⟨-32, 224, -48, 0⟩,
    17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, false, false, false, true,
    false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ false true ⟨⟨-32, 0, 48, -224⟩, ⟨-16, -80, 224, 144⟩, ⟨16, 144, 224, -80⟩, ⟨-32, 224,
    -48, 0⟩, 17⟩ ⟨⟨128, -896, -1856, 1792⟩, ⟨-1600, -1472, -3712, 2752⟩, ⟨1600, 2752, -3712, -1472⟩,
    ⟨128, -1792, 1856, 896⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ false true ⟨⟨128, -896, -1856, 1792⟩, ⟨-1600, -1472, -3712, 2752⟩, ⟨1600, 2752, -3712,
    -1472⟩, ⟨128, -1792, 1856, 896⟩, 25⟩ ⟨⟨-15104, -41216, 62976, 24832⟩, ⟨-2560, 36864, 13568,
    -23040⟩, ⟨-2560, 23040, -13568, -36864⟩, ⟨15104, 24832, 62976, -41216⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    false, false, false, true, false, false⟩, ⟨false, false, false, false, false, false, true,
    false⟩] _ false true ⟨⟨-15104, -41216, 62976, 24832⟩, ⟨-2560, 36864, 13568, -23040⟩, ⟨-2560,
    23040, -13568, -36864⟩, ⟨15104, 24832, 62976, -41216⟩, 33⟩ ⟨⟨106240, -69376, -8960, 80640⟩,
    ⟨-9472, 30464, 61696, 203008⟩, ⟨-203008, -61696, -30464, 9472⟩, ⟨80640, -8960, -69376, 106240⟩,
    36⟩ rfl).trans ?_
  rfl
theorem mux3_8_10_eval :
    evalAnf3Layers mux3_8 true false matPlus = ⟨⟨-196864, 63232, 40192, -768⟩, ⟨-8448, -114432,
      -102144, 27392⟩, ⟨27392, -102144, -114432, -8448⟩, ⟨768, -40192, -63232, 196864⟩, 36⟩ := by
  dsimp only [mux3_8]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ true false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, 16, -4,
    8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, true, false,
    false, false, true, false⟩, ⟨true, true, false, true, true, true, false,
    true⟩] _ true false ⟨⟨8, 16, -4, 8⟩, ⟨-4, -4, -8, 4⟩, ⟨4, 4, -8, -4⟩, ⟨8, -8, 4, -16⟩, 9⟩ ⟨⟨-80,
    -48, -64, -176⟩, ⟨96, 256, -112, 0⟩, ⟨-96, 0, -112, 256⟩, ⟨-80, 176, 64, 48⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, false, false, false, true,
    false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ true false ⟨⟨-80, -48, -64, -176⟩, ⟨96, 256, -112, 0⟩, ⟨-96, 0, -112, 256⟩, ⟨-80, 176,
    64, 48⟩, 17⟩ ⟨⟨576, -3520, -1792, -448⟩, ⟨-1920, 3200, 1472, -1152⟩, ⟨-1920, 1152, -1472,
    -3200⟩, ⟨-576, -448, -1792, -3520⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ true false ⟨⟨576, -3520, -1792, -448⟩, ⟨-1920, 3200, 1472, -1152⟩, ⟨-1920, 1152,
    -1472, -3200⟩, ⟨-576, -448, -1792, -3520⟩, 25⟩ ⟨⟨56320, 15872, 37120, 29696⟩, ⟨-32512, -27392,
    28672, -16640⟩, ⟨-32512, 16640, -28672, 27392⟩, ⟨-56320, 29696, 37120, 15872⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    false, false, false, true, false, false⟩, ⟨false, false, false, false, false, false, true,
    false⟩] _ true false ⟨⟨56320, 15872, 37120, 29696⟩, ⟨-32512, -27392, 28672, -16640⟩, ⟨-32512,
    16640, -28672, 27392⟩, ⟨-56320, 29696, 37120, 15872⟩, 33⟩ ⟨⟨-196864, 63232, 40192, -768⟩,
    ⟨-8448, -114432, -102144, 27392⟩, ⟨27392, -102144, -114432, -8448⟩, ⟨768, -40192, -63232,
    196864⟩, 36⟩ rfl).trans ?_
  rfl
theorem mux3_8_11_eval :
    evalAnf3Layers mux3_8 true true matPlus = ⟨⟨19200, 30976, -154368, -131328⟩, ⟨61184, 25344,
      -97024, 111872⟩, ⟨-111872, 97024, -25344, -61184⟩, ⟨-131328, -154368, 30976, 19200⟩, 36⟩ := by
  dsimp only [mux3_8]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    true, true, false, true, true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨false, true, true, false, false, true, true, false⟩, ⟨true, false, false, false,
    true, false, false, false⟩, ⟨false, true, true, false, false, true, true,
    false⟩] _ true true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, -8, 4,
    -16⟩, ⟨4, 4, -8, -4⟩, ⟨4, 4, 8, -4⟩, ⟨-8, -16, 4, -8⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, true, false, false, true, true, false, false⟩, ⟨true, true,
    false, true, true, true, false, true⟩, ⟨true, true, true, false, true, true, true, false⟩,
    ⟨true, true, false, false, true, true, false, false⟩, ⟨true, false, false, true, true, false,
    false, true⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨false, false, true, false,
    false, false, true, false⟩, ⟨true, true, false, true, true, true, false, true⟩] _ true true ⟨⟨8,
    -8, 4, -16⟩, ⟨4, 4, -8, -4⟩, ⟨4, 4, 8, -4⟩, ⟨-8, -16, 4, -8⟩, 9⟩ ⟨⟨16, 16, 128, -272⟩, ⟨-128,
    -32, 80, 128⟩, ⟨-128, -128, -80, 32⟩, ⟨-16, -272, 128, 16⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, true, false, true, false, true⟩, ⟨false,
    false, false, false, false, false, false, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, false, false, false, true,
    false, false, false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, false, false,
    false, true, false, false, false⟩, ⟨true, false, false, true, true, false, false,
    true⟩] _ true true ⟨⟨16, 16, 128, -272⟩, ⟨-128, -32, 80, 128⟩, ⟨-128, -128, -80, 32⟩, ⟨-16,
    -272, 128, 16⟩, 17⟩ ⟨⟨-384, -1408, 2112, -1280⟩, ⟨3392, 1088, -3456, -832⟩, ⟨3392, 832, 3456,
    -1088⟩, ⟨384, -1280, 2112, -1408⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, false, false, false, true, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, true, true, false, false, true,
    true⟩, ⟨false, true, false, true, false, true, false, true⟩, ⟨false, false, false, false, false,
    false, false, false⟩, ⟨true, true, true, true, true, true, true, true⟩, ⟨true, true, true, true,
    true, true, true, true⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ true true ⟨⟨-384, -1408, 2112, -1280⟩, ⟨3392, 1088, -3456, -832⟩, ⟨3392, 832, 3456,
    -1088⟩, ⟨384, -1280, 2112, -1408⟩, 25⟩ ⟨⟨51968, -13568, 23552, 43776⟩, ⟨-13824, 12288, 37120,
    38912⟩, ⟨-13824, -38912, -37120, -12288⟩, ⟨-51968, 43776, 23552, -13568⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, false, true, true, false, false, true, true⟩, ⟨false, true,
    false, false, false, true, false, false⟩, ⟨false, false, false, false, false, false, true,
    false⟩] _ true true ⟨⟨51968, -13568, 23552, 43776⟩, ⟨-13824, 12288, 37120, 38912⟩, ⟨-13824,
    -38912, -37120, -12288⟩, ⟨-51968, 43776, 23552, -13568⟩, 33⟩ ⟨⟨19200, 30976, -154368, -131328⟩,
    ⟨61184, 25344, -97024, 111872⟩, ⟨-111872, 97024, -25344, -61184⟩, ⟨-131328, -154368, 30976,
    19200⟩, 36⟩ rfl).trans ?_
  rfl
/-- Shared Stage-2 `AffineLayer2` sequence `mux2_11` (`L2 = 37`). -/
def mux2_11 : List AffineLayer2 :=
  List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true, false, true,
    false⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩, ⟨false, false, false,
    false⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩] (List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false, true, false,
    true⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨true, false, true, false⟩,
    ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] (List.append (α :=
    AffineLayer2) [⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩,
    ⟨false, true, false, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, false,
    true, false⟩, ⟨false, true, false, true⟩] (List.append (α :=
    AffineLayer2) [⟨false, false, false, false⟩, ⟨false, false, false, false⟩, ⟨false, false, false,
    false⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩,
    ⟨false, false, false, false⟩, ⟨false, false, false, false⟩] (List.append (α :=
    AffineLayer2) [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false, true⟩,
    ⟨true, true, true, true⟩, ⟨false, false, true, false⟩] (([] : List AffineLayer2))))))
theorem mux2_11_0_eval :
    evalMux2Layers mux2_11 false matPlus = ⟨⟨-107520, -148480, -312832, 187904⟩, ⟨284672, 50176,
      28160, 154112⟩, ⟨-50176, -284672, 154112, 28160⟩, ⟨-148480, -107520, -187904, 312832⟩, 38⟩ :=
      by
  dsimp only [mux2_11]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true,
    false, true, false⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩, ⟨false, false,
    false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩] _ false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0,
    0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨12, -12, 0, -4⟩, ⟨0, 0, 12, 8⟩, ⟨0, -8, -12, 0⟩, ⟨-12,
    -4, 0, -12⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false,
    true, false, true⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨true, false, true,
    false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] _ false ⟨⟨12, -12, 0, -4⟩, ⟨0,
    0, 12, 8⟩, ⟨0, -8, -12, 0⟩, ⟨-12, -4, 0, -12⟩, 9⟩ ⟨⟨-144, -48, 32, -48⟩, ⟨192, 192, -176, 0⟩,
    ⟨-192, 0, -176, 192⟩, ⟨-144, 48, -32, 48⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false,
    true⟩, ⟨true, false, true, false⟩, ⟨false, true, false, true⟩] _ false ⟨⟨-144, -48, 32, -48⟩,
    ⟨192, 192, -176, 0⟩, ⟨-192, 0, -176, 192⟩, ⟨-144, 48, -32, 48⟩, 17⟩ ⟨⟨4224, -256, 2112, 1152⟩,
    ⟨-960, -1856, -1920, 1344⟩, ⟨-960, -1344, 1920, 1856⟩, ⟨-4224, 1152, 2112, -256⟩,
    25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, false, false, false⟩, ⟨false,
    false, false, false⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, true,
    true, true⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩] _ false ⟨⟨4224, -256,
    2112, 1152⟩, ⟨-960, -1856, -1920, 1344⟩, ⟨-960, -1344, 1920, 1856⟩, ⟨-4224, 1152, 2112, -256⟩,
    25⟩ ⟨⟨9472, 13056, 35328, 16640⟩, ⟨62976, -37376, 12544, -35840⟩, ⟨-62976, -35840, 12544,
    -37376⟩, ⟨9472, -16640, -35328, -13056⟩, 33⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨false, false, true, false⟩] _ false ⟨⟨9472, 13056,
    35328, 16640⟩, ⟨62976, -37376, 12544, -35840⟩, ⟨-62976, -35840, 12544, -37376⟩, ⟨9472, -16640,
    -35328, -13056⟩, 33⟩ ⟨⟨-107520, -148480, -312832, 187904⟩, ⟨284672, 50176, 28160, 154112⟩,
    ⟨-50176, -284672, 154112, 28160⟩, ⟨-148480, -107520, -187904, 312832⟩, 38⟩ rfl).trans ?_
  rfl
theorem mux2_11_1_eval :
    evalMux2Layers mux2_11 true matPlus = ⟨⟨-108544, -272384, -115200, -294400⟩, ⟨-40960, -117760,
      206336, -175616⟩, ⟨117760, 40960, -175616, 206336⟩, ⟨-272384, -108544, 294400, 115200⟩, 38⟩ :=
      by
  dsimp only [mux2_11]
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨true, true, true, true⟩, ⟨true,
    false, true, false⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩, ⟨false, false,
    false, false⟩, ⟨true, true, true, true⟩, ⟨true, true, true, true⟩] _ true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0,
    0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-4, 4, 0, 4⟩, ⟨-8, 0, 20, 0⟩, ⟨8, 0, 20, 0⟩, ⟨-4, -4,
    0, -4⟩, 9⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨false,
    true, false, true⟩, ⟨false, true, false, true⟩, ⟨true, false, true, false⟩, ⟨true, false, true,
    false⟩, ⟨true, true, true, true⟩, ⟨false, false, false, false⟩] _ true ⟨⟨-4, 4, 0, 4⟩, ⟨-8, 0,
    20, 0⟩, ⟨8, 0, 20, 0⟩, ⟨-4, -4, 0, -4⟩, 9⟩ ⟨⟨64, 96, 208, 64⟩, ⟨80, -240, 64, 48⟩, ⟨80, -48,
    -64, 240⟩, ⟨-64, 64, 208, 96⟩, 17⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, true, false, true⟩, ⟨false, true, false, true⟩, ⟨true,
    true, true, true⟩, ⟨false, true, false, true⟩, ⟨true, true, true, true⟩, ⟨false, true, false,
    true⟩, ⟨true, false, true, false⟩, ⟨false, true, false, true⟩] _ true ⟨⟨64, 96, 208, 64⟩, ⟨80,
    -240, 64, 48⟩, ⟨80, -48, -64, 240⟩, ⟨-64, 64, 208, 96⟩, 17⟩ ⟨⟨-704, 3520, -384, 1216⟩, ⟨-768,
    640, -3648, -2176⟩, ⟨-768, 2176, 3648, -640⟩, ⟨704, 1216, -384, 3520⟩, 25⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨false, false, false, false⟩, ⟨false, false, false, false⟩, ⟨false,
    false, false, false⟩, ⟨false, false, false, false⟩, ⟨false, true, false, true⟩, ⟨true, true,
    true, true⟩, ⟨false, false, false, false⟩, ⟨false, false, false, false⟩] _ true ⟨⟨-704, 3520,
    -384, 1216⟩, ⟨-768, 640, -3648, -2176⟩, ⟨-768, 2176, 3648, -640⟩, ⟨704, 1216, -384, 3520⟩,
    25⟩ ⟨⟨-22784, -2816, -26624, 33024⟩, ⟨6656, 75776, -3840, 21504⟩, ⟨-6656, 21504, -3840, 75776⟩,
    ⟨-22784, -33024, 26624, 2816⟩, 33⟩ rfl).trans ?_
  refine (evalMux2Layers_append [⟨true, true, true, true⟩, ⟨true, true, true, true⟩, ⟨false, true,
    false, true⟩, ⟨true, true, true, true⟩, ⟨false, false, true, false⟩] _ true ⟨⟨-22784, -2816,
    -26624, 33024⟩, ⟨6656, 75776, -3840, 21504⟩, ⟨-6656, 21504, -3840, 75776⟩, ⟨-22784, -33024,
    26624, 2816⟩, 33⟩ ⟨⟨-108544, -272384, -115200, -294400⟩, ⟨-40960, -117760, 206336, -175616⟩,
    ⟨117760, 40960, -175616, 206336⟩, ⟨-272384, -108544, 294400, 115200⟩, 38⟩ rfl).trans ?_
  rfl
/-- Shared Stage-3 `AnfLayer3` sequence `mux3_17` (`L3 = 40`, `zeroAnc = false`). -/
def mux3_17 : List AnfLayer3 :=
  List.append (α :=
    AnfLayer3) [⟨false, false, false, false, false, false, false, false⟩, ⟨false, true, false,
    false, false, true, false, false⟩, ⟨false, true, false, false, false, true, false, false⟩,
    ⟨true, false, true, true, true, false, true, true⟩, ⟨false, true, true, false, false, true,
    true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, false, true,
    false, false, false, true⟩, ⟨true, false, true, true, true, false, true,
    true⟩] (List.append (α :=
    AnfLayer3) [⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false,
    true, false, true, false⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨true, true, true, false, true, true, true,
    false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, true, true, true,
    false, true, true⟩, ⟨false, false, false, true, false, false, false, true⟩] (List.append (α :=
    AnfLayer3) [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true, true, true, true,
    true, true, true⟩, ⟨false, false, true, false, false, false, true, false⟩, ⟨true, false, false,
    true, true, false, false, true⟩, ⟨true, true, false, true, true, true, false, true⟩, ⟨false,
    false, false, true, false, false, false, true⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨true, true, true, false, true, true, true, false⟩] (List.append (α :=
    AnfLayer3) [⟨true, false, false, false, true, false, false, false⟩, ⟨true, true, false, true,
    true, true, false, true⟩, ⟨false, false, false, false, false, false, false, false⟩, ⟨true,
    false, false, false, true, false, false, false⟩, ⟨false, false, false, false, false, false,
    false, false⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨false, false, true,
    false, false, false, true, false⟩, ⟨false, false, true, false, false, false, true,
    false⟩] (List.append (α :=
    AnfLayer3) [⟨false, true, false, false, false, true, false, false⟩, ⟨true, false, false, true,
    true, false, false, true⟩, ⟨true, true, false, false, true, true, false, false⟩, ⟨false, false,
    true, true, false, false, true, true⟩, ⟨true, true, false, true, true, true, false, true⟩,
    ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, true, false, true, true,
    true, false⟩, ⟨true, true, false, false, true, true, true, true⟩] (([] : List AnfLayer3))))))
theorem mux3_17_00_eval :
    evalAnf3Layers mux3_17 false false matPlus = ⟨⟨-652288, -377856, -866304, 424960⟩, ⟨-598016,
      483328, -261120, -200704⟩, ⟨-598016, 200704, 261120, -483328⟩, ⟨652288, 424960, -866304,
      -377856⟩, 41⟩ := by
  dsimp only [mux3_17]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, false, false, false, true, false, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, false,
    true, false, false, false, true⟩, ⟨true, false, true, true, true, false, true,
    true⟩] _ false false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-16, -8, -4,
    -8⟩, ⟨4, 4, -8, 4⟩, ⟨-4, 4, -8, 4⟩, ⟨-16, 8, 4, 8⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, true,
    true, true, false, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ false false ⟨⟨-16, -8, -4, -8⟩, ⟨4, 4, -8, 4⟩, ⟨-4, 4, -8, 4⟩, ⟨-16, 8, 4, 8⟩,
    9⟩ ⟨⟨-128, -32, -112, -32⟩, ⟨-272, 112, -32, 112⟩, ⟨-272, -112, 32, -112⟩, ⟨128, -32, -112,
    -32⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    true, true, true, true, true, true⟩, ⟨false, false, true, false, false, false, true, false⟩,
    ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, false, true, true, true,
    false, true⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨true, true, false, false,
    true, true, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ false false ⟨⟨-128, -32, -112, -32⟩, ⟨-272, 112, -32, 112⟩, ⟨-272, -112, 32, -112⟩,
    ⟨128, -32, -112, -32⟩, 17⟩ ⟨⟨-1344, 576, 4224, -704⟩, ⟨256, -1152, 2112, 2688⟩, ⟨256, -2688,
    -2112, 1152⟩, ⟨1344, -704, 4224, 576⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, false, false, true, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨false,
    false, true, false, false, false, true, false⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ false false ⟨⟨-1344, 576, 4224, -704⟩, ⟨256, -1152, 2112, 2688⟩, ⟨256, -2688, -2112,
    1152⟩, ⟨1344, -704, 4224, 576⟩, 25⟩ ⟨⟨3840, -2816, -53760, 256⟩, ⟨4096, 55808, -31488, -39424⟩,
    ⟨-4096, -39424, -31488, 55808⟩, ⟨3840, -256, 53760, 2816⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, false, true, true,
    true, false, true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, true,
    false, true, true, true, false⟩, ⟨true, true, false, false, true, true, true,
    true⟩] _ false false ⟨⟨3840, -2816, -53760, 256⟩, ⟨4096, 55808, -31488, -39424⟩, ⟨-4096, -39424,
    -31488, 55808⟩, ⟨3840, -256, 53760, 2816⟩, 33⟩ ⟨⟨-652288, -377856, -866304, 424960⟩, ⟨-598016,
    483328, -261120, -200704⟩, ⟨-598016, 200704, 261120, -483328⟩, ⟨652288, 424960, -866304,
    -377856⟩, 41⟩ rfl).trans ?_
  rfl
theorem mux3_17_01_eval :
    evalAnf3Layers mux3_17 false true matPlus = ⟨⟨236544, 128000, -415744, 455680⟩, ⟨-1048576,
      -215040, -744448, -215040⟩, ⟨-1048576, 215040, 744448, 215040⟩, ⟨-236544, 455680, -415744,
      128000⟩, 41⟩ := by
  dsimp only [mux3_17]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, false, false, false, true, false, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, false,
    true, false, false, false, true⟩, ⟨true, false, true, true, true, false, true,
    true⟩] _ false true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨4, -4, 8,
    12⟩, ⟨0, -8, 12, 8⟩, ⟨0, 8, 12, -8⟩, ⟨4, -12, -8, 4⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, true,
    true, true, false, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ false true ⟨⟨4, -4, 8, 12⟩, ⟨0, -8, 12, 8⟩, ⟨0, 8, 12, -8⟩, ⟨4, -12, -8, 4⟩, 9⟩ ⟨⟨-192,
    -256, 80, -96⟩, ⟨16, -80, 0, 80⟩, ⟨16, -80, 0, 80⟩, ⟨192, -96, 80, -256⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    true, true, true, true, true, true⟩, ⟨false, false, true, false, false, false, true, false⟩,
    ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, false, true, true, true,
    false, true⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨true, true, false, false,
    true, true, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ false true ⟨⟨-192, -256, 80, -96⟩, ⟨16, -80, 0, 80⟩, ⟨16, -80, 0, 80⟩, ⟨192, -96, 80,
    -256⟩, 17⟩ ⟨⟨-2944, -1408, 2240, 896⟩, ⟨832, -64, 2560, -3136⟩, ⟨832, 3136, -2560, 64⟩, ⟨2944,
    896, 2240, -1408⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, false, false, true, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨false,
    false, true, false, false, false, true, false⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ false true ⟨⟨-2944, -1408, 2240, 896⟩, ⟨832, -64, 2560, -3136⟩, ⟨832, 3136, -2560,
    64⟩, ⟨2944, 896, 2240, -1408⟩, 25⟩ ⟨⟨-4096, 14848, -10496, 58368⟩, ⟨-20736, -34048, 52224,
    22784⟩, ⟨20736, 22784, 52224, -34048⟩, ⟨-4096, -58368, 10496, -14848⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, false, true, true,
    true, false, true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, true,
    false, true, true, true, false⟩, ⟨true, true, false, false, true, true, true,
    true⟩] _ false true ⟨⟨-4096, 14848, -10496, 58368⟩, ⟨-20736, -34048, 52224, 22784⟩, ⟨20736,
    22784, 52224, -34048⟩, ⟨-4096, -58368, 10496, -14848⟩, 33⟩ ⟨⟨236544, 128000, -415744, 455680⟩,
    ⟨-1048576, -215040, -744448, -215040⟩, ⟨-1048576, 215040, 744448, 215040⟩, ⟨-236544, 455680,
    -415744, 128000⟩, 41⟩ rfl).trans ?_
  rfl
theorem mux3_17_10_eval :
    evalAnf3Layers mux3_17 true false matPlus = ⟨⟨757760, 595968, -513024, 288768⟩, ⟨-138240,
      -402432, 104448, 855040⟩, ⟨-138240, -855040, -104448, 402432⟩, ⟨-757760, 288768, -513024,
      595968⟩, 41⟩ := by
  dsimp only [mux3_17]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, false, false, false, true, false, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, false,
    true, false, false, false, true⟩, ⟨true, false, true, true, true, false, true,
    true⟩] _ true false ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨8, 8, 4, 0⟩,
    ⟨4, -12, -8, 12⟩, ⟨-4, 12, -8, -12⟩, ⟨8, 0, -4, -8⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, true,
    true, true, false, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ true false ⟨⟨8, 8, 4, 0⟩, ⟨4, -12, -8, 12⟩, ⟨-4, 12, -8, -12⟩, ⟨8, 0, -4, -8⟩, 9⟩ ⟨⟨0,
    288, -48, -192⟩, ⟨-48, -16, 0, 80⟩, ⟨-48, -80, 0, 16⟩, ⟨0, -192, -48, 288⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    true, true, true, true, true, true⟩, ⟨false, false, true, false, false, false, true, false⟩,
    ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, false, true, true, true,
    false, true⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨true, true, false, false,
    true, true, false, false⟩, ⟨true, true, true, false, true, true, true, false⟩] _ true false ⟨⟨0,
    288, -48, -192⟩, ⟨-48, -16, 0, 80⟩, ⟨-48, -80, 0, 16⟩, ⟨0, -192, -48, 288⟩, 17⟩ ⟨⟨-2560, -128,
    2880, 1664⟩, ⟨-576, 1600, -2176, 2880⟩, ⟨-576, -2880, 2176, -1600⟩, ⟨2560, 1664, 2880, -128⟩,
    25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, false, false, true, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨false,
    false, true, false, false, false, true, false⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ true false ⟨⟨-2560, -128, 2880, 1664⟩, ⟨-576, 1600, -2176, 2880⟩, ⟨-576, -2880, 2176,
    -1600⟩, ⟨2560, 1664, 2880, -128⟩, 25⟩ ⟨⟨24576, -75776, -11520, -1024⟩, ⟨24832, 19712, -27136,
    -19200⟩, ⟨24832, 19200, 27136, -19712⟩, ⟨-24576, -1024, -11520, -75776⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, false, true, true,
    true, false, true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, true,
    false, true, true, true, false⟩, ⟨true, true, false, false, true, true, true,
    true⟩] _ true false ⟨⟨24576, -75776, -11520, -1024⟩, ⟨24832, 19712, -27136, -19200⟩, ⟨24832,
    19200, 27136, -19712⟩, ⟨-24576, -1024, -11520, -75776⟩, 33⟩ ⟨⟨757760, 595968, -513024, 288768⟩,
    ⟨-138240, -402432, 104448, 855040⟩, ⟨-138240, -855040, -104448, 402432⟩, ⟨-757760, 288768,
    -513024, 595968⟩, 41⟩ rfl).trans ?_
  rfl
theorem mux3_17_11_eval :
    evalAnf3Layers mux3_17 true true matPlus = ⟨⟨-206848, -1175552, -125952, 399360⟩, ⟨-244736,
      519168, -489472, 173056⟩, ⟨-244736, -173056, 489472, -519168⟩, ⟨206848, 399360, -125952,
      -1175552⟩, 41⟩ := by
  dsimp only [mux3_17]
  refine (evalAnf3Layers_append [⟨false, false, false, false, false, false, false, false⟩, ⟨false,
    true, false, false, false, true, false, false⟩, ⟨false, true, false, false, false, true, false,
    false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨false, true, true, false, false,
    true, true, false⟩, ⟨true, true, true, false, true, true, true, false⟩, ⟨false, false, false,
    true, false, false, false, true⟩, ⟨true, false, true, true, true, false, true,
    true⟩] _ true true ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩, 1⟩ ⟨⟨-12, 12, 8,
    4⟩, ⟨-8, 8, 4, 0⟩, ⟨-8, 0, -4, -8⟩, ⟨12, 4, 8, 12⟩, 9⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, true, false, true,
    true, true, false⟩, ⟨true, false, true, true, true, false, true, true⟩, ⟨true, false, true,
    true, true, false, true, true⟩, ⟨false, false, false, true, false, false, false,
    true⟩] _ true true ⟨⟨-12, 12, 8, 4⟩, ⟨-8, 8, 4, 0⟩, ⟨-8, 0, -4, -8⟩, ⟨12, 4, 8, 12⟩, 9⟩ ⟨⟨-96,
    0, 176, -64⟩, ⟨-48, -80, 256, 112⟩, ⟨48, 112, 256, -80⟩, ⟨-96, 64, -176, 0⟩, 17⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, true, false, true, false, true, false⟩, ⟨true, true,
    true, true, true, true, true, true⟩, ⟨false, false, true, false, false, false, true, false⟩,
    ⟨true, false, false, true, true, false, false, true⟩, ⟨true, true, false, true, true, true,
    false, true⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨true, true, false, false,
    true, true, false, false⟩, ⟨true, true, true, false, true, true, true,
    false⟩] _ true true ⟨⟨-96, 0, 176, -64⟩, ⟨-48, -80, 256, 112⟩, ⟨48, 112, 256, -80⟩, ⟨-96, 64,
    -176, 0⟩, 17⟩ ⟨⟨1792, 384, -2112, -2816⟩, ⟨-2112, 3136, -256, -1856⟩, ⟨2112, -1856, -256, 3136⟩,
    ⟨1792, 2816, 2112, -384⟩, 25⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨true, false, false, false, true, false, false, false⟩, ⟨true,
    true, false, true, true, true, false, true⟩, ⟨false, false, false, false, false, false, false,
    false⟩, ⟨true, false, false, false, true, false, false, false⟩, ⟨false, false, false, false,
    false, false, false, false⟩, ⟨false, false, false, true, false, false, false, true⟩, ⟨false,
    false, true, false, false, false, true, false⟩, ⟨false, false, true, false, false, false, true,
    false⟩] _ true true ⟨⟨1792, 384, -2112, -2816⟩, ⟨-2112, 3136, -256, -1856⟩, ⟨2112, -1856, -256,
    3136⟩, ⟨1792, 2816, 2112, -384⟩, 25⟩ ⟨⟨34304, 37376, -31488, -19968⟩, ⟨26368, -60672, -10240,
    12032⟩, ⟨-26368, 12032, -10240, -60672⟩, ⟨34304, 19968, 31488, -37376⟩, 33⟩ rfl).trans ?_
  refine (evalAnf3Layers_append [⟨false, true, false, false, false, true, false, false⟩, ⟨true,
    false, false, true, true, false, false, true⟩, ⟨true, true, false, false, true, true, false,
    false⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, false, true, true,
    true, false, true⟩, ⟨false, false, true, true, false, false, true, true⟩, ⟨true, true, true,
    false, true, true, true, false⟩, ⟨true, true, false, false, true, true, true,
    true⟩] _ true true ⟨⟨34304, 37376, -31488, -19968⟩, ⟨26368, -60672, -10240, 12032⟩, ⟨-26368,
    12032, -10240, -60672⟩, ⟨34304, 19968, 31488, -37376⟩, 33⟩ ⟨⟨-206848, -1175552, -125952,
    399360⟩, ⟨-244736, 519168, -489472, 173056⟩, ⟨-244736, -173056, 489472, -519168⟩, ⟨206848,
    399360, -125952, -1175552⟩, 41⟩ rfl).trans ?_
  rfl
end Part1_ZeroAncAndTightCoins135598

end TierTightSpine

end QuantumComputation.Specs.StoppingPowerSolution
