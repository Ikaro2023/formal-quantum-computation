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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WideTwist54Bridge

set_option Elab.async false

/-!
# `266 T` `withSharedBank114WState` and `0-T` `H = 54` `X`-Uncompute Nuclear Twist

1. Uses `withSharedBank114WState` (`266 T`), mapping even unary indices `2 * k` (`k < 54`)
   into `rHi54Of61 rHdr61` and odd indices `2 * m + 1` (`m < 54`) into `rPreHold`
   (`119 + 2 * W` clean wires: `108 + 2 * W ≤ mWork` on `(mWork + 11, mWork + 14)`).
2. Omits `dAndSandwich` (`4 T`/axis) from `H = 54` `X`-basis uncomputation
   (`dMKXUncomputeAnc_54_0T`), since `decide (54 ≤ i.val) = false` for all `i : Fin 54`.
3. Exports `tTw114ZeroUnc54 W = 9400 + 360 * (W - 28)`,
   `mkGenWidthAsymHeldTwSpec114ZeroUnc54`, `mkSlot3GenAsymHeldTwSpec114ZeroUnc54_mWork`, and
   `mkSlot3InnerGenAsymHeldTwSpec114ZeroUnc54_11_14_mWor`.
-/

@[expose] public section

set_option exponentiation.threshold 8192

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace Twist114HoistCore

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
  ModWrapCoarse8PureMomentum.modWrapNeZeroPow2
  PosSlots24BranchConcrete.instNeZeroTwoPow

local instance (priority := 1000000) instNeZeroTwoPow05d0 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority :=
  1000000) instGroupUnitaryFast_05d0 (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_05d0 (D : ℕ) : Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

open scoped BigOperators Matrix Matrix.Norms.L2Operator Circuit.Notation
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open PrimitiveGate (TOFF T)
open _root_ (bitsVal basisKet regVal)
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open FullSysCatSegmentBridge (fullSysCoreWires coreCosetB1Block)
open NuclearTwistAndXor654Concrete (rNucIdx)
open NuclearTwistRealizes (RealizesCleanPair coin0Active ite_pos_eq ite_neg_eq embedUnitary_inv_eq)
open NuclearTwistMulKickAndBridge288 (count_dyn_seq)
open FusedPreDiagFromTwist288 (hm6_of_hm22)
open FusedVepCore288 (CleanUnitaryWp DiagOn shiftCatKet shiftCatKet_outside)
open UltraAsymVepTwist288 (realizesClean_of_workspace_subset)
open Slot2ZeroMuxSignedMul46 (apexCatModAddZ apexCatModAddZ_inv)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open InterWalkRSum42Hoist (embedUnitary_inv_symm)
open WindowedSlot2FusedTwist288 (slice_disj_of_le)
open KoffPrunedSlot2ZeroMuxTrunc37 (uInnerKoffSlot2DeltaGen)
open MeasureBranchHadamardSem (ket)
open MomSlot0CircuitHalf (phaseDiagUnitary)
open SharedUnary54Trunc37 (embedUnitary_diagSignUnitary_eq)
open SharedUnary108ZeroTUncompTwist
open Leaf4Twist162 hiding CommutesWithReg rCoreTopCatInCT rCtrl3InCore rCtrl3InCoreCat
open TwistShared108HadCut558 (zero_lt_anc one_lt_anc anc_one_ne_zero h9_of_K28 rMPad48_disj_rAnc)
open TwistShared108AndLeaf3Bk (kickSkipKoffSpecTight)
open SharedUnaryTrunc37Stitch220 (withSharedBank114WState count_withSharedBank114WState_toff
  count_withSharedBank114WState_t withSharedBank114WState_phasePerm_const)
open WStateSharedBank114AndTwist114 (cleanUnitaryEquiv_of_cleanUnitaryWp
  cleanUnitaryWp_of_cleanUnitaryEquiv)
open TruncWAsymHeldTwShell (Slot3InnerGenAsymHeldTwSpec_mWork)
open TruncWAsymHeldTwShell.Slot3InnerTrunc36 (qreg_ext37 shiftNat34 phiCat34 apexCatModAdd37Z
  apexCatModAdd37Z_mulVec_basisKet apexCatModAdd37Z_inv_of_dvd11
  embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11 rPGPad48_37 rPGPad48_37_disj_rMPad48
  rSum14_disj_rPGPad48_37)
open TruncWAsymHeldTwShell.Slot3InnerKick37
open SlimNorm1sWideSelect (compose_rCSP37InSub37)
open WideTwist54Core
open WideTwist54AndSlot3Bridge

-- ============================================================================
-- Section 1: `0-T` `H = 54` Pure-Clifford `X`-Basis Uncomputation
-- ============================================================================

theorem sum_hiD_54_eq_zero {H : ℕ} (h54H : 54 ≤ H) (P : Fin 54 → Bool → Bool) (g : Fin 54 →
    ZMod 2) :
    (∑ i : Fin 54,
      if (decide (H ≤ i.val) && xor (P i false) (P i true)) = true then g i else 0) = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hdec : decide (H ≤ i.val) = false :=
    decide_eq_false (not_le_of_gt (lt_of_lt_of_le i.isLt h54H))
  rw [hdec]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- `0-T`, `0-TOFF` pure-Clifford continuation of `rMK` `X`-basis uncomputation at `H = 54`
(omits `dAndSandwich` since `decide (H ≤ i.val) = false` for every `i : Fin 54` when `54 ≤ H`). -/
noncomputable def dMKXUncomputeContAnc_54_0T {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload)
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rAnc : QRegister mAnc n)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc)
    (hPHA : rPreHold.DisjointWires rAnc) (f : Fin K → Bool) : DynamicCircuit Var n :=
  vepLockVal <|
    .circuit (cPhaseFixupMK108_0T hK9 hH54 c hm w f rCore rHdr61 rPreHold
      (rAnc ⟨0, zero_lt_anc h9⟩) (rAnc ⟨1, one_lt_anc h9⟩)
      (fun q ↦ hCA.ne q ⟨0, zero_lt_anc h9⟩)
      (fun q ↦ hH61A.ne q ⟨0, zero_lt_anc h9⟩)
      (fun m ↦ hPHA.ne m ⟨0, zero_lt_anc h9⟩)
      (anc_one_ne_zero h9 rAnc))

/-- `0-T`, `0-TOFF` `X`-basis measurement uncomputation of `rMK` at `H = 54`. -/
noncomputable def dMKXUncomputeAnc_54_0T {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload)
    (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rMK : QRegister K n) (rAnc : QRegister
      mAnc n)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc)
    (hPHA : rPreHold.DisjointWires rAnc) : DynamicCircuit Var n :=
  DynCircuitExt.measureXResetAndBranch v K rMK
    (dMKXUncomputeContAnc_54_0T hK9 h9 hH54 c hm w rCore rHdr61 rPreHold rAnc hCA hH61A hPHA)

theorem count_dMKXUncomputeAnc_54_0T_toff {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload)
    (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rMK : QRegister K n) (rAnc : QRegister
      mAnc n)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc)
    (hPHA : rPreHold.DisjointWires rAnc) :
    (dMKXUncomputeAnc_54_0T hK9 h9 hH54 c hm v w rCore rHdr61 rPreHold rMK rAnc
      hCA hH61A hPHA).count TOFF = 0 := by
  refine Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v K rMK _ 0 fun f ↦ ?_)
  rw [dMKXUncomputeContAnc_54_0T, vepLockVal_eq]
  dsimp only [DynamicCircuit.count]
  exact Nat.le_of_eq (count_cPhaseFixupMK108_0T_toff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem count_dMKXUncomputeAnc_54_0T_t {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload)
    (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rMK : QRegister K n) (rAnc : QRegister
      mAnc n)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc)
    (hPHA : rPreHold.DisjointWires rAnc) :
    (dMKXUncomputeAnc_54_0T hK9 h9 hH54 c hm v w rCore rHdr61 rPreHold rMK rAnc
      hCA hH61A hPHA).count T = 0 := by
  refine Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_T_le v K rMK _ 0 fun f ↦ ?_)
  rw [dMKXUncomputeContAnc_54_0T, vepLockVal_eq]
  dsimp only [DynamicCircuit.count]
  exact Nat.le_of_eq (count_cPhaseFixupMK108_0T_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem dMKXUncomputeContAnc_54_0T_realizes_37 {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload K H mAnc n : ℕ} [NeZero (2 ^ n)]
    (hK9 : 9 ≤ K) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54) (h54H : 54 ≤ H) (c : Configuration) (hm : 22 ≤
      mPayload)
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (rPG37 :
      QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hCHSP : ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc)
    (hPHA : rPreHold.DisjointWires rAnc) (hMKA : rMK.DisjointWires rAnc) (f : Fin K → Bool) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP)
      (rMK.concat rAnc hMKA)
      (diagSignUnitary (fun x ↦ f2Parity K f (tblMK108Data37 K H hK9 hH54 c hm w x)))
      (dMKXUncomputeContAnc_54_0T (Var := Var) hK9 h9 hH54 c hm w rCore rHdr61 rPreHold rAnc
        hCA hH61A hPHA f) := by
  let rCH := rCHHold rCore rHdr61 rPreHold hCH61 hCHPH
  have hwCH : CleanUnitaryWp (Var := Var) rAnc
      (rCH.embedUnitary (phaseDiagUnitary (fun xCH ↦
        ∑ k : Fin K, if f k = true then fullMK108BitFn K H hK9 hH54 c hm w xCH k else 0)))
      (dMKXUncomputeContAnc_54_0T (Var := Var) hK9 h9 hH54 c hm w rCore rHdr61 rPreHold rAnc
        hCA hH61A hPHA f) := by
    rw [dMKXUncomputeContAnc_54_0T, vepLockVal_eq]
    refine (CleanUnitaryWp.circuit (Var := Var) rAnc _).congr_cleanKet fun β hzAnc ↦ ?_
    rw [show basisKet β = ket β from rfl, embedUnitary_phaseDiagUnitary_mulVec_ket rCH _ β,
      cPhaseFixupMK108_0T_eval_ket hK9 hH54 c hm w f rCore rHdr61 rPreHold
        (rAnc ⟨0, zero_lt_anc h9⟩) (rAnc ⟨1, one_lt_anc h9⟩)
        (fun q ↦ hCA.ne q ⟨0, zero_lt_anc h9⟩) (fun q ↦ hH61A.ne q ⟨0, zero_lt_anc h9⟩)
        (fun m ↦ hPHA.ne m ⟨0, zero_lt_anc h9⟩) (anc_one_ne_zero h9 rAnc) β
        (hzAnc ⟨0, zero_lt_anc h9⟩)]
    refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β) ?_
    rw [sum_fullMK108BitFn_eq K H hK9 hH54 c hm w f (fun q ↦ β (rCH q))]
    dsimp only
    have hCoreCH (q) : β (rCH (Fin.castAdd H (Fin.castAdd 61 q))) = β (rCore q) := by
      dsimp only [rCH, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hHdrCH (q) :
        β (rCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) q))) = β (rHdr61 q) := by
      dsimp only [rCH, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_right]
    have hPreCH (m) :
        β (rCH (Fin.natAdd (fullSysCoreWires mPayload + 61) m)) = β (rPreHold m) := by
      dsimp only [rCH, rCHHold]
      rw [QRegister.concat_apply_right]
    simp only [hCoreCH, hHdrCH, hPreCH, sum_hiD_54_eq_zero h54H, mul_zero, add_zero]
  have hRealCH := hwCH.to_realizesClean
  have hCompCH :
      (rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).compose
        (chHoldInData37 (mPayload := mPayload) (H := H)) = rCH :=
    qreg_ext37 fun q ↦ by
      dsimp only [rAxisData37, rCH, rCHHold, chHoldInData37, QRegister.compose_apply,
        Function.Embedding.coeFn_mk]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  rw [← hCompCH] at hRealCH
  have hRealData := hRealCH.widenActive
  have hUeq :
      (chHoldInData37 (mPayload := mPayload) (H := H)).embedUnitary
        (phaseDiagUnitary (fun xCH ↦
          ∑ k : Fin K, if f k = true then fullMK108BitFn K H hK9 hH54 c hm w xCH k else 0)) =
      diagSignUnitary (fun x ↦ f2Parity K f (tblMK108Data37 K H hK9 hH54 c hm w x)) := by
    rw [phaseDiagUnitary_eq_diagSignUnitary_f2Parity_gen, embedUnitary_diagSignUnitary_eq]
    exact congrArg diagSignUnitary (funext fun x ↦ congrArg (f2Parity K f)
      (congrArg (basisBitsEquiv K).symm (funext fun k ↦
        congrArg (fun fn ↦ fullMK108BitFn K H hK9 hH54 c hm w fn k) (funext fun q ↦
          QRegister.basisBits_extractIndex (chHoldInData37 (mPayload := mPayload) (H := H)) x q))))
  rw [hUeq] at hRealData
  exact realizesClean_of_workspace_subset
    (QRegExt.image_concat rMK rAnc hMKA ▸ Finset.subset_union_right) hRealData

-- ============================================================================
-- Section 2: `0-T`-Uncompute Per-Axis `108`-Leaf Circuit (`dAxisInner108_37_54_0T`)
-- ============================================================================

theorem hmClean54 (K : ℕ) : 56 - 54 ≤ 6 + (K - 2) :=
  Nat.le_trans (by decide : 56 - 54 ≤ 6) (Nat.le_add_right 6 (K - 2))

/-- Per-axis `108`-leaf circuit `dAxisPre108KH_37_54 ;; dMKXUncomputeAnc_54_0T` on `rPG37` at `H =
  54`
(`0` `TOFF`, `≤ 4 * K + 60 + tZeroMuxSkip (48 - K)` `T`). -/
noncomputable def dAxisInner108_37_54_0T {Var : Type} {mPayload K n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister 54 n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister (6 + (K - 2)) n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hH61MK : rHdr61.DisjointWires rMK) (hPHMK : rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hCSum : rCore.DisjointWires rSum14) (hSP37 : rSum14.DisjointWires rPG37)
    (hSMK : rSum14.DisjointWires rMK) (hP37MK : rPG37.DisjointWires rMK)
    (hSA : rSum14.DisjointWires rAnc) (hP37A : rPG37.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) : DynamicCircuit Var n :=
  vepLockVal <|
    .seq
      (dAxisPre108KH_37_54 hK28 hK36 (hmClean54 K) (le_refl 54) isInv c hm v w
        rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
        hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA)
      (dMKXUncomputeAnc_54_0T (hK9_of_K28 K hK28) (h9_of_K28 K hK28) (le_refl 54) c hm v w
        rCore rHdr61 rPreHold rMK rAnc hCA hH61A hPHA)

theorem count_dAxisInner108_37_54_0T_toff {Var : Type} {mPayload K n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister 54 n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister (6 + (K - 2)) n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hH61MK : rHdr61.DisjointWires rMK) (hPHMK : rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hCSum : rCore.DisjointWires rSum14) (hSP37 : rSum14.DisjointWires rPG37)
    (hSMK : rSum14.DisjointWires rMK) (hP37MK : rPG37.DisjointWires rMK)
    (hSA : rSum14.DisjointWires rAnc) (hP37A : rPG37.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) :
    (dAxisInner108_37_54_0T hK28 hK36 isInv c hm v w rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
      hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A
        hMKA).count TOFF = 0 := by
  rw [dAxisInner108_37_54_0T, vepLockVal_eq, dAxisPre108KH_37_54, vepLockVal_eq]
  simp only [count_dyn_seq, count_dLoadAndVepMK108Anc_54_toff,
    count_dApexKoffWithInvMsbInc7Scr_toff, count_dMKXUncomputeAnc_54_0T_toff]

theorem count_dAxisInner108_37_54_0T_t_le {Var : Type} {mPayload K n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister 54 n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister (6 + (K - 2)) n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hH61MK : rHdr61.DisjointWires rMK) (hPHMK : rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hCSum : rCore.DisjointWires rSum14) (hSP37 : rSum14.DisjointWires rPG37)
    (hSMK : rSum14.DisjointWires rMK) (hP37MK : rPG37.DisjointWires rMK)
    (hSA : rSum14.DisjointWires rAnc) (hP37A : rPG37.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) :
    (dAxisInner108_37_54_0T hK28 hK36 isInv c hm v w rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
      hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A
        hMKA).count T ≤
      4 * K + 60 + tZeroMuxSkip (48 - K) := by
  rw [dAxisInner108_37_54_0T, vepLockVal_eq, dAxisPre108KH_37_54, vepLockVal_eq]
  simp only [count_dyn_seq, count_dLoadAndVepMK108Anc_54_t]
  have h1 := count_dApexKoffWithInvMsbInc7Scr_t_le (kickSkipKoffSpecTight K hK28 hK36) isInv v
    (rCore (coreCosetB1Block (hm6_of_hm22 hm) w)) rSum14
    (rMPad48 (hK48_of_K36 K hK36) rCore rMK hCMK) (rPGPad48_37 rCore rPG37 hCP37) rAnc
    (wCtrl_ne_rMPad48 hm (hK48_of_K36 K hK36) w rCore rMK hCMK)
    (fun i ↦ hCA.ne (coreCosetB1Block (hm6_of_hm22 hm) w) i)
    (rSum14_disj_rMPad48 (hK48_of_K36 K hK36) rCore rSum14 rMK hCMK hCSum hSMK)
    (rSum14_disj_rPGPad48_37 rCore rSum14 rPG37 hCP37 hCSum hSP37)
    (rPGPad48_37_disj_rMPad48 (hK48_of_K36 K hK36) rCore rPG37 rMK hCP37 hCMK hP37MK)
    hSA (rMPad48_disj_rAnc (hK48_of_K36 K hK36) rCore rMK rAnc hCMK hCA hMKA)
    (rPGPad48_37_disj_rAnc rCore rPG37 rAnc hCP37 hCA hP37A)
  have h2 := count_dMKXUncomputeAnc_54_0T_t (Var :=
    Var) (hK9_of_K28 K hK28) (h9_of_K28 K hK28) (le_refl 54) c hm v w
    rCore rHdr61 rPreHold rMK rAnc hCA hH61A hPHA
  change _ ≤ 24 + tZeroMuxSkip (48 - K) at h1
  omega

theorem dAxisInner108_37_54_0T_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload K n : ℕ} [NeZero (2 ^ n)]
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister 54 n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister (6 + (K - 2)) n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hH61MK : rHdr61.DisjointWires rMK) (hPHMK : rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hCSum : rCore.DisjointWires rSum14) (hSP37 : rSum14.DisjointWires rPG37)
    (hSMK : rSum14.DisjointWires rMK) (hP37MK : rPG37.DisjointWires rMK)
    (hSA : rSum14.DisjointWires rAnc) (hP37A : rPG37.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hCHSP : ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37)
      :
    let hK9 := hK9_of_K28 K hK28
    let kSysNo14 := (((fullSysCoreWires mPayload - 14) + 61) + 54) + 14
    let rData := rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP
    RealizesCleanPair rData (rMK.concat rAnc hMKA)
      ((selNo14InAxisData37 (mPayload := mPayload) (H := 54)).embedUnitary
        (apexCatModAddZ kSysNo14 (axisDelta108No14 K 54 hK9 (le_refl 54) c hm w)))
      (dAxisInner108_37_54_0T hK28 hK36 false c hm v w rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
        hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA)
      (dAxisInner108_37_54_0T hK28 hK36 true c hm v w rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
        hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA)
          := by
  intro hK9 kSysNo14 rData
  let k0 := (((fullSysCoreWires mPayload + 61) + 54) + 14) + 37
  have hDMK : rData.DisjointWires rMK :=
    QRegExt.disjointWires_concat_left (h₁₂ := hCHSP) (QRegExt.disjointWires_concat_left
      (h₁₂ := hCHSum) (QRegExt.disjointWires_concat_left (h₁₂ := hCHPH)
        (QRegExt.disjointWires_concat_left (h₁₂ := hCH61) hCMK hH61MK) hPHMK) hSMK) hP37MK
  have hDA : rData.DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left (h₁₂ := hCHSP) (QRegExt.disjointWires_concat_left
      (h₁₂ := hCHSum) (QRegExt.disjointWires_concat_left (h₁₂ := hCHPH)
        (QRegExt.disjointWires_concat_left (h₁₂ := hCH61) hCA hH61A) hPHA) hSA) hP37A
  let tblData := tblMK108Data37 K 54 hK9 (le_refl 54) c hm w
  let uBase := (selNo14InAxisData37 (mPayload := mPayload) (H := 54)).embedUnitary
    (apexCatModAddZ kSysNo14 (axisDelta108No14 K 54 hK9 (le_refl 54) c hm w))
  have hBoth (isInv : Bool) :
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData (rMK.concat rAnc hMKA)
        (if isInv then uBase⁻¹ else uBase)
        (dAxisInner108_37_54_0T hK28 hK36 isInv c hm v w rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
          hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA)
            := by
    let Δ_s : BitAssignment kSysNo14 → ℤ :=
      fun γNo14 ↦ (if isInv then -1 else 1) * axisDelta108No14 K 54 hK9 (le_refl 54) c hm w γNo14
    have huEq : (if isInv then uBase⁻¹ else uBase) =
        (selNo14InAxisData37 (mPayload := mPayload) (H :=
          54)).embedUnitary (apexCatModAddZ kSysNo14 Δ_s) := by
      dsimp only [uBase, Δ_s]
      cases isInv
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      · simp only [↓reduceIte, neg_one_mul]
        rw [← embedUnitary_inv_eq,
          apexCatModAddZ_inv kSysNo14 (axisDelta108No14 K 54 hK9 (le_refl 54) c hm w)]
    have hPre := dAxisPre108KH_37_54_realizes (Var :=
      Var) hK28 hK36 (hmClean54 K) (le_refl 54) isInv c hm v w
      rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
      hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA
        hCHSum hCHSP hDMK
    have hAct := dAxisPre108KH_37_54_action_eq hK28 hK36 (le_refl 54) isInv c hm w
      rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
      hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCSum hSP37 hSMK hP37MK hMKA hCHSum hCHSP hDMK
    rw [huEq, dAxisInner108_37_54_0T, vepLockVal_eq, dMKXUncomputeAnc_54_0T]
    exact @DynCircuitExt.realizesCleanTableXUncompute Var _ _ n k0 K (6 + (K - 2)) _
      v rData rMK rAnc hDMK hDA hMKA tblData _ _
      (dAxisPre108KH_37_54 hK28 hK36 (hmClean54 K) (le_refl 54) isInv c hm v w rCore rHdr61 rPreHold
        rSum14 rPG37 rMK rAnc
        hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA)
      (dMKXUncomputeContAnc_54_0T (Var := Var) hK9 (h9_of_K28 K hK28) (le_refl 54) c hm w
        rCore rHdr61 rPreHold rAnc hCA hH61A hPHA)
      hPre hAct fun f ↦ dMKXUncomputeContAnc_54_0T_realizes_37 (Var := Var) hK9
        (h9_of_K28 K hK28) (le_refl 54) (le_refl 54) c hm w rCore rHdr61 rPreHold rSum14 rPG37
        rMK rAnc hCH61 hCHPH hCHSum hCHSP hCA hH61A hPHA hMKA f
  exact { fwd := hBoth false, inv := hBoth true }

theorem dAxisInner108_37_54_0T_cleanWp {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload K n : ℕ} [NeZero (2 ^ n)]
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister 54 n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister (6 + (K - 2)) n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCPH : rCore.DisjointWires rPreHold) (hHPH :
      rHdr61.DisjointWires rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hH61P37 : rHdr61.DisjointWires rPG37) (hPHP37 :
      rPreHold.DisjointWires rPG37)
    (hCMK : rCore.DisjointWires rMK) (hH61MK : rHdr61.DisjointWires rMK) (hPHMK :
      rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hCSum : rCore.DisjointWires rSum14) (hH61Sum : rHdr61.DisjointWires rSum14) (hPHSum :
      rPreHold.DisjointWires rSum14)
    (hSP37 : rSum14.DisjointWires rPG37) (hSMK : rSum14.DisjointWires rMK) (hP37MK :
      rPG37.DisjointWires rMK)
    (hSA : rSum14.DisjointWires rAnc) (hP37A : rPG37.DisjointWires rAnc) (hMKA : rMK.DisjointWires
      rAnc) :
    let hCHPH := QRegExt.disjointWires_concat_left hCPH hHPH
    let hCHSum :=
      QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCSum hH61Sum) hPHSum
    let hSysP37 :=
      rSysNo14_disj_rPG37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCP37 hH61P37 hPHP37
      hSP37
    CleanUnitaryWp (rMK.concat rAnc hMKA)
      (((rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).concat rPG37
        hSysP37).embedUnitary
        (apexCatModAdd37Z ((((fullSysCoreWires mPayload - 14) + 61) + 54) + 14)
          (fun γNo14 ↦
            (if isInv then -1 else 1) *
            axisDelta108No14 K 54 (hK9_of_K28 K hK28) (le_refl 54) c hm w γNo14)))
      (dAxisInner108_37_54_0T hK28 hK36 isInv c hm v w rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
        hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA)
          := by
  intro hCHPH hCHSum hSysP37
  have hCHSP : ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires
    rPG37 :=
    QRegExt.disjointWires_concat_left
      (QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCP37 hH61P37) hPHP37)
        hSP37
  have hSysLo11 : (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).DisjointWires
      (rCore.slice 0 11 (by
        have hc := core_ge_3954 mPayload
        omega)) :=
    QRegExt.disjointWires_concat_left
      (QRegExt.disjointWires_concat_left
        (QRegExt.disjointWires_concat_left
          (QRegExt.disjointWires_symm (slice_disj_of_le rCore 0 _ 14 _ (by decide)))
          (QRegExt.disjointWires_symm (hCH61.compose_left _)))
        (QRegExt.disjointWires_symm (hCPH.compose_left _)))
      (QRegExt.disjointWires_symm (hCSum.compose_left _))
  have hSysPG : (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).DisjointWires
      (rPGPad48_37 rCore rPG37 hCP37) :=
    QRegExt.disjointWires_concat_right hSysLo11 hSysP37
  have hp := dAxisInner108_37_54_0T_realizesPair (Var := Var) hK28 hK36 c hm v w
    rCore rHdr61 rPreHold rSum14 rPG37 rMK rAnc
    hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A hMKA hCHSum
      hCHSP
  have hU0 :
      (rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).embedUnitary
        ((selNo14InAxisData37 (mPayload := mPayload) (H := 54)).embedUnitary
          (apexCatModAddZ _ (axisDelta108No14 K 54 (hK9_of_K28 K hK28) (le_refl 54) c hm w))) =
      ((rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).concat rPG37 hSysP37).embedUnitary
        (apexCatModAdd37Z _ (axisDelta108No14 K 54 (hK9_of_K28 K hK28) (le_refl 54) c hm w)) := by
    rw [← QRegister.embedUnitary_compose,
      compose_selNo14InAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP hCP37
        hSysPG]
    exact (embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11 _ _ rPG37 _ hSysPG hSysP37 _
      (dvd_two_pow11_axisDelta108No14 K 54 (hK9_of_K28 K hK28) hK36 (le_refl 54) c hm w)).symm
  cases isInv
  · exact (CleanUnitaryWp.of_realizesClean hp.fwd).congr_unitary
      (hU0.trans (by simp only [Bool.false_eq_true, ↓reduceIte, one_mul]))
  · exact (CleanUnitaryWp.of_realizesClean hp.inv).congr_unitary (by
      rw [← embedUnitary_inv_symm, hU0, embedUnitary_inv_symm,
        apexCatModAdd37Z_inv_of_dvd11 (dvd_two_pow11_axisDelta108No14 K 54 (hK9_of_K28 K hK28) hK36
          (le_refl 54) c hm w)]
      simp only [↓reduceIte, neg_one_mul])

-- ============================================================================
-- Section 3: `withSharedBank114WState` (`266 T`) Even/Odd `108`-Leaf Kick
-- ============================================================================

theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := by decide

theorem u108_even_eq_u54 (c0 : Bool) (i₀ : Fin 64) (b₁ : ZMod 2) (k : Fin 54) :
    (if (c0 = true ∧ 2 * i₀.val + b₁.val = 2 * k.val) then (1 : ZMod 2) else 0) =
      ((if c0 = true then (1 : ZMod 2) else 0) * (if k.val = i₀.val then 1 else 0)) * (1 + b₁) := by
  rcases zmod2_eq_zero_or_one b₁ with rfl | rfl
  · rw [ZMod.val_zero, add_zero, add_zero, mul_one]
    by_cases hc : c0 = true
    · by_cases hk : k.val = i₀.val
      · rw [ite_pos_eq ⟨hc, by omega⟩, ite_pos_eq hc, ite_pos_eq hk, mul_one]
      · rw [ite_neg_eq fun ⟨_, h⟩ ↦ hk (by omega), ite_pos_eq hc, ite_neg_eq hk, mul_zero]
    · rw [ite_neg_eq fun h ↦ hc h.1, ite_neg_eq hc, zero_mul]
  · rw [ZMod.val_one, one_add_one_zmod2, mul_zero]
    exact ite_neg_eq fun ⟨_, h⟩ ↦ by omega

theorem u108_odd_eq_u54 (c0 : Bool) (i₀ : Fin 64) (b₁ : ZMod 2) (m : Fin 54) :
    (if (c0 = true ∧ 2 * i₀.val + b₁.val = 2 * m.val + 1) then (1 : ZMod 2) else 0) =
      ((if c0 = true then (1 : ZMod 2) else 0) * (if m.val = i₀.val then 1 else 0)) * b₁ := by
  rcases zmod2_eq_zero_or_one b₁ with rfl | rfl
  · rw [ZMod.val_zero, add_zero, mul_zero]
    exact ite_neg_eq fun ⟨_, h⟩ ↦ by omega
  · rw [ZMod.val_one, mul_one]
    by_cases hc : c0 = true
    · by_cases hm : m.val = i₀.val
      · rw [ite_pos_eq ⟨hc, by omega⟩, ite_pos_eq hc, ite_pos_eq hm, mul_one]
      · rw [ite_neg_eq fun ⟨_, h⟩ ↦ hm (by omega), ite_pos_eq hc, ite_neg_eq hm, mul_zero]
    · rw [ite_neg_eq fun h ↦ hc h.1, ite_neg_eq hc, zero_mul]

theorem regVal_rNucIdx_div2_eq {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γc : BitAssignment (fullSysCoreWires mPayload)) :
    let i₀ : Fin 64 := (basisBitsEquiv 6).symm
      (fun d : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩))
    let b₁ : ZMod 2 := γc (rNucIdx hm (QRegExt.idReg _) 1)
    regVal (rNucIdx hm (QRegExt.idReg _)) γc / 2 = 2 * i₀.val + b₁.val := by
  intro i₀ b₁
  have hd := SharedUnary54Trunc37.bitsVal8_decomp
    (fun i ↦ γc (rNucIdx hm (QRegExt.idReg _) i))
  have hb : (fun j : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg _) ⟨2 + j.val, by omega⟩)) =
      basisBits 6 i₀ := funext fun j ↦ by
    rw [show (⟨2 + j.val, by omega⟩ : Fin 8) = ⟨j.val + 2, by omega⟩ from
      Fin.ext (Nat.add_comm 2 j.val)]
    exact (NuclearTwistRealizes.basisBits_symm_apply 6
      (fun d : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)) j).symm
  rw [hb, bitsVal_basisBits6] at hd
  have hReg : regVal (rNucIdx hm (QRegExt.idReg _)) γc =
      4 * i₀.val + 2 * b₁.val + (γc (rNucIdx hm (QRegExt.idReg _) 0)).val := hd
  have hb0 := ZMod.val_lt (γc (rNucIdx hm (QRegExt.idReg _) 0))
  have hb1 := ZMod.val_lt b₁
  omega

/-- Even-indexed `54`-wire sub-register `k ↦ 2 * k` inside `108` unary wires (`s = false`
  leaves). -/
def even54In108 : QRegister 54 108 :=
  ⟨⟨fun k ↦ ⟨2 * k.val, Nat.mul_lt_mul_of_pos_left k.isLt zero_lt_two⟩,
    fun _ _ h ↦ Fin.ext (Nat.mul_left_cancel zero_lt_two (Fin.val_eq_of_eq h))⟩⟩

/-- Odd-indexed `54`-wire sub-register `m ↦ 2 * m + 1` inside `108` unary wires (`s = true`
  leaves). -/
def odd54In108 : QRegister 54 108 :=
  ⟨⟨fun m ↦ ⟨2 * m.val + 1, by
      have := m.isLt
      omega⟩,
    fun _ _ h ↦ Fin.ext <|
      Nat.mul_left_cancel zero_lt_two (Nat.add_right_cancel (Fin.val_eq_of_eq h))⟩⟩

theorem even54In108_disj_odd54In108 : even54In108.DisjointWires odd54In108 :=
  QRegister.disjoint_iff.mpr fun i j h ↦ by
    have hv : 2 * i.val = 2 * j.val + 1 := congrArg Fin.val h
    omega

/-- `7`-wire scratch slice `[0, 7)` of `rWExt` (`119 + 2 * K ≤ mWExt`). -/
def rS7Of114 {K mWExt n : ℕ} (hW : 119 + 2 * K ≤
    mWExt) (rWExt : QRegister mWExt n) : QRegister 7 n :=
  rWExt.slice 0 7 (by omega)

/-- `108`-wire unary bank slice `[7, 115)` of `rWExt` (`119 + 2 * K ≤ mWExt`). -/
def rU108Of114 {K mWExt n : ℕ} (hW : 119 + 2 * K ≤
    mWExt) (rWExt : QRegister mWExt n) : QRegister 108 n :=
  rWExt.slice 7 108 (by omega)

/-- `K`-wire table target slice `[115, 115 + K)` of `rWExt` (`119 + 2 * K ≤ mWExt`). -/
def rMKOf114 {K mWExt n : ℕ} (hW : 119 + 2 * K ≤
    mWExt) (rWExt : QRegister mWExt n) : QRegister K n :=
  rWExt.slice 115 K (by omega)

/-- `(6 + (K - 2))`-wire ancilla slice `[115 + K, 119 + 2 * K)` of `rWExt` (`28 ≤ K`, `119 + 2 *
  K ≤ mWExt`). -/
def rAncOf114 {K mWExt n : ℕ} (hK28 : 28 ≤ K) (hW : 119 + 2 * K ≤ mWExt)
    (rWExt : QRegister mWExt n) : QRegister (6 + (K - 2)) n :=
  rWExt.slice (115 + K) (6 + (K - 2)) (by omega)

theorem rHdr61_even_six {n : ℕ} (rS7 : QRegister 7 n) (rU108 : QRegister 108 n)
    (hSU : rS7.DisjointWires rU108) :
    (rS7.concat (rU108.compose even54In108) (hSU.compose_right even54In108)) ⟨6, by decide⟩ =
      rS7 6 := by
  have h6 : (⟨6, by decide⟩ : Fin 61) = Fin.castAdd 54 (⟨6, by decide⟩ : Fin 7) := Fin.ext rfl
  rw [h6, QRegister.concat_apply_left]
  rfl

theorem rHi54Of61_even_apply {n : ℕ} (rS7 : QRegister 7 n) (rU108 : QRegister 108 n)
    (hSU : rS7.DisjointWires rU108) (k : Fin 54) :
    rHi54Of61 (rS7.concat (rU108.compose even54In108) (hSU.compose_right even54In108)) k =
      rU108 (even54In108 k) := by
  exact (congrArg (rS7.concat (rU108.compose even54In108) (hSU.compose_right even54In108))
    (Fin.ext (by simp))).trans (QRegister.concat_apply_right rS7 (rU108.compose even54In108)
      (hSU.compose_right even54In108) k)

/-- Inner 3-axis Mode-1 `k_off` `T`-count using `withSharedBank114WState` (`266 T`) and `0-T` `H =
  54`
`X`-uncompute (`266 + 3 * (4 * K + 60 + tZeroMuxSkip (48 - K))`). -/
def tKickKoff114ZeroUnc54 (K : ℕ) : ℕ :=
  266 + 3 * (4 * K + 60 + tZeroMuxSkip (48 - K))

/-- Complete 3-axis Mode-1 `k_off` inner kick circuit on `(rCore ++ rPG37) ++ rSum42` (`28 ≤ K ≤
  36`,
`119 + 2 * K ≤ mWExt`), fusing `withSharedBank114WState` (`266 T`) and `dAxisInner108_37_54_0T`. -/
noncomputable def dKickKoff114ZeroUnc54 {Var : Type} {mPayload K mWExt n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hW : 119 + 2 * K ≤ mWExt)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var)
    (rSub : QRegister ((fullSysCoreWires mPayload + 37) + 42) n) (rWExt : QRegister mWExt n)
    (hSW : rSub.DisjointWires rWExt) : DynamicCircuit Var n :=
  vepLockVal <|
    let rCore := rSub.compose (rCoreInSub37 mPayload)
    let rPG37 := rSub.compose (rPG37InSub37 mPayload)
    let rS7 := rS7Of114 hW rWExt
    let rU108 := rU108Of114 hW rWExt
    let rMK := rMKOf114 hW rWExt
    let rAnc := rAncOf114 hK28 hW rWExt
    let hSU : rS7.DisjointWires rU108 := slice_disj_of_le rWExt 0 _ 7 _ (by decide)
    let hSMK : rS7.DisjointWires rMK := slice_disj_of_le rWExt 0 _ 115 _ (by decide)
    let hSAnc : rS7.DisjointWires rAnc := slice_disj_of_le rWExt 0 _ (115 + K) _ (by omega)
    let hUMK : rU108.DisjointWires rMK := slice_disj_of_le rWExt 7 _ 115 _ (by decide)
    let hUAnc : rU108.DisjointWires rAnc := slice_disj_of_le rWExt 7 _ (115 + K) _ (by omega)
    let hMKA : rMK.DisjointWires rAnc := slice_disj_of_le rWExt 115 _ (115 + K) _ (by omega)
    let rHdr61 := rS7.concat (rU108.compose even54In108) (hSU.compose_right even54In108)
    let rPreHold := rU108.compose odd54In108
    let rTail := rMK.concat rAnc hMKA
    let hCS7 : rCore.DisjointWires rS7 := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
    let hCU : rCore.DisjointWires rU108 :=
      (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
    let hCMK : rCore.DisjointWires rMK := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
    let hCA : rCore.DisjointWires rAnc := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
    let hCH61 : rCore.DisjointWires rHdr61 :=
      QRegExt.disjointWires_concat_right hCS7 (hCU.compose_right even54In108)
    let hCPH : rCore.DisjointWires rPreHold := hCU.compose_right odd54In108
    let hHPH : rHdr61.DisjointWires rPreHold :=
      QRegExt.disjointWires_concat_left (hSU.compose_right odd54In108)
        (disj_compose_both rU108 even54In108_disj_odd54In108)
    let hCHPH := QRegExt.disjointWires_concat_left (h₁₂ := hCH61) hCPH hHPH
    let hH61MK : rHdr61.DisjointWires rMK :=
      QRegExt.disjointWires_concat_left hSMK (hUMK.compose_left even54In108)
    let hPHMK : rPreHold.DisjointWires rMK := hUMK.compose_left odd54In108
    let hH61A : rHdr61.DisjointWires rAnc :=
      QRegExt.disjointWires_concat_left hSAnc (hUAnc.compose_left even54In108)
    let hPHA : rPreHold.DisjointWires rAnc := hUAnc.compose_left odd54In108
    let hCTail : rCore.DisjointWires rTail := QRegExt.disjointWires_concat_right hCMK hCA
    let hUTail : rU108.DisjointWires rTail := QRegExt.disjointWires_concat_right hUMK hUAnc
    let dAx (w : Fin 3) :=
      dAxisInner108_37_54_0T hK28 hK36 isInv (truncWCfg K c) hm v w
        rCore rHdr61 rPreHold (rSub.compose (rSum14InSub37 mPayload w)) rPG37 rMK rAnc
        hCH61 hCHPH (disj_compose_both rSub (rCoreInSub37_disj_rPG37InSub37 mPayload)) hCMK
        hH61MK hPHMK hCA hH61A hPHA
        (disj_compose_both rSub (rCoreInSub37_disj_rSum14InSub37 mPayload w))
        (disj_compose_both rSub (rSum14InSub37_disj_rPG37InSub37 mPayload w))
        ((hSW.compose_left (rSum14InSub37 mPayload w)).compose_right _)
        ((hSW.compose_left (rPG37InSub37 mPayload)).compose_right _)
        ((hSW.compose_left (rSum14InSub37 mPayload w)).compose_right _)
        ((hSW.compose_left (rPG37InSub37 mPayload)).compose_right _)
        hMKA
    withSharedBank114WState hm (by omega : 3 ≤ K + (6 + (K - 2))) v rCore rS7 rU108 rTail
      hCS7 hCU hSU hCTail hUTail
      (if isInv then .seq (dAx 2) (.seq (dAx 1) (dAx 0)) else .seq (dAx 0) (.seq (dAx 1) (dAx 2)))

private theorem count_seq3_toff {Var : Type} {n : ℕ} {d₁ d₂ d₃ : DynamicCircuit Var n}
    (h₁ : d₁.count TOFF = 0) (h₂ : d₂.count TOFF = 0) (h₃ : d₃.count TOFF = 0) :
    (DynamicCircuit.seq d₁ (.seq d₂ d₃)).count TOFF = 0 := by
  simp only [count_dyn_seq, h₁, h₂, h₃]

private theorem count_seq3_t_bound {Var : Type} {n M : ℕ} {d₁ d₂ d₃ : DynamicCircuit Var n}
    (h₁ : d₁.count T ≤ M) (h₂ : d₂.count T ≤ M) (h₃ : d₃.count T ≤ M) :
    266 + (DynamicCircuit.seq d₁ (.seq d₂ d₃)).count T ≤ 266 + 3 * M := by
  simp only [count_dyn_seq]
  omega

theorem dKickKoff114ZeroUnc54_counts {Var : Type} {mPayload K mWExt n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hW : 119 + 2 * K ≤ mWExt)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var)
    (rSub : QRegister ((fullSysCoreWires mPayload + 37) + 42) n) (rWExt : QRegister mWExt n)
    (hSW : rSub.DisjointWires rWExt) :
    let d := dKickKoff114ZeroUnc54 hK28 hK36 hW isInv c hm v rSub rWExt hSW
    d.count TOFF = 0 ∧ d.count T ≤ tKickKoff114ZeroUnc54 K := by
  dsimp only [tKickKoff114ZeroUnc54]
  rw [dKickKoff114ZeroUnc54, vepLockVal_eq]
  dsimp only
  refine ⟨(count_withSharedBank114WState_toff _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_,
    (Nat.le_of_eq (count_withSharedBank114WState_t _ _ _ _ _ _ _ _ _ _ _ _ _)).trans ?_⟩
  · cases isInv with
    | false =>
        refine (congrArg (DynamicCircuit.count TOFF) (ite_eq_right Bool.false_ne_true)).trans
          (count_seq3_toff ?_ ?_ ?_)
        · apply count_dAxisInner108_37_54_0T_toff
        · apply count_dAxisInner108_37_54_0T_toff
        · apply count_dAxisInner108_37_54_0T_toff
    | true =>
        refine (congrArg (DynamicCircuit.count TOFF) (ite_eq_left rfl)).trans
          (count_seq3_toff ?_ ?_ ?_)
        · apply count_dAxisInner108_37_54_0T_toff
        · apply count_dAxisInner108_37_54_0T_toff
        · apply count_dAxisInner108_37_54_0T_toff
  · cases isInv with
    | false =>
        refine (Nat.le_of_eq (congrArg (266 + DynamicCircuit.count T ·)
          (ite_eq_right Bool.false_ne_true))).trans (count_seq3_t_bound ?_ ?_ ?_)
        · apply count_dAxisInner108_37_54_0T_t_le
        · apply count_dAxisInner108_37_54_0T_t_le
        · apply count_dAxisInner108_37_54_0T_t_le
    | true =>
        refine (Nat.le_of_eq (congrArg (266 + DynamicCircuit.count T ·)
          (ite_eq_left rfl))).trans (count_seq3_t_bound ?_ ?_ ?_)
        · apply count_dAxisInner108_37_54_0T_t_le
        · apply count_dAxisInner108_37_54_0T_t_le
        · apply count_dAxisInner108_37_54_0T_t_le

theorem disjoint_image_of_disj {a b n : ℕ} {r₁ : QRegister a n} {r₂ : QRegister b n}
    (h : r₁.DisjointWires r₂) : Disjoint r₁.image r₂.image := by
  refine Finset.disjoint_left.mpr fun u h₁ h₂ ↦ ?_
  obtain ⟨i, rfl⟩ := (QRegister.mem_image r₁ u).mp h₁
  obtain ⟨j, hj⟩ := (QRegister.mem_image r₂ (r₁ i)).mp h₂
  exact h.ne i j hj.symm

theorem rBank114_sub_rWExt {K mWExt n : ℕ} (hK28 : 28 ≤ K) (hW : 119 + 2 * K ≤ mWExt)
    (rWExt : QRegister mWExt n) :
    let rS7 := rS7Of114 hW rWExt
    let rU108 := rU108Of114 hW rWExt
    let rMK := rMKOf114 hW rWExt
    let rAnc := rAncOf114 hK28 hW rWExt
    let hSU : rS7.DisjointWires rU108 := slice_disj_of_le rWExt 0 _ 7 _ (by decide)
    let hSMK : rS7.DisjointWires rMK := slice_disj_of_le rWExt 0 _ 115 _ (by decide)
    let hSAnc : rS7.DisjointWires rAnc := slice_disj_of_le rWExt 0 _ (115 + K) _ (by omega)
    let hUMK : rU108.DisjointWires rMK := slice_disj_of_le rWExt 7 _ 115 _ (by decide)
    let hUAnc : rU108.DisjointWires rAnc := slice_disj_of_le rWExt 7 _ (115 + K) _ (by omega)
    let hMKA : rMK.DisjointWires rAnc := slice_disj_of_le rWExt 115 _ (115 + K) _ (by omega)
    let rTail := rMK.concat rAnc hMKA
    let hSTail := QRegExt.disjointWires_concat_right hSMK hSAnc
    let hUTail := QRegExt.disjointWires_concat_right hUMK hUAnc
    ((rS7.concat rU108 hSU).concat rTail (QRegExt.disjointWires_concat_left hSTail hUTail)).image ⊆
      rWExt.image := by
  intro rS7 rU108 rMK rAnc hSU hSMK hSAnc hUMK hUAnc hMKA rTail hSTail hUTail
  change ((rS7.concat rU108 hSU).concat (rMK.concat rAnc hMKA) _).image ⊆ rWExt.image
  simp only [QRegExt.image_concat, Finset.union_subset_iff]
  exact ⟨⟨QRegister.image_compose_subset rWExt _, QRegister.image_compose_subset rWExt _⟩,
    QRegister.image_compose_subset rWExt _, QRegister.image_compose_subset rWExt _⟩

theorem dKickKoff114ZeroUnc54_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload K mWExt n : ℕ} [NeZero (2 ^ n)]
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hW : 119 + 2 * K ≤ mWExt)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var)
    (rSub : QRegister ((fullSysCoreWires mPayload + 37) + 42) n) (rWExt : QRegister mWExt n)
    (hSW : rSub.DisjointWires rWExt) :
    RealizesCleanPair rSub rWExt (uKickKoffSub37 hm (truncWCfg K c))
      (dKickKoff114ZeroUnc54 hK28 hK36 hW false c hm v rSub rWExt hSW)
      (dKickKoff114ZeroUnc54 hK28 hK36 hW true c hm v rSub rWExt hSW) := by
  let rCore := rSub.compose (rCoreInSub37 mPayload)
  let rPG37 := rSub.compose (rPG37InSub37 mPayload)
  let rCat34 := rPG37.slice 0 34 (by decide)
  let rSum14 (w : Fin 3) := rSub.compose (rSum14InSub37 mPayload w)
  let rS7 := rS7Of114 hW rWExt
  let rU108 := rU108Of114 hW rWExt
  let rMK := rMKOf114 hW rWExt
  let rAnc := rAncOf114 hK28 hW rWExt
  let hSU : rS7.DisjointWires rU108 := slice_disj_of_le rWExt 0 _ 7 _ (by decide)
  let hSMK : rS7.DisjointWires rMK := slice_disj_of_le rWExt 0 _ 115 _ (by decide)
  let hSAnc : rS7.DisjointWires rAnc := slice_disj_of_le rWExt 0 _ (115 + K) _ (by omega)
  let hUMK : rU108.DisjointWires rMK := slice_disj_of_le rWExt 7 _ 115 _ (by decide)
  let hUAnc : rU108.DisjointWires rAnc := slice_disj_of_le rWExt 7 _ (115 + K) _ (by omega)
  let hMKA : rMK.DisjointWires rAnc := slice_disj_of_le rWExt 115 _ (115 + K) _ (by omega)
  let rHdr61 := rS7.concat (rU108.compose even54In108) (hSU.compose_right even54In108)
  let rPreHold := rU108.compose odd54In108
  let rTail := rMK.concat rAnc hMKA
  let hCS7 : rCore.DisjointWires rS7 := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
  let hCU : rCore.DisjointWires rU108 := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
  let hCMK : rCore.DisjointWires rMK := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
  let hCA : rCore.DisjointWires rAnc := (hSW.compose_left (rCoreInSub37 mPayload)).compose_right _
  let hCH61 : rCore.DisjointWires rHdr61 :=
    QRegExt.disjointWires_concat_right hCS7 (hCU.compose_right even54In108)
  let hCPH : rCore.DisjointWires rPreHold := hCU.compose_right odd54In108
  let hHPH : rHdr61.DisjointWires rPreHold :=
    QRegExt.disjointWires_concat_left (hSU.compose_right odd54In108)
      (disj_compose_both rU108 even54In108_disj_odd54In108)
  let hCHPH := QRegExt.disjointWires_concat_left (h₁₂ := hCH61) hCPH hHPH
  let hH61MK : rHdr61.DisjointWires rMK :=
    QRegExt.disjointWires_concat_left hSMK (hUMK.compose_left even54In108)
  let hPHMK : rPreHold.DisjointWires rMK := hUMK.compose_left odd54In108
  let hH61A : rHdr61.DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left hSAnc (hUAnc.compose_left even54In108)
  let hPHA : rPreHold.DisjointWires rAnc := hUAnc.compose_left odd54In108
  let hCTail : rCore.DisjointWires rTail := QRegExt.disjointWires_concat_right hCMK hCA
  let hSTail : rS7.DisjointWires rTail := QRegExt.disjointWires_concat_right hSMK hSAnc
  let hUTail : rU108.DisjointWires rTail := QRegExt.disjointWires_concat_right hUMK hUAnc
  let hCP37 := disj_compose_both rSub (rCoreInSub37_disj_rPG37InSub37 mPayload)
  let hP37S7 : rPG37.DisjointWires rS7 := (hSW.compose_left (rPG37InSub37 mPayload)).compose_right _
  let hP37U : rPG37.DisjointWires rU108 :=
    (hSW.compose_left (rPG37InSub37 mPayload)).compose_right _
  let hH61P37 : rHdr61.DisjointWires rPG37 :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_symm hP37S7)
      ((QRegExt.disjointWires_symm hP37U).compose_left even54In108)
  let hPHP37 : rPreHold.DisjointWires rPG37 :=
    (QRegExt.disjointWires_symm hP37U).compose_left odd54In108
  let hP37MK : rPG37.DisjointWires rMK := (hSW.compose_left (rPG37InSub37 mPayload)).compose_right _
  let hP37A : rPG37.DisjointWires rAnc := (hSW.compose_left (rPG37InSub37 mPayload)).compose_right _
  let hCSum (w : Fin 3) := disj_compose_both rSub (rCoreInSub37_disj_rSum14InSub37 mPayload w)
  let hSP37 (w : Fin 3) := disj_compose_both rSub (rSum14InSub37_disj_rPG37InSub37 mPayload w)
  let hSumS7 (w : Fin 3) : (rSum14 w).DisjointWires rS7 :=
    (hSW.compose_left (rSum14InSub37 mPayload w)).compose_right _
  let hSumU (w : Fin 3) : (rSum14 w).DisjointWires rU108 :=
    (hSW.compose_left (rSum14InSub37 mPayload w)).compose_right _
  let hSumMK (w : Fin 3) : (rSum14 w).DisjointWires rMK :=
    (hSW.compose_left (rSum14InSub37 mPayload w)).compose_right _
  let hSumA (w : Fin 3) : (rSum14 w).DisjointWires rAnc :=
    (hSW.compose_left (rSum14InSub37 mPayload w)).compose_right _
  let hH61Sum (w : Fin 3) : rHdr61.DisjointWires (rSum14 w) :=
    QRegExt.disjointWires_concat_left (hSumS7 w).symm ((QRegExt.disjointWires_symm (hSumU
      w)).compose_left even54In108)
  let hPHSum (w : Fin 3) : rPreHold.DisjointWires (rSum14 w) :=
    (QRegExt.disjointWires_symm (hSumU w)).compose_left odd54In108
  let hCHSum (w : Fin 3) := QRegExt.disjointWires_concat_left (h₁₂ := hCHPH)
    (QRegExt.disjointWires_concat_left (h₁₂ := hCH61) (hCSum w) (hH61Sum w)) (hPHSum w)
  let rSys (w : Fin 3) := rSysNo14 rCore rHdr61 rPreHold (rSum14 w) hCH61 hCHPH (hCHSum w)
  let hSysP37 (w : Fin 3) := rSysNo14_disj_rPG37 rCore rHdr61 rPreHold (rSum14 w) rPG37
    hCH61 hCHPH (hCHSum w) hCP37 hH61P37 hPHP37 (hSP37 w)
  let S : Finset (Wire n) := Finset.univ \ rCat34.image
  have hMA_S : rTail.image ⊆ S :=
    image_subset_compl_of_disj ((QRegExt.disjointWires_symm (QRegExt.disjointWires_concat_right
      hP37MK hP37A)).compose_right _)
  have hCM : Disjoint rCore.image rCat34.image := disjoint_image_of_disj (hCP37.compose_right _)
  have hSM : Disjoint rS7.image rCat34.image :=
    disjoint_image_of_disj ((QRegExt.disjointWires_symm hP37S7).compose_right _)
  have hUM : Disjoint rU108.image rCat34.image :=
    disjoint_image_of_disj ((QRegExt.disjointWires_symm hP37U).compose_right _)
  have hBoth (isInv : Bool) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWExt
      (if isInv then (uKickKoffSub37 hm (truncWCfg K c))⁻¹ else uKickKoffSub37 hm (truncWCfg K c))
      (dKickKoff114ZeroUnc54 hK28 hK36 hW isInv c hm v rSub rWExt hSW) := by
    let Δ_hdr (w : Fin 3) (γNo14 : BitAssignment ((((fullSysCoreWires mPayload - 14) + 61) + 54) +
      14)) : ℤ :=
      (if isInv then -1 else 1) *
        axisDelta108No14 K 54 (hK9_of_K28 K hK28) (le_refl 54) (truncWCfg K c) hm w γNo14
    let U_ax (w : Fin 3) : Unitary (2 ^ n) :=
      ((rSys w).concat rPG37 (hSysP37 w)).embedUnitary (apexCatModAdd37Z _ (Δ_hdr w))
    let dFn_hdr (w : Fin 3) (ξ : BitAssignment n) : ℤ := Δ_hdr w (fun i ↦ ξ ((rSys w) i))
    let dAx (w : Fin 3) := dAxisInner108_37_54_0T hK28 hK36 isInv (truncWCfg K c) hm v w
      rCore rHdr61 rPreHold (rSum14 w) rPG37 rMK rAnc hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A
        hPHA
      (hCSum w) (hSP37 w) (hSumMK w) hP37MK (hSumA w) hP37A hMKA
    have hwAx (w : Fin 3) : CleanUnitaryWp rTail (U_ax w) (dAx w) :=
      dAxisInner108_37_54_0T_cleanWp hK28 hK36 isInv (truncWCfg K c) hm v w
        rCore rHdr61 rPreHold (rSum14 w) rPG37 rMK rAnc hCH61 hCPH hHPH hCP37 hH61P37 hPHP37
        hCMK hH61MK hPHMK hCA hH61A hPHA (hCSum w) (hH61Sum w) (hPHSum w)
        (hSP37 w) (hSumMK w) hP37MK (hSumA w) hP37A hMKA
    have hEvAx (w : Fin 3) (ξ : BitAssignment n) : (U_ax w).1.mulVec (basisKet ξ) =
        phiCat34 (dFn_hdr w ξ) (regVal rCat34 ξ) • basisKet (shiftCatKet rCat34 ξ (shiftNat34
          (dFn_hdr w ξ))) :=
      apexCatModAdd37Z_mulVec_basisKet (rSys w) rPG37 (hSysP37 w) (Δ_hdr w) ξ
    have hInvAx (w : Fin 3) (ξ : BitAssignment n) (N : ℕ) : dFn_hdr w (shiftCatKet rCat34 ξ N) =
      dFn_hdr w ξ :=
      congrArg (Δ_hdr w) (funext fun i ↦
        shiftCatKet_outside rCat34 ξ N (((hSysP37 w).compose_right _).apply_not_mem_right i))
    have hdAx (w : Fin 3) : DiagOn S (U_ax w).1 :=
      diagOn_compl_of_mulVec_shiftCatKet rCat34 (fun ξ ↦ ⟨_, _, hEvAx w ξ⟩)
    let uInner : Unitary (2 ^ n) :=
      if isInv then U_ax 0 * (U_ax 1 * U_ax 2) else U_ax 2 * (U_ax 1 * U_ax 0)
    let dInner : DynamicCircuit Var n :=
      if isInv then .seq (dAx 2) (.seq (dAx 1) (dAx 0)) else .seq (dAx 0) (.seq (dAx 1) (dAx 2))
    have hwIn : CleanUnitaryWp rTail uInner dInner := by
      dsimp only [uInner, dInner]
      cases isInv
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ((hwAx 0).seq_of_diag ((hwAx 1).seq_of_diag (hwAx 2) ((hdAx 1).anti hMA_S)) ((hdAx
          0).anti hMA_S)).congr_unitary
          (mul_assoc (U_ax 2) (U_ax 1) (U_ax 0))
      · simp only [↓reduceIte]
        exact ((hwAx 2).seq_of_diag ((hwAx 1).seq_of_diag (hwAx 0) ((hdAx 1).anti hMA_S)) ((hdAx
          2).anti hMA_S)).congr_unitary
          (mul_assoc (U_ax 0) (U_ax 1) (U_ax 2))
    have hEvIn (ξ : BitAssignment n) : uInner.1.mulVec (basisKet ξ) =
        threeAxis37Phi isInv (dFn_hdr 0 ξ) (dFn_hdr 1 ξ) (dFn_hdr 2 ξ) (regVal rCat34 ξ) •
          basisKet (shiftCatKet rCat34 ξ (threeAxis37Shift isInv (dFn_hdr 0 ξ) (dFn_hdr 1 ξ)
            (dFn_hdr 2 ξ))) :=
      threeAxis37_mulVec_basisKet rPG37 isInv U_ax dFn_hdr hEvAx hInvAx ξ
    obtain ⟨U_sh, φ_sh, f_sh, hPermSh, hOutSh, hCleanSh, hEvalSh⟩ :=
      withSharedBank114WState_phasePerm_const hm (by omega : 3 ≤ K + (6 + (K - 2))) v
        rCore rS7 rU108 rTail hCS7 hCU hSU hCTail hSTail hUTail hCM hSM hUM
        hEvIn (fun β u hu ↦ shiftCatKet_outside rCat34 β _ hu)
        (cleanUnitaryEquiv_of_cleanUnitaryWp hwIn)
    have hdEq : dKickKoff114ZeroUnc54 hK28 hK36 hW isInv c hm v rSub rWExt hSW =
        withSharedBank114WState hm (by omega : 3 ≤ K + (6 + (K - 2))) v rCore rS7 rU108 rTail
          hCS7 hCU hSU hCTail hUTail dInner := by
      rw [dKickKoff114ZeroUnc54, vepLockVal_eq]
    rw [hdEq]
    have hwWExt := (cleanUnitaryWp_of_cleanUnitaryEquiv hCleanSh).mono_workspace
      (rBank114_sub_rWExt hK28 hW rWExt)
    let uTargetSub : Unitary (2 ^ ((fullSysCoreWires mPayload + 37) + 42)) :=
      if isInv then (uKickKoffSub37 hm (truncWCfg K c))⁻¹ else uKickKoffSub37 hm (truncWCfg K c)
    let Δ_core (w : Fin 3) (γ14 : BitAssignment (fullSysCoreWires mPayload + 14)) : ℤ :=
      (if isInv then -1 else 1) * uInnerKoffSlot2DeltaGen (truncWCfg K c) hm w γ14
    let hCSP (w : Fin 3) := QRegExt.disjointWires_concat_left (h₁₂ := hCSum w) hCP37 (hSP37 w)
    let U_core (w : Fin 3) : Unitary (2 ^ n) :=
      ((rCore.concat (rSum14 w) (hCSum w)).concat rPG37 (hCSP w)).embedUnitary
        (apexCatModAdd37Z (fullSysCoreWires mPayload + 14) (Δ_core w))
    let dFn_core (w : Fin 3) (ξ : BitAssignment n) : ℤ :=
      Δ_core w (fun i ↦ ξ ((rCore.concat (rSum14 w) (hCSum w)) i))
    have hU_core_eq (w : Fin 3) : rSub.embedUnitary
        (if isInv then (uKickAxisSub37 hm (truncWCfg K c) w)⁻¹ else
          uKickAxisSub37 hm (truncWCfg K c) w) = U_core w := by
      dsimp only [uKickAxisSub37, U_core, Δ_core]
      cases isInv
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [← QRegister.embedUnitary_compose, compose_rCSP37InSub37 rSub w]
      · simp only [↓reduceIte, neg_one_mul]
        rw [← embedUnitary_inv_symm rSub, ← QRegister.embedUnitary_compose,
          compose_rCSP37InSub37 rSub w,
          embedUnitary_inv_symm,
            apexCatModAdd37Z_inv_of_dvd11 (dvd11_uInnerKoffSlot2DeltaGen_truncWCfg hK36 c hm w)]
    have huTargetEmbed : rSub.embedUnitary uTargetSub =
        (if isInv then U_core 0 * (U_core 1 * U_core 2) else U_core 2 * (U_core 1 * U_core 0)) := by
      dsimp only [uTargetSub, uKickKoffSub37]
      cases isInv
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← hU_core_eq 2, ← hU_core_eq 1,
          ← hU_core_eq 0]
        simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, mul_assoc, QRegister.embedUnitary_mul,
          QRegister.embedUnitary_mul,
          ← hU_core_eq 0, ← hU_core_eq 1, ← hU_core_eq 2]
        simp only [↓reduceIte]
    have hEvCore (w : Fin 3) (ξ : BitAssignment n) : (U_core w).1.mulVec (basisKet ξ) =
        phiCat34 (dFn_core w ξ) (regVal rCat34 ξ) • basisKet (shiftCatKet rCat34 ξ (shiftNat34
          (dFn_core w ξ))) :=
      apexCatModAdd37Z_mulVec_basisKet (rCore.concat (rSum14 w) (hCSum w)) rPG37 (hCSP w) (Δ_core w)
        ξ
    have hInvCore (w : Fin 3) (ξ : BitAssignment n) (N : ℕ) : dFn_core w (shiftCatKet rCat34 ξ N) =
      dFn_core w ξ :=
      congrArg (Δ_core w) (funext fun i ↦
        shiftCatKet_outside rCat34 ξ N (((hCSP w).compose_right _).apply_not_mem_right i))
    refine (hwWExt.congr_cleanKet (u₂ := rSub.embedUnitary uTargetSub) ?_).to_realizesClean
    intro β hzW
    have hzSub {m : ℕ} (r : QRegister m n) (hr : r.image ⊆ rWExt.image) (q : Fin m) : β (r q) = 0 :=
      by
      obtain ⟨idx, hidx⟩ :=
        (QRegister.mem_image rWExt _).mp (hr ((QRegister.mem_image r _).mpr ⟨q, rfl⟩))
      rw [← hidx]
      exact hzW idx
    obtain ⟨β_bank, hφSh, hOnCat, hOutBank, hVH, hU108⟩ := hEvalSh β
      (hzSub rS7 (QRegister.image_compose_subset rWExt _))
      (hzSub rU108 (QRegister.image_compose_subset rWExt _))
    have hSubOut (u : Wire n) (hu : u ∈ rSub.image) : β_bank u = β u := by
      obtain ⟨idx, rfl⟩ := (QRegister.mem_image rSub _).mp hu
      exact hOutBank (rSub idx)
        ((hSW.compose_right _).apply_not_mem_right idx)
        ((hSW.compose_right _).apply_not_mem_right idx)
    have hCorePt (q : Fin (fullSysCoreWires mPayload)) : β_bank (rCore q) = β (rCore q) :=
      hSubOut (rCore q) (QRegister.image_compose_subset rSub _ ((QRegister.mem_image rCore _).mpr
        ⟨q, rfl⟩))
    have hCat34Val : regVal rCat34 β_bank = regVal rCat34 β :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rCat34 fun p ↦
        hSubOut (rCat34 p)
        (QRegister.image_compose_subset rSub _
          (QRegister.image_compose_subset rPG37 _ ((QRegister.mem_image rCat34 _).mpr ⟨p, rfl⟩)))
    have hfSh_eq : f_sh β =
        shiftCatKet rCat34 β (threeAxis37Shift isInv (dFn_hdr 0 β_bank) (dFn_hdr 1 β_bank) (dFn_hdr
          2 β_bank)) := by
      funext u
      by_cases hu : u ∈ rCat34.image
      · rw [hOnCat u hu]
        obtain ⟨p, rfl⟩ := (QRegister.mem_image rCat34 u).mp hu
        dsimp only [shiftCatKet]
        rw [dite_eq_left ⟨p, rfl⟩, dite_eq_left ⟨p, rfl⟩]
        refine congrArg (fun idx : Fin (2 ^ 34) ↦ basisBits 34 idx _) (Fin.ext ?_)
        dsimp only
        rw [hCat34Val]
      · rw [hOutSh β u hu, shiftCatKet_outside rCat34 β _ hu]
    let γc : BitAssignment (fullSysCoreWires mPayload) := fun q ↦ β (rCore q)
    let i₀ : Fin 64 := (basisBitsEquiv 6).symm
      (fun d : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩))
    let b₁ : ZMod 2 := γc (rNucIdx hm (QRegExt.idReg _) 1)
    have hdiv : regVal (rNucIdx hm (QRegExt.idReg _)) (fun q ↦ β (rCore q)) / 2 =
        2 * i₀.val + b₁.val := regVal_rNucIdx_div2_eq hm γc
    have hDeltaEq (w : Fin 3) : dFn_hdr w β_bank = dFn_core w β := by
      dsimp only [dFn_hdr, dFn_core, Δ_hdr, Δ_core]
      refine congrArg ((if isInv then (-1 : ℤ) else 1) * ·)
        ((axisDelta108No14_on_hdr_eq (hK9_of_K28 K hK28) (by omega : K ≤ 48) (le_refl 54) c hm w
          rCore rHdr61 rPreHold (rSum14 w) hCH61 hCHPH (hCHSum w) (hCSum w) β_bank
          ?_ ?_ (fun k hk ↦ absurd hk (not_le_of_gt k.isLt)) ?_).trans ?_)
      · rw [rHdr61_even_six rS7 rU108 hSU]
        simp only [hCorePt]
        exact hVH
      · intro k _
        simp only [hCorePt]
        rw [rHi54Of61_even_apply rS7 rU108 hSU k, hU108 (even54In108 k), hdiv]
        exact u108_even_eq_u54 (coin0Active γc) i₀ b₁ k
      · intro m
        simp only [hCorePt]
        rw [QRegister.compose_apply, hU108 (odd54In108 m), hdiv]
        exact u108_odd_eq_u54 (coin0Active γc) i₀ b₁ m
      · exact congrArg (uInnerKoffSlot2DeltaGen (truncWCfg K c) hm w)
          (funext fun p ↦ hSubOut ((rCore.concat (rSum14 w) (hCSum w)) p)
            (Or.elim (Finset.mem_union.mp (QRegExt.image_concat _ _ _ ▸
                (QRegister.mem_image _ _).mpr ⟨p, rfl⟩))
              (fun h ↦ QRegister.image_compose_subset rSub _ h)
              (fun h ↦ QRegister.image_compose_subset rSub _ h)))
    rw [hPermSh β, hφSh, hfSh_eq, huTargetEmbed,
      threeAxis37_mulVec_basisKet rPG37 isInv U_core dFn_core hEvCore hInvCore β,
      hDeltaEq 0, hDeltaEq 1, hDeltaEq 2, hCat34Val]
  exact { fwd := hBoth false, inv := hBoth true }

-- ============================================================================
-- Section 4: `dTwHeld114ZeroUnc54`, `tTw114ZeroUnc54` & `AsymHeldTw` Specs
-- ============================================================================

/-- Complete `coin = 0`-only `37`-catalyst stream-held nuclear twist circuit fusing
`withSharedBank114WState` (`266 T`) and `0-T` `H = 54` `X`-uncomputation (`558 +
tKickKoff114ZeroUnc54 K` `T`). -/
noncomputable def dTwHeld114ZeroUnc54 {Var : Type} {K mWExt n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hW : 119 + 2 * K ≤ mWExt)
    (isInv : Bool) (c : Configuration) (v : Var)
    (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rWExt : QRegister mWExt n)
    (hSW : rSub.DisjointWires rWExt) : DynamicCircuit Var n :=
  if isInv then
    .seq (dKickKoff114ZeroUnc54 hK28 hK36 hW true c (by decide : 22 ≤ 80) v rSub rWExt hSW)
      (dPref37HadCut (by omega : 56 ≤ mWExt) true v rSub rWExt hSW)
  else
    .seq (dPref37HadCut (by omega : 56 ≤ mWExt) false v rSub rWExt hSW)
      (dKickKoff114ZeroUnc54 hK28 hK36 hW false c (by decide : 22 ≤ 80) v rSub rWExt hSW)

theorem dTwHeld114ZeroUnc54_counts {Var : Type} {K mWExt n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hW : 119 + 2 * K ≤ mWExt)
    (isInv : Bool) (c : Configuration) (v : Var)
    (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rWExt : QRegister mWExt n)
    (hSW : rSub.DisjointWires rWExt) :
    let d := dTwHeld114ZeroUnc54 hK28 hK36 hW isInv c v rSub rWExt hSW
    d.count TOFF = 0 ∧ d.count T ≤ 558 + tKickKoff114ZeroUnc54 K := by
  dsimp only [dTwHeld114ZeroUnc54]
  have hK :=
    dKickKoff114ZeroUnc54_counts hK28 hK36 hW isInv c (by decide : 22 ≤ 80) v rSub rWExt hSW
  have hPT := count_dPref37HadCut_t_le (by omega : 56 ≤ mWExt) isInv v rSub rWExt hSW
  have hP0 := count_dPref37HadCut_toff (by omega : 56 ≤ mWExt) isInv v rSub rWExt hSW
  cases isInv
  · simp only [Bool.false_eq_true, ↓reduceIte, count_dyn_seq]
    exact ⟨by omega, by omega⟩
  · simp only [↓reduceIte, count_dyn_seq]
    exact ⟨by omega, by omega⟩

theorem dTwHeld114ZeroUnc54_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {K mWExt n : ℕ} [NeZero (2 ^ n)]
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hW : 119 + 2 * K ≤ mWExt)
    (c : Configuration) (v : Var)
    (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rWExt : QRegister mWExt n)
    (hSW : rSub.DisjointWires rWExt) :
    RealizesCleanPair rSub rWExt (uTwHeldSum42Sub37 uPref37HadCut K c)
      (dTwHeld114ZeroUnc54 hK28 hK36 hW false c v rSub rWExt hSW)
      (dTwHeld114ZeroUnc54 hK28 hK36 hW true c v rSub rWExt hSW) := by
  have hpP := dPref37HadCut_realizesPair (by omega : 56 ≤ mWExt) v rSub rWExt hSW
  have hpK :=
    dKickKoff114ZeroUnc54_realizesPair hK28 hK36 hW c (by decide : 22 ≤ 80) v rSub rWExt hSW
  refine { fwd := hpP.fwd.seq hSW hpK.fwd, inv := ?_ }
  change DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rSub rWExt
    (uKickKoffSub37 (by decide : 22 ≤ 80) (truncWCfg K c) * uPref37Sub37)⁻¹ _
  rw [_root_.mul_inv_rev]
  exact hpK.inv.seq hSW hpP.inv

/-- `coin = 0`-only `37`-catalyst `114`-bank + `0-T`-uncompute nuclear twist pair `T`-count
(`9,400 .. 12,280 T` for `W = 28..36`). -/
def tTw114ZeroUnc54 (W : ℕ) : ℕ := 2 * (558 + tKickKoff114ZeroUnc54 W)

noncomputable def mkSlot3InnerGenAsymHeldTwSpec114ZeroUnc54_11_14_mWor (W mWork : ℕ)
    (hW28 : 28 ≤ W) (hW36 : W ≤ 36) (hmTw : 108 + 2 * W ≤ mWork) :
    Slot3InnerGenAsymHeldTwSpec_mWork mWork (twHeld37Wide54Spec190 W hW28 hW36).uTwHeldSub37
      (tTw114ZeroUnc54 W) (tTw114ZeroUnc54 W) where
  dTwCtrl c {_ _} v rSub rW hSW := dTwHeld114ZeroUnc54 hW28 hW36 (by omega) false c v rSub rW hSW
  dTwCtrlInv c {_ _} v rSub rW hSW := dTwHeld114ZeroUnc54 hW28 hW36 (by omega) true c v rSub rW hSW
  hToffPairCtrl c {_ _} v rSub rW hSW :=
    ⟨(dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) false c v rSub rW hSW).1,
     (dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) true c v rSub rW hSW).1⟩
  hTPairCtrl c {_ _} v rSub rW hSW :=
    (Nat.add_le_add (dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) false c v rSub rW hSW).2
      (dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) true c v rSub rW hSW).2).trans
      (Nat.two_mul _).ge
  hRealPairCtrl c {_} [_] [_] {_} [_] v rSub rW hSW :=
    dTwHeld114ZeroUnc54_realizesPair hW28 hW36 (by omega) c v rSub rW hSW
  dTwCat c {_ _} v rSub rW hSW := dTwHeld114ZeroUnc54 hW28 hW36 (by omega) false c v rSub rW hSW
  dTwCatInv c {_ _} v rSub rW hSW := dTwHeld114ZeroUnc54 hW28 hW36 (by omega) true c v rSub rW hSW
  hToffPairCat c {_ _} v rSub rW hSW :=
    ⟨(dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) false c v rSub rW hSW).1,
     (dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) true c v rSub rW hSW).1⟩
  hTPairCat c {_ _} v rSub rW hSW :=
    (Nat.add_le_add (dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) false c v rSub rW hSW).2
      (dTwHeld114ZeroUnc54_counts hW28 hW36 (by omega) true c v rSub rW hSW).2).trans
      (Nat.two_mul _).ge
  hRealPairCat c {_} [_] [_] {_} [_] v rSub rW hSW :=
    dTwHeld114ZeroUnc54_realizesPair hW28 hW36 (by omega) c v rSub rW hSW

end Twist114HoistCore

end QuantumComputation.Specs.StoppingPowerSolution
end
