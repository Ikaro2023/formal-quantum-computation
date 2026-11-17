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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Gf8Code18Guard
set_option Elab.async false

/-!
# `H = 54` Wide `37`-Catalyst Nuclear Twist & Generic `Slot 3` `SELECT` Bridge
(`WideTwist54AndSlot3Bridge`)

1. Lifts the `coin = 0`-only `37`-catalyst `108`-leaf W-state nuclear twist chain from `H ≤ 52` to
   `H ≤ 54`, saving `-16 T` one-way = **`-32 T/SELECT = -64 T/seg`** at zero extra qubits
   (`113 + 2 * W ≤ 190` for `W ≤ 36`, and `99 + 2 * W ≤ mWork` on symmetric `mWork + 14` wires).
2. Exports `tTwHeld37Wide54` (`9,680 .. 12,560 T` for `W = 28..36`), `twHeld37Wide54Spec190`
   (`rfl`-identical unitaries to `twHeld37Wide52Spec190`), `mkSlot3GenAsymHeldTwSpecWide54_mWExt`,
   `mkSlot3GenAsymHeldTwSpecWide54_mWork`, and `mkSlot3GenAsymHeldTwSpecWide54_11_14_mWork`.
3. Exports `Slot3Sym14CircuitSpec`, symmetric `(mWork + 14, mWork + 14)` guard-wrapped `ora1`
`SELECT`,
   and turnkey `mkSlot3SpecTw54Ora1HoistedExtHkSelectSpec_mWork` / `mkGuardTw54...` /
   `mkHeldU54Tw54...`.
-/

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section WideTwist54Core

section
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192
namespace WideTwist54Core
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowRadWide_13a (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instGroupUnitaryFast_13a (D : ℕ) : Group (Operator.Unitary
  D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_13a (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open scoped BigOperators Matrix Matrix.Norms.L2Operator Circuit.Notation
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open PrimitiveGate (TOFF T)
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete (rNucIdx)
open NuclearTwistRealizes (RealizesCleanPair dite_pos_eq dite_neg_eq)
open NuclearTwistMulKickAndBridge288 (count_dyn_seq)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq vepProj9CoreIdx)
open MeasureBranchHadamardSem (ket eval_seq_mulVec ket_Z)
open FastMidKick275Aux (fmkCZ ket_fmkCZ)
open SharedUnary108ZeroTUncompTwist
open Leaf4Twist162
open TwistShared108HadCut558 (dVepXorMKAnc count_dVepXorMKAnc_toff count_dVepXorMKAnc_t
  dVepXorMKAnc_realizesPair)
open TwistShared108 (loadMK108BitFn loadMK108_eq_sum54 dLoadMK108Anc count_dLoadMK108Anc_toff
  count_dLoadMK108Anc_t dLoadMK108Anc_realizesPair)
/-- Combined `108`-leaf nuclear + VEP `K`-bit lookup table on `rCHHold` for `H ≤ 54`. -/
noncomputable def fullMK108BitFn {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (xCH : BitAssignment ((fullSysCoreWires mPayload + 61) + H)) (k : Fin K) : ZMod 2 :=
  vepLockVal <| loadMK108BitFn K H hH54 c hm w xCH k + vepMKBitFn K H hK9 hm w xCH k
theorem sum_uLeaf54_decomp_54 {H : ℕ} (hH54 : H ≤ 54) (P : Fin 54 → Bool → Bool)
    (b1 : ZMod 2) (xHi : Fin 54 → ZMod 2) (xPre : Fin H → ZMod 2) :
    (∑ i : Fin 54,
      ((if P i false = true then uLeaf54 b1 xHi xPre i false else 0) +
       (if P i true = true then uLeaf54 b1 xHi xPre i true else 0))) =
    ((∑ i : Fin 54, if P i false = true then xHi i else 0) +
     (∑ m : Fin H, if P ⟨m.val, by omega⟩ true = true then xPre m else 0)) +
    b1 *
      (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (P i false) (P i true)) = true then xHi i else 0) := by
  have hTerm : ∀ i : Fin 54, (if P i false = true then uLeaf54 b1 xHi xPre i false else 0) +
      (if P i true = true then uLeaf54 b1 xHi xPre i true else 0) = ((if P i false = true then
      xHi i else 0) + (if hi : i.val < H then (if P i true = true then xPre ⟨i.val, hi⟩ else
      0) else 0)) + b1 * (if (decide (H ≤ i.val) && xor (P i false) (P i true)) = true then
      xHi i else 0) :=
    fun i ↦ by
      dsimp only [uLeaf54]
      by_cases hi : i.val < H
      · have hd : decide (H ≤ i.val) = false := decide_eq_false (by omega)
        rw [dite_pos_eq hi, dite_pos_eq hi, dite_pos_eq hi, hd]; simp
      · have hd : decide (H ≤ i.val) = true := decide_eq_true (by omega)
        rw [dite_neg_eq hi, dite_neg_eq hi, dite_neg_eq hi, hd, Bool.true_and, add_zero]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact zmod2_split_b0_xor b1 (xHi i) (P i false) (P i true)
  rw [Finset.sum_congr rfl fun i _ ↦ hTerm i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have hPreSum :
      (∑ i : Fin 54, if hi : i.val < H then (if P i true = true then xPre ⟨i.val, hi⟩ else 0) else
        0) =
      ∑ m : Fin H, if P ⟨m.val, by omega⟩ true = true then xPre m else 0 := by
    let e : Fin (H + (54 - H)) ≃ Fin 54 := finCongr (by omega)
    rw [← Equiv.sum_comp e, Fin.sum_univ_add]
    have hL : (∑ m : Fin H,
        if hi : (e (Fin.castAdd (54 - H) m)).val < H then
          (if P (e (Fin.castAdd (54 - H) m)) true = true then xPre ⟨_, hi⟩ else 0)
        else 0) =
        ∑ m : Fin H, if P ⟨m.val, by omega⟩ true = true then xPre m else 0 :=
      Finset.sum_congr rfl fun m _ ↦ by
        have hmH : (e (Fin.castAdd (54 - H) m)).val < H := by dsimp [e]; exact m.isLt
        rw [dite_pos_eq hmH]
        have hm' : (⟨(e (Fin.castAdd (54 - H) m)).val, hmH⟩ : Fin H) = m := Fin.ext rfl
        have he : e (Fin.castAdd (54 - H) m) = ⟨m.val, by omega⟩ := Fin.ext rfl
        rw [hm', he]
    have hR : (∑ r : Fin (54 - H), if hi : (e (Fin.natAdd H r)).val < H then (if P (e
        (Fin.natAdd H r)) true = true then xPre ⟨_, hi⟩ else 0) else 0) = 0 :=
      Finset.sum_eq_zero fun r _ ↦ dite_neg_eq (by dsimp [e]; omega)
    rw [hL, hR, add_zero]
  rw [hPreSum]
theorem sum_nucMK108_alg (K H : ℕ) (hH54 : H ≤ 54)
    (tblBit : Fin 54 → Bool → Bool → Fin K → Bool)
    {f : Fin K → Bool} (P0 PD : Fin 54 → Bool → Bool)
    (hP0 : ∀ i s, P0 i s = parityMaskK f (tblBit i s false))
    (hPD : ∀ i s, PD i s = parityMaskK f (fun k ↦ xor (tblBit i s false k) (tblBit i s true k)))
    (b0 b1 : ZMod 2) (xHi : Fin 54 → ZMod 2) (xPre : Fin H → ZMod 2)
    (T_vep : ZMod 2) :
    (∑ k : Fin K, if f k = true then
      ((∑ i : Fin 54,
        ((if tblBit i false false k = true then uLeaf54 b1 xHi xPre i false else 0) +
         (if tblBit i true false k = true then uLeaf54 b1 xHi xPre i true else 0))) +
       b0 *
        (∑ i : Fin 54,
          ((if xor (tblBit i false false k) (tblBit i false true k) = true then
              uLeaf54 b1 xHi xPre i false else 0) +
           (if xor (tblBit i true false k) (tblBit i true true k) = true then
              uLeaf54 b1 xHi xPre i true else 0)))) else 0) + T_vep =
      T_vep +
      ((∑ i : Fin 54, if P0 i false = true then xHi i else 0) +
        (∑ m : Fin H, if P0 ⟨m.val, by omega⟩ true = true then xPre m else 0)) +
      b1 * (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (P0 i false) (P0 i true)) = true then xHi i else 0) +
      b0 * ((∑ i : Fin 54, if PD i false = true then xHi i else 0) +
        (∑ m : Fin H, if PD ⟨m.val, by omega⟩ true = true then xPre m else 0)) +
      (b0 * b1) * (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (PD i false) (PD i true)) = true then xHi i else 0) := by
  have h1 : ∀ k : Fin K,
      (if f k = true then
        ((∑ i : Fin 54,
          ((if tblBit i false false k = true then uLeaf54 b1 xHi xPre i false else 0) +
           (if tblBit i true false k = true then uLeaf54 b1 xHi xPre i true else 0))) +
         b0 *
          (∑ i : Fin 54,
            ((if xor (tblBit i false false k) (tblBit i false true k) = true then
                uLeaf54 b1 xHi xPre i false else 0) +
             (if xor (tblBit i true false k) (tblBit i true true k) = true then
                uLeaf54 b1 xHi xPre i true else 0)))) else 0) =
      (∑ i : Fin 54,
        ((if f k = true then (if tblBit i false false k = true then
            uLeaf54 b1 xHi xPre i false else 0) else 0) +
         (if f k = true then (if tblBit i true false k = true then
            uLeaf54 b1 xHi xPre i true else 0) else 0))) +
      b0 *
        (∑ i : Fin 54,
          ((if f k = true then (if xor (tblBit i false false k) (tblBit i false true k) = true then
              uLeaf54 b1 xHi xPre i false else 0) else 0) +
           (if f k = true then (if xor (tblBit i true false k) (tblBit i true true k) = true then
              uLeaf54 b1 xHi xPre i true else 0) else 0))) := fun k ↦ by
    cases f k <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Finset.sum_const_zero,
      mul_zero]
  have hS0 : (∑ k : Fin K, ∑ i : Fin 54, ((if f k = true then (if tblBit i false false k =
      true then uLeaf54 b1 xHi xPre i false else 0) else 0) + (if f k = true then (if tblBit i
      true false k = true then uLeaf54 b1 xHi xPre i true else 0) else 0))) = ∑ i : Fin 54,
      ((if P0 i false = true then uLeaf54 b1 xHi xPre i false else 0) + (if P0 i true = true
      then uLeaf54 b1 xHi xPre i true else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_add_distrib, sum_ite_parityMaskK, sum_ite_parityMaskK, ← hP0 i false,
      ← hP0 i true]
  have hSD : (∑ k : Fin K, ∑ i : Fin 54, ((if f k = true then (if xor (tblBit i false false k)
      (tblBit i false true k) = true then uLeaf54 b1 xHi xPre i false else 0) else 0) + (if f
      k = true then (if xor (tblBit i true false k) (tblBit i true true k) = true then uLeaf54
      b1 xHi xPre i true else 0) else 0))) = ∑ i : Fin 54, ((if PD i false = true then uLeaf54
      b1 xHi xPre i false else 0) + (if PD i true = true then uLeaf54 b1 xHi xPre i true else
      0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_add_distrib, sum_ite_parityMaskK, sum_ite_parityMaskK, ← hPD i false,
      ← hPD i true]
  rw [Finset.sum_congr rfl fun k _ ↦ h1 k, Finset.sum_add_distrib, ← Finset.mul_sum,
      hS0, hSD, sum_uLeaf54_decomp_54 hH54 P0 b1 xHi xPre, sum_uLeaf54_decomp_54 hH54 PD b1 xHi
        xPre]
  ring
theorem sum_fullMK108BitFn_eq {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3) (f : Fin K → Bool)
    (xCH : BitAssignment ((fullSysCoreWires mPayload + 61) + H)) :
    let kC := fullSysCoreWires mPayload
    let b0 := xCH (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg kC) ⟨0, by decide⟩)))
    let b1 := xCH (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg kC) ⟨1, by decide⟩)))
    let xFlag := xCH (Fin.castAdd H (Fin.natAdd kC ⟨6, by decide⟩))
    let xHi : Fin 54 → ZMod 2 := fun i ↦ xCH (Fin.castAdd H (Fin.natAdd kC ⟨7 + i.val, by omega⟩))
    let xPre : Fin H → ZMod 2 := fun m ↦ xCH (Fin.natAdd (kC + 61) m)
    let pB0 := parB0MK K c w f
    let pD := parDMK K c w f
    (∑ k : Fin K, if f k = true then fullMK108BitFn K H hK9 hH54 c hm w xCH k else 0) =
      xFlag * (∑ m : Fin 9,
        if f ⟨(K - 9) + m.val, by omega⟩ = true then
          xCH (Fin.castAdd H (Fin.castAdd 61 (vepProj9CoreIdx hm w m))) else 0) +
      ((∑ i : Fin 54, if pB0 i false = true then xHi i else 0) +
        (∑ m : Fin H, if pB0 ⟨m.val, by omega⟩ true = true then xPre m else 0)) +
      b1 * (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (pB0 i false) (pB0 i true)) = true then xHi i else 0) +
      b0 * ((∑ i : Fin 54, if pD i false = true then xHi i else 0) +
        (∑ m : Fin H, if pD ⟨m.val, by omega⟩ true = true then xPre m else 0)) +
      (b0 * b1) * (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (pD i false) (pD i true)) = true then xHi i else 0) := by
  intro kC b0 b1 xFlag xHi xPre pB0 pD
  have hSplit : (∑ k : Fin K, if f k = true then fullMK108BitFn K H hK9 hH54 c hm w xCH k else
      0) = (∑ k : Fin K, if f k = true then loadMK108BitFn K H hH54 c hm w xCH k else 0) + (∑
      k : Fin K, if f k = true then vepMKBitFn K H hK9 hm w xCH k else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [fullMK108BitFn, vepLockVal_eq]
    cases f k <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  have hNucCongr : (∑ k : Fin K, if f k = true then loadMK108BitFn K H hH54 c hm w xCH k else
      0) = ∑ k : Fin K, if f k = true then ((∑ i : Fin 54, ((if (mkEntry54 K c w i false
      false).testBit k.val then uLeaf54 b1 xHi xPre i false else 0) + (if (mkEntry54 K c w i
      true false).testBit k.val then uLeaf54 b1 xHi xPre i true else 0))) + b0 * (∑ i : Fin
      54, ((if xor ((mkEntry54 K c w i false false).testBit k.val) ((mkEntry54 K c w i false
      true).testBit k.val) then uLeaf54 b1 xHi xPre i false else 0) + (if xor ((mkEntry54 K c
      w i true false).testBit k.val) ((mkEntry54 K c w i true true).testBit k.val) then
      uLeaf54 b1 xHi xPre i true else 0)))) else 0 :=
    Finset.sum_congr rfl fun k _ ↦ by
      rw [loadMK108_eq_sum54 K H hH54 c hm w xCH k]
  rw [hSplit, hNucCongr, sum_vepMKBitFn_eq]
  exact sum_nucMK108_alg K H hH54 (fun i s b k ↦ (mkEntry54 K c w i s b).testBit k.val)
    pB0 pD (fun i s ↦ vepLockVal_eq _) (fun i s ↦ vepLockVal_eq _) b0 b1 xHi xPre _
theorem finH_lt54_54 {H : ℕ} (hH54 : H ≤ 54) (m : Fin H) : m.val < 54 := by omega
/-- Combined `(54 + H)`-wire `L_lo` Clifford fanout onto `wAnc` for `H ≤ 54`. -/
noncomputable def fanoutLoMK_54 {H n : ℕ} (hH54 : H ≤ 54) (rHdr61 : QRegister 61 n)
    (rPreHold : QRegister H n) (wAnc : Wire n)
    (hHiAnc : ∀ i : Fin 54, rHdr61 ⟨7 + i.val, seven_add_lt61 i⟩ ≠ wAnc)
    (hPreAnc : ∀ m : Fin H, rPreHold m ≠ wAnc) (P : Fin 54 → Bool → Bool) : CliffProg n :=
    .seq (fanoutCliffFull 54 (fun i ↦ rHdr61 ⟨7 + i.val, seven_add_lt61 i⟩) wAnc hHiAnc (fun i
    ↦ P i false)) (fanoutCliffFull H (fun m ↦ rPreHold m) wAnc hPreAnc (fun m ↦ P ⟨m.val,
    finH_lt54_54 hH54 m⟩ true))
theorem fanoutLoMK_54_eval {H n : ℕ} (hH54 : H ≤ 54)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (wAnc : Wire n)
    (hHiAnc : ∀ i : Fin 54, rHdr61 ⟨7 + i.val, by omega⟩ ≠ wAnc)
    (hPreAnc : ∀ m : Fin H, rPreHold m ≠ wAnc)
    (P : Fin 54 → Bool → Bool) (β : BitAssignment n) :
    (fanoutLoMK_54 hH54 rHdr61 rPreHold wAnc hHiAnc hPreAnc P).eval β =
      Function.update β wAnc
        (β wAnc +
          ((∑ i : Fin 54, if P i false = true then β (rHdr61 ⟨7 + i.val, by omega⟩) else 0) +
           (∑ m : Fin H, if P ⟨m.val, by omega⟩ true = true then β (rPreHold m) else 0))) := by
  dsimp only [fanoutLoMK_54, CliffProg.eval]
  rw [fanoutCliffFull_eval, fanoutCliffFull_eval, Function.update_self, Function.update_idem]
  have hPreEq : (∑ m : Fin H,
      if P ⟨m.val, by omega⟩ true = true then
        (Function.update β wAnc
          (β wAnc + ∑ i : Fin 54, if P i false = true then β (rHdr61 ⟨7 + i.val, by omega⟩) else 0))
          (rPreHold m)
      else 0) =
      ∑ m : Fin H, if P ⟨m.val, by omega⟩ true = true then β (rPreHold m) else 0 :=
    Finset.sum_congr rfl fun m _ ↦ by rw [Function.update_of_ne (hPreAnc m)]
  rw [hPreEq, add_assoc]
/-- `0-T`, `0-TOFF` pure-Clifford 5-block phase fixup circuit on `wAnc` reading `w01` for `H ≤
54`. -/
noncomputable def cPhaseFixupMK108_0T {mPayload K H n : ℕ}
    (hK9 : 9 ≤ K) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3) (f : Fin K →
      Bool)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n) (rPreHold :
      QRegister H n)
    (wAnc w01 : Wire n) (hCAnc : ∀ q, rCore q ≠ wAnc) (hH61Anc : ∀ q, rHdr61 q ≠ wAnc)
    (hPHAnc : ∀ m, rPreHold m ≠ wAnc) (h01Anc : w01 ≠ wAnc) : Circuit n :=
  vepLockVal <|
    let b0 := rCore (rNucIdx hm (QRegExt.idReg _) ⟨0, by decide⟩)
    let b1 := rCore (rNucIdx hm (QRegExt.idReg _) ⟨1, by decide⟩)
    let wFlag := rHdr61 ⟨6, by decide⟩
    let pB0 := parB0MK K c w f; let pD := parDMK K c w f
    let cVep := fanoutCliffFull 9 (fun m ↦ rCore (vepProj9CoreIdx hm w m)) wAnc
      (fun m ↦ hCAnc _) (fun m ↦ f ⟨(K - 9) + m.val, sub9_add_fin9_lt hK9 m⟩)
    let cLoB0 := fanoutLoMK_54 hH54 rHdr61 rPreHold wAnc (fun i ↦ hH61Anc _) hPHAnc pB0
    let cHiB0 := fanoutCliffFull 54 (fun i ↦ rHdr61 ⟨7 + i.val, seven_add_lt61 i⟩) wAnc
      (fun i ↦ hH61Anc _) (fun i ↦ decide (H ≤ i.val) && xor (pB0 i false) (pB0 i true))
    let cLoD := fanoutLoMK_54 hH54 rHdr61 rPreHold wAnc (fun i ↦ hH61Anc _) hPHAnc pD
    let cHiD := fanoutCliffFull 54 (fun i ↦ rHdr61 ⟨7 + i.val, seven_add_lt61 i⟩) wAnc
      (fun i ↦ hH61Anc _) (fun i ↦ decide (H ≤ i.val) && xor (pD i false) (pD i true))
    (cVep.toCircuit ;;ᶜ fmkCZ wFlag wAnc (hH61Anc _) ;;ᶜ cVep.inv.toCircuit) ;;ᶜ
    ((cLoB0.toCircuit ;;ᶜ Circuit.Z wAnc ;;ᶜ cLoB0.inv.toCircuit) ;;ᶜ
     ((cHiB0.toCircuit ;;ᶜ fmkCZ b1 wAnc (hCAnc _) ;;ᶜ cHiB0.inv.toCircuit) ;;ᶜ
      ((cLoD.toCircuit ;;ᶜ fmkCZ b0 wAnc (hCAnc _) ;;ᶜ cLoD.inv.toCircuit) ;;ᶜ
       (cHiD.toCircuit ;;ᶜ fmkCZ w01 wAnc h01Anc ;;ᶜ cHiD.inv.toCircuit))))
@[local simp] theorem count_cPhaseFixupMK108_0T_toff {mPayload K H n : ℕ}
    (hK9 : 9 ≤ K) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3) (f : Fin K →
      Bool)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n) (rPreHold :
      QRegister H n)
    (wAnc w01 : Wire n) (hCAnc : ∀ q, rCore q ≠ wAnc) (hH61Anc : ∀ q, rHdr61 q ≠ wAnc)
    (hPHAnc : ∀ m, rPreHold m ≠ wAnc) (h01Anc : w01 ≠ wAnc) :
    (cPhaseFixupMK108_0T hK9 hH54 c hm w f rCore rHdr61 rPreHold wAnc w01
      hCAnc hH61Anc hPHAnc h01Anc).count TOFF = 0 := by
  rw [cPhaseFixupMK108_0T, vepLockVal_eq]; simp [Circuit.Z, Circuit.single]
@[local simp] theorem count_cPhaseFixupMK108_0T_t {mPayload K H n : ℕ}
    (hK9 : 9 ≤ K) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3) (f : Fin K →
      Bool)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n) (rPreHold :
      QRegister H n)
    (wAnc w01 : Wire n) (hCAnc : ∀ q, rCore q ≠ wAnc) (hH61Anc : ∀ q, rHdr61 q ≠ wAnc)
    (hPHAnc : ∀ m, rPreHold m ≠ wAnc) (h01Anc : w01 ≠ wAnc) :
    (cPhaseFixupMK108_0T hK9 hH54 c hm w f rCore rHdr61 rPreHold wAnc w01
      hCAnc hH61Anc hPHAnc h01Anc).count T = 0 := by
  rw [cPhaseFixupMK108_0T, vepLockVal_eq]; simp [Circuit.Z, Circuit.single]
theorem cPhaseFixupMK108_0T_eval_ket {mPayload K H n : ℕ}
    (hK9 : 9 ≤ K) (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3) (f : Fin K →
      Bool)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n) (rPreHold :
      QRegister H n)
    (wAnc w01 : Wire n) (hCAnc : ∀ q, rCore q ≠ wAnc) (hH61Anc : ∀ q, rHdr61 q ≠ wAnc)
    (hPHAnc : ∀ m, rPreHold m ≠ wAnc) (h01Anc : w01 ≠ wAnc) (β : BitAssignment n) (hzAnc : β wAnc =
      0) :
    let b0 := rCore (rNucIdx hm (QRegExt.idReg _) ⟨0, by decide⟩)
    let b1 := rCore (rNucIdx hm (QRegExt.idReg _) ⟨1, by decide⟩)
    let wFlag := rHdr61 ⟨6, by decide⟩
    let pB0 := parB0MK K c w f; let pD := parDMK K c w f
    (cPhaseFixupMK108_0T hK9 hH54 c hm w f rCore rHdr61 rPreHold wAnc w01
      hCAnc hH61Anc hPHAnc h01Anc).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^
        (β wFlag * (∑ m : Fin 9,
            if f ⟨(K - 9) + m.val, by omega⟩ = true then β (rCore (vepProj9CoreIdx hm w m)) else 0)
              +
         ((∑ i : Fin 54, if pB0 i false = true then β (rHdr61 ⟨7 + i.val, by omega⟩) else 0) +
          (∑ m : Fin H, if pB0 ⟨m.val, by omega⟩ true = true then β (rPreHold m) else 0)) +
         β b1 * (∑ i : Fin 54,
            if (decide (H ≤ i.val) && xor (pB0 i false) (pB0 i true)) = true then
              β (rHdr61 ⟨7 + i.val, by omega⟩) else 0) +
         β b0 * ((∑ i : Fin 54, if pD i false = true then β (rHdr61 ⟨7 + i.val, by omega⟩) else 0) +
          (∑ m : Fin H, if pD ⟨m.val, by omega⟩ true = true then β (rPreHold m) else 0)) +
         β w01 * (∑ i : Fin 54,
            if (decide (H ≤ i.val) && xor (pD i false) (pD i true)) = true then
              β (rHdr61 ⟨7 + i.val, by omega⟩) else 0)).val) • ket β := by
  intro b0 b1 wFlag pB0 pD
  let cVep := fanoutCliffFull 9 (fun m ↦ rCore (vepProj9CoreIdx hm w m)) wAnc
    (fun m ↦ hCAnc _) (fun m ↦ f ⟨(K - 9) + m.val, by omega⟩)
  let cLoB0 := fanoutLoMK_54 hH54 rHdr61 rPreHold wAnc (fun i ↦ hH61Anc _) hPHAnc pB0
  let cHiB0 := fanoutCliffFull 54 (fun i ↦ rHdr61 ⟨7 + i.val, by omega⟩) wAnc
    (fun i ↦ hH61Anc _) (fun i ↦ decide (H ≤ i.val) && xor (pB0 i false) (pB0 i true))
  let cLoD := fanoutLoMK_54 hH54 rHdr61 rPreHold wAnc (fun i ↦ hH61Anc _) hPHAnc pD
  let cHiD := fanoutCliffFull 54 (fun i ↦ rHdr61 ⟨7 + i.val, by omega⟩) wAnc
    (fun i ↦ hH61Anc _) (fun i ↦ decide (H ≤ i.val) && xor (pD i false) (pD i true))
  have h1 : (cVep.toCircuit ;;ᶜ fmkCZ wFlag wAnc (hH61Anc _) ;;ᶜ cVep.inv.toCircuit).eval.1.mulVec
    (ket β) =
      ((-1 : ℂ) ^ (β wFlag * (∑ m : Fin 9,
        if f ⟨(K - 9) + m.val, by omega⟩ = true then β (rCore (vepProj9CoreIdx hm w m)) else
          0)).val) • ket β :=
    cliff_conj_eval_ket cVep (fmkCZ wFlag wAnc (hH61Anc _)) β _ (by
      dsimp only [cVep]; rw [ket_fmkCZ, TempPhaseProg.bitSign_eq_neg_one_pow,
        fanoutCliffFull_eval, Function.update_of_ne (hH61Anc _), Function.update_self, hzAnc,
          zero_add])
  have h2 : (cLoB0.toCircuit ;;ᶜ Circuit.Z wAnc ;;ᶜ cLoB0.inv.toCircuit).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ ((∑ i : Fin 54, if pB0 i false = true then β (rHdr61 ⟨7 + i.val, by omega⟩) else
        0) +
        (∑ m : Fin H, if pB0 ⟨m.val, by omega⟩ true = true then β (rPreHold m) else 0)).val) • ket
          β :=
    cliff_conj_eval_ket cLoB0 (Circuit.Z wAnc) β _ (by
      dsimp only [cLoB0]; rw [ket_Z, TempPhaseProg.bitSign_eq_neg_one_pow,
        fanoutLoMK_54_eval, Function.update_self, hzAnc, zero_add])
  have h3 : (cHiB0.toCircuit ;;ᶜ fmkCZ b1 wAnc (hCAnc _) ;;ᶜ cHiB0.inv.toCircuit).eval.1.mulVec (ket
    β) =
      ((-1 : ℂ) ^ (β b1 * (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (pB0 i false) (pB0 i true)) = true then
          β (rHdr61 ⟨7 + i.val, by omega⟩) else 0)).val) • ket β :=
    cliff_conj_eval_ket cHiB0 (fmkCZ b1 wAnc (hCAnc _)) β _ (by
      dsimp only [cHiB0]; rw [ket_fmkCZ, TempPhaseProg.bitSign_eq_neg_one_pow,
        fanoutCliffFull_eval, Function.update_of_ne (hCAnc _), Function.update_self, hzAnc,
          zero_add])
  have h4 : (cLoD.toCircuit ;;ᶜ fmkCZ b0 wAnc (hCAnc _) ;;ᶜ cLoD.inv.toCircuit).eval.1.mulVec (ket
    β) =
      ((-1 : ℂ) ^ (β b0 * ((∑ i : Fin 54, if pD i false = true then β (rHdr61 ⟨7 + i.val,
        by omega⟩) else 0) +
        (∑ m : Fin H, if pD ⟨m.val, by omega⟩ true = true then β (rPreHold m) else 0))).val) • ket
          β :=
    cliff_conj_eval_ket cLoD (fmkCZ b0 wAnc (hCAnc _)) β _ (by
      dsimp only [cLoD]; rw [ket_fmkCZ, TempPhaseProg.bitSign_eq_neg_one_pow,
        fanoutLoMK_54_eval, Function.update_of_ne (hCAnc _), Function.update_self, hzAnc, zero_add])
  have h5 : (cHiD.toCircuit ;;ᶜ fmkCZ w01 wAnc h01Anc ;;ᶜ cHiD.inv.toCircuit).eval.1.mulVec (ket
    β) =
      ((-1 : ℂ) ^ (β w01 * (∑ i : Fin 54,
        if (decide (H ≤ i.val) && xor (pD i false) (pD i true)) = true then
          β (rHdr61 ⟨7 + i.val, by omega⟩) else 0)).val) • ket β :=
    cliff_conj_eval_ket cHiD (fmkCZ w01 wAnc h01Anc) β _ (by
      dsimp only [cHiD]; rw [ket_fmkCZ, TempPhaseProg.bitSign_eq_neg_one_pow,
        fanoutCliffFull_eval, Function.update_of_ne h01Anc, Function.update_self, hzAnc, zero_add])
  rw [cPhaseFixupMK108_0T, vepLockVal_eq]
  change ((cVep.toCircuit ;;ᶜ fmkCZ wFlag wAnc (hH61Anc _) ;;ᶜ cVep.inv.toCircuit) ;;ᶜ
    ((cLoB0.toCircuit ;;ᶜ Circuit.Z wAnc ;;ᶜ cLoB0.inv.toCircuit) ;;ᶜ
     ((cHiB0.toCircuit ;;ᶜ fmkCZ b1 wAnc (hCAnc _) ;;ᶜ cHiB0.inv.toCircuit) ;;ᶜ
      ((cLoD.toCircuit ;;ᶜ fmkCZ b0 wAnc (hCAnc _) ;;ᶜ cLoD.inv.toCircuit) ;;ᶜ
       (cHiD.toCircuit ;;ᶜ fmkCZ w01 wAnc h01Anc ;;ᶜ cHiD.inv.toCircuit))))).eval.1.mulVec (ket β) =
         _
  rw [eval_seq_mulVec, h1, Matrix.mulVec_smul, eval_seq_mulVec, h2, Matrix.mulVec_smul,
      eval_seq_mulVec, h3, Matrix.mulVec_smul, eval_seq_mulVec, h4, Matrix.mulVec_smul,
      h5, smul_smul, smul_smul, smul_smul, smul_smul,
      neg_one_pow_zmod2_add, neg_one_pow_zmod2_add, neg_one_pow_zmod2_add, neg_one_pow_zmod2_add]
/-- Prefix embedding `(kC + 61) + H ↪ (((kC + 61) + H) + 14) + 37`. -/
def chHoldInData37 {mPayload H : ℕ} : QRegister ((fullSysCoreWires mPayload + 61) + H)
    ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) := ⟨⟨fun q ↦ Fin.castAdd 37
    (Fin.castAdd 14 q), fun _ _ h ↦ Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h)⟩⟩
/-- Combined `108`-leaf lookup table on `rAxisData37` for `H ≤ 54`. -/
noncomputable def tblMK108Data37 {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (x : Fin (2 ^ ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37))) : Fin (2 ^ K) :=
  let kCH := (fullSysCoreWires mPayload + 61) + H
  (basisBitsEquiv K).symm (fullMK108BitFn K H hK9 hH54 c hm w
    (fun q : Fin kCH ↦ basisBits ((kCH + 14) + 37) x (Fin.castAdd 37 (Fin.castAdd 14 q))))
/-- Combined `108`-leaf nuclear + VEP XOR loader on `rMK` (`H ≤ 54`, `4 * ((54 - H) + K) + 36`
`T`). -/
noncomputable def dLoadAndVepMK108Anc_54 {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (hmClean : 56 - H ≤ mAnc) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCMK : rCore.DisjointWires rMK) (hH61MK : rHdr61.DisjointWires rMK) (hPHMK :
      rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) : DynamicCircuit Var n :=
  let rCH := (rCore.concat rHdr61 hCH61).concat rPreHold hCHPH
  let hCHM : rCH.DisjointWires rMK :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCMK hH61MK) hPHMK
  let hCHA : rCH.DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCA hH61A) hPHA
  .seq (dLoadMK108Anc hmClean hH54 c hm v w rCH rMK rAnc hCHM hCHA hMKA)
    (dVepXorMKAnc hK9 h9 hm v w rCore rHdr61 rPreHold rMK rAnc hCH61 hCMK hH61MK hCA hH61A hMKA)
/-- Reverse-order inverse of `dLoadAndVepMK108Anc_54` (`H ≤ 54`). -/
noncomputable def dLoadAndVepMK108AncInv_54 {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (hmClean : 56 - H ≤ mAnc) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCMK : rCore.DisjointWires rMK) (hH61MK : rHdr61.DisjointWires rMK) (hPHMK :
      rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) : DynamicCircuit Var n :=
  let rCH := (rCore.concat rHdr61 hCH61).concat rPreHold hCHPH
  let hCHM : rCH.DisjointWires rMK :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCMK hH61MK) hPHMK
  let hCHA : rCH.DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCA hH61A) hPHA
  .seq (dVepXorMKAnc hK9 h9 hm v w rCore rHdr61 rPreHold rMK rAnc hCH61 hCMK hH61MK hCA hH61A hMKA)
    (dLoadMK108Anc hmClean hH54 c hm v w rCH rMK rAnc hCHM hCHA hMKA)
@[local simp] theorem count_dLoadAndVepMK108Anc_54_toff {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (hmClean : 56 - H ≤ mAnc) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCMK : rCore.DisjointWires rMK) (hH61MK : rHdr61.DisjointWires rMK) (hPHMK :
      rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) :
    (dLoadAndVepMK108Anc_54 hK9 hmClean h9 hH54 c hm v w rCore rHdr61 rPreHold rMK rAnc
      hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA).count TOFF = 0 := by
  simp [dLoadAndVepMK108Anc_54, count_dLoadMK108Anc_toff, count_dVepXorMKAnc_toff]
@[local simp] theorem count_dLoadAndVepMK108Anc_54_t {Var : Type} {mPayload K H mAnc n : ℕ}
    (hK9 : 9 ≤ K) (hmClean : 56 - H ≤ mAnc) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCMK : rCore.DisjointWires rMK) (hH61MK : rHdr61.DisjointWires rMK) (hPHMK :
      rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) :
    (dLoadAndVepMK108Anc_54 hK9 hmClean h9 hH54 c hm v w rCore rHdr61 rPreHold rMK rAnc
      hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA).count T =
      4 * ((54 - H) + K) + 36 := by
  simp only [dLoadAndVepMK108Anc_54, count_dyn_seq, count_dLoadMK108Anc_t, count_dVepXorMKAnc_t]
theorem dLoadAndVepMK108Anc_54_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload K H mAnc n : ℕ} [NeZero (2 ^ n)]
    (hK9 : 9 ≤ K) (hmClean : 56 - H ≤ mAnc) (h9 : 9 ≤ mAnc) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCMK : rCore.DisjointWires rMK) (hH61MK : rHdr61.DisjointWires rMK) (hPHMK :
      rPreHold.DisjointWires rMK)
    (hCA : rCore.DisjointWires rAnc) (hH61A : rHdr61.DisjointWires rAnc) (hPHA :
      rPreHold.DisjointWires rAnc)
    (hMKA : rMK.DisjointWires rAnc) :
    let hCHM : ((rCore.concat rHdr61 hCH61).concat rPreHold hCHPH).DisjointWires rMK :=
      QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCMK hH61MK) hPHMK
    RealizesCleanPair (((rCore.concat rHdr61 hCH61).concat rPreHold hCHPH).concat rMK hCHM) rAnc
      (uXorMK (fullMK108BitFn K H hK9 hH54 c hm w))
      (dLoadAndVepMK108Anc_54 hK9 hmClean h9 hH54 c hm v w rCore rHdr61 rPreHold rMK rAnc
        hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA)
      (dLoadAndVepMK108AncInv_54 hK9 hmClean h9 hH54 c hm v w rCore rHdr61 rPreHold rMK rAnc
        hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA) := by
  intro hCHM
  let rCH := (rCore.concat rHdr61 hCH61).concat rPreHold hCHPH
  have hCHA : rCH.DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCA hH61A) hPHA
  have hActA : (rCH.concat rMK hCHM).DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left hCHA hMKA
  have hp108 := dLoadMK108Anc_realizesPair hmClean hH54 c hm v w rCH rMK rAnc hCHM hCHA hMKA
  have hpVep := dVepXorMKAnc_realizesPair hK9 h9 hm v w rCore rHdr61 rPreHold rMK rAnc
    hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hMKA
  have hFwd := hp108.fwd.seq hActA hpVep.fwd
  have hInv := hpVep.fwd.seq hActA hp108.fwd
  have hUFwd : uXorMK (vepMKBitFn K H hK9 hm w) * uXorMK (loadMK108BitFn K H hH54 c hm w) =
      uXorMK (fullMK108BitFn K H hK9 hH54 c hm w) := by
    rw [uXorMK_mul]
    refine congrArg uXorMK (funext fun xCH ↦ funext fun k ↦ ?_)
    rw [fullMK108BitFn, vepLockVal_eq]; ring
  have hUInv : uXorMK (loadMK108BitFn K H hH54 c hm w) * uXorMK (vepMKBitFn K H hK9 hm w) =
      (uXorMK (fullMK108BitFn K H hK9 hH54 c hm w))⁻¹ := by
    rw [uXorMK_inv, uXorMK_mul]
    refine congrArg uXorMK (funext fun xCH ↦ funext fun k ↦ ?_)
    rw [fullMK108BitFn, vepLockVal_eq]
  rw [hUFwd] at hFwd
  rw [hUInv] at hInv
  exact { fwd := hFwd, inv := hInv }
end WideTwist54Core
end
end WideTwist54Core


set_option maxRecDepth 262144
set_option exponentiation.threshold 8192

namespace WideTwist54AndSlot3Bridge

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
  ModWrapCoarse8PureMomentum.modWrapNeZeroPow2
  PosSlots24BranchConcrete.instNeZeroTwoPow

local instance (priority := 1000000) instNeZeroTwoPowRadWide_13 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instGroupUnitaryFast_13 (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_13 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

open scoped BigOperators Matrix Matrix.Norms.L2Operator Circuit.Notation
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open _root_ (bitsVal basisKet regVal)
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open FullSysCatSegmentBridge (fullSysCoreWires coreCosetB1Block)
open NuclearTwistAndXor654Concrete (rNucIdx nuclearM48)
open NuclearTwistRealizes
  (coin0Active slot2M48Val dite_pos_eq dite_neg_eq ite_pos_eq ite_neg_eq
  basisBits_symm_apply bitsVal_eq_of_testBit
)
open FusedPreDiagFromTwist288 (hm6_of_hm22)
open FusedVepCore288
  (shiftCatKet shiftCatKet_outside regVal_shiftCatKet mat_ext_basisKet)
open UltraAsymVepTwist288 (asym_embedUnitary_mul_mulVec)
open Slot2ZeroMuxSignedMul46 (apexCatModAddZ apexCatModAddZ_inv)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq vepHighNuc)
open ProjZ512QftAndTwist288 (vepProj9CoreIdx vepOnlyM48Val)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg nuclearMW nuclearMW_lt)
open HeldMsbInc7ApexWrap288 (mEffBits)
open KoffPrunedSlot2ZeroMuxTrunc37 (uInnerKoffSlot2DeltaGen)
open KoffPrunedSlot2ZeroMuxTrunc37 (vepEffSlope48 kOffFromEff)
open Leaf4Twist162 hiding CommutesWithReg rCoreTopCatInCT rCtrl3InCore rCtrl3InCoreCat
open TwistShared108HadCut558 (h9_of_K28 rMPad48_disj_rAnc)
open TwistShared108AndLeaf3Bk (kickSkipKoffSpecTight)
open TwistShared108 (loadMK108_eq_sum54)
open WStateSharedBank114AndTwist114
  (tKickKoff55WState_108KH)
open TruncWAsymHeldTwShell.Slot3InnerTrunc36
  (shiftNat34 phiCat34
   rPGPad48_37 rPGPad48_37_disj_rMPad48 rSum14_disj_rPGPad48_37
   apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11)
open TruncWAsymHeldTwShell.Slot3InnerSharedCoin06NucTwist_Select
  (Slot3InnerHeldTwSpec Slot3InnerSlot3InnerSpec uT0CoreOfTrunc)
open TruncWAsymHeldTwShell.Slot3InnerKick37
open SlimNorm1sWideSelect
  (twHeld37Wide52Spec190
   mkNorm1sSlot3InnerSlot3InnerSpec)
open WideTwist54Core

-- ============================================================================
-- Section 1: `H ≤ 54` `axisDelta108No14` & `dHeaderWrap55WStateKH` Evaluation
-- ============================================================================

theorem fullMK108BitFn_congr_ge14 {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (x₁ x₂ : BitAssignment ((fullSysCoreWires mPayload + 61) + H))
    (hEq : ∀ q : Fin ((fullSysCoreWires mPayload + 61) + H), 14 ≤ q.val → x₁ q = x₂ q) :
    fullMK108BitFn K H hK9 hH54 c hm w x₁ = fullMK108BitFn K H hK9 hH54 c hm w x₂ := by
  funext k
  rw [fullMK108BitFn, vepLockVal_eq, fullMK108BitFn, vepLockVal_eq,
      loadMK108_eq_sum54 K H hH54 c hm w x₁ k, loadMK108_eq_sum54 K H hH54 c hm w x₂ k]
  have hb0 : x₁ (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg _) ⟨0, by decide⟩))) =
      x₂ (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg _) ⟨0, by decide⟩))) :=
    hEq _ (by
      simp only [Fin.val_castAdd]
      have h3960 : 3960 ≤ (rNucIdx hm (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires
        mPayload)) ⟨0, by decide⟩).val :=
        rNucIdx_val_ge_3960 hm ⟨0, by decide⟩
      omega)
  have hb1 : x₁ (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg _) ⟨1, by decide⟩))) =
      x₂ (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg _) ⟨1, by decide⟩))) :=
    hEq _ (by
      simp only [Fin.val_castAdd]
      have h3960 : 3960 ≤ (rNucIdx hm (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires
        mPayload)) ⟨1, by decide⟩).val :=
        rNucIdx_val_ge_3960 hm ⟨1, by decide⟩
      omega)
  have hxHi : (fun i : Fin 54 ↦ x₁ (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨7 +
    i.val, by omega⟩))) =
      (fun i : Fin 54 ↦ x₂ (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨7 + i.val,
        by omega⟩))) :=
    funext fun i ↦ hEq _ (by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; have := core_ge_3954 mPayload; omega)
  have hxPre : (fun m : Fin H ↦ x₁ (Fin.natAdd (fullSysCoreWires mPayload + 61) m)) =
      (fun m : Fin H ↦ x₂ (Fin.natAdd (fullSysCoreWires mPayload + 61) m)) :=
    funext fun m ↦ hEq _ (by simp only [Fin.val_natAdd]; have := core_ge_3954 mPayload; omega)
  have hVep : vepMKBitFn K H hK9 hm w x₁ k = vepMKBitFn K H hK9 hm w x₂ k := by
    dsimp only [vepMKBitFn]; split_ifs with hk9
    · refine congrArg₂ HMul.hMul ?_ ?_
      · exact hEq _ (by
          simp only [Fin.val_castAdd, Fin.val_natAdd]; have := core_ge_3954 mPayload; omega)
      · exact hEq _ (by
          simp only [Fin.val_castAdd]
          have := vepProj9CoreIdx_val_ge_3924 hm w ⟨k.val - (K - 9), by have := k.isLt; omega⟩
          omega)
    · rfl
  rw [hb0, hb1, hxHi, hxPre, hVep]

/-- Effective 48-bit slope `(2^(48-K) * fullMK108 + (1 - b_1(w)) * 2^41) % 2^48` on `kSysNo14` (`H ≤
54`). -/
noncomputable def axisEffSlope108KH {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γNo14 : BitAssignment ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14)) : ℕ :=
  let hi := bitsVal (fullMK108BitFn K H hK9 hH54 c hm w (padZero14CH γNo14))
  let iCtrlNo14 : Fin (fullSysCoreWires mPayload - 14) :=
    ⟨(coreCosetB1Block (hm6_of_hm22 hm) w).val - 14, by
      have := (coreCosetB1Block (hm6_of_hm22 hm) w).isLt
      have := coreCosetB1Block_val_ge_3954 hm w; omega⟩
  let bBar := 1 - (γNo14 (Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61 iCtrlNo14)))).val
  (2 ^ (48 - K) * hi + bBar * 2 ^ 41) % 2 ^ 48

/-- Per-axis Mode-1 `k_off` `ℤ`-delta `B * mEff - kOffFromEff mEff` on `kSysNo14` (`H ≤ 54`). -/
noncomputable def axisDelta108No14 {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γNo14 : BitAssignment ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14)) : ℤ :=
  let kCHNo14 := ((fullSysCoreWires mPayload - 14) + 61) + H
  let m := axisEffSlope108KH K H hK9 hH54 c hm w γNo14
  (bitsVal (fun s : Fin 14 ↦ γNo14 (Fin.natAdd kCHNo14 s)) : ℤ) * (m : ℤ) - kOffFromEff m

theorem dvd_two_pow11_axisDelta108No14 {mPayload : ℕ} (K H : ℕ) (hK9 : 9 ≤ K) (hK36 : K ≤ 36)
    (hH54 : H ≤ 54) (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γNo14 : BitAssignment ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14)) :
    (2 ^ 11 : ℤ) ∣ axisDelta108No14 K H hK9 hH54 c hm w γNo14 := by
  apply dvd_two_pow11_kOffDelta_of_dvd12
  unfold axisEffSlope108KH; dsimp only []
  refine (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by decide))).mpr ?_
  exact Nat.dvd_add (dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega)) _)
    (dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by decide)) _)

theorem bitsVal_basisBits6 : ∀ u : Fin 64, bitsVal (basisBits 6 u) = u.val := by decide

theorem fullMK108_val_on_hdr_eq {mPayload K H : ℕ}
    (hK9 : 9 ≤ K) (hK48 : K ≤ 48) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (xCH : BitAssignment ((fullSysCoreWires mPayload + 61) + H))
    (hHdr6 : xCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨6, by decide⟩)) =
      if vepHighNuc hm (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) then 1 else 0)
    (hHiLt : ∀ k : Fin 54, k.val < H →
      xCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨7 + k.val, by omega⟩)) =
        ((if coin0Active (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) then 1 else 0) *
          (if k.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ xCH (Fin.castAdd H (Fin.castAdd 61
                (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩))))).val
            then 1 else 0)) *
          (1 + xCH (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg _) 1)))))
    (hHiGe : ∀ k : Fin 54, H ≤ k.val →
      xCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨7 + k.val, by omega⟩)) =
        (if coin0Active (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) then 1 else 0) *
          (if k.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ xCH (Fin.castAdd H (Fin.castAdd 61
                (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩))))).val
            then 1 else 0))
    (hPre : ∀ m : Fin H,
      xCH (Fin.natAdd (fullSysCoreWires mPayload + 61) m) =
        ((if coin0Active (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) then 1 else 0) *
          (if m.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ xCH (Fin.castAdd H (Fin.castAdd 61
                (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩))))).val
            then 1 else 0)) *
          xCH (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg _) 1)))) :
    2 ^ (48 - K) * bitsVal (fullMK108BitFn K H hK9 hH54 (truncWCfg K c) hm w xCH) =
      slot2M48Val (truncWCfg K c) hm w (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) +
        vepOnlyM48Val hm w (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) := by
  let kC := fullSysCoreWires mPayload
  let γc : BitAssignment kC := fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))
  let i₀ : Fin 64 := (basisBitsEquiv 6).symm
    (fun d : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg kC) ⟨d.val + 2, by omega⟩))
  let b₀ : ZMod 2 := γc (rNucIdx hm (QRegExt.idReg kC) ⟨0, by decide⟩)
  let b₁ : ZMod 2 := γc (rNucIdx hm (QRegExt.idReg kC) ⟨1, by decide⟩)
  let u54Val : Fin 54 → ZMod 2 := fun k ↦
    (if coin0Active γc then 1 else 0) * (if k.val = i₀.val then 1 else 0)
  let xHi : Fin 54 → ZMod 2 := fun i ↦ xCH (Fin.castAdd H (Fin.natAdd kC ⟨7 + i.val, by omega⟩))
  let xPre : Fin H → ZMod 2 := fun m ↦ xCH (Fin.natAdd (kC + 61) m)
  have hLeaf : ∀ (i : Fin 54) (s : Bool), uLeaf54 b₁ xHi xPre i s = u54Val i *
      (if s then b₁ else 1 + b₁) := uLeaf54_on_hdr_eq hH54 b₁ u54Val xHi xPre hHiLt hHiGe hPre
  have hdecomp : regVal (rNucIdx hm (QRegExt.idReg kC)) γc = 4 * i₀.val + 2 * b₁.val + b₀.val := by
    have hd := SharedUnary54Trunc37.bitsVal8_decomp
      (fun i ↦ γc (rNucIdx hm (QRegExt.idReg kC) i))
    have hi0_bits : bitsVal (fun j : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg kC) ⟨2 + j.val,
      by omega⟩)) = i₀.val := by
      have hb : (fun j : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg kC) ⟨2 + j.val, by omega⟩)) =
        basisBits 6 i₀ :=
        funext fun j ↦ by
          rw [show (⟨2 + j.val, by omega⟩ : Fin 8) = ⟨j.val + 2, by omega⟩ from Fin.ext (by
            dsimp; omega)]
          exact (basisBits_symm_apply 6 (fun d : Fin 6 ↦ γc (rNucIdx hm (QRegExt.idReg kC) ⟨d.val +
            2, by omega⟩)) j).symm
      rw [hb, bitsVal_basisBits6]
    change bitsVal (fun i ↦ γc (rNucIdx hm (QRegExt.idReg kC) i)) = _
    rw [hd, hi0_bits]
  have hb0_lt : b₀.val < 2 := ZMod.val_lt b₀
  have hb1_lt : b₁.val < 2 := ZMod.val_lt b₁
  by_cases hc : coin0Active γc = true ∧ regVal (rNucIdx hm (QRegExt.idReg kC)) γc < 216
  · have hnVep : vepHighNuc hm γc = false :=
      Bool.eq_false_iff.mpr fun hv ↦
        absurd ((ProjZ512QftAndTwist288.vepHighNuc_iff hm γc).mp hv).2 (not_le_of_gt hc.2)
    have hVep0 : ∀ k : Fin K, vepMKBitFn K H hK9 hm w xCH k = 0 := fun k ↦ by
      dsimp only [vepMKBitFn]; split_ifs with hk9
      · rw [hHdr6]; change (if vepHighNuc hm γc then 1 else 0) * _ = 0; rw [hnVep]; simp
      · rfl
    let iStar : Fin 54 := ⟨i₀.val, by have := hc.2; omega⟩
    have huStar : u54Val iStar = 1 := by
      dsimp only [u54Val, iStar]; rw [ite_pos_eq hc.1, ite_pos_eq rfl, mul_one]
    have huNe : ∀ i : Fin 54, i ≠ iStar → ∀ s : Bool, uLeaf54 b₁ xHi xPre i s = 0 := fun i hne s ↦
      by
      rw [hLeaf]; dsimp only [u54Val]
      rw [ite_neg_eq (fun he : i.val = i₀.val ↦ hne (Fin.ext he)), mul_zero, zero_mul]
    let sStar : Bool := decide (b₁ = 1)
    let dStar : Bool := decide (b₀ = 1)
    have hCollapseS : ∀ pf pt : Bool,
        (if pf then uLeaf54 b₁ xHi xPre iStar false else 0) + (if pt then uLeaf54 b₁ xHi xPre iStar
          true else 0) =
        if (if sStar then pt else pf) then 1 else 0 := fun pf pt ↦ by
      rw [hLeaf, hLeaf, huStar, one_mul, one_mul]; exact zmod2_collapse_s_comb b₁ pf pt
    let lStar : Fin 216 := ⟨regVal (rNucIdx hm (QRegExt.idReg kC)) γc, hc.2⟩
    have hlEq : (⟨4 * iStar.val + (if sStar then 2 else 0) + (if dStar then 1 else 0),
        mkEntry54_lt216 iStar sStar dStar⟩ : Fin 216) = lStar :=
      Fin.ext ((zmod2_four_i_add_bits iStar.val b₁ b₀).trans hdecomp.symm)
    have hfn : fullMK108BitFn K H hK9 hH54 (truncWCfg K c) hm w xCH =
        fun k : Fin K ↦ if (nuclearMW K c lStar w).testBit k.val then (1 : ZMod 2) else 0 :=
      funext fun k ↦ by
        rw [fullMK108BitFn, vepLockVal_eq, loadMK108_eq_sum54 K H hH54 (truncWCfg K c) hm w xCH k,
          hVep0 k, add_zero]
        change (∑ i : Fin 54,
            ((if (mkEntry54 K (truncWCfg K c) w i false false).testBit k.val then uLeaf54 b₁ xHi
              xPre i false else 0) +
             (if (mkEntry54 K (truncWCfg K c) w i true false).testBit k.val then uLeaf54 b₁ xHi xPre
               i true else 0))) +
          b₀ * (∑ i : Fin 54,
            ((if xor ((mkEntry54 K (truncWCfg K c) w i false false).testBit k.val)
                     ((mkEntry54 K (truncWCfg K c) w i false true).testBit k.val) then uLeaf54 b₁
                       xHi xPre i false else 0) +
             (if xor ((mkEntry54 K (truncWCfg K c) w i true false).testBit k.val)
                     ((mkEntry54 K (truncWCfg K c) w i true true).testBit k.val) then uLeaf54 b₁ xHi
                       xPre i true else 0))) = _
        rw [Finset.sum_eq_single iStar
              (fun i _ hne ↦ by
                rw [huNe i hne false, huNe i hne true, ite_self, ite_self, add_zero])
              (fun ha ↦ False.elim (ha (Finset.mem_univ _))),
            Finset.sum_eq_single iStar
              (fun i _ hne ↦ by
                rw [huNe i hne false, huNe i hne true, ite_self, ite_self, add_zero])
              (fun ha ↦ False.elim (ha (Finset.mem_univ _))),
            hCollapseS, hCollapseS,
            show (if sStar then (mkEntry54 K (truncWCfg K c) w iStar true false).testBit k.val
                  else (mkEntry54 K (truncWCfg K c) w iStar false false).testBit k.val) =
                 (mkEntry54 K (truncWCfg K c) w iStar sStar false).testBit k.val by
                   cases sStar <;> rfl,
            show (if sStar then xor ((mkEntry54 K (truncWCfg K c) w iStar true false).testBit k.val)
                                    ((mkEntry54 K (truncWCfg K c) w iStar true true).testBit k.val)
                  else xor ((mkEntry54 K (truncWCfg K c) w iStar false false).testBit k.val)
                           ((mkEntry54 K (truncWCfg K c) w iStar false true).testBit k.val)) =
                 xor ((mkEntry54 K (truncWCfg K c) w iStar sStar false).testBit k.val)
                     ((mkEntry54 K (truncWCfg K c) w iStar sStar true).testBit k.val) by
                       cases sStar <;> rfl,
            zmod2_testBit_b0_comb,
            show (if b₀ = 1 then (mkEntry54 K (truncWCfg K c) w iStar sStar true).testBit k.val
                  else (mkEntry54 K (truncWCfg K c) w iStar sStar false).testBit k.val) =
                 (mkEntry54 K (truncWCfg K c) w iStar sStar dStar).testBit k.val by
              dsimp only [dStar]; by_cases hb01 : b₀ = 1 <;> simp [hb01],
            mkEntry54_truncWCfg_eq hK48 c w iStar sStar dStar, hlEq]
    rw [hfn, bitsVal_eq_of_testBit K _ (nuclearMW_lt K c lStar w),
      ← SubvoxelNuclearTrunc28To35Chiral.nuclearM48_truncWCfg hK48 c lStar w]
    have hsl : slot2M48Val (truncWCfg K c) hm w γc = nuclearM48 (truncWCfg K c) lStar w := by
      unfold slot2M48Val; rw [dite_pos_eq hc]
    have hvo : vepOnlyM48Val hm w γc = 0 := by unfold vepOnlyM48Val; rw [hnVep]; simp
    rw [hsl, hvo, add_zero]
  · have hu54_zero : ∀ i : Fin 54, u54Val i = 0 := fun i ↦ by
      dsimp only [u54Val]; by_cases hcoin : coin0Active γc = true
      · have hge216 : 216 ≤ regVal (rNucIdx hm (QRegExt.idReg kC)) γc :=
          Nat.le_of_not_lt fun hlt ↦ hc ⟨hcoin, hlt⟩
        rw [hdecomp] at hge216
        rw [ite_neg_eq (by have := i.isLt; omega : i.val ≠ i₀.val), mul_zero]
      · rw [ite_neg_eq hcoin, zero_mul]
    have huLeaf0 : ∀ (i : Fin 54) (s : Bool),
        uLeaf54
          (xCH (Fin.castAdd H (Fin.castAdd 61 (rNucIdx hm (QRegExt.idReg (fullSysCoreWires
            mPayload)) ⟨1, by decide⟩))))
          (fun i ↦ xCH (Fin.castAdd H (Fin.natAdd (fullSysCoreWires mPayload) ⟨7 + i.val,
            by omega⟩)))
          (fun m ↦ xCH (Fin.natAdd (fullSysCoreWires mPayload + 61) m)) i s = 0 := fun i s ↦ by
      change uLeaf54 b₁ xHi xPre i s = 0; rw [hLeaf, hu54_zero i, zero_mul]
    have hfn : fullMK108BitFn K H hK9 hH54 (truncWCfg K c) hm w xCH = vepMKBitFn K H hK9 hm w xCH :=
      funext fun k ↦ by
        rw [fullMK108BitFn, vepLockVal_eq, loadMK108_eq_sum54 K H hH54 (truncWCfg K c) hm w xCH k]
        simp only [huLeaf0, ite_self, add_zero, Finset.sum_const_zero, mul_zero, zero_add]
    have hsl0 : slot2M48Val (truncWCfg K c) hm w γc = 0 := by
      unfold slot2M48Val; rw [dite_neg_eq hc]
    rw [hfn, hsl0, zero_add, bitsVal_split_gen (by omega : (K - 9) + 9 = K)]
    have hLo0 : bitsVal (fun i : Fin (K - 9) ↦ vepMKBitFn K H hK9 hm w xCH ⟨i.val, by omega⟩) = 0 :=
      by
      have hf0 : (fun i : Fin (K - 9) ↦ vepMKBitFn K H hK9 hm w xCH ⟨i.val, by omega⟩) = fun _ ↦
        0 :=
        funext fun i ↦ by dsimp only [vepMKBitFn]; exact dite_neg_eq (by have := i.isLt; omega)
      rw [hf0]; simp [bitsVal]
    have hHiEq : (fun m : Fin 9 ↦ vepMKBitFn K H hK9 hm w xCH ⟨(K - 9) + m.val, by omega⟩) =
        fun m : Fin 9 ↦ (if vepHighNuc hm γc then (1 : ZMod 2) else 0) * γc (vepProj9CoreIdx hm w
          m) :=
      funext fun m ↦ by
        dsimp only [vepMKBitFn]; rw [dite_pos_eq (by omega), hHdr6]
        exact congrArg₂ HMul.hMul rfl (congrArg γc (congrArg (vepProj9CoreIdx hm w) (Fin.ext (by
          dsimp; omega))))
    rw [hLo0, zero_add, hHiEq]; change _ = vepOnlyM48Val hm w γc; unfold vepOnlyM48Val
    by_cases hv : vepHighNuc hm γc = true
    · simp only [hv, ↓reduceIte, one_mul]
      rw [← mul_assoc, ← pow_add, show (48 - K) + (K - 9) = 39 by omega]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, zero_mul]
      have hz9 : bitsVal (fun _ : Fin 9 ↦ (0 : ZMod 2)) = 0 := by simp [bitsVal]
      rw [hz9, mul_zero, mul_zero]

theorem axisEffSlope108KH_on_hdr_eq {mPayload K H n : ℕ}
    (hK9 : 9 ≤ K) (hK48 : K ≤ 48) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rSum14 : QRegister 14 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (ξ : BitAssignment n)
    (hHdr6 : ξ (rHdr61 ⟨6, by decide⟩) = if vepHighNuc hm (fun q ↦ ξ (rCore q)) then 1 else 0)
    (hHiLt : ∀ k : Fin 54, k.val < H →
      ξ (rHi54Of61 rHdr61 k) =
        ((if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0) *
          (if k.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ ξ (rCore (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)))).val
            then 1 else 0)) *
          (1 + ξ (rCore (rNucIdx hm (QRegExt.idReg _) 1))))
    (hHiGe : ∀ k : Fin 54, H ≤ k.val →
      ξ (rHi54Of61 rHdr61 k) =
        (if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0) *
          (if k.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ ξ (rCore (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)))).val
            then 1 else 0))
    (hPre : ∀ m : Fin H,
      ξ (rPreHold m) =
        ((if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0) *
          (if m.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ ξ (rCore (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)))).val
            then 1 else 0)) *
          ξ (rCore (rNucIdx hm (QRegExt.idReg _) 1))) :
    axisEffSlope108KH K H hK9 hH54 (truncWCfg K c) hm w
        (fun p ↦ ξ ((rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum) p)) =
      vepEffSlope48 (truncWCfg K c) hm w (fun q ↦ ξ (rCore q)) := by
  let xCH : BitAssignment ((fullSysCoreWires mPayload + 61) + H) :=
    fun q ↦ ξ ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH) q)
  have hCoreCH : (fun q ↦ xCH (Fin.castAdd H (Fin.castAdd 61 q))) = (fun q ↦ ξ (rCore q)) :=
    funext fun q ↦ by
      dsimp only [xCH, rCHHold]; rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  have hCongrMK := fullMK108BitFn_congr_ge14 K H hK9 hH54 (truncWCfg K c) hm w _ xCH
    (padZero14CH_on_rSysNo14_ge14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum ξ)
  have hrHi : ∀ k : Fin 54, rHdr61 ⟨7 + k.val, by omega⟩ = rHi54Of61 rHdr61 k :=
    fun k ↦ congrArg rHdr61 (Fin.ext (by simp))
  have hCoreCH_at : ∀ q, xCH (Fin.castAdd H (Fin.castAdd 61 q)) = ξ (rCore q) := congrFun hCoreCH
  have hValMK := fullMK108_val_on_hdr_eq hK9 hK48 hH54 c hm w xCH
    (by
      simp_rw [hCoreCH_at]; dsimp only [xCH, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_right]; exact hHdr6)
    (fun k hk ↦ by
      simp_rw [hCoreCH_at]; dsimp only [xCH, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_right, hrHi k]; exact hHiLt k hk)
    (fun k hk ↦ by
      simp_rw [hCoreCH_at]; dsimp only [xCH, rCHHold]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_right, hrHi k]; exact hHiGe k hk)
    (fun m ↦ by
      simp_rw [hCoreCH_at]; dsimp only [xCH, rCHHold]; rw [QRegister.concat_apply_right]
      exact hPre m)
  have hCtrlEq :
      (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum)
        (Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61
          ⟨(coreCosetB1Block (hm6_of_hm22 hm) w).val - 14, by
            have := (coreCosetB1Block (hm6_of_hm22 hm) w).isLt
            have := coreCosetB1Block_val_ge_3954 hm w; omega⟩))) =
      rCore (coreCosetB1Block (hm6_of_hm22 hm) w) := by
    dsimp only [rSysNo14]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.slice_apply]
    exact congrArg rCore (Fin.ext (by have := coreCosetB1Block_val_ge_3954 hm w; dsimp; omega))
  unfold axisEffSlope108KH vepEffSlope48; dsimp only []
  rw [hCongrMK, hValMK, hCoreCH, congrArg (fun u ↦ (ξ u).val) hCtrlEq]

theorem axisDelta108No14_on_hdr_eq {mPayload K H n : ℕ}
    (hK9 : 9 ≤ K) (hK48 : K ≤ 48) (hH54 : H ≤ 54)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rSum14 : QRegister 14 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hCSum : rCore.DisjointWires rSum14)
    (ξ : BitAssignment n)
    (hHdr6 : ξ (rHdr61 ⟨6, by decide⟩) = if vepHighNuc hm (fun q ↦ ξ (rCore q)) then 1 else 0)
    (hHiLt : ∀ k : Fin 54, k.val < H →
      ξ (rHi54Of61 rHdr61 k) =
        ((if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0) *
          (if k.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ ξ (rCore (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)))).val
            then 1 else 0)) *
          (1 + ξ (rCore (rNucIdx hm (QRegExt.idReg _) 1))))
    (hHiGe : ∀ k : Fin 54, H ≤ k.val →
      ξ (rHi54Of61 rHdr61 k) =
        (if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0) *
          (if k.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ ξ (rCore (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)))).val
            then 1 else 0))
    (hPre : ∀ m : Fin H,
      ξ (rPreHold m) =
        ((if coin0Active (fun q ↦ ξ (rCore q)) then 1 else 0) *
          (if m.val = ((basisBitsEquiv 6).symm
              (fun d : Fin 6 ↦ ξ (rCore (rNucIdx hm (QRegExt.idReg _) ⟨d.val + 2, by omega⟩)))).val
            then 1 else 0)) *
          ξ (rCore (rNucIdx hm (QRegExt.idReg _) 1))) :
    axisDelta108No14 K H hK9 hH54 (truncWCfg K c) hm w
        (fun p ↦ ξ ((rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum) p)) =
      uInnerKoffSlot2DeltaGen (truncWCfg K c) hm w (fun p ↦ ξ ((rCore.concat rSum14 hCSum) p)) := by
  have hmEq := axisEffSlope108KH_on_hdr_eq hK9 hK48 hH54 c hm w
    rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum ξ hHdr6 hHiLt hHiGe hPre
  have hCore14 : (fun q ↦ ξ ((rCore.concat rSum14 hCSum) (Fin.castAdd 14 q))) = (fun q ↦
    ξ (rCore q)) :=
    funext fun q ↦ congrArg ξ (QRegister.concat_apply_left _ _ _ _)
  have hSumEq : (fun s : Fin 14 ↦ ξ ((rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH
      hCHSum) (Fin.natAdd (((fullSysCoreWires mPayload - 14) + 61) + H) s))) = (fun s : Fin
      14 ↦ ξ ((rCore.concat rSum14 hCSum) (Fin.natAdd (fullSysCoreWires mPayload) s))) :=
    funext fun s ↦ by
      dsimp only [rSysNo14]; rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
  unfold axisDelta108No14 uInnerKoffSlot2DeltaGen; dsimp only []
  rw [hmEq, hCore14, hSumEq]

-- ============================================================================
-- Section 2: `H ≤ 54` `dAxisInner108KH_37_54`, `dKickKoff55WState_108KH_37_54` &
-- `dTwHeld55WState_108KH_37_54`
-- ============================================================================

/-- Pre-measurement circuit `dLoadAndVepMK108Anc_54 ;; dApexKoffWithInvMsbInc7Scr` on `rPG37` (`H ≤
54`). -/
noncomputable def dAxisPre108KH_37_54 {Var : Type} {mPayload K H n : ℕ}
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hmClean : 56 - H ≤ 6 + (K - 2)) (hH54 : H ≤ 54)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
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
    let hK48 := hK48_of_K36 K hK36
    let rM48 := rMPad48 hK48 rCore rMK hCMK
    let rPG48 := rPGPad48_37 rCore rPG37 hCP37
    .seq
      (dLoadAndVepMK108Anc_54 (hK9_of_K28 K hK28) hmClean (h9_of_K28 K hK28) hH54 c hm v w
        rCore rHdr61 rPreHold rMK rAnc hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA)
      (dApexKoffWithInvMsbInc7Scr (kickSkipKoffSpecTight K hK28 hK36) isInv v
        (rCore (coreCosetB1Block (hm6_of_hm22 hm) w)) rSum14 rM48 rPG48 rAnc
        (wCtrl_ne_rMPad48 hm hK48 w rCore rMK hCMK)
        (fun i ↦ hCA.ne (coreCosetB1Block (hm6_of_hm22 hm) w) i)
        (rSum14_disj_rMPad48 hK48 rCore rSum14 rMK hCMK hCSum hSMK)
        (rSum14_disj_rPGPad48_37 rCore rSum14 rPG37 hCP37 hCSum hSP37)
        (rPGPad48_37_disj_rMPad48 hK48 rCore rPG37 rMK hCP37 hCMK hP37MK)
        hSA (rMPad48_disj_rAnc hK48 rCore rMK rAnc hCMK hCA hMKA)
        (rPGPad48_37_disj_rAnc rCore rPG37 rAnc hCP37 hCA hP37A))

theorem disj_of_image_subset_left {k₁ k₂ k₃ n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {r₃ : QRegister k₃ n} (hSub : r₁.image ⊆ r₂.image) (hDisj : r₂.DisjointWires r₃) :
    r₁.DisjointWires r₃ := by
  rw [QRegister.disjoint_iff]; intro i j hij
  obtain ⟨i₂, hi₂⟩ := (QRegister.mem_image r₂ (r₁ i)).mp
    (hSub ((QRegister.mem_image r₁ (r₁ i)).mpr ⟨i, rfl⟩))
  exact hDisj.ne i₂ j (hi₂.trans hij)

theorem dAxisPre108KH_37_54_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload K H n : ℕ} [NeZero (2 ^ n)]
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hmClean : 56 - H ≤ 6 + (K - 2)) (hH54 : H ≤ 54)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
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
    (hDMK : (rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).DisjointWires
      rMK) :
    let hK9 := hK9_of_K28 K hK28
    let hK48 := hK48_of_K36 K hK36
    let kTail := ((fullSysCoreWires mPayload - (62 - K)) + 61) + H
    let fMul_s : BitAssignment ((kTail + 14) + 48) → ℤ :=
      fun γ ↦ (if isInv then -1 else 1) * fApexKoffShiftedZ (48 - K) kTail (iCtrlTail K H hm w) γ
    let uL := (selLoadInDataMK37 (mPayload := mPayload) (K := K) (H := H)).embedUnitary
      (uXorMK (fullMK108BitFn K H hK9 hH54 c hm w))
    let uM := (selKickInDataMK37 (mPayload := mPayload) (K := K) (H := H) hK48).embedUnitary
      (apexCatModAddZ ((kTail + 14) + 48) fMul_s)
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      ((rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).concat rMK hDMK)
      rAnc (uM * uL)
      (dAxisPre108KH_37_54 hK28 hK36 hmClean hH54 isInv c hm v w rCore rHdr61 rPreHold rSum14 rPG37
        rMK rAnc
        hCH61 hCHPH hCP37 hCMK hH61MK hPHMK hCA hH61A hPHA hCSum hSP37 hSMK hP37MK hSA hP37A
          hMKA) := by
  intro hK9 hK48 kTail fMul_s uL uM
  let rData := rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP
  let rDMK := rData.concat rMK hDMK
  have hCHA : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCA hH61A) hPHA
  have hDA : rData.DisjointWires rAnc :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCHA hSA) hP37A
  have hDMKA : rDMK.DisjointWires rAnc := QRegExt.disjointWires_concat_left hDA hMKA
  have hCHM : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rMK :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCMK hH61MK) hPHMK
  have hpLoadRaw := dLoadAndVepMK108Anc_54_realizesPair (Var := Var) hK9 hmClean (h9_of_K28 K hK28)
    hH54 c hm v w
    rCore rHdr61 rPreHold rMK rAnc hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA
  have hCompL := compose_selLoadInDataMK37 rCore rHdr61 rPreHold rSum14 rPG37 rMK
    hCH61 hCHPH hCHSum hCHSP hDMK hCHM
  have hpLoad : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rDMK rAnc uL
      (dLoadAndVepMK108Anc_54 hK9 hmClean (h9_of_K28 K hK28) hH54 c hm v w rCore rHdr61 rPreHold rMK
        rAnc
        hCH61 hCHPH hCMK hH61MK hPHMK hCA hH61A hPHA hMKA) := by
    have hf := hpLoadRaw.fwd
    change DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rMK hCHM) rAnc _ _ at hf
    rw [← hCompL] at hf; exact hf.widenActive
  let rST := rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH
  let rM48 := rMPad48 hK48 rCore rMK hCMK
  let rPG48 := rPGPad48_37 rCore rPG37 hCP37
  have hSubST := rSysTail_image_sub_rCHHold (K := K) rCore rHdr61 rPreHold hCH61 hCHPH
  have hCHP37 : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rPG37 := by
    rw [QRegister.disjoint_iff]; intro x y hxy
    exact hCHSP.ne (Fin.castAdd 14 x) y (by rwa [QRegister.concat_apply_left])
  have hTSum : rST.DisjointWires rSum14 := disj_of_image_subset_left hSubST hCHSum
  have hTP48 : rST.DisjointWires rPG48 :=
    rSysTail_disj_rPGPad48_37 hK48 rCore rHdr61 rPreHold rPG37 hCH61 hCHPH hCP37 hCHP37
  have hTM48 : rST.DisjointWires rM48 :=
    rSysTail_disj_rMPad48 hK48 rCore rHdr61 rPreHold rMK hCH61 hCHPH hCMK hH61MK hPHMK
  have hTA : rST.DisjointWires rAnc := disj_of_image_subset_left hSubST hCHA
  have hSM48 := rSum14_disj_rMPad48 hK48 rCore rSum14 rMK hCMK hCSum hSMK
  have hSP48 := rSum14_disj_rPGPad48_37 rCore rSum14 rPG37 hCP37 hCSum hSP37
  have hMP48 := rPGPad48_37_disj_rMPad48 hK48 rCore rPG37 rMK hCP37 hCMK hP37MK
  have hM48A := rMPad48_disj_rAnc hK48 rCore rMK rAnc hCMK hCA hMKA
  have hP48A := rPGPad48_37_disj_rAnc rCore rPG37 rAnc hCP37 hCA hP37A
  have hpKickRaw := dApexKoffWithInvMsbInc7Scr_realizesPair_core14M48PG
    (kickSkipKoffSpecTight K hK28 hK36) (Var := Var) v rST (iCtrlTail K H hm w)
    rSum14 rM48 rPG48 rAnc hTSum hTP48 hSP48 hTM48 hSM48 hMP48 hTA hSA hM48A hP48A
  have hCompK := compose_selKickInDataMK37 hK48 rCore rHdr61 rPreHold rSum14 rPG37 rMK
    hCH61 hCHPH hCHSum hCHSP hDMK hCP37 hCMK hTSum (QRegExt.disjointWires_concat_left hTM48 hSM48)
    (QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hTP48 hSP48) hMP48)
  have hwEq := rSysTail_iCtrlTail (K := K) (H := H) hm w rCore rHdr61 rPreHold hCH61 hCHPH
  have hpMul_s : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rDMK rAnc uM
      (dApexKoffWithInvMsbInc7Scr (kickSkipKoffSpecTight K hK28 hK36) isInv v (rCore
      (coreCosetB1Block (hm6_of_hm22 hm) w)) rSum14 rM48 rPG48 rAnc (wCtrl_ne_rMPad48 hm hK48
      w rCore rMK hCMK) (fun i ↦ hCA.ne (coreCosetB1Block (hm6_of_hm22 hm) w) i) hSM48 hSP48
      hMP48 hSA hM48A hP48A) := by
    have hdEq := dApexKoffWithInvMsbInc7Scr_congr_wCtrl (kickSkipKoffSpecTight K hK28 hK36) isInv
      (Var := Var) v hwEq rSum14 rM48 rPG48 rAnc
      (fun j ↦ hTM48.ne (iCtrlTail K H hm w) j) (fun i ↦ hTA.ne (iCtrlTail K H hm w) i)
      hSM48 hSP48 hMP48 hSA hM48A hP48A
      (wCtrl_ne_rMPad48 hm hK48 w rCore rMK hCMK)
      (fun i ↦ hCA.ne (coreCosetB1Block (hm6_of_hm22 hm) w) i)
      hSM48 hSP48 hMP48 hSA hM48A hP48A
    rw [← hdEq]; dsimp only [uM, fMul_s]; cases isInv
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      have hf := hpKickRaw.fwd; rw [← hCompK] at hf; exact hf.widenActive
    · simp only [↓reduceIte, neg_one_mul]
      have hi := hpKickRaw.inv; rw [← hCompK] at hi; have hw := hi.widenActive
      rw [apexCatModAddZ_inv ((kTail + 14) + 48) (fApexKoffShiftedZ (48 - K) kTail (iCtrlTail K H hm
        w))] at hw
      exact hw
  rw [dAxisPre108KH_37_54, vepLockVal_eq]; exact hpLoad.seq hDMKA hpMul_s

theorem dAxisPre108KH_37_54_action_eq {mPayload K H mAnc n : ℕ} [NeZero (2 ^ n)]
    (hK28 : 28 ≤ K) (hK36 : K ≤ 36) (hH54 : H ≤ 54)
    (isInv : Bool) (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (rAnc : QRegister mAnc n)
    (hCH61 : rCore.DisjointWires rHdr61) (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires
      rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hH61MK : rHdr61.DisjointWires rMK) (hPHMK : rPreHold.DisjointWires rMK)
    (hCSum : rCore.DisjointWires rSum14) (hSP37 : rSum14.DisjointWires rPG37)
    (hSMK : rSum14.DisjointWires rMK) (hP37MK : rPG37.DisjointWires rMK)
    (hMKA : rMK.DisjointWires rAnc)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hCHSP : ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37)
    (hDMK : (rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).DisjointWires
      rMK) :
    let hK9 := hK9_of_K28 K hK28
    let hK48 : K ≤ 48 := by omega
    let kTail := ((fullSysCoreWires mPayload - (62 - K)) + 61) + H
    let kSysNo14 := (((fullSysCoreWires mPayload - 14) + 61) + H) + 14
    let rData := rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP
    let fMul_s : BitAssignment ((kTail + 14) + 48) → ℤ :=
      fun γ ↦ (if isInv then -1 else 1) * fApexKoffShiftedZ (48 - K) kTail (iCtrlTail K H hm w) γ
    let Δ_s : BitAssignment kSysNo14 → ℤ :=
      fun γNo14 ↦ (if isInv then -1 else 1) * axisDelta108No14 K H hK9 hH54 c hm w γNo14
    let uL := (selLoadInDataMK37 (mPayload := mPayload) (K := K) (H := H)).embedUnitary
      (uXorMK (fullMK108BitFn K H hK9 hH54 c hm w))
    let uM := (selKickInDataMK37 (mPayload := mPayload) (K := K) (H := H) hK48).embedUnitary
      (apexCatModAddZ ((kTail + 14) + 48) fMul_s)
    let uTarget := (selNo14InAxisData37 (mPayload := mPayload) (H := H)).embedUnitary
      (apexCatModAddZ kSysNo14 Δ_s)
    ((rData.concat rMK hDMK).embedUnitary (uM * uL)).1 *
        (rMK.concat rAnc hMKA).basisOutcomeProjector 0 =
      setTableOp rData rMK (tblMK108Data37 K H hK9 hH54 c hm w) *
        (rData.embedUnitary uTarget).1 *
        (rMK.concat rAnc hMKA).basisOutcomeProjector 0 := by
  intro hK9 hK48 kTail kSysNo14 rData fMul_s Δ_s uL uM uTarget
  let rCH := rCHHold rCore rHdr61 rPreHold hCH61 hCHPH
  let rDMK := rData.concat rMK hDMK
  let rST := rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH
  let rSN := rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum
  let rM48 := rMPad48 hK48 rCore rMK hCMK
  let rPG48 := rPGPad48_37 rCore rPG37 hCP37
  let rCat34 := rPG37.slice 0 34 (by decide)
  have hCHM : rCH.DisjointWires rMK :=
    QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left hCMK hH61MK) hPHMK
  have hSubST := rSysTail_image_sub_rCHHold (K := K) rCore rHdr61 rPreHold hCH61 hCHPH
  have hCHP37 : rCH.DisjointWires rPG37 := by
    rw [QRegister.disjoint_iff]; intro x y hxy
    exact hCHSP.ne (Fin.castAdd 14 x) y (by rwa [QRegister.concat_apply_left])
  have hTSum : rST.DisjointWires rSum14 := disj_of_image_subset_left hSubST hCHSum
  have hTP48 : rST.DisjointWires rPG48 :=
    rSysTail_disj_rPGPad48_37 hK48 rCore rHdr61 rPreHold rPG37 hCH61 hCHPH hCP37 hCHP37
  have hTM48 : rST.DisjointWires rM48 :=
    rSysTail_disj_rMPad48 hK48 rCore rHdr61 rPreHold rMK hCH61 hCHPH hCMK hH61MK hPHMK
  have hSM48 : rSum14.DisjointWires rM48 :=
    rSum14_disj_rMPad48 hK48 rCore rSum14 rMK hCMK hCSum hSMK
  have hSP48 : rSum14.DisjointWires rPG48 :=
    rSum14_disj_rPGPad48_37 rCore rSum14 rPG37 hCP37 hCSum hSP37
  have hMP48 : rM48.DisjointWires rPG48 :=
    rPGPad48_37_disj_rMPad48 hK48 rCore rPG37 rMK hCP37 hCMK hP37MK
  have hTSM : (rST.concat rSum14 hTSum).DisjointWires rM48 :=
    QRegExt.disjointWires_concat_left (h₁₂ := hTSum) hTM48 hSM48
  have hExtP : ((rST.concat rSum14 hTSum).concat rM48 hTSM).DisjointWires rPG48 :=
    QRegExt.disjointWires_concat_left (h₁₂ := hTSM)
      (QRegExt.disjointWires_concat_left (h₁₂ := hTSum) hTP48 hSP48) hMP48
  have hSysPG := rSysNo14_disj_rPGPad48_37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCP37
    hCSum hCHSum hCHSP
  have hEL : (rDMK.embedUnitary uL).1 = ((rCH.concat rMK hCHM).embedUnitary
      (uXorMK (fullMK108BitFn K H hK9 hH54 c hm w))).1 := by
    dsimp only [uL]
    rw [← QRegister.embedUnitary_compose, compose_selLoadInDataMK37 rCore rHdr61 rPreHold rSum14
      rPG37 rMK
      hCH61 hCHPH hCHSum hCHSP hDMK hCHM]
  have hEM : (rDMK.embedUnitary uM).1 = ((((rST.concat rSum14 hTSum).concat rM48 hTSM).concat
      rPG48 hExtP).embedUnitary (apexCatModAddZ ((kTail + 14) + 48) fMul_s)).1 := by
    dsimp only [uM]
    rw [← QRegister.embedUnitary_compose, compose_selKickInDataMK37 hK48 rCore rHdr61 rPreHold
      rSum14 rPG37 rMK
      hCH61 hCHPH hCHSum hCHSP hDMK hCP37 hCMK hTSum hTSM hExtP]
  have hET : (rData.embedUnitary uTarget).1 =
      ((rSN.concat rPG48 hSysPG).embedUnitary (apexCatModAddZ kSysNo14 Δ_s)).1 := by
    dsimp only [uTarget]
    rw [← QRegister.embedUnitary_compose, compose_selNo14InAxisData37 rCore rHdr61 rPreHold rSum14
      rPG37
      hCH61 hCHPH hCHSum hCHSP hCP37 hSysPG]
  apply mat_ext_basisKet; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    FusedVepCore288.reg_zero_proj_mulVec_basisKet]
  split_ifs with hzAll
  · have hzMK : ∀ k : Fin K, β (rMK k) = 0 := fun k ↦ by
      have h := hzAll (Fin.castAdd mAnc k); rwa [QRegister.concat_apply_left] at h
    let β₁ : BitAssignment n := fun u ↦
      if hu : u ∈ rMK.image then
        let j := Classical.choose ((QRegister.mem_image rMK u).mp hu)
        β (rMK j) + fullMK108BitFn K H hK9 hH54 c hm w (fun q ↦ β (rCH q)) j
      else β u
    have hβ₁_out : ∀ z, z ∉ rMK.image → β₁ z = β z := fun z hz ↦ dite_neg_eq hz
    have hβ₁_in : ∀ k : Fin K, β₁ (rMK k) = fullMK108BitFn K H hK9 hH54 c hm w (fun q ↦
      β (rCH q)) k := fun k ↦ by
      have hm_in : rMK k ∈ rMK.image := (QRegister.mem_image rMK _).mpr ⟨k, rfl⟩
      have hch : Classical.choose ((QRegister.mem_image rMK _).mp hm_in) = k :=
        rMK.wires.injective (Classical.choose_spec ((QRegister.mem_image rMK _).mp hm_in))
      dsimp only [β₁]; rw [dite_pos_eq hm_in, hch, hzMK k, zero_add]
    have hevL : (rDMK.embedUnitary uL).1.mulVec (basisKet β) = basisKet β₁ := by
      rw [hEL]; exact embedUnitary_uXorMK_mulVec_ket _ rCH rMK hCHM β
    let γ₀ : BitAssignment kSysNo14 := fun q ↦ β (rSN q)
    let γ₁ : BitAssignment ((kTail + 14) + 48) := fun idx ↦ β₁ (((rST.concat rSum14 hTSum).concat
      rM48 hTSM) idx)
    let d₀ : ℤ := Δ_s γ₀
    have hfEq : fMul_s γ₁ = d₀ := by
      have hFullEq : fullMK108BitFn K H hK9 hH54 c hm w (fun q ↦ β (rCH q)) =
          fullMK108BitFn K H hK9 hH54 c hm w (padZero14CH γ₀) := by
        apply fullMK108BitFn_congr_ge14 K H hK9 hH54 c hm w; intro q hq14
        let kC := fullSysCoreWires mPayload; have hkC := core_ge_3954 mPayload
        dsimp only [padZero14CH, γ₀, rSN, rSysNo14, rCH, rCHHold]
        have hn14 : ¬(q.val < 14) := by omega
        have hqSub : q.val - 14 < kSysNo14 := by have := q.isLt; dsimp [kSysNo14, kC] at *; omega
        rw [dite_eq_right hn14]
        by_cases h1 : q.val < kC
        · have hcL : q = Fin.castAdd H (Fin.castAdd 61 ⟨q.val, h1⟩) := Fin.ext rfl
          have hcR : (⟨q.val - 14, hqSub⟩ : Fin kSysNo14) =
              Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61 ⟨q.val - 14, by omega⟩)) := Fin.ext rfl
          rw [congrArg (fun idx ↦ β (((rCore.concat rHdr61 hCH61).concat rPreHold hCHPH) idx)) hcL,
            QRegister.concat_apply_left, QRegister.concat_apply_left, hcR,
            QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
              QRegister.slice_apply]
          exact congrArg (fun idx ↦ β (rCore idx)) (Fin.ext (by dsimp; omega))
        · by_cases h2 : q.val < kC + 61
          · have hcL : q = Fin.castAdd H (Fin.natAdd kC (⟨q.val - kC, by omega⟩ : Fin 61)) :=
              Fin.ext (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
            have hcR : (⟨q.val - 14, hqSub⟩ : Fin kSysNo14) =
                Fin.castAdd 14 (Fin.castAdd H (Fin.natAdd (kC - 14) (⟨(q.val - 14) - (kC - 14),
                  by omega⟩ : Fin 61))) :=
              Fin.ext (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
            rw [congrArg (fun idx ↦ β (((rCore.concat rHdr61 hCH61).concat rPreHold hCHPH) idx))
              hcL,
              QRegister.concat_apply_left, QRegister.concat_apply_right, hcR,
              QRegister.concat_apply_left, QRegister.concat_apply_left,
                QRegister.concat_apply_right]
            exact congrArg (fun idx ↦ β (rHdr61 idx)) (Fin.ext (by dsimp; omega))
          · have hcL : q = Fin.natAdd (kC + 61) (⟨q.val - (kC + 61), by have := q.isLt; omega⟩ : Fin
              H) :=
              Fin.ext (by simp only [Fin.val_natAdd]; omega)
            have hcR : (⟨q.val - 14, hqSub⟩ : Fin kSysNo14) =
                Fin.castAdd 14 (Fin.natAdd ((kC - 14) + 61) (⟨(q.val - 14) - ((kC - 14) + 61),
                  by have := q.isLt; omega⟩ : Fin H)) :=
              Fin.ext (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
            rw [congrArg (fun idx ↦ β (((rCore.concat rHdr61 hCH61).concat rPreHold hCHPH) idx))
              hcL,
              QRegister.concat_apply_right, hcR, QRegister.concat_apply_left,
                QRegister.concat_apply_right]
            exact congrArg (fun idx ↦ β (rPreHold idx)) (Fin.ext (by dsimp; omega))
      have hSumEq : (fun s : Fin 14 ↦ γ₁ (Fin.castAdd 48 (Fin.natAdd kTail s))) =
          (fun s : Fin 14 ↦ γ₀ (Fin.natAdd (((fullSysCoreWires mPayload - 14) + 61) + H) s)) :=
            funext fun s ↦ by
        dsimp only [γ₁, γ₀, rSN, rSysNo14]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_right, QRegister.concat_apply_right,
          hβ₁_out _ (hSMK.apply_not_mem_right s)]
      have hCtrlEq : γ₁ (Fin.castAdd 48 (Fin.castAdd 14 (iCtrlTail K H hm w))) =
          γ₀ (Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61
            ⟨(coreCosetB1Block (hm6_of_hm22 hm) w).val - 14, by
              have := (coreCosetB1Block (hm6_of_hm22 hm) w).isLt
              have := coreCosetB1Block_val_ge_3954 hm w; omega⟩))) := by
        dsimp only [γ₁, γ₀, rSN, rSysNo14]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_left,
          rSysTail_iCtrlTail (K := K) (H := H) hm w rCore rHdr61 rPreHold hCH61 hCHPH,
          hβ₁_out _ (hCMK.apply_not_mem_right _), QRegister.concat_apply_left,
            QRegister.concat_apply_left,
          QRegister.concat_apply_left, QRegister.slice_apply]
        exact congrArg (fun idx ↦ β (rCore idx)) (Fin.ext (by
          have := coreCosetB1Block_val_ge_3954 hm w; dsimp; omega))
      let M₁ : Fin 48 → ZMod 2 := fun j ↦ γ₁ (Fin.natAdd (kTail + 14) j)
      let lo := bitsVal (fun i : Fin (48 - K) ↦ M₁ ⟨i.val, by omega⟩)
      have hlo_lt : lo < 2 ^ (48 - K) := bitsVal_lt_two_pow_gen _
      have hM_hi : (fun k : Fin K ↦ M₁ ⟨(48 - K) + k.val, by omega⟩) = fullMK108BitFn K H hK9 hH54 c
        hm w (padZero14CH γ₀) := by
        rw [← hFullEq]; funext k; dsimp only [M₁, γ₁, rM48]
        rw [QRegister.concat_apply_right, rMPad48_apply, dite_eq_right (by
          omega : ¬((48 - K) + k.val < 48 - K)),
          show (⟨((48 - K) + k.val) - (48 - K), by omega⟩ : Fin K) = k from Fin.ext (by
            dsimp; omega), hβ₁_in k]
      have hrRaw : bitsVal M₁ = lo + 2 ^ (48 - K) * bitsVal (fullMK108BitFn K H hK9 hH54 c hm w
        (padZero14CH γ₀)) := by
        rw [bitsVal_split_48 hK48 M₁, hM_hi]
      have hSlope : bitsVal (mEffBits (48 - K)
          (basisBits 48 ⟨(bitsVal M₁ + (1 - (γ₁ (Fin.castAdd 48 (Fin.castAdd 14 (iCtrlTail K H hm
            w)))).val) * 2 ^ 41) % 2 ^ 48,
            Nat.mod_lt _ (Nat.two_pow_pos 48)⟩)) = axisEffSlope108KH K H hK9 hH54 c hm w γ₀ := by
        rw [hrRaw, hCtrlEq]; exact mEffBits_shifted_pad_eq (48 - K) (by omega) lo _ _ hlo_lt
      have hBase : fApexKoffShiftedZ (48 - K) kTail (iCtrlTail K H hm w) γ₁ = axisDelta108No14 K H
        hK9 hH54 c hm w γ₀ := by
        dsimp only [fApexKoffShiftedZ, axisDelta108No14]
        rw [apexKoffDelta_eq_kOffFromEff (48 - K) (by omega) (by omega)]
        change (bitsVal (fun s : Fin 14 ↦ γ₁ (Fin.castAdd 48 (Fin.natAdd kTail s))) : ℤ) *
            (bitsVal (mEffBits (48 - K) (basisBits 48 ⟨(bitsVal M₁ + (1 - (γ₁ (Fin.castAdd 48
              (Fin.castAdd 14 (iCtrlTail K H hm w)))).val) * 2 ^ 41) % 2 ^ 48, _⟩)) : ℤ) -
          kOffFromEff (bitsVal (mEffBits (48 - K) (basisBits 48 ⟨(bitsVal M₁ + (1 - (γ₁ (Fin.castAdd
            48 (Fin.castAdd 14 (iCtrlTail K H hm w)))).val) * 2 ^ 41) % 2 ^ 48, _⟩))) = _
        rw [hSumEq, hSlope]
      dsimp only [fMul_s, d₀, Δ_s]; rw [hBase]
    have hdvd₀ : (2 ^ 11 : ℤ) ∣ d₀ :=
      dvd_mul_of_dvd_right (dvd_two_pow11_axisDelta108No14 K H hK9 hK36 hH54 c hm w γ₀) _
    have hdvd₁ : (2 ^ 11 : ℤ) ∣ fMul_s γ₁ := hfEq ▸ hdvd₀
    have hevM : (rDMK.embedUnitary uM).1.mulVec (basisKet β₁) =
        phiCat34 d₀ (regVal rCat34 β₁) • basisKet (shiftCatKet rCat34 β₁ (shiftNat34 d₀)) := by
      rw [hEM]
      exact (apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11
        ((rST.concat rSum14 hTSum).concat rM48 hTSM) (rCore.slice 0 11 _) rPG37
        (hCP37.compose_left _) hExtP fMul_s β₁ hdvd₁).trans
        (by dsimp only [γ₁] at hfEq; rw [hfEq])
    have hevT : (rData.embedUnitary uTarget).1.mulVec (basisKet β) =
        phiCat34 d₀ (regVal rCat34 β) • basisKet (shiftCatKet rCat34 β (shiftNat34 d₀)) := by
      rw [hET]
      exact apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11 rSN (rCore.slice 0 11 _) rPG37
        (hCP37.compose_left _) hSysPG Δ_s β hdvd₀
    have hCat34DisjMK : rCat34.DisjointWires rMK := hP37MK.compose_left _
    have hCatVal₁ : regVal rCat34 β₁ = regVal rCat34 β :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rCat34 fun p ↦
        hβ₁_out _ (hCat34DisjMK.apply_not_mem_right p)
    rw [asym_embedUnitary_mul_mulVec rDMK uM uL, hevL, hevM, hCatVal₁, hevT, Matrix.mulVec_smul]
    refine congrArg (phiCat34 d₀ (regVal rCat34 β) • ·) ?_
    let β_pg := shiftCatKet rCat34 β (shiftNat34 d₀)
    rw [show basisKet β_pg = Pi.single (M := fun _ ↦ ℂ) ((basisBitsEquiv n).symm β_pg) (1 : ℂ) from
      rfl,
      setTableOp_mulVec_single]
    let mTbl : Fin (2 ^ K) := (basisBitsEquiv K).symm (fullMK108BitFn K H hK9 hH54 c hm w (fun q ↦
      β (rCH q)))
    have hCHDisjCat34 : rCH.DisjointWires rCat34 := hCHP37.compose_right _
    have hTblEq : tblMK108Data37 K H hK9 hH54 c hm w (rData.extractIndex ((basisBitsEquiv n).symm
      β_pg)) = mTbl := by
      dsimp only [tblMK108Data37, mTbl]
      refine congrArg (basisBitsEquiv K).symm (congrArg (fullMK108BitFn K H hK9 hH54 c hm w) (funext
        fun q ↦ ?_))
      rw [rData.basisBits_extractIndex, basisBits_symm_apply]; dsimp only [rData]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      exact shiftCatKet_outside rCat34 β (shiftNat34 d₀) (hCHDisjCat34.apply_not_mem_right q)
    rw [hTblEq]
    let β_fin : BitAssignment n := basisBits n (rMK.replaceIndex ((basisBitsEquiv n).symm β_pg)
      mTbl)
    have hket_fin : Pi.single (M := fun _ ↦ ℂ) (rMK.replaceIndex ((basisBitsEquiv n).symm β_pg)
      mTbl) (1 : ℂ) =
        basisKet β_fin :=
      congrArg (fun g : Fin (2 ^ n) ↦ Pi.single (M := fun _ ↦ ℂ) g (1 : ℂ)) ((basisBitsEquiv
        n).symm_apply_apply _).symm
    rw [hket_fin]
    refine congrArg basisKet (FusedVepCore288.eq_shiftCatKet_of_outside_and_regVal
      rCat34 β_fin β₁ (shiftNat34 d₀) (fun z hzNot34 ↦ ?_) ?_).symm
    · by_cases hzM : z ∈ rMK.image
      · obtain ⟨k, rfl⟩ := (QRegister.mem_image rMK z).mp hzM
        dsimp only [β_fin, mTbl]
        rw [rMK.basisBits_replaceIndex_apply, hβ₁_in k, basisBits_symm_apply]
      · have hnR : z ∉ Set.range rMK.wires := fun ⟨k, hk⟩ ↦ hzM ((QRegister.mem_image rMK z).mpr ⟨k,
          hk⟩)
        dsimp only [β_fin, β_pg]
        rw [rMK.basisBits_replaceIndex_of_not_mem _ _ z hnR, basisBits_symm_apply,
          shiftCatKet_outside rCat34 β (shiftNat34 d₀) hzNot34, hβ₁_out z hzM]
    · have hfin_pg : regVal rCat34 β_fin = regVal rCat34 β_pg :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rCat34 fun p ↦ by
        have hnR : rCat34 p ∉ Set.range rMK.wires := fun ⟨k, hk⟩ ↦ hCat34DisjMK.ne p k hk.symm
        dsimp only [β_fin]
        rw [rMK.basisBits_replaceIndex_of_not_mem _ _ _ hnR, basisBits_symm_apply]
      rw [hfin_pg, regVal_shiftCatKet, hCatVal₁]
  · simp only [Matrix.mulVec_zero]

def tTwHeld37Wide54 (W : ℕ) : ℕ := 2 * (558 + tKickKoff55WState_108KH W 54)

noncomputable def twHeld37Wide54Spec190 (W : ℕ) (hW28 : 28 ≤ W) (hW36 : W ≤ 36) :
    Slot3InnerHeldTwSpec (tTwHeld37Wide54 W) where
  uTwHeldSub37 := uTwHeldSum42Sub37 uPref37HadCut W
  uTwCatSub37 := uTwCatSub37_base uPref37HadCut W
  uTwEff := uT0CoreOfTrunc (truncWCfg W)
  hCommCtrl3Cat := (twHeld37Wide52Spec190 W hW28 hW36).hCommCtrl3Cat
  hTwStreamE := (twHeld37Wide52Spec190 W hW28 hW36).hTwStreamE
  hSlack010 := (twHeld37Wide52Spec190 W hW28 hW36).hSlack010
  hIntertwinesTw := (twHeld37Wide52Spec190 W hW28 hW36).hIntertwinesTw

section Part4_Slot3AndSym14Select
open Slot3Norm1s36_161w (Norm1sTier)
open GqspSlot3UltraBkAnd8TierCert (IsCertifiedNorm1sTier6)
open UltraSlot3MasterBkBundle (tLeaf3CtrlUltraBk tLeaf3CatUltraBk)

noncomputable def mkNorm1sSlot3InnerSlot3InnerSpec_tw54 (trunc : Configuration → Configuration)
    (W bk : ℕ) (t : Norm1sTier) (hW28 : 28 ≤ W) (hW36 : W ≤ 36) (hTrunc : trunc = truncWCfg W)
    (hbk : 21 ≤ bk ∧ bk ≤ 36) (ht : IsCertifiedNorm1sTier6 t) : Slot3InnerSlot3InnerSpec trunc
    (twHeld37Wide54Spec190 W hW28 hW36) (tLeaf3CtrlUltraBk bk t) (tLeaf3CatUltraBk bk t) :=
    mkNorm1sSlot3InnerSlot3InnerSpec trunc W bk t hW28 hW36 hTrunc hbk ht

end Part4_Slot3AndSym14Select
end WideTwist54AndSlot3Bridge

noncomputable section Held210

section
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace Held210
local instance (priority := 1000000) instNeZeroTwoPowAuxHeld210 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (T toffoli)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (TempPhaseProg cleanRem tailScr
  mul_mulVec_prog writeRegProg writeRegProg_apply_reg writeRegProg_apply_of_not_mem)
open FullSysCatSegmentBridge (fullSysCoreWires)
open ShiftedMagS1 (disjConcatLeft)
open StepBBlock0 (padZeroBits149_clean)
open MeasureBranchHadamardSem (ket ket_projZeroAll matrix_ext_ket projZeroAll
  projZeroAll_conjTranspose RealizesCleanUnitary)
open Prod57BoothHoist StepBOuter
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (permOfInvol permReg st0)
open Slot3ZRetCore
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36Physics80 (uCore149Norm1s)
open Slot3Norm1s36CoreWide
open Leaf3Slot3Norm1sWidth204 (Slot3LeafSpec uSlot3Swap3Cat36Norm1s)
open OraAndPrepBundle (castNatReg catUnitaryToFullSys)
open Slot3StreamUncK35Shift3 (rEC80)
open Barrel3PassSelectStitch (rCoreInCT80)
open Leaf4Twist162 (rCtrl3InCoreCat)
open Leaf3HadCutBridge (uSlot3HadCutCat36Mom uSlot3HadCutCat36FullSys dSub36OfLeaf
  count_dSub36OfLeaf_toff count_dSub36OfLeaf_t_le dSub36OfLeaf_realizes)
open SelectStitch (Leaf3SpecCore rCoreTopCatInCT)
open Leaf3Slot3ZRet193
open Leaf3Slot3ZRetOuter
open Leaf3MidKickBkAnd (dRejKick0_437 dRejKick0_437_count_t dRejKick0_437_count_toff
  n1s_st2_out32_zero_of_ge_wAcc)
open Leaf3BundleFast2770AndMidKickOpt (wAcc_bounds stepBundleW_dRejKick0 dRevTailZQuadRet216_256
  dRevTailZQuadRet216_256_count_t dRevTailZQuadRet216_256_count_toff
  stepBundleW_dRevTailZQuadRet256)
open Slot3BoothOpt (n1sTotOptSaveS3 zret_opt3_core_arith dN1sFwdW_opt3 dN1sFwdW_opt3_count_toff
  dN1sFwdW_opt3_count_t_exact stepBundleW_dN1sFwdW_opt3 dN1sRevW_opt3 dN1sRevW_opt3_count_toff
  dN1sRevW_opt3_count_t_exact stepBundleW_dN1sRevW_opt3)
open Leaf3MasterBundle (dPostMKCtrl84 dPostMKCtrl84_count_t dPostMKCtrl84_count_toff
  stepBundleW_dPostMKCtrl84)
open Slot3Fast414BkPullback94 (Slot3MidKickBkCompactSpec)
open Slot3NuclearTruncBkPhysics (truncBkNucCfg)
open Slot3MasterBk2490NoTopBridge (slot3HadCutLeafSpec36OfTrunc fast414TruncBkCfg
  fast414_truncBkNucCfg_of_truncBkNucCfg)
open Leaf3MasterBkBundle (StepBundleW.widen_topW mkSlot3Cat36LeafOfTruncCoreWithDummy
  castNatUnitary_uSlot3HadCutCat36Mom)
open GqspSlot3UltraBkAnd8TierCert (IsCertifiedNorm1sTier6 s3Swap3OracleNorm1sUltraBk
  s3Swap3OracleNorm1sUltraBk_commEC embed_uSlot3HadCutCat36FullSys_ultraBk_top
  commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut_ultra)
open FastNorm1sMasterBkBundle (stage26SaveFast)
open FastSTrue18XorSq (swap388W validSwapRelayWM_388 pStep1XorSq_275 pStep1XorSq_275_count
  stepBundleW_step1XorSq dSTrue18RevXorSq_275 dSTrue18RevXorSq_275_count_t
  dSTrue18RevXorSq_275_count_toff stepBundleW_dSTrue18RevXorSq)
open FastSlot3PrepAndCompact2458 (tPrepAdaptiveRT slot3PrepAdaptiveSpec)
open WideSlot3ZeroPostMKAndMaster (Leaf3WideSpec mkLeaf3WideSpecOfTruncLeaves)
open WideSlot3HeldU54Shave (tMidKickHeldU54BkOpt slot3MidKickHeldU54BkOptSpec)
/-- Effective core workspace width (`210 ≤ mCoreEff mWB ≤ 288` for `210 ≤ mWB`). -/
abbrev mCoreEff (mWB : ℕ) : ℕ := min mWB 288
/-- Full `bk - 3` `MidKick` clean-wire slack at `210 ≤ mWB` (`36 - bk + (bk - 3) = 33`). -/
abbrev kHeld210 (bk : ℕ) : ℕ := bk - 3
theorem kHeld210_hs {bk : ℕ} (hbk : 9 ≤ bk ∧ bk ≤ 36) :
    33 ≤ 36 - bk + kHeld210 bk := by
  dsimp only [kHeld210]
  omega
/-- Held-`u54` Regime-A `uCore149Norm1s` `.T` cap (`210 ≤ mWB`). -/
def tCoreHeld210 (bk : ℕ) (t : Norm1sTier) : ℕ :=
  Norm1sTier.tCoreWide t + tMidKickHeldU54BkOpt bk - 5352 - stage26SaveFast t
/-- Held-`u54` full Slot-3 (`Prep + Core`) `.T` cap (`210 ≤ mWB`). -/
def tLeaf3Held210 (mWB bk : ℕ) (t : Norm1sTier) : ℕ :=
  tPrepAdaptiveRT mWB + tCoreHeld210 bk t
theorem tCoreWide_ge_5436_save (t : Norm1sTier) :
    5436 + stage26SaveFast t ≤ Norm1sTier.tCoreWide t := by
  cases t <;> decide
def clearMaskWide (mMW mQ : ℕ) (ξ : BitAssignment 437) (w : Wire 437) : ZMod 2 :=
  if (177 ≤ w.val ∧ w.val < 177 + mMW) ∨ (251 ≤ w.val ∧ w.val < 251 + mQ) then 0 else ξ w
theorem clearMaskWide_21_3 : clearMaskWide 21 3 = clearPreMKCtrl := by
  funext ξ w; dsimp only [clearMaskWide, clearPreMKCtrl]
theorem cleanRem_clearMaskWide (mMW mQ : ℕ) (_ : mMW ≤ 21) (_ : mQ ≤ 3)
    {ξ : BitAssignment 437} (hcl : cleanRem 437 (437 - 275) ξ) :
    cleanRem 437 (437 - 275) (clearMaskWide mMW mQ ξ) := fun w hw ↦ by
  dsimp only [clearMaskWide]
  split_ifs
  · rfl
  · exact hcl w hw
/-- Unified `174 + (94 + k)` selector function harvesting `[0..174)` followed by the first `94 + k`
clean wires of `[177 .. 177 + mMW) ++ [201 + t.wAcc .. 251 + mQ) ++ {257} ++ [275 .. topW)`. -/
def mkSelMaskWideFun (mMW mQ k topW : ℕ) (t : Norm1sTier) (hmMW : mMW ≤ 21) (hmQ : mQ ≤ 3)
    (htop : topW ≤ 437) (hk_cap : 318 + k + t.wAcc ≤ topW + mMW + mQ)
    (idx : Fin (174 + (94 + k))) : Fin 437 :=
  if h0 : idx.val < 174 then ⟨idx.val, by omega⟩
  else if h1 : idx.val < 174 + mMW then ⟨177 + (idx.val - 174), by omega⟩
  else if h2 : idx.val < 224 + mMW + mQ - t.wAcc then
    ⟨(201 + t.wAcc) + (idx.val - (174 + mMW)), by have := wAcc_bounds t; omega⟩
  else if h3 : idx.val = 224 + mMW + mQ - t.wAcc then ⟨257, by decide⟩
  else ⟨275 + (idx.val - (225 + mMW + mQ - t.wAcc)), by
    have := wAcc_bounds t; have := idx.isLt; omega⟩
theorem mkSelMaskWideFun_inj (mMW mQ k topW : ℕ) (t : Norm1sTier) (hmMW : mMW ≤ 21)
    (hmQ : mQ ≤ 3) (htop : topW ≤ 437) (hk_cap : 318 + k + t.wAcc ≤ topW + mMW + mQ) :
    Function.Injective (mkSelMaskWideFun mMW mQ k topW t hmMW hmQ htop hk_cap) := by
  intro a b h
  have hw := wAcc_bounds t
  have ha := a.isLt
  have hb := b.isLt
  have hv := congrArg Fin.val h
  dsimp only [mkSelMaskWideFun] at hv
  split_ifs at hv <;> (dsimp only at hv; exact Fin.ext (by omega))
/-- Bundled `QRegister (174 + (94 + k)) 437` selector for `clearMaskWide mMW mQ`. -/
def mkSelMaskWide (mMW mQ k topW : ℕ) (t : Norm1sTier) (hmMW : mMW ≤ 21) (hmQ : mQ ≤ 3)
    (htop : topW ≤ 437) (hk_cap : 318 + k + t.wAcc ≤ topW + mMW + mQ) : QRegister
    (174 + (94 + k)) 437 := ⟨⟨mkSelMaskWideFun mMW mQ k topW t hmMW hmQ htop hk_cap,
    mkSelMaskWideFun_inj mMW mQ k topW t hmMW hmQ htop hk_cap⟩⟩
theorem mkSelMaskWide_apply (mMW mQ k topW : ℕ) (t : Norm1sTier) (hmMW : mMW ≤ 21)
    (hmQ : mQ ≤ 3) (htop : topW ≤ 437) (hk_cap : 318 + k + t.wAcc ≤ topW + mMW + mQ)
    (idx : Fin (174 + (94 + k))) : mkSelMaskWide mMW mQ k topW t hmMW hmQ htop hk_cap idx =
    mkSelMaskWideFun mMW mQ k topW t hmMW hmQ htop hk_cap idx := rfl
/-- General `StepBundleW` bridge for any `Slot3MidKickBkCompactSpec bk (94 + k) tMK` under
`clearMaskWide mMW mQ` across all 4 regimes `(21, 3)`, `(7, 3)`, `(0, 3)`, `(0, 0)`. -/
theorem stepBundleW_midKickBk_maskWide {bk k tMK : ℕ}
    (S : Slot3MidKickBkCompactSpec bk (94 + k) tMK) (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) (mMW mQ topW : ℕ) (hmMW : mMW ≤ 21) (hmQ : mQ ≤ 3)
    (h275 : 275 ≤ topW) (htop : topW ≤ 437) (hk_cap : 318 + k + t.wAcc ≤ topW + mMW + mQ)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCombBase : QRegister 437 n) : StepBundleW topW v rCombBase
    (clearMaskWide mMW mQ ∘ putQZ ∘ n1sSt2 t)
    (clearMaskWide mMW mQ ∘ putQZ ∘ n1sSt3 t (fast414TruncBkCfg bk cfg)) (fun _ ↦ 0)
    (S.dMidKick cfg v (rCombBase.compose (mkSelMaskWide mMW mQ k topW t hmMW hmQ htop
    hk_cap))) := by
  have hw := wAcc_bounds t
  let mClean := 94 + k
  let sel := mkSelMaskWide mMW mQ k topW t hmMW hmQ htop hk_cap
  let cBk := fast414TruncBkCfg bk cfg
  let δ_in : BitAssignment 149 → BitAssignment 437 := clearMaskWide mMW mQ ∘ putQZ ∘ n1sSt2 t
  let δ_out : BitAssignment 149 → BitAssignment 437 := clearMaskWide mMW mQ ∘ putQZ ∘ n1sSt3 t cBk
  let rMK : QRegister (174 + mClean) n := rCombBase.compose sel
  have hsel_lt : ∀ i : Fin 174, sel ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := fun i ↦ by
    dsimp only [sel]
    rw [mkSelMaskWide_apply]
    exact Fin.ext (by dsimp [mkSelMaskWideFun]; rw [dite_eq_left i.isLt])
  have hsel_top : ∀ j : Fin mClean, (sel ⟨174 + j.val, by omega⟩).val < topW := fun j ↦ by
    have hj := j.isLt
    dsimp only [sel]
    rw [mkSelMaskWide_apply]
    dsimp only [mkSelMaskWideFun]
    split_ifs <;> (dsimp; omega)
  have hsel_zero : ∀ (α : BitAssignment 149) (j : Fin mClean),
      δ_in α (sel ⟨174 + j.val, by omega⟩) = 0 := fun α j ↦ by
    have hj := j.isLt
    have hcl_in : cleanRem 437 (437 - 275) (δ_in α) :=
      cleanRem_clearMaskWide mMW mQ hmMW hmQ (cleanRem_putQZ (n1s_st2_props t α).1.hcl)
    by_cases hj1 : j.val < mMW
    · dsimp only [δ_in, sel, Function.comp_apply]
      rw [mkSelMaskWide_apply]; dsimp only [mkSelMaskWideFun]
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      dsimp only [clearMaskWide]
      exact ite_eq_left (Or.inl ⟨by omega, by omega⟩)
    · by_cases hj2 : j.val < mMW + (32 - t.wAcc)
      · dsimp only [δ_in, sel, Function.comp_apply]
        rw [mkSelMaskWide_apply]; dsimp only [mkSelMaskWideFun]
        rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
        dsimp only [clearMaskWide]
        rw [ite_eq_right (by omega), putQZ_of_lt251 (by dsimp; omega)]
        have hidx : (⟨(201 + t.wAcc) + (174 + j.val - (174 + mMW)), by omega⟩ : Wire 437) =
            ⟨201 + (t.wAcc + (j.val - mMW)), by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hidx]
        exact n1s_st2_out32_zero_of_ge_wAcc t α ⟨t.wAcc + (j.val - mMW), by omega⟩ (by dsimp; omega)
      · by_cases hj3 : j.val < mMW + (50 - t.wAcc)
        · dsimp only [δ_in, sel, Function.comp_apply]
          rw [mkSelMaskWide_apply]; dsimp only [mkSelMaskWideFun]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
          dsimp only [clearMaskWide]
          rw [ite_eq_right (by omega), putQZ_of_lt251 (by dsimp; omega)]
          exact (n1s_st2_props t α).1.hz233 _ (by dsimp; omega) (by dsimp; omega)
        · by_cases hj4 : j.val < mMW + (50 + mQ - t.wAcc)
          · dsimp only [δ_in, sel, Function.comp_apply]
            rw [mkSelMaskWide_apply]; dsimp only [mkSelMaskWideFun]
            rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
            dsimp only [clearMaskWide]
            exact ite_eq_left (Or.inr ⟨by omega, by omega⟩)
          · by_cases hj5 : j.val = mMW + (50 + mQ - t.wAcc)
            · dsimp only [δ_in, sel, Function.comp_apply]
              rw [mkSelMaskWide_apply]; dsimp only [mkSelMaskWideFun]
              rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                dite_eq_left (by omega)]
              dsimp only [clearMaskWide]
              rw [ite_eq_right (by omega), putQZ_of_ge257 (by decide)]
              exact (n1s_st2_props t α).1.hz233 _ (by decide) (by decide)
            · refine hcl_in _ ?_
              dsimp only [sel]; rw [mkSelMaskWide_apply]; dsimp only [mkSelMaskWideFun]
              rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                dite_eq_right (by omega)]
              dsimp; omega
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) :=
    fun α ↦ cleanRem_clearMaskWide mMW mQ hmMW hmQ (cleanRem_putQZ (n1s_st3_retainedInv t cBk
      α).hcl)
  have hTail : ∀ j : Fin mClean,
      tailScr rMK mClean (by omega) j = rCombBase (sel ⟨174 + j.val, by omega⟩) := fun j ↦ by
    dsimp only [tailScr, rMK]
    rw [QRegister.compose_apply]
    congr 2
    exact Fin.ext (by dsimp; omega)
  have hSlice : ∀ i : Fin 174,
      rMK.slice 0 174 (by omega) i = rCombBase ⟨i.val, by omega⟩ := fun i ↦ by
    dsimp only [rMK]
    rw [QRegister.slice_apply, QRegister.compose_apply]
    congr 1
    exact (congrArg (fun x ↦ sel x) (Fin.ext (Nat.zero_add i.val))).trans (hsel_lt i)
  have hδ_lt174 : ∀ α (i : Fin 174), δ_in α ⟨i.val, by omega⟩ = n1sSt2 t α ⟨i.val, by omega⟩ :=
    fun α i ↦ by
      dsimp only [δ_in, clearMaskWide, Function.comp_apply]
      rw [ite_eq_right (by omega), putQZ_of_lt251 (by dsimp; omega)]
  have hδ_out_lt174 : ∀ α (i : Fin 174),
      δ_out α ⟨i.val, by omega⟩ = n1sSt3 t cBk α ⟨i.val, by omega⟩ := fun α i ↦ by
    dsimp only [δ_out, clearMaskWide, Function.comp_apply]
    rw [ite_eq_right (by omega), putQZ_of_lt251 (by dsimp; omega)]
  have hnon3 : ∀ α (q : Wire 437), ¬(107 ≤ q.val ∧ q.val < 149) →
      n1sSt3 t cBk α q = n1sSt2 t α q := fun α q hq ↦ by
    obtain ⟨hInv2, hAct2, _, _, _, hacc2⟩ := n1s_st2_props t α
    obtain ⟨hmk_non, _⟩ := n1s_midKick36_cat42_eq t cBk α hInv2 hAct2 hacc2
    dsimp only [n1sSt3, n1sLiftEval411]
    by_cases h411 : q.val < 411
    · rw [dite_eq_left h411]; exact hmk_non ⟨q.val, h411⟩ hq
    · rw [dite_eq_right h411]; exact (hInv2.hcl q (by omega)).symm
  have hδ_ge174 : ∀ α (q : Wire 437), 174 ≤ q.val → δ_out α q = δ_in α q := fun α q hq ↦ by
    have hpz : ∀ u : Wire 437, 174 ≤ u.val → putZ3 (n1sSt3 t cBk α) u = putZ3 (n1sSt2 t α) u :=
      fun u hu ↦ by
        dsimp only [putZ3]
        split_ifs with hz
        · exact zMagBit_congr_u22 (fun i ↦ hnon3 α (u22WAux i) (by dsimp [u22WAux]; omega)) _
        · exact hnon3 α u (by omega)
    have hpqz : ∀ u : Wire 437, 174 ≤ u.val → putQZ (n1sSt3 t cBk α) u = putQZ (n1sSt2 t α) u :=
      fun u hu ↦ by
        dsimp only [putQZ, putQ3]
        split_ifs with h251
        · have hl_all : ∀ idx : Fin 3, 174 ≤ (lhsQuad3 idx).val := by decide
          have hr_all : ∀ idx : Fin 3, 174 ≤ (rhsQuad3 idx).val := by decide
          have hl := hpz (lhsQuad3 ⟨u.val - 251, by omega⟩) (hl_all _)
          have hr := hpz (rhsQuad3 ⟨u.val - 251, by omega⟩) (hr_all _)
          exact congrArg₂ (· * ·) hl hr
        · exact hpz u hu
    dsimp only [δ_out, δ_in, clearMaskWide, Function.comp_apply]
    split_ifs
    · rfl
    · exact hpqz q hq
  obtain ⟨U, hRealMK, hKetMK⟩ := S.hReal cfg v rMK
  let P_in := baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α)
  have hSub : projZeroAll mClean (tailScr rMK mClean (by omega)) * P_in = P_in := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, ket_baseDiagProjW]
    by_cases hP : (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
        ∃ α, zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α
    · rw [ite_eq_left hP, ket_projZeroAll]
      obtain ⟨_, α, htop_eq⟩ := hP
      refine ite_eq_left fun j ↦ ?_
      rw [hTail j]
      have hz := congrFun htop_eq (sel ⟨174 + j.val, by omega⟩)
      rw [zeroTopW_lt (hsel_top j)] at hz
      exact hz.trans (hsel_zero α j)
    · rw [ite_eq_right hP, Matrix.mulVec_zero]
  have hReal : RealizesCleanUnitary v P_in (S.dMidKick cfg v rMK) U :=
    RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose mClean _)
      (baseDiagProjW_conjTranspose topW rCombBase _) hSub hRealMK
  have hMulVec : ∀ (β : BitAssignment n) (α : BitAssignment 149), zeroTopW topW
      (fun idx ↦ β (rCombBase idx)) = δ_in α → U.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (0 : ZMod 2).val) • ket (writeRegProg β rCombBase (liftTopW topW (δ_out α)
      (fun idx ↦ β (rCombBase idx)))) := by
    intro β α htop_eq
    have hβ_zero : ∀ j : Fin mClean, β (tailScr rMK mClean (by omega) j) = 0 := fun j ↦ by
      rw [hTail j]
      have hz := congrFun htop_eq (sel ⟨174 + j.val, by omega⟩)
      rw [zeroTopW_lt (hsel_top j)] at hz
      exact hz.trans (hsel_zero α j)
    rw [hKetMK β hβ_zero, ZMod.val_zero, _root_.pow_zero, one_smul]
    let γ0 : BitAssignment 411 :=
      fun w ↦ if hw : w.val < 174 then β (rMK ⟨w.val, by omega⟩) else 0
    let γ411 : BitAssignment 411 := fun w ↦ n1sSt2 t α ⟨w.val, by omega⟩
    have hγ0_lt : ∀ i : ℕ, (hi1 : i < 174) →
        γ0 ⟨i, by omega⟩ = n1sSt2 t α ⟨i, by omega⟩ := fun i hi1 ↦ by
      dsimp only [γ0, rMK, QRegister.compose_apply]
      rw [dite_eq_left hi1, hsel_lt ⟨i, hi1⟩]
      have hz := congrFun htop_eq ⟨i, by omega⟩
      rw [zeroTopW_lt (by dsimp; omega)] at hz
      exact hz.trans (hδ_lt174 α ⟨i, hi1⟩)
    have hmk0 : Slot3MidKick36_161w.mk36Clean161 γ0 := fun u hu ↦ by
      dsimp only [γ0]
      rcases hu with ⟨h1, _⟩ | h3 <;> exact dite_eq_right (by omega)
    have hmk411 : Slot3MidKick36_161w.mk36Clean161 γ411 := fun u hu ↦ by
      rcases hu with ⟨h1, h2⟩ | h3
      · exact (n1s_st2_props t α).1.hz233 ⟨u.val, by omega⟩ h1 h2
      · exact (n1s_st2_props t α).1.hcl ⟨u.val, by omega⟩ (by dsimp; omega)
    have hEv174 : ∀ i : Fin 174,
        (Slot3MidKick36_161w.progMidKick216_36_411 cBk).evalBits
          γ0 ⟨i.val, by omega⟩ = δ_out α ⟨i.val, by omega⟩ := fun i ↦ by
      have h1 := Slot3MidKick36_161w.progMidKick216_36_411_eq_437
        cBk γ0 (n1sSt2 t α) hmk0 (n1s_st2_props t α).1.hcl hγ0_lt i.val i.isLt
      have h2 := Slot3MidKick36_161w.progMidKick216_36_411_eq_437
        cBk γ411 (n1sSt2 t α) hmk411 (n1s_st2_props t α).1.hcl (fun _ _ ↦ rfl) i.val i.isLt
      rw [hδ_out_lt174 α i]
      dsimp only [n1sSt3, n1sLiftEval411]
      rw [dite_eq_left (by omega)]
      exact h1.trans h2.symm
    congr 1; funext x
    by_cases hmem : x ∈ Set.range rCombBase.wires
    · obtain ⟨w, rfl⟩ := hmem
      rw [writeRegProg_apply_reg]
      by_cases hw174 : w.val < 174
      · let i : Fin 174 := ⟨w.val, hw174⟩
        have hw_eq : rCombBase w = rMK.slice 0 174 (by omega) i := (hSlice i).symm
        rw [hw_eq, writeRegProg_apply_reg, liftTopW_lt (by omega)]
        exact hEv174 i
      · have hnot174 : rCombBase w ∉ Set.range (rMK.slice 0 174 (by omega)).wires := by
          rintro ⟨i, hi⟩
          have hi' : rCombBase ⟨i.val, by omega⟩ = rCombBase w := (hSlice i).symm.trans hi
          have hv := congrArg Fin.val (rCombBase.wires.injective hi')
          dsimp at hv; omega
        rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot174]
        by_cases hwTop : w.val < topW
        · rw [liftTopW_lt hwTop, hδ_ge174 α w (by omega)]
          have hz := congrFun htop_eq w
          rw [zeroTopW_lt hwTop] at hz
          exact hz
        · rw [liftTopW_ge (by omega)]
    · have hnot174 : x ∉ Set.range (rMK.slice 0 174 (by omega)).wires := by
        rintro ⟨i, rfl⟩
        exact hmem ⟨⟨i.val, by omega⟩, (hSlice i).symm⟩
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot174,
          writeRegProg_apply_of_not_mem _ _ _ _ hmem]
  refine ⟨h275, hcl_out, S.hPres cfg v rMK, ⟨U, hReal, hMulVec, ?_⟩⟩
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_baseDiagProjW]
  by_cases hP : (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
      ∃ α, zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α
  · rw [ite_eq_left hP]
    obtain ⟨_, α, htop_eq⟩ := hP
    rw [hMulVec β α htop_eq, Matrix.mulVec_smul, ket_baseDiagProjW]
    let β' := writeRegProg β rCombBase (liftTopW topW (δ_out α) (fun idx ↦ β (rCombBase idx)))
    have hβ'_reg : (fun idx ↦ β' (rCombBase idx)) = liftTopW topW (δ_out α)
        (fun idx ↦ β (rCombBase idx)) := funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
    have hscr' : ∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β' (rCombBase w) = 0 :=
      fun w hw1 hw2 ↦ by
        change (fun idx ↦ β' (rCombBase idx)) w = 0
        rw [hβ'_reg, liftTopW_lt hw2]
        exact hcl_out α w hw1
    have htop' : ∃ α', zeroTopW topW (fun idx ↦ β' (rCombBase idx)) = δ_out α' :=
      ⟨α, by rw [hβ'_reg, zeroTopW_liftTopW h275 _ (hcl_out α)]⟩
    rw [ite_eq_left ⟨hscr', htop'⟩]
  · rw [ite_eq_right hP, Matrix.mulVec_zero, Matrix.mulVec_zero]
/-! ## Section 3: 4-Regime `dCore149Regime{A,B,B2,C}` Pipelines & Adaptive `dCore149WideGen` (`190 ≤
mWB`) -/
/-- Regime-A (`190 ≤ mCoreEff mWB`, `84-T` `dPostMKCtrl84`) 10-stage core pipeline on `QRegister 437
n`. -/
noncomputable def dCore149RegimeA_onBase (mWB bk : ℕ)
    (hm : 210 ≤ mCoreEff mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36)
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) : DynamicCircuit Var n :=
  let cBk := truncBkNucCfg bk cfg
  let topW := 149 + mCoreEff mWB
  let kA := kHeld210 bk
  have htop437 : topW ≤ 437 := by dsimp [topW, mCoreEff]; omega
  have hk_cap : 318 + kA + t.wAcc ≤ topW + 21 + 3 := by
    have := wAcc_bounds t; have := hbk.2; dsimp [topW, kA, kHeld210, mCoreEff] at hm ⊢; omega
  let rRelay388 := rCombBase.compose (permReg (permOfInvol
    (swap388W 339 (by decide) (by decide))
    (validSwapRelayWM_388 (topW := 339) (by decide) (by decide)).invol))
  let rRelay374 := rCombBase.compose (permReg (permOfInvol
    (swap374W 339 (by decide) (by decide))
    (validSwapRelayWM_374 (topW := 339) (by decide) (by decide)).invol))
  .seq ((pStep1XorSq_275.onRegister rRelay388).toDyn v)
    (.seq (dPreMKCtrl v rCombBase)
      (.seq (dN1sFwdW_opt3 t 339 (Or.inr (Or.inl rfl)) v rCombBase)
        (.seq (dRejKick0_437 v rCombBase)
          (.seq ((slot3MidKickHeldU54BkOptSpec bk kA hbk.1 hbk.2 (kHeld210_hs hbk)).dMidKick
              cBk v (rCombBase.compose
                (mkSelMaskWide 21 3 kA topW t le_rfl le_rfl htop437 hk_cap)))
            (.seq ((pStep5ZRet30.onRegister rCombBase).toDyn v)
              (.seq (dN1sRevW_opt3 t cBk 339 (Or.inr (Or.inl rfl)) v rCombBase)
                (.seq (dPostMKCtrl84 v rCombBase)
                  (.seq (dSTrue18RevXorSq_275 v rRelay388)
                    (dRevTailZQuadRet216_256 v rRelay374)))))))))
theorem dCore149RegimeA_onBase_count_toff (mWB bk : ℕ)
    (hm : 210 ≤ mCoreEff mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36)
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dCore149RegimeA_onBase mWB bk hm hbk t cfg v rCombBase).count toffoli = 0 := by
  dsimp only [dCore149RegimeA_onBase]
  repeat rw [n1s_dyn_count_seq]
  rw [TempPhaseProg.toDyn_count_toff, dPreMKCtrl_count_toff, dN1sFwdW_opt3_count_toff,
    dRejKick0_437_count_toff,
    (slot3MidKickHeldU54BkOptSpec bk (kHeld210 bk) hbk.1 hbk.2 (kHeld210_hs hbk)).hToff,
    TempPhaseProg.toDyn_count_toff, dN1sRevW_opt3_count_toff, dPostMKCtrl84_count_toff,
    dSTrue18RevXorSq_275_count_toff, dRevTailZQuadRet216_256_count_toff]
theorem dCore149RegimeA_onBase_count_t (mWB bk : ℕ)
    (hm : 210 ≤ mCoreEff mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36)
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dCore149RegimeA_onBase mWB bk hm hbk t cfg v rCombBase).count T ≤
      tCoreHeld210 bk t := by
  have hf := dN1sFwdW_opt3_count_t_exact t 339 (Or.inr (Or.inl rfl)) v rCombBase
  have hr := dN1sRevW_opt3_count_t_exact t (truncBkNucCfg bk cfg) 339 (Or.inr (Or.inl rfl)) v
    rCombBase
  have htop437 : 149 + mCoreEff mWB ≤ 437 := by dsimp [mCoreEff]; omega
  have hk_cap : 318 + kHeld210 bk + t.wAcc ≤ (149 + mCoreEff mWB) + 21 + 3 := by
    have := wAcc_bounds t; have := hbk.2; dsimp [kHeld210, mCoreEff] at hm ⊢; omega
  have hmk := (slot3MidKickHeldU54BkOptSpec bk (kHeld210 bk) hbk.1 hbk.2 (kHeld210_hs hbk)).hT
    (truncBkNucCfg bk cfg) v
    (rCombBase.compose (mkSelMaskWide 21 3 (kHeld210 bk) (149 + mCoreEff mWB) t
      le_rfl le_rfl htop437 hk_cap))
  have har := zret_opt3_core_arith t
  have hge := tCoreWide_ge_5436_save t
  dsimp only [dCore149RegimeA_onBase, tCoreHeld210, stage26SaveFast, n1sTotOptSaveS3]
  repeat rw [n1s_dyn_count_seq]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd, pStep1XorSq_275_count,
    dPreMKCtrl_count_t, dRejKick0_437_count_t,
    TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
    pStep5ZRet30_count, dPostMKCtrl84_count_t, dSTrue18RevXorSq_275_count_t,
    dRevTailZQuadRet216_256_count_t, hf, hr]
  omega
theorem stepBundleW_dCore149RegimeA_onBase (mWB bk : ℕ)
    (hm : 210 ≤ mCoreEff mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n) : StepBundleW
    (149 + mCoreEff mWB) v rCombBase st0
    (fun α ↦ st0 (corePerm149_norm1s t (truncBkNucCfg bk cfg) α)) (corePhase149_norm1s t)
    (dCore149RegimeA_onBase mWB bk hm hbk t cfg v rCombBase) := by
  let cBk := truncBkNucCfg bk cfg
  let topW := 149 + mCoreEff mWB
  have hle : 339 ≤ topW := by dsimp [topW]; omega
  have htop437 : topW ≤ 437 := by dsimp [topW, mCoreEff]; omega
  have hk_cap : 318 + kHeld210 bk + t.wAcc ≤ topW + 21 + 3 := by
    have := wAcc_bounds t; have := hbk.2; dsimp [topW, kHeld210, mCoreEff] at hm ⊢; omega
  have hclr : clearPreMKOfTopW 339 = clearPreMKCtrl := ite_eq_right (by decide)
  have hcl_st0 : ∀ α : BitAssignment 149, cleanRem 437 (437 - 275) (st0 α) :=
    fun α w hw ↦ padZeroBits149_clean α w (by omega)
  have hcl_st1 : ∀ α : BitAssignment 149, cleanRem 437 (437 - 275) (st1QZ α) :=
    fun α ↦ cleanRem_putQZ (n1s_st1_props α).1.hcl
  have hcl_pre : ∀ α : BitAssignment 149,
      cleanRem 437 (437 - 275) ((clearPreMKCtrl ∘ st1QZ) α) :=
    fun α ↦ clearMaskWide_21_3 ▸ cleanRem_clearMaskWide 21 3 le_rfl le_rfl (hcl_st1 α)
  have hcl_st2 : ∀ α : BitAssignment 149, cleanRem 437 (437 - 275)
      ((clearPreMKCtrl ∘ putQZ ∘ n1sSt2 t) α) := fun α ↦ clearMaskWide_21_3 ▸
      cleanRem_clearMaskWide 21 3 le_rfl le_rfl (cleanRem_putQZ (n1s_st2_props t α).1.hcl)
  have hcl_st3 : ∀ α : BitAssignment 149,
      cleanRem 437 (437 - 275) ((clearPreMKCtrl ∘ putQZ ∘ n1sSt3 t cBk) α) :=
    fun α ↦ clearMaskWide_21_3 ▸
      cleanRem_clearMaskWide 21 3 le_rfl le_rfl (cleanRem_putQZ (n1s_st3_retainedInv t cBk α).hcl)
  have h1 := StepBundleW.widen_topW hle hcl_st0
    (stepBundleW_step1XorSq (topW := 339) (by decide) (by decide) v rCombBase)
  have hpre := StepBundleW.widen_topW hle hcl_st1
    (stepBundleW_dPreMKCtrl 339 (Or.inr rfl) v rCombBase)
  have h2_0 := stepBundleW_dN1sFwdW_opt3 t 339 (Or.inr (Or.inl rfl)) v rCombBase
  have h3_0 := stepBundleW_dRejKick0 t 339 (by decide) (by decide) v rCombBase
  have h4 := stepBundleW_midKickBk_maskWide (slot3MidKickHeldU54BkOptSpec bk (kHeld210 bk) hbk.1
    hbk.2 (kHeld210_hs hbk)) t cBk 21 3 topW le_rfl le_rfl
      (by omega) htop437 hk_cap v rCombBase
  rw [clearMaskWide_21_3, fast414_truncBkNucCfg_of_truncBkNucCfg bk cfg] at h4
  have h5 := stepBundleW_pStep5ZRet30 t cBk 339 (by decide) (by decide) (by decide) v rCombBase
  have h6 := stepBundleW_dN1sRevW_opt3 t cBk 339 (Or.inr (Or.inl rfl)) v rCombBase
  have hpost := stepBundleW_dPostMKCtrl84 t cBk v rCombBase
  have h7 := stepBundleW_dSTrue18RevXorSq t cBk (topW := 339) (by decide) (by decide) v rCombBase
  have h8 := stepBundleW_dRevTailZQuadRet256 t cBk (topW := 339) (by decide) (by decide) v rCombBase
  rw [hclr] at h2_0 h3_0 h5 h6
  have h2 := StepBundleW.widen_topW hle hcl_pre h2_0
  have h3 := StepBundleW.widen_topW hle hcl_st2 h3_0
  have h5_end := StepBundleW.widen_topW hle hcl_st3
    (h5.seq_zero_left (h6.seq_zero_left (hpost.seq_zero_left (h7.seq_zero_left h8))))
  exact h1.seq_zero_left (hpre.seq_zero_left (h2.seq_zero_left (h3.seq_zero_right (h4.seq_zero_left
    h5_end))))
theorem le_mCoreEff_210 {mWB : ℕ} (hm210 : 210 ≤ mWB) : 210 ≤ mCoreEff mWB := by
  dsimp only [mCoreEff]; omega
/-- Adaptive 4-regime `onBase` core selector choosing the exact minimum-`T` active regime at `(F,
mWB, bk, t)`. -/
noncomputable def dCore149WideGen_onBase (mWB bk : ℕ)
    (hm210 : 210 ≤ mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36)
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) : DynamicCircuit Var n :=
  dCore149RegimeA_onBase mWB bk (le_mCoreEff_210 hm210) hbk t cfg v rCombBase
theorem dCore149WideGen_onBase_count_toff (mWB bk : ℕ)
    (hm210 : 210 ≤ mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36)
    (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dCore149WideGen_onBase mWB bk hm210 hbk t cfg v rCombBase).count toffoli = 0 :=
  dCore149RegimeA_onBase_count_toff mWB bk (le_mCoreEff_210 hm210) hbk t cfg v rCombBase
theorem dCore149WideGen_onBase_count_t (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type}
    {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dCore149WideGen_onBase mWB bk hm210 hbk t cfg v rCombBase).count T ≤ tCoreHeld210 bk t :=
  dCore149RegimeA_onBase_count_t mWB bk (le_mCoreEff_210 hm210) hbk t cfg v rCombBase
theorem stepBundleW_dCore149WideGen_onBase (mWB bk : ℕ)
    (hm210 : 210 ≤ mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n) : StepBundleW
    (149 + mCoreEff mWB) v rCombBase st0
    (fun α ↦ st0 (corePerm149_norm1s t (truncBkNucCfg bk cfg) α)) (corePhase149_norm1s t)
    (dCore149WideGen_onBase mWB bk hm210 hbk t cfg v rCombBase) :=
  stepBundleW_dCore149RegimeA_onBase mWB bk (le_mCoreEff_210 hm210) hbk t cfg v rCombBase
/-- Clean-workspace adaptive `uCore149Norm1s t (truncBkNucCfg bk cfg)` realizer on `mCoreEff
mWB`. -/
noncomputable def dCore149WideEffGen (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type}
    {n : ℕ} (v : Var) (rAct149 : QRegister 149 n) (rWorkEff : QRegister (mCoreEff mWB) n)
    (rDummy : QRegister (288 - mCoreEff mWB) n) (hAW : rAct149.DisjointWires rWorkEff)
    (hAD : rAct149.DisjointWires rDummy) (hWD : rWorkEff.DisjointWires rDummy) :
    DynamicCircuit Var n :=
  dCore149WideGen_onBase mWB bk hm210 hbk t cfg v
    (castNatReg (by dsimp [mCoreEff]; omega : (149 + mCoreEff mWB) + (288 - mCoreEff mWB) = 437)
      ((rAct149.concat rWorkEff hAW).concat rDummy (disjConcatLeft hAD hWD)))
/-- Width-unrestricted (`190 ≤ mWB`) adaptive clean-workspace realizer of
`uCore149Norm1s t (truncBkNucCfg bk cfg)` at `tCoreHeld210 bk t`. -/
noncomputable def dCore149WideGen (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type}
    {n : ℕ} (v : Var) (rAct149 : QRegister 149 n) (rWork : QRegister mWB n)
    (rDummy : QRegister (288 - mCoreEff mWB) n) (hAW : rAct149.DisjointWires rWork)
    (hAD : rAct149.DisjointWires rDummy) (hWD : rWork.DisjointWires rDummy) : DynamicCircuit
    Var n :=
  dCore149WideEffGen mWB bk hm210 hbk t cfg v rAct149
    (rWork.slice 0 (mCoreEff mWB) (by dsimp [mCoreEff]; omega)) rDummy
    (hAW.compose_right _) hAD (hWD.compose_left _)
theorem dCore149WideGen_count_toff (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type}
    {n : ℕ} (v : Var) (rAct149 : QRegister 149 n) (rWork : QRegister mWB n)
    (rDummy : QRegister (288 - mCoreEff mWB) n) (hAW : rAct149.DisjointWires rWork)
    (hAD : rAct149.DisjointWires rDummy) (hWD : rWork.DisjointWires rDummy) : (dCore149WideGen
    mWB bk hm210 hbk t cfg v rAct149 rWork rDummy hAW hAD hWD).count toffoli = 0 :=
    dCore149WideGen_onBase_count_toff mWB bk hm210 hbk t cfg v _
theorem dCore149WideGen_count_t (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type}
    {n : ℕ} (v : Var) (rAct149 : QRegister 149 n) (rWork : QRegister mWB n)
    (rDummy : QRegister (288 - mCoreEff mWB) n) (hAW : rAct149.DisjointWires rWork)
    (hAD : rAct149.DisjointWires rDummy) (hWD : rWork.DisjointWires rDummy) : (dCore149WideGen
    mWB bk hm210 hbk t cfg v rAct149 rWork rDummy hAW hAD hWD).count T ≤ tCoreHeld210 bk t :=
      dCore149WideGen_onBase_count_t mWB bk hm210 hbk t cfg v _
theorem dCore149WideGen_realizes (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rAct149 : QRegister 149 n) (rWork : QRegister mWB n)
    (rDummy : QRegister (288 - mCoreEff mWB) n) (hAW : rAct149.DisjointWires rWork)
    (hAD : rAct149.DisjointWires rDummy) (hWD : rWork.DisjointWires rDummy) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct149 rWork
    (uCore149Norm1s t (truncBkNucCfg bk cfg)) (dCore149WideGen mWB bk hm210 hbk t cfg v
    rAct149 rWork rDummy hAW hAD hWD) :=
  (StepBundleW.to_cleanWorkspace
    (by dsimp [mCoreEff]; omega : (149 + mCoreEff mWB) + (288 - mCoreEff mWB) = 437)
    (by dsimp [mCoreEff]; omega : 275 ≤ 149 + mCoreEff mWB) v rAct149
    (rWork.slice 0 (mCoreEff mWB) (by dsimp [mCoreEff]; omega)) rDummy
    (hAW.compose_right _) hAD (hWD.compose_left _)
    (uCore149Norm1s t (truncBkNucCfg bk cfg))
    (corePerm149_norm1s t (truncBkNucCfg bk cfg))
    (corePhase149_norm1s t)
    (Slot3Norm1s36Physics80.uCore149Norm1s_mulVec t
      (truncBkNucCfg bk cfg)) _
    (stepBundleW_dCore149WideGen_onBase mWB bk hm210 hbk t cfg v _)).widenWorkspace
/-! ## Section 4: `Slot3LeafSpec 36 mWB`, `Leaf3WideSpec`, & `Leaf3WideBundleGen` Master
Closures -/
/-- Raw `36`-catalyst `Slot3LeafSpec 36 mWB (tLeaf3Held210 mWB bk t)` (`190 ≤ mWB`, `9 ≤ bk ≤
36`). -/
noncomputable def slot3CatWideZRetGen (mWB bk : ℕ)
    (hm210 : 210 ≤ mWB) (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) :
    Slot3LeafSpec 36 mWB (tLeaf3Held210 mWB bk t) :=
  mkSlot3Cat36LeafOfTruncCoreWithDummy (bk := bk) t
    (by dsimp [mCoreEff]; omega : 18 + (288 - mCoreEff mWB) ≤ 3924)
    (le_refl mWB) le_rfl
    (slot3PrepAdaptiveSpec mWB (by omega))
    (dCore149WideGen mWB bk (by omega) hbk t)
    (dCore149WideGen_count_toff mWB bk (by omega) hbk t)
    (dCore149WideGen_count_t mWB bk (by omega) hbk t)
    (dCore149WideGen_realizes mWB bk (by omega) hbk t)
theorem slot3CatWideZRetGen_uCat (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) :
    (slot3CatWideZRetGen mWB bk hm210 hbk t).uCat = fun cfg ↦ uSlot3Swap3Cat36Norm1s t
    (truncBkNucCfg bk cfg) := rfl
/-- HadCut-wrapped `Slot3LeafSpec 36 mWB (tLeaf3Held210 mWB bk t)` (`200 ≤ mWB`, `9 ≤ bk ≤ 36`). -/
noncomputable def slot3CatWideHadCutGen (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) : Slot3LeafSpec 36 mWB
    (tLeaf3Held210 mWB bk t) := slot3HadCutLeafSpec36OfTrunc t (truncBkNucCfg bk)
    (slot3CatWideZRetGen mWB bk hm210 hbk t) (slot3CatWideZRetGen_uCat mWB bk hm210 hbk t)
    le_rfl
theorem slot3CatWideHadCutGen_uCat (mWB bk : ℕ) (hm210 : 210 ≤ mWB)
    (hbk : 9 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) :
    (slot3CatWideHadCutGen mWB bk hm210 hbk t).uCat = fun cfg ↦ uSlot3HadCutCat36Mom t
    (truncBkNucCfg bk cfg) := rfl
/-- Held-`u54` 6-tier `Leaf3WideSpec wCtrl wCat` (`210 ≤ wCtrl`, `210 ≤ wCat`, `21 ≤ bk ≤ 36`). -/
noncomputable def stepLeaf3HeldU54WideSpec_ultra (wCtrl wCat bk : ℕ)
    (hwCtrl : 210 ≤ wCtrl) (hwCat : 210 ≤ wCat)
    (hbk : 21 ≤ bk ∧ bk ≤ 36) (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t) :
    Leaf3WideSpec wCtrl wCat (tLeaf3Held210 wCtrl bk t) (tLeaf3Held210 wCat bk t) :=
  mkLeaf3WideSpecOfTruncLeaves bk hbk t ht
    (slot3CatWideHadCutGen wCtrl bk hwCtrl ⟨by omega, hbk.2⟩ t)
    (slot3CatWideHadCutGen wCat bk hwCat ⟨by omega, hbk.2⟩ t)
    (slot3CatWideHadCutGen_uCat wCtrl bk hwCtrl ⟨by omega, hbk.2⟩ t)
    (slot3CatWideHadCutGen_uCat wCat bk hwCat ⟨by omega, hbk.2⟩ t)
end
end Held210
end
end Held210

end QuantumComputation.Specs.StoppingPowerSolution
